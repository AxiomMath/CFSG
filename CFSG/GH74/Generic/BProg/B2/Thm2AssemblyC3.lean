module

public import CFSG.GH74.Generic.BProg.B2.Thm2AssemblyList
public import CFSG.GH74.GLS.C3.Layer1.BkB2G4Def
import CFSG.GH74.Generic.BProg.B2.Prop31
import CFSG.GH74.Generic.BProg.B2.T1Comp
import CFSG.GH74.Generic.BProg.B2.Lemma82
public import CFSG.GH74.Generic.BProg.B2.Defs

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.GH74.Uniqueness
  CFSG.ABGLocalTools CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup
open scoped Pointwise

namespace Thm2AssemblyC3

theorem center_eq_bot_of_simple_quasisimple {Q : Type*} [Group Q] (hQ : IsQuasisimple Q)
    (hs : IsSimpleGroup Q) : center Q = ⊥ := by
  rcases (inferInstance : (center Q).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    obtain ⟨-, -, a, b, hab⟩ := hQ
    apply hab
    induction a using QuotientGroup.induction_on with | H a => ?_
    induction b using QuotientGroup.induction_on with | H b => ?_
    have ha : a ∈ center Q := h ▸ Subgroup.mem_top a
    have := Subgroup.mem_center_iff.1 ha b
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, this]

section Swap

variable {Y : Type} [Group Y]

@[expose] noncomputable def diagHom (t : Y) (L₁ L₂ : Subgroup Y)
    (hc : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) (h12 : ∀ a ∈ L₁, t * a * t⁻¹ ∈ L₂) :
    ↥L₁ →* Y where
  toFun a := (a : Y) * (t * (a : Y) * t⁻¹)
  map_one' := by simp
  map_mul' a b := by
    have h := hc (b : Y) b.2 (t * (a : Y) * t⁻¹) (h12 a a.2)
    calc ((a * b : ↥L₁) : Y) * (t * ((a * b : ↥L₁) : Y) * t⁻¹)
        = (a : Y) * ((b : Y) * (t * (a : Y) * t⁻¹)) * (t * (b : Y) * t⁻¹) := by
          simp only [Subgroup.coe_mul]; group
      _ = (a : Y) * ((t * (a : Y) * t⁻¹) * (b : Y)) * (t * (b : Y) * t⁻¹) := by rw [h]
      _ = ((a : Y) * (t * (a : Y) * t⁻¹)) * ((b : Y) * (t * (b : Y) * t⁻¹)) := by group

variable {t : Y} {L₁ L₂ : Subgroup Y}

theorem diagHom_apply (hc : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) (h12 : ∀ a ∈ L₁, t * a * t⁻¹ ∈ L₂)
    (a : ↥L₁) : diagHom t L₁ L₂ hc h12 a = (a : Y) * (t * (a : Y) * t⁻¹) := rfl

theorem le_normalizer_of_commute (hc : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) :
    L₂ ≤ normalizer (L₁ : Set Y) := by
  intro b hb
  refine Lemma82.mem_normalizer_of_forall (fun n hn => ?_) (fun n hn => ?_)
  · have e : b * n * b⁻¹ = n := by
      rw [← hc n hn b hb]; group
    rw [e]; exact hn
  · have e : b⁻¹ * n * b⁻¹⁻¹ = n := by
      rw [← hc n hn b⁻¹ (L₂.inv_mem hb)]; group
    rw [inv_inv] at e
    rw [e]; exact hn

theorem mem_sup_iff (hc : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) {y : Y} :
    y ∈ L₁ ⊔ L₂ ↔ ∃ a ∈ L₁, ∃ b ∈ L₂, a * b = y := by
  have h := Subgroup.coe_mul_of_right_le_normalizer_left L₁ L₂ (le_normalizer_of_commute hc)
  have : y ∈ ((L₁ ⊔ L₂ : Subgroup Y) : Set Y) ↔ y ∈ (L₁ : Set Y) * (L₂ : Set Y) := by rw [h]
  simpa [Set.mem_mul] using this

theorem diagHom_injective (hc : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) (hcap : L₁ ⊓ L₂ = ⊥)
    (h12 : ∀ a ∈ L₁, t * a * t⁻¹ ∈ L₂) : Function.Injective (diagHom t L₁ L₂ hc h12) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro a ha
  rw [MonoidHom.mem_ker] at ha
  have h1 : (a : Y) * (t * (a : Y) * t⁻¹) = 1 := ha
  have h2 : (a : Y) = (t * (a : Y) * t⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left h1
  have h3 : (a : Y) ∈ L₂ := h2 ▸ L₂.inv_mem (h12 a a.2)
  have h4 : (a : Y) ∈ L₁ ⊓ L₂ := ⟨a.2, h3⟩
  rw [hcap, Subgroup.mem_bot] at h4
  exact Subgroup.mem_bot.2 (Subtype.ext h4)

theorem range_diagHom (ht : t * t = 1) (hc : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a)
    (hcap : L₁ ⊓ L₂ = ⊥) (h12 : ∀ a ∈ L₁, t * a * t⁻¹ ∈ L₂) (h21 : ∀ b ∈ L₂, t * b * t⁻¹ ∈ L₁) :
    (diagHom t L₁ L₂ hc h12).range = (L₁ ⊔ L₂) ⊓ centralizer ({t} : Set Y) := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  ext y
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨?_, ?_⟩
    · exact Subgroup.mul_mem _ (Subgroup.mem_sup_left a.2) (Subgroup.mem_sup_right (h12 a a.2))
    · show _ ∈ centralizer ({t} : Set Y)
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h := hc (a : Y) a.2 (t * (a : Y) * t⁻¹) (h12 a a.2)
      rw [htinv] at h
      rw [diagHom_apply, htinv]
      have e : t * ((a : Y) * (t * (a : Y) * t)) * t = (a : Y) * (t * (a : Y) * t) := by
        calc t * ((a : Y) * (t * (a : Y) * t)) * t = (t * (a : Y) * t) * (a : Y) * (t * t) := by
              group
          _ = (t * (a : Y) * t) * (a : Y) := by rw [ht, mul_one]
          _ = (a : Y) * (t * (a : Y) * t) := h.symm
      have e2 : t * ((a : Y) * (t * (a : Y) * t)) = (a : Y) * (t * (a : Y) * t) * t := by
        calc t * ((a : Y) * (t * (a : Y) * t))
            = t * ((a : Y) * (t * (a : Y) * t)) * (t * t) := by rw [ht, mul_one]
          _ = (t * ((a : Y) * (t * (a : Y) * t)) * t) * t := by group
          _ = (a : Y) * (t * (a : Y) * t) * t := by rw [e]
      exact e2.symm
  · rintro ⟨hy, hyc⟩
    have hyc : y ∈ centralizer ({t} : Set Y) := hyc
    have hy : y ∈ L₁ ⊔ L₂ := hy
    rw [Subgroup.mem_centralizer_singleton_iff] at hyc
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff hc).1 hy
    have hty : t * (a * b) * t⁻¹ = a * b := by
      rw [mul_inv_eq_iff_eq_mul]
      exact hyc.symm
    have e1 : t * (a * b) * t⁻¹ = (t * a * t⁻¹) * (t * b * t⁻¹) := by group
    have hb' : t * b * t⁻¹ ∈ L₁ := h21 b hb
    have ha' : t * a * t⁻¹ ∈ L₂ := h12 a ha
    have hcomm : (t * a * t⁻¹) * (t * b * t⁻¹) = (t * b * t⁻¹) * (t * a * t⁻¹) :=
      (hc _ hb' _ ha').symm
    have hab : (t * b * t⁻¹)⁻¹ * a = (t * a * t⁻¹) * b⁻¹ := by
      have h2 : a * b = (t * b * t⁻¹) * (t * a * t⁻¹) := by rw [← hcomm, ← e1, hty]
      calc (t * b * t⁻¹)⁻¹ * a = (t * b * t⁻¹)⁻¹ * (a * b) * b⁻¹ := by group
        _ = (t * b * t⁻¹)⁻¹ * ((t * b * t⁻¹) * (t * a * t⁻¹)) * b⁻¹ := by rw [h2]
        _ = (t * a * t⁻¹) * b⁻¹ := by group
    have hmem1 : (t * b * t⁻¹)⁻¹ * a ∈ L₁ := L₁.mul_mem (L₁.inv_mem hb') ha
    have hmem2 : (t * b * t⁻¹)⁻¹ * a ∈ L₂ := by
      rw [hab]; exact L₂.mul_mem ha' (L₂.inv_mem hb)
    have hone : (t * b * t⁻¹)⁻¹ * a = 1 := by
      have : (t * b * t⁻¹)⁻¹ * a ∈ L₁ ⊓ L₂ := ⟨hmem1, hmem2⟩
      rw [hcap, Subgroup.mem_bot] at this
      exact this
    have haeq : a = t * b * t⁻¹ := by
      have := inv_mul_eq_one.1 hone
      exact this.symm
    have hbeq : t * a * t⁻¹ = b := by
      have htt : t⁻¹ * t⁻¹ = 1 := by rw [htinv, ht]
      rw [haeq]
      calc t * (t * b * t⁻¹) * t⁻¹ = (t * t) * b * (t⁻¹ * t⁻¹) := by group
        _ = b := by rw [ht, htt]; simp
    refine ⟨⟨a, ha⟩, ?_⟩
    rw [diagHom_apply]
    show a * (t * a * t⁻¹) = a * b
    rw [hbeq]

theorem mulEquiv_centralizer_of_swap (ht : t * t = 1) (hc : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a)
    (hcap : L₁ ⊓ L₂ = ⊥) (h12 : ∀ a ∈ L₁, t * a * t⁻¹ ∈ L₂) (h21 : ∀ b ∈ L₂, t * b * t⁻¹ ∈ L₁) :
    Nonempty (↥L₁ ≃* ↥((L₁ ⊔ L₂) ⊓ centralizer ({t} : Set Y))) :=
  ⟨(MonoidHom.ofInjective (diagHom_injective hc hcap h12)).trans
    (MulEquiv.subgroupCongr (range_diagHom ht hc hcap h12 h21))⟩

end Swap

section Comp

variable {Y : Type} [Group Y]

theorem eq_of_isCompIn_of_simple {N Kb : Subgroup Y} (hN : IsSimpleGroup ↥N) (hK : IsCompIn N Kb) :
    Kb = N := by
  rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hN hK.2.2 with h | h
  · exfalso
    have := CFSG.LocalCores.isQuasisimple_nontrivial hK.2.1
    rw [h] at this
    exact not_nontrivial_iff_subsingleton.2 (inferInstance : Subsingleton (⊥ : Subgroup ↥N)) this
  · exact le_antisymm hK.1 (Subgroup.subgroupOf_eq_top.1 h)

end Comp

section Stage2

variable {G : Type} [Group G] [Finite G] {x : G} {K A M P Q H : Subgroup G}

theorem qShapeNS_of_swap (hB : B_B2_g4) (hs : Stage2Setup G x K A M P Q)
    (h1 : Stage2Concl1Core x K M Q H) (hxM : x ∈ M) {L₁ L₂ : Subgroup (Mbar M)}
    (hL₁ : IsComponent L₁) (hL₂ : IsComponent L₂) (hne : L₁ ≠ L₂) (hs₁ : IsSimpleGroup ↥L₁)
    (hsup : barIn M H = L₁ ⊔ L₂)
    (h12 : ∀ a ∈ L₁, (QuotientGroup.mk (⟨x, hxM⟩ : ↥M) : Mbar M) * a *
      (QuotientGroup.mk (⟨x, hxM⟩ : ↥M) : Mbar M)⁻¹ ∈ L₂)
    (h21 : ∀ b ∈ L₂, (QuotientGroup.mk (⟨x, hxM⟩ : ↥M) : Mbar M) * b *
      (QuotientGroup.mk (⟨x, hxM⟩ : ↥M) : Mbar M)⁻¹ ∈ L₁) : QShapeNS ↥L₁ := by
  have := hs₁
  set t : Mbar M := (QuotientGroup.mk (⟨x, hxM⟩ : ↥M) : Mbar M) with htdef
  have ht2 : orderOf t = 2 := Prop31.orderOf_mk_involution hxM hs.pair.1.1.1.1
  have ht : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht2, pow_two] at this
  have hc : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a := by
    intro a ha b hb
    have hle : L₁ ≤ centralizer (L₂ : Set (Mbar M)) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1
        ((CFSG.LocalCores.distinct_components_commute hL₁ hL₂).resolve_left hne)
    exact (Subgroup.mem_centralizer_iff.1 (hle ha) b hb).symm
  have hZ1 : center ↥L₁ = ⊥ := center_eq_bot_of_simple_quasisimple hL₁.1 hs₁
  have hcap : L₁ ⊓ L₂ = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hzc : (⟨z, hz.1⟩ : ↥L₁) ∈ center ↥L₁ := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hc g g.2 z hz.2)
    rw [hZ1, Subgroup.mem_bot] at hzc
    exact Subgroup.mem_bot.2 (congrArg Subtype.val hzc)
  obtain ⟨e⟩ := mulEquiv_centralizer_of_swap ht hc hcap h12 h21
  set N : Subgroup (Mbar M) := (L₁ ⊔ L₂) ⊓ centralizer ({t} : Set (Mbar M)) with hN
  have hNsimple : IsSimpleGroup ↥N := e.symm.isSimpleGroup
  have hcomp := barIn_K_isCompIn hB hs h1.K_le hxM
  have hKH : K ≤ H := h1.H_min.1
  have hbarKH : barIn M K ≤ L₁ ⊔ L₂ := by
    rw [← hsup]
    rintro _ ⟨m, hm, rfl⟩
    exact ⟨m, hKH hm, rfl⟩
  have hcomp' : IsCompIn N (barIn M K) :=
    Prop31.isCompIn_of_le (le_inf hbarKH hcomp.1) inf_le_right hcomp
  have hKN : barIn M K = N := eq_of_isCompIn_of_simple hNsimple hcomp'
  have hKq : IsQuasisimple ↥(barIn M K) := Prop31.isQuasisimple_of_isCompIn hcomp
  let e' : ↥(barIn M K) ≃* ↥L₁ := (MulEquiv.subgroupCongr hKN).trans e.symm
  have hKsimple : IsSimpleGroup ↥(barIn M K) := e'.isSimpleGroup
  obtain ⟨Z, hZc, -, hZn, hZshape⟩ := Prop31.exists_shape hs h1.K_le hKq
  have hZbot : Z = ⊥ := by
    have := center_eq_bot_of_simple_quasisimple hKq hKsimple
    rw [this] at hZc
    exact le_bot_iff.1 hZc
  subst hZbot
  exact QShapeNS.of_mulEquiv e'
    (QShapeNS.of_mulEquiv (QuotientGroup.quotientBot (G := ↥(barIn M K))) hZshape)

end Stage2

end Thm2AssemblyC3

theorem listedK_of_c3 {G : Type} [Group G] [Finite G] {x : G} {K A M P Q H : Subgroup G}
    (hB : B_B2_g4) (hs : Stage2Setup G x K A M P Q) (h1 : Stage2Concl1Core x K M Q H) (hxM : x ∈ M)
    {L₁ L₂ : Subgroup (Mbar M)} (hL₁ : IsComponent L₁) (hL₂ : IsComponent L₂) (hne : L₁ ≠ L₂)
    (hs₁ : IsSimpleGroup ↥L₁) (hs₂ : IsSimpleGroup ↥L₂) (hsup : barIn M H = L₁ ⊔ L₂)
    (hconj : L₁.map (MulAut.conj (QuotientGroup.mk (⟨x, hxM⟩ : ↥M) : Mbar M)).toMonoidHom = L₂) :
    ListedK ↥L₁ ∧ ListedK ↥L₂ := by
  set t : Mbar M := (QuotientGroup.mk (⟨x, hxM⟩ : ↥M) : Mbar M) with htdef
  have ht2 : orderOf t = 2 := Prop31.orderOf_mk_involution hxM hs.pair.1.1.1.1
  have ht : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht2, pow_two] at this
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have h12 : ∀ a ∈ L₁, t * a * t⁻¹ ∈ L₂ := by
    intro a ha
    have := Subgroup.mem_map_of_mem (MulAut.conj t).toMonoidHom ha
    rw [hconj] at this
    simpa using this
  have h21 : ∀ b ∈ L₂, t * b * t⁻¹ ∈ L₁ := by
    intro b hb
    rw [← hconj] at hb
    obtain ⟨a, ha, rfl⟩ := hb
    have e : t * ((MulAut.conj t).toMonoidHom a) * t⁻¹ = a := by
      show t * (t * a * t⁻¹) * t⁻¹ = a
      rw [htinv]
      calc t * (t * a * t) * t = (t * t) * a * (t * t) := by group
        _ = a := by rw [ht]; simp
    rw [e]; exact ha
  refine ⟨Thm2AssemblyC3.qShapeNS_of_swap hB hs h1 hxM hL₁ hL₂ hne hs₁ hsup h12 h21,
    Thm2AssemblyC3.qShapeNS_of_swap hB hs h1 hxM hL₂ hL₁ hne.symm hs₂ (by rw [hsup, sup_comm])
      h21 h12⟩

theorem listedPair_of_qShapeNS {J : Type} [Group J] (hq : IsQuasisimple J) (hs : IsSimpleGroup J)
    (h : QShapeNS J) : ListedPair J := by
  refine ⟨hs, ?_⟩
  rcases h with h1 | h3 | h4 | h5
  · exfalso
    have hc := CFSG.GH74.L5U5.IsSL4Model.natCard_center h1
    rw [Thm2AssemblyC3.center_eq_bot_of_simple_quasisimple hq hs, Subgroup.card_bot] at hc
    omega
  · exact Or.inl h3
  · exact Or.inr (Or.inl h4)
  · exact Or.inr (Or.inr h5)

theorem listedPair_of_c3 {G : Type} [Group G] [Finite G] {x : G} {K A M P Q H : Subgroup G}
    (hB : B_B2_g4) (hs : Stage2Setup G x K A M P Q) (h1 : Stage2Concl1Core x K M Q H) (hxM : x ∈ M)
    {L₁ L₂ : Subgroup (Mbar M)} (hL₁ : IsComponent L₁) (hL₂ : IsComponent L₂) (hne : L₁ ≠ L₂)
    (hs₁ : IsSimpleGroup ↥L₁) (hs₂ : IsSimpleGroup ↥L₂) (hsup : barIn M H = L₁ ⊔ L₂)
    (hconj : L₁.map (MulAut.conj (QuotientGroup.mk (⟨x, hxM⟩ : ↥M) : Mbar M)).toMonoidHom = L₂) :
    ListedPair ↥L₁ ∧ ListedPair ↥L₂ := by
  obtain ⟨h₁, h₂⟩ := listedK_of_c3 hB hs h1 hxM hL₁ hL₂ hne hs₁ hs₂ hsup hconj
  exact ⟨listedPair_of_qShapeNS hL₁.1 hs₁ h₁, listedPair_of_qShapeNS hL₂.1 hs₂ h₂⟩

end CFSG.GH74.Generic.BProg.B2
