module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5Transfer
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5Props
import CFSG.LocalAnalysis.ComponentClassification.StandardSubgroupAPI

public section

namespace CFSG.EvenSporadicStandard.HSStd

open Subgroup CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.NativeSporadic

@[expose] def CatNoOuterHS : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Blueprint.Catalog X → IsSimpleGroup X →
    ∀ τ : MulAut X, τ * τ = 1 → (∀ x : X, τ ≠ MulAut.conj x) →
      ¬ ∃ A : Subgroup X, A ≤ autCentralizer τ ∧ (A.subgroupOf (autCentralizer τ)).Normal ∧
        IsSporadic ↥A .HS

section

variable {H : Type} [Group H]

theorem mem_normalizer_of_commute_involution {A : Subgroup H}
    (hA : CFSG.Open.standardComponentIsStandard A) {t g : H} (ht : orderOf t = 2)
    (htC : t ∈ centralizer (A : Set H)) (hg : g * t = t * g) : g ∈ normalizer (A : Set H) :=
  CFSG.Open.standardComponentIsStandard.mem_normalizer_of_commute hA htC ht hg

theorem catalog_of_kProper_simple {K : Subgroup H}
    (hkp : KProper CFSG.Blueprint.Catalog H) (hK : K ≠ ⊤) (hs : IsSimpleGroup ↥K)
    (hna : ∃ a b : ↥K, a * b ≠ b * a) : CFSG.Blueprint.Catalog ↥K := by
  have hb : (⊥ : Subgroup H).subgroupOf K = ⊥ := Subgroup.bot_subgroupOf K
  let e : (↥K ⧸ (⊥ : Subgroup H).subgroupOf K) ≃* ↥K :=
    (QuotientGroup.quotientMulEquivOfEq hb).trans QuotientGroup.quotientBot
  have hn : ((⊥ : Subgroup H).subgroupOf K).Normal := by
    rw [hb]
    infer_instance
  have hs' : IsSimpleGroup (↥K ⧸ (⊥ : Subgroup H).subgroupOf K) := e.isSimpleGroup
  obtain ⟨a, b, hab⟩ := hna
  have hcat := hkp K ⊥ hK bot_le hs'
    ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩
  exact CFSG.SectionRank.catalog_of_mulEquiv e.symm hcat

variable [Finite H]

theorem mem_of_centralizes_of_index_le_two {D : Subgroup H} (hZ : center H = ⊥)
    (hidx : D.index ≤ 2) {u : H} (hu : ∀ d ∈ D, u * d = d * u) : u ∈ D := by
  by_contra hnu
  have h2 : D.index = 2 := by
    have h0 : D.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have h1 : D.index ≠ 1 := fun h =>
      hnu (by rw [Subgroup.index_eq_one.1 h]; exact Subgroup.mem_top u)
    omega
  have hcent : u ∈ center H := by
    rw [Subgroup.mem_center_iff]
    intro h
    by_cases hh : h ∈ D
    · exact (hu h hh).symm
    · have hd : u⁻¹ * h ∈ D := by
        rw [Subgroup.mul_mem_iff_of_index_two h2]
        exact iff_of_false (fun hi => hnu (by simpa using D.inv_mem hi)) hh
      have hcomm := hu _ hd
      calc h * u = (u * (u⁻¹ * h)) * u := by group
        _ = u * ((u⁻¹ * h) * u) := by rw [mul_assoc]
        _ = u * (u * (u⁻¹ * h)) := by rw [← hcomm]
        _ = u * h := by group
  rw [hZ, Subgroup.mem_bot] at hcent
  exact hnu (by rw [hcent]; exact D.one_mem)

theorem exists_involution_not_mem {C D : Subgroup H} (hidx : D.index ≤ 2) (hC : ¬ C ≤ D)
    (hsyl : ∀ P : Sylow 2 ↥C, Nat.card P = 2) : ∃ t : H, t ∈ C ∧ orderOf t = 2 ∧ t ∉ D := by
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 ↥C))
  have hPD : ¬ (P : Subgroup ↥C) ≤ D.subgroupOf C := by
    intro hle
    have h1 : (D.subgroupOf C).index ∣ (P : Subgroup ↥C).index := Subgroup.index_dvd_of_le hle
    have h2 : ¬ 2 ∣ (P : Subgroup ↥C).index := P.not_dvd_index
    have h3 : (D.subgroupOf C).index ≤ 2 := by
      have := Subgroup.relIndex_le_of_le_right (H := D) (K := C) (L := ⊤) le_top (by
        rw [Subgroup.relIndex_top_right]
        exact Subgroup.index_ne_zero_of_finite)
      rw [Subgroup.relIndex_top_right] at this
      exact this.trans hidx
    have h0 : (D.subgroupOf C).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have h4 : (D.subgroupOf C).index = 1 := by
      by_contra h4
      have h5 : (D.subgroupOf C).index = 2 := by omega
      rw [h5] at h1
      exact h2 h1
    have h6 : D.subgroupOf C = ⊤ := Subgroup.index_eq_one.1 h4
    apply hC
    intro x hx
    have : (⟨x, hx⟩ : ↥C) ∈ D.subgroupOf C := by
      rw [h6]
      exact Subgroup.mem_top _
    exact this
  obtain ⟨y, hyP, hyD⟩ := Set.not_subset.1 hPD
  have hy1 : y ≠ 1 := fun h => hyD (by rw [h]; exact (D.subgroupOf C).one_mem)
  have hdvd : orderOf (⟨y, hyP⟩ : ↥(P : Subgroup ↥C)) ∣ 2 := by
    have := orderOf_dvd_natCard (⟨y, hyP⟩ : ↥(P : Subgroup ↥C))
    rwa [hsyl P] at this
  have hord : orderOf (y : H) = 2 := by
    rw [Subgroup.orderOf_coe]
    have h2 : orderOf y = orderOf (⟨y, hyP⟩ : ↥(P : Subgroup ↥C)) :=
      Subgroup.orderOf_coe (⟨y, hyP⟩ : ↥(P : Subgroup ↥C))
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.1 (h2.trans h)) hy1
    · exact h2.trans h
  exact ⟨(y : H), y.2, hord, hyD⟩

theorem centralizer_le_commutator_of_catNoOuterHS (hCat : CatNoOuterHS) {A : Subgroup H}
    (hkp : KProper CFSG.Blueprint.Catalog H) (hZ : center H = ⊥)
    (hsimple : IsSimpleGroup ↥(commutator H)) (hidx : (commutator H).index ≤ 2)
    (hA : CFSG.Open.standardComponentIsStandard A) (hAHS : IsSporadic ↥A .HS)
    (hsyl : ∀ P : Sylow 2 ↥(centralizer (A : Set H)), Nat.card P = 2) :
    centralizer (A : Set H) ≤ commutator H := by
  by_contra hnle
  obtain ⟨t, htC, ht2, htD⟩ := exists_involution_not_mem hidx hnle hsyl
  have hAD : A ≤ commutator H := Transfer.le_commutator_of_quasisimple_open A hA.1
  obtain ⟨a, b, hab⟩ := Transfer.exists_noncomm_of_quasisimple_open hA.1
  have hnab : ∃ x y : ↥(commutator H), x * y ≠ y * x :=
    ⟨⟨a, hAD a.2⟩, ⟨b, hAD b.2⟩, fun h => hab (Subtype.ext
      (congrArg (fun z : ↥(commutator H) => (z : H)) h))⟩
  have hDtop : commutator H ≠ ⊤ := fun h => htD (by rw [h]; exact Subgroup.mem_top t)
  have hcat := catalog_of_kProper_simple hkp hDtop hsimple hnab
  have ht1 : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rw [ht2] at this
    rw [← sq]
    exact this
  obtain ⟨τ, hτ⟩ : ∃ τ : MulAut ↥(commutator H),
      ∀ x : ↥(commutator H), ((τ x : ↥(commutator H)) : H) = t * (x : H) * t⁻¹ :=
    ⟨MulAut.conjNormal t, fun x => MulAut.conjNormal_apply t x⟩
  have hττ : τ * τ = 1 := by
    refine MulEquiv.ext fun x => ?_
    show τ (τ x) = x
    apply Subtype.ext
    rw [hτ, hτ]
    calc t * (t * (x : H) * t⁻¹) * t⁻¹ = (t * t) * (x : H) * (t * t)⁻¹ := by group
      _ = (x : H) := by rw [ht1]; group
  have hout : ∀ g : ↥(commutator H), τ ≠ MulAut.conj g := by
    intro g hg
    have hu : ∀ d ∈ commutator H, (g : H)⁻¹ * t * d = d * ((g : H)⁻¹ * t) := by
      intro d hd
      have h1 := congrArg (fun φ : MulAut ↥(commutator H) => (φ ⟨d, hd⟩ : H)) hg
      simp only [hτ, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h1
      calc (g : H)⁻¹ * t * d = (g : H)⁻¹ * (t * d * t⁻¹) * t := by group
        _ = (g : H)⁻¹ * ((g : H) * d * (g : H)⁻¹) * t := by rw [h1]
        _ = d * ((g : H)⁻¹ * t) := by group
    have hmem := mem_of_centralizes_of_index_le_two hZ hidx hu
    apply htD
    have : (g : H) * ((g : H)⁻¹ * t) ∈ commutator H := (commutator H).mul_mem g.2 hmem
    simpa using this
  obtain ⟨e⟩ := hAHS
  refine hCat ↥(commutator H) hcat hsimple τ hττ hout ⟨A.subgroupOf (commutator H), ?_, ?_,
    ⟨(Subgroup.subgroupOfEquivOfLe hAD).trans e⟩⟩
  · intro x hx
    show τ x = x
    apply Subtype.ext
    rw [hτ]
    have hc := mem_centralizer_iff.1 htC (x : H) hx
    calc t * (x : H) * t⁻¹ = ((x : H) * t) * t⁻¹ := by rw [hc]
      _ = (x : H) := by group
  · have hle : A.subgroupOf (commutator H) ≤ autCentralizer τ := by
      intro x hx
      show τ x = x
      apply Subtype.ext
      rw [hτ]
      have hc := mem_centralizer_iff.1 htC (x : H) hx
      calc t * (x : H) * t⁻¹ = ((x : H) * t) * t⁻¹ := by rw [hc]
        _ = (x : H) := by group
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hle).2 fun g hg => ?_
    have hg' : t * (g : H) * t⁻¹ = (g : H) := by
      have := congrArg (fun z : ↥(commutator H) => (z : H)) (show τ g = g from hg)
      simpa [hτ] using this
    have hcomm : (g : H) * t = t * (g : H) := by
      calc (g : H) * t = (t * (g : H) * t⁻¹) * t := by rw [hg']
        _ = t * (g : H) := by group
    exact (Transfer.mem_normalizer_subgroupOf_iff hAD g).2
      (mem_normalizer_of_commute_involution hA ht2 htC hcomm)

end

end CFSG.EvenSporadicStandard.HSStd
