module

public import CFSG.GH74.Generic.BProg.B1.PilotS5Facts
public import CFSG.ClassicalInvolution.Models.Transfer.Basic
public import CFSG.LocalAnalysis.ComponentInitial.QuasisimpleOddCenterFourGroup

public section

namespace CFSG.GH74.Generic.BProg.B1.PilotS3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint Subgroup
open CFSG.GH74.Generic.BProg.B1.PilotS5
open CFSG.ClassicalInvolution
open scoped MatrixGroups commutatorElement

section Gen

theorem odd_orderOf_of_mem_pPrimeCore {H : Type*} [Group H] [Finite H] {h : H}
    (hO : h ∈ pPrimeCore 2 H) : Odd (orderOf h) := by
  have hdvd : orderOf h ∣ Nat.card (pPrimeCore 2 H) := Subgroup.orderOf_dvd_natCard (pPrimeCore 2 H) hO
  have hcop : Nat.Coprime 2 (Nat.card (pPrimeCore 2 H)) := CFSG.pPrimeCore_coprime_card
  exact Nat.coprime_two_left.1 (hcop.coprime_dvd_right hdvd)

theorem isPComponent_of_inf_pPrimeCore {H : Type*} [Group H] {M : Subgroup H} (hn : M.Normal)
    (hq : IsQuasisimple ↥M) (hinf : ∀ m ∈ M, m ∈ pPrimeCore 2 H → m = 1) : IsPComponent 2 M := by
  have hinj : ∀ z ∈ M, z ∈ (QuotientGroup.mk' (pPrimeCore 2 H)).ker → z = 1 := fun z hz hzk =>
    hinf z hz (by rwa [QuotientGroup.ker_mk'] at hzk)
  refine ⟨M.map (QuotientGroup.mk' (pPrimeCore 2 H)), ⟨?_, ?_⟩, hn.isSubnormal, rfl, ?_⟩
  · exact (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr
      (CFSG.ClassicalInvolution.Models.Transfer.mulEquivMap hinj)).1 hq
  · exact (hn.map _ (QuotientGroup.mk'_surjective _)).isSubnormal
  · intro J hJ _ hmap
    refine hJ.not_ge fun m hm => ?_
    have hm' : QuotientGroup.mk' (pPrimeCore 2 H) m ∈ J.map (QuotientGroup.mk' (pPrimeCore 2 H)) := by
      rw [hmap]; exact ⟨m, hm, rfl⟩
    obtain ⟨j, hj, hjm⟩ := hm'
    have hjM : j ∈ M := hJ.le hj
    have h1 : j⁻¹ * m = 1 := by
      apply hinj _ (M.mul_mem (M.inv_mem hjM) hm)
      rw [MonoidHom.mem_ker, map_mul, map_inv, hjm, inv_mul_cancel]
    have : m = j := by rw [← mul_one j, ← h1]; group
    rw [this]; exact hj

theorem inf_pPrimeCore_eq_one {H : Type*} [Group H] [Finite H] {M : Subgroup H}
    (hq : IsQuasisimple ↥M) (hZ : Nat.card ↥(center ↥M) = 2) :
    ∀ m ∈ M, m ∈ pPrimeCore 2 H → m = 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : ((pPrimeCore 2 H).subgroupOf M).Normal :=
    Subgroup.Normal.subgroupOf (inferInstance : (pPrimeCore 2 H).Normal) M
  rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_normal_subgroups hq hN with htop | hcen
  · exfalso
    have h2 : 2 ∣ Nat.card ↥(center ↥M) := by rw [hZ]
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(center ↥M)) 2 h2
    have hzO : ((z : ↥M) : H) ∈ pPrimeCore 2 H := by
      have : (z : ↥M) ∈ (pPrimeCore 2 H).subgroupOf M := by rw [htop]; trivial
      exact this
    have hodd := odd_orderOf_of_mem_pPrimeCore hzO
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz] at hodd
    exact absurd hodd (by decide)
  · intro m hm hmO
    have hmc : (⟨m, hm⟩ : ↥M) ∈ center ↥M := hcen (by exact hmO)
    have h1 : orderOf m ∣ 2 := by
      have := Subgroup.orderOf_dvd_natCard (center ↥M) hmc
      rwa [hZ, Subgroup.orderOf_mk] at this
    have h2 : Odd (orderOf m) := odd_orderOf_of_mem_pPrimeCore hmO
    have : orderOf m = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h | h
      · exact h
      · rw [h] at h2; exact absurd h2 (by decide)
    exact orderOf_eq_one_iff.1 this

end Gen

section SL2

variable {F : Type} [Field F] [Finite F]

theorem isQuasisimple_sl2 (h4 : 4 ≤ Nat.card F) : IsQuasisimple SL(2, F) := by
  have hperf : Group.IsPerfect SL(2, F) := sl2_isPerfect h4
  have hs : IsSimpleGroup (SL(2, F) ⧸ center SL(2, F)) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  refine ⟨hperf, hs, ?_⟩
  by_contra hab
  push Not at hab
  have hle : commutator SL(2, F) ≤ center SL(2, F) := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [← QuotientGroup.eq_one_iff]
    change (QuotientGroup.mk' (center SL(2, F))) ⁅x, y⁆ = 1
    rw [map_commutatorElement, commutatorElement_def, hab (QuotientGroup.mk' _ x),
      mul_inv_cancel_right, mul_inv_cancel]
  rw [hperf.commutator_eq_top, top_le_iff] at hle
  obtain ⟨a, b, hne⟩ := exists_pair_ne (SL(2, F) ⧸ center SL(2, F))
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  exact hne (QuotientGroup.eq.mpr (hle ▸ Subgroup.mem_top _))

theorem isQuasisimple_of_equiv_sl2 {P : Type*} [Group P] (h4 : 4 ≤ Nat.card F)
    (e : P ≃* SL(2, F)) : IsQuasisimple P :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm (isQuasisimple_sl2 h4)

theorem isPCompIn_of_normal_sl2 {X : Type} [Group X] [Finite X] {J H : Subgroup X} (hle : J ≤ H)
    (hn : (J.subgroupOf H).Normal) (e : ↥J ≃* SL(2, F)) (hodd : Odd (Nat.card F))
    (h4 : 4 ≤ Nat.card F) : IsPCompIn 2 H J := by
  refine ⟨hle, ?_⟩
  have e' : ↥(J.subgroupOf H) ≃* SL(2, F) := (Subgroup.subgroupOfEquivOfLe hle).trans e
  exact isPComponent_of_inf_pPrimeCore hn (isQuasisimple_of_equiv_sl2 h4 e')
    (inf_pPrimeCore_eq_one (isQuasisimple_of_equiv_sl2 h4 e') (natCard_center_of_equiv_sl2 hodd e'))

end SL2

section Split3

variable {X : Type}  [Group X]

structure IsSplit3 (F : Type) [Field F] [Finite F] (u : X) (J H : Subgroup X) : Prop where
  ord : orderOf u = 2
  le_H : J ≤ H
  comm : ∀ a ∈ H, ∀ b ∈ H, ⁅a, b⁆ ∈ J
  equiv : Nonempty (↥J ≃* SL(2, F))
  odd : Odd (Nat.card F)
  big : 4 ≤ Nat.card F

namespace IsSplit3

variable {F : Type} [Field F] [Finite F] {u : X} {J H : Subgroup X}

theorem quasisimple (h : IsSplit3 F u J H) : IsQuasisimple ↥J := by
  obtain ⟨e⟩ := h.equiv
  exact isQuasisimple_of_equiv_sl2 h.big e

theorem perfect (h : IsSplit3 F u J H) : ⁅J, J⁆ = J := Subgroup.isPerfect_iff.1 h.quasisimple.1

theorem card (h : IsSplit3 F u J H) : Nat.card ↥J = Nat.card SL(2, F) := by
  obtain ⟨e⟩ := h.equiv
  exact Nat.card_congr e.toEquiv

theorem normal (h : IsSplit3 F u J H) : (J.subgroupOf H).Normal := by
  refine (Subgroup.normal_subgroupOf_iff h.le_H).2 fun a b ha hb => ?_
  have e : b * a * b⁻¹ = ⁅b, a⁆ * a := by rw [commutatorElement_def]; group
  rw [e]
  exact J.mul_mem (h.comm b hb a (h.le_H ha)) ha

theorem le_of_perfect' (h : IsSplit3 F u J H) {P : Subgroup X} (hPH : P ≤ H) (hP : ⁅P, P⁆ = P) :
    P ≤ J := by
  rw [← hP, Subgroup.commutator_le]
  intro g₁ hg₁ g₂ hg₂
  exact h.comm g₁ (hPH hg₁) g₂ (hPH hg₂)

variable [Finite X]

theorem isPCompIn (h : IsSplit3 F u J H) : IsPCompIn 2 H J := by
  obtain ⟨e⟩ := h.equiv
  exact isPCompIn_of_normal_sl2 h.le_H h.normal e h.odd h.big

theorem isPCompIn_self (h : IsSplit3 F u J H) : IsPCompIn 2 J J := by
  obtain ⟨e⟩ := h.equiv
  refine isPCompIn_of_normal_sl2 le_rfl ?_ e h.odd h.big
  rw [Subgroup.subgroupOf_self]
  infer_instance

theorem card_le_of_isPCompIn (h : IsSplit3 F u J H) {L' : Subgroup X} (hL' : IsPCompIn 2 H L') :
    Nat.card ↥L' ≤ Nat.card ↥J := by
  have hperf : Group.IsPerfect ↥(L'.subgroupOf H) :=
    CFSG.ComponentClassification.CatalogueBAlternating.pComponent_perfect hL'.2
  have h1 : L'.subgroupOf H ≤ J.subgroupOf H := by
    have h2 : ⁅L'.subgroupOf H, L'.subgroupOf H⁆ ≤ J.subgroupOf H := by
      rw [Subgroup.commutator_le]
      intro g₁ _ g₂ _
      rw [Subgroup.mem_subgroupOf]
      exact h.comm g₁ g₁.2 g₂ g₂.2
    have := hperf
    rwa [Subgroup.commutator_eq_self] at h2
  have h2 : L' ≤ J := fun g hg =>
    Subgroup.mem_subgroupOf.1
      (h1 (Subgroup.mem_subgroupOf.2 hg : (⟨g, hL'.1 hg⟩ : ↥H) ∈ L'.subgroupOf H))
  exact Subgroup.card_le_of_le h2

theorem pLayerOf_ne_bot (h : IsSplit3 F u J H) : pLayerOf 2 H ≠ ⊥ := by
  intro hbot
  have h1 : J ≤ pLayerOf 2 H := le_sSup h.isPCompIn
  rw [hbot, le_bot_iff] at h1
  have h2 : Nat.card ↥J = 1 := by rw [h1]; exact Subgroup.card_bot
  rw [h.card] at h2
  have h3 : Nat.card ↥(center SL(2, F)) = 2 := sl2_natCard_center h.odd
  have h4 := Subgroup.card_le_card_group (center SL(2, F))
  omega

end IsSplit3

end Split3

section Split3Like

variable {X : Type} [Group X]

structure Split3Like (F : Type) [Field F] [Finite F] (Y : Subgroup X) : Prop where
  odd : Odd (Nat.card F)
  big : 4 ≤ Nat.card F
  center : ∀ z ∈ Y, (∀ g ∈ Y, g * z = z * g) → z = 1
  split : ∀ u ∈ Y, orderOf u = 2 →
    ∃ J : Subgroup X, J ≤ Y ∧ IsSplit3 F u J (centralizer ({u} : Set X) ⊓ Y)

variable [Finite X] {F : Type} [Field F] [Finite F] {Y : Subgroup X} (hY : Split3Like F Y)
include hY

theorem Split3Like.isPCompIn_of_le_centralizer {u d : X} {L : Subgroup X} (hdY : d ∈ Y)
    (hd2 : orderOf d = 2) (hLY : L ≤ Y) (hL : IsSplit3 F u L (centralizer ({u} : Set X) ⊓ Y))
    (hLd : L ≤ centralizer ({d} : Set X)) :
    IsPCompIn 2 (centralizer ({d} : Set X) ⊓ Y) L := by
  obtain ⟨Ld, hLdY, hsp⟩ := hY.split d hdY hd2
  have hle : L ≤ Ld := hsp.le_of_perfect' (le_inf hLd hLY) hL.perfect
  have heq : L = Ld := Subgroup.eq_of_le_of_card_ge hle (by rw [hL.card, hsp.card])
  rw [heq]
  exact hsp.isPCompIn

theorem Split3Like.subtermRel {u : X} {L : Subgroup X} (hu : u ∈ Y) (hLY : L ≤ Y)
    (hL : IsSplit3 F u L (centralizer ({u} : Set X) ⊓ Y)) : SubtermRel Y u L := by
  refine ⟨hL.ord, Subgroup.le_normalizer hu, Or.inl ⟨hL.isPCompIn, ?_⟩⟩
  intro z hz hz2
  have hYu : Y ⊔ zpowers u = Y := sup_eq_left.2 (Subgroup.zpowers_le.2 hu)
  rw [hYu] at hz
  have hcomm : ∀ a ∈ centralizer (L : Set X) ⊓ Y, ∀ b ∈ centralizer (Y : Set X), a * b = b * a :=
    fun a ha b hb => Subgroup.mem_centralizer_iff.1 hb a ha.2
  obtain ⟨d, hd, w, hw, rfl⟩ := mem_sup_of_commute hcomm hz
  have hdY : d ∈ Y := hd.2
  have hdw : Commute d w := hcomm d hd w hw
  have hwY : ∀ g ∈ Y, Commute g w := fun g hg => Subgroup.mem_centralizer_iff.1 hw g hg
  have hd2sq : d ^ 2 = 1 := by
    have h1 : (d * w) ^ 2 = 1 := by rw [← hz2]; exact pow_orderOf_eq_one _
    rw [hdw.mul_pow] at h1
    have h3 : d ^ 2 = (w ^ 2)⁻¹ := eq_inv_of_mul_eq_one_left h1
    apply hY.center (d ^ 2) (Subgroup.pow_mem Y hdY 2)
    intro g hg
    rw [h3]
    exact ((hwY g hg).pow_right 2).inv_right.eq
  by_cases hd1 : d = 1
  · right
    rw [hd1, one_mul]
    exact hw
  · left
    have hd2 : orderOf d = 2 := orderOf_eq_prime hd2sq hd1
    have hLd : L ≤ centralizer ({d} : Set X) := fun l hl =>
      Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hd.1 l hl)
    have hcent : centralizer ({d * w} : Set X) ⊓ Y = centralizer ({d} : Set X) ⊓ Y := by
      ext g
      simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
      constructor
      · rintro ⟨h1, hg⟩
        refine ⟨?_, hg⟩
        have h2 : g * d * w = d * g * w := by
          calc g * d * w = g * (d * w) := by rw [mul_assoc]
            _ = d * w * g := h1
            _ = d * (w * g) := by rw [mul_assoc]
            _ = d * (g * w) := by rw [(hwY g hg).eq]
            _ = d * g * w := by rw [mul_assoc]
        exact mul_right_cancel h2
      · rintro ⟨h1, hg⟩
        refine ⟨?_, hg⟩
        calc g * (d * w) = g * d * w := by rw [mul_assoc]
          _ = d * g * w := by rw [h1]
          _ = d * (g * w) := by rw [mul_assoc]
          _ = d * (w * g) := by rw [(hwY g hg).eq]
          _ = d * w * g := by rw [mul_assoc]
    rw [hcent]
    exact hY.isPCompIn_of_le_centralizer hdY hd2 hLY hL hLd

theorem Split3Like.exists_pair {u : X} (hu : u ∈ Y) (hu2 : orderOf u = 2) :
    ∃ L : Subgroup X, L ≤ Y ∧ IsSplit3 F u L (centralizer ({u} : Set X) ⊓ Y) ∧ SubtermRel Y u L := by
  obtain ⟨L, hLY, hL⟩ := hY.split u hu hu2
  exact ⟨L, hLY, hL, hY.subtermRel hu hLY hL⟩

end Split3Like

section Models

structure GrpS3 (F : Type) [Field F] [Finite F] (P : Type) [Group P] : Prop where
  odd : Odd (Nat.card F)
  big : 4 ≤ Nat.card F
  split : ∀ u : P, orderOf u = 2 → ∃ J : Subgroup P, J ≤ centralizer ({u} : Set P) ∧
    (∀ a b : P, a * u = u * a → b * u = u * b → ⁅a, b⁆ ∈ J) ∧ Nonempty (↥J ≃* SL(2, F))

theorem GrpS3.of_single {F : Type} [Field F] [Finite F] {P : Type} [Group P] (hodd : Odd (Nat.card F))
    (hbig : 4 ≤ Nat.card F)
    (hsingle : ∀ a b : P, a * a = 1 → a ≠ 1 → b * b = 1 → b ≠ 1 → ∃ g : P, g * a * g⁻¹ = b)
    {u₀ : P} (hu₀ : orderOf u₀ = 2) {J₀ : Subgroup P} (hJ₀ : J₀ ≤ centralizer ({u₀} : Set P))
    (hcomm : ∀ a b : P, a * u₀ = u₀ * a → b * u₀ = u₀ * b → ⁅a, b⁆ ∈ J₀)
    (e₀ : Nonempty (↥J₀ ≃* SL(2, F))) : GrpS3 F P := by
  refine ⟨hodd, hbig, fun u hu => ?_⟩
  have hsq : ∀ v : P, orderOf v = 2 → v * v = 1 ∧ v ≠ 1 := fun v hv =>
    ⟨by rw [← pow_two]; exact hv ▸ pow_orderOf_eq_one v, fun h => by simp [h] at hv⟩
  obtain ⟨g, hg⟩ := hsingle u₀ u (hsq u₀ hu₀).1 (hsq u₀ hu₀).2 (hsq u hu).1 (hsq u hu).2
  subst hg
  refine ⟨J₀.map (MulAut.conj g).toMonoidHom, ?_, ?_, ?_⟩
  · rintro _ ⟨j, hj, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hj' : j * u₀ = u₀ * j := Subgroup.mem_centralizer_singleton_iff.1 (hJ₀ hj)
    calc (MulAut.conj g).toMonoidHom j * (g * u₀ * g⁻¹) = g * (j * u₀) * g⁻¹ := by
          simp [MulAut.conj_apply, mul_assoc]
      _ = g * (u₀ * j) * g⁻¹ := by rw [hj']
      _ = (g * u₀ * g⁻¹) * (MulAut.conj g).toMonoidHom j := by simp [MulAut.conj_apply, mul_assoc]
  · intro a b ha hb
    have key : ∀ c : P, c * (g * u₀ * g⁻¹) = (g * u₀ * g⁻¹) * c → g⁻¹ * c * g * u₀ = u₀ * (g⁻¹ * c * g) := by
      intro c hc
      calc g⁻¹ * c * g * u₀ = g⁻¹ * (c * (g * u₀ * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * u₀ * g⁻¹) * c) * g := by rw [hc]
        _ = u₀ * (g⁻¹ * c * g) := by group
    have h := hcomm _ _ (key a ha) (key b hb)
    refine ⟨⁅g⁻¹ * a * g, g⁻¹ * b * g⁆, h, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_commutatorElement]
    simp [mul_assoc]
  · obtain ⟨e⟩ := e₀
    exact ⟨(Subgroup.equivMapOfInjective J₀ (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).symm.trans e⟩

variable {X : Type} [Group X]

theorem Split3Like.of_equiv {F : Type} [Field F] [Finite F] {Y : Subgroup X} {P : Type} [Group P]
    (e : ↥Y ≃* P) (hP : GrpS3 F P) (hZ : ∀ z ∈ Y, (∀ g ∈ Y, g * z = z * g) → z = 1) :
    Split3Like F Y := by
  refine ⟨hP.odd, hP.big, hZ, fun u hu hu2 => ?_⟩
  set u₀ : ↥Y := ⟨u, hu⟩ with hu₀
  have hu₀2 : orderOf (e u₀) = 2 := by
    rw [MulEquiv.orderOf_eq, hu₀, Subgroup.orderOf_mk]; exact hu2
  obtain ⟨J', hJ'c, hJ'comm, ⟨eJ⟩⟩ := hP.split (e u₀) hu₀2
  set J'' : Subgroup ↥Y := J'.map e.symm.toMonoidHom with hJ''
  set J : Subgroup X := J''.map Y.subtype with hJ
  have hJY : J ≤ Y := Subgroup.map_subtype_le _
  have hJmem : ∀ l ∈ J, ∃ l' ∈ J', ((e.symm l' : ↥Y) : X) = l := by
    rintro _ ⟨a, ⟨l', hl', rfl⟩, rfl⟩
    exact ⟨l', hl', rfl⟩
  have hJc : J ≤ centralizer ({u} : Set X) := by
    intro l hl
    obtain ⟨l', hl', rfl⟩ := hJmem l hl
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 (hJ'c hl')
    have h2 := congrArg e.symm h1
    rw [map_mul, map_mul, MulEquiv.symm_apply_apply] at h2
    exact congrArg Subtype.val h2
  refine ⟨J, hJY, hu2, le_inf hJc hJY, ?_, ⟨?_⟩, hP.odd, hP.big⟩
  · intro a ha b hb
    have haY : a ∈ Y := ha.2
    have hbY : b ∈ Y := hb.2
    have ha₀ : (⟨a, haY⟩ : ↥Y) * u₀ = u₀ * ⟨a, haY⟩ :=
      Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 ha.1)
    have hb₀ : (⟨b, hbY⟩ : ↥Y) * u₀ = u₀ * ⟨b, hbY⟩ :=
      Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 hb.1)
    have hc := hJ'comm (e ⟨a, haY⟩) (e ⟨b, hbY⟩) (by rw [← map_mul, ← map_mul, ha₀])
      (by rw [← map_mul, ← map_mul, hb₀])
    refine ⟨(e.symm ⁅e ⟨a, haY⟩, e ⟨b, hbY⟩⁆ : ↥Y), ⟨⁅e ⟨a, haY⟩, e ⟨b, hbY⟩⁆, hc, rfl⟩, ?_⟩
    simp [map_commutatorElement]
  · exact (Subgroup.equivMapOfInjective J'' Y.subtype Y.subtype_injective).symm.trans
      ((e.symm.subgroupMap J').symm.trans eJ)

end Models

section Centerless

theorem center_trivial_of_simple_of_quasisimple {S : Type*} [Group S] (hs : IsSimpleGroup S)
    (hq : IsQuasisimple S) : ∀ z : S, (∀ g : S, g * z = z * g) → z = 1 := by
  obtain ⟨-, -, a', b', hab'⟩ := hq
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a'
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b'
  have hnab : a * b ≠ b * a := fun h' =>
    hab' (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h'])
  intro z hz
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center S) with hb | ht
  · have : z ∈ center S := Subgroup.mem_center_iff.2 hz
    rwa [hb, Subgroup.mem_bot] at this
  · exfalso
    apply hnab
    have : a ∈ center S := by rw [ht]; exact Subgroup.mem_top a
    exact (Subgroup.mem_center_iff.1 this b).symm

theorem exists_four_of_quasisimple_centerless {S : Type*} [Group S] [Finite S] (hq : IsQuasisimple S)
    (hZ : ∀ z : S, (∀ g : S, g * z = z * g) → z = 1) :
    ∃ V : Subgroup S, CFSG.IsElementaryAbelian 2 V ∧ Nat.card V = 4 := by
  have hc : center S = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    exact hZ z fun g => Subgroup.mem_center_iff.1 hz g
  obtain ⟨V, hV, h4⟩ := CFSG.LocalAnalysis.ComponentInitial.exists_four_group_of_two_le_pRank
    (CFSG.LocalAnalysis.ComponentInitial.two_le_pRank_of_isQuasisimple_of_odd_center hq
      (by rw [hc, Subgroup.card_bot]; exact odd_one))
  exact ⟨V, (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 V).2 hV, h4⟩

end Centerless

end CFSG.GH74.Generic.BProg.B1.PilotS3
