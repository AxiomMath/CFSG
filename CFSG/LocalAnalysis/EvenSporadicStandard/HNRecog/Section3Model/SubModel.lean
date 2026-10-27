module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Interface
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Model.Unique
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Transport
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.HSide.Map
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.A8Abstract
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.A8Label
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.SubModelClass
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.TableMaps
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ShapeCard
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Vert
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Rows
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.Config
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19Defs

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3Model

open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3 Subgroup

theorem natCard_of_isShapeTwoTwoTimesTwoFourA5 {X : Type*} [Group X]
    (h : IsShapeTwoTwoTimesTwoFourA5 X) : Nat.card X = 3840 := by
  obtain ⟨Y, _, ⟨N, hN, ⟨e⟩, ⟨f⟩⟩, ⟨g⟩⟩ := h
  have hA5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    norm_num [Nat.factorial]
  have hE : ∀ n : ℕ, Nat.card (Elem2 n) = 2 ^ n := fun n => by
    rw [Elem2, Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  have hN16 : Nat.card ↥N = 16 := by
    rw [Nat.card_congr e.toEquiv, hE]
    norm_num
  have hY : Nat.card Y = 960 := by
    rw [← Subgroup.card_mul_index N, hN16, Subgroup.index_eq_card, Nat.card_congr f.toEquiv, hA5]
  rw [Nat.card_congr g.toEquiv, Nat.card_prod, hY, hE]
  norm_num

theorem exists_mulEquiv_derivedOf_Gx {H H' : Type} [Group H] [Group H'] (e : H ≃* H') (c : H) :
    ∃ f : ↥(derivedOf (Gx c)) ≃* ↥(derivedOf (Gx (e c))),
      ∀ x, ((f x : ↥(derivedOf (Gx (e c)))) : H') = e x := by
  have hinj : Function.Injective e.toMonoidHom := e.injective
  have hrange : e.toMonoidHom.range = ⊤ := MonoidHom.range_eq_top.mpr e.surjective
  have h1 : (Gx c).map e.toMonoidHom = Gx (e c) := by
    rw [map_Gx_of_injective hinj, hrange, inf_top_eq]
    rfl
  have h2 : derivedOf (Gx (e c)) = (derivedOf (Gx c)).map e.toMonoidHom := by
    rw [← h1]
    exact derivedOf_map_of_injective hinj (Gx c)
  exact ⟨(Subgroup.equivMapOfInjective (derivedOf (Gx c)) e.toMonoidHom hinj).trans
    (MulEquiv.subgroupCongr h2.symm), fun x => rfl⟩

theorem exists_mulEquiv_derivedOf_Gx' {H H' : Type} [Group H] [Group H'] {e : H ≃* H'} {c : H}
    {c' : H'} (hc : e c = c') :
    ∃ f : ↥(derivedOf (Gx c)) ≃* ↥(derivedOf (Gx c')),
      ∀ x, ((f x : ↥(derivedOf (Gx c'))) : H') = e x := by
  subst hc
  exact exists_mulEquiv_derivedOf_Gx e c

structure IsLabelled {H : Type} [Group H] (Ψ : H ≃* ↥P1408) (a z b z₁ : H) : Prop where
  a_eq : Ψ a = pA
  b_conj : IsConj pB (Ψ b)
  z_conj : IsConj pZ (Ψ z)
  z₁_conj : IsConj pZ₁ (Ψ z₁)

section Cert


theorem conj_pA_eq' (g : ↥P1408) : g * pA * g⁻¹ = pA := by
  have h : g * pA = pA * g := by
    have := Subgroup.mem_center_iff.mp pA_mem_center' g
    exact this
  rw [h, mul_assoc, mul_inv_cancel, mul_one]

theorem IsLabelled.conj {H : Type} [Group H] {Ψ : H ≃* ↥P1408} {a z b z₁ : H}
    (h : IsLabelled Ψ a z b z₁) (g : ↥P1408) :
    IsLabelled (Ψ.trans (MulAut.conj g)) a z b z₁ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [MulEquiv.trans_apply, MulAut.conj_apply, h.a_eq]
    exact conj_pA_eq' g
  · exact h.b_conj.trans (isConj_iff.mpr ⟨g, rfl⟩)
  · exact h.z_conj.trans (isConj_iff.mpr ⟨g, rfl⟩)
  · exact h.z₁_conj.trans (isConj_iff.mpr ⟨g, rfl⟩)

theorem IsLabelled.exists_eq {H : Type} [Group H] {Ψ : H ≃* ↥P1408} {a z b z₁ : H}
    (h : IsLabelled Ψ a z b z₁) {y : H} {r : ↥P1408} (hy : IsConj r (Ψ y)) :
    ∃ Ψ' : H ≃* ↥P1408, IsLabelled Ψ' a z b z₁ ∧ Ψ' y = r := by
  obtain ⟨c, hc⟩ := isConj_iff.mp hy
  refine ⟨Ψ.trans (MulAut.conj c⁻¹), h.conj c⁻¹, ?_⟩
  simp only [MulEquiv.trans_apply, MulAut.conj_apply, ← hc]
  group

theorem exists_labelled_iso {H : Type} [Group H] {E : Subgroup H} (h : TwoHS.IsF5Centralizer H E)
    {a z b z₁ : H} (hf : TwoHSFacts H a z b z₁) :
    ∃ Ψ : H ≃* ↥P1408, Ψ a = pA ∧ Ψ b = pB ∧ IsConj pZ₁ (Ψ z₁) := by
  have hP : Nat.card ↥P1408 = 177408000 := card_P1408 (hsCtx_of_isHSCover h.toIsHSCover)
  obtain ⟨Ψ₀, -⟩ := exists_mulEquiv_p1408_of_isF5Centralizer h
  have hcentre : Nat.card ↥(center ↥P1408) = 2 := by
    rw [← Nat.card_congr (Subgroup.centerCongr Ψ₀).toEquiv, hf.center_eq, Nat.card_zpowers,
      hf.orderOf_a]
  have hΨa_mem : Ψ₀ a ∈ center ↥P1408 := by
    rw [Subgroup.mem_center_iff]
    intro g
    have ha : a ∈ center H := by
      rw [hf.center_eq]
      exact Subgroup.mem_zpowers a
    have h1 := Subgroup.mem_center_iff.mp ha (Ψ₀.symm g)
    calc g * Ψ₀ a = Ψ₀ (Ψ₀.symm g * a) := by rw [map_mul, MulEquiv.apply_symm_apply]
      _ = Ψ₀ (a * Ψ₀.symm g) := by rw [h1]
      _ = Ψ₀ a * g := by rw [map_mul, MulEquiv.apply_symm_apply]
  have hΨa_ne : Ψ₀ a ≠ 1 := by
    intro h1
    have := hf.orderOf_a
    rw [← MulEquiv.orderOf_eq Ψ₀, h1, orderOf_one] at this
    omega
  have hpA_ord : orderOf pA = 2 := (Subgroup.orderOf_coe pA).symm.trans twoHSBasic_spec.1
  have hpA_ne : pA ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hpA_ord
    omega
  have hΨa : Ψ₀ a = pA := by
    obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : ↥(center ↥P1408))).mp hcentre
    have h1 := hy ⟨Ψ₀ a, hΨa_mem⟩ (fun h1 => hΨa_ne (congrArg Subtype.val h1))
    have h2 := hy ⟨pA, pA_mem_center'⟩ (fun h1 => hpA_ne (congrArg Subtype.val h1))
    exact congrArg Subtype.val (h1.trans h2.symm)
  have hΨb : IsConj pB (Ψ₀ b) := by
    refine isConj_pB_of_natCard hP (by rw [MulEquiv.orderOf_eq, hf.orderOf_b]) ?_
    rw [show Nat.card ↥(centralizer ({Ψ₀ b} : Set ↥P1408)) = Nat.card ↥(Gx b) from
      natCard_Gx_map Ψ₀ b]
    exact hf.cent_b.card_eq
  have hΨz₁ : IsConj pZ₁ (Ψ₀ z₁) := by
    refine isConj_pZ₁_of_natCard hP (by rw [MulEquiv.orderOf_eq, hf.orderOf_z₁]) ?_
    rw [show Nat.card ↥(centralizer ({Ψ₀ z₁} : Set ↥P1408)) = Nat.card ↥(Gx z₁) from
      natCard_Gx_map Ψ₀ z₁]
    exact natCard_of_isShapeTwoTwoTimesTwoFourA5 hf.cent_z₁
  obtain ⟨g, hg⟩ := isConj_iff.mp hΨb.symm
  refine ⟨Ψ₀.trans (MulAut.conj g), ?_, ?_, ?_⟩
  · simp only [MulEquiv.trans_apply, MulAut.conj_apply, hΨa]
    rw [← (pA_mem_center'.comm g).eq]
    group
  · simpa using hg
  · simp only [MulEquiv.trans_apply, MulAut.conj_apply]
    exact hΨz₁.trans (isConj_iff.mpr ⟨g, rfl⟩)

theorem isConj_pZ_of_A8Dict {H : Type} [Group H] (hP : Nat.card ↥P1408 = 177408000)
    {Ψ : H ≃* ↥P1408} {z b : H} (hb : Ψ b = pB) (hcb : IsShapeTwoTwoTimesA8 ↥(Gx b))
    (hd : A8Dict z b) : IsConj pZ (Ψ z) := by
  obtain ⟨φ⟩ := nonempty_mulEquiv_A8_derivedOf hcb
  obtain ⟨t, ht⟩ := exists_cycleType_two_four
  have hz : IsConj z (φ t : H) := hd φ t ht
  obtain ⟨f, hfx⟩ := exists_mulEquiv_derivedOf_Gx' hb
  have hord : orderOf t = 2 := by
    have h1 : orderOf (t : Equiv.Perm (Fin 8)) = 2 := by
      rw [← Equiv.Perm.lcm_cycleType, ht]
      decide
    rw [← h1]
    exact (Subgroup.orderOf_coe t).symm
  have ht2 : t * t = 1 := by rw [← pow_two]; exact orderOf_dvd_iff_pow_eq_one.mp hord.dvd
  have ht1 : t ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hord
    omega
  have hu2 : f (φ t) * f (φ t) = 1 := by rw [← map_mul, ← map_mul, ht2, map_one, map_one]
  have hu1 : f (φ t) ≠ 1 := fun h1 => ht1 (φ.injective (f.injective (by rw [h1, map_one, map_one])))
  have hc : Nat.card ↥(Subgroup.centralizer ({f (φ t)} : Set ↥(derivedOf (Gx pB)))) = 192 := by
    rw [show f (φ t) = (φ.trans f) t from rfl, card_centralizer_eq_of_mulEquiv (φ.trans f) t]
    exact card_centralizer_A8_two_four ht
  have h1 := model_A8Label hP (f (φ t)) hu2 hu1 hc
  rw [hfx (φ t)] at h1
  exact h1.trans (TwoHSData.isConj_map_mulEquiv Ψ hz).symm

theorem exists_labelled_iso_dict {H : Type} [Group H] {E : Subgroup H}
    (h : TwoHS.IsF5Centralizer H E) {a z b z₁ : H} (hf : TwoHSFacts H a z b z₁)
    (hd : A8Dict z b) : ∃ Ψ : H ≃* ↥P1408, IsLabelled Ψ a z b z₁ ∧ Ψ b = pB := by
  have hP : Nat.card ↥P1408 = 177408000 := card_P1408 (hsCtx_of_isHSCover h.toIsHSCover)
  obtain ⟨Ψ, ha, hb, hz₁⟩ := exists_labelled_iso h hf
  exact ⟨Ψ, ⟨ha, by rw [hb], isConj_pZ_of_A8Dict hP hb hf.cent_b hd, hz₁⟩, hb⟩

theorem exists_labelled_iso_at_b {H : Type} [Group H] {E : Subgroup H}
    (h : TwoHS.IsF5Centralizer H E) {a z b z₁ : H} (hf : TwoHSFacts H a z b z₁)
    (hd : A8Dict z b) {y : H} (hy : IsConj b y) :
    ∃ Ψ : H ≃* ↥P1408, IsLabelled Ψ a z b z₁ ∧ Ψ y = pB := by
  obtain ⟨Ψ, hΨ, hb⟩ := exists_labelled_iso_dict h hf hd
  refine hΨ.exists_eq ?_
  rw [← hb]
  exact (TwoHSData.isConj_map_mulEquiv Ψ hy).symm.symm

theorem exists_labelled_iso_at_az {H : Type} [Group H] {E : Subgroup H}
    (h : TwoHS.IsF5Centralizer H E) {a z b z₁ : H} (hf : TwoHSFacts H a z b z₁)
    (hd : A8Dict z b) {y : H} (hy : IsConj (a * z) y) :
    ∃ Ψ : H ≃* ↥P1408, IsLabelled Ψ a z b z₁ ∧ Ψ y = pA * pZ := by
  obtain ⟨Ψ, hΨ, -⟩ := exists_labelled_iso_dict h hf hd
  refine hΨ.exists_eq ?_
  have h1 := TwoHSData.isConj_map_mulEquiv Ψ hy
  rw [map_mul, hΨ.a_eq] at h1
  obtain ⟨c, hc⟩ := isConj_iff.mp hΨ.z_conj
  have h2 : IsConj (pA * pZ) (pA * Ψ z) := isConj_iff.mpr ⟨c, by
    rw [show c * (pA * pZ) * c⁻¹ = (c * pA * c⁻¹) * (c * pZ * c⁻¹) by group, conj_pA_eq' c, hc]⟩
  exact h2.trans h1

theorem exists_labelled_iso_at_z {H : Type} [Group H] {E : Subgroup H}
    (h : TwoHS.IsF5Centralizer H E) {a z b z₁ : H} (hf : TwoHSFacts H a z b z₁)
    (hd : A8Dict z b) {y : H} (hy : IsConj z y) :
    ∃ Ψ : H ≃* ↥P1408, IsLabelled Ψ a z b z₁ ∧ Ψ y = pZ := by
  obtain ⟨Ψ, hΨ, -⟩ := exists_labelled_iso_dict h hf hd
  exact hΨ.exists_eq (hΨ.z_conj.trans (TwoHSData.isConj_map_mulEquiv Ψ hy))

end Cert

end CFSG.EvenSporadicStandard.HNRecog.Section3Model
