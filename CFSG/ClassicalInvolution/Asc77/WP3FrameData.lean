module

public import CFSG.ClassicalInvolution.Asc77.WP3FrameStmt
public import CFSG.ClassicalInvolution.Asc77.AscT3Sym
public import CFSG.ClassicalInvolution.Asc77.AscL62Main
public import CFSG.ClassicalInvolution.Asc77.AscSix63
public import CFSG.ClassicalInvolution.Asc77.WP3LayerSec
import CFSG.ClassicalInvolution.Asc77.AscT7AHyp51Eng

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement

namespace ChainFrame

section Group

variable {G : Type} [Group G]

theorem commutes_closure {s : Set G} (h : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a) :
    ∀ x ∈ Subgroup.closure s, ∀ y ∈ Subgroup.closure s, x * y = y * x := by
  exact CFSG.ClassicalInvolution.Asc77.T7AHyp51Eng.commutes_closure_gen h

theorem sq_closure {s : Set G} (hs : ∀ a ∈ s, a * a = 1)
    (h : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a) : ∀ x ∈ Subgroup.closure s, x * x = 1 := by
  exact CFSG.ClassicalInvolution.Asc77.T7AHyp51Eng.sq_closure_gen hs h

theorem le_normalizer_of_commutes {A B : Subgroup G} (h : Commutes A B) :
    B ≤ Subgroup.normalizer (A : Set G) := by
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have : y * x * y⁻¹ = x := by
      have := h x hx y hy
      calc y * x * y⁻¹ = (x * y) * y⁻¹ := by rw [this]
        _ = x := by group
    rw [this]
    exact hx
  · intro hx
    have h2 := h _ hx y⁻¹ (B.inv_mem hy)
    have : x = y * x * y⁻¹ := by
      calc x = y⁻¹ * (y * x * y⁻¹) * y := by group
        _ = (y * x * y⁻¹) * y⁻¹ * y := by rw [← h2]
        _ = y * x * y⁻¹ := by group
    rw [this]
    exact hx

theorem card_sup_mul_card_inf' {A C : Subgroup G} (hC : C ≤ Subgroup.normalizer (A : Set G)) :
    Nat.card (C ⊔ A : Subgroup G) * Nat.card (A ⊓ C : Subgroup G) =
      Nat.card A * Nat.card C := by
  let := Subgroup.normal_subgroupOf_of_le_normalizer hC
  let := Subgroup.normal_subgroupOf_sup_of_le_normalizer hC
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient C A hC
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (A.subgroupOf C)
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (A.subgroupOf (C ⊔ A))
  have h3 : Nat.card (A.subgroupOf (C ⊔ A)) = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  have h4 : Nat.card (A.subgroupOf C) = Nat.card (A ⊓ C : Subgroup G) := by
    rw [← Subgroup.inf_subgroupOf_right]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  rw [h2, h3, h1, h4, Nat.card_congr e.toEquiv]
  ring

theorem eq_one_or_eq_of_mem_zpowers {a x : G} (ha : orderOf a = 2) (hx : x ∈ Subgroup.zpowers a) :
    x = 1 ∨ x = a := by
  exact CFSG.ClassicalInvolution.Asc77.T7AHyp51Eng.eq_one_or_eq_of_mem_zpowers_gen ha hx

section Triple

theorem mem_closure_four {a b : G} (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) {x : G}
    (hx : x ∈ Subgroup.closure ({a, b} : Set G)) : x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
  have c : b * a = a * b := hab.symm
  have s1' : ∀ y, a * (a * y) = y := fun y => by rw [← mul_assoc, ha, one_mul]
  have c' : ∀ y, b * (a * y) = a * (b * y) := fun y => by rw [← mul_assoc, c, mul_assoc]
  have i1 : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have i2 : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  refine Subgroup.closure_induction
    (p := fun x _ => x = 1 ∨ x = a ∨ x = b ∨ x = a * b) ?_ ?_ ?_ ?_ hx
  · intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with hy | hy <;> subst hy <;> simp
  · simp
  · rintro u v - - (hu | hu | hu | hu) (hv | hv | hv | hv) <;> subst hu <;> subst hv <;>
      simp [mul_assoc, ha, hb, s1', c, c']
  · rintro u - (hu | hu | hu | hu) <;> subst hu <;> simp [mul_inv_rev, i1, i2, c]

theorem mem_closure_eight {a b c : G} (ha : a * a = 1) (hb : b * b = 1) (hc : c * c = 1)
    (hab : a * b = b * a) (hac : a * c = c * a) (hbc : b * c = c * b) {x : G}
    (hx : x ∈ Subgroup.closure ({a, b, c} : Set G)) :
    x = 1 ∨ x = a ∨ x = b ∨ x = c ∨ x = a * b ∨ x = a * c ∨ x = b * c ∨ x = a * (b * c) := by
  have c12 : b * a = a * b := hab.symm
  have c13 : c * a = a * c := hac.symm
  have c23 : c * b = b * c := hbc.symm
  have s1' : ∀ y, a * (a * y) = y := fun y => by rw [← mul_assoc, ha, one_mul]
  have s2' : ∀ y, b * (b * y) = y := fun y => by rw [← mul_assoc, hb, one_mul]
  have c12' : ∀ y, b * (a * y) = a * (b * y) := fun y => by rw [← mul_assoc, c12, mul_assoc]
  have c13' : ∀ y, c * (a * y) = a * (c * y) := fun y => by rw [← mul_assoc, c13, mul_assoc]
  have c23' : ∀ y, c * (b * y) = b * (c * y) := fun y => by rw [← mul_assoc, c23, mul_assoc]
  have i1 : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have i2 : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have i3 : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc
  refine Subgroup.closure_induction
    (p := fun x _ => x = 1 ∨ x = a ∨ x = b ∨ x = c ∨ x = a * b ∨ x = a * c ∨
      x = b * c ∨ x = a * (b * c)) ?_ ?_ ?_ ?_ hx
  · intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with hy | hy | hy <;> subst hy <;> simp
  · simp
  · rintro u v - - (hu | hu | hu | hu | hu | hu | hu | hu)
      (hv | hv | hv | hv | hv | hv | hv | hv) <;> subst hu <;> subst hv <;>
      simp [mul_assoc, ha, hb, hc, s1', s2', c12, c13, c23, c12', c13', c23']
  · rintro u - (hu | hu | hu | hu | hu | hu | hu | hu) <;> subst hu <;>
      simp [mul_assoc, mul_inv_rev, i1, i2, i3, c12, c13, c23, c12']

theorem two_mul_card_le_of_lt [Finite G] {A B : Subgroup G} (h : A < B) :
    2 * Nat.card A ≤ Nat.card B := by
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le h.le
  have hA : 0 < Nat.card A := Nat.card_pos
  have hB : 0 < Nat.card B := Nat.card_pos
  have hk1 : k ≠ 1 := by
    rintro rfl
    exact h.ne (Subgroup.eq_of_le_of_card_ge h.le (by omega))
  have hk0 : k ≠ 0 := by
    rintro rfl
    omega
  have hk2 : 2 ≤ k := by omega
  nlinarith

theorem card_closure_triple_eq_eight [Finite G] {a b c : G} (ha : a * a = 1) (hb : b * b = 1)
    (hc : c * c = 1) (hab : a * b = b * a) (hac : a * c = c * a) (hbc : b * c = c * b)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hba : b ≠ a) (hc1 : c ≠ 1) (hca : c ≠ a) (hcb : c ≠ b)
    (hcab : c ≠ a * b) : Nat.card (Subgroup.closure ({a, b, c} : Set G)) = 8 := by
  classical
  apply le_antisymm
  · have hsub : (Subgroup.closure ({a, b, c} : Set G) : Set G) ⊆ ({1, a, b, c, a * b, a * c,
        b * c, a * (b * c)} : Finset G) := by
      intro x hx
      simpa only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] using mem_closure_eight ha hb hc hab hac hbc hx
    calc Nat.card (Subgroup.closure ({a, b, c} : Set G))
        = Nat.card ((Subgroup.closure ({a, b, c} : Set G) : Set G)) := rfl
      _ ≤ Nat.card (({1, a, b, c, a * b, a * c, b * c, a * (b * c)} : Finset G) : Set G) :=
        Nat.card_mono (Set.toFinite _) hsub
      _ = Finset.card ({1, a, b, c, a * b, a * c, b * c, a * (b * c)} : Finset G) :=
        Nat.card_eq_finsetCard _
      _ ≤ 8 := by
        refine (Finset.card_insert_le _ _).trans ?_
        refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
        refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
        refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
        refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
        refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
        refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
        simp
  · set A₁ : Subgroup G := Subgroup.closure ({a} : Set G) with hA₁
    set A₂ : Subgroup G := Subgroup.closure ({a, b} : Set G) with hA₂
    have key1 : ∀ g ∈ A₁, g = 1 ∨ g = a := by
      intro g hg
      refine Subgroup.closure_induction (p := fun g _ => g = 1 ∨ g = a) ?_ ?_ ?_ ?_ hg
      · intro u hu
        right
        simpa using hu
      · left
        rfl
      · rintro u v - - (hu | hu) (hv | hv) <;> subst hu <;> subst hv
        · left; simp
        · right; simp
        · right; simp
        · left; exact ha
      · rintro u - (hu | hu) <;> subst hu
        · left; simp
        · right; exact inv_eq_of_mul_eq_one_right ha
    have h1 : (⊥ : Subgroup G) < A₁ := by
      refine lt_of_le_of_ne bot_le fun hh => ha1 ?_
      have : a ∈ A₁ := Subgroup.subset_closure rfl
      rwa [← hh, Subgroup.mem_bot] at this
    have h2 : A₁ < A₂ := by
      refine lt_of_le_of_ne (Subgroup.closure_mono (by simp)) fun hh => ?_
      have hb' : b ∈ A₂ := Subgroup.subset_closure (by simp)
      rw [← hh] at hb'
      rcases key1 b hb' with h | h
      · exact hb1 h
      · exact hba h
    have h3 : A₂ < Subgroup.closure ({a, b, c} : Set G) := by
      refine lt_of_le_of_ne (Subgroup.closure_mono (by intro x hx; simp at hx ⊢; tauto))
        fun hh => ?_
      have hc' : c ∈ A₂ := by
        rw [hh]
        exact Subgroup.subset_closure (by simp)
      rcases mem_closure_four ha hb hab hc' with h | h | h | h
      · exact hc1 h
      · exact hca h
      · exact hcb h
      · exact hcab h
    have c1 := two_mul_card_le_of_lt h1
    have c2 := two_mul_card_le_of_lt h2
    have c3 := two_mul_card_le_of_lt h3
    have hbot : Nat.card (⊥ : Subgroup G) = 1 := Subgroup.card_bot
    omega

end Triple

end Group

end ChainFrame

section Data

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J K' : Subgroup G} {z t z' : G}

theorem mem_omegaNbr_of_trivialOnQuot (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hK : K ∈ Ω) (hz : IsUniqueInvolution K z) (hJ : J ∈ Ω) (hne : J ≠ K)
    (htq : z ∈ trivialOnQuot J) : J ∈ omegaNbr Ω K := by
  have hz2 : IsPGroup 2 (Subgroup.zpowers z) :=
    ExactLayer.isPGroup_zpowers_of_sq_eq_one hz.sq
  have hmem : J ∈ ExactLayer.tqMembers Ω z := ExactLayer.mem_tqMembers_iff.mpr ⟨hJ, htq⟩
  obtain ⟨-, R, hR, hRc⟩ := (ExactLayer.mem_tqMembers_iff_exists_sylow hp hq hΩ hz2).mp hmem
  have hRset : R ∈ RSet Ω := mem_RSet_of_isSylow2In hJ hR
  have h8 := hΩ.eight_le_of_mem_RSet hp hRset
  exact ⟨hJ, hne, R, hRset, hR.1,
    hΩ.le_normalizer_of_le_centralizer hp hq hK hJ hne.symm hz hR.1 hR.2.1 (by omega) hRc⟩

theorem trivialOnQuot_of_mem_of_commute {K : Subgroup G} {z : G} (hz : z ∈ K)
    (hc : ∀ x ∈ K, z * x = x * z) : z ∈ trivialOnQuot K := by
  refine ⟨Subgroup.le_normalizer hz, fun x hx => ?_⟩
  have : ⁅z, x⁆ = 1 := by
    rw [commutatorElement_def]
    calc z * x * z⁻¹ * x⁻¹ = (x * z) * z⁻¹ * x⁻¹ := by rw [hc x hx]
      _ = 1 := by group
  rw [this]
  exact one_mem _

theorem trivialOnQuot_of_isUniqueInvolution (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) (hK : K ∈ Ω) (hz : IsUniqueInvolution K z) :
    z ∈ trivialOnQuot K := by
  obtain ⟨z₀, hz₀⟩ := hΩ.classical K hK
  have hzz : z₀ = z := hz.eq (ConnectedA2.isUniqueInvolution_of_isClassicalMember hp hq hz₀) |>.symm
  subst hzz
  refine trivialOnQuot_of_mem_of_commute hz₀.mem fun x hx => ?_
  exact Subgroup.mem_centralizer_iff.mp (isSubnormal_le hz₀.subnormal hx) z₀
    (Set.mem_singleton z₀)

namespace ChainFrameData

omit [Fact p.Prime] [Finite G] in
theorem memJ (h : ChainFrameData Ω K J K' z t z') : J ∈ Ω := h.hJ.1

omit [Fact p.Prime] [Finite G] in
theorem memK' (h : ChainFrameData Ω K J K' z t z') : K' ∈ Ω := h.hK'.1

theorem tq_z_J (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (h : ChainFrameData Ω K J K' z t z') : z ∈ trivialOnQuot J := by
  obtain ⟨a, ha, hJa⟩ := tq_of_mem_omegaNbr hp hq hΩ.classical h.mem h.hJ
  have haz : a = z :=
    (ConnectedA2.isUniqueInvolution_of_isClassicalMember hp hq ha).eq h.hz
  exact (mem_trivialOnQuot_iff_actsTrivOnQuot (J := J)).mpr (haz ▸ hJa)

theorem tq_z_K' (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (h : ChainFrameData Ω K J K' z t z') : z ∈ trivialOnQuot K' := by
  obtain ⟨a, ha, hKa⟩ := tq_of_mem_omegaNbr hp hq hΩ.classical h.mem h.hK'
  have haz : a = z :=
    (ConnectedA2.isUniqueInvolution_of_isClassicalMember hp hq ha).eq h.hz
  exact (mem_trivialOnQuot_iff_actsTrivOnQuot (J := K')).mpr (haz ▸ hKa)

theorem tq_t (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (h : ChainFrameData Ω K J K' z t z') : t ∈ trivialOnQuot K := by
  have hKJ : K ∈ omegaNbr Ω J :=
    T3.omegaNbr_symm (l6_2 p f) hp hq hΩ h.mem h.memJ h.hJ
  obtain ⟨a, ha, hKa⟩ := tq_of_mem_omegaNbr hp hq hΩ.classical h.memJ hKJ
  have hat : a = t :=
    (ConnectedA2.isUniqueInvolution_of_isClassicalMember hp hq ha).eq h.ht
  exact (mem_trivialOnQuot_iff_actsTrivOnQuot (J := K)).mpr (hat ▸ hKa)

theorem tq_z' (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (h : ChainFrameData Ω K J K' z t z') : z' ∈ trivialOnQuot K := by
  have hKK' : K ∈ omegaNbr Ω K' :=
    T3.omegaNbr_symm (l6_2 p f) hp hq hΩ h.mem h.memK' h.hK'
  obtain ⟨a, ha, hKa⟩ := tq_of_mem_omegaNbr hp hq hΩ.classical h.memK' hKK'
  have haz : a = z' :=
    (ConnectedA2.isUniqueInvolution_of_isClassicalMember hp hq ha).eq h.hz'
  exact (mem_trivialOnQuot_iff_actsTrivOnQuot (J := K)).mpr (haz ▸ hKa)

theorem comm_zt (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω) (h : ChainFrameData Ω K J K' z t z') :
    z * t = t * z := by
  obtain ⟨-, -, R, hR, hRJ, hRN⟩ := h.hJ
  have hRsyl : IsSylow2In R J := T3.isSylow2In_of_mem_RSet_of_le hp hΩ h.memJ hR hRJ
  have h8 := hΩ.eight_le_of_mem_RSet hp hR
  have htR : t ∈ R := mem_of_isUniqueInvolution_of_isPGroup h.ht hRsyl.1 hRsyl.2.1 (by omega)
  exact (Subgroup.mem_centralizer_singleton_iff.mp
    (le_centralizer_of_le_normalizer h.hz hRN htR)).symm

theorem comm_zz' (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω) (h : ChainFrameData Ω K J K' z t z') :
    z * z' = z' * z := by
  obtain ⟨-, -, R, hR, hRK', hRN⟩ := h.hK'
  have hRsyl : IsSylow2In R K' := T3.isSylow2In_of_mem_RSet_of_le hp hΩ h.memK' hR hRK'
  have h8 := hΩ.eight_le_of_mem_RSet hp hR
  have hz'R : z' ∈ R :=
    mem_of_isUniqueInvolution_of_isPGroup h.hz' hRsyl.1 hRsyl.2.1 (by omega)
  exact (Subgroup.mem_centralizer_singleton_iff.mp
    (le_centralizer_of_le_normalizer h.hz hRN hz'R)).symm

theorem t_ne_z (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (h : ChainFrameData Ω K J K' z t z') : t ≠ z := by
  intro htz
  have hJz : IsUniqueInvolution J z := htz ▸ h.ht
  exact h.hperp (omegaNbr_subset_kPerp_of_twin hp hq hΩ h.memJ h.hz hJz h.hK')

theorem z'_ne_z (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (h : ChainFrameData Ω K J K' z t z') : z' ≠ z := by
  intro hz'z
  have hzK' : IsUniqueInvolution K' z := hz'z ▸ h.hz'
  have hJ : J ∈ KPerp Ω K' := omegaNbr_subset_kPerp_of_twin hp hq hΩ h.memK' h.hz hzK' h.hJ
  rcases hJ with hJK' | hJK'
  · exact h.hperp (by rw [hJK']; exact Set.mem_insert _ _)
  · have := T3.omegaNbr_symm (l6_2 p f) hp hq hΩ h.memK' h.memJ hJK'
    exact h.hperp (Set.mem_insert_of_mem _ this)

theorem z'_ne_t (hΩ : HypOmegaMod p f Ω) (h : ChainFrameData Ω K J K' z t z') : z' ≠ t := by
  intro hz't
  have hzK' : IsUniqueInvolution K' t := hz't ▸ h.hz'
  exact h.hperp (mem_kPerp_of_twin hΩ h.memK' h.memJ hzK' h.ht)

theorem z'_ne_zt (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (h : ChainFrameData Ω K J K' z t z') : z' ≠ z * t := by
  intro hz'
  have hJK' : J ≠ K' := fun e => h.hperp (by rw [e]; exact Set.mem_insert _ _)
  have htJ : t ∈ trivialOnQuot J := trivialOnQuot_of_isUniqueInvolution hp hq hΩ h.memJ h.ht
  have hzt : z * t ∈ trivialOnQuot J := mul_mem (h.tq_z_J hp hq hΩ) htJ
  have hJ' : J ∈ omegaNbr Ω K' :=
    mem_omegaNbr_of_trivialOnQuot hp hq hΩ h.memK' h.hz' h.memJ hJK'
      (by rw [hz']; exact hzt)
  have := T3.omegaNbr_symm (l6_2 p f) hp hq hΩ h.memK' h.memJ hJ'
  exact h.hperp (Set.mem_insert_of_mem _ this)

theorem comm_gen (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω) (h : ChainFrameData Ω K J K' z t z') :
    ∀ a ∈ ({z, t, z'} : Set G), ∀ b ∈ ({z, t, z'} : Set G), a * b = b * a := by
  have hzt := h.comm_zt hp hΩ
  have hzz' := h.comm_zz' hp hΩ
  have htz' := h.htz'
  intro a ha b hb
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
  all_goals first | rfl | assumption | exact (by assumption : _ = _).symm

omit [Finite G] in
theorem sq_gen (h : ChainFrameData Ω K J K' z t z') : ∀ a ∈ ({z, t, z'} : Set G), a * a = 1 := by
  intro a ha
  rcases ha with rfl | rfl | rfl
  · exact h.hz.sq
  · exact h.ht.sq
  · exact h.hz'.sq

theorem isElemAbelian (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω)
    (h : ChainFrameData Ω K J K' z t z') :
    IsElemAbelian 2 (Subgroup.closure ({z, t, z'} : Set G)) := by
  have hcomm := ChainFrame.commutes_closure (h.comm_gen hp hΩ)
  refine ⟨⟨⟨fun a b => Subtype.ext (hcomm _ a.2 _ b.2)⟩⟩, fun x hx => ?_⟩
  rw [pow_two]
  exact ChainFrame.sq_closure h.sq_gen (h.comm_gen hp hΩ) x hx

theorem natCard_eight (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (h : ChainFrameData Ω K J K' z t z') :
    Nat.card (Subgroup.closure ({z, t, z'} : Set G)) = 8 :=
  ChainFrame.card_closure_triple_eq_eight h.hz.sq h.ht.sq h.hz'.sq (h.comm_zt hp hΩ)
    (h.comm_zz' hp hΩ) h.htz' h.hz.ne_one h.ht.ne_one (h.t_ne_z hp hq hΩ) h.hz'.ne_one
    (h.z'_ne_z hp hq hΩ) (h.z'_ne_t hΩ) (h.z'_ne_zt hp hq hΩ)

theorem tq_B (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (h : ChainFrameData Ω K J K' z t z') :
    Subgroup.closure ({z, t, z'} : Set G) ≤ trivialOnQuot K := by
  rw [Subgroup.closure_le]
  intro x hx
  rcases hx with rfl | rfl | rfl
  · exact trivialOnQuot_of_isUniqueInvolution hp hq hΩ h.mem h.hz
  · exact h.tq_t hp hq hΩ
  · exact h.tq_z' hp hq hΩ

end ChainFrameData

end Data

end CFSG.ClassicalInvolution.Asc77
