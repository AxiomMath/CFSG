module

public import CFSG.ClassicalInvolution.Models.Transfer.Linear
public import CFSG.ClassicalInvolution.Q3.Q3PlanOrthChain
public import CFSG.ClassicalInvolution.WeakCT.SimplyLaced
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerGaussUnitary
public import CFSG.ClassicalInvolution.Q3.Q3WLift
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Models.Transfer
  CFSG.ClassicalInvolution.WeakCT
open scoped MatrixGroups commutatorElement

theorem nonempty_ringEquiv_zmod_three {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3) :
    Nonempty (K ≃+* ZMod 3) := by
  have := Fintype.ofFinite K
  exact ⟨FiniteField.ringEquivOfCardEq (by rw [← Nat.card_eq_fintype_card, hK, ZMod.card])⟩

@[expose] noncomputable def slEquiv {K K' : Type} [Field K] [Field K'] (e : K ≃+* K') (m : ℕ) :
    SL(m, K) ≃* SL(m, K') where
  toFun := Matrix.SpecialLinearGroup.map e.toRingHom
  invFun := Matrix.SpecialLinearGroup.map e.symm.toRingHom
  left_inv := map_map_symm e
  right_inv := map_symm_map e
  map_mul' := map_mul _

theorem pow_three_mem_commutator_of_equiv {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3)
    {Y : Type} [Group Y] {L : Subgroup Y} (e : ↥L ≃* SL(2, K)) : ∀ l ∈ L, l ^ 3 ∈ ⁅L, L⁆ := by
  obtain ⟨ε⟩ := nonempty_ringEquiv_zmod_three hK
  let φ : ↥L ≃* SL(2, ZMod 3) := e.trans (slEquiv ε 2)
  intro l hl
  have h1 : (φ ⟨l, hl⟩) ^ 3 ∈
      ⁅(⊤ : Subgroup SL(2, ZMod 3)), (⊤ : Subgroup SL(2, ZMod 3))⁆ :=
    Subgroup.commutator_mono (le_refl _) le_top (sl2ThreeQ8_le_commutator
      (pow_three_mem_sl2ThreeQ8 _))
  have h2 : (⟨l, hl⟩ : ↥L) ^ 3 ∈ ⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ := by
    have h3 : (⟨l, hl⟩ : ↥L) ^ 3 = φ.symm ((φ ⟨l, hl⟩) ^ 3) := by
      rw [map_pow, MulEquiv.symm_apply_apply]
    rw [h3]
    have hsurj : Function.Surjective φ.symm.toMonoidHom := φ.symm.surjective
    have := Subgroup.map_commutator (H₁ := (⊤ : Subgroup SL(2, ZMod 3))) (H₂ := ⊤)
      φ.symm.toMonoidHom
    rw [Subgroup.map_top_of_surjective φ.symm.toMonoidHom hsurj] at this
    rw [← this]
    exact ⟨_, h1, rfl⟩
  have h4 : Subgroup.map L.subtype ⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ ≤ ⁅L, L⁆ := by
    rw [Subgroup.map_commutator]
    refine Subgroup.commutator_mono ?_ ?_ <;>
      · rintro _ ⟨y, -, rfl⟩
        exact y.2
  exact h4 ⟨_, h2, rfl⟩

theorem orderOf_not_dvd_three_of_center {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3)
    {n : ℕ} (hn : 1 ≤ n) {z : SL(n, K)} (hz : z ∈ Subgroup.center SL(n, K)) :
    ¬ 3 ∣ orderOf z := by
  have := Fintype.ofFinite K
  obtain ⟨r, hrp, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [Fintype.card_fin, zero_pow (by omega)] at hrp
    exact zero_ne_one hrp
  have hr2 : r * r = 1 := by
    have h := FiniteField.pow_card_sub_one_eq_one r hr0
    rw [← Nat.card_eq_fintype_card, hK] at h
    simpa [pow_two] using h
  have hz2 : z * z = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, ← hr, ← map_mul, hr2, map_one,
      Matrix.SpecialLinearGroup.coe_one]
  have hord : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hz2)
  intro h3
  have := (Nat.le_of_dvd (by norm_num) (h3.trans hord))
  omega

theorem ker_orderOf_not_dvd_three {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3) {n : ℕ}
    (hn : 1 ≤ n) {X : Type*} [Group X] {θ : SL(n, K) →* X}
    (hker : θ.ker ≤ Subgroup.center SL(n, K)) : ∀ z ∈ θ.ker, ¬ 3 ∣ orderOf z :=
  fun _ hz => orderOf_not_dvd_three_of_center hK hn (hker hz)

theorem mem_centralizer_of_map3 {G X : Type*} [Group G] [Group X] (θ : G →* X)
    (hker : θ.ker ≤ Subgroup.center G) (hcop : ∀ z ∈ θ.ker, ¬ 3 ∣ orderOf z) {L : Subgroup G}
    (hL : ∀ l ∈ L, l ^ 3 ∈ ⁅L, L⁆) {g : G}
    (hg : θ g ∈ Subgroup.centralizer ((L.map θ : Subgroup X) : Set X)) :
    g ∈ Subgroup.centralizer (L : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have hc : ∀ a ∈ Subgroup.zpowers g, ∀ l ∈ L, θ a * θ l = θ l * θ a := by
    intro a ha l hl
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have h1 : Commute (θ g) (θ l) :=
      (Subgroup.mem_centralizer_iff.mp hg (θ l) ⟨l, hl, rfl⟩).symm
    rw [map_zpow]
    exact (h1.zpow_left k).eq
  exact (commutes_of_map_commute_exponent3 θ hker hcop (A := Subgroup.zpowers g) hL hc g
    (Subgroup.mem_zpowers g) l hl).symm

section Lemma65

variable {K : Type} [Field K] [Finite K] {n : ℕ} {X : Type} [Group X] {θ : SL(n, K) →* X}
  {hn : 2 ≤ n}

theorem lemma_6_5_map_of_commute3 (hK : Nat.card K = 3) (hn3 : 3 ≤ n)
    (hker : θ.ker ≤ Subgroup.center SL(n, K)) {L₁ L₂ : Subgroup SL(n, K)}
    {i₁ i₂ : SL(n, K)} (h₁ : IsLongRootSL2 hn L₁ i₁) (h₂ : IsLongRootSL2 hn L₂ i₂)
    (hc : Commute i₁ i₂) (hne : i₁ ≠ i₂) :
    (∀ x ∈ L₁.map θ, ∀ y ∈ L₂.map θ, x * y = y * x) ∨
      (θ i₂ ∉ Subgroup.centralizer ((L₁.map θ : Subgroup X) : Set X) ∧
        LinearBlockStandardPair K (L₁.map θ ⊔ L₂.map θ) (L₁.map θ) (L₂.map θ)) := by
  have hodd : Odd (Nat.card K) := by rw [hK]; decide
  have h2 := two_ne_zero_of_odd_natCard hodd
  obtain ⟨e⟩ := (h₁.isClassicalSL2 h2).nonempty_mulEquiv
  have hL₁ := pow_three_mem_commutator_of_equiv hK e
  rcases lemma_6_5 h2 hn3 h₁ h₂ hc hne with ⟨hcomm, -⟩ | ⟨hnot, ρ, hinj, hrange, hU, hV⟩
  · left
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hcomm x hx y hy]
  · right
    refine ⟨fun hmem => hnot (mem_centralizer_of_map3 θ hker
      (ker_orderOf_not_dvd_three hK (by omega) hker) hL₁ hmem), ?_⟩
    refine linearBlockStandardPair_of_normalized
      (CFSG.ClassicalInvolution.Models.Transfer.ker_comp_le_center ρ hinj hker) ?_ ?_ ?_
    · rw [MonoidHom.range_comp, hrange, Subgroup.map_sup]
    · rw [← Subgroup.map_map, hU]
    · rw [← Subgroup.map_map, hV]

theorem lemma_6_5_image3 (hK : Nat.card K = 3) (hn3 : 3 ≤ n)
    (hker : θ.ker ≤ Subgroup.center SL(n, K)) (hlift : n ≠ 4 ∨ KerInvolutionFree θ)
    {L₁' L₂' : Subgroup X} {i₁' i₂' : X} (h₁ : IsLongRootImage θ hn L₁' i₁')
    (h₂ : IsLongRootImage θ hn L₂' i₂') (hc : Commute i₁' i₂') (hne : i₁' ≠ i₂') :
    (∀ x ∈ L₁', ∀ y ∈ L₂', x * y = y * x) ∨
      (i₂' ∉ Subgroup.centralizer (L₁' : Set X) ∧
        LinearBlockStandardPair K (L₁' ⊔ L₂') L₁' L₂') := by
  obtain ⟨L₁, i₁, h₁, rfl, rfl⟩ := h₁
  obtain ⟨L₂, i₂, h₂, rfl, rfl⟩ := h₂
  have hodd : Odd (Nat.card K) := by rw [hK]; decide
  obtain ⟨hc', hne'⟩ :=
    commute_and_ne_of_map (two_ne_zero_of_odd_natCard hodd) h₂ hker hlift hc hne
  exact lemma_6_5_map_of_commute3 hK hn3 hker h₁ h₂ hc' hne'

end Lemma65

end CFSG.ClassicalInvolution.Q3.Q3W
