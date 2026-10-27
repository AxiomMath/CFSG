module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofSpFour
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLeviInner
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofSpLevi

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Matrix Subgroup CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

section TwoByTwo

variable {K : Type} [Field K] [CharP K 2]

theorem det_sub_one_eq_add (X : SL(2, K)) :
    ((X : Matrix (Fin 2) (Fin 2) K) - 1).det = X 0 0 + X 1 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hdet := X.2
  rw [Matrix.det_fin_two] at hdet ⊢
  simp only [Matrix.sub_apply, Matrix.one_apply_eq,
    Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
    Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), sub_zero]
  linear_combination hdet + (1 - X 0 0 - X 1 1) * h2

theorem ne_of_det_sub_one_ne_zero {X : SL(2, K)}
    (hX : ((X : Matrix (Fin 2) (Fin 2) K) - 1).det ≠ 0) : X 0 0 ≠ X 1 1 := by
  intro h
  apply hX
  rw [det_sub_one_eq_add, h, CharTwo.add_self_eq_zero]

theorem mul_self_eq_add (X : SL(2, K)) :
    (X : Matrix (Fin 2) (Fin 2) K) * X = (X 0 0 + X 1 1) • (X : Matrix (Fin 2) (Fin 2) K) + 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hdet := X.2
  rw [Matrix.det_fin_two] at hdet
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | ring1 | linear_combination -hdet - h2

theorem det_sub_one_ne_zero_of_mul_self_ne_one {X : SL(2, K)} (hX : X * X ≠ 1) :
    ((X : Matrix (Fin 2) (Fin 2) K) - 1).det ≠ 0 := by
  intro h
  apply hX
  rw [det_sub_one_eq_add] at h
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, mul_self_eq_add, h, zero_smul, zero_add,
    Matrix.SpecialLinearGroup.coe_one]

omit [CharP K 2] in
theorem relations_of_commute {S X : Matrix (Fin 2) (Fin 2) K} (h : S * X = X * S) :
    S 0 1 * (X 0 0 - X 1 1) = X 0 1 * (S 0 0 - S 1 1) ∧
      S 1 0 * (X 0 0 - X 1 1) = X 1 0 * (S 0 0 - S 1 1) := by
  have h01 := congrFun (congrFun h 0) 1
  have h10 := congrFun (congrFun h 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at h01 h10
  constructor
  · linear_combination -h01
  · linear_combination h10

omit [CharP K 2] in
theorem commute_of_commute_of_ne {S S' X : Matrix (Fin 2) (Fin 2) K} (hX : X 0 0 ≠ X 1 1)
    (h : S * X = X * S) (h' : S' * X = X * S') : S * S' = S' * S := by
  have hδ : X 0 0 - X 1 1 ≠ 0 := sub_ne_zero.mpr hX
  obtain ⟨hb, hc⟩ := relations_of_commute h
  obtain ⟨hb', hc'⟩ := relations_of_commute h'
  have e00 : S 0 1 * S' 1 0 - S' 0 1 * S 1 0 = 0 := by
    have : (X 0 0 - X 1 1) ^ 2 * (S 0 1 * S' 1 0 - S' 0 1 * S 1 0) = 0 := by
      linear_combination (S' 1 0 * (X 0 0 - X 1 1)) * hb + (X 0 1 * (S 0 0 - S 1 1)) * hc' -
        (S 1 0 * (X 0 0 - X 1 1)) * hb' - (X 0 1 * (S' 0 0 - S' 1 1)) * hc
    exact (mul_eq_zero.mp this).resolve_left (pow_ne_zero 2 hδ)
  have e01 : S' 0 1 * (S 0 0 - S 1 1) - S 0 1 * (S' 0 0 - S' 1 1) = 0 := by
    have : (X 0 0 - X 1 1) * (S' 0 1 * (S 0 0 - S 1 1) - S 0 1 * (S' 0 0 - S' 1 1)) = 0 := by
      linear_combination (S 0 0 - S 1 1) * hb' - (S' 0 0 - S' 1 1) * hb
    exact (mul_eq_zero.mp this).resolve_left hδ
  have e10 : S 1 0 * (S' 0 0 - S' 1 1) - S' 1 0 * (S 0 0 - S 1 1) = 0 := by
    have : (X 0 0 - X 1 1) * (S 1 0 * (S' 0 0 - S' 1 1) - S' 1 0 * (S 0 0 - S 1 1)) = 0 := by
      linear_combination (S' 0 0 - S' 1 1) * hc - (S 0 0 - S 1 1) * hc'
    exact (mul_eq_zero.mp this).resolve_left hδ
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination e00
  · linear_combination e01
  · linear_combination e10
  · linear_combination -e00

theorem eq_one_of_commute_of_mul_self {a X : SL(2, K)}
    (hX : ((X : Matrix (Fin 2) (Fin 2) K) - 1).det ≠ 0)
    (h : (a : Matrix (Fin 2) (Fin 2) K) * X = X * a) (ha : a * a = 1) : a = 1 := by
  have hXne := ne_of_det_sub_one_ne_zero hX
  have hδ : X 0 0 - X 1 1 ≠ 0 := sub_ne_zero.mpr hXne
  have htr : a 0 0 + a 1 1 = 0 := by
    have h1 := mul_self_eq_add a
    rw [← Matrix.SpecialLinearGroup.coe_mul, ha, Matrix.SpecialLinearGroup.coe_one] at h1
    by_contra hne
    have h2 : (a 0 0 + a 1 1) • (a : Matrix (Fin 2) (Fin 2) K) = 0 := by
      have := congrArg (· - (1 : Matrix (Fin 2) (Fin 2) K)) h1
      simpa using this.symm
    have h3 : (a : Matrix (Fin 2) (Fin 2) K) = 0 := (smul_eq_zero.mp h2).resolve_left hne
    have h4 := a.2
    rw [h3, Matrix.det_zero] at h4
    exact zero_ne_one h4
  have hdiag : a 0 0 = a 1 1 := by
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    linear_combination htr - a 1 1 * h2
  obtain ⟨hb, hc⟩ := relations_of_commute h
  rw [hdiag, sub_self, mul_zero] at hb hc
  have hb0 : a 0 1 = 0 := (mul_eq_zero.mp hb).resolve_right hδ
  have hc0 : a 1 0 = 0 := (mul_eq_zero.mp hc).resolve_right hδ
  have hdet := a.2
  rw [Matrix.det_fin_two, hb0, hc0, mul_zero, sub_zero, ← hdiag] at hdet
  have h1 := eq_one_of_mul_self_eq_one hdet
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hb0, hc0, h1, ← hdiag]

end TwoByTwo

section Blocks

open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)

variable {K : Type} [Field K] {m : ℕ}

variable (K m) in
@[expose] noncomputable def spWL : SL(2, K) × StatedSp m K →* StatedSp (m + 1) K :=
  (spW K m).noncommCoprod (spL K m) fun a h => spW_commute_spL a h

theorem spWL_apply (a : SL(2, K)) (h : StatedSp m K) :
    spWL K m (a, h) = spW K m a * spL K m h :=
  MonoidHom.noncommCoprod_apply _ _ _ _

theorem spWL_one_left (h : StatedSp m K) : spWL K m (1, h) = spL K m h := by
  rw [spWL_apply, map_one, one_mul]

theorem exists_spWL_of_commute {X : SL(2, K)} (hX : ((X : Matrix (Fin 2) (Fin 2) K) - 1).det ≠ 0)
    {g : StatedSp (m + 1) K} (hc : g * spW K m X = spW K m X * g) :
    ∃ (a : SL(2, K)) (h : StatedSp m K), g = spWL K m (a, h) ∧ a * X = X * a := by
  obtain ⟨a, ha, -⟩ := exists_longBlock_mul_of_col (k := Fin.last m) fun r hr c hc' =>
    mat_apply_eq_zero_of_commute' hX hc hr hc'
  rw [← range_spL] at ha
  obtain ⟨h, hh⟩ := ha
  have hg : g = spW K m a * spL K m h := by
    rw [hh, spW, mul_inv_cancel_left]
  refine ⟨a, h, by rw [spWL_apply, hg], ?_⟩
  have e1 : spW K m a * spL K m h * spW K m X = spW K m (a * X) * spL K m h := by
    rw [mul_assoc, ← spW_commute_spL X h, ← mul_assoc, ← map_mul]
  have e2 : spW K m X * (spW K m a * spL K m h) = spW K m (X * a) * spL K m h := by
    rw [← mul_assoc, ← map_mul]
  rw [hg, e1, e2] at hc
  exact longBlock_injective _ (mul_right_cancel hc)

theorem proj_spWL_mem_normalizer (a : SL(2, K)) (h : StatedSp m K) :
    proj (m + 1) K (spWL K m (a, h)) ∈
      normalizer (spBarL K m : Set (StatedProj (StatedSp (m + 1) K))) := by
  rw [spWL_apply, map_mul]
  refine mul_mem (centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun l hl => ?_))
    (le_normalizer ⟨h, rfl⟩)
  exact (spBarW_commute_spBarL ⟨a, rfl⟩ hl).symm

theorem commutatorElement_proj_spWL_mem {a a' : SL(2, K)} (h h' : StatedSp m K)
    (haa : a * a' = a' * a) :
    ⁅proj (m + 1) K (spWL K m (a, h)), proj (m + 1) K (spWL K m (a', h'))⁆ ∈ spBarL K m := by
  rw [← map_commutatorElement, ← map_commutatorElement]
  have hc : ⁅((a, h) : SL(2, K) × StatedSp m K), (a', h')⁆ = (1, ⁅h, h'⁆) := by
    refine Prod.ext ?_ rfl
    change ⁅a, a'⁆ = 1
    rw [commutatorElement_def, haa, mul_inv_cancel_right, mul_inv_cancel]
  rw [hc, spWL_one_left]
  exact ⟨⁅h, h'⁆, rfl⟩

end Blocks

section Lift

open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)

variable {K : Type} [Field K] {m : ℕ} {G : Type} [Group G] {A : Subgroup G}
  {θ : ↥A →* StatedProj (StatedSp (m + 1) K)} [CharP K 2]

theorem exists_spWL_of_mem_centralizer {X : SL(2, K)}
    (hX : ((X : Matrix (Fin 2) (Fin 2) K) - 1).det ≠ 0) {y : G} (hyA : y ∈ A)
    (hyθ : θ ⟨y, hyA⟩ = proj (m + 1) K (spW K m X)) {g : G}
    (hg : g ∈ centralizer ((zpowers y : Subgroup G) : Set G)) (hgA : g ∈ A) :
    ∃ (a : SL(2, K)) (h : StatedSp m K), θ ⟨g, hgA⟩ = proj (m + 1) K (spWL K m (a, h)) ∧
      a * X = X * a := by
  obtain ⟨g', hg'⟩ := QuotientGroup.mk'_surjective _ (θ ⟨g, hgA⟩)
  have h1 := mem_centralizer_iff.mp hg y (mem_zpowers y)
  have h2 : θ ⟨g, hgA⟩ * θ ⟨y, hyA⟩ = θ ⟨y, hyA⟩ * θ ⟨g, hgA⟩ := by
    rw [← map_mul, ← map_mul]
    exact congrArg θ (Subtype.ext h1.symm)
  rw [hyθ, ← hg'] at h2
  change proj (m + 1) K g' * _ = _ * proj (m + 1) K g' at h2
  rw [← map_mul, ← map_mul] at h2
  obtain ⟨a, h, hah, hX'⟩ := exists_spWL_of_commute hX (proj_sp_injective h2)
  exact ⟨a, h, by rw [← hg', hah]; rfl, hX'⟩

variable (hker : θ.ker = center ↥A) (hθ : Function.Surjective θ)
  (h4 : ∃ s : Finset K, s.card = 4)
include hker hθ h4

theorem layerCentralizer_zpowers_eq_spLeviL (hm : 1 ≤ m) {X : SL(2, K)}
    (hX : ((X : Matrix (Fin 2) (Fin 2) K) - 1).det ≠ 0) {y : G} (hyW : y ∈ spLeviW θ)
    (hyA : y ∈ A) (hyθ : θ ⟨y, hyA⟩ = proj (m + 1) K (spW K m X)) :
    AS76b.layerCentralizer A (zpowers y) = spLeviL θ := by
  have hXne := ne_of_det_sub_one_ne_zero hX
  refine layerCentralizer_eq_levLift hker hθ (commutator_spBarL h4) (isQuasisimple_spBarL hm h4)
    ?_ ?_ ?_
  · refine le_inf levLift_le ?_
    rw [le_centralizer_iff, zpowers_le]
    exact levLift_le_centralizer_levLift hker (fun _ hs _ hs' => spBarW_commute_spBarL hs hs')
      hyW
  · intro g hgM hgA
    obtain ⟨a, h, hah, -⟩ := exists_spWL_of_mem_centralizer hX hyA hyθ (mem_inf.mp hgM).2 hgA
    rw [hah]
    exact proj_spWL_mem_normalizer a h
  · intro a ha b hb haA hbA
    obtain ⟨a₀, a₁, ha', hac⟩ := exists_spWL_of_mem_centralizer hX hyA hyθ (mem_inf.mp ha).2 haA
    obtain ⟨b₀, b₁, hb', hbc⟩ := exists_spWL_of_mem_centralizer hX hyA hyθ (mem_inf.mp hb).2 hbA
    rw [ha', hb']
    exact commutatorElement_proj_spWL_mem a₁ b₁ (Subtype.ext (commute_of_commute_of_ne hXne
      (congrArg Subtype.val hac) (congrArg Subtype.val hbc)))

theorem exists_mem_spLeviW_orderOf [Finite G] [Finite K] (hZ : Odd (Nat.card (center ↥A)))
    {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f) (r : ℕ) [hr : Fact r.Prime] (hr2 : r ≠ 2)
    (hrd : r ∣ Nat.card SL(2, K)) :
    ∃ (X : SL(2, K)) (y : G) (hyA : y ∈ A), y ∈ spLeviW θ ∧
      θ ⟨y, hyA⟩ = proj (m + 1) K (spW K m X) ∧ orderOf y = r ∧ orderOf X = r ∧
        ((X : Matrix (Fin 2) (Fin 2) K) - 1).det ≠ 0 := by
  obtain ⟨X, hX⟩ := exists_prime_orderOf_dvd_card' r hrd
  have hXr : X ^ r = 1 := hX ▸ pow_orderOf_eq_one X
  have hX1 : X ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hX
    exact hr.out.one_lt.ne hX
  have hs : proj (m + 1) K (spW K m X) ∈ spBarW K m := ⟨X, rfl⟩
  have hsr : proj (m + 1) K (spW K m X) ^ r = 1 := by
    rw [← map_pow, ← map_pow, hXr, map_one, map_one]
  have hs1 : proj (m + 1) K (spW K m X) ≠ 1 := fun h =>
    hX1 (proj_spW_injective (h.trans (map_one _).symm))
  obtain ⟨y, hyW, hyA, hyθ, hyr⟩ := exists_mem_levLift_orderOf hker hθ hZ hf hK
    (commutator_spBarW h4) (spBarWEquiv K m) hs hsr hs1
  refine ⟨X, y, hyA, hyW, hyθ, hyr, hX, det_sub_one_ne_zero_of_mul_self_ne_one fun h => hr2 ?_⟩
  have h2 : orderOf X ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact h)
  rw [hX] at h2
  exact (Nat.prime_dvd_prime_iff_eq hr.out Nat.prime_two).mp h2

end Lift

end CFSG.ComponentClassification.RankTwoClassical
