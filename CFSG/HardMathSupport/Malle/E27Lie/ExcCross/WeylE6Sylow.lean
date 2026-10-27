module

public import CFSG.HardMathSupport.Malle.E27Lie.ExcCross.WeylE6Check
public import CFSG.RankThree.E6.LargePrimeStabilizers
public import CFSG.RankThree.Lattice.SteinbergBIChecks
public import CFSG.RankThree.PartOne.KE.CTStatement

public section

namespace CFSG.HardMathSupport.Malle.E27Lie.ExcCross

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 CFSG.RankThree.Lattice

set_option linter.unusedSectionVars false

section Weyl


theorem weylMatrix_wordProd' (τ : Tag) (l : List (Fin τ.rank)) :
    weylMatrix ((coxeterSystem τ).wordProd l) = wordMat τ l := by
  ext i j
  rw [weylMatrix_apply, CFSG.RankThree.PartOne.KE.wordProd_smul_eq_wordMat_mulVec,
    Matrix.mulVec_single_one]
  rfl

@[expose] def e6SylX : WeylGroup Tag.E6 := (coxeterSystem Tag.E6).wordProd e6SylWordX

@[expose] def e6SylY : WeylGroup Tag.E6 := (coxeterSystem Tag.E6).wordProd e6SylWordY

theorem weylMatrix_e6SylX : weylMatrix e6SylX = toMat Tag.E6.rank e6SylMX := by
  rw [e6SylX, weylMatrix_wordProd']
  exact wordMat_eq_toMat Tag.E6 _ (by decide +kernel)

theorem weylMatrix_e6SylY : weylMatrix e6SylY = toMat Tag.E6.rank e6SylMY := by
  rw [e6SylY, weylMatrix_wordProd']
  exact wordMat_eq_toMat Tag.E6 _ (by decide +kernel)

theorem e6SylS_one : (1 : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ) ∈ e6SylS := by
  decide +kernel

@[expose] def e6MX : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ := toMat Tag.E6.rank e6SylMX

@[expose] def e6MY : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ := toMat Tag.E6.rank e6SylMY

theorem e6MX_cube : e6MX * e6MX * e6MX = 1 := by
  unfold e6MX; decide +kernel

theorem e6MY_cube : e6MY * e6MY * e6MY = 1 := by
  unfold e6MY; decide +kernel

theorem e6S_mulX : ∀ M ∈ e6SylS, e6MX * M ∈ e6SylS := by
  unfold e6MX; decide +kernel

theorem e6S_mulY : ∀ M ∈ e6SylS, e6MY * M ∈ e6SylS := by
  unfold e6MY; decide +kernel

theorem e6SylX_cube : e6SylX ^ 3 = 1 := by
  apply weylMatrix_injective
  rw [weylMatrix_pow, weylMatrix_e6SylX, weylMatrix_one, pow_succ, pow_succ, pow_one]
  exact e6MX_cube

theorem e6SylY_cube : e6SylY ^ 3 = 1 := by
  apply weylMatrix_injective
  rw [weylMatrix_pow, weylMatrix_e6SylY, weylMatrix_one, pow_succ, pow_succ, pow_one]
  exact e6MY_cube

@[expose] def e6SylP : Subgroup (WeylGroup Tag.E6) :=
  Subgroup.closure ({e6SylX, e6SylY} : Set (WeylGroup Tag.E6))

theorem weylMatrix_mem_e6SylS {x : WeylGroup Tag.E6} (hx : x ∈ e6SylP) :
    weylMatrix x ∈ e6SylS := by
  induction hx using Subgroup.closure_induction_left with
  | one => rw [weylMatrix_one]; exact e6SylS_one
  | mul_left a ha y _ ih =>
    rcases ha with rfl | rfl
    · rw [weylMatrix_mul, weylMatrix_e6SylX]; exact e6S_mulX _ ih
    · rw [weylMatrix_mul, weylMatrix_e6SylY]; exact e6S_mulY _ ih
  | inv_mul_cancel a ha y _ ih =>
    have e : ∀ b : WeylGroup Tag.E6, b ^ 3 = 1 → b⁻¹ = b * b := fun b hb =>
      inv_eq_of_mul_eq_one_right (by rw [show b * (b * b) = b ^ 3 by simp only [pow_succ, pow_zero, one_mul, mul_assoc]]; exact hb)
    rcases ha with rfl | rfl
    · rw [e _ e6SylX_cube, mul_assoc, weylMatrix_mul, weylMatrix_mul, weylMatrix_e6SylX]
      exact e6S_mulX _ (e6S_mulX _ ih)
    · rw [e _ e6SylY_cube, mul_assoc, weylMatrix_mul, weylMatrix_mul, weylMatrix_e6SylY]
      exact e6S_mulY _ (e6S_mulY _ ih)

theorem e6SylS_card : e6SylS.toFinset.card = 81 := by
  decide +kernel

@[expose] def e6SylProd (w : List Bool) : WeylGroup Tag.E6 :=
  (w.map fun b => if b then e6SylY else e6SylX).prod

theorem e6SylProd_mem (w : List Bool) : e6SylProd w ∈ e6SylP := by
  refine Subgroup.list_prod_mem _ fun g hg => ?_
  obtain ⟨b, -, rfl⟩ := List.mem_map.1 hg
  cases b
  · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.subset_closure (by simp)

theorem weylMatrix_e6SylProd (w : List Bool) :
    weylMatrix (e6SylProd w) = toMat Tag.E6.rank (e6SylList w) := by
  induction w with
  | nil =>
    rw [e6SylProd, List.map_nil, List.prod_nil, weylMatrix_one, e6SylList, List.foldr_nil,
      toMat_lid]
  | cons b w ih =>
    have hl : e6SylList (b :: w) = lmul Tag.E6.rank (if b then e6SylMY else e6SylMX)
        (e6SylList w) := rfl
    have hp : e6SylProd (b :: w) = (if b then e6SylY else e6SylX) * e6SylProd w := by
      rw [e6SylProd, List.map_cons, List.prod_cons]; rfl
    rw [hp, weylMatrix_mul, ih, hl, toMat_lmul]
    cases b
    · simp [weylMatrix_e6SylX]
    · simp [weylMatrix_e6SylY]

theorem weylMatrix_image_e6SylP :
    weylMatrix '' (e6SylP : Set (WeylGroup Tag.E6)) = (e6SylS.toFinset : Set _) := by
  ext M
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using weylMatrix_mem_e6SylS hx
  · intro hM
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hM)
    exact ⟨e6SylProd w, e6SylProd_mem w, weylMatrix_e6SylProd w⟩

theorem e6Syl_card : Nat.card e6SylP = 81 := by
  have h1 : Nat.card e6SylP = Nat.card (weylMatrix '' (e6SylP : Set (WeylGroup Tag.E6))) :=
    (Nat.card_image_of_injective weylMatrix_injective _).symm
  rw [h1, weylMatrix_image_e6SylP, Nat.card_coe_set_eq, Set.ncard_coe_finset, e6SylS_card]

theorem padicValNat_three_card_weylGroup_E6 :
    (Nat.card (WeylGroup Tag.E6)).factorization 3 = 4 := by
  rw [card_weylGroup_E6, Nat.factorization_def _ Nat.prime_three,
    show (51840 : ℕ) = 3 ^ 4 * 640 by norm_num,
    padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by norm_num)]

theorem exists_conj_mem_e6SylP (p : WeylGroup Tag.E6) (hp : p ^ 3 = 1) :
    ∃ g : WeylGroup Tag.E6, g⁻¹ * p * g ∈ e6SylP := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card e6SylP = 3 ^ (Nat.card (WeylGroup Tag.E6)).factorization 3 := by
    rw [padicValNat_three_card_weylGroup_E6, e6Syl_card]; norm_num
  let S0 : Sylow 3 (WeylGroup Tag.E6) := Sylow.ofCard e6SylP hcard
  have hpg : IsPGroup 3 (Subgroup.zpowers p) := by
    intro x
    refine ⟨1, ?_⟩
    obtain ⟨x, m, rfl⟩ := x
    refine Subtype.ext ?_
    simp only [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
    simp [hp]
  obtain ⟨S, hS⟩ := hpg.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (WeylGroup Tag.E6) S0 S
  refine ⟨g, ?_⟩
  have hpS : p ∈ (S : Subgroup (WeylGroup Tag.E6)) := hS (Subgroup.mem_zpowers p)
  rw [← hg] at hpS
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hpS
  obtain ⟨y, hy, hyp⟩ := hpS
  have hy' : y ∈ e6SylP := by
    have : (S0 : Subgroup _) = e6SylP := Sylow.coe_ofCard _ _
    rwa [← this]
  have : g⁻¹ * p * g = y := by
    rw [← hyp, MulAut.smul_def, MulAut.conj_apply]; group
  rwa [this]

theorem weylMatrix_cube_of_cube {τ : Tag} {q : WeylGroup τ} (hq : q ^ 3 = 1) :
    weylMatrix q * weylMatrix q * weylMatrix q = 1 := by
  rw [← weylMatrix_mul, ← weylMatrix_mul, ← weylMatrix_one (τ := τ)]
  congr 1
  calc q * q * q = q ^ 3 := by simp only [pow_succ, pow_zero, one_mul]
    _ = 1 := hq

theorem exists_conj_fixed3_E6 (p : WeylGroup Tag.E6) (hp : p ^ 3 = 1) :
    ∃ g : WeylGroup Tag.E6, 81 ≤ (fixed3 Tag.E6.cartan (weylMatrix (g⁻¹ * p * g))).card := by
  obtain ⟨g, hg⟩ := exists_conj_mem_e6SylP p hp
  refine ⟨g, e6S_fixed3 _ (weylMatrix_mem_e6SylS hg) ?_⟩
  refine weylMatrix_cube_of_cube (q := g⁻¹ * p * g) ?_
  have e3 : g⁻¹ * p * g * (g⁻¹ * p * g) * (g⁻¹ * p * g) = g⁻¹ * p ^ 3 * g := by
    simp only [pow_succ, pow_zero, one_mul]; group
  calc (g⁻¹ * p * g) ^ 3 = g⁻¹ * p * g * (g⁻¹ * p * g) * (g⁻¹ * p * g) := by
        simp only [pow_succ, pow_zero, one_mul]
    _ = 1 := by rw [e3, hp]; group

end Weyl

end CFSG.HardMathSupport.Malle.E27Lie.ExcCross
