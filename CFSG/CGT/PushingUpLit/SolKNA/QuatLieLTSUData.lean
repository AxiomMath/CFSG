module

public import CFSG.ClassicalInvolution.ModelFacts.TG3SmallSU
public import CFSG.ClassicalInvolution.ModelFacts.TG3VacPSU
public import CFSG.ClassicalInvolution.RouteD.TypeULocal
public import CFSG.ClassicalInvolution.Models.UnitaryFrames
public import CFSG.LieType.Universal.Unitary.Clause0
public import CFSG.GroupTheory.LocalCores.Components

public section

open Matrix

namespace CFSG.CGT.PushingUpLit.SolKNA.LTSU

open CFSG.ClassicalInvolution
open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.ModelFacts.TG3 CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

section Pure

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem mem_center_of_suMat_eq_neg_one {n : ℕ} {x : Su K p f n} (h : suMat x = -1) :
    x ∈ Subgroup.center (Su K p f n) := by
  rw [Subgroup.mem_center_iff]
  intro y
  apply suMat_injective
  rw [suMat_mul, suMat_mul, h, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_one, Matrix.one_mul]

theorem exists_swap_four (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) :
    ∃ c : Su K p f 4,
      (rootSU2 K p f (by norm_num : 2 ≤ 4)).map (MulAut.conj c).toMonoidHom =
        (blockEmb K p f 4 2 2 (by norm_num)).range ∧
      c * rootInvSU K p f (by norm_num : 2 ≤ 4) * c⁻¹ *
        (rootInvSU K p f (by norm_num : 2 ≤ 4))⁻¹ ∈ Subgroup.center (Su K p f 4) := by
  have h4 : (2 : ℕ) ≤ 4 := by norm_num
  have hb := isLongRootSU2_range_blockEmb hK hp (j := 2) (n := 4) (by norm_num)
  have hs := isLongRootSU2_standard (K := K) (p := p) (f := f) h4
  obtain ⟨c, hc⟩ := ModelFacts.exists_conj_of_isLongRootSU2 hb hs
  refine ⟨c, hc.symm, ?_⟩
  have hcl := hs.conj c
  rw [← hc] at hcl
  have hi := hcl.involution_unique hK hp hb
  rw [hi]
  apply mem_center_of_suMat_eq_neg_one
  have hinv : (rootInvSU K p f h4)⁻¹ = rootInvSU K p f h4 :=
    inv_eq_of_mul_eq_one_right hs.mul_self
  rw [hinv, suMat_mul, suMat_blockEmb, suMat_negOneSU, suMat_rootInvSU]
  rw [show blockMat 4 2 (-1 : Matrix (Fin 2) (Fin 2) K) = negBlock K 4 2 from rfl,
    negBlock_four_two (K := K), Matrix.neg_mul, negBlock_mul_self]

theorem comm_blocks_four (A B : Su K p f 2) :
    blockEmb K p f 4 2 0 (by norm_num) A * blockEmb K p f 4 2 2 (by norm_num) B =
      blockEmb K p f 4 2 2 (by norm_num) B * blockEmb K p f 4 2 0 (by norm_num) A := by
  apply suMat_injective
  rw [suMat_mul, suMat_mul, suMat_blockEmb, suMat_blockEmb]
  exact blockMat_mul_comm_of_disjoint (by norm_num) _ _

theorem isQuasisimple_su (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) {m : ℕ} (hm : 3 ≤ m) :
    CFSG.IsQuasisimple (Su K p f m) := by
  have h := (isQuasisimple_statedSU_of_card hK hm (by
    intro h
    exact prime_pow_ne_two_of_ne_two hp f (Prod.mk.inj h).2)).1
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (MulEquiv.subgroupCongr (SUid_eq_statedSU hK m)).symm h

end Pure

section Matrices

variable {K : Type} [Field K]

theorem negBlock_zero_eq (n : ℕ) :
    negBlock K n 0 =
      Matrix.diagonal (fun a : Fin n => if a.val < 2 then (-1 : K) else 1) := by
  rw [negBlock_eq_diagonal]
  congr 1
  funext a
  simp

theorem eq_blockMat_of_commute_fix (h2 : (2 : K) ≠ 0) {n : ℕ} (hn : 2 ≤ n)
    {X : Matrix (Fin n) (Fin n) K} (h1 : X * -negBlock K n 0 = -negBlock K n 0 * X)
    (h3 : X * (1 + -negBlock K n 0) = 1 + -negBlock K n 0) :
    X = blockMat n 2 (Matrix.of fun u v : Fin (n - 2) =>
      X (blockIdx 2 (by omega) u) (blockIdx 2 (by omega) v)) := by
  rw [negBlock_zero_eq] at h1 h3
  set d : Fin n → K := fun a => if a.val < 2 then (-1 : K) else 1 with hd
  have e1 : ∀ a b, X a b * d b = d a * X a b := by
    intro a b
    have := congrFun (congrFun h1 a) b
    simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.neg_apply, Matrix.mul_diagonal,
      Matrix.diagonal_mul] at this
    linear_combination -this
  have hD : (1 : Matrix (Fin n) (Fin n) K) + -Matrix.diagonal d =
      Matrix.diagonal (fun c => 1 - d c) := by
    ext a b
    by_cases hab : a = b
    · subst hab
      rw [Matrix.add_apply, Matrix.neg_apply, Matrix.one_apply_eq, Matrix.diagonal_apply_eq,
        Matrix.diagonal_apply_eq]
      ring
    · rw [Matrix.add_apply, Matrix.neg_apply, Matrix.one_apply_ne hab,
        Matrix.diagonal_apply_ne _ hab, Matrix.diagonal_apply_ne _ hab]
      ring
  have e3a : ∀ a, X a a * (1 - d a) = 1 - d a := by
    intro a
    have := congrFun (congrFun h3 a) a
    rw [hD, Matrix.mul_diagonal, Matrix.diagonal_apply_eq] at this
    exact this
  have e3b : ∀ a b, a ≠ b → X a b * (1 - d b) = 0 := by
    intro a b hab
    have := congrFun (congrFun h3 a) b
    rw [hD, Matrix.mul_diagonal, Matrix.diagonal_apply_ne _ hab] at this
    exact this
  ext a b
  rw [blockMat_apply]
  have ha := a.isLt
  have hb := b.isLt
  by_cases hab : (2 ≤ a.val ∧ a.val < 2 + (n - 2)) ∧ (2 ≤ b.val ∧ b.val < 2 + (n - 2))
  · rw [dite_eq_left hab]
    have ha' : a = blockIdx 2 (by omega) (⟨a.val - 2, by omega⟩ : Fin (n - 2)) :=
      Fin.ext (by simp [blockIdx]; omega)
    have hb' : b = blockIdx 2 (by omega) (⟨b.val - 2, by omega⟩ : Fin (n - 2)) :=
      Fin.ext (by simp [blockIdx]; omega)
    simp only [Matrix.of_apply]
    exact congrArg₂ X ha' hb'
  · rw [dite_eq_right hab]
    by_cases hb2 : b.val < 2
    · have hdb : d b = -1 := by
        simp only [hd]
        exact ite_eq_left hb2
      rcases eq_or_ne a b with rfl | hne
      · rw [Matrix.one_apply_eq]
        have h4 := e3a a
        rw [hdb] at h4
        have h5 : (2 : K) * (X a a - 1) = 0 := by linear_combination h4
        have h6 := (mul_eq_zero.mp h5).resolve_left h2
        linear_combination h6
      · rw [Matrix.one_apply_ne hne]
        have h4 := e3b a b hne
        rw [hdb] at h4
        have h5 : (2 : K) * X a b = 0 := by linear_combination h4
        exact (mul_eq_zero.mp h5).resolve_left h2
    · have hb2' : 2 ≤ b.val := by omega
      have ha2 : a.val < 2 := by
        by_contra h
        exact hab ⟨⟨by omega, by omega⟩, ⟨hb2', by omega⟩⟩
      have hda : d a = -1 := by
        simp only [hd]
        exact ite_eq_left ha2
      have hdb : d b = 1 := by
        simp only [hd]
        exact ite_eq_right hb2
      have h1' := e1 a b
      rw [hda, hdb] at h1'
      have hne : a ≠ b := by
        intro h
        subst h
        omega
      rw [Matrix.one_apply_ne hne]
      have h5 : (2 : K) * X a b = 0 := by linear_combination h1'
      exact (mul_eq_zero.mp h5).resolve_left h2

end Matrices

section Component

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem exists_blockEmb_of_mem_longRootGroupSU_neg (h2 : (2 : K) ≠ 0) {n : ℕ} (hn : 2 ≤ n)
    {x : Su K p f n} (hx : x ∈ longRootGroupSU K p f (-negBlock K n 0)) :
    ∃ B : Su K p f (n - 2), blockEmb K p f n (n - 2) 2 (by omega) B = x := by
  obtain ⟨h1, h3⟩ := mem_longRootGroupSU.mp hx
  have hX := eq_blockMat_of_commute_fix h2 hn h1 h3
  set B0 : Matrix (Fin (n - 2)) (Fin (n - 2)) K := Matrix.of fun u v : Fin (n - 2) =>
      suMat x (blockIdx 2 (by omega) u) (blockIdx 2 (by omega) v) with hB0
  have hdet : B0.det = 1 := by
    rw [← det_blockMat (by omega : 2 + (n - 2) ≤ n) B0, ← hX]
    exact det_suMat x
  have hunit : conjTr (unitaryInvolution K p f) B0 * B0 = 1 := by
    have hx1 : conjTr (unitaryInvolution K p f) (suMat x) * suMat x = 1 := x.2.2
    rw [hX, conjTr_blockMat, ← blockMat_mul (by omega : 2 + (n - 2) ≤ n)] at hx1
    exact blockMat_injective (by omega : 2 + (n - 2) ≤ n) (by rw [hx1, blockMat_one])
  refine ⟨mkSU K p f B0 hdet hunit, ?_⟩
  apply suMat_injective
  rw [suMat_blockEmb, suMat_mkSU, ← hX]

theorem blockEmb_mem_longRootGroupSU_neg {n : ℕ} (hn : 2 ≤ n) (B : Su K p f (n - 2)) :
    blockEmb K p f n (n - 2) 2 (by omega) B ∈ longRootGroupSU K p f (-negBlock K n 0) := by
  rw [mem_longRootGroupSU, suMat_blockEmb]
  refine ⟨?_, ?_⟩
  · rw [Matrix.mul_neg, Matrix.neg_mul, negBlock]
    exact congrArg Neg.neg (blockMat_mul_comm_of_disjoint (m := n) (i := 0) (i' := 2)
      (by omega) (-1 : Matrix (Fin 2) (Fin 2) K) (suMat B)).symm
  · rw [negBlock_zero_eq]
    have hD : (1 : Matrix (Fin n) (Fin n) K) +
        -Matrix.diagonal (fun a : Fin n => if a.val < 2 then (-1 : K) else 1) =
        Matrix.diagonal (fun c : Fin n => if c.val < 2 then (2 : K) else 0) := by
      ext a b
      by_cases hab : a = b
      · subst hab
        rw [Matrix.add_apply, Matrix.neg_apply, Matrix.one_apply_eq, Matrix.diagonal_apply_eq,
          Matrix.diagonal_apply_eq]
        split_ifs <;> ring
      · rw [Matrix.add_apply, Matrix.neg_apply, Matrix.one_apply_ne hab,
          Matrix.diagonal_apply_ne _ hab, Matrix.diagonal_apply_ne _ hab]
        ring
    rw [hD]
    ext a b
    rw [Matrix.mul_diagonal, Matrix.diagonal_apply]
    by_cases hb : b.val < 2
    · rw [blockMat_apply_of_not_mem_right _ a (by omega)]
      by_cases hab : a = b
      · subst hab
        rw [Matrix.one_apply_eq, ite_eq_left hb, ite_eq_left rfl]
        ring
      · rw [Matrix.one_apply_ne hab, ite_eq_right hab, zero_mul]
    · by_cases hab : a = b
      · subst hab
        rw [ite_eq_right hb, mul_zero, ite_eq_left rfl]
      · rw [ite_eq_right hab, ite_eq_right hb, mul_zero]

theorem commute_of_mem_longRootGroupSU_neg {n : ℕ} {i x : Su K p f n}
    (hx : x ∈ longRootGroupSU K p f (-suMat i)) : x * i = i * x := by
  apply suMat_injective
  rw [suMat_mul, suMat_mul]
  have h := (mem_longRootGroupSU.mp hx).1
  rw [Matrix.mul_neg, Matrix.neg_mul, neg_inj] at h
  exact h

theorem commute_of_central_ratio (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hf : 1 ≤ f)
    {n : ℕ} (hn2 : 2 ≤ n) (hn3 : 3 ≤ n) (hn4 : n ≠ 4) {a : Su K p f n}
    (ha : a * rootInvSU K p f hn2 * a⁻¹ * (rootInvSU K p f hn2)⁻¹ ∈
      Subgroup.center (Su K p f n)) :
    a * rootInvSU K p f hn2 = rootInvSU K p f hn2 * a := by
  have hs := isLongRootSU2_standard (K := K) (p := p) (f := f) hn2
  have hcl := hs.isClassicalSL2 hK hp
  have hs₂ := hs.conj a
  have hcl₂ := hs₂.isClassicalSL2 hK hp
  set i₀ := rootInvSU K p f hn2 with hi₀
  have hii : i₀ * i₀ = 1 := hs.mul_self
  have hord : orderOf i₀ = 2 := hcl.orderOf_eq_two
  have hi1 : i₀ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hord
    exact absurd hord (by norm_num)
  have hord₂ : orderOf (a * i₀ * a⁻¹) = 2 := by
    rw [← hord]
    exact MulEquiv.orderOf_eq (MulAut.conj a) i₀
  have hLeq : (rootSU2 K p f hn2).map (MulAut.conj a).toMonoidHom = rootSU2 K p f hn2 := by
    by_contra hne
    apply hn4
    refine rank_eq_four_of_central_pair_su3 hK hp hf hn3 (hn := hn2)
      (R₁ := rootSU2 K p f hn2) (R₂ := (rootSU2 K p f hn2).map (MulAut.conj a).toMonoidHom)
      ⟨i₀, hs⟩ ⟨_, hs₂⟩ (Ne.symm hne) (r₁ := i₀) (r₂ := a * i₀ * a⁻¹) hs.mem ?_ hi1 hs₂.mem
      ?_ ?_ ?_
    · intro s hs'
      exact (Subgroup.mem_centralizer_singleton_iff.mp (hcl.le_centralizer hs')).symm
    · intro s hs'
      exact (Subgroup.mem_centralizer_singleton_iff.mp (hcl₂.le_centralizer hs')).symm
    · intro h
      apply hi1
      have := congrArg (fun z => a⁻¹ * z * a) h
      simpa [mul_assoc] using this
    · have hz := Subgroup.mem_center_iff.mp ha i₀
      have hx : a * i₀ * a⁻¹ = (a * i₀ * a⁻¹ * i₀⁻¹) * i₀ := by group
      have : i₀ * (a * i₀ * a⁻¹) = a * i₀ * a⁻¹ * i₀⁻¹ := by
        calc i₀ * (a * i₀ * a⁻¹) = i₀ * ((a * i₀ * a⁻¹ * i₀⁻¹) * i₀) := by rw [← hx]
          _ = (i₀ * (a * i₀ * a⁻¹ * i₀⁻¹)) * i₀ := by group
          _ = ((a * i₀ * a⁻¹ * i₀⁻¹) * i₀) * i₀ := by rw [hz]
          _ = a * i₀ * a⁻¹ * i₀⁻¹ * (i₀ * i₀) := by group
          _ = a * i₀ * a⁻¹ * i₀⁻¹ := by rw [hii, mul_one]
      rw [this]
      exact ha
  have hmem : a * i₀ * a⁻¹ ∈ rootSU2 K p f hn2 := by
    rw [← hLeq]
    exact hs₂.mem
  have hci := hs.eq_of_orderOf_eq_two hK hp hmem hord₂
  calc a * i₀ = a * i₀ * a⁻¹ * a := by group
    _ = i₀ * a := by rw [hci]

theorem conj_mem_range_blockEmb (h2 : (2 : K) ≠ 0) {n : ℕ} (hn : 2 ≤ n) {a : Su K p f n}
    (ha : a * rootInvSU K p f hn = rootInvSU K p f hn * a) {y : Su K p f n}
    (hy : y ∈ (blockEmb K p f n (n - 2) 2 (by omega)).range) :
    a * y * a⁻¹ ∈ (blockEmb K p f n (n - 2) 2 (by omega)).range := by
  obtain ⟨B, rfl⟩ := hy
  have h1 := blockEmb_mem_longRootGroupSU_neg (K := K) (p := p) (f := f) hn B
  have hc : suMat a * -negBlock K n 0 = -negBlock K n 0 * suMat a := by
    have := congrArg suMat ha
    rw [suMat_mul, suMat_mul, suMat_rootInvSU] at this
    rw [Matrix.mul_neg, Matrix.neg_mul, this]
  obtain ⟨B', hB'⟩ := exists_blockEmb_of_mem_longRootGroupSU_neg h2 hn
    (conj_mem_longRootGroupSU_of_commute hc h1)
  exact ⟨B', hB'⟩

theorem commute_of_mem_range_blockEmb {n : ℕ} (hn : 2 ≤ n) {y : Su K p f n}
    (hy : y ∈ (blockEmb K p f n (n - 2) 2 (by omega)).range) :
    y * rootInvSU K p f hn = rootInvSU K p f hn * y := by
  obtain ⟨B, rfl⟩ := hy
  exact commute_of_mem_longRootGroupSU_neg (i := rootInvSU K p f hn) (by
    rw [suMat_rootInvSU]
    exact blockEmb_mem_longRootGroupSU_neg hn B)

theorem eq_one_of_mem_range_blockEmb_of_mem_center (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2)
    (hf : 1 ≤ f) {n : ℕ} (hn : 3 ≤ n) {y : Su K p f n}
    (hy : y ∈ (blockEmb K p f n (n - 2) 2 (by omega)).range)
    (hz : y ∈ Subgroup.center (Su K p f n)) : y = 1 := by
  obtain ⟨μ, hμ⟩ := exists_smul_one_of_mem_center hK hp hf hn hz
  obtain ⟨B, rfl⟩ := hy
  have h0 : (0 : ℕ) < n := by omega
  have h := congrFun (congrFun hμ ⟨0, h0⟩) ⟨0, h0⟩
  rw [suMat_blockEmb, blockMat_apply_of_not_mem_left _ (by simp)] at h
  have hμ1 : μ = 1 := by simpa using h.symm
  apply suMat_injective
  rw [hμ, hμ1, one_smul, suMat_one]

theorem isQuasisimple_range_blockEmb (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) {n : ℕ}
    (hn : 5 ≤ n) : CFSG.IsQuasisimple ↥(blockEmb K p f n (n - 2) 2 (by omega)).range :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (MonoidHom.ofInjective (blockEmb_injective (K := K) (p := p) (f := f) (by omega)))
    (isQuasisimple_su hK hp (by omega : 3 ≤ n - 2))

end Component

section Transport

theorem mem_center_of_equiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) {x : A}
    (h : e x ∈ Subgroup.center B) : x ∈ Subgroup.center A := by
  rw [Subgroup.mem_center_iff] at h ⊢
  intro g
  apply e.injective
  rw [map_mul, map_mul]
  exact h (e g)

theorem mem_center_map_equiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) {x : A}
    (h : x ∈ Subgroup.center A) : e x ∈ Subgroup.center B := by
  rw [Subgroup.mem_center_iff] at h ⊢
  intro g
  rw [← e.apply_symm_apply g, ← map_mul, ← map_mul, h (e.symm g)]

end Transport

section Model


open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic

theorem four_data :
    ∃ R₀ ∈ fundamentalSubgroups .PSU (modelUniv .PSU 4 3 1 Nat.prime_three).D,
      ∃ z₀ w₀ : (modelUniv .PSU 4 3 1 Nat.prime_three).K,
        z₀ ∈ R₀ ∧ z₀ * z₀ = 1 ∧ z₀ ≠ 1 ∧ w₀ * z₀ * w₀⁻¹ * z₀⁻¹ ∈ Subgroup.center _ ∧
          ∀ a ∈ R₀, ∀ b ∈ R₀, Commute (w₀ * a * w₀⁻¹) b := by
  have h4 : (2 : ℕ) ≤ 4 := by norm_num
  have hadm : StatedLieAdmissible .PSU 4 3 1 :=
    ⟨Nat.prime_three, le_rfl, by norm_num, fun h => by simpa using congrArg Prod.snd h⟩
  obtain ⟨e, hfund⟩ := RouteD.psu_model_equiv (p := 3) (f := 1) (by norm_num) hadm
  have hK : Nat.card (GaloisField 3 (2 * 1)) = (3 ^ 1) ^ 2 := by
    rw [GaloisField.card 3 (2 * 1) (by norm_num)]
    norm_num
  have hp : (3 : ℕ) ≠ 2 := by norm_num
  obtain ⟨c, hcR, hcz⟩ := exists_swap_four (K := GaloisField 3 (2 * 1)) (p := 3) (f := 1) hK hp
  have hs := isLongRootSU2_standard (K := GaloisField 3 (2 * 1)) (p := 3) (f := 1) h4
  have hord := (hs.isClassicalSL2 hK hp).orderOf_eq_two
  refine ⟨(rootSU2 (GaloisField 3 (2 * 1)) 3 1 h4).comap e.toMonoidHom, ?_,
    e.symm (rootInvSU (GaloisField 3 (2 * 1)) 3 1 h4), e.symm c, ?_, ?_, ?_, ?_, ?_⟩
  · refine (hfund _).mpr ?_
    rw [Subgroup.map_comap_eq_self_of_surjective e.surjective]
    exact ⟨_, hs⟩
  · show e (e.symm (rootInvSU (GaloisField 3 (2 * 1)) 3 1 h4)) ∈
      rootSU2 (GaloisField 3 (2 * 1)) 3 1 h4
    rw [MulEquiv.apply_symm_apply]
    exact rootInvSU_mem_rootSU2 h4
  · apply e.injective
    rw [map_mul, MulEquiv.apply_symm_apply, map_one]
    exact hs.mul_self
  · intro h
    have h' := congrArg e h
    rw [MulEquiv.apply_symm_apply, map_one] at h'
    rw [h', orderOf_one] at hord
    exact absurd hord (by norm_num)
  · apply mem_center_of_equiv e
    simpa only [map_mul, map_inv, MulEquiv.apply_symm_apply] using hcz
  · intro a ha b hb
    have ha' : e a ∈ rootSU2 (GaloisField 3 (2 * 1)) 3 1 h4 := ha
    obtain ⟨A, hA⟩ := MonoidHom.mem_range.mp (show e b ∈ rootSU2 (GaloisField 3 (2 * 1)) 3 1 h4
      from hb)
    have hca : c * e a * c⁻¹ ∈
        (blockEmb (GaloisField 3 (2 * 1)) 3 1 4 2 2 (by norm_num)).range := by
      rw [← hcR]
      exact ⟨e a, ha', rfl⟩
    obtain ⟨B, hB⟩ := hca
    apply e.injective
    show e (e.symm c * a * (e.symm c)⁻¹ * b) = e (b * (e.symm c * a * (e.symm c)⁻¹))
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
    rw [← hA, ← hB]
    exact (comm_blocks_four A B).symm

theorem comp_data (n : ℕ) (hn : 5 ≤ n) :
    ∃ R₀ ∈ fundamentalSubgroups .PSU (modelUniv .PSU n 3 1 Nat.prime_three).D,
      ∃ z₀ : (modelUniv .PSU n 3 1 Nat.prime_three).K, z₀ ∈ R₀ ∧ z₀ * z₀ = 1 ∧ z₀ ≠ 1 ∧
        ∃ E₀ : Subgroup (modelUniv .PSU n 3 1 Nat.prime_three).K,
          (∀ y ∈ E₀, y * z₀ = z₀ * y) ∧
          (∀ a, a * z₀ * a⁻¹ * z₀⁻¹ ∈ Subgroup.center _ → ∀ y ∈ E₀, a * y * a⁻¹ ∈ E₀) ∧
          CFSG.IsQuasisimple ↥E₀ ∧ ∀ y ∈ E₀, y ∈ Subgroup.center _ → y = 1 := by
  have hn2 : 2 ≤ n := by omega
  have hn3 : 3 ≤ n := by omega
  have hn4 : n ≠ 4 := by omega
  have hadm : StatedLieAdmissible .PSU n 3 1 :=
    ⟨Nat.prime_three, le_rfl, hn3, fun h => by simpa using congrArg Prod.snd h⟩
  obtain ⟨e, hfund⟩ := RouteD.psu_model_equiv (p := 3) (f := 1) (by norm_num) hadm
  have hK : Nat.card (GaloisField 3 (2 * 1)) = (3 ^ 1) ^ 2 := by
    rw [GaloisField.card 3 (2 * 1) (by norm_num)]
    norm_num
  have hp : (3 : ℕ) ≠ 2 := by norm_num
  have h2 : (2 : GaloisField 3 (2 * 1)) ≠ 0 := two_ne_zero_of_charP_ne_two hp
  have hs := isLongRootSU2_standard (K := GaloisField 3 (2 * 1)) (p := 3) (f := 1) hn2
  have hord := (hs.isClassicalSL2 hK hp).orderOf_eq_two
  have hmemE : ∀ {y : (modelUniv .PSU n 3 1 Nat.prime_three).K},
      y ∈ (blockEmb (GaloisField 3 (2 * 1)) 3 1 n (n - 2) 2 (by omega)).range.map
        e.symm.toMonoidHom →
      e y ∈ (blockEmb (GaloisField 3 (2 * 1)) 3 1 n (n - 2) 2 (by omega)).range := by
    intro y hy
    simpa using Subgroup.mem_map_equiv.mp hy
  refine ⟨(rootSU2 (GaloisField 3 (2 * 1)) 3 1 hn2).comap e.toMonoidHom, ?_,
    e.symm (rootInvSU (GaloisField 3 (2 * 1)) 3 1 hn2), ?_, ?_, ?_,
    (blockEmb (GaloisField 3 (2 * 1)) 3 1 n (n - 2) 2 (by omega)).range.map e.symm.toMonoidHom,
    ?_, ?_, ?_, ?_⟩
  · refine (hfund _).mpr ?_
    rw [Subgroup.map_comap_eq_self_of_surjective e.surjective]
    exact ⟨_, hs⟩
  · show e (e.symm (rootInvSU (GaloisField 3 (2 * 1)) 3 1 hn2)) ∈
      rootSU2 (GaloisField 3 (2 * 1)) 3 1 hn2
    rw [MulEquiv.apply_symm_apply]
    exact rootInvSU_mem_rootSU2 hn2
  · apply e.injective
    rw [map_mul, MulEquiv.apply_symm_apply, map_one]
    exact hs.mul_self
  · intro h
    have h' := congrArg e h
    rw [MulEquiv.apply_symm_apply, map_one] at h'
    rw [h', orderOf_one] at hord
    exact absurd hord (by norm_num)
  · intro y hy
    apply e.injective
    simp only [map_mul, MulEquiv.apply_symm_apply]
    exact commute_of_mem_range_blockEmb hn2 (hmemE hy)
  · intro a ha y hy
    have ha' : e a * rootInvSU (GaloisField 3 (2 * 1)) 3 1 hn2 * (e a)⁻¹ *
        (rootInvSU (GaloisField 3 (2 * 1)) 3 1 hn2)⁻¹ ∈ Subgroup.center _ := by
      simpa only [map_mul, map_inv, MulEquiv.apply_symm_apply] using mem_center_map_equiv e ha
    have := conj_mem_range_blockEmb h2 hn2
      (commute_of_central_ratio hK hp le_rfl hn2 hn3 hn4 ha') (hmemE hy)
    exact Subgroup.mem_map_equiv.mpr (by simpa using this)
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Subgroup.equivMapOfInjective _ e.symm.toMonoidHom e.symm.injective)
      (isQuasisimple_range_blockEmb hK hp hn)
  · intro y hy hz
    have := eq_one_of_mem_range_blockEmb_of_mem_center hK hp le_rfl hn3 (hmemE hy)
      (mem_center_map_equiv e hz)
    exact e.injective (this.trans (map_one e).symm)

end Model

end CFSG.CGT.PushingUpLit.SolKNA.LTSU
