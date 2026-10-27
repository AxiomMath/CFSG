module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDesc2LinRes
public import CFSG.Quasithin.EmptyFaithful.R3c21Aux
public import CFSG.HardMathSupport.Solomon.Coordinator.FixSubgroupInf
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherLinearAutNormal
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HDescLinRes

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie
open Polynomial Module Matrix
open CFSG.RankThree.PartOne.CTP CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)

section LinearPart

variable {k : Type} [Field k]

theorem exists_common_eigvec_of_mul_self_eq_one [CharP k 2] {U : GL (Fin 3) k} (hU : U ≠ 1)
    (hU2 : U * U = 1) :
    ∃ v : Fin 3 → k, v ≠ 0 ∧ ∀ M : GL (Fin 3) k, M * U = U * M →
      ∃ c : k, c ≠ 0 ∧ (M : Matrix (Fin 3) (Fin 3) k) *ᵥ v = c • v := by
  classical
  set N : Matrix (Fin 3) (Fin 3) k := (U : Matrix (Fin 3) (Fin 3) k) - 1 with hN
  have hN0 : Matrix.toLin' N ≠ 0 := by
    intro h
    apply hU
    have : N = 0 := Matrix.toLin'.injective (by rw [h, map_zero])
    exact Units.ext (sub_eq_zero.1 this)
  have h2 : (2 : k) = 0 := CharP.cast_eq_zero k 2
  have h2M : (2 : Matrix (Fin 3) (Fin 3) k) = 0 := by
    rw [← map_ofNat (Matrix.scalar (Fin 3)) 2, h2, map_zero]
  have hU2' : (U : Matrix (Fin 3) (Fin 3) k) * U = 1 := by
    rw [← Units.val_mul, hU2, Units.val_one]
  have hNN : N * N = 0 := by
    have : N * N = (U : Matrix (Fin 3) (Fin 3) k) * U - 1 - 2 * N := by
      rw [hN]
      noncomm_ring
    rw [this, h2M, zero_mul, sub_zero, hU2', sub_self]
  have hN2 : Matrix.toLin' N * Matrix.toLin' N = 0 := by
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hNN, map_zero]
  have hR1 := finrank_range_eq_one_of_mul_self_eq_zero (Module.finrank_fin_fun k) hN0 hN2
  obtain ⟨⟨v, hvR⟩, hv0, hall⟩ := finrank_eq_one_iff'.1 hR1
  have hv0' : v ≠ 0 := fun h => hv0 (Subtype.ext h)
  refine ⟨v, hv0', fun M hMU => ?_⟩
  have hMN : (M : Matrix (Fin 3) (Fin 3) k) * N = N * M := by
    rw [hN, mul_sub, sub_mul, mul_one, one_mul, ← Units.val_mul, hMU, Units.val_mul]
  have hMvR : (M : Matrix (Fin 3) (Fin 3) k) *ᵥ v ∈ LinearMap.range (Matrix.toLin' N) := by
    obtain ⟨w, hw⟩ := hvR
    refine ⟨(M : Matrix (Fin 3) (Fin 3) k) *ᵥ w, ?_⟩
    rw [Matrix.toLin'_apply] at hw ⊢
    rw [← hw, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hMN]
  obtain ⟨c, hc⟩ := hall ⟨_, hMvR⟩
  have hc' : (M : Matrix (Fin 3) (Fin 3) k) *ᵥ v = c • v := (congrArg Subtype.val hc).symm
  refine ⟨c, ?_, hc'⟩
  rintro rfl
  rw [zero_smul] at hc'
  apply hv0'
  have : ((M⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *ᵥ
      ((M : Matrix (Fin 3) (Fin 3) k) *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  rw [← this, hc', Matrix.mulVec_zero]

theorem commute_of_commutator_eq_scalar [CharP k 2] {U A B : GL (Fin 3) k} (hU : U ≠ 1)
    (hU2 : U * U = 1) (hAU : A * U = U * A) (hBU : B * U = U * B) {z : kˣ}
    (hz : A * B * A⁻¹ * B⁻¹ = GeneralLinearGroup.scalar (Fin 3) z) : A * B = B * A := by
  obtain ⟨v, hv0, hv⟩ := exists_common_eigvec_of_mul_self_eq_one hU hU2
  obtain ⟨α, hα0, hα⟩ := hv A hAU
  obtain ⟨β, hβ0, hβ⟩ := hv B hBU
  have hAB : A * B = GeneralLinearGroup.scalar (Fin 3) z * (B * A) := by
    rw [← hz]
    group
  have h1 : ((A * B : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *ᵥ v = (α * β) • v := by
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hβ, Matrix.mulVec_smul, hα, smul_smul, mul_comm]
  have h2 : ((A * B : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *ᵥ v = ((z : k) * (α * β)) • v := by
    rw [hAB, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hα,
      Matrix.mulVec_smul, hβ, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal, Matrix.smul_mulVec, Matrix.one_mulVec, smul_smul, smul_smul]
    congr 1
    ring
  have hz1 : (z : k) = 1 := by
    rw [h1] at h2
    have h0 : ((α * β) - (z : k) * (α * β)) • v = 0 := by rw [sub_smul, h2, sub_self]
    rcases smul_eq_zero.1 h0 with h | h
    · have hab : α * β ≠ 0 := mul_ne_zero hα0 hβ0
      have : (1 - (z : k)) * (α * β) = 0 := by rw [sub_mul, one_mul]; exact h
      rcases mul_eq_zero.1 this with h' | h'
      · exact (sub_eq_zero.1 h').symm
      · exact absurd h' hab
    · exact absurd h hv0
  have hz1' : z = 1 := Units.ext hz1
  rw [hAB, hz1', map_one, one_mul]

theorem exists_third_index {i j : Fin 3} (hij : i ≠ j) :
    ∃ l : Fin 3, l ≠ i ∧ l ≠ j ∧ ∀ t : Fin 3, t = i ∨ t = j ∨ t = l := by
  revert i j
  decide

theorem eq_one_of_commute_two_diagonal_of_mul_self_eq_one [CharP k 2] {n : ℕ} {a b : Fin n → k}
    (hab : ∀ i j, i ≠ j → a i ≠ a j ∨ b i ≠ b j) {U : Matrix (Fin n) (Fin n) k}
    (hUa : diagonal a * U = U * diagonal a) (hUb : diagonal b * U = U * diagonal b)
    (hU2 : U * U = 1) : U = 1 := by
  have hoff : ∀ i j, i ≠ j → U i j = 0 := by
    intro i j hij
    have hcomm : ∀ d : Fin n → k, diagonal d * U = U * diagonal d → (d i - d j) * U i j = 0 := by
      intro d hd
      have h := congrFun (congrFun hd i) j
      rw [diagonal_mul, mul_diagonal] at h
      rw [sub_mul, h, mul_comm (d j)]
      exact sub_self _
    rcases hab i j hij with h | h
    · rcases mul_eq_zero.1 (hcomm a hUa) with h1 | h1
      · exact absurd (sub_eq_zero.1 h1) h
      · exact h1
    · rcases mul_eq_zero.1 (hcomm b hUb) with h1 | h1
      · exact absurd (sub_eq_zero.1 h1) h
      · exact h1
  have hdiag : U = diagonal (fun i => U i i) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      rw [diagonal_apply_eq]
    · rw [diagonal_apply_ne _ hij, hoff i j hij]
  have hii : ∀ i, U i i = 1 := by
    intro i
    have h := congrFun (congrFun hU2 i) i
    rw [hdiag, diagonal_mul_diagonal, diagonal_apply_eq, one_apply_eq] at h
    have h2 : (2 : k) = 0 := CharP.cast_eq_zero k 2
    have h3 : (U i i - 1) * (U i i - 1) = 0 := by linear_combination h + (1 - U i i) * h2
    exact sub_eq_zero.1 (mul_self_eq_zero.1 h3)
  rw [hdiag]
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [diagonal_apply_eq, hii, one_apply_eq]
  · rw [diagonal_apply_ne _ hij, one_apply_ne hij]

theorem exists_pow_of_diag_eq {a b : Fin 3 → k} {i j : Fin 3} (hij : i ≠ j) (haij : a i = a j)
    (hbij : b i = b j) (ha3 : ∀ t, a t ^ 3 = 1) (hb3 : ∀ t, b t ^ 3 = 1) (hnc : ∃ t, a t ≠ a i) :
    ∃ (m : ℕ) (s : k), s ≠ 0 ∧ ∀ t, b t = s * a t ^ m := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨l, hli, hlj, hcov⟩ := exists_third_index hij
  have hne0 : ∀ {x : k}, x ^ 3 = 1 → x ≠ 0 := fun hx h => by
    rw [h] at hx
    norm_num at hx
  have hai0 := hne0 (ha3 i)
  have hbi0 := hne0 (hb3 i)
  have hal : a l ≠ a i := by
    obtain ⟨t, ht⟩ := hnc
    rcases hcov t with rfl | rfl | rfl
    · exact absurd rfl ht
    · exact absurd haij.symm ht
    · exact ht
  set r : k := a l / a i with hr
  have hr3 : r ^ 3 = 1 := by rw [hr, div_pow, ha3, ha3, div_one]
  have hr1 : r ≠ 1 := by
    rw [hr, Ne, div_eq_one_iff_eq hai0]
    exact hal
  have hrprim : IsPrimitiveRoot r 3 := by
    rw [IsPrimitiveRoot.iff_orderOf]
    exact orderOf_eq_prime hr3 hr1
  have hb3' : (b l / b i) ^ 3 = 1 := by rw [div_pow, hb3, hb3, div_one]
  obtain ⟨m, -, hm⟩ := hrprim.eq_pow_of_pow_eq_one hb3'
  refine ⟨m, b i / a i ^ m, div_ne_zero hbi0 (pow_ne_zero _ hai0), fun t => ?_⟩
  rcases hcov t with rfl | rfl | rfl
  · field_simp
  · rw [← haij, ← hbij]
    field_simp
  · have : b t = b i * r ^ m := by
      rw [hm]
      field_simp
    rw [this, hr, div_pow]
    field_simp

theorem eq_scalar_of_conj_eq_scalar {P A : GL (Fin 3) k} {c : kˣ}
    (h : P * A * P⁻¹ = GeneralLinearGroup.scalar (Fin 3) c) :
    A = GeneralLinearGroup.scalar (Fin 3) c := by
  calc A = P⁻¹ * (P * A * P⁻¹) * P := by group
    _ = P⁻¹ * (GeneralLinearGroup.scalar (Fin 3) c * P) := by rw [h, mul_assoc]
    _ = GeneralLinearGroup.scalar (Fin 3) c := by
        rw [GeneralLinearGroup.scalar_commute c P, ← mul_assoc, inv_mul_cancel, one_mul]

theorem card_le_three_of_le_linearAutGroup [Finite k] [CharP k 2] (h3 : 3 ∣ Nat.card k - 1)
    {E : Subgroup (MulAut (projectiveSL 3 k))} (hE : IsElemAbelian 3 E)
    (hEl : E ≤ linearAutGroup 3 k) {t : projectiveSL 3 k} (ht : orderOf t = 2)
    (hfix : ∀ e ∈ E, e t = t) : Nat.card E ≤ 3 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hlt
  push Not at hlt
  have hpE : IsPGroup 3 E := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hE.2 g g.2)⟩
  obtain ⟨n, hn⟩ := hpE.exists_card_eq
  have h9 : 3 ^ 2 ≤ Nat.card E := by
    rw [hn] at hlt ⊢
    have h1 : 1 < n := by
      by_contra h
      push Not at h
      interval_cases n <;> simp at hlt
    exact Nat.pow_le_pow_right (by norm_num) h1
  obtain ⟨D, hDE, hD9⟩ := CFSG.LocalAnalysis.GLTheoremA.exists_sub_card_pow Nat.prime_three hE h9
  have hD : IsElemAbelian 3 D :=
    ⟨⟨⟨fun x y => Subtype.ext (show (x : MulAut (projectiveSL 3 k)) * y = y * x from
      congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hDE x.2⟩ ⟨y, hDE y.2⟩))⟩⟩,
      fun x hx => hE.2 x (hDE hx)⟩
  obtain ⟨A, B, hA, hB, hA1, hBA, ⟨a, ha⟩, ⟨b, hb⟩, z, -, hz⟩ :=
    exists_lifts_of_le_linearAutGroup Nat.prime_three (by norm_num) hD hD9 (hDE.trans hEl)
  have ht2 : t ^ 2 = 1 := by
    rw [← ht]
    exact pow_orderOf_eq_one t
  obtain ⟨U, hUt, hU2⟩ := exists_lift_of_sq_eq_one ht2
  set u := Matrix.SpecialLinearGroup.toGL U with hu
  have hu1 : u ≠ 1 := by
    intro h
    have hU : U = 1 := Matrix.SpecialLinearGroup.toGL_injective (by rw [← hu, h, map_one])
    rw [hU, map_one] at hUt
    rw [← hUt, orderOf_one] at ht
    exact absurd ht (by norm_num)
  have hu2 : u * u = 1 := by
    rw [hu, ← map_mul, ← sq, hU2, map_one]
  have hAU : A * u = u * A := mul_comm_of_conjAut_proj_eq hU2 (by rw [hUt]; exact hfix _ (hDE hA))
  have hBU : B * u = u * B := mul_comm_of_conjAut_proj_eq hU2 (by rw [hUt]; exact hfix _ (hDE hB))
  have hAB : A * B = B * A := commute_of_commutator_eq_scalar hu1 hu2 hAU hBU hz
  obtain ⟨μ, hμ⟩ := exists_cube_root_of_commute ha hu1 hu2 hAU
  obtain ⟨ν, hν⟩ := exists_cube_root_of_commute hb hu1 hu2 hBU
  set A' := GeneralLinearGroup.scalar (Fin 3) μ⁻¹ * A with hA'
  set B' := GeneralLinearGroup.scalar (Fin 3) ν⁻¹ * B with hB'
  have hA'3 : A' ^ 3 = 1 := by
    rw [hA', scalar_mul_pow, ha, ← map_mul, inv_pow, hμ, inv_mul_cancel, map_one]
  have hB'3 : B' ^ 3 = 1 := by
    rw [hB', scalar_mul_pow, hb, ← map_mul, inv_pow, hν, inv_mul_cancel, map_one]
  have hsc : ∀ (c : kˣ) (g : GL (Fin 3) k),
      GeneralLinearGroup.scalar (Fin 3) c * g = g * GeneralLinearGroup.scalar (Fin 3) c :=
    fun c g => GeneralLinearGroup.scalar_commute c g
  have hA'B' : A' * B' = B' * A' := by
    rw [hA', hB']
    calc GeneralLinearGroup.scalar (Fin 3) μ⁻¹ * A * (GeneralLinearGroup.scalar (Fin 3) ν⁻¹ * B)
        = GeneralLinearGroup.scalar (Fin 3) μ⁻¹ * GeneralLinearGroup.scalar (Fin 3) ν⁻¹ *
            (A * B) := by rw [mul_assoc, ← mul_assoc A, ← hsc ν⁻¹ A]; group
      _ = GeneralLinearGroup.scalar (Fin 3) ν⁻¹ * GeneralLinearGroup.scalar (Fin 3) μ⁻¹ *
            (B * A) := by rw [hAB, hsc μ⁻¹]
      _ = GeneralLinearGroup.scalar (Fin 3) ν⁻¹ * B * (GeneralLinearGroup.scalar (Fin 3) μ⁻¹ * A) := by
          rw [mul_assoc (GeneralLinearGroup.scalar (Fin 3) ν⁻¹) B, ← mul_assoc B, ← hsc μ⁻¹ B]
          group
  have hA'U : A' * u = u * A' := by
    rw [hA', mul_assoc, hAU, ← mul_assoc, ← mul_assoc, hsc μ⁻¹ u]
  have hB'U : B' * u = u * B' := by
    rw [hB', mul_assoc, hBU, ← mul_assoc, ← mul_assoc, hsc ν⁻¹ u]
  set s : Set (GL (Fin 3) k) := {A', B'} with hs
  have hss : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x := by
    intro x hx y hy
    rw [hs, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · rfl
    · exact hA'B'
    · exact hA'B'.symm
    · rfl
  have hcomm : ∀ x ∈ Subgroup.closure s, ∀ y ∈ Subgroup.closure s, x * y = y * x := by
    intro x hx y hy
    letI := Subgroup.closureCommGroupOfComm (k := s) (fun x hx y hy _ => hss x hx y hy)
    exact congrArg Subtype.val (mul_comm (⟨x, hx⟩ : Subgroup.closure s) ⟨y, hy⟩)
  have hexp : ∀ x ∈ Subgroup.closure s, x ^ 3 = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rw [hs, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact hA'3
      · exact hB'3
    | one => exact one_pow 3
    | mul x y hx hy ihx ihy => rw [(Commute.mul_pow (hcomm x hx y hy) 3), ihx, ihy, one_mul]
    | inv x hx ih => rw [inv_pow, ih, inv_one]
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_of_dvd Nat.prime_three h3
  obtain ⟨P, hP⟩ := exists_conj_diagonal_of_exponent_prime (n := 3) (p := 3) ⟨ζ, hζ⟩
    (Subgroup.closure s) hcomm hexp
  have hPA := hP A' (Subgroup.subset_closure (by rw [hs]; exact Set.mem_insert _ _))
  have hPB := hP B' (Subgroup.subset_closure (by rw [hs]; exact Set.mem_insert_of_mem _ rfl))
  set da : Fin 3 → k := fun l => ((P * A' * P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) l l
    with hdadef
  set db : Fin 3 → k := fun l => ((P * B' * P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) l l
    with hdbdef
  have hda : ((P * A' * P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) = diagonal da :=
    glConj_eq_diagonal hPA
  have hdb : ((P * B' * P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) = diagonal db :=
    glConj_eq_diagonal hPB
  have hcube : ∀ {X : GL (Fin 3) k} {d : Fin 3 → k}, X ^ 3 = 1 →
      ((P * X * P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) = diagonal d → ∀ l, d l ^ 3 = 1 := by
    intro X d hX hd l
    have h1 : (P * X * P⁻¹ : GL (Fin 3) k) ^ 3 = 1 := by rw [conj_pow, hX]; group
    have h2 := congrArg (fun g : GL (Fin 3) k => (g : Matrix (Fin 3) (Fin 3) k) l l) h1
    simp only [Units.val_pow_eq_pow_val, hd, diagonal_pow, diagonal_apply_eq, Units.val_one,
      one_apply_eq] at h2
    exact h2
  have hda3 := hcube hA'3 hda
  have hdb3 := hcube hB'3 hdb
  set W := P * u * P⁻¹ with hW
  have hWcomm : ∀ {X : GL (Fin 3) k} {d : Fin 3 → k}, X * u = u * X →
      ((P * X * P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) = diagonal d →
      diagonal d * (W : Matrix (Fin 3) (Fin 3) k) = (W : Matrix (Fin 3) (Fin 3) k) * diagonal d := by
    intro X d hXu hd
    rw [← hd, ← Units.val_mul, ← Units.val_mul]
    congr 1
    rw [hW]
    calc P * X * P⁻¹ * (P * u * P⁻¹) = P * (X * u) * P⁻¹ := by group
      _ = P * (u * X) * P⁻¹ := by rw [hXu]
      _ = P * u * P⁻¹ * (P * X * P⁻¹) := by group
  have hW2 : (W : Matrix (Fin 3) (Fin 3) k) * W = 1 := by
    rw [← Units.val_mul]
    have : W * W = 1 := by
      rw [hW]
      calc P * u * P⁻¹ * (P * u * P⁻¹) = P * (u * u) * P⁻¹ := by group
        _ = 1 := by rw [hu2]; group
    rw [this, Units.val_one]
  by_cases hjoint : ∀ i j, i ≠ j → da i ≠ da j ∨ db i ≠ db j
  · apply hu1
    have h1 := eq_one_of_commute_two_diagonal_of_mul_self_eq_one hjoint (hWcomm hA'U hda)
      (hWcomm hB'U hdb) hW2
    have h1' : W = 1 := Units.ext h1
    calc u = P⁻¹ * W * P := by rw [hW]; group
      _ = 1 := by rw [h1']; group
  · push Not at hjoint
    obtain ⟨i, j, hij, hai, hbi⟩ := hjoint
    have hconjA : LinearFlag.conjAut 3 k A' = LinearFlag.conjAut 3 k A := by
      rw [hA', conjAut_scalar_mul]
    have hconjB : LinearFlag.conjAut 3 k B' = LinearFlag.conjAut 3 k B := by
      rw [hB', conjAut_scalar_mul]
    have hnc : ∃ l, da l ≠ da i := by
      by_contra hc
      push Not at hc
      apply hA1
      have hai0 : da i ≠ 0 := by
        intro h0
        have := hda3 i
        rw [h0] at this
        norm_num at this
      have hsc' : P * A' * P⁻¹ = GeneralLinearGroup.scalar (Fin 3) (Units.mk0 (da i) hai0) := by
        apply Units.ext
        rw [hda, GeneralLinearGroup.coe_scalar, Units.val_mk0, Matrix.scalar_apply]
        congr 1
        funext l
        exact hc l
      rw [← hconjA, eq_scalar_of_conj_eq_scalar hsc', LinearFlag.conjAut_scalar]
    obtain ⟨m, c, hc0, hbm⟩ := exists_pow_of_diag_eq hij hai hbi hda3 hdb3 hnc
    apply hBA
    have hPB' : P * B' * P⁻¹ =
        GeneralLinearGroup.scalar (Fin 3) (Units.mk0 c hc0) * (P * A' * P⁻¹) ^ m := by
      apply Units.ext
      rw [hdb, Units.val_mul, GeneralLinearGroup.coe_scalar, Units.val_pow_eq_pow_val, hda,
        diagonal_pow, Units.val_mk0, Matrix.scalar_apply, diagonal_mul_diagonal]
      congr 1
      funext l
      rw [hbm l]
      rfl
    have hB'eq : B' = GeneralLinearGroup.scalar (Fin 3) (Units.mk0 c hc0) * A' ^ m := by
      have h1 : P * B' * P⁻¹ = P * (GeneralLinearGroup.scalar (Fin 3) (Units.mk0 c hc0) * A' ^ m) *
          P⁻¹ := by
        rw [hPB', conj_pow]
        calc GeneralLinearGroup.scalar (Fin 3) (Units.mk0 c hc0) * (P * A' ^ m * P⁻¹)
            = (GeneralLinearGroup.scalar (Fin 3) (Units.mk0 c hc0) * P) * A' ^ m * P⁻¹ := by group
          _ = (P * GeneralLinearGroup.scalar (Fin 3) (Units.mk0 c hc0)) * A' ^ m * P⁻¹ := by
              rw [hsc]
          _ = P * (GeneralLinearGroup.scalar (Fin 3) (Units.mk0 c hc0) * A' ^ m) * P⁻¹ := by group
      have h2 := congrArg (fun g => P⁻¹ * g * P) h1
      simpa [mul_assoc] using h2
    rw [← hconjB, hB'eq, conjAut_scalar_mul, map_pow, hconjA]
    exact Subgroup.npow_mem_zpowers _ m

end LinearPart

section Block

variable {R : Type*} [CommRing R]

@[expose] def blkMat (g : Matrix (Fin 2) (Fin 2) R) : Matrix (Fin 3) (Fin 3) R :=
  !![g 0 0, g 0 1, 0; g 1 0, g 1 1, 0; 0, 0, 1]

theorem blkMat_mul (g h : Matrix (Fin 2) (Fin 2) R) : blkMat (g * h) = blkMat g * blkMat h := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blkMat, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]

theorem blkMat_one : blkMat (1 : Matrix (Fin 2) (Fin 2) R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blkMat]

theorem det_blkMat (g : Matrix (Fin 2) (Fin 2) R) : (blkMat g).det = g.det := by
  simp [blkMat, Matrix.det_fin_three, Matrix.det_fin_two]

@[expose] def slBlk :
    Matrix.SpecialLinearGroup (Fin 2) R →* Matrix.SpecialLinearGroup (Fin 3) R where
  toFun g := ⟨blkMat (g : Matrix (Fin 2) (Fin 2) R), by rw [det_blkMat]; exact g.2⟩
  map_one' := Subtype.ext (by
    show blkMat ((1 : Matrix.SpecialLinearGroup (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) = 1
    rw [Matrix.SpecialLinearGroup.coe_one, blkMat_one])
  map_mul' g h := Subtype.ext (by
    show blkMat ((g * h : Matrix.SpecialLinearGroup (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) =
      blkMat (g : Matrix (Fin 2) (Fin 2) R) * blkMat (h : Matrix (Fin 2) (Fin 2) R)
    rw [Matrix.SpecialLinearGroup.coe_mul, blkMat_mul])

theorem coe_slBlk (g : Matrix.SpecialLinearGroup (Fin 2) R) :
    ((slBlk g : Matrix.SpecialLinearGroup (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) =
      blkMat (g : Matrix (Fin 2) (Fin 2) R) := rfl

end Block

section Core

variable {k : Type} [Field k]

theorem mul_apply_two_two {P Q : Matrix (Fin 3) (Fin 3) k} (h0 : P 2 0 = 0) (h1 : P 2 1 = 0) :
    (P * Q) 2 2 = P 2 2 * Q 2 2 := by
  rw [Matrix.mul_apply, Fin.sum_univ_three, h0, h1, zero_mul, zero_mul, zero_add, zero_add]

theorem eq_zero_of_diagonal_commute {d : Fin 3 → k} {Y : Matrix (Fin 3) (Fin 3) k}
    (hY : diagonal d * Y = Y * diagonal d) {i j : Fin 3} (hij : d i ≠ d j) : Y i j = 0 := by
  have h := congrFun (congrFun hY i) j
  rw [diagonal_mul, mul_diagonal] at h
  have h' : (d i - d j) * Y i j = 0 := by
    rw [sub_mul, h, mul_comm (d j)]
    exact sub_self _
  exact (mul_eq_zero.1 h').resolve_left (sub_ne_zero.2 hij)

theorem diagonal_mul_blkMat {d : Fin 3 → k} (hd01 : d 0 = d 1) (g : Matrix (Fin 2) (Fin 2) k) :
    diagonal d * blkMat g = blkMat g * diagonal d := by
  ext i j
  rw [diagonal_mul, mul_diagonal]
  fin_cases i <;> fin_cases j <;> simp [blkMat, hd01, mul_comm]

theorem commute_of_conjAut_fix_diag [CharP k 2] {X : GL (Fin 3) k} {d : Fin 3 → k}
    (hX : (X : Matrix (Fin 3) (Fin 3) k) = diagonal d) (hd01 : d 0 = d 1)
    {Y : Matrix.SpecialLinearGroup (Fin 3) k}
    (hfix : LinearFlag.conjAut 3 k X (proj 3 k Y) = proj 3 k Y) :
    X * Matrix.SpecialLinearGroup.toGL Y = Matrix.SpecialLinearGroup.toGL Y * X := by
  rw [conjAut_proj, proj_eq_proj_iff] at hfix
  obtain ⟨c, -, hc⟩ := mem_scalars.1 hfix
  set W := CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 k X Y with hW
  have hWm : Matrix.SpecialLinearGroup.toGL W = X * Matrix.SpecialLinearGroup.toGL Y * X⁻¹ := by
    apply Units.ext
    rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hW, coe_slConjugation, Units.val_mul,
      Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
  have hWU : Matrix.SpecialLinearGroup.toGL (W⁻¹ * Y) = GeneralLinearGroup.scalar (Fin 3) c := by
    apply Units.ext
    rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hc, GeneralLinearGroup.coe_scalar]
  set u := Matrix.SpecialLinearGroup.toGL Y with hu
  set s := GeneralLinearGroup.scalar (Fin 3) c with hs
  have hUWs : u = X * u * X⁻¹ * s := by
    rw [← hWU, map_mul, map_inv, ← hWm, mul_inv_cancel_left]
  have hsc : ∀ g : GL (Fin 3) k, s * g = g * s := fun g => GeneralLinearGroup.scalar_commute c g
  have hXu : X = u⁻¹ * X * u * s := by
    calc X = u⁻¹ * (u * X) := by group
      _ = u⁻¹ * (X * u * X⁻¹ * s * X) := by rw [← hUWs]
      _ = u⁻¹ * (X * u * (X⁻¹ * (s * X))) := by group
      _ = u⁻¹ * (X * u * (X⁻¹ * (X * s))) := by rw [hsc X]
      _ = u⁻¹ * X * u * s := by group
  have h2 : (2 : k) = 0 := CharP.cast_eq_zero k 2
  have htrX : Matrix.trace (X : Matrix (Fin 3) (Fin 3) k) = d 2 := by
    rw [hX, Matrix.trace_diagonal, Fin.sum_univ_three, ← hd01]
    linear_combination d 0 * h2
  have hd2 : d 2 ≠ 0 := by
    intro h0
    have hdet : (X : Matrix (Fin 3) (Fin 3) k).det ≠ 0 :=
      ((Matrix.isUnit_iff_isUnit_det _).1 X.isUnit).ne_zero
    apply hdet
    rw [hX, Matrix.det_diagonal, Fin.prod_univ_three, h0, mul_zero]
  have htr := congrArg (fun g : GL (Fin 3) k => Matrix.trace (g : Matrix (Fin 3) (Fin 3) k)) hXu
  simp only [Units.val_mul, hs, GeneralLinearGroup.coe_scalar] at htr
  rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one,
    Matrix.trace_smul, Matrix.trace_units_conj', htrX, smul_eq_mul] at htr
  have hc1 : (c : k) = 1 := by
    have : (1 - (c : k)) * d 2 = 0 := by rw [sub_mul, one_mul, ← htr, sub_self]
    exact (sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hd2)).symm
  have hs1 : s = 1 := by rw [hs, show c = 1 from Units.ext hc1, map_one]
  rw [hs1, mul_one] at hXu
  calc X * u = u * (u⁻¹ * X * u) := by group
    _ = u * X := by rw [← hXu]

theorem map_slBlk_map_subtype {σ : k ≃+* k} {k₀ : Subfield k} (hσ : ∀ c ∈ k₀, σ c = c)
    (g : Matrix.SpecialLinearGroup (Fin 2) k₀) :
    Matrix.SpecialLinearGroup.map σ.toRingHom
        (slBlk (Matrix.SpecialLinearGroup.map k₀.subtype g)) =
      slBlk (Matrix.SpecialLinearGroup.map k₀.subtype g) := by
  have hσ' : ∀ x : k₀, σ (x : k) = x := fun x => hσ x x.2
  ext i j
  rw [Matrix.SpecialLinearGroup.map_apply_coe, coe_slBlk, RingHom.mapMatrix_apply,
    Matrix.map_apply]
  fin_cases i <;> fin_cases j <;>
    simp [blkMat, Matrix.SpecialLinearGroup.map_apply_coe, hσ']

theorem exists_slBlk_eq {k₀ : Subfield k} {Z : Matrix.SpecialLinearGroup (Fin 3) k}
    (hmem : ∀ i j, (Z : Matrix (Fin 3) (Fin 3) k) i j ∈ k₀)
    (h02 : (Z : Matrix (Fin 3) (Fin 3) k) 0 2 = 0) (h12 : (Z : Matrix (Fin 3) (Fin 3) k) 1 2 = 0)
    (h20 : (Z : Matrix (Fin 3) (Fin 3) k) 2 0 = 0) (h21 : (Z : Matrix (Fin 3) (Fin 3) k) 2 1 = 0)
    (h22 : (Z : Matrix (Fin 3) (Fin 3) k) 2 2 = 1) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 2) k₀,
      slBlk (Matrix.SpecialLinearGroup.map k₀.subtype g) = Z := by
  let gm : Matrix (Fin 2) (Fin 2) k₀ :=
    !![⟨Z.1 0 0, hmem 0 0⟩, ⟨Z.1 0 1, hmem 0 1⟩; ⟨Z.1 1 0, hmem 1 0⟩, ⟨Z.1 1 1, hmem 1 1⟩]
  have hdet : gm.det = 1 := by
    apply k₀.subtype.injective
    rw [map_one, RingHom.map_det, Matrix.det_fin_two]
    have hZ : (Z : Matrix (Fin 3) (Fin 3) k).det = 1 := Z.2
    rw [Matrix.det_fin_three, h02, h12, h20, h21, h22] at hZ
    simp [gm]
    linear_combination hZ
  let g₀ : Matrix.SpecialLinearGroup (Fin 2) k₀ := ⟨gm, hdet⟩
  have hg₀ : (g₀ : Matrix (Fin 2) (Fin 2) k₀) = gm := rfl
  refine ⟨g₀, ?_⟩
  ext i j
  rw [coe_slBlk, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, hg₀]
  fin_cases i <;> fin_cases j <;> simp [blkMat, gm, h02, h12, h20, h21, h22]

theorem glaPLayer_ne_bot_of_diagonal [Finite k] [CharP k 2] {σ : k ≃+* k} {f₀ : ℕ}
    (hf₀ : 2 ≤ f₀) (hk₀ : Nat.card (semilinearFixedSubfield σ) = 2 ^ f₀)
    (h3 : 3 ∣ Nat.card (semilinearFixedSubfield σ) - 1)
    {X : GL (Fin 3) k} {d : Fin 3 → k} (hX : (X : Matrix (Fin 3) (Fin 3) k) = diagonal d)
    (hd01 : d 0 = d 1) (hd02 : d 0 ≠ d 2) :
    GLAPLayer 3 (fixSubgroup (fieldAut 3 k σ) ⊓ fixSubgroup (LinearFlag.conjAut 3 k X)) ≠ ⊥ := by
  classical
  set k₀ := semilinearFixedSubfield σ with hk₀def
  have hσk₀ : ∀ c ∈ k₀, σ c = c := fun c hc => RingHom.mem_eqLocusField.mp hc
  set Y := fixSubgroup (fieldAut 3 k σ) ⊓ fixSubgroup (LinearFlag.conjAut 3 k X) with hYdef
  set φ : Matrix.SpecialLinearGroup (Fin 2) k₀ →* projectiveSL 3 k :=
    (proj 3 k).comp (slBlk.comp (Matrix.SpecialLinearGroup.map k₀.subtype)) with hφdef
  have hφ : ∀ g, φ g = proj 3 k (slBlk (Matrix.SpecialLinearGroup.map k₀.subtype g)) :=
    fun g => rfl
  have hd12 : d 1 ≠ d 2 := by rwa [← hd01]
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    rw [hφ, proj_eq_one_iff] at hg
    obtain ⟨c, -, hcg⟩ := mem_scalars.1 hg
    rw [coe_slBlk] at hcg
    have hc1 : (c : k) = 1 := by
      have h := congrFun (congrFun hcg 2) 2
      rw [Matrix.scalar_apply, Matrix.diagonal_apply_eq] at h
      rw [← h]
      simp [blkMat]
    rw [hc1, map_one] at hcg
    have he : ∀ i j : Fin 2, ((g : Matrix (Fin 2) (Fin 2) k₀) i j : k) =
        blkMat ((Matrix.SpecialLinearGroup.map k₀.subtype g :
          Matrix.SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) i.castSucc j.castSucc := by
      intro i j
      fin_cases i <;> fin_cases j <;> simp [blkMat, Matrix.SpecialLinearGroup.map_apply_coe]
    ext i j
    rw [he, hcg]
    fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply]
  have hJY : φ.range ≤ Y := by
    rintro _ ⟨g, rfl⟩
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [mem_fixSubgroup, hφ, fieldAut_proj, map_slBlk_map_subtype hσk₀]
    · rw [mem_fixSubgroup, hφ, conjAut_proj]
      congr 1
      apply Subtype.ext
      have hXB : (X : Matrix (Fin 3) (Fin 3) k) * blkMat ((Matrix.SpecialLinearGroup.map
          k₀.subtype g : Matrix.SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
          blkMat ((Matrix.SpecialLinearGroup.map k₀.subtype g :
            Matrix.SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) * X := by
        rw [hX]
        exact diagonal_mul_blkMat hd01 _
      rw [coe_slConjugation, coe_slBlk, hXB, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  have hJn : (φ.range.subgroupOf Y).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hJY]
    rintro _ y ⟨g, rfl⟩ hy
    obtain ⟨Y₁, rfl⟩ := proj_surjective 3 k y
    have hyσ := (Subgroup.mem_inf.1 hy).1
    have hyX := (Subgroup.mem_inf.1 hy).2
    rw [mem_fixSubgroup] at hyσ hyX
    have hXu := commute_of_conjAut_fix_diag hX hd01 hyX
    rw [fieldAut_proj, proj_eq_proj_iff] at hyσ
    set w := (Matrix.SpecialLinearGroup.map σ.toRingHom Y₁)⁻¹ * Y₁ with hw
    have hwc : w ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) k) := by
      rw [← scalars_eq_center 3 k]
      exact hyσ
    set B := slBlk (Matrix.SpecialLinearGroup.map k₀.subtype g) with hB
    set Z := Y₁ * B * Y₁⁻¹ with hZ
    have hσY : Matrix.SpecialLinearGroup.map σ.toRingHom Y₁ = Y₁ * w⁻¹ := by
      rw [hw, _root_.mul_inv_rev, inv_inv, mul_inv_cancel_left]
    have hZσ : Matrix.SpecialLinearGroup.map σ.toRingHom Z = Z := by
      have hwB : w⁻¹ * B = B * w⁻¹ :=
        ((Subgroup.mem_center_iff.1 (Subgroup.inv_mem _ hwc)) B).symm
      rw [hZ, map_mul, map_mul, map_inv, hσY, hB, map_slBlk_map_subtype hσk₀, ← hB]
      calc Y₁ * w⁻¹ * B * (Y₁ * w⁻¹)⁻¹ = Y₁ * (w⁻¹ * B) * w * Y₁⁻¹ := by group
        _ = Y₁ * (B * w⁻¹) * w * Y₁⁻¹ := by rw [hwB]
        _ = Y₁ * B * Y₁⁻¹ := by group
    set u := Matrix.SpecialLinearGroup.toGL Y₁ with hu
    set b := Matrix.SpecialLinearGroup.toGL B with hb
    have hXb : X * b = b * X := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, hb, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hB,
        coe_slBlk, hX]
      exact diagonal_mul_blkMat hd01 _
    have hZgl : Matrix.SpecialLinearGroup.toGL Z = u * b * u⁻¹ := by
      rw [hZ, map_mul, map_mul, map_inv]
    have hXZ : X * (u * b * u⁻¹) = (u * b * u⁻¹) * X := by
      have h1 : Commute X u := hXu
      have h2 : Commute X b := hXb
      exact (h1.mul_right h2).mul_right h1.inv_right
    have hXZm : diagonal d * (Z : Matrix (Fin 3) (Fin 3) k) =
        (Z : Matrix (Fin 3) (Fin 3) k) * diagonal d := by
      rw [← hZgl] at hXZ
      have := congrArg Units.val hXZ
      rwa [Units.val_mul, Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hX] at this
    have hum : diagonal d * (u : Matrix (Fin 3) (Fin 3) k) =
        (u : Matrix (Fin 3) (Fin 3) k) * diagonal d := by
      have := congrArg Units.val hXu
      rwa [Units.val_mul, Units.val_mul, hX] at this
    have hu20 : (u : Matrix (Fin 3) (Fin 3) k) 2 0 = 0 :=
      eq_zero_of_diagonal_commute hum hd02.symm
    have hu21 : (u : Matrix (Fin 3) (Fin 3) k) 2 1 = 0 :=
      eq_zero_of_diagonal_commute hum hd12.symm
    have hbm : (b : Matrix (Fin 3) (Fin 3) k) = blkMat ((Matrix.SpecialLinearGroup.map k₀.subtype
        g : Matrix.SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) := by
      rw [hb, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hB, coe_slBlk]
    have hb20 : (b : Matrix (Fin 3) (Fin 3) k) 2 0 = 0 := by rw [hbm]; simp [blkMat]
    have hb21 : (b : Matrix (Fin 3) (Fin 3) k) 2 1 = 0 := by rw [hbm]; simp [blkMat]
    have hb22 : (b : Matrix (Fin 3) (Fin 3) k) 2 2 = 1 := by rw [hbm]; simp [blkMat]
    have hZ22 : (Z : Matrix (Fin 3) (Fin 3) k) 2 2 = 1 := by
      have e1 : (Z : Matrix (Fin 3) (Fin 3) k) = (u : Matrix (Fin 3) (Fin 3) k) *
          ((b : Matrix (Fin 3) (Fin 3) k) * ((u⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)) := by
        rw [← Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hZgl, Units.val_mul, Units.val_mul,
          Matrix.mul_assoc]
      have e2 : (u : Matrix (Fin 3) (Fin 3) k) 2 2 *
          ((u⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) 2 2 = 1 := by
        have := mul_apply_two_two (Q := ((u⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k))
          hu20 hu21
        rw [Units.mul_inv, Matrix.one_apply_eq] at this
        exact this.symm
      rw [e1, mul_apply_two_two hu20 hu21, mul_apply_two_two hb20 hb21, hb22, one_mul, e2]
    have hZmem : ∀ i j, (Z : Matrix (Fin 3) (Fin 3) k) i j ∈ k₀ := by
      intro i j
      have := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 3) k =>
        (A : Matrix (Fin 3) (Fin 3) k) i j) hZσ
      simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
        Matrix.map_apply] at this
      exact RingHom.mem_eqLocusField.mpr this
    obtain ⟨g', hg'⟩ := exists_slBlk_eq hZmem (eq_zero_of_diagonal_commute hXZm hd02)
      (eq_zero_of_diagonal_commute hXZm hd12) (eq_zero_of_diagonal_commute hXZm hd02.symm)
      (eq_zero_of_diagonal_commute hXZm hd12.symm) hZ22
    refine ⟨g', ?_⟩
    rw [hφ g', hg', hZ, map_mul, map_mul, map_inv, hφ g, ← hB]
  haveI : Fintype k₀ := Fintype.ofFinite k₀
  haveI : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) k₀) :=
    CFSG.Quasithin.R3c21.isSimpleGroup_sl2_of_card_two_pow hf₀
      (by rw [← Nat.card_eq_fintype_card, hk₀])
  let eJ : Matrix.SpecialLinearGroup (Fin 2) k₀ ≃* φ.range := MonoidHom.ofInjective hφinj
  haveI : IsSimpleGroup φ.range := eJ.symm.isSimpleGroup
  have hnc : ∃ a b : φ.range, a * b ≠ b * a := by
    let t1 : Matrix.SpecialLinearGroup (Fin 2) k₀ := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
    let t2 : Matrix.SpecialLinearGroup (Fin 2) k₀ := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩
    have ht1 : (t1 : Matrix (Fin 2) (Fin 2) k₀) = !![1, 1; 0, 1] := rfl
    have ht2 : (t2 : Matrix (Fin 2) (Fin 2) k₀) = !![1, 0; 1, 1] := rfl
    refine ⟨eJ t1, eJ t2, fun h => ?_⟩
    rw [← map_mul, ← map_mul] at h
    have h' := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) k₀ =>
      (A : Matrix (Fin 2) (Fin 2) k₀) 0 0) (eJ.injective h)
    simp only [Matrix.SpecialLinearGroup.coe_mul, ht1, ht2] at h'
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h'
  have h3J : 3 ∣ Nat.card φ.range := by
    rw [← Nat.card_congr eJ.toEquiv]
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_of_dvd (F := k₀) Nat.prime_three h3
    have hζ3 : ζ ^ 3 = 1 := hζ.pow_eq_one
    have hζ6 : (ζ ^ 2) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ3, one_pow]
    let t3 : Matrix.SpecialLinearGroup (Fin 2) k₀ := ⟨diagonal ![ζ, ζ ^ 2], by
      rw [Matrix.det_diagonal, Fin.prod_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      rw [← pow_succ', hζ3]⟩
    have ht3 : t3 ^ 3 = 1 := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
      show (diagonal ![ζ, ζ ^ 2]) ^ 3 = 1
      rw [diagonal_pow, ← Matrix.diagonal_one]
      congr 1
      funext i
      fin_cases i <;> simp [hζ3, hζ6]
    have ht31 : t3 ≠ 1 := by
      intro h
      have h1 := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) k₀ =>
        (A : Matrix (Fin 2) (Fin 2) k₀) 0 0) h
      simp [t3] at h1
      exact hζ.ne_one (by norm_num) h1
    rw [← orderOf_eq_prime ht3 ht31]
    exact orderOf_dvd_natCard t3
  have hle := le_glaPLayer_of_normal_simple Nat.prime_three hJY hJn hnc h3J
  intro hbot
  rw [hbot] at hle
  obtain ⟨a, b, hab⟩ := hnc
  apply hab
  have ha : a = 1 := Subtype.ext (Subgroup.mem_bot.1 (hle a.2))
  have hb : b = 1 := Subtype.ext (Subgroup.mem_bot.1 (hle b.2))
  rw [ha, hb]

end Core


section Reduction

theorem fixSubgroup_conj {G : Type*} [Group G] (g a : MulAut G) :
    fixSubgroup (g * a * g⁻¹) = (fixSubgroup a).map g.toMonoidHom := by
  ext x
  rw [mem_fixSubgroup, Subgroup.mem_map_equiv, mem_fixSubgroup]
  show g (a (g.symm x)) = x ↔ a (g.symm x) = g.symm x
  exact ⟨fun h => (g.symm_apply_apply _).symm.trans (congrArg g.symm h),
    fun h => by rw [h, MulEquiv.apply_symm_apply]⟩

theorem glaPLayer_ne_bot_of_conj {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (g a b : MulAut G)
    (h : GLAPLayer p (fixSubgroup (g * a * g⁻¹) ⊓ fixSubgroup (g * b * g⁻¹)) ≠ ⊥) :
    GLAPLayer p (fixSubgroup a ⊓ fixSubgroup b) ≠ ⊥ := by
  intro hbot
  apply h
  rw [fixSubgroup_conj, fixSubgroup_conj,
    ← Subgroup.map_inf_eq _ _ _ (g.injective : Function.Injective g.toMonoidHom),
    ← glaPLayer_map_eq_of_injective hp _ g.injective, hbot, Subgroup.map_bot]

theorem exists_perm_conj_diagonal {F : Type*} [Field F] {i j l : Fin 3} (hij : i ≠ j)
    (hli : l ≠ i) (hlj : l ≠ j) :
    ∃ S : GL (Fin 3) F, ∀ (X : GL (Fin 3) F) (d : Fin 3 → F),
      (X : Matrix (Fin 3) (Fin 3) F) = diagonal d →
        ((S * X * S⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
          diagonal ![d i, d j, d l] := by
  classical
  have hinj : Function.Injective ![i, j, l] := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all
  let π : Fin 3 ≃ Fin 3 := Equiv.ofBijective _ (Finite.injective_iff_bijective.1 hinj)
  let S : GL (Fin 3) F := ⟨π.toPEquiv.toMatrix, π.symm.toPEquiv.toMatrix, by
      rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.self_trans_symm,
        Equiv.toPEquiv_refl, PEquiv.toMatrix_refl], by
      rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.symm_trans_self,
        Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]⟩
  refine ⟨S, fun X d hX => ?_⟩
  rw [Units.val_mul, Units.val_mul, hX]
  show π.toPEquiv.toMatrix * diagonal d * π.symm.toPEquiv.toMatrix = _
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, Equiv.symm_symm,
    Matrix.submatrix_submatrix, Function.comp_id, Function.id_comp,
    Matrix.submatrix_diagonal_equiv]
  congr 1
  funext t
  fin_cases t <;> rfl

theorem exists_conj_diagonal_of_pow_three {F : Type} [Field F] {ζ : F}
    (hζ : IsPrimitiveRoot ζ 3) {M : GL (Fin 3) F} (hM3 : M ^ 3 = 1) :
    ∃ P : GL (Fin 3) F, ((P * M * P⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      diagonal (fun l => ((P * M * P⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) l l) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hP⟩ := exists_conj_diagonal_of_exponent_prime (n := 3) (p := 3) ⟨ζ, hζ⟩
    (Subgroup.zpowers M)
    (fun x hx y hy => by
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      obtain ⟨m', rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      exact (Commute.zpow_zpow_self M m m').eq)
    (fun x hx => orderOf_dvd_iff_pow_eq_one.1
      ((orderOf_dvd_of_mem_zpowers hx).trans (orderOf_dvd_of_pow_eq_one hM3)))
  exact ⟨P, glConj_eq_diagonal (hP M (Subgroup.mem_zpowers M))⟩

theorem diag_pow_three_eq_one {F : Type*} [Field F] {P M : GL (Fin 3) F} {d : Fin 3 → F}
    (hM3 : M ^ 3 = 1)
    (hd : ((P * M * P⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = diagonal d) (t : Fin 3) :
    d t ^ 3 = 1 := by
  have h1 : (P * M * P⁻¹ : GL (Fin 3) F) ^ 3 = 1 := by rw [conj_pow, hM3]; group
  have h2 := congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F) t t) h1
  simp only [Units.val_pow_eq_pow_val, hd, diagonal_pow, diagonal_apply_eq, Units.val_one,
    one_apply_eq] at h2
  exact h2

variable {k : Type} [Field k]

theorem exists_eq_ne_of_diag [CharP k 2] {P M u : GL (Fin 3) k} {d : Fin 3 → k}
    (hd : ((P * M * P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) = diagonal d)
    (hu1 : u ≠ 1) (hu2 : u * u = 1) (hMu : M * u = u * M)
    (hM1 : LinearFlag.conjAut 3 k M ≠ 1) :
    ∃ i j l : Fin 3, i ≠ j ∧ l ≠ i ∧ l ≠ j ∧ d i = d j ∧ d l ≠ d i := by
  classical
  set W := P * u * P⁻¹ with hW
  have hWd : diagonal d * (W : Matrix (Fin 3) (Fin 3) k) =
      (W : Matrix (Fin 3) (Fin 3) k) * diagonal d := by
    rw [← hd, ← Units.val_mul, ← Units.val_mul]
    congr 1
    rw [hW]
    calc P * M * P⁻¹ * (P * u * P⁻¹) = P * (M * u) * P⁻¹ := by group
      _ = P * (u * M) * P⁻¹ := by rw [hMu]
      _ = P * u * P⁻¹ * (P * M * P⁻¹) := by group
  have hW2 : (W : Matrix (Fin 3) (Fin 3) k) * W = 1 := by
    rw [← Units.val_mul]
    have : W * W = 1 := by
      rw [hW]
      calc P * u * P⁻¹ * (P * u * P⁻¹) = P * (u * u) * P⁻¹ := by group
        _ = 1 := by rw [hu2]; group
    rw [this, Units.val_one]
  by_cases hinj : ∀ i j, i ≠ j → d i ≠ d j
  · exfalso
    apply hu1
    have h1 := eq_one_of_commute_two_diagonal_of_mul_self_eq_one (a := d) (b := d)
      (fun i j hij => Or.inl (hinj i j hij)) hWd hWd hW2
    have h1' : W = 1 := Units.ext h1
    calc u = P⁻¹ * W * P := by rw [hW]; group
      _ = 1 := by rw [h1']; group
  push Not at hinj
  obtain ⟨i, j, hij, hdij⟩ := hinj
  by_cases hc : ∀ l, d l = d i
  · exfalso
    apply hM1
    have hdi0 : d i ≠ 0 := by
      intro h0
      have hdet : ((P * M * P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k).det ≠ 0 :=
        ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)).ne_zero
      apply hdet
      rw [hd, Matrix.det_diagonal, Fin.prod_univ_three, hc 0, h0, zero_mul, zero_mul]
    have hsc : P * M * P⁻¹ = GeneralLinearGroup.scalar (Fin 3) (Units.mk0 (d i) hdi0) := by
      apply Units.ext
      rw [hd, GeneralLinearGroup.coe_scalar, Units.val_mk0, Matrix.scalar_apply]
      congr 1
      funext l
      exact hc l
    rw [eq_scalar_of_conj_eq_scalar hsc, LinearFlag.conjAut_scalar]
  push Not at hc
  obtain ⟨l, hl⟩ := hc
  exact ⟨i, j, l, hij, fun h => hl (by rw [h]), fun h => hl (by rw [h, hdij]), hdij, hl⟩

theorem sum_three_of_ne {i j l : Fin 3} (hij : i ≠ j) (hli : l ≠ i) (hlj : l ≠ j)
    (d : Fin 3 → k) : d 0 + d 1 + d 2 = d i + d j + d l := by
  fin_cases i <;> fin_cases j <;> fin_cases l <;> simp at hij hli hlj ⊢ <;> ring

theorem exists_gl_subfield {k₀ : Subfield k} {M : GL (Fin 3) k}
    (hM : ∀ i j, (M : Matrix (Fin 3) (Fin 3) k) i j ∈ k₀) :
    ∃ M₀ : GL (Fin 3) k₀, GeneralLinearGroup.map k₀.subtype M₀ = M := by
  let A : Matrix (Fin 3) (Fin 3) k₀ := fun i j => ⟨(M : Matrix (Fin 3) (Fin 3) k) i j, hM i j⟩
  have hA : k₀.subtype.mapMatrix A = (M : Matrix (Fin 3) (Fin 3) k) := rfl
  have hdet : A.det ≠ 0 := by
    intro h
    have h' := congrArg k₀.subtype h
    rw [RingHom.map_det, hA, map_zero] at h'
    exact ((Matrix.isUnit_iff_isUnit_det _).1 M.isUnit).ne_zero h'
  refine ⟨GeneralLinearGroup.mkOfDetNeZero A hdet, ?_⟩
  ext i j
  rfl

theorem glaPLayer_ne_bot_of_fieldAut_conjAut [Finite k] [CharP k 2] {σ : k ≃+* k} {f₀ : ℕ}
    (hf₀ : 2 ≤ f₀) (hk₀ : Nat.card (semilinearFixedSubfield σ) = 2 ^ f₀)
    (h3 : 3 ∣ Nat.card (semilinearFixedSubfield σ) - 1)
    {M : GL (Fin 3) k} (hM1 : LinearFlag.conjAut 3 k M ≠ 1)
    (hM3 : LinearFlag.conjAut 3 k M ^ 3 = 1)
    (hcomm : fieldAut 3 k σ * LinearFlag.conjAut 3 k M =
      LinearFlag.conjAut 3 k M * fieldAut 3 k σ)
    {t : projectiveSL 3 k} (ht : orderOf t = 2) (hfix : LinearFlag.conjAut 3 k M t = t) :
    GLAPLayer 3 (fixSubgroup (fieldAut 3 k σ) ⊓ fixSubgroup (LinearFlag.conjAut 3 k M)) ≠ ⊥ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set k₀ := semilinearFixedSubfield σ with hk₀def
  have hσk₀ : ∀ c ∈ k₀, σ c = c := fun c hc => RingHom.mem_eqLocusField.mp hc
  have htr := (LinearFlag.standard_automorphism_transport (K := k) (n := 3)).2.2.1
  have ht2 : t ^ 2 = 1 := by
    rw [← ht]
    exact pow_orderOf_eq_one t
  obtain ⟨U, hUt, hU2⟩ := exists_lift_of_sq_eq_one ht2
  set u := Matrix.SpecialLinearGroup.toGL U with hu
  have hu1 : u ≠ 1 := by
    intro h
    have hU : U = 1 := Matrix.SpecialLinearGroup.toGL_injective (by rw [← hu, h, map_one])
    rw [hU, map_one] at hUt
    rw [← hUt, orderOf_one] at ht
    exact absurd ht (by norm_num)
  have hu2 : u * u = 1 := by rw [hu, ← map_mul, ← sq, hU2, map_one]
  have hMu : M * u = u * M := mul_comm_of_conjAut_proj_eq hU2 (by rw [hUt]; exact hfix)
  obtain ⟨a, ha⟩ := exists_eq_scalar_of_conjAut_eq_one (n := 3) (by norm_num)
    (show LinearFlag.conjAut 3 k (M ^ 3) = 1 by rw [map_pow, hM3])
  obtain ⟨μ, hμ⟩ := exists_cube_root_of_commute ha hu1 hu2 hMu
  set M' := GeneralLinearGroup.scalar (Fin 3) μ⁻¹ * M with hM'
  have hM'3 : M' ^ 3 = 1 := by
    rw [hM', scalar_mul_pow, ha, ← map_mul, inv_pow, hμ, inv_mul_cancel, map_one]
  have hcM' : LinearFlag.conjAut 3 k M' = LinearFlag.conjAut 3 k M := by
    rw [hM', conjAut_scalar_mul]
  have hM'u : M' * u = u * M' := by
    rw [hM', mul_assoc, hMu, ← mul_assoc, ← mul_assoc, GeneralLinearGroup.scalar_commute μ⁻¹ u]
  have hM'1 : LinearFlag.conjAut 3 k M' ≠ 1 := by rwa [hcM']
  have hσc : LinearFlag.conjAut 3 k (GeneralLinearGroup.map (σ : k →+* k) M') =
      LinearFlag.conjAut 3 k M' := by
    rw [← htr σ M', hcM', hcomm, mul_inv_cancel_right]
  obtain ⟨lam, hlam⟩ := exists_eq_scalar_of_conjAut_eq_one (n := 3) (by norm_num)
    (show LinearFlag.conjAut 3 k (M'⁻¹ * GeneralLinearGroup.map (σ : k →+* k) M') = 1 by
      rw [map_mul, map_inv, hσc, inv_mul_cancel])
  have hσM : GeneralLinearGroup.map (σ : k →+* k) M' =
      M' * GeneralLinearGroup.scalar (Fin 3) lam := by
    rw [← hlam, mul_inv_cancel_left]
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_of_dvd (F := k₀) Nat.prime_three h3
  have hζk : IsPrimitiveRoot (ζ : k) 3 := hζ.map_of_injective k₀.subtype.injective
  have hμ3 : ∀ x : k, x ^ 3 = 1 → σ x = x := by
    intro x hx
    obtain ⟨m, -, rfl⟩ := hζk.eq_pow_of_pow_eq_one hx
    rw [map_pow, hσk₀ _ ζ.2]
  obtain ⟨P, hP⟩ := exists_conj_diagonal_of_pow_three hζk hM'3
  set d : Fin 3 → k := fun l => ((P * M' * P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) l l
    with hd
  obtain ⟨i, j, l, hij, hli, hlj, hdij, hdl⟩ := exists_eq_ne_of_diag hP hu1 hu2 hM'u hM'1
  have h2 : (2 : k) = 0 := CharP.cast_eq_zero k 2
  have htrM : Matrix.trace (M' : Matrix (Fin 3) (Fin 3) k) = d l := by
    rw [← Matrix.trace_units_conj P (M' : Matrix (Fin 3) (Fin 3) k), ← Units.val_mul,
      ← Units.val_mul, hP, Matrix.trace_diagonal, Fin.sum_univ_three, sum_three_of_ne hij hli hlj,
      ← hdij]
    linear_combination d i * h2
  have hσtr : σ (Matrix.trace (M' : Matrix (Fin 3) (Fin 3) k)) =
      lam * Matrix.trace (M' : Matrix (Fin 3) (Fin 3) k) := by
    have e1 : Matrix.trace ((GeneralLinearGroup.map (σ : k →+* k) M' : GL (Fin 3) k) :
        Matrix (Fin 3) (Fin 3) k) = σ (Matrix.trace (M' : Matrix (Fin 3) (Fin 3) k)) := by
      rw [Matrix.trace_fin_three, Matrix.trace_fin_three, map_add, map_add]
      simp only [Matrix.GeneralLinearGroup.map_apply, RingEquiv.coe_toRingHom]
    rw [← e1, hσM, Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul,
      smul_eq_mul]
  have hdl3 := diag_pow_three_eq_one hM'3 hP l
  have hdl0 : d l ≠ 0 := by
    intro h0
    rw [h0] at hdl3
    norm_num at hdl3
  have hlam1 : lam = 1 := by
    rw [htrM, hμ3 _ hdl3] at hσtr
    have h0 : ((lam : k) - 1) * d l = 0 := by linear_combination -hσtr
    exact Units.ext (sub_eq_zero.1 ((mul_eq_zero.1 h0).resolve_right hdl0))
  have hσM' : GeneralLinearGroup.map (σ : k →+* k) M' = M' := by
    rw [hσM, hlam1, map_one, mul_one]
  have hmem : ∀ i j, (M' : Matrix (Fin 3) (Fin 3) k) i j ∈ k₀ := by
    intro i j
    have := congrArg (fun g : GL (Fin 3) k => (g : Matrix (Fin 3) (Fin 3) k) i j) hσM'
    simp only [Matrix.GeneralLinearGroup.map_apply, RingEquiv.coe_toRingHom] at this
    exact RingHom.mem_eqLocusField.mpr this
  obtain ⟨M₀, hM₀⟩ := exists_gl_subfield hmem
  have hmapinj : Function.Injective (GeneralLinearGroup.map (n := Fin 3) k₀.subtype) := by
    intro x y hxy
    ext i j
    have := congrArg (fun g : GL (Fin 3) k => (g : Matrix (Fin 3) (Fin 3) k) i j) hxy
    simp only [Matrix.GeneralLinearGroup.map_apply] at this
    exact this
  have hM₀3 : M₀ ^ 3 = 1 := hmapinj (by rw [map_pow, hM₀, hM'3, map_one])
  have hmapdiag : ∀ (R : GL (Fin 3) k₀) (e : Fin 3 → k₀),
      ((R * M₀ * R⁻¹ : GL (Fin 3) k₀) : Matrix (Fin 3) (Fin 3) k₀) = diagonal e →
      ((GeneralLinearGroup.map k₀.subtype R * M' * (GeneralLinearGroup.map k₀.subtype R)⁻¹ :
        GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) = diagonal (fun t => (e t : k)) := by
    intro R e hR
    rw [← hM₀, ← map_inv, ← map_mul, ← map_mul]
    ext i j
    rw [Matrix.GeneralLinearGroup.map_apply, hR]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [Matrix.diagonal_apply_ne _ hij]
  obtain ⟨P₀, hP₀⟩ := exists_conj_diagonal_of_pow_three hζ hM₀3
  set d₀ : Fin 3 → k₀ := fun l =>
    ((P₀ * M₀ * P₀⁻¹ : GL (Fin 3) k₀) : Matrix (Fin 3) (Fin 3) k₀) l l with hd₀
  obtain ⟨i', j', l', hij', hli', hlj', hdij', hdl'⟩ :=
    exists_eq_ne_of_diag (hmapdiag P₀ d₀ hP₀) hu1 hu2 hM'u hM'1
  obtain ⟨S₀, hS₀⟩ := exists_perm_conj_diagonal (F := k₀) hij' hli' hlj'
  set R := S₀ * P₀ with hR
  have hRdiag : ((R * M₀ * R⁻¹ : GL (Fin 3) k₀) : Matrix (Fin 3) (Fin 3) k₀) =
      diagonal ![d₀ i', d₀ j', d₀ l'] := by
    rw [← hS₀ (P₀ * M₀ * P₀⁻¹) d₀ hP₀, hR]
    congr 1
    group
  set Q := GeneralLinearGroup.map k₀.subtype R with hQ
  have hcore := glaPLayer_ne_bot_of_diagonal hf₀ hk₀ h3 (hmapdiag R _ hRdiag)
    (show (d₀ i' : k) = d₀ j' from hdij') (show (d₀ i' : k) ≠ d₀ l' from fun h => hdl' h.symm)
  have hσQ : GeneralLinearGroup.map (σ : k →+* k) Q = Q := by
    ext i j
    simp only [hQ, Matrix.GeneralLinearGroup.map_apply, RingEquiv.coe_toRingHom]
    exact hσk₀ _ ((R : Matrix (Fin 3) (Fin 3) k₀) i j).2
  have hfconj : LinearFlag.conjAut 3 k Q * fieldAut 3 k σ * (LinearFlag.conjAut 3 k Q)⁻¹ =
      fieldAut 3 k σ := by
    calc LinearFlag.conjAut 3 k Q * fieldAut 3 k σ * (LinearFlag.conjAut 3 k Q)⁻¹
        = (fieldAut 3 k σ * LinearFlag.conjAut 3 k Q * (fieldAut 3 k σ)⁻¹) * fieldAut 3 k σ *
            (LinearFlag.conjAut 3 k Q)⁻¹ := by rw [htr σ Q, hσQ]
      _ = fieldAut 3 k σ := by group
  have hcX : LinearFlag.conjAut 3 k (Q * M' * Q⁻¹) = LinearFlag.conjAut 3 k Q *
      LinearFlag.conjAut 3 k M * (LinearFlag.conjAut 3 k Q)⁻¹ := by
    rw [map_mul, map_mul, map_inv, hcM']
  apply glaPLayer_ne_bot_of_conj Nat.prime_three (LinearFlag.conjAut 3 k Q)
  rw [hfconj, ← hcX]
  exact hcore

end Reduction

section Field

variable {k : Type} [Field k] [Finite k]

theorem card_le_three_mul_card_inf_linear {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) [CharP k ℓ]
    (hK : Nat.card k = ℓ ^ f) {B : Subgroup (MulAut (projectiveSL 3 k))}
    (hB : ∀ b ∈ B, b ^ 3 = 1) :
    Nat.card B ≤ 3 * Nat.card (B ⊓ linearAutGroup 3 k : Subgroup (MulAut (projectiveSL 3 k))) := by
  classical
  obtain ⟨-, -, -, -, -, hnorm, -, -⟩ :=
    CFSG.RankThree.LinearDescent.higher_linear_prime_semilinear_field_descent hℓ hf (le_refl 3) hK
  haveI := hnorm
  let π : MulAut (projectiveSL 3 k) →* MulAut (projectiveSL 3 k) ⧸ linearAutGroup 3 k :=
    QuotientGroup.mk' (linearAutGroup 3 k)
  let φ : B →* MulAut (projectiveSL 3 k) ⧸ linearAutGroup 3 k := π.comp B.subtype
  have hker : Nat.card φ.ker =
      Nat.card (B ⊓ linearAutGroup 3 k : Subgroup (MulAut (projectiveSL 3 k))) := by
    have h1 : φ.ker = (linearAutGroup 3 k).subgroupOf B := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      exact QuotientGroup.eq_one_iff _
    rw [h1, ← Subgroup.inf_subgroupOf_left]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  haveI : IsCyclic (k ≃+* k) := by
    obtain ⟨σ₀, -, -, htop, -⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality hℓ hf hK
    exact isCyclic_iff_exists_zpowers_eq_top.mpr ⟨σ₀, htop⟩
  let ψ : (k ≃+* k) →* MulAut (projectiveSL 3 k) ⧸ linearAutGroup 3 k := π.comp (fieldAut 3 k)
  haveI : IsCyclic ψ.range := isCyclic_of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective
  have hle : φ.range ≤ ψ.range := by
    rintro _ ⟨b, rfl⟩
    have hb : (b : MulAut (projectiveSL 3 k)) ∈ semilinearAutGroup 3 k :=
      LinearFlag.mem_semilinearAutGroup_of_pow_odd (le_refl 3) (by decide) (hB b b.2)
    obtain ⟨A, τ, hAτ⟩ := mem_semilinearAutGroup_iff.1 hb
    refine ⟨τ, ?_⟩
    show π (fieldAut 3 k τ) = π b
    have hA1 : π (LinearFlag.conjAut 3 k A) = 1 :=
      (QuotientGroup.eq_one_iff _).2 (mem_linearAutGroup_iff.2 ⟨A, rfl⟩)
    rw [hAτ, map_mul, hA1, one_mul]
  haveI : IsCyclic φ.range := Subgroup.isCyclic_of_le hle
  have hrange : Nat.card φ.range ∣ 3 := by
    rw [← IsCyclic.exponent_eq_card]
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun x => ?_
    obtain ⟨y, hy⟩ := x
    obtain ⟨b, rfl⟩ := MonoidHom.mem_range.1 hy
    apply Subtype.ext
    show φ b ^ 3 = 1
    rw [← map_pow, show b ^ 3 = 1 from Subtype.ext (hB b b.2), map_one]
  rw [← Subgroup.card_ker_mul_card_range φ, hker, mul_comm]
  exact Nat.mul_le_mul_right _ (Nat.le_of_dvd (by norm_num) hrange)

end Field

section Coprime

variable {S : Type} [Group S] [Finite S]

private def restrictToStableB (D : Subgroup (MulAut S)) (T : Subgroup S)
    (h : ∀ β ∈ D, ∀ x ∈ T, β x ∈ T) : D →* MulAut T where
  toFun β :=
    { toFun := fun x => ⟨(β : MulAut S) x, h β β.2 x x.2⟩
      invFun := fun x => ⟨(β : MulAut S)⁻¹ x, h _ (D.inv_mem β.2) x x.2⟩
      left_inv := fun x => Subtype.ext (MulAut.inv_apply_self _ _ _)
      right_inv := fun x => Subtype.ext (MulAut.apply_inv_self _ _ _)
      map_mul' := fun x y => Subtype.ext (map_mul (β : MulAut S) (x : S) (y : S)) }
  map_one' := by
    ext x
    rfl
  map_mul' β γ := by
    ext x
    rfl

theorem exists_hyperplane_fix_involution {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {D : Subgroup (MulAut S)} (hD : IsElemAbelian p D) (hD1 : D ≠ ⊥)
    {T : Subgroup S} (hT2 : IsPGroup 2 T) (hT : T ≠ ⊥)
    (hDT : ∀ α ∈ D, T.map α.toMonoidHom = T) :
    ∃ B ≤ D, Nat.card B * p = Nat.card D ∧
      ∃ t ∈ T, orderOf t = 2 ∧ ∀ e ∈ B, e t = t := by
  classical
  have hmem : ∀ β ∈ D, ∀ x ∈ T, β x ∈ T := fun β hβ x hx => by
    rw [← hDT β hβ]
    exact Subgroup.mem_map_of_mem _ hx
  haveI : IsMulCommutative D := hD.1
  let _ : CommGroup D := IsMulCommutative.instCommGroup
  haveI : CFSG.IsElementaryAbelian p D :=
    { toIsMulCommutative := hD.1
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
        Subtype.ext (by simpa using hD.2 x x.2) }
  haveI : Nontrivial D := (Subgroup.nontrivial_iff_ne_bot D).2 hD1
  let α := restrictToStableB D T hmem
  have hcop : ¬ p ∣ Nat.card T := by
    intro h
    obtain ⟨n, hn⟩ := hT2.exists_card_eq
    rw [hn] at h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
  have htop := CFSG.SolvableSignalizer.iSup_fixedBySubgroup_index_eq_top p hp α hcop
  by_contra hno
  push Not at hno
  have hbot : ∀ B : Subgroup D, B.index = p →
      CFSG.SolvableSignalizer.fixedBySubgroup α B = ⊥ := by
    intro B hB
    by_contra hne
    set F := CFSG.SolvableSignalizer.fixedBySubgroup α B with hF
    have hF2 : IsPGroup 2 F := hT2.to_subgroup F
    haveI : Nontrivial F := (Subgroup.nontrivial_iff_ne_bot F).2 hne
    have h2F : 2 ∣ Nat.card F := by
      obtain ⟨n, hn⟩ := hF2.exists_card_eq
      have h1 : 1 < Nat.card F := Finite.one_lt_card
      rw [hn] at h1 ⊢
      have : n ≠ 0 := by
        rintro rfl
        simp at h1
      exact dvd_pow_self 2 this
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2F
    have ho : orderOf ((x : T) : S) = 2 := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx]
    have hBcard : Nat.card (B.map D.subtype) * p = Nat.card D := by
      rw [Subgroup.card_map_of_injective D.subtype_injective, ← hB, Subgroup.card_mul_index]
    obtain ⟨e, he, hne'⟩ :=
      hno (B.map D.subtype) (Subgroup.map_subtype_le B) hBcard ((x : T) : S) (x : T).2 ho
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 he
    apply hne'
    have hxF : ∀ b' ∈ B, α b' (x : T) = (x : T) :=
      (CFSG.SolvableSignalizer.mem_fixedBySubgroup α B (x : T)).1 x.2
    exact congrArg Subtype.val (hxF b hb)
  have hall : (⨆ (B : Subgroup D) (_ : B.index = p),
      CFSG.SolvableSignalizer.fixedBySubgroup α B) = ⊥ := iSup₂_eq_bot.2 hbot
  rw [hall] at htop
  apply hT
  rw [eq_bot_iff]
  intro x hx
  have : (⟨x, hx⟩ : T) ∈ (⊥ : Subgroup T) := by
    rw [htop]
    exact Subgroup.mem_top _
  rw [Subgroup.mem_bot] at this
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val this

end Coprime

section SLevel

@[expose] def GoodSubThree (S : Type) [Group S] [Finite S] : Prop :=
  ∀ A : Subgroup (MulAut S), IsElemAbelian 3 A → 3 ^ 3 ≤ Nat.card A →
    ∀ T : Subgroup S, IsPGroup 2 T → T ≠ ⊥ → (∀ α ∈ A, T.map α.toMonoidHom = T) →
      ∃ F ≤ A, Nat.card F = 3 ^ 2 ∧ IsGood 3 F

theorem fixSubgroup_mulAutCongr {S S' : Type} [Group S] [Group S'] (e : S ≃* S')
    (β : MulAut S) : fixSubgroup (MulAut.congr e β) = (fixSubgroup β).map (e : S →* S') := by
  ext x
  rw [mem_fixSubgroup]
  refine Iff.trans ?_ (Subgroup.mem_map_equiv (f := e)).symm
  rw [mem_fixSubgroup]
  show e (β (e.symm x)) = x ↔ β (e.symm x) = e.symm x
  exact e.eq_symm_apply.symm

theorem isGood_map_mulAutCongr {S S' : Type} [Group S] [Group S'] [Finite S] [Finite S']
    (e : S ≃* S') {F : Subgroup (MulAut S)} (hF : IsGood 3 F) :
    IsGood 3 (F.map (MulAut.congr e).toMonoidHom) := by
  have key : (⨅ f ∈ F.map (MulAut.congr e).toMonoidHom, fixSubgroup f) =
      (⨅ f ∈ F, fixSubgroup f).map e.toMonoidHom := by
    apply le_antisymm
    · intro x hx
      refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
      refine Subgroup.mem_iInf.2 fun f => Subgroup.mem_iInf.2 fun hf => ?_
      have hx' : x ∈ fixSubgroup (MulAut.congr e f) :=
        Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hx (MulAut.congr e f))
          (Subgroup.mem_map_of_mem _ hf)
      rw [fixSubgroup_mulAutCongr] at hx'
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hx'
      have hyeq : y = e.symm x := by
        rw [← hyx]
        simp
      rw [← hyeq]
      exact hy
    · rintro _ ⟨y, hy, rfl⟩
      refine Subgroup.mem_iInf.2 fun g => Subgroup.mem_iInf.2 fun hg => ?_
      obtain ⟨f, hf, rfl⟩ := Subgroup.mem_map.1 hg
      show e y ∈ fixSubgroup (MulAut.congr e f)
      rw [fixSubgroup_mulAutCongr]
      exact Subgroup.mem_map_of_mem _ (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hy f) hf)
  unfold IsGood at hF ⊢
  rw [key, ← glaPLayer_map_eq_of_injective Nat.prime_three e.toMonoidHom e.injective]
  exact fun h => hF ((Subgroup.map_eq_bot_iff_of_injective _ e.injective).1 h)

theorem GoodSubThree.of_mulEquiv {S S' : Type} [Group S] [Group S'] [Finite S] [Finite S']
    (e : S ≃* S') (h : GoodSubThree S) : GoodSubThree S' := by
  intro A' hA' hcard T' hT2 hT hAT
  let c : MulAut S ≃* MulAut S' := MulAut.congr e
  let A : Subgroup (MulAut S) := A'.map (c.symm : MulAut S' →* MulAut S)
  have hAel : IsElemAbelian 3 A := hA'.map _
  have hAcard : 3 ^ 3 ≤ Nat.card A := by
    rw [Subgroup.card_map_of_injective c.symm.injective]
    exact hcard
  let T : Subgroup S := T'.map (e.symm : S' →* S)
  have hT2' : IsPGroup 2 T := hT2.map _
  have hT' : T ≠ ⊥ := fun hbot =>
    hT ((Subgroup.map_eq_bot_iff_of_injective T' e.symm.injective).1 hbot)
  have hAT' : ∀ α ∈ A, T.map α.toMonoidHom = T := by
    rintro _ ⟨α', hα', rfl⟩
    have hcomp : (((c.symm α' : MulAut S) : S ≃* S).toMonoidHom.comp (e.symm : S' →* S)) =
        (e.symm : S' →* S).comp α'.toMonoidHom := by
      ext g
      change e.symm (α' (e (e.symm g))) = e.symm (α' g)
      rw [e.apply_symm_apply]
    change (T'.map (e.symm : S' →* S)).map (c.symm α').toMonoidHom = T'.map (e.symm : S' →* S)
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hAT α' hα']
  obtain ⟨F, hFA, hF9, hFg⟩ := h A hAel hAcard T hT2' hT' hAT'
  refine ⟨F.map (MulAut.congr e).toMonoidHom, ?_, ?_, isGood_map_mulAutCongr e hFg⟩
  · rintro _ ⟨f, hf, rfl⟩
    obtain ⟨a', ha', rfl⟩ := hFA hf
    show c (c.symm a') ∈ A'
    rw [c.apply_symm_apply]
    exact ha'
  · rw [Subgroup.card_map_of_injective (MulAut.congr e).injective]
    exact hF9

end SLevel

section Model

theorem closure_eq_of_card_nine_not_mem {G : Type*} [Group G] {B L : Subgroup G} [Finite B]
    (hB : Nat.card B = 9) {x e : G} (hxB : x ∈ B) (heB : e ∈ B) (hx3 : x ^ 3 = 1) (hxL : x ∉ L)
    (heL : e ∈ L) (he1 : e ≠ 1) : Subgroup.closure {x, e} = B := by
  classical
  have hle : Subgroup.closure {x, e} ≤ B := by
    rw [Subgroup.closure_le]
    intro y hy
    rcases hy with rfl | rfl
    · exact hxB
    · exact heB
  apply Subgroup.eq_of_le_of_card_ge hle
  have hdvd : Nat.card (Subgroup.closure ({x, e} : Set G)) ∣ 9 := hB ▸ Subgroup.card_dvd_of_le hle
  have hx1 : x ≠ 1 := fun h => hxL (h ▸ L.one_mem)
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hz : Subgroup.zpowers x ≤ Subgroup.closure {x, e} :=
    Subgroup.zpowers_le.2 (Subgroup.subset_closure (Set.mem_insert _ _))
  have hne : e ∉ Subgroup.zpowers x := by
    intro h
    have hfin : IsOfFinOrder x := isOfFinOrder_iff_pow_eq_one.2 ⟨3, by norm_num, hx3⟩
    rw [hfin.mem_zpowers_iff_mem_range_orderOf, hxo, Finset.mem_image] at h
    obtain ⟨m, hm, rfl⟩ := h
    rw [Finset.mem_range] at hm
    interval_cases m
    · exact he1 (pow_zero x)
    · exact hxL (by simpa using heL)
    · apply hxL
      have hx4 : x = (x ^ 2) ^ 2 := by
        rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, hx3, one_mul]
      rw [hx4]
      exact L.pow_mem heL 2
  have hlt : Subgroup.zpowers x < Subgroup.closure {x, e} :=
    lt_of_le_of_ne hz (fun h => hne (h ▸ Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)))
  have h3 : 3 < Nat.card (Subgroup.closure ({x, e} : Set G)) := by
    haveI : Finite (Subgroup.closure ({x, e} : Set G)) := Finite.of_injective _
      (Subgroup.inclusion_injective hle)
    rw [← hxo, ← Nat.card_zpowers]
    exact Subgroup.card_lt_of_lt hlt
  rw [hB]
  set c := Nat.card (Subgroup.closure ({x, e} : Set G)) with hc
  have hc9 : c ≤ 9 := Nat.le_of_dvd (by norm_num) hdvd
  interval_cases c <;> omega

theorem isGood_closure_pair {S : Type} [Group S] [Finite S] (a b : MulAut S)
    (h : GLAPLayer 3 (fixSubgroup a ⊓ fixSubgroup b) ≠ ⊥) :
    IsGood 3 (Subgroup.closure {a, b}) := by
  unfold IsGood
  rw [iInf_fixSubgroup_closure, iInf_insert, iInf_singleton]
  exact h

variable {k : Type} [Field k] [Finite k]

theorem goodSubThree_projectiveSL [CharP k 2] {e : ℕ} (he : Even e) (he1 : 1 ≤ e)
    (hK : Nat.card k = 2 ^ e) : GoodSubThree (projectiveSL 3 k) := by
  classical
  intro A hA hA27 T hT2 hT hAT
  have hA1 : A ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hA27
    norm_num at hA27
  obtain ⟨B, hBA, hBcard, t, -, ht, hBt⟩ :=
    exists_hyperplane_fix_involution Nat.prime_three (by norm_num) hA hA1 hT2 hT hAT
  have hB : IsElemAbelian 3 B := isElemAbelian_mono hA hBA
  have h3k : 3 ∣ Nat.card k - 1 := by
    obtain ⟨m, rfl⟩ := he
    have h4 : 2 ^ (m + m) % 3 = 1 := by
      rw [← two_mul, pow_mul, Nat.pow_mod]
      norm_num
    rw [hK]
    omega
  have hBL : Nat.card (B ⊓ linearAutGroup 3 k : Subgroup (MulAut (projectiveSL 3 k))) ≤ 3 :=
    card_le_three_of_le_linearAutGroup h3k (isElemAbelian_mono hB inf_le_left) inf_le_right ht
      (fun e he => hBt e (Subgroup.mem_inf.1 he).1)
  have hBf := card_le_three_mul_card_inf_linear Nat.prime_two he1 hK (B := B)
    (fun b hb => hB.2 b hb)
  have h27 : (27 : ℕ) ≤ Nat.card B * 3 := by
    rw [hBcard]
    exact hA27
  have hB9 : Nat.card B = 9 := by omega
  obtain ⟨x, hxB, hxL⟩ : ∃ x ∈ B, x ∉ linearAutGroup 3 k := by
    by_contra hc
    push Not at hc
    have := Subgroup.card_le_of_le (le_inf le_rfl hc : B ≤ B ⊓ linearAutGroup 3 k)
    omega
  have hBL1 : (B ⊓ linearAutGroup 3 k : Subgroup (MulAut (projectiveSL 3 k))) ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hBf
    omega
  obtain ⟨⟨c, hcBL⟩, hc1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hBL1
  have hc1' : c ≠ 1 := fun h => hc1 (Subtype.ext h)
  have hcB := (Subgroup.mem_inf.1 hcBL).1
  have hcL := (Subgroup.mem_inf.1 hcBL).2
  have hx3 : x ^ 3 = 1 := hB.2 x hxB
  have hcomm : x * c = c * x := congrArg Subtype.val (hB.1.is_comm.comm ⟨x, hxB⟩ ⟨c, hcB⟩)
  have hcl := closure_eq_of_card_nine_not_mem hB9 hxB hcB hx3 hxL hcL hc1'
  refine ⟨Subgroup.closure {x, c}, hcl.le.trans hBA, by rw [hcl, hB9]; norm_num, ?_⟩
  apply isGood_closure_pair
  obtain ⟨-, -, -, -, -, -, -, hord⟩ :=
    CFSG.RankThree.LinearDescent.higher_linear_prime_semilinear_field_descent Nat.prime_two he1
      (le_refl 3) hK
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 (fun h => hxL (h ▸ Subgroup.one_mem _))
  obtain ⟨h3e, σ, -, ⟨h, hhL, hxh⟩, hk₀⟩ := hord 3 Nat.prime_three (by norm_num) x
    (LinearFlag.mem_semilinearAutGroup_of_pow_odd (le_refl 3) (by decide) hx3) hxL hxo
  have hc3 : c ^ 3 = 1 := hB.2 c hcB
  have hct : c t = t := hBt c hcB
  obtain ⟨H, rfl⟩ := mem_linearAutGroup_iff.1 hhL
  obtain ⟨M, rfl⟩ := mem_linearAutGroup_iff.1 hcL
  set g := LinearFlag.conjAut 3 k H with hg
  set M' := H⁻¹ * M * H with hM'
  have hcM' : LinearFlag.conjAut 3 k M' = g⁻¹ * LinearFlag.conjAut 3 k M * g := by
    rw [hM', map_mul, map_mul, map_inv]
  have hfσ : fieldAut 3 k σ = g⁻¹ * x * g := by
    rw [hxh]
    group
  have he' : e % 2 = 0 := Nat.even_iff.1 he
  have hf₀ : 2 ≤ e / 3 := by omega
  have h3₀ : 3 ∣ Nat.card (CFSG.GroupTheory.SteinbergBK.semilinearFixedSubfield σ) - 1 := by
    obtain ⟨m, hm⟩ : Even (e / 3) := Nat.even_iff.2 (by omega)
    have h4 : 2 ^ (e / 3) % 3 = 1 := by
      rw [hm, ← two_mul, pow_mul, Nat.pow_mod]
      norm_num
    rw [hk₀]
    omega
  have hM1 : LinearFlag.conjAut 3 k M' ≠ 1 := by
    rw [hcM']
    intro h1
    apply hc1'
    calc LinearFlag.conjAut 3 k M = g * (g⁻¹ * LinearFlag.conjAut 3 k M * g) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group
  have hM3 : LinearFlag.conjAut 3 k M' ^ 3 = 1 := by
    rw [hcM']
    have := conj_pow (a := g⁻¹) (b := LinearFlag.conjAut 3 k M) (i := 3)
    rw [inv_inv] at this
    rw [this, hc3]
    group
  have hcomm' : fieldAut 3 k σ * LinearFlag.conjAut 3 k M' =
      LinearFlag.conjAut 3 k M' * fieldAut 3 k σ := by
    rw [hfσ, hcM']
    calc g⁻¹ * x * g * (g⁻¹ * LinearFlag.conjAut 3 k M * g)
        = g⁻¹ * (x * LinearFlag.conjAut 3 k M) * g := by group
      _ = g⁻¹ * (LinearFlag.conjAut 3 k M * x) * g := by rw [hcomm]
      _ = g⁻¹ * LinearFlag.conjAut 3 k M * g * (g⁻¹ * x * g) := by group
  have ht' : orderOf (g⁻¹ t) = 2 := by
    rw [← ht]
    exact orderOf_injective (g⁻¹ : MulAut (projectiveSL 3 k)).toMonoidHom (MulEquiv.injective _) t
  have hfix' : LinearFlag.conjAut 3 k M' (g⁻¹ t) = g⁻¹ t := by
    rw [hcM']
    simp only [MulAut.mul_apply, MulAut.apply_inv_self, hct]
  have hred := glaPLayer_ne_bot_of_fieldAut_conjAut hf₀ hk₀ h3₀ hM1 hM3 hcomm' ht' hfix'
  apply glaPLayer_ne_bot_of_conj Nat.prime_three g⁻¹
  rw [show g⁻¹ * x * g⁻¹⁻¹ = fieldAut 3 k σ by rw [hfσ, inv_inv],
    show g⁻¹ * LinearFlag.conjAut 3 k M * g⁻¹⁻¹ = LinearFlag.conjAut 3 k M' by rw [hcM', inv_inv]]
  exact hred

end Model

theorem goodSubAt_linear (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.A 2 q).Valid)
    (hq : q.p = 2) (he : Even q.exponent) : HDesc.GoodSubAt 3 ⟨.A 2 q, hv⟩ 2 := by
  intro _ _ A hA hcard T hT2 hT hAT
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  let k := GaloisField q.p q.exponent
  have hK : Nat.card k = 2 ^ q.exponent := by
    dsimp only [k]
    rw [GaloisField.card q.p q.exponent q.exponent_pos.ne', hq]
  haveI : CharP k 2 := CharP.congr q.p hq
  let eModel : (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.A 2 q, hv⟩).Group ≃*
      LinearFlag.projectiveSL 3 k :=
    (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 k)
  exact GoodSubThree.of_mulEquiv eModel.symm (goodSubThree_projectiveSL he q.exponent_pos hK) A hA
    hcard T hT2 hT hAT

theorem linearRes_holds : HDesc.LinearRes := fun q hv hq he =>
  ⟨lpEpsNoGoodTwoLocal_linear q hv hq, goodSubAt_linear q hv hq he⟩

end CFSG.LocalAnalysis.GLTheoremA.HDescLinRes

end
