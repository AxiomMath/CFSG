module

public import CFSG.LargeExtraspecial.S14C12TOrd
public import CFSG.LargeExtraspecial.AS35Weak
public import CFSG.LargeExtraspecial.DW37Input
public import CFSG.LargeExtraspecial.DW37Statement
public import CFSG.LargeExtraspecial.GLRCent
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyLinearBinary
public import CFSG.LargeExtraspecial.AS35Fis

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

namespace SmithQ

open Subgroup Module QuadraticMap CFSG.Open
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem orderOf_mul_mem_of_mem_QG (S : Setting G) {x y : G} (hx : x ∈ S.QG) (hy : y ∈ S.QG) :
    orderOf (x * y) ∈ ({1, 2, 3, 4} : Set ℕ) ∧
      (orderOf (x * y) = 4 → IsConj S.z ((x * y) ^ 2)) := by
  have hxy := S.QG.mul_mem hx hy
  have hd : orderOf (x * y) ∣ 4 := orderOf_dvd_of_pow_eq_one (S.pow_four_eq_one hxy)
  refine ⟨?_, fun ho => ?_⟩
  · have hle : orderOf (x * y) ≤ 4 := Nat.le_of_dvd (by norm_num) hd
    have hpos : 0 < orderOf (x * y) := orderOf_pos (x * y)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  · rcases S.sq_eq_one_or_z hxy with h | h
    · have h2 := orderOf_dvd_of_pow_eq_one h
      rw [ho] at h2
      norm_num at h2
    · rw [h]

theorem orderOf_mul_eq_four (S : Setting G) {x y : G} (hx : x ∈ S.QG) (hy : y ∈ S.QG)
    (hx2 : x * x = 1) (hy2 : y * y = 1) (hxy : x * y ≠ y * x) : orderOf (x * y) = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  have hsq : ¬ (x * y) ^ 2 ^ 1 = 1 := by
    intro h
    apply hxy
    have h1 : (x * y) * (x * y) = 1 := by rw [← _root_.sq]; simpa using h
    calc x * y = (x * y)⁻¹ := eq_inv_of_mul_eq_one_left h1
      _ = y * x := by rw [mul_inv_rev, hxi, hyi]
  have h4 : (x * y) ^ 2 ^ (1 + 1) = 1 := by
    simpa using S.pow_four_eq_one (S.QG.mul_mem hx hy)
  simpa using orderOf_eq_prime_pow hsq h4

theorem isReducible_of_commute (S : Setting G) (hw : 0 < S.width) {a : G} (ha : IsConj S.z a)
    (haQ : a ∈ S.QG) (hne : a ≠ S.z)
    (hcomm : ∀ x y : G, IsConj S.z x → x ∈ S.QG → IsConj S.z y → y ∈ S.QG → x * y = y * x) :
    S.IsReducible := by
  set W : Submodule (ZMod 2) S.Qt :=
    Submodule.span (ZMod 2) {v | ∃ x : G, IsConj S.z x ∧ x ∈ S.QG ∧ S.cl x = v} with hWdef
  have ha0 : S.cl a ≠ 0 := by
    rw [ne_eq, S.cl_eq_zero_iff haQ]
    rintro (h | h)
    · obtain ⟨c, hc⟩ := isConj_iff.mp ha
      apply S.z_ne_one
      rw [h] at hc
      calc S.z = c⁻¹ * (c * S.z * c⁻¹) * c := by group
        _ = 1 := by rw [hc]; group
    · exact hne h
  have haW : S.cl a ∈ W := Submodule.subset_span ⟨a, ha, haQ, rfl⟩
  have hiso : W ≤ LinearMap.BilinForm.orthogonal S.q.polarBilin W := by
    rw [hWdef, Submodule.span_le]
    rintro v ⟨y, hy, hyQ, rfl⟩
    rw [SetLike.mem_coe, LinearMap.BilinForm.mem_orthogonal_iff]
    intro u hu
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨x, hx, hxQ, rfl⟩ := hu
      change S.q.polarBilin (S.cl x) (S.cl y) = 0
      rw [polarBilin_apply_apply, S.polar_cl_eq_zero_iff hxQ hyQ]
      exact hcomm x y hx hxQ hy hyQ
    | zero =>
      change S.q.polarBilin 0 (S.cl y) = 0
      rw [map_zero, LinearMap.zero_apply]
    | add u u' _ _ h1 h2 =>
      change S.q.polarBilin (u + u') (S.cl y) = 0
      rw [map_add, LinearMap.add_apply, h1, h2, add_zero]
    | smul c u _ h =>
      change S.q.polarBilin (c • u) (S.cl y) = 0
      rw [map_smul, LinearMap.smul_apply, h, smul_zero]
  have hdim : finrank (ZMod 2) W ≤ S.width := by
    have h1 := LinearMap.BilinForm.finrank_orthogonal S.q_nondegenerate W
    have h2 := Submodule.finrank_mono hiso
    rw [S.finrank_Qt_eq_two_mul_width] at h1
    omega
  refine ⟨W, fun h => ha0 ((Submodule.mem_bot _).mp (h ▸ haW)), fun h => ?_, ?_⟩
  · rw [h, finrank_top, S.finrank_Qt_eq_two_mul_width] at hdim
    omega
  · intro m v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨x, hx, hxQ, rfl⟩ := hv
      rw [S.ρ_cl m hxQ]
      exact Submodule.subset_span ⟨_, hx.trans (isConj_iff.mpr ⟨m, rfl⟩),
        S.conj_mem_QG m.2 hxQ, rfl⟩
    | zero => rw [map_zero]; exact W.zero_mem
    | add v v' _ _ h1 h2 => rw [map_add]; exact W.add_mem h1 h2
    | smul c v _ h => rw [map_smul]; exact W.smul_mem c h

omit [Finite G] in
theorem mul_self_eq_one_of_isConj (S : Setting G) {x : G} (hx : IsConj S.z x) : x * x = 1 := by
  rw [← _root_.sq, ← S.orderOf_of_isConj hx, pow_orderOf_eq_one]

theorem two_pow_dvd_card_timmesfeldPSU_twelve : 2 ^ 38 ∣ Nat.card (timmesfeldPSU 12) := by
  rw [Nat.card_congr ((timmesfeldPSUEquiv (n := 12) (by norm_num)).trans
    (ClassicalGroups.UnitaryFlag.unitaryPSUEquiv unitaryFieldData_two_one
      (n := 12) (by norm_num))).toEquiv,
    Timmesfeld.ClassicalOrders.card_statedProj_statedSU Nat.prime_two le_rfl
      (by rw [GaloisField.card 2 2 (by norm_num)]; norm_num) (by norm_num)]
  decide

theorem factorization_card_psl (m : ℕ) :
    (Nat.card (PSL(m, ZMod 2))).factorization 2 = m * (m - 1) / 2 := by
  rw [Nat.card_congr ((DW.slEquivPSL m).symm.trans
    (CFSG.QuasithinUnique.Setup.Family.slEquivGL m)).toEquiv,
    GLR.factorization_card_GL_zmod_two]

theorem exists_isConj_orderOf_mul_eq_four [IsSimpleGroup G] (hAS : AschbacherSmithWideInput)
    (hDW : DW.DW37Statement) (S : Setting G) (hw : S.width = 10)
    (hU : Nonempty (Mbar0 S ≃* timmesfeldPSU 6)) :
    ∃ a b : G, IsConj S.z a ∧ IsConj S.z b ∧ orderOf (a * b) = 4 := by
  have h2 := factorization_card_of_U6 S hw hU
  by_cases hW : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ = S.z
  · exfalso
    obtain ⟨e⟩ := hAS G S (by omega) hW
    rw [hw] at e
    have h38 : 2 ^ 38 ∣ Nat.card G := by
      rw [Nat.card_congr e.toEquiv]
      exact two_pow_dvd_card_timmesfeldPSU_twelve
    have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp h38
    omega
  · push Not at hW
    obtain ⟨g, hgQ, hne⟩ := hW
    by_contra hno
    have hcomm : ∀ x y : G, IsConj S.z x → x ∈ S.QG → IsConj S.z y → y ∈ S.QG →
        x * y = y * x := by
      intro x y hx hxQ hy hyQ
      by_contra hxy
      exact hno ⟨x, y, hx, hy, orderOf_mul_eq_four S hxQ hyQ (mul_self_eq_one_of_isConj S hx)
        (mul_self_eq_one_of_isConj S hy) hxy⟩
    obtain ⟨e⟩ := hDW G S g (by omega) hgQ hne
      (isReducible_of_commute S (by omega) (isConj_iff.mpr ⟨g, rfl⟩) hgQ hne hcomm)
    have h66 : (Nat.card G).factorization 2 = (S.width + 2) * (S.width + 2 - 1) / 2 := by
      rw [Nat.card_congr e.toEquiv]
      exact factorization_card_psl _
    rw [hw] at h66
    omega

end SmithQ

end CFSG.LargeExtraspecial.S14
