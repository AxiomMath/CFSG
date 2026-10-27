module

public import CFSG.ClassicalInvolution.Q3.Q3T6BAutCO
public import CFSG.ClassicalInvolution.Q3.Q3T6AutUni
public import CFSG.ClassicalInvolution.Q3.Q3T6BSwap

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6B

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Hat2A7
  CFSG.ClassicalInvolution.Uniform.U4
open scoped commutatorElement MatrixGroups

variable {F : Type} [Group F] [Finite F]

theorem exists_action {Y : Subgroup F} {y : F} (hY : Mem3 Y y) :
    ∃ ρ : ↥(Subgroup.normalizer (Y : Set F)) →* MulAut SL(2, ZMod 3),
      ∀ n : ↥(Subgroup.normalizer (Y : Set F)), ρ n = 1 ↔ ∀ l ∈ Y, ⁅(n : F), l⁆ ∈ oddCoreOf Y := by
  obtain ⟨e⟩ := Q3T6.nonempty_equiv_of_memberU hY.member
  exact ⟨Q3T6.normalizerToAutSL3 e, fun n => Q3T6.normalizerToAutSL3_eq_one_iff e n⟩

theorem exists_comm_order_four_of_trivial {Y : Subgroup F} {y x : F} (hY : Mem3 Y y)
    (hxN : x ∈ Subgroup.normalizer (Y : Set F)) (hx2 : x * x = 1)
    (htriv : ∀ k ∈ Y, ⁅x, k⁆ ∈ oddCoreOf Y) : ∃ a ∈ Y, orderOf a = 4 ∧ a * x = x * a := by
  classical
  have hy2 : y * y = 1 := hY.mul_self
  set T : Subgroup F := Subgroup.zpowers x with hT
  have hT2 : IsPGroup 2 T := Balance.isPGroup_zpowers_of_mul_self_eq_one hx2
  have hTN : T ≤ Subgroup.normalizer (Y : Set F) := Subgroup.zpowers_le.mpr hxN
  set H : Subgroup F := Y ⊔ T with hH
  have hYH : Y ≤ H := le_sup_left
  have hHN : H ≤ Subgroup.normalizer (Y : Set F) := sup_le Subgroup.le_normalizer hTN
  obtain ⟨R, hRH, hTR⟩ := Asc77.IsSylow2In.exists_ge hT2 (le_sup_right : T ≤ H)
  have hR2 : IsPGroup 2 R := hRH.2.1
  have hxR : x ∈ R := hTR (Subgroup.mem_zpowers x)
  have hRY : IsSylow2In (R ⊓ Y) Y := isSylow2In_inf_of_le_normalizer hRH hYH hHN
  obtain ⟨a, haR, ha2⟩ := exists_sq_eq_of_isSylow2In hY hRY
  have haY : a ∈ Y := haR.2
  have h1 : ⁅x, a⁆ ∈ oddCoreOf Y := htriv a haY
  have h2 : ⁅x, a⁆ ∈ R := by
    rw [commutatorElement_def]
    exact R.mul_mem (R.mul_mem (R.mul_mem hxR haR.1) (R.inv_mem hxR)) (R.inv_mem haR.1)
  have h3 : ⁅x, a⁆ = 1 :=
    eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard Y) h1
      (hR2.to_le (Subgroup.zpowers_le.mpr h2))
  have hxa : a * x = x * a := (commutatorElement_eq_one_iff_mul_comm.mp h3).symm
  have hap : IsPGroup 2 (Subgroup.zpowers a) := hR2.to_le (Subgroup.zpowers_le.mpr haR.1)
  have h4 : 4 ≤ orderOf a := four_le_orderOf hap (by rw [ha2]; exact hY.ne_one)
  have h4' : orderOf a ∣ 4 := by
    apply orderOf_dvd_of_pow_eq_one
    calc a ^ 4 = (a * a) * (a * a) := by
          rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
      _ = 1 := by rw [ha2, hy2]
  exact ⟨a, haY, Nat.le_antisymm (Nat.le_of_dvd (by norm_num) h4') h4, hxa⟩

theorem act_trivial_of_odd {Y : Subgroup F}
    (ρ : ↥(Subgroup.normalizer (Y : Set F)) →* MulAut SL(2, ZMod 3)) {x g : F}
    (hxN : x ∈ Subgroup.normalizer (Y : Set F)) (hx2 : x * x = 1) (hρx : ρ ⟨x, hxN⟩ ≠ 1)
    (hgN : g ∈ Subgroup.normalizer (Y : Set F)) (hgx : g * x = x * g) (hodd : Odd (orderOf g)) :
    ρ ⟨g, hgN⟩ = 1 := by
  refine mulAut_eq_one_of_odd_commute_involution (ρ ⟨x, hxN⟩) (ρ ⟨g, hgN⟩) ?_ hρx ?_ ?_
  · rw [← map_mul]
    have : (⟨x, hxN⟩ * ⟨x, hxN⟩ : ↥(Subgroup.normalizer (Y : Set F))) = 1 :=
      Subtype.ext hx2
    rw [this, map_one]
  · rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hgx
  · exact hodd.of_dvd_nat (orderOf_map_dvd ρ ⟨g, hgN⟩ |>.trans
      (by rw [Subgroup.orderOf_mk]))

theorem closure_act_trivial {Y : Subgroup F}
    (ρ : ↥(Subgroup.normalizer (Y : Set F)) →* MulAut SL(2, ZMod 3)) {S : Set F}
    (hS : ∀ g ∈ S, ∃ hg : g ∈ Subgroup.normalizer (Y : Set F), ρ ⟨g, hg⟩ = 1) :
    ∀ d ∈ Subgroup.closure S, ∃ hd : d ∈ Subgroup.normalizer (Y : Set F), ρ ⟨d, hd⟩ = 1 := by
  let K : Subgroup F := ρ.ker.map (Subgroup.normalizer (Y : Set F)).subtype
  have hK : Subgroup.closure S ≤ K := (Subgroup.closure_le K).mpr fun g hg => by
    obtain ⟨hgN, hg1⟩ := hS g hg
    exact ⟨⟨g, hgN⟩, hg1, rfl⟩
  intro d hd
  obtain ⟨n, hn, rfl⟩ := hK hd
  exact ⟨n.2, hn⟩

end CFSG.ClassicalInvolution.Q3.Q3T6B
