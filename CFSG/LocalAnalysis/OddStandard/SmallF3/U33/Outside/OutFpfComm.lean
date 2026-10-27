module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutFpf
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.Outside

open Subgroup
open scoped commutatorElement

variable {S : Type} [Group S] [Finite S]

private theorem center_map_rho (ρ : MulAut S) :
    (center S).map ρ.toMonoidHom = center S :=
  map_eq_of_forall_mem ρ (center S) fun n hn => rho_mem_center ρ hn

private theorem rho_cube_apply (ρ : MulAut S) (hρ : ρ ^ 3 = 1) (a : S) :
    ρ (ρ (ρ a)) = a := by
  have h := congrArg (fun f : MulAut S => f a) hρ
  simpa [pow_succ, MulAut.mul_apply] using h

private theorem commutator_mem_center_of_card_quot_center_four
    (h4 : Nat.card (S ⧸ center S) = 4) (x y : S) : ⁅x, y⁆ ∈ center S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcomm : IsMulCommutative (S ⧸ center S) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (G := S ⧸ center S) (by
      rw [h4]; norm_num)
  have hle : commutator S ≤ center S :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := center S)).mp hcomm
  exact hle (Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y))

private theorem commutatorElement_mul_right_of_central
    (hc : ∀ p q : S, ⁅p, q⁆ ∈ center S) (a b c : S) :
    ⁅a, b * c⁆ = ⁅a, b⁆ * ⁅a, c⁆ := by
  rw [commutatorElement_mul_right_eq_mul_conj, mul_assoc (⁅a, b⁆) b ⁅a, c⁆,
    Subgroup.mem_center_iff.mp (hc a c) b]
  group

private theorem commutatorElement_inv_right_of_central
    (hc : ∀ p q : S, ⁅p, q⁆ ∈ center S) (a b : S) :
    ⁅a, b⁻¹⁆ = ⁅a, b⁆⁻¹ := by
  have hmem : ⁅a, b⁆⁻¹ ∈ center S := (center S).inv_mem (hc a b)
  rw [commutatorElement_inv_right, ← commutatorElement_inv a b, mul_assoc,
    ← Subgroup.mem_center_iff.mp hmem b]
  group

private theorem commutator_rho_self_eq_one (ρ : MulAut S) (hρ : ρ ^ 3 = 1)
    (hfpf : ∀ g : S, ρ g = g → g = 1) (h4 : Nat.card (S ⧸ center S) = 4) (x : S) :
    ⁅x, ρ x⁆ = 1 := by
  have hc : ∀ p q : S, ⁅p, q⁆ ∈ center S :=
    fun p q => commutator_mem_center_of_card_quot_center_four h4 p q
  have hN : (center S).map ρ.toMonoidHom = center S := center_map_rho ρ
  let qa : MulAut (S ⧸ center S) := quotAut ρ (center S) hN
  have hq3 : qa ^ 3 = 1 := quotAut_pow_three ρ hρ (center S) hN
  have hqfpf : ∀ q : S ⧸ center S, qa q = q → q = 1 :=
    quotAut_fpf ρ hρ hfpf (center S) hN
  have hburn := forall_mul_rho_rho_sq qa hq3 hqfpf (QuotientGroup.mk x)
  have hx1 : qa (QuotientGroup.mk x) = QuotientGroup.mk (ρ x) :=
    quotAut_mk ρ (center S) hN x
  have hx2 : qa (qa (QuotientGroup.mk x)) = QuotientGroup.mk (ρ (ρ x)) := by
    rw [hx1, quotAut_mk ρ (center S) hN (ρ x)]
  rw [hx2, hx1] at hburn
  set z : S := x * ρ x * ρ (ρ x) with hz_def
  have hburn' : (QuotientGroup.mk z : S ⧸ center S) = 1 := by
    rw [hz_def]
    simpa only [QuotientGroup.mk_mul] using hburn
  have hzmem : z ∈ center S := (QuotientGroup.eq_one_iff z).mp hburn'
  have hz : ρ (ρ x) = (x * ρ x)⁻¹ * z := by
    rw [hz_def, ← mul_assoc, inv_mul_cancel, one_mul]
  have h3 : ⁅ρ x, ρ (ρ x)⁆ = ⁅x, ρ x⁆ := by
    rw [hz, commutatorElement_mul_right_of_central hc,
      commutatorElement_inv_right_of_central hc,
      commutatorElement_mul_right_of_central hc,
      commutatorElement_self, mul_one, commutatorElement_inv,
      commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hzmem (ρ x)),
      mul_one]
  have hkey : ρ ⁅x, ρ x⁆ = ⁅x, ρ x⁆ := by
    rw [map_commutatorElement]
    exact h3
  exact hfpf ⁅x, ρ x⁆ hkey

private theorem coset_cover (ρ : MulAut S) (hρ : ρ ^ 3 = 1)
    (hfpf : ∀ g : S, ρ g = g → g = 1) (h4 : Nat.card (S ⧸ center S) = 4)
    {a : S} (ha : a ∉ center S) (b : S) :
    (QuotientGroup.mk b : S ⧸ center S) = 1 ∨
    (QuotientGroup.mk b : S ⧸ center S) = QuotientGroup.mk a ∨
    (QuotientGroup.mk b : S ⧸ center S) = QuotientGroup.mk (ρ a) ∨
    (QuotientGroup.mk b : S ⧸ center S) = QuotientGroup.mk (ρ (ρ a)) := by
  classical
  haveI : Fintype (S ⧸ center S) := Fintype.ofFinite _
  have hN : (center S).map ρ.toMonoidHom = center S := center_map_rho ρ
  let qa : MulAut (S ⧸ center S) := quotAut ρ (center S) hN
  have hqfpf : ∀ q : S ⧸ center S, qa q = q → q = 1 :=
    quotAut_fpf ρ hρ hfpf (center S) hN
  have hrho3 : ρ (ρ (ρ a)) = a := rho_cube_apply ρ hρ a
  let f : Fin 4 → (S ⧸ center S) :=
    ![1, QuotientGroup.mk a, QuotientGroup.mk (ρ a), QuotientGroup.mk (ρ (ρ a))]
  have ha1 : (QuotientGroup.mk a : S ⧸ center S) ≠ 1 := by
    intro h
    exact ha ((QuotientGroup.eq_one_iff a).mp h)
  have hra1 : (QuotientGroup.mk (ρ a) : S ⧸ center S) ≠ 1 := by
    intro h
    have h1 : ρ a ∈ center S := (QuotientGroup.eq_one_iff (ρ a)).mp h
    exact ha (by simpa using rho_mem_center (ρ⁻¹) h1)
  have hr2a1 : (QuotientGroup.mk (ρ (ρ a)) : S ⧸ center S) ≠ 1 := by
    intro h
    have h1 : ρ (ρ a) ∈ center S := (QuotientGroup.eq_one_iff (ρ (ρ a))).mp h
    have h2 : ρ a ∈ center S := by simpa using rho_mem_center (ρ⁻¹) h1
    exact ha (by simpa using rho_mem_center (ρ⁻¹) h2)
  have hara : (QuotientGroup.mk a : S ⧸ center S) ≠ QuotientGroup.mk (ρ a) := by
    intro h
    have h1 : qa (QuotientGroup.mk a) = QuotientGroup.mk a := by
      rw [quotAut_mk]; exact h.symm
    exact ha1 (hqfpf _ h1)
  have har2a : (QuotientGroup.mk a : S ⧸ center S) ≠ QuotientGroup.mk (ρ (ρ a)) := by
    intro h
    have h1 : qa (QuotientGroup.mk a) = qa (QuotientGroup.mk (ρ (ρ a))) := by rw [h]
    rw [quotAut_mk, quotAut_mk, hrho3] at h1
    exact hara h1.symm
  have hrar2a : (QuotientGroup.mk (ρ a) : S ⧸ center S) ≠
      QuotientGroup.mk (ρ (ρ a)) := by
    intro h
    have h1 : qa (QuotientGroup.mk (ρ a)) = qa (QuotientGroup.mk (ρ (ρ a))) := by rw [h]
    rw [quotAut_mk, quotAut_mk, hrho3] at h1
    exact har2a h1.symm
  have h01 : f 0 ≠ f 1 := by
    simp only [f, Fin.cons_zero, Fin.cons_succ]
    exact fun h => ha1 h.symm
  have h02 : f 0 ≠ f 2 := by
    simp only [f, Fin.cons_zero, Fin.cons_succ]
    exact fun h => hra1 h.symm
  have h03 : f 0 ≠ f 3 := by
    simp only [f, Fin.cons_zero, Fin.cons_succ]
    exact fun h => hr2a1 h.symm
  have h12 : f 1 ≠ f 2 := by
    simp only [f, Fin.cons_zero, Fin.cons_succ]
    exact hara
  have h13 : f 1 ≠ f 3 := by
    simp only [f, Fin.cons_zero, Fin.cons_succ]
    exact har2a
  have h23 : f 2 ≠ f 3 := by
    simp only [f, Fin.cons_zero, Fin.cons_succ]
    exact hrar2a
  have hfinj : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
      | rfl
      | exact absurd hij (by assumption)
      | exact absurd hij.symm (by assumption)
  have hcard : Fintype.card (Fin 4) = Fintype.card (S ⧸ center S) := by
    rw [Fintype.card_fin, ← Nat.card_eq_fintype_card]
    exact h4.symm
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hfinj, hcard⟩
  obtain ⟨i, hi⟩ := hbij.2 (QuotientGroup.mk b)
  fin_cases i
  · left; simpa [f] using hi.symm
  · right; left; simpa [f] using hi.symm
  · right; right; left; simpa [f] using hi.symm
  · right; right; right; simpa [f] using hi.symm

private theorem commutator_notMem_center_eq_one (ρ : MulAut S) (hρ : ρ ^ 3 = 1)
    (hfpf : ∀ g : S, ρ g = g → g = 1) (h4 : Nat.card (S ⧸ center S) = 4)
    {a : S} (ha : a ∉ center S) (b : S) : ⁅a, b⁆ = 1 := by
  have hc : ∀ p q : S, ⁅p, q⁆ ∈ center S :=
    fun p q => commutator_mem_center_of_card_quot_center_four h4 p q
  have h1 : ⁅a, ρ a⁆ = 1 := commutator_rho_self_eq_one ρ hρ hfpf h4 a
  have h2 : ⁅a, ρ (ρ a)⁆ = 1 := by
    have hmap : ρ ⁅a, ρ (ρ a)⁆ = ⁅ρ a, ρ (ρ (ρ a))⁆ :=
      map_commutatorElement ρ a (ρ (ρ a))
    rw [rho_cube_apply ρ hρ a] at hmap
    have hraa : ⁅ρ a, a⁆ = 1 := by
      rw [(commutatorElement_inv a (ρ a)).symm, h1, inv_one]
    rw [hraa] at hmap
    exact ρ.injective (hmap.trans (map_one ρ).symm)
  rcases coset_cover ρ hρ hfpf h4 ha b with hb | hb | hb | hb
  · have hbc : b ∈ center S := (QuotientGroup.eq_one_iff b).mp hb
    exact commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hbc a)
  · have hdiv : b / a ∈ center S := (QuotientGroup.eq_iff_div_mem).mp hb
    rw [show b = (b / a) * a from by rw [div_eq_mul_inv, mul_assoc, inv_mul_cancel, mul_one],
      commutatorElement_mul_right_of_central hc,
      commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hdiv a),
      commutatorElement_self, mul_one]
  · have hdiv : b / (ρ a) ∈ center S := (QuotientGroup.eq_iff_div_mem).mp hb
    rw [show b = (b / (ρ a)) * (ρ a) from by
        rw [div_eq_mul_inv, mul_assoc, inv_mul_cancel, mul_one],
      commutatorElement_mul_right_of_central hc,
      commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hdiv a), h1,
      mul_one]
  · have hdiv : b / (ρ (ρ a)) ∈ center S := (QuotientGroup.eq_iff_div_mem).mp hb
    rw [show b = (b / (ρ (ρ a))) * (ρ (ρ a)) from by
        rw [div_eq_mul_inv, mul_assoc, inv_mul_cancel, mul_one],
      commutatorElement_mul_right_of_central hc,
      commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hdiv a), h2,
      mul_one]

theorem comm_of_card_quot_center_four (ρ : MulAut S) (hρ : ρ ^ 3 = 1)
    (hfpf : ∀ g : S, ρ g = g → g = 1) (h4 : Nat.card (S ⧸ center S) = 4) (a b : S) :
    a * b = b * a := by
  by_cases ha : a ∈ center S
  · exact (Subgroup.mem_center_iff.mp ha b).symm
  · exact commutatorElement_eq_one_iff_mul_comm.mp
      (commutator_notMem_center_eq_one ρ hρ hfpf h4 ha b)

theorem card_quot_center_ne_four (ρ : MulAut S) (hρ : ρ ^ 3 = 1)
    (hfpf : ∀ g : S, ρ g = g → g = 1) : Nat.card (S ⧸ center S) ≠ 4 := by
  intro h4
  have htop : center S = ⊤ := by
    rw [eq_top_iff]
    intro g _
    exact Subgroup.mem_center_iff.mpr fun b => comm_of_card_quot_center_four ρ hρ hfpf h4 b g
  have h : (center S).index = 4 := h4
  rw [htop, Subgroup.index_top] at h
  omega

end CFSG.OddStandard.SmallF3.HarrisU33.Outside
