module

public import CFSG.LocalAnalysis.OddStandard.ONanDefs
public import CFSG.Sporadic.Recognition.PresentedWords
public import Certificates.Data.ONanF2Pres
public import Certificates.Data.ONanF2Model
public import CFSG.LocalAnalysis.SectionRank.Ccomm.PGroupBasics
public import Mathlib.Order.CompletePartialOrder

public section

namespace CFSG.OddStandard.ONanRec

open CFSG.Sporadic.Recognition.PresentedWords CFSG.CosetTable F2

theorem one_of_eq_mul_inv {G : Type*} [Group G] {a b c : G} (h : b = c) (e : a = b * c⁻¹) :
    a = 1 := by
  rw [e, h, mul_inv_cancel]

theorem eq_of_one_of_eq_mul_inv {G : Type*} [Group G] {a b c : G} (hA : a = 1)
    (e : a = b * c⁻¹) : b = c := by
  rw [e] at hA
  exact mul_inv_eq_one.1 hA

theorem wprod_alpRels {G : Type*} [Group G] {v1 v2 v3 s t : G} (h : AlpFrame v1 v2 v3 s t) :
    ∀ w ∈ alpRels, wprod ![v1, v2, v3, s, t] w = 1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
  simp only [pow_succ, pow_zero, one_mul] at h1 h2 h3 h4 h8
  simp only [alpRels, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  simp only [wprod, List.map, List.prod_cons, List.prod_nil, mul_one, ite_true,
    Bool.false_eq_true, ite_false, Matrix.cons_val]
  refine ⟨one_of_eq_mul_inv h1 (by group), one_of_eq_mul_inv h2 (by group),
    one_of_eq_mul_inv h3 (by group), one_of_eq_mul_inv h4 (by group),
    one_of_eq_mul_inv h5 (by group), one_of_eq_mul_inv h6 (by group),
    one_of_eq_mul_inv h7 (by group), one_of_eq_mul_inv h8 (by group),
    one_of_eq_mul_inv h9 (by group), one_of_eq_mul_inv h10 (by group),
    one_of_eq_mul_inv h11 (by group), one_of_eq_mul_inv h12 (by group),
    one_of_eq_mul_inv h13 (by group), one_of_eq_mul_inv h14 (by group),
    one_of_eq_mul_inv h15 (by group)⟩

theorem frame_of_wprod_alpRels {G : Type*} [Group G] {v1 v2 v3 s t : G}
    (h : ∀ w ∈ alpRels, wprod ![v1, v2, v3, s, t] w = 1) : AlpFrame v1 v2 v3 s t := by
  simp only [alpRels, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true] at h
  simp only [wprod, List.map, List.prod_cons, List.prod_nil, mul_one, ite_true,
    Bool.false_eq_true, ite_false, Matrix.cons_val] at h
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try simp only [pow_succ, pow_zero, one_mul]
  · exact eq_of_one_of_eq_mul_inv r1 (by group)
  · exact eq_of_one_of_eq_mul_inv r2 (by group)
  · exact eq_of_one_of_eq_mul_inv r3 (by group)
  · exact eq_of_one_of_eq_mul_inv r4 (by group)
  · exact eq_of_one_of_eq_mul_inv r5 (by group)
  · exact eq_of_one_of_eq_mul_inv r6 (by group)
  · exact eq_of_one_of_eq_mul_inv r7 (by group)
  · exact eq_of_one_of_eq_mul_inv r8 (by group)
  · exact eq_of_one_of_eq_mul_inv r9 (by group)
  · exact eq_of_one_of_eq_mul_inv r10 (by group)
  · exact eq_of_one_of_eq_mul_inv r11 (by group)
  · exact eq_of_one_of_eq_mul_inv r12 (by group)
  · exact eq_of_one_of_eq_mul_inv r13 (by group)
  · exact eq_of_one_of_eq_mul_inv r14 (by group)
  · exact eq_of_one_of_eq_mul_inv r15 (by group)

open AlpE in
theorem frame_gen : AlpFrame (gen 0) (gen 1) (gen 2) (gen 3) (gen 4) := by
  constructor <;> decide +kernel

namespace F2.AlpE

theorem card : Nat.card AlpE = 512 := by
  rw [Nat.card_congr equivProd]
  simp [ZMod.card]

theorem tr_eq : ∀ u0 u1 u2 : ZMod 4,
    (⟨0, u0, u1, u2⟩ : AlpE) = gen 0 ^ u0.val * gen 1 ^ u1.val * gen 2 ^ u2.val := by
  decide +kernel

theorem rep_eq : ∀ d : Fin 8,
    (⟨d, 0, 0, 0⟩ : AlpE) = gen 3 ^ (d.val % 4) * gen 4 ^ (d.val / 4) := by
  decide +kernel

theorem eq_tr_mul_rep : ∀ x : AlpE, x = ⟨0, x.v0, x.v1, x.v2⟩ * ⟨x.d, 0, 0, 0⟩ := by
  decide +kernel

theorem closure_range_gen : Subgroup.closure (Set.range gen) = ⊤ := by
  have hg : ∀ i, gen i ∈ Subgroup.closure (Set.range gen) := fun i =>
    Subgroup.subset_closure ⟨i, rfl⟩
  refine eq_top_iff.mpr fun x _ => ?_
  rw [eq_tr_mul_rep x, tr_eq, rep_eq]
  exact mul_mem (mul_mem (mul_mem (pow_mem (hg 0) _) (pow_mem (hg 1) _)) (pow_mem (hg 2) _))
    (mul_mem (pow_mem (hg 3) _) (pow_mem (hg 4) _))

theorem isPGroup : IsPGroup 2 AlpE :=
  IsPGroup.of_card (n := 9) (by rw [card]; norm_num)

theorem mem_center_iff : ∀ s : AlpE, (∀ g : AlpE, g * s = s * g) ↔ s = 1 ∨ s = zc := by
  decide +kernel

theorem zc_mem_of_normal {K : Subgroup AlpE} [K.Normal] (hK : K ≠ ⊥) : zc ∈ K := by
  obtain ⟨-, hle⟩ := CFSG.SectionRank.Ccomm.normal_inf_center_card isPGroup hK
  by_contra hz
  have hsub : (K ⊓ Subgroup.center AlpE : Subgroup AlpE) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxK, hxc⟩ := Subgroup.mem_inf.1 hx
    have := (mem_center_iff x).1 (fun g => ((Subgroup.mem_center_iff.1 hxc) g))
    rcases this with h | h
    · simp [h]
    · exact absurd (h ▸ hxK) hz
  rw [hsub, Subgroup.card_bot] at hle
  omega

end F2.AlpE

abbrev AlpGrp : Type := PG 5 alpRels

theorem range_pgHom' {n : ℕ} {ws : List (List (Fin n × Bool))} {G : Type*} [Group G]
    (x : Fin n → G) (hx : ∀ w ∈ ws, wprod x w = 1) :
    (pgHom x hx).range = Subgroup.closure (Set.range x) := by
  rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of, MonoidHom.map_closure,
    ← Set.range_comp]
  congr 1
  ext i
  simp [pgHom_of]

theorem wprod_gen : ∀ w ∈ alpRels, wprod AlpE.gen w = 1 := wprod_alpRels frame_gen

@[expose] noncomputable def homE : AlpGrp →* AlpE := pgHom AlpE.gen wprod_gen

theorem homE_of (i : Fin 5) : homE (PresentedGroup.of i) = AlpE.gen i := pgHom_of _ _ _

theorem surjective_homE : Function.Surjective homE := by
  rw [← MonoidHom.range_eq_top]
  unfold homE
  rw [range_pgHom', AlpE.closure_range_gen]

theorem bijective_homE (h : Finite AlpGrp ∧ Nat.card AlpGrp ≤ 512) :
    Function.Bijective homE := by
  obtain ⟨hfin, hle⟩ := h
  exact surjective_homE.bijective_of_nat_card_le (by rw [AlpE.card]; exact hle)

@[expose] noncomputable def equivAlpE (h : Finite AlpGrp ∧ Nat.card AlpGrp ≤ 512) :
    AlpGrp ≃* AlpE :=
  MulEquiv.ofBijective homE (bijective_homE h)

theorem equivAlpE_of (h : Finite AlpGrp ∧ Nat.card AlpGrp ≤ 512) (i : Fin 5) :
    equivAlpE h (PresentedGroup.of i) = AlpE.gen i := homE_of i

theorem equivAlpE_symm_gen (h : Finite AlpGrp ∧ Nat.card AlpGrp ≤ 512) (i : Fin 5) :
    (equivAlpE h).symm (AlpE.gen i) = PresentedGroup.of i := by
  rw [MulEquiv.symm_apply_eq, equivAlpE_of]

theorem AlpFrame.map {G H : Type*} [Group G] [Group H] (f : G →* H) {v1 v2 v3 s t : G}
    (h : AlpFrame v1 v2 v3 s t) : AlpFrame (f v1) (f v2) (f v3) (f s) (f t) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_pow, h1, map_one]
  · rw [← map_pow, h2, map_one]
  · rw [← map_pow, h3, map_one]
  · rw [← map_pow, h4, map_one]
  · rw [← map_mul, ← map_mul, h5]
  · rw [← map_mul, ← map_mul, h6]
  · rw [← map_mul, ← map_mul, h7]
  · rw [← map_pow, h8, map_mul]
  · rw [← map_inv, ← map_mul, ← map_mul, h9, map_inv]
  · rw [← map_inv, ← map_mul, ← map_mul, h10]
  · rw [← map_inv, ← map_mul, ← map_mul, h11]
  · rw [← map_inv, ← map_mul, ← map_mul, h12, map_mul, map_mul, map_inv]
  · rw [← map_inv, ← map_mul, ← map_mul, h13, map_inv]
  · rw [← map_inv, ← map_mul, ← map_mul, h14, map_inv]
  · rw [← map_inv, ← map_mul, ← map_mul, h15, map_inv]

namespace AlpFrame

variable {G : Type*} [Group G] {v1 v2 v3 s t : G}

@[expose] noncomputable def toG (hfr : AlpFrame v1 v2 v3 s t)
    (h : Finite AlpGrp ∧ Nat.card AlpGrp ≤ 512) : AlpE →* G :=
  (pgHom ![v1, v2, v3, s, t] (wprod_alpRels hfr)).comp (equivAlpE h).symm.toMonoidHom

theorem toG_gen (hfr : AlpFrame v1 v2 v3 s t)
    (h : Finite AlpGrp ∧ Nat.card AlpGrp ≤ 512) (i : Fin 5) :
    hfr.toG h (AlpE.gen i) = ![v1, v2, v3, s, t] i := by
  have : hfr.toG h (AlpE.gen i) = pgHom ![v1, v2, v3, s, t] (wprod_alpRels hfr)
      ((equivAlpE h).symm (AlpE.gen i)) := rfl
  rw [this, equivAlpE_symm_gen]
  exact pgHom_of ![v1, v2, v3, s, t] (wprod_alpRels hfr) i

theorem range_toG (hfr : AlpFrame v1 v2 v3 s t)
    (h : Finite AlpGrp ∧ Nat.card AlpGrp ≤ 512) :
    (hfr.toG h).range = alpP v1 v2 v3 s t := by
  rw [toG, MonoidHom.range_comp, MulEquiv.toMonoidHom_eq_coe,
    MonoidHom.range_eq_top.mpr (equivAlpE h).symm.surjective, ← MonoidHom.range_eq_map,
    range_pgHom']
  unfold alpP
  congr 1
  ext g
  simp
  tauto

theorem toG_injective (hfr : AlpFrame v1 v2 v3 s t)
    (h : Finite AlpGrp ∧ Nat.card AlpGrp ≤ 512) (hz : v1 ^ 2 * v3 ^ 2 ≠ 1) :
    Function.Injective (hfr.toG h) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  by_contra hK
  have hzm : AlpE.zc ∈ (hfr.toG h).ker := AlpE.zc_mem_of_normal hK
  apply hz
  have := MonoidHom.mem_ker.1 hzm
  rw [AlpE.zc, map_mul, map_pow, map_pow, toG_gen, toG_gen] at this
  simpa using this

end AlpFrame

end CFSG.OddStandard.ONanRec
