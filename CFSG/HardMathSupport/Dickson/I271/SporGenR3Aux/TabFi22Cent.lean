module

public import Certificates.Certificate17336
public import CFSG.Monster.B.Fischer.Fi22Order

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabFi22Cent

open Subgroup CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Monster.B.Mathieu CFSG.Monster.B.Fischer CFSG.RankThree.Native

section Basic

@[expose] noncomputable def dPerm : Equiv.Perm (Fin 3510) := permOfArr 3510 (dArr ())

@[expose] noncomputable def xPerm : Equiv.Perm (Fin 3510) := permOfArr 3510 (xArr ())

theorem cent_facts : Rep 3510 (dArr ()) dPerm ∧ Rep 3510 (xArr ()) xPerm ∧
    dPerm ∈ fi22P ∧ xPerm ∈ fi22P ∧ dPerm * dPerm = 1 ∧ xPerm ^ 3 = 1 ∧ xPerm ≠ 1 ∧
    (dPerm * xPerm) * (dPerm * xPerm) = 1 ∧ xPerm 0 = 1 ∧ xPerm 1 ≠ 0 ∧ xPerm 1 ≠ 1 ∧
    Nat.card {v : Fin 3510 // xPerm v = v} = 126 ∧
    (∀ g ∈ fi22P, g 0 = 0 → g * dPerm = dPerm * g) ∧
    (∀ g ∈ fi22P, g 0 = 0 → g 1 = 1 → g * xPerm = xPerm * g) ∧
    (∀ g ∈ fi22P, g * xPerm = xPerm * g → g 0 = 0 ∨ g 0 = 1 ∨ g 0 = xPerm 1) := by
  obtain ⟨d, x, hd, hx, rest⟩ := Certificates.certificate17336
  have e1 : dPerm = d := CFSG.Monster.B.Mathieu.permOfArr_eq_of_rep hd
  have e2 : xPerm = x := CFSG.Monster.B.Mathieu.permOfArr_eq_of_rep hx
  rw [e1, e2]
  exact ⟨hd, hx, rest⟩

theorem card_fix_xPerm : Nat.card {v : Fin 3510 // xPerm v = v} = 126 :=
  cent_facts.2.2.2.2.2.2.2.2.2.2.2.1

theorem rep_xPerm : Rep 3510 (xArr ()) xPerm := cent_facts.2.1

theorem xPerm_pow_three : xPerm ^ 3 = 1 := cent_facts.2.2.2.2.2.1

theorem xPerm_ne_one : xPerm ≠ 1 := cent_facts.2.2.2.2.2.2.1

end Basic

section Chain

theorem fi22_hQ : ValidSchreier fi22Chain := fi22Chain_valid.1

theorem xPerm_mem : xPerm ∈ fi22P := cent_facts.2.2.2.1

theorem base_take_two : fi22Chain.base.toList.take 2 = [(0 : Fin 3510), 1] := by rfl

theorem lev2_comm_x : ∀ h ∈ fi22Chain.levelSubgroup 2, h * xPerm = xPerm * h := by
  intro h hh
  rw [RawSchreierDatum.mem_levelSubgroup_iff _ fi22_hQ 2 (by decide), base_take_two] at hh
  exact cent_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h hh.1 (hh.2 0 (by simp)) (hh.2 1 (by simp))

theorem xPerm_zero : xPerm 0 = 1 := cent_facts.2.2.2.2.2.2.2.2.1

theorem xPerm_one_ne_zero : xPerm 1 ≠ 0 := cent_facts.2.2.2.2.2.2.2.2.2.1

theorem xPerm_one_ne_one : xPerm 1 ≠ 1 := cent_facts.2.2.2.2.2.2.2.2.2.2.1

theorem mem_lev2_iff (g : Equiv.Perm (Fin 3510)) :
    g ∈ fi22Chain.levelSubgroup 2 ↔ g ∈ fi22P ∧ g 0 = 0 ∧ g 1 = 1 := by
  rw [RawSchreierDatum.mem_levelSubgroup_iff _ fi22_hQ 2 (by decide), base_take_two]
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq]
  rfl

theorem mem_lev2_of_g0_gen {x g : Equiv.Perm (Fin 3510)} (hx0 : x 0 = 1) (hxP : x ∈ fi22P)
    (hgP : g ∈ fi22P) (hgx : g * x = x * g) {j : ℕ} (hj : g 0 = (x ^ j) 0) :
    (x ^ j)⁻¹ * g ∈ fi22Chain.levelSubgroup 2 := by
  rw [mem_lev2_iff]
  have hxjP : x ^ j ∈ fi22P := Subgroup.pow_mem _ hxP j
  have hcomm : (x ^ j)⁻¹ * g * x = x * ((x ^ j)⁻¹ * g) := by
    have h1 : x * (x ^ j)⁻¹ = (x ^ j)⁻¹ * x := ((Commute.refl x).pow_right j).inv_right.eq
    calc (x ^ j)⁻¹ * g * x = (x ^ j)⁻¹ * (g * x) := by rw [mul_assoc]
      _ = (x ^ j)⁻¹ * (x * g) := by rw [hgx]
      _ = ((x ^ j)⁻¹ * x) * g := by rw [← mul_assoc]
      _ = (x * (x ^ j)⁻¹) * g := by rw [h1]
      _ = x * ((x ^ j)⁻¹ * g) := by rw [mul_assoc]
  have h0 : ((x ^ j)⁻¹ * g) 0 = 0 := by
    show (x ^ j)⁻¹ (g 0) = 0
    rw [hj]
    simp
  refine ⟨(fi22P).mul_mem ((fi22P).inv_mem hxjP) hgP, h0, ?_⟩
  calc ((x ^ j)⁻¹ * g) 1 = ((x ^ j)⁻¹ * g) (x 0) := by rw [hx0]
    _ = (((x ^ j)⁻¹ * g) * x) 0 := rfl
    _ = (x * ((x ^ j)⁻¹ * g)) 0 := by rw [hcomm]
    _ = x (((x ^ j)⁻¹ * g) 0) := rfl
    _ = 1 := by rw [h0, hx0]

theorem mem_lev2_of_g0 {g : Equiv.Perm (Fin 3510)} (hgP : g ∈ fi22P)
    (hgx : g * xPerm = xPerm * g) {j : ℕ} (hj : g 0 = (xPerm ^ j) 0) :
    (xPerm ^ j)⁻¹ * g ∈ fi22Chain.levelSubgroup 2 :=
  mem_lev2_of_g0_gen xPerm_zero xPerm_mem hgP hgx hj

theorem cent_decomp {g : Equiv.Perm (Fin 3510)} (hgP : g ∈ fi22P)
    (hgx : g * xPerm = xPerm * g) :
    ∃ j : ℕ, j < 3 ∧ (xPerm ^ j)⁻¹ * g ∈ fi22Chain.levelSubgroup 2 := by
  rcases cent_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2 g hgP hgx with h0 | h1 | h2
  · refine ⟨0, by norm_num, mem_lev2_of_g0 hgP hgx ?_⟩
    rw [pow_zero, Equiv.Perm.coe_one, id]
    exact h0
  · refine ⟨1, by norm_num, mem_lev2_of_g0 hgP hgx ?_⟩
    rw [pow_one, xPerm_zero]
    exact h1
  · refine ⟨2, by norm_num, mem_lev2_of_g0 hgP hgx ?_⟩
    rw [pow_two, Equiv.Perm.mul_apply, xPerm_zero]
    exact h2

theorem card_lev2 : Nat.card ↥(fi22Chain.levelSubgroup 2) = 6531840 := by
  rw [RawSchreierDatum.level_card_eq_orbit_product _ fi22_hQ 2 (by decide)]
  simp only [← RawSchreierDatum.orbitSize_eq_card, fi22Chain_orbitSize]
  rfl

theorem orbit_cent_zero_gen {x : Equiv.Perm (Fin 3510)} (hx0 : x 0 = 1) (hxP : x ∈ fi22P)
    (hdec : ∀ g ∈ fi22P, g * x = x * g →
      ∃ j : ℕ, j < 3 ∧ (x ^ j)⁻¹ * g ∈ fi22Chain.levelSubgroup 2) :
    MulAction.orbit ↥(Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin 3510))) ⊓ fi22P)
      (0 : Fin 3510) = {0, 1, x 1} := by
  ext y
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨g, hy⟩
    have hy' : (g : Equiv.Perm (Fin 3510)) 0 = y := hy
    have hgx : (g : Equiv.Perm (Fin 3510)) * x = x * g :=
      (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 g.2).1)
    obtain ⟨j, hj, hm⟩ := hdec _ (Subgroup.mem_inf.1 g.2).2 hgx
    have hg0 : (g : Equiv.Perm (Fin 3510)) 0 = (x ^ j) 0 := by
      have := ((mem_lev2_iff _).1 hm).2.1
      rw [Equiv.Perm.mul_apply] at this
      have h2 := congrArg (x ^ j) this
      simpa using h2
    rw [hg0] at hy'
    interval_cases j
    · left; rw [← hy']; simp
    · right; left; rw [← hy', pow_one, hx0]
    · right; right; rw [← hy', pow_two, Equiv.Perm.mul_apply, hx0]
  · intro hy
    have hxc : ∀ n : ℕ, x ^ n ∈ Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin 3510))) ⊓ fi22P :=
      fun n => Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2
        ((Commute.refl x).pow_right n).eq.symm, Subgroup.pow_mem _ hxP n⟩
    rcases hy with rfl | rfl | rfl
    · exact ⟨1, one_smul _ _⟩
    · exact ⟨⟨x ^ 1, hxc 1⟩, by show (x ^ 1) 0 = 1; rw [pow_one, hx0]⟩
    · exact ⟨⟨x ^ 2, hxc 2⟩, by show (x ^ 2) 0 = x 1; rw [pow_two, Equiv.Perm.mul_apply, hx0]⟩

theorem card_cent_eq_gen {x : Equiv.Perm (Fin 3510)} (hx0 : x 0 = 1) (hxP : x ∈ fi22P)
    (hx10 : x 1 ≠ 0) (hx11 : x 1 ≠ 1)
    (hdec : ∀ g ∈ fi22P, g * x = x * g →
      ∃ j : ℕ, j < 3 ∧ (x ^ j)⁻¹ * g ∈ fi22Chain.levelSubgroup 2)
    (hM : ∀ m ∈ fi22Chain.levelSubgroup 2, m * x = x * m) :
    Nat.card ↥(Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin 3510))) ⊓ fi22P) =
      3 * Nat.card ↥(fi22Chain.levelSubgroup 2) := by
  set C := Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin 3510))) ⊓ fi22P with hC
  have h1 := (MulAction.stabilizer ↥C (0 : Fin 3510)).card_mul_index
  rw [MulAction.index_stabilizer] at h1
  have horb : (MulAction.orbit ↥C (0 : Fin 3510)).ncard = 3 := by
    rw [orbit_cent_zero_gen hx0 hxP hdec]
    have h01 : (0 : Fin 3510) ≠ 1 := by decide
    have hx1' : (1 : Fin 3510) ≠ x 1 := fun h => hx11 h.symm
    have hx0' : (0 : Fin 3510) ≠ x 1 := fun h => hx10 h.symm
    rw [Set.ncard_insert_of_notMem, Set.ncard_pair hx1']
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨h01, hx0'⟩
  have hstab : Nat.card ↥(MulAction.stabilizer ↥C (0 : Fin 3510)) =
      Nat.card ↥(fi22Chain.levelSubgroup 2) := by
    refine Nat.card_congr
      { toFun := fun m => ⟨(m : ↥C).1, ?_⟩
        invFun := fun m => ⟨⟨m.1, ?_⟩, ?_⟩
        left_inv := fun m => rfl
        right_inv := fun m => rfl }
    · have hm0 : ((m : ↥C) : Equiv.Perm (Fin 3510)) 0 = 0 := m.2
      have hgx : ((m : ↥C) : Equiv.Perm (Fin 3510)) * x = x * (m : ↥C) :=
        (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 (m : ↥C).2).1)
      have := mem_lev2_of_g0_gen hx0 hxP (Subgroup.mem_inf.1 (m : ↥C).2).2 hgx (j := 0)
        (by rw [hm0]; simp)
      simpa using this
    · exact Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 (hM m.1 m.2),
        ((mem_lev2_iff _).1 m.2).1⟩
    · exact ((mem_lev2_iff _).1 m.2).2.1
  rw [horb, hstab] at h1
  omega

theorem card_cent_eq : Nat.card ↥(Subgroup.centralizer ({xPerm} : Set (Equiv.Perm (Fin 3510))) ⊓
    fi22P) = 3 * 6531840 := by
  rw [card_cent_eq_gen xPerm_zero xPerm_mem xPerm_one_ne_zero xPerm_one_ne_one
    (fun g hg hgx => cent_decomp hg hgx) lev2_comm_x, card_lev2]

end Chain

end CFSG.HardMathSupport.Dickson.I271.TabFi22Cent
