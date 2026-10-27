
module

public import CFSG.Sporadic.Co1.Module.OrbitsBase
public import CFSG.Certificates.Kernel.Co1M.VOrbitFull
import CFSG.Perm.OrbitTree

public section

namespace CFSG.KC.Co1Orb

open CFSG.Sporadic.Co1.Module CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.Th.Native CFSG.KC.VOrbFull CFSG.KC.VecK

theorem toVecD_surj24 (w : Vec24) : ∃ x < 2 ^ 24, toVecD 24 x = w := by
  refine ⟨ofBits 24 fun j => if h : j < 24 then decide (w ⟨j, h⟩ = 1) else false,
    ofBits_lt 24 _, ?_⟩
  funext j
  rw [toVecD_ofBits]
  simp only [j.isLt, dite_true]
  have hz : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  rcases hz (w j) with h | h <;> simp [h]

theorem vecMulN_lt24 (R : Array Nat) (hR : ∀ j : Nat, R[j]?.getD 0 < 2 ^ 24) (v : Nat) :
    vecMulN 24 R v < 2 ^ 24 := by
  have key : ∀ (m acc : Nat), acc < 2 ^ 24 →
      (List.range m).foldl (fun acc j => if v.testBit j then acc ^^^ (R[j]?.getD 0) else acc)
        acc < 2 ^ 24 := by
    intro m
    induction m with
    | zero => intro acc h; simpa using h
    | succ m ih =>
      intro acc h
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      have := ih acc h
      split_ifs
      · exact Nat.xor_lt_two_pow this (hR m)
      · exact this
  exact key 24 0 (by norm_num)

theorem cols_lt (M : Array Nat) (j : Nat) :
    (CFSG.Sporadic.SmallF2.Native.transposeRows 24 M)[j]?.getD 0 < 2 ^ 24 := by
  unfold CFSG.Sporadic.SmallF2.Native.transposeRows
  by_cases hj : j < 24
  · simp only [Array.getElem?_ofFn, hj, ↓reduceDIte, Option.getD_some]
    exact ofBits_lt _ _
  · simp [hj]

theorem fA_lt (x : Nat) : vecMulN 24 dat.colsA x < 2 ^ 24 :=
  vecMulN_lt24 _ (cols_lt _) x

theorem fB_lt (x : Nat) : vecMulN 24 dat.colsB x < 2 ^ 24 :=
  vecMulN_lt24 _ (cols_lt _) x

theorem smul_orbit {g : Jmat} {y v : Vec24} (hy : y ∈ MulAction.orbit Jmat v) :
    g • y ∈ MulAction.orbit Jmat v := by
  obtain ⟨h, rfl⟩ := hy
  exact ⟨g * h, mul_smul g h v⟩

open Classical in
noncomputable def codes (v : Nat) : Finset Nat :=
  (Finset.range (2 ^ 24)).filter fun x => toVecD 24 x ∈ MulAction.orbit Jmat (toVecD 24 v)

theorem mem_codes {v x : Nat} :
    x ∈ codes v ↔ x < 2 ^ 24 ∧ toVecD 24 x ∈ MulAction.orbit Jmat (toVecD 24 v) := by
  classical
  unfold codes
  rw [Finset.mem_filter, Finset.mem_range]

theorem codes_card (v : Nat) :
    (codes v).card = (MulAction.orbit Jmat (toVecD 24 v)).ncard := by
  have e : MulAction.orbit Jmat (toVecD 24 v) = toVecD 24 '' ↑(codes v) := by
    ext y
    constructor
    · intro hy
      obtain ⟨x, hx, rfl⟩ := toVecD_surj24 y
      exact ⟨x, mem_codes.2 ⟨hx, hy⟩, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact (mem_codes.1 hx).2
  rw [e, Set.InjOn.ncard_image (fun x hx y hy h =>
    toVecD_injective (mem_codes.1 hx).1 (mem_codes.1 hy).1 h), Set.ncard_coe_finset]

theorem codes_min {v : Nat} (hv24 : v < 2 ^ 24) (S : Set Nat)
    (hv : v ∈ S) (hS : ∀ x ∈ S, vecMulN 24 dat.colsA x ∈ S ∧ vecMulN 24 dat.colsB x ∈ S) :
    ∀ x ∈ codes v, x ∈ S := by
  intro x hx
  obtain ⟨hx24, g, hg⟩ := mem_codes.1 hx
  let F : Set Vec24 := toVecD 24 '' {y | y ∈ S ∧ y < 2 ^ 24}
  have hF : F.Finite := ((Set.finite_lt_nat (2 ^ 24)).subset fun y hy => hy.2).image _
  have hcl : ∀ s ∈ ({genA, genB} : Set Jmat), ∀ y ∈ F, s • y ∈ F := by
    rintro s hs _ ⟨y, ⟨hyS, hy24⟩, rfl⟩
    rcases hs with rfl | hs
    · exact ⟨_, ⟨(hS y hyS).1, fA_lt y⟩, (a_smul_toVecD y).symm⟩
    · rw [Set.mem_singleton_iff] at hs
      subst hs
      exact ⟨_, ⟨(hS y hyS).2, fB_lt y⟩, (b_smul_toVecD y).symm⟩
  have hgc : g ∈ Subgroup.closure ({genA, genB} : Set Jmat) := by
    have hc : Subgroup.closure ({genA, genB} : Set Jmat) = ⊤ := closure_ab dat
    rw [hc]
    exact Subgroup.mem_top g
  have hmem := CFSG.Perm.smul_mem_of_finite_of_mem_closure hF hcl hgc
    (x := toVecD 24 v) ⟨v, ⟨hv, hv24⟩, rfl⟩
  have hg' : g • toVecD 24 v = toVecD 24 x := hg
  rw [hg'] at hmem
  obtain ⟨y, ⟨hyS, hy24⟩, e⟩ := hmem
  rw [← toVecD_injective hy24 hx24 e]
  exact hyS

theorem orbitCheck_of_ncard {v n : Nat} {others : List Nat}
    (hv : v < 2 ^ 24) (hn : n < 2 ^ 30)
    (hcard : (MulAction.orbit Jmat (toVecD 24 v)).ncard = n)
    (hoth : ∀ w ∈ others, w < 2 ^ 24 → toVecD 24 w ∉ MulAction.orbit Jmat (toVecD 24 v)) :
    orbitCheck v n others = true := by
  have hR : (codes v).card = n := by rw [codes_card, hcard]
  have hRlt : ∀ y ∈ codes v, y < 2 ^ 24 := fun y hy => (mem_codes.1 hy).1
  have hv0 : v ∈ codes v := mem_codes.2 ⟨hv, MulAction.mem_orbit_self _⟩
  have hA : ∀ x ∈ codes v, vecMulN 24 dat.colsA x ∈ codes v := fun x hx => by
    refine mem_codes.2 ⟨fA_lt x, ?_⟩
    rw [← a_smul_toVecD]
    exact smul_orbit (mem_codes.1 hx).2
  have hB : ∀ x ∈ codes v, vecMulN 24 dat.colsB x ∈ codes v := fun x hx => by
    refine mem_codes.2 ⟨fB_lt x, ?_⟩
    rw [← b_smul_toVecD]
    exact smul_orbit (mem_codes.1 hx).2
  have hmin := codes_min hv
  obtain ⟨hsz, hasz, hbsz, h0, hmem, hinj, hao, hbo⟩ :=
    vOrbitBFS_full (d := 24) (cA := dat.colsA) (cB := dat.colsB) hR hn hRlt hv0 hA hB hmin
  have hn0 : 0 < n := by
    have := Finset.card_pos.2 ⟨v, hv0⟩
    omega
  unfold orbitCheck orbitOf
  simp only [Bool.and_eq_true, beq_iff_eq]
  have hlt : ∀ i < n, (vOrbitBFS 24 dat.colsA dat.colsB v n).pts[i]! < 2 ^ 24 :=
    fun i hi => hRlt _ (hmem i hi)
  have hT := tree_of hn0 hn (fun i hi => (hao i hi).1) (fun i hi => (hbo i hi).1)
    (reach_of_min hinj hao hbo hn0 hmem (by rw [h0]; exact hmin))
  refine ⟨⟨⟨⟨orbit_ok_of hn hsz hasz hbsz hlt hinj hao hbo, h0⟩, hT.1⟩, hT.2⟩,
    others_of hsz hmem fun w hw hwR => ?_⟩
  obtain ⟨hw24, hwo⟩ := mem_codes.1 hwR
  exact hoth w hw hw24 hwo

end CFSG.KC.Co1Orb

end
