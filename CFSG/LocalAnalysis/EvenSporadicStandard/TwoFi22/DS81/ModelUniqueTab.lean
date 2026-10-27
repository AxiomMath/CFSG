module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelUniqueTabCheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelUniqueLin
public import CFSG.Sporadic.Fi22.Classes

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81

open CFSG.F3.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native
open CFSG.Sporadic.Fi22 CFSG.Sporadic.Fi22.Native
open CFSG.EvenSporadicStandard.TwoFi22.FrameJ (fjDLeaf)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def uqDelta {G : Type*} [Group G] (g0 g1 : ℕ → G) (dp : Array (ℕ × ℕ)) (j : ℕ) : G :=
  g0 dp[j]!.1 * g1 dp[j]!.2

@[expose] def uqB {G : Type*} [Group G] (g0 g1 : ℕ → G) (dp : Array (ℕ × ℕ)) (bas : Array ℕ)
    (i : ℕ) : G :=
  uqDelta g0 g1 dp bas[i]!

structure TabFacts (g0 g1 : ℕ → J) (n0 n1 : ℕ)
    (dp : Array (ℕ × ℕ)) (bas W : Array ℕ) (cu cw : Array (Array ℕ)) : Prop where
  delta_D : ∀ j < 22, uqDelta g0 g1 dp j ∈ D
  delta_inj : ∀ i < 22, ∀ j < 22, uqDelta g0 g1 dp i = uqDelta g0 g1 dp j → i = j
  b_comm : ∀ i < 10, ∀ j < 10,
    uqB g0 g1 dp bas i * uqB g0 g1 dp bas j = uqB g0 g1 dp bas j * uqB g0 g1 dp bas i
  bas_lt : ∀ i < 10, bas[i]! < 22
  delta_phi : ∀ j < 22, uqDelta g0 g1 dp j = phi (uqB g0 g1 dp bas) W[j]!
  cu_size : cu.size = n0
  cw_size : cw.size = n1
  cu_lt : ∀ k < n0, ∀ i < 10, (cu[k]!)[i]! < 1024
  cw_lt : ∀ k < n1, ∀ i < 10, (cw[k]!)[i]! < 1024
  act0 : ∀ k < n0, ∀ i < 10, g0 k * uqB g0 g1 dp bas i * (g0 k)⁻¹ =
    phi (uqB g0 g1 dp bas) (cu[k]!)[i]!
  act1 : ∀ k < n1, ∀ i < 10, g1 k * uqB g0 g1 dp bas i * (g1 k)⁻¹ =
    phi (uqB g0 g1 dp bas) (cw[k]!)[i]!
  pair_lt : ∀ j < 22, dp[j]!.1 < n0 ∧ dp[j]!.2 < n1

theorem uq_compT_size (n : ℕ) (P Q : Table) : (compT n P Q).size = n := by
  unfold compT
  simp

theorem getElem!_map' {α β : Type*} [Inhabited α] [Inhabited β] (f : α → β) (a : Array α) {j : ℕ}
    (hj : j < a.size) : (a.map f)[j]! = f a[j]! := by
  rw [getElem!_pos _ j (by simpa using hj), Array.getElem_map, getElem!_pos a j hj]

theorem uqCols_getElem! (W : Array ℕ) (sg : Array (Array ℕ)) {k i : ℕ} (hk : k < sg.size)
    (hi : i < sg[k]!.size) : ((uqCols W sg)[k]!)[i]! = W[(sg[k]!)[i]!]! := by
  unfold uqCols
  rw [getElem!_map' _ sg hk, getElem!_map' _ _ hi]

theorem uqActOK_parts {t D B : Array Table} {sg : Array (Array ℕ)} (hD : D.size = 22)
    (h : uqActOK t D B sg = true) :
    ∀ k < t.size, sg[k]!.size = 10 ∧ ∀ i < 10, (sg[k]!)[i]! < 22 ∧
      compT 3510 t[k]! B[i]! = compT 3510 D[(sg[k]!)[i]!]! t[k]! := by
  unfold uqActOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, allIn_eq_true] at h
  intro k hk
  obtain ⟨h1, h2⟩ := h k (Nat.zero_le _) hk
  refine ⟨h1, fun i hi => ?_⟩
  obtain ⟨h3, h4⟩ := h2 i (Nat.zero_le _) hi
  refine ⟨h3, ?_⟩
  rw [h4, getElem!_map' _ D (by omega)]

section


theorem rep_unique22 {T : Table} {g h : J} (hg : Rep 3510 T g) (hh : Rep 3510 T h) : g = h := by
  have : h⁻¹ * g = 1 := by
    apply eq_one_of_idx
    intro i hi
    rw [idx_mul, ← hg i hi, hh i hi, idx_inv_idx]
  rw [inv_mul_eq_one] at this
  exact this.symm

theorem mem_D_of_fjDLeaf {A B : Table} {g : J} (hg : Rep 3510 (compT 3510 A B) g)
    (h : fjDLeaf orb.alpha A B = true) : g ∈ D := by
  unfold fjDLeaf at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨h1, -⟩, h3⟩ := h
  have hg2 : g ^ 2 = 1 := eq_one_of_idx (idx_sq_of_invoOK hg h1)
  exact mem_D_of_cube a_mem_D hg2 (cube_of_order3OK (Rep.compT hg rep_alpha) h3)

theorem table_eq_of_rep22 {T T' : Table} {g : J} (hT : Rep 3510 T g) (hT' : Rep 3510 T' g)
    (hs : T.size = 3510) (hs' : T'.size = 3510) : T = T' := by
  apply Array.ext (hs.trans hs'.symm)
  intro i hi hi'
  have hi31 : i < 3510 := hs ▸ hi
  have h := (hT i hi31).trans (hT' i hi31).symm
  unfold ap at h
  rw [getElem!_pos T i hi, getElem!_pos T' i hi'] at h
  exact UInt32.toNat_inj.1 h

theorem rep_uqPhiTab {B : Array Table} {b : ℕ → J} (hB : ∀ i < 10, Rep 3510 B[i]! (b i)) (m : ℕ)
    {l : List ℕ} (hl : ∀ i ∈ l, i < 10) :
    Rep 3510 (l.foldr (fun i P => if m.testBit i then compT 3510 B[i]! P else P) (idT 3510))
      (phiL b m l) := by
  induction l with
  | nil =>
    have e : phiL b m [] = 1 := rfl
    rw [List.foldr_nil, e]
    exact Rep.idT (G := J) (n := 3510) (by norm_num)
  | cons i l ih =>
    have h1 := ih fun k hk => hl k (List.mem_cons_of_mem _ hk)
    rw [phiL_cons, List.foldr_cons]
    split_ifs
    · exact Rep.compT (hB i (hl i List.mem_cons_self)) h1
    · exact h1

theorem uqTabCheckT_sound {t0 t1 : Array Table} {g0 g1 : ℕ → J}
    (h0 : ∀ k < t0.size, Rep 3510 t0[k]! (g0 k)) (h1 : ∀ k < t1.size, Rep 3510 t1[k]! (g1 k))
    {dp : Array (ℕ × ℕ)} {bas W : Array ℕ} {sg0 sg1 : Array (Array ℕ)}
    (h : uqTabCheckT orb.alpha t0 t1 dp bas W sg0 sg1 = true) :
    TabFacts g0 g1 t0.size t1.size dp bas W (uqCols W sg0) (uqCols W sg1) := by
  unfold uqTabCheckT at h
  simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true', decide_eq_true_eq, allIn_eq_true,
    Bool.or_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hdp, hbas⟩, hW⟩, hbaslt⟩, hWlt⟩, hpairs⟩, hdist⟩, hcomm⟩, hrel⟩, hs0⟩,
    hs1⟩, hact0⟩, hact1⟩ := h
  have hDsz : (uqD t0 t1 dp).size = 22 := by rw [uqD, Array.size_map, hdp]
  have hBsz : (uqBt (uqD t0 t1 dp) bas).size = 10 := by rw [uqBt, Array.size_map, hbas]
  have hbas_lt : ∀ i < 10, bas[i]! < 22 := fun i hi => by
    rw [getElem!_pos bas i (by omega)]
    exact hbaslt _ (Array.getElem_mem _)
  have hW_lt : ∀ j < 22, W[j]! < 1024 := fun j hj => by
    rw [getElem!_pos W j (by omega)]
    exact hWlt _ (Array.getElem_mem _)
  have hpair : ∀ j < 22, (dp[j]!.1 < t0.size ∧ dp[j]!.2 < t1.size) ∧
      fjDLeaf orb.alpha t0[dp[j]!.1]! t1[dp[j]!.2]! = true := fun j hj => by
    rw [getElem!_pos dp j (by omega)]
    exact hpairs _ (Array.getElem_mem _)
  have hDj : ∀ j < 22, (uqD t0 t1 dp)[j]! = compT 3510 t0[dp[j]!.1]! t1[dp[j]!.2]! := fun j hj => by
    unfold uqD
    rw [getElem!_map' _ dp (by omega)]
  have hDrep : ∀ j < 22, Rep 3510 (uqD t0 t1 dp)[j]! (uqDelta g0 g1 dp j) := fun j hj => by
    rw [hDj j hj]
    exact Rep.compT (h0 _ (hpair j hj).1.1) (h1 _ (hpair j hj).1.2)
  have hDsize : ∀ j < 22, (uqD t0 t1 dp)[j]!.size = 3510 := fun j hj => by
    exact (congrArg Array.size (hDj j hj)).trans (uq_compT_size _ _ _)
  have hBj : ∀ i < 10, (uqBt (uqD t0 t1 dp) bas)[i]! = (uqD t0 t1 dp)[bas[i]!]! := fun i hi => by
    unfold uqBt
    rw [getElem!_map' _ bas (by omega)]
  have hBrep : ∀ i < 10, Rep 3510 (uqBt (uqD t0 t1 dp) bas)[i]! (uqB g0 g1 dp bas i) :=
    fun i hi => by
      rw [hBj i hi]
      exact hDrep _ (hbas_lt i hi)
  have hBsize : ∀ i < 10, (uqBt (uqD t0 t1 dp) bas)[i]!.size = 3510 := fun i hi => by
    rw [hBj i hi]
    exact hDsize _ (hbas_lt i hi)
  have hdelta_phi : ∀ j < 22, uqDelta g0 g1 dp j = phi (uqB g0 g1 dp bas) W[j]! := fun j hj => by
    have h1' := rep_uqPhiTab (B := uqBt (uqD t0 t1 dp) bas) hBrep W[j]!
      (l := List.range 10) (fun _ hi => List.mem_range.1 hi)
    have h2' := hrel j (Nat.zero_le _) hj
    exact rep_unique22 (hDrep j hj) (h2' ▸ h1')
  refine ⟨fun j hj => ?_, fun i hi j hj hij => ?_, fun i hi j hj => ?_, hbas_lt, hdelta_phi,
    ?_, ?_, ?_, ?_, ?_, ?_, fun j hj => (hpair j hj).1⟩
  · exact mem_D_of_fjDLeaf (A := t0[dp[j]!.1]!) (B := t1[dp[j]!.2]!)
      (Rep.compT (h0 _ (hpair j hj).1.1) (h1 _ (hpair j hj).1.2)) (hpair j hj).2
  · by_contra hne
    rcases hdist i (Nat.zero_le _) hi j (Nat.zero_le _) hj with h' | h'
    · exact hne h'
    · have hrep : Rep 3510 (uqD t0 t1 dp)[j]! (uqDelta g0 g1 dp i) := by
        rw [hij]
        exact hDrep j hj
      exact h' (table_eq_of_rep22 (hDrep i hi) hrep (hDsize i hi) (hDsize j hj))
  · have h' := hcomm i (Nat.zero_le _) hi j (Nat.zero_le _) hj
    have hrep : Rep 3510 (compT 3510 (uqBt (uqD t0 t1 dp) bas)[j]! (uqBt (uqD t0 t1 dp) bas)[i]!)
        (uqB g0 g1 dp bas i * uqB g0 g1 dp bas j) := by
      rw [← h']
      exact Rep.compT (hBrep i hi) (hBrep j hj)
    exact rep_unique22 hrep (Rep.compT (hBrep j hj) (hBrep i hi))
  · rw [uqCols, Array.size_map, hs0]
  · rw [uqCols, Array.size_map, hs1]
  · intro k hk i hi
    obtain ⟨hrow, hi'⟩ := uqActOK_parts hDsz hact0 k hk
    have hσ := (hi' i hi).1
    have hk' : k < sg0.size := by rw [hs0]; exact hk
    rw [uqCols_getElem! W sg0 hk' (by omega)]
    exact hW_lt _ hσ
  · intro k hk i hi
    obtain ⟨hrow, hi'⟩ := uqActOK_parts hDsz hact1 k hk
    have hσ := (hi' i hi).1
    have hk' : k < sg1.size := by rw [hs1]; exact hk
    rw [uqCols_getElem! W sg1 hk' (by omega)]
    exact hW_lt _ hσ
  · intro k hk i hi
    obtain ⟨hrow, hi'⟩ := uqActOK_parts hDsz hact0 k hk
    obtain ⟨hσ, heq⟩ := hi' i hi
    have hk' : k < sg0.size := by rw [hs0]; exact hk
    have hrep1 : Rep 3510 (compT 3510 t0[k]! (uqBt (uqD t0 t1 dp) bas)[i]!)
        (g0 k * uqB g0 g1 dp bas i) := Rep.compT (h0 k hk) (hBrep i hi)
    have hrep2 : Rep 3510 (compT 3510 t0[k]! (uqBt (uqD t0 t1 dp) bas)[i]!)
        (uqDelta g0 g1 dp (sg0[k]!)[i]! * g0 k) := by
      rw [heq]
      exact Rep.compT (hDrep _ hσ) (h0 k hk)
    have hmul := rep_unique22 hrep1 hrep2
    rw [uqCols_getElem! W sg0 hk' (by omega), ← hdelta_phi _ hσ, hmul, mul_inv_cancel_right]
  · intro k hk i hi
    obtain ⟨hrow, hi'⟩ := uqActOK_parts hDsz hact1 k hk
    obtain ⟨hσ, heq⟩ := hi' i hi
    have hk' : k < sg1.size := by rw [hs1]; exact hk
    have hrep1 : Rep 3510 (compT 3510 t1[k]! (uqBt (uqD t0 t1 dp) bas)[i]!)
        (g1 k * uqB g0 g1 dp bas i) := Rep.compT (h1 k hk) (hBrep i hi)
    have hrep2 : Rep 3510 (compT 3510 t1[k]! (uqBt (uqD t0 t1 dp) bas)[i]!)
        (uqDelta g0 g1 dp (sg1[k]!)[i]! * g1 k) := by
      rw [heq]
      exact Rep.compT (hDrep _ hσ) (h1 k hk)
    have hmul := rep_unique22 hrep1 hrep2
    rw [uqCols_getElem! W sg1 hk' (by omega), ← hdelta_phi _ hσ, hmul, mul_inv_cancel_right]

end

end CFSG.EvenSporadicStandard.TwoFi22.DS81
