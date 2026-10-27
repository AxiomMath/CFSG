module

public import Certificates.Certificate17337
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi22Cent
public import CFSG.LieType.Multipliers.U43Data

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabFi22Cent

open Subgroup CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Monster.B.Mathieu CFSG.Monster.B.Fischer CFSG.RankThree.Native
  CFSG.RankThree.PartOne CFSG.RankThree.PartTwo.KFacts.K426

section L

@[expose] noncomputable def aPerm : Equiv.Perm (Fin 3510) := permOfArr 3510 (lArrs ())[0]!

@[expose] noncomputable def bPerm : Equiv.Perm (Fin 3510) := permOfArr 3510 (lArrs ())[1]!

theorem l_facts : Rep 3510 (lArrs ())[0]! aPerm ∧ Rep 3510 (lArrs ())[1]! bPerm ∧
    Nat.card (Subgroup.closure {aPerm, bPerm}) = 3265920 ∧ aPerm ∈ fi22P ∧ bPerm ∈ fi22P ∧
    aPerm 0 = 0 ∧ aPerm 1 = 1 ∧ bPerm 0 = 0 ∧ bPerm 1 = 1 ∧
    (∀ x : Equiv.Perm (Fin 3510), (∀ v : Fin 3510, (xArr ())[(v : ℕ)]! = x v) →
      aPerm * x = x * aPerm ∧ bPerm * x = x * bPerm) ∧
    ∀ w ∈ relsU43,
      (w.map fun l => cond l.2 (![aPerm, bPerm] l.1) (![aPerm, bPerm] l.1)⁻¹).prod = 1 := by
  obtain ⟨a, b, ha, hb, rest⟩ := Certificates.certificate17337
  have e1 : aPerm = a := CFSG.Monster.B.Mathieu.permOfArr_eq_of_rep ha
  have e2 : bPerm = b := CFSG.Monster.B.Mathieu.permOfArr_eq_of_rep hb
  rw [e1, e2]
  exact ⟨ha, hb, rest⟩

theorem arr_pair_get_zero (A B : Array ℕ) :
    (#[A, B] : Array (Array ℕ))[((0 : Fin 2) : ℕ)]! = A := rfl

theorem arr_pair_get_one (A B : Array ℕ) :
    (#[A, B] : Array (Array ℕ))[((1 : Fin 2) : ℕ)]! = B := rfl

@[expose] noncomputable def lGen (i : Fin 2) : Equiv.Perm (Fin 3510) :=
  permOfArr 3510 (#[(lArrs ())[0]!, (lArrs ())[1]!] : Array (Array ℕ))[i.val]!

theorem lGen_zero : lGen 0 = aPerm := by
  unfold lGen aPerm
  rw [arr_pair_get_zero]

theorem lGen_one : lGen 1 = bPerm := by
  unfold lGen bPerm
  rw [arr_pair_get_one]

@[expose] noncomputable def lSub : Subgroup (Equiv.Perm (Fin 3510)) :=
  Subgroup.closure {aPerm, bPerm}

theorem range_lGen : Set.range lGen = {aPerm, bPerm} := by
  ext y
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i
    · exact Or.inl lGen_zero
    · exact Or.inr lGen_one
  · rintro (rfl | rfl)
    · exact ⟨0, lGen_zero⟩
    · exact ⟨1, lGen_one⟩

theorem closure_lGen : Subgroup.closure (Set.range lGen) = lSub := by
  rw [range_lGen]
  rfl

theorem card_lSub : Nat.card ↥lSub = 3265920 := l_facts.2.2.1

theorem aPerm_mem : aPerm ∈ fi22P := l_facts.2.2.2.1

theorem bPerm_mem : bPerm ∈ fi22P := l_facts.2.2.2.2.1

theorem aPerm_fix : aPerm 0 = 0 ∧ aPerm 1 = 1 :=
  ⟨l_facts.2.2.2.2.2.1, l_facts.2.2.2.2.2.2.1⟩

theorem bPerm_fix : bPerm 0 = 0 ∧ bPerm 1 = 1 :=
  ⟨l_facts.2.2.2.2.2.2.2.1, l_facts.2.2.2.2.2.2.2.2.1⟩

theorem aPerm_comm : aPerm * xPerm = xPerm * aPerm :=
  (l_facts.2.2.2.2.2.2.2.2.2.1 xPerm rep_xPerm).1

theorem bPerm_comm : bPerm * xPerm = xPerm * bPerm :=
  (l_facts.2.2.2.2.2.2.2.2.2.1 xPerm rep_xPerm).2

theorem lSub_le_lev2 : lSub ≤ fi22Chain.levelSubgroup 2 := by
  rw [lSub, Subgroup.closure_le]
  intro y hy
  rcases hy with rfl | rfl
  · exact (mem_lev2_iff _).2 ⟨aPerm_mem, aPerm_fix.1, aPerm_fix.2⟩
  · exact (mem_lev2_iff _).2 ⟨bPerm_mem, bPerm_fix.1, bPerm_fix.2⟩

theorem lSub_comm_x : ∀ l ∈ lSub, l * xPerm = xPerm * l := by
  intro l hl
  rw [lSub] at hl
  induction hl using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with rfl | rfl
    · exact aPerm_comm
    · exact bPerm_comm
  | one => simp
  | mul a b _ _ ha hb =>
    calc a * b * xPerm = a * (xPerm * b) := by rw [mul_assoc, hb]
      _ = xPerm * (a * b) := by rw [← mul_assoc, ha, mul_assoc]
  | inv a _ ha =>
    calc a⁻¹ * xPerm = a⁻¹ * (xPerm * a) * a⁻¹ := by group
      _ = a⁻¹ * (a * xPerm) * a⁻¹ := by rw [ha]
      _ = xPerm * a⁻¹ := by group

theorem rels_lGen : ∀ w ∈ CFSG.LieType.Multipliers.U43.rels,
    CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest.evalW lGen w = 1 := by
  intro w hw
  have hw' : w ∈ relsU43 := hw
  have hg : lGen = ![aPerm, bPerm] := by
    funext i
    revert i
    rw [Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    exact ⟨lGen_zero, lGen_one⟩
  rw [CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest.evalW, hg]
  exact l_facts.2.2.2.2.2.2.2.2.2.2 w hw'

theorem index_lSub_lev2 :
    (lSub.subgroupOf (fi22Chain.levelSubgroup 2)).index = 2 := by
  have h1 := Subgroup.card_mul_index (lSub.subgroupOf (fi22Chain.levelSubgroup 2))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe lSub_le_lev2).toEquiv, card_lSub,
    card_lev2] at h1
  omega

theorem lSub_normalized_lev2 : ∀ m ∈ fi22Chain.levelSubgroup 2, ∀ l ∈ lSub,
    m * l * m⁻¹ ∈ lSub := by
  intro m hm l hl
  haveI : (lSub.subgroupOf (fi22Chain.levelSubgroup 2)).Normal :=
    Subgroup.normal_of_index_eq_two index_lSub_lev2
  have := (inferInstance : (lSub.subgroupOf (fi22Chain.levelSubgroup 2)).Normal).conj_mem
    ⟨l, lSub_le_lev2 hl⟩ (Subgroup.mem_subgroupOf.2 hl) ⟨m, hm⟩
  exact Subgroup.mem_subgroupOf.1 this

theorem lSub_normalized_cent : ∀ g ∈ Subgroup.centralizer ({xPerm} : Set (Equiv.Perm (Fin 3510))) ⊓
    fi22P, ∀ l ∈ lSub, g * l * g⁻¹ ∈ lSub := by
  intro g hg l hl
  have hgx : g * xPerm = xPerm * g :=
    Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hg).1
  obtain ⟨j, -, hm⟩ := cent_decomp (Subgroup.mem_inf.1 hg).2 hgx
  set m := (xPerm ^ j)⁻¹ * g with hmdef
  have hgm : g = xPerm ^ j * m := by rw [hmdef]; group
  have hl' : m * l * m⁻¹ ∈ lSub := lSub_normalized_lev2 m hm l hl
  have hcomm : xPerm ^ j * (m * l * m⁻¹) = (m * l * m⁻¹) * xPerm ^ j := by
    have hM : m * l * m⁻¹ ∈ fi22Chain.levelSubgroup 2 :=
      (fi22Chain.levelSubgroup 2).mul_mem
        ((fi22Chain.levelSubgroup 2).mul_mem hm (lSub_le_lev2 hl))
        ((fi22Chain.levelSubgroup 2).inv_mem hm)
    exact (((show Commute (m * l * m⁻¹) xPerm from lev2_comm_x _ hM).pow_right j).eq).symm
  have : g * l * g⁻¹ = m * l * m⁻¹ := by
    calc g * l * g⁻¹ = xPerm ^ j * (m * l * m⁻¹) * (xPerm ^ j)⁻¹ := by rw [hgm]; group
      _ = (m * l * m⁻¹) * xPerm ^ j * (xPerm ^ j)⁻¹ := by rw [hcomm]
      _ = m * l * m⁻¹ := by group
  rw [this]
  exact hl'

end L

end CFSG.HardMathSupport.Dickson.I271.TabFi22Cent
