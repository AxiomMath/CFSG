module

public import CFSG.LocalAnalysis.ComponentClassification.SmallLocalDihedral
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSCRankOneCenter
public import CFSG.LocalAnalysis.ComponentInitial.SLTwoInvolution
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.J1ModelTransport
public import CFSG.Open.StatedDefs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import CFSG.Open.Defs

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedGS

namespace MathieuJankoExclusion

open CFSG.Open CFSG.ProperTwoGeneratedCore Matrix

@[expose] def m11GenA : StatedM11 :=
  ⟨StatedCyclePerm 11 [[2, 10], [4, 11], [5, 7], [8, 9]],
    Subgroup.subset_closure (Set.mem_insert _ _)⟩

@[expose] def m11GenB : StatedM11 :=
  ⟨StatedCyclePerm 11 [[1, 4, 3, 8], [2, 5, 6, 9]],
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩

@[expose] def m11QuatX : StatedM11 := m11GenB * m11GenA * m11GenB * m11GenA * m11GenB⁻¹

@[expose] def m11QuatY : StatedM11 :=
  m11GenB⁻¹ * m11GenA * m11GenB * m11GenB * m11GenA * m11GenB * m11GenA * m11GenB * m11GenB *
    m11GenA * m11GenB

theorem m11_quaternion_relations :
    m11QuatX ^ 2 ≠ 1 ∧ (m11QuatX ^ 2) ^ 2 = 1 ∧ m11QuatY ^ 2 = m11QuatX ^ 2 ∧
      m11QuatX * m11QuatY = m11QuatX ^ 2 * (m11QuatY * m11QuatX) := by
  decide +kernel

theorem exists_quaternion_of_mulEquiv_m11 {T : Type*} [Group T] (e : T ≃* StatedM11) :
    ∃ R : Subgroup T, Nonempty (R ≃* QuaternionGroup 2) := by
  obtain ⟨h1, h2, h3, h4⟩ := m11_quaternion_relations
  obtain ⟨H, -, -, ⟨eH⟩⟩ :=
    LocalAnalysis.ComponentInitial.exists_quaternion_subgroup_of_anticommuting
      (x := e.symm m11QuatX) (y := e.symm m11QuatY) (z := e.symm (m11QuatX ^ 2))
      (by rw [Ne, map_eq_one_iff _ e.symm.injective]; exact h1)
      (by rw [← map_pow, h2, map_one])
      (by rw [← map_pow])
      (by rw [← map_pow, h3])
      (by rw [← map_mul, h4, map_mul, map_mul])
  exact ⟨H, ⟨eH.symm⟩⟩

@[expose] def j1Gen (i : ℕ) : GL (Fin 7) (ZMod 11) :=
  if i = 0 then j1_first_unit else j1_second_unit

@[expose] def j1WordUnit (w : List (ℕ × Bool)) : GL (Fin 7) (ZMod 11) :=
  (w.map fun l => if l.2 then j1Gen l.1 else (j1Gen l.1)⁻¹).prod

theorem j1Gen_mem (i : ℕ) : j1Gen i ∈ properTwoGenCoreJ1 := by
  rw [j1_canonical_subgroup_eq]
  unfold j1Gen
  split
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem j1WordUnit_mem (w : List (ℕ × Bool)) : j1WordUnit w ∈ properTwoGenCoreJ1 := by
  induction w with
  | nil => exact one_mem _
  | cons l w ih =>
    simp only [j1WordUnit, List.map_cons, List.prod_cons] at ih ⊢
    refine mul_mem ?_ ih
    split
    · exact j1Gen_mem _
    · exact inv_mem (j1Gen_mem _)

@[expose] def j1LetterMat (l : ℕ × Bool) : Matrix (Fin 7) (Fin 7) (ZMod 11) :=
  if l.1 = 0 then j1_first_matrix else if l.2 then j1_second_matrix else j1_second_matrix ^ 2

@[expose] def j1WordMat (w : List (ℕ × Bool)) : Matrix (Fin 7) (Fin 7) (ZMod 11) :=
  (w.map j1LetterMat).prod

theorem j1_first_unit_inv : j1_first_unit⁻¹ = j1_first_unit :=
  inv_eq_of_mul_eq_one_right (by rw [← sq]; exact Units.pow_ofPowEqOne _ _)

theorem j1_second_unit_inv : j1_second_unit⁻¹ = j1_second_unit ^ 2 :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact Units.pow_ofPowEqOne _ _)

theorem val_j1WordUnit (w : List (ℕ × Bool)) :
    ((j1WordUnit w : GL (Fin 7) (ZMod 11)) : Matrix (Fin 7) (Fin 7) (ZMod 11)) = j1WordMat w := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    simp only [j1WordUnit, j1WordMat, List.map_cons, List.prod_cons, Units.val_mul] at ih ⊢
    rw [ih]
    congr 1
    obtain ⟨i, s⟩ := l
    unfold j1Gen j1LetterMat
    by_cases hi : i = 0 <;> cases s
    · simp only [hi, ↓reduceIte, Bool.false_eq_true, j1_first_unit_inv]; rfl
    · simp only [hi, ↓reduceIte]; rfl
    · simp only [hi, ↓reduceIte, Bool.false_eq_true, j1_second_unit_inv,
        Units.val_pow_eq_pow_val]; rfl
    · simp only [hi, ↓reduceIte]; rfl

@[expose] def j1InvolWordX : List (ℕ × Bool) :=
  [(0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true),
    (0, true), (1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, true),
    (0, true), (1, false), (0, true), (1, true), (0, true)]

@[expose] def j1InvolWordY : List (ℕ × Bool) :=
  [(1, false), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true),
    (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, false), (0, true),
    (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true)]

@[expose] def j1InvolWordZ : List (ℕ × Bool) :=
  [(1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true),
    (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, false), (0, true),
    (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false)]

@[expose] def j1InvolX : Matrix (Fin 7) (Fin 7) (ZMod 11) :=
  !![4, 6, 9, 8, 5, 8, 10;
     6, 10, 0, 6, 2, 6, 3;
     9, 0, 10, 9, 3, 9, 10;
     8, 6, 9, 0, 3, 4, 9;
     5, 2, 3, 3, 1, 5, 7;
     8, 6, 9, 4, 5, 4, 7;
     10, 3, 10, 9, 7, 7, 3]

@[expose] def j1InvolY : Matrix (Fin 7) (Fin 7) (ZMod 11) :=
  !![6, 5, 4, 5, 5, 4, 10;
     5, 8, 8, 3, 6, 3, 5;
     4, 8, 5, 0, 4, 3, 6;
     5, 3, 0, 8, 4, 5, 4;
     5, 6, 4, 4, 10, 6, 5;
     4, 3, 3, 5, 6, 0, 7;
     10, 5, 6, 4, 5, 7, 6]

@[expose] def j1InvolZ : Matrix (Fin 7) (Fin 7) (ZMod 11) :=
  !![10, 5, 9, 3, 10, 0, 4;
     5, 1, 4, 6, 9, 3, 8;
     9, 4, 0, 2, 1, 2, 7;
     3, 6, 2, 2, 3, 2, 10;
     10, 9, 1, 3, 8, 1, 8;
     0, 3, 2, 2, 1, 0, 7;
     4, 8, 7, 10, 8, 7, 0]

theorem j1WordMat_involWord : j1WordMat j1InvolWordX = j1InvolX ∧
    j1WordMat j1InvolWordY = j1InvolY ∧ j1WordMat j1InvolWordZ = j1InvolZ := by
  decide +kernel

theorem j1WordMat_append (u v : List (ℕ × Bool)) :
    j1WordMat (u ++ v) = j1WordMat u * j1WordMat v := by
  simp only [j1WordMat, List.map_append, List.prod_append]

@[expose] def j1VMat (i : Fin 8) : Matrix (Fin 7) (Fin 7) (ZMod 11) :=
  (if i.val % 2 = 1 then j1InvolX else 1) * (if i.val / 2 % 2 = 1 then j1InvolY else 1) *
    (if i.val / 4 % 2 = 1 then j1InvolZ else 1)

@[expose] def j1VWord (i : Fin 8) : List (ℕ × Bool) :=
  (if i.val % 2 = 1 then j1InvolWordX else []) ++
    (if i.val / 2 % 2 = 1 then j1InvolWordY else []) ++
    (if i.val / 4 % 2 = 1 then j1InvolWordZ else [])

theorem j1WordMat_vWord (i : Fin 8) : j1WordMat (j1VWord i) = j1VMat i := by
  obtain ⟨hX, hY, hZ⟩ := j1WordMat_involWord
  simp only [j1VWord, j1VMat, j1WordMat_append, apply_ite j1WordMat, hX, hY, hZ]
  rfl

@[expose] def j1VXor (i j : Fin 8) : Fin 8 := ⟨(i.val ^^^ j.val) % 8, Nat.mod_lt _ (by omega)⟩

theorem j1VMat_mul : ∀ i j : Fin 8, j1VMat i * j1VMat j = j1VMat (j1VXor i j) := by
  decide +kernel

theorem j1VMat_one : j1VMat 0 = 1 := by
  decide +kernel

theorem j1VMat_mul_self (i : Fin 8) : j1VMat i * j1VMat i = 1 := by
  rw [j1VMat_mul, show j1VXor i i = 0 by revert i; decide, j1VMat_one]

theorem j1VMat_injective : ∀ i j : Fin 8, j1VMat i = j1VMat j → i = j := by
  decide +kernel

theorem j1VXor_comm : ∀ i j : Fin 8, j1VXor i j = j1VXor j i := by decide

@[expose] def j1ElemAbelian : Subgroup (GL (Fin 7) (ZMod 11)) where
  carrier := {g | ∃ i, (g : Matrix (Fin 7) (Fin 7) (ZMod 11)) = j1VMat i}
  mul_mem' {g h} := by
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    exact ⟨j1VXor i j, by rw [Units.val_mul, hi, hj, j1VMat_mul]⟩
  one_mem' := ⟨0, by rw [Units.val_one, j1VMat_one]⟩
  inv_mem' {g} := by
    rintro ⟨i, hi⟩
    have h2 : g * g = 1 := Units.ext (by rw [Units.val_mul, Units.val_one, hi, j1VMat_mul_self])
    exact ⟨i, by rw [inv_eq_of_mul_eq_one_right h2, hi]⟩

theorem mem_j1ElemAbelian {g : GL (Fin 7) (ZMod 11)} :
    g ∈ j1ElemAbelian ↔ ∃ i, (g : Matrix (Fin 7) (Fin 7) (ZMod 11)) = j1VMat i := Iff.rfl

theorem j1ElemAbelian_le : j1ElemAbelian ≤ properTwoGenCoreJ1 := by
  intro g hg
  obtain ⟨i, hi⟩ := mem_j1ElemAbelian.mp hg
  rw [show g = j1WordUnit (j1VWord i) from
    Units.ext (by rw [val_j1WordUnit, j1WordMat_vWord, hi])]
  exact j1WordUnit_mem _

theorem card_j1ElemAbelian : Nat.card j1ElemAbelian = 8 := by
  let f : Fin 8 → j1ElemAbelian := fun i =>
    ⟨⟨j1VMat i, j1VMat i, j1VMat_mul_self i, j1VMat_mul_self i⟩, mem_j1ElemAbelian.mpr ⟨i, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j h
      exact j1VMat_injective i j (congrArg
        (fun g : j1ElemAbelian => ((g : GL (Fin 7) (ZMod 11)) : Matrix (Fin 7) (Fin 7) (ZMod 11)))
          h)
    · rintro ⟨g, hg⟩
      obtain ⟨i, hi⟩ := mem_j1ElemAbelian.mp hg
      exact ⟨i, Subtype.ext (Units.ext hi.symm)⟩
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_eq_fintype_card, Fintype.card_fin]

instance : CFSG.IsElementaryAbelian 2 j1ElemAbelian where
  is_comm := ⟨fun g h => by
    obtain ⟨i, hi⟩ := mem_j1ElemAbelian.mp g.2
    obtain ⟨j, hj⟩ := mem_j1ElemAbelian.mp h.2
    refine Subtype.ext (Units.ext ?_)
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, hi, hj, j1VMat_mul,
      j1VMat_mul, j1VXor_comm]⟩
  exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun g => by
    obtain ⟨i, hi⟩ := mem_j1ElemAbelian.mp g.2
    refine Subtype.ext (Units.ext ?_)
    rw [sq, Subgroup.coe_mul, Units.val_mul, hi, j1VMat_mul_self, OneMemClass.coe_one,
      Units.val_one]

theorem le_pRank_of_mulEquiv_j1 {T : Type*} [Group T] [Finite T]
    (e : T ≃* CFSG.Blueprint.NativeSporadic.J1) : 3 ≤ pRank 2 T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let E₀ := j1ElemAbelian.subgroupOf properTwoGenCoreJ1
  have : CFSG.IsElementaryAbelian 2 E₀ := CFSG.IsElementaryAbelian.subgroupOf j1ElemAbelian_le
  have hE₀ : Nat.card E₀ = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe j1ElemAbelian_le).toEquiv,
      card_j1ElemAbelian]
  let φ : properTwoGenCoreJ1 →* T := e.symm.toMonoidHom.comp j1_exact_model_equiv.toMonoidHom
  have hφ : Function.Injective φ := e.symm.injective.comp j1_exact_model_equiv.injective
  have hE : CFSG.IsElementaryAbelian 2 (E₀.map φ) := CFSG.IsElementaryAbelian.map φ
  refine RankOneCenter.le_pRank_of_subgroup hE (r := 3) ?_
  rw [Subgroup.card_map_of_injective hφ, hE₀]
  norm_num

end MathieuJankoExclusion

open MathieuJankoExclusion

theorem dihedral_sylow_M11_J1_involution_count_exclusion {T : Type*} [Group T]
    (hT : Nonempty (T ≃* CFSG.Open.StatedM11) ∨
      Nonempty (T ≃* CFSG.Blueprint.NativeSporadic.J1))
    (s : ℕ) (hs : 2 ≤ s) (P : Sylow 2 T) :
    ¬ Nonempty ((P : Subgroup T) ≃* DihedralGroup (2 ^ (s - 1))) := by
  rintro ⟨eP⟩
  rcases hT with he | he
  · obtain ⟨e⟩ := he
    have : Finite T := Finite.of_equiv _ e.symm.toEquiv
    obtain ⟨-, hQ8⟩ := SmallLocal.dihedral_sylow_rank_and_quaternion_obstructions hs ⟨P, ⟨eP⟩⟩
    exact hQ8 (exists_quaternion_of_mulEquiv_m11 e)
  · obtain ⟨e⟩ := he
    have : Finite T :=
      Finite.of_equiv _
        (e.trans CFSG.ProperTwoGeneratedCore.j1_exact_model_equiv.symm).symm.toEquiv
    obtain ⟨hrank, -⟩ := SmallLocal.dihedral_sylow_rank_and_quaternion_obstructions hs ⟨P, ⟨eP⟩⟩
    have := le_pRank_of_mulEquiv_j1 e
    omega

end CFSG.ComponentClassification.UnbalancedGS
