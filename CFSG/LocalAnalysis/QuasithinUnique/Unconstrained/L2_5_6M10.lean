module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_6Sharp

public section

namespace CFSG.QuasithinUnique.Unc25G2

open Equiv CFSG.Sporadic.Bridge

@[expose] def gen10 (i : ℕ) : Perm (Fin 10) :=
  if i = 0 then A6Models.tAdd else if i = 1 then A6Models.tSq else if i = 2 then A6Models.tInv
  else if i = 3 then A6Models.tMulFrob else 1

theorem gen10_mem (i : ℕ) : gen10 i ∈ A6Models.m10 := by
  unfold gen10
  split
  · exact Subgroup.subset_closure (by simp)
  · split
    · exact Subgroup.subset_closure (by simp)
    · split
      · exact Subgroup.subset_closure (by simp)
      · split
        · exact Subgroup.subset_closure (by simp)
        · exact Subgroup.one_mem _

@[expose] def w10_0 : List (Fin 10 × List (ℕ × Bool)) :=
  [(0, []),
    (1, [(0, true)]),
    (2, [(0, false)]),
    (9, [(2, true)]),
    (3, [(1, true), (0, false)]),
    (4, [(3, true), (0, true)]),
    (6, [(1, true), (0, true)]),
    (8, [(3, true), (0, false)]),
    (5, [(0, true), (3, true), (0, true)]),
    (7, [(0, true), (1, true), (0, true)])]

@[expose] def w10_1 : List (Fin 10 × List (ℕ × Bool)) :=
  [(1, []),
    (3, [(1, false)]),
    (4, [(3, true)]),
    (6, [(1, true)]),
    (8, [(3, false)]),
    (2, [(1, true), (1, true)]),
    (5, [(1, true), (3, false)]),
    (7, [(1, true), (3, true)]),
    (9, [(0, false), (2, true), (0, false)])]

@[expose] def w10_2 : List (Fin 10 × List (ℕ × Bool)) :=
  [(2, []),
    (3, [(2, true), (0, false), (3, false), (0, true), (2, true)]),
    (4, [(1, true), (0, false), (2, true), (0, false), (3, false)]),
    (5, [(2, true), (0, false), (1, false), (0, true), (2, true)]),
    (6, [(2, true), (3, true), (0, true), (1, true), (2, true)]),
    (7, [(1, true), (2, true), (0, false), (3, false), (2, true)]),
    (8, [(2, true), (0, false), (1, true), (0, true), (2, true)]),
    (9, [(0, false), (1, true), (1, true), (2, true), (0, true)])]

theorem w10_ok0 : ∀ x ∈ w10_0, wordProd gen10 x.2 (0 : Fin 10) = x.1 := by
  decide +kernel

theorem w10_ok1 : ∀ x ∈ w10_1,
    wordProd gen10 x.2 (0 : Fin 10) = 0 ∧ wordProd gen10 x.2 (1 : Fin 10) = x.1 := by
  decide +kernel

theorem w10_ok2 : ∀ x ∈ w10_2, wordProd gen10 x.2 (0 : Fin 10) = 0 ∧
    wordProd gen10 x.2 (1 : Fin 10) = 1 ∧ wordProd gen10 x.2 (2 : Fin 10) = x.1 := by
  decide +kernel

theorem w10_nodup : (w10_0.map Prod.fst).Nodup ∧ (w10_1.map Prod.fst).Nodup ∧
    (w10_2.map Prod.fst).Nodup := by
  decide +kernel

theorem w10_length : w10_0.length = 10 ∧ w10_1.length = 9 ∧ w10_2.length = 8 := by
  decide +kernel

theorem card_m10_ge : 720 ≤ Nat.card ↥A6Models.m10 := by
  have h0 := le_card_of_witnesses (K := A6Models.m10) gen10 0 w10_0
    (fun x _ => wordProd_mem gen10_mem x.2) (fun x hx => w10_ok0 x hx) w10_nodup.1
  have h1 := le_card_of_witnesses
    (K := A6Models.m10 ⊓ MulAction.stabilizer (Perm (Fin 10)) (0 : Fin 10)) gen10 1 w10_1
    (fun x hx => ⟨wordProd_mem gen10_mem x.2, mem_stabilizer_iff_apply.mpr (w10_ok1 x hx).1⟩)
    (fun x hx => (w10_ok1 x hx).2) w10_nodup.2.1
  have h2 := le_card_of_witnesses
    (K := A6Models.m10 ⊓ MulAction.stabilizer (Perm (Fin 10)) (0 : Fin 10) ⊓
      MulAction.stabilizer (Perm (Fin 10)) (1 : Fin 10)) gen10 2 w10_2
    (fun x hx => ⟨⟨wordProd_mem gen10_mem x.2, mem_stabilizer_iff_apply.mpr (w10_ok2 x hx).1⟩,
      mem_stabilizer_iff_apply.mpr (w10_ok2 x hx).2.1⟩)
    (fun x hx => (w10_ok2 x hx).2.2) w10_nodup.2.2
  obtain ⟨l0, l1, l2⟩ := w10_length
  rw [l0] at h0
  rw [l1] at h1
  rw [l2] at h2
  have h3 : 1 ≤ Nat.card ↥(A6Models.m10 ⊓ MulAction.stabilizer (Perm (Fin 10)) (0 : Fin 10) ⊓
      MulAction.stabilizer (Perm (Fin 10)) (1 : Fin 10) ⊓
      MulAction.stabilizer (Perm (Fin 10)) (2 : Fin 10)) := Nat.card_pos
  omega

@[expose] def lab10 : Fin 10 ≃ {y : Fin 11 // y ≠ 0} where
  toFun j := ⟨Fin.succ (A6Models.perm10 [[1, 6, 2, 9]] j), Fin.succ_ne_zero _⟩
  invFun y := (A6Models.perm10 [[1, 6, 2, 9]]).symm (Fin.pred y.1 y.2)
  left_inv j := by simp
  right_inv y := by
    apply Subtype.ext
    simp

@[expose] def psi : Perm (Fin 10) →* Perm (Fin 11) := Equiv.Perm.extendDomainHom lab10

theorem psi_injective : Function.Injective psi := Equiv.Perm.extendDomainHom_injective lab10

theorem psi_apply_zero (s : Perm (Fin 10)) : psi s 0 = 0 :=
  Equiv.Perm.extendDomain_apply_not_subtype s lab10 (by simp)

theorem psi_tAdd : psi A6Models.tAdd = wordProd CFSG.Sporadic.Bridge.M11.gen
    [(1, false), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (1, true),
      (0, true), (1, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true),
      (1, true), (0, true)] := by
  decide +kernel

theorem psi_tSq : psi A6Models.tSq = wordProd CFSG.Sporadic.Bridge.M11.gen
    [(1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (0, true), (1, false),
      (0, true), (1, false), (0, true), (1, false)] := by
  decide +kernel

theorem psi_tInv : psi A6Models.tInv = wordProd CFSG.Sporadic.Bridge.M11.gen
    [(1, false), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true),
      (1, true), (0, true), (1, true)] := by
  decide +kernel

theorem psi_tMulFrob : psi A6Models.tMulFrob = wordProd CFSG.Sporadic.Bridge.M11.gen
    [(1, true), (0, true), (1, true), (1, true), (0, true), (1, false), (0, true), (1, true),
      (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true),
      (1, true)] := by
  decide +kernel

theorem map_m10_eq_stab1
    : A6Models.m10.map psi = CFSG.Sporadic.Bridge.M11.stab1 := by
  have hle : A6Models.m10.map psi ≤ CFSG.Sporadic.Bridge.M11.stab1 := by
    rw [Subgroup.map_le_iff_le_comap]
    unfold A6Models.m10
    rw [Subgroup.closure_le]
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    have hs0 := psi_apply_zero s
    rcases hs with rfl | rfl | rfl | rfl
    · exact ⟨by rw [psi_tAdd]; exact CFSG.Sporadic.Bridge.M11.nativeWord_mem _,
        mem_stabilizer_iff_apply.mpr hs0⟩
    · exact ⟨by rw [psi_tSq]; exact CFSG.Sporadic.Bridge.M11.nativeWord_mem _,
        mem_stabilizer_iff_apply.mpr hs0⟩
    · exact ⟨by rw [psi_tInv]; exact CFSG.Sporadic.Bridge.M11.nativeWord_mem _,
        mem_stabilizer_iff_apply.mpr hs0⟩
    · exact ⟨by rw [psi_tMulFrob]; exact CFSG.Sporadic.Bridge.M11.nativeWord_mem _,
        mem_stabilizer_iff_apply.mpr hs0⟩
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective psi_injective]
  exact le_trans m11_stab_card_le.1 card_m10_ge

theorem stabilizer_zero_eq_subgroupOf :
    MulAction.stabilizer ↥CFSG.Blueprint.NativeSporadic.M11 (0 : Fin 11) =
      CFSG.Sporadic.Bridge.M11.stab1.subgroupOf CFSG.Blueprint.NativeSporadic.M11 := by
  ext g
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
  constructor
  · intro hg
    exact ⟨g.2, mem_stabilizer_iff_apply.mpr hg⟩
  · intro hg
    exact mem_stabilizer_iff_apply.mp hg.2

theorem nonempty_stabilizer_zero_equiv_m10 :
    Nonempty (↥(MulAction.stabilizer ↥CFSG.Blueprint.NativeSporadic.M11 (0 : Fin 11)) ≃*
      ↥A6Models.m10) := by
  have hle : CFSG.Sporadic.Bridge.M11.stab1 ≤ CFSG.Blueprint.NativeSporadic.M11 :=
    fun g hg => hg.1
  exact ⟨(MulEquiv.subgroupCongr stabilizer_zero_eq_subgroupOf).trans
    ((Subgroup.subgroupOfEquivOfLe hle).trans
      ((MulEquiv.subgroupCongr map_m10_eq_stab1.symm).trans
        (Subgroup.equivMapOfInjective A6Models.m10 psi psi_injective).symm))⟩

theorem nonempty_stabilizer_equiv_m10 (x : Fin 11) :
    Nonempty (↥(MulAction.stabilizer ↥CFSG.Blueprint.NativeSporadic.M11 x) ≃*
      ↥A6Models.m10) := by
  obtain ⟨g, hg⟩ := m11_trans 0 x
  obtain ⟨e⟩ := nonempty_stabilizer_zero_equiv_m10
  exact ⟨(MulAction.stabilizerEquivStabilizer (g := g) (a := (0 : Fin 11)) (b := x)
    hg.symm).symm.trans e⟩

end CFSG.QuasithinUnique.Unc25G2
