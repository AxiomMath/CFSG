module

public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutCheck
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutTables
public import CFSG.Sporadic.Schreier.Outer
public import CFSG.Sporadic.Schreier.ClassSum
public import CFSG.Sporadic.Mathieu.Simple
public import CFSG.Sporadic.J2.Simple

public section

namespace CFSG.ComponentClassification.J2Cover

open CFSG.Blueprint CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2
open CFSG.Monster.B.Co2.Native CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.Native CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.CatalogueSchreierAlternating

@[expose] noncomputable def perm (t : Array ℕ) : Equiv.Perm (Fin 315) := permOfArr 315 t

@[expose] noncomputable def permA : Equiv.Perm (Fin 315) := perm autStrong[0]!

@[expose] noncomputable def permB : Equiv.Perm (Fin 315) := perm autStrong[1]!

@[expose] noncomputable def P : Subgroup (Equiv.Perm (Fin 315)) :=
  Subgroup.closure {permA, permB}

theorem autBase_eq : (([0, 4, 3] : List (Fin 315)).map Fin.val).toArray = autBase := rfl

@[expose] noncomputable def autChain : RawSchreierDatum 315 :=
  RawSchreierDatum.ofArrays 315 (by norm_num) autStrong 2 (by decide) [0, 4, 3] (by decide)
    autWords

theorem autChain_ok : rawChainOK 315 (autStrong.extract 0 2) autStrong
    (([0, 4, 3] : List (Fin 315)).map Fin.val).toArray autWords 4 = true := by
  rw [autBase_eq]
  exact autChain_check.1

theorem autChain_valid : ValidSchreier autChain :=
  ofArrays_valid (by norm_num) autChain_ok

theorem autStrong_size : autStrong.size = 7 := rfl

theorem rep_strong {j : ℕ} (hj : j < 7) : Rep 315 autStrong[j]! (perm autStrong[j]!) :=
  rep_permOfArr_of_chainOK autChain_ok (by rw [autStrong_size]; exact hj)

theorem getElem!_rawInvs {m : ℕ} {S : Array (Array ℕ)} {j : ℕ} (hj : j < S.size) :
    (rawInvs m S)[j]! = invCand m S[j]! := by
  rw [rawInvs, getElem!_pos _ j (by simpa using hj), Array.getElem_map, getElem!_pos S j hj]

theorem rep_strong_inv {j : ℕ} (hj : j < 7) :
    Rep 315 (invCand 315 autStrong[j]!) (perm autStrong[j]!)⁻¹ := by
  have h := (chainCheckFacts autChain_ok).strong_inv j (by rw [autStrong_size]; exact hj)
  rw [getElem!_rawInvs (by rw [autStrong_size]; exact hj)] at h
  exact (rep_permOfArr h).2

theorem autChain_originalSubgroup : autChain.originalSubgroup = P := by
  rw [autChain, ofArrays_originalSubgroup, P]
  congr 1
  ext g
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, hi, rfl⟩
    obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨0, by norm_num, rfl⟩
    · exact ⟨1, by norm_num, rfl⟩

theorem card_P : Nat.card P = 604800 := by
  rw [← autChain_originalSubgroup, autChain, ofArrays_card (by norm_num) autChain_ok, autBase_eq,
    autChain_check.2]
  rfl

theorem mem_P_iff {t : Array ℕ} {g : Equiv.Perm (Fin 315)} (h : Rep 315 t g) :
    inP t = true ↔ g ∈ P := by
  have key : siftA 315 (rawLevels 315 autStrong (([0, 4, 3] : List (Fin 315)).map Fin.val).toArray)
      (([0, 4, 3] : List (Fin 315)).map Fin.val).toArray 0 t = true ↔
        g ∈ autChain.originalSubgroup :=
    ofArrays_mem_iff (by norm_num) autChain_ok h
  rw [autBase_eq, autChain_originalSubgroup] at key
  exact key

theorem rep_permA : Rep 315 autStrong[0]! permA := rep_strong (j := 0) (by norm_num)

theorem rep_permB : Rep 315 autStrong[1]! permB := rep_strong (j := 1) (by norm_num)

theorem permA_mem : permA ∈ P := Subgroup.subset_closure (Set.mem_insert _ _)

theorem permB_mem : permB ∈ P := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem levelTables_autChain : levelTables autChain = autTables := by
  rw [autChain, ofArrays_levelTables autChain_ok, autBase_eq]
  rfl

theorem orderTables_autChain (m : ℕ) : orderTables autChain m = orderTablesOf (idT 315) m := by
  rw [orderTables, levelTables_autChain]
  rfl

section Action

open CFSG.Sporadic.J2

@[expose] noncomputable def actionHom : J →* Equiv.Perm (Fin 315) :=
  MulAction.toPermHom J (Fin 315)

theorem actionHom_apply (g : J) (x : Fin 315) : actionHom g x = g • x := rfl

theorem orb_point {i : ℕ} (hi : i < 315) :
    ap orb.alpha i = (autStrong[0]!)[i]! ∧ ap orb.beta i = (autStrong[1]!)[i]! := by
  have h := allLt_spec orb_check hi
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h

theorem actionHom_a : actionHom a = permA := by
  ext x
  rw [actionHom_apply, show permA = perm autStrong[0]! from rfl,
    ← (rep_strong (j := 0) (by norm_num)) x, ← (orb_point x.isLt).1, rep_alpha x.val x.isLt,
    CFSG.Sporadic.Th.idx_of_lt _ x.isLt, Fin.eta]

theorem actionHom_b : actionHom b = permB := by
  ext x
  rw [actionHom_apply, show permB = perm autStrong[1]! from rfl,
    ← (rep_strong (j := 1) (by norm_num)) x, ← (orb_point x.isLt).2, rep_beta x.val x.isLt,
    CFSG.Sporadic.Th.idx_of_lt _ x.isLt, Fin.eta]

theorem actionHom_injective : Function.Injective actionHom :=
  MulAction.toPerm_injective

theorem actionHom_range : actionHom.range = P := by
  rw [MonoidHom.range_eq_map, ← closure_ab, MonoidHom.map_closure, Set.image_pair, actionHom_a,
    actionHom_b]
  rfl

@[expose] noncomputable def jEquivP : J ≃* P :=
  (MonoidHom.ofInjective actionHom_injective).trans (MulEquiv.subgroupCongr actionHom_range)

theorem jEquivP_apply (g : J) : (jEquivP g : Equiv.Perm (Fin 315)) = actionHom g := rfl

@[expose] noncomputable def nativeEquivP : NativeSporadic.J2 ≃* P := nativeEquiv.trans jEquivP

theorem nativeEquivP_a : (nativeEquivP (nativeEquiv.symm a) : Equiv.Perm (Fin 315)) = permA := by
  rw [nativeEquivP, MulEquiv.trans_apply, MulEquiv.apply_symm_apply, jEquivP_apply, actionHom_a]

theorem nativeEquivP_b : (nativeEquivP (nativeEquiv.symm b) : Equiv.Perm (Fin 315)) = permB := by
  rw [nativeEquivP, MulEquiv.trans_apply, MulEquiv.apply_symm_apply, jEquivP_apply, actionHom_b]

theorem isSimpleGroup_P : IsSimpleGroup P :=
  @MulEquiv.isSimpleGroup _ _ _ _ isSimpleGroup_J jEquivP.symm

theorem P_transitive (x : Fin 315) : ∃ g ∈ P, g 0 = x := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq J (0 : Fin 315) x
  refine ⟨actionHom g, ?_, ?_⟩
  · rw [← actionHom_range]
    exact ⟨g, rfl⟩
  · rw [actionHom_apply, hg]

end Action

@[expose] noncomputable def pa : P := ⟨permA, permA_mem⟩

@[expose] noncomputable def pb : P := ⟨permB, permB_mem⟩

theorem closure_pa_pb : Subgroup.closure ({pa, pb} : Set P) = ⊤ :=
  CFSG.Sporadic.Mathieu.closure_pair_eq_top rfl permA_mem permB_mem

theorem rep_tblA : CFSG.Sporadic.Th.Rep 315 tblA permA :=
  rep_arrTable (by norm_num) (rep_strong (j := 0) (by norm_num))

theorem rep_tblB : CFSG.Sporadic.Th.Rep 315 tblB permB :=
  rep_arrTable (by norm_num) (rep_strong (j := 1) (by norm_num))

theorem rep_tblAInv : CFSG.Sporadic.Th.Rep 315 tblAInv permA⁻¹ :=
  rep_arrTable (by norm_num) (rep_strong_inv (j := 0) (by norm_num))

theorem rep_tblBInv : CFSG.Sporadic.Th.Rep 315 tblBInv permB⁻¹ :=
  rep_arrTable (by norm_num) (rep_strong_inv (j := 1) (by norm_num))

theorem genTables_spec : ∀ l < (#[tblA, tblB] : Array Table).size,
    CFSG.Sporadic.Th.Rep 315 (#[tblA, tblB] : Array Table)[l]! (if l = 0 then permA else permB) ∧
      CFSG.Sporadic.Th.Rep 315 (#[tblAInv, tblBInv] : Array Table)[l]!
        (if l = 0 then permA else permB)⁻¹ ∧
      (if l = 0 then permA else permB) ∈ autChain.originalSubgroup := by
  intro l hl
  have hl2 : l < 2 := by simpa using hl
  rw [autChain_originalSubgroup]
  obtain rfl | rfl : l = 0 ∨ l = 1 := by omega
  · exact ⟨by simpa using rep_tblA, by simpa using rep_tblAInv, by simpa using permA_mem⟩
  · exact ⟨by simpa using rep_tblB, by simpa using rep_tblBInv, by simpa using permB_mem⟩

theorem orderOf_permA : orderOf permA = 2 :=
  (ordTest_iff perm_faithful rep_tblA (by norm_num)).1 pair_check.1

theorem orderOf_permB : orderOf permB = 3 :=
  (ordTest_iff perm_faithful rep_tblB (by norm_num)).1 pair_check.2.1

theorem at_j2_image_pair_count :
    orderOf pa = 2 ∧ orderOf pb = 3 ∧ orderOf (pa * pb) = 7 ∧
      orderOf (pa * pb * pa⁻¹ * pb⁻¹) = 12 ∧
      Nat.card {x : P // orderOf x = 2} = 2835 ∧ Nat.card {y : P // orderOf y = 3} = 17360 ∧
      Nat.card {p : P × P // orderOf p.1 = 2 ∧ orderOf p.2 = 3 ∧ orderOf (p.1 * p.2) = 7 ∧
        orderOf (p.1 * p.2 * p.1⁻¹ * p.2⁻¹) = 12} = 1209600 := by
  have hn : (315 : ℕ) < 2 ^ 32 := by norm_num
  have hQ := autChain_valid
  obtain ⟨-, -, hab, h2, h3, hcl, htot⟩ := pair_check
  obtain ⟨hab', hc'⟩ := (pairTest_iff perm_faithful rep_tblA rep_tblB (by norm_num)
    (by norm_num) orderOf_permA orderOf_permB (by norm_num) (by norm_num)).1 hab
  have hc2 := card_orderOf_eq hn autChain hQ (m := 2) (by norm_num)
  have hc3 := card_orderOf_eq hn autChain hQ (m := 3) (by norm_num)
  have hpairs := card_image_pairs_eq_classTotal hn autChain hQ (mx := 2) (my := 3) (r := 7)
    (s := 12) (by norm_num) (by norm_num) (by norm_num) (by norm_num) genTables_spec 4000
    (by rw [orderTables_autChain]; exact hcl)
  rw [orderTables_autChain, h2] at hc2
  rw [orderTables_autChain, h3] at hc3
  rw [orderTables_autChain, orderTables_autChain, htot] at hpairs
  rw [autChain_originalSubgroup] at hc2 hc3 hpairs
  refine ⟨?_, ?_, ?_, ?_, hc2, hc3, hpairs⟩
  · rw [← Subgroup.orderOf_coe]; exact orderOf_permA
  · rw [← Subgroup.orderOf_coe]; exact orderOf_permB
  · rw [← Subgroup.orderOf_coe]; exact hab'
  · rw [← Subgroup.orderOf_coe]; exact hc'

theorem outer_P :
    Nat.card (Outer P) ≤ 2 ∧ IsMulCommutative (Outer P) ∧ Group.IsSolvable (Outer P) := by
  obtain ⟨ha, hb, hab, hc, -, -, hT⟩ := at_j2_image_pair_count
  exact outer_schreier_of_counts isSimpleGroup_P closure_pa_pb ha hb hab hc (by norm_num) card_P
    (by norm_num) hT (by norm_num) (by norm_num)

@[expose] noncomputable def mulAutEquivP : MulAut NativeSporadic.J2 ≃ MulAut P where
  toFun α := (nativeEquivP.symm.trans α).trans nativeEquivP
  invFun β := (nativeEquivP.trans β).trans nativeEquivP.symm
  left_inv α := by
    ext x
    simp
  right_inv β := by
    ext x
    simp

@[expose] noncomputable def outerEquivP : Outer NativeSporadic.J2 ≃* Outer P :=
  equivalence (G := NativeSporadic.J2) (H := P) nativeEquivP

theorem finite_outer_P : Finite (Outer P) := by
  have hfin : Finite (MulAut P) :=
    Finite.of_injective (fun α : MulAut P => (α : P → P)) DFunLike.coe_injective
  exact Finite.of_surjective (QuotientGroup.mk' (inner P)) (QuotientGroup.mk'_surjective _)

theorem at_j2_schreier :
    Nat.card (Outer NativeSporadic.J2) ≤ 2 ∧ IsMulCommutative (Outer NativeSporadic.J2) ∧
      Group.IsSolvable (Outer NativeSporadic.J2) := by
  have := finite_outer_P
  have hfin : Finite (Outer NativeSporadic.J2) := Finite.of_equiv (Outer P) outerEquivP.symm.toEquiv
  have hle : Nat.card (Outer NativeSporadic.J2) ≤ 2 := by
    rw [Nat.card_congr outerEquivP.toEquiv]
    exact outer_P.1
  exact ⟨hle, commutative_of_card_le_four (by omega), solvable_of_card_le_four (by omega)⟩

end CFSG.ComponentClassification.J2Cover
