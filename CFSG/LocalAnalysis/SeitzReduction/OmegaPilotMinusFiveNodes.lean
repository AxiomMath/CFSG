module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusGlobal

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup Matrix
open CFSG.LieType CFSG.LieType.Universal
open CFSG.Blueprint (LieModel)
open CFSG.Assembly.LowTwoRank (StatedOmega StatedQuadPlus)
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadMinus)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (spEmbedGL)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore commutator_centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)
open CFSG.SeitzReduction.SymplecticPilot (planeCoords planeEnum planeEnum_injective suppGL)
open CFSG.SeitzReduction.LinearPilot (consecutiveBlock mem_consecutiveBlock blockSpecialLinear
  transvection_mem_blockSpecialLinear)
open CFSG.Timmesfeld (edgeD)
open scoped commutatorElement

section Model

theorem blockSpecialLinear_pair_le_sup {m : ℕ} {F : Type*} [Field F] {a b c : Fin m}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    blockSpecialLinear (K := F) ({a, b} : Finset (Fin m)) ≤
      blockSpecialLinear (insert c {a}) ⊔ blockSpecialLinear (insert c {b}) := by
  have hmem : ∀ {A B : Subgroup (Matrix.SpecialLinearGroup (Fin m) F)}
      {x y : Matrix.SpecialLinearGroup (Fin m) F}, x ∈ A → y ∈ B → ⁅x, y⁆ ∈ A ⊔ B := by
    intro A B x y hx hy
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem (mem_sup_left hx) (mem_sup_right hy))
      (inv_mem (mem_sup_left hx))) (inv_mem (mem_sup_right hy))
  rw [LinearPilot.blockSpecialLinear_eq_closure, Subgroup.closure_le]
  rintro _ ⟨i, j, hij, x, hi, hj, rfl⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  · exact absurd rfl hij
  · rw [← mul_one x, ← Matrix.SpecialLinearGroup.commutatorElement_transvection hac hbc.symm hij]
    exact hmem (transvection_mem_blockSpecialLinear hac (by simp) (by simp) x)
      (transvection_mem_blockSpecialLinear hbc.symm (by simp) (by simp) 1)
  · rw [← mul_one x, ← Matrix.SpecialLinearGroup.commutatorElement_transvection hbc hac.symm hij,
      sup_comm]
    exact hmem (transvection_mem_blockSpecialLinear hbc (by simp) (by simp) x)
      (transvection_mem_blockSpecialLinear hac.symm (by simp) (by simp) 1)
  · exact absurd rfl hij

theorem siegelBlockGL_pair_le_sup {m : ℕ} {F : Type} [Field F] {a b c : Fin m}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    siegelBlockGL F ({a, b} : Finset (Fin m)) ≤
      siegelBlockGL F (insert c {a}) ⊔ siegelBlockGL F (insert c {b}) := by
  unfold siegelBlockGL SymplecticPilot.siegelBlock
  rw [← Subgroup.map_sup, ← Subgroup.map_sup]
  exact Subgroup.map_mono (Subgroup.map_mono (blockSpecialLinear_pair_le_sup hab hac hbc))

theorem siegelBlockGL_le_map_statedOmega {m : ℕ} {F : Type} [Field F] [Finite F]
    (hF : 4 ≤ Nat.card F) {B : Finset (Fin m)} (hB : 2 ≤ B.card) :
    siegelBlockGL F B ≤ (StatedOmega (StatedQuadPlus B.card F)).map
      (spEmbedGL (planeEnum B) (planeEnum_injective B)) := by
  rw [siegelBlockGL_eq_map_omegaLeviSL hF hB]
  exact Subgroup.map_mono (omegaLeviSL_le_statedOmega hF hB)

theorem consecutiveBlock_two_eq_pair {m i : ℕ} (h : i + 2 ≤ m) :
    consecutiveBlock m i 2 = {(⟨i, by omega⟩ : Fin m), ⟨i + 1, by omega⟩} := by
  ext x
  rw [mem_consecutiveBlock, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, Fin.ext_iff]
  simp only
  omega

theorem commutator_sup_of_perfect {M : Type*} [Group M] {A B : Subgroup M} (hA : ⁅A, A⁆ = A)
    (hB : ⁅B, B⁆ = B) : ⁅A ⊔ B, A ⊔ B⁆ = A ⊔ B :=
  le_antisymm (Subgroup.commutator_le_self _) (sup_le
    (hA.symm.le.trans (Subgroup.commutator_mono le_sup_left le_sup_left))
    (hB.symm.le.trans (Subgroup.commutator_mono le_sup_right le_sup_right)))

end Model

section Pieces

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {F : Type} [Field F] [Finite F] {r : ℕ} {hn : 1 ≤ r + 2} {b c : K}
  {e : L ≃* matrixProjectiveDerived (coordinateQuadMinus (r + 2) K hn b c)} {ι : K →+* F}
  {k : Fin (r + 1)}

theorem preimagePlanes_singleton {p : Fin (r + 1)} {p' : Fin r} (hp : k.succAbove p' = p) :
    preimagePlanes k {p} = {p'} := by
  ext x
  rw [mem_preimagePlanes, Finset.mem_singleton, Finset.mem_singleton, ← hp]
  exact Fin.succAbove_right_inj

theorem preimagePlanes_pair {p q : Fin (r + 1)} {p' q' : Fin r} (hp : k.succAbove p' = p)
    (hq : k.succAbove q' = q) : preimagePlanes k {p, q} = {p', q'} := by
  ext x
  rw [mem_preimagePlanes, Finset.mem_insert, Finset.mem_singleton, Finset.mem_insert,
    Finset.mem_singleton, ← hp, ← hq, Fin.succAbove_right_inj, Fin.succAbove_right_inj]

theorem castSuccPlanes_singleton (p : Fin r) : castSuccPlanes {p} = {p.castSucc} := by
  simp [castSuccPlanes]

theorem castSuccPlanes_pair (p q : Fin r) : castSuccPlanes {p, q} = {p.castSucc, q.castSucc} := by
  simp [castSuccPlanes]

theorem MinusFieldCover.minusLevelCore_pair_le_sup [CharP F 2] (C : MinusFieldCover e ι k)
    (hK : 4 ≤ Nat.card K) (hF : 4 ≤ Nat.card F) {a b' : Fin (r + 1)} (hab : a ≠ b')
    (hka : k ≠ a) (hkb : k ≠ b') :
    minusLevelCore e ({a, b'} : Finset (Fin (r + 1))) ≤
      minusPieceCore e ({a} : Finset (Fin (r + 1))) ⊔
        minusPieceCore e ({b'} : Finset (Fin (r + 1))) := by
  set E := minusNeighbourCore e k
  obtain ⟨a', ha'⟩ := Fin.exists_succAbove_eq (Ne.symm hka)
  obtain ⟨b'', hb''⟩ := Fin.exists_succAbove_eq (Ne.symm hkb)
  have hab' : a' ≠ b'' := fun h => hab (by rw [← ha', ← hb'', h])
  have hkJ : k ∉ ({a, b'} : Finset (Fin (r + 1))) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hka, hkb⟩
  have hka' : k ∉ ({a} : Finset (Fin (r + 1))) := by simpa using hka
  have hkb' : k ∉ ({b'} : Finset (Fin (r + 1))) := by simpa using hkb
  have hUE := minusLevelCore_le_minusNeighbourCore e hkJ
  have hPaE := minusPieceCore_le_minusNeighbourCore e hka'
  have hPbE := minusPieceCore_le_minusNeighbourCore e hkb'
  have hU := C.map_levelCore hK hF hkJ (by rw [Finset.card_pair hab])
  have hPa := C.map_pieceCore hK hF hka' (Finset.singleton_nonempty _)
  have hPb := C.map_pieceCore hK hF hkb' (Finset.singleton_nonempty _)
  rw [preimagePlanes_pair ha' hb'', castSuccPlanes_pair] at hU
  rw [preimagePlanes_singleton ha', castSuccPlanes_singleton] at hPa
  rw [preimagePlanes_singleton hb'', castSuccPlanes_singleton] at hPb
  have hne : ∀ x : Fin r, Fin.last r ≠ x.castSucc := fun x h => Fin.castSucc_ne_last x h.symm
  have hcard : ∀ x : Fin r, 2 ≤ (insert (Fin.last r) ({x.castSucc} : Finset (Fin (r + 1)))).card :=
    fun x => by rw [Finset.card_insert_of_notMem (by simpa using hne x), Finset.card_singleton]
  have hmodel : siegelBlockGL F ({a'.castSucc, b''.castSucc} : Finset (Fin (r + 1))) ≤
      (((minusPieceCore e {a}).subgroupOf E).map C.π).map
          (StatedOmega (StatedQuadPlus (r + 1) F)).subtype ⊔
        (((minusPieceCore e {b'}).subgroupOf E).map C.π).map
          (StatedOmega (StatedQuadPlus (r + 1) F)).subtype := by
    rw [hPa, hPb]
    refine (siegelBlockGL_pair_le_sup (fun h => hab' (Fin.castSucc_injective _ h))
      (fun h => hne a' h.symm) (fun h => hne b'' h.symm)).trans (sup_le_sup ?_ ?_)
    · exact siegelBlockGL_le_map_statedOmega hF (hcard a')
    · exact siegelBlockGL_le_map_statedOmega hF (hcard b'')
  have hA := commutator_subgroupOf_eq_of_le_perfect hUE (commutator_centralizerPerfectCore _)
  have hB := commutator_subgroupOf_eq_of_le_perfect (sup_le hPaE hPbE)
    (commutator_sup_of_perfect (commutator_centralizerPerfectCore _)
      (commutator_centralizerPerfectCore _))
  have hle := le_of_map_le_of_perfect C.ker_comp_subtype_le hA hB (by
    rw [Subgroup.subgroupOf_sup hPaE hPbE, Subgroup.map_sup, ← Subgroup.map_map,
      ← Subgroup.map_map, ← Subgroup.map_map, hU]
    exact hmodel)
  intro x hx
  exact hle (show (⟨x, hUE hx⟩ : E) ∈ (minusLevelCore e {a, b'}).subgroupOf E from hx)

theorem MinusFieldCover.minusLevelCore_le_centralizer_minusPieceCore [CharP F 2]
    (C : MinusFieldCover e ι k) (hK : 4 ≤ Nat.card K) (hF : 4 ≤ Nat.card F)
    {J : Finset (Fin (r + 1))} (hJ : 2 ≤ J.card) {p : Fin (r + 1)} (hkJ : k ∉ J) (hkp : k ≠ p)
    (hpJ : p ∉ J) :
    minusLevelCore e J ≤ centralizer (minusPieceCore e ({p} : Finset (Fin (r + 1))) : Set G) := by
  have hkI : k ∉ ({p} : Finset (Fin (r + 1))) := by simpa using hkp
  have hU := C.map_levelCore hK hF hkJ hJ
  have hV := C.map_pieceCore hK hF hkI (Finset.singleton_nonempty _)
  have hdisj : Disjoint (castSuccPlanes (preimagePlanes k J))
      (insert (Fin.last r) (castSuccPlanes (preimagePlanes k {p}))) := by
    rw [Finset.disjoint_insert_right]
    refine ⟨last_notMem_castSuccPlanes _, disjoint_castSuccPlanes_preimagePlanes ?_⟩
    rwa [Finset.disjoint_singleton_right]
  refine C.le_centralizer (minusLevelCore_le_minusNeighbourCore e hkJ)
    (minusPieceCore_le_minusNeighbourCore e hkI) (commutator_centralizerPerfectCore _) ?_
  intro x hx y hy
  rw [hU] at hx
  rw [hV] at hy
  exact commute_of_mem_suppGL_of_disjoint (disjoint_planeCoords hdisj)
    (siegelBlockGL_le_suppGL _ hx) (map_statedOmega_spEmbedGL_le_suppGL _ hy)

end Pieces

section Commute

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {F : Type} [Field F] [Finite F] {r : ℕ} {hn : 1 ≤ r + 2} {b c : K}
  {e : L ≃* matrixProjectiveDerived (coordinateQuadMinus (r + 2) K hn b c)} {ι : K →+* F}

omit [Finite G] [Finite K] [CharP K 2] [Finite F] in
theorem exists_splitPlane_notMem {S : Finset (Fin (r + 1))} (hS : S.card < r + 1) :
    ∃ k, k ∉ S := by
  obtain ⟨k, -, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := S) (t := Finset.univ)
    (by rwa [Finset.card_univ, Fintype.card_fin])
  exact ⟨k, hk⟩

theorem minusLevelCore_le_centralizer_minusLevelCore_of_three_le [CharP F 2] (hr : 3 ≤ r)
    (hC : ∀ k, MinusFieldCover e ι k) (hK : 4 ≤ Nat.card K) (hF : 4 ≤ Nat.card F) {i j : ℕ}
    (hi : i + 2 ≤ r + 1) (hj : j + 2 ≤ r + 1)
    (hd : Disjoint (consecutiveBlock (r + 1) i 2) (consecutiveBlock (r + 1) j 2)) :
    minusLevelCore e (consecutiveBlock (r + 1) i 2) ≤
      centralizer (minusLevelCore e (consecutiveBlock (r + 1) j 2) : Set G) := by
  set I := consecutiveBlock (r + 1) i 2 with hI
  set a : Fin (r + 1) := ⟨j, by omega⟩ with ha
  set b' : Fin (r + 1) := ⟨j + 1, by omega⟩ with hb
  have hJ : consecutiveBlock (r + 1) j 2 = {a, b'} := consecutiveBlock_two_eq_pair hj
  have hab : a ≠ b' := by simp [a, b', Fin.ext_iff]
  have haI : a ∉ I := fun h => Finset.disjoint_left.1 hd h (by rw [hJ]; simp)
  have hbI : b' ∉ I := fun h => Finset.disjoint_left.1 hd h (by rw [hJ]; simp)
  have hIcard : I.card = 2 := card_consecutiveBlock_two hi
  have hcent : ∀ p : Fin (r + 1), p ∉ I →
      minusLevelCore e I ≤ centralizer (minusPieceCore e ({p} : Finset (Fin (r + 1))) : Set G) := by
    intro p hp
    obtain ⟨k, hk⟩ := exists_splitPlane_notMem (S := insert p I)
      (by rw [Finset.card_insert_of_notMem hp, hIcard]; omega)
    rw [Finset.mem_insert, not_or] at hk
    exact (hC k).minusLevelCore_le_centralizer_minusPieceCore hK hF (by omega) hk.2 hk.1 hp
  obtain ⟨k, hk⟩ := exists_splitPlane_notMem (S := {a, b'}) (by rw [Finset.card_pair hab]; omega)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
  have hUJ := (hC k).minusLevelCore_pair_le_sup hK hF hab hk.1 hk.2
  rw [hJ, Subgroup.le_centralizer_iff]
  exact hUJ.trans (sup_le (Subgroup.le_centralizer_iff.1 (hcent a haI))
    (Subgroup.le_centralizer_iff.1 (hcent b' hbI)))

theorem minusNode_le_centralizer_of_three_le [CharP F 2] (hr : 3 ≤ r)
    (hC : ∀ k, MinusFieldCover e ι k) (hK : 4 ≤ Nat.card K) (hF : 4 ≤ Nat.card F)
    {i j : Fin (r + 2)} (hij : i ≠ j) (h1 : ¬ edgeD (r + 2) i j) (h2 : ¬ edgeD (r + 2) j i) :
    minusNode (hC 0) i ≤ centralizer (minusNode (hC 0) j : Set G) := by
  have hv : i.val ≠ j.val := fun h => hij (Fin.ext h)
  unfold edgeD at h1 h2
  have hfork : ∀ x : Fin (r + 2), r ≤ x.val →
      minusNode (hC 0) x ≤ minusPieceCore e {Fin.last r} := by
    intro x hx
    rcases (show x.val = r ∨ x.val = r + 1 by omega) with h | h
    · rw [minusNode_of_eq _ h]
      exact lift_forkBlock_le_minusPieceCore (hC 0) hF (by omega) (Finset.empty_subset _)
    · rw [minusNode_of_eq_succ _ h]
      exact lift_forkBlock_le_minusPieceCore (hC 0) hF (by omega) le_rfl
  by_cases hi : i.val + 1 ≤ r <;> by_cases hj : j.val + 1 ≤ r
  · rw [minusNode_of_le _ hi, minusNode_of_le _ hj]
    refine minusLevelCore_le_centralizer_minusLevelCore_of_three_le hr hC hK hF (by omega)
      (by omega) ?_
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [mem_consecutiveBlock] at hx hx'
    omega
  ·
    rw [minusNode_of_le _ hi]
    exact (minusLevelCore_le_centralizer_minusPieceCore (by omega) hC hK hF (by omega)).trans
      (Subgroup.centralizer_le (hfork j (by omega)))
  ·
    rw [minusNode_of_le _ hj]
    have h := (minusLevelCore_le_centralizer_minusPieceCore (e := e) (by omega) hC hK hF
      (j := j.val) (by omega)).trans (Subgroup.centralizer_le (hfork i (by omega)))
    exact Subgroup.le_centralizer_iff.1 h
  ·
    rcases (show (i.val = r ∧ j.val = r + 1) ∨ (i.val = r + 1 ∧ j.val = r) by omega) with
      ⟨hi', hj'⟩ | ⟨hi', hj'⟩
    · rw [minusNode_of_eq _ hi', minusNode_of_eq_succ _ hj']
      exact lift_forkBlock_le_centralizer (hC 0) (by omega) hF
    · rw [minusNode_of_eq_succ _ hi', minusNode_of_eq _ hj']
      exact Subgroup.le_centralizer_iff.1 (lift_forkBlock_le_centralizer (hC 0) (by omega) hF)

end Commute

section Global

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {F : Type} [Field F] [Finite F] [CharP F 2] {r : ℕ} {hn : 1 ≤ r + 2} {b c : K}
  {e : L ≃* matrixProjectiveDerived (coordinateQuadMinus (r + 2) K hn b c)} {ι : K →+* F}

theorem exists_weakCT_minus_of_covers_of_three_le (hr : 3 ≤ r) {f : ℕ}
    (hKf : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K) (hF : Nat.card F = 2 ^ (2 * f))
    (hC : ∀ k, MinusFieldCover e ι k) {G₀ : Subgroup G} (hG₀ : G₀ = ⨆ j, minusNode (hC 0) j)
    {t : G} (htC : t ∈ centralizer (L : Set G)) :
    (∃ Ψ : spinGroup (Spin.quadPlus (r + 2) F) →* G₀, Function.Surjective Ψ ∧
        Ψ.ker ≤ center (spinGroup (Spin.quadPlus (r + 2) F))) ∧
      CFSG.IsQuasisimple G₀ ∧ center G₀ = ⊥ ∧ LieModel G₀ .POmegaPlus (r + 2) 2 (2 * f) ∧
      minusNeighbourCore e (0 : Fin (r + 1)) ≤ G₀ ∧ minusPieceCore e {Fin.last r} ≤ G₀ ∧
      t ∈ normalizer (G₀ : Set G) := by
  have hf2 : 2 ≤ f := by
    by_contra h
    have hf1 : 2 ^ f ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hF16 : 16 ≤ Nat.card F := by
    rw [hF]
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ (2 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hF4 : 4 ≤ Nat.card F := by omega
  have hcomm : ∀ i j : Fin (r + 2), i ≠ j → ¬ edgeD (r + 2) i j → ¬ edgeD (r + 2) j i →
      minusNode (hC 0) i ≤ centralizer (minusNode (hC 0) j : Set G) :=
    fun i j hij h1 h2 => minusNode_le_centralizer_of_three_le hr hC hq hF4 hij h1 h2
  have hpair := fun (i j : Fin (r + 2)) (hij : edgeD (r + 2) i j) =>
    exists_theta_minusNode (by omega) hC hq (by omega) hij
  obtain ⟨Ψ, hΨs, hΨk, hG₀q, -, -⟩ := exists_weakCT_spinPlus_of_pieces (n := r + 2) (by omega)
    (by omega) (by omega : 1 ≤ f) hF (minusNode (hC 0)) hG₀ hcomm hpair
  obtain ⟨Ψ', -, hcen, hmodel⟩ := exists_weakCT_spinPlus_of_pieces_two_pow (n := r + 2)
    (by omega) (by omega : 1 ≤ 2 * f) hF hF4 (minusNode (hC 0)) hG₀ hcomm hpair
  have hZ : center G₀ = ⊥ := by
    rw [hcen, center_spinGroup_quadPlus_eq_bot' (by omega), Subgroup.map_bot]
  have hG₀L : LieModel G₀ .POmegaPlus (r + 2) 2 (2 * f) :=
    LieType.CurtisTits.lieModel_of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot) hmodel
  have hE : minusNeighbourCore e (0 : Fin (r + 1)) ≤ G₀ := by
    refine (minusNeighbourCore_zero_le_iSup (by omega) hC hq hF hF4).trans ?_
    rw [hG₀]
    exact iSup_le fun j => le_iSup (minusNode (hC 0)) j.succ
  have h0 : (0 : Fin (r + 1)) ∉ ({Fin.last r} : Finset (Fin (r + 1))) := by
    rw [Finset.mem_singleton, Fin.ext_iff, Fin.val_zero, Fin.val_last]
    omega
  have hD : minusPieceCore e {Fin.last r} ≤ G₀ :=
    (minusPieceCore_le_minusNeighbourCore e h0).trans hE
  have hconj : ∀ x ∈ centralizer (L : Set G), ∀ g ∈ G₀, x * g * x⁻¹ ∈ G₀ := by
    intro x hx g hg
    rw [hG₀] at hg
    refine Subgroup.iSup_induction (minusNode (hC 0)) (C := fun g => x * g * x⁻¹ ∈ G₀) hg ?_ ?_ ?_
    · intro j y hy
      by_cases hj : j.val + 1 ≤ r
      · rw [minusNode_of_le _ hj] at hy
        have h1 := (mem_normalizer_iff.1
          (UnitaryPilot.mem_normalizer_centralizerPerfectCore_modelToG_of_mem_centralizer e hx
            (minusLevelTorus hn b c (consecutiveBlock (r + 1) j.val 2))) y).1 hy
        rw [hG₀]
        exact le_iSup (minusNode (hC 0)) j (by rw [minusNode_of_le _ hj]; exact h1)
      · have hyD := minusNode_le_minusPieceCore_of_le (by omega) hC hF4 (by omega) hy
        exact hD ((mem_normalizer_iff.1 (mem_normalizer_minusPieceCore e hx _) y).1 hyD)
    · simp only [mul_one, mul_inv_cancel]
      exact one_mem _
    · intro y z hy hz
      have h1 : x * (y * z) * x⁻¹ = (x * y * x⁻¹) * (x * z * x⁻¹) := by group
      rw [h1]
      exact mul_mem hy hz
  have htN : t ∈ normalizer (G₀ : Set G) := by
    rw [mem_normalizer_iff]
    intro g
    refine ⟨fun hg => hconj t htC g hg, fun hg => ?_⟩
    have h1 := hconj t⁻¹ (inv_mem htC) _ hg
    have h2 : t⁻¹ * (t * g * t⁻¹) * t⁻¹⁻¹ = g := by group
    rwa [h2] at h1
  exact ⟨⟨Ψ, hΨs, hΨk⟩, hG₀q, hZ, hG₀L, hE, hD, htN⟩

end Global

end CFSG.SeitzReduction.OmegaPilot
