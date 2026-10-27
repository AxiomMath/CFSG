module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6FourCore
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeFactsFour
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotAutDTwo
public import Certificates.Certificate13615

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Timmesfeld.Balance
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3T Timmesfeld.Co1Leaf
  CFSG.SeitzReduction.E6Pilot

set_option linter.unusedSectionVars false

section Anti

open Native


variable {τ : Tag} {K : Type} [Field K] {ω : Kˣ} {kb : List (List ℕ)}

theorem rootChar_neg_vec_E6Four (b : Fin τ.rank → Kˣ) (v : Fin τ.rank → ℤ) :
    rootChar b (-v) = (rootChar b v)⁻¹ := by
  rw [← zero_sub, rootChar_sub, rootChar_zero, one_mul]

theorem fibL_smul_of_anti (hω : orderOf ω = 3) (hlen : ∀ b ∈ kb, b.length = τ.rank)
    (hlt : ∀ b ∈ kb, ∀ x ∈ b, x < 3) {w : WeylGroup τ}
    (hw : ∀ j v, rootChar (famV (τ := τ) ω kb j) (w • v) = (rootChar (famV ω kb j) v)⁻¹)
    (v : Fin τ.rank → ℤ) :
    fibL kb (List.ofFn (w • v)) = fibL kb (List.ofFn (-v)) := by
  rw [fibL_eq_iff]
  intro j
  have h1 : rootChar (famV (τ := τ) ω kb j) (w • v) = rootChar (famV ω kb j) (-v) := by
    rw [hw j v, rootChar_neg_vec_E6Four]
  rw [rootChar_famV hlen hlt, rootChar_famV hlen hlt, zpow_eq_zpow_iff_modEq, hω] at h1
  exact h1

theorem imgTuple_mem_tuplesL_anti (hω : orderOf ω = 3) (hlen : ∀ b ∈ kb, b.length = τ.rank)
    (hlt : ∀ b ∈ kb, ∀ x ∈ b, x < 3) {w : WeylGroup τ}
    (hw : ∀ j v, rootChar (famV (τ := τ) ω kb j) (w • v) = (rootChar (famV ω kb j) v)⁻¹) :
    imgTuple w ∈ tuplesL (gramL τ) (fibRoots (rootsN τ) kb) (simpleL τ)
      ((simpleL τ).map fun e => fibL kb (e.map fun x => -x))
      ((simpleL τ).map fun e => formB (gramL τ) e e) := by
  rw [tuplesL, length_simpleL]
  refine mem_foldl_extend τ.rank (imgTuple w) (by simp [imgTuple]) fun i hi => ⟨?_, ?_⟩
  · set i' : Fin τ.rank := ⟨i, hi⟩
    have hgi : (imgTuple w).getD i [] = List.ofFn (w • (Pi.single i' 1 : Fin τ.rank → ℤ)) :=
      getD_imgTuple w i'
    rw [hgi, candL, List.mem_map]
    have hroot : IsRoot τ (w • (Pi.single i' 1 : Fin τ.rank → ℤ)) :=
      IsRoot.smul (isRoot_single τ i') w
    refine ⟨(List.ofFn (w • (Pi.single i' 1 : Fin τ.rank → ℤ)),
      iform (w • (Pi.single i' 1 : Fin τ.rank → ℤ)) (w • (Pi.single i' 1 : Fin τ.rank → ℤ)),
      fibL kb (List.ofFn (w • (Pi.single i' 1 : Fin τ.rank → ℤ)))), List.mem_filter.2 ⟨?_, ?_⟩,
      rfl⟩
    · rw [fibRoots, List.mem_map]
      exact ⟨_, mem_rootsN hroot, rfl⟩
    · have hE : (simpleL τ).getD i [] = List.ofFn (Pi.single i' 1 : Fin τ.rank → ℤ) :=
        getD_simpleL i'
      have h1 : ((simpleL τ).map fun e => formB (gramL τ) e e).getD i 0 =
          formB (gramL τ) ((simpleL τ).getD i []) ((simpleL τ).getD i []) := by
        rw [List.getD_eq_getElem _ _ (by simp [length_simpleL, hi]),
          List.getD_eq_getElem _ _ (by simp [length_simpleL, hi])]
        simp
      have h2 : ((simpleL τ).map fun e => fibL kb (e.map fun x => -x)).getD i [] =
          fibL kb (((simpleL τ).getD i []).map fun x => -x) := by
        rw [List.getD_eq_getElem _ _ (by simp [length_simpleL, hi]),
          List.getD_eq_getElem _ _ (by simp [length_simpleL, hi])]
        simp
      have h3 : (List.ofFn (Pi.single i' 1 : Fin τ.rank → ℤ)).map (fun x => -x) =
          List.ofFn (-(Pi.single i' 1 : Fin τ.rank → ℤ)) := by
        rw [List.map_ofFn]
        rfl
      rw [h1, h2, hE, h3, formB_gramL, iform_smul, fibL_smul_of_anti hω hlen hlt hw]
      simp
  · rw [List.all_eq_true]
    intro j hj
    rw [List.mem_range] at hj
    set i' : Fin τ.rank := ⟨i, hi⟩
    set j' : Fin τ.rank := ⟨j, by omega⟩
    rw [getD_take_of_lt hj, getD_imgTuple w j', getD_imgTuple w i', getD_simpleL j',
      getD_simpleL i', formB_gramL, formB_gramL, iform_smul]
    simp

theorem length_liftL_mem {l : List (List ℕ)} :
    ∀ b ∈ l.map (liftL (τ := .E6) e6InnerVec), b.length = Tag.E6.rank := by
  intro b hb
  obtain ⟨b', -, rfl⟩ := List.mem_map.1 hb
  exact length_liftL _ _

theorem lt_of_mem_liftL_mem {l : List (List ℕ)} :
    ∀ b ∈ l.map (liftL (τ := .E6) e6InnerVec), ∀ x ∈ b, x < 3 := by
  intro b hb
  obtain ⟨b', -, rfl⟩ := List.mem_map.1 hb
  exact lt_of_mem_liftL _ _

theorem false_of_anti_E6 (hω : orderOf ω = 3)
    {w : WeylGroup .E6}
    (hw : ∀ j v, rootChar (famV (τ := .E6) ω ((stdBasis 5).map (liftL e6InnerVec)) j) (w • v) =
      (rootChar (famV ω ((stdBasis 5).map (liftL e6InnerVec)) j) v)⁻¹) : False := by
  have hcert := Certificates.certificate13615
  unfold e6FourRigidCheck e6AntiCheck at hcert
  simp only [Bool.and_eq_true, List.all_eq_true] at hcert
  have h1 := hcert.1 _ (imgTuple_mem_tuplesL_anti hω length_liftL_mem lt_of_mem_liftL_mem hw)
  simp [e6WeylTest_imgTuple] at h1

theorem kerNonemptyOK_E6 : kerNonemptyOK .E6 = true := by
  have hcert := Certificates.certificate13615
  unfold e6FourRigidCheck at hcert
  simp only [Bool.and_eq_true] at hcert
  exact hcert.2

end Anti

section Param


variable {K : Type} [Field K]

@[expose] def e6TorParam (j : Fin Tag.E6.rank) (μ : Kˣ) : Fin Tag.E6.rank → Kˣ :=
  fun k => μ ^ Tag.E6.cartan j k

theorem torusElt_eq_rootDiagUnit_e6TorParam (j : Fin Tag.E6.rank) (μ : Kˣ) :
    torusElt .E6 K j μ = rootDiagUnit .E6 (e6TorParam j μ) :=
  torusElt_eq_rootDiagUnit j μ

theorem rootChar_e6TorParam (j : Fin Tag.E6.rank) (μ : Kˣ) (z : Fin Tag.E6.rank → ℤ) :
    rootChar (e6TorParam j μ) z = μ ^ (∑ k, Tag.E6.cartan j k * z k) := by
  rw [rootChar, ← prod_zpow_eq_zpow_sum]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [e6TorParam, ← zpow_mul]

@[expose] def e6RhoFour : Equiv.Perm (Fin Tag.E6.rank) := exactPerm .E6 1

theorem e6RhoFour_apply_apply : ∀ j : Fin Tag.E6.rank, e6RhoFour (e6RhoFour j) = j := by
  decide

theorem e6RhoFour_symm_apply : ∀ j : Fin Tag.E6.rank, e6RhoFour.symm j = e6RhoFour j := by
  intro j
  rw [Equiv.symm_apply_eq, e6RhoFour_apply_apply]

theorem cartan_e6RhoFour : ∀ j m : Fin Tag.E6.rank,
    Tag.E6.cartan j (e6RhoFour m) = Tag.E6.cartan (e6RhoFour j) m := by
  decide

theorem cartan_e6RhoFour_both (i j : Fin Tag.E6.rank) :
    Tag.E6.cartan (e6RhoFour i) (e6RhoFour j) = Tag.E6.cartan i j := by
  rw [cartan_e6RhoFour, e6RhoFour_apply_apply]

theorem rootChar_e6TorParam_perm (j : Fin Tag.E6.rank) (μ : Kˣ) (z : Fin Tag.E6.rank → ℤ) :
    rootChar (e6TorParam (e6RhoFour j) μ) z =
      rootChar (e6TorParam j μ) (permLattice e6RhoFour z) := by
  rw [rootChar_e6TorParam, rootChar_e6TorParam]
  congr 1
  rw [← Equiv.sum_comp e6RhoFour (fun k => Tag.E6.cartan j k * permLattice e6RhoFour z k)]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [permLattice, Function.comp_apply, Equiv.symm_apply_apply]
  rw [cartan_e6RhoFour]

@[expose] def e6W0FourWord : List (Fin Tag.E6.rank) :=
  ([0, 1, 2, 0, 3, 1, 2, 0, 3, 2, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1,
    5, 4, 3, 2, 0] : List (Fin 6))

@[expose] noncomputable def e6W0Four : WeylGroup Tag.E6 :=
  (coxeterSystem Tag.E6).wordProd e6W0FourWord

theorem wordProd_smul_foldr_E6Four (l : List (Fin Tag.E6.rank)) (v : Fin Tag.E6.rank → ℤ) :
    (coxeterSystem Tag.E6).wordProd l • v = l.foldr (reflect Tag.E6) v := by
  induction l with
  | nil => rw [CoxeterSystem.wordProd_nil, one_smul, List.foldr_nil]
  | cons i l ih => rw [CoxeterSystem.wordProd_cons, mul_smul, ih, simple_smul, List.foldr_cons]

theorem e6W0Four_single : ∀ i : Fin Tag.E6.rank,
    e6W0FourWord.foldr (reflect Tag.E6) (Pi.single i 1) = -Pi.single (e6RhoFour i) 1 := by
  decide +kernel

theorem e6W0Four_smul (z : Fin Tag.E6.rank → ℤ) :
    e6W0Four • z = -(permLattice e6RhoFour z) := by
  have hf : ∀ (i : Fin Tag.E6.rank) (c : ℤ), e6W0Four • (Pi.single i c : Fin Tag.E6.rank → ℤ) =
      -(permLattice e6RhoFour (Pi.single i c : Fin Tag.E6.rank → ℤ)) := by
    intro i c
    have e : (Pi.single i c : Fin Tag.E6.rank → ℤ) = c • Pi.single i 1 := by
      rw [← Pi.single_smul, smul_eq_mul, mul_one]
    have e' : permLattice e6RhoFour (c • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) =
        c • Pi.single (e6RhoFour i) 1 := by
      ext j
      simp [permLattice, Pi.single_apply, Equiv.symm_apply_eq]
    rw [e, smul_comm, e6W0Four, wordProd_smul_foldr_E6Four, e6W0Four_single, e', smul_neg]
  conv_lhs => rw [← Finset.univ_sum_single z]
  rw [Finset.smul_sum]
  simp only [hf, Finset.sum_neg_distrib]
  congr 1
  conv_rhs => rw [← Finset.univ_sum_single z]
  ext j
  simp [permLattice, Finset.sum_apply]

theorem rootChar_e6TorParam_perm_w0 (j : Fin Tag.E6.rank) (μ : Kˣ) (z : Fin Tag.E6.rank → ℤ) :
    rootChar (e6TorParam (e6RhoFour j) μ) z =
      (rootChar (e6TorParam j μ) (e6W0Four • z))⁻¹ := by
  rw [rootChar_e6TorParam_perm, e6W0Four_smul, rootChar_neg_vec_E6Four, inv_inv]

theorem rootChar_e6TorParam_sq {ω : Kˣ} (hω : ω ^ 3 = 1) (j : Fin Tag.E6.rank)
    (z : Fin Tag.E6.rank → ℤ) :
    rootChar (e6TorParam j (ω ^ 2)) z = (rootChar (e6TorParam j ω) z)⁻¹ := by
  rw [rootChar_e6TorParam, rootChar_e6TorParam]
  set n := ∑ k, Tag.E6.cartan j k * z k
  have h1 : (ω ^ 2) ^ n = (ω ^ n) ^ 2 := by
    rw [← zpow_natCast ω 2, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
  have h3 : (ω ^ n) ^ 2 * ω ^ n = 1 := by
    rw [← pow_succ, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hω, one_zpow]
  rw [h1]
  exact eq_inv_of_mul_eq_one_left h3

end Param

section Rigid


variable {K : Type} [Field K] [Finite K]

theorem mem_innerAut_of_fix_E6_four
    (hK : Nat.card K = 4) {ω : Kˣ} (hω : orderOf ω = 3) {y : Fin 5 → ZMod 3} (hy : y ≠ 0)
    (α : MulAut (adjointGroup Tag.E6 K)) (hα3 : Nat.Coprime 3 (orderOf α))
    (hfix : ∀ x ∈ Subgroup.centralizer {dE6 (pow_three_of_orderOf hω) y}, α x = x) :
    α ∈ innerAut (adjointGroup Tag.E6 K) := by
  classical
  have : CharP K 2 := charP_two_of_card_four hK
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hω3 : ω ^ 3 = 1 := pow_three_of_orderOf hω
  have hu3 : ∀ μ : Kˣ, μ ^ 3 = 1 := fun μ => by
    have h := pow_card_eq_one' (G := Kˣ) (x := μ)
    rwa [card_units_four hK] at h
  set x0 : Fin Tag.E6.rank → ZMod 3 := subLin (τ := .E6) e6InnerVec y with hx0
  have hx0ne : x0 ≠ 0 := by
    intro h
    apply hy
    apply subLin_e6InnerVec_injective
    rw [← hx0, h, subLin_zero]
  obtain ⟨-, -, hex⟩ := ordinary_E_exact_automorphism_normal_form .E6 (Or.inl rfl) K
  obtain ⟨g, a, σ, ε, hga⟩ := hex α
  have hαψ : ∀ x : adjointGroup .E6 K, (α x : ModGL .E6 K) =
      (g : ModGL .E6 K) * exactNormalAutGL .E6 K a σ ε (x : ModGL .E6 K) *
        (g : ModGL .E6 K)⁻¹ := by
    intro x
    rw [hga x, exactNormalAutGL_apply]
    simp only [mul_assoc]
  have htorC : ∀ (j : Fin Tag.E6.rank) (μ : Kˣ),
      (⟨torusElt .E6 K j μ, torusElt_mem_adjointGroup j μ⟩ : adjointGroup .E6 K) ∈
        Subgroup.centralizer {dE6 (pow_three_of_orderOf hω) y} := by
    intro j μ
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    change torusElt .E6 K j μ * dV ω x0 = dV ω x0 * torusElt .E6 K j μ
    exact (rootDiagUnit_mul_comm_of_mem_torusGroup _ (torusElt_mem_torusGroup j μ)).symm
  have hg1 : (g : ModGL .E6 K) ∈ toralCentralizer .E6 K 1 := by
    refine mem_toralCentralizer.2 ⟨g.2, ?_⟩
    rw [rootDiagUnit_one, one_mul, inv_one, mul_one]
  obtain ⟨w, -, h, hh, u, hu, v, hv, hgdec⟩ :=
    (Chevalley_toral_centralizer_Bruhat_factors .E6 K 1).1 g hg1
  have huU : u ∈ posUnipotent .E6 K := rootSpan_mono Set.inter_subset_right hu
  have hvI : v ∈ rootSpan .E6 K (inversionSet w) := rootSpan_mono Set.inter_subset_right hv
  have hrel : ∀ (j : Fin Tag.E6.rank) (μ : Kˣ),
      rootDiagUnit .E6 (e6TorParam j μ) * u * (rootDiagUnit .E6 (e6TorParam j μ))⁻¹ = u ∧
      rootDiagUnit .E6 (e6TorParam (exactPerm .E6 ε j) (Units.map σ.toRingHom.toMonoidHom μ)) *
          v * (rootDiagUnit .E6 (e6TorParam (exactPerm .E6 ε j)
            (Units.map σ.toRingHom.toMonoidHom μ)))⁻¹ = v ∧
      rootDiagUnit .E6 (e6TorParam j μ) = canonicalRep (coxeterSystem Tag.E6) K w *
        rootDiagUnit .E6 (e6TorParam (exactPerm .E6 ε j) (Units.map σ.toRingHom.toMonoidHom μ)) *
          (canonicalRep (coxeterSystem Tag.E6) K w)⁻¹ := by
    intro j μ
    have hx := congrArg Subtype.val (hfix _ (htorC j μ))
    rw [hαψ] at hx
    change (g : ModGL .E6 K) * exactNormalAutGL .E6 K a σ ε (torusElt .E6 K j μ) *
      (g : ModGL .E6 K)⁻¹ = torusElt .E6 K j μ at hx
    rw [exactNormalAutGL_E6_torusElt, torusElt_eq_rootDiagUnit_e6TorParam,
      torusElt_eq_rootDiagUnit_e6TorParam, hgdec] at hx
    have hconj : h * u * canonicalRep (coxeterSystem Tag.E6) K w * v *
          rootDiagUnit .E6 (e6TorParam (exactPerm .E6 ε j)
            (Units.map σ.toRingHom.toMonoidHom μ)) =
        rootDiagUnit .E6 (e6TorParam j μ) *
          (h * u * canonicalRep (coxeterSystem Tag.E6) K w * v) := by
      rw [← hx]
      group
    exact twisted_torus_bruhat hh huU hvI
      (by rw [← torusElt_eq_rootDiagUnit_e6TorParam]; exact torusElt_mem_torusGroup _ _)
      (by rw [← torusElt_eq_rootDiagUnit_e6TorParam]; exact torusElt_mem_torusGroup _ _) hconj
  set kbS : List (List ℕ) := (Native.stdBasis 5).map (liftL (τ := .E6) e6InnerVec) with hkbS
  have hlenkb : kbS.length = 5 := by
    rw [hkbS, List.length_map, length_stdBasis']
  have hidx : ∀ j : Fin kbS.length, j.val < Tag.E6.rank := fun j =>
    lt_of_lt_of_le j.2 (by rw [hlenkb]; decide)
  have hfam : ∀ j : Fin kbS.length,
      famV (τ := .E6) ω kbS j = e6TorParam ⟨j.val, hidx j⟩ ω := by
    intro j
    apply rootDiagUnit_injective (τ := .E6) (K := K)
    change dV ω (listVec Tag.E6.rank (kbS.get j)) = _
    have hj : kbS.get j =
        liftL (τ := .E6) e6InnerVec ((Native.stdBasis 5).get ⟨j.val, by
          rw [length_stdBasis']; exact hlenkb ▸ j.2⟩) := by
      simp [hkbS]
    rw [hj, listVec_liftL, listVec_stdBasis', subLin_single, dV_e6InnerVec hω3,
      torusElt_eq_rootDiagUnit_e6TorParam]
  have hcert := Certificates.certificate13614
  unfold Native.e6FourCoreCheck at hcert
  simp only [Bool.and_eq_true, List.all_eq_true] at hcert
  obtain ⟨⟨-, hstd0⟩, -⟩ := hcert
  obtain ⟨hker0, hstab0⟩ := famData0_of_famOK0W hω length_liftL_mem lt_of_mem_liftL_mem hstd0
  have hstab : ∀ w' : WeylGroup .E6, (∀ j : Fin kbS.length, ∀ z,
      rootChar (e6TorParam ⟨j.val, hidx j⟩ ω) (w' • z) =
        rootChar (e6TorParam ⟨j.val, hidx j⟩ ω) z) → w' = 1 := by
    intro w' hw'
    refine hstab0 w' fun j z => ?_
    rw [hfam j]
    exact hw' j z
  have hanti : ∀ w' : WeylGroup .E6, (∀ j : Fin kbS.length, ∀ z,
      rootChar (e6TorParam ⟨j.val, hidx j⟩ ω) (w' • z) =
        (rootChar (e6TorParam ⟨j.val, hidx j⟩ ω) z)⁻¹) → False := by
    intro w' hw'
    refine false_of_anti_E6 hω (w := w') fun j z => ?_
    rw [hfam j]
    exact hw' j z
  have hbot : rootSpan .E6 K (∅ : Set (Fin Tag.E6.rank → ℤ)) = ⊥ := by
    simp [rootSpan]
  have hposfin : {β : Fin Tag.E6.rank → ℤ | IsRoot .E6 β ∧ 0 < height β}.Finite :=
    (finite_setOf_isRoot _).subset fun β hβ => hβ.1
  have hu1 : u = 1 := by
    have hm := mem_rootSpan_inter_of_conj_eq_family (famV (τ := .E6) ω kbS) hposfin
      (fun β hβ => hβ.1) (fun α hα hr => (positive_root_collection .E6 K).2 α hα hr) huU
      (fun j => by rw [hfam j]; exact (hrel _ ω).1)
    rw [hker0, Set.empty_inter, hbot, Subgroup.mem_bot] at hm
    exact hm
  have hσσ : Units.map σ.toRingHom.toMonoidHom (Units.map σ.symm.toRingHom.toMonoidHom ω) = ω :=
    Units.ext (by simp)
  have hv1 : v = 1 := by
    have hm := mem_rootSpan_inter_of_conj_eq_family (famV (τ := .E6) ω kbS)
      (inversionSet_finite w) (fun β hβ => hβ.1)
      (fun α hα hr => (bruhat_cell_factorization .E6 K).2.1 w α hα hr) hvI
      (fun j => by
        rw [hfam j]
        have := (hrel (exactPerm .E6 ε ⟨j.val, hidx j⟩)
          (Units.map σ.symm.toRingHom.toMonoidHom ω)).2.1
        rw [exactPerm_E6_involutive, hσσ] at this
        exact this)
    rw [hker0, Set.empty_inter, hbot, Subgroup.mem_bot] at hm
    exact hm
  have hchar : ∀ (j : Fin Tag.E6.rank) (μ : Kˣ) (z : Fin Tag.E6.rank → ℤ),
      rootChar (e6TorParam j μ) z = rootChar (e6TorParam (exactPerm .E6 ε j)
        (Units.map σ.toRingHom.toMonoidHom μ)) (w⁻¹ • z) := by
    intro j μ z
    have h3 := (hrel j μ).2.2
    rw [canonicalRep_conj_rootDiagUnit] at h3
    rw [rootDiagUnit_injective (τ := .E6) (K := K) h3, rootChar_weylTuple]
  have hgw : (g : ModGL .E6 K) = h * canonicalRep (coxeterSystem Tag.E6) K w := by
    rw [hgdec, hu1, hv1, mul_one, mul_one]
  have hε2 : (ε : ℕ) = 0 ∨ (ε : ℕ) = 1 := by
    have := ε.isLt
    change (ε : ℕ) < 2 at this
    omega
  by_cases hσ : σ = RingEquiv.refl K
  · subst hσ
    have hσμ : ∀ μ : Kˣ, Units.map (RingEquiv.refl K).toRingHom.toMonoidHom μ = μ :=
      fun μ => Units.ext rfl
    rcases hε2 with hε | hε
    ·
      have hP : ∀ j, exactPerm .E6 ε j = j := fun j => by rw [hε]; rfl
      have hw1 : w = 1 := by
        have := hstab w⁻¹ fun j z => by
          rw [hchar ⟨j.val, hidx j⟩ ω z, hP, hσμ]
        exact inv_eq_one.1 this
      have hgh : (g : ModGL .E6 K) = h := by rw [hgw, hw1, canonicalRep_one, mul_one]
      set m := h * rootDiagUnit .E6 a with hm
      have hαm : ∀ x : adjointGroup .E6 K, (α x : ModGL .E6 K) = m * x * m⁻¹ := by
        intro x
        rw [hαψ, exactNormalAutGL_apply, hgh, hε, exactQ_zero]
        have e1 : Units.map (entrywiseHom (RingEquiv.refl K).toRingHom) (x : ModGL .E6 K) = x :=
          Units.ext (entrywise_id _)
        rw [e1, hm]
        group
      obtain ⟨l', rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
      have hm3 : m ^ 3 = 1 := by
        have e : m = rootDiagUnitHom .E6 K (l' * a) := by
          rw [hm, map_mul]
          rfl
        rw [e, ← map_pow]
        have hla : (l' * a) ^ 3 = 1 := funext fun i => hu3 _
        rw [hla, map_one]
      have hα3' : α ^ 3 = 1 := by
        refine MulEquiv.ext fun x => Subtype.ext ?_
        have e : ((α ^ 3) x : ModGL .E6 K) = m ^ 3 * x * (m ^ 3)⁻¹ := by
          simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, hαm]
          group
        rw [e, hm3, one_mul, inv_one, mul_one]
        rfl
      have hord : orderOf α = 1 :=
        Nat.Coprime.eq_one_of_dvd hα3.symm (orderOf_dvd_of_pow_eq_one hα3')
      rw [orderOf_eq_one_iff.1 hord]
      exact one_mem _
    ·
      have hP : ∀ j, exactPerm .E6 ε j = e6RhoFour j := fun j => by
        rw [hε]
        rfl
      exact (hanti (e6W0Four * w⁻¹) fun j z => by
        have e := hchar ⟨j.val, hidx j⟩ ω z
        rw [hP, hσμ, rootChar_e6TorParam_perm_w0] at e
        rw [mul_smul, e, inv_inv]).elim
  · have hσω : Units.map σ.toRingHom.toMonoidHom ω = ω ^ 2 :=
      Units.ext (by simpa using ringEquiv_apply_eq_sq hK hω hσ)
    rcases hε2 with hε | hε
    ·
      have hP : ∀ j, exactPerm .E6 ε j = j := fun j => by rw [hε]; rfl
      exact (hanti w⁻¹ fun j z => by
        rw [hchar ⟨j.val, hidx j⟩ ω z, hP, hσω, rootChar_e6TorParam_sq hω3, inv_inv]).elim
    ·
      have hP : ∀ j, exactPerm .E6 ε j = e6RhoFour j := fun j => by
        rw [hε]
        rfl
      have hw0 : w = e6W0Four := by
        have := hstab (e6W0Four * w⁻¹) fun j z => by
          have e := hchar ⟨j.val, hidx j⟩ ω z
          rw [hP, hσω, rootChar_e6TorParam_sq hω3, rootChar_e6TorParam_perm_w0, inv_inv] at e
          rw [mul_smul, e]
        exact (mul_inv_eq_one.1 this).symm
      obtain ⟨β₀, hβ₀, hβ₀1⟩ := exists_kernelRoot_of_kerNonemptyOK kerNonemptyOK_E6 hω hx0ne
      obtain ⟨β, hβ, hβ1, hβpos⟩ : ∃ β, IsRoot .E6 β ∧ rootChar (torV ω x0) β = 1 ∧
          0 < height β := by
        rcases IsRoot.height_pos_or_neg hβ₀ with hpos | hneg
        · exact ⟨β₀, hβ₀, hβ₀1, hpos⟩
        · refine ⟨-β₀, IsRoot.neg hβ₀, ?_, ?_⟩
          · rw [rootChar_neg_vec_E6Four, hβ₀1, inv_one]
          · rw [show height (-β₀) = -height β₀ by simp [height]]
            omega
      set X : ModGL .E6 K := pinnedX .E6 K β 1 with hX
      have hXG : X ∈ adjointGroup .E6 K := pinnedX_mem_adjointGroup β 1
      have hXc : (⟨X, hXG⟩ : adjointGroup .E6 K) ∈
          Subgroup.centralizer {dE6 (pow_three_of_orderOf hω) y} := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        apply Subtype.ext
        change X * dV ω x0 = dV ω x0 * X
        have h1 := rootDiagUnit_conj_pinnedX (torV ω x0) hβ (1 : K)
        rw [hβ1, Units.val_one, one_mul, mul_inv_eq_iff_eq_mul] at h1
        exact h1.symm
      have h1 := congrArg Subtype.val (hfix _ hXc)
      rw [hαψ] at h1
      change (g : ModGL .E6 K) * exactNormalAutGL .E6 K a σ ε X * (g : ModGL .E6 K)⁻¹ = X at h1
      have hρβ : IsRoot .E6 (permLattice e6RhoFour β) :=
        IsRoot.permLattice cartan_e6RhoFour_both hβ
      have hψ : exactNormalAutGL .E6 K a σ ε X = pinnedX .E6 K (permLattice e6RhoFour β)
          (rootChar a (permLattice e6RhoFour β) : K) := by
        rw [exactNormalAutGL_apply, hX, CFSG.RankThree.PartOne.KE.units_map_entrywiseHom_pinnedX,
          map_one, hε]
        have e1 : exactQ .E6 K 1 * pinnedX .E6 K β 1 * (exactQ .E6 K 1)⁻¹ =
            pinnedX .E6 K (permLattice e6RhoFour β) 1 := by
          rw [exactQ_one_conj_pinnedX h2 hβ (1 : K)]
          congr 1
        have e2 := rootDiagUnit_conj_pinnedX a hρβ (1 : K)
        rw [mul_one] at e2
        calc rootDiagUnit .E6 a * exactQ .E6 K 1 * pinnedX .E6 K β 1 * (exactQ .E6 K 1)⁻¹ *
              (rootDiagUnit .E6 a)⁻¹ = rootDiagUnit .E6 a *
                (exactQ .E6 K 1 * pinnedX .E6 K β 1 * (exactQ .E6 K 1)⁻¹) *
                  (rootDiagUnit .E6 a)⁻¹ := by group
          _ = _ := by rw [e1, e2]
      have hw0β : e6W0Four • permLattice e6RhoFour β = -β := by
        rw [e6W0Four_smul]
        congr 1
        funext k
        simp [permLattice, e6RhoFour_symm_apply]
      rw [hψ, hgw, hw0] at h1
      have e3 := canonicalRep_conj_pinnedX_charTwo (K := K) e6W0Four hρβ
        (rootChar a (permLattice e6RhoFour β) : K)
      rw [hw0β] at e3
      have e4 := conj_pinnedX_of_mem_torusGroup hh (IsRoot.neg hβ)
        (rootChar a (permLattice e6RhoFour β) : K)
      have h5 : X = pinnedX .E6 K (-β) (torusRootChar h (-β) *
          (rootChar a (permLattice e6RhoFour β) : K)) := by
        rw [← e4, ← e3, ← h1]
        group
      have hpos : X ∈ posUnipotent .E6 K :=
        (le_iSup₂_of_le (f := fun γ (_ : γ ∈ {α : Fin Tag.E6.rank → ℤ | IsRoot .E6 α ∧
          0 < height α}) => rootSubgroup .E6 K γ) β ⟨hβ, hβpos⟩ le_rfl)
          (Subgroup.subset_closure ⟨1, rfl⟩)
      have hneg : X ∈ negUnipotent .E6 K := by
        rw [h5]
        exact (le_iSup₂_of_le (f := fun γ (_ : γ ∈ {α : Fin Tag.E6.rank → ℤ | IsRoot .E6 α ∧
          height α < 0}) => rootSubgroup .E6 K γ) (-β) ⟨IsRoot.neg hβ, by
            rw [show height (-β) = -height β by simp [height]]; omega⟩ le_rfl)
          (Subgroup.subset_closure ⟨_, rfl⟩)
      have hbot' : X ∈ posUnipotent .E6 K ⊓ negUnipotent .E6 K := ⟨hpos, hneg⟩
      rw [CFSG.Blueprint.Chevalley.posUnipotent_inf_negUnipotent .E6 K, Subgroup.mem_bot] at hbot'
      have h6 : pinnedX .E6 K β 1 = pinnedX .E6 K β 0 := by rw [← hX, hbot', pinnedX_zero]
      exact absurd (pinnedX_injective .E6 K β h6) one_ne_zero

end Rigid

end CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3

end
