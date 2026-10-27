module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3LDX
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX11CharOmTools

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.Burgoyne.O CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.C
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL signMat isoOrthGL
  trans_commutator isQuasisimple_trans)
open CFSG.LocalAnalysis.ComponentInitial
  (orthogonal_low_dimensional_fixed_derived_component_coverage)
open CFSG.GroupTheory.WeirSylow (IsPlusType isPlusType_congr)
open P58b3 (tBlockP OddGen)
open scoped MatrixGroups

namespace P58b3L

variable {K : Type} [Field K] {d : ℕ}

variable (K) in
abbrev coordSub (I : Finset (Fin d)) : Submodule K (Fin d → K) :=
  Submodule.pi (↑Iᶜ : Set (Fin d)) fun _ => ⊥

theorem mem_coordSub {I : Finset (Fin d)} {v : Fin d → K} :
    v ∈ coordSub K I ↔ ∀ i, i ∉ I → v i = 0 := by
  simp [coordSub, Submodule.mem_pi]

theorem isCompl_coordSub (I : Finset (Fin d)) : IsCompl (coordSub K I) (coordSub K Iᶜ) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro v h1 h2
    funext i
    by_cases hi : i ∈ I
    · exact (mem_coordSub.1 h2) i (by simpa using hi)
    · exact (mem_coordSub.1 h1) i hi
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    have hv : v = (fun i => if i ∈ I then v i else 0) + (fun i => if i ∈ I then 0 else v i) := by
      funext i
      by_cases hi : i ∈ I <;> simp [hi]
    rw [hv]
    refine Submodule.add_mem_sup ?_ ?_
    · rw [mem_coordSub]
      intro i hi
      simp [hi]
    · rw [mem_coordSub]
      intro i hi
      have hi' : i ∈ I := by simpa using hi
      simp [hi']

theorem polar_coordSub_eq_zero {w : Fin d → K} (hw : ∀ i, w i ≠ 0) (I : Finset (Fin d))
    (x : coordSub K I) (y : coordSub K Iᶜ) :
    QuadraticMap.polar (oQ (diagGL hw)) (x : Fin d → K) (y : Fin d → K) = 0 := by
  have hx := mem_coordSub.1 x.2
  have hy := mem_coordSub.1 y.2
  rw [QuadraticMap.polar, oQ_apply, oQ_apply, oQ_apply, coe_diagGL]
  simp only [dotProduct, mulVec_diagonal, Pi.add_apply]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : i ∈ I
  · rw [hy i (by simpa using hi)]
    ring
  · rw [hx i hi]
    ring

@[expose] def coordSubEquiv (I : Finset (Fin d)) : (Fin I.card → K) ≃ₗ[K] coordSub K I where
  toFun x := ⟨fun i => if h : i ∈ I then x (I.equivFin ⟨i, h⟩) else 0, by
    rw [mem_coordSub]
    intro i hi
    simp [hi]⟩
  invFun v a := (v : Fin d → K) (I.equivFin.symm a)
  map_add' x y := by
    apply Subtype.ext
    funext i
    by_cases h : i ∈ I <;> simp [h]
  map_smul' c x := by
    apply Subtype.ext
    funext i
    by_cases h : i ∈ I <;> simp [h]
  left_inv x := by
    funext a
    simp
  right_inv v := by
    apply Subtype.ext
    funext i
    by_cases h : i ∈ I
    · simp [h]
    · simp [h, (mem_coordSub.1 v.2) i h]

@[expose] def blockIsometry {w : Fin d → K} (hw : ∀ i, w i ≠ 0) (I : Finset (Fin d)) :
    (oQ (diagGL (wRes_ne_zero hw I))).IsometryEquiv
      ((oQ (diagGL hw)).comp (coordSub K I).subtype) where
  toLinearEquiv := coordSubEquiv I
  map_app' x := by
    change oQ (diagGL hw) (fun i => if h : i ∈ I then x (I.equivFin ⟨i, h⟩) else 0) =
      oQ (diagGL (wRes_ne_zero hw I)) x
    rw [oQ_apply, oQ_apply, coe_diagGL, coe_diagGL]
    simp only [dotProduct, mulVec_diagonal]
    rw [← Finset.sum_subset (Finset.subset_univ I) (fun i _ hi => by simp [hi]),
      ← Finset.sum_coe_sort I]
    refine Fintype.sum_equiv I.equivFin _ _ fun i => ?_
    simp [wRes]

theorem isPlusType_coordSub_of_not_isQuasisimple [Finite K] (hK : ringChar K ≠ 2)
    {w : Fin d → K} (hw : ∀ i, w i ≠ 0) {I : Finset (Fin d)} (hI4 : I.card = 4)
    (hIc : Iᶜ.Nonempty) (hq : ¬ IsQuasisimple (blockP K hw I)) :
    IsPlusType ((oQ (diagGL hw)).comp (coordSub K I).subtype) := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hodd' : Odd (Nat.card K) := CatalogueBLinearHigherB.odd_card_of_ringChar_ne_two K hK
  obtain ⟨eP⟩ := nonempty_projBlock_equiv hw h2 hIc (le_refl (omegaI hw I))
  rw [← blockP_eq_projBlock] at eP
  have hq' : ¬ IsQuasisimple (Burgoyne.C.omegaR (diagGL (wRes_ne_zero hw I))) := fun h =>
    hq (LocalCores.isQuasisimple_of_mulEquiv eP.symm h)
  set R := diagGL (wRes_ne_zero hw I) with hRdef
  have hR : (R : Matrix (Fin I.card) (Fin I.card) K)ᵀ = R := diagGL_transpose _
  set Q := CatalogueBLinearHigherB.matrixQuadraticForm R with hQ
  have hQnd := CatalogueBLinearHigherB.polarBilin_matrixQuadraticForm_nondegenerate hK R hR
  have hdim : Module.finrank K (Fin I.card → K) = 4 := by rw [Module.finrank_fin_fun, hI4]
  set e₁ := isoOrthGL hK R hR with he₁
  obtain ⟨S, hS2, hSQ⟩ : ∃ S : Submodule K (Fin I.card → K), Module.finrank K S = 2 ∧
      ∀ x ∈ S, Q x = 0 := by
    by_contra hS
    obtain ⟨-, -, -, -, h4n, -, -⟩ := orthogonal_low_dimensional_fixed_derived_component_coverage
      Q hQnd (Or.inl ⟨hodd', Or.inr (Or.inl hdim)⟩)
    obtain ⟨-, -, -, -, -, -, -, -, hq''⟩ := h4n hodd' hdim hS
    apply hq'
    have h := isQuasisimple_trans e₁ hq''
    rwa [trans_commutator] at h
  exact (isPlusType_congr (blockIsometry hw I)).1 ⟨S, by rw [hS2, hdim], hSQ⟩

theorem isPlusType_of_not_isQuasisimple_four [Finite K] (hK : ringChar K ≠ 2) {w : Fin d → K}
    (hw : ∀ i, w i ≠ 0) {J : Finset (Fin d)} (hJ4 : J.card = 4) (hJc4 : Jᶜ.card = 4)
    (hqJ : ¬ IsQuasisimple (blockP K hw J)) (hqJc : ¬ IsQuasisimple (blockP K hw Jᶜ)) :
    IsPlusType (oQ (diagGL hw)) := by
  have hJc : Jᶜ.Nonempty := Finset.card_pos.1 (by omega)
  have hJcc : Jᶜᶜ.Nonempty := by
    rw [compl_compl]
    exact Finset.card_pos.1 (by omega)
  have h1 := isPlusType_coordSub_of_not_isQuasisimple hK hw hJ4 hJc hqJ
  have h2 := isPlusType_coordSub_of_not_isQuasisimple hK hw hJc4 hJcc hqJc
  exact (isPlusType_congr (CatLeafProof.X11Char.sumIsometry (isCompl_coordSub J)
    (polar_coordSub_eq_zero hw J))).1 (h1.prod h2)

theorem exists_sign_frame_plus [Finite K] (hK : ringChar K ≠ 2) {R : GL (Fin d) K}
    (hR : (R : Matrix (Fin d) (Fin d) K)ᵀ = R) (hker : OKer (oQ R)) {T : GL (Fin d) K}
    (hT : T ∈ matrixDerived (oQ R)) (hT2 : (T : Matrix (Fin d) (Fin d) K) * T = 1)
    (hT1 : projH _ (⟨T, hT⟩ : matrixDerived (oQ R)) ≠ 1) :
    ∃ (w : Fin d → K) (hw : ∀ i, w i ≠ 0) (J : Finset (Fin d))
      (hJ : signGL K J ∈ matrixDerived (oQ (diagGL hw)))
      (θ : StatedProj (matrixDerived (oQ R)) ≃* StatedProj (matrixDerived (oQ (diagGL hw)))),
      OKer (oQ (diagGL hw)) ∧ J.Nonempty ∧ Jᶜ.Nonempty ∧
      (∀ I : Finset (Fin d), (I = J ∨ I = Jᶜ) → 3 ≤ I.card → BlockNF w I) ∧
      θ (projH _ ⟨T, hT⟩) = projH _ ⟨signGL K J, hJ⟩ ∧
      (IsPlusType (oQ (diagGL hw)) → IsPlusType (oQ R)) := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hTiso : T ∈ matrixIsometries (oQ R) := matrixDerived_le_isometries _ hT
  have hTR : (T : Matrix (Fin d) (Fin d) K)ᵀ * R * T = R :=
    (CatalogueBGraphForm.mem_isometryGroup _ _ _ _).1
      ((mem_matrixIsometries_oQ h2 R hR T).1 hTiso)
  obtain ⟨hab, cfr, hcA, horth, hdiag, hNF₁, hNF₂⟩ := exists_split_nf hK hR hTR hT2
  obtain ⟨hw, S, hS, heq⟩ := exists_transport_of_family h2 hTiso hab cfr hcA horth hdiag
  have hST : S * T * S⁻¹ = signGL K (famJ hab) := by
    have e := congrArg (fun g : similarityPairs (oQ (diagGL hw)) => g.val.left) heq
    simp only [transPair_left, linPair_left, linPair_right, map_one, MulAut.one_apply] at e
    rw [sgnPair, linPair_left] at e
    exact e
  have hXv : ((derivedTransport S 1 hS ⟨T, hT⟩ : matrixDerived (oQ (diagGL hw))) :
      GL (Fin d) K) = signGL K (famJ hab) := by
    rw [coe_derivedTransport]
    exact hST
  have hJ : signGL K (famJ hab) ∈ matrixDerived (oQ (diagGL hw)) :=
    hXv ▸ (derivedTransport S 1 hS ⟨T, hT⟩).2
  have hθt : oTransport S 1 hS (projH _ ⟨T, hT⟩) = projH _ ⟨signGL K (famJ hab), hJ⟩ := by
    rw [oTransport_proj]
    congr 1
    exact Subtype.ext hXv
  have hθ1 : oTransport S 1 hS (projH _ ⟨T, hT⟩) ≠ 1 := fun h1 =>
    hT1 ((oTransport S 1 hS).injective (by rw [h1, map_one]))
  let eL : (Fin d → K) ≃ₗ[K] (Fin d → K) := LinearEquiv.ofLinearMap
    (Matrix.toLin' (S : Matrix (Fin d) (Fin d) K))
    (Matrix.toLin' ((S⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K))
    (by rw [← Matrix.toLin'_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.toLin'_one])
  let eS : (oQ R).IsometryEquiv (oQ (diagGL hw)) :=
    { eL with
      map_app' := fun v => by
        change oQ (diagGL hw) (Matrix.toLin' (S : Matrix (Fin d) (Fin d) K) v) = oQ R v
        rw [Matrix.toLin'_apply, hS, Units.val_one, one_mul] }
  refine ⟨_, hw, famJ hab, hJ, oTransport S 1 hS, hker.transport S 1 hS, ?_, ?_, ?_, hθt,
    fun h => GroupTheory.WeirSylow.IsPlusType.of_isometryEquiv eS.symm h⟩
  · rw [Finset.nonempty_iff_ne_empty]
    intro hJe
    apply hθ1
    rw [hθt]
    have e : (⟨signGL K (famJ hab), hJ⟩ : matrixDerived (oQ (diagGL hw))) = 1 := by
      apply Subtype.ext
      apply Units.ext
      change ((signGL K (famJ hab) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1
      rw [coe_signGL, hJe]
      ext i j
      simp [signMat, Matrix.diagonal_apply, Matrix.one_apply]
    rw [e, map_one]
  · rw [Finset.nonempty_iff_ne_empty]
    intro hJe
    apply hθ1
    rw [hθt]
    have hJu : famJ hab = Finset.univ := (Finset.compl_eq_empty_iff _).1 hJe
    have hsc : signGL K (famJ hab) = GeneralLinearGroup.scalar (Fin d) (-1 : Kˣ) := by
      apply Units.ext
      rw [coe_signGL, GeneralLinearGroup.coe_scalar, hJu]
      ext i j
      simp [signMat, Matrix.diagonal_apply, Matrix.scalar_apply]
    have hmem : GeneralLinearGroup.scalar (Fin d) (-1 : Kˣ) ∈ matrixDerived (oQ (diagGL hw)) :=
      hsc ▸ hJ
    have e : (⟨signGL K (famJ hab), hJ⟩ : matrixDerived (oQ (diagGL hw))) =
        ⟨GeneralLinearGroup.scalar (Fin d) (-1 : Kˣ), hmem⟩ := Subtype.ext hsc
    rw [e]
    exact (QuotientGroup.eq_one_iff _).2 (mem_subgroupOf.2 ⟨-1, rfl⟩)
  · rintro I (rfl | rfl) h3
    · exact hNF₁ (by rw [card_famJ] at h3; exact h3)
    · apply hNF₂
      rw [Finset.card_compl, Fintype.card_fin, card_famJ] at h3
      omega

theorem false_of_typeD_three' {X : Type} [Group X] [Finite X] (hO : pPrimeCore 2 X = ⊥)
    {K : Type} [Field K] [Finite K] (hK3 : Nat.card K = 3) {n : ℕ}
    {R : GL (Fin (2 * n)) K} (hR : (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K)ᵀ = R)
    (hbig : 5 ≤ n ∨ (4 ≤ n ∧ ¬ IsPlusType (oQ R))) (hker : OKer (oQ R))
    (θ : X ⧸ center X ≃* StatedProj (matrixDerived (oQ R))) {c t : X}
    (hcZ : c ∈ center X) (hc2 : orderOf c = 2) (ht2 : orderOf t = 2) (htZ : t ∉ center X)
    {Q₁ : Subgroup X} (hQ₁ : IsSolvableTwoComponentIn Q₁ (centralizer {t})) (hcQ₁ : c ∈ Q₁) :
    False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 3 := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hK3])
  have hK : ringChar K ≠ 2 := by rw [ringChar.eq K 3]; norm_num
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hn4 : 4 ≤ n := by rcases hbig with h | h <;> omega
  set π₀ : X →* StatedProj (matrixDerived (oQ R)) :=
    θ.toMonoidHom.comp (QuotientGroup.mk' (center X)) with hπ₀
  have hπ₀s : Function.Surjective π₀ := θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hπ₀k : π₀.ker = center X := by
    ext y
    rw [MonoidHom.mem_ker, hπ₀, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have htt : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rwa [ht2, pow_two] at h
  have hxx : π₀ t * π₀ t = 1 := by rw [← map_mul, htt, map_one]
  have hx1 : π₀ t ≠ 1 := fun h => htZ (hπ₀k ▸ MonoidHom.mem_ker.mpr h)
  obtain ⟨T, hT, hxT, hT2 | hT2⟩ := P51e.Orth.exists_lift_sq h2 (by omega) hR hxx
  ·
    obtain ⟨w, hw, J, hJ, θ', hker', hJne, hJc, hNF, hθ'T, hplus⟩ :=
      exists_sign_frame_plus hK hR hker hT hT2 (by rw [← hxT]; exact hx1)
    set π : X →* StatedProj (matrixDerived (oQ (diagGL hw))) := θ'.toMonoidHom.comp π₀ with hπ
    have hπs : Function.Surjective π := θ'.surjective.comp hπ₀s
    have hπk : π.ker = center X := by
      ext y
      rw [MonoidHom.mem_ker, hπ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.map_eq_one_iff, ← MonoidHom.mem_ker, hπ₀k]
    have hπt : π t = projH _ ⟨signGL K J, hJ⟩ := by
      rw [hπ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hxT, hθ'T]
    obtain ⟨hR₁x, hR₁s, hR₁solv, hR₁odd, ⟨r, hr, hr3, hr1⟩, hnc⟩ :=
      facts_map_solvable_two hO π hπs hπk hcZ hc2 hQ₁ hcQ₁
    rw [hπt] at hR₁x hR₁s
    have hJev := P58b.OLie.even_card_of_signGL_mem hK hJ
    have hsum : J.card + Jᶜ.card = 2 * n := by
      rw [Finset.card_compl, Fintype.card_fin]
      have := Finset.card_le_univ J
      rw [Fintype.card_fin] at this
      omega
    have hJcev : Even Jᶜ.card := by
      obtain ⟨a, ha⟩ := hJev
      exact ⟨n - a, by omega⟩
    obtain ⟨I, hI, h3I, hqI, hIcev⟩ : ∃ I : Finset (Fin (2 * n)), (I = J ∨ I = Jᶜ) ∧
        3 ≤ I.card ∧ IsQuasisimple (blockP K hw I) ∧ Even Iᶜ.card := by
      by_cases h5 : 5 ≤ J.card
      · exact ⟨J, Or.inl rfl, by omega, P58b3.isQuasisimple_blockP_of_five_le hw hK h5 hJc,
          hJcev⟩
      by_cases h5' : 5 ≤ Jᶜ.card
      · exact ⟨Jᶜ, Or.inr rfl, by omega, P58b3.isQuasisimple_blockP_of_five_le hw hK h5'
          (by rwa [compl_compl]), by rw [compl_compl]; exact hJev⟩
      have hJ4 : J.card = 4 := by
        obtain ⟨a, ha⟩ := hJev
        obtain ⟨b, hb⟩ := hJcev
        omega
      have hJc4 : Jᶜ.card = 4 := by omega
      by_cases hqJ : IsQuasisimple (blockP K hw J)
      · exact ⟨J, Or.inl rfl, by omega, hqJ, hJcev⟩
      by_cases hqJc : IsQuasisimple (blockP K hw Jᶜ)
      · exact ⟨Jᶜ, Or.inr rfl, by omega, hqJc, by rw [compl_compl]; exact hJev⟩
      exfalso
      rcases hbig with h | ⟨-, hnp⟩
      · omega
      exact hnp (hplus (isPlusType_of_not_isQuasisimple_four hK hw hJ4 hJc4 hqJ hqJc))
    exact false_of_sign_of_quasisimple hw hK3 hker' hJ hJne hJc hNF hI h3I hqI hIcev hR₁x hR₁s
      hR₁solv hR₁odd hr hr3 hr1 hnc
  ·
    obtain ⟨R₁, A, θ₂, hR₁m, hAm, hθ₂T⟩ := exists_pc_model hK hR hT hT2
    set π : X →* StatedProj (matrixDerived (oQ R₁)) := θ₂.toMonoidHom.comp π₀ with hπ
    have hπs : Function.Surjective π := θ₂.surjective.comp hπ₀s
    have hπk : π.ker = center X := by
      ext y
      rw [MonoidHom.mem_ker, hπ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.map_eq_one_iff, ← MonoidHom.mem_ker, hπ₀k]
    have hπt : π t = projH _ A := by
      rw [hπ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hxT, hθ₂T]
    obtain ⟨hR₁x, hR₁s, hR₁solv, -, ⟨r, hr, hr3, hr1⟩, -⟩ :=
      facts_map_solvable_two hO π hπs hπk hcZ hc2 hQ₁ hcQ₁
    rw [hπt] at hR₁x hR₁s
    exact hr1 (eq_one_of_odd_of_pc hK3 (by omega) hR₁m hAm hR₁x hR₁s hR₁solv hr
      (Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hr3)))

end P58b3L

end CFSG.ComponentClassification.HarrisLit.T1
