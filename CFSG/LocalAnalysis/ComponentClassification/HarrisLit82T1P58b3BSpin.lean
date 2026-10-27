module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3B57
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58bOLieComp

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinearFiltration
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.Burgoyne.O CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.C
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL signMat)
open CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.Classical.SteinbergBY
  (OrthogonalGates orthogonal_large_prime_semilinear_field_and_diagonal_gates)
open scoped MatrixGroups

namespace P58b3

theorem oddAutInner_of_isCoverOf_POmegaOdd_three {X : Type} [Group X] [Finite X] {n p f : ℕ}
    (hp : p.Prime) (h3 : p ^ f = 3) (hX : IsCoverOf .POmegaOdd n p f 2 X) : OddAutInner X := by
  intro α k hk hα
  obtain ⟨hq, -, hL⟩ := hX
  have : Group.IsPerfect X := hq.1
  rcases hL with ⟨-, hcm⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩
  · have hcm' := hcm
    obtain ⟨⟨-, hf, hn, hp2⟩, K, _, _, hK, ⟨e⟩⟩ := hcm'
    have h2 : ringChar K ≠ 2 := by
      rw [CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq hp hf hK]
      exact hp2
    have hK3 : Nat.card K = 3 := hK.trans h3
    obtain ⟨-, ⟨ψ, -, hψker, -⟩, ⟨-, m, hm⟩, -⟩ :=
      orthogonal_large_prime_semilinear_field_and_diagonal_gates
        (X ⧸ center X) .POmegaOdd (Or.inl rfl) n p f hcm K hK e
    have htop := CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_odd K n
      hn h2
    have hD : (linearConjugationHom (coordinateQuadOdd n K)).range = ⊤ := by
      rw [eq_top_iff]
      intro a _
      have ha : a ∈ matrixProjectiveImage (coordinateQuadOdd n K) := htop ▸ mem_top a
      have hker : (⟨a, ha⟩ : matrixProjectiveImage (coordinateQuadOdd n K)) ∈ ψ.ker :=
        MonoidHom.mem_ker.mpr (ringEquiv_eq_one_of_card_eq_three hK3 _)
      rw [hψker] at hker
      exact hker
    rw [hD, relIndex_top_right] at hm
    set e' := coordinateOddWitnessEquiv K e with he'
    let Φ : MulAut X →* MulAut (matrixProjectiveDerived (coordinateQuadOdd n K)) :=
      (MulAut.congr e').toMonoidHom.comp (PerfectAutomorphisms.centerQuotientHom X)
    have hΦconj : ∀ x : X, Φ (MulAut.conj x) = MulAut.conj (e' (QuotientGroup.mk' (center X) x)) :=
      fun x => by
        change MulAut.congr e' (PerfectAutomorphisms.onCenterQuotient (MulAut.conj x)) = _
        rw [onCenterQuotient_conj, OuterAutomorphisms.congr_conj]
    have hconjΦ : ∀ y, ∃ x : X, MulAut.conj y = Φ (MulAut.conj x) := fun y => by
      obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (center X) (e'.symm y)
      exact ⟨x, by rw [hΦconj, hx, MulEquiv.apply_symm_apply]⟩
    have hΦ : Function.Injective Φ :=
      (MulAut.congr e').injective.comp (PerfectAutomorphisms.centerQuotientHom_injective X)
    have hI : (inner (matrixProjectiveDerived (coordinateQuadOdd n K))).comap Φ =
        (MulAut.conj : X →* MulAut X).range := by
      ext β
      rw [mem_comap]
      constructor
      · rintro ⟨y, hy⟩
        obtain ⟨x, hx⟩ := hconjΦ y
        exact ⟨x, hΦ (hx.symm.trans hy)⟩
      · rintro ⟨x, rfl⟩
        exact ⟨_, (hΦconj x).symm⟩
    rw [← hI] at hα ⊢
    rw [mem_comap, map_pow] at hα
    exact mem_of_pow_mem_of_index_eq_two_pow hm hk hα
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)

theorem cyclicCenterTwo_of_card_center_eq_two {X : Type} [Group X]
    (hZ : Nat.card (center X) = 2) : CyclicCenterTwo X :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  cyclicCenterTwo_of_isCyclic (isCyclic_of_prime_card hZ)

theorem exists_spin_compat_three {Y : Type} [Group Y] [Finite Y] {n : ℕ} {K : Type} [Field K]
    [Finite K] (hK3 : Nat.card K = 3) (h2 : (2 : K) ≠ 0) (hn4 : 4 ≤ n) (hY : IsQuasisimple Y)
    (hZ : Nat.card (center Y) = 2)
    (e : Y ⧸ center Y ≃* StatedProj (StatedOmega (StatedQuadOdd n K))) :
    ∃ α : spinGroup (quadOdd n K) ≃* Y, ∀ s, e (QuotientGroup.mk (α s)) =
      spinToStatedProj (quadOdd n K) (range_spinMatrix_quadOdd h2 (by omega)) s := by
  have hn : 3 ≤ n := by omega
  have : Finite (spinGroup (quadOdd n K)) :=
    LieType.Steinberg.finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadOdd h2)
  have : Group.IsPerfect Y := hY.1
  obtain ⟨hβs, -, -⟩ := spinToStatedProj_quadOdd h2 hn
  set β := spinToStatedProj (quadOdd n K) (range_spinMatrix_quadOdd h2 hn) with hβ
  set η : Y →* StatedProj (StatedOmega (StatedQuadOdd n K)) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (center Y)) with hη
  have hηs : Function.Surjective η := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hηker : η.ker = center Y := by
    ext y
    rw [MonoidHom.mem_ker, hη, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hZ2 : IsPGroup 2 (center Y) := IsPGroup.of_card (n := 1) (by rw [hZ, pow_one])
  obtain ⟨α, hα, hαs, hker⟩ := LieType.Steinberg.exists_surjective_of_isPerfect
    (fun E _ _ π hπ hcen _ =>
      LieType.Steinberg.CentralExt.SpinOddClosed.spinOdd_three_exists_section_of_central hK3 hn4
        hπ hcen)
    hβs hηs (hηker ▸ le_rfl) (hηker ▸ hZ2)
  have hβcard : Nat.card β.ker = 2 :=
    LieType.Steinberg.CentralExt.SpinOddClosed.card_ker_spinToStatedProj_quadOdd h2 hn
  have hαβ : α.ker ≤ β.ker := by
    intro A hA
    rw [MonoidHom.mem_ker] at hA ⊢
    rw [← hα, hA, map_one]
  have hne : α.ker ≠ β.ker := by
    intro h1
    have hbot : center Y = ⊥ := by
      rw [← hηker, hker, ← h1, eq_bot_iff]
      rintro _ ⟨x, hx, rfl⟩
      exact hx
    rw [hbot, Subgroup.card_bot] at hZ
    exact absurd hZ (by norm_num)
  have hdvd : Nat.card α.ker ∣ Nat.card β.ker := Subgroup.card_dvd_of_le hαβ
  have h1 : Nat.card α.ker = 1 := by
    rw [hβcard] at hdvd
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact h
    · exact absurd (Subgroup.eq_of_le_of_card_ge hαβ (by rw [h, hβcard])) hne
  have hinj : Function.Injective α :=
    (MonoidHom.ker_eq_bot_iff α).1 (Subgroup.eq_bot_of_card_eq _ h1)
  exact ⟨MulEquiv.ofBijective α ⟨hinj, hαs⟩, fun s => hα s⟩

variable {K : Type} [Field K] [Finite K] {d : ℕ}

theorem exists_sign_frame_rank_ker (hK : ringChar K ≠ 2) {R : GL (Fin d) K}
    (hR : (R : Matrix (Fin d) (Fin d) K)ᵀ = R) (hker : OKer (oQ R)) {T : GL (Fin d) K}
    (hT : T ∈ matrixDerived (oQ R)) (hT2 : (T : Matrix (Fin d) (Fin d) K) * T = 1)
    (hT1 : projH _ (⟨T, hT⟩ : matrixDerived (oQ R)) ≠ 1) :
    ∃ (w : Fin d → K) (hw : ∀ i, w i ≠ 0) (J : Finset (Fin d))
      (hJ : signGL K J ∈ matrixDerived (oQ (diagGL hw)))
      (θ : StatedProj (matrixDerived (oQ R)) ≃* StatedProj (matrixDerived (oQ (diagGL hw)))),
      OKer (oQ (diagGL hw)) ∧ J.Nonempty ∧ Jᶜ.Nonempty ∧
      (∀ I : Finset (Fin d), (I = J ∨ I = Jᶜ) → 3 ≤ I.card → BlockNF w I) ∧
      θ (projH _ ⟨T, hT⟩) = projH _ ⟨signGL K J, hJ⟩ ∧
      ((T : Matrix (Fin d) (Fin d) K) + 1).rank = Jᶜ.card := by
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
  have hrankJ : ∀ J : Finset (Fin d), S * T * S⁻¹ = signGL K J →
      ((T : Matrix (Fin d) (Fin d) K) + 1).rank = Jᶜ.card := by
    intro J hSTJ
    have hTm : (T : Matrix (Fin d) (Fin d) K) =
        ((S⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * signMat K J * S := by
      rw [← coe_signGL, ← hSTJ]
      simp only [Units.val_mul]
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mul, Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.mul_one]
    have hsum : (T : Matrix (Fin d) (Fin d) K) + 1 =
        ((S⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * (signMat K J + 1) * S := by
      rw [hTm, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, ← Units.val_mul, inv_mul_cancel,
        Units.val_one]
    rw [hsum, rank_mul_eq_left_of_isUnit_det _ _ (Matrix.isUnits_det_units S),
      rank_mul_eq_right_of_isUnit_det _ _ (Matrix.isUnits_det_units S⁻¹),
      P58b.OLie.rank_signMat_add_one hK]
  have hrank := hrankJ _ hST
  refine ⟨_, hw, famJ hab, hJ, oTransport S 1 hS, hker.transport S 1 hS, ?_, ?_, ?_, hθt, hrank⟩
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

end P58b3

end CFSG.ComponentClassification.HarrisLit.T1
