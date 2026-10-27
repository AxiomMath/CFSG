module

public import Mathlib
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKFLift
public import CFSG.LocalAnalysis.AGLEmbeddingD2.LieCross
public import CFSG.Open.StatedDefs
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Adapters.LinearCatalog
public import CFSG.Adapters.RankTwoModelTransports
public import CFSG.Open.StatedSUFieldChange
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Classification
public import CFSG.Assembly.QuasithinDefs
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Permutation.AlternatingAutomorphism
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKF

open CFSG CFSG.Open CFSG.Assembly.LowTwoRank

theorem SeitzGen.of_mulEquiv {p : ℕ} {Q Q' : Type*} [Group Q] [Group Q'] (e : Q ≃* Q')
    (h : SeitzGen p Q') : SeitzGen p Q := by
  intro D hD hcard
  have hinj : Function.Injective e.toMonoidHom := e.injective
  have hD' : IsElemAbelian p (D.map e.toMonoidHom) := hD.map e.toMonoidHom
  have hcard' : Nat.card (D.map e.toMonoidHom) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective hinj]
    exact hcard
  have htop := h (D.map e.toMonoidHom) hD' hcard'
  have hset : {k' : Q' | ∃ d' ∈ D.map e.toMonoidHom, d' ≠ 1 ∧ k' * d' = d' * k'} =
      e.toMonoidHom '' {k : Q | ∃ d ∈ D, d ≠ 1 ∧ k * d = d * k} := by
    ext k'
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨d', hd', hd1', hk'⟩
      obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hd'
      refine ⟨e.symm k', ⟨d, hd, fun h1 => hd1' (by rw [h1, map_one]), ?_⟩, by simp⟩
      apply e.injective
      rw [map_mul, map_mul, e.apply_symm_apply]
      exact hk'
    · rintro ⟨k, ⟨d, hd, hd1, hkd⟩, rfl⟩
      refine ⟨e.toMonoidHom d, Subgroup.mem_map_of_mem _ hd, fun h1 => hd1 ?_, ?_⟩
      · exact hinj (h1.trans (map_one e.toMonoidHom).symm)
      · rw [← map_mul, ← map_mul, hkd]
  rw [hset, ← MonoidHom.map_closure] at htop
  have hc := congrArg (Subgroup.comap e.toMonoidHom) htop
  rw [Subgroup.comap_map_eq_self_of_injective hinj, Subgroup.comap_top] at hc
  exact hc

theorem seitzGen_of_lie (hS : CFSG.AGLEmbeddingD2.KFactSeitzRankTwo) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (d : TauCeti.ValidLieTypeIndex) (hpc : p ≠ d.1.characteristic)
    (hexc : ¬ CFSG.AGLEmbeddingD2.IsD2SeitzException p d.1)
    {Q : Type} [Group Q] [IsSimpleGroup Q] (hQ : ∃ a b : Q, a * b ≠ b * a)
    (e : Q ≃* (TauCeti.CFSGIndex.lie d).Group) : SeitzGen p Q := by
  have hZ : Subgroup.center Q = ⊥ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center Q) with h | h
    · exact h
    · obtain ⟨a, b, hab⟩ := hQ
      have hb : b ∈ Subgroup.center Q := by
        rw [h]
        exact Subgroup.mem_top _
      exact absurd (Subgroup.mem_center_iff.mp hb a) hab
  have hcentre : ∀ g : (TauCeti.CFSGIndex.lie d).Group,
      (∀ x : (TauCeti.CFSGIndex.lie d).Group, g * x = x * g) → g = 1 := by
    intro g hg
    have hq : e.symm g ∈ Subgroup.center Q := by
      rw [Subgroup.mem_center_iff]
      intro x
      apply e.injective
      rw [map_mul, map_mul, e.apply_symm_apply]
      exact (hg (e x)).symm
    rw [hZ, Subgroup.mem_bot] at hq
    have h2 : e (e.symm g) = e 1 := by rw [hq]
    rwa [e.apply_symm_apply, map_one] at h2
  have hinj : Function.Injective (MulAut.conj : (TauCeti.CFSGIndex.lie d).Group →*
      MulAut (TauCeti.CFSGIndex.lie d).Group) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    apply hcentre g
    intro x
    have h1 := DFunLike.congr_fun hg x
    rw [MulAut.conj_apply, MulAut.one_apply] at h1
    exact mul_inv_eq_iff_eq_mul.mp h1
  have hK : SeitzGen p (TauCeti.CFSGIndex.lie d).Group := by
    intro D hD hcard
    have hE : IsElemAbelian p (D.map (MulAut.conj : (TauCeti.CFSGIndex.lie d).Group →*
        MulAut (TauCeti.CFSGIndex.lie d).Group)) := hD.map _
    have hEcard : Nat.card (D.map (MulAut.conj : (TauCeti.CFSGIndex.lie d).Group →*
        MulAut (TauCeti.CFSGIndex.lie d).Group)) = p ^ 2 := by
      rw [Subgroup.card_map_of_injective hinj]
      exact hcard
    have htop := hS d p hp hp2 hpc hexc _ hE hEcard
    have hset : {k : (TauCeti.CFSGIndex.lie d).Group | ∃ f ∈ D.map (MulAut.conj :
        (TauCeti.CFSGIndex.lie d).Group →* MulAut (TauCeti.CFSGIndex.lie d).Group),
          f ≠ 1 ∧ f k = k} =
        {k : (TauCeti.CFSGIndex.lie d).Group | ∃ g ∈ D, g ≠ 1 ∧ k * g = g * k} := by
      ext k
      simp only [Set.mem_setOf_eq, Subgroup.mem_map]
      constructor
      · rintro ⟨φ, ⟨g, hg, rfl⟩, hφ1, hφk⟩
        refine ⟨g, hg, fun h1 => hφ1 ?_, ?_⟩
        · rw [h1, map_one]
        · rw [MulAut.conj_apply] at hφk
          exact (mul_inv_eq_iff_eq_mul.mp hφk).symm
      · rintro ⟨g, hg, hg1, hkg⟩
        refine ⟨MulAut.conj g, ⟨g, hg, rfl⟩, fun h1 => hg1 ?_, ?_⟩
        · apply hinj
          rw [map_one]
          exact h1
        · rw [MulAut.conj_apply, ← hkg, mul_inv_cancel_right]
    rw [hset] at htop
    exact htop
  exact SeitzGen.of_mulEquiv e hK

theorem lieIndex_of_statedPSL {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {Q : Type} [Group Q]
    (K : Type) [Field K] [Finite K] (hK : p ∣ Nat.card K - 1)
    (e : Q ≃* StatedProj (StatedSL p K)) :
    ∃ d : TauCeti.ValidLieTypeIndex, Nonempty (Q ≃* (TauCeti.CFSGIndex.lie d).Group) ∧
      p ≠ d.1.characteristic ∧ ¬ CFSG.AGLEmbeddingD2.IsD2SeitzException p d.1 := by
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by omega⟩
  letI : Fintype K := Fintype.ofFinite K
  obtain ⟨r, -, ⟨f, hf⟩, hr, hKcard⟩ := FiniteField.card' K
  have hK' : Nat.card K = r ^ f := by
    rw [Nat.card_eq_fintype_card]
    exact hKcard
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : Fact (TauCeti.PrimePower.p ⟨r, f, hr, hf⟩).Prime := ⟨hr⟩
  have hv : (TauCeti.LieTypeIndex.A n ⟨r, f, hr, hf⟩).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    refine ⟨⟨by omega, fun h => by omega⟩, ?_⟩
    rintro (⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩) <;> omega
  refine ⟨⟨TauCeti.LieTypeIndex.A n ⟨r, f, hr, hf⟩, hv⟩,
    ⟨e.trans ((CFSG.ClassicalModels.statedLinearModelEquivGaloisPSL K (n + 1) r f hf hK').trans
      (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL n ⟨r, f, hr, hf⟩ hv).symm)⟩, ?_, ?_⟩
  · intro h
    change n + 1 = (TauCeti.LieTypeIndex.A n ⟨r, f, hr, hf⟩).characteristic at h
    rw [TauCeti.LieTypeIndex.characteristic_A] at h
    have h' : n + 1 = r := h
    rw [h', hK'] at hK
    have h1 : r ∣ r ^ f := dvd_pow_self r hf.ne'
    have h2 : r ∣ r ^ f - (r ^ f - 1) := Nat.dvd_sub h1 hK
    have h3 : 0 < r ^ f := pow_pos hr.pos f
    have h4 : r ^ f - (r ^ f - 1) = 1 := by omega
    rw [h4] at h2
    exact hr.one_lt.ne' (Nat.dvd_one.mp h2)
  · simp only [CFSG.AGLEmbeddingD2.IsD2SeitzException]
    rintro (⟨h3, -⟩ | ⟨-, hd | hd⟩)
    · omega
    · cases hd
    · cases hd

theorem lieIndex_of_statedPSU {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {Q : Type} [Group Q] (q : ℕ)
    (K : Type) [Field K] [Finite K] (hKq : Nat.card K = q ^ 2) (hq : p ∣ q + 1)
    (e : Q ≃* StatedProj (StatedSU p q K)) :
    ∃ d : TauCeti.ValidLieTypeIndex, Nonempty (Q ≃* (TauCeti.CFSGIndex.lie d).Group) ∧
      p ≠ d.1.characteristic ∧ ¬ CFSG.AGLEmbeddingD2.IsD2SeitzException p d.1 := by
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by omega⟩
  have hn4 : 4 ≤ n := by omega
  letI : Fintype K := Fintype.ofFinite K
  obtain ⟨m, hρ, hKm⟩ := FiniteField.card K (ringChar K)
  have hcard : Fintype.card K = q ^ 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact hKq
  have hdvd : q ∣ ringChar K ^ (m : ℕ) := ⟨q, by rw [← hKm, hcard, sq]⟩
  obtain ⟨j, -, hqj⟩ := (Nat.dvd_prime_pow hρ).1 hdvd
  have hq4 : 4 ≤ q := by
    have := Nat.le_of_dvd (by omega) hq
    omega
  have hj : 0 < j := by
    rcases Nat.eq_zero_or_pos j with h | h
    · rw [h, pow_zero] at hqj
      omega
    · exact h
  subst hqj
  haveI : Fact (ringChar K).Prime := ⟨hρ⟩
  letI : Fintype (GaloisField (ringChar K) (2 * j)) := Fintype.ofFinite _
  have hcardK : Fintype.card K = Fintype.card (GaloisField (ringChar K) (2 * j)) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hKq,
      GaloisField.card (ringChar K) (2 * j) (by omega), ← pow_mul, mul_comm]
  let φ : K ≃+* GaloisField (ringChar K) (2 * j) := FiniteField.ringEquivOfCardEq hcardK
  have e1 := CFSG.Open.StatedSUFieldChange.statedProjSUEquiv φ (n + 1) (ringChar K ^ j)
  have hv : (TauCeti.LieTypeIndex.twistedA n ⟨ringChar K, j, hρ, hj⟩).Valid :=
    (TauCeti.LieTypeIndex.valid_iff _).2
      ⟨(TauCeti.LieTypeIndex.inStandardRange_iff _).2 ⟨by omega, fun _ => by omega⟩,
        fun h => (TauCeti.LieTypeIndex.isDuplicateRepresentative_iff _).1 h⟩
  have hc : TauCeti.ValidLieTypeIndex.characteristic
      ⟨TauCeti.LieTypeIndex.twistedA n ⟨ringChar K, j, hρ, hj⟩, hv⟩ = ringChar K :=
    TauCeti.LieTypeIndex.characteristic_twistedA n _
  have hf : TauCeti.ValidLieTypeIndex.fieldExponent
      ⟨TauCeti.LieTypeIndex.twistedA n ⟨ringChar K, j, hρ, hj⟩, hv⟩ = j :=
    TauCeti.LieTypeIndex.fieldExponent_twistedA n _
  have key : ∀ (a b f g : ℕ) [Fact a.Prime] [Fact b.Prime], a = b → f = g →
      Nonempty (StatedProj (StatedSU (n + 1) (a ^ f) (GaloisField a (2 * f))) ≃*
        StatedProj (StatedSU (n + 1) (b ^ g) (GaloisField b (2 * g)))) := by
    intro a b f g _ _ hab hfg
    subst hab hfg
    exact ⟨MulEquiv.refl _⟩
  obtain ⟨eX⟩ := key _ _ _ _ hc.symm hf.symm
  have hc' : (TauCeti.LieTypeIndex.twistedA n ⟨ringChar K, j, hρ, hj⟩).characteristic =
      ringChar K :=
    TauCeti.LieTypeIndex.characteristic_twistedA n _
  refine ⟨⟨TauCeti.LieTypeIndex.twistedA n ⟨ringChar K, j, hρ, hj⟩, hv⟩, ?_, ?_, ?_⟩
  · exact ⟨e.trans (e1.trans (eX.trans (CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj
      n ⟨ringChar K, j, hρ, hj⟩ hv).symm))⟩
  · show n + 1 ≠ (TauCeti.LieTypeIndex.twistedA n ⟨ringChar K, j, hρ, hj⟩).characteristic
    rw [hc']
    intro h
    rw [h] at hq
    exact hρ.not_dvd_one ((Nat.dvd_add_right (dvd_pow_self (ringChar K) hj.ne')).mp hq)
  · show ¬ CFSG.AGLEmbeddingD2.IsD2SeitzException (n + 1)
      (TauCeti.LieTypeIndex.twistedA n ⟨ringChar K, j, hρ, hj⟩)
    rintro (⟨h3, -⟩ | ⟨-, h | h⟩)
    · omega
    · cases h
    · cases h

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKF
