module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24CentreClass
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.ExactSU

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

namespace KSConn

open TauCeti CFSG.ClassicalModels CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open Matrix
open scoped MatrixGroups

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

section PSL

theorem exists_A_of_statedClassicalModel_PSL (G : Type) [Group G] (n p f : ℕ)
    (h : StatedClassicalModel G .PSL n p f)
    (hdup : ¬ (LieTypeIndex.A (n - 1)
      ⟨p, f, h.1.1, by have hf := h.1.2.1; omega⟩).IsDuplicateRepresentative) :
    ∃ (q : PrimePower) (hv : (LieTypeIndex.A (n - 1) q).Valid), q.p = p ∧ q.exponent = f ∧
      Nonempty (G ≃* (CFSGIndex.lie ⟨LieTypeIndex.A (n - 1) q, hv⟩).Group) := by
  let q : PrimePower := ⟨p, f, h.1.1, by have hf := h.1.2.1; omega⟩
  let _ : Fact p.Prime := ⟨h.1.1⟩
  have hv : (LieTypeIndex.A (n - 1) q).Valid :=
    linearCatalog_index_valid n p f h.1 hdup
  obtain ⟨K, hfield, hfinite, hKcard, e⟩ := h.2
  let _ := hfield
  let _ := hfinite
  obtain ⟨e⟩ := e
  let eK := statedLinearModelEquivGaloisPSL K n p f
    (by have hf := h.1.2.1; omega) hKcard
  have hdim : n - 1 + 1 = n := by have hn := h.1.2.2.1; omega
  have eC := linearCatalogCandidateEquivPSL (n - 1) q hv
  have eC' : (ValidLieTypeIndex.Group ⟨LieTypeIndex.A (n - 1) q, hv⟩) ≃*
      ProjectiveSpecialLinearGroup (Fin n) (GaloisField p f) := by
    rw [hdim] at eC
    exact eC
  exact ⟨q, hv, rfl, rfl, ⟨(e.trans eK).trans eC'.symm⟩⟩

theorem statedClassicalModel_PSL_of_slCover {R : Type} [Group R] {K : Type} [Field K] [Finite K]
    {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) (hK4 : 4 ≤ Nat.card K)
    (g : SL(2, K) →* R) (hg : Function.Surjective g) (hgk : g.ker ≤ Subgroup.center SL(2, K))
    (hperf : commutator SL(2, K) = ⊤) :
    StatedClassicalModel (R ⧸ Subgroup.center R) .PSL 2 p f := by
  obtain ⟨e⟩ := nonempty_centralQuotient_mulEquiv hperf g hg hgk
  refine ⟨⟨hp, hf, le_rfl, fun h => ?_, fun h => ?_⟩, K, inferInstance, inferInstance, hK,
    ⟨e.symm.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K)⟩⟩
  · have := congrArg Prod.snd h
    simp only at this
    omega
  · have := congrArg Prod.snd h
    simp only at this
    omega

end PSL

section Shape


variable {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}

theorem exists_lieIndex_of_conn_class (S : LangSetup Tag.E6 L p₀) {Fr : L →+* L}
    (hFr : ∀ c, Fr c = c ^ S.D.q) (hΦ : S.D.Φ = twistHom TwistTag.E6 L Fr)
    (h3 : ((3 : ℕ) : L) ≠ 0) (hL2 : ringChar L = 2) {a : Fin Tag.E6.rank → Lˣ}
    (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus) (hap : ∀ i, a i ^ 3 = 1) (h3q : 3 ∣ S.D.q + 1)
    (hq8 : (kernelRoots (rootCharHom a)).ncard = 22 → S.D.q ≠ 8)
    (hk : (kernelRoots (rootCharHom a)).ncard = 22 ∨ (kernelRoots (rootCharHom a)).ncard = 30)
    (i : KernelComponent (rootCharHom a))
    (hQS : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    ∃ d : ValidLieTypeIndex,
      Nonempty ((↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) ≃*
          (CFSGIndex.lie d).Group) ∧
        3 ≠ d.1.characteristic ∧ ¬ CFSG.AGLEmbeddingD2.IsD2SeitzException 3 d.1 := by
  classical
  obtain ⟨m, hm, ψ, σ, π, hψ, hΨ, hπ1, hs1, -, hS1⟩ :=
    conn_class_unitary S hFr hΦ h3 hT hap h3q hk i
  have hπ : ∀ x y, x ≠ y → (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ
      (componentRoots (rootCharHom a) i)] (σ x y) = σ (π y) (π x) := fun x y hxy => by
    rw [hs1, Function.iterate_one]
    exact hπ1 x y hxy
  obtain ⟨r, e, hr, hchar, he, hq⟩ := S.exists_char_pow
  have hr2 : r = 2 := (ringChar.eq L r).symm.trans hL2
  subst hr2
  rcases hm with rfl | rfl | rfl
  ·
    obtain ⟨K, _, _, g, hg, hgk, hKcard, hK4, -⟩ :=
      exists_slCover_of_rankOne S hT i (hS1 rfl).1 (hS1 rfl).2.1 hQS hr hchar he hq
    rw [hs1, Nat.mul_one] at hKcard
    have he3 : e ≠ 3 := fun h => hq8 (hS1 rfl).2.2 (by rw [hq, h]; norm_num)
    haveI : Fintype K := Fintype.ofFinite K
    have hperf : commutator SL(2, K) = ⊤ :=
      (slFactorFacts_holds K 2 le_rfl (fun _ => by rwa [← Nat.card_eq_fintype_card])).perfect
    have hmodel := statedClassicalModel_PSL_of_slCover hr he hKcard hK4 g hg hgk hperf
    have hdup : ¬ (LieTypeIndex.A (2 - 1) ⟨2, e, hmodel.1.1, by have := hmodel.1.2.1; omega⟩
        ).IsDuplicateRepresentative := by
      rw [LieTypeIndex.isDuplicateRepresentative_iff]
      simp only [PrimePower.card_def]
      have hpar : 2 ∣ 2 ^ e := dvd_pow_self 2 (by omega)
      have h3q' : 3 ∣ 2 ^ e + 1 := hq ▸ h3q
      omega
    obtain ⟨q', hv, hqp, hqf, ⟨eq⟩⟩ := exists_A_of_statedClassicalModel_PSL _ 2 2 e hmodel hdup
    refine ⟨⟨LieTypeIndex.A (2 - 1) q', hv⟩, ⟨eq⟩, ?_, ?_⟩
    · simp [hqp]
    · simp only [CFSG.AGLEmbeddingD2.IsD2SeitzException]
      simp
      intro _ h
      exact he3 (hqf ▸ h)
  ·
    have hmodel := KSExact.rationalComponent_suN_model S hT i (ν := 4 + 1) (by norm_num) hψ hΨ π
      hπ hr hchar he hq (by simp)
    rw [hs1, Nat.mul_one] at hmodel
    obtain ⟨q', hv, hqp, hqf, ⟨eq⟩⟩ := KSExact.exists_twistedA_of_statedClassicalModel_PSU hmodel
    refine ⟨⟨LieTypeIndex.twistedA 4 q', hv⟩, ⟨eq⟩, ?_, ?_⟩
    · simp [hqp]
    · simp [CFSG.AGLEmbeddingD2.IsD2SeitzException]
  ·
    have hmodel := KSExact.rationalComponent_suN_model S hT i (ν := 5 + 1) (by norm_num) hψ hΨ π
      hπ hr hchar he hq (by simp)
    rw [hs1, Nat.mul_one] at hmodel
    obtain ⟨q', hv, hqp, hqf, ⟨eq⟩⟩ := KSExact.exists_twistedA_of_statedClassicalModel_PSU hmodel
    refine ⟨⟨LieTypeIndex.twistedA 5 q', hv⟩, ⟨eq⟩, ?_, ?_⟩
    · simp [hqp]
    · simp [CFSG.AGLEmbeddingD2.IsD2SeitzException]

end Shape

end KSConn

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
