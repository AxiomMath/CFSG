module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24A2CubeOuter
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24CentreFinal
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24D4T2Comp
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24D4T2Outer
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24EvenClass
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24EvenD5Index
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.IndicesTwistedA
public import CFSG.LieType.SeitzGeneration.QuasiHigh
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.ExcOuter

public section

namespace CFSG.LieType.SeitzGeneration.CubeCoverE6

open TauCeti CFSG.ClassicalModels CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.Seitz
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSConn
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24
open scoped MatrixGroups

theorem not_isLThreeFour_of_psu_stated
    {X : Type} [Group X] {m f : ℕ} (h : StatedClassicalModel X .PSU m 2 f) :
    ¬ IsLThreeFour X :=
  CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2.not_isLThreeFour_of_lieModel_two
    (show Blueprint.LieModel X .PSU m 2 f from Or.inl ⟨by decide, h⟩) (by decide)

theorem cover_shape_of_map_injective {X Y : Type} [Group X] [Group Y] (ι : X →* Y)
    (hι : Function.Injective ι) {J : Subgroup X}
    (h : ∃ (d : TauCeti.ValidLieTypeIndex)
        (_ : ((J.map ι) ⧸ Subgroup.center (J.map ι)) ≃*
          (TauCeti.CFSGIndex.lie d).Group),
        3 ≠ d.1.characteristic ∧ ¬ AGLEmbeddingD2.IsD2SeitzException 3 d.1 ∧
          (QuasiHigh.CoverIndex 3 d.1 →
            ¬ ExcIndex 3 d.1 ∧
              ¬ IsLThreeFour ((J.map ι) ⧸ Subgroup.center (J.map ι)))) :
    ∃ (d : TauCeti.ValidLieTypeIndex)
        (_ : (J ⧸ Subgroup.center J) ≃* (TauCeti.CFSGIndex.lie d).Group),
      3 ≠ d.1.characteristic ∧ ¬ AGLEmbeddingD2.IsD2SeitzException 3 d.1 ∧
        (QuasiHigh.CoverIndex 3 d.1 →
          ¬ ExcIndex 3 d.1 ∧ ¬ IsLThreeFour (J ⧸ Subgroup.center J)) := by
  obtain ⟨d, e, hd3, hD2, hcl⟩ := h
  let φ : J ≃* J.map ι := J.equivMapOfInjective ι hι
  have hZ : (Subgroup.center J).map φ.toMonoidHom = Subgroup.center (J.map ι) :=
    Subgroup.map_center_eq φ
  let ψ : (J ⧸ Subgroup.center J) ≃*
      ((J.map ι) ⧸ Subgroup.center (J.map ι)) := QuotientGroup.congr _ _ φ hZ
  refine ⟨d, ψ.trans e, hd3, hD2, fun hc => ⟨(hcl hc).1, fun hL => (hcl hc).2 ?_⟩⟩
  exact CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz3.isLThreeFour_congr ψ.symm hL

section ConnClass

theorem exists_coverIndex_of_conn_class
    {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup Tag.E6 L p₀)
    {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ S.D.q)
    (hΦ : S.D.Φ = twistHom TwistTag.E6 L Fr) (h3 : ((3 : ℕ) : L) ≠ 0)
    (hL2 : ringChar L = 2) {a : Fin Tag.E6.rank → Lˣ}
    (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus) (hap : ∀ i, a i ^ 3 = 1)
    (h3q : 3 ∣ S.D.q + 1) (hq2 : S.D.q ≠ 2) (hq8 : S.D.q ≠ 8)
    (hk : (kernelRoots (rootCharHom a)).ncard = 22 ∨
      (kernelRoots (rootCharHom a)).ncard = 30)
    (i : KernelComponent (rootCharHom a))
    (hQS : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    ∃ (d : TauCeti.ValidLieTypeIndex)
        (_ : (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
          Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) ≃*
          (TauCeti.CFSGIndex.lie d).Group),
      3 ≠ d.1.characteristic ∧ ¬ CFSG.AGLEmbeddingD2.IsD2SeitzException 3 d.1 ∧
        (QuasiHigh.CoverIndex 3 d.1 →
          ¬ ExcIndex 3 d.1 ∧
            ¬ IsLThreeFour (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
              Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))) := by
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
    have he3 : e ≠ 3 := fun h => hq8 (by rw [hq, h]; norm_num)
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
    refine ⟨⟨LieTypeIndex.A (2 - 1) q', hv⟩, eq, ?_, ?_, ?_⟩
    · simp [hqp]
    · simp only [CFSG.AGLEmbeddingD2.IsD2SeitzException]
      simp
      intro _ h
      exact he3 (hqf ▸ h)
    · intro hc
      exact absurd hc (by simp [QuasiHigh.CoverIndex])
  ·
    have hmodel := KSExact.rationalComponent_suN_model S hT i (ν := 4 + 1) (by norm_num) hψ hΨ π
      hπ hr hchar he hq (by simp)
    rw [hs1, Nat.mul_one] at hmodel
    obtain ⟨q', hv, hqp, hqf, ⟨eq⟩⟩ := KSExact.exists_twistedA_of_statedClassicalModel_PSU hmodel
    refine ⟨⟨LieTypeIndex.twistedA 4 q', hv⟩, eq, ?_, ?_, ?_⟩
    · simp [hqp]
    · simp [CFSG.AGLEmbeddingD2.IsD2SeitzException]
    · intro hc
      exact absurd hc (by simp [QuasiHigh.CoverIndex])
  ·
    have hmodel := KSExact.rationalComponent_suN_model S hT i (ν := 5 + 1) (by norm_num) hψ hΨ π
      hπ hr hchar he hq (by simp)
    rw [hs1, Nat.mul_one] at hmodel
    obtain ⟨q', hv, hqp, hqf, ⟨eq⟩⟩ := KSExact.exists_twistedA_of_statedClassicalModel_PSU hmodel
    have hq'1 : ¬ IsTwoPow q' 1 := by
      rintro ⟨-, h1⟩
      have he1 : e = 1 := by rw [hqf] at h1; omega
      exact hq2 (by rw [hq, he1]; norm_num)
    have hq'3 : ¬ IsTwoPow q' 3 := by
      rintro ⟨-, h3⟩
      have he3 : e = 3 := by rw [hqf] at h3; omega
      exact hq8 (by rw [hq, he3]; norm_num)
    refine ⟨⟨LieTypeIndex.twistedA 5 q', hv⟩, eq, ?_, ?_, ?_⟩
    · simp [hqp]
    · simp [CFSG.AGLEmbeddingD2.IsD2SeitzException]
    · intro _
      exact ⟨not_excIndex_twistedA hq'1 hq'3, not_isLThreeFour_of_psu_stated hmodel⟩

end ConnClass

section Dim

theorem twE6CoverShape_of_dim
    (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ)
    (hK3 : ringChar K ≠ 3) (hK2 : ringChar K = 2) (hσ : ∀ c, σ c = c ^ q)
    (hKq : Nat.card K = q ^ 2) (hq2 : 2 ≤ q) (h3q : 3 ∣ q + 1) (hq2ne : q ≠ 2)
    (hq8 : q ≠ 8) (h : twistedE6InndiagGL K σ) (hh1 : h ≠ 1) (hh3 : h ^ 3 = 1)
    (hdim : twE6MatFixDim K σ h = 28 ∨ twE6MatFixDim K σ h = 36)
    {J : Subgroup (twistedE6RootGroup K σ)}
    (hJ : CFSG.Open.IsComponentOf J
      (fixedPoints (Subgroup.zpowers (twistedE6InndiagConj K σ h)))) :
    ∃ (d : TauCeti.ValidLieTypeIndex)
        (_ : (J ⧸ Subgroup.center J) ≃* (TauCeti.CFSGIndex.lie d).Group),
      3 ≠ d.1.characteristic ∧ ¬ AGLEmbeddingD2.IsD2SeitzException 3 d.1 ∧
        (QuasiHigh.CoverIndex 3 d.1 →
          ¬ ExcIndex 3 d.1 ∧ ¬ IsLThreeFour (J ⧸ Subgroup.center J)) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨hp, f, hf, hqf⟩ := prime_ringChar_and_eq_pow_of_card_sq K q hKq hq2
  have hK' : Nat.card K = (ringChar K ^ f) ^ 2 := by rw [← hqf]; exact hKq
  have hσ' : ∀ c, σ c = c ^ (ringChar K ^ f) := by intro c; rw [← hqf]; exact hσ c
  have hpℓ : 3 ≠ ringChar K := fun h' => hK3 h'.symm
  obtain ⟨p₀, hp₀, hp₀ℓ, hq₀⟩ := exists_setup_prime hp hf Nat.prime_three (by norm_num) hpℓ
  have hh3' : (h : ModGL TwistTag.E6.tag K) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, hh3]
    rfl
  have hh1' : (h : ModGL TwistTag.E6.tag K) ≠ 1 := fun h' => hh1 (Subtype.ext h')
  obtain ⟨S, a, ι, hDq, ⟨Fr, hFr, hΦ⟩, hT, hap, h1, hinj, hrange, hconj, hg0⟩ :=
    exists_langSetup_conj_of_inndiag_twE6_phi hp hf hK' σ hσ' Nat.prime_three hpℓ hp₀ hp₀ℓ hq₀
      monomialToralAt_E6_three (twistedE6InndiagConj K σ h) (h : ModGL TwistTag.E6.tag K) h.2
      (twistedE6InndiagConj_apply h) hh3' hh1'
  have hker := twE6MatFixDim_eq_of_conj σ h S.D.g0 a hg0
  have hk : (kernelRoots (rootCharHom a)).ncard = 22 ∨
      (kernelRoots (rootCharHom a)).ncard = 30 := by
    omega
  have hL3 : ((3 : ℕ) : AlgebraicClosure K) ≠ 0 :=
    natCast_ne_zero_algebraicClosure_of_ne hp Nat.prime_three hK' hpℓ
  have hTame := langSetup_hTame_of_prime S Nat.prime_three hL3 (fun h => absurd h (by decide)) hT
    hap h1
  rw [← fixSubgroup_eq_fixedPoints] at hJ
  obtain ⟨i, hQS, hi⟩ := components_of_langSetup S Nat.prime_three ι hinj hrange
    (twistedE6InndiagConj K σ h) hconj hT hap h1 hTame hJ
  have h3q' : 3 ∣ S.D.q + 1 := by rw [hDq, ← hqf]; exact h3q
  have hFr' : ∀ c, Fr c = c ^ S.D.q := fun c => by rw [hDq]; exact hFr c
  haveI : CharP (AlgebraicClosure K) (ringChar K) :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective (ringChar K)
  have hL2 : ringChar (AlgebraicClosure K) = 2 := by
    rw [ringChar.eq (AlgebraicClosure K) (ringChar K), hK2]
  have hSq : S.D.q = q := by rw [hDq, ← hqf]
  have hSq2 : S.D.q ≠ 2 := fun h' => hq2ne (hSq ▸ h')
  have hSq8 : S.D.q ≠ 8 := fun h' => hq8 (hSq ▸ h')
  obtain ⟨d, ed, hd3, hexc, hcov⟩ := exists_coverIndex_of_conn_class S hFr' hΦ hL3 hL2 hT hap
    h3q' hSq2 hSq8 hk i hQS
  exact cover_shape_of_map_injective ι hinj (by rw [hi]; exact ⟨d, ed, hd3, hexc, hcov⟩)

end Dim

section D5

theorem exists_coverIndex_of_pominus {G : Type} [Group G] {n r e : ℕ}
    (h : LieModel G .POmegaMinus n r e) (hr3 : r ≠ 3) :
    ∃ (d : TauCeti.ValidLieTypeIndex),
      Nonempty (G ≃* (TauCeti.CFSGIndex.lie d).Group) ∧
        3 ≠ d.1.characteristic ∧ ¬ AGLEmbeddingD2.IsD2SeitzException 3 d.1 ∧
          (QuasiHigh.CoverIndex 3 d.1 → ¬ ExcIndex 3 d.1 ∧ ¬ IsLThreeFour G) := by
  have hadm := h.admissible
  have hn4 : 4 ≤ n := hadm.2.2
  have hp : r.Prime := hadm.1
  have hf : 0 < e := hadm.2.1
  rcases h with ⟨-, hmod⟩ | ⟨hn0, ht, -⟩ | ⟨hn0, ht, -⟩ | ⟨hn0, ht, -⟩
  · obtain ⟨-, K, _, _, hK, b, c, hirr, ⟨eG⟩⟩ := hmod
    haveI : Fintype K := Fintype.ofFinite K
    have hring : ringChar K = r :=
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ringChar_eq_of_natCard_eq_pow hp hK hf
    obtain ⟨q, hv, hqp, ⟨eq⟩⟩ := exists_twistedD_of_statedProj_minus (K := K) n hn4 hirr
    refine ⟨⟨LieTypeIndex.twistedD n q, hv⟩, ⟨eG.trans eq⟩, ?_, ?_, ?_⟩
    · simp only [LieTypeIndex.characteristic_twistedD]
      rw [hqp, hring]
      exact fun h => hr3 h.symm
    · simp [CFSG.AGLEmbeddingD2.IsD2SeitzException]
    · intro hc
      exact absurd hc (by simp [QuasiHigh.CoverIndex])
  all_goals simp [chevalleyExceptionalTags, reeTitsTags] at ht

theorem twE6CoverShape_of_d5
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {q : ℕ}
    {E : Subgroup (MulAut (twistedE6RootGroup K σ))} (hE : TwE6Cube K σ q E)
    (h : twistedE6InndiagGL K σ) (hh1 : h ≠ 1) (hh3 : h ^ 3 = 1)
    (hdim : twE6MatFixDim K σ h = 46)
    {J : Subgroup (twistedE6RootGroup K σ)}
    (hJ : CFSG.Open.IsComponentOf J
      (fixedPoints (Subgroup.zpowers (twistedE6InndiagConj K σ h)))) :
    ∃ (d : TauCeti.ValidLieTypeIndex)
        (_ : (J ⧸ Subgroup.center J) ≃* (TauCeti.CFSGIndex.lie d).Group),
      3 ≠ d.1.characteristic ∧ ¬ AGLEmbeddingD2.IsD2SeitzException 3 d.1 ∧
        (QuasiHigh.CoverIndex 3 d.1 →
          ¬ ExcIndex 3 d.1 ∧ ¬ IsLThreeFour (J ⧸ Subgroup.center J)) := by
  have hq2 : 2 ≤ q := by
    have := Nat.le_of_dvd (by omega) hE.three_dvd
    omega
  obtain ⟨r, e, hrK, hmodel⟩ := strongModel_of_d5_component K σ q hE.char_ne_three hE.frob
    hE.card_field hq2 hE.three_dvd h hh1 hh3 hdim hJ
  obtain ⟨d, ⟨ed⟩, hd3, hex, hcov⟩ := exists_coverIndex_of_pominus hmodel.1
    (by rw [← hrK]; exact hE.char_ne_three)
  exact ⟨d, ed, hd3, hex, hcov⟩

end D5

section D4

theorem exists_coverIndex_of_inner_d4
    {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup .E6 L p₀)
    {l f : ℕ} (hl : l.Prime) (hf : 0 < f) (hq : S.D.q = l ^ f) (hl3 : l ≠ 3)
    (h3 : ((3 : ℕ) : L) ≠ 0)
    {a : Fin Tag.E6.rank → Lˣ} (hT : rootDiagUnit .E6 a ∈ S.D.torus) (hap : ∀ i, a i ^ 3 = 1)
    (i : KernelComponent (rootCharHom a))
    (hr : compRank (componentRoots (rootCharHom a) i) = 4)
    (hc : (componentRoots (rootCharHom a) i).ncard = 24)
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i)
    (hin : twistInner (componentRoots (rootCharHom a) i)
      (S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))) :
    ∃ (d : TauCeti.ValidLieTypeIndex)
        (_ : (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
          Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) ≃*
          (TauCeti.CFSGIndex.lie d).Group),
      3 ≠ d.1.characteristic ∧ ¬ AGLEmbeddingD2.IsD2SeitzException 3 d.1 ∧
        (QuasiHigh.CoverIndex 3 d.1 →
          ¬ ExcIndex 3 d.1 ∧
            ¬ IsLThreeFour (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
              Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))) := by
  classical
  obtain ⟨_, w, m0, m1, m2, m3, m4, m5, -, hsum, -, hcl⟩ := TwE6UniqAbs.kac_class_data h3 hap
  obtain ⟨x, hx, hroots, hncard, -, -⟩ := hcl i
  have hD4 := d4t2in_cmpF_eq_sD4 hsum hx (hncard.symm.trans hc)
  have hfam : componentRoots (rootCharHom a) i =
      rootsOfFam (fun y => w⁻¹ • kacE6.extRoot y) (Set.range TwE6InnerAbs.lD4) := by
    rw [hroots, hD4, ← TwE6InnerAbs.range_lD4]
    exact TwE6InnerAbs.image_rootsOf_eq_rootsOfFam kacE6 w⁻¹ _
  have hfin : (componentRoots (rootCharHom a) i).Finite :=
    (CFSG.Blueprint.Chevalley.finite_setOf_isRoot Tag.E6).subset fun γ hγ => hγ.1.1
  have hs1 : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1 :=
    componentOrbitLength_eq_one hfin hρ
  have hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]) := by
    rw [hs1, Function.iterate_one]
    exact hin
  obtain ⟨hmodel, -⟩ := d4t2in_dModel_center S (Or.inr (Or.inl rfl)) hT i hinner
    (n := 4) le_rfl (fun y => w⁻¹ • kacE6.extRoot y)
    (fun y => IsRoot.smul (kacE6.isRoot_extRoot y) w⁻¹) TwE6InnerAbs.lD4 hfam
    (fun c d hcd h1 h2 => by
      show iform (w⁻¹ • kacE6.extRoot (TwE6InnerAbs.lD4 c))
        (w⁻¹ • kacE6.extRoot (TwE6InnerAbs.lD4 d)) = 0
      rw [iform_smul, kacE6_extRoot]
      exact TwE6InnerAbs.d4_hgram c d hcd h1 h2)
    (fun {F} _ c d h => TwE6InnerAbs.d4_frames w⁻¹ c d h) hl hf hq
  rw [hs1, Nat.mul_one] at hmodel
  obtain ⟨q', hv, hqp, -, ⟨e⟩⟩ := KSExact.exists_D_of_statedClassicalModel_POmegaPlus hmodel
  refine ⟨⟨.D 4 q', hv⟩, e, ?_, ?_, ?_⟩
  · show 3 ≠ (TauCeti.LieTypeIndex.D 4 q').characteristic
    rw [TauCeti.LieTypeIndex.characteristic_D, hqp]
    exact fun h => hl3 h.symm
  · simp [AGLEmbeddingD2.IsD2SeitzException]
  · intro hc
    exact absurd hc (by simp [QuasiHigh.CoverIndex])

theorem exists_coverIndex_of_outer_d4
    {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup .E6 L p₀)
    (hS : ∃ (t : TwistTag) (h : t.tag = .E6) (Fr : L →+* L), (∀ c, Fr c = c ^ S.D.q) ∧
      ∀ g, S.D.Φ g = diagramAt .E6 L t h * Units.map (entrywiseHom Fr) g *
        (diagramAt .E6 L t h)⁻¹)
    {l f : ℕ} (hl : l.Prime) (hf : 0 < f) (hq : S.D.q = l ^ f) (hl3 : l ≠ 3)
    (h3 : ((3 : ℕ) : L) ≠ 0) (h3q : 3 ∣ l ^ f + 1)
    {a : Fin Tag.E6.rank → Lˣ} (hT : rootDiagUnit .E6 a ∈ S.D.torus) (hap : ∀ i, a i ^ 3 = 1)
    (i : KernelComponent (rootCharHom a))
    (hall : (kernelRoots (rootCharHom a)).ncard = 24)
    (hr : compRank (componentRoots (rootCharHom a) i) = 4)
    (hc : (componentRoots (rootCharHom a) i).ncard = 24)
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i)
    (hnin : ¬ twistInner (componentRoots (rootCharHom a) i)
      (S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))) :
    ∃ (d : TauCeti.ValidLieTypeIndex)
        (_ : (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
          Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) ≃*
          (TauCeti.CFSGIndex.lie d).Group),
      3 ≠ d.1.characteristic ∧ ¬ AGLEmbeddingD2.IsD2SeitzException 3 d.1 ∧
        (QuasiHigh.CoverIndex 3 d.1 →
          ¬ ExcIndex 3 d.1 ∧
            ¬ IsLThreeFour (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
              Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))) := by
  haveI : Fact l.Prime := ⟨hl⟩
  haveI : CharP L l := by
    rw [CharP.charP_iff_prime_eq_zero hl]
    have h := S.hqpow.2
    rw [hq, Nat.cast_pow] at h
    exact (pow_eq_zero_iff hf.ne').1 h
  have hTp : rootDiagUnit Tag.E6 a ^ 3 = 1 := by
    have h1 : rootDiagUnit Tag.E6 (a ^ 3) = rootDiagUnit Tag.E6 a ^ 3 :=
      (rootDiagUnitHom Tag.E6 L).map_pow a 3
    have h2 : a ^ 3 = 1 := funext fun j => by rw [Pi.pow_apply, hap j, Pi.one_apply]
    rw [← h1, h2, CFSG.LieType.Chevalley.rootDiagUnit_one]
  obtain ⟨v, hv, -⟩ := S.d4_pinnedT_of_prime Nat.prime_three h3 facts_E6 kacCount_E6_four
    (by decide) (by decide)
    (fun y hy => far_d4_E6 y fun z hz => by
      have h := hy z hz
      rwa [KacData.Adj, extRoot_eq_extRootOf] at h)
    ⟨none, by decide⟩ (lt_of_eq_of_lt kacCount_far_E6 (by decide)) hT hTp i hr hc
  have hfin : (kernelRoots (rootCharHom a)).Finite :=
    (finite_setOf_isRoot _).subset fun γ hγ => hγ.1
  have hle : componentRoots (rootCharHom a) i ⊆ kernelRoots (rootCharHom a) := fun γ hγ => hγ.1
  have hsub : kernelRoots (rootCharHom a) ⊆ componentRoots (rootCharHom a) i :=
    (Set.eq_of_subset_of_ncard_le hle (hall.trans hc.symm).le hfin).ge
  obtain ⟨⟨e⟩, hZ⟩ := d4t2out_rationalComponent_equiv S hS hf hq h3q hT hap i v hv hsub hρ hnin
  refine ⟨⟨.trialityD4 ⟨l, f, hl, hf⟩, TauCeti.LieTypeIndex.valid_trialityD4 _⟩,
    (QuotientGroup.quotientMulEquivOfEq hZ).trans (QuotientGroup.quotientBot.trans e), ?_, ?_, ?_⟩
  · simp only [TauCeti.LieTypeIndex.characteristic_trialityD4]
    exact fun h => hl3 h.symm
  · simp [CFSG.AGLEmbeddingD2.IsD2SeitzException]
  · intro hc
    exact absurd hc (by simp [QuasiHigh.CoverIndex])

theorem twE6CoverShape_of_d4
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {q : ℕ}
    {E : Subgroup (MulAut (twistedE6RootGroup K σ))} (hE : TwE6Cube K σ q E)
    {f : MulAut (twistedE6RootGroup K σ)} (hf : f ∈ E) (hf1 : f ≠ 1)
    (hd : TwE6LineDim K σ f 30)
    {J : Subgroup (twistedE6RootGroup K σ)}
    (hJ : CFSG.Open.IsComponentOf J (fixedPoints (Subgroup.zpowers f))) :
    ∃ (d : TauCeti.ValidLieTypeIndex)
        (_ : (J ⧸ Subgroup.center J) ≃* (TauCeti.CFSGIndex.lie d).Group),
      3 ≠ d.1.characteristic ∧ ¬ AGLEmbeddingD2.IsD2SeitzException 3 d.1 ∧
        (QuasiHigh.CoverIndex 3 d.1 →
          ¬ ExcIndex 3 d.1 ∧ ¬ IsLThreeFour (J ⧸ Subgroup.center J)) := by
  classical
  obtain ⟨h, hh, -, -, hdim, ⟨D⟩⟩ := exists_twE6LineLang_of_cube hE hf hf1 hd
  subst hh
  have hall : (kernelRoots (rootCharHom D.a)).ncard = 24 := by
    have := D.hker
    omega
  have hq3 : 3 ∣ ringChar K ^ D.e + 1 := D.hqe ▸ hE.three_dvd
  obtain ⟨i, -, hi⟩ := D.exists_rationalComponent hJ
  obtain ⟨hr, hc⟩ := d4t2_class_of_card D.hL3 D.hap hall i
  have hker := d4t2_class_eq_kernel D.hL3 D.hap hall i
  have hρ : ∀ γ ∈ componentRoots (rootCharHom D.a) i,
      D.S.ρ γ ∈ componentRoots (rootCharHom D.a) i := by
    intro γ hγ
    rw [hker] at hγ ⊢
    exact outer_rho_mem_kernelRoots D.S D.hT hγ
  have hR : ∃ (d : TauCeti.ValidLieTypeIndex)
      (_ : (↥(rationalComponent D.S.ρ D.S.Γ (rootCharHom D.a) i) ⧸
        Subgroup.center ↥(rationalComponent D.S.ρ D.S.Γ (rootCharHom D.a) i)) ≃*
        (TauCeti.CFSGIndex.lie d).Group),
      3 ≠ d.1.characteristic ∧ ¬ AGLEmbeddingD2.IsD2SeitzException 3 d.1 ∧
        (QuasiHigh.CoverIndex 3 d.1 →
          ¬ ExcIndex 3 d.1 ∧
            ¬ IsLThreeFour (↥(rationalComponent D.S.ρ D.S.Γ (rootCharHom D.a) i) ⧸
              Subgroup.center ↥(rationalComponent D.S.ρ D.S.Γ (rootCharHom D.a) i))) := by
    by_cases hin : twistInner (componentRoots (rootCharHom D.a) i)
        (D.S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))
    · exact exists_coverIndex_of_inner_d4 D.S D.hℓ D.he D.hSq hE.char_ne_three D.hL3 D.hT
        D.hap i hr hc hρ hin
    · exact exists_coverIndex_of_outer_d4 D.S D.hS D.hℓ D.he D.hSq hE.char_ne_three D.hL3
        hq3 D.hT D.hap i hall hr hc hρ hin
  exact cover_shape_of_map_injective D.ι D.hinj (hi ▸ hR)

end D4

section A2Out

theorem exists_coverIndex_of_a2out
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {q : ℕ}
    {h : twistedE6InndiagGL K σ} (hdim : twE6MatFixDim K σ h = 24)
    (hq3 : 3 ∣ q + 1) (hq2 : q ≠ 2) (hK3 : ringChar K ≠ 3) (hK2 : ringChar K = 2)
    (hout : twistedE6InndiagConj K σ h ∉ twistedE6Inn K σ)
    (D : TwE6LineLang K σ q h) (i : KernelComponent (rootCharHom D.a)) :
    ∃ (d : TauCeti.ValidLieTypeIndex)
        (_ : (↥(rationalComponent D.S.ρ D.S.Γ (rootCharHom D.a) i) ⧸
          Subgroup.center ↥(rationalComponent D.S.ρ D.S.Γ (rootCharHom D.a) i)) ≃*
          (TauCeti.CFSGIndex.lie d).Group),
      3 ≠ d.1.characteristic ∧ ¬ AGLEmbeddingD2.IsD2SeitzException 3 d.1 ∧
        (QuasiHigh.CoverIndex 3 d.1 →
          ¬ ExcIndex 3 d.1 ∧
            ¬ IsLThreeFour (↥(rationalComponent D.S.ρ D.S.Γ (rootCharHom D.a) i) ⧸
              Subgroup.center ↥(rationalComponent D.S.ρ D.S.Γ (rootCharHom D.a) i))) := by
  classical
  obtain ⟨-, -, hmodel⟩ := D.rationalComponent_a2out hdim hq3 hq2 hout i
  obtain ⟨q', hv, hq'p, hq'f, ⟨e⟩⟩ :=
    KSExact.exists_twistedA_of_statedClassicalModel_PSU (m := 2) hmodel
  have hde1 : D.e ≠ 1 := by
    intro he1
    apply hq2
    rw [D.hqe, hK2, he1, pow_one]
  have hq'1 : ¬ IsTwoPow q' 1 := by
    rintro ⟨-, h1⟩
    rw [hq'f] at h1
    omega
  have hq'3 : ¬ IsTwoPow q' 3 := by
    rintro ⟨-, h3⟩
    rw [hq'f] at h3
    exact hde1 (by omega)
  have hmodel' : StatedClassicalModel (↥(rationalComponent D.S.ρ D.S.Γ (rootCharHom D.a) i) ⧸
      Subgroup.center ↥(rationalComponent D.S.ρ D.S.Γ (rootCharHom D.a) i)) .PSU 3 2
      (D.e * 3) := hK2 ▸ hmodel
  refine ⟨⟨.twistedA 2 q', hv⟩, e, ?_, ?_, ?_⟩
  · change 3 ≠ (TauCeti.LieTypeIndex.twistedA 2 q').characteristic
    rw [TauCeti.LieTypeIndex.characteristic_twistedA, hq'p]
    exact fun h => hK3 h.symm
  · simp [CFSG.AGLEmbeddingD2.IsD2SeitzException]
  · intro _
    exact ⟨not_excIndex_twistedA hq'1 hq'3, not_isLThreeFour_of_psu_stated hmodel'⟩

theorem twE6CoverShape_of_a2out
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {q : ℕ}
    {E : Subgroup (MulAut (twistedE6RootGroup K σ))} (hE : TwE6Cube K σ q E)
    (hK2 : ringChar K = 2) {f : MulAut (twistedE6RootGroup K σ)} (hf : f ∈ E)
    (hf1 : f ≠ 1) (hfo : f ∉ twistedE6Inn K σ) (hd : TwE6LineDim K σ f 24)
    {J : Subgroup (twistedE6RootGroup K σ)}
    (hJ : CFSG.Open.IsComponentOf J (fixedPoints (Subgroup.zpowers f))) :
    ∃ (d : TauCeti.ValidLieTypeIndex)
        (_ : (J ⧸ Subgroup.center J) ≃* (TauCeti.CFSGIndex.lie d).Group),
      3 ≠ d.1.characteristic ∧ ¬ AGLEmbeddingD2.IsD2SeitzException 3 d.1 ∧
        (QuasiHigh.CoverIndex 3 d.1 →
          ¬ ExcIndex 3 d.1 ∧ ¬ IsLThreeFour (J ⧸ Subgroup.center J)) := by
  classical
  obtain ⟨h, rfl, -, -, hdim, ⟨D⟩⟩ := exists_twE6LineLang_of_cube hE hf hf1 hd
  obtain ⟨i, -, hi⟩ := D.exists_rationalComponent hJ
  have hR := exists_coverIndex_of_a2out hdim hE.three_dvd hE.ne_two hE.char_ne_three hK2
    hfo D i
  exact cover_shape_of_map_injective D.ι D.hinj (hi ▸ hR)

end A2Out

section Main

theorem twE6ComponentCoverShape_of_even
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {q : ℕ}
    {E : Subgroup (MulAut (twistedE6RootGroup K σ))} (hE : TwE6Cube K σ q E)
    (hK2 : ringChar K = 2) (hq8 : q ≠ 8) {f : MulAut (twistedE6RootGroup K σ)} (hf : f ∈ E)
    (hf1 : f ≠ 1)
    (hty : ∀ s : twistedE6RootGroup K σ, f = MulAut.conj s → twE6FixDim K σ s ≠ 24)
    {J : Subgroup (twistedE6RootGroup K σ)}
    (hJ : CFSG.Open.IsComponentOf J (fixedPoints (Subgroup.zpowers f))) :
    (∃ (d : TauCeti.ValidLieTypeIndex)
        (_ : (J ⧸ Subgroup.center J) ≃* (TauCeti.CFSGIndex.lie d).Group),
        3 ≠ d.1.characteristic ∧ ¬ AGLEmbeddingD2.IsD2SeitzException 3 d.1 ∧
          (QuasiHigh.CoverIndex 3 d.1 →
            ¬ ExcIndex 3 d.1 ∧ ¬ IsLThreeFour (J ⧸ Subgroup.center J))) ∨
      NoPlane3 (J ⧸ Subgroup.center J) ∨ ¬ 3 ∣ Nat.card J := by
  classical
  have hq2 : 2 ≤ q := by
    have := Nat.le_of_dvd (by omega) hE.three_dvd
    omega
  obtain ⟨h, hh, hh1, hdim⟩ := twE6MatFixDim_mem_of_mem twE6Order3Dim_holds K σ q
    hE.char_ne_three hE.frob hE.card_field hE.three_dvd hE.ne_two hE.elemAbelian
    hE.le_inndiag hf hf1
  have hLD : ∀ d, twE6MatFixDim K σ h = d → TwE6LineDim K σ f d := fun d hd => ⟨h, hh, hd⟩
  have hf3 : f ^ 3 = 1 := hE.elemAbelian.2 f hf
  have hh3 : h ^ 3 = 1 := by
    apply twE6_conj_injective K σ q hE.frob hE.card_field hq2
    rw [map_pow, hh, map_one]
    exact hf3
  by_cases h3 : 3 ∣ Nat.card (J ⧸ Subgroup.center J)
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hdim
    rcases hdim with h24 | h28 | h30 | h36 | h46
    · have hout : f ∉ twistedE6Inn K σ := by
        rintro ⟨s, hs⟩
        have hfd := twE6MatFixDim_of_inner K σ q hE.frob hE.card_field hq2 s h
          (hh.trans hs.symm)
        exact hty s hs.symm (hfd ▸ h24)
      exact Or.inl (twE6CoverShape_of_a2out hE hK2 hf hf1 hout (hLD 24 h24) hJ)
    · exact Or.inl (twE6CoverShape_of_dim K σ q hE.char_ne_three hK2 hE.frob hE.card_field
        hq2 hE.three_dvd hE.ne_two hq8 h hh1 hh3 (Or.inl h28) (hh ▸ hJ))
    · exact Or.inl (twE6CoverShape_of_d4 hE hf hf1 (hLD 30 h30) hJ)
    · exact Or.inl (twE6CoverShape_of_dim K σ q hE.char_ne_three hK2 hE.frob hE.card_field
        hq2 hE.three_dvd hE.ne_two hq8 h hh1 hh3 (Or.inr h36) (hh ▸ hJ))
    · exact Or.inl (twE6CoverShape_of_d5 hE h hh1 hh3 h46 (hh ▸ hJ))
  · exact Or.inr (Or.inr (not_three_dvd_card_of_perfect hJ.2.2.1 h3))

end Main

end CFSG.LieType.SeitzGeneration.CubeCoverE6
