module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanP1ThreeLieDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanP1ThreeLieWeakCore
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCharPGenExc

public section

namespace CFSG.AGLEmbedding.P1Lie

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Universal CFSG.ClassicalInvolution.ModelFacts

private def HeightData {r : ℕ} (R : (Fin r → ℤ) → Prop) : Prop :=
  ∃ M k : ℤ, 2 ≤ k ∧ M < 2 * k ∧ (∀ ε, R ε → ht ε ≤ M) ∧
    ∃ γ₁, R γ₁ ∧ ∃ γ₂, R γ₂ ∧ ∃ γ₃, R γ₃ ∧ γ₁ ≠ γ₂ ∧ γ₁ ≠ γ₃ ∧ γ₂ ≠ γ₃ ∧
      k ≤ ht γ₁ ∧ k ≤ ht γ₂ ∧ k ≤ ht γ₃

private theorem HeightData.congr {r : ℕ} {R R' : (Fin r → ℤ) → Prop} (h : HeightData R)
    (e : ∀ ε, R' ε ↔ R ε) : HeightData R' := by
  obtain ⟨M, k, hk, hMk, hM, γ₁, h₁, γ₂, h₂, γ₃, h₃, h12, h13, h23, k1, k2, k3⟩ := h
  exact ⟨M, k, hk, hMk, fun ε hε => hM ε ((e ε).1 hε), γ₁, (e γ₁).2 h₁, γ₂, (e γ₂).2 h₂, γ₃,
    (e γ₃).2 h₃, h12, h13, h23, k1, k2, k3⟩

private theorem g2_heights : (∀ v ∈ rootFinset .G2, ht v ≤ 5) ∧
    3 ≤ ((rootFinset .G2).filter fun v => 3 ≤ ht v).card := by
  decide +kernel

private theorem f4_heights : (∀ v ∈ rootFinset .F4, ht v ≤ 11) ∧
    3 ≤ ((rootFinset .F4).filter fun v => 6 ≤ ht v).card := by
  decide +kernel

private theorem e6_heights : (∀ v ∈ rootFinset .E6, ht v ≤ 11) ∧
    3 ≤ ((rootFinset .E6).filter fun v => 6 ≤ ht v).card := by
  decide +kernel

private theorem e7_heights : (∀ v ∈ rootFinset .E7, ht v ≤ 17) ∧
    3 ≤ ((rootFinset .E7).filter fun v => 9 ≤ ht v).card := by
  decide +kernel

private theorem e8_heights : (∀ v ∈ rootFinset .E8, ht v ≤ 29) ∧
    3 ≤ ((rootFinset .E8).filter fun v => 15 ≤ ht v).card := by
  decide +kernel

private theorem exists_pGroup_weakCore_of_core_eq_top {K X : Type} [Group K] [Finite K] [Group X]
    [Finite X] {p : ℕ} (hp : p.Prime) {D : UniversalRootDatum K} {nn : Fin D.rank → K}
    {H : Fin D.rank → Subgroup K} (hext : SteinbergExtras D nn H)
    (hX : ∀ γ ∈ D.roots, IsPGroup p (D.rootGroup γ))
    (hcen : ∀ z ∈ Subgroup.center K, z ^ p = 1 → z = 1) (ψ : K →* X)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center K)
    (hcore : GLBWeakCore p (posUnipotent D) = ⊤) :
    ∃ P : Subgroup X, IsPGroup p P ∧ GLBWeakCore p P = ⊤ := by
  have hU : IsPGroup p (posUnipotent D) := isPGroup_iSup_pos hext hX
  have hinj : ∀ x ∈ posUnipotent D, ψ x = 1 → x = 1 := by
    intro x hx hx1
    obtain ⟨k, hk⟩ := hU ⟨x, hx⟩
    exact CharPGen.eq_one_of_mem_center_of_pow_prime_pow hcen (hker (MonoidHom.mem_ker.2 hx1))
      (congrArg Subtype.val hk)
  exact ⟨(posUnipotent D).map ψ, hU.map ψ, weakCore_map_eq_top hp ψ hψ hinj hcore⟩

section Tags


private theorem heightData_of_rootFinset {τ : Tag} {M k : ℤ} (hk : 2 ≤ k) (hMk : M < 2 * k)
    (h : (∀ v ∈ rootFinset τ, ht v ≤ M) ∧
      3 ≤ ((rootFinset τ).filter fun v => k ≤ ht v).card) : HeightData (IsRoot τ) := by
  refine ⟨M, k, hk, hMk, fun ε hε => h.1 ε (mem_rootFinset.2 hε), ?_⟩
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := Finset.two_lt_card_iff.1 h.2
  simp only [Finset.mem_filter] at ha hb hc
  exact ⟨a, mem_rootFinset.1 ha.1, b, mem_rootFinset.1 hb.1, c, mem_rootFinset.1 hc.1, hab, hac,
    hbc, ha.2, hb.2, hc.2⟩

end Tags

section Certified


private theorem heightData_modelUniv {t : StatedLieTag}
    (htag : t ∈ chevalleyExceptionalTags) (p f : ℕ) (hp : p.Prime) :
    HeightData (fun ε => ε ∈ (modelUniv t 0 p f hp).D.roots) := by
  have : Fact p.Prime := ⟨hp⟩
  simp only [chevalleyExceptionalTags, Finset.mem_insert, Finset.mem_singleton] at htag
  rcases htag with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (heightData_of_rootFinset (M := 5) (k := 3) (by norm_num) (by norm_num)
      g2_heights).congr fun ε => Adjoint.mem_adjDatum_roots
  · exact (heightData_of_rootFinset (M := 11) (k := 6) (by norm_num) (by norm_num)
      f4_heights).congr fun ε => Adjoint.mem_adjDatum_roots
  · exact (heightData_of_rootFinset (M := 11) (k := 6) (by norm_num) (by norm_num)
      e6_heights).congr fun ε => Minuscule.MinData.Valid.mem_minDatum_roots _ _ _
  · exact (heightData_of_rootFinset (M := 17) (k := 9) (by norm_num) (by norm_num)
      e7_heights).congr fun ε => Minuscule.MinData.Valid.mem_minDatum_roots _ _ _
  · exact (heightData_of_rootFinset (M := 29) (k := 15) (by norm_num) (by norm_num)
      e8_heights).congr fun ε => Adjoint.mem_adjDatum_roots
  · exact (heightData_of_rootFinset (M := 11) (k := 6) (by norm_num) (by norm_num)
      f4_heights).congr fun ε =>
      Set.ext_iff.1 (TwistedE6.twistedDatum_roots (k := GaloisField p (2 * f))
        (θ := Exceptional.frobQ p f)) ε
  · exact (heightData_of_rootFinset (M := 5) (k := 3) (by norm_num) (by norm_num)
      g2_heights).congr fun ε =>
      Set.ext_iff.1 (TwistedD4.twistedDatum_roots
        (iterateFrobenius (GaloisField p (3 * f)) p f)) ε

theorem exists_pGroup_weakCore_of_chevalleyExceptionalModel {t : StatedLieTag}
    (htag : t ∈ chevalleyExceptionalTags) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible t 0 p f) {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (hmodel : ChevalleyExceptionalModel X t p f) :
    ∃ P : Subgroup X, IsPGroup p P ∧ GLBWeakCore p P = ⊤ := by
  have hfund : CFSG.ClassicalInvolution.Generic.IsFundTag t := by
    simp only [chevalleyExceptionalTags, Finset.mem_insert, Finset.mem_singleton] at htag
    rcases htag with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> trivial
  have h1 : ¬ (t = .PSL ∧ 0 = 2) := fun h => absurd h.2 (by decide)
  have h2 : ¬ (t = .PSU ∧ 0 = 3) := fun h => absurd h.2 (by decide)
  have h3 : ¬ (t = .PSU ∧ ¬ Even 0) := fun h => by
    obtain ⟨rfl, -⟩ := h
    simp [chevalleyExceptionalTags] at htag
  have hX : LieModel X t 0 p f := Or.inr (Or.inl ⟨rfl, htag, hmodel⟩)
  have : Finite (modelUniv t 0 p f hp).K := finite_modelUniv hp2 hp hfund hadm
  obtain ⟨ψ, hψs, hψk⟩ := CFSG.ClassicalInvolution.Upgrade.lieModelCentralCover t 0 p f hp hp2
    hfund hadm X hX
  obtain ⟨nn, H, hct, hext⟩ := hasBruhatDatum t 0 p f hp hfund hadm
  have hXp := CFSG.LieType.HighestRoot.isPGroup_rootGroup_modelUniv t 0 p f hp hfund hadm
  obtain ⟨M, k, hk, hMk, hM, hγ⟩ := heightData_modelUniv htag p f hp
  have hcore := weakCore_posUnipotent_eq_top_of_heights hct hext hp
    (two_le_rank t 0 p f hp hfund hadm h1 h2) hXp
    (CFSG.LieType.HighestRoot.divisible_modelUniv t 0 p f hp hfund hadm h3) hk hMk hM hγ
  exact exists_pGroup_weakCore_of_core_eq_top hp hext hXp
    (CFSG.ComponentClassification.RankTwoOddLie.modelCenterPPrime t 0 p f hp hp2 hfund hadm)
    ψ hψs hψk hcore

end Certified

end CFSG.AGLEmbedding.P1Lie

namespace CFSG.AGLEmbedding

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.Assembly.LowTwoRank CFSG.AGLEmbedding.P1Lie

section Certified


theorem weakCharPGenAt_exceptional : WeakCharPGenAt IsExceptionalIndex := by
  intro K _ _ _ _ d hd ⟨e⟩ p hp hp2 hchar hrank T
  suffices h : ∃ P : Subgroup K, IsPGroup p P ∧ GLBWeakCore p P = ⊤ by
    obtain ⟨P, hP, hcore⟩ := h
    exact weakCore_eq_top_of_pGroup hp hP hcore T
  obtain ⟨⟨d, hv⟩, rfl⟩ : ∃ d' : {d : TauCeti.LieTypeIndex // d.Valid}, d' = d := ⟨d, rfl⟩
  rcases hd with ⟨q, hd⟩ | ⟨q, hd⟩ | ⟨q, hd⟩ | ⟨q, hd⟩ | ⟨q, hd⟩ | ⟨q, hd⟩ | ⟨q, hd⟩ <;>
    simp only at hd hchar <;> subst hd <;> (have hpq : p = q.p := by simpa using hchar) <;>
    subst hpq
  · have h3 : 3 ≤ q.p ^ q.exponent := by
      have h := ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
      simpa only [TauCeti.LieTypeIndex.inStandardRange_iff, TauCeti.PrimePower.card_def] using h
    have hadm : StatedLieAdmissible .G2 0 q.p q.exponent := ⟨q.prime_p, q.exponent_pos, rfl, h3⟩
    exact exists_pGroup_weakCore_of_chevalleyExceptionalModel (t := .G2) (by decide) q.prime_p
      hp2 hadm ⟨hadm, CFSG.TauCetiBridge.untwistedModel_of_bridge
        CFSG.TauCetiBridge.chevalleyBridges.g2 q hv hp2 e⟩
  · have hadm : StatedLieAdmissible .F4 0 q.p q.exponent := ⟨q.prime_p, q.exponent_pos, rfl⟩
    exact exists_pGroup_weakCore_of_chevalleyExceptionalModel (t := .F4) (by decide) q.prime_p
      hp2 hadm ⟨hadm, CFSG.TauCetiBridge.untwistedModel_of_bridge
        CFSG.TauCetiBridge.chevalleyBridges.f4 q hv hp2 e⟩
  · have hadm : StatedLieAdmissible .E6 0 q.p q.exponent := ⟨q.prime_p, q.exponent_pos, rfl⟩
    exact exists_pGroup_weakCore_of_chevalleyExceptionalModel (t := .E6) (by decide) q.prime_p
      hp2 hadm ⟨hadm, CFSG.TauCetiBridge.untwistedModel_of_bridge
        CFSG.TauCetiBridge.chevalleyBridges.e6 q hv hp2 e⟩
  · have hadm : StatedLieAdmissible .E7 0 q.p q.exponent := ⟨q.prime_p, q.exponent_pos, rfl⟩
    exact exists_pGroup_weakCore_of_chevalleyExceptionalModel (t := .E7) (by decide) q.prime_p
      hp2 hadm ⟨hadm, CFSG.TauCetiBridge.untwistedModel_of_bridge
        CFSG.TauCetiBridge.chevalleyBridges.e7 q hv hp2 e⟩
  · have hadm : StatedLieAdmissible .E8 0 q.p q.exponent := ⟨q.prime_p, q.exponent_pos, rfl⟩
    exact exists_pGroup_weakCore_of_chevalleyExceptionalModel (t := .E8) (by decide) q.prime_p
      hp2 hadm ⟨hadm, CFSG.TauCetiBridge.untwistedModel_of_bridge
        CFSG.TauCetiBridge.chevalleyBridges.e8 q hv hp2 e⟩
  · have hadm : StatedLieAdmissible .twistedE6 0 q.p q.exponent :=
      ⟨q.prime_p, q.exponent_pos, rfl⟩
    exact exists_pGroup_weakCore_of_chevalleyExceptionalModel (t := .twistedE6) (by decide)
      q.prime_p hp2 hadm ⟨hadm, CFSG.TauCetiBridge.twistedModel_of_bridge
        CFSG.TauCetiBridge.chevalleyBridges.twistedE6 q hv hp2 (by decide) e⟩
  · have hadm : StatedLieAdmissible .trialityD4 0 q.p q.exponent :=
      ⟨q.prime_p, q.exponent_pos, rfl⟩
    exact exists_pGroup_weakCore_of_chevalleyExceptionalModel (t := .trialityD4) (by decide)
      q.prime_p hp2 hadm ⟨hadm, CFSG.TauCetiBridge.twistedModel_of_bridge
        CFSG.TauCetiBridge.chevalleyBridges.trialityD4 q hv hp2 (by decide) e⟩

end Certified

end CFSG.AGLEmbedding
