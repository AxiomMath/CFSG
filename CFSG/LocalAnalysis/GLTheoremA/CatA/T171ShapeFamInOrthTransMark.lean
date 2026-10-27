module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172AGrp
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatTypeDet
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatEvenOuterOmega
public import CFSG.LocalAnalysis.StandardType.Marking
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerMoreCl
public import CFSG.Adapters.TauCetiLieModels
public import Certificates.Certificate113
public import Certificates.Certificate8064
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate8033
public import CFSG.Blueprint.LieModelAPI
public import CFSG.GH74.GLS.IVK.Proofs2.OddTools
public import CFSG.GH74.GLS.Stage2.Local.P34Main
public import CFSG.GH74.GLS.Stage2.Local.P34S5A
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CoatomAbs
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GenCell
public import CFSG.LargeExtraspecial.OfFStar
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevInnerCover
public import CFSG.Models.Transport

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Assembly CFSG.StandardType
open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10

private theorem pPrimeCore_le_center_of_nontrivial {Ω : Type} [Group Ω] [Finite Ω]
    {L : Subgroup Ω} {p : ℕ} (hq : CFSG.Open.IsQuasisimple ↥L)
    (hnt : Nontrivial (PSimple p L)) :
    GLAPPrimeCore p ↥L ≤ Subgroup.center ↥L := by
  haveI : Group.IsPerfect ↥L := ⟨hq.1⟩
  haveI : Nontrivial (PSimple p L) := hnt
  refine CFSG.LocalAnalysis.GLTheoremA.le_center_of_normal_of_isQuasisimple hq
    (GLAPPrimeCore.normal p ↥L) ?_
  intro htop
  have hsub : Subsingleton (PQuot p L) := by
    rw [PQuot, QuotientGroup.subsingleton_iff]
    exact htop
  haveI : Subsingleton (PQuot p L) := hsub
  have hsub2 : Subsingleton (PSimple p L) := by
    rw [PSimple, QuotientGroup.subsingleton_iff]
    refine top_unique ?_
    intro x _
    rw [Subgroup.mem_center_iff]
    intro y
    rw [Subsingleton.elim x y]
  exact not_subsingleton (PSimple p L) hsub2

theorem lieModel_of_catalogIs_D {S : Type} [Group S] {m n : ℕ}
    (hcat : catalogIs S (onLie fun i =>
      ∃ q : TauCeti.PrimePower, i = .D m q ∧ q.card = 2 ^ n)) :
    CFSG.Blueprint.LieModel S .POmegaPlus m 2 n := by
  obtain ⟨d, hv, ⟨q, rfl, hq⟩, ⟨e⟩⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.exists_lieIndex hcat
  have hLM := CFSG.Models.lieModel_D m q hv e
  have hp2 : q.p = 2 := by
    have hdiv : q.p ∣ 2 ^ n := by
      rw [← hq, TauCeti.PrimePower.card_def]
      exact dvd_pow_self q.p (Nat.ne_of_gt q.exponent_pos)
    have hd := (Nat.Prime.dvd_of_dvd_pow q.prime_p hdiv)
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h1
    · exact absurd h1 q.prime_p.ne_one
    · exact h1
  have hq' : q.p ^ q.exponent = 2 ^ n := by simpa using hq
  have hqn : q.exponent = n := by
    rw [hp2] at hq'
    exact Nat.pow_right_injective (le_refl 2) hq'
  rw [hp2, hqn] at hLM
  exact CFSG.Models.LieModel.toBlueprint (by simp [CFSG.Blueprint.classicalTags]) hLM

theorem lieModel_of_catalogIs_twistedD {S : Type} [Group S] {m n : ℕ}
    (hcat : catalogIs S (onLie fun i =>
      ∃ q : TauCeti.PrimePower, i = .twistedD m q ∧ q.card = 2 ^ n)) :
    CFSG.Blueprint.LieModel S .POmegaMinus m 2 n := by
  obtain ⟨d, hv, ⟨q, rfl, hq⟩, ⟨e⟩⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.exists_lieIndex hcat
  have hLM := CFSG.Models.lieModel_twistedD m q hv e
  have hp2 : q.p = 2 := by
    have hdiv : q.p ∣ 2 ^ n := by
      rw [← hq, TauCeti.PrimePower.card_def]
      exact dvd_pow_self q.p (Nat.ne_of_gt q.exponent_pos)
    have hd := (Nat.Prime.dvd_of_dvd_pow q.prime_p hdiv)
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h1
    · exact absurd h1 q.prime_p.ne_one
    · exact h1
  have hq' : q.p ^ q.exponent = 2 ^ n := by simpa using hq
  have hqn : q.exponent = n := by
    rw [hp2] at hq'
    exact Nat.pow_right_injective (le_refl 2) hq'
  rw [hp2, hqn] at hLM
  exact CFSG.Models.LieModel.toBlueprint (by simp [CFSG.Blueprint.classicalTags]) hLM

section Certificates


private theorem label_orthPlus {X : Type} [Group X] {lab : LargeEvenLabel} {m n : ℕ}
    (hM : MarkedModel lab X) (hX : CFSG.Blueprint.LieModel X .POmegaPlus m 2 n) :
    lab.tag = .D ∧ lab.rank = m ∧ lab.n = n := by
  have hdet : markTag lab = .POmegaPlus ∧ markRank lab = m ∧ markChar lab = 2 ∧
      markDeg lab = n := by
    by_cases hc : markChar lab = 2
    · have hM' : CFSG.Blueprint.LieModel X (markTag lab) (markRank lab) 2 (markDeg lab) :=
        CFSG.StandardType.NbrInnerMore.lieModel_of_markedModel_two hc hM
      obtain ⟨ht, hr, hn⟩ := CFSG.SeitzReduction.OmegaPilot.lieModel_POmega_two_unique
        (Or.inl rfl) hX hM'
      exact ⟨ht, hr, hc, hn⟩
    · exfalso
      exact (CFSG.StandardType.NbrInnerMore.not_markedModel_of_char_ne_two hX
        (by simp) (by simp) (by simp) hc) hM
  obtain ⟨ht, hr, hc, hn⟩ := hdet
  obtain ⟨tag, rank, nn⟩ := lab
  cases tag <;> simp [markTag, markRank, markDeg, markChar] at ht hr hn hc ⊢
  case D =>
    by_cases h3 : rank = 3
    · simp [h3] at ht
    · simp [h3] at ht hr hn ⊢
      exact ⟨hr, hn⟩
  case twD =>
    by_cases h2 : rank = 2
    · simp [h2] at ht
    · by_cases h3 : rank = 3
      · simp [h3] at ht
      · simp [h2, h3] at ht

private theorem label_orthMinus {X : Type} [Group X] {lab : LargeEvenLabel} {m n : ℕ}
    (hM : MarkedModel lab X) (hX : CFSG.Blueprint.LieModel X .POmegaMinus m 2 n) :
    lab.tag = .twD ∧ lab.rank = m ∧ lab.n = n := by
  have hdet : markTag lab = .POmegaMinus ∧ markRank lab = m ∧ markChar lab = 2 ∧
      markDeg lab = n := by
    by_cases hc : markChar lab = 2
    · have hM' : CFSG.Blueprint.LieModel X (markTag lab) (markRank lab) 2 (markDeg lab) :=
        CFSG.StandardType.NbrInnerMore.lieModel_of_markedModel_two hc hM
      obtain ⟨ht, hr, hn⟩ := CFSG.SeitzReduction.OmegaPilot.lieModel_POmega_two_unique
        (Or.inr rfl) hX hM'
      exact ⟨ht, hr, hc, hn⟩
    · exfalso
      exact (CFSG.StandardType.NbrInnerMore.not_markedModel_of_char_ne_two hX
        (by simp) (by simp) (by simp) hc) hM
  obtain ⟨ht, hr, hc, hn⟩ := hdet
  obtain ⟨tag, rank, nn⟩ := lab
  cases tag <;> simp [markTag, markRank, markDeg, markChar] at ht hr hn hc ⊢
  case twD =>
    by_cases h2 : rank = 2
    · simp [h2] at ht
    · by_cases h3 : rank = 3
      · simp [h3] at ht
      · simp [h2, h3] at ht hr hn ⊢
        exact ⟨hr, hn⟩
  case D =>
    by_cases h3 : rank = 3
    · simp [h3] at ht
    · simp [h3] at ht

private theorem orthMarking_plus
    (G : Type) [Group G] [Finite G] (p : ℕ) (L J A : Subgroup G) (d b : G) (m n : ℕ)
    (hS : Setup p L J A d b)
    (hcat : catalogIs (PSimple p L) (onLie fun i =>
      ∃ q : TauCeti.PrimePower, i = .D m q ∧ q.card = 2 ^ n)) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
      ∃ θ : ↥L ⧸ Subgroup.center ↥L ≃*
          LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m)),
        ∀ a ∈ A,
          ∃ φ ∈ LargeEvenInnSet (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m))),
            LargeEvenInduces θ (fun l l' => (l' : G) = a⁻¹ * l * a) φ := by
  have hLM : CFSG.Blueprint.LieModel (PSimple p L) .POmegaPlus m 2 n :=
    lieModel_of_catalogIs_D hcat
  haveI : IsSimpleGroup (PSimple p L) :=
    CFSG.SeitzReduction.LinearPilot.isSimpleGroup_of_lieModel_POmega (Or.inl rfl) hLM
  have hnt : Nontrivial (PSimple p L) := inferInstance
  have hcore := pPrimeCore_le_center_of_nontrivial hS.qs hnt
  haveI : Group.IsPerfect ↥L := ⟨hS.qs.1⟩
  let eP : ↥L ⧸ Subgroup.center ↥L ≃* PSimple p L :=
    CFSG.LocalAnalysis.GLTheoremA.S172A.pSimpleEquivCenterQuot p hcore
  have hLieZ : CFSG.Blueprint.LieModel (↥L ⧸ Subgroup.center ↥L) .POmegaPlus m 2 n :=
    hLM.of_mulEquiv eP.symm
  obtain ⟨-, lab, -, hraw⟩ :=
    CFSG.StandardType.Canonical.largeEvenMarking_markedModel hS.idiag
  obtain ⟨R, _, _, _, _, _, θ, _, hM⟩ :=
    CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  have hLieR : CFSG.Blueprint.LieModel R .POmegaPlus m 2 n := hLieZ.of_mulEquiv θ
  have hm4 : 4 ≤ m :=
    CFSG.SeitzReduction.OmegaPilot.four_le_of_lieModel_POmega (Or.inl rfl) hLieR
  obtain ⟨htag, hrank, hnlab⟩ := label_orthPlus hM hLieR
  have hrecipe := hraw
  dsimp only [CFSG.Assembly.LargeEvenRawDatum] at hrecipe
  rw [htag] at hrecipe
  dsimp only at hrecipe
  rw [hrank, hnlab] at hrecipe
  rw [if_neg (by omega : ¬ (m = 3))] at hrecipe
  dsimp only [LargeEvenRecipeOmegaPlus] at hrecipe
  obtain ⟨K, hKfield, hKfinite, hKcard, hQ⟩ := hrecipe
  obtain ⟨-, -, ⟨θ', hP', -⟩⟩ := hQ
  obtain ⟨-, hBI⟩ := hP'
  letI := hKfield
  letI := hKfinite
  exact ⟨K, hKfield, hKfinite, hKcard, θ', hBI⟩

private theorem orthMarking_minus
    (G : Type) [Group G] [Finite G] (p : ℕ) (L J A : Subgroup G) (d b : G) (m n : ℕ)
    (hS : Setup p L J A d b)
    (hcat : catalogIs (PSimple p L) (onLie fun i =>
      ∃ q : TauCeti.PrimePower, i = .twistedD m q ∧ q.card = 2 ^ n)) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
      ∃ b c : K, (∀ s : K, s ^ 2 + b * s + c ≠ 0) ∧
      ∃ θ : ↥L ⧸ Subgroup.center ↥L ≃*
          LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (m - 1) b c)),
        ∀ a ∈ A,
          ∃ φ ∈ LargeEvenInnSet (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (m - 1) b c))),
            LargeEvenInduces θ (fun l l' => (l' : G) = a⁻¹ * l * a) φ := by
  have hLM : CFSG.Blueprint.LieModel (PSimple p L) .POmegaMinus m 2 n :=
    lieModel_of_catalogIs_twistedD hcat
  haveI : IsSimpleGroup (PSimple p L) :=
    CFSG.SeitzReduction.LinearPilot.isSimpleGroup_of_lieModel_POmega (Or.inr rfl) hLM
  have hnt : Nontrivial (PSimple p L) := inferInstance
  have hcore := pPrimeCore_le_center_of_nontrivial hS.qs hnt
  haveI : Group.IsPerfect ↥L := ⟨hS.qs.1⟩
  let eP : ↥L ⧸ Subgroup.center ↥L ≃* PSimple p L :=
    CFSG.LocalAnalysis.GLTheoremA.S172A.pSimpleEquivCenterQuot p hcore
  have hLieZ : CFSG.Blueprint.LieModel (↥L ⧸ Subgroup.center ↥L) .POmegaMinus m 2 n :=
    hLM.of_mulEquiv eP.symm
  obtain ⟨-, lab, -, hraw⟩ :=
    CFSG.StandardType.Canonical.largeEvenMarking_markedModel hS.idiag
  obtain ⟨R, _, _, _, _, _, θ, _, hM⟩ :=
    CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  have hLieR : CFSG.Blueprint.LieModel R .POmegaMinus m 2 n := hLieZ.of_mulEquiv θ
  have hm4 : 4 ≤ m :=
    CFSG.SeitzReduction.OmegaPilot.four_le_of_lieModel_POmega (Or.inr rfl) hLieR
  obtain ⟨htag, hrank, hnlab⟩ := label_orthMinus hM hLieR
  have hrecipe := hraw
  dsimp only [CFSG.Assembly.LargeEvenRawDatum] at hrecipe
  rw [htag] at hrecipe
  dsimp only at hrecipe
  rw [hrank, hnlab] at hrecipe
  rw [if_neg (by omega : ¬ (m = 2)), if_neg (by omega : ¬ (m = 3))] at hrecipe
  dsimp only [LargeEvenRecipeOmegaMinus] at hrecipe
  obtain ⟨K, hKfield, hKfinite, hKcard, hQ⟩ := hrecipe
  obtain ⟨b, c, hbc, hQ'⟩ := hQ
  obtain ⟨-, -, ⟨θ', hP', -⟩⟩ := hQ'
  obtain ⟨-, hBI⟩ := hP'
  letI := hKfield
  letI := hKfinite
  exact ⟨K, hKfield, hKfinite, hKcard, b, c, hbc, θ', hBI⟩

theorem orthMarking_holds :
    (∀ (G : Type) [Group G] [Finite G] (p : ℕ) (L J A : Subgroup G) (d b : G) (m n : ℕ),
      Setup p L J A d b →
      catalogIs (PSimple p L) (onLie fun i =>
          ∃ q : TauCeti.PrimePower, i = .D m q ∧ q.card = 2 ^ n) →
      ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
        ∃ θ : ↥L ⧸ Subgroup.center ↥L ≃*
            LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m)),
          ∀ a ∈ A,
            ∃ φ ∈ LargeEvenInnSet (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m))),
              LargeEvenInduces θ (fun l l' => (l' : G) = a⁻¹ * l * a) φ) ∧
    (∀ (G : Type) [Group G] [Finite G] (p : ℕ) (L J A : Subgroup G) (d b : G) (m n : ℕ),
      Setup p L J A d b →
      catalogIs (PSimple p L) (onLie fun i =>
          ∃ q : TauCeti.PrimePower, i = .twistedD m q ∧ q.card = 2 ^ n) →
      ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
        ∃ b c : K, (∀ s : K, s ^ 2 + b * s + c ≠ 0) ∧
        ∃ θ : ↥L ⧸ Subgroup.center ↥L ≃*
            LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (m - 1) b c)),
          ∀ a ∈ A,
            ∃ φ ∈ LargeEvenInnSet (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (m - 1) b c))),
              LargeEvenInduces θ (fun l l' => (l' : G) = a⁻¹ * l * a) φ) :=
  ⟨orthMarking_plus, orthMarking_minus⟩

end Certificates

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
