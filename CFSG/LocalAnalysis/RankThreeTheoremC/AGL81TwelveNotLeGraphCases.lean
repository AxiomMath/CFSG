module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNotLeGraphHatDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.Reduce
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.LargeFieldProof
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNotLeGraphHat
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNotLeGraphOmega
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveLeCartanSolv
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenTwelveRanksNotLe
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenTwelveRanksLeOrth
public import CFSG.LocalAnalysis.GLTheoremB.PQuotientTools
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNotLeDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique Subgroup
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open scoped commutatorElement

theorem graph_lie_case (hGA : GriessAllModelsStatement) (hZ : OddCenterRest) (hT1 : ∀ (A : Type)
    [Group A] [Finite A] (Y P : Subgroup A) (X : Subgroup (↥P ⧸ CFSG.pCore 2 ↥P)), IsParabolicTwo Y
    P → Sym.IsSymThree X → IsSubnormal X ⊤ → ∃ P'' : Subgroup A, IsParabolicTwo Y P'' ∧ P'' ≤ P ∧ ¬
    IsSylowTwoOf (pCoreOf 2 P'') Y ∧ ∀ K : Subgroup A, K ≤ P'' → ⁅K, K⁆ = K → ¬ 3 ∣ Nat.card K)
    (hT2 : ∀ (A : Type) [Group A] [Finite A] (Y P : Subgroup A), IsParabolicTwo Y P → (∀ P'' :
        Subgroup A, IsParabolicTwo Y P'' → P'' ≤ P → (∀ K : Subgroup A, K ≤ P'' → ⁅K, K⁆ = K → ¬ 3 ∣
        Nat.card K) → ∀ S : Subgroup A, S ≤ P'' → IsPGroup 2 S → Nat.card S ≤ 2 * Nat.card (pCoreOf
        2 P'')) → NoTwoSymThree P) (hSp : ∀ (A : Type) [Group A] [Finite A] (Y P J : Subgroup A) (t : A),
        OddCenterRest → Open.IsQuasisimple ↥Y → pCoreOf 2 Y = ⊥ → IsLieOf ParabCensus.IdxBTwo (↥Y ⧸
        center ↥Y) → IsParabolicTwo Y P → J ≤ P → IsSubnormal (hatOf P J) ⊤ → Sym.IsSymThree (hatOf
        P J) → t ∈ Subgroup.normalizer (Y : Set A) → t ∈ Subgroup.normalizer (P : Set A) → hatOf P
        (J.map (MulAut.conj t).toMonoidHom) = hatOf P J) (hU42 : ∀ (A : Type) [Group A] [Finite A] (Y P : Subgroup A),
        Open.IsQuasisimple ↥Y → pCoreOf 2 Y = ⊥ → IsLieOver (↥Y ⧸ Subgroup.center ↥Y) (.twistedA 3)
        2 1 → IsParabolicTwo Y P → NoTwoSymThree P)
    {A : Type} [Group A] [Finite A] {Y P J : Subgroup A} {t : A}
    (hY : Open.IsQuasisimple ↥Y) (hO : pCoreOf 2 Y = ⊥) {d : TauCeti.ValidLieTypeIndex}
    (hd : IsClassicalOrG2Index d.1)
    (e : ↥Y ⧸ center ↥Y ≃* (TauCeti.CFSGIndex.lie d).Group) (hP : IsParabolicTwo Y P)
    (hrk : Open.pRank 3 Y ≤ 3) (hJP : J ≤ P) (hJs : IsSubnormal (hatOf P J) ⊤)
    (hJiso : Sym.IsSymThree (hatOf P J)) (htY : t ∈ Subgroup.normalizer (Y : Set A))
    (htP : t ∈ Subgroup.normalizer (P : Set A))
    (hJt : hatOf P (J.map (MulAut.conj t).toMonoidHom) ≠ hatOf P J) :
    ∃ r : ℕ, 4 ≤ r ∧ IsLieOver ↥Y (.A r) 2 1 := by
  classical
  obtain ⟨hJ's, hJ'iso⟩ := hatOf_map_conj_symThree hJP htP hJs hJiso
  haveI : Group.IsPerfect ↥Y := ⟨hY.1⟩
  have hodd : Odd (Nat.card (center ↥Y)) := ParabCensus.odd_card_center_of_pCoreOf_eq_bot hO
  have hq4 : LieField d.1 < 4 := by
    by_contra hge
    obtain ⟨P'', hP'', -, hSyl, hsolv⟩ := hT1 A Y P (hatOf P J) hP hJiso hJs
    obtain ⟨K, hKP, hKperf, hK3⟩ :=
      largeFieldParabolic_proved A Y P'' hY d hd (by omega) ⟨e⟩ hP'' hSyl
    exact hsolv K hKP hKperf hK3
  have hcenter : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ Nat.card (center ↥Y) →
      (∃ r q, d.1 = .A r q ∧ ℓ ∣ q.card - 1) ∨ (∃ r q, d.1 = .twistedA r q ∧ ℓ ∣ q.card + 1) := by
    intro ℓ hℓ hℓd
    have hℓ2 : ℓ ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hℓd)
    exact AGLEmbedding.ToralCensus.prime_dvd_torus_of_dvd_card_center hGA d hd e hℓ hℓ2 hℓd
  obtain ⟨d', hv⟩ := d
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hdup := ((TauCeti.LieTypeIndex.valid_iff _).1 hv).2
  cases d' <;> try exact hd.elim
  ·
    rename_i r q
    have hqp : q.p = 2 := hd
    simp only [LieField] at hq4
    rcases TwelveLe.card_eq_two_or_four_le hqp with ⟨hc2, hqe⟩ | h4
    swap
    · omega
    have hZ1 : Nat.card (center ↥Y) = 1 := by
      by_contra hne
      obtain ⟨ℓ, hℓ, hℓd⟩ := Nat.exists_prime_and_dvd hne
      rcases hcenter ℓ hℓ hℓd with ⟨r', q', hdq, hdvd⟩ | ⟨r', q', hdq, -⟩
      · injection hdq with h1 h2
        subst h2
        rw [hc2] at hdvd
        exact hℓ.not_dvd_one (by simpa using hdvd)
      · cases hdq
    have hLie : IsLieOver ↥Y (.A r) 2 1 :=
      TwelveLe.isLieOver_of_card_center_eq_one hqp hqe rfl e hZ1
    refine ⟨r, ?_, hLie⟩
    simp only [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff] at hdup
    have hr1 : 1 ≤ r ∧ (r = 1 → 4 ≤ q.card) := hrange
    by_contra hlt
    push Not at hlt
    omega
  ·
    rename_i r q
    have hqp : q.p = 2 := hd
    simp only [LieField] at hq4
    rcases TwelveLe.card_eq_two_or_four_le hqp with ⟨hc2, hqe⟩ | h4
    swap
    · omega
    have hr2 : 2 ≤ r ∧ (r = 2 → 3 ≤ q.card) := hrange
    have hr3 : 3 ≤ r := by
      by_contra hlt
      have := hr2.2 (by omega)
      omega
    have hLieU : IsLieOver (↥Y ⧸ center ↥Y) (.twistedA r) 2 1 :=
      ⟨⟨.twistedA r q, hv⟩, ⟨q, hqp, hqe, rfl⟩, ⟨e⟩⟩
    by_cases hr : r = 3
    · subst hr
      exact absurd (hU42 A Y P hY hO hLieU hP (hatOf P (J.map (MulAut.conj t).toMonoidHom))
        (hatOf P J) hJ'iso hJiso hJ's hJs) hJt
    · have h4 := TwelveLe.four_le_pRank_of_isLieOver_twistedA hY hO (by omega : 4 ≤ r) hLieU
      omega
  ·
    rename_i r q
    have hqp : q.p = 2 := hd
    simp only [LieField] at hq4
    rcases TwelveLe.card_eq_two_or_four_le hqp with ⟨hc2, hqe⟩ | h4
    swap
    · omega
    have hB2 : IsLieOf ParabCensus.IdxBTwo (↥Y ⧸ center ↥Y) := ⟨⟨.B r q, hv⟩, hc2, ⟨e⟩⟩
    exact absurd (hSp A Y P J t hZ hY hO hB2 hP hJP hJs hJiso htY htP) hJt
  ·
    rename_i r q
    have hqp : q.p = 2 := hd
    simp only [LieField] at hq4
    rcases TwelveLe.card_eq_two_or_four_le hqp with ⟨hc2, hqe⟩ | h4
    swap
    · omega
    have hZ1 : Nat.card (center ↥Y) = 1 :=
      AGLEmbedding.ToralCensus.card_center_eq_one_of_index hGA ⟨.D r q, hv⟩ hd
        (fun r' q' h => by cases h) (fun r' q' h => by cases h) e hodd
    have hLie : IsLieOver ↥Y (.D r) 2 1 :=
      TwelveLe.isLieOver_of_card_center_eq_one hqp hqe rfl e hZ1
    have h4 := TwelveRanksNotLe.four_le_pRank_three_of_isLieOver_D hLie
    rw [← CFSG.LocalAnalysis.GLTheoremB.pRank_eq_pRank_top_subtype (by norm_num) Y] at h4
    omega
  ·
    rename_i r q
    have hqp : q.p = 2 := hd
    simp only [LieField] at hq4
    rcases TwelveLe.card_eq_two_or_four_le hqp with ⟨hc2, hqe⟩ | h4
    swap
    · omega
    have hZ1 : Nat.card (center ↥Y) = 1 :=
      AGLEmbedding.ToralCensus.card_center_eq_one_of_index hGA ⟨.twistedD r q, hv⟩ hd
        (fun r' q' h => by cases h) (fun r' q' h => by cases h) e hodd
    have hLie : IsLieOver ↥Y (.twistedD r) 2 1 :=
      TwelveLe.isLieOver_of_card_center_eq_one hqp hqe rfl e hZ1
    have hr4 : 4 ≤ r := hrange
    by_cases hr : r = 4
    · subst hr
      have hb : ∀ P'' : Subgroup A, IsParabolicTwo Y P'' → P'' ≤ P →
          (∀ K : Subgroup A, K ≤ P'' → ⁅K, K⁆ = K → ¬ 3 ∣ Nat.card K) →
          ∀ S : Subgroup A, S ≤ P'' → IsPGroup 2 S → Nat.card S ≤ 2 * Nat.card (pCoreOf 2 P'') :=
        fun P'' hP'' _ hperf => Omega.card_le_two_mul_pCoreOf_of_solvThree hLie hP'' hperf
      exact absurd (hT2 A Y P hP hb (hatOf P (J.map (MulAut.conj t).toMonoidHom))
        (hatOf P J) hJ'iso hJiso hJ's hJs) hJt
    · have h4 := TwelveRanksLe.four_le_pRank_of_isLieOver_twistedD hLie (by omega)
      rw [← CFSG.LocalAnalysis.GLTheoremB.pRank_eq_pRank_top_subtype (by norm_num) Y] at h4
      omega
  ·
    rename_i q
    have hqp : q.p = 2 := hd
    simp only [LieField] at hq4
    have h3q : 3 ≤ q.card := hrange
    rcases TwelveLe.card_eq_two_or_four_le hqp with ⟨hc2, hqe⟩ | h4
    · omega
    · omega


theorem kFactTwelveNotLeGraph_of_griess (hGA : GriessAllModelsStatement) (hT1 : ∀ (A : Type) [Group
    A] [Finite A] (Y P : Subgroup A) (X : Subgroup (↥P ⧸ CFSG.pCore 2 ↥P)), IsParabolicTwo Y P →
    Sym.IsSymThree X → IsSubnormal X ⊤ → ∃ P'' : Subgroup A, IsParabolicTwo Y P'' ∧ P'' ≤ P ∧ ¬
    IsSylowTwoOf (pCoreOf 2 P'') Y ∧ ∀ K : Subgroup A, K ≤ P'' → ⁅K, K⁆ = K → ¬ 3 ∣ Nat.card K)
    (hT2 : ∀ (A : Type) [Group A] [Finite A] (Y P : Subgroup A), IsParabolicTwo Y P → (∀ P'' :
        Subgroup A, IsParabolicTwo Y P'' → P'' ≤ P → (∀ K : Subgroup A, K ≤ P'' → ⁅K, K⁆ = K → ¬ 3 ∣
        Nat.card K) → ∀ S : Subgroup A, S ≤ P'' → IsPGroup 2 S → Nat.card S ≤ 2 * Nat.card (pCoreOf
        2 P'')) → NoTwoSymThree P) (hSp : ∀ (A : Type) [Group A] [Finite A] (Y P J : Subgroup A) (t : A),
        OddCenterRest → Open.IsQuasisimple ↥Y → pCoreOf 2 Y = ⊥ → IsLieOf ParabCensus.IdxBTwo (↥Y ⧸
        center ↥Y) → IsParabolicTwo Y P → J ≤ P → IsSubnormal (hatOf P J) ⊤ → Sym.IsSymThree (hatOf
        P J) → t ∈ Subgroup.normalizer (Y : Set A) → t ∈ Subgroup.normalizer (P : Set A) → hatOf P
        (J.map (MulAut.conj t).toMonoidHom) = hatOf P J) (hSmall : ∀ (A : Type) [Group A] [Finite A] (Y P : Subgroup
        A), Open.IsQuasisimple ↥Y → pCoreOf 2 Y = ⊥ →
        CFSG.HardMathSupport.Curtis.Proving.OvergroupOrder96 (↥Y ⧸ Subgroup.center ↥Y) →
        IsParabolicTwo Y P → NoTwoSymThree P) (hU42 : ∀ (A : Type) [Group A] [Finite
        A] (Y P : Subgroup A), Open.IsQuasisimple ↥Y → pCoreOf 2 Y = ⊥ → IsLieOver (↥Y ⧸
        Subgroup.center ↥Y) (.twistedA 3) 2 1 → IsParabolicTwo Y P → NoTwoSymThree P)
    (hA8 : ∀ (A : Type) [Group A] [Finite A] (Y P : Subgroup A), Open.IsQuasisimple ↥Y → pCoreOf 2 Y
        = ⊥ → Nonempty (↥Y ⧸ Subgroup.center ↥Y ≃* alternatingGroup (Fin 8)) → IsParabolicTwo Y P →
        ∀ X X' X₁ : Subgroup (↥P ⧸ CFSG.pCore 2 ↥P), Sym.IsSymThree X → Sym.IsSymThree X' →
        IsSubnormal X ⊤ → IsSubnormal X' ⊤ → X ≠ X' → IsSubnormal X₁ ⊤ → (IsSymThreeOrSUThreeTwo ↥X₁
        ∨ Open.IsQuasisimple ↥X₁) → X₁ ≠ X → X₁ ≠ X' → False) : KFactTwelveNotLeGraph := by
  intro A _ _ Y P J J₁ t hY hO hcl hP hrk hJP hJs hJiso htY htP _ hJt hJ₁P hJ₁s hJ₁ty hne1 hne2
  have hZ : OddCenterRest := oddCenterRest_of_griess hGA
  obtain ⟨hJ's, hJ'iso⟩ := hatOf_map_conj_symThree hJP htP hJs hJiso
  rcases hcl with ⟨d, hd, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨d, hd, ⟨e⟩⟩
  · exact graph_lie_case hGA hZ hT1 hT2 hSp hU42 hY hO hd e hP hrk hJP hJs hJiso htY htP hJt
  · rcases hn with rfl | rfl | rfl
    · have h96 := CFSG.HardMathSupport.Curtis.Proving.ordBound_isSmallFourTwo
        (Or.inl ⟨5, Or.inl rfl, ⟨e⟩⟩)
      exact absurd (hSmall A Y P hY hO h96 hP _ _ hJ'iso hJiso hJ's hJs) hJt
    · have h96 := CFSG.HardMathSupport.Curtis.Proving.ordBound_isSmallFourTwo
        (Or.inl ⟨6, Or.inr rfl, ⟨e⟩⟩)
      exact absurd (hSmall A Y P hY hO h96 hP _ _ hJ'iso hJiso hJ's hJs) hJt
    · exact (hA8 A Y P hY hO ⟨e⟩ hP _ _ _ hJiso hJ'iso hJs hJ's (Ne.symm hJt) hJ₁s hJ₁ty hne1
        hne2).elim
  · have h96 := CFSG.HardMathSupport.Curtis.Proving.ordBound_isSmallFourTwo
      (Or.inr ⟨d, hd, ⟨e⟩⟩)
    exact absurd (hSmall A Y P hY hO h96 hP _ _ hJ'iso hJiso hJ's hJs) hJt

end CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe
