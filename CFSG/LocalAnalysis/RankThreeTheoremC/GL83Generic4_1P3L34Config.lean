module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34L45
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34L44
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34Choice
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34Comm
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34Inspect
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34Sign
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34Escape
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34L44c
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1P34b

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

structure L34Config (P : Sylow 3 G) (M J : Subgroup G) (x : G) (U S₁ T : Subgroup G) : Prop where
  U_le : U ≤ (P : Subgroup G)
  U_elemAbelian : IsElemAbelian 3 U
  U_card : Nat.card U = 3 ^ 2
  x_mem : x ∈ U
  U_inf_J : U ⊓ J ≠ ⊥
  lemma42 : ∀ u ∈ U, u ∉ zpowers x → centralizer ({u} : Set G) ≤ M
  lemma43 : ∀ Y : Subgroup G, IsPGroup 2 Y → Y ≤ M → U ≤ normalizer (Y : Set G) →
    IsSylowOf 2 (Y ⊓ GLBPrimeCore 3 M) (GLBPrimeCore 3 M) → normalizer (Y : Set G) ≤ M
  remark : L34Remark 3 P M J
  lemma44 : ∀ A : Subgroup G, IsPGroup 2 A → A ≤ GLBPrimeCore 3 M ⊓ centralizer ({x} : Set G) →
    Nat.card A ≤ 2
  maximal : rankTwoMaximalInvariantTwoSubgroup U S₁
  not_le : ¬ S₁ ≤ M
  inf_maximal : invariantTwoMaximalWithin U J (S₁ ⊓ J)
  choice : ∀ S₁' : Subgroup G, rankTwoMaximalInvariantTwoSubgroup U S₁' → ¬ S₁' ≤ M →
    invariantTwoMaximalWithin U J (S₁' ⊓ J) →
    Nat.card (S₁' ⊓ M : Subgroup G) < Nat.card (S₁ ⊓ M : Subgroup G) ∨
      (Nat.card (S₁' ⊓ M : Subgroup G) = Nat.card (S₁ ⊓ M : Subgroup G) ∧
        Nat.card (S₁' ⊓ GLBPrimeCore 3 M : Subgroup G) ≤
          Nat.card (S₁ ⊓ GLBPrimeCore 3 M : Subgroup G))
  comm_le : ⁅S₁, zpowers x⁆ ≤ M
  comm_eq : ⁅S₁ ⊓ M, zpowers x⁆ = ⁅S₁, zpowers x⁆
  comm_normal : S₁ ≤ normalizer ((⁅S₁ ⊓ M, zpowers x⁆ : Subgroup G) : Set G)
  sylow_two : IsSylowOf 2 (l34Img x J (S₁ ⊓ J)) (l34Img x J J)
  cent_eq : S₁ ⊓ centralizer ({x} : Set G) = (S₁ ⊓ J) ⊔ (S₁ ⊓ centralizer (U : Set G))
  W_card : Nat.card ↥(S₁ ⊓ centralizer (U : Set G)) ≤ 2
  cent_inf_M : S₁ ⊓ M ⊓ centralizer ({x} : Set G) = S₁ ⊓ centralizer (U : Set G)
  W_graph : ∀ w ∈ S₁ ⊓ centralizer (U : Set G), w ≠ 1 →
    ¬ (l34Img x J (zpowers w) ≤ centralizer ((l34Img x J ((P : Subgroup G) ⊓ J) :
      Subgroup (L34Quot x J)) : Set (L34Quot x J)))
  M₀_exists : ∃ M₀ : Subgroup G, M₀ ≤ M ∧ (M₀.subgroupOf M).Normal ∧ M₀.relIndex M ≤ 2 ∧
    GLBPrimeCore 3 M ≤ M₀ ∧ (∀ a ∈ M, ∀ b ∈ M, a * b * a⁻¹ * b⁻¹ ∈ M₀) ∧
    S₁ ⊓ M ⊓ M₀ = ⁅S₁ ⊓ M, zpowers x⁆
  pair : invariantTwoMaximalWithin U M T ∧ S₁ ⊓ M ≤ T
  escape_le : T ⊓ GLBPrimeCore 3 M ⊓ normalizer ((S₁ ⊓ M : Subgroup G) : Set G) ≤
    normalizer ((⁅S₁ ⊓ M, zpowers x⁆ : Subgroup G) : Set G)
  escape_not : ¬ (T ⊓ GLBPrimeCore 3 M ⊓ normalizer ((S₁ ⊓ M : Subgroup G) : Set G) ≤
    GLBPrimeCore 3 (normalizer ((⁅S₁ ⊓ M, zpowers x⁆ : Subgroup G) : Set G)))

theorem l34_config_exists (hS : Setting G) (hU0 : FullCoreLocal G) (hD1 : TheoremD1 G)
    (hK1 : KFactL34TwoSignalizer) (hK2 : KFactL34Three) (hK3 : KFactL34Unitary)
    (hK4 : KFactL34Borel) (hK5 : KFactL34Graph) (hK8 : KFactL34SylowCentralizer)
    (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M)
    {x : G} (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsL34Normal M x J)
    (hplane : L34PlaneData 3 P M x J) : ∃ U S₁ T : Subgroup G, L34Config P M J x U S₁ T := by
  obtain ⟨hR1, h42, h43, hR3⟩ := hplane
  obtain ⟨U, hUP, hU, hUc, hxU, hL43⟩ := h43
  have hC := h42 U hUP hU hUc hxU
  obtain ⟨hxP, ⟨-, hx1, hx3, -, -⟩, -, -⟩ := id hgen
  have hUM : U ≤ M := hUP.trans (sylow_le_of_isCoreMaxLocal hS hp hM).1
  have hUJ := l34_inf_ne_bot hx1 hR1 hU hUc hUP hxU
  have hL45 := l34_exists_maximal_not_le hS hU0 hK1 hp hM hgen hJ hU hUc hUP hxU hUJ
  obtain ⟨S₁, hS₁, hS₁M, hS₁J, hmax⟩ := l34_exists_choice (N := GLBPrimeCore 3 M) hL45
  have hUab : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := fun a ha b hb =>
    p34_comm_of_isMulCommutative hU.1 ha hb
  have hF := l34_stepF hS₁.1 hU.2 hUab hUc hxU hS₁.2.1 hC
  have hG := l34_stepG hS hU0 hD1 hK1 hK2 hK4 hK5 hp hM hgen hJ
    (l34_Kimg_inf_M hS hU0 hK1 hK2 hp hM hgen hJ) hU hUc hUP hxU hUJ hS₁ hS₁J hC
  have hH := l34_stepH hS hU0 hK1 hK2 hK8 hp hM hgen hJ hR3 hU hUc hUP hxU hUJ hS₁.1 hS₁.2.1
    hG.2.2.1 hG.2.2.2.1 hG.2.2.2.2
  have hinv : U ≤ normalizer ((S₁ ⊓ M : Subgroup G) : Set G) :=
    common_normalizer_le_normalizer_inf U S₁ M hS₁.2.1 (hUM.trans Subgroup.le_normalizer)
  obtain ⟨T, hST, hT⟩ := exists_invariantTwoMaximalWithin_containing U M (S₁ ⊓ M) inf_le_right
    hS₁.1.to_inf_left hinv
  have hI := l34_stepI hU hUc hUM hxU hJ.le_centralizer hJ.centralizer_le hC hL43 hS₁ hS₁M hS₁J
    hmax hF.2.2 (by
      obtain ⟨M₀, h1, h2, h3, h4, -, h6⟩ := hH
      exact ⟨M₀, h1, h2, h3, h4, h6⟩) hT hST
  exact ⟨U, S₁, T, ⟨hUP, hU, hUc, hxU, hUJ, hC, hL43, hR3,
    l34_lemma44_card hS hU0 hD1 hK1 hK2 hK3 hp hM hgen hJ, hS₁, hS₁M, hS₁J, hmax, hF.1, hF.2.1,
    hF.2.2, hG.1, hG.2.1, hG.2.2.1, hG.2.2.2.1, hG.2.2.2.2, hH, ⟨hT, hST⟩, hI.1, hI.2⟩⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
