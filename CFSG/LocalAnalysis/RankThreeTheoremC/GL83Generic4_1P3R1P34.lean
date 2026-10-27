module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3M11Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3M11P34Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.SignalizerNoncentral2_7KFact
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1P34d
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1P34e
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1P34g
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerRank
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.MaximalPairGeometry
public import CFSG.LocalAnalysis.AGLEmbeddingD2.PairMaximal

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

theorem m11_prop34 (hS : Setting G) (hU0 : FullCoreLocal G) (hD1 : TheoremD1 G)
    (hKM : CFSG.AGLEmbeddingD2.KFactM11Three) (hKA : KFactM11TwoSignalizer)
    (hKT : KFactM11SylowTransitive) (hSig : SignalizerTwoGroupKFact)
    (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M)
    {x : G} (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsM11Normal M x J) :
    M11Prop34 3 P x := by
  have hY := p34_yData hS hU0 hKM hKA hp hM hgen hJ
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  set Q : Subgroup G := (P : Subgroup G) ⊓ C with hQ
  have hQsyl : IsSylowOf 3 Q C := hgen.2.2.1
  have hQab : IsMulCommutative Q := p34_isMulCommutative_of_isSylowOf hY hKM hKA hQsyl
  have hQc : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := fun a ha b hb =>
    p34_comm_of_isMulCommutative hQab ha hb
  have hrank : CFSG.Open.pRank 3 Q = 3 := hgen.2.2.2
  obtain ⟨K₀, hK₀Q, hK₀el, hK₀card, hxK₀, hK₀tr⟩ :=
    p34_exists_K₀ hS hU0 hKM hKA hKT hp hM hgen hJ
  have hL33 : ∀ D : Subgroup G, D ≤ Q → IsElemAbelian 3 D → Nat.card D = 3 ^ 2 →
      ¬ ∃ S : Finset (Subgroup G), S.card = 3 ∧ ∀ L ∈ S, L ≤ D ∧ Nat.card L = 3 ∧
        ∃ g : G, L = (zpowers x).map (MulAut.conj g).toMonoidHom :=
    fun D hDQ hD hDc => p34_not_exists_conj_lines hS hU0 hD1 hKM hKA hSig hp hM hgen hJ hDQ hD hDc
  obtain ⟨hxP, hlo, -, -⟩ := hgen
  obtain ⟨-, hx1, hx3, -, -⟩ := hlo
  have hxC : x ∈ C := mem_centralizer_singleton_iff.mpr rfl
  have hxQ : x ∈ Q := ⟨hxP, hxC⟩
  have hK₀C : K₀ ≤ C := hK₀Q.trans inf_le_right
  have hK₀Q' : K₀ ≤ Q := hK₀Q
  have hfus := p34_fusion hL33 hx1 hx3 hxQ hK₀Q' hK₀C hK₀el hK₀card hxK₀ hK₀tr
  set E : Subgroup G := K₀ ⊔ zpowers x with hE
  have hEQ : E ≤ Q := sup_le hK₀Q' (zpowers_le.mpr hxQ)
  have hK₀cent : K₀ ≤ centralizer ((zpowers x : Subgroup G) : Set G) := fun k hk => by
    rw [p34_centralizer_zpowers x]; exact hK₀C hk
  have hEel : IsElemAbelian 3 E :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_sup_of_commuting 3 hK₀el
      (CFSG.AGLEmbedding.isElemAbelian_zpowers hx3) hK₀cent
  have hEcard : Nat.card E = 3 ^ 3 := by
    rw [hE, CFSG.RankThree.PartOne.Planes.card_sup_zpowers Nat.prime_three K₀ hx3 hxK₀
      (fun e he => mem_centralizer_singleton_iff.mp (hK₀C he)), hK₀card]
    norm_num
  have hΩ : ∀ y ∈ Q, y ^ 3 = 1 → y ∈ E := by
    intro y hyQ hy3
    by_contra hyE
    have hcomm : ∀ e ∈ E, e * y = y * e := fun e he => hQc e (hEQ he) y hyQ
    have hcard := CFSG.RankThree.PartOne.Planes.card_sup_zpowers Nat.prime_three E hy3 hyE hcomm
    have hcent : E ≤ centralizer ((zpowers y : Subgroup G) : Set G) := fun e he => by
      rw [p34_centralizer_zpowers y]
      exact mem_centralizer_singleton_iff.mpr (hcomm e he)
    have hel := CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_sup_of_commuting 3 hEel
      (CFSG.AGLEmbedding.isElemAbelian_zpowers hy3) hcent
    have hle : E ⊔ zpowers y ≤ Q := sup_le hEQ (zpowers_le.mpr hyQ)
    have h4 := le_pRank_of_elemAbelian_card (p := 3) hle hel (k := 4)
      (by rw [hcard, hEcard]; norm_num)
    omega
  have hPC : (P : Subgroup G) ≤ C := by
    by_contra hnot
    have hlt : Q < (P : Subgroup G) := inf_lt_left.mpr hnot
    have hgrow := pGroup_proper_subgroup_lt_internal_normalizer 3 Nat.prime_three
      (P : Subgroup G) Q P.isPGroup' hlt
    obtain ⟨y, hy, hyQ⟩ := IsConcreteLE.exists_of_lt hgrow
    have hyP : y ∈ (P : Subgroup G) := hy.1
    have hyN : y ∈ normalizer (Q : Set G) := hy.2
    have hx'Q : y * x * y⁻¹ ∈ Q := (mem_normalizer_iff.mp hyN x).mp hxQ
    have hx'3 : (y * x * y⁻¹) ^ 3 = 1 := by rw [conj_pow, hx3]; simp
    have hx'x : y * x * y⁻¹ ∈ zpowers x := hfus _ (hΩ _ hx'Q hx'3) ⟨y, rfl⟩
    obtain ⟨m, hm⟩ := P.isPGroup' ⟨y, hyP⟩
    have hym : y ^ (3 ^ m) = 1 := congrArg Subtype.val hm
    have hxy := p34_conj_eq_of_pow hx1 hx3 hym hx'x
    have hyC : y ∈ C := mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hxy)
    exact hyQ ⟨hyP, hyC⟩
  have hPQ : (P : Subgroup G) = Q := (inf_eq_left.mpr hPC).symm
  refine ⟨?_, ?_⟩
  · rw [hPQ]
    exact hQab
  · intro g hg
    have hy : g * x * g⁻¹ ∈ (P : Subgroup G) := hg ⟨x, mem_zpowers x, rfl⟩
    have hyQ : g * x * g⁻¹ ∈ Q := hPQ ▸ hy
    have hy3 : (g * x * g⁻¹) ^ 3 = 1 := by rw [conj_pow, hx3]; simp
    have hyx : g * x * g⁻¹ ∈ zpowers x := hfus _ (hΩ _ hyQ hy3) ⟨g, rfl⟩
    have hle : (zpowers x).map (MulAut.conj g).toMonoidHom ≤ zpowers x := by
      rw [MonoidHom.map_zpowers]
      exact zpowers_le.mpr hyx
    exact Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])

end CFSG.LocalAnalysis.RankThreeTheoremC
