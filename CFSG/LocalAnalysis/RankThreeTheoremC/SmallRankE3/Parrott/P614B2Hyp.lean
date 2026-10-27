module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank618Point
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P5IiiPx

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614B2

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

variable {G : Type} [Group G] [Finite G]

theorem conj_mem_zpowers (hS : RankThreeTheoremC.Setting G) {P : Sylow 3 G} {M : Subgroup G}
    (hsit : SmallRankSituation G 3 P M) {x z : G} (hx : SmallRankPoint P M x)
    (hz : SmallRankCentral P z) {g : G} (hg : g * z * g⁻¹ ∈ zpowers x ⊔ zpowers z) :
    g * z * g⁻¹ ∈ zpowers z := by
  by_contra hgz
  have h2 := pRank_centralizer_le_two3 hS hsit (smallRankPoint_of_mem_plane hS hsit hx hz hg hgz)
  have hP3 := (sylow_le_of_isCoreMaxLocal hS hsit.mem_sigmaA hsit.isCoreMaxLocal).2
  have hPz : (P : Subgroup G).map (MulAut.conj g).toMonoidHom ≤
      centralizer ({g * z * g⁻¹} : Set G) := by
    rintro _ ⟨q, hq, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have hqz : q * z = z * q := mem_centralizer_iff.mp hz.centralizes q hq
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * q * g⁻¹ * (g * z * g⁻¹) = g * (q * z) * g⁻¹ := by group
      _ = g * (z * q) * g⁻¹ := by rw [hqz]
      _ = g * z * g⁻¹ * (g * q * g⁻¹) := by group
  have h3 := pRank_mono 3 Nat.prime_three.one_lt hPz
  rw [pRank_map_automorphism 3 Nat.prime_three.one_lt, hP3] at h3
  omega

theorem kFact64ii_apply (h : KFact64ii) {P : Sylow 3 G} {M : Subgroup G} {x z : G}
    {H S : Subgroup G} (hyp : Hyp P M x z H S) (hΩ : OmegaLe x z H) :
    (∃ K : Subgroup G, PComp 3 ((M ⊓ H) ⊔ rankThreePrimeCore 3 H) H K z) ∧
      ∃ b ∈ zpowers x ⊔ zpowers z, b ∉ zpowers z ∧
        ¬ CFSG.HasNormalPComplement 3 ↥(H ⊓ centralizer ({b} : Set G)) := by
  have hS := hyp.setting
  have hsit := hyp.situation
  have hx := hyp.point
  have hz := hyp.central
  have hopt := hyp.optimal
  have : IsSimpleGroup G := hS.simple
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hHtop : H ≠ ⊤ := twoLocal_ne_top hS.nonab H hopt.ext.pair.isTwoLocal
  have hKH : CFSG.Open.IsKGroup ↥H :=
    CFSG.AGLEmbedding.catalogSimpleSections_iff_isKGroup.mp
      (CFSG.AGLEmbedding.catalogSimpleSections_of_isKProper hS.kProper H hHtop)
  have hxo : orderOf x = 3 := orderOf_eq_prime hx.pow_eq_one hx.ne_one
  have hzo : orderOf z = 3 := orderOf_eq_prime hz.pow_eq_one hz.ne_one
  have hxz : x * z = z * x := mem_centralizer_iff.mp hz.centralizes x hx.mem
  have hpl := SmallRankPlane.of_situation hS hsit hx hz
  have hxnz : x ∉ zpowers z := by
    intro hxZ
    have h1 := Subgroup.card_le_of_le
      (sup_le (zpowers_le.2 hxZ) le_rfl : zpowers x ⊔ zpowers z ≤ zpowers z)
    rw [hpl.card_eq, Nat.card_zpowers, hzo] at h1
    norm_num at h1
  have hB3 : IsPGroup 3 (zpowers x ⊔ zpowers z : Subgroup G) :=
    IsPGroup.of_card (n := 2) hpl.card_eq
  have hBH : zpowers x ⊔ zpowers z ≤ H := hopt.ext.pair.le
  have hB3' : IsPGroup 3 ↥((zpowers x ⊔ zpowers z).subgroupOf H) :=
    hB3.of_equiv (subgroupOfEquivOfLe hBH).symm
  obtain ⟨Q', hQ'⟩ := hB3'.exists_le_sylow
  set Q : Subgroup G := (Q' : Subgroup H).map H.subtype with hQ
  have hQsyl : CFSG.ABGLocalTools.IsSylowOf 3 Q H := ⟨Q', rfl⟩
  have hBQ : zpowers x ⊔ zpowers z ≤ Q := by
    intro b hb
    have hbH : (⟨b, hBH hb⟩ : H) ∈ (zpowers x ⊔ zpowers z).subgroupOf H := hb
    exact ⟨⟨b, hBH hb⟩, hQ' hbH, rfl⟩
  have hQM : Q ≤ M := hopt.sylow_le Q hQsyl.isPGroup hQsyl.le hBQ
  have hΩQ := hΩ Q hQsyl.le hQsyl.isPGroup hBQ
  have hfr : x ∉ (frattini ↥Q).map Q.subtype := x_not_mem_frattini3 hS hsit hx hQsyl.isPGroup
  have hwc : ∀ g ∈ H, g * z * g⁻¹ ∈ zpowers x ⊔ zpowers z → g * z * g⁻¹ ∈ zpowers z :=
    fun g _ hg => conj_mem_zpowers hS hsit hx hz hg
  have hNZ : normalizer (zpowers z : Set G) ⊓ H ≤ M ⊓ H := fun g hg =>
    ⟨normalizer_zpowers_le_of_largeObstruction_empty hS hsit.mem_sigmaA hsit.isCoreMaxLocal
      hsit.largeObstruction_empty hz.mem hz.centralizes hz.ne_one hz.pow_eq_one hg.1, hg.2⟩
  have hcover : ¬ H ≤ (M ⊓ H) ⊔ rankThreePrimeCore 3 H := fun hle =>
    hopt.ext.pair.not_le (hle.trans (sup_le inf_le_left hyp.core_le))
  exact h G 3 H Q (M ⊓ H) x z Nat.prime_three (by norm_num) hKH hxo hzo hxz hxnz hQsyl hBQ hΩQ
    hfr hwc (le_inf hQM hQsyl.le) inf_le_right hNZ hcover

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614B2
