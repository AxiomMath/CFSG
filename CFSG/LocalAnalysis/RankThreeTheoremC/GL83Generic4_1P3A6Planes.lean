module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3PlaneLines
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3SylowLift
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3A6Plane
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1P34f
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3U3Lemma42
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerRank

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

theorem a6_lemma42_of_not_wc (hS : Setting G) (hU0 : FullCoreLocal G) (hD1 : TheoremD1 G)
    (K1 : StronglyEmbeddedRankTwoKFactNoBM) (K2 : StronglyEmbeddedCyclicOuterKFact)
    (K3 : KFactOutCyclic) (K4 : KFactComponentPCoreThree) (hno : NoExcludedSection3 G)
    (hKM : CFSG.AGLEmbeddingD2.KFactM11Three) (hKA : KFactM11TwoSignalizer)
    (hL : KFactsL34Full) (hA1 : A6SylowData) (hA3 : A6BorelCore) (hE1 : KFactL28Three)
    (hE3 : KFactL28BorelCore) (hAct : KFactA6SylowAction) (hp : 3 ∈ rankThreeSigmaA G)
    {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M) {x : G}
    (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsA6Normal M x J)
    (hR : A6Prop34 3 P J x)
    (hwc : ¬ LineWeaklyClosed x ((P : Subgroup G) ⊓ centralizer ({x} : Set G))) :
    A6PointLemma42 3 P M J x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro U hV u huU hux
  by_contra hCu
  obtain ⟨hPM, -⟩ := sylow_le_of_isCoreMaxLocal hS hp hM
  have hxJ : x ∉ J := a6_x_not_mem_J hS hU0 hp hM hgen hJ
  have hxLO : IsLargeObstruction 3 M x := hgen.2.1
  obtain ⟨hxM, hx1, hx3, -, -⟩ := id hxLO
  have hJC := hJ.le_centralizer
  set Q : Subgroup G := (P : Subgroup G) ⊓ centralizer ({x} : Set G) with hQ
  have hQP : Q ≤ (P : Subgroup G) := inf_le_left
  have hQc : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hR.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  set K₀ : Subgroup G := (P : Subgroup G) ⊓ J with hK₀
  have hK₀Q : K₀ ≤ Q := le_inf inf_le_left (inf_le_right.trans hJC)
  have hK₀el : IsElemAbelian 3 K₀ := a6_inf_isElemAbelian hA1 hgen hJ
  have hK₀c : Nat.card K₀ = 3 ^ 2 := (a6_T_data hS hU0 hA1 hp hM hgen hJ).2.2
  have hK₀M : K₀ ≤ M := (hK₀Q.trans hQP).trans hPM
  have hK₀N : normalizer (K₀ : Set G) ≤ M := normalizer_le_of_le_of_two_le_pRank hS hU0 hp hM
    (elementary_isPGroup 3 K₀ hK₀el) hK₀M (le_pRank_of_elemAbelian_card le_rfl hK₀el hK₀c)
  have hK₀x : ∀ t ∈ K₀, ∀ c ∈ zpowers x, t * c = c * t := fun t ht c hc => by
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hc
    exact (Commute.zpow_right (show Commute t x from
      mem_centralizer_singleton_iff.mp (hJC ht.2)) j).eq
  have hnx : ∀ n ∈ centralizer ({x} : Set G), n * x * n⁻¹ = x := fun n hn =>
    mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hn)
  obtain ⟨hUQ, hUel, hUc, hxU, hδ⟩ := hV
  have hUJc : Nat.card ↥(U ⊓ J) = 3 := a6plane_card_inf hJ hxJ hR ⟨hUQ, hUel, hUc, hxU, hδ⟩
  have hu1 : u ≠ 1 := fun h => hux (h ▸ one_mem _)
  have hu3 : u ^ 3 = 1 := hUel.2 u huU
  have hLO : IsLargeObstruction 3 M u := by
    refine ⟨hPM (hQP (hUQ huU)), hu1, hu3, ?_, hCu⟩
    have hQC : Q ≤ centralizer ({u} : Set G) := fun q hq =>
      mem_centralizer_singleton_iff.mpr (hQc q hq u (hUQ huU))
    exact (le_of_eq hgen.2.2.2.symm).trans (pRank_mono 3 (by norm_num) hQC)
  obtain ⟨t, ht, c, hc, rfl⟩ := u3l42_decomp hK₀x (hR.2.1 u (hUQ huU) hu3)
  have ht3 : t ^ 3 = 1 := hK₀el.2 t ht
  have htU : t ∈ U := by
    simpa using U.mul_mem huU (U.inv_mem (zpowers_le.mpr hxU hc))
  have hxK₀ : x ∉ K₀ := fun h => hxJ h.2
  by_cases ht1 : t = 1
  · exact hux (by simpa [ht1] using hc)
  have hxt : x ∉ zpowers t := fun h => hxK₀ (zpowers_le.mpr ht h)
  have htx : t * x = x * t := hK₀x t ht x (mem_zpowers x)
  by_cases hc1 : c = 1
  ·
    rw [hc1, mul_one] at hLO
    have hUJ : zpowers t = U ⊓ J := Subgroup.eq_of_le_of_card_ge
      (zpowers_le.mpr ⟨htU, ht.2⟩) (by rw [hUJc, Nat.card_zpowers, orderOf_eq_prime ht3 ht1])
    unfold LineWeaklyClosed at hwc
    push Not at hwc
    obtain ⟨g, hgle, hgne⟩ := hwc
    have hx₁mem : g * x * g⁻¹ ∈ (zpowers x).map (MulAut.conj g).toMonoidHom :=
      ⟨x, mem_zpowers x, rfl⟩
    have hgJ : (zpowers x).map (MulAut.conj g).toMonoidHom ≤ J :=
      (hR.2.2 g hgle).resolve_left hgne
    have hx₁Q : g * x * g⁻¹ ∈ Q := hgle hx₁mem
    have hx₁K₀ : g * x * g⁻¹ ∈ K₀ := ⟨hx₁Q.1, hgJ hx₁mem⟩
    have hx₁1 : g * x * g⁻¹ ≠ 1 := fun h => hx1 (by simpa using h)
    obtain ⟨h, hhN, hhx⟩ := exists_mem_normalizer_conj hgen.2.2.1 hQc hx₁Q
    have hNQ : normalizer (Q : Set G) ≤ M := normalizer_le_of_le_of_two_le_pRank hS hU0 hp hM
      (P.isPGroup'.to_le hQP) (hQP.trans hPM) (by rw [hgen.2.2.2]; norm_num)
    have hx₁LO : IsLargeObstruction 3 M (g * x * g⁻¹) := by
      have h1 := hxLO.conj (hNQ hhN)
      rw [MulAut.conj_apply, hhx] at h1
      exact h1
    obtain ⟨n, hnC, hnN, hnmv⟩ := a6_exists_moving hAct hgen hJ hx₁K₀ hx₁1
    have hnM : n ∈ M := hK₀N hnN
    have hx₂K₀ : n * (g * x * g⁻¹) * n⁻¹ ∈ K₀ := (mem_normalizer_iff.mp hnN _).mp hx₁K₀
    have hx₂LO : IsLargeObstruction 3 M (n * (g * x * g⁻¹) * n⁻¹) := by
      have h1 := hx₁LO.conj hnM
      rwa [MulAut.conj_apply] at h1
    have hconjline : ∀ g' : G, (zpowers x).map (MulAut.conj g').toMonoidHom =
        zpowers (g' * x * g'⁻¹) := fun g' => by
      rw [MonoidHom.map_zpowers]
      rfl
    have h₁t : zpowers (g * x * g⁻¹) ≠ zpowers t := fun h =>
      hδ g (by rw [hconjline, h, hUJ])
    have h₂t : zpowers (n * (g * x * g⁻¹) * n⁻¹) ≠ zpowers t := fun h =>
      hδ (n * g) (by
        rw [hconjline, ← hUJ, ← h]
        congr 1
        group)
    have h₁₂ : zpowers (g * x * g⁻¹) ≠ zpowers (n * (g * x * g⁻¹) * n⁻¹) :=
      zpowers_ne_of_not_mem hnmv
    have hx₂1 : n * (g * x * g⁻¹) * n⁻¹ ≠ 1 := hx₂LO.2.1
    exact false_of_three_lines hS hU0 hD1 K1 K2 K3 K4 hno hKM hKA hL hA1 hA3 hE1 hE3 hp hM hK₀M
      hK₀el hK₀c hx₁K₀ hx₂K₀ ht hx₁1 hx₂1 ht1 h₁₂ h₁t h₂t hx₁LO hx₂LO hLO
  ·
    obtain ⟨n, hnC, hnN, hninv⟩ := a6_exists_inverting hAct hgen hJ
    have hnM : n ∈ M := hK₀N hnN
    have hyD : t * c ∈ zpowers t ⊔ zpowers x := Subgroup.mul_mem _ (mem_sup_left (mem_zpowers t))
      (mem_sup_right hc)
    have hyk : t * c ∉ zpowers t := fun h => by
      have hc' : c ∈ zpowers t := by
        simpa using Subgroup.mul_mem _ (Subgroup.inv_mem _ (mem_zpowers t)) h
      have hcx : zpowers c = zpowers x :=
        p34_zpowers_eq_of_mem (orderOf_eq_prime hx3 hx1) hc hc1
      have hxc : x ∈ zpowers c := by
        rw [hcx]
        exact mem_zpowers x
      exact hxt (zpowers_le.mpr hc' hxc)
    exact false_of_mixed_pair hS hU0 hD1 K1 K2 K3 K4 hno hKM hKA hL hA1 hA3 hE1 hE3 hp hM hxLO
      (hK₀M ht) ht1 ht3 hxt htx hnM (hnx n hnC) (hninv t ht) hyD hyk hux hLO

end CFSG.LocalAnalysis.RankThreeTheoremC
