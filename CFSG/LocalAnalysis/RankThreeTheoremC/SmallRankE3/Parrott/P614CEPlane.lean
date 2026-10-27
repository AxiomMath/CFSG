module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627Lines
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank65Plane
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L618OmegaPGroup

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614CE

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem centralizer_conj_singleton (g y : G) :
    centralizer ({g * y * g⁻¹} : Set G) =
      (centralizer ({y} : Set G)).map (MulAut.conj g).toMonoidHom := by
  have hcz : ∀ w : G,
      centralizer ({w} : Set G) = centralizer ((zpowers w : Subgroup G) : Set G) := fun w => by
    rw [zpowers_eq_closure, centralizer_closure]
  rw [hcz, hcz y, centralizer_map_automorphism, MonoidHom.map_zpowers]
  rfl

theorem sit_pRank_centralizer_point_le_two {P : Sylow 3 G} {M : Subgroup G} {x z : G}
    (hsit : Sit P M x z) : CFSG.Open.pRank 3 (centralizer ({x} : Set G)) ≤ 2 := by
  have hPM : (P : Subgroup G) ≤ M := (sylow_le_of_isCoreMaxLocal hsit.setting
    hsit.situation.mem_sigmaA hsit.situation.isCoreMaxLocal).1
  by_contra hc
  exact hsit.situation.largeObstruction_empty x ⟨hPM hsit.point.mem, hsit.point.ne_one,
    hsit.point.pow_eq_one, by omega, hsit.point.not_centralizer_le⟩

theorem sit_pRank_centralizer_le_two_of_mem_plane {P : Sylow 3 G} {M : Subgroup G} {x z : G}
    (hsit : Sit P M x z) {y : G} (hy : y ∈ zpowers x ⊔ zpowers z) (hyz : y ∉ zpowers z) :
    CFSG.Open.pRank 3 (centralizer ({y} : Set G)) ≤ 2 := by
  obtain ⟨g, -, hconj⟩ := exists_mem_normalizer_conj_zpowers hsit.setting hsit.situation
    hsit.point hsit.central hy hyz
  have hcz : ∀ w : G,
      centralizer ({w} : Set G) = centralizer ((zpowers w : Subgroup G) : Set G) := fun w => by
    rw [zpowers_eq_closure, centralizer_closure]
  have hC : centralizer ({y} : Set G) =
      (centralizer ({x} : Set G)).map (MulAut.conj g).toMonoidHom := by
    rw [hcz, ← hconj, ← centralizer_map_automorphism, ← hcz]
  rw [hC, pRank_map_automorphism 3 Nat.prime_three.one_lt]
  exact sit_pRank_centralizer_point_le_two hsit

theorem sit_mem_zpowers_of_conj_mem_plane {P : Sylow 3 G} {M : Subgroup G} {x z : G}
    (hsit : Sit P M x z) {g : G} (hg : g * z * g⁻¹ ∈ zpowers x ⊔ zpowers z) :
    g * z * g⁻¹ ∈ zpowers z := by
  by_contra hgz
  have h2 := sit_pRank_centralizer_le_two_of_mem_plane hsit hg hgz
  have hP3 := (sylow_le_of_isCoreMaxLocal hsit.setting hsit.situation.mem_sigmaA
    hsit.situation.isCoreMaxLocal).2
  have hPz : (P : Subgroup G).map (MulAut.conj g).toMonoidHom ≤
      centralizer ({g * z * g⁻¹} : Set G) := by
    rw [centralizer_conj_singleton]
    refine Subgroup.map_mono fun q hq => ?_
    rw [mem_centralizer_singleton_iff]
    exact mem_centralizer_iff.mp hsit.central.centralizes q hq
  have h3 := pRank_mono 3 Nat.prime_three.one_lt hPz
  rw [pRank_map_automorphism 3 Nat.prime_three.one_lt, hP3] at h3
  omega

theorem sit_normalizer_zpowers_le {P : Sylow 3 G} {M : Subgroup G} {x z : G}
    (hsit : Sit P M x z) {u : G} (huM : u ∈ M) (hu1 : u ≠ 1) (hu3 : u ^ 3 = 1)
    (hr : 3 ≤ CFSG.Open.pRank 3 (M ⊓ centralizer ({u} : Set G))) :
    normalizer ((zpowers u : Subgroup G) : Set G) ≤ M := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsit' := hsit.situation
  have hCM : centralizer ({u} : Set G) ≤ M := by
    by_contra hCM
    exact hsit'.largeObstruction_empty u ⟨huM, hu1, hu3,
      hr.trans (pRank_mono 3 Nat.prime_three.one_lt inf_le_right), hCM⟩
  obtain ⟨E, hE, hEe, hEc⟩ := exists_isElemAbelian_of_le_pRank Nat.prime_three hr
  obtain ⟨S, hES, hSC, hS3, hSidx⟩ := exists_sylow_le_of_isPGroup Nat.prime_three
    (hE.trans inf_le_right) (elementary_isPGroup 3 E hEe)
  have hSsyl : CFSG.ABGLocalTools.IsSylowOf 3 S (centralizer ({u} : Set G)) :=
    CFSG.ABGLocalTools.isSylowOf_iff.mpr ⟨hSC, hS3, hSidx⟩
  have hS3' : 3 ≤ CFSG.Open.pRank 3 S := le_pRank_of_isElemAbelian Nat.prime_three hES hEe hEc
  have hSM : normalizer (S : Set G) ≤ M :=
    normalizer_le_of_le_of_two_le_pRank hsit.setting hsit.u0 hsit'.mem_sigmaA
      hsit'.isCoreMaxLocal hS3 (hSC.trans hCM) (by omega)
  exact (le_sup_normalizer_of_isSylowOf (normalizer_zpowers_le_normalizer_centralizer u)
    hSsyl).trans (sup_le hCM hSM)

theorem mem_of_mem_centralizer_of_pRank_le_two {X E : Subgroup G}
    (hX : CFSG.Open.pRank 3 X ≤ 2) (hEX : E ≤ X) (hEe : IsElemAbelian 3 E)
    (hEc : Nat.card E = 3 ^ 2) {y : G} (hyX : y ∈ X) (hy : y ^ 3 = 1)
    (hyc : y ∈ centralizer (E : Set G)) : y ∈ E := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hyE
  have hcard := CFSG.RankThree.PartOne.Planes.card_sup_zpowers Nat.prime_three E hy hyE
    (mem_centralizer_iff.mp hyc)
  have : CFSG.IsElementaryAbelian 3 E :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 E).2 hEe
  have : CFSG.IsElementaryAbelian 3 (zpowers y) :=
    CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one hy
  have hF : CFSG.IsElementaryAbelian 3 ↥(E ⊔ zpowers y) :=
    CFSG.IsElementaryAbelian.sup_of_le_centralizer (zpowers_le.mpr hyc)
  have h3 : 3 ≤ CFSG.Open.pRank 3 X :=
    le_pRank_of_isElemAbelian Nat.prime_three (sup_le hEX (zpowers_le.mpr hyX))
      ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 _).1 hF)
      (by rw [hcard, hEc]; norm_num)
  omega

theorem sit_exists_plane_centralizer_three {P : Sylow 3 G} {M : Subgroup G} {x z : G}
    (hsit : Sit P M x z) {Q E : Subgroup G} (hQp : IsPGroup 3 Q) (hQM : Q ≤ M) (hEQ : E ≤ Q)
    (hEe : IsElemAbelian 3 E) (hEc : Nat.card E = 3 ^ 2) {q : G} (hqQ : q ∈ Q)
    (hq1 : q ^ 3 = 1) (hqE : q ∉ E) :
    ∃ U : Subgroup G, U ≤ Q ∧ IsElemAbelian 3 U ∧ Nat.card U = 3 ^ 2 ∧
      ∀ u ∈ U, u ≠ 1 → 3 ≤ CFSG.Open.pRank 3 (M ⊓ centralizer ({u} : Set G)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsit' := hsit.situation
  obtain ⟨hPM, hP3⟩ := sylow_le_of_isCoreMaxLocal hsit.setting hsit'.mem_sigmaA
    hsit'.isCoreMaxLocal
  obtain ⟨m, hm⟩ := pGroup_conjugate_into_sylow_within_overgroup 3 Nat.prime_three P M hPM Q
    hQp hQM
  obtain ⟨A₀, hA₀P, hA₀e, hA₀c⟩ := pRank_attained 3 (P : Subgroup G) (by omega)
  rw [hP3] at hA₀c
  have hinj : Function.Injective (MulAut.conj ((m : G)⁻¹)).toMonoidHom :=
    (MulAut.conj ((m : G)⁻¹)).injective
  set R : Subgroup G := (P : Subgroup G).map (MulAut.conj ((m : G)⁻¹)).toMonoidHom with hR
  have hQR : Q ≤ R := by
    intro y hy
    refine ⟨(m : G) * y * (m : G)⁻¹, hm (Subgroup.mem_map_of_mem _ hy), ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hRM : R ≤ M := by
    rintro _ ⟨y, hy, rfl⟩
    exact M.mul_mem (M.mul_mem (M.inv_mem m.2) (hPM hy)) (M.inv_mem (M.inv_mem m.2))
  have hRp : IsPGroup 3 R := by
    obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
    exact IsPGroup.of_card (n := n) (by rw [Subgroup.card_map_of_injective hinj, hn])
  set A : Subgroup G := A₀.map (MulAut.conj ((m : G)⁻¹)).toMonoidHom with hA
  have hAR : A ≤ R := Subgroup.map_mono hA₀P
  have : CFSG.IsElementaryAbelian 3 A₀ :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 A₀).2 hA₀e
  have : CFSG.IsElementaryAbelian 3 A := CFSG.IsElementaryAbelian.map _
  have hAc : Nat.card A = 3 ^ 3 := by rw [hA, Subgroup.card_map_of_injective hinj, hA₀c]
  have hER : E ≤ R := hEQ.trans hQR
  have : CFSG.IsElementaryAbelian 3 E :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 E).2 hEe
  have hA' : CFSG.IsElementaryAbelian 3 (A.subgroupOf R) :=
    CFSG.IsElementaryAbelian.subgroupOf hAR
  have hAc' : Nat.card (A.subgroupOf R) = 3 ^ 3 :=
    (Nat.card_congr (subgroupOfEquivOfLe hAR).toEquiv).trans hAc
  have hE' : CFSG.IsElementaryAbelian 3 (E.subgroupOf R) :=
    CFSG.IsElementaryAbelian.subgroupOf hER
  have hEc' : Nat.card (E.subgroupOf R) = 3 ^ 2 :=
    (Nat.card_congr (subgroupOfEquivOfLe hER).toEquiv).trans hEc
  have hEQ' : E.subgroupOf R ≤ Q.subgroupOf R := fun b hb => hEQ hb
  obtain ⟨U', hU'Q, hU'e, hU'c, hU'W⟩ :=
    CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L618Om.exists_plane_of_omega (by norm_num) hRp
      hA' hAc' hEQ' hE' hEc' (q := ⟨q, hQR hqQ⟩) hqQ (Subtype.ext (by simpa using hq1))
      (fun h => hqE (Subgroup.mem_subgroupOf.mp h))
  have : CFSG.IsElementaryAbelian 3 U' := hU'e
  refine ⟨U'.map R.subtype, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨u, hu, rfl⟩
    exact hU'Q hu
  · exact (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 _).1
      CFSG.IsElementaryAbelian.map_subtype
  · rw [Subgroup.card_map_of_injective R.subtype_injective, hU'c]
  · rintro _ ⟨u, hu, rfl⟩ hu1
    have hu1' : u ≠ 1 := fun h => hu1 (by rw [h, map_one])
    obtain ⟨W, hWc, hWe, hW3⟩ := hU'W u hu hu1'
    have : CFSG.IsElementaryAbelian 3 W := hWe
    have hW'e : IsElemAbelian 3 (W.map R.subtype) :=
      (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 _).1
        CFSG.IsElementaryAbelian.map_subtype
    have hW'le : W.map R.subtype ≤ M ⊓ centralizer ({R.subtype u} : Set G) := by
      rintro _ ⟨w, hw, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨hRM w.2, mem_centralizer_singleton_iff.mpr ?_⟩
      exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp (hWc hw))
    obtain ⟨n, hn⟩ := (elementary_isPGroup 3 _ hW'e).exists_card_eq
    have hcard : 3 ^ 3 ≤ Nat.card (W.map R.subtype) := by
      rw [Subgroup.card_map_of_injective R.subtype_injective]
      exact hW3
    rw [hn] at hcard
    have h3n : 3 ≤ n := (Nat.pow_le_pow_iff_right (by norm_num)).mp hcard
    exact h3n.trans (le_pRank_of_isElemAbelian Nat.prime_three hW'le hW'e hn)

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614CE
