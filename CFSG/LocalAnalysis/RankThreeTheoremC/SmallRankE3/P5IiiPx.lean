module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P5IiiBase
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesL630FivePx
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62yCommon
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LieType.SeitzGeneration.HeisTorusU87Arith
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesL630Steps
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627Lines
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open scoped commutatorElement
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L630

variable {G : Type} [Group G] [Finite G]

theorem exists_elemAbelian_cube_of_sylow3 (hS : Setting G) {p : ℕ} {P : Sylow p G}
    {M : Subgroup G} (hsit : SmallRankSituation G p P M) (R : Sylow p G) :
    ∃ A : Subgroup G, A ≤ (R : Subgroup G) ∧ CFSG.IsElementaryAbelian p A ∧
      Nat.card A = p ^ 3 := by
  have hprime : p.Prime := sigmaA_prime p hsit.mem_sigmaA
  have h3 := selected_sylow_rank_at_least_three hS.rank p hsit.mem_sigmaA R
  obtain ⟨E, hER, hE, hEc⟩ := CFSG.SectionRank.exists_pRank hprime.one_lt (R : Subgroup G)
  have hdvd : p ^ 3 ∣ Nat.card E := hEc ▸ pow_dvd_pow p (by omega)
  obtain ⟨A, hAc, -, hAE⟩ :=
    Sylow.exists_subgroup_card_pow_prime_le_le hprime (H := ⊥) (L := E) (by simp) hdvd bot_le
  exact ⟨A, hAE.trans hER,
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p A).2
      (CFSG.Open.IsElemAbelian.mono hE hAE), hAc⟩

theorem pRank_centralizer_le_two3 (hS : Setting G) {p : ℕ} {P : Sylow p G} {M : Subgroup G}
    (hsit : SmallRankSituation G p P M) {x : G} (hx : SmallRankPoint P M x) :
    CFSG.Open.pRank p (centralizer ({x} : Set G)) ≤ 2 := by
  by_contra h
  have hPM : (P : Subgroup G) ≤ M :=
    (sylow_le_of_isCoreMaxLocal hS hsit.mem_sigmaA hsit.isCoreMaxLocal).1
  exact hsit.largeObstruction_empty x
    ⟨hPM hx.mem, hx.ne_one, hx.pow_eq_one, by omega, hx.not_centralizer_le⟩

theorem x_not_mem_frattini3 (hS : Setting G) {p : ℕ} {P : Sylow p G} {M : Subgroup G}
    (hsit : SmallRankSituation G p P M) {x : G} (hx : SmallRankPoint P M x) {Q : Subgroup G}
    (hQ : IsPGroup p Q) : x ∉ (frattini ↥Q).map Q.subtype := by
  classical
  have hprime : p.Prime := sigmaA_prime p hsit.mem_sigmaA
  haveI : Fact p.Prime := ⟨hprime⟩
  rintro ⟨q, hqfr, hqx⟩
  obtain ⟨R, hQR⟩ := hQ.exists_le_sylow
  have hxR : x ∈ (R : Subgroup G) := hQR (hqx ▸ q.2)
  obtain ⟨A, hAR, hAe, hAc⟩ := exists_elemAbelian_cube_of_sylow3 hS hsit R
  set e := (Subgroup.subgroupOfEquivOfLe hQR).symm with he
  have hxQ : ∃ h : (⟨x, hxR⟩ : ↥(R : Subgroup G)) ∈ Q.subgroupOf (R : Subgroup G),
      (⟨⟨x, hxR⟩, h⟩ : ↥(Q.subgroupOf (R : Subgroup G))) ∈
        frattini ↥(Q.subgroupOf (R : Subgroup G)) := by
    have h1 : (⟨x, hxR⟩ : ↥(R : Subgroup G)) ∈ Q.subgroupOf (R : Subgroup G) :=
      show x ∈ Q from hqx ▸ q.2
    refine ⟨h1, ?_⟩
    have h2 : e q ∈ frattini ↥(Q.subgroupOf (R : Subgroup G)) :=
      Subgroup.mem_comap.mp (frattini_le_comap_frattini_of_surjective (φ := e.toMonoidHom)
        e.surjective (SetLike.mem_coe.mp hqfr))
    have h3 : e q = ⟨⟨x, hxR⟩, h1⟩ := Subtype.ext (Subtype.ext hqx)
    rwa [h3] at h2
  have hA' : CFSG.IsElementaryAbelian p ↥(A.subgroupOf (R : Subgroup G)) :=
    CFSG.IsElementaryAbelian.subgroupOf hAR
  have hAc' : Nat.card ↥(A.subgroupOf (R : Subgroup G)) = p ^ 3 :=
    (Nat.card_congr (subgroupOfEquivOfLe hAR).toEquiv).trans hAc
  have hxp : (⟨x, hxR⟩ : ↥(R : Subgroup G)) ^ p = 1 := Subtype.ext hx.pow_eq_one
  obtain ⟨E, hEC, hEe, hE3⟩ := exists_centralizer_rank_three_of_mem_frattini (sigmaA_odd p hsit.mem_sigmaA)
    R.isPGroup' hxp hxQ hA' hAc'
  have hE : IsElemAbelian p (E.map (R : Subgroup G).subtype) := by
    have h := CFSG.IsElementaryAbelian.map_subtype (p := p) (K := (R : Subgroup G)) (H := E)
    exact ⟨h.toIsMulCommutative, fun y hy => CFSG.elemPow_eq_one_of_isElementaryAbelian y hy⟩
  have hEC' : E.map (R : Subgroup G).subtype ≤ centralizer ({x} : Set G) := by
    rintro _ ⟨e, he, rfl⟩
    have h := mem_centralizer_singleton_iff.mp (hEC he)
    exact mem_centralizer_singleton_iff.mpr (congrArg Subtype.val h)
  have hEp : IsPGroup p (E.map (R : Subgroup G).subtype) :=
    fun y => ⟨1, Subtype.ext (by simpa using hE.2 y y.2)⟩
  obtain ⟨n, hn⟩ := hEp.exists_card_eq
  have hn2 : n ≤ 2 := (CFSG.SectionRank.le_pRank hprime.one_lt hEC' hE hn).trans
    (pRank_centralizer_le_two3 hS hsit hx)
  have hcard : p ^ 3 ≤ Nat.card (E.map (R : Subgroup G).subtype) := by
    rw [card_map_of_injective (R : Subgroup G).subtype_injective]
    exact hE3
  rw [hn] at hcard
  have := (Nat.pow_le_pow_iff_right hprime.one_lt).mp hcard
  omega


theorem px_eq_plane3 {P : Sylow 5 G} {M : Subgroup G} {x z : G} {T : Subgroup G}
    (hS : Setting G) (hsit : SmallRankSituation G 5 P M) (hx : SmallRankPoint P M x)
    (hz : SmallRankCentral P z) (hT : SmallRankSylowTwo P M T)
    (hR : smallRankIsQ8D8 (smallRankR x z T)) (hK : KFactAutQ8D8Five) :
    (P : Subgroup G) ⊓ centralizer ({x} : Set G) = zpowers x ⊔ zpowers z := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hB : CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankPlane 5 (P : Subgroup G) x z :=
    SmallRankPlane.of_situation hS hsit hx hz
  have hBcard : Nat.card ↥(zpowers x ⊔ zpowers z) = 5 ^ 2 := hB.card_eq
  have hx1 : x ≠ 1 := hx.ne_one
  have hx5 : x ^ 5 = 1 := hx.pow_eq_one
  have hz5 : z ^ 5 = 1 := hz.pow_eq_one
  have hz1 : z ≠ 1 := hz.ne_one
  have hxP : x ∈ (P : Subgroup G) := hx.mem
  have hzP : z ∈ (P : Subgroup G) := hz.mem
  have hxz : x * z = z * x := mem_centralizer_iff.mp hz.centralizes x hxP
  have hcard5 : Nat.card (zpowers x) = 5 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hx5 hx1]
  set Px : Subgroup G := (P : Subgroup G) ⊓ centralizer ({x} : Set G) with hPxdef
  have hPxpg : IsPGroup 5 Px := P.isPGroup'.to_le inf_le_left
  have hxPx : x ∈ Px := ⟨hxP, mem_centralizer_singleton_iff.mpr rfl⟩
  have hzPx : z ∈ Px := ⟨hzP, mem_centralizer_singleton_iff.mpr hxz.symm⟩
  set B : Subgroup G := zpowers x ⊔ zpowers z with hBdef
  have hxB : x ∈ B := mem_sup_left (mem_zpowers x)
  have hzB' : z ∈ B := mem_sup_right (mem_zpowers z)
  have hBPx : B ≤ Px := sup_le (zpowers_le.mpr hxPx) (zpowers_le.mpr hzPx)
  have hBcent : ∀ y ∈ Px, B ≤ centralizer ({y} : Set G) := by
    intro y hy
    have hyx : y * x = x * y := mem_centralizer_singleton_iff.mp hy.2
    have hyz : y * z = z * y := mem_centralizer_iff.mp hz.centralizes y hy.1
    refine sup_le (zpowers_le.mpr ?_) (zpowers_le.mpr ?_)
    · exact mem_centralizer_singleton_iff.mpr hyx.symm
    · exact mem_centralizer_singleton_iff.mpr hyz.symm
  have hSC : ∀ y ∈ Px, y ^ 5 = 1 → y ∈ B := by
    intro y hy hy5
    refine hB.mem_of_mem_centralizer y (mem_centralizer_iff.mpr ?_) hy5
    intro b hb
    exact mem_centralizer_singleton_iff.mp (hBcent y hy hb)
  set R : Subgroup G := smallRankR x z T with hRdef
  set S : Subgroup G := smallRankS x T with hSdef
  have hRcomm : ⁅S, zpowers z⁆ = R := (smallRankR_eq_comm x z T).symm
  have hzS : zpowers z ≤ normalizer (S : Set G) := (Prop627Failure.mk_five hsit hx hz hT).z_le_normalizer_S
  have hS2 : IsPGroup 2 S := hT.isPGroup.to_inf_left
  have hcomp : ¬ 5 ∣ Nat.card S := not_five_dvd_card_of_isPGroup_two hS2
  have hpgz : IsPGroup 5 (zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime hz5 hz1]; norm_num)
  have hRz : ⁅R, zpowers z⁆ = R := commutator_smallRankR_zpowers hpgz hcomp hzS
  have hRne : R ≠ ⊥ := by
    obtain ⟨A, A', ⟨eA⟩, -, -, hsup, -⟩ := hR
    intro h
    have hAle : A ≤ R := le_sup_left.trans hsup.le
    have hAbot : A = ⊥ := eq_bot_iff.mpr (h ▸ hAle)
    have hA8 : Nat.card A = 8 := by
      rw [Nat.card_congr eA.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    rw [hAbot, Subgroup.card_bot] at hA8
    norm_num at hA8
  have hxz_cent : zpowers z ≤ centralizer ({x} : Set G) :=
    zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hxz.symm)
  have hRC : R ≤ centralizer ({x} : Set G) := by
    rw [← hRcomm, Subgroup.commutator_le]
    intro s hs a ha
    have hsC : s ∈ centralizer ({x} : Set G) := hs.2
    have haC : a ∈ centralizer ({x} : Set G) := hxz_cent ha
    have hCx := (centralizer ({x} : Set G)).mul_mem
      ((centralizer ({x} : Set G)).mul_mem ((centralizer ({x} : Set G)).mul_mem hsC haC)
        ((centralizer ({x} : Set G)).inv_mem hsC)) ((centralizer ({x} : Set G)).inv_mem haC)
    exact hCx
  have hxR : x ∈ centralizer (R : Set G) :=
    mem_centralizer_iff.mpr (fun r hr => mem_centralizer_singleton_iff.mp (hRC hr))
  have hPxR : Px ≤ normalizer (R : Set G) := by
    intro y hy
    have hyT : y ∈ normalizer (T : Set G) := hT.normalized hy.1
    have hyC : y ∈ normalizer ((centralizer ({x} : Set G) : Subgroup G) : Set G) :=
      mem_normalizer_centralizer_singleton (mem_centralizer_singleton_iff.mp hy.2)
    have hyS : y ∈ normalizer (S : Set G) := mem_normalizer_inf_of hyT hyC
    have hyZ : y ∈ normalizer ((zpowers z : Subgroup G) : Set G) :=
      centralizer_singleton_le_normalizer_zpowers z
        (mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hz.centralizes y hy.1))
    rw [← hRcomm]
    exact mem_normalizer_commutator' hyS hyZ
  set φ : Px →* MulAut R := (Subgroup.normalizerMonoidHom R).comp (Subgroup.inclusion hPxR)
    with hφdef
  have hφ_apply : ∀ g : Px, φ g = Subgroup.normalizerMonoidHom R ⟨(g : G), hPxR g.2⟩ :=
    fun g => rfl
  set K0G : Subgroup G := Px ⊓ centralizer (R : Set G) with hK0def
  have hK0_ker : K0G = φ.ker.map Px.subtype := by
    ext g
    constructor
    · intro hg
      refine ⟨⟨g, hg.1⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, MonoidHom.mem_ker, hφ_apply, normalizerMonoidHom_eq_one_iff]
      exact hg.2
    · rintro ⟨h, hh, rfl⟩
      rw [SetLike.mem_coe, MonoidHom.mem_ker, hφ_apply, normalizerMonoidHom_eq_one_iff] at hh
      exact ⟨h.2, hh⟩
  have hKcard : Nat.card φ.ker = Nat.card K0G := by
    rw [hK0_ker, Subgroup.card_map_of_injective Px.subtype_injective]
  have hK0Px : K0G ≤ Px := inf_le_left
  have hK0pg : IsPGroup 5 K0G := hPxpg.to_le hK0Px
  have hK0_elt : ∀ g ∈ K0G, g ^ 5 = 1 → g ∈ zpowers x := by
    intro g hg hg5
    have hgPx : g ∈ Px := hg.1
    have hgR : g ∈ centralizer (R : Set G) := hg.2
    have hgB : g ∈ B := hSC g hgPx hg5
    by_contra hgx
    have hgcomm : ∀ e ∈ zpowers x, e * g = g * e := fun e he =>
      mem_centralizer_singleton_iff.mp (hBcent g hgPx ((zpowers_le.mpr hxB) he))
    have hcard := CFSG.RankThree.PartOne.Planes.card_sup_zpowers (by norm_num : Nat.Prime 5)
      (zpowers x) hg5 hgx hgcomm
    rw [hcard5] at hcard
    have hle : zpowers x ⊔ zpowers g ≤ B :=
      sup_le (zpowers_le.mpr hxB) (zpowers_le.mpr hgB)
    have heq : zpowers x ⊔ zpowers g = B :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hBcard]; norm_num)
    have hzC : z ∈ centralizer (R : Set G) := by
      have hzB : z ∈ zpowers x ⊔ zpowers g := heq ▸ hzB'
      have hle' : zpowers x ⊔ zpowers g ≤ centralizer (R : Set G) :=
        sup_le (zpowers_le.mpr hxR) (zpowers_le.mpr hgR)
      exact hle' hzB
    have hRzbot : ⁅R, zpowers z⁆ = ⊥ := by
      rw [commutator_eq_bot_iff_le_centralizer]
      intro r hr
      rw [mem_centralizer_iff]
      intro w hw
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hw
      have hcr : Commute z r := (mem_centralizer_iff.mp hzC r hr).symm
      exact (Commute.zpow_left hcr k).eq
    apply hRne
    rw [← hRz, hRzbot]
  have hxK0 : x ∈ K0G := ⟨hxPx, hxR⟩
  have hzK0 : zpowers x ≤ K0G := zpowers_le.mpr hxK0
  haveI : Fact (IsPGroup 5 Px) := ⟨hPxpg⟩
  have hcyc : IsCyclic K0G := by
    refine CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6Delta.isCyclic_of_pow_eq_one_mem
      (by norm_num) hK0pg ((zpowers x).subgroupOf K0G) ?_ ?_
    · rw [Nat.card_congr (subgroupOfEquivOfLe hzK0).toEquiv, hcard5]
    · intro g hg
      have hg5 : (g : G) ^ 5 = 1 := by
        have := congrArg Subtype.val hg
        simpa using this
      exact Subgroup.mem_subgroupOf.mpr (hK0_elt g g.2 hg5)
  have hK0le : Nat.card K0G ≤ 5 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hK0pg
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · rw [hk]
      interval_cases k <;> norm_num
    · exfalso
      obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := K0G)
      rw [hk] at hg
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
      have hgG : (g : G) ∈ K0G := g.2
      have hord : orderOf (g : G) = 5 ^ (j + 2) := by
        rw [Subgroup.orderOf_coe, hg]
      have hg1 : (g : G) ^ (5 ^ (j + 2)) = 1 := by
        rw [← hord]
        exact pow_orderOf_eq_one _
      have ha₂5 : ((g : G) ^ (5 ^ j)) ^ 5 = (g : G) ^ (5 ^ (j + 1)) := by
        rw [← pow_mul, pow_succ]
      have ha₁5 : ((g : G) ^ (5 ^ (j + 1))) ^ 5 = 1 := by
        rw [← pow_mul, ← pow_succ]
        exact hg1
      have ha₁1 : (g : G) ^ (5 ^ (j + 1)) ≠ 1 := by
        intro h
        have hdvd : orderOf (g : G) ∣ 5 ^ (j + 1) := orderOf_dvd_of_pow_eq_one h
        rw [hord] at hdvd
        have h1 := Nat.le_of_dvd (by positivity) hdvd
        have h2 : 5 ^ (j + 1) < 5 ^ (j + 2) := Nat.pow_lt_pow_right (by norm_num) (by omega)
        omega
      have ha₁ord : orderOf ((g : G) ^ (5 ^ (j + 1))) = 5 := orderOf_eq_prime ha₁5 ha₁1
      have ha₁K : (g : G) ^ (5 ^ (j + 1)) ∈ K0G := K0G.pow_mem hgG _
      have ha₁x : (g : G) ^ (5 ^ (j + 1)) ∈ zpowers x := hK0_elt _ ha₁K ha₁5
      have h5a : Nat.card (zpowers ((g : G) ^ (5 ^ (j + 1)))) = 5 := by
        rw [Nat.card_zpowers, ha₁ord]
      have hza : zpowers ((g : G) ^ (5 ^ (j + 1))) = zpowers x := by
        apply Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr ha₁x)
        rw [hcard5, h5a]
      have hxa : x ∈ zpowers ((g : G) ^ (5 ^ (j + 1))) := by
        rw [hza]
        exact mem_zpowers x
      obtain ⟨t, ht⟩ := mem_zpowers_iff.mp hxa
      have hcomm5 : ∀ (a : G) (t : ℤ) (n : ℕ), (a ^ t) ^ n = (a ^ n) ^ t := by
        intro a t n
        rw [← zpow_natCast, ← zpow_mul, ← zpow_natCast, ← zpow_mul, mul_comm]
      have ha₂K : (g : G) ^ (5 ^ j) ∈ K0G := K0G.pow_mem hgG _
      have hxpow : ((((g : G) ^ (5 ^ j)) ^ t) ^ (5 : ℕ)) = ((g : G) ^ (5 ^ (j + 1))) ^ t := by
        rw [hcomm5, ha₂5]
      have hxeq : ((((g : G) ^ (5 ^ j)) ^ t) ^ (5 : ℕ)) = x := by
        rw [hxpow, ht]
      have hfr := pth_power_mem_frattini_of_isPGroup (p := 5)
        (⟨((g : G) ^ (5 ^ j)) ^ t, Px.zpow_mem (hK0Px ha₂K) t⟩ : Px)
      have heq : (⟨((g : G) ^ (5 ^ j)) ^ t, Px.zpow_mem (hK0Px ha₂K) t⟩ : Px) ^ 5 =
          ⟨x, hxPx⟩ := Subtype.ext (by simpa using hxeq)
      rw [heq] at hfr
      exact x_not_mem_frattini3 hS hsit hx hPxpg (Subgroup.mem_map.mpr ⟨⟨x, hxPx⟩, hfr, rfl⟩)
  have hrange : Nat.card φ.range ≤ 5 := by
    have hR' : smallRankIsQ8D8 (⊤ : Subgroup ↥R) := by
      apply smallRankIsQ8D8_of_map R.subtype R.subtype_injective
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
      exact hR
    have hTop : IsPGroup 5 (⊤ : Subgroup Px) := hPxpg.to_subgroup ⊤
    have himg : IsPGroup 5 ((⊤ : Subgroup Px).map φ) := IsPGroup.map hTop φ
    rw [← MonoidHom.range_eq_map] at himg
    exact hK ↥R hR' φ.range himg
  have hindex : φ.ker.index = Nat.card φ.range := Subgroup.index_ker φ
  have hPxcard : Nat.card Px ≤ 25 := by
    have h := Subgroup.index_mul_card φ.ker
    rw [hindex] at h
    have h2 : Nat.card φ.ker ≤ 5 := by
      rw [hKcard]
      exact hK0le
    calc Nat.card Px = Nat.card φ.range * Nat.card φ.ker := h.symm
      _ ≤ 5 * 5 := Nat.mul_le_mul hrange h2
      _ = 25 := by norm_num
  have h25 : (5 : ℕ) ^ 2 = 25 := by norm_num
  exact (Subgroup.eq_of_le_of_card_ge hBPx (by rw [hBcard, h25]; exact hPxcard)).symm


end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
