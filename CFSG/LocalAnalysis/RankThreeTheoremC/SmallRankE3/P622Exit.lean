module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622ExitKlein
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622K3Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P5IiiPx
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622KxCfg
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62yCommon

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup CFSG.QuasithinUnique.Setup.Family
open CFSG.LocalAnalysis.RankThreeTheoremC.L32Insp
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem p622Exit_hno {x : G} (hbot : rankThreePrimeCore 3 (centralizer ({x} : Set G)) = ⊥) :
    ∀ N : Subgroup ↥(centralizer ({x} : Set G)), N.Normal → Nat.Coprime 3 (Nat.card N) →
      N = ⊥ := by
  intro N hN hcop
  have hle : N.map (centralizer ({x} : Set G)).subtype ≤
      rankThreePrimeCore 3 (centralizer ({x} : Set G)) := by
    unfold rankThreePrimeCore relPPrimeCore
    refine le_sSup ⟨Subgroup.map_subtype_le N, ?_, ?_⟩
    · rw [show (N.map (centralizer ({x} : Set G)).subtype).subgroupOf (centralizer ({x} : Set G))
          = N from Subgroup.comap_map_eq_self_of_injective
            (centralizer ({x} : Set G)).subtype_injective N]
      exact hN
    · rw [Subgroup.card_subtype]
      exact hcop
  rw [hbot, le_bot_iff] at hle
  rw [Subgroup.eq_bot_iff_forall]
  intro n hn
  have hmem : (n : G) ∈ N.map (centralizer ({x} : Set G)).subtype :=
    Subgroup.mem_map.mpr ⟨n, hn, rfl⟩
  rw [hle, Subgroup.mem_bot] at hmem
  exact Subtype.ext hmem

theorem p622Exit_hrk {x : G} (h : CFSG.Open.pRank 3 (centralizer ({x} : Set G)) ≤ 2) :
    ∀ E : Subgroup ↥(centralizer ({x} : Set G)), IsElemAbelian 3 E → Nat.card E ≤ 9 := by
  intro E hE
  obtain ⟨hcomm, hexp⟩ := hE
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hEC : E.map (centralizer ({x} : Set G)).subtype ≤ centralizer ({x} : Set G) :=
    Subgroup.map_subtype_le E
  have hEcomm : IsElemAbelian 3 (E.map (centralizer ({x} : Set G)).subtype) := by
    refine ⟨isMulCommutative_iff.mpr ?_, ?_⟩
    · rintro ⟨a, ha⟩ ⟨b, hb⟩
      obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
      obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hb
      have key := congrArg (fun z : ↥E => ((z : ↥(centralizer ({x} : Set G))) : G))
        (isMulCommutative_iff.mp hcomm ⟨a', ha'⟩ ⟨b', hb'⟩)
      apply Subtype.ext
      simpa using key
    · intro a ha
      obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
      show (centralizer ({x} : Set G)).subtype a' ^ 3 = 1
      rw [← map_pow, hexp a' ha', map_one]
  have hcard : Nat.card (E.map (centralizer ({x} : Set G)).subtype) = Nat.card E :=
    Subgroup.card_subtype _ E
  have hPE : IsPGroup 3 E := by
    refine fun g => ⟨1, ?_⟩
    show g ^ 3 = 1
    exact Subtype.ext (by simpa using hexp (g : ↥(centralizer ({x} : Set G))) g.2)
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hPE
  have hbdd : BddAbove {k : ℕ | ∃ F : Subgroup G,
      F ≤ centralizer ({x} : Set G) ∧ IsElemAbelian 3 F ∧ Nat.card F = 3 ^ k} := by
    refine ⟨Nat.card G, fun k hk => ?_⟩
    obtain ⟨F, -, -, hF⟩ := hk
    have h1 : Nat.card F ≤ Nat.card G := Subgroup.card_le_card_group F
    have h2 : k < 3 ^ k := Nat.lt_pow_self (a := 3) (n := k) (by norm_num)
    have h3 : 3 ^ k ≤ Nat.card G := by rw [← hF]; exact h1
    exact le_trans (le_of_lt h2) h3
  have hmem : n ∈ {k : ℕ | ∃ F : Subgroup G,
      F ≤ centralizer ({x} : Set G) ∧ IsElemAbelian 3 F ∧ Nat.card F = 3 ^ k} :=
    ⟨E.map (centralizer ({x} : Set G)).subtype, hEC, hEcomm, by rw [hcard, hn]⟩
  have hnle : n ≤ CFSG.Open.pRank 3 (centralizer ({x} : Set G)) := le_csSup hbdd hmem
  have hn2 : n ≤ 2 := le_trans hnle h
  calc Nat.card E = 3 ^ n := hn
    _ ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hn2
    _ = 9 := by norm_num

def p622ExitX (x : G) : ↥(centralizer ({x} : Set G)) :=
  ⟨x, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩

theorem p622ExitX_mem_center (x : G) : p622ExitX x ∈ Subgroup.center ↥(centralizer ({x} : Set G)) := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  exact (Subgroup.mem_centralizer_singleton_iff.mp g.2 : (g : G) * x = x * (g : G))

theorem p622Exit_hcube (hS : Setting G) {P : Sylow 3 G} {M : Subgroup G}
    (hsit : SmallRankSituation G 3 P M) {x : G} (hx : SmallRankPoint P M x) :
    ∀ y : ↥(centralizer ({x} : Set G)), (∃ k : ℕ, y ^ 3 ^ k = 1) → y ^ 3 ≠ p622ExitX x := by
  rintro y ⟨k, hk⟩ hy
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hyk : (y : G) ^ 3 ^ k = 1 := by
    have h := congrArg Subtype.val hk
    simpa using h
  have hyx : (y : G) ^ 3 = x := by
    have h := congrArg Subtype.val hy
    simpa [p622ExitX] using h
  have hord : orderOf (y : G) ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hyk
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hord
  have hQ : IsPGroup 3 ↥(Subgroup.zpowers (y : G)) := by
    rw [IsPGroup.iff_card]
    exact ⟨m, by rw [Nat.card_zpowers, hm]⟩
  let q : ↥(Subgroup.zpowers (y : G)) := ⟨(y : G), Subgroup.mem_zpowers _⟩
  have hfr : q ^ 3 ∈ frattini ↥(Subgroup.zpowers (y : G)) :=
    CFSG.SectionRank.Ccomm.pow_mem_frattini hQ q
  have hmem : x ∈ (frattini ↥(Subgroup.zpowers (y : G))).map (Subgroup.zpowers (y : G)).subtype := by
    refine Subgroup.mem_map.mpr ⟨q ^ 3, hfr, ?_⟩
    show ((q ^ 3 : ↥(Subgroup.zpowers (y : G))) : G) = x
    rw [Subgroup.coe_pow]
    exact hyx
  exact x_not_mem_frattini3 hS hsit hx hQ hmem

theorem p622L27Exit_holds : P622L27Exit := by
  intro G _ _ P M x z T S L c hbot e
  obtain ⟨e⟩ := e
  have hsit := c.conf.failure.situation
  have hx := c.conf.failure.point
  have hz := c.conf.failure.central
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hLC : L ≤ centralizer ({x} : Set G) := c.le_C
  haveI hLn : (L.subgroupOf (centralizer ({x} : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLC).mpr c.normC
  let e' : ↥(L.subgroupOf (centralizer ({x} : Set G))) ≃* PSL(3, ZMod 2) :=
    (Subgroup.subgroupOfEquivOfLe hLC).trans e
  have hxc := p622ExitX_mem_center x
  have hx3 : orderOf (p622ExitX x) = 3 := by
    have h3 : orderOf x = 3 := orderOf_eq_prime hx.pow_eq_one hx.ne_one
    exact (Subgroup.orderOf_mk x _).trans h3
  have hno := p622Exit_hno hbot
  have hrk := p622Exit_hrk (pRank_centralizer_le_two3 c.setting hsit hx)
  have hcube := p622Exit_hcube c.setting hsit hx
  refine ⟨?_, p622Exit_structure e' hxc hx3 hno hrk hcube⟩
  let e'' : ↥(L.subgroupOf (centralizer ({x} : Set G))) ≃* GL32 := e'.trans pslEquiv
  have hcent := p622Exit_centralizer_eq e'' hxc hx3 hno hrk hcube
  have hcard := p622Exit_card e'' hx3 hcent
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  have hSC : smallRankS x T ≤ C := inf_le_right
  set z' : ↥C := ⟨z, c.conf.z_mem_centralizer⟩ with hz'
  have hzL' : z' ∈ L.subgroupOf C := c.z_mem
  have hz3' : orderOf z' = 3 := (Subgroup.orderOf_mk z _).trans c.orderOf_z
  have hS2 : IsPGroup 2 (smallRankS x T) := c.conf.S_isPGroup.to_le c.conf.le_S
  have hU2 : IsPGroup 2 ↥((smallRankS x T).subgroupOf C) :=
    hS2.of_injective (Subgroup.subgroupOfEquivOfLe hSC).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hSC).injective
  have hzT : z ∈ normalizer (T : Set G) := c.conf.failure.sylowTwo.normalized hz.mem
  have hzS : z ∈ normalizer ((smallRankS x T : Subgroup G) : Set G) :=
    inf_normalizer_le_normalizer_inf ⟨hzT, Subgroup.le_normalizer c.conf.z_mem_centralizer⟩
  have hzU : z' ∈ normalizer (((smallRankS x T).subgroupOf C : Subgroup ↥C) : Set ↥C) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hSC]
    exact hzS
  have hnc : ∃ y ∈ (smallRankS x T).subgroupOf C, z' * y ≠ y * z' := by
    by_contra hcon
    push Not at hcon
    apply c.conf.failure.R_ne_bot c.setting
    show ⁅zpowers z, smallRankS x T⁆ = ⊥
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer, zpowers_le]
    intro y hy
    have := hcon ⟨y, hSC hy⟩ hy
    have h2 := congrArg Subtype.val this
    exact h2.symm
  obtain ⟨f⟩ := p622Exit_klein e'' hxc hx3 hcent hcard hzL' hz3' hU2 hzU hnc
  exact ⟨(Subgroup.subgroupOfEquivOfLe hSC).symm.trans f⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
