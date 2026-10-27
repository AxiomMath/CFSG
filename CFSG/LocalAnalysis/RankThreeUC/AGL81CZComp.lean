module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CInputs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CZComm
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CZFStar
import CFSG.GH74.GLS.AssemblyComponents
import CFSG.LocalAnalysis.SectionRank.GroupRankTransport

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open CFSG.Open Subgroup

private theorem pRank_coe_eq_open_pRank {G : Type*} [Group G] [Finite G] (p : ℕ) (H : Subgroup G) :
    CFSG.pRank p ↥H = CFSG.Open.pRank p H :=
  (CFSG.SectionRank.pRank_eq_open_pRank_top p ↥H).trans
    (CFSG.SectionRank.pRank_eq_pRank_top_subgroup H).symm

private theorem pRank_top_subgroup_eq_pRank {G : Type*} [Group G] (p : ℕ) :
    CFSG.pRank p ↥(⊤ : Subgroup G) = CFSG.pRank p G :=
  CFSG.pRank_congr_of_mulEquiv (Subgroup.topEquiv (G := G)) p

theorem prime_dvd_card_of_isComponent {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (hO : CFSG.pPrimeCore p X = ⊥) {C : Subgroup X} (hC : CFSG.IsComponent C) :
    p ∣ Nat.card C := by
  by_contra hpdvd
  haveI : Fact p.Prime := ⟨hp⟩
  have hcop : Nat.Coprime p (Nat.card C) := (hp.coprime_iff_not_dvd).mpr hpdvd
  have hle : C ≤ CFSG.pPrimeCore p X :=
    CFSG.GH74.GLS.le_pPrimeCore_of_subnormal p hC.2 hcop
  rw [hO] at hle
  have hbot : C = ⊥ := le_bot_iff.mp hle
  obtain ⟨-, -, a, b, hab⟩ := hC.1
  haveI : Subsingleton C := by
    rw [hbot]
    refine ⟨fun x y => Subtype.ext ?_⟩
    rw [Subgroup.mem_bot.mp x.2, Subgroup.mem_bot.mp y.2]
  exact hab (Subsingleton.elim (a * b) (b * a))

theorem ncard_isComponent_le_three (hk : KFactOmegaNotCentral) {X : Type} [Group X] [Finite X]
    (hX : CFSG.Open.IsKGroup X) (hO : CFSG.pPrimeCore 3 X = ⊥) (hr : pRank 3 (⊤ : Subgroup X) ≤ 3) :
    {C : Subgroup X | CFSG.IsComponent C}.ncard ≤ 3 := by
  classical
  have hfin : ({C : Subgroup X | CFSG.IsComponent C} : Set (Subgroup X)).Finite :=
    Set.toFinite _
  rw [Set.ncard_eq_toFinset_card _ hfin]
  refine (card_le_pRank_of_components Nat.prime_three hfin.toFinset ?_).trans hr
  intro C hC
  rw [Set.Finite.mem_toFinset] at hC
  refine ⟨hC, ?_⟩
  have h3 : 3 ∣ Nat.card C := prime_dvd_card_of_isComponent Nat.prime_three hO hC
  exact hk X hX C hC 3 Nat.prime_three (by norm_num) h3

theorem pRank_pCore_le_two (hk : KFactOmegaNotCentral) {X : Type} [Group X] [Finite X]
    (hX : CFSG.Open.IsKGroup X) (hO : CFSG.pPrimeCore 3 X = ⊥) (hr : pRank 3 (⊤ : Subgroup X) ≤ 3)
    {L : Subgroup X} (hL : CFSG.IsComponent L) : pRank 3 (CFSG.pCore 3 X) ≤ 2 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [pRank_coe_eq_open_pRank]
  obtain ⟨A, hA_le, hAab, hAcard⟩ :=
    CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) (CFSG.pCore 3 X)
  have hAcent : A ≤ centralizer (L : Set X) :=
    hA_le.trans (pCore_le_centralizer_of_isComponent hL)
  have h3 : 3 ∣ Nat.card L := prime_dvd_card_of_isComponent Nat.prime_three hO hL
  obtain ⟨e, heL, hord, hnc⟩ := hk X hX L hL 3 Nat.prime_three (by norm_num) h3
  have hle := add_one_le_pRank_of_le_centralizer Nat.prime_three hAab hAcard hAcent heL hord hnc
  omega

theorem le_normalizer_of_isComponent {X : Type*} [Group X] [Finite X] {d : ℕ} (hd : d.Prime)
    {W : Subgroup X} (hW : IsPGroup d W)
    (hc : {C : Subgroup X | CFSG.IsComponent C}.ncard < d) {C : Subgroup X}
    (hC : CFSG.IsComponent C) : W ≤ normalizer (C : Set X) := by
  let S : Set (Subgroup X) := {C' | CFSG.IsComponent C'}
  have hfin : S.Finite := Set.toFinite S
  let f : ↥W →* MulAut X := (MulAut.conj : X →* MulAut X).comp W.subtype
  letI : MulAction (MulAut X) (Subgroup X) := Subgroup.pointwiseMulAction
  letI : MulAction ↥W (Subgroup X) := MulAction.compHom (Subgroup X) f
  let O : Set (Subgroup X) := MulAction.orbit ↥W C
  have hOsub : O ⊆ S := by
    rintro C' ⟨w, rfl⟩
    change CFSG.IsComponent (C.map (MulAut.conj (w : X)).toMonoidHom)
    exact CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj (w : X)) hC
  have hOfin : O.Finite := hfin.subset hOsub
  haveI : Finite O := hOfin
  haveI : Fact d.Prime := ⟨hd⟩
  obtain ⟨k, hk⟩ := IsPGroup.card_orbit (p := d) (G := ↥W) hW C
  have hcard_le : O.ncard ≤ S.ncard := Set.ncard_le_ncard hOsub hfin
  have hk0 : k = 0 := by
    by_contra hkne
    have hdle : d ≤ O.ncard := by
      have h : d ≤ d ^ k := Nat.le_self_pow hkne d
      rw [← hk, Nat.card_coe_set_eq] at h
      exact h
    exact absurd (lt_of_le_of_lt (hdle.trans hcard_le) hc) (lt_irrefl d)
  have hOcard1 : O.ncard = 1 := by
    rw [← Nat.card_coe_set_eq, hk, hk0, pow_zero]
  obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp hOcard1
  have hCeq : C = a := by
    have : C ∈ O := MulAction.mem_orbit_self C
    rw [ha] at this
    simpa using this
  have hOeq : O = {C} := by rw [ha, ← hCeq]
  intro w hw
  have hwC : (⟨w, hw⟩ : ↥W) • C = C := by
    have hmem : (⟨w, hw⟩ : ↥W) • C ∈ O := MulAction.mem_orbit C (⟨w, hw⟩ : ↥W)
    rw [hOeq] at hmem
    simpa using hmem
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact hwC

theorem IsL34Type.of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : IsL34Type A) : IsL34Type B := by
  obtain ⟨d, hd, ⟨f⟩⟩ := h
  exact ⟨d, hd, ⟨(QuotientGroup.congr (Subgroup.center B) (Subgroup.center A) e.symm
    (Subgroup.map_center_eq e.symm)).trans f⟩⟩

theorem IsA11Type.of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : IsA11Type A) : IsA11Type B := by
  obtain ⟨f⟩ := h
  exact ⟨e.symm.trans f⟩

theorem two_le_pRank_of_isL34Type_or_isA11Type (hk : ZKFacts) {X : Type} [Group X] [Finite X]
    {L : Subgroup X} (hq : CFSG.IsQuasisimple L) (h : IsL34Type ↥L ∨ IsA11Type ↥L) :
    2 ≤ pRank 3 L := by
  rcases h with h34 | h11
  · have h2 := hk.rankL34 ↥L hq h34
    rwa [pRank_top_subgroup_eq_pRank] at h2
  · obtain ⟨e⟩ := h11
    have h2 : 2 ≤ CFSG.pRank 3 ↥(⊤ : Subgroup (alternatingGroup (Fin 11))) := hk.rankA11
    rw [pRank_top_subgroup_eq_pRank] at h2
    rw [CFSG.pRank_congr_of_mulEquiv e 3]
    exact h2

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
