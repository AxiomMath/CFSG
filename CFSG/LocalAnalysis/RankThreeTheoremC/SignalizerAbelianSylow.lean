module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Basic
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.PrimeComplementCore
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.ReducedLayer
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericCaseSetup
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.LocalHallConfinement
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Theorem5_1

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem le_of_normalizer_inf_Op_p'p_le_of_sylow {p : ℕ} [Fact p.Prime] {M H : Subgroup G}
    (T : Sylow p H) (hKM : (CFSG.pPrimeCore p H).map H.subtype ≤ M)
    (hNR : normalizer ((((T : Subgroup H) ⊓ CFSG.Op_p'p p H).map H.subtype : Subgroup G) : Set G)
      ≤ M) : H ≤ M := by
  classical
  have hprime : p.Prime := Fact.out
  have hK₀n : (CFSG.pPrimeCore p H).Normal := CFSG.pPrimeCore_normal
  have hK₀L₀ : CFSG.pPrimeCore p H ≤ CFSG.Op_p'p p H := CFSG.ABGLocalTools.pPrimeCore_le_Op_p'p
  obtain ⟨R₁, hR₁⟩ := CFSG.Glauberman.sylow_inf_normal T (N := CFSG.Op_p'p p H)
  have hR₁map : (R₁ : Subgroup (CFSG.Op_p'p p H)).map (CFSG.Op_p'p p H).subtype =
      ((T : Subgroup H) ⊓ CFSG.Op_p'p p H) := by
    rw [hR₁, map_subgroupOf_eq_of_le inf_le_right]
  set Q₀ : Subgroup H := (T : Subgroup H) ⊓ CFSG.Op_p'p p H with hQ₀
  have hL₀eq : Q₀ ⊔ CFSG.pPrimeCore p H = CFSG.Op_p'p p H := by
    have hquot : IsPGroup p (CFSG.Op_p'p p H ⧸ (CFSG.pPrimeCore p H).subgroupOf
        (CFSG.Op_p'p p H)) := by
      intro y
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
      have hx : QuotientGroup.mk' (CFSG.pPrimeCore p H) (x : H) ∈
          CFSG.pCore p (H ⧸ CFSG.pPrimeCore p H) := x.2
      obtain ⟨n, hn⟩ := CFSG.pCore_isPGroup ⟨_, hx⟩
      refine ⟨n, ?_⟩
      have hn' : (QuotientGroup.mk' (CFSG.pPrimeCore p H) (x : H)) ^ p ^ n = 1 :=
        congrArg Subtype.val hn
      rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hn'
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_subgroupOf]
      simpa using hn'
    have hsup := normal_subgroup_sup_sylow_eq_top_of_pGroup_quotient p hprime
      ((CFSG.pPrimeCore p H).subgroupOf (CFSG.Op_p'p p H)) inferInstance hquot R₁
    have himage := congrArg (fun S : Subgroup (CFSG.Op_p'p p H) =>
      S.map (CFSG.Op_p'p p H).subtype) hsup
    rw [Subgroup.map_sup, hR₁map, map_subgroupOf_eq_of_le hK₀L₀, ← MonoidHom.range_eq_map,
      range_subtype] at himage
    exact himage
  have hfrat := Sylow.normalizer_sup_eq_top R₁
  rw [hR₁map] at hfrat
  have htop : (⊤ : Subgroup H) ≤ normalizer (Q₀ : Set H) ⊔ CFSG.pPrimeCore p H := by
    rw [← hfrat]
    refine sup_le le_sup_left ?_
    rw [← hL₀eq]
    exact sup_le (le_sup_of_le_left le_normalizer) le_sup_right
  intro h hh
  have himage : h ∈ (normalizer (Q₀ : Set H) ⊔ CFSG.pPrimeCore p H).map H.subtype :=
    ⟨⟨h, hh⟩, htop (mem_top _), rfl⟩
  rw [Subgroup.map_sup] at himage
  exact (sup_le ((map_subtype_le_normalizer_map_subtype le_rfl).trans hNR) hKM) himage

theorem le_of_abelian_sylow {p : ℕ} (hp : p ∈ rankThreeSigmaA G)
    {P : Sylow p G} {M : Subgroup G} (hM : IsCoreMaxLocal p P M) {H : Subgroup G}
    (T : Sylow p H) (hTP : (T : Subgroup H).map H.subtype ≤ (P : Subgroup G))
    (h3 : 3 ≤ CFSG.Open.pRank p ((T : Subgroup H).map H.subtype))
    (hKM : (CFSG.pPrimeCore p H).map H.subtype ≤ M)
    (hTab : ∀ a b : H, a ∈ (T : Subgroup H) → b ∈ (T : Subgroup H) → a * b = b * a)
    (hcon : HasPrimeConstraint (G := H) p) : H ≤ M := by
  classical
  have hprime := sigmaA_prime p hp
  have : Fact p.Prime := ⟨hprime⟩
  have hIsP := isPConstrained_of_hasPrimeConstraint hcon
  obtain ⟨R₁, hR₁⟩ := CFSG.Glauberman.sylow_inf_normal T (N := CFSG.Op_p'p p H)
  have hR₁map : (R₁ : Subgroup (CFSG.Op_p'p p H)).map (CFSG.Op_p'p p H).subtype =
      ((T : Subgroup H) ⊓ CFSG.Op_p'p p H) := by
    rw [hR₁, map_subgroupOf_eq_of_le inf_le_right]
  have hcent := hIsP _ ⟨R₁, hR₁map⟩
  have hTle : (T : Subgroup H) ≤ CFSG.Op_p'p p H := fun t ht =>
    hcent (mem_centralizer_iff.mpr fun q hq => hTab q t hq.1 ht)
  refine le_of_normalizer_inf_Op_p'p_le_of_sylow T hKM ?_
  rw [inf_eq_left.mpr hTle]
  have h3S : 3 ≤ CFSG.Open.pRank p
      ((T : Subgroup H).map H.subtype ⊔
        ((P : Subgroup G) ⊓ centralizer (((T : Subgroup H).map H.subtype : Subgroup G) : Set G))) :=
    h3.trans (pRank_mono p hprime.one_lt le_sup_left)
  exact (aschCore_normalizer_le 2 p (P : Subgroup G) _ hTP (by omega) h3S).trans hM.2

theorem centralizer_le_of_abelian_sylow (hS : Setting G) {p : ℕ} (hp : p ∈ rankThreeSigmaA G)
    {P : Sylow p G} {M : Subgroup G} (hM : IsCoreMaxLocal p P M) {u : G}
    (T : Sylow p (centralizer ({u} : Set G)))
    (hTP : (T : Subgroup (centralizer ({u} : Set G))).map (centralizer ({u} : Set G)).subtype ≤
      (P : Subgroup G))
    (h3 : 3 ≤ CFSG.Open.pRank p ((T : Subgroup (centralizer ({u} : Set G))).map
      (centralizer ({u} : Set G)).subtype))
    (hTab : ∀ a b : centralizer ({u} : Set G), a ∈ (T : Subgroup (centralizer ({u} : Set G))) →
      b ∈ (T : Subgroup (centralizer ({u} : Set G))) → a * b = b * a)
    (hcon : HasPrimeConstraint (G := centralizer ({u} : Set G)) p) :
    centralizer ({u} : Set G) ≤ M := by
  have hprime := sigmaA_prime p hp
  have h3' : 3 ≤ CFSG.Open.pRank p ((P : Subgroup G) ⊓ centralizer ({u} : Set G)) :=
    h3.trans (pRank_mono p hprime.one_lt (le_inf hTP (map_subtype_le _)))
  exact le_of_abelian_sylow hp hM T hTP h3 (pPrimeCoreIn_centralizer_le hS hp hM h3') hTab hcon

end CFSG.LocalAnalysis.RankThreeTheoremC
