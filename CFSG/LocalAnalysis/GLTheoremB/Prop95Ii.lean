module

public import CFSG.LocalAnalysis.GLTheoremB.Prop95Parts
import CFSG.LocalAnalysis.GLTheoremB.Prop95Setup
import CFSG.LocalAnalysis.GLTheoremB.CentralizerLift
import CFSG.LocalAnalysis.ComponentClassification.SmallLocalThompson
public import CFSG.LocalAnalysis.GLTheoremB.PCompBasics

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Parts

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

section Transport

variable {G : Type*} [Group G]

theorem isPGroup_barX {r p : ℕ} {M H : Subgroup G} (hH : IsPGroup r H) (hHM : H ≤ M) :
    IsPGroup r (barX p M H) :=
  (hH.of_equiv (Subgroup.subgroupOfEquivOfLe hHM).symm).map _

theorem barX_le_iff {p : ℕ} {M S : Subgroup G} (hSM : S ≤ M)
    {C : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)} :
    barX p M S ≤ C ↔
      S ≤ (C.comap (QuotientGroup.mk' (GLAPPrimeCore p ↥M))).map M.subtype := by
  constructor
  · intro h x hx
    exact ⟨⟨x, hSM hx⟩, h ⟨⟨x, hSM hx⟩, (Subgroup.mem_subgroupOf).2 hx, rfl⟩, rfl⟩
  · rintro h _ ⟨y, hy, rfl⟩
    obtain ⟨k, hk, hky⟩ := h ((Subgroup.mem_subgroupOf).1 hy)
    have : k = y := Subtype.ext hky
    exact this ▸ hk

theorem isPGroup_zpowers_of_pow_eq_one' {p : ℕ} {X : Type*} [Group X] {x : X} (hx : x ^ p = 1) :
    IsPGroup p (Subgroup.zpowers x) :=
  IsPGroup.of_card_dvd_pow (n := 1) (by
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one hx)

end Transport

section Key

variable {G : Type*} [Group G] [Finite G]

theorem barX_pCoreOf_centralizer_le {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {M : Subgroup G}
    {d : G} (hdM : d ∈ M) (hdp : d ^ p = 1)
    (hHM : pCoreOf 2 (Subgroup.centralizer ({d} : Set G)) ≤ M) :
    barX p M (pCoreOf 2 (Subgroup.centralizer ({d} : Set G))) ≤
      Subgroup.centralizer
        ((CFSG.Open.pCore p (↥M ⧸ GLAPPrimeCore p ↥M) : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) :
          Set (↥M ⧸ GLAPPrimeCore p ↥M)) := by
  have hpF : Fact p.Prime := ⟨hp⟩
  have h2F : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H : Subgroup G := pCoreOf 2 (Subgroup.centralizer ({d} : Set G)) with hH
  set db : ↥M ⧸ GLAPPrimeCore p ↥M := QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨d, hdM⟩ with hdb
  have hdbp : db ^ p = 1 := by
    rw [hdb, ← map_pow]
    have h1 : (⟨d, hdM⟩ : ↥M) ^ p = 1 := Subtype.ext (by simpa using hdp)
    rw [h1, map_one]
  have hT : IsPGroup p (Subgroup.zpowers db) := isPGroup_zpowers_of_pow_eq_one' hdbp
  have hdT : IsPGroup p (Subgroup.zpowers d) := isPGroup_zpowers_of_pow_eq_one' hdp
  have hA2 : IsPGroup 2 (barX p M H) :=
    isPGroup_barX (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _) hHM
  have hcop : Nat.Coprime p (Nat.card (barX p M H)) := by
    obtain ⟨k, hk⟩ := hA2.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  have hcentr : Subgroup.centralizer ((Subgroup.zpowers db : Subgroup _) : Set _) =
      Subgroup.centralizer ({db} : Set (↥M ⧸ GLAPPrimeCore p ↥M)) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hDC : barX p M H ≤ Subgroup.centralizer ((Subgroup.zpowers db : Subgroup _) : Set _) := by
    rw [hcentr]
    rintro _ ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hyc : (y : G) ∈ Subgroup.centralizer ({d} : Set G) :=
      CFSG.LieType.BorelTits.pCoreOf_le 2 _ ((Subgroup.mem_subgroupOf).1 hy)
    have h1 : (y : G) * d = d * y := Subgroup.mem_centralizer_singleton_iff.1 hyc
    have h2 : y * (⟨d, hdM⟩ : ↥M) = ⟨d, hdM⟩ * y := Subtype.ext h1
    rw [hdb, ← map_mul, ← map_mul, h2]
  have hDn : ((barX p M H).subgroupOf
      (Subgroup.centralizer ((Subgroup.zpowers db : Subgroup _) : Set _))).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hg : (g : ↥M ⧸ GLAPPrimeCore p ↥M) ∈
        Subgroup.centralizer ({db} : Set (↥M ⧸ GLAPPrimeCore p ↥M)) := hcentr ▸ g.2
    have hgb : (g : ↥M ⧸ GLAPPrimeCore p ↥M) ∈
        barX p M (M ⊓ Subgroup.centralizer ({d} : Set G)) := by
      rw [barX_inf_centralizer hp hdM le_rfl (Subgroup.le_normalizer hdM) hdT]
      exact ⟨by rw [barX_self]; exact Subgroup.mem_top _, hg⟩
    obtain ⟨z, hz, hzg⟩ := hgb
    have hzc : (z : G) ∈ Subgroup.centralizer ({d} : Set G) :=
      ((Subgroup.mem_subgroupOf).1 hz).2
    obtain ⟨y, hy, hyn⟩ := (Subgroup.mem_subgroupOf).1 hn
    refine (Subgroup.mem_subgroupOf).2 ⟨z * y * z⁻¹, ?_, ?_⟩
    · refine (Subgroup.mem_subgroupOf).2 ?_
      have hyH : (y : G) ∈ H := (Subgroup.mem_subgroupOf).1 hy
      have hnorm := Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 _ hzc) (y : G)
      exact hnorm.1 hyH
    · simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
      rw [hzg, hyn]
  have key :=
    CFSG.ComponentClassification.SmallLocal.normal_coprime_centralizer_centralizes_prime_core
      hp hT hDC hDn hcop
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 key

theorem barX_sigmaStar_le {p : ℕ} {M D : Subgroup G} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : Prop95Hyp p M D) :
    barX p M (sigmaStar D) ≤
      Subgroup.centralizer
        ((CFSG.Open.pCore p (↥M ⧸ GLAPPrimeCore p ↥M) : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) :
          Set (↥M ⧸ GLAPPrimeCore p ↥M)) := by
  refine (barX_le_iff (sigmaStar_le h)).2 ?_
  refine iSup_le fun d => iSup_le fun hd => iSup_le fun hd1 => ?_
  have hHM := h.clause_a d hd hd1
  exact (barX_le_iff hHM).1 (barX_pCoreOf_centralizer_le hp hp2 (h.le hd) (h.plane.1.2 d hd) hHM)

end Key

theorem prop95ii_holds : Prop95ii := by
  intro G _ _ m p hS M D hD
  exact (barX_mono p (gammaD_le_sigmaStar D)).trans
    (barX_sigmaStar_le (prime_of_standing hS) (ne_two_of_standing hS) hD)

end CFSG.LocalAnalysis.GLTheoremB.Prop95Parts
