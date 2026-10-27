module

public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEscapeAux
import CFSG.Monster.Existence.StdOdd.Coprime
public import CFSG.LocalAnalysis.AGLEmbedding.EscapeTwoCore

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers

section Count

variable {Y : Type*} [Group Y] [Finite Y]

theorem not_dvd_card_of_fixed_le {p : ℕ} (hp : p.Prime) {L J : Subgroup Y} {x : Y}
    (hxL : x ∈ Subgroup.normalizer (L : Set Y)) (hx : IsPGroup p (Subgroup.zpowers x))
    (hJ : p.Coprime (Nat.card J)) (hC : ∀ l ∈ L, x * l * x⁻¹ = l → l ∈ J) :
    ¬ p ∣ Nat.card L := by
  have : Fact p.Prime := ⟨hp⟩
  intro hdvd
  have hmod := CFSG.Monster.Existence.StdOdd.card_modEq_inf_centralizer hx
    (Subgroup.zpowers_le.mpr hxL)
  have hFJ : L ⊓ Subgroup.centralizer (Subgroup.zpowers x : Set Y) ≤ J := fun l hl =>
    hC l hl.1 (by
      rw [Subgroup.mem_centralizer_iff.mp hl.2 x (Subgroup.mem_zpowers x), mul_inv_cancel_right])
  exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hJ
    (((hmod.dvd_iff dvd_rfl).mp hdvd).trans (Subgroup.card_dvd_of_le hFJ)))

end Count

section Block

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}

theorem fixed_le_barM_normalizer_inf_of_twoCore_le {S : Subgroup G}
    (hQS : pCoreOf 2 M ≤ S) (hp : p.Prime) (hp2 : p ≠ 2) {z : G} (hzM : z ∈ M)
    (hz : IsPGroup p (Subgroup.zpowers z))
    (hCz : M ⊓ Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (S : Set G))
    {L : Subgroup G} :
    ∀ l ∈ barM M L, QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩ * l *
        (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩)⁻¹ = l →
      l ∈ barM M (Subgroup.normalizer (S : Set G) ⊓ L) := by
  have : Fact p.Prime := ⟨hp⟩
  intro l hl hfix
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M)
  obtain ⟨m, hmL, rfl⟩ := hl
  have hcop : p.Coprime (Nat.card (CFSG.pCore 2 ↥M)) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥M))
    rw [hk]
    exact ((Nat.coprime_primes hp Nat.prime_two).mpr hp2).pow_right k
  have hzMp : IsPGroup p (Subgroup.zpowers (⟨z, hzM⟩ : M)) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hz
    refine IsPGroup.of_card (n := n) ?_
    rw [Nat.card_zpowers, ← Subgroup.orderOf_coe, ← Nat.card_zpowers]
    exact hn
  have hx : mk m ∈ Subgroup.centralizer ({mk ⟨z, hzM⟩} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc mk m * mk ⟨z, hzM⟩ = mk ⟨z, hzM⟩ * mk m * (mk ⟨z, hzM⟩)⁻¹ * mk ⟨z, hzM⟩ := by
          rw [hfix]
      _ = mk ⟨z, hzM⟩ * mk m := by group
  obtain ⟨g, hg, hgm⟩ := exists_mem_centralizer_mk_eq hp (CFSG.pCore 2 ↥M) hcop hzMp hx
  have hgC : (g : G) ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hg))
  have hgS : (g : G) ∈ Subgroup.normalizer (S : Set G) := hCz ⟨g.2, hgC⟩
  have hq : g⁻¹ * m ∈ CFSG.pCore 2 ↥M := by
    rw [← QuotientGroup.ker_mk' (CFSG.pCore 2 ↥M), MonoidHom.mem_ker, map_mul, map_inv, hgm,
      inv_mul_cancel]
  have hqQ : ((g⁻¹ * m : M) : G) ∈ pCoreOf 2 M := by
    have : ((g⁻¹ * m : M) : G) ∈ (CFSG.pCore 2 ↥M).map M.subtype := ⟨g⁻¹ * m, hq, rfl⟩
    assumption
  have hqS : ((g⁻¹ * m : M) : G) ∈ Subgroup.normalizer (S : Set G) :=
    Subgroup.le_normalizer (hQS hqQ)
  have hmS : (m : G) ∈ Subgroup.normalizer (S : Set G) := by
    simpa using Subgroup.mul_mem _ hgS hqS
  exact ⟨m, Subgroup.mem_subgroupOf.mpr ⟨hmS, Subgroup.mem_subgroupOf.mp hmL⟩, rfl⟩

theorem D1PhaseThree.fixed_le_barM_normalizer_inf (h : D1PhaseThree p P M H R) (hp : p.Prime)
    (hp2 : p ≠ 2) {z : G} (hzM : z ∈ M) (hz : IsPGroup p (Subgroup.zpowers z))
    (hCz : Subgroup.centralizer ({z} : Set G) ≤ H) {L : Subgroup G} :
    ∀ l ∈ barM M L, QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩ * l *
        (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩)⁻¹ = l →
      l ∈ barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L) :=
  fixed_le_barM_normalizer_inf_of_twoCore_le (h.twoCore_M_le h.twoCore_inf) hp hp2 hzM hz
    (fun _ hx => localGroup_le_normalizer_pCoreOf 2 H (hCz hx.2))

end Block

end CFSG.AGLEmbedding
