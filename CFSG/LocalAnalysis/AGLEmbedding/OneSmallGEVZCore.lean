module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalAltInv
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbAltDefs
import CFSG.LocalAnalysis.AGLEmbedding.CommuteOfDecomp
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroAb
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

structure D1SmallZCore (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)) (z : G) : Prop where
  data : D1OneSmallData p P M H R Rbar K
  elt : D1SmallCZElt p H R K z
  b0 : D1CzB0 p R z
  phase : D1PhaseThree p P M H R
  dec : ∀ r ∈ R, ∃ t ∈ d1LiftX p H R K, ∃ i : ℕ, r = t * z ^ i
  exp : ∀ r ∈ R, r ^ p = 1
  five_le : 5 ≤ p
  not_fi22 : ¬ (p = 5 ∧ IsFi22 K)
  card_T : Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
    Subgroup (H ⧸ primeComplementCore (G := H) p)) = p ^ 2

variable {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} {z : G}

theorem D1IbConfig.toZCore (hc : D1IbConfig p P M H R Rbar K z) :
    D1SmallZCore p P M H R Rbar K z :=
  ⟨hc.data, hc.elt, hc.b0, hc.phase, hc.dec, hc.exp, hc.five_le, hc.not_fi22, hc.card_T⟩

theorem D1IbAltConfig.toZCore (hc : D1IbAltConfig p P M H R Rbar K z) :
    D1SmallZCore p P M H R Rbar K z :=
  ⟨hc.data, hc.elt, hc.b0, hc.phase, hc.dec, hc.exp, by rcases hc.prime57 with h | h <;> omega,
    hc.not_fi22, hc.card_T⟩

theorem D1SmallAltConfig.toZCore (hc : D1SmallAltConfig p P M H R Rbar K z) :
    D1SmallZCore p P M H R Rbar K z :=
  ⟨hc.data, hc.elt, hc.b0, hc.phase, hc.dec, hc.exp, hc.five_le, hc.not_fi22, hc.card_rbar_inf⟩

namespace D1SmallZCore

theorem prime (hc : D1SmallZCore p P M H R Rbar K z) : p.Prime := hc.data.cfg.red.prime

theorem mem_M (hc : D1SmallZCore p P M H R Rbar K z) : z ∈ M := hc.phase.le_M hc.elt.1

theorem le_centralizer (hc : D1SmallZCore p P M H R Rbar K z) :
    R ≤ Subgroup.centralizer ({z} : Set G) :=
  hc.data.le_centralizer_czElt hc.elt

theorem card_d1LiftX (hc : D1SmallZCore p P M H R Rbar K z) :
    Nat.card (d1LiftX p H R K) = p ^ 2 ∧ z ∉ d1LiftX p H R K := by
  obtain ⟨hzT, hT⟩ := hc.data.d1LiftX_facts hc.elt
  exact ⟨hT.trans hc.card_T, hzT⟩

theorem sizes_of_invSubset (hc : D1SmallZCore p P M H R Rbar K z) (hOrb : KFactSmallOrbits)
    {S : Set G} (hS : D1InvSubset p H R K z S) :
    S.ncard = 0 ∨ S.ncard = p ^ 2 - 1 ∨ 2 * S.ncard = p ^ 2 - 1 ∨ S.ncard = 2 * (p - 1) ∨
      S.ncard = (p - 1) ^ 2 := by
  rcases hc.data.orbit_sizes hOrb hc.elt hc.dec hc.not_fi22 hc.card_T with h | ⟨-, -, h⟩ |
    ⟨-, h⟩
  · rcases h S hS with h | h <;> simp [h]
  · rcases h S hS with h | h | h <;> simp [h]
  · rcases h S hS with h | h | h | h <;> simp [h]

theorem card_R (hc : D1SmallZCore p P M H R Rbar K z) : Nat.card R = p ^ 3 := by
  have hp := hc.prime
  obtain ⟨hTcard, hzT⟩ := hc.card_d1LiftX
  have hTR : d1LiftX p H R K ≤ R := d1LiftX_le p H R K
  have hzR : Subgroup.zpowers z ≤ R := Subgroup.zpowers_le.mpr hc.elt.1
  have hzc : Nat.card (Subgroup.zpowers z) = p := by rw [Nat.card_zpowers, hc.elt.2.1]
  have hinf : d1LiftX p H R K ⊓ Subgroup.zpowers z = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).mpr fun y hy => ?_
    by_contra hy1
    exact hzT ((Subgroup.zpowers_le.mpr hy.1)
      (mem_zpowers_of_mem_zpowers_of_prime hp hc.elt.2.1 hy.2 hy1))
  refine le_antisymm ?_ ?_
  · have hs : Function.Surjective (fun x : d1LiftX p H R K × Subgroup.zpowers z =>
        (⟨(x.1 : G) * x.2, R.mul_mem (hTR x.1.2) (hzR x.2.2)⟩ : R)) := by
      rintro ⟨r, hr⟩
      obtain ⟨t, ht, i, rfl⟩ := hc.dec r hr
      exact ⟨(⟨t, ht⟩, ⟨z ^ i, Subgroup.npow_mem_zpowers z i⟩), rfl⟩
    have := Nat.card_le_card_of_surjective _ hs
    rw [Nat.card_prod, hTcard, hzc] at this
    rw [pow_succ]
    exact this
  · have := mul_card_le_of_inf_eq_bot hTR hzR hinf
    rw [hTcard, hzc, ← pow_succ] at this
    exact this

theorem barM_R (hc : D1SmallZCore p P M H R Rbar K z) :
    IsElemAbelian p (barM M R) ∧ Nat.card (barM M R) = p ^ 3 := by
  have hp := hc.prime
  have : Fact p.Prime := ⟨hp⟩
  set mkM := QuotientGroup.mk' (CFSG.pCore 2 ↥M)
  have hRM := hc.phase.le_M
  have hRp : IsPGroup p (R.subgroupOf M) := hc.phase.isPGroup.comap_subtype
  have hinj := pGroup_quotient_subgroupMap_injective_of_coprime_kernel p hp (CFSG.pCore 2 ↥M)
    (by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥M))
      rw [hk]
      exact fun h => hc.data.cfg.red.ne_two
        ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h)))
    _ hRp
  refine ⟨⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩, ?_⟩
  · obtain ⟨_, ⟨s, hs, rfl⟩⟩ := a
    obtain ⟨_, ⟨t, ht, rfl⟩⟩ := b
    change mkM s * mkM t = mkM t * mkM s
    rw [← map_mul, ← map_mul]
    exact congrArg mkM (Subtype.ext (commute_of_mem_of_decomp
      (IsPGroup.isMulCommutative_of_card_eq_prime_sq hc.card_d1LiftX.1) (d1LiftX_le p H R K)
      (fun r hr => Subgroup.mem_centralizer_singleton_iff.mp (hc.le_centralizer hr)) hc.dec
      (Subgroup.mem_subgroupOf.mp hs) (Subgroup.mem_subgroupOf.mp ht)))
  · rintro _ ⟨r, hr, rfl⟩
    have : r ^ p = 1 := Subtype.ext (by simpa using hc.exp r (Subgroup.mem_subgroupOf.mp hr))
    rw [← map_pow, this, map_one]
  · rw [← hc.card_R, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRM).toEquiv]
    exact (Nat.card_congr (Equiv.ofBijective _ ⟨hinj,
      MonoidHom.subgroupMap_surjective _ _⟩)).symm

end D1SmallZCore

end CFSG.AGLEmbedding
