module

public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThreeUnique

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}

theorem D1PhaseThree.isWeakSBlock_conj (h : D1PhaseThree p P M H R)
    (hperf : ∀ Y : Subgroup G, Y ≤ H ⊓ M → ⁅Y, Y⁆ = Y → Nat.Coprime 3 (Nat.card Y))
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    {x : ↥M ⧸ CFSG.pCore 2 ↥M} (hxL : x ∈ barM M L) (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1)
    {g : G} (hg : g ∈ M) :
    IsWeakSBlock M (pCoreOf 2 H) (L.map (MulAut.conj g).toMonoidHom) := by
  have hL' := hL.toIsTwoPrimeComponent.map_conj hg
  refine ⟨hL', fun hle => ?_⟩
  set L' := L.map (MulAut.conj g).toMonoidHom with hL'def
  have hL'K : L' ≤ H ⊓ M := by
    rw [h.inf_eq_inf_normalizer_twoCore]
    exact le_inf hL'.le hle
  have hcop := hperf L' hL'K hL'.perfect
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have h3bar : 3 ∣ Nat.card (barM M L) := by
    rw [← hxo]
    exact Subgroup.orderOf_dvd_natCard _ hxL
  have hdvd : Nat.card (barM M L) ∣ Nat.card L := by
    have h1 := Subgroup.card_map_dvd (L.subgroupOf M) (QuotientGroup.mk' (CFSG.pCore 2 ↥M))
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hL.le).toEquiv] at h1
  have hcard : Nat.card L' = Nat.card L :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have h3 : 3 ∣ Nat.card L' := hcard ▸ h3bar.trans hdvd
  have := Nat.Coprime.coprime_dvd_right h3 hcop
  norm_num at this

theorem D1PhaseThree.mem_normalizer_of_zbar_mem (h : D1PhaseThree p P M H R) (hp : p.Prime)
    (hp2 : p ≠ 2)
    (hperf : ∀ Y : Subgroup G, Y ≤ H ⊓ M → ⁅Y, Y⁆ = Y → Nat.Coprime 3 (Nat.card Y))
    {z : G} (hzM : z ∈ M) (hz : IsPGroup p (Subgroup.zpowers z)) (hz3 : z ^ 3 = 1)
    (hCz : Subgroup.centralizer ({z} : Set G) ≤ H) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hzL : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩ ∈ barM M L) {g : G} (hg : g ∈ M) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨g, hg⟩ ∈
      Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  have hzC := h.not_mem_centralizer_block hp hp2 hzM hz hCz hL
  have hz1 : mk ⟨z, hzM⟩ ≠ 1 := fun h1 => hzC (h1 ▸ Subgroup.one_mem _)
  have hzb3 : mk ⟨z, hzM⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨z, hzM⟩ : M) ^ 3 = 1 := Subtype.ext (by simpa using hz3)
    rw [this, map_one]
  have hL' := h.isWeakSBlock_conj hperf hL hzL hz1 hzb3 hg
  have heq := h.barM_eq_of_mem_component hp hp2 hzM hz hCz hL.component hzL hL'
  rw [barM_map_conj hg L] at heq
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq

end CFSG.AGLEmbedding
