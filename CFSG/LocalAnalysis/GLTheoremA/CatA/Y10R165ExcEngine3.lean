module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcEngine
public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofExcLayerBasic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open
open scoped commutatorElement

namespace ExcEngine

theorem normalizer_commutator_le_normalizer {G : Type*} [Group G] (M : Subgroup G) :
    Subgroup.normalizer (M : Set G) ≤ Subgroup.normalizer (⁅M, M⁆ : Subgroup G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hg ⊢
  rw [Subgroup.map_commutator, hg]

theorem dvd_card_commutator_comap {H K : Type*} [Group H] [Group K] {π : H →* K}
    (hπ : Function.Surjective π) {L : Subgroup K} (hL : ⁅L, L⁆ = L) {p : ℕ}
    (hp : p ∣ Nat.card L) :
    p ∣ Nat.card ↥(⁅Subgroup.comap π L, Subgroup.comap π L⁆) := by
  let ψ : ↥(⁅Subgroup.comap π L, Subgroup.comap π L⁆) →* ↥L :=
    (π.comp (⁅Subgroup.comap π L, Subgroup.comap π L⁆).subtype).codRestrict L fun x => by
      have hx : π (x : H) ∈ (⁅Subgroup.comap π L, Subgroup.comap π L⁆).map π :=
        ⟨(x : H), x.2, rfl⟩
      rwa [CFSG.ClassicalInvolution.RouteD.Exotic.map_commutator_comap_eq π hπ hL] at hx
  have hψ : Function.Surjective ψ := by
    intro y
    have hy : (y : K) ∈ (⁅Subgroup.comap π L, Subgroup.comap π L⁆).map π := by
      rw [CFSG.ClassicalInvolution.RouteD.Exotic.map_commutator_comap_eq π hπ hL]
      exact y.2
    obtain ⟨x, hx, hxy⟩ := hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have hcard := Subgroup.card_ker_mul_card_of_surjective hψ
  exact hp.trans ⟨Nat.card ↥ψ.ker, by rw [mul_comm]; exact hcard.symm⟩

theorem commutator_comap_le_centralizer {H K : Type*} [Group H] [Group K] {π : H →* K}
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center H) {L : Subgroup K}
    (hL : ⁅L, L⁆ = L) {x : H} (hLx : L ≤ Subgroup.centralizer ({π x} : Set K)) :
    ⁅Subgroup.comap π L, Subgroup.comap π L⁆ ≤ Subgroup.centralizer ({x} : Set H) := by
  set M : Subgroup H := Subgroup.comap π L with hM
  set P : Subgroup H := ⁅M, M⁆ with hP
  have hPperf : Group.IsPerfect ↥P :=
    Subgroup.isPerfect_iff.mpr (by
      rw [hP]
      exact CFSG.ClassicalInvolution.RouteD.Exotic.commutator_comap_perfect π hπ hker hL)
  have hMx : ⁅M, Subgroup.zpowers x⁆ ≤ π.ker := by
    rw [← Subgroup.map_eq_bot_iff (f := π)]
    rw [Subgroup.map_commutator, MonoidHom.map_zpowers]
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro y hy
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hy
    rw [CFSG.centralizer_zpowers_eq_centralizer_singleton]
    exact hLx hm
  have hPle : P ≤ M := by
    rw [hP]
    exact Subgroup.commutator_le_self M
  have hinner : ⁅⁅P, Subgroup.zpowers x⁆, P⁆ = ⊥ := by
    refine le_bot_iff.mp ?_
    calc ⁅⁅P, Subgroup.zpowers x⁆, P⁆ ≤ ⁅⁅M, Subgroup.zpowers x⁆, M⁆ :=
          Subgroup.commutator_mono (Subgroup.commutator_mono hPle le_rfl) hPle
      _ ≤ ⁅π.ker, M⁆ := Subgroup.commutator_mono hMx le_rfl
      _ ≤ ⁅Subgroup.center H, M⁆ := Subgroup.commutator_mono hker le_rfl
      _ = ⊥ := Subgroup.commutator_center_left M
  have hcomm : ⁅P, Subgroup.zpowers x⁆ = ⊥ :=
    CFSG.LocalCores.perfect_double_commutator hPperf hinner
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hcomm
  rwa [CFSG.centralizer_zpowers_eq_centralizer_singleton] at hcomm

private theorem mem_normalizer_comap_of_mem_normalizer {H K : Type*} [Group H] [Group K]
    {π : H →* K}
    (hπ : Function.Surjective π) {L : Subgroup K} {g : H}
    (hg : π g ∈ Subgroup.normalizer (L : Set K)) :
    g ∈ Subgroup.normalizer (Subgroup.comap π L : Set H) := by
  rw [← Subgroup.comap_normalizer_eq_of_surjective (f := π) L hπ]
  exact hg

end ExcEngine

theorem concl165Avoid_of_central_lift {H K : Type} [Group H] [Finite H] [Group K] [Finite K]
    {p q : ℕ} (hp : p.Prime) (π : H →* K) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center H)
    {Ã : Subgroup H} (hÃ : IsElemAbelian p Ã) {x z : H} (hx : x ∈ Ã) (hz : z ∈ Ã)
    (hx1 : x ≠ 1) (hzx : z ∉ Subgroup.zpowers x)
    {J : Subgroup K} (hJx : J ≤ Subgroup.centralizer ({π x} : Set K))
    (hJn : (J.subgroupOf (Subgroup.centralizer ({π x} : Set K))).Normal)
    (hJ : CFSG.Open.IsQuasisimple ↥J) (hpJ : p ∣ Nat.card J)
    {Q : Subgroup K} (hQJ : Q ≤ J) (hQz : Q ≤ Subgroup.centralizer ({π z} : Set K))
    (hQn : (Q.subgroupOf (J ⊓ Subgroup.centralizer ({π z} : Set K))).Normal)
    (hQ : CFSG.Open.IsQuasisimple ↥Q) (hpQ : p ∣ Nat.card Q)
    {F : Subgroup H} (hF : IsElemAbelian q F)
    (hFx : F ≤ Subgroup.centralizer ({x} : Set H))
    (hFJ : F.map π ≤ Subgroup.normalizer (J : Set K))
    (hF3 : 3 ≤ CFSG.Open.pRank q F) (hFZ : F ⊓ π.ker = ⊥) :
    Concl165Avoid H p q Ã π.ker := by
  classical
  have hJperf : ⁅J, J⁆ = J :=
    Subgroup.isPerfect_iff.mp (Group.IsPerfect.mk hJ.1)
  have hQperf : ⁅Q, Q⁆ = Q :=
    Subgroup.isPerfect_iff.mp (Group.IsPerfect.mk hQ.1)
  set M : Subgroup H := Subgroup.comap π J with hM
  set N : Subgroup H := Subgroup.comap π Q with hN
  set J' : Subgroup H := ⁅M, M⁆ with hJ'
  set Q' : Subgroup H := ⁅N, N⁆ with hQ'
  have hJ'q : CFSG.Open.IsQuasisimple ↥J' := by
    rw [hJ']
    exact CFSG.ClassicalInvolution.RouteD.Exotic.isQuasisimple_commutator_comap π hπ hker hJ
  have hpJ' : p ∣ Nat.card J' := by
    rw [hJ']
    exact ExcEngine.dvd_card_commutator_comap hπ hJperf hpJ
  have hJ'x : J' ≤ Subgroup.centralizer ({x} : Set H) := by
    rw [hJ']
    exact ExcEngine.commutator_comap_le_centralizer hπ hker hJperf hJx
  have hxCent : Subgroup.centralizer ({x} : Set H) ≤
      Subgroup.normalizer (M : Set H) := by
    intro g hg
    have hπg : π g ∈ Subgroup.centralizer ({π x} : Set K) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
      rw [← map_mul, ← map_mul, hg]
    exact ExcEngine.mem_normalizer_comap_of_mem_normalizer hπ
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hJx).mp hJn hπg)
  have hJ'n : (J'.subgroupOf (Subgroup.centralizer ({x} : Set H))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hJ'x, hJ']
    exact hxCent.trans (ExcEngine.normalizer_commutator_le_normalizer M)
  have hQ'q : CFSG.Open.IsQuasisimple ↥Q' := by
    rw [hQ']
    exact CFSG.ClassicalInvolution.RouteD.Exotic.isQuasisimple_commutator_comap π hπ hker hQ
  have hpQ' : p ∣ Nat.card Q' := by
    rw [hQ']
    exact ExcEngine.dvd_card_commutator_comap hπ hQperf hpQ
  have hQ'J' : Q' ≤ J' := by
    rw [hQ', hJ']
    exact Subgroup.commutator_mono (Subgroup.comap_mono hQJ) (Subgroup.comap_mono hQJ)
  have hQ'z : Q' ≤ Subgroup.centralizer ({z} : Set H) := by
    rw [hQ']
    exact ExcEngine.commutator_comap_le_centralizer hπ hker hQperf hQz
  have hQ'le : Q' ≤ J' ⊓ Subgroup.centralizer ({z} : Set H) := le_inf hQ'J' hQ'z
  have hQN : J ⊓ Subgroup.centralizer ({π z} : Set K) ≤
      Subgroup.normalizer (Q : Set K) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (le_inf hQJ hQz)).mp hQn
  have hJn_le : J' ⊓ Subgroup.centralizer ({z} : Set H) ≤
      Subgroup.normalizer (N : Set H) := by
    intro g hg
    obtain ⟨hgJ, hgz⟩ := Subgroup.mem_inf.mp hg
    have hgJ' : g ∈ ⁅M, M⁆ := by rwa [hJ'] at hgJ
    have hπgJ : π g ∈ J :=
      Subgroup.mem_comap.mp (Subgroup.commutator_le_self M hgJ')
    have hπgz : π g ∈ Subgroup.centralizer ({π z} : Set K) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hgz ⊢
      rw [← map_mul, ← map_mul, hgz]
    exact ExcEngine.mem_normalizer_comap_of_mem_normalizer hπ (hQN ⟨hπgJ, hπgz⟩)
  have hQ'n : (Q'.subgroupOf (J' ⊓ Subgroup.centralizer ({z} : Set H))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hQ'le, hQ']
    exact hJn_le.trans (ExcEngine.normalizer_commutator_le_normalizer N)
  have hF_le_NJ' : F ≤ Subgroup.normalizer (J' : Set H) := by
    intro f hf
    have hπf : π f ∈ Subgroup.normalizer (J : Set K) :=
      hFJ (Subgroup.mem_map_of_mem π hf)
    have hfN : f ∈ Subgroup.normalizer (M : Set H) :=
      ExcEngine.mem_normalizer_comap_of_mem_normalizer hπ hπf
    rw [hJ']
    exact ExcEngine.normalizer_commutator_le_normalizer M hfN
  exact concl165Avoid_of_layers hp hÃ hx hz hx1 hzx hJ'x hJ'n hJ'q hpJ'
    hQ'J' hQ'z hQ'n hQ'q hpQ' hF hFx hF_le_NJ' hF3 hFZ

end CFSG.LocalAnalysis.GLTheoremA.Y10F
