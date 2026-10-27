module

public import CFSG.ClassicalInvolution.RouteD.GapsR2

public section

namespace CFSG.ClassicalInvolution.RouteD.TWZ

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps
open CFSG.Open (classicalInvolutionOddCore)

section Normalizer

variable {G : Type} [Group G]

theorem le_normalizer_of_forall_conj_mem {S X : Subgroup G}
    (h : ∀ c ∈ S, ∀ y ∈ X, c * y * c⁻¹ ∈ X) : S ≤ Subgroup.normalizer (X : Set G) := by
  intro c hc
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨h c hc y, fun hy => ?_⟩
  have := h c⁻¹ (S.inv_mem hc) _ hy
  simpa [mul_assoc] using this

theorem conjSub_le_centralizingLayer {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) {x c : G}
    (hc : c * x = x * c) :
    conjSub c (centralizingLayer Ω {x}) ≤ centralizingLayer Ω {x} := by
  unfold conjSub
  rw [Subgroup.map_le_iff_le_comap]
  refine iSup₂_le fun L hL => ?_
  intro l hl
  have hcx : c * x * c⁻¹ = x := by rw [hc]; group
  have hmem : conjSub c L ∈ centralizingMembers Ω {x} := by
    have := centralizingMembers_conj hΩ c x
    rw [hcx] at this
    rw [this]
    exact ⟨L, hL, rfl⟩
  exact le_centralizingLayer hmem (conj_mem_conjSub hl)

theorem centralizer_le_normalizer_centralizingLayer {Ω : Set (Subgroup G)}
    (hΩ : ConjInvariant Ω) (x : G) :
    Subgroup.centralizer ({x} : Set G) ≤
      Subgroup.normalizer (centralizingLayer Ω {x} : Set G) := by
  refine le_normalizer_of_forall_conj_mem fun c hc y hy => ?_
  have hc' : c * x = x * c := Subgroup.mem_centralizer_singleton_iff.mp hc
  exact conjSub_le_centralizingLayer hΩ hc' (conj_mem_conjSub hy)

theorem le_normalizer_centralizingLayer_of_forall {Ω : Set (Subgroup G)} {x : G} {S : Subgroup G}
    (h : ∀ c ∈ S, ∀ N ∈ centralizingMembers Ω {x}, conjSub c N ∈ centralizingMembers Ω {x}) :
    S ≤ Subgroup.normalizer (centralizingLayer Ω {x} : Set G) := by
  refine le_normalizer_of_forall_conj_mem fun c hc y hy => ?_
  have hle : conjSub c (centralizingLayer Ω {x}) ≤ centralizingLayer Ω {x} := by
    unfold conjSub
    rw [Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun L hL l hl => ?_
    exact le_centralizingLayer (h c hc L hL) (conj_mem_conjSub hl)
  exact hle (conj_mem_conjSub hy)

theorem le_centralizer_of_forall_mem {Ω : Set (Subgroup G)} {x k : G}
    (hk : ∀ N ∈ centralizingMembers Ω {x}, ∀ n ∈ N, k * n = n * k) :
    centralizingLayer Ω {x} ≤ Subgroup.centralizer ({k} : Set G) := by
  refine iSup₂_le fun N hN n hn => ?_
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (hk N hN n hn).symm

theorem conj_eq_of_forall_mem {Ω : Set (Subgroup G)} {x k : G}
    (hk : ∀ N ∈ centralizingMembers Ω {x}, ∀ n ∈ N, k * n = n * k) {y : G}
    (hy : y ∈ centralizingLayer Ω {x}) : k * y * k⁻¹ = y := by
  have h := Subgroup.mem_centralizer_singleton_iff.mp (le_centralizer_of_forall_mem hk hy)
  rw [← h]
  group

theorem mem_normalizer_centralizingLayer_of_forall {Ω : Set (Subgroup G)} {x k : G}
    (hk : ∀ N ∈ centralizingMembers Ω {x}, ∀ n ∈ N, k * n = n * k) :
    k ∈ Subgroup.normalizer (centralizingLayer Ω {x} : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have hk' : ∀ N ∈ centralizingMembers Ω {x}, ∀ n ∈ N, k⁻¹ * n = n * k⁻¹ :=
    fun N hN n hn => (Commute.inv_left (show Commute k n from hk N hN n hn))
  refine ⟨fun hy => by rw [conj_eq_of_forall_mem hk hy]; exact hy, fun hy => ?_⟩
  have h2 := conj_eq_of_forall_mem hk' hy
  have h3 : k⁻¹ * (k * y * k⁻¹) * k⁻¹⁻¹ = y := by group
  rw [h3] at h2
  exact h2.symm ▸ hy

end Normalizer

section Perfect

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

theorem subgroupOf_le_of_locImg_le {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) {x : G}
    (hP1 : LocalOddCentral Ω {x}) {L : Subgroup G} (hL : L ∈ centralizingMembers Ω {x})
    {H₀ : Subgroup ↥(locLayer Ω x)} (h : locImg Ω x L ≤ H₀.map (locMk Ω x)) :
    L.subgroupOf (locLayer Ω x) ≤ H₀ := by
  refine le_of_perfect_of_le_sup_center (Z := classicalInvolutionOddCore ↥(locLayer Ω x)) hP1
    (subgroupOf_le_commutator hΩ hL) ?_
  intro a ha
  obtain ⟨h₀, hh₀, hh₀a⟩ := h ⟨a, ha, rfl⟩
  have e : a = h₀ * (h₀⁻¹ * a) := by group
  rw [e]
  refine Subgroup.mul_mem _ (Subgroup.mem_sup_left hh₀) (Subgroup.mem_sup_right ?_)
  refine (QuotientGroup.eq_one_iff _).mp ?_
  show locMk Ω x (h₀⁻¹ * a) = 1
  rw [map_mul, map_inv, hh₀a, inv_mul_cancel]

end Perfect

end CFSG.ClassicalInvolution.RouteD.TWZ
