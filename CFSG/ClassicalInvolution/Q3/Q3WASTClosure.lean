module

public import CFSG.ClassicalInvolution.Q3.Q3WARoot
public import CFSG.ClassicalInvolution.Q3.Generation
public import CFSG.ClassicalInvolution.Generic.CoreAssemblyBase

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD

theorem commutes_join3 {G : Type} [Group G] {A B C : Subgroup G} (hB : Commutes A B)
    (hC : Commutes A C) : Commutes A (B ⊔ C) := by
  intro a ha y hy
  have hle : B ⊔ C ≤ Subgroup.centralizer ({a} : Set G) := sup_le
    (fun b hb => Subgroup.mem_centralizer_singleton_iff.mpr (hB a ha b hb).symm)
    (fun c hc => Subgroup.mem_centralizer_singleton_iff.mpr (hC a ha c hc).symm)
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hy)).symm

theorem le_centralizer_of_commutes3 {G : Type} [Group G] {K N : Subgroup G} (h : Commutes N K)
    {z : G} (hz : z ∈ K) : N ≤ Subgroup.centralizer ({z} : Set G) := fun n hn =>
  Subgroup.mem_centralizer_singleton_iff.mpr (h n hn z hz)

@[expose] def commNbhd3 {G : Type} [Group G] (Ω : Set (Subgroup G)) (a : Subgroup G) :
    Set (Subgroup G) :=
  {L | L ∈ Ω ∧ Commutes a L}

section Neighbours

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K₀ : Subgroup G} {z₀ : G}

theorem commutes_of_centralizing3 (hΩ : InClass3 Ω)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K₀) (hz : IsClassicalMember3 K₀ z₀)
    (hD1 : ∀ L ∈ centralizingMembers Ω {z₀}, L ≠ K₀ → Commutes K₀ L) {N : Subgroup G}
    (hN : N ∈ Ω) {u : G} (hu : IsClassicalMember3 N u) {L : Subgroup G}
    (hL : L ∈ centralizingMembers Ω {u}) (hLN : L ≠ N) : Commutes N L := by
  obtain ⟨g, hg⟩ := hsingle N hN
  have hu' : u = g * z₀ * g⁻¹ := involution_unique3 hu (hg ▸ hz.conj g)
  subst hu'
  rw [centralizingMembers_conj hΩ.conjInvariant g z₀] at hL
  obtain ⟨L', hL', rfl⟩ := hL
  have hne : L' ≠ K₀ := fun h => hLN (by rw [h, hg])
  rw [hg]
  exact (commutes_conjSub_iff g).mpr (hD1 L' hL' hne)

theorem commNbhd3_eq (hΩ : InClass3 Ω) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K₀)
    (hz : IsClassicalMember3 K₀ z₀)
    (hD1 : ∀ L ∈ centralizingMembers Ω {z₀}, L ≠ K₀ → Commutes K₀ L) {a : Subgroup G}
    (ha : a ∈ Ω) {u : G} (hu : IsClassicalMember3 a u) :
    commNbhd3 Ω a = centralizingMembers Ω {u} \ {a} := by
  ext L
  constructor
  · rintro ⟨hL, hc⟩
    refine ⟨⟨hL, le_centralizer_of_commutes3 hc.symm hu.mem⟩, ?_⟩
    rintro (rfl : L = a)
    exact not_commutes_self3 hu hc
  · rintro ⟨hL, hLa⟩
    exact ⟨hL.1, commutes_of_centralizing3 hΩ hsingle hz hD1 ha hu hL hLa⟩

theorem ncard_commNbhd3_add_one (hΩ : InClass3 Ω) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K₀)
    (hz : IsClassicalMember3 K₀ z₀)
    (hD1 : ∀ L ∈ centralizingMembers Ω {z₀}, L ≠ K₀ → Commutes K₀ L) {a : Subgroup G}
    (ha : a ∈ Ω) :
    (commNbhd3 Ω a).ncard + 1 = (centralizingMembers Ω {z₀}).ncard := by
  obtain ⟨u, hu⟩ := hΩ.classical a ha
  obtain ⟨g, hg⟩ := hsingle a ha
  have hu' : u = g * z₀ * g⁻¹ := involution_unique3 hu (hg ▸ hz.conj g)
  have hmem : a ∈ centralizingMembers Ω {u} := ⟨ha, isSubnormal_le hu.subnormal⟩
  rw [commNbhd3_eq hΩ hsingle hz hD1 ha hu,
    Set.ncard_sdiff_singleton_add_one hmem (Set.toFinite _), hu',
    ncard_centralizingMembers_conj hΩ.conjInvariant g z₀]

theorem false_of_nbhd_subset3 [IsSimpleGroup G] (hnab : ∃ x y : G, x * y ≠ y * x)
    (hΩ : InClass3 Ω) (hconn : RouteD.DeltaConnected Ω)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K₀) (hz : IsClassicalMember3 K₀ z₀)
    (hD1 : ∀ L ∈ centralizingMembers Ω {z₀}, L ≠ K₀ → Commutes K₀ L) {K j₀ j₁ : Subgroup G}
    (hK : K ∈ Ω) (hj₀ : j₀ ∈ Ω) (hj₁ : j₁ ∈ Ω) (hKj₀ : Commutes K j₀)
    (hlayer : ∀ N ∈ Ω, Commutes K N → N ≤ j₀ ⊔ j₁)
    (hsub : ∀ N ∈ Ω, Commutes j₁ N → Commutes j₀ N) : False := by
  have hν : ∀ a ∈ Ω, (commNbhd3 Ω a).ncard + 1 = (centralizingMembers Ω {z₀}).ncard :=
    fun a ha => ncard_commNbhd3_add_one hΩ hsingle hz hD1 ha
  have hfin : ∀ a, (commNbhd3 Ω a).Finite := fun a => Set.toFinite _
  have hL : commNbhd3 Ω j₁ = commNbhd3 Ω j₀ := by
    refine Set.eq_of_subset_of_ncard_le (fun L hL => ⟨hL.1, hsub L hL.1 hL.2⟩) ?_ (hfin _)
    have h0 := hν j₀ hj₀
    have h1 := hν j₁ hj₁
    omega
  have hLM : ∀ K' ∈ commNbhd3 Ω j₀, ∀ N ∈ commNbhd3 Ω K, Commutes K' N := by
    intro K' hK' N hN
    have h0 : Commutes K' j₀ := hK'.2.symm
    have h1 : Commutes K' j₁ := (show K' ∈ commNbhd3 Ω j₁ from hL ▸ hK').2.symm
    exact fun a ha y hy => commutes_join3 h0 h1 a ha y (hlayer N hN.1 hN.2 hy)
  have hnK' : ∀ K' ∈ commNbhd3 Ω j₀, commNbhd3 Ω K' = commNbhd3 Ω K := by
    intro K' hK'
    apply Eq.symm
    refine Set.eq_of_subset_of_ncard_le (fun N hN => ⟨hN.1, hLM K' hK' N hN⟩) ?_ (hfin _)
    have h0 := hν K' hK'.1
    have h1 := hν K hK
    omega
  have hnN : ∀ N ∈ commNbhd3 Ω K, commNbhd3 Ω N = commNbhd3 Ω j₀ := by
    intro N hN
    apply Eq.symm
    refine Set.eq_of_subset_of_ncard_le
      (fun K' hK' => ⟨hK'.1, (hLM K' hK' N hN).symm⟩) ?_ (hfin _)
    have h0 := hν N hN.1
    have h1 := hν j₀ hj₀
    omega
  have hKL : K ∈ commNbhd3 Ω j₀ := ⟨hK, hKj₀.symm⟩
  have hS : Ω ⊆ commNbhd3 Ω j₀ ∪ commNbhd3 Ω K := by
    refine subset_of_adj_closed hconn (𝔖 := commNbhd3 Ω j₀ ∪ commNbhd3 Ω K) ?_ ⟨K, Or.inl hKL⟩ ?_
    · rintro N (hN | hN)
      exacts [hN.1, hN.1]
    · rintro A (hA | hA) L hL' hLA hc
      · exact Or.inr (hnK' A hA ▸ ⟨hL', hc⟩)
      · exact Or.inl (hnN A hA ▸ ⟨hL', hc⟩)
  let M₁ : Subgroup G := ⨆ L ∈ commNbhd3 Ω j₀, L
  have hle : ∀ N ∈ commNbhd3 Ω K, ∀ n ∈ N, M₁ ≤ Subgroup.centralizer ({n} : Set G) := by
    intro N hN n hn
    exact iSup₂_le fun L hL' l hl => Subgroup.mem_centralizer_singleton_iff.mpr
      (hLM L hL' N hN l hl n hn)
  have hcent : ∀ N ∈ commNbhd3 Ω K, ∀ n ∈ N, ∀ m ∈ M₁, n * m * n⁻¹ = m := by
    intro N hN n hn m hm
    rw [mul_inv_eq_iff_eq_mul]
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle N hN n hn hm)).symm
  have hnorm : M₁.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hΩ.generated]
    refine iSup₂_le fun N hN => ?_
    rcases hS hN with hN' | hN'
    · exact le_trans (le_iSup₂ (f := fun L (_ : L ∈ commNbhd3 Ω j₀) => L) N hN')
        Subgroup.le_normalizer
    · intro n hn
      refine Subgroup.mem_normalizer_iff.mpr fun m => ⟨fun hm => ?_, fun hm => ?_⟩
      · rw [hcent N hN' n hn m hm]
        exact hm
      · have h1 := hcent N hN' n⁻¹ (N.inv_mem hn) _ hm
        have h2 : n⁻¹ * (n * m * n⁻¹) * n⁻¹⁻¹ = m := by group
        rw [h2] at h1
        rw [h1]
        exact hm
  have := hnorm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal M₁ with h | h
  · obtain ⟨u, hu⟩ := hΩ.classical K hK
    have hKle : K ≤ M₁ := le_iSup₂ (f := fun L (_ : L ∈ commNbhd3 Ω j₀) => L) K hKL
    rw [h] at hKle
    have hu1 : u = 1 := Subgroup.mem_bot.mp (hKle hu.mem)
    have := hu.orderOf_eq_two
    rw [hu1, orderOf_one] at this
    omega
  · obtain ⟨u, hu⟩ := hΩ.classical j₀ hj₀
    have hj₀M : j₀ ∈ commNbhd3 Ω K := ⟨hj₀, hKj₀⟩
    have hmem : u ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : g ∈ M₁ := h ▸ Subgroup.mem_top g
      exact Subgroup.mem_centralizer_singleton_iff.mp (hle j₀ hj₀M u hu.mem hg)
    rw [CoreAssembly.center_eq_bot hnab, Subgroup.mem_bot] at hmem
    have := hu.orderOf_eq_two
    rw [hmem, orderOf_one] at this
    omega

end Neighbours

end CFSG.ClassicalInvolution.Q3.Q3W
