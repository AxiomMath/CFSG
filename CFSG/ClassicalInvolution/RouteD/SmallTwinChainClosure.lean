module

public import CFSG.ClassicalInvolution.RouteD.GapsEnd4Aux
public import CFSG.ClassicalInvolution.Generic.CoreAssemblyBase
public import CFSG.ClassicalInvolution.RouteD.NonClassicalLocal

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD.Gaps

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

theorem commutes_join_of_commutes {A B C : Subgroup G} (hB : Commutes A B) (hC : Commutes A C) :
    Commutes A (B ⊔ C) := by
  intro a ha y hy
  have hle : B ⊔ C ≤ Subgroup.centralizer ({a} : Set G) := sup_le
    (fun b hb => Subgroup.mem_centralizer_singleton_iff.mpr (hB a ha b hb).symm)
    (fun c hc => Subgroup.mem_centralizer_singleton_iff.mpr (hC a ha c hc).symm)
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hy)).symm

@[expose] def commNbhd (Ω : Set (Subgroup G)) (a : Subgroup G) : Set (Subgroup G) :=
  {L | L ∈ Ω ∧ Commutes a L}

section Neighbours

variable [Finite G] {Ω : Set (Subgroup G)} {K₀ : Subgroup G} {z₀ : G}

omit [Finite G] in
theorem commutes_of_centralizing (h2 : (2 : GaloisField p f) ≠ 0) (hΩ : InClass p f Ω)
    (hex : ExactMembers Ω) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K₀)
    (hz : IsClassicalMember p f K₀ z₀)
    (hD1 : ∀ L ∈ centralizingMembers Ω {z₀}, L ≠ K₀ → Commutes K₀ L) {N : Subgroup G}
    (hN : N ∈ Ω) {u : G} (hu : IsClassicalMember p f N u) {L : Subgroup G}
    (hL : L ∈ centralizingMembers Ω {u}) (hLN : L ≠ N) : Commutes N L := by
  obtain ⟨g, hg⟩ := hsingle N hN
  have hu' : u = g * z₀ * g⁻¹ :=
    unique_involution_of_isClassicalMember h2 (hex N hN) hu (hg ▸ hz.conj g)
  subst hu'
  rw [centralizingMembers_conj hΩ.conjInvariant g z₀] at hL
  obtain ⟨L', hL', rfl⟩ := hL
  have hne : L' ≠ K₀ := fun h => hLN (by rw [h, hg])
  rw [hg]
  exact (commutes_conjSub_iff g).mpr (hD1 L' hL' hne)

omit [Finite G] in
theorem commNbhd_eq (h2 : (2 : GaloisField p f) ≠ 0) (hΩ : InClass p f Ω) (hex : ExactMembers Ω)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K₀) (hz : IsClassicalMember p f K₀ z₀)
    (hD1 : ∀ L ∈ centralizingMembers Ω {z₀}, L ≠ K₀ → Commutes K₀ L) {a : Subgroup G}
    (ha : a ∈ Ω) {u : G} (hu : IsClassicalMember p f a u) :
    commNbhd Ω a = centralizingMembers Ω {u} \ {a} := by
  ext L
  constructor
  · rintro ⟨hL, hc⟩
    refine ⟨⟨hL, NonClassical.le_centralizer_of_commutes hc.symm hu.mem⟩, ?_⟩
    rintro (rfl : L = a)
    exact not_commutes_self_of_isClassicalMember hu hc
  · rintro ⟨hL, hLa⟩
    exact ⟨hL.1, commutes_of_centralizing h2 hΩ hex hsingle hz hD1 ha hu hL hLa⟩

theorem ncard_commNbhd_add_one (h2 : (2 : GaloisField p f) ≠ 0) (hΩ : InClass p f Ω)
    (hex : ExactMembers Ω) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K₀)
    (hz : IsClassicalMember p f K₀ z₀)
    (hD1 : ∀ L ∈ centralizingMembers Ω {z₀}, L ≠ K₀ → Commutes K₀ L) {a : Subgroup G}
    (ha : a ∈ Ω) :
    (commNbhd Ω a).ncard + 1 = (centralizingMembers Ω {z₀}).ncard := by
  obtain ⟨u, hu⟩ := hΩ.classical a ha
  obtain ⟨g, hg⟩ := hsingle a ha
  have hu' : u = g * z₀ * g⁻¹ :=
    unique_involution_of_isClassicalMember h2 (hex a ha) hu (hg ▸ hz.conj g)
  have hmem : a ∈ centralizingMembers Ω {u} := ⟨ha, le_centralizer_of_isClassicalMember hu⟩
  rw [commNbhd_eq h2 hΩ hex hsingle hz hD1 ha hu,
    Set.ncard_sdiff_singleton_add_one hmem (Set.toFinite _), hu',
    ncard_centralizingMembers_conj hΩ.conjInvariant g z₀]

theorem false_of_nbhd_subset [IsSimpleGroup G] (hnab : ∃ x y : G, x * y ≠ y * x)
    (h2 : (2 : GaloisField p f) ≠ 0) (hΩ : InClass p f Ω) (hconn : DeltaConnected Ω)
    (hex : ExactMembers Ω) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K₀)
    (hz : IsClassicalMember p f K₀ z₀)
    (hD1 : ∀ L ∈ centralizingMembers Ω {z₀}, L ≠ K₀ → Commutes K₀ L) {K j₀ j₁ : Subgroup G}
    (hK : K ∈ Ω) (hj₀ : j₀ ∈ Ω) (hj₁ : j₁ ∈ Ω) (hKj₀ : Commutes K j₀)
    (hlayer : ∀ N ∈ Ω, Commutes K N → N ≤ j₀ ⊔ j₁)
    (hsub : ∀ N ∈ Ω, Commutes j₁ N → Commutes j₀ N) : False := by
  have hν : ∀ a ∈ Ω, (commNbhd Ω a).ncard + 1 = (centralizingMembers Ω {z₀}).ncard :=
    fun a ha => ncard_commNbhd_add_one h2 hΩ hex hsingle hz hD1 ha
  have hfin : ∀ a, (commNbhd Ω a).Finite := fun a => Set.toFinite _
  have hL : commNbhd Ω j₁ = commNbhd Ω j₀ := by
    refine Set.eq_of_subset_of_ncard_le (fun L hL => ⟨hL.1, hsub L hL.1 hL.2⟩) ?_ (hfin _)
    have h0 := hν j₀ hj₀
    have h1 := hν j₁ hj₁
    omega
  have hLM : ∀ K' ∈ commNbhd Ω j₀, ∀ N ∈ commNbhd Ω K, Commutes K' N := by
    intro K' hK' N hN
    have h0 : Commutes K' j₀ := hK'.2.symm
    have h1 : Commutes K' j₁ := (show K' ∈ commNbhd Ω j₁ from hL ▸ hK').2.symm
    exact fun a ha y hy => commutes_join_of_commutes h0 h1 a ha y (hlayer N hN.1 hN.2 hy)
  have hnK' : ∀ K' ∈ commNbhd Ω j₀, commNbhd Ω K' = commNbhd Ω K := by
    intro K' hK'
    apply Eq.symm
    refine Set.eq_of_subset_of_ncard_le (fun N hN => ⟨hN.1, hLM K' hK' N hN⟩) ?_ (hfin _)
    have h0 := hν K' hK'.1
    have h1 := hν K hK
    omega
  have hnN : ∀ N ∈ commNbhd Ω K, commNbhd Ω N = commNbhd Ω j₀ := by
    intro N hN
    apply Eq.symm
    refine Set.eq_of_subset_of_ncard_le
      (fun K' hK' => ⟨hK'.1, (hLM K' hK' N hN).symm⟩) ?_ (hfin _)
    have h0 := hν N hN.1
    have h1 := hν j₀ hj₀
    omega
  have hKL : K ∈ commNbhd Ω j₀ := ⟨hK, hKj₀.symm⟩
  have hS : Ω ⊆ commNbhd Ω j₀ ∪ commNbhd Ω K := by
    refine subset_of_adj_closed hconn (𝔖 := commNbhd Ω j₀ ∪ commNbhd Ω K) ?_ ⟨K, Or.inl hKL⟩ ?_
    · rintro N (hN | hN)
      exacts [hN.1, hN.1]
    · rintro A (hA | hA) L hL' hLA hc
      · exact Or.inr (hnK' A hA ▸ ⟨hL', hc⟩)
      · exact Or.inl (hnN A hA ▸ ⟨hL', hc⟩)
  let M₁ : Subgroup G := ⨆ L ∈ commNbhd Ω j₀, L
  have hle : ∀ N ∈ commNbhd Ω K, ∀ n ∈ N, M₁ ≤ Subgroup.centralizer ({n} : Set G) := by
    intro N hN n hn
    exact iSup₂_le fun L hL' l hl => Subgroup.mem_centralizer_singleton_iff.mpr
      (hLM L hL' N hN l hl n hn)
  have hcent : ∀ N ∈ commNbhd Ω K, ∀ n ∈ N, ∀ m ∈ M₁, n * m * n⁻¹ = m := by
    intro N hN n hn m hm
    rw [mul_inv_eq_iff_eq_mul]
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle N hN n hn hm)).symm
  have hnorm : M₁.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hΩ.generated]
    refine iSup₂_le fun N hN => ?_
    rcases hS hN with hN' | hN'
    · exact le_trans (le_iSup₂ (f := fun L (_ : L ∈ commNbhd Ω j₀) => L) N hN')
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
    have hKle : K ≤ M₁ := le_iSup₂ (f := fun L (_ : L ∈ commNbhd Ω j₀) => L) K hKL
    rw [h] at hKle
    have hu1 : u = 1 := Subgroup.mem_bot.mp (hKle hu.mem)
    have := hu.orderOf_eq_two
    rw [hu1, orderOf_one] at this
    omega
  · obtain ⟨u, hu⟩ := hΩ.classical j₀ hj₀
    have hj₀M : j₀ ∈ commNbhd Ω K := ⟨hj₀, hKj₀⟩
    have hmem : u ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : g ∈ M₁ := h ▸ Subgroup.mem_top g
      exact Subgroup.mem_centralizer_singleton_iff.mp (hle j₀ hj₀M u hu.mem hg)
    rw [center_eq_bot hnab, Subgroup.mem_bot] at hmem
    have := hu.orderOf_eq_two
    rw [hmem, orderOf_one] at this
    omega

end Neighbours

end CFSG.ClassicalInvolution.RouteD
