module

public import CFSG.ClassicalInvolution.RouteD.SmallTwinChainClosure

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD.Gaps

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K₀ : Subgroup G} {z₀ : G}

theorem commNbhd_eq_insert (h2 : (2 : GaloisField p f) ≠ 0) (hΩ : InClass p f Ω)
    (hex : ExactMembers Ω) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K₀)
    (hz : IsClassicalMember p f K₀ z₀)
    (hD1 : ∀ L ∈ centralizingMembers Ω {z₀}, L ≠ K₀ → Commutes K₀ L) {R : Set (Subgroup G)}
    (hRΩ : R ⊆ Ω) (hcard : (centralizingMembers Ω {z₀}).ncard ≤ R.ncard + 2)
    {a b : Subgroup G} (ha : a ∈ Ω) (hb : b ∈ Ω) (hRa : ∀ L ∈ R, Commutes a L)
    (hba : Commutes a b) (hbR : b ∉ R) : commNbhd Ω a = insert b R := by
  have hν := ncard_commNbhd_add_one h2 hΩ hex hsingle hz hD1 ha
  have hsub : insert b R ⊆ commNbhd Ω a := by
    intro L hL
    rcases hL with rfl | hL
    · exact ⟨hb, hba⟩
    · exact ⟨hRΩ hL, hRa L hL⟩
  have hins : (insert b R).ncard = R.ncard + 1 := Set.ncard_insert_of_notMem hbR (Set.toFinite _)
  exact (Set.eq_of_subset_of_ncard_le hsub (by omega) (Set.toFinite _)).symm

theorem false_of_bipartite [IsSimpleGroup G] (hnab : ∃ x y : G, x * y ≠ y * x)
    (h2 : (2 : GaloisField p f) ≠ 0) (hΩ : InClass p f Ω) (hconn : DeltaConnected Ω)
    (hex : ExactMembers Ω) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K₀)
    (hz : IsClassicalMember p f K₀ z₀)
    (hD1 : ∀ L ∈ centralizingMembers Ω {z₀}, L ≠ K₀ → Commutes K₀ L) {P Q : Set (Subgroup G)}
    (hPΩ : P ⊆ Ω) (hQΩ : Q ⊆ Ω) (hPne : P.Nonempty) (hQne : Q.Nonempty)
    (hPQ : ∀ N ∈ P, ∀ M ∈ Q, Commutes N M)
    (hPcard : (centralizingMembers Ω {z₀}).ncard ≤ P.ncard + 2)
    (hQcard : (centralizingMembers Ω {z₀}).ncard ≤ Q.ncard + 2)
    (hPpart : ∀ N ∈ P, ∃ N' ∈ P, Commutes N N')
    (hQpart : ∀ M ∈ Q, ∃ M' ∈ Q, Commutes M M') : False := by
  have hdisj : ∀ N ∈ P, N ∉ Q := fun N hN hNQ =>
    not_commutes_self_of_mem hΩ (hPΩ hN) (hPQ N hN N hNQ)
  have hnbP : ∀ N ∈ P, ∃ N' ∈ P, commNbhd Ω N = insert N' Q := by
    intro N hN
    obtain ⟨N', hN', hNN'⟩ := hPpart N hN
    exact ⟨N', hN', commNbhd_eq_insert h2 hΩ hex hsingle hz hD1 hQΩ hQcard (hPΩ hN) (hPΩ hN')
      (hPQ N hN) hNN' (hdisj N' hN')⟩
  have hnbQ : ∀ M ∈ Q, ∃ M' ∈ Q, commNbhd Ω M = insert M' P := by
    intro M hM
    obtain ⟨M', hM', hMM'⟩ := hQpart M hM
    refine ⟨M', hM', commNbhd_eq_insert h2 hΩ hex hsingle hz hD1 hPΩ hPcard (hQΩ hM) (hQΩ hM')
      (fun N hN => (hPQ N hN M hM).symm) hMM' ?_⟩
    intro hM'P
    exact hdisj M' hM'P hM'
  have hall : Ω ⊆ P ∪ Q := by
    refine subset_of_adj_closed hconn (Set.union_subset hPΩ hQΩ)
      (hPne.mono Set.subset_union_left) ?_
    intro N hN L hL hLN hc
    rcases hN with hN | hN
    · obtain ⟨N', hN', hnb⟩ := hnbP N hN
      have hmem : L ∈ commNbhd Ω N := ⟨hL, hc⟩
      rw [hnb] at hmem
      rcases hmem with rfl | hmem
      · exact Or.inl hN'
      · exact Or.inr hmem
    · obtain ⟨M', hM', hnb⟩ := hnbQ N hN
      have hmem : L ∈ commNbhd Ω N := ⟨hL, hc⟩
      rw [hnb] at hmem
      rcases hmem with rfl | hmem
      · exact Or.inr hM'
      · exact Or.inl hmem
  let M₁ : Subgroup G := ⨆ N ∈ P, N
  have hle : ∀ M ∈ Q, ∀ m ∈ M, M₁ ≤ Subgroup.centralizer ({m} : Set G) := by
    intro M hM m hm
    refine iSup₂_le fun N hN n hn => ?_
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hPQ N hN M hM n hn m hm)
  have hcent : ∀ M ∈ Q, ∀ n ∈ M, ∀ m ∈ M₁, n * m * n⁻¹ = m := by
    intro M hM n hn m hm
    rw [mul_inv_eq_iff_eq_mul]
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle M hM n hn hm)).symm
  have hnorm : M₁.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hΩ.generated]
    refine iSup₂_le fun N hN => ?_
    rcases hall hN with hN' | hN'
    · exact le_trans (le_iSup₂ (f := fun L (_ : L ∈ P) => L) N hN') Subgroup.le_normalizer
    · intro n hn
      refine Subgroup.mem_normalizer_iff.mpr fun m => ⟨fun hm => ?_, fun hm => ?_⟩
      · rw [hcent N hN' n hn m hm]
        exact hm
      · have h1 := hcent N hN' n⁻¹ (N.inv_mem hn) _ hm
        have h3 : n⁻¹ * (n * m * n⁻¹) * n⁻¹⁻¹ = m := by group
        rw [h3] at h1
        rw [h1]
        exact hm
  have := hnorm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal M₁ with h | h
  · obtain ⟨N, hN⟩ := hPne
    obtain ⟨u, hu⟩ := hΩ.classical N (hPΩ hN)
    have hNle : N ≤ M₁ := le_iSup₂ (f := fun L (_ : L ∈ P) => L) N hN
    rw [h] at hNle
    have hu1 : u = 1 := Subgroup.mem_bot.mp (hNle hu.mem)
    have := hu.orderOf_eq_two
    rw [hu1, orderOf_one] at this
    omega
  · obtain ⟨M, hM⟩ := hQne
    obtain ⟨u, hu⟩ := hΩ.classical M (hQΩ hM)
    have hmem : u ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : g ∈ M₁ := h ▸ Subgroup.mem_top g
      exact Subgroup.mem_centralizer_singleton_iff.mp (hle M hM u hu.mem hg)
    rw [center_eq_bot hnab, Subgroup.mem_bot] at hmem
    have := hu.orderOf_eq_two
    rw [hmem, orderOf_one] at this
    omega

end CFSG.ClassicalInvolution.RouteD
