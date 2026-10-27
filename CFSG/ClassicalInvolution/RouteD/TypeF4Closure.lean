module

public import CFSG.ClassicalInvolution.RouteD.ConsistencyA

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.ClassicalInvolution.Generic

section Perfect

theorem map_conjSub_eq {X Y : Type*} [Group X] [Group Y] (φ : X →* Y) (g : X)
    (R : Subgroup X) : (conjSub g R).map φ = conjSub (φ g) (R.map φ) :=
  map_map_conj φ g R

theorem eq_of_map_eq_of_perfect_ker_central {H X : Type*} [Group H] [Group X] (φ : H →* X)
    (hker : φ.ker ≤ Subgroup.center H) {A B : Subgroup H} (hA : A ≤ ⁅A, A⁆) (hB : B ≤ ⁅B, B⁆)
    (h : A.map φ = B.map φ) : A = B := by
  have key : ∀ A B : Subgroup H, A.map φ = B.map φ → A ≤ B ⊔ φ.ker := by
    intro A B hAB a ha
    have : φ a ∈ B.map φ := hAB ▸ ⟨a, ha, rfl⟩
    obtain ⟨b, hb, hba⟩ := this
    have hmem : b⁻¹ * a ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hba, inv_mul_cancel]
    have : a = b * (b⁻¹ * a) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hb) (Subgroup.mem_sup_right hmem)
  exact le_antisymm (le_of_perfect_of_le_sup_center hker hA (key A B h))
    (le_of_perfect_of_le_sup_center hker hB (key B A h.symm))

theorem conjSub_perfect {G : Type*} [Group G] {A : Subgroup G} (hA : A ≤ ⁅A, A⁆) (g : G) :
    conjSub g A ≤ ⁅conjSub g A, conjSub g A⁆ := by
  unfold conjSub
  rw [← Subgroup.map_commutator]
  exact Subgroup.map_mono hA

theorem commutes_map_hom {X Y : Type*} [Group X] [Group Y] (φ : X →* Y) {A B : Subgroup X}
    (h : Commutes A B) : Commutes (A.map φ) (B.map φ) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  rw [← map_mul, ← map_mul, h x hx y hy]


theorem commutes_sup_of_both {G : Type*} [Group G] {A₁ A₂ B : Subgroup G} (h₁ : Commutes A₁ B)
    (h₂ : Commutes A₂ B) : Commutes (A₁ ⊔ A₂) B := by
  intro y hy b hb
  have : A₁ ⊔ A₂ ≤ Subgroup.centralizer (B : Set G) :=
    sup_le (fun y hy => Subgroup.mem_centralizer_iff.mpr fun b hb => (h₁ y hy b hb).symm)
      (fun y hy => Subgroup.mem_centralizer_iff.mpr fun b hb => (h₂ y hy b hb).symm)
  exact (Subgroup.mem_centralizer_iff.mp (this hy) b hb).symm


theorem commutes_sup_sup {G : Type*} [Group G] {A₁ A₂ B₁ B₂ : Subgroup G} (h11 : Commutes A₁ B₁)
    (h12 : Commutes A₁ B₂) (h21 : Commutes A₂ B₁) (h22 : Commutes A₂ B₂) :
    Commutes (A₁ ⊔ A₂) (B₁ ⊔ B₂) :=
  commutes_sup_of_both (commutes_sup_of_both h11.symm h12.symm).symm
    (commutes_sup_of_both h21.symm h22.symm).symm

theorem commutes_iSup_of_forall {G : Type*} [Group G] {ι : Type*} {A : ι → Subgroup G}
    {B : Subgroup G} (h : ∀ i, Commutes (A i) B) : Commutes (⨆ i, A i) B := by
  intro y hy b hb
  have : (⨆ i, A i) ≤ Subgroup.centralizer (B : Set G) :=
    iSup_le fun i y hy => Subgroup.mem_centralizer_iff.mpr fun b hb => (h i y hy b hb).symm
  exact (Subgroup.mem_centralizer_iff.mp (this hy) b hb).symm

end Perfect

section Closure

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

theorem adj_closed_of_base_members [Finite G] {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω)
    {K : Subgroup G} (hK : K ∈ Ω) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) {z : G}
    (hz : IsClassicalMember p f K z) {𝔖 : Set (Subgroup G)} (hsub : 𝔖 ⊆ Ω) {N₀ : Subgroup G}
    (hN₀ : N₀ ∈ 𝔖) {𝓡 : Set (Subgroup G)} (h𝓡 : 𝓡 ⊆ 𝔖) (hcomm : ∀ R ∈ 𝓡, Commutes R N₀)
    (hcard : (centralizingMembers Ω {z}).ncard ≤ 1 + 𝓡.ncard) {H : Subgroup G}
    (hH : ∀ N ∈ 𝔖, ∃ g ∈ H, N = conjSub g N₀) (hinv : ∀ g ∈ H, ∀ M ∈ 𝔖, conjSub g M ∈ 𝔖) :
    ∀ N ∈ 𝔖, ∀ L ∈ Ω, L ≠ N → Commutes N L → L ∈ 𝔖 := by
  have hKz : K ∈ centralizingMembers Ω {z} := ⟨hK, le_centralizer_of_isClassicalMember hz⟩
  obtain ⟨g₀, hg₀⟩ := hsingle N₀ (hsub hN₀)
  have hxN : g₀ * z * g₀⁻¹ ∈ N₀ := by
    rw [hg₀]
    exact conj_mem_conjSub hz.mem
  have hNm : N₀ ∈ centralizingMembers Ω {g₀ * z * g₀⁻¹} := by
    rw [centralizingMembers_conj hΩ.conjInvariant g₀ z]
    exact ⟨K, hKz, hg₀.symm⟩
  have h𝓡x : 𝓡 ⊆ centralizingMembers Ω {g₀ * z * g₀⁻¹} := fun R hR =>
    ⟨hsub (h𝓡 hR), fun y hy => by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hcomm R hR y hy _ hxN⟩
  have hNR : N₀ ∉ 𝓡 := fun h => by
    have h1 := hcomm N₀ h
    rw [hg₀] at h1
    exact not_commutes_self_of_isClassicalMember hz ((commutes_conjSub_iff g₀).mp h1)
  have hcard' : (centralizingMembers Ω {g₀ * z * g₀⁻¹}).ncard ≤ 1 + 𝓡.ncard := by
    rw [ncard_centralizingMembers_conj hΩ.conjInvariant]
    exact hcard
  have hΩx := centralizingMembers_eq_insert hNm h𝓡x hNR hcard'
  intro N hN L hL hLN hcommNL
  obtain ⟨g, hgH, hNg⟩ := hH N hN
  set L' := conjSub g⁻¹ L with hL'
  have hL'Ω : L' ∈ Ω := hΩ.conjInvariant _ L hL
  have hLL' : L = conjSub g L' := (conjSub_conjSub_inv g L).symm
  have hL'N : L' ≠ N₀ := fun e => hLN (by rw [hLL', e, ← hNg])
  have hcomm' : Commutes N₀ L' := by
    rw [hNg, hLL'] at hcommNL
    exact (commutes_conjSub_iff g).mp hcommNL
  have hL'x : L' ∈ centralizingMembers Ω {g₀ * z * g₀⁻¹} :=
    ⟨hL'Ω, fun y hy => by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hcomm' _ hxN y hy).symm⟩
  rw [hΩx] at hL'x
  rcases hL'x with h | h
  · exact absurd h hL'N
  · rw [hLL']
    exact hinv g hgH L' (h𝓡 h)

end Closure

end CFSG.ClassicalInvolution.RouteD
