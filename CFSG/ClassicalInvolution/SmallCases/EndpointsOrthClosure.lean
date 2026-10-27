module

public import CFSG.ClassicalInvolution.RouteD.TypeF4Closure
public import CFSG.ClassicalInvolution.RouteD.LocalTwin

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.ClassicalInvolution.Generic

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

theorem surjective_of_layer_closure [Finite G] {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω)
    (hconn : DeltaConnected Ω) {K : Subgroup G} (hK : K ∈ Ω)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) {z : G} (hz : IsClassicalMember p f K z)
    (hP1 : LocalOddCentral Ω {z}) {KT : Type} [Group KT] {FT : Set (Subgroup KT)}
    (hFTconj : ∀ R ∈ FT, ∀ g : KT, conjSub g R ∈ FT)
    (hFTsingle : ∀ R ∈ FT, ∀ R' ∈ FT, ∃ g : KT, R' = conjSub g R) (Ψ : KT →* G)
    (hΩΨ : ∀ R ∈ FT, R.map Ψ ∈ Ω) {N₀R TR : Subgroup KT} (hN₀R : N₀R ∈ FT) (hTR : TR ∈ FT)
    (hTN : Commutes (TR.map Ψ) (N₀R.map Ψ)) {KY : Type} [Group KY] {Y : Set (Subgroup KY)}
    (ψD : KY →* G) (hkerD : ψD.ker ≤ Subgroup.center KY) (hYperf : ∀ R ∈ Y, R ≤ ⁅R, R⁆)
    (hYFT : ∀ R ∈ Y, ∃ S ∈ FT, R.map ψD = S.map Ψ)
    (hYN : ∀ R ∈ Y, Commutes (R.map ψD) (N₀R.map Ψ))
    (hYT : ∀ R ∈ Y, Commutes (TR.map Ψ) (R.map ψD))
    (hcount : (locFamily Ω z).ncard ≤ 2 + Y.ncard) :
    (∀ L : Subgroup G, L ∈ Ω ↔ ∃ R ∈ FT, L = R.map Ψ) ∧ Function.Surjective Ψ := by
  classical
  set 𝔖 : Set (Subgroup G) := {L | ∃ R ∈ FT, L = R.map Ψ} with h𝔖
  have hΩ𝔖 : 𝔖 ⊆ Ω := by
    rintro _ ⟨R, hR, rfl⟩
    exact hΩΨ R hR
  set N₀ : Subgroup G := N₀R.map Ψ with hN₀
  have hN₀𝔖 : N₀ ∈ 𝔖 := ⟨_, hN₀R, rfl⟩
  set T : Subgroup G := TR.map Ψ with hT
  have hT𝔖 : T ∈ 𝔖 := ⟨_, hTR, rfl⟩
  set 𝓡 : Set (Subgroup G) := insert T ((fun R => R.map ψD) '' Y) with h𝓡
  have h𝓡𝔖 : 𝓡 ⊆ 𝔖 := by
    rintro _ (rfl | ⟨R, hR, rfl⟩)
    · exact hT𝔖
    · obtain ⟨S, hS, hRS⟩ := hYFT R hR
      exact ⟨S, hS, hRS⟩
  have hcommR : ∀ R ∈ 𝓡, Commutes R N₀ := by
    rintro _ (rfl | ⟨R, hR, rfl⟩)
    · exact hTN
    · exact hYN R hR
  have hTnot : T ∉ (fun R => R.map ψD) '' Y := by
    rintro ⟨R, hR, hRT⟩
    have h1 := hYT R hR
    have h2 : Commutes T T := by
      simpa only [hRT] using h1
    exact not_commutes_self_of_mem hΩ (hΩ𝔖 hT𝔖) h2
  have hinj : Set.InjOn (fun R => R.map ψD) Y := fun R hR R' hR' h =>
    eq_of_map_eq_of_perfect_ker_central ψD hkerD (hYperf R hR) (hYperf R' hR') h
  have hcard : (centralizingMembers Ω {z}).ncard ≤ 1 + 𝓡.ncard := by
    rw [ncard_centralizingMembers_eq hΩ hP1, h𝓡, Set.ncard_insert_of_notMem hTnot (Set.toFinite _),
      hinj.ncard_image]
    omega
  have hH : ∀ N ∈ 𝔖, ∃ g ∈ Ψ.range, N = conjSub g N₀ := by
    rintro _ ⟨R, hR, rfl⟩
    obtain ⟨g, hg⟩ := hFTsingle N₀R hN₀R R hR
    exact ⟨Ψ g, ⟨g, rfl⟩, by rw [hg, map_conjSub_eq]⟩
  have hinv : ∀ g ∈ Ψ.range, ∀ M ∈ 𝔖, conjSub g M ∈ 𝔖 := by
    rintro _ ⟨h, rfl⟩ _ ⟨R, hR, rfl⟩
    exact ⟨conjSub h R, hFTconj R hR h, by rw [map_conjSub_eq]⟩
  have hcl := adj_closed_of_base_members hΩ hK hsingle hz hΩ𝔖 hN₀𝔖 h𝓡𝔖 hcommR hcard hH hinv
  have hΩsub : Ω ⊆ 𝔖 := subset_of_adj_closed hconn hΩ𝔖 ⟨N₀, hN₀𝔖⟩ hcl
  refine ⟨fun L => ⟨fun hL => hΩsub hL, fun hL => hΩ𝔖 hL⟩, ?_⟩
  refine MonoidHom.range_eq_top.mp (eq_top_iff.mpr ?_)
  calc (⊤ : Subgroup G) = ⨆ L ∈ Ω, L := hΩ.generated.symm
    _ ≤ Ψ.range := iSup₂_le fun L hL => by
      obtain ⟨R, -, rfl⟩ := hΩsub hL
      exact Subgroup.map_le_range Ψ R

end CFSG.ClassicalInvolution.RouteD
