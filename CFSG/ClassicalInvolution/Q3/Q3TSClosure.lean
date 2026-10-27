module

public import CFSG.ClassicalInvolution.Q3.Q3WAClose
public import CFSG.ClassicalInvolution.Q3.Q3WAPow
public import CFSG.ClassicalInvolution.RouteD.LocalTwin

public section

namespace CFSG.ClassicalInvolution.Q3.Q3TS

open CFSG.Open hiding StatedLieTag
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.Q3.Q3W CFSG.Assembly.LowTwoRank

theorem surjective_of_layer_closure3 {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω) (hconn : RouteD.DeltaConnected Ω)
    {K : Subgroup G} (hK : K ∈ Ω) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) {z : G}
    (hz : IsClassicalMember3 K z) (hP1 : LocalOddCentral Ω {z}) (hO3 : LocalOddThreeFree3 Ω z)
    {KT : Type} [Group KT] {FT : Set (Subgroup KT)}
    (hFTconj : ∀ R ∈ FT, ∀ g : KT, conjSub g R ∈ FT)
    (hFTsingle : ∀ R ∈ FT, ∀ R' ∈ FT, ∃ g : KT, R' = conjSub g R) (Ψ : KT →* G)
    (hΩΨ : ∀ R ∈ FT, R.map Ψ ∈ Ω) {N₀R TR : Subgroup KT} (hN₀R : N₀R ∈ FT) (hTR : TR ∈ FT)
    (hTN : Commutes (TR.map Ψ) (N₀R.map Ψ)) {KY : Type} [Group KY] {Y : Set (Subgroup KY)}
    (ψD : KY →* G) (hkerD : ψD.ker ≤ Subgroup.center KY)
    (hcopD : ∀ w ∈ ψD.ker, ¬ 3 ∣ orderOf w) (hYpow : ∀ R ∈ Y, Pow3 R)
    (hYFT : ∀ R ∈ Y, ∃ S ∈ FT, R.map ψD = S.map Ψ)
    (hYN : ∀ R ∈ Y, Commutes (R.map ψD) (N₀R.map Ψ))
    (hYT : ∀ R ∈ Y, Commutes (TR.map Ψ) (R.map ψD))
    (hcount : (locFamily Ω z).ncard ≤ 2 + Y.ncard) :
    (∀ L : Subgroup G, L ∈ Ω ↔ ∃ R ∈ FT, L = R.map Ψ) ∧ Function.Surjective Ψ := by
  classical
  have hnc : ∀ L ∈ Ω, ¬ Commutes L L := fun L hL => by
    obtain ⟨w, hw⟩ := hΩ.classical L hL
    exact not_commutes_self3 hw
  set 𝔖 : Set (Subgroup G) := {L | ∃ R ∈ FT, L = R.map Ψ} with h𝔖
  have hsub : 𝔖 ⊆ Ω := by
    rintro _ ⟨R, hR, rfl⟩
    exact hΩΨ R hR
  set N₀ : Subgroup G := N₀R.map Ψ with hN₀
  have hN₀𝔖 : N₀ ∈ 𝔖 := ⟨_, hN₀R, rfl⟩
  have hN₀Ω : N₀ ∈ Ω := hsub hN₀𝔖
  set T : Subgroup G := TR.map Ψ with hT
  have hT𝔖 : T ∈ 𝔖 := ⟨_, hTR, rfl⟩
  obtain ⟨g₀, hg₀⟩ := hsingle N₀ hN₀Ω
  have hxN : g₀ * z * g₀⁻¹ ∈ N₀ := by
    rw [hg₀]
    exact conj_mem_conjSub hz.mem
  set x : G := g₀ * z * g₀⁻¹ with hx
  have hK₀z : K ∈ centralizingMembers Ω {z} := ⟨hK, isSubnormal_le hz.subnormal⟩
  have hN₀x : N₀ ∈ centralizingMembers Ω {x} := by
    rw [hx, centralizingMembers_conj hΩ.conjInvariant g₀ z]
    exact ⟨K, hK₀z, hg₀.symm⟩
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
  have h𝓡sub : 𝓡 ⊆ centralizingMembers Ω {x} := fun S hS =>
    mem_centralizingMembers_of_commutes (hsub (h𝓡𝔖 hS)) hxN (hcommR S hS)
  have hN₀R' : N₀ ∉ 𝓡 := by
    intro hmem
    exact hnc N₀ hN₀Ω (hcommR N₀ hmem)
  have hTnot : T ∉ (fun R => R.map ψD) '' Y := by
    rintro ⟨R, hR, hRT⟩
    have h1 := hYT R hR
    have h2 : Commutes T T := by
      simpa only [hRT] using h1
    exact hnc T (hsub hT𝔖) h2
  have hinj : Set.InjOn (fun R => R.map ψD) Y := by
    intro R hR R' hR' h
    exact eq_of_map_eq_of_pow3 ψD hkerD hcopD (hYpow R hR) (hYpow R' hR') h
  have h𝓡card : 𝓡.ncard = 1 + Y.ncard := by
    rw [h𝓡, Set.ncard_insert_of_notMem hTnot (Set.toFinite _), hinj.ncard_image]
    omega
  have hcard : (centralizingMembers Ω {x}).ncard ≤ 1 + 𝓡.ncard := by
    rw [hx, ncard_centralizingMembers_conj hΩ.conjInvariant,
      ncard_centralizingMembers_eq3 hΩ hex hP1 hO3, h𝓡card]
    omega
  have hEq : centralizingMembers Ω {x} = insert N₀ 𝓡 :=
    centralizingMembers_eq_insert hN₀x h𝓡sub hN₀R' hcard
  have hcl : ∀ N ∈ 𝔖, ∀ L ∈ Ω, L ≠ N → Commutes N L → L ∈ 𝔖 := by
    rintro N ⟨R, hR, rfl⟩ L hL hLN hcomm
    obtain ⟨h, hh⟩ := hFTsingle N₀R hN₀R R hR
    have hNeq : R.map Ψ = conjSub (Ψ h) N₀ := by
      rw [hh, hN₀, conjSub_map]
    set L' := conjSub (Ψ h)⁻¹ L with hL'
    have hL'Ω : L' ∈ Ω := hΩ.conjInvariant _ L hL
    have hLL' : L = conjSub (Ψ h) L' := (conjSub_conjSub_inv _ L).symm
    have hL'N : L' ≠ N₀ := fun e => hLN (by rw [hNeq, hLL', e])
    have hcomm' : Commutes N₀ L' := by
      rw [hNeq, hLL'] at hcomm
      exact (commutes_conjSub_iff _).mp hcomm
    have hL'x : L' ∈ centralizingMembers Ω {x} :=
      mem_centralizingMembers_of_commutes hL'Ω hxN hcomm'.symm
    rw [hEq] at hL'x
    rcases hL'x with h1 | h1
    · exact absurd h1 hL'N
    · obtain ⟨S, hS, hSL'⟩ : ∃ S ∈ FT, L' = S.map Ψ := by
        have := h𝓡𝔖 h1
        obtain ⟨S, hS, hSL⟩ := this
        exact ⟨S, hS, hSL⟩
      refine ⟨conjSub h S, hFTconj S hS h, ?_⟩
      rw [hLL', hSL', conjSub_map]
  have hΩsub : Ω ⊆ 𝔖 := subset_of_adj_closed hconn hsub ⟨N₀, hN₀𝔖⟩ hcl
  refine ⟨fun L => ⟨fun hL => hΩsub hL, fun hL => hsub hL⟩, ?_⟩
  refine MonoidHom.range_eq_top.mp (eq_top_iff.mpr ?_)
  calc (⊤ : Subgroup G) = ⨆ L ∈ Ω, L := hΩ.generated.symm
    _ ≤ Ψ.range := iSup₂_le fun L hL => by
      obtain ⟨R, -, rfl⟩ := hΩsub hL
      exact Subgroup.map_le_range Ψ R

end CFSG.ClassicalInvolution.Q3.Q3TS
