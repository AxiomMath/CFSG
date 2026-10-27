module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockAFiveDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockL28OrthPlus

public section

namespace CFSG.AGLEmbedding

open CFSG.Open
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs (isElemAbelian_range_of_pow
  plus_exists_torus_of_borel_le)

private theorem sixty_mem_of_isFiveComponent (hLB : LeviBlocksOfFiveComponents) {Y : Type}
    [Group Y] [Finite Y] {L P : Subgroup Y} (hPL : P ≤ L) {K : Type} [Group K] [Finite K]
    (ρ : K →* ↥L) (hρ : Function.Surjective ρ) (hker : ρ.ker ≤ Subgroup.center K) {𝒯 : Set ℕ}
    (hQ : HasLeviBlocks ↥((P.subgroupOf L).comap ρ) 𝒯) {C : Subgroup (↥P ⧸ CFSG.pCore 2 ↥P)}
    (hC : IsFiveComponent P C) : 60 ∈ 𝒯 := by
  obtain ⟨k, G, _, _, S, β, hkerβ, hpi, hcomm, hS, h𝒯⟩ := hQ
  obtain ⟨j, hq, h60⟩ := (hLB Y L P hPL K ρ hρ hker (Fin k) G S β hkerβ hpi hcomm hS).1 C hC
  exact h60 ▸ h𝒯 j hq

private theorem e9_of_torus {Y : Type} [Group Y] {L : Subgroup Y} {M : Type} [CommGroup M]
    (hM : Nat.card M = 3) (f : (Fin 2 → M) →* Y) (hf : Function.Injective f)
    (hL : f.range ≤ L) (hc : ∀ a, f a ∈ Subgroup.centralizer (L : Set Y) → a = 1) :
    ∃ E : Subgroup Y, E ≤ L ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 2 ∧
      E ⊓ Subgroup.centralizer (L : Set Y) = ⊥ := by
  have hpow : ∀ a : Fin 2 → M, a ^ 3 = 1 := fun a => funext fun j => by
    rw [Pi.pow_apply, Pi.one_apply, ← hM]
    exact pow_card_eq_one'
  refine ⟨f.range, hL, isElemAbelian_range_of_pow (fun a b => mul_comm a b) hpow f, ?_, ?_⟩
  · rw [← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv, Nat.card_fun, hM, Nat.card_fin]
  · rw [eq_bot_iff]
    rintro _ ⟨⟨a, rfl⟩, hxC⟩
    rw [hc a hxC, map_one]
    exact Subgroup.one_mem _

private theorem plus_card_eq_four (hLB : LeviBlocksOfFiveComponents) {Y : Type} [Group Y]
    [Finite Y] {L P : Subgroup Y} (hPL : P ≤ L) {E : Type} [Group E] (ρ : E ≃* ↥L) {K : Type}
    [Field K] [Finite K] [CharP K 2]
    (hQ : HasLeviBlocks ↥((P.subgroupOf L).comap ρ.toMonoidHom) (plusBlockOrders (Nat.card K)))
    {C : Subgroup (↥P ⧸ CFSG.pCore 2 ↥P)} (hC : IsFiveComponent P C) : Nat.card K = 4 := by
  have := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  have hK : Nat.card K = 2 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  have : Finite E := Finite.of_equiv _ ρ.symm.toEquiv
  have hker : ρ.toMonoidHom.ker ≤ Subgroup.center E := by
    rw [(MonoidHom.ker_eq_bot_iff _).2 ρ.injective]
    exact bot_le
  exact eq_four_of_sixty_mem_plusBlockOrders hK
    (sixty_mem_of_isFiveComponent hLB hPL ρ.toMonoidHom ρ.surjective hker hQ hC)

theorem kFactCompParabTwoFivesOn_idxD (hZ : OddCenterRest) (hLB : LeviBlocksOfFiveComponents) :
    KFactCompParabTwoFivesOn (IsLieOf IdxD) := by
  intro Y _ _ L P hCP hD h3 C₁ _ _ hC₁ _
  obtain ⟨r, K, _, _, _, ρ, hr, hQ, hB⟩ := LeviBlock.exists_hasLeviBlocks_of_idxD hZ hCP hD
  have hP := LeviBlock.four_le_pRank_of_borel_le (plus_card_eq_four hLB hCP.parab.1 ρ hQ hC₁) hr
    ρ hB
  have hPL := CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) hCP.parab.1
  omega

theorem kFactCompParabOneFiveOn_idxD (hZ : OddCenterRest) (hLB : LeviBlocksOfFiveComponents) :
    KFactCompParabOneFiveOn (IsLieOf IdxD) := by
  intro Y _ _ L P hCP hD C hC
  obtain ⟨r, K, _, _, _, ρ, hr, hQ, hB⟩ := LeviBlock.exists_hasLeviBlocks_of_idxD hZ hCP hD
  have hu : Nat.card Kˣ = 3 := by
    rw [Nat.card_units, plus_card_eq_four hLB hCP.parab.1 ρ hQ hC]
  have hPL : P ≤ L := hCP.parab.1
  have hZ1 : Subgroup.center ↥L = ⊥ := by
    refine Subgroup.eq_bot_of_card_eq _ ?_
    rcases hZ Y L hCP.comp hCP.odd (Or.inr (Or.inl hD)) with h1 | ⟨h3, ⟨e6⟩⟩
    · exact h1
    · exfalso
      obtain ⟨f4, hf4, hf4P⟩ := plus_exists_torus_of_borel_le (k := 4) (by omega) hr ρ hB
      have h81 : Nat.card (Fin 4 → Kˣ) ∣ Nat.card ↥L := by
        rw [Nat.card_congr (MonoidHom.ofInjective hf4).toEquiv]
        exact Subgroup.card_dvd_of_le (hf4P.trans hPL)
      rw [Nat.card_fun, hu, Nat.card_fin,
        Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥L), h3,
        Nat.card_congr e6.toEquiv, nat_card_alternatingGroup, Nat.card_fin] at h81
      exact absurd h81 (by decide)
  obtain ⟨f2, hf2, hf2P⟩ := plus_exists_torus_of_borel_le (k := 2) (by omega) (by omega) ρ hB
  refine Or.inl (e9_of_torus hu f2 hf2 (hf2P.trans hPL) fun a ha => ?_)
  have hmem : (⟨f2 a, hf2P.trans hPL ⟨a, rfl⟩⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 ha g g.2)
  rw [hZ1, Subgroup.mem_bot] at hmem
  exact hf2 ((congrArg Subtype.val hmem).trans (map_one f2).symm)

end CFSG.AGLEmbedding
