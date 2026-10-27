module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockAFiveDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockL28Symp
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockSympMain

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial LeviBlock
  CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
open SymplecticHigher (flagStabilizer)

private theorem sympFive_two_blocks {r : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {I : Set ℕ} (hI : ∀ i ∈ I, 1 ≤ i ∧ i ≤ r) (hI' : ∀ i ∈ I, i ≤ r) {t : ℕ} (htI : t ∈ I)
    (hmax : ∀ c ∈ I, c ≤ t) {j₁ j₂ : Fin (r + 1)} (hne : j₁ ≠ j₂)
    (hq₁ : CFSG.Open.IsQuasisimple (spFlagLeviBlock (K := K) hI' t j₁))
    (h₁ : Nat.card (↥(spFlagLeviBlock (K := K) hI' t j₁) ⧸
      Subgroup.center ↥(spFlagLeviBlock (K := K) hI' t j₁)) = 60)
    (hq₂ : CFSG.Open.IsQuasisimple (spFlagLeviBlock (K := K) hI' t j₂))
    (h₂ : Nat.card (↥(spFlagLeviBlock (K := K) hI' t j₂) ⧸
      Subgroup.center ↥(spFlagLeviBlock (K := K) hI' t j₂)) = 60) :
    Nat.card K = 4 ∧ 3 ≤ r ∧ (r ≤ 3 → I = {2}) := by
  obtain ⟨hK, -, h1⟩ := spFlagLeviBlock_sixty hI' t hq₁ h₁
  obtain ⟨-, -, h2⟩ := spFlagLeviBlock_sixty hI' t hq₂ h₂
  have htr : t ≤ r := hI' t htI
  have hne' : (j₁ : ℕ) ≠ (j₂ : ℕ) := fun h => hne (Fin.ext h)
  have key : ∀ b ∈ I, b - spFlagPrev I b = 2 → r - t = 1 → 3 ≤ r ∧ (r ≤ 3 → I = {2}) := by
    intro b hbI hb2 hrt
    have hbt := hmax b hbI
    refine ⟨by omega, fun hr => ?_⟩
    have ht : t = 2 := by omega
    obtain rfl : b = 2 := by omega
    ext i
    simp only [Set.mem_singleton_iff]
    refine ⟨fun hi => ?_, fun hi => by rw [hi, ← ht]; exact htI⟩
    have hi1 := hI i hi
    have hit := hmax i hi
    by_contra hi2
    have hp := le_spFlagPrev hi (show i < 2 by omega)
    omega
  rcases h1 with ⟨h10, h1r⟩ | ⟨-, h1I, h1p⟩ <;> rcases h2 with ⟨h20, h2r⟩ | ⟨-, h2I, h2p⟩
  · exact absurd (h10.trans h20.symm) hne'
  · exact ⟨hK, key _ h2I h2p h1r⟩
  · exact ⟨hK, key _ h1I h1p h2r⟩
  · have h4 : 4 ≤ r := by
      rcases lt_or_gt_of_ne hne' with h | h
      · have := le_spFlagPrev h1I h
        have := hI' _ h2I
        omega
      · have := le_spFlagPrev h2I h
        have := hI' _ h1I
        omega
    exact ⟨hK, by omega, fun hr => absurd hr (by omega)⟩

private theorem sympFive_e9_of_torus {Y : Type} [Group Y] {L : Subgroup Y} {r : ℕ} {K : Type}
    [Field K] [CharP K 2] {M : Type*} [CommGroup M] (hM : Nat.card M = 3)
    (ρ : StatedSp r K ≃* ↥L) (τ : (Fin 2 → M) →* Y) (hτ : Function.Injective τ)
    (hL : τ.range ≤ L) :
    ∃ E : Subgroup Y, E ≤ L ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 2 ∧
      E ⊓ Subgroup.centralizer (L : Set Y) = ⊥ := by
  have hcen : ∀ z : ↥L, z ∈ Subgroup.center ↥L → z = 1 := by
    intro z hz
    have hz' : ρ.symm z ∈ Subgroup.center ↥(StatedSp r K) := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro g
      apply ρ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hz (ρ g)
    rw [CFSG.LieType.Universal.Symplectic.center_eq,
      CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot, Subgroup.mem_bot] at hz'
    simpa using congrArg ρ hz'
  refine ⟨τ.range, hL, isElemAbelian_range_of_pow (fun a b => mul_comm a b) (fun a => ?_) τ, ?_,
    ?_⟩
  · funext j
    rw [Pi.pow_apply, Pi.one_apply, ← hM]
    exact pow_card_eq_one'
  · rw [← Nat.card_congr (MonoidHom.ofInjective hτ).toEquiv, Nat.card_fun, hM, Nat.card_fin]
  · rw [eq_bot_iff]
    rintro _ ⟨⟨a, rfl⟩, hxC⟩
    have h1 := hcen ⟨τ a, hL ⟨a, rfl⟩⟩ (by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp hxC g g.2)
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val h1

theorem kFactCompParabTwoFivesOn_idxB (hLB : LeviBlocksOfFiveComponents) (hZ : OddCenterRest) :
    KFactCompParabTwoFivesOn (IsLieOf IdxB) := by
  intro Y _ _ L P hCP hB h3 C₁ C₂ hne hC₁ hC₂
  obtain ⟨r, K, _, _, _, -, ⟨φ⟩⟩ := exists_mulEquiv_statedSp_of_idxB hZ hCP.comp hCP.odd hB
  obtain ⟨ρ, I, t, hI, htI, hmax, hρ⟩ := exists_flagStabilizer_of_compParab hCP φ
  have hI' : ∀ i ∈ I, i ≤ r := fun i hi => (hI i hi).2
  obtain ⟨β, hβk, hβp, hβc⟩ :=
    sympL28_exists_leviData hI' (fun i hi => (hI i hi).1) htI hmax ρ hρ
  obtain ⟨j₁, j₂, hj, hq₁, hq₂, h₁, h₂⟩ := (hLB Y L P hCP.parab.1 (StatedSp r K)
    ρ.toMonoidHom ρ.surjective
    (by rw [(MonoidHom.ker_eq_bot_iff _).mpr ρ.injective]; exact bot_le) (Fin (r + 1))
    (fun _ => StatedSp r K) (spFlagLeviBlock hI' t) β hβk hβp hβc
    (spFlagLeviBlock_cases hI' t)).2 C₁ C₂ hne hC₁ hC₂
  obtain ⟨hK, hr3, hrI⟩ := sympFive_two_blocks hI hI' htI hmax hj hq₁ h₁ hq₂ h₂
  obtain rfl : r = 3 := by
    by_contra hr
    have h4 := le_pRank_three_of_torus hK hI' ρ hρ
    have h5 := CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) hCP.parab.1
    omega
  obtain rfl := hrI le_rfl
  exact Or.inr ⟨K, inferInstance, inferInstance, inferInstance, hK, ρ, hρ⟩

theorem kFactCompParabOneFiveOn_idxB (hLB : LeviBlocksOfFiveComponents) (hZ : OddCenterRest) :
    KFactCompParabOneFiveOn (IsLieOf IdxB) := by
  intro Y _ _ L P hCP hB C hC
  obtain ⟨r, K, _, _, _, hr2, ⟨φ⟩⟩ := exists_mulEquiv_statedSp_of_idxB hZ hCP.comp hCP.odd hB
  obtain ⟨ρ, I, t, hI, htI, hmax, hρ⟩ := exists_flagStabilizer_of_compParab hCP φ
  have hI' : ∀ i ∈ I, i ≤ r := fun i hi => (hI i hi).2
  obtain ⟨β, hβk, hβp, hβc⟩ :=
    sympL28_exists_leviData hI' (fun i hi => (hI i hi).1) htI hmax ρ hρ
  obtain ⟨j, hq, h60⟩ := (hLB Y L P hCP.parab.1 (StatedSp r K) ρ.toMonoidHom ρ.surjective
    (by rw [(MonoidHom.ker_eq_bot_iff _).mpr ρ.injective]; exact bot_le) (Fin (r + 1))
    (fun _ => StatedSp r K) (spFlagLeviBlock hI' t) β hβk hβp hβc
    (spFlagLeviBlock_cases hI' t)).1 C hC
  obtain ⟨hK, -, -⟩ := spFlagLeviBlock_sixty hI' t hq h60
  have hu : Nat.card Kˣ = 3 := by rw [Nat.card_units, hK]
  obtain ⟨τ, hτ, hτP⟩ := sympL28_exists_torus hr2 hI' ρ hρ
  exact Or.inl (sympFive_e9_of_torus hu ρ τ hτ (hτP.trans hCP.parab.1))

end CFSG.AGLEmbedding
