module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockL28Generic
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockSympHas
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockL28Arith
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockSympCover

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.LeviBlock CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher (flagStabilizer)

theorem sympL28_card_eq_eight {q f : ℕ} (hq : q = 2 ^ f) (h : 504 ∈ spBlockOrders q) : q = 8 := by
  rcases h with ⟨k, hk⟩ | ⟨m, hm⟩ | h
  · exact ((ordA_eq_504_iff hq).1 hk.symm).2
  · exact ((ordBC_eq_504_iff hq).1 hm.symm).2
  · norm_num at h

theorem sympL28_extendByOne_injective {M : Type*} [MulOneClass M] {n r : ℕ} (h : n ≤ r) :
    Function.Injective (Function.ExtendByOne.hom M (Fin.castLE h)) := by
  intro a b hab
  funext i
  have := congrFun hab (Fin.castLE h i)
  simpa [Function.ExtendByOne.hom_apply, (Fin.castLE_injective h).extend_apply] using this

theorem sympL28_exists_torus {n r : ℕ} {K : Type} [Field K] {I : Set ℕ} (hn : n ≤ r)
    (hI : ∀ i ∈ I, i ≤ r) {Y : Type} [Group Y] {L P : Subgroup Y} (ρ : StatedSp r K ≃* ↥L)
    (hρ : (P.subgroupOf L).comap ρ.toMonoidHom = flagStabilizer r K I) :
    ∃ τ : (Fin n → Kˣ) →* Y, Function.Injective τ ∧ τ.range ≤ P := by
  let ι : (Fin n → Kˣ) →* (Fin r → Kˣ) := Function.ExtendByOne.hom Kˣ (Fin.castLE hn)
  refine ⟨L.subtype.comp (ρ.toMonoidHom.comp (SymplecticTorusWeyl.torusHom.comp ι)), ?_, ?_⟩
  · exact (Subgroup.subtype_injective _).comp (ρ.injective.comp
      (SymplecticTorusWeyl.torusHom_injective.comp (sympL28_extendByOne_injective hn)))
  · rintro _ ⟨x, rfl⟩
    have hx : SymplecticTorusWeyl.torusHom (ι x) ∈ (P.subgroupOf L).comap ρ.toMonoidHom := by
      rw [hρ]
      exact SymplecticHigher.borelSubgroup_le_flagStabilizer hI
        (SymplecticFlag.torus_le_borelSubgroup ⟨ι x, rfl⟩)
    exact Subgroup.mem_subgroupOf.mp hx

theorem sympL28_leviBlock_fiveOhFour {r : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {I : Set ℕ} (hI : ∀ i ∈ I, i ≤ r) (t : ℕ) {j : Fin (r + 1)}
    (hq : CFSG.Open.IsQuasisimple (spFlagLeviBlock (K := K) hI t j))
    (h504 : Nat.card (↥(spFlagLeviBlock (K := K) hI t j) ⧸
      Subgroup.center ↥(spFlagLeviBlock (K := K) hI t j)) = 504) :
    Nat.card K = 8 ∧
      (((j : ℕ) = 0 ∧ r - t = 1) ∨ ((j : ℕ) ≠ 0 ∧ (j : ℕ) ∈ I ∧ j - spFlagPrev I j = 2)) := by
  obtain ⟨f, -, hqf⟩ := spFlag_card_eq_two_pow (K := K)
  by_cases hj0 : (j : ℕ) = 0
  · rcases card_spFlagLeviBlock_zero hI t hj0 hq with h | ⟨-, -, h⟩
    · rw [h504] at h
      obtain ⟨hm, hK8⟩ := (ordBC_eq_504_iff hqf).mp h.symm
      exact ⟨hK8, Or.inl ⟨hj0, hm⟩⟩
    · omega
  by_cases hj : (j : ℕ) ∈ I
  · rw [card_spFlagLeviBlock_mem hI t hj0 hj] at h504
    obtain ⟨hn, hK8⟩ := (ordA_eq_504_iff hqf).mp h504
    have hprev := spFlagPrev_le I j
    exact ⟨hK8, Or.inr ⟨hj0, hj, by omega⟩⟩
  · exfalso
    rw [spFlagLeviBlock_of_not_mem hI hj0 hj] at hq
    exact spFlag_not_isSolvable hq (Group.isSolvable_of_comm fun a b => Subsingleton.elim _ _)

theorem sympL28_three_le_of_two_blocks {r : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {I : Set ℕ} (hI : ∀ i ∈ I, i ≤ r) {t : ℕ} (htI : t ∈ I) (hmax : ∀ c ∈ I, c ≤ t)
    {j₁ j₂ : Fin (r + 1)} (hne : j₁ ≠ j₂)
    (hq₁ : CFSG.Open.IsQuasisimple (spFlagLeviBlock (K := K) hI t j₁))
    (h₁ : Nat.card (↥(spFlagLeviBlock (K := K) hI t j₁) ⧸
      Subgroup.center ↥(spFlagLeviBlock (K := K) hI t j₁)) = 504)
    (hq₂ : CFSG.Open.IsQuasisimple (spFlagLeviBlock (K := K) hI t j₂))
    (h₂ : Nat.card (↥(spFlagLeviBlock (K := K) hI t j₂) ⧸
      Subgroup.center ↥(spFlagLeviBlock (K := K) hI t j₂)) = 504) :
    Nat.card K = 8 ∧ 3 ≤ r := by
  obtain ⟨hK, h1⟩ := sympL28_leviBlock_fiveOhFour hI t hq₁ h₁
  obtain ⟨-, h2⟩ := sympL28_leviBlock_fiveOhFour hI t hq₂ h₂
  refine ⟨hK, ?_⟩
  have htr : t ≤ r := hI t htI
  have hne' : (j₁ : ℕ) ≠ (j₂ : ℕ) := fun h => hne (Fin.ext h)
  rcases h1 with ⟨h10, h1r⟩ | ⟨-, h1I, h1p⟩ <;> rcases h2 with ⟨h20, h2r⟩ | ⟨-, h2I, h2p⟩
  · exact absurd (h10.trans h20.symm) hne'
  · have := hmax _ h2I
    omega
  · have := hmax _ h1I
    omega
  · rcases lt_or_gt_of_ne hne' with h | h
    · have := le_spFlagPrev h1I h
      have := hI _ h2I
      omega
    · have := le_spFlagPrev h2I h
      have := hI _ h1I
      omega

theorem sympL28_three_le_pRank_of_blocks {r : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {I : Set ℕ} (hI : ∀ i ∈ I, i ≤ r) {t : ℕ} (htI : t ∈ I) (hmax : ∀ c ∈ I, c ≤ t)
    {Y : Type} [Group Y] [Finite Y] {L P : Subgroup Y} (hPL : P ≤ L) (ρ : StatedSp r K ≃* ↥L)
    (hρ : (P.subgroupOf L).comap ρ.toMonoidHom = flagStabilizer r K I)
    {j₁ j₂ : Fin (r + 1)} (hne : j₁ ≠ j₂)
    (hq₁ : CFSG.Open.IsQuasisimple (spFlagLeviBlock (K := K) hI t j₁))
    (h₁ : Nat.card (↥(spFlagLeviBlock (K := K) hI t j₁) ⧸
      Subgroup.center ↥(spFlagLeviBlock (K := K) hI t j₁)) = 504)
    (hq₂ : CFSG.Open.IsQuasisimple (spFlagLeviBlock (K := K) hI t j₂))
    (h₂ : Nat.card (↥(spFlagLeviBlock (K := K) hI t j₂) ⧸
      Subgroup.center ↥(spFlagLeviBlock (K := K) hI t j₂)) = 504) :
    3 ≤ Open.pRank 7 L := by
  obtain ⟨hK, hr⟩ := sympL28_three_le_of_two_blocks hI htI hmax hne hq₁ h₁ hq₂ h₂
  have hu : Nat.card Kˣ = 7 := by rw [Nat.card_units, hK]
  obtain ⟨τ, hτ, hτP⟩ := sympL28_exists_torus hr hI ρ hρ
  exact three_le_pRank_of_torus hu τ hτ (hτP.trans hPL)

theorem sympL28_exists_leviData {r : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] {I : Set ℕ}
    (hI : ∀ i ∈ I, i ≤ r) (hI1 : ∀ i ∈ I, 1 ≤ i) {t : ℕ} (htI : t ∈ I)
    (hmax : ∀ c ∈ I, c ≤ t) {Y : Type} [Group Y] {L P : Subgroup Y} (ρ : StatedSp r K ≃* ↥L)
    (hρ : (P.subgroupOf L).comap ρ.toMonoidHom = flagStabilizer r K I) :
    ∃ β : ↥((P.subgroupOf L).comap ρ.toMonoidHom) →* (Fin (r + 1) → StatedSp r K),
      IsPGroup 2 β.ker ∧ Subgroup.pi Set.univ (spFlagLeviBlock (K := K) hI t) ≤ β.range ∧
        ⁅β.range, β.range⁆ ≤ Subgroup.pi Set.univ (spFlagLeviBlock (K := K) hI t) := by
  rw [hρ]
  exact ⟨spFlagLeviHom hI htI, isPGroup_ker_spFlagLeviHom hI htI hI1,
    pi_le_range_spFlagLeviHom hI htI hmax, commutator_range_spFlagLeviHom_le hI htI⟩

theorem kFactCompParabL28RankOn_idxB (hZ : OddCenterRest) :
    KFactCompParabL28RankOn (IsLieOf IdxB) := by
  intro Y _ _ L P hCP hB N hNP hPN d ψ hd hψ
  obtain ⟨r, K, _, _, _, hr2, ⟨φ⟩⟩ := exists_mulEquiv_statedSp_of_idxB hZ hCP.comp hCP.odd hB
  obtain ⟨ρ, I, t, hI, htI, hmax, hρ⟩ := exists_flagStabilizer_of_compParab hCP φ
  have hI' : ∀ i ∈ I, i ≤ r := fun i hi => (hI i hi).2
  obtain ⟨f, -, hq⟩ := spFlag_card_eq_two_pow (K := K)
  have hQ : HasLeviBlocks ↥((P.subgroupOf L).comap ρ.toMonoidHom) (spBlockOrders (Nat.card K)) := by
    rw [hρ]
    exact hasLeviBlocks_spFlag hI htI hmax
  have h504 := card_mem_of_l28Section hCP.parab.1 ρ.toMonoidHom ρ.surjective hQ hNP hPN ψ hd hψ
  have hK : Nat.card K = 8 := sympL28_card_eq_eight hq h504
  have hu : Nat.card Kˣ = 7 := by rw [Nat.card_units, hK]
  have hZ7 : ¬ 7 ∣ Nat.card (Subgroup.center ↥L) :=
    not_dvd_card_center_rest hZ hCP.comp hCP.odd (Or.inl hB) (by norm_num) (by norm_num)
  obtain ⟨τ, hτ, hτP⟩ := sympL28_exists_torus hr2 hI' ρ hρ
  exact l28_E_of_torus_of_not_dvd hu hZ7 τ hτ (hτP.trans hCP.parab.1)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
