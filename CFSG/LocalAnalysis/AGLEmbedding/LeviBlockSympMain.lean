module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockSympCover
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockSection
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGenFive
import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherSubflag
import CFSG.Assembly.RankThreeEvenDefs
import CFSG.Fischer.Classification.Recognition.PSU6
import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher (flagStabilizer)
open LeviBlock

theorem kFactCompParabSU38On_idxB (hZ : OddCenterRest) : KFactCompParabSU38On (IsLieOf IdxB) := by
  intro Y _ _ L P hCP hB
  obtain ⟨K, hKg, hKf, ρ, 𝒯, hρ, hL, h1, -⟩ := exists_hasLeviBlocks_of_idxB hZ hCP hB
  exact su38At_of_levi hCP.parab.1 ⟨K, hKg, hKf, ρ, 𝒯, hρ, hL, h1⟩

theorem kFactCompParabLeviU42On_idxB (hZ : OddCenterRest) :
    KFactCompParabLeviU42On (IsLieOf IdxB) := by
  intro Y _ _ L P hCP hB
  obtain ⟨K, hKg, hKf, ρ, 𝒯, hρ, hL, -, h2⟩ := exists_hasLeviBlocks_of_idxB hZ hCP hB
  exact leviU42At_of_levi hCP.parab.1 ⟨K, hKg, hKf, ρ, 𝒯, hρ, hL, h2⟩

namespace LeviBlock

variable {r : ℕ} {K : Type} [Field K] {I : Set ℕ}

theorem card_four_and_four_le_of_three [Finite K] [CharP K 2] (hI : ∀ i ∈ I, i ≤ r) (t : ℕ)
    (h3 : 3 ≤ Nat.card {j // CFSG.Open.IsQuasisimple (spFlagLeviBlock (K := K) hI t j) ∧
      Nat.card (↥(spFlagLeviBlock (K := K) hI t j) ⧸
        Subgroup.center ↥(spFlagLeviBlock (K := K) hI t j)) = 60}) :
    Nat.card K = 4 ∧ 4 ≤ r := by
  classical
  set s := Finset.univ.filter fun j : Fin (r + 1) =>
    CFSG.Open.IsQuasisimple (spFlagLeviBlock (K := K) hI t j) ∧
      Nat.card (↥(spFlagLeviBlock (K := K) hI t j) ⧸
        Subgroup.center ↥(spFlagLeviBlock (K := K) hI t j)) = 60 with hs
  have hcard : 3 ≤ s.card := by
    rwa [Nat.card_eq_fintype_card, Fintype.card_subtype] at h3
  have hsix : ∀ j ∈ s, Nat.card K = 4 ∧
      (((j : ℕ) = 0 ∧ r - t = 1) ∨ ((j : ℕ) ≠ 0 ∧ (j : ℕ) ∈ I ∧ j - spFlagPrev I j = 2)) := by
    intro j hj
    obtain ⟨hq, h60⟩ := (Finset.mem_filter.mp hj).2
    obtain ⟨hK, -, h⟩ := spFlagLeviBlock_sixty hI t hq h60
    exact ⟨hK, h⟩
  have h2 : 1 < (s.erase 0).card := by
    have := Finset.pred_card_le_card_erase (s := s) (a := 0)
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp h2
  have hK := (hsix a (Finset.mem_of_mem_erase ha)).1
  have hblock : ∀ j ∈ s.erase 0, (j : ℕ) ∈ I ∧ j - spFlagPrev I j = 2 := by
    intro j hj
    have hj0 : (j : ℕ) ≠ 0 := fun h => Finset.ne_of_mem_erase hj (Fin.ext h)
    rcases (hsix j (Finset.mem_of_mem_erase hj)).2 with ⟨h0, -⟩ | ⟨-, hjI, hj2⟩
    · exact absurd h0 hj0
    · exact ⟨hjI, hj2⟩
  obtain ⟨haI, ha2⟩ := hblock a ha
  obtain ⟨hbI, hb2⟩ := hblock b hb
  refine ⟨hK, ?_⟩
  have hab' : (a : ℕ) ≠ (b : ℕ) := fun h => hab (Fin.ext h)
  rcases lt_or_gt_of_ne hab' with h | h
  · have := le_spFlagPrev haI h
    have := hI b hbI
    omega
  · have := le_spFlagPrev hbI h
    have := hI a haI
    omega

theorem le_pRank_three_of_torus [Finite K] (hK : Nat.card K = 4) (hI : ∀ i ∈ I, i ≤ r)
    {Y : Type} [Group Y] [Finite Y] {L P : Subgroup Y} (ρ : StatedSp r K ≃* ↥L)
    (hρ : (P.subgroupOf L).comap ρ.toMonoidHom = flagStabilizer r K I) :
    r ≤ CFSG.Open.pRank 3 P := by
  have hu : Nat.card Kˣ = 3 := by rw [Nat.card_units, hK]
  let τ : (Fin r → Kˣ) →* Y := L.subtype.comp (ρ.toMonoidHom.comp SymplecticTorusWeyl.torusHom)
  have hτ : Function.Injective τ :=
    (Subgroup.subtype_injective _).comp (ρ.injective.comp SymplecticTorusWeyl.torusHom_injective)
  have hrange : τ.range ≤ P := by
    rintro _ ⟨x, rfl⟩
    have hx : SymplecticTorusWeyl.torusHom x ∈ (P.subgroupOf L).comap ρ.toMonoidHom := by
      rw [hρ]
      exact SymplecticHigher.borelSubgroup_le_flagStabilizer hI
        (SymplecticFlag.torus_le_borelSubgroup ⟨x, rfl⟩)
    exact Subgroup.mem_subgroupOf.mp hx
  refine CFSG.SectionRank.le_pRank_of_injective (p := 3) (by norm_num) (fun a b => mul_comm a b)
    (fun a => funext fun i => ?_) ?_ τ hτ hrange
  · rw [Pi.pow_apply, ← hu, pow_card_eq_one', Pi.one_apply]
  · rw [Nat.card_fun, hu, Nat.card_fin]

end LeviBlock

theorem kFactCompParabThreeFivesOn_idxB (hZ : OddCenterRest) :
    KFactCompParabThreeFivesOn (IsLieOf IdxB) := by
  intro Y _ _ L P hCP hB O J _ hPO _ hsec hJ hJc
  obtain ⟨r, K, _, _, _, -, ⟨φ⟩⟩ := exists_mulEquiv_statedSp_of_idxB hZ hCP.comp hCP.odd hB
  obtain ⟨ρ, I, t, hI, htI, hmax, hρ⟩ := exists_flagStabilizer_of_compParab hCP φ
  have hI' : ∀ i ∈ I, i ≤ r := fun i hi => (hI i hi).2
  let f : flagStabilizer r K I →* Y :=
    L.subtype.comp (ρ.toMonoidHom.comp (flagStabilizer r K I).subtype)
  have hf : f.range = P := by
    apply le_antisymm
    · rintro _ ⟨q, rfl⟩
      have hq : (q : StatedSp r K) ∈ (P.subgroupOf L).comap ρ.toMonoidHom := by
        rw [hρ]
        exact q.2
      exact Subgroup.mem_subgroupOf.mp hq
    · intro p hp
      have hk : ρ.symm ⟨p, hCP.parab.1 hp⟩ ∈ flagStabilizer r K I := by
        rw [← hρ, Subgroup.mem_comap]
        change ρ (ρ.symm ⟨p, hCP.parab.1 hp⟩) ∈ P.subgroupOf L
        rw [MulEquiv.apply_symm_apply]
        exact Subgroup.mem_subgroupOf.mpr hp
      refine ⟨⟨_, hk⟩, ?_⟩
      change ((ρ (ρ.symm ⟨p, hCP.parab.1 hp⟩) : ↥L) : Y) = p
      rw [MulEquiv.apply_symm_apply]
  have h3 := three_le_card_fiveBlocks f hf (spFlagLeviHom hI' htI)
    (isPGroup_ker_spFlagLeviHom hI' htI fun i hi => (hI i hi).1)
    (pi_le_range_spFlagLeviHom hI' htI hmax) (commutator_range_spFlagLeviHom_le hI' htI)
    (spFlagLeviBlock_cases hI' t) (fun j hq h60 => (spFlagLeviBlock_sixty hI' t hq h60).2.1)
    hPO hsec hJ hJc
  obtain ⟨hK, hr⟩ := card_four_and_four_le_of_three hI' t h3
  exact hr.trans (le_pRank_three_of_torus hK hI' ρ hρ)

end CFSG.AGLEmbedding
