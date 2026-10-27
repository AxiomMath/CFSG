module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTUAlignFourCT
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTUAlignLevi

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_involutive)
open CFSG.LieType.CurtisTits (rankOne levi)
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear mem_blockSpecialLinear)
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)

section Factors

variable {F : Type} [Field F] {σ : F ≃+* F} {hσ : ∀ c, σ (σ c) = c} {ε : ℕ}

theorem mem_ctuPlanes_of_blkShort_zero_ne_zero (hε : ε ≤ 1) (h0 : 0 + 1 < (2 * 3 + ε) / 2)
    {a : Fin (2 * 3 + ε)} (ha : blkShort (n := 2 * 3 + ε) ⟨0, by omega⟩ h0 a ≠ 0) :
    a ∈ ctuPlanes ε ({0, 1} : Finset (Fin 3)) := by
  rw [blkShort_ne_zero_iff] at ha
  obtain ⟨w, rfl⟩ := (ctuCoord 3 ε).surjective a
  rw [ctuCoord_mem_ctuPlanes]
  rcases w with (p | p) | i
  · rw [ctuCoord_inl_inl] at ha
    rw [inPlanes_inl, planeOf_inl]
    have hp := p.2
    simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
    simp only at ha
    omega
  · rw [ctuCoord_inl_inr] at ha
    rw [inPlanes_inl, planeOf_inr]
    have hp := p.2
    simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
    simp only at ha
    omega
  · rw [ctuCoord_inr] at ha
    have hi := i.2
    simp only at ha
    omega

theorem rankOne_two_le_ctuBlock_zero_one (hε : ε ≤ 1) :
    rankOne (rootGroup σ hσ (2 * 3 + ε)) ⟨2, by omega⟩ ≤
      ctuBlock σ ε ({0, 1} : Finset (Fin 3)) := fun _ hy =>
  mem_ctuBlock_pair (rankOne_le_ctuBlock hε ⟨2, by omega⟩ (k := 0) (by simp) (by simp) hy)
    (rankOne_le_ctuBlock hε ⟨2, by omega⟩ (k := 1) (by simp) (by simp) hy)

theorem disjoint_blkShort_zero_ctuPlanes (hε : ε ≤ 1) (h0 : 0 + 1 < (2 * 3 + ε) / 2) :
    Disjoint (Finset.univ.filter fun a => blkShort (n := 2 * 3 + ε) ⟨0, by omega⟩ h0 a ≠ 0)
      (ctuPlanes ε ({0, 1} : Finset (Fin 3)))ᶜ := by
  rw [Finset.disjoint_left]
  intro a ha hac
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
  exact (Finset.mem_compl.1 hac) (mem_ctuPlanes_of_blkShort_zero_ne_zero hε h0 ha)

theorem commute_rankOne_zero_two_three (hε : ε ≤ 1) {x y : SU σ (2 * 3 + ε)}
    (hx : x ∈ rankOne (rootGroup σ hσ (2 * 3 + ε)) ⟨0, by omega⟩)
    (hy : y ∈ rankOne (rootGroup σ hσ (2 * 3 + ε)) ⟨2, by omega⟩) : Commute x y := by
  have h0 : 0 + 1 < (2 * 3 + ε) / 2 := by omega
  have h := LinearPilot.commute_blockSpecialLinear_of_disjoint
    (disjoint_blkShort_zero_ctuPlanes hε h0) (ctuToSL_mem_blockSpecialLinear_of_mem_rankOne h0 hx)
    (rankOne_two_le_ctuBlock_zero_one hε hy)
  apply ctuToSL_injective
  rw [map_mul, map_mul]
  exact h.eq

theorem rankOne_zero_inf_two_three (hε : ε ≤ 1) :
    rankOne (rootGroup σ hσ (2 * 3 + ε)) ⟨0, by omega⟩ ⊓
      rankOne (rootGroup σ hσ (2 * 3 + ε)) ⟨2, by omega⟩ = ⊥ := by
  have h0 : 0 + 1 < (2 * 3 + ε) / 2 := by omega
  rw [eq_bot_iff]
  rintro x ⟨hx0, hx2⟩
  have h1 := blockSpecialLinear_inf_le _ _ ⟨ctuToSL_mem_blockSpecialLinear_of_mem_rankOne h0 hx0,
    rankOne_two_le_ctuBlock_zero_one hε hx2⟩
  rw [Finset.disjoint_iff_inter_eq_empty.1 (disjoint_blkShort_zero_ctuPlanes hε h0),
    LinearPilot.blockSpecialLinear_empty] at h1
  rw [Subgroup.mem_bot]
  exact ctuToSL_injective (by rw [map_one]; exact Subgroup.mem_bot.1 h1)

end Factors

theorem ctuThree_placement {m : ℕ} (hm : m = 3) (J : Finset (Fin m)) (hJ : J.card ≤ 2)
    {j₀ j₁ j₂ : Fin m} (h₀ : j₀.val = 0) (h₁ : j₁.val = 1) (h₂ : j₂.val = 2)
    (hJ₀ : J ≠ {j₀, j₂}) (hJ₁ : J ≠ {j₀, j₁}) :
    ∀ j ∈ J, (if j₀ ∈ J then 2 else 0 : ℕ) ≠ j.val ∧ (if j₀ ∈ J then 2 else 0 : ℕ) ≠ j.val + 1 := by
  intro j hj
  have hjm := j.2
  by_cases h0 : j₀ ∈ J
  · rw [ite_eq_left h0]
    have hj0 : j = j₀ := by
      by_contra hne
      have hval : j.val = 1 ∨ j.val = 2 := by
        have : j.val ≠ 0 := fun h => hne (Fin.ext (h.trans h₀.symm))
        omega
      have hsub : ({j₀, j} : Finset (Fin m)) ⊆ J := by
        intro x hx
        rcases Finset.mem_insert.1 hx with rfl | hx
        · exact h0
        · rw [Finset.mem_singleton.1 hx]
          exact hj
      have heq : ({j₀, j} : Finset (Fin m)) = J :=
        Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_pair (Ne.symm hne)]; exact hJ)
      rcases hval with h | h
      · exact hJ₁ (heq.symm.trans (by rw [show j = j₁ from Fin.ext (h.trans h₁.symm)]))
      · exact hJ₀ (heq.symm.trans (by rw [show j = j₂ from Fin.ext (h.trans h₂.symm)]))
    rw [hj0, h₀]
    omega
  · rw [ite_eq_right h0]
    have : j.val ≠ 0 := fun h => h0 (by rw [show j₀ = j from Fin.ext (h₀.trans h.symm)]; exact hj)
    omega

theorem ctuThree_levi_empty_eq_bot {I : Type*} [DecidableEq I] {K : Type*} [Group K]
    (X : (I → ℤ) → Subgroup K) : levi X (∅ : Finset I) = ⊥ := by
  simp [CFSG.LieType.CurtisTits.levi]

theorem ctuThree_forall_mem_of_levi_pair {I : Type*} [DecidableEq I] {S : Type*} [Group S]
    {H : Type*} [Group H] (R : (I → ℤ) → Subgroup S) (i j : I) (ρ : levi R {i, j} →* H)
    (T : Subgroup H)
    (hi : ∀ (x : S) (hx : x ∈ rankOne R i),
      ρ ⟨x, CFSG.LieType.CurtisTits.rankOne_le_levi R (Finset.mem_insert_self _ _) hx⟩ ∈ T)
    (hj : ∀ (x : S) (hx : x ∈ rankOne R j),
      ρ ⟨x, CFSG.LieType.CurtisTits.rankOne_le_levi R
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) hx⟩ ∈ T) :
    ∀ z, ρ z ∈ T := by
  have hle : levi R {i, j} ≤ (T.comap ρ).map (levi R {i, j}).subtype := by
    refine (F4Pilot.levi_pair R i j).le.trans (sup_le ?_ ?_)
    · intro y hy
      have hyL : y ∈ rankOne R i := by
        simpa only [CFSG.LieType.CurtisTits.levi, Finset.iSup_singleton] using hy
      exact ⟨_, hi y hyL, rfl⟩
    · intro y hy
      have hyL : y ∈ rankOne R j := by
        simpa only [CFSG.LieType.CurtisTits.levi, Finset.iSup_singleton] using hy
      exact ⟨_, hj y hyL, rfl⟩
  intro z
  obtain ⟨⟨y, hyX⟩, hy, hyx⟩ := hle z.2
  change y = (z : S) at hyx
  subst hyx
  exact hy

section Recognition

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]
  [CharP K 2] {ε : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} {hε : ε ≤ 1}
  {ι : K →+* F} {hι : ∀ c, unitaryInvolution F 2 f (ι c) = ι c} {e : L ≃* StatedSp 3 K}

set_option maxHeartbeats 400000 in
theorem exists_ct_uniRow_three [Finite K] (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (hF : Nat.card F = (2 ^ f) ^ 2)
    (P : ∀ k : Fin 3, CtuParam ε hε (unitaryInvolution F 2 f) ι hι e k)
    (horth : ∀ a ∈ pieceCore e ({0} : Finset (Fin 3)),
      ∀ b ∈ pieceCore e ({2} : Finset (Fin 3)), Commute a b)
    (ρ₁ : levi (rootGroup (unitaryInvolution F 2 f) (unitaryInvolution_involutive hF)
      (2 * 3 + ε)) {⟨0, by omega⟩, ⟨1, by omega⟩} →* G)
    (hρ₀ : ∀ (x : SU (unitaryInvolution F 2 f) (2 * 3 + ε))
      (hx : x ∈ rankOne (rootGroup (unitaryInvolution F 2 f) (unitaryInvolution_involutive hF)
        (2 * 3 + ε)) ⟨0, by omega⟩),
      ρ₁ ⟨x, CFSG.LieType.CurtisTits.rankOne_le_levi _ (by simp) hx⟩ =
        (P 2).Φ ⟨x, rankOne_le_ctuBlock hε ⟨0, by omega⟩ (by simp) (by simp) hx⟩)
    (hρ₁ : ∀ (x : SU (unitaryInvolution F 2 f) (2 * 3 + ε))
      (hx : x ∈ rankOne (rootGroup (unitaryInvolution F 2 f) (unitaryInvolution_involutive hF)
        (2 * 3 + ε)) ⟨1, by omega⟩),
      ρ₁ ⟨x, CFSG.LieType.CurtisTits.rankOne_le_levi _ (by simp) hx⟩ =
        (P 0).Φ ⟨x, rankOne_le_ctuBlock hε ⟨1, by omega⟩ (by simp) (by simp) hx⟩) :
    ∃ ψ : SU (unitaryInvolution F 2 f) (2 * 3 + ε) →* G, ψ.range = spGlobal e ∧
      ψ.ker ≤ center (SU (unitaryInvolution F 2 f) (2 * 3 + ε)) ∧
      CFSG.IsQuasisimple (spGlobal e) ∧ Odd (Nat.card (center (spGlobal e))) ∧
      LieModel (spGlobal e ⧸ center (spGlobal e)) .PSU (2 * 3 + ε) 2 f := by
  classical
  have hK4 : 4 ≤ Nat.card K := hKc ▸ four_le_two_pow hf
  have hn3 : 3 ≤ 2 * 3 + ε := by omega
  have hnq : (2 * 3 + ε, 2 ^ f) ≠ (3, 2) := fun h => by
    have := (Prod.mk.inj h).1
    omega
  set σ := unitaryInvolution F 2 f with hσdef
  set D := rootDatum hF (2 * 3 + ε) with hD
  have hrank : D.rank = 3 := by
    change (2 * 3 + ε) / 2 = 3
    omega
  have h0 : 0 + 1 < (2 * 3 + ε) / 2 := by omega
  set j₀ : Fin D.rank := ⟨0, by omega⟩ with hj₀
  set j₁ : Fin D.rank := ⟨1, by omega⟩ with hj₁
  set j₂ : Fin D.rank := ⟨2, by omega⟩ with hj₂
  have hj02 : j₀ ≠ j₂ := fun h => by simp [hj₀, hj₂, Fin.ext_iff] at h
  have hj01 : j₀ ≠ j₁ := fun h => by simp [hj₀, hj₁, Fin.ext_iff] at h
  have hj12 : j₁ ≠ j₂ := fun h => by simp [hj₁, hj₂, Fin.ext_iff] at h
  set J₀ : Finset (Fin D.rank) := {j₀, j₂} with hJ₀def
  set J₁ : Finset (Fin D.rank) := {j₀, j₁} with hJ₁def
  have hJ₀c : J₀.card = 2 := Finset.card_pair hj02
  have hJ₁c : J₁.card = 2 := Finset.card_pair hj01
  have hJ₁₀ : J₁ ≠ J₀ := fun h => by
    have : j₁ ∈ J₀ := h ▸ (by simp [hJ₁def])
    simp only [hJ₀def, Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h1 | h1
    · exact hj01 h1.symm
    · exact hj12 h1
  set kJ : Finset (Fin D.rank) → Fin 3 := fun J =>
    ⟨if j₀ ∈ J then 2 else 0, by split_ifs <;> norm_num⟩ with hkJdef
  have hkJ : ∀ (J : {J : Finset (Fin D.rank) // J.card ≤ 2}), J.1 ≠ J₀ → J.1 ≠ J₁ →
      ∀ j ∈ J.1, (kJ J.1).val ≠ j.val ∧ (kJ J.1).val ≠ j.val + 1 := fun J h₀' h₁' =>
    ctuThree_placement hrank J.1 J.2 (j₀ := j₀) (j₁ := j₁) (j₂ := j₂) rfl rfl rfl h₀' h₁'
  have hKle : ∀ (J : {J : Finset (Fin D.rank) // J.card ≤ 2}) (h₀' : J.1 ≠ J₀)
      (h₁' : J.1 ≠ J₁), D.leviAmalgam J ≤ ctuBlock σ ε ({kJ J.1} : Finset (Fin 3)) :=
    fun J h₀' h₁' => levi_le_ctuBlock hε (hkJ J h₀' h₁')
  have hk2 : ∀ J : Finset (Fin D.rank), j₀ ∈ J → kJ J = 2 := fun J h => Fin.ext (by
    simp only [hkJdef, ite_eq_left h]
    rfl)
  have hk0 : ∀ J : Finset (Fin D.rank), j₀ ∉ J → kJ J = 0 := fun J h => Fin.ext (by
    simp only [hkJdef, ite_eq_right h]
    rfl)
  set JA : {J : Finset (Fin D.rank) // J.card ≤ 2} := ⟨{j₀}, by simp⟩ with hJA
  set JB : {J : Finset (Fin D.rank) // J.card ≤ 2} := ⟨{j₂}, by simp⟩ with hJB
  set A := D.leviAmalgam JA with hA
  set B := D.leviAmalgam JB with hB
  have hArank : A ≤ rankOne D.rootGroup j₀ := iSup₂_le fun j hj => by
    rw [Finset.mem_singleton.1 hj]
  have hBrank : B ≤ rankOne D.rootGroup j₂ := iSup₂_le fun j hj => by
    rw [Finset.mem_singleton.1 hj]
  have hcommAB : ∀ a ∈ A, ∀ b ∈ B, Commute a b := fun a ha b hb =>
    commute_rankOne_zero_two_three hε (hArank ha) (hBrank hb)
  have hdisjAB : A ⊓ B = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [← rankOne_zero_inf_two_three (σ := σ) (hσ := unitaryInvolution_involutive hF) hε]
    exact ⟨hArank hx.1, hBrank hx.2⟩
  have hlevi₀ : ∀ J : {J : Finset (Fin D.rank) // J.card ≤ 2}, J.1 = J₀ →
      D.leviAmalgam J = A ⊔ B := by
    intro J hJ
    change levi _ J.1 = _
    rw [hJ, hJ₀def]
    exact F4Pilot.levi_pair D.rootGroup j₀ j₂
  have hlevi₁ : ∀ J : {J : Finset (Fin D.rank) // J.card ≤ 2}, J.1 = J₁ →
      D.leviAmalgam J ≤ levi D.rootGroup J₁ := by
    intro J hJ
    change levi _ J.1 ≤ _
    rw [hJ]
  have hA2 : A ≤ ctuBlock σ ε ({2} : Finset (Fin 3)) :=
    hArank.trans (rankOne_le_ctuBlock hε j₀ (by simp [hj₀]) (by simp [hj₀]))
  have hB0 : B ≤ ctuBlock σ ε ({0} : Finset (Fin 3)) :=
    hBrank.trans (rankOne_le_ctuBlock hε j₂ (by simp [hj₂]) (by simp [hj₂]))
  set fA : A →* G := (P 2).Φ.comp (Subgroup.inclusion hA2) with hfA
  set gB : B →* G := (P 0).Φ.comp (Subgroup.inclusion hB0) with hgB
  have hfA_mem : ∀ a : A, fA a ∈ pieceCore e ({0} : Finset (Fin 3)) := fun a =>
    (P 2).mem_pieceCore hF hf hn3 j₀ (by simp [hj₀]) (by simp [hj₀]) (hArank a.2)
  have hgB_mem : ∀ b : B, gB b ∈ pieceCore e ({2} : Finset (Fin 3)) := fun b =>
    (P 0).mem_pieceCore hF hf hn3 j₂ (by simp [hj₂]) (by simp [hj₂]) (hBrank b.2)
  have hfg : ∀ a b, Commute (fA a) (gB b) := fun a b => horth _ (hfA_mem a) _ (hgB_mem b)
  set ρ₀ : ↥(A ⊔ B) →* G := F4Pilot.supLift hcommAB hdisjAB fA gB hfg with hρ₀def
  have hρA : ∀ a : A, ρ₀ ⟨a, mem_sup_left a.2⟩ = fA a := F4Pilot.supLift_apply_left _ _ hfg
  have hρB : ∀ b : B, ρ₀ ⟨b, mem_sup_right b.2⟩ = gB b := F4Pilot.supLift_apply_right _ _ hfg
  obtain ⟨φ, hφ0, hφ1, hφne⟩ : ∃ φ : ∀ J : {J : Finset (Fin D.rank) // J.card ≤ 2},
      D.leviAmalgam J →* G,
      (∀ (J : {J : Finset (Fin D.rank) // J.card ≤ 2}) (h : J.1 = J₀) x,
        φ J x = ρ₀ ⟨x, (hlevi₀ J h).le x.2⟩) ∧
      (∀ (J : {J : Finset (Fin D.rank) // J.card ≤ 2}) (h : J.1 = J₁) x,
        φ J x = ρ₁ ⟨x, hlevi₁ J h x.2⟩) ∧
      ∀ (J : {J : Finset (Fin D.rank) // J.card ≤ 2}) (h₀' : J.1 ≠ J₀) (h₁' : J.1 ≠ J₁) x,
        φ J x = (P (kJ J.1)).Φ ⟨x, hKle J h₀' h₁' x.2⟩ := by
    refine ⟨fun J => if h₀' : J.1 = J₀ then ρ₀.comp (Subgroup.inclusion (hlevi₀ J h₀').le)
      else if h₁' : J.1 = J₁ then ρ₁.comp (Subgroup.inclusion (hlevi₁ J h₁'))
      else (P (kJ J.1)).Φ.comp (Subgroup.inclusion (hKle J h₀' h₁')),
      fun J h x => ?_, fun J h x => ?_, fun J h₀' h₁' x => ?_⟩
    · simp only [h, ↓reduceDIte]
      rfl
    · simp only [h, hJ₁₀, ↓reduceDIte]
      rfl
    · simp only [h₀', h₁', ↓reduceDIte]
      rfl
  have hsame : ∀ (I : {J : Finset (Fin D.rank) // J.card ≤ 2}) (hI0 : I.1 ≠ J₀)
      (hI1 : I.1 ≠ J₁) (k : Fin 3) (x : D.leviAmalgam I)
      (y : ctuBlock σ ε ({k} : Finset (Fin 3))) (_ : (x : SU σ (2 * 3 + ε)) = y),
      kJ I.1 = k ∨ I.1 = ∅ → φ I x = (P k).Φ y := by
    intro I hI0 hI1 k x y hxy hk
    rw [hφne I hI0 hI1]
    rcases hk with rfl | hemp
    · exact congrArg _ (Subtype.ext hxy)
    · have hx1 : (x : SU σ (2 * 3 + ε)) = 1 := by
        have hx := x.2
        change (x : SU σ (2 * 3 + ε)) ∈ levi _ I.1 at hx
        rw [hemp, ctuThree_levi_empty_eq_bot] at hx
        exact Subgroup.mem_bot.1 hx
      have hy1 : y = 1 := Subtype.ext (hxy.symm.trans hx1)
      have hx1' : (⟨x, hKle I hI0 hI1 x.2⟩ : ctuBlock σ ε ({kJ I.1} : Finset (Fin 3))) = 1 :=
        Subtype.ext hx1
      rw [hx1', hy1, map_one, map_one]
  have hsub1 : ∀ (I : Finset (Fin D.rank)) (a : Fin D.rank), I ⊆ {a} → a ∈ I ∨ I = ∅ := by
    intro I a h
    rcases Finset.subset_singleton_iff.1 h with h | h
    · exact Or.inr h
    · exact Or.inl (h ▸ Finset.mem_singleton_self a)
  have hcomp : CFSG.LieType.CurtisTits.IsCompatible D.leviAmalgam φ := by
    intro I J hIJ x y hxy
    have hIJ' : I.1 ⊆ J.1 := hIJ
    by_cases hJ0 : J.1 = J₀
    · by_cases hI0 : I.1 = J₀
      · have hIJeq : I = J := Subtype.ext (hI0.trans hJ0.symm)
        subst hIJeq
        exact congrArg (φ I) (Subtype.ext hxy)
      · have hI1 : I.1 ≠ J₁ := fun h => hJ₁₀ (Finset.eq_of_subset_of_card_le
          (by rw [← h, ← hJ0]; exact hIJ') (by rw [hJ₀c, hJ₁c]))
        rw [hφ0 J hJ0]
        have hIJ₀ : I.1 ⊆ J₀ := hJ0 ▸ hIJ'
        rcases subset_singleton_or_of_subset_pair_ctua hIJ₀ hI0 with hIa | hIb
        · have hyA : (y : SU σ (2 * 3 + ε)) ∈ A := by
            rw [← hxy]
            exact CFSG.LieType.CurtisTits.levi_mono _ hIa x.2
          change _ = ρ₀ ⟨((⟨y, hyA⟩ : A) : SU σ (2 * 3 + ε)), mem_sup_left hyA⟩
          rw [hρA]
          exact hsame I hI0 hI1 2 x (Subgroup.inclusion hA2 ⟨y, hyA⟩) hxy
            ((hsub1 I.1 j₀ hIa).imp (hk2 I.1) id)
        · have hyB : (y : SU σ (2 * 3 + ε)) ∈ B := by
            rw [← hxy]
            exact CFSG.LieType.CurtisTits.levi_mono _ hIb x.2
          change _ = ρ₀ ⟨((⟨y, hyB⟩ : B) : SU σ (2 * 3 + ε)), mem_sup_right hyB⟩
          rw [hρB]
          exact hsame I hI0 hI1 0 x (Subgroup.inclusion hB0 ⟨y, hyB⟩) hxy
            (Or.inl (hk0 I.1 fun h => hj02 (Finset.mem_singleton.1 (hIb h))))
    · by_cases hJ1 : J.1 = J₁
      · by_cases hI1 : I.1 = J₁
        · have hIJeq : I = J := Subtype.ext (hI1.trans hJ1.symm)
          subst hIJeq
          exact congrArg (φ I) (Subtype.ext hxy)
        · have hI0 : I.1 ≠ J₀ := fun h => hJ₁₀ (Finset.eq_of_subset_of_card_le
            (by rw [← h, ← hJ1]; exact hIJ') (by rw [hJ₀c, hJ₁c])).symm
          rw [hφ1 J hJ1]
          have hIJ₁ : I.1 ⊆ J₁ := hJ1 ▸ hIJ'
          rcases subset_singleton_or_of_subset_pair_ctua hIJ₁ hI1 with hIa | hIb
          · have hyL : (y : SU σ (2 * 3 + ε)) ∈ rankOne D.rootGroup j₀ := by
              rw [← hxy]
              have h1 := CFSG.LieType.CurtisTits.levi_mono _ hIa x.2
              simpa only [CFSG.LieType.CurtisTits.levi, Finset.iSup_singleton] using h1
            change _ = ρ₁ ⟨y, CFSG.LieType.CurtisTits.rankOne_le_levi _
              (Finset.mem_insert_self _ _) hyL⟩
            rw [hρ₀ _ hyL]
            exact hsame I hI0 hI1 2 x _ hxy ((hsub1 I.1 j₀ hIa).imp (hk2 I.1) id)
          · have hyL : (y : SU σ (2 * 3 + ε)) ∈ rankOne D.rootGroup j₁ := by
              rw [← hxy]
              have h1 := CFSG.LieType.CurtisTits.levi_mono _ hIb x.2
              simpa only [CFSG.LieType.CurtisTits.levi, Finset.iSup_singleton] using h1
            change _ = ρ₁ ⟨y, CFSG.LieType.CurtisTits.rankOne_le_levi _
              (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) hyL⟩
            rw [hρ₁ _ hyL]
            exact hsame I hI0 hI1 0 x _ hxy
              (Or.inl (hk0 I.1 fun h => hj01 (Finset.mem_singleton.1 (hIb h))))
      · have hI0 : I.1 ≠ J₀ := fun h => hJ0 (Finset.eq_of_subset_of_card_le
          (by rw [← h]; exact hIJ') (by rw [hJ₀c]; exact J.2)).symm
        have hI1 : I.1 ≠ J₁ := fun h => hJ1 (Finset.eq_of_subset_of_card_le
          (by rw [← h]; exact hIJ') (by rw [hJ₁c]; exact J.2)).symm
        rw [hφne J hJ0 hJ1]
        refine hsame I hI0 hI1 (kJ J.1) x ⟨y, hKle J hJ0 hJ1 y.2⟩ hxy ?_
        by_cases hj0 : j₀ ∈ I.1
        · exact Or.inl ((hk2 I.1 hj0).trans (hk2 J.1 (hIJ' hj0)).symm)
        · by_cases hj0J : j₀ ∈ J.1
          · right
            have hJs : J.1 ⊆ {j₀} := by
              intro j hj
              have h1 := hkJ J hJ0 hJ1 j hj
              rw [hk2 J.1 hj0J] at h1
              have hjv : j.val < 3 := by
                have h := j.isLt
                change j.val < (2 * 3 + ε) / 2 at h
                omega
              rw [Finset.mem_singleton]
              apply Fin.ext
              simp only [hj₀]
              change 2 ≠ j.val ∧ 2 ≠ j.val + 1 at h1
              omega
            rcases hsub1 I.1 j₀ (hIJ'.trans hJs) with h | h
            · exact absurd h hj0
            · exact h
          · exact Or.inl ((hk0 I.1 hj0).trans (hk0 J.1 hj0J).symm)
  set G₀ : Subgroup G := ⨆ J, (φ J).range with hG₀
  have hle : ∀ J x, φ J x ∈ G₀ := fun J x => le_iSup (fun J => (φ J).range) J ⟨x, rfl⟩
  set φ' : ∀ J, D.leviAmalgam J →* G₀ := fun J => (φ J).codRestrict G₀ (hle J) with hφ'
  have hcomp' : CFSG.LieType.CurtisTits.IsCompatible D.leviAmalgam φ' :=
    fun I J hIJ x y hxy => Subtype.ext (hcomp I J hIJ x y hxy)
  have hgen' : ⨆ J, (φ' J).range = ⊤ := by
    apply Subgroup.map_injective G₀.subtype_injective
    rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    refine (iSup_congr fun J => ?_).trans hG₀.symm
    rw [← MonoidHom.range_comp]
    rfl
  have htau : ∀ (j : Fin D.rank) (y : StatedSp 3 K)
      (hy : ctuEmbed ε hε σ ι hι y ∈ rankOne D.rootGroup j)
      (hys : ∀ k : Fin 3, k.val ≠ j.val → k.val ≠ j.val + 1 →
        y ∈ spBlock K ({k} : Finset (Fin 3))ᶜ),
      ∃ (J : {J : Finset (Fin D.rank) // J.card ≤ 2}) (x : D.leviAmalgam J),
        (x : SU σ (2 * 3 + ε)) = ctuEmbed ε hε σ ι hι y ∧ φ J x = ((e.symm y : L) : G) := by
    intro j y hy hys
    set J : {J : Finset (Fin D.rank) // J.card ≤ 2} := ⟨{j}, by simp⟩ with hJ
    have hJ0 : J.1 ≠ J₀ := fun h => by
      have := congrArg Finset.card h
      rw [Finset.card_singleton, hJ₀c] at this
      omega
    have hJ1 : J.1 ≠ J₁ := fun h => by
      have := congrArg Finset.card h
      rw [Finset.card_singleton, hJ₁c] at this
      omega
    have hxJ : ctuEmbed ε hε σ ι hι y ∈ D.leviAmalgam J :=
      CFSG.LieType.CurtisTits.rankOne_le_levi _ (Finset.mem_singleton_self j) hy
    refine ⟨J, ⟨_, hxJ⟩, rfl, ?_⟩
    rw [hφne J hJ0 hJ1]
    obtain ⟨h1, h2⟩ := hkJ J hJ0 hJ1 j (Finset.mem_singleton_self j)
    exact (P (kJ J.1)).N1' (hys _ h1 h2) _ rfl
  have hnt : ∃ J, ∃ x, φ' J x ≠ 1 := by
    obtain ⟨κ, hκ⟩ := exists_units_mul_self_ne_one_of_four_le hK4
    have hκ1 : κ ≠ 1 := fun h => hκ (by rw [h, one_mul])
    obtain ⟨J, x, -, hφx⟩ := htau ⟨0, by omega⟩ _
      (ctuEmbed_shortTorus_mem_rankOne hF hε (ι := ι) (hι := hι) (j := ⟨0, by omega⟩) h0 κ)
      (fun k hk1 hk2 => diagSp_mem_spBlock_compl_of_eq_one (by
        have hk1' : k ≠ ⟨0, by omega⟩ := fun h => hk1 (by rw [h])
        have hk2' : k ≠ ⟨0 + 1, by omega⟩ := fun h => hk2 (by rw [h])
        rw [Pi.mul_apply, Pi.mulSingle_eq_of_ne hk1', Pi.mulSingle_eq_of_ne hk2', mul_one]))
    refine ⟨J, x, fun h => ?_⟩
    have h1 : φ J x = 1 := congrArg Subtype.val h
    rw [hφx] at h1
    have h2 : e.symm (diagSp K 3 (Pi.mulSingle (⟨0, by omega⟩ : Fin 3) κ *
        Pi.mulSingle ⟨0 + 1, by omega⟩ κ⁻¹)) = 1 := Subtype.ext h1
    rw [MulEquiv.map_eq_one_iff] at h2
    have h3 := congrFun (diagSp_injective (h2.trans (map_one _).symm)) ⟨0, by omega⟩
    have hne : (⟨0, by omega⟩ : Fin 3) ≠ ⟨0 + 1, by omega⟩ := fun h => by
      have := congrArg Fin.val h
      simp at this
    rw [Pi.mul_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hne, mul_one] at h3
    exact hκ1 h3
  have hadm : StatedLieAdmissible .PSU (2 * 3 + ε) 2 f := ⟨Nat.prime_two, by omega, hn3, hnq⟩
  obtain ⟨-, -, hrec, -⟩ :=
    CFSG.LieType.CurtisTits.curtisTitsConclusion_unitary.{0} (F := F) (p := 2) (f := f)
      (n := 2 * 3 + ε) hadm hF
  obtain ⟨ψ₀, hψ₀, hsurj, hker, hqs, hZ, -, hLM⟩ := hrec G₀ φ' hcomp' hgen' hnt
  set ψ : SU σ (2 * 3 + ε) →* G := G₀.subtype.comp ψ₀ with hψdef
  have hψrange : ψ.range = G₀ := by
    rw [hψdef, MonoidHom.range_comp, MonoidHom.range_eq_top.2 hsurj, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hψφ : ∀ J (x : D.leviAmalgam J), ψ x = φ J x := fun J x =>
    congrArg Subtype.val (hψ₀ J x)
  have hψker : ψ.ker ≤ center (SU σ (2 * 3 + ε)) := by
    intro z hz
    apply hker
    rw [MonoidHom.mem_ker] at hz ⊢
    exact G₀.subtype_injective (by rw [map_one]; exact hz)
  have hG₀le : G₀ ≤ spGlobal e := by
    refine iSup_le fun J => ?_
    rintro _ ⟨x, rfl⟩
    by_cases hJ0 : J.1 = J₀
    · rw [hφ0 J hJ0]
      have hρle : ρ₀.range ≤ spGlobal e := by
        rw [hρ₀def, F4Pilot.range_supLift]
        refine sup_le ?_ ?_
        · rintro _ ⟨a, rfl⟩
          exact le_iSup (fun j : Fin 3 => pieceCore e ({j} : Finset (Fin 3))) 0 (hfA_mem a)
        · rintro _ ⟨b, rfl⟩
          exact le_iSup (fun j : Fin 3 => pieceCore e ({j} : Finset (Fin 3))) 2 (hgB_mem b)
      exact hρle ⟨_, rfl⟩
    · by_cases hJ1 : J.1 = J₁
      · rw [hφ1 J hJ1]
        refine ctuThree_forall_mem_of_levi_pair _ _ _ ρ₁ (spGlobal e) (fun y hyL => ?_)
          (fun y hyL => ?_) _
        · rw [hρ₀ y hyL]
          exact le_iSup (fun j : Fin 3 => pieceCore e ({j} : Finset (Fin 3))) 0
            ((P 2).mem_pieceCore hF hf hn3 j₀ (by simp [hj₀]) (by simp [hj₀]) hyL)
        · rw [hρ₁ y hyL]
          exact le_iSup (fun j : Fin 3 => pieceCore e ({j} : Finset (Fin 3))) 1
            ((P 0).mem_pieceCore hF hf hn3 j₁ (by simp [hj₁]) (by simp [hj₁]) hyL)
      · rw [hφne J hJ0 hJ1]
        set A' : Subgroup (SU σ (2 * 3 + ε)) := ((spGlobal e).comap (P (kJ J.1)).Φ).map
          (ctuBlock σ ε ({kJ J.1} : Finset (Fin 3))).subtype with hA'
        have hAle : D.leviAmalgam J ≤ A' := by
          refine iSup₂_le fun j hj => ?_
          intro y hy
          obtain ⟨h1, h2⟩ := hkJ J hJ0 hJ1 j hj
          refine ⟨⟨y, rankOne_le_ctuBlock hε j h1 h2 hy⟩, ?_, rfl⟩
          exact le_iSup (fun j : Fin 3 => pieceCore e ({j} : Finset (Fin 3))) _
            ((P (kJ J.1)).mem_pieceCore hF hf hn3 j h1 h2 hy)
        obtain ⟨y, hy, hyx⟩ := hAle x.2
        have hyx' : (⟨x, hKle J hJ0 hJ1 x.2⟩ : ctuBlock σ ε ({kJ J.1} : Finset (Fin 3))) = y :=
          Subtype.ext hyx.symm
        rw [hyx']
        exact hy
  have htor : ∀ (k : Fin 3) (κ : Kˣ), ψ (ctuEmbed ε hε σ ι hι (rootTorusHom K 3 k κ)) =
      ((e.symm (rootTorusHom K 3 k κ) : L) : G) := by
    intro k κ
    refine eq_of_rootTorusHom_of_tau (ψ.comp (ctuEmbed ε hε σ ι hι))
      (L.subtype.comp e.symm.toMonoidHom) (fun j hj κ => ?_) (fun j hj κ => ?_) k κ
    · have hjr : j.val + 1 < (2 * 3 + ε) / 2 := by omega
      obtain ⟨J, x, hx, hφx⟩ := htau ⟨j.val, by omega⟩ _
        (ctuEmbed_shortTorus_mem_rankOne hF hε (ι := ι) (hι := hι) (j := ⟨j.val, by omega⟩)
          hjr κ)
        (fun k hk1 hk2 => diagSp_mem_spBlock_compl_of_eq_one (by
          have hk1' : k ≠ ⟨j.val, by omega⟩ := fun h => hk1 (by rw [h])
          have hk2' : k ≠ ⟨j.val + 1, by omega⟩ := fun h => hk2 (by rw [h])
          rw [Pi.mul_apply, Pi.mulSingle_eq_of_ne hk1', Pi.mulSingle_eq_of_ne hk2', mul_one]))
      change ψ (ctuEmbed ε hε σ ι hι _) = ((e.symm _ : L) : G)
      rw [← hx, hψφ J x, hφx]
    · have hjr : ¬(j.val + 1 < (2 * 3 + ε) / 2) := by omega
      obtain ⟨J, x, hx, hφx⟩ := htau ⟨j.val, by omega⟩ _
        (ctuEmbed_rootTorusHom_mem_rankOne hF hε (ι := ι) (hι := hι) (j := ⟨j.val, by omega⟩)
          hjr κ)
        (fun k hk1 _ => by
          rw [rootTorusHom_apply]
          exact diagSp_mem_spBlock_compl_of_eq_one (by
            have hk1' : k ≠ ⟨j.val, by omega⟩ := fun h => hk1 (by rw [h])
            rw [Pi.mulSingle_eq_of_ne hk1']))
      change ψ (ctuEmbed ε hε σ ι hι _) = ((e.symm _ : L) : G)
      rw [← hx, hψφ J x, hφx]
  have hEk : ∀ k : Fin 3, neighbourCore e k ≤ G₀ := by
    intro k
    set B' := ctuBlock σ ε ({k} : Finset (Fin 3)) with hB'
    set A' := perfectCore B' with hA'def
    have hAB : A' ≤ B' := CFSG.Quasithin.perfectCore_le B'
    have hk' : k ∈ ({k} : Finset (Fin 3)) := Finset.mem_singleton_self k
    have hA1 : A'.map ψ ≤ neighbourCore e k := by
      refine CFSG.Quasithin.le_perfectCore_of_perfect ?_ ?_
      · rintro _ ⟨a, ha, rfl⟩
        rw [mem_centralizer_iff]
        intro g hg
        obtain ⟨x, hx, rfl⟩ := (UnitaryPilot.mem_modelToG e).1 hg
        obtain ⟨κ, rfl⟩ := mem_rootTorusSp.1 hx
        have hxs : rootTorusHom K 3 k κ ∈ spBlock K ({k} : Finset (Fin 3)) := by
          rw [spBlock_singleton]
          exact rootTorusSp_le_longRootSp2 k (rootTorusHom_mem_rootTorusSp k κ)
        rw [← htor k κ, ← map_mul, ← map_mul]
        congr 1
        exact (commute_ctuBlock_ctuEmbed (hAB ha) hxs).symm
      · rw [← map_commutator, CFSG.Quasithin.perfectCore_perfect]
    have hcardE : Nat.card (neighbourCore e k) ≤ Nat.card (A'.map ψ) := by
      have hinj : Function.Injective (ψ.comp A'.subtype) := by
        intro x y hxy
        exact Subtype.ext (injOn_ctuBlock_of_ker_le_center hF hn3 hnq hψker hk' (hAB x.2)
          (hAB y.2) hxy)
      have h1 : Nat.card (A'.map ψ) = Nat.card A' := by
        have h2 : A'.map ψ = (ψ.comp A'.subtype).range := by
          rw [MonoidHom.range_comp, range_subtype]
        rw [h2]
        exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
      have hEperf : perfectCore (neighbourCore e k) = neighbourCore e k :=
        CFSG.Quasithin.perfectCore_eq_self_of_perfect
          (F4Pilot.commutator_centralizerPerfectCore _)
      have h3 : neighbourCore e k = (perfectCore (⊤ : Subgroup B')).map (P k).Φ := by
        rw [CFSG.Quasithin.map_perfectCore, ← MonoidHom.range_eq_map, (P k).range_eq, hEperf]
      have h4 : (perfectCore (⊤ : Subgroup B')).map B'.subtype = A' := by
        rw [CFSG.Quasithin.map_perfectCore, ← MonoidHom.range_eq_map, range_subtype]
      rw [h1, h3, ← h4, Subgroup.card_map_of_injective B'.subtype_injective]
      exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd _ _)
    have heq := Subgroup.eq_of_le_of_card_ge hA1 hcardE
    rw [← heq, ← hψrange]
    rintro _ ⟨a, -, rfl⟩
    exact ⟨a, rfl⟩
  have hG₀eq : G₀ = spGlobal e := le_antisymm hG₀le
    ((spGlobal_le_iSup_neighbourCore le_rfl e).trans (iSup_le hEk))
  clear_value G₀
  subst hG₀eq
  refine ⟨ψ, hψrange, hψker, hqs, ?_, hLM⟩
  rw [hZ]
  exact Odd.of_dvd_nat (odd_card_center_SU hF (by omega) hn3 hnq) (Subgroup.card_map_dvd _ _)

theorem spGlobalCoverType_three_of_ctuParam [Finite K] (hKc : Nat.card K = 2 ^ f)
    (hf : 2 ≤ f) (hF : Nat.card F = (2 ^ f) ^ 2) {κ : Sp2mKind}
    (hκ : (κ = .unitaryEven ∧ ε = 0) ∨ (κ = .unitaryOdd ∧ ε = 1))
    (P : ∀ k : Fin 3, CtuParam ε hε (unitaryInvolution F 2 f) ι hι e k)
    (horth : ∀ a ∈ pieceCore e ({0} : Finset (Fin 3)),
      ∀ b ∈ pieceCore e ({2} : Finset (Fin 3)), Commute a b)
    (ρ₁ : levi (rootGroup (unitaryInvolution F 2 f) (unitaryInvolution_involutive hF)
      (2 * 3 + ε)) {⟨0, by omega⟩, ⟨1, by omega⟩} →* G)
    (hρ₀ : ∀ (x : SU (unitaryInvolution F 2 f) (2 * 3 + ε))
      (hx : x ∈ rankOne (rootGroup (unitaryInvolution F 2 f) (unitaryInvolution_involutive hF)
        (2 * 3 + ε)) ⟨0, by omega⟩),
      ρ₁ ⟨x, CFSG.LieType.CurtisTits.rankOne_le_levi _ (by simp) hx⟩ =
        (P 2).Φ ⟨x, rankOne_le_ctuBlock hε ⟨0, by omega⟩ (by simp) (by simp) hx⟩)
    (hρ₁ : ∀ (x : SU (unitaryInvolution F 2 f) (2 * 3 + ε))
      (hx : x ∈ rankOne (rootGroup (unitaryInvolution F 2 f) (unitaryInvolution_involutive hF)
        (2 * 3 + ε)) ⟨1, by omega⟩),
      ρ₁ ⟨x, CFSG.LieType.CurtisTits.rankOne_le_levi _ (by simp) hx⟩ =
        (P 0).Φ ⟨x, rankOne_le_ctuBlock hε ⟨1, by omega⟩ (by simp) (by simp) hx⟩) :
    SpGlobalCoverType e f κ := by
  obtain ⟨-, -, -, hqs, hodd, hLM⟩ :=
    exists_ct_uniRow_three hKc hf hF P horth ρ₁ hρ₀ hρ₁
  refine ⟨hqs, hodd, ?_⟩
  rcases hκ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hLM
  · exact hLM

end Recognition

end CFSG.SeitzReduction.SymplecticPilot
