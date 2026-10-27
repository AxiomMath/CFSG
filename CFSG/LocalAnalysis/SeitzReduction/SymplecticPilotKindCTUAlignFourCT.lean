module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTUnitaryMain

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

theorem exists_plane_four_ctua_numeric : ∀ a b : Fin 4, ¬(a.val = 0 ∧ b.val = 2) →
    ¬(a.val = 2 ∧ b.val = 0) → ∃ k : Fin 4,
      k.val ≠ a.val ∧ k.val ≠ a.val + 1 ∧ k.val ≠ b.val ∧ k.val ≠ b.val + 1 := by
  decide

theorem exists_plane_off_ctu_four {m : ℕ} (hm : m ≤ 4) (J : Finset (Fin m)) (hJ : J.card ≤ 2)
    (hJ₀ : ∀ a ∈ J, ∀ b ∈ J, ¬(a.val = 0 ∧ b.val = 2)) :
    ∃ k : Fin 4, ∀ j ∈ J, k.val ≠ j.val ∧ k.val ≠ j.val + 1 := by
  have key : ∀ a b : Fin m, ¬(a.val = 0 ∧ b.val = 2) → ¬(a.val = 2 ∧ b.val = 0) →
      ∃ k : Fin 4, ∀ j : Fin m, (j = a ∨ j = b) → k.val ≠ j.val ∧ k.val ≠ j.val + 1 := by
    intro a b h1 h2
    obtain ⟨k, hk⟩ := exists_plane_four_ctua_numeric ⟨a.val, by omega⟩ ⟨b.val, by omega⟩ h1 h2
    refine ⟨k, fun j hj => ?_⟩
    rcases hj with rfl | rfl
    · exact ⟨hk.1, hk.2.1⟩
    · exact ⟨hk.2.2.1, hk.2.2.2⟩
  rcases Nat.lt_or_ge J.card 2 with hlt | hge
  · rcases Nat.lt_or_ge J.card 1 with h0 | h1
    · have hJe : J = ∅ := Finset.card_eq_zero.1 (by omega)
      subst hJe
      exact ⟨0, fun j hj => by simp at hj⟩
    · obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 (show J.card = 1 by omega)
      obtain ⟨k, hk⟩ := key a a (fun h' => by obtain ⟨h1, h2⟩ := h'; omega)
        (fun h' => by obtain ⟨h1, h2⟩ := h'; omega)
      exact ⟨k, fun j hj => hk j (Or.inl (Finset.mem_singleton.1 hj))⟩
  · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 (show J.card = 2 by omega)
    obtain ⟨k, hk⟩ := key a b (hJ₀ a (by simp) b (by simp))
      (fun h' => hJ₀ b (by simp) a (by simp) ⟨h'.2, h'.1⟩)
    exact ⟨k, fun j hj => hk j (by simpa using hj)⟩

theorem subset_singleton_or_of_subset_pair_ctua {α : Type*} [DecidableEq α] {a b : α}
    {I : Finset α} (hI : I ⊆ {a, b}) (hne : I ≠ {a, b}) : I ⊆ {a} ∨ I ⊆ {b} := by
  by_cases hb : b ∈ I
  · right
    intro j hj
    rcases Finset.mem_insert.1 (hI hj) with rfl | h
    · exfalso
      exact hne (Finset.Subset.antisymm hI (by
        intro x hx
        rcases Finset.mem_insert.1 hx with rfl | hx
        · exact hj
        · rw [Finset.mem_singleton.1 hx]
          exact hb))
    · exact h
  · left
    intro j hj
    rcases Finset.mem_insert.1 (hI hj) with rfl | h
    · exact Finset.mem_singleton_self _
    · rw [Finset.mem_singleton.1 h] at hj
      exact absurd hj hb

section Factors

variable {F : Type} [Field F] {σ : F ≃+* F} {hσ : ∀ c, σ (σ c) = c} {n : ℕ}

theorem ctuToSL_mem_blockSpecialLinear_of_mem_rankOne {j : Fin (n / 2)} (hj : j.val + 1 < n / 2)
    {x : SU σ n} (hx : x ∈ rankOne (rootGroup σ hσ n) j) :
    ctuToSL σ n x ∈ blockSpecialLinear (Finset.univ.filter fun a => blkShort j hj a ≠ 0) := by
  rw [mem_blockSpecialLinear]
  intro a b hab
  rw [coe_ctuToSL]
  apply (isBlk_short_of_mem hj hx).1 a b
  rintro ⟨h1, h2⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hab
  rcases hab with h | h
  · exact h2 h
  · exact h2 (h1.trans h)

theorem blkShort_ne_zero_iff {j : Fin (n / 2)} (hj : j.val + 1 < n / 2) (a : Fin n) :
    blkShort j hj a ≠ 0 ↔ (a.val = j.val ∨ a.val = j.val + 1) ∨
      (a.val = n - 1 - j.val ∨ a.val = n - 1 - (j.val + 1)) := by
  unfold blkShort
  simp only [Fin.ext_iff, Fin.val_rev, val_lowIdx]
  split_ifs with h1 h2 <;> omega

theorem disjoint_blkShort_zero_two (hn : 8 ≤ n) (h0 : 0 + 1 < n / 2) (h2 : 2 + 1 < n / 2) :
    Disjoint (Finset.univ.filter fun a => blkShort (n := n) ⟨0, by omega⟩ h0 a ≠ 0)
      (Finset.univ.filter fun a => blkShort (n := n) ⟨2, by omega⟩ h2 a ≠ 0) := by
  rw [Finset.disjoint_left]
  intro a ha hb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  rw [blkShort_ne_zero_iff] at ha hb
  simp only at ha hb
  omega

theorem commute_rankOne_zero_two (hn : 8 ≤ n) (h0 : 0 + 1 < n / 2) (h2 : 2 + 1 < n / 2)
    {x y : SU σ n} (hx : x ∈ rankOne (rootGroup σ hσ n) ⟨0, by omega⟩)
    (hy : y ∈ rankOne (rootGroup σ hσ n) ⟨2, by omega⟩) : Commute x y := by
  have h := LinearPilot.commute_blockSpecialLinear_of_disjoint (disjoint_blkShort_zero_two hn h0 h2)
    (ctuToSL_mem_blockSpecialLinear_of_mem_rankOne h0 hx)
    (ctuToSL_mem_blockSpecialLinear_of_mem_rankOne h2 hy)
  apply ctuToSL_injective
  rw [map_mul, map_mul]
  exact h.eq

theorem rankOne_zero_inf_two (hn : 8 ≤ n) (h0 : 0 + 1 < n / 2) (h2 : 2 + 1 < n / 2) :
    rankOne (rootGroup σ hσ n) ⟨0, by omega⟩ ⊓ rankOne (rootGroup σ hσ n) ⟨2, by omega⟩ = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx0, hx2⟩
  have h1 := blockSpecialLinear_inf_le _ _ ⟨ctuToSL_mem_blockSpecialLinear_of_mem_rankOne h0 hx0,
    ctuToSL_mem_blockSpecialLinear_of_mem_rankOne h2 hx2⟩
  rw [Finset.disjoint_iff_inter_eq_empty.1 (disjoint_blkShort_zero_two hn h0 h2),
    LinearPilot.blockSpecialLinear_empty] at h1
  rw [Subgroup.mem_bot]
  exact ctuToSL_injective (by rw [map_one]; exact Subgroup.mem_bot.1 h1)

end Factors

section Recognition

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]
  [CharP K 2] {ε : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} {hε : ε ≤ 1}
  {ι : K →+* F} {hι : ∀ c, unitaryInvolution F 2 f (ι c) = ι c} {e : L ≃* StatedSp 4 K}

set_option maxHeartbeats 400000 in
theorem exists_ct_uniRow_four_of_agree [Finite K] (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (hF : Nat.card F = (2 ^ f) ^ 2)
    (P : ∀ k : Fin 4, CtuParam ε hε (unitaryInvolution F 2 f) ι hι e k)
    (hagree : CtuParamAgree P)
    (horth : ∀ a ∈ pieceCore e ({0} : Finset (Fin 4)),
      ∀ b ∈ pieceCore e ({2} : Finset (Fin 4)), Commute a b) :
    ∃ ψ : SU (unitaryInvolution F 2 f) (2 * 4 + ε) →* G, ψ.range = spGlobal e ∧
      ψ.ker ≤ center (SU (unitaryInvolution F 2 f) (2 * 4 + ε)) ∧
      CFSG.IsQuasisimple (spGlobal e) ∧ Odd (Nat.card (center (spGlobal e))) ∧
      LieModel (spGlobal e ⧸ center (spGlobal e)) .PSU (2 * 4 + ε) 2 f := by
  classical
  have hK4 : 4 ≤ Nat.card K := hKc ▸ four_le_two_pow hf
  have hn3 : 3 ≤ 2 * 4 + ε := by omega
  have hnq : (2 * 4 + ε, 2 ^ f) ≠ (3, 2) := fun h => by
    have := (Prod.mk.inj h).1
    omega
  set σ := unitaryInvolution F 2 f with hσdef
  set D := rootDatum hF (2 * 4 + ε) with hD
  have hrank : D.rank = (2 * 4 + ε) / 2 := rfl
  have hdiv : (2 * 4 + ε) / 2 = 4 := by omega
  have h0 : 0 + 1 < (2 * 4 + ε) / 2 := by omega
  have h2 : 2 + 1 < (2 * 4 + ε) / 2 := by omega
  set j₀ : Fin D.rank := ⟨0, by omega⟩ with hj₀
  set j₂ : Fin D.rank := ⟨2, by omega⟩ with hj₂
  have hj02 : j₀ ≠ j₂ := fun h => by simp [hj₀, hj₂, Fin.ext_iff] at h
  set J₀ : Finset (Fin D.rank) := {j₀, j₂} with hJ₀def
  have hgood : ∀ J : {J : Finset (Fin D.rank) // J.card ≤ 2}, J.1 ≠ J₀ →
      ∀ a ∈ J.1, ∀ b ∈ J.1, ¬(a.val = 0 ∧ b.val = 2) := by
    intro J hJ a ha b hb ⟨ha0, hb2⟩
    apply hJ
    have ha' : a = j₀ := Fin.ext ha0
    have hb' : b = j₂ := Fin.ext hb2
    rw [ha'] at ha
    rw [hb'] at hb
    symm
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact ha
      · rw [Finset.mem_singleton.1 hx]
        exact hb
    · rw [hJ₀def, Finset.card_pair hj02]
      exact J.2
  choose kJ hkJ using fun (J : {J : Finset (Fin D.rank) // J.card ≤ 2}) (h : J.1 ≠ J₀) =>
    exists_plane_off_ctu_four (m := D.rank) (by omega) J.1 J.2 (hgood J h)
  have hKle : ∀ (J : {J : Finset (Fin D.rank) // J.card ≤ 2}) (h : J.1 ≠ J₀),
      D.leviAmalgam J ≤ ctuBlock σ ε ({kJ J h} : Finset (Fin 4)) :=
    fun J h => levi_le_ctuBlock hε (hkJ J h)
  set J₁ : {J : Finset (Fin D.rank) // J.card ≤ 2} := ⟨{j₀}, by simp⟩ with hJ₁
  set J₃ : {J : Finset (Fin D.rank) // J.card ≤ 2} := ⟨{j₂}, by simp⟩ with hJ₃
  have hJ₁ne : J₁.1 ≠ J₀ := fun h => by
    have := congrArg Finset.card h
    rw [Finset.card_singleton, hJ₀def, Finset.card_pair hj02] at this
    omega
  have hJ₃ne : J₃.1 ≠ J₀ := fun h => by
    have := congrArg Finset.card h
    rw [Finset.card_singleton, hJ₀def, Finset.card_pair hj02] at this
    omega
  set A := D.leviAmalgam J₁ with hA
  set B := D.leviAmalgam J₃ with hB
  have hArank : A ≤ rankOne D.rootGroup j₀ := iSup₂_le fun j hj => by
    rw [Finset.mem_singleton.1 hj]
  have hBrank : B ≤ rankOne D.rootGroup j₂ := iSup₂_le fun j hj => by
    rw [Finset.mem_singleton.1 hj]
  have hcommAB : ∀ a ∈ A, ∀ b ∈ B, Commute a b := fun a ha b hb =>
    commute_rankOne_zero_two (by omega) h0 h2 (hArank ha) (hBrank hb)
  have hdisjAB : A ⊓ B = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [← rankOne_zero_inf_two (σ := σ) (hσ := unitaryInvolution_involutive hF) (by omega) h0 h2]
    exact ⟨hArank hx.1, hBrank hx.2⟩
  have hlevi₀ : ∀ J : {J : Finset (Fin D.rank) // J.card ≤ 2}, J.1 = J₀ →
      D.leviAmalgam J = A ⊔ B := by
    intro J hJ
    change levi _ J.1 = _
    rw [hJ, hJ₀def]
    exact F4Pilot.levi_pair D.rootGroup j₀ j₂
  have h20 : (2 : Fin 4).val ≠ j₀.val := by simp [hj₀]
  have h21 : (2 : Fin 4).val ≠ j₀.val + 1 := by simp [hj₀]
  have h02 : (0 : Fin 4).val ≠ j₂.val := by simp [hj₂]
  have h03 : (0 : Fin 4).val ≠ j₂.val + 1 := by simp [hj₂]
  set fA : A →* G := (P (kJ J₁ hJ₁ne)).Φ.comp (Subgroup.inclusion (hKle J₁ hJ₁ne)) with hfA
  set gB : B →* G := (P (kJ J₃ hJ₃ne)).Φ.comp (Subgroup.inclusion (hKle J₃ hJ₃ne)) with hgB
  have hfA2 : ∀ a : A, fA a = (P 2).Φ ⟨a, rankOne_le_ctuBlock hε j₀ h20 h21 (hArank a.2)⟩ :=
    fun a => hagree _ _ _ (hKle J₁ hJ₁ne a.2) _
  have hgB0 : ∀ b : B, gB b = (P 0).Φ ⟨b, rankOne_le_ctuBlock hε j₂ h02 h03 (hBrank b.2)⟩ :=
    fun b => hagree _ _ _ (hKle J₃ hJ₃ne b.2) _
  have hfA_mem : ∀ a : A, fA a ∈ pieceCore e ({0} : Finset (Fin 4)) := by
    intro a
    rw [hfA2]
    exact (P 2).mem_pieceCore hF hf hn3 j₀ h20 h21 (hArank a.2)
  have hgB_mem : ∀ b : B, gB b ∈ pieceCore e ({2} : Finset (Fin 4)) := by
    intro b
    rw [hgB0]
    exact (P 0).mem_pieceCore hF hf hn3 j₂ h02 h03 (hBrank b.2)
  have hfg : ∀ a b, Commute (fA a) (gB b) := fun a b => horth _ (hfA_mem a) _ (hgB_mem b)
  set ρ : ↥(A ⊔ B) →* G := F4Pilot.supLift hcommAB hdisjAB fA gB hfg with hρ
  have hρA : ∀ a : A, ρ ⟨a, mem_sup_left a.2⟩ = fA a := F4Pilot.supLift_apply_left _ _ hfg
  have hρB : ∀ b : B, ρ ⟨b, mem_sup_right b.2⟩ = gB b := F4Pilot.supLift_apply_right _ _ hfg
  obtain ⟨φ, hφne, hφ0⟩ : ∃ φ : ∀ J : {J : Finset (Fin D.rank) // J.card ≤ 2},
      D.leviAmalgam J →* G,
      (∀ (J : {J : Finset (Fin D.rank) // J.card ≤ 2}) (h : J.1 ≠ J₀) x,
        φ J x = (P (kJ J h)).Φ ⟨x, hKle J h x.2⟩) ∧
      ∀ (J : {J : Finset (Fin D.rank) // J.card ≤ 2}) (h : J.1 = J₀) x,
        φ J x = ρ ⟨x, (hlevi₀ J h).le x.2⟩ := by
    refine ⟨fun J => if h : J.1 = J₀ then ρ.comp (Subgroup.inclusion (hlevi₀ J h).le)
      else (P (kJ J h)).Φ.comp (Subgroup.inclusion (hKle J h)), fun J h x => ?_, fun J h x => ?_⟩
    · simp only [h, ↓reduceDIte]
      rfl
    · simp only [h, ↓reduceDIte]
      rfl
  have hcomp : CFSG.LieType.CurtisTits.IsCompatible D.leviAmalgam φ := by
    intro I J hIJ x y hxy
    have hIJ' : I.1 ⊆ J.1 := hIJ
    by_cases hJ : J.1 = J₀
    · by_cases hI : I.1 = J₀
      · have hIJeq : I = J := Subtype.ext (hI.trans hJ.symm)
        subst hIJeq
        exact congrArg (φ I) (Subtype.ext hxy)
      · rw [hφne I hI, hφ0 J hJ]
        have hIJ₀ : I.1 ⊆ J₀ := by
          rw [← hJ]
          exact hIJ'
        rcases subset_singleton_or_of_subset_pair_ctua hIJ₀ hI with hI1 | hI2
        · have hyA : (y : SU σ (2 * 4 + ε)) ∈ A := by
            rw [← hxy]
            exact CFSG.LieType.CurtisTits.levi_mono _ hI1 x.2
          change _ = ρ ⟨((⟨y, hyA⟩ : A) : SU σ (2 * 4 + ε)), mem_sup_left hyA⟩
          rw [hρA, hfA]
          have hy' : (x : SU σ (2 * 4 + ε)) ∈ ctuBlock σ ε ({kJ J₁ hJ₁ne} : Finset (Fin 4)) := by
            rw [hxy]
            exact hKle J₁ hJ₁ne hyA
          rw [hagree (kJ I hI) (kJ J₁ hJ₁ne) _ (hKle I hI x.2) hy']
          exact congrArg _ (Subtype.ext hxy)
        · have hyB : (y : SU σ (2 * 4 + ε)) ∈ B := by
            rw [← hxy]
            exact CFSG.LieType.CurtisTits.levi_mono _ hI2 x.2
          change _ = ρ ⟨((⟨y, hyB⟩ : B) : SU σ (2 * 4 + ε)), mem_sup_right hyB⟩
          rw [hρB, hgB]
          have hy' : (x : SU σ (2 * 4 + ε)) ∈ ctuBlock σ ε ({kJ J₃ hJ₃ne} : Finset (Fin 4)) := by
            rw [hxy]
            exact hKle J₃ hJ₃ne hyB
          rw [hagree (kJ I hI) (kJ J₃ hJ₃ne) _ (hKle I hI x.2) hy']
          exact congrArg _ (Subtype.ext hxy)
    · have hI : I.1 ≠ J₀ := fun hI => by
        have hJ₀J : J₀ ⊆ J.1 := by
          rw [← hI]
          exact hIJ'
        exact hJ (Finset.eq_of_subset_of_card_le hJ₀J
          (by rw [hJ₀def, Finset.card_pair hj02]; exact J.2)).symm
      rw [hφne I hI, hφne J hJ]
      have hy' : (x : SU σ (2 * 4 + ε)) ∈ ctuBlock σ ε ({kJ J hJ} : Finset (Fin 4)) := by
        rw [hxy]
        exact hKle J hJ y.2
      rw [hagree (kJ I hI) (kJ J hJ) _ (hKle I hI x.2) hy']
      exact congrArg _ (Subtype.ext hxy)
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
  have htau : ∀ (j : Fin D.rank) (y : StatedSp 4 K)
      (hy : ctuEmbed ε hε σ ι hι y ∈ rankOne D.rootGroup j)
      (hys : ∀ k : Fin 4, k.val ≠ j.val → k.val ≠ j.val + 1 →
        y ∈ spBlock K ({k} : Finset (Fin 4))ᶜ),
      ∃ (J : {J : Finset (Fin D.rank) // J.card ≤ 2}) (x : D.leviAmalgam J),
        (x : SU σ (2 * 4 + ε)) = ctuEmbed ε hε σ ι hι y ∧ φ J x = ((e.symm y : L) : G) := by
    intro j y hy hys
    set J : {J : Finset (Fin D.rank) // J.card ≤ 2} := ⟨{j}, by simp⟩ with hJ
    have hJne : J.1 ≠ J₀ := fun h => by
      have := congrArg Finset.card h
      rw [Finset.card_singleton, hJ₀def, Finset.card_pair hj02] at this
      omega
    have hxJ : ctuEmbed ε hε σ ι hι y ∈ D.leviAmalgam J :=
      CFSG.LieType.CurtisTits.rankOne_le_levi _ (Finset.mem_singleton_self j) hy
    refine ⟨J, ⟨_, hxJ⟩, rfl, ?_⟩
    rw [hφne J hJne]
    obtain ⟨h1, h2⟩ := hkJ J hJne j (Finset.mem_singleton_self j)
    exact (P (kJ J hJne)).N1' (hys _ h1 h2) _ rfl
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
    have h2 : e.symm (diagSp K 4 (Pi.mulSingle (⟨0, by omega⟩ : Fin 4) κ *
        Pi.mulSingle ⟨0 + 1, by omega⟩ κ⁻¹)) = 1 := Subtype.ext h1
    rw [MulEquiv.map_eq_one_iff] at h2
    have h3 := congrFun (diagSp_injective (h2.trans (map_one _).symm)) ⟨0, by omega⟩
    have hne : (⟨0, by omega⟩ : Fin 4) ≠ ⟨0 + 1, by omega⟩ := fun h => by
      have := congrArg Fin.val h
      simp at this
    rw [Pi.mul_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hne, mul_one] at h3
    exact hκ1 h3
  have hadm : StatedLieAdmissible .PSU (2 * 4 + ε) 2 f := ⟨Nat.prime_two, by omega, hn3, hnq⟩
  obtain ⟨-, -, hrec, -⟩ :=
    CFSG.LieType.CurtisTits.curtisTitsConclusion_unitary.{0} (F := F) (p := 2) (f := f)
      (n := 2 * 4 + ε) hadm hF
  obtain ⟨ψ₀, hψ₀, hsurj, hker, hqs, hZ, -, hLM⟩ := hrec G₀ φ' hcomp' hgen' hnt
  set ψ : SU σ (2 * 4 + ε) →* G := G₀.subtype.comp ψ₀ with hψdef
  have hψrange : ψ.range = G₀ := by
    rw [hψdef, MonoidHom.range_comp, MonoidHom.range_eq_top.2 hsurj, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hψφ : ∀ J (x : D.leviAmalgam J), ψ x = φ J x := fun J x =>
    congrArg Subtype.val (hψ₀ J x)
  have hψker : ψ.ker ≤ center (SU σ (2 * 4 + ε)) := by
    intro z hz
    apply hker
    rw [MonoidHom.mem_ker] at hz ⊢
    exact G₀.subtype_injective (by rw [map_one]; exact hz)
  have hG₀le : G₀ ≤ spGlobal e := by
    refine iSup_le fun J => ?_
    rintro _ ⟨x, rfl⟩
    by_cases hJ : J.1 = J₀
    · rw [hφ0 J hJ]
      have hρle : ρ.range ≤ spGlobal e := by
        rw [hρ, F4Pilot.range_supLift]
        refine sup_le ?_ ?_
        · rintro _ ⟨a, rfl⟩
          exact le_iSup (fun j : Fin 4 => pieceCore e ({j} : Finset (Fin 4))) 0 (hfA_mem a)
        · rintro _ ⟨b, rfl⟩
          exact le_iSup (fun j : Fin 4 => pieceCore e ({j} : Finset (Fin 4))) 2 (hgB_mem b)
      exact hρle ⟨_, rfl⟩
    · rw [hφne J hJ]
      set A' : Subgroup (SU σ (2 * 4 + ε)) := ((spGlobal e).comap (P (kJ J hJ)).Φ).map
        (ctuBlock σ ε ({kJ J hJ} : Finset (Fin 4))).subtype with hA'
      have hAle : D.leviAmalgam J ≤ A' := by
        refine iSup₂_le fun j hj => ?_
        intro y hy
        obtain ⟨h1, h2⟩ := hkJ J hJ j hj
        refine ⟨⟨y, rankOne_le_ctuBlock hε j h1 h2 hy⟩, ?_, rfl⟩
        exact le_iSup (fun j : Fin 4 => pieceCore e ({j} : Finset (Fin 4))) _
          ((P (kJ J hJ)).mem_pieceCore hF hf hn3 j h1 h2 hy)
      obtain ⟨y, hy, hyx⟩ := hAle x.2
      have hyx' : (⟨x, hKle J hJ x.2⟩ : ctuBlock σ ε ({kJ J hJ} : Finset (Fin 4))) = y :=
        Subtype.ext hyx.symm
      rw [hyx']
      exact hy
  have htor : ∀ (k : Fin 4) (κ : Kˣ), ψ (ctuEmbed ε hε σ ι hι (rootTorusHom K 4 k κ)) =
      ((e.symm (rootTorusHom K 4 k κ) : L) : G) := by
    intro k κ
    refine eq_of_rootTorusHom_of_tau (ψ.comp (ctuEmbed ε hε σ ι hι))
      (L.subtype.comp e.symm.toMonoidHom) (fun j hj κ => ?_) (fun j hj κ => ?_) k κ
    · have hjr : j.val + 1 < (2 * 4 + ε) / 2 := by omega
      obtain ⟨J, x, hx, hφx⟩ := htau ⟨j.val, by omega⟩ _
        (ctuEmbed_shortTorus_mem_rankOne hF hε (ι := ι) (hι := hι) (j := ⟨j.val, by omega⟩)
          hjr κ)
        (fun k hk1 hk2 => diagSp_mem_spBlock_compl_of_eq_one (by
          have hk1' : k ≠ ⟨j.val, by omega⟩ := fun h => hk1 (by rw [h])
          have hk2' : k ≠ ⟨j.val + 1, by omega⟩ := fun h => hk2 (by rw [h])
          rw [Pi.mul_apply, Pi.mulSingle_eq_of_ne hk1', Pi.mulSingle_eq_of_ne hk2', mul_one]))
      change ψ (ctuEmbed ε hε σ ι hι _) = ((e.symm _ : L) : G)
      rw [← hx, hψφ J x, hφx]
    · have hjr : ¬(j.val + 1 < (2 * 4 + ε) / 2) := by omega
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
  have hEk : ∀ k : Fin 4, neighbourCore e k ≤ G₀ := by
    intro k
    set B' := ctuBlock σ ε ({k} : Finset (Fin 4)) with hB'
    set A' := perfectCore B' with hA'def
    have hAB : A' ≤ B' := CFSG.Quasithin.perfectCore_le B'
    have hk' : k ∈ ({k} : Finset (Fin 4)) := Finset.mem_singleton_self k
    have hA1 : A'.map ψ ≤ neighbourCore e k := by
      refine CFSG.Quasithin.le_perfectCore_of_perfect ?_ ?_
      · rintro _ ⟨a, ha, rfl⟩
        rw [mem_centralizer_iff]
        intro g hg
        obtain ⟨x, hx, rfl⟩ := (UnitaryPilot.mem_modelToG e).1 hg
        obtain ⟨κ, rfl⟩ := mem_rootTorusSp.1 hx
        have hxs : rootTorusHom K 4 k κ ∈ spBlock K ({k} : Finset (Fin 4)) := by
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
    ((spGlobal_le_iSup_neighbourCore (by omega) e).trans (iSup_le hEk))
  clear_value G₀
  subst hG₀eq
  refine ⟨ψ, hψrange, hψker, hqs, ?_, hLM⟩
  rw [hZ]
  exact Odd.of_dvd_nat (odd_card_center_SU hF (by omega) hn3 hnq) (Subgroup.card_map_dvd _ _)

theorem spGlobalCoverType_four_of_ctuParamAgree [Finite K] (hKc : Nat.card K = 2 ^ f)
    (hf : 2 ≤ f) (hF : Nat.card F = (2 ^ f) ^ 2) {κ : Sp2mKind}
    (hκ : (κ = .unitaryEven ∧ ε = 0) ∨ (κ = .unitaryOdd ∧ ε = 1))
    (P : ∀ k : Fin 4, CtuParam ε hε (unitaryInvolution F 2 f) ι hι e k)
    (hagree : CtuParamAgree P)
    (horth : ∀ a ∈ pieceCore e ({0} : Finset (Fin 4)),
      ∀ b ∈ pieceCore e ({2} : Finset (Fin 4)), Commute a b) :
    SpGlobalCoverType e f κ := by
  obtain ⟨-, -, -, hqs, hodd, hLM⟩ := exists_ct_uniRow_four_of_agree hKc hf hF P hagree horth
  refine ⟨hqs, hodd, ?_⟩
  rcases hκ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hLM
  · exact hLM

end Recognition

end CFSG.SeitzReduction.SymplecticPilot
