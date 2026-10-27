module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf91MuS4
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf90AE5Mu

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open scoped commutatorElement

open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE

section Ex

section Datum

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K K' K₃ : Subgroup G}
  {z u₁ u₂ u₃ : G}

theorem exists_adapted_hyp22G (hd : A7T22.Hyp22G Ω K K' K₃ z u₁ u₂ u₃) :
    ∃ x y w : G, A7T22.Hyp22G Ω K K' K₃ z x y w ∧ ∃ W ∈ WSet Ω, ∃ R₁ R₂ R₃ : Subgroup G,
      IsSylow2In R₁ K ∧ IsSylow2In R₂ K' ∧ IsSylow2In R₃ K₃ ∧ R₁ ∈ DSet Ω W ∧ R₂ ∈ DSet Ω W ∧
        R₃ ∈ DSet Ω W ∧ x ∈ R₁ ⊓ W ∧ y ∈ R₂ ⊓ W ∧ w ∈ R₃ ⊓ W := by
  classical
  have hΩ := hd.hyp
  have hz := hd.hz
  have hKt : K ∈ twinSet Ω K := mem_twinSet_self hd.mem hz
  obtain ⟨R, hRs, hRc, hRP⟩ := Q3T8.Asc77.T7V.exists_sylow_family hΩ hz
    ({K, K', K₃} : Finset (Subgroup G)) (by
      intro M hM
      simp only [Finset.mem_insert, Finset.mem_singleton] at hM
      rcases hM with rfl | rfl | rfl
      · exact hKt
      · exact hd.hK'
      · exact hd.hK₃)
  obtain ⟨W, hW, hWD⟩ := Q3T8.Asc77.exists_W_of_isPGroup hΩ hRP
  have hRK : IsSylow2In (R K) K := hRs K (by simp)
  have hRK' : IsSylow2In (R K') K' := hRs K' (by simp)
  have hRK₃ : IsSylow2In (R K₃) K₃ := hRs K₃ (by simp)
  have hD : ∀ M ∈ ({K, K', K₃} : Finset (Subgroup G)), ∀ hM : M ∈ Ω, R M ∈ DSet Ω W := by
    intro M hM hMΩ
    exact hWD (R M) (mem_RSet_of_isSylow2In hMΩ (hRs M hM))
      (le_iSup₂_of_le M hM le_rfl)
  have hDK : R K ∈ DSet Ω W := hD K (by simp) hd.mem
  have hDK' : R K' ∈ DSet Ω W := hD K' (by simp) hd.hK'.1
  have hDK₃ : R K₃ ∈ DSet Ω W := hD K₃ (by simp) hd.hK₃.1
  obtain ⟨x, hx, ox⟩ := Q3T8.Asc77.Thompson.exists_orderOf_four hΩ hW hDK
  obtain ⟨y, hy, oy⟩ := Q3T8.Asc77.Thompson.exists_orderOf_four hΩ hW hDK'
  obtain ⟨w, hw, ow⟩ := Q3T8.Asc77.Thompson.exists_orderOf_four hΩ hW hDK₃
  have c12 : Commutes (R K) (R K') := hRc K (by simp) K' (by simp) (Ne.symm hd.hne)
  have c13 : Commutes (R K) (R K₃) := hRc K (by simp) K₃ (by simp) (Ne.symm hd.hK₃K)
  have c23 : Commutes (R K') (R K₃) := hRc K' (by simp) K₃ (by simp) (Ne.symm hd.hK₃K')
  exact ⟨x, y, w, hd.of_sylows hKt hd.hK' hd.hK₃ hd.hne hd.hK₃K hd.hK₃K' hRK hRK' hRK₃ c12 c13 c23
    hx.1 hy.1 hw.1 ox oy ow, W, hW, R K, R K', R K₃, hRK, hRK', hRK₃, hDK, hDK', hDK₃, hx, hy, hw⟩

theorem exists_adapted_hyp22G_of_isPGroup (hd : A7T22.Hyp22G Ω K K' K₃ z u₁ u₂ u₃)
    (h2g : ∀ J ∈ Ω, IsPGroup 2 ↥J) :
    ∃ x y w : G, A7T22.Hyp22G Ω K K' K₃ z x y w ∧ ∃ W ∈ WSet Ω, K ∈ DSet Ω W ∧ K' ∈ DSet Ω W ∧
      K₃ ∈ DSet Ω W ∧ x ∈ W ∧ y ∈ W ∧ w ∈ W := by
  obtain ⟨x, y, w, hd', W, hW, R₁, R₂, R₃, h1, h2, h3, hD1, hD2, hD3, hx, hy, hw⟩ :=
    exists_adapted_hyp22G hd
  have e1 : K = R₁ := h1.2.2 K le_rfl (h2g K hd.mem) h1.1
  have e2 : K' = R₂ := h2.2.2 K' le_rfl (h2g K' hd.hK'.1) h2.1
  have e3 : K₃ = R₃ := h3.2.2 K₃ le_rfl (h2g K₃ hd.hK₃.1) h3.1
  subst e1 e2 e3
  exact ⟨x, y, w, hd', W, hW, hD1, hD2, hD3, hx.2, hy.2, hw.2⟩

end Datum

section Std

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y}

theorem exists_adapted_v3Std (hStd : V3Std n Y R S t K K' K₃ u₁ u₂ u₃)
    (h2g : ∀ J ∈ CoreAssembly.conjClass (tightCore R), IsPGroup 2 ↥J) :
    ∃ x y w : Y, V3Std n Y R S t K K' K₃ x y w ∧
      ∃ W ∈ WSet (CoreAssembly.conjClass (tightCore R)),
        K ∈ DSet (CoreAssembly.conjClass (tightCore R)) W ∧
        K' ∈ DSet (CoreAssembly.conjClass (tightCore R)) W ∧
        K₃ ∈ DSet (CoreAssembly.conjClass (tightCore R)) W ∧ x ∈ W ∧ y ∈ W ∧ w ∈ W := by
  obtain ⟨x, y, w, hd', W, hW, hD1, hD2, hD3, hx, hy, hw⟩ :=
    exists_adapted_hyp22G_of_isPGroup hStd.datum h2g
  exact ⟨x, y, w, ⟨hStd.perp, hStd.two, hStd.exit, hd', hStd.wyl⟩, W, hW, hD1, hD2, hD3, hx, hy, hw⟩

end Std

section AE5

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K K' K₃ K₄ : Subgroup Y} {u₁ u₂ u₃ : Y}

theorem v3ExitAE5_adapted (hin : V3ExitIn n R S t K K' K₃ u₁ u₂ u₃ K₄)
    {W : Subgroup Y} (hW : W ∈ WSet (CoreAssembly.conjClass (tightCore R)))
    (hKD : K ∈ DSet (CoreAssembly.conjClass (tightCore R)) W)
    (hK'D : K' ∈ DSet (CoreAssembly.conjClass (tightCore R)) W)
    (hK₃D : K₃ ∈ DSet (CoreAssembly.conjClass (tightCore R)) W) (hu₁ : u₁ ∈ W) (hu₂ : u₂ ∈ W)
    (hI : Nonempty (AEIdent (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) 5)) :
    False := by
  obtain ⟨W', hW', hE⟩ := v3SecAE5MuE4_proved n Y R S t K K' K₃ u₁ u₂ u₃ K₄ hin hI
  obtain ⟨e₁⟩ := hE
  obtain ⟨e₂⟩ := v3SecMuS4_adapted hin hW hKD hK'D hK₃D hu₁ hu₂ W' hW'
  have h := Nat.card_congr (e₁.symm.trans e₂).toEquiv
  have h24 : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]; rfl
  have h4 : Nat.card (Multiplicative (ZMod 2 × ZMod 2)) = 4 := by
    rw [Nat.card_eq_fintype_card]; rfl
  rw [h24, h4] at h
  omega

theorem v3ExitAE5W_proved (n : ℕ) :
    ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
      (K K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y) (K₄ : Subgroup Y),
      V3ExitIn n R S t K K' K₃ u₁ u₂ u₃ K₄ →
        ∀ W ∈ WSet (CoreAssembly.conjClass (tightCore R)),
          K ∈ DSet (CoreAssembly.conjClass (tightCore R)) W →
          K' ∈ DSet (CoreAssembly.conjClass (tightCore R)) W →
          K₃ ∈ DSet (CoreAssembly.conjClass (tightCore R)) W → u₁ ∈ W → u₂ ∈ W →
            Nonempty (AEIdent (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) 5) →
              False := by
  intro Y _ _ R S t K K' K₃ u₁ u₂ u₃ K₄ hin W hW hKD hK'D hK₃D hu₁ hu₂ hI
  exact v3ExitAE5_adapted hin hW hKD hK'D hK₃D hu₁ hu₂ hI

end AE5

end Ex

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
