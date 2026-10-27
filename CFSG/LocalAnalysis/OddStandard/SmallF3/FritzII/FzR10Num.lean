module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL319Mod
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL319Elt
public import Certificates.Data.FzR10

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Certificates.FzL26 Certificates.FzR10 Subgroup CFSG.OddStandard.SmallF3.HarrisU33
  CFSG.GH74.GLS.Bg.TwoGroups

variable {G : Type} [Group G] [Finite G] {t : G} {x₁ x₂ lam rho tau : G} {T₂ : Subgroup G}

abbrev FzDat (t x₁ x₂ lam rho tau : G) (T₂ : Subgroup G) : Type :=
  Fz319Data t tau lam rho (fourGrp x₁ x₂) (baseGrp x₁ x₂) (ctxW t x₁ x₂) (fzQ t x₁ x₂ rho)
    (fzR t x₁ x₂) T₂ (fzP t x₁ x₂ rho)

@[expose] noncomputable def fzrCMu (D : FzDat t x₁ x₂ lam rho tau T₂) (n : ℕ) : G :=
  D.mu (fzEOf n)

@[expose] noncomputable def fzrCPar (D : FzDat t x₁ x₂ lam rho tau T₂) : Par :=
  parOf (pctx ()) (fzAutI D.cT) (actTab (fzAutI D.cT) (fzAutI D.cS) (fzAutI D.cL))

variable (D : FzDat t x₁ x₂ lam rho tau T₂)

private theorem fzrAux_fzEOf_64 : fzEOf 64 = (1, (1, 0, 0)) := by decide +kernel

private theorem fzrAux_fzEOf_128 : fzEOf 128 = (1, (0, 1, 0)) := by decide +kernel

private theorem fzrAux_rho0_lt {y : ℕ} (hy : y < 64) : rho0 y < 64 := by
  have h : y = fzIdx (fzElt y) := (fzIdx_fzElt hy).symm
  rw [h, fzIdx_rho0]
  exact fzIdx_lt _

private theorem fzrAux_e_eq {n m : ℕ} (hn : n < 512) (hm : m < 512) :
    (fzrCPar D).e n m =
      fzEIdx (fzMulC D.cT D.cS D.cL (fzEOf n) (fzEOf m)) := by
  show (pctx ()).em (actTab (fzAutI D.cT) (fzAutI D.cS) (fzAutI D.cL)) n m = _
  have h1 : (pctx ()).em (actTab (fzAutI D.cT) (fzAutI D.cS) (fzAutI D.cL)) n m =
      (pctx ()).em (actTab (fzAutI D.cT) (fzAutI D.cS) (fzAutI D.cL))
        (fzEIdx (fzEOf n)) (fzEIdx (fzEOf m)) := by
    rw [fzEIdx_fzEOf hn, fzEIdx_fzEOf hm]
  rw [h1, fzEm]

theorem fzrCPar_e_lt (x y : ℕ) (hx : x < 512) (hy : y < 512) :
    (fzrCPar D).e x y < 512 := by
  rw [fzrAux_e_eq D hx hy]
  exact fzEIdx_lt _

theorem fzrCMu_mem (n : ℕ) : fzrCMu D n ∈ T₂ := by
  unfold fzrCMu
  exact D.mu_mem (fzEOf n)

theorem fzrCMu_zero : fzrCMu D 0 = 1 := by
  unfold fzrCMu
  rw [← fzEIdx_one, fzEOf_fzEIdx, D.mu_one]

theorem fzrCMu_mul {n m : ℕ} (hn : n < 512) (hm : m < 512) :
    fzrCMu D ((fzrCPar D).e n m) = fzrCMu D n * fzrCMu D m := by
  unfold fzrCMu
  rw [fzrAux_e_eq D hn hm, fzEOf_fzEIdx, D.mu_mul]

theorem fzrCMu_inj {n m : ℕ} (hn : n < 512) (hm : m < 512) (h : fzrCMu D n = fzrCMu D m) :
    n = m := by
  unfold fzrCMu at h
  have h2 : fzEOf n = fzEOf m := D.mu_injective h
  have h3 := congrArg fzEIdx h2
  rwa [fzEIdx_fzEOf hn, fzEIdx_fzEOf hm] at h3

theorem fzrCMu_surj {g : G} (hg : g ∈ T₂) : ∃ n, n < 512 ∧ fzrCMu D n = g := by
  obtain ⟨x, hx⟩ := D.mu_surj hg
  exact ⟨fzEIdx x, fzEIdx_lt x, by unfold fzrCMu; rw [fzEOf_fzEIdx, hx]⟩

theorem fzrCMu_tI : fzrCMu D 64 = t := by
  unfold fzrCMu Fz319Data.mu
  rw [fzrAux_fzEOf_64]
  simp [ZMod.val_one, ZMod.val_zero]

theorem fzrCMu_sI : fzrCMu D 128 = tau := by
  unfold fzrCMu Fz319Data.mu
  rw [fzrAux_fzEOf_128]
  simp [ZMod.val_one, ZMod.val_zero]

theorem fzrCPar_lt : (fzrCPar D).tI < 512 ∧ (fzrCPar D).sI < 512 ∧
    (∀ g ∈ (fzrCPar D).gens.toList, g < 512) ∧ (∀ x, x < 256 → (fzrCPar D).rhoMap x < 512) := by
  refine ⟨by norm_num [fzrCPar, parOf], by norm_num [fzrCPar, parOf], ?_, ?_⟩
  · intro g hg
    simp only [fzrCPar, parOf] at hg
    fin_cases hg <;> norm_num
  · intro x hx
    have hx64 : x % 64 < 64 := Nat.mod_lt _ (by norm_num)
    have hd : x / 64 < 4 := by omega
    have hrho : rho0 (x % 64) < 64 := fzrAux_rho0_lt hx64
    show (fzrCPar D).rhoMap x < 512
    simp only [fzrCPar, parOf]
    omega

end CFSG.OddStandard.SmallF3.FritzII
