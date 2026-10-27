module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoBaumO1
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15GNOffenderContext
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoB2Offender
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoB2OneFactor
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15SeriesKernel
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoB2Parity

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open
open CFSG.Quasithin
open CFSG.RankThree.FFModules
open CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open CFSG.Quasithin.B42Sp4 (spM)
open Polynomial

private theorem finrank_ker_aeval_eq_kerDim {G W : Type} [Group G] [AddCommGroup W]
    [Module (ZMod 2) W] (ρ : Representation (ZMod 2) G W) (f : (ZMod 2)[X]) (x : G) :
    Module.finrank (ZMod 2) (LinearMap.ker (Polynomial.aeval (ρ x) f)) =
      kerDim ρ f x ⊤ := by
  unfold kerDim
  rw [top_inf_eq]

private theorem one_add_one_end {W : Type} [AddCommGroup W] [Module (ZMod 2) W] :
    (1 + 1 : Module.End (ZMod 2) W) = 0 := by
  rw [← two_smul (ZMod 2) (1 : Module.End (ZMod 2) W), show (2 : ZMod 2) = 0 from rfl,
    zero_smul]

private theorem cyclo3_mul_linear :
    (Polynomial.X ^ 2 + Polynomial.X + 1) * (Polynomial.X + 1) =
      (Polynomial.X ^ 3 + 1 : (ZMod 2)[X]) := by
  have h2 : (2 : (ZMod 2)[X]) = 0 := CharP.cast_eq_zero _ 2
  ring_nf
  rw [h2]
  simp

private theorem cyclo3_coprime :
    IsCoprime (Polynomial.X ^ 2 + Polynomial.X + 1 : (ZMod 2)[X]) (Polynomial.X + 1) :=
  ⟨1, -Polynomial.X, by ring⟩

private theorem cyclo3_eval_one_ne_zero :
    (Polynomial.X ^ 2 + Polynomial.X + 1 : (ZMod 2)[X]).eval 1 ≠ 0 := by
  simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
  decide

private theorem mulAut_congr_apply_apply {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (f : MulAut A) (y : A) : (MulAut.congr e f) (e y) = e (f y) := by
  simp [MulAut.congr_apply]

theorem k543DynkinB2 : K543DynkinB2 := by
  intro X _ _ T hGN Ls hL hJ n hn e s
  have hV : IsElemAbelian 2 (gnV T) := isElemAbelian_gnV T hGN
  let : Module (ZMod 2) (Additive (IntMod (gnV T) hV)) :=
    binModule (fun v : IntMod (gnV T) hV => IntMod.sq_eq_one v)
  have hF : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  obtain ⟨B, hBJ, hB2, hBc, hBN, hinvB, hLnt, hBnt, hbestB, hquadB, hmove⟩ :=
    exists_strictMin_offender_of_gn_component hGN hV hL hJ
  have hinn : ∀ b ∈ B, ∃ l ∈ Ls, ConjAgree Ls b l :=
    strictMin_inner_sp4 (gnRep hV) Ls B hn hF e hL.2.2 hBN hB2 hBc hinvB hLnt hbestB hquadB hmove
  obtain ⟨r, Vs, i₀, α, φ, hcomp, htriv, hnat⟩ :=
    exists_series_natural_factor_sp4 (gnRep hV) Ls B hn hF e hL.2.2.1 hL.2.2.2 hB2 hBc hinn
      (U := commOn (gnRep hV) Ls ⊤) le_rfl hinvB hbestB hmove hBnt
  obtain ⟨x₀, hx₀3, hx₀⟩ :=
    exists_order_three_conjSp_mul_fieldSp (F := GaloisField 2 n) (by omega) hF
  let ρ := gnRep hV
  let ρ' := ρ.comp Ls.subtype
  let β : MulAut (StatedSp 2 (GaloisField 2 n)) :=
    MulAut.congr e (Ls.normalizerMonoidHom s)
  let ℓ₀ : ↥Ls := e.symm x₀
  have heℓ₀ : e ℓ₀ = x₀ := e.apply_symm_apply x₀
  let ℓ₁ : ↥Ls := (Ls.normalizerMonoidHom s) ℓ₀
  have heℓ₁ : e ℓ₁ = β x₀ := by
    have h1 : e ℓ₁ = e ((Ls.normalizerMonoidHom s) ℓ₀) := rfl
    rw [h1, show x₀ = e ℓ₀ from heℓ₀.symm]
    exact (mulAut_congr_apply_apply e (Ls.normalizerMonoidHom s) ℓ₀).symm
  have hℓ₀3 : ℓ₀ ^ 3 = 1 := by
    show (e.symm x₀) ^ 3 = 1
    rw [← map_pow e.symm x₀ 3, hx₀3, map_one]
  have hℓ₁3 : ℓ₁ ^ 3 = 1 := by
    show ((Ls.normalizerMonoidHom s) ℓ₀) ^ 3 = 1
    rw [← map_pow (Ls.normalizerMonoidHom s) ℓ₀ 3, hℓ₀3, map_one]
  have hfh : ∀ ℓ : ↥Ls, ℓ ^ 3 = 1 →
      Polynomial.aeval (ρ' ℓ)
        (((Polynomial.X ^ 2 + Polynomial.X + 1) * (Polynomial.X + 1)) :
          (ZMod 2)[X]) = 0 := by
    intro ℓ hℓ3
    rw [cyclo3_mul_linear, map_add, map_pow, Polynomial.aeval_X, map_one]
    have hT3 : (ρ' ℓ) ^ 3 = 1 := by
      rw [← map_pow ρ' ℓ 3, hℓ3, map_one]
    rw [hT3]
    exact one_add_one_end
  have hker_factor : ∀ ℓ : ↥Ls, ℓ ^ 3 = 1 →
      Module.finrank (ZMod 2)
          (LinearMap.ker (Polynomial.aeval (ρ' ℓ)
            (Polynomial.X ^ 2 + Polynomial.X + 1 : (ZMod 2)[X]))) =
        Module.finrank (ZMod 2)
          (LinearMap.ker (Polynomial.aeval
            (factorRep (Vs i₀.castSucc) (Vs i₀.succ) ℓ)
            (Polynomial.X ^ 2 + Polynomial.X + 1 : (ZMod 2)[X]))) := by
    intro ℓ hℓ3
    exact finrank_ker_aeval_eq_factor_of_trivial hcomp cyclo3_coprime (hfh ℓ hℓ3)
      cyclo3_eval_one_ne_zero i₀ (fun i hi => htriv i hi ℓ)
  have hbridge : ∀ ℓ : ↥Ls, ℓ ^ 3 = 1 →
      stspKerCard (α (e ℓ)) =
        2 ^ Module.finrank (ZMod 2)
          (LinearMap.ker (Polynomial.aeval (ρ' ℓ)
            (Polynomial.X ^ 2 + Polynomial.X + 1 : (ZMod 2)[X]))) := by
    intro ℓ hℓ3
    have hφ : ∀ x : ↥(Vs i₀.succ).toSubmodule ⧸
          factorSub (Vs i₀.castSucc) (Vs i₀.succ),
        φ ((factorRep (Vs i₀.castSucc) (Vs i₀.succ) ℓ) x) =
          (spM (α (e ℓ))).mulVec (φ x) := by
      intro x
      have h1 := hnat (e ℓ) x
      rwa [e.symm_apply_apply ℓ] at h1
    have hb := two_pow_finrank_ker_aeval_cyclo3_eq φ
      (factorRep (Vs i₀.castSucc) (Vs i₀.succ) ℓ) (α (e ℓ)) hφ
    rw [← hb, hker_factor ℓ hℓ3]
  have hconj : ((ℓ₁ : ↥Ls) : X ⧸ gnC T) =
      (s : X ⧸ gnC T) * (ℓ₀ : X ⧸ gnC T) * (s : X ⧸ gnC T)⁻¹ := by
    show (((Ls.normalizerMonoidHom s) ℓ₀ : ↥Ls) : X ⧸ gnC T) = _
    exact Subgroup.normalizerMonoidHom_apply_apply_coe Ls s ℓ₀
  have hρℓ₀ : ρ' ℓ₀ = ρ (ℓ₀ : X ⧸ gnC T) := rfl
  have hρℓ₁ : ρ' ℓ₁ =
      ρ ((s : X ⧸ gnC T) * (ℓ₀ : X ⧸ gnC T) * (s : X ⧸ gnC T)⁻¹) := by
    change ρ ((ℓ₁ : X ⧸ gnC T)) =
      ρ ((s : X ⧸ gnC T) * (ℓ₀ : X ⧸ gnC T) * (s : X ⧸ gnC T)⁻¹)
    rw [hconj]
  have hker_eq : Module.finrank (ZMod 2)
        (LinearMap.ker (Polynomial.aeval (ρ' ℓ₁)
          (Polynomial.X ^ 2 + Polynomial.X + 1 : (ZMod 2)[X]))) =
      Module.finrank (ZMod 2)
        (LinearMap.ker (Polynomial.aeval (ρ' ℓ₀)
          (Polynomial.X ^ 2 + Polynomial.X + 1 : (ZMod 2)[X]))) := by
    rw [hρℓ₁, hρℓ₀]
    rw [finrank_ker_aeval_eq_kerDim ρ (Polynomial.X ^ 2 + Polynomial.X + 1 : (ZMod 2)[X])
          ((s : X ⧸ gnC T) * (ℓ₀ : X ⧸ gnC T) * (s : X ⧸ gnC T)⁻¹),
        finrank_ker_aeval_eq_kerDim ρ (Polynomial.X ^ 2 + Polynomial.X + 1 : (ZMod 2)[X])
          (ℓ₀ : X ⧸ gnC T)]
    exact kerDim_conj ρ (Polynomial.X ^ 2 + Polynomial.X + 1 : (ZMod 2)[X]) (ℓ₀ : X ⧸ gnC T)
      (s : X ⧸ gnC T) ⊤ (fun _ _ => Submodule.mem_top) (fun _ _ => Submodule.mem_top)
  have hx₀' : stspKerCard (α (β x₀)) = stspKerCard (α x₀) := by
    rw [← heℓ₁, ← heℓ₀, hbridge ℓ₁ hℓ₁3, hbridge ℓ₀ hℓ₀3, hker_eq]
  exact hx₀ α β hx₀'

end CFSG.LocalAnalysis.RankThreeUC.S15

end
