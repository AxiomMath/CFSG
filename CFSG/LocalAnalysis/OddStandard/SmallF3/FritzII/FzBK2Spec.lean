module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL319Spec
public import Certificates.Data.FzBU

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open CFSG.GH74.GLS.Bg.TwoGroups CFSG.GH74.GLS.Bg.TwoGroups.L23

@[expose] def fzbDec4 (n : ℕ) : F4c := ⟨((n % 2 : ℕ) : ZMod 2), ((n / 2 % 2 : ℕ) : ZMod 2)⟩

@[expose] def fzbDecB (n : ℕ) : FzUT := ⟨fzbDec4 (n / 16 % 4), fzbDec4 (n / 4 % 4), fzbDec4 (n % 4)⟩

@[expose] def fzbRepD (c : Bool) (i : ℕ) : FzAutD :=
  ⟨fzbDecB ((Certificates.FzBU.repImgs c)[i]!)[0]!,
    fzbDecB ((Certificates.FzBU.repImgs c)[i]!)[1]!,
    fzbDecB ((Certificates.FzBU.repImgs c)[i]!)[2]!,
    fzbDecB ((Certificates.FzBU.repImgs c)[i]!)[3]!⟩

structure FzbAdm (r aq as ay : MulAut FzUT) : Prop where
  r3 : ∀ x, r (r (r x)) = x
  r_fpf : ∀ x, x ≠ 1 → r x ≠ x
  q_r : ∀ x, aq (r x) = r (aq x)
  q4 : ∀ x, aq (aq (aq (aq x))) = x
  q_fix : (Finset.univ.filter fun x : FzUT => aq (aq x) = x).card = 16
  s_r : ∀ x, as (r x) = r (as x)
  s_sq : ∃ k : Fin 4, ∀ x, as (as x) = (aq ^ (k : ℕ)) x
  s_q : (∀ x, as (aq x) = aq (as x)) ∨ (∀ x, as (aq x) = aq (aq (aq (as x))))
  s_inv : ∀ x, aq (aq x) = x → as x * x = 1
  s_Z : ∀ x, FzInZ (as x * x⁻¹)
  y_sq : ∀ x, ay (ay x) = x
  y_r : ∀ x, ay (r x) = r (r (ay x))
  y_q : ∀ x, ay (aq x) = aq (ay x)
  y_s : ∀ x, ay (as x) = as (ay x)

@[expose] def FzbClassSpec : Prop :=
  ∀ r aq as ay : MulAut FzUT, FzbAdm r aq as ay →
    ∃ (c : Bool) (g : MulAut FzUT), (∀ x, g (r x) = fzRho0 (fzRho0 (g x))) ∧
      fzGens (g * aq * g⁻¹) = fzbRepD c 0 ∧ fzGens (g * as * g⁻¹) = fzbRepD c 1 ∧
      fzGens (g * ay * g⁻¹) = fzbRepD c 2 ∧
      (∀ x, as (as x) = x) ∧ (∀ x, as (aq x) = aq (aq (aq (as x))))

end CFSG.OddStandard.SmallF3.FritzII
