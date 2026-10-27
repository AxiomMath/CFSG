module

public import CFSG.LieType.ChevTwo.OppCl.Defs
public import CFSG.LieType.BorelTits.OrthogonalSingular
public import CFSG.LieType.BorelTits.Symplectic
public import CFSG.LieType.BorelTits.UnitaryForm
import CFSG.LieType.ChevTwo.OppCl.FormsEASp
import CFSG.LieType.ChevTwo.OppCl.FormsEASU
import CFSG.LieType.ChevTwo.OppCl.FormsEAOmega
import CFSG.LieType.ChevTwo.OppCl.FormsSplitBasic
import CFSG.LieType.ChevTwo.OppCl.FormsSplit
import CFSG.LieType.ChevTwo.OppCl.FormsCases
import CFSG.LieType.ChevTwo.OppCl.Toolkit

public section

namespace CFSG.LieType.ChevTwo.OppCl

open CFSG.Open CFSG.LieType.BorelTits

section FormFamilies

section Avail

variable (r : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2]

theorem ea_Sp :
    EA0 (spForm r F) (fun _ => True) (natRep (StatedSp r F)) ∧
    EA1 (spForm r F) (fun _ => True) (natRep (StatedSp r F)) ∧
    EA2 (spForm r F) (fun _ => True) (natRep (StatedSp r F)) := ea_Sp_aux r F

variable (f : ℕ) (hK : Nat.card F = (2 ^ f) ^ 2) (n : ℕ)

theorem ea_SU :
    EA0 (unitaryForm 2 f hK n) (fun v => (unitaryForm 2 f hK n).β v v = 0)
      (natRep (StatedSU n (2 ^ f) F)) ∧
    EA1 (unitaryForm 2 f hK n) (fun v => (unitaryForm 2 f hK n).β v v = 0)
      (natRep (StatedSU n (2 ^ f) F)) ∧
    EA2 (unitaryForm 2 f hK n) (fun v => (unitaryForm 2 f hK n).β v v = 0)
      (natRep (StatedSU n (2 ^ f) F)) := ea_SU_aux F f hK n

variable {ι : Type} [Fintype ι] [DecidableEq ι] (Φ : QuadForm F (ι → F))

theorem ea_Omega (hι : 5 ≤ Fintype.card ι) :
    EA0 Φ.polar (fun v => Φ.Q v = 0) (natRep (StatedOmega Φ.Q)) ∧
    EA1 Φ.polar (fun v => Φ.Q v = 0) (natRep (StatedOmega Φ.Q)) ∧
    ∀ (h : StatedOmega Φ.Q) (w : ι → F),
      Φ.Q (natRep (StatedOmega Φ.Q) h w - w) = 0 →
        Φ.polar.β w (natRep (StatedOmega Φ.Q) h w - w) = 0 := ea_Omega_aux F Φ hι

end Avail

section Flags

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [Finite V] {H : Type} [Group H]

theorem hflag_iso (Φ : ReflForm F V) (ρ : H →* Module.End F V) :
    ∀ Q : Subgroup H, IsPGroup 2 Q → ∃ (X : ℕ → Submodule F V) (m : ℕ), X 0 = ⊥ ∧ Monotone X ∧
      (∀ k, Φ.IsTotallyIsotropic (X k)) ∧ isoFlag Φ ρ Q = isoCompletion Φ X m := fun Q _ =>
  ⟨isoSeq Φ ρ Q, Module.finrank F V, isoSeq_zero Φ ρ Q, isoSeq_mono Φ ρ Q,
    isoSeq_isTotallyIsotropic Φ ρ Q, rfl⟩

theorem hflag_sing (Φ : QuadForm F V) (ρ : H →* Module.End F V) :
    ∀ Q : Subgroup H, IsPGroup 2 Q → ∃ (X : ℕ → Submodule F V) (m : ℕ), X 0 = ⊥ ∧ Monotone X ∧
      (∀ k, Φ.IsTotallySingular (X k)) ∧ singFlag Φ ρ Q = isoCompletion Φ.polar X m := fun Q _ =>
  ⟨singSeq Φ ρ Q, Module.finrank F V, singSeq_zero Φ ρ Q, singSeq_mono Φ ρ Q,
    isTotallySingular_singSeq Φ ρ Q, rfl⟩

end Flags

section Raise

variable (F : Type) [Field F] [Finite F] [CharP F 2] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)

include hp2

theorem raise_Sp (r : ℕ) :
    RaiseProp (SemiIso (spForm r F)) (natRep (StatedSp r F))
      (fun Q => isoFlag (spForm r F) (natRep (StatedSp r F)) Q) p := by
  obtain ⟨hE0, hE1, hE2⟩ := ea_Sp r F
  have hsymm : ∀ u v, (spForm r F).β v u = (spForm r F).σ ((spForm r F).β u v) := fun u v =>
    ((spForm r F).β_swap_of_alt (spForm_self r F) u v).trans (CharTwo.neg_eq _)
  exact raise_form (spForm r F) (fun _ => True) (spForm r F).IsTotallyIsotropic
    (natRep (StatedSp r F)) p (SemiIso (spForm r F)) (fun g h => h) (fun c => rfl) hsymm
    (fun v _ => spForm_self r F v) (fun U hU => hU) (fun U _ v _ => trivial)
    (isIsometric_natRep_statedSp r F) (natRep_injective _) hE0 hE1 (Or.inl hE2)
    (fun Rh hs hP hR W hW hWinv => split_refl (spForm r F) p Rh (fun c => rfl) hsymm
      (fun v => ⟨0, by rw [map_zero, add_zero, spForm_self]⟩) hp2 hs hP hR W hW hWinv)
    (fun Q => isoFlag (spForm r F) (natRep (StatedSp r F)) Q)
    (hflag_iso (spForm r F) (natRep (StatedSp r F)))
    (fun Q _ g hg hΦ h1 h2 => isoFlag_inv (spForm r F) (natRep (StatedSp r F))
      (isIsometric_natRep_statedSp r F) g hg hΦ Q h1 h2) hp2

theorem raise_SU (f : ℕ) (hK : Nat.card F = (2 ^ f) ^ 2) (n : ℕ) :
    RaiseProp (SemiIso (unitaryForm 2 f hK n)) (natRep (StatedSU n (2 ^ f) F))
      (fun Q => isoFlag (unitaryForm 2 f hK n) (natRep (StatedSU n (2 ^ f) F)) Q) p := by
  obtain ⟨hE0, hE1, hE2⟩ := ea_SU F f hK n
  have hdiag : ∀ v, ∃ t, t + (unitaryForm 2 f hK n).σ t = (unitaryForm 2 f hK n).β v v := fun v =>
    exists_add_unitaryInvolution_eq hK (unitaryForm_symm hK v v).symm
  exact raise_form (unitaryForm 2 f hK n) (fun v => (unitaryForm 2 f hK n).β v v = 0)
    (unitaryForm 2 f hK n).IsTotallyIsotropic (natRep (StatedSU n (2 ^ f) F)) p
    (SemiIso (unitaryForm 2 f hK n)) (fun g h => h) (fun c => unitaryInvolution_involutive hK c)
    (fun u v => unitaryForm_symm hK u v) (fun v hv => hv) (fun U hU => hU)
    (fun U hU v hv => hU hv v hv) (isIsometric_natRep_statedSU hK n) (natRep_injective _) hE0 hE1
    (Or.inl hE2)
    (fun Rh hs hP hR W hW hWinv => split_refl (unitaryForm 2 f hK n) p Rh
      (fun c => unitaryInvolution_involutive hK c) (fun u v => unitaryForm_symm hK u v) hdiag hp2
      hs hP hR W hW hWinv)
    (fun Q => isoFlag (unitaryForm 2 f hK n) (natRep (StatedSU n (2 ^ f) F)) Q)
    (hflag_iso (unitaryForm 2 f hK n) (natRep (StatedSU n (2 ^ f) F)))
    (fun Q _ g hg hΦ h1 h2 => isoFlag_inv (unitaryForm 2 f hK n)
      (natRep (StatedSU n (2 ^ f) F)) (isIsometric_natRep_statedSU hK n) g hg hΦ Q h1 h2) hp2

theorem raise_Omega_aux {ι : Type} [Fintype ι] [DecidableEq ι] (Φ : QuadForm F (ι → F))
    (hι : 5 ≤ Fintype.card ι) :
    RaiseProp (SemiIsoQ Φ) (natRep (StatedOmega Φ.Q))
      (fun Q => singFlag Φ (natRep (StatedOmega Φ.Q)) Q) p := by
  obtain ⟨hE0, hE1, hE2⟩ := ea_Omega F Φ hι
  have hQ : ∀ (h : StatedOmega Φ.Q) (v : ι → F), Φ.Q (natRep (StatedOmega Φ.Q) h v) = Φ.Q v :=
    fun h v => by
      rw [natRep_apply]
      exact orthGroup_preserves Φ.Q (statedOmega_le_orthGroup Φ.Q h.2) v
  have hsymm : ∀ u v, Φ.polar.β v u = Φ.polar.σ (Φ.polar.β u v) := fun u v => by
    rw [Φ.polar_σ]
    exact Φ.polar_symm v u
  have h := raise_form Φ.polar (fun v => Φ.Q v = 0) Φ.IsTotallySingular
    (natRep (StatedOmega Φ.Q)) p (fun g => g ∈ semilinGroup F (ι → F) ∧ SemiIsoQ Φ g)
    (fun g hg => FS.semiIso_polar Φ hg.1 hg.2) (fun c => by rw [Φ.polar_σ]; rfl) hsymm
    (fun v hv => by rw [Φ.polar_self, hv, mul_zero]) (fun U hU => hU.isTotallyIsotropic)
    (fun U hU v hv => hU v hv) (isIsometric_natRep_statedOmega Φ) (natRep_injective _) hE0 hE1
    (Or.inr fun h w hw => hE2 h w hw)
    (fun Rh hs hP hR W hW hWinv => split_quad p Rh Φ hp2 hs (fun g hg => (hP g hg).2) hR W hW
      hWinv)
    (fun Q => singFlag Φ (natRep (StatedOmega Φ.Q)) Q) (hflag_sing Φ (natRep (StatedOmega Φ.Q)))
    (fun Q _ g hg hΦ h1 h2 => singFlag_inv Φ (natRep (StatedOmega Φ.Q)) hQ g hΦ.1 hΦ.2 Q h1 h2)
    hp2
  intro Rh hs hP hR hN Q hQ2 hNQ x hx hx1 hxc
  exact h Rh hs (fun g hg => ⟨hs hg, hP g hg⟩) hR hN Q hQ2 hNQ x hx hx1 hxc

theorem raise_OmegaPlus (n : ℕ) (hn : 3 ≤ n) :
    RaiseProp (SemiIsoQ (quadPlusForm n F)) (natRep (StatedOmega (StatedQuadPlus n F)))
      (fun Q => singFlag (quadPlusForm n F) (natRep (StatedOmega (StatedQuadPlus n F))) Q) p :=
  raise_Omega_aux F p hp2 (quadPlusForm n F) (by rw [Fintype.card_sum, Fintype.card_fin]; omega)

theorem raise_OmegaMinus (n : ℕ) (hn : 3 ≤ n) (b c : F) (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    RaiseProp (SemiIsoQ (quadMinusForm n F b c hirr))
      (natRep (StatedOmega (StatedQuadMinus n F b c)))
      (fun Q => singFlag (quadMinusForm n F b c hirr)
        (natRep (StatedOmega (StatedQuadMinus n F b c))) Q) p :=
  raise_Omega_aux F p hp2 (quadMinusForm n F b c hirr)
    (by simp only [Fintype.card_sum, Fintype.card_fin]; omega)

end Raise

end FormFamilies

end CFSG.LieType.ChevTwo.OppCl
