module

public import CFSG.GH74.GLS.Classes
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29TwoNilpDef
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29TwoNilp
import CFSG.GH74.GLS.Stage2.Local.Lemma23e
import CFSG.LieType.HighestRoot.CentChevalleySLThree

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87.L29G3

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS
open CFSG.GH74.GLS.Stage2.Local (sl2_model_center_inv)

theorem sl2_three_center_inv {Y : Type} [Group Y] {L : Subgroup Y}
    (h : HasSL2Model ↥L (fun r => r = 3)) :
    Nat.card (center ↥L) = 2 ∧ ∀ x ∈ L, ∀ y ∈ L, orderOf x = 2 → orderOf y = 2 → x = y :=
  sl2_model_center_inv ⟨1, rfl⟩ h

section Aux

private abbrev SL3 : Type := Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)

private abbrev Q8 : Type := QuaternionGroup 2

private def mA : SL3 := ⟨!![0, -1; 1, 0], by decide⟩

private def mB : SL3 := ⟨!![1, 1; 1, -1], by decide⟩

private def mT : SL3 := ⟨!![1, 1; 0, 1], by decide⟩

private def Fgen {M : Type} [Group M] (P R : M) : Q8 → M
  | .a k => P ^ k.val
  | .xa k => R * P ^ k.val

private def fQ : Q8 →* SL3 where
  toFun := Fgen mA mB
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

private theorem map_Fgen {F M N : Type} [Group M] [Group N] [FunLike F M N] [MonoidHomClass F M N]
    (g : F) (P R : M) (x : Q8) : g (Fgen P R x) = Fgen (g P) (g R) x := by
  cases x with
  | a k => simp [Fgen, map_pow]
  | xa k => simp [Fgen, map_mul, map_pow]

private def Valid {M : Type} [Group M] (A B : M) : Prop :=
  A * A ≠ 1 ∧ A ^ 4 = 1 ∧ B * B = A * A ∧ B * A * B⁻¹ = A⁻¹ ∧ B ≠ A ∧ B ≠ A ^ 3

private instance {M : Type} [Group M] [DecidableEq M] (A B : M) : Decidable (Valid A B) := by
  unfold Valid
  infer_instance

private theorem valid_map {M N : Type} [Group M] [Group N] (g : M →* N)
    (hg : Function.Injective g) (A B : M) : Valid (g A) (g B) ↔ Valid A B := by
  unfold Valid
  have h1 : ∀ x : M, g x = 1 ↔ x = 1 := fun x => by rw [← map_one g]; exact hg.eq_iff
  simp only [ne_eq, ← map_mul, ← map_pow, ← map_inv, h1, hg.eq_iff]

private theorem fQ_inj : ∀ x y : Q8, fQ x = fQ y → x = y := by decide +kernel

private theorem fQ_injective : Function.Injective fQ := fQ_inj

private theorem fQ_surj4 : ∀ g : SL3, g ^ 4 = 1 → ∃ x : Q8, fQ x = g := by decide +kernel

private theorem fQ_a_one : fQ (QuaternionGroup.a 1) = mA := by decide +kernel

private theorem fQ_xa_zero : fQ (QuaternionGroup.xa 0) = mB := by decide +kernel

private theorem T_norm : ∀ x : Q8, ∃ x' : Q8, mT * fQ x * mT⁻¹ = fQ x' := by decide +kernel

private theorem centr_key : ∀ g : SL3, (∀ x : Q8, g * fQ x = fQ x * g) →
    (mT * g) ^ 3 = 1 → g = 1 := by decide +kernel

private theorem decomp : ∀ g : SL3, ∃ x : Q8, ∃ i : Fin 3, g = fQ x * mT ^ (i : ℕ) := by
  decide +kernel

private theorem T_cube : mT ^ 3 = 1 := by decide +kernel

private theorem A_four : mA ^ 4 = 1 := by decide +kernel

private theorem B_four : mB ^ 4 = 1 := by decide +kernel

private theorem valid_AB : Valid mA mB := by decide +kernel

private theorem q8_key : ∀ A₁ B₁ A₂ B₂ : Q8, Valid A₁ B₁ → Valid A₂ B₂ →
    Fgen A₁ B₁ A₁ = QuaternionGroup.a 1 → Fgen A₁ B₁ B₁ = QuaternionGroup.xa 0 →
    ¬ (A₁ = QuaternionGroup.a 1 ∧ B₁ = QuaternionGroup.xa 0) →
    Fgen A₁ B₁ A₂ = Fgen A₂ B₂ A₁ → Fgen A₁ B₁ B₂ = Fgen A₂ B₂ B₁ →
    Fgen A₂ B₂ (Fgen A₂ B₂ (Fgen A₂ B₂ (Fgen A₂ B₂ (QuaternionGroup.a 1)))) =
        QuaternionGroup.a 1 ∧
      Fgen A₂ B₂ (Fgen A₂ B₂ (Fgen A₂ B₂ (Fgen A₂ B₂ (QuaternionGroup.xa 0)))) =
        QuaternionGroup.xa 0 := by
  decide +kernel

private theorem exists_code (α : MulAut SL3) :
    ∃ x y : Q8, fQ x = α mA ∧ fQ y = α mB := by
  obtain ⟨x, hx⟩ := fQ_surj4 (α mA) (by rw [← map_pow, A_four, map_one])
  obtain ⟨y, hy⟩ := fQ_surj4 (α mB) (by rw [← map_pow, B_four, map_one])
  exact ⟨x, y, hx, hy⟩

private theorem apply_fQ (α : MulAut SL3) {x₁ y₁ : Q8} (h1 : fQ x₁ = α mA)
    (h2 : fQ y₁ = α mB) (x : Q8) : α (fQ x) = fQ (Fgen x₁ y₁ x) := by
  have e1 : fQ x = Fgen mA mB x := rfl
  rw [e1, map_Fgen α, ← h1, ← h2]
  exact (map_Fgen fQ x₁ y₁ x).symm

private theorem valid_code (α : MulAut SL3) {x₁ y₁ : Q8} (h1 : fQ x₁ = α mA)
    (h2 : fQ y₁ = α mB) : Valid x₁ y₁ := by
  rw [← valid_map fQ fQ_injective x₁ y₁, h1, h2]
  exact (valid_map α.toMonoidHom α.injective mA mB).2 valid_AB

private theorem eq_one_of_fix (α : MulAut SL3) (hA : α mA = mA) (hB : α mB = mB) : α = 1 := by
  have h1 : ∀ x : Q8, α (fQ x) = fQ x := fun x => by
    have : α (Fgen mA mB x) = Fgen mA mB x := by rw [map_Fgen α, hA, hB]
    exact this
  have hT : ∀ x : Q8, α mT * fQ x * (α mT)⁻¹ = mT * fQ x * mT⁻¹ := by
    intro x
    obtain ⟨x', hx'⟩ := T_norm x
    have h2 : α (mT * fQ x * mT⁻¹) = α (fQ x') := by rw [hx']
    rw [map_mul, map_mul, map_inv, h1, h1] at h2
    rw [h2, hx']
  have hg : ∀ x : Q8, (mT⁻¹ * α mT) * fQ x = fQ x * (mT⁻¹ * α mT) := by
    intro x
    have h3 := hT x
    calc (mT⁻¹ * α mT) * fQ x
        = mT⁻¹ * (α mT * fQ x * (α mT)⁻¹) * α mT := by group
      _ = mT⁻¹ * (mT * fQ x * mT⁻¹) * α mT := by rw [h3]
      _ = fQ x * (mT⁻¹ * α mT) := by group
  have hg1 : mT⁻¹ * α mT = 1 := by
    apply centr_key _ hg
    have : mT * (mT⁻¹ * α mT) = α mT := by group
    rw [this, ← map_pow, T_cube, map_one]
  have hαT : α mT = mT := by
    have := hg1
    rwa [inv_mul_eq_one, eq_comm] at this
  ext g
  obtain ⟨x, i, rfl⟩ := decomp g
  rw [map_mul, map_pow, h1, hαT]
  rfl

private theorem core (φ γ : MulAut SL3) (hφ2 : φ * φ = 1) (hφ1 : φ ≠ 1)
    (hc : γ * φ = φ * γ) : γ ^ 4 = 1 := by
  obtain ⟨x₁, y₁, hx₁, hy₁⟩ := exists_code φ
  obtain ⟨x₂, y₂, hx₂, hy₂⟩ := exists_code γ
  have hv₁ := valid_code φ hx₁ hy₁
  have hv₂ := valid_code γ hx₂ hy₂
  have hφφ : ∀ g, φ (φ g) = g := fun g => by
    have := congrArg (fun ψ : MulAut SL3 => ψ g) hφ2
    simpa using this
  have k1 : Fgen x₁ y₁ x₁ = QuaternionGroup.a 1 := by
    apply fQ_injective
    rw [← apply_fQ φ hx₁ hy₁ x₁, hx₁, hφφ, fQ_a_one]
  have k2 : Fgen x₁ y₁ y₁ = QuaternionGroup.xa 0 := by
    apply fQ_injective
    rw [← apply_fQ φ hx₁ hy₁ y₁, hy₁, hφφ, fQ_xa_zero]
  have k3 : ¬ (x₁ = QuaternionGroup.a 1 ∧ y₁ = QuaternionGroup.xa 0) := by
    rintro ⟨rfl, rfl⟩
    apply hφ1
    apply eq_one_of_fix
    · rw [← hx₁, fQ_a_one]
    · rw [← hy₁, fQ_xa_zero]
  have k4 : Fgen x₁ y₁ x₂ = Fgen x₂ y₂ x₁ := by
    apply fQ_injective
    rw [← apply_fQ φ hx₁ hy₁ x₂, ← apply_fQ γ hx₂ hy₂ x₁, hx₂, hx₁]
    exact (congrArg (fun ψ : MulAut SL3 => ψ mA) hc).symm
  have k5 : Fgen x₁ y₁ y₂ = Fgen x₂ y₂ y₁ := by
    apply fQ_injective
    rw [← apply_fQ φ hx₁ hy₁ y₂, ← apply_fQ γ hx₂ hy₂ y₁, hy₂, hy₁]
    exact (congrArg (fun ψ : MulAut SL3 => ψ mB) hc).symm
  obtain ⟨m1, m2⟩ := q8_key x₁ y₁ x₂ y₂ hv₁ hv₂ k1 k2 k3 k4 k5
  have hγpow : ∀ x : Q8, (γ ^ 4) (fQ x) =
      fQ (Fgen x₂ y₂ (Fgen x₂ y₂ (Fgen x₂ y₂ (Fgen x₂ y₂ x)))) := by
    intro x
    have e : (γ ^ 4) (fQ x) = γ (γ (γ (γ (fQ x)))) := by
      simp [pow_succ, MulAut.mul_apply]
    rw [e, apply_fQ γ hx₂ hy₂, apply_fQ γ hx₂ hy₂, apply_fQ γ hx₂ hy₂, apply_fQ γ hx₂ hy₂]
  apply eq_one_of_fix
  · rw [← fQ_a_one, hγpow, m1]
  · rw [← fQ_xa_zero, hγpow, m2]

private theorem nonempty_mulEquiv_sl3 {Q : Type} [Group Q]
    (h : HasSL2Model Q (fun r => r = 3)) : Nonempty (Q ≃* SL3) := by
  obtain ⟨F, hF, hFin, hq, ⟨e⟩⟩ := h
  have hq' : Nat.card F = 3 := hq
  exact ⟨(e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F).symm).trans
    (CFSG.LieType.HighestRoot.slEquivSL23 hq')⟩

end Aux

theorem twoNilp_centralizer_aut_sl3 {Q : Type} [Group Q] (h : HasSL2Model Q (fun r => r = 3))
    (φ : MulAut Q) (hφ2 : φ * φ = 1) (hφ1 : φ ≠ 1) :
    TwoNilp ↥(centralizer ({φ} : Set (MulAut Q))) := by
  obtain ⟨Φ⟩ := nonempty_mulEquiv_sl3 h
  have hQ : Finite Q := Finite.of_equiv SL3 Φ.symm.toEquiv
  have hMA : Finite (MulAut Q) :=
    Finite.of_injective (MulEquiv.toEquiv : MulAut Q → Equiv.Perm Q) MulEquiv.toEquiv_injective
  have h2 : MulAut.congr Φ φ * MulAut.congr Φ φ = 1 := by rw [← map_mul, hφ2, map_one]
  have h1 : MulAut.congr Φ φ ≠ 1 := fun h' =>
    hφ1 ((MulAut.congr Φ).injective (h'.trans (map_one _).symm))
  apply twoNilp_of_isPGroup
  intro g
  refine ⟨2, ?_⟩
  have hg : φ * (g : MulAut Q) = (g : MulAut Q) * φ :=
    Subgroup.mem_centralizer_iff.mp g.2 φ (Set.mem_singleton φ)
  have h4 := core (MulAut.congr Φ φ) (MulAut.congr Φ g) h2 h1
    (by rw [← map_mul, ← map_mul, hg])
  have h5 : (MulAut.congr Φ) ((g : MulAut Q) ^ 4) = 1 := by rw [map_pow]; exact h4
  have h6 : (g : MulAut Q) ^ 4 = 1 := (MulAut.congr Φ).injective (h5.trans (map_one _).symm)
  refine Subtype.ext ?_
  show (g : MulAut Q) ^ 2 ^ 2 = 1
  exact h6

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87.L29G3
