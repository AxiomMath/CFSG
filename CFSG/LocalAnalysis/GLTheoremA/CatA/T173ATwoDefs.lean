module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ADefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172AExistGL

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.S172A.GL (fixSp comSp)

section Two

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

instance linTwoFiniteAut [FiniteDimensional (ZMod 2) V] : Finite (V ≃ₗ[ZMod 2] V) := by
  have : Finite V := Module.finite_of_finite (ZMod 2)
  exact Finite.of_injective (fun g : V ≃ₗ[ZMod 2] V => (g : V → V)) DFunLike.coe_injective

@[expose] def linTwoOddBlock (g : V ≃ₗ[ZMod 2] V) : Subgroup (V ≃ₗ[ZMod 2] V) where
  carrier := {h | (∀ v ∈ fixSp g, h v = v) ∧ ∀ w, w ∈ comSp g ↔ h w ∈ comSp g}
  mul_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    show (∀ v ∈ fixSp g, (a * b) v = v) ∧ ∀ w, w ∈ comSp g ↔ (a * b) w ∈ comSp g
    refine ⟨fun v hv => ?_, fun w => ?_⟩
    · rw [LinearEquiv.mul_apply, hb1 v hv, ha1 v hv]
    · rw [LinearEquiv.mul_apply]
      exact (hb2 w).trans (ha2 (b w))
  one_mem' := by
    show (∀ v ∈ fixSp g, (1 : V ≃ₗ[ZMod 2] V) v = v) ∧
      ∀ w, w ∈ comSp g ↔ (1 : V ≃ₗ[ZMod 2] V) w ∈ comSp g
    exact ⟨fun v _ => rfl, fun w => Iff.rfl⟩
  inv_mem' := by
    rintro a ⟨ha1, ha2⟩
    show (∀ v ∈ fixSp g, a⁻¹ v = v) ∧ ∀ w, w ∈ comSp g ↔ a⁻¹ w ∈ comSp g
    refine ⟨fun v hv => ?_, fun w => ?_⟩
    · have h : a v = v := ha1 v hv
      have h' := LinearEquiv.symm_apply_apply a v
      rw [h] at h'
      exact h'
    · have h1 : a (a⁻¹ w) = w := LinearEquiv.apply_symm_apply a w
      have := ha2 (a⁻¹ w)
      rw [h1] at this
      exact this.symm

@[expose] def LinTwoStdFrame (E : Subgroup (V ≃ₗ[ZMod 2] V)) {r : ℕ} (x : Fin r → V ≃ₗ[ZMod 2] V)
    (P : Fin r → Submodule (ZMod 2) V) (V0 : Submodule (ZMod 2) V) : Prop :=
  E = ⨆ i, Subgroup.zpowers (x i) ∧
  DirectSum.IsInternal (fun o : Option (Fin r) => o.elim V0 P) ∧
  (∀ i, Module.finrank (ZMod 2) (P i) = 2) ∧
  (∀ i, x i ^ 3 = 1) ∧
  (∀ i, comSp (x i) = P i) ∧
  (∀ i, ∀ v ∈ V0, x i v = v) ∧
  (∀ i j, i ≠ j → ∀ v ∈ P j, x i v = v)

end Two

theorem lin_two_params {p : ℕ} (hp : p.Prime) {Ω : Type} [Group Ω] {S B : Subgroup Ω} {d : ℕ}
    {F : Type} [Field F] [Finite F]
    {θ : ↥S ⧸ Subgroup.center ↥S ≃* LargeEvenProj (LargeEvenSLGroup (Fin d) F)}
    (hM : LinMarking p S B 1 d F θ) : Nat.card F = 2 ∧ 3 ≤ d ∧ p = 3 := by
  obtain ⟨hF, -, hd2, hd2', hp3, -⟩ := hM
  refine ⟨by simpa using hF, ?_, ?_⟩
  · by_contra h
    have h2 : d = 2 := by omega
    have := hd2' h2
    omega
  · rcases hp3 with h | ⟨-, h⟩
    · exfalso
      have h1 : p ∣ 1 := by simpa using h
      have := Nat.dvd_one.1 h1
      have := hp.two_le
      omega
    · exact h

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
