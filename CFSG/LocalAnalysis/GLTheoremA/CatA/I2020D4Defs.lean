module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2020Transfer
public import CFSG.HardMathSupport.Lang.D4Three.NormalForm
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Graph.Layer

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2020

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Lang.D4Three
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

@[expose] def NoJTypeComponent (p q : ℕ) {X : Type} [Group X] (β : MulAut X) : Prop :=
  ∀ J : Subgroup X, GLAPComponent p (fixSubgroup β) J → ¬ JType p q J

theorem i2020FixCent_of_noJTypeComponent {p q : ℕ} {X : Type} [Group X] {β : MulAut X}
    (h : NoJTypeComponent p q β) : I2020FixCent p (JType p q) β :=
  fun J hJ hJT => absurd hJT (h J hJ)

theorem noJTypeComponent_inv {p q : ℕ} {X : Type} [Group X] {β : MulAut X}
    (h : NoJTypeComponent p q β) : NoJTypeComponent p q β⁻¹ := by
  intro J hJ
  rw [CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.fixSubgroup_inv_eq] at hJ
  exact h J hJ

theorem noJTypeComponent_congr {p q : ℕ} {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y]
    (hp : p.Prime) (e : X ≃* Y) {β : MulAut X} (h : NoJTypeComponent p q β) :
    NoJTypeComponent p q (MulAut.congr e β) := by
  intro J' hJ' hJT'
  have hfix : (fixSubgroup (MulAut.congr e β)).map e.symm.toMonoidHom = fixSubgroup β := by
    rw [CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroup_congr e β, Subgroup.map_map]
    convert Subgroup.map_id (fixSubgroup β)
    ext x
    simp
  have hker : ∀ y ∈ fixSubgroup (MulAut.congr e β) ⊓ e.symm.toMonoidHom.ker,
      ∀ x ∈ fixSubgroup (MulAut.congr e β), x * y = y * x := by
    intro y hy x _
    have hy1 : y = 1 := e.symm.injective (by
      rw [map_one]
      exact (Subgroup.mem_inf.1 hy).2)
    rw [hy1, mul_one, one_mul]
  have hJ := (CFSG.glaPComponent_map_bijective_of_ker_le_center hp e.symm.toMonoidHom hker).1 J'
    hJ'
  rw [hfix] at hJ
  exact h _ hJ ((jType_map_mulEquiv hp e.symm).1 hJT')

theorem noJTypeComponent_conj {p q : ℕ} {X : Type} [Group X] [Finite X] (hp : p.Prime)
    (ψ : MulAut X) {β : MulAut X} (h : NoJTypeComponent p q β) :
    NoJTypeComponent p q (ψ * β * ψ⁻¹) := by
  have hc : MulAut.congr ψ β = ψ * β * ψ⁻¹ :=
    MulEquiv.ext fun x => by simp [MulAut.congr_apply, MulAut.mul_apply]
  rw [← hc]
  exact noJTypeComponent_congr hp ψ h

section Cert


@[expose] def I2020D4GraphType : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (q f : ℕ), q.Prime → q ≠ 2 → q ≠ 3 → Nat.card K = q ^ f →
    ∀ α : MulAut (adjointGroup Tag.D4 K), α ^ 3 = 1 →
      ∀ (g : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ) (ε : ℕ), ε < 3 → ε ≠ 0 →
        α = MulAut.conj g * (exactNormalAut Tag.D4 K a 1 0 * d4Graph K ε) →
        NoJTypeComponent 3 q α

end Cert

end CFSG.LocalAnalysis.GLTheoremA.I2020

end
