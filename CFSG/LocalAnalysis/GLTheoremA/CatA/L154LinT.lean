module

public import CFSG.LieType.SemisimpleCentralizers.HeldLang
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

open CFSG.Open CFSG.LieType.SemisimpleCentralizers.HeldLang
open scoped commutatorElement MatrixGroups

theorem hom_eq_one_of_perfect_of_commute {G A : Type*} [Group G] [Group A] (hG : commutator G = ⊤)
    (f : G →* A) (hc : ∀ a b : G, Commute (f a) (f b)) (g : G) : f g = 1 := by
  have hle : commutator G ≤ f.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact (hc a b).eq
  have hg : g ∈ commutator G := by
    rw [hG]
    exact Subgroup.mem_top g
  exact MonoidHom.mem_ker.1 (hle hg)

theorem hom_of_displacement {G H : Type*} [Group G] [Group H] (hG : commutator G = ⊤)
    (γ κ : G →* H) (Sc : H → Prop) (hScS : ∀ v v', Sc v → Sc v' → v * v' = v' * v)
    (hScκ : ∀ v, Sc v → ∀ g : G, v * κ g = κ g * v) (hw : ∀ g, Sc (γ g * (κ g)⁻¹)) (g : G) :
    γ g = κ g := by
  let wf : G →* H :=
    { toFun := fun g => γ g * (κ g)⁻¹
      map_one' := by simp
      map_mul' := by
        intro a b
        have h1 : (γ b * (κ b)⁻¹) * (κ a)⁻¹ = (κ a)⁻¹ * (γ b * (κ b)⁻¹) := by
          have := hScκ _ (hw b) a⁻¹
          rwa [map_inv] at this
        calc γ (a * b) * (κ (a * b))⁻¹
            = γ a * ((γ b * (κ b)⁻¹) * (κ a)⁻¹) := by rw [map_mul, map_mul]; group
          _ = γ a * ((κ a)⁻¹ * (γ b * (κ b)⁻¹)) := by rw [h1]
          _ = (γ a * (κ a)⁻¹) * (γ b * (κ b)⁻¹) := by group }
  have h1 := hom_eq_one_of_perfect_of_commute hG wf (fun a b => hScS _ _ (hw a) (hw b)) g
  have h2 : γ g * (κ g)⁻¹ = 1 := h1
  exact mul_inv_eq_one.1 h2

section

variable {F D₁ : Type} [Field F] [Field D₁] {d d₁ : ℕ}

theorem no_inner_of_transvections
    (ι : GL (Fin d₁) D₁ →* GL (Fin d) F)
    (hperf : commutator ↥(StatedSL d₁ D₁) = ⊤)
    (σ : F ≃+* F) (hσ : σ ≠ 1) (B : GL (Fin d) F) (P : GL (Fin d₁) D₁)
    (E : Matrix (Fin d) (Fin d) F) (hE : E ≠ 0)
    (hT : ∀ c : F, ∃ t ∈ StatedSL d₁ D₁,
      ((ι t : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) = 1 + c • E)
    (h : ∀ m ∈ StatedSL d₁ D₁, ∃ (z : Fˣ) (z' : D₁ˣ),
      Matrix.GeneralLinearGroup.scalar (Fin d) z * (B * glMap σ (ι m) * B⁻¹) =
        ι (Matrix.GeneralLinearGroup.scalar (Fin d₁) z' * (P * m * P⁻¹))) : False := by
  classical
  set Q : GL (Fin d) F := ι P with hQdef
  let γ₀ : ↥(StatedSL d₁ D₁) →* GL (Fin d) F :=
    ((MulAut.conj B).toMonoidHom.comp (glMap σ)).comp (ι.comp (StatedSL d₁ D₁).subtype)
  let κ₀ : ↥(StatedSL d₁ D₁) →* GL (Fin d) F :=
    (MulAut.conj Q).toMonoidHom.comp (ι.comp (StatedSL d₁ D₁).subtype)
  have hγ₀ : ∀ m : ↥(StatedSL d₁ D₁), γ₀ m = B * glMap σ (ι (m : GL (Fin d₁) D₁)) * B⁻¹ := fun m => rfl
  have hκ₀ : ∀ m : ↥(StatedSL d₁ D₁), κ₀ m = ι (P * (m : GL (Fin d₁) D₁) * P⁻¹) := by
    intro m
    show Q * ι (m : GL (Fin d₁) D₁) * Q⁻¹ = _
    rw [map_mul, map_mul, map_inv]
  let Sc : GL (Fin d) F → Prop := fun v =>
    ∃ (z : Fˣ) (z' : D₁ˣ), v = Matrix.GeneralLinearGroup.scalar (Fin d) z *
      ι (Matrix.GeneralLinearGroup.scalar (Fin d₁) z')
  have hScg : ∀ v, Sc v → ∀ g : GL (Fin d₁) D₁, v * ι g = ι g * v := by
    rintro v ⟨z, z', rfl⟩ g
    have h1 := scalar_mul_comm z (ι g)
    have h2 : ι (Matrix.GeneralLinearGroup.scalar (Fin d₁) z') * ι g =
        ι g * ι (Matrix.GeneralLinearGroup.scalar (Fin d₁) z') := by
      rw [← map_mul, ← map_mul, scalar_mul_comm z' g]
    calc Matrix.GeneralLinearGroup.scalar (Fin d) z * ι (Matrix.GeneralLinearGroup.scalar (Fin d₁) z') * ι g
        = Matrix.GeneralLinearGroup.scalar (Fin d) z * (ι g *
            ι (Matrix.GeneralLinearGroup.scalar (Fin d₁) z')) := by rw [mul_assoc, h2]
      _ = (Matrix.GeneralLinearGroup.scalar (Fin d) z * ι g) *
            ι (Matrix.GeneralLinearGroup.scalar (Fin d₁) z') := by rw [mul_assoc]
      _ = ι g * Matrix.GeneralLinearGroup.scalar (Fin d) z *
            ι (Matrix.GeneralLinearGroup.scalar (Fin d₁) z') := by rw [h1]
      _ = ι g * (Matrix.GeneralLinearGroup.scalar (Fin d) z *
            ι (Matrix.GeneralLinearGroup.scalar (Fin d₁) z')) := by rw [mul_assoc]
  have hScS : ∀ v v', Sc v → Sc v' → v * v' = v' * v := by
    intro v v' hv hv'
    obtain ⟨z, z', rfl⟩ := hv'
    have h1 := hScg v hv (Matrix.GeneralLinearGroup.scalar (Fin d₁) z')
    have h2 := scalar_mul_comm z v
    calc v * (Matrix.GeneralLinearGroup.scalar (Fin d) z *
          ι (Matrix.GeneralLinearGroup.scalar (Fin d₁) z'))
        = (v * Matrix.GeneralLinearGroup.scalar (Fin d) z) *
          ι (Matrix.GeneralLinearGroup.scalar (Fin d₁) z') := by rw [mul_assoc]
      _ = (Matrix.GeneralLinearGroup.scalar (Fin d) z * v) *
          ι (Matrix.GeneralLinearGroup.scalar (Fin d₁) z') := by rw [← h2]
      _ = Matrix.GeneralLinearGroup.scalar (Fin d) z * (v *
          ι (Matrix.GeneralLinearGroup.scalar (Fin d₁) z')) := by rw [mul_assoc]
      _ = Matrix.GeneralLinearGroup.scalar (Fin d) z * (
          ι (Matrix.GeneralLinearGroup.scalar (Fin d₁) z') * v) := by rw [h1]
      _ = (Matrix.GeneralLinearGroup.scalar (Fin d) z *
          ι (Matrix.GeneralLinearGroup.scalar (Fin d₁) z')) * v := by rw [mul_assoc]
  have hScκ : ∀ v, Sc v → ∀ g : ↥(StatedSL d₁ D₁), v * κ₀ g = κ₀ g * v := by
    intro v hv g
    rw [hκ₀]
    exact hScg v hv _
  have hw : ∀ m : ↥(StatedSL d₁ D₁), Sc (γ₀ m * (κ₀ m)⁻¹) := by
    intro m
    obtain ⟨z, z', hzz⟩ := h (m : GL (Fin d₁) D₁) m.2
    refine ⟨z⁻¹, z', ?_⟩
    have h1 : γ₀ m = (Matrix.GeneralLinearGroup.scalar (Fin d) z)⁻¹ *
        (ι (Matrix.GeneralLinearGroup.scalar (Fin d₁) z') * κ₀ m) := by
      rw [hγ₀, eq_inv_mul_iff_mul_eq, hzz, map_mul, hκ₀]
    rw [h1, map_inv]
    group
  have hperf' : commutator ↥(StatedSL d₁ D₁) = ⊤ := hperf
  have hγκ : ∀ m : ↥(StatedSL d₁ D₁), γ₀ m = κ₀ m :=
    hom_of_displacement hperf' γ₀ κ₀ Sc hScS hScκ hw
  have hBB : (B : Matrix (Fin d) (Fin d) F) * ((B⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hQQ : (Q : Matrix (Fin d) (Fin d) F) * ((Q⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hQQ' : ((Q⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) * (Q : Matrix (Fin d) (Fin d) F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  set X : Matrix (Fin d) (Fin d) F := (B : Matrix (Fin d) (Fin d) F) * E.map σ *
    ((B⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) with hX
  set Y : Matrix (Fin d) (Fin d) F := (Q : Matrix (Fin d) (Fin d) F) * E *
    ((Q⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) with hY
  have hmat : ∀ c : F, σ c • X = c • Y := by
    intro c
    obtain ⟨t, ht, hιt⟩ := hT c
    have h1 := hγκ ⟨t, ht⟩
    have h2 : ((B * glMap σ (ι t) * B⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) =
        ((Q * ι t * Q⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) := by
      have := congrArg (fun g : GL (Fin d) F => (g : Matrix (Fin d) (Fin d) F)) h1
      exact this
    have hγt : ((B * glMap σ (ι t) * B⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) = 1 + σ c • X := by
      have e1 : ((glMap σ (ι t) : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) = 1 + σ c • E.map σ := by
        rw [coe_glMap, hιt]
        ext i j
        simp [Matrix.one_apply, apply_ite σ]
      rw [Units.val_mul, Units.val_mul, e1, hX, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hBB,
        Matrix.mul_smul, Matrix.smul_mul]
    have hκt : ((Q * ι t * Q⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) = 1 + c • Y := by
      rw [Units.val_mul, Units.val_mul, hιt, hY, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hQQ,
        Matrix.mul_smul, Matrix.smul_mul]
    rw [hγt, hκt] at h2
    exact add_left_cancel h2
  have hXY : X = Y := by
    have := hmat 1
    rwa [map_one, one_smul, one_smul] at this
  have hY0 : Y ≠ 0 := by
    intro h0
    apply hE
    have : ((Q⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) * Y * (Q : Matrix (Fin d) (Fin d) F) = E := by
      have e : ((Q⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) * ((Q : Matrix (Fin d) (Fin d) F) * E *
          ((Q⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F)) * (Q : Matrix (Fin d) (Fin d) F) =
          (((Q⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) * (Q : Matrix (Fin d) (Fin d) F)) * E *
          (((Q⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) * (Q : Matrix (Fin d) (Fin d) F)) := by
        simp only [Matrix.mul_assoc]
      rw [hY, e, hQQ', Matrix.one_mul, Matrix.mul_one]
    rw [← this, h0, Matrix.mul_zero, Matrix.zero_mul]
  apply hσ
  ext c
  have h1 := hmat c
  rw [hXY] at h1
  have h2 : (σ c - c) • Y = 0 := by rw [sub_smul, h1, sub_self]
  rcases smul_eq_zero.1 h2 with h3 | h3
  · exact sub_eq_zero.1 h3
  · exact absurd h3 hY0

end

end CFSG.LocalAnalysis.GLTheoremA.K155X
