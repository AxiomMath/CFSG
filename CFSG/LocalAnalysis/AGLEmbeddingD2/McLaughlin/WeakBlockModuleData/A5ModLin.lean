module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.A5ModF4
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.A5ModOrbit

@[expose] public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.A5Mod

open Matrix

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [DistribMulAction A5 W]
  [SMulCommClass A5 (ZMod 2) W]

theorem lin_case [Finite W] (ω : W →ₗ[ZMod 2] W) (hcomm : ∀ (g : A5) (w : W), ω (g • w) = g • ω w)
    (hω : ∀ w : W, ω (ω w) + ω w + w = 0) (hcard : Nat.card W = 16)
    (hact : ∃ (g : A5) (w : W), g • w ≠ w) :
    ∃ (e : W ≃+ (Fin 2 → F4)) (α₂ : A5 →* SpecialLinearGroup (Fin 2) F4),
      Function.Injective α₂ ∧ Function.Surjective α₂ ∧
      ∀ (g : A5) (w : W), e (g • w) = (α₂ g : Matrix (Fin 2) (Fin 2) F4).mulVec (e w) := by
  classical
  have h2 : ∀ w : W, w + w = 0 := add_self_eq_zero'
  letI : Module F4 W := modF4 ω.toAddMonoidHom h2 hω
  have hsm : ∀ (g : A5) (x : F4) (v : W), g • (x • v) = x • (g • v) := by
    intro g x v
    cases x
    · show g • (0 : W) = 0
      exact smul_zero g
    · rfl
    · show g • ω v = ω (g • v)
      exact (hcomm g v).symm
    · show g • (ω v + v) = ω (g • v) + g • v
      rw [smul_add, hcomm]
  let tl : A5 → (W →ₗ[F4] W) := fun g =>
    { toFun := fun v => g • v
      map_add' := fun v v' => smul_add g v v'
      map_smul' := fun x v => by simp only [RingHom.id_apply]; exact hsm g x v }
  have hfin : Module.Finite F4 W := Module.Finite.of_finite
  have hrank : Module.finrank F4 W = 2 := by
    have h := Module.natCard_eq_pow_finrank (K := F4) (V := W)
    rw [hcard, F4.card_F4] at h
    have h16 : (4 : ℕ) ^ Module.finrank F4 W = 4 ^ 2 := by rw [← h]; norm_num
    exact Nat.pow_right_injective (by norm_num) h16
  let b := Module.finBasisOfFinrankEq F4 W hrank
  let α₁ : A5 →* (W →ₗ[F4] W) :=
    { toFun := tl
      map_one' := by ext v; simp [tl]
      map_mul' := fun g h => by ext v; simp [tl, mul_smul] }
  let α₁' : A5 →* Matrix (Fin 2) (Fin 2) F4 :=
    ((LinearMap.toMatrixAlgEquiv b : (W →ₗ[F4] W) →* Matrix (Fin 2) (Fin 2) F4)).comp α₁
  let δ : A5 →* F4ˣ := MonoidHom.toHomUnits (Matrix.detMonoidHom.comp α₁')
  have htop : commutator A5 = ⊤ := commutator_alternatingGroup_eq_top (by simp)
  have hdet : ∀ g, (α₁' g).det = 1 := by
    intro g
    have hg : g ∈ δ.ker := Abelianization.commutator_subset_ker δ (htop ▸ Subgroup.mem_top g)
    have h1 : δ g = 1 := hg
    have h2' := congrArg (fun u : F4ˣ => (u : F4)) h1
    simpa [δ] using h2'
  let α₂ : A5 →* SpecialLinearGroup (Fin 2) F4 :=
    { toFun := fun g => ⟨α₁' g, hdet g⟩
      map_one' := Subtype.ext (map_one α₁')
      map_mul' := fun g h => Subtype.ext (map_mul α₁' g h) }
  have hequi : ∀ (g : A5) (w : W), b.equivFun (g • w) = (α₁' g).mulVec (b.equivFun w) := by
    intro g w
    exact (LinearMap.toMatrix_mulVec_repr b b (tl g) w).symm
  have hinj : Function.Injective α₂ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal α₂.ker with h | h
    · exact h
    · exfalso
      obtain ⟨g, w, hgw⟩ := hact
      apply hgw
      have hg : g ∈ α₂.ker := by rw [h]; exact Subgroup.mem_top g
      have h1 : α₂ g = 1 := hg
      have h2' : α₁' g = 1 := congrArg Subtype.val h1
      apply b.equivFun.injective
      rw [hequi, h2', Matrix.one_mulVec]
  refine ⟨b.equivFun.toAddEquiv, α₂, hinj, ?_, fun g w => hequi g w⟩
  have hcardSL : Nat.card (SpecialLinearGroup (Fin 2) F4) = 60 := by
    have hq : Fintype.card F4 = 4 := rfl
    rw [Matrix.card_SL_field, hq]
    decide
  have hcardA : Nat.card A5 = 60 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  exact (hinj.bijective_of_nat_card_le (by rw [hcardSL, hcardA])).2

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.A5Mod
