module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutEngineGen

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Fin76b
  CFSG.EvenSporadicStandard.M23Std

abbrev AutNorm (Y : Type) [Group Y] (F : Subgroup Y) : Subgroup (MulAut Y) :=
  normalizer ((innerImage Y F : Subgroup (MulAut Y)) : Set (MulAut Y))

@[expose] def InvClassG (Y : Type) [Group Y] (F : Subgroup Y) (c f : ℕ) : Set ↥(AutNorm Y F) :=
  {μ | μ * μ = 1 ∧ μ ≠ 1 ∧ Nat.card (centralizer ({μ} : Set _)) = c ∧
    Nat.card {y : Y // y ∈ F ∧ (μ : MulAut Y) y = y} = f}

@[expose] def AutCensus (Y : Type) [Group Y] (F : Subgroup Y) : Prop :=
  Nat.card {μ : ↥(AutNorm Y F) // μ * μ = 1 ∧ μ ≠ 1} = 375 ∧
    Nat.card (InvClassG Y F 768 16) = 15 ∧ Nat.card (InvClassG Y F 384 8) = 30 ∧
    Nat.card (InvClassG Y F 128 8) = 90 ∧ Nat.card (InvClassG Y F 192 4) = 60 ∧
    Nat.card (InvClassG Y F 64 4) = 180 ∧
    (∀ cf ∈ ([(768, 16), (384, 8), (128, 8), (192, 4), (64, 4)] : List (ℕ × ℕ)),
      ∀ μ ν : ↥(AutNorm Y F), μ ∈ InvClassG Y F cf.1 cf.2 → ν ∈ InvClassG Y F cf.1 cf.2 →
        IsConj ν μ) ∧
    (∀ μ : ↥(AutNorm Y F), μ ∈ InvClassG Y F 768 16 ↔
      (μ : MulAut Y) ∈ innerImage Y F ∧ μ ≠ 1) ∧
    (∀ μ ∈ InvClassG Y F 64 4, (μ : MulAut Y) ∈ innerImage Y ⊤ ∧
      (μ : MulAut Y) ∉ innerImage Y F) ∧
    (∀ μ : ↥(AutNorm Y F), μ ∈ InvClassG Y F 384 8 ∨ μ ∈ InvClassG Y F 128 8 ∨
      μ ∈ InvClassG Y F 192 4 → (μ : MulAut Y) ∉ innerImage Y ⊤) ∧
    (∀ μ : ↥(AutNorm Y F), μ * μ = 1 → μ ≠ 1 →
      μ ∈ InvClassG Y F 768 16 ∨ μ ∈ InvClassG Y F 384 8 ∨ μ ∈ InvClassG Y F 128 8 ∨
        μ ∈ InvClassG Y F 192 4 ∨ μ ∈ InvClassG Y F 64 4)

theorem card_centralizer_singleton_congr {X Y : Type} [Group X] [Group Y] (Ψ : X ≃* Y) (a : X) :
    Nat.card (centralizer ({a} : Set X)) = Nat.card (centralizer ({Ψ a} : Set Y)) :=
  Nat.card_congr
    { toFun := fun c => ⟨Ψ c.1, by
        have := mem_centralizer_singleton_iff.1 c.2
        exact mem_centralizer_singleton_iff.2 (by rw [← map_mul, ← map_mul, this])⟩
      invFun := fun c => ⟨Ψ.symm c.1, by
        have := mem_centralizer_singleton_iff.1 c.2
        refine mem_centralizer_singleton_iff.2 (Ψ.injective ?_)
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply, this]⟩
      left_inv := fun c => Subtype.ext (Ψ.symm_apply_apply c.1)
      right_inv := fun c => Subtype.ext (Ψ.apply_symm_apply c.1) }

variable {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (F : Subgroup X)

@[expose] noncomputable def normAutEquiv :
    ↥(normalizer ((innerImage X F : Subgroup (MulAut X)) : Set (MulAut X))) ≃*
      ↥(normalizer ((innerImage Y (F.map e.toMonoidHom) : Subgroup (MulAut Y)) :
        Set (MulAut Y))) :=
  (Subgroup.equivMapOfInjective _ (MulAut.congr e).toMonoidHom (MulAut.congr e).injective).trans
    (MulEquiv.subgroupCongr (by
      rw [Subgroup.map_equiv_normalizer_eq, innerImage_map' e (MulAut.congr e) (congr_conj e)]))

theorem coe_normAutEquiv (μ : ↥(normalizer ((innerImage X F : Subgroup (MulAut X)) :
    Set (MulAut X)))) : ((normAutEquiv e F μ : ↥(normalizer ((innerImage Y (F.map e.toMonoidHom) :
      Subgroup (MulAut Y)) : Set (MulAut Y)))) : MulAut Y) = MulAut.congr e (μ : MulAut X) := rfl

theorem normAutEquiv_sq (μ : ↥(normalizer ((innerImage X F : Subgroup (MulAut X)) :
    Set (MulAut X)))) : normAutEquiv e F μ * normAutEquiv e F μ = 1 ↔ μ * μ = 1 := by
  rw [← map_mul, map_eq_one_iff _ (normAutEquiv e F).injective]

theorem normAutEquiv_ne (μ : ↥(normalizer ((innerImage X F : Subgroup (MulAut X)) :
    Set (MulAut X)))) : normAutEquiv e F μ ≠ 1 ↔ μ ≠ 1 := by
  rw [ne_eq, map_eq_one_iff _ (normAutEquiv e F).injective, ne_eq]

theorem normAutEquiv_mem_invClassG (μ : ↥(normalizer ((innerImage X F : Subgroup (MulAut X)) :
    Set (MulAut X)))) (c f : ℕ) :
    normAutEquiv e F μ ∈ InvClassG Y (F.map e.toMonoidHom) c f ↔ μ ∈ InvClassG X F c f := by
  have hc : Nat.card (centralizer ({normAutEquiv e F μ} : Set _)) =
      Nat.card (centralizer ({μ} : Set _)) :=
    (card_centralizer_singleton_congr (normAutEquiv e F) μ).symm
  have hf : Nat.card {y : Y // y ∈ F.map e.toMonoidHom ∧
      (normAutEquiv e F μ : MulAut Y) y = y} =
        Nat.card {y : X // y ∈ F ∧ (μ : MulAut X) y = y} := by
    refine (Nat.card_congr (e.toEquiv.subtypeEquiv fun y => ?_)).symm
    show y ∈ F ∧ (μ : MulAut X) y = y ↔ e y ∈ F.map e.toMonoidHom ∧
      MulAut.congr e (μ : MulAut X) (e y) = e y
    rw [congr_apply_mk, e.injective.eq_iff]
    exact and_congr (Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective).symm Iff.rfl
  show _ ∧ _ ∧ _ ∧ _ ↔ _ ∧ _ ∧ _ ∧ _
  rw [normAutEquiv_sq, normAutEquiv_ne, hc, hf]

theorem coe_normAutEquiv_mem_innerImage (μ : ↥(AutNorm X F)) :
    (normAutEquiv e F μ : MulAut Y) ∈ innerImage Y (F.map e.toMonoidHom) ↔
      (μ : MulAut X) ∈ innerImage X F := by
  rw [coe_normAutEquiv, ← innerImage_map' e (MulAut.congr e) (congr_conj e) F]
  exact Subgroup.mem_map_iff_mem (f := (MulAut.congr e).toMonoidHom) (MulAut.congr e).injective

theorem coe_normAutEquiv_mem_innerImage_top (μ : ↥(AutNorm X F)) :
    (normAutEquiv e F μ : MulAut Y) ∈ innerImage Y ⊤ ↔ (μ : MulAut X) ∈ innerImage X ⊤ := by
  rw [coe_normAutEquiv, ← innerImage_top_map' e (MulAut.congr e) (congr_conj e)]
  exact Subgroup.mem_map_iff_mem (f := (MulAut.congr e).toMonoidHom) (MulAut.congr e).injective

theorem AutCensus.map_equiv (h : AutCensus X F) : AutCensus Y (F.map e.toMonoidHom) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, hconj, hF1, hb, hout, hcov⟩ := h
  have key : ∀ c f : ℕ, Nat.card (InvClassG Y (F.map e.toMonoidHom) c f) =
      Nat.card (InvClassG X F c f) := fun c f =>
    (Nat.card_congr ((normAutEquiv e F).toEquiv.subtypeEquiv fun μ =>
      (normAutEquiv_mem_invClassG e F μ c f).symm)).symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← h0]
    exact (Nat.card_congr ((normAutEquiv e F).toEquiv.subtypeEquiv fun μ =>
      (and_congr (normAutEquiv_sq e F μ) (normAutEquiv_ne e F μ)).symm)).symm
  · rw [key, h1]
  · rw [key, h2]
  · rw [key, h3]
  · rw [key, h4]
  · rw [key, h5]
  · intro cf hcf μ ν hμ hν
    obtain ⟨μ₀, rfl⟩ := (normAutEquiv e F).surjective μ
    obtain ⟨ν₀, rfl⟩ := (normAutEquiv e F).surjective ν
    exact (normAutEquiv e F).toMonoidHom.map_isConj (hconj cf hcf μ₀ ν₀
      ((normAutEquiv_mem_invClassG e F μ₀ cf.1 cf.2).1 hμ)
      ((normAutEquiv_mem_invClassG e F ν₀ cf.1 cf.2).1 hν))
  · intro μ
    obtain ⟨μ₀, rfl⟩ := (normAutEquiv e F).surjective μ
    rw [normAutEquiv_mem_invClassG, hF1, coe_normAutEquiv_mem_innerImage,
      normAutEquiv_ne]
  · intro μ hμ
    obtain ⟨μ₀, rfl⟩ := (normAutEquiv e F).surjective μ
    obtain ⟨h1', h2'⟩ := hb μ₀ ((normAutEquiv_mem_invClassG e F μ₀ 64 4).1 hμ)
    exact ⟨(coe_normAutEquiv_mem_innerImage_top e F μ₀).2 h1',
      fun h => h2' ((coe_normAutEquiv_mem_innerImage e F μ₀).1 h)⟩
  · intro μ hμ
    obtain ⟨μ₀, rfl⟩ := (normAutEquiv e F).surjective μ
    rw [coe_normAutEquiv_mem_innerImage_top]
    refine hout μ₀ ?_
    rcases hμ with h | h | h
    · exact Or.inl ((normAutEquiv_mem_invClassG e F μ₀ 384 8).1 h)
    · exact Or.inr (Or.inl ((normAutEquiv_mem_invClassG e F μ₀ 128 8).1 h))
    · exact Or.inr (Or.inr ((normAutEquiv_mem_invClassG e F μ₀ 192 4).1 h))
  · intro μ h1 h2
    obtain ⟨μ₀, rfl⟩ := (normAutEquiv e F).surjective μ
    have := hcov μ₀ ((normAutEquiv_sq e F μ₀).1 h1) ((normAutEquiv_ne e F μ₀).1 h2)
    simp only [normAutEquiv_mem_invClassG e F μ₀]
    exact this

theorem AutCensus.isoInv : IsoInv (fun Y _ F => AutCensus Y F) :=
  fun e _ h => h.map_equiv e _

end CFSG.EvenSporadicStandard.M22Std
