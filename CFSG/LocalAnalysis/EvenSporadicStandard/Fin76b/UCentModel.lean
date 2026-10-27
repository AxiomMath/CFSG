module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.AutEModel
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.UCentSound
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.PinModel

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

@[expose] def wUTabs (n m capW : ℕ) (tT : Table) (cg : Array Table) : Array Table :=
  (mulClosureS n m (wRoots n tT (mulClosureS n m cg capW).1) 40).1

@[expose] def wUMul (n m capW : ℕ) (tT : Table) (cg : Array Table) : ℕ → ℕ → ℕ :=
  tblMulIdx n (wUTabs n m capW tT cg)

@[expose] def wUIdx (n m capW : ℕ) (tT : Table) (cg : Array Table) : ℕ :=
  (wUTabs n m capW tT cg).findIdx (fun T => tblEq n T tT)

theorem ELabelling.map {Γ Δ : Type*} [Group Γ] [Group Δ] {E' : Subgroup Γ} {t : Γ}
    {mulE : ℕ → ℕ → ℕ} {tI : ℕ} {eltE : ℕ → Γ} (h : ELabelling E' t mulE tI eltE) (f : Γ →* Δ)
    (hf : Function.Injective f) :
    ELabelling (E'.map f) (f t) mulE tI (fun a => f (eltE a)) where
  mem a ha := ⟨eltE a, h.mem a ha, rfl⟩
  surj e he := by
    obtain ⟨x, hx, rfl⟩ := he
    obtain ⟨k, hk, rfl⟩ := h.surj x hx
    exact ⟨k, hk, rfl⟩
  inj a ha b hb hab := h.inj a ha b hb (hf hab)
  lt := h.lt
  mul a ha b hb := by simp only [h.mul a ha b hb, map_mul]
  one := by simp only [h.one, map_one]
  tI_lt := h.tI_lt
  at_tI := by simp only [h.at_tI]

theorem map_rootGroup_equiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (t : X) :
    (rootGroup X t).map e.toMonoidHom = rootGroup Y (e t) := by
  have hroots : {y : Y | y * y = e t} = e '' {x : X | x * x = t} := by
    ext y
    constructor
    · intro hy
      refine ⟨e.symm y, ?_, by simp⟩
      apply e.injective
      simp only [map_mul, MulEquiv.apply_symm_apply]
      exact hy
    · rintro ⟨x, hx, rfl⟩
      simp only [Set.mem_ofPred_eq, ← map_mul]
      exact congrArg e hx
  unfold rootGroup
  rw [hroots, MonoidHom.map_closure]
  rfl

theorem ELabelling.transport {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) {t : X}
    {mulE : ℕ → ℕ → ℕ} {tI : ℕ} {eltE : ℕ → X}
    (h : ELabelling (rootGroup X t) t mulE tI eltE) :
    ELabelling (rootGroup Y (e t)) (e t) mulE tI (fun a => e (eltE a)) := by
  have := h.map e.toMonoidHom e.injective
  rwa [map_rootGroup_equiv] at this

@[expose] def ULabelClass (X : Type*) [Group X] (mulE : ℕ → ℕ → ℕ) (tI : ℕ) : Prop :=
  ∀ t : X, orderOf t = 2 → (∃ g : X, g * g = t) →
    ∃ eltE : ℕ → X, ELabelling (rootGroup X t) t mulE tI eltE

theorem ULabelClass.of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    {mulE : ℕ → ℕ → ℕ} {tI : ℕ} (h : ULabelClass X mulE tI) : ULabelClass Y mulE tI := by
  intro t ht2 ⟨g, hg⟩
  obtain ⟨eltE, hlab⟩ := h (e.symm t) (by rw [MulEquiv.orderOf_eq]; exact ht2)
    ⟨e.symm g, by rw [← map_mul, hg]⟩
  have := hlab.transport e
  rw [MulEquiv.apply_symm_apply] at this
  exact ⟨_, this⟩

theorem ULabelClass.of_class {X : Type*} [Group X] (t₀ : X) {mulE : ℕ → ℕ → ℕ} {tI : ℕ}
    (h₀ : ∃ eltE : ℕ → X, ELabelling (rootGroup X t₀) t₀ mulE tI eltE)
    (hcls : ∀ t : X, orderOf t = 2 → (∃ g : X, g * g = t) → ∃ g : X, t = g * t₀ * g⁻¹) :
    ULabelClass X mulE tI := by
  intro t ht2 hsq
  obtain ⟨g, rfl⟩ := hcls t ht2 hsq
  obtain ⟨eltE, hlab⟩ := h₀
  exact ⟨_, hlab.transport (MulAut.conj g)⟩

section Model

variable {G : Type*} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T₀ E : Subgroup G}

theorem eLabelling_of_model (h : InnerConfig G L z t T₀) (hE : EConfig L T₀ E t) {X : Type*}
    [Group X] [Finite X] (φ : X ≃* L) {T Ex : Subgroup X} {tx : X} (hM : PinModel X T Ex tx)
    (hR : RootFactsClass X) {mulE : ℕ → ℕ → ℕ} {tI : ℕ} (hU : ULabelClass X mulE tI) :
    ∃ eltE : ℕ → G, ELabelling E t mulE tI eltE := by
  obtain ⟨ι, hι, -, hrange, hTι, hιt⟩ := h.exists_embedding hM φ
  have hEι : E = Ex.map ι := hE.eq_map_of_pinModel h hM ι hι hrange hTι hιt
  have htx2 : orderOf tx = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact hM.t_sq) hM.t_ne
  have hsq : ∃ g : X, g * g = tx := by
    have hne : {x | x ∈ T ∧ x * x = tx}.Nonempty := by
      by_contra hempty
      rw [Set.not_nonempty_iff_eq_empty] at hempty
      have := hM.roots_ge
      rw [hempty, Set.ncard_empty] at this
      omega
    obtain ⟨x, -, hx⟩ := hne
    exact ⟨x, hx⟩
  have hRf := hR tx htx2 hsq
  have hroots : {x : X | x * x = tx} = {x | x ∈ T ∧ x * x = tx} := by
    have hsub : {x | x ∈ T ∧ x * x = tx} ⊆ {x : X | x * x = tx} := fun x hx => hx.2
    exact (Set.eq_of_subset_of_ncard_le hsub (le_trans hRf.roots_le hM.roots_ge)
      (Set.toFinite _)).symm
  have hEx : rootGroup X tx = Ex := by
    rw [rootGroup, hroots, ← hM.E_eq]
  obtain ⟨eltE, hlab⟩ := hU tx htx2 hsq
  rw [hEx] at hlab
  have := hlab.map ι hι
  rw [hιt, ← hEι] at this
  exact ⟨_, this⟩

end Model

end CFSG.EvenSporadicStandard.Fin76b
