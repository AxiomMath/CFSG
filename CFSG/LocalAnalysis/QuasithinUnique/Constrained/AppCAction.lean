module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCZ
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Action

public section

namespace CFSG.QuasithinUnique.AppC

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.A5
  CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.A5.Action Equiv

section Abstract

variable {X : Type*} [Group X] (L Q U : Subgroup X) [L.Normal] [Q.Normal] [U.Normal]
  (α : ↥L →* Alt5) (hα : Function.Surjective α) (hker : ∀ ℓ : ↥L, α ℓ = 1 ↔ (ℓ : X) ∈ Q)
  (β : ↥U ≃* Multiplicative (evenWeight 5))
  (hβ : ∀ (ℓ : ↥L) (u u' : ↥U), (u' : X) = (ℓ : X) * (u : X) * (ℓ : X)⁻¹ →
    Multiplicative.toAdd (β u') = vact ((α ℓ : Alt5) : Perm (Fin 5)) (Multiplicative.toAdd (β u)))

include hβ in
theorem pi_compat' (x : X) (u u' : ↥U) (h : (u' : X) = x * u * x⁻¹) :
    Multiplicative.toAdd (β u') =
      vact (piFun L Q α hα hker x) (Multiplicative.toAdd (β u)) := by
  have hu' : u' = MulAut.conjNormal x u := by
    apply Subtype.ext; rw [MulAut.conjNormal_apply]; exact h
  have hg : ∀ w, vact (piFun L Q α hα hker x)⁻¹ (fX U β x w) = w := by
    apply rigid (fun w => vact (piFun L Q α hα hker x)⁻¹ (fX U β x w))
    · intro w w'
      show vact _ (fX U β x (w + w')) = vact _ (fX U β x w) + vact _ (fX U β x w')
      rw [fX_add, vact_add]
    · intro w w' h
      apply fX_inj U β x
      have := congrArg (vact (piFun L Q α hα hker x)) h
      simpa [← vact_mul, vact_one] using this
    · intro σ hσ w
      show vact _ (fX U β x (vact σ w)) = vact σ (vact _ (fX U β x w))
      obtain ⟨ℓ, hℓ⟩ := hα ⟨σ, Equiv.Perm.mem_alternatingGroup.mpr hσ⟩
      have hℓσ : ((α ℓ : Alt5) : Perm (Fin 5)) = σ := by rw [hℓ]
      set u₀ := β.symm (Multiplicative.ofAdd w) with hu₀
      have hw : w = Multiplicative.toAdd (β u₀) := by simp [hu₀]
      have h1 : vact σ w = Multiplicative.toAdd (β (MulAut.conjNormal (ℓ : X) u₀)) := by
        rw [hβ ℓ u₀ _ (by rw [MulAut.conjNormal_apply]), hℓσ, ← hw]
      have h2 : MulAut.conjNormal x (MulAut.conjNormal (ℓ : X) u₀) =
          MulAut.conjNormal ((MulAut.conjNormal x ℓ : ↥L) : X) (MulAut.conjNormal x u₀) := by
        apply Subtype.ext
        simp only [MulAut.conjNormal_apply]
        group
      have h3 : fX U β x (vact σ w) =
          vact ((piFun L Q α hα hker x) * σ * (piFun L Q α hα hker x)⁻¹) (fX U β x w) := by
        rw [h1, fX_bU, h2]
        rw [hβ (MulAut.conjNormal x ℓ) (MulAut.conjNormal x u₀) _ rfl]
        rw [hw, fX_bU]
        congr 1
        rw [← psiHom_apply L Q α hα hker x ℓ]
        rw [← hℓσ, ← piFun_spec]
      rw [h3, ← vact_mul, ← vact_mul]
      congr 1
      group
  have h5 := hg (Multiplicative.toAdd (β u))
  rw [fX_bU] at h5
  have h6 := congrArg (vact (piFun L Q α hα hker x)) h5
  rw [← vact_mul, mul_inv_cancel, vact_one] at h6
  rw [hu']
  exact h6

include hα hker hβ in
theorem exists_pi_abs : ∃ π : X →* Perm (Fin 5),
    (∀ (x : X) (u u' : ↥U), (u' : X) = x * u * x⁻¹ →
      Multiplicative.toAdd (β u') = vact (π x) (Multiplicative.toAdd (β u))) ∧
    (∀ ℓ : ↥L, π (ℓ : X) = ((α ℓ : Alt5) : Perm (Fin 5))) ∧
    (∀ (x : X) (ℓ ℓ' : ↥L), (ℓ' : X) = x * ℓ * x⁻¹ →
      ((α ℓ' : Alt5) : Perm (Fin 5)) = π x * α ℓ * (π x)⁻¹) := by
  refine ⟨piHom L Q α hα hker, fun x u u' h => pi_compat' L Q U α hα hker β hβ x u u' h,
    fun ℓ => piFun_alt L Q α hα hker ℓ, ?_⟩
  intro x ℓ ℓ' h
  have hℓ' : ℓ' = MulAut.conjNormal x ℓ := by
    apply Subtype.ext; rw [MulAut.conjNormal_apply]; exact h
  rw [hℓ', ← psiHom_apply L Q α hα hker x ℓ]
  exact piFun_spec L Q α hα hker x (α ℓ)

end Abstract

section Ambient

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_beta (hL : IsShort2 L) (h5 : IsAltType L 5) (α : ↥L →* alternatingGroup (Fin 5))
    (hα : Function.Surjective α) (hαk : α.ker = CFSG.pCore 2 L) :
    ∃ β : ↥(blockU L) ≃* Multiplicative (evenWeight 5),
      ∀ (ℓ : ↥L) (u u' : ↥(blockU L)), (u' : G) = (ℓ : G) * (u : G) * (ℓ : G)⁻¹ →
        Multiplicative.toAdd (β u') =
          vact ((α ℓ : Alt5) : Perm (Fin 5)) (Multiplicative.toAdd (β u)) := by
  have hZ := blockZ_eq_bot_of_alt5 hL h5
  obtain ⟨α₀, hα₀, hα₀k, β₀, hβ₀, hβ₀k, hβ₀e⟩ := h5
  have hinj : Function.Injective β₀ := by
    rw [← MonoidHom.ker_eq_bot_iff, hβ₀k, hZ, Subgroup.bot_subgroupOf]
  let β₁ : ↥(blockU L) ≃* Multiplicative (evenWeight 5) := MulEquiv.ofBijective β₀ ⟨hinj, hβ₀⟩
  have hβ₁ : ∀ (ℓ : ↥L) (u u' : ↥(blockU L)), (u' : G) = (ℓ : G) * (u : G) * (ℓ : G)⁻¹ →
      Multiplicative.toAdd (β₁ u') =
        vact ((α₀ ℓ : Alt5) : Perm (Fin 5)) (Multiplicative.toAdd (β₁ u)) := by
    intro ℓ u u' h
    apply Subtype.ext
    funext i
    exact hβ₀e ℓ u u' h i
  have hle : α₀.ker ≤ α.ker := by rw [hα₀k, hαk]
  let ψ : Alt5 →* Alt5 := α₀.liftOfSurjective hα₀ ⟨α, hle⟩
  have hψ : ∀ ℓ : ↥L, ψ (α₀ ℓ) = α ℓ := fun ℓ =>
    MonoidHom.liftOfRightInverse_comp_apply α₀ (Function.surjInv hα₀)
      (Function.rightInverse_surjInv hα₀) ⟨α, hle⟩ ℓ
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    obtain ⟨ℓ, rfl⟩ := hα₀ a
    rw [hψ] at ha
    have : ℓ ∈ α.ker := ha
    rw [hαk, ← hα₀k] at this
    exact this
  have hψsurj : Function.Surjective ψ := by
    intro b
    obtain ⟨ℓ, rfl⟩ := hα b
    exact ⟨α₀ ℓ, hψ ℓ⟩
  let ψe : Alt5 ≃* Alt5 := MulEquiv.ofBijective ψ ⟨hψinj, hψsurj⟩
  obtain ⟨σ, hσ⟩ := aut_inner ψe
  refine ⟨β₁.trans (vactEquiv σ), ?_⟩
  intro ℓ u u' h
  show vact σ (Multiplicative.toAdd (β₁ u')) = _
  rw [hβ₁ ℓ u u' h, ← vact_mul]
  show _ = vact ((α ℓ : Alt5) : Perm (Fin 5)) (vact σ (Multiplicative.toAdd (β₁ u)))
  rw [← vact_mul]
  congr 1
  have h1 : ((α ℓ : Alt5) : Perm (Fin 5)) = σ * (α₀ ℓ : Perm (Fin 5)) * σ⁻¹ := by
    rw [← hψ ℓ]
    exact hσ (α₀ ℓ)
  rw [h1]
  group

theorem exists_pi_normalizer (hL : IsShort2 L) (h5 : IsAltType L 5)
    (α : ↥L →* alternatingGroup (Fin 5)) (hα : Function.Surjective α)
    (hαk : α.ker = CFSG.pCore 2 L) :
    ∃ (β : ↥(blockU L) ≃* Multiplicative (evenWeight 5))
      (π : ↥(Subgroup.normalizer (L : Set G)) →* Perm (Fin 5)),
      (∀ (ℓ : ↥L) (u u' : ↥(blockU L)), (u' : G) = (ℓ : G) * (u : G) * (ℓ : G)⁻¹ →
        Multiplicative.toAdd (β u') =
          vact ((α ℓ : Alt5) : Perm (Fin 5)) (Multiplicative.toAdd (β u))) ∧
      (∀ (y : ↥(Subgroup.normalizer (L : Set G))) (u u' : ↥(blockU L)),
        (u' : G) = (y : G) * (u : G) * (y : G)⁻¹ →
        Multiplicative.toAdd (β u') = vact (π y) (Multiplicative.toAdd (β u))) ∧
      (∀ (ℓ : G) (hℓ : ℓ ∈ L),
        π ⟨ℓ, Subgroup.le_normalizer hℓ⟩ = ((α ⟨ℓ, hℓ⟩ : Alt5) : Perm (Fin 5))) ∧
      (∀ y : ↥(Subgroup.normalizer (L : Set G)),
        π y = 1 ↔ ∀ u ∈ blockU L, (y : G) * u * (y : G)⁻¹ = u) := by
  obtain ⟨β, hβ⟩ := exists_beta hL h5 α hα hαk
  set N := Subgroup.normalizer (L : Set G) with hN
  have hLN : L ≤ N := Subgroup.le_normalizer
  have hQL : blockQ L ≤ N := (C1.blockQ_le L).trans hLN
  have hUL : blockU L ≤ N := (C1.blockU_le_blockQ hL).trans hQL
  have hNQ : N ≤ Subgroup.normalizer (blockQ L : Set G) := fun g hg => C1.mem_normalizer_blockQ hg
  have hNU : N ≤ Subgroup.normalizer (blockU L : Set G) := fun g hg => C1.mem_normalizer_blockU hg
  have hLn : (L.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLN).mpr le_rfl
  have hQn : ((blockQ L).subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQL).mpr hNQ
  have hUn : ((blockU L).subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUL).mpr hNU
  let e1 : ↥(L.subgroupOf N) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLN
  let e2 : ↥((blockU L).subgroupOf N) ≃* ↥(blockU L) := Subgroup.subgroupOfEquivOfLe hUL
  let α' : ↥(L.subgroupOf N) →* Alt5 := α.comp e1.toMonoidHom
  have hα' : Function.Surjective α' := hα.comp e1.surjective
  let β' : ↥((blockU L).subgroupOf N) ≃* Multiplicative (evenWeight 5) := e2.trans β
  have hker' : ∀ ℓ : ↥(L.subgroupOf N), α' ℓ = 1 ↔ (ℓ : ↥N) ∈ (blockQ L).subgroupOf N := by
    intro ℓ
    show α (e1 ℓ) = 1 ↔ _
    rw [← MonoidHom.mem_ker, hαk, mem_pCore_iff_mem_blockQ, Subgroup.mem_subgroupOf]
    rfl
  have hβ' : ∀ (ℓ : ↥(L.subgroupOf N)) (u u' : ↥((blockU L).subgroupOf N)),
      (u' : ↥N) = (ℓ : ↥N) * (u : ↥N) * (ℓ : ↥N)⁻¹ →
      Multiplicative.toAdd (β' u') =
        vact ((α' ℓ : Alt5) : Perm (Fin 5)) (Multiplicative.toAdd (β' u)) := by
    intro ℓ u u' h
    have hG : ((e2 u' : ↥(blockU L)) : G) =
        ((e1 ℓ : ↥L) : G) * ((e2 u : ↥(blockU L)) : G) * ((e1 ℓ : ↥L) : G)⁻¹ := by
      have := congrArg Subtype.val h
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
      exact this
    exact hβ (e1 ℓ) (e2 u) (e2 u') hG
  obtain ⟨π, hπc, hπα, -⟩ := exists_pi_abs (L.subgroupOf N) ((blockQ L).subgroupOf N)
    ((blockU L).subgroupOf N) α' hα' hker' β' hβ'
  have hcompat : ∀ (y : ↥N) (u u' : ↥(blockU L)), (u' : G) = (y : G) * (u : G) * (y : G)⁻¹ →
      Multiplicative.toAdd (β u') = vact (π y) (Multiplicative.toAdd (β u)) := by
    intro y u u' hG
    have h1 := hπc y (e2.symm u) (e2.symm u') (by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact hG)
    have e3 : β' (e2.symm u) = β u := by
      show β (e2 (e2.symm u)) = _
      rw [MulEquiv.apply_symm_apply]
    have e4 : β' (e2.symm u') = β u' := by
      show β (e2 (e2.symm u')) = _
      rw [MulEquiv.apply_symm_apply]
    rw [e3, e4] at h1
    exact h1
  refine ⟨β, π, hβ, hcompat, ?_, ?_⟩
  · intro ℓ hℓ
    exact hπα ⟨⟨ℓ, hLN hℓ⟩, Subgroup.mem_subgroupOf.mpr hℓ⟩
  · intro y
    constructor
    · intro h1 u hu
      have hmem : (y : G) * u * (y : G)⁻¹ ∈ blockU L := by
        have := C1.mem_normalizer_blockU (L := L) y.2
        exact (Subgroup.mem_normalizer_iff.mp this u).mp hu
      have h2 := hcompat y ⟨u, hu⟩ ⟨_, hmem⟩ rfl
      rw [h1, vact_one] at h2
      have h3 := β.injective (Multiplicative.toAdd.injective h2)
      exact congrArg Subtype.val h3
    · intro h1
      apply vact_faithful
      intro w
      obtain ⟨u, rfl⟩ : ∃ u : ↥(blockU L), Multiplicative.toAdd (β u) = w :=
        ⟨β.symm (Multiplicative.ofAdd w), by simp⟩
      exact (hcompat y u u (h1 u u.2).symm).symm

end Ambient

end CFSG.QuasithinUnique.AppC
