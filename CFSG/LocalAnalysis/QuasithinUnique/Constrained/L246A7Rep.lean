module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246A7Perm
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C1Blocks
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.Foundations
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.QuasithinUnique.L246A7

open Equiv CFSG.Open

local notation "S₇" => Equiv.Perm (Fin 7)
local notation "A₇" => alternatingGroup (Fin 7)

@[expose] noncomputable def autA7 : S₇ ≃* MulAut A₇ :=
  MulEquiv.ofBijective (MulAut.conjNormal (H := A₇))
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by norm_num)
      (by norm_num))

theorem autA7_apply (σ : S₇) (y : A₇) : ((autA7 σ y : A₇) : S₇) = σ * y * σ⁻¹ :=
  MulAut.conjNormal_apply σ y

theorem centerless {σ τ : S₇} (h : ∀ a : A₇, σ * a * σ⁻¹ = τ * a * τ⁻¹) : σ = τ := by
  apply autA7.injective
  apply MulEquiv.ext
  intro a
  apply Subtype.ext
  rw [autA7_apply, autA7_apply]
  exact h a

section Data

variable {G : Type*} [Group G]

structure Alt7Data (L : Subgroup G) where
  α : ↥L →* A₇
  hα : Function.Surjective α
  hker : α.ker = CFSG.pCore 2 ↥L
  β : ↥(blockU L) →* Multiplicative (evenWeight 7)
  hβ : Function.Surjective β
  hβker : β.ker = (blockZ L).subgroupOf (blockU L)
  hβeq : ∀ ℓ : ↥L, ∀ u v : ↥(blockU L), (v : G) = ℓ * u * ℓ⁻¹ → ∀ i : Fin 7,
    ((Multiplicative.toAdd (β v) : evenWeight 7) : Fin 7 → ZMod 2) i =
      ((Multiplicative.toAdd (β u) : evenWeight 7) : Fin 7 → ZMod 2)
        ((α ℓ : Perm (Fin 7))⁻¹ i)

theorem isAltType_seven_iff {L : Subgroup G} : IsAltType L 7 ↔ Nonempty (Alt7Data L) := by
  constructor
  · rintro ⟨α, hα, hker, β, hβ, hβker, hβeq⟩
    exact ⟨⟨α, hα, hker, β, hβ, hβker, hβeq⟩⟩
  · rintro ⟨⟨α, hα, hker, β, hβ, hβker, hβeq⟩⟩
    exact ⟨α, hα, hker, β, hβ, hβker, hβeq⟩

variable {L : Subgroup G}

@[expose] def Alt7Data.vec (D : Alt7Data L) (u : ↥(blockU L)) : Fin 7 → ZMod 2 :=
  ((Multiplicative.toAdd (D.β u) : evenWeight 7) : Fin 7 → ZMod 2)

theorem Alt7Data.vec_conj (D : Alt7Data L) (ℓ : ↥L) (u v : ↥(blockU L))
    (h : (v : G) = ℓ * u * ℓ⁻¹) : D.vec v = pact (D.α ℓ : Perm (Fin 7)) (D.vec u) :=
  funext fun i => D.hβeq ℓ u v h i

@[expose] noncomputable def Alt7Data.conjα (D : Alt7Data L) (σ : A₇) : ↥L →* A₇ :=
  (MulAut.conj σ).toMonoidHom.comp D.α

theorem Alt7Data.conjα_coe (D : Alt7Data L) (σ : A₇) (ℓ : ↥L) :
    ((D.conjα σ ℓ : A₇) : S₇) = (σ : S₇) * (D.α ℓ : S₇) * (σ : S₇)⁻¹ := by
  simp [Alt7Data.conjα, MulAut.conj_apply]

@[expose] noncomputable def Alt7Data.conjβ (D : Alt7Data L) (σ : A₇) :
    ↥(blockU L) →* Multiplicative (evenWeight 7) :=
  (AddMonoidHom.toMultiplicative (vactHom (σ : S₇))).comp D.β

theorem Alt7Data.conjβ_vec (D : Alt7Data L) (σ : A₇) (u : ↥(blockU L)) (i : Fin 7) :
    ((Multiplicative.toAdd (D.conjβ σ u) : evenWeight 7) : Fin 7 → ZMod 2) i =
      ((Multiplicative.toAdd (D.β u) : evenWeight 7) : Fin 7 → ZMod 2) ((σ : S₇)⁻¹ i) := rfl

@[expose] noncomputable def Alt7Data.conj (D : Alt7Data L) (σ : A₇) : Alt7Data L where
  α := D.conjα σ
  hα := (MulAut.conj σ).surjective.comp D.hα
  hker := by
    rw [Alt7Data.conjα, MonoidHom.ker_comp_of_injective D.α _ (MulAut.conj σ).injective]
    exact D.hker
  β := D.conjβ σ
  hβ := by
    have h : Function.Surjective (AddMonoidHom.toMultiplicative (vactHom (σ : S₇))) := fun w => by
      obtain ⟨x, hx⟩ := vactHom_surjective (σ : S₇) (Multiplicative.toAdd w)
      refine ⟨Multiplicative.ofAdd x, ?_⟩
      show Multiplicative.ofAdd ((vactHom (σ : S₇)) x) = w
      rw [hx]
      rfl
    exact h.comp D.hβ
  hβker := by
    have hinj : Function.Injective (AddMonoidHom.toMultiplicative (vactHom (σ : S₇))) :=
      fun a b hab => vactHom_injective (σ : S₇) (Multiplicative.toAdd.injective hab)
    rw [Alt7Data.conjβ, MonoidHom.ker_comp_of_injective D.β _ hinj]
    exact D.hβker
  hβeq := by
    intro ℓ u v h i
    rw [Alt7Data.conjβ_vec, Alt7Data.conjβ_vec, D.hβeq ℓ u v h ((σ : S₇)⁻¹ i)]
    have h2 := D.conjα_coe σ ℓ
    rw [h2]
    simp [mul_assoc]

end Data

section Abstract

variable {X : Type*} [Group X] (L Q : Subgroup X) [L.Normal] [Q.Normal]
  (α : ↥L →* A₇) (hα : Function.Surjective α)
  (hker : ∀ ℓ : ↥L, α ℓ = 1 ↔ (ℓ : X) ∈ Q)

@[expose] noncomputable def psiHom (x : X) : A₇ →* A₇ :=
  (α.liftOfSurjective hα) ⟨α.comp (MulAut.conjNormal x).toMonoidHom, by
    intro ℓ hℓ
    rw [MonoidHom.mem_ker] at hℓ ⊢
    show α (MulAut.conjNormal x ℓ) = 1
    rw [hker] at hℓ ⊢
    rw [MulAut.conjNormal_apply]
    exact Subgroup.Normal.conj_mem inferInstance _ hℓ x⟩

theorem psiHom_apply (x : X) (ℓ : ↥L) :
    psiHom L Q α hα hker x (α ℓ) = α (MulAut.conjNormal x ℓ) := by
  unfold psiHom
  exact MonoidHom.liftOfRightInverse_comp_apply α _ _ _ ℓ

theorem psiHom_mul (x y : X) (a : A₇) :
    psiHom L Q α hα hker (x * y) a = psiHom L Q α hα hker x (psiHom L Q α hα hker y a) := by
  obtain ⟨ℓ, rfl⟩ := hα a
  rw [psiHom_apply, psiHom_apply, psiHom_apply, map_mul, MulAut.mul_apply]

theorem psiHom_one (a : A₇) : psiHom L Q α hα hker 1 a = a := by
  obtain ⟨ℓ, rfl⟩ := hα a
  rw [psiHom_apply, map_one]
  rfl

@[expose] noncomputable def psiEquiv (x : X) : A₇ ≃* A₇ :=
  (psiHom L Q α hα hker x).toMulEquiv (psiHom L Q α hα hker x⁻¹)
    (by ext a; rw [MonoidHom.comp_apply, ← psiHom_mul, inv_mul_cancel, psiHom_one]; rfl)
    (by ext a; rw [MonoidHom.comp_apply, ← psiHom_mul, mul_inv_cancel, psiHom_one]; rfl)

@[expose] noncomputable def piFun (x : X) : S₇ := autA7.symm (psiEquiv L Q α hα hker x)

theorem piFun_spec (x : X) (a : A₇) :
    ((psiHom L Q α hα hker x a : A₇) : S₇) =
      piFun L Q α hα hker x * a * (piFun L Q α hα hker x)⁻¹ := by
  have h := congrArg (fun φ : MulAut A₇ => ((φ a : A₇) : S₇))
    (autA7.apply_symm_apply (psiEquiv L Q α hα hker x))
  simp only [autA7_apply] at h
  exact h.symm

theorem piFun_mul (x y : X) :
    piFun L Q α hα hker (x * y) = piFun L Q α hα hker x * piFun L Q α hα hker y := by
  apply centerless
  intro a
  have h1 := piFun_spec L Q α hα hker (x * y) a
  rw [psiHom_mul] at h1
  have h2 := piFun_spec L Q α hα hker x (psiHom L Q α hα hker y a)
  have h3 := piFun_spec L Q α hα hker y a
  rw [h2, h3] at h1
  rw [← h1]
  simp only [mul_inv_rev]
  group

theorem piFun_alt (ℓ : ↥L) : piFun L Q α hα hker (ℓ : X) = ((α ℓ : A₇) : S₇) := by
  apply centerless
  intro a
  rw [← piFun_spec]
  obtain ⟨m, rfl⟩ := hα a
  rw [psiHom_apply]
  have : (MulAut.conjNormal (ℓ : X)) m = ℓ * m * ℓ⁻¹ := by
    apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    simp
  rw [this]
  simp [map_mul, map_inv]

@[expose] noncomputable def piHom : X →* S₇ :=
  MonoidHom.mk' (piFun L Q α hα hker) (piFun_mul L Q α hα hker)

include hα hker in
theorem exists_pi_abs : ∃ π : X →* S₇,
    (∀ ℓ : ↥L, π (ℓ : X) = ((α ℓ : A₇) : S₇)) ∧
    (∀ (x : X) (ℓ ℓ' : ↥L), (ℓ' : X) = x * ℓ * x⁻¹ →
      ((α ℓ' : A₇) : S₇) = π x * α ℓ * (π x)⁻¹) := by
  refine ⟨piHom L Q α hα hker, fun ℓ => piFun_alt L Q α hα hker ℓ, ?_⟩
  intro x ℓ ℓ' h
  have hℓ' : ℓ' = MulAut.conjNormal x ℓ := by
    apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    exact h
  rw [hℓ', ← psiHom_apply L Q α hα hker x ℓ]
  exact piFun_spec L Q α hα hker x (α ℓ)

end Abstract

section Ambient

variable {G : Type*} [Group G] {L : Subgroup G}

theorem mem_pCore_iff_mem_blockQ (x : ↥L) : x ∈ CFSG.pCore 2 ↥L ↔ (x : G) ∈ blockQ L := by
  show x ∈ CFSG.pCore 2 ↥L ↔ (x : G) ∈ pCoreOf 2 L
  unfold pCoreOf
  exact (Subgroup.mem_map_iff_mem L.subtype_injective).symm

theorem exists_rhoN [Finite G] (D : Alt7Data L) :
    ∃ π : ↥(Subgroup.normalizer (L : Set G)) →* S₇,
      (∀ (ℓ : G) (hℓ : ℓ ∈ L), π ⟨ℓ, Subgroup.le_normalizer hℓ⟩ = ((D.α ⟨ℓ, hℓ⟩ : A₇) : S₇)) ∧
      (∀ (y : ↥(Subgroup.normalizer (L : Set G))) (ℓ ℓ' : ↥L),
        (ℓ' : G) = (y : G) * (ℓ : G) * (y : G)⁻¹ →
        ((D.α ℓ' : A₇) : S₇) = π y * D.α ℓ * (π y)⁻¹) := by
  set N := Subgroup.normalizer (L : Set G) with hN
  have hLN : L ≤ N := Subgroup.le_normalizer
  have hQL : blockQ L ≤ N := (C1.blockQ_le L).trans hLN
  have hNQ : N ≤ Subgroup.normalizer (blockQ L : Set G) := fun g hg => C1.mem_normalizer_blockQ hg
  have hLn : (L.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLN).mpr le_rfl
  have hQn : ((blockQ L).subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQL).mpr hNQ
  let e1 : ↥(L.subgroupOf N) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLN
  let α' : ↥(L.subgroupOf N) →* A₇ := D.α.comp e1.toMonoidHom
  have hα' : Function.Surjective α' := D.hα.comp e1.surjective
  have hker' : ∀ ℓ : ↥(L.subgroupOf N), α' ℓ = 1 ↔ (ℓ : ↥N) ∈ (blockQ L).subgroupOf N := by
    intro ℓ
    show D.α (e1 ℓ) = 1 ↔ _
    rw [← MonoidHom.mem_ker, D.hker, mem_pCore_iff_mem_blockQ, Subgroup.mem_subgroupOf]
    rfl
  obtain ⟨π, hπα, hπc⟩ := exists_pi_abs (L.subgroupOf N) ((blockQ L).subgroupOf N) α' hα' hker'
  refine ⟨π, ?_, ?_⟩
  · intro ℓ hℓ
    exact hπα ⟨⟨ℓ, hLN hℓ⟩, Subgroup.mem_subgroupOf.mpr hℓ⟩
  · intro y ℓ ℓ' h
    have := hπc y ((e1.symm ℓ)) (e1.symm ℓ') (by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact h)
    have e3 : α' (e1.symm ℓ) = D.α ℓ := by
      show D.α (e1 (e1.symm ℓ)) = _
      rw [MulEquiv.apply_symm_apply]
    have e4 : α' (e1.symm ℓ') = D.α ℓ' := by
      show D.α (e1 (e1.symm ℓ')) = _
      rw [MulEquiv.apply_symm_apply]
    rw [e3, e4] at this
    exact this

@[expose] noncomputable def rhoN [Finite G] (D : Alt7Data L) :
    ↥(Subgroup.normalizer (L : Set G)) →* S₇ :=
  Classical.choose (exists_rhoN D)

@[expose] noncomputable def rho [Finite G] (D : Alt7Data L) (g : G) : S₇ := by
  classical
  exact if h : g ∈ Subgroup.normalizer (L : Set G) then rhoN D ⟨g, h⟩ else 1

variable [Finite G] (D : Alt7Data L)

theorem rho_eq {g : G} (h : g ∈ Subgroup.normalizer (L : Set G)) : rho D g = rhoN D ⟨g, h⟩ := by
  classical
  simp [rho, h]

theorem rho_mul {g h : G} (hg : g ∈ Subgroup.normalizer (L : Set G))
    (hh : h ∈ Subgroup.normalizer (L : Set G)) : rho D (g * h) = rho D g * rho D h := by
  rw [rho_eq D (mul_mem hg hh), rho_eq D hg, rho_eq D hh]
  exact map_mul (rhoN D) ⟨g, hg⟩ ⟨h, hh⟩

theorem rho_one : rho D (1 : G) = 1 := by
  rw [rho_eq D (one_mem _)]
  exact map_one (rhoN D)

theorem rho_inv {g : G} (hg : g ∈ Subgroup.normalizer (L : Set G)) : rho D g⁻¹ = (rho D g)⁻¹ := by
  rw [rho_eq D (inv_mem hg), rho_eq D hg]
  exact map_inv (rhoN D) ⟨g, hg⟩

theorem rho_of_mem {ℓ : G} (hℓ : ℓ ∈ L) : rho D ℓ = ((D.α ⟨ℓ, hℓ⟩ : A₇) : S₇) := by
  rw [rho_eq D (Subgroup.le_normalizer hℓ)]
  exact (Classical.choose_spec (exists_rhoN D)).1 ℓ hℓ

theorem rho_conj {y : G} (hy : y ∈ Subgroup.normalizer (L : Set G)) {ℓ : G} (hℓ : ℓ ∈ L) :
    ((D.α ⟨y * ℓ * y⁻¹, (Subgroup.mem_normalizer_iff.1 hy ℓ).1 hℓ⟩ : A₇) : S₇) =
      rho D y * D.α ⟨ℓ, hℓ⟩ * (rho D y)⁻¹ := by
  rw [rho_eq D hy]
  exact (Classical.choose_spec (exists_rhoN D)).2 ⟨y, hy⟩ ⟨ℓ, hℓ⟩ _ rfl

end Ambient

end CFSG.QuasithinUnique.L246A7
