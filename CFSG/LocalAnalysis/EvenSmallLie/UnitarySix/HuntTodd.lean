module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.HuntSetting
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.MathieuExtTodd

public section

namespace CFSG.EvenSmallLie.UnitarySix.Hunt

open Subgroup CFSG.Fischer ToddOrbit CFSG.ComponentClassification.WittDesign
  CFSG.EvenSmallLie.UnitarySix.MathieuExt
open scoped IsMulCommutative

variable {G : Type*} [Group G] {t : G} {L E : Subgroup G} {p : L →* Equiv.Perm (Fin 693)}

@[expose] def rhoF (f : orb E t ≃ Fin 22) : normalizer (E : Set G) →* Equiv.Perm (Fin 22) :=
  (Equiv.permCongrHom f).toMonoidHom.comp actHom

theorem rhoF_apply (f : orb E t ≃ Fin 22) (n : normalizer (E : Set G)) (i : Fin 22) :
    rhoF f n i = f (actHom n (f.symm i)) := rfl

theorem rhoF_symm (f : orb E t ≃ Fin 22) (n : normalizer (E : Set G)) (i : Fin 22) :
    ((f.symm (rhoF f n i) : orb E t) : G) = n * f.symm i * (n : G)⁻¹ := by
  rw [rhoF_apply, Equiv.symm_apply_apply, coe_actHom_apply]

theorem isMulCommutative_E
    (H : ToddOrbit.Hyp t L E p) : IsMulCommutative E :=
  ⟨⟨fun a b => Subtype.ext (H.E_comm a.2 b.2)⟩⟩

@[reducible] def eModule [IsMulCommutative E] (hsq : ∀ e ∈ E, e ^ 2 = 1) :
    Module (ZMod 2) (Additive E) :=
  AddCommMonoid.zmodModule (n := 2) fun x : Additive E => by
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero]
    exact Subtype.ext (by simpa using hsq _ (Additive.toMul x).2)

section Module

@[expose] def conjE (n : normalizer (E : Set G)) (e : E) : E :=
  ⟨n * e * (n : G)⁻¹, (mem_normalizer_iff.1 n.2 e).1 e.2⟩

@[expose] def conjAdd (n : normalizer (E : Set G)) : Additive E →+ Additive E where
  toFun v := Additive.ofMul (conjE n (Additive.toMul v))
  map_zero' := by
    change Additive.ofMul (conjE n 1) = Additive.ofMul 1
    congr 1
    exact Subtype.ext (by simp [conjE])
  map_add' u v := by
    change Additive.ofMul (conjE n (Additive.toMul u * Additive.toMul v)) =
      Additive.ofMul (conjE n (Additive.toMul u) * conjE n (Additive.toMul v))
    congr 1
    exact Subtype.ext (by simp only [conjE, Subgroup.coe_mul]; group)

theorem coe_conjAdd (n : normalizer (E : Set G)) (v : Additive E) :
    ((Additive.toMul (conjAdd n v) : E) : G) = n * (Additive.toMul v : E) * (n : G)⁻¹ := rfl

variable
    (H : ToddOrbit.Hyp t L E p)

@[expose] def pt
    (f : orb E t ≃ Fin 22) (i : Fin 22) : Additive E :=
  Additive.ofMul ⟨f.symm i, H.orb_subset_E (f.symm i).2⟩

theorem pt_injective
    (f : orb E t ≃ Fin 22) : Function.Injective (pt H f) := fun _ _ h =>
  f.symm.injective (Subtype.ext (congrArg (fun v : Additive E => ((Additive.toMul v : E) : G)) h))

theorem conjAdd_pt
    (f : orb E t ≃ Fin 22) (n : normalizer (E : Set G)) (i : Fin 22) :
    conjAdd n (pt H f i) = pt H f (rhoF f n i) := by
  apply Additive.toMul.injective
  refine Subtype.ext ?_
  rw [coe_conjAdd]
  exact (rhoF_symm f n i).symm

end Module

section Todd

variable
    [Finite G] (H : ToddOrbit.Hyp t L E p) (f : orb E t ≃ Fin 22)
include H

omit [Finite G] in
theorem exists_conjAdd
    (hM : M22 ≤ (rhoF f).range) {g : Equiv.Perm (Fin 22)} (hg : g ∈ M22) :
    ∃ ρ : Additive E →+ Additive E, ∀ i, ρ (pt H f i) = pt H f (g i) := by
  obtain ⟨n, rfl⟩ := hM hg
  exact ⟨conjAdd n, conjAdd_pt H f n⟩

theorem span_pt
    [IsMulCommutative E] [Module (ZMod 2) (Additive E)]
    (hM : M22 ≤ (rhoF f).range) : Submodule.span (ZMod 2) (Set.range (pt H f)) = ⊤ :=
  (todd_module_unique (V := Additive E) H.card_E (pt_injective H f)
    fun _ hg => exists_conjAdd H f hM hg).1

theorem closure_orb
    (hM : M22 ≤ (rhoF f).range) : closure (orb E t) = E := by
  have := isMulCommutative_E H
  let _ := eModule H.E_sq
  refine le_antisymm ((closure_le E).2 H.orb_subset_E) fun e he => ?_
  have key : ∀ v ∈ Submodule.span (ZMod 2) (Set.range (pt H f)),
      ((Additive.toMul v : E) : G) ∈ closure (orb E t) := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact subset_closure (f.symm i).2
    | zero => exact one_mem _
    | add x y _ _ hx hy => exact mul_mem hx hy
    | smul c x _ hx =>
      rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
      · rw [zero_smul]
        exact one_mem _
      · rwa [one_smul]
  exact key (Additive.ofMul ⟨e, he⟩) (by rw [span_pt H f hM]; exact Submodule.mem_top)

theorem exists_toddEquiv
    [IsMulCommutative E] [Module (ZMod 2) (Additive E)]
    (hM : M22 ≤ (rhoF f).range) :
    ∃ e : Additive E ≃ₗ[ZMod 2] toddModule, ∀ (n : normalizer (E : Set G))
      (hn : rhoF f n ∈ hexadAut) (v : Additive E), e (conjAdd n v) = toddAct hn (e v) := by
  obtain ⟨e, he⟩ := todd_module_equiv (V := Additive E) H.card_E (pt_injective H f)
    fun _ hg => exists_conjAdd H f hM hg
  refine ⟨e, fun n hn v => ?_⟩
  have key : ∀ v ∈ Submodule.span (ZMod 2) (Set.range (pt H f)),
      e (conjAdd n v) = toddAct hn (e v) := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      rw [conjAdd_pt, he, he, toddAct_point]
    | zero => simp only [map_zero]
    | add x y _ _ hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
    | smul c x _ hx =>
      rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
      · simp only [zero_smul, map_zero]
      · rwa [one_smul]
  exact key v (by rw [span_pt H f hM]; exact Submodule.mem_top)

end Todd

section Kernel

variable
    [Finite G] (H : Hyp t L E p) (f : orb E t ≃ Fin 22)
include H

theorem Hyp.ker_rhoF
    (hM : M22 ≤ (rhoF f).range) :
    (rhoF f).ker = E.subgroupOf (normalizer (E : Set G)) := by
  ext n
  rw [MonoidHom.mem_ker, mem_subgroupOf]
  constructor
  · intro hn
    have h1 : actHom (E := E) (t := t) n = 1 :=
      (MulEquiv.map_eq_one_iff (Equiv.permCongrHom f)).1 hn
    have hle : closure (orb E t) ≤ centralizer ({(n : G)} : Set G) := by
      refine (closure_le _).2 fun s hs => mem_centralizer_singleton_iff.2 ?_
      have h2 := congrArg Subtype.val (Equiv.ext_iff.1 h1 ⟨s, hs⟩)
      change (n : G) * s * (n : G)⁻¹ = s at h2
      calc s * n = (n : G) * s * (n : G)⁻¹ * n := by rw [h2]
        _ = n * s := by group
    rw [closure_orb H.todd f hM] at hle
    refine H.cent (mem_centralizer_iff.2 fun e he => ?_)
    exact mem_centralizer_singleton_iff.1 (hle he)
  · intro hn
    change (Equiv.permCongrHom f).toMonoidHom (actHom n) = 1
    rw [actHom_eq_one_of_mem H.todd hn, map_one]

theorem Hyp.card_le_mul_card_fixed
    (hM : M22 ≤ (rhoF f).range) {B : Subgroup G}
    (hBN : B ≤ normalizer (E : Set G)) (hB2 : ∀ b ∈ B, b ^ 2 = 1)
    (hX : (B.subgroupOf (normalizer (E : Set G))).map (rhoF f) ≤ hexadAut) :
    Nat.card B ≤ Nat.card ((B.subgroupOf (normalizer (E : Set G))).map (rhoF f)) *
      Nat.card {v : toddModule // ∀ x (hx : x ∈ (B.subgroupOf
        (normalizer (E : Set G))).map (rhoF f)), toddAct (hX hx) v = v} := by
  have := isMulCommutative_E H.todd
  let _ := eModule H.todd.E_sq
  obtain ⟨e, he⟩ := exists_toddEquiv H.todd f hM
  set N := normalizer (E : Set G)
  set X := (B.subgroupOf N).map (rhoF f)
  set ψ : (B.subgroupOf N) →* Equiv.Perm (Fin 22) := (rhoF f).comp (B.subgroupOf N).subtype
  have hψ : ψ.range = X := by rw [MonoidHom.range_comp, range_subtype]
  have hcardB : Nat.card B = Nat.card (B.subgroupOf N) :=
    (Nat.card_congr (subgroupOfEquivOfLe hBN).toEquiv).symm
  have hsplit : Nat.card (B.subgroupOf N) = Nat.card ψ.range * Nat.card ψ.ker := by
    rw [card_eq_card_quotient_mul_card_subgroup ψ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv]
  have hkerE : ∀ k : ψ.ker, (((k : B.subgroupOf N) : N) : G) ∈ E := by
    intro k
    have hk : (k : B.subgroupOf N) ∈ ψ.ker := k.2
    rw [MonoidHom.mem_ker] at hk
    have := (Hyp.ker_rhoF H f hM).le hk
    exact mem_subgroupOf.1 this
  have hBc : ∀ b ∈ B, ∀ c ∈ B, b * c = c * b :=
    fun _ hb _ hc => SolomonWong.mul_comm_of_sq_eq_one hB2 hb hc
  let F : ψ.ker → {v : toddModule // ∀ x (hx : x ∈ X), toddAct (hX hx) v = v} :=
    fun k => ⟨e (Additive.ofMul ⟨_, hkerE k⟩), by
      rintro _ ⟨m, hm, rfl⟩
      rw [← he]
      congr 1
      apply Additive.toMul.injective
      refine Subtype.ext ?_
      rw [coe_conjAdd]
      change (m : G) * (((k : B.subgroupOf N) : N) : G) * (m : G)⁻¹ = _
      rw [hBc _ (mem_subgroupOf.1 hm) _ (mem_subgroupOf.1 (k : B.subgroupOf N).2),
        mul_inv_cancel_right]
      rfl⟩
  have hF : Function.Injective F := by
    intro k k' h
    have h1 := congrArg (fun v => ((Additive.toMul (e.symm v.1) : E) : G)) h
    simp only [F, LinearEquiv.symm_apply_apply] at h1
    exact Subtype.ext (Subtype.ext (Subtype.ext h1))
  rw [hcardB, hsplit, hψ]
  exact Nat.mul_le_mul_left _ (Nat.card_le_card_of_injective F hF)

end Kernel

end CFSG.EvenSmallLie.UnitarySix.Hunt
