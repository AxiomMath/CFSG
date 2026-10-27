module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitSylow
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitSevenPerm
public import CFSG.LocalAnalysis.ComponentClassification.TBLitAction
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

noncomputable def permEquivAutA7 : Perm (Fin 7) ≃* MulAut (alternatingGroup (Fin 7)) :=
  MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin 7)))
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by norm_num)
      (by norm_num))

theorem permEquivAutA7_apply (σ : Perm (Fin 7)) (g : alternatingGroup (Fin 7)) :
    ((permEquivAutA7 σ g : alternatingGroup (Fin 7)) : Perm (Fin 7)) = σ * g * σ⁻¹ := by
  rw [permEquivAutA7, MulEquiv.ofBijective_apply, MulAut.conjNormal_apply]

theorem permEquivAutA7_of_mem (g : alternatingGroup (Fin 7)) :
    permEquivAutA7 (g : Perm (Fin 7)) = MulAut.conj g := by
  ext h : 2
  rw [permEquivAutA7_apply, MulAut.conj_apply]
  rfl

variable {X : Type} [Group X]

noncomputable def actPerm (L : Subgroup X)
    (e : L ⧸ pPrimeCore 2 L ≃* alternatingGroup (Fin 7)) :
    normalizer (L : Set X) →* Perm (Fin 7) :=
  permEquivAutA7.symm.toMonoidHom.comp ((MulAut.congr e).toMonoidHom.comp (TBLit.oddQuotAction L))

theorem actPerm_eq_one_iff {L : Subgroup X} (e : L ⧸ pPrimeCore 2 L ≃* alternatingGroup (Fin 7))
    (g : normalizer (L : Set X)) : actPerm L e g = 1 ↔ (g : X) ∈ coreActionKernel L := by
  rw [actPerm, MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_eq, map_one, MulEquiv.map_eq_one_iff,
    TBLit.oddQuotAction_eq_one_iff, mem_coreActionKernel]
  have hg := g.2
  constructor
  · intro h
    refine ⟨g.2, fun j hj => ?_⟩
    have h1 := h j⁻¹ (inv_mem hj)
    have h2 := TBLit.conj_mem_oddCoreIn (inv_mem hg) (inv_mem h1)
    rw [show (g : X)⁻¹ * (⁅j⁻¹, (g : X)⁆)⁻¹ * (g : X)⁻¹⁻¹ = j⁻¹ * (g : X)⁻¹ * j * g by
      simp only [commutatorElement_def]; group] at h2
    exact h2
  · rintro ⟨-, h⟩ s hs
    have h1 := h s⁻¹ (inv_mem hs)
    have h2 := TBLit.conj_mem_oddCoreIn hg (inv_mem h1)
    rw [show (g : X) * (s⁻¹⁻¹ * (g : X)⁻¹ * s⁻¹ * g)⁻¹ * (g : X)⁻¹ = ⁅s, (g : X)⁆ by
      simp only [commutatorElement_def]; group] at h2
    exact h2

theorem actPerm_of_mem {L : Subgroup X} (e : L ⧸ pPrimeCore 2 L ≃* alternatingGroup (Fin 7))
    (l : L) :
    actPerm L e ⟨l, le_normalizer l.2⟩ =
      ((e (QuotientGroup.mk l) : alternatingGroup (Fin 7)) : Perm (Fin 7)) := by
  rw [actPerm, MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_eq, permEquivAutA7_of_mem]
  ext g : 2
  obtain ⟨q, rfl⟩ := e.surjective g
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
  rw [MulAut.congr_apply]
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rw [TBLit.oddQuotAction_mk, MulAut.conj_apply]
  have : (⟨((⟨l, le_normalizer l.2⟩ : normalizer (L : Set X)) : X) * (m : X) *
      ((⟨l, le_normalizer l.2⟩ : normalizer (L : Set X)) : X)⁻¹,
      (mem_normalizer_iff.mp (le_normalizer l.2) m).mp m.2⟩ : L) = l * m * l⁻¹ := by
    apply Subtype.ext
    simp
  rw [this, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_mul,
    map_inv]

variable [Finite X] {t : X} {L : Subgroup X}

theorem Config.exists_good_action (h : Config t L)
    (e : L ⧸ pPrimeCore 2 L ≃* alternatingGroup (Fin 7))
    (T : Sylow 2 ↥(centralizer ({t} : Set X))) :
    ∃ ψ : normalizer (L : Set X) →* Perm (Fin 7),
      (∀ g, ψ g = 1 ↔ (g : X) ∈ coreActionKernel L) ∧
      (∀ g : normalizer (L : Set X), (g : X) ∈ L → ψ g ∈ alternatingGroup (Fin 7)) ∧
      (∀ g : normalizer (L : Set X), (g : X) ∈ Config.sylowIn T → ψ g ∈ P0) ∧
      (∀ σ ∈ R0, ∃ g : normalizer (L : Set X), (g : X) ∈ Config.sylowIn T ⊓ L ∧ ψ g = σ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := normalizer (L : Set X) with hN
  set φ := actPerm L e with hφ
  set T' := Config.sylowIn T with hT'
  have hT'N : T' ≤ N := (Config.sylowIn_le T).trans h.le_normalizer
  have hQ : IsPGroup 2 ((T'.subgroupOf N).map φ) :=
    ((Config.isPGroup_sylowIn T).comap_of_injective N.subtype (subtype_injective N)).map φ
  obtain ⟨S, hS⟩ := hQ.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Perm (Fin 7)) sylowP0 S
  set ψ : N →* Perm (Fin 7) := (MulAut.conj g⁻¹).toMonoidHom.comp φ with hψ
  have hψφ : ∀ x, ψ x = g⁻¹ * φ x * g := by
    intro x; simp [hψ]
  have hψker : ∀ x, ψ x = 1 ↔ (x : X) ∈ coreActionKernel L := by
    intro x
    rw [hψφ, ← actPerm_eq_one_iff e x]
    constructor
    · intro h1
      have := congrArg (fun y => g * y * g⁻¹) h1
      simpa [mul_assoc] using this
    · intro h1
      rw [h1]; group
  have hA7 : ∀ x : N, (x : X) ∈ L → ψ x ∈ alternatingGroup (Fin 7) := by
    intro x hx
    rw [hψφ]
    have hl : φ x = ((e (QuotientGroup.mk (⟨x, hx⟩ : L))) : Perm (Fin 7)) := by
      rw [hφ]
      have := actPerm_of_mem e ⟨x, hx⟩
      convert this using 2
    rw [hl]
    have := (alternatingGroup.normal (α := Fin 7)).conj_mem _
      (e (QuotientGroup.mk (⟨x, hx⟩ : L))).2 g⁻¹
    simpa using this
  have hP0 : ∀ x : N, (x : X) ∈ T' → ψ x ∈ P0 := by
    intro x hx
    rw [hψφ]
    have h1 : φ x ∈ (S : Subgroup (Perm (Fin 7))) := hS ⟨x, hx, rfl⟩
    rw [← hg, Sylow.coe_subgroup_smul, coe_sylowP0,
      Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h1
    simpa [MulAut.smul_def, MulAut.conj_apply, mul_assoc] using h1
  refine ⟨ψ, hψker, hA7, hP0, ?_⟩
  set R := (T' ⊓ L : Subgroup X) with hR
  have hRN : R ≤ N := inf_le_left.trans hT'N
  set f : (R.subgroupOf N) →* Perm (Fin 7) := ψ.comp (R.subgroupOf N).subtype with hf
  have hfinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker, hf, MonoidHom.comp_apply, hψker] at hx
    have hxR : ((x : N) : X) ∈ R := x.2
    have h1 : ((x : N) : X) ∈ (T' ⊓ coreActionKernel L ⊓ L : Subgroup X) :=
      ⟨⟨hxR.1, hx⟩, hxR.2⟩
    rw [h.inf_kernel_inf_L T, mem_bot] at h1
    rw [mem_bot]
    exact Subtype.ext (Subtype.ext h1)
  have hrange : f.range ≤ R0 := by
    rintro _ ⟨x, rfl⟩
    have hxR : ((x : N) : X) ∈ R := x.2
    exact ⟨hP0 _ hxR.1, hA7 _ hxR.2⟩
  have hcard : Nat.card f.range = 8 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hfinj).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe hRN).toEquiv]
    exact h.card_inf_L T
  have heq : f.range = R0 := Subgroup.eq_of_le_of_card_ge hrange (by rw [card_R0, hcard])
  intro σ hσ
  rw [← heq] at hσ
  obtain ⟨x, rfl⟩ := hσ
  exact ⟨x, x.2, rfl⟩

end CFSG.ComponentClassification.HSFLit
