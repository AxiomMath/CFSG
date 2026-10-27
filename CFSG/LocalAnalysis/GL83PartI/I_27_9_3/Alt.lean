module

public import CFSG.LocalAnalysis.GL83PartI.I_27_9.Perm

public section

namespace GL83.PiGen

open Equiv Equiv.Perm GL83

section PermLemmas

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem altOn_le_alternatingGroup (S : Set Ω) : altOn S ≤ alternatingGroup Ω := inf_le_left

theorem conj_mem_altOn {S : Set Ω} {ρ g : Perm Ω} (hρ : ∀ x, ρ x ∈ S ↔ x ∈ S)
    (hg : g ∈ altOn S) : ρ * g * ρ⁻¹ ∈ altOn S := by
  rw [mem_altOn] at hg ⊢
  refine ⟨(alternatingGroup.normal (α := Ω)).conj_mem g hg.1 ρ, fun x hx => ?_⟩
  have h1 : ρ⁻¹ x ∉ S := fun h => hx (by simpa using (hρ (ρ⁻¹ x)).2 h)
  rw [Perm.mul_apply, Perm.mul_apply, hg.2 _ h1]
  simp

theorem commute_of_mem_altOn {S : Set Ω} {ρ g : Perm Ω} (hρ : ∀ x ∈ S, ρ x = x)
    (hg : g ∈ altOn S) : ρ * g = g * ρ := by
  ext x
  rw [Perm.mul_apply, Perm.mul_apply]
  by_cases hx : x ∈ S
  · rw [hρ x hx, hρ (g x) (apply_mem_of_mem_altOn hg hx)]
  · have hgx : g x = x := (mem_altOn.1 hg).2 x hx
    have hρx : ρ x ∉ S := fun h => hx (by
      have h2 : ρ x = x := ρ.injective (hρ _ h)
      rwa [h2] at h)
    rw [hgx, (mem_altOn.1 hg).2 _ hρx]

theorem altOn_subgroupOf_eq_range (s : Finset Ω) :
    (altOn (s : Set Ω)).subgroupOf (alternatingGroup Ω) =
      (alternatingGroup.ofSubtype s).range := by
  ext g
  rw [Subgroup.mem_subgroupOf, alternatingGroup.mem_range_ofSubtype_iff, mem_altOn]
  constructor
  · rintro ⟨-, h⟩ x hx
    by_contra hxs
    exact (Perm.mem_support.1 hx) (h x (by simpa using hxs))
  · intro h
    refine ⟨g.2, fun x hx => ?_⟩
    by_contra hne
    exact hx (h (Perm.mem_support.2 hne))

@[expose] noncomputable def altOnEquiv (s : Finset Ω) :
    ↥(altOn (s : Set Ω)) ≃* ↥(alternatingGroup ↥s) :=
  ((Subgroup.subgroupOfEquivOfLe (altOn_le_alternatingGroup (s : Set Ω))).symm.trans
    (MulEquiv.subgroupCongr (altOn_subgroupOf_eq_range s))).trans
    (MonoidHom.ofInjective (alternatingGroup.ofSubtype_injective (s := s))).symm

theorem exists_altOn_equiv_fin (s : Finset Ω) {m : ℕ} (h : s.card = m) :
    Nonempty (↥(altOn (s : Set Ω)) ≃* ↥(alternatingGroup (Fin m))) :=
  ⟨(altOnEquiv s).trans (Equiv.altCongrHom (s.equivFin.trans (finCongr h)))⟩

end PermLemmas

section Cover

variable {X : Type*} [Group X] {K : Subgroup X} {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

@[expose] def subAlt (e : ↥K ≃* ↥(alternatingGroup Ω)) (S : Set Ω) : Subgroup X :=
  ((altOn S).subgroupOf (alternatingGroup Ω)).map (K.subtype.comp e.symm.toMonoidHom)

theorem mem_subAlt {e : ↥K ≃* ↥(alternatingGroup Ω)} {S : Set Ω} {x : X} :
    x ∈ subAlt e S ↔ ∃ hx : x ∈ K, ((e ⟨x, hx⟩ : alternatingGroup Ω) : Perm Ω) ∈ altOn S := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨(e.symm u).2, ?_⟩
    have h : e ⟨((e.symm u : ↥K) : X), (e.symm u).2⟩ = u := e.apply_symm_apply u
    show ((e ⟨((e.symm u : ↥K) : X), (e.symm u).2⟩ : alternatingGroup Ω) : Perm Ω) ∈ altOn S
    rw [h]
    exact Subgroup.mem_subgroupOf.1 hu
  · rintro ⟨hx, h⟩
    refine ⟨e ⟨x, hx⟩, h, ?_⟩
    simp

theorem subAlt_le (e : ↥K ≃* ↥(alternatingGroup Ω)) (S : Set Ω) : subAlt e S ≤ K := by
  rintro _ ⟨u, -, rfl⟩
  exact (e.symm u).2

@[expose] noncomputable def subAltEquiv (e : ↥K ≃* ↥(alternatingGroup Ω)) (S : Set Ω) :
    ↥(subAlt e S) ≃* ↥(altOn S) :=
  ((Subgroup.equivMapOfInjective ((altOn S).subgroupOf (alternatingGroup Ω))
    (K.subtype.comp e.symm.toMonoidHom) (K.subtype_injective.comp e.symm.injective)).symm).trans
    (Subgroup.subgroupOfEquivOfLe (altOn_le_alternatingGroup S))

theorem iSup_subAlt {ι : Sort*} (e : ↥K ≃* ↥(alternatingGroup Ω)) (S : ι → Set Ω)
    (h : (⨆ i, altOn (S i)) = alternatingGroup Ω) : (⨆ i, subAlt e (S i)) = K := by
  unfold subAlt
  rw [← Subgroup.map_iSup]
  have h1 : (⨆ i, (altOn (S i)).subgroupOf (alternatingGroup Ω)) = ⊤ := by
    apply Subgroup.map_injective (alternatingGroup Ω).subtype_injective
    rw [Subgroup.map_iSup, Subgroup.map_top, Subgroup.range_subtype]
    conv_rhs => rw [← h]
    exact iSup_congr fun i => Subgroup.map_subgroupOf_eq_of_le (altOn_le_alternatingGroup (S i))
  rw [h1, ← MonoidHom.range_eq_map, MonoidHom.range_comp]
  have h2 : e.symm.toMonoidHom.range = ⊤ := MonoidHom.range_eq_top.2 e.symm.surjective
  rw [h2, Subgroup.map_top, Subgroup.range_subtype]

@[expose] def Implements (e : ↥K ≃* ↥(alternatingGroup Ω)) (g : X) (σ : Perm Ω) : Prop :=
  ∀ x : ↥K, ∃ y : ↥K, (y : X) = g * x * g⁻¹ ∧
    σ * ((e x : alternatingGroup Ω) : Perm Ω) * σ⁻¹ = ((e y : alternatingGroup Ω) : Perm Ω)

theorem implements_of_mem (e : ↥K ≃* ↥(alternatingGroup Ω)) {g : X} (hg : g ∈ K) :
    Implements e g ((e ⟨g, hg⟩ : alternatingGroup Ω) : Perm Ω) := by
  intro x
  refine ⟨⟨g, hg⟩ * x * ⟨g, hg⟩⁻¹, rfl, ?_⟩
  simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]

theorem Implements.mem_subAlt_conj {e : ↥K ≃* ↥(alternatingGroup Ω)} {g : X} {σ : Perm Ω}
    (h : Implements e g σ) {S : Set Ω} (hσ : ∀ ω, σ ω ∈ S ↔ ω ∈ S) {x : X}
    (hx : x ∈ subAlt e S) : g * x * g⁻¹ ∈ subAlt e S := by
  obtain ⟨hxK, hxS⟩ := mem_subAlt.1 hx
  obtain ⟨y, hy, hyσ⟩ := h ⟨x, hxK⟩
  rw [← hy]
  refine mem_subAlt.2 ⟨y.2, ?_⟩
  have hy' : (⟨(y : X), y.2⟩ : ↥K) = y := rfl
  rw [hy', ← hyσ]
  exact conj_mem_altOn hσ hxS

theorem Implements.comm_of_mem_subAlt {e : ↥K ≃* ↥(alternatingGroup Ω)} {g : X} {σ : Perm Ω}
    (h : Implements e g σ) {S : Set Ω} (hσ : ∀ ω ∈ S, σ ω = ω) {x : X}
    (hx : x ∈ subAlt e S) : g * x = x * g := by
  obtain ⟨hxK, hxS⟩ := mem_subAlt.1 hx
  obtain ⟨y, hy, hyσ⟩ := h ⟨x, hxK⟩
  have hc := commute_of_mem_altOn hσ hxS
  have h1 : ((e y : alternatingGroup Ω) : Perm Ω) =
      ((e ⟨x, hxK⟩ : alternatingGroup Ω) : Perm Ω) := by
    rw [← hyσ, hc, mul_assoc, mul_inv_cancel, mul_one]
  have h2 : y = ⟨x, hxK⟩ := e.injective (Subtype.ext h1)
  have h3 : g * x * g⁻¹ = x := by
    rw [← hy, h2]
  calc g * x = g * x * g⁻¹ * g := by group
    _ = x * g := by rw [h3]

theorem exists_mem_subAlt_eq (e : ↥K ≃* ↥(alternatingGroup Ω)) {S : Set Ω} {σ : Perm Ω}
    (hσ : σ ∈ altOn S) :
    ∃ x : X, x ∈ subAlt e S ∧ ∃ hx : x ∈ K,
      ((e ⟨x, hx⟩ : alternatingGroup Ω) : Perm Ω) = σ := by
  refine ⟨((e.symm ⟨σ, altOn_le_alternatingGroup S hσ⟩ : ↥K) : X), ?_, (e.symm _).2, ?_⟩
  · refine mem_subAlt.2 ⟨(e.symm _).2, ?_⟩
    have : e ⟨((e.symm ⟨σ, altOn_le_alternatingGroup S hσ⟩ : ↥K) : X), (e.symm _).2⟩ =
        ⟨σ, altOn_le_alternatingGroup S hσ⟩ := e.apply_symm_apply _
    rw [this]
    exact hσ
  · have : e ⟨((e.symm ⟨σ, altOn_le_alternatingGroup S hσ⟩ : ↥K) : X), (e.symm _).2⟩ =
        ⟨σ, altOn_le_alternatingGroup S hσ⟩ := e.apply_symm_apply _
    rw [this]

end Cover

end GL83.PiGen
