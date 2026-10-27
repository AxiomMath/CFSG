module

public import CFSG.LargeExtraspecial.S14Nine

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup CFSG.Open CFSG.LargeExtraspecial.S4

theorem center_map_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (center A).map e.toMonoidHom = center B := by
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply, Subgroup.mem_center_iff,
    Subgroup.mem_center_iff]
  constructor
  · intro hx b
    obtain ⟨b, rfl⟩ := e.surjective b
    rw [← map_mul, ← map_mul, hx]
  · intro hx b
    apply e.injective
    rw [map_mul, map_mul, hx]

theorem isExtraspecialPGroup_of_mulEquiv {p : ℕ} {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (h : IsExtraspecialPGroup p A) : IsExtraspecialPGroup p B := by
  obtain ⟨hp, hcomm, hfrat, hcard⟩ := h
  have hc : (commutator A).map e.toMonoidHom = commutator B := by
    rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ e.surjective]
  have hf : (frattini A).map e.toMonoidHom = frattini B :=
    OrderIso.map_radical (MulEquiv.mapSubgroup e)
  refine ⟨hp.of_equiv e, ?_, ?_, ?_⟩
  · rw [← hc, hcomm, center_map_mulEquiv]
  · rw [← hf, hfrat, center_map_mulEquiv]
  · rw [← center_map_mulEquiv e, Subgroup.card_map_of_injective e.injective, hcard]

variable {G : Type} [Group G] [Finite G]

structure W4Hyp (S : Setting G) (g : G) (t : S.O) (c : Config) : Prop where
  stage : Stage S g t
  hc : c = .omegaMinus6 ∨ c = .omegaPlus6
  occ : c.Occurs S g t
  ext : IsExtraspecialPGroup 2 (Nbar S g t)
  simple : IsSimpleGroup (Mbar0 S)
  c7 : Concl14_7 S g t
  le : Rbar S g t ≤ (Mbar0 S).map S.Mbar.subtype
  fstar : FCt S t = Nbar S g t

noncomputable abbrev ι (S : Setting G) : ↥(Mbar0 S) →* S.O :=
  S.Mbar.subtype.comp (Mbar0 S).subtype

theorem ι_injective (S : Setting G) : Function.Injective (ι S) :=
  S.Mbar.subtype_injective.comp (Mbar0 S).subtype_injective

theorem ι_mem_Mbar (S : Setting G) (x : ↥(Mbar0 S)) : ι S x ∈ S.Mbar := (x : S.Mbar).2

theorem ι_mem_map (S : Setting G) (x : ↥(Mbar0 S)) : ι S x ∈ (Mbar0 S).map S.Mbar.subtype :=
  ⟨x, x.2, rfl⟩

theorem ι_conj (S : Setting G) (a b : ↥(Mbar0 S)) :
    ι S (a * b * a⁻¹) = ι S a * ι S b * (ι S a)⁻¹ :=
  (map_mul (ι S) (a * b) a⁻¹).trans (congrArg₂ (· * ·) (map_mul (ι S) a b) (map_inv (ι S) a))

theorem exists_ι_eq {S : Setting G} {y : S.O} (hy : y ∈ (Mbar0 S).map S.Mbar.subtype) :
    ∃ x : ↥(Mbar0 S), ι S x = y := by
  obtain ⟨x, hx, rfl⟩ := hy
  exact ⟨⟨x, hx⟩, rfl⟩

namespace W4Hyp

variable {S : Setting G} {g : G} {t : S.O} {c : Config} (h : W4Hyp S g t c)
include h

theorem haQ : g * S.z * g⁻¹ ∈ S.QG := h.stage.hyp4.conj_mem

theorem t_mem_Rbar : t ∈ Rbar S g t := Lbar_le_Rbar h.stage.mem h.stage.mem

theorem Nbar_le_map : Nbar S g t ≤ (Mbar0 S).map S.Mbar.subtype := fun _ hx => h.le hx.1

theorem t_mem_map : t ∈ (Mbar0 S).map S.Mbar.subtype := h.le h.t_mem_Rbar

theorem t_mem_Mbar : t ∈ S.Mbar := Rbar_le_Mbar h.t_mem_Rbar

theorem t_mem_Mbar0 : (⟨t, h.t_mem_Mbar⟩ : S.Mbar) ∈ Mbar0 S := by
  obtain ⟨x, hx, hxt⟩ := h.t_mem_map
  have hx' : x = ⟨t, h.t_mem_Mbar⟩ := Subtype.ext hxt
  exact hx' ▸ hx

theorem t_mul_t : t * t = 1 := mul_self_of_mem_Lbar S h.haQ h.stage.mem

theorem orderOf_t : orderOf t = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [pow_two]; exact h.t_mul_t) h.stage.ne_one

omit h in
@[expose] def t₀ (h : W4Hyp S g t c) : ↥(Mbar0 S) := ⟨⟨t, h.t_mem_Mbar⟩, h.t_mem_Mbar0⟩

@[simp] theorem ι_t₀ : ι S h.t₀ = t := rfl

theorem orderOf_t₀ : orderOf h.t₀ = 2 := by
  rw [← orderOf_injective (ι S) (ι_injective S) h.t₀, ι_t₀, h.orderOf_t]

theorem mem_centralizer_t₀_iff {x : ↥(Mbar0 S)} :
    x ∈ centralizer ({h.t₀} : Set ↥(Mbar0 S)) ↔ ι S x * t = t * ι S x := by
  rw [mem_centralizer_singleton_iff]
  constructor
  · intro hx
    have := congrArg (ι S) hx
    simpa only [map_mul, ι_t₀] using this
  · intro hx
    apply ι_injective S
    simpa only [map_mul, ι_t₀] using hx

omit h in
@[expose] noncomputable def ιK (h : W4Hyp S g t c) :
    ↥(centralizer ({h.t₀} : Set ↥(Mbar0 S))) →* S.O :=
  (ι S).comp (centralizer ({h.t₀} : Set ↥(Mbar0 S))).subtype

theorem ιK_injective : Function.Injective h.ιK :=
  (ι_injective S).comp Subtype.val_injective

theorem ιK_commute (x : ↥(centralizer ({h.t₀} : Set ↥(Mbar0 S)))) :
    h.ιK x * t = t * h.ιK x :=
  h.mem_centralizer_t₀_iff.mp x.2

theorem ιK_mem_Ct (x : ↥(centralizer ({h.t₀} : Set ↥(Mbar0 S)))) : h.ιK x ∈ Ct S t :=
  ⟨ι_mem_Mbar S _, mem_centralizer_singleton_iff.mpr (h.ιK_commute x)⟩

theorem mem_range_ιK {y : S.O} :
    y ∈ h.ιK.range ↔ y ∈ (Mbar0 S).map S.Mbar.subtype ∧ y * t = t * y := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨ι_mem_map S _, h.ιK_commute x⟩
  · rintro ⟨hy, hyt⟩
    obtain ⟨x, rfl⟩ := exists_ι_eq hy
    exact ⟨⟨x, h.mem_centralizer_t₀_iff.mpr hyt⟩, rfl⟩

theorem Nbar_le_range_ιK : Nbar S g t ≤ h.ιK.range := fun _ hy =>
  h.mem_range_ιK.mpr ⟨h.Nbar_le_map hy, commute_of_mem_Rbar h.haQ (Nbar_le_Rbar hy)⟩

omit h in
@[expose] noncomputable def Q₀ (h : W4Hyp S g t c) :
    Subgroup ↥(centralizer ({h.t₀} : Set ↥(Mbar0 S))) :=
  (Nbar S g t).comap h.ιK

theorem map_Q₀ : h.Q₀.map h.ιK = Nbar S g t := by
  rw [Q₀, Subgroup.map_comap_eq, inf_of_le_right h.Nbar_le_range_ιK]

noncomputable def Q₀EquivNbar : h.Q₀ ≃* Nbar S g t :=
  (h.Q₀.equivMapOfInjective h.ιK h.ιK_injective).trans (MulEquiv.subgroupCongr h.map_Q₀)

theorem card_Q₀ : Nat.card h.Q₀ = Nat.card (Nbar S g t) :=
  Nat.card_congr h.Q₀EquivNbar.toEquiv

theorem conj_mem_Q₀ {n : ↥(centralizer ({h.t₀} : Set ↥(Mbar0 S)))} (hn : n ∈ h.Q₀)
    (k : ↥(centralizer ({h.t₀} : Set ↥(Mbar0 S)))) : k * n * k⁻¹ ∈ h.Q₀ := by
  have e : h.ιK (k * n * k⁻¹) = h.ιK k * h.ιK n * (h.ιK k)⁻¹ := by
    simp only [map_mul, map_inv]
  change h.ιK (k * n * k⁻¹) ∈ Nbar S g t
  rw [e]
  exact conj_mem_Nbar_of_mem_Ct h.haQ (h.ιK_mem_Ct k) hn

theorem Q₀_normal : h.Q₀.Normal := ⟨fun _ hn k => h.conj_mem_Q₀ hn k⟩

theorem Q₀_extraspecial : IsExtraspecialPGroup 2 h.Q₀ :=
  isExtraspecialPGroup_of_mulEquiv h.Q₀EquivNbar.symm h.ext

end W4Hyp

end CFSG.LargeExtraspecial.S14
