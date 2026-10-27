module

public import Mathlib.RepresentationTheory.Character
public import Mathlib.RepresentationTheory.FiniteIndex
public import Mathlib.Basic.Complex.Basic

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson.InducedCharacterConstruction

open Representation LinearMap

universe u w

variable {G : Type u} [Group G]

def classFun (k : Type*) [Field k] (G : Type*) [Group G] : Submodule k (G → k) where
  carrier := {f | ∀ g h : G, f (h * g * h⁻¹) = f g}
  add_mem' hf hg := fun x y => by simp only [Pi.add_apply, hf x y, hg x y]
  zero_mem' := fun _ _ => rfl
  smul_mem' c f hf := fun x y => by simp only [Pi.smul_apply, hf x y]

@[simp] theorem mem_classFun {k : Type*} [Field k] {f : G → k} :
    f ∈ classFun k G ↔ ∀ g h : G, f (h * g * h⁻¹) = f g := Iff.rfl

theorem character_mem_classFun {V : Type w} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) : ρ.character ∈ classFun ℂ G :=
  fun g h => ρ.char_conj g h

noncomputable def charInner [Fintype G] (f h : G → ℂ) : ℂ :=
  (Nat.card G : ℂ)⁻¹ * ∑ g : G, f g * (starRingEnd ℂ) (h g)

omit [Group G] in
theorem charInner_apply [Fintype G] (f h : G → ℂ) :
    charInner f h = (Nat.card G : ℂ)⁻¹ * ∑ g : G, f g * (starRingEnd ℂ) (h g) := (rfl)

def irrCharacters (G : Type u) [Group G] : Set (G → ℂ) :=
  {χ | ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : FiniteDimensional ℂ V)
    (ρ : Representation ℂ G V), ρ.IsIrreducible ∧ ρ.character = χ}

theorem mem_irrCharacters_iff {χ : G → ℂ} :
    χ ∈ irrCharacters G ↔ ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module ℂ V)
      (_ : FiniteDimensional ℂ V) (ρ : Representation ℂ G V),
      ρ.IsIrreducible ∧ ρ.character = χ := Iff.rfl

theorem irrCharacters_subset_classFun : irrCharacters G ⊆ (classFun ℂ G : Set (G → ℂ)) := by
  rintro χ ⟨V, _, _, _, ρ, -, rfl⟩
  exact character_mem_classFun ρ

variable {S : Subgroup G}

abbrev RightCosets (S : Subgroup G) := Quotient (QuotientGroup.rightRel S)

theorem rightCosets_mk_eq_mk_iff {x y : G} :
    (Quotient.mk (QuotientGroup.rightRel S) x = Quotient.mk _ y) ↔ y * x⁻¹ ∈ S := by
  rw [Quotient.eq]; exact QuotientGroup.rightRel_apply

theorem card_rightCosets (S : Subgroup G) : Nat.card (RightCosets S) = S.index := by
  rw [Subgroup.index_eq_card]
  exact Nat.card_eq_of_bijective _
    (QuotientGroup.quotientRightRelEquivQuotientLeftRel S).bijective

noncomputable def subgroupPart (S : Subgroup G) (x : G) : S :=
  ⟨x * (Quotient.out (Quotient.mk (QuotientGroup.rightRel S) x))⁻¹,
    rightCosets_mk_eq_mk_iff.mp (Quotient.out_eq (Quotient.mk (QuotientGroup.rightRel S) x))⟩

theorem subgroupPart_coe (x : G) : (subgroupPart S x : G)
    = x * (Quotient.out (Quotient.mk (QuotientGroup.rightRel S) x))⁻¹ := (rfl)

theorem subgroupPart_mul_out (x : G) :
    (subgroupPart S x : G) * Quotient.out (Quotient.mk (QuotientGroup.rightRel S) x) = x := by
  simp [subgroupPart_coe]

theorem rightCosets_mk_mul_left (s : S) (x : G) :
    Quotient.mk (QuotientGroup.rightRel S) ((s : G) * x) = Quotient.mk _ x :=
  rightCosets_mk_eq_mk_iff.mpr (by simp)

theorem rightCosets_mk_mul_out (s : S) (q : RightCosets S) :
    Quotient.mk (QuotientGroup.rightRel S) ((s : G) * Quotient.out q) = q := by
  rw [rightCosets_mk_mul_left, Quotient.out_eq]

theorem subgroupPart_mul_left (s : S) (x : G) :
    subgroupPart S ((s : G) * x) = s * subgroupPart S x := by
  ext
  simp only [subgroupPart_coe, rightCosets_mk_mul_left, Subgroup.coe_mul, mul_assoc]

theorem subgroupPart_out (q : RightCosets S) : subgroupPart S (Quotient.out q) = 1 := by
  ext; simp only [subgroupPart_coe, Quotient.out_eq]; simp

noncomputable def rightCosetsProdEquiv (S : Subgroup G) : RightCosets S × S ≃ G where
  toFun p := (p.2 : G) * Quotient.out p.1
  invFun x := (Quotient.mk _ x, subgroupPart S x)
  left_inv := by
    rintro ⟨q, s⟩
    refine Prod.ext (rightCosets_mk_mul_out s q) ?_
    change subgroupPart S ((s : G) * Quotient.out q) = s
    rw [subgroupPart_mul_left, subgroupPart_out, mul_one]
  right_inv x := subgroupPart_mul_out x

theorem rightCosetsProdEquiv_apply (p : RightCosets S × S) :
    rightCosetsProdEquiv S p = (p.2 : G) * Quotient.out p.1 := (rfl)

def resClassFun (S : Subgroup G) (f : G → ℂ) : S → ℂ := fun s => f (s : G)

theorem resClassFun_apply (S : Subgroup G) (f : G → ℂ) (s : S) :
    resClassFun S f s = f (s : G) := (rfl)

theorem resClassFun_conj (S : Subgroup G) {f : G → ℂ} (hf : f ∈ classFun ℂ G) (s h : S) :
    resClassFun S f (s * h * s⁻¹) = resClassFun S f h := by
  simpa only [resClassFun_apply, Subgroup.coe_mul, Subgroup.coe_inv] using hf (h : G) (s : G)

noncomputable def subgroupExtend (S : Subgroup G) (f : S → ℂ) : G → ℂ :=
  Function.extend S.subtype f 0

@[simp] theorem subgroupExtend_coe (S : Subgroup G) (f : S → ℂ) (s : S) :
    subgroupExtend S f (s : G) = f s :=
  Subtype.val_injective.extend_apply _ _ _

theorem subgroupExtend_of_notMem (S : Subgroup G) (f : S → ℂ) {x : G} (hx : x ∉ S) :
    subgroupExtend S f x = 0 := by
  rw [subgroupExtend, Function.extend_apply']
  · rfl
  · rintro ⟨a, rfl⟩; exact hx a.2

theorem subgroupExtend_conj (S : Subgroup G) (f : S → ℂ)
    (hf : ∀ s h : S, f (s * h * s⁻¹) = f h) (s : S) (x : G) :
    subgroupExtend S f ((s : G) * x * (s : G)⁻¹) = subgroupExtend S f x := by
  by_cases hx : x ∈ S
  · have h1 : (s : G) * x * (s : G)⁻¹ = ((s * ⟨x, hx⟩ * s⁻¹ : S) : G) := by simp
    rw [h1, subgroupExtend_coe, hf, ← subgroupExtend_coe S f ⟨x, hx⟩]
  · have hx' : (s : G) * x * (s : G)⁻¹ ∉ S := by
      intro hmem
      refine hx ?_
      have h2 : (s : G)⁻¹ * ((s : G) * x * (s : G)⁻¹) * (s : G) ∈ S :=
        S.mul_mem (S.mul_mem (S.inv_mem s.2) hmem) s.2
      simpa [mul_assoc] using h2
    rw [subgroupExtend_of_notMem _ _ hx', subgroupExtend_of_notMem _ _ hx]

noncomputable def indClassFun (S : Subgroup G) [Fintype G] (f : S → ℂ) : G → ℂ :=
  fun g => (Nat.card S : ℂ)⁻¹ * ∑ x : G, subgroupExtend S f (x⁻¹ * g * x)

theorem indClassFun_apply (S : Subgroup G) [Fintype G] (f : S → ℂ) (g : G) :
    indClassFun S f g = (Nat.card S : ℂ)⁻¹ * ∑ x : G, subgroupExtend S f (x⁻¹ * g * x) := (rfl)

theorem indClassFun_one (S : Subgroup G) [Fintype G] (f : S → ℂ) :
    indClassFun S f 1 = (S.index : ℂ) * f 1 := by
  have hS : (Nat.card S : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hterm : ∀ x : G, subgroupExtend S f (x⁻¹ * 1 * x) = f 1 := fun x => by
    rw [show x⁻¹ * 1 * x = ((1 : S) : G) from by simp, subgroupExtend_coe]
  rw [indClassFun_apply]
  simp only [hterm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Nat.card_eq_fintype_card, ← Subgroup.index_mul_card S]
  push_cast
  rw [mul_comm (S.index : ℂ) (Nat.card S : ℂ), ← mul_assoc, ← mul_assoc,
    inv_mul_cancel₀ hS, one_mul]

theorem indClassFun_conj (S : Subgroup G) [Fintype G] (f : S → ℂ) (g y : G) :
    indClassFun S f (y * g * y⁻¹) = indClassFun S f g := by
  rw [indClassFun_apply, indClassFun_apply]
  congr 1
  refine Fintype.sum_equiv (Equiv.mulLeft y⁻¹) _ _ fun z => ?_
  simp only [Equiv.coe_mulLeft]
  rw [show z⁻¹ * (y * g * y⁻¹) * z = (y⁻¹ * z)⁻¹ * g * (y⁻¹ * z) from by group]

theorem indClassFun_mem_classFun (S : Subgroup G) [Fintype G] (f : S → ℂ) :
    indClassFun S f ∈ classFun ℂ G := fun g y => indClassFun_conj S f g y

theorem indClassFun_eq_sum_rightCosets [Fintype G] [DecidablePred (· ∈ S)] (f : S → ℂ)
    (hf : ∀ s h : S, f (s * h * s⁻¹) = f h) (g : G) :
    indClassFun S f g
      = ∑ q : RightCosets S, subgroupExtend S f (Quotient.out q * g * (Quotient.out q)⁻¹) := by
  rw [indClassFun_apply]
  have h1 : ∑ x : G, subgroupExtend S f (x⁻¹ * g * x)
      = ∑ t : G, subgroupExtend S f (t * g * t⁻¹) :=
    Fintype.sum_equiv (Equiv.inv G) _ _ fun t => by simp only [Equiv.inv_apply, inv_inv]
  rw [h1, ← Fintype.sum_equiv (rightCosetsProdEquiv S) (fun p => subgroupExtend S f
      (rightCosetsProdEquiv S p * g * (rightCosetsProdEquiv S p)⁻¹)) _ (fun _ => rfl),
    Fintype.sum_prod_type]
  have h2 : ∀ (q : RightCosets S) (s : S),
      subgroupExtend S f (rightCosetsProdEquiv S (q, s) * g * (rightCosetsProdEquiv S (q, s))⁻¹)
        = subgroupExtend S f (Quotient.out q * g * (Quotient.out q)⁻¹) := by
    intro q s
    rw [rightCosetsProdEquiv_apply,
      show ((s : G) * Quotient.out q) * g * ((s : G) * Quotient.out q)⁻¹
        = (s : G) * (Quotient.out q * g * (Quotient.out q)⁻¹) * (s : G)⁻¹ from by group]
    exact subgroupExtend_conj S f hf s _
  simp only [h2, Finset.sum_const, Finset.card_univ]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [nsmul_eq_mul, ← mul_assoc, ← Nat.card_eq_fintype_card,
    inv_mul_cancel₀ (by exact_mod_cast Nat.card_pos.ne' : (Nat.card S : ℂ) ≠ 0), one_mul]

variable {V : Type w} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ S V)

noncomputable def coindEquivPi : Representation.coindV S.subtype ρ ≃ₗ[ℂ] (RightCosets S → V) where
  toFun f q := f.1 (Quotient.out q)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun u := ⟨fun x => ρ (subgroupPart S x) (u (Quotient.mk _ x)), by
    rw [Representation.mem_coindV]
    intro s x
    simp only [Subgroup.coe_subtype, subgroupPart_mul_left, rightCosets_mk_mul_left, map_mul]
    rfl⟩
  left_inv f := by
    ext x
    change ρ (subgroupPart S x) (f.1 (Quotient.out (Quotient.mk _ x))) = f.1 x
    conv_rhs => rw [← subgroupPart_mul_out (S := S) x]
    exact ((Representation.mem_coindV _ _ _).mp f.2 (subgroupPart S x) _).symm
  right_inv u := by
    ext q
    change ρ (subgroupPart S (Quotient.out q)) (u (Quotient.mk _ (Quotient.out q))) = u q
    rw [subgroupPart_out, Quotient.out_eq]
    simp

noncomputable def indPiMap (g : G) : (RightCosets S → V) →ₗ[ℂ] (RightCosets S → V) where
  toFun u q := ρ (subgroupPart S (Quotient.out q * g)) (u (Quotient.mk _ (Quotient.out q * g)))
  map_add' _ _ := by ext q; simp
  map_smul' _ _ := by ext q; simp

theorem indPiMap_apply (g : G) (u : RightCosets S → V) (q : RightCosets S) :
    indPiMap ρ g u q
      = ρ (subgroupPart S (Quotient.out q * g)) (u (Quotient.mk _ (Quotient.out q * g))) :=
  (rfl)

theorem coindEquivPi_conj (g : G) :
    (coindEquivPi ρ).conj (Representation.coind S.subtype ρ g) = indPiMap ρ g := by
  ext u q
  simp only [LinearEquiv.conj_apply, indPiMap_apply]
  rfl

private theorem trace_pi_eq_sum_diag {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M] [Fintype ι] [DecidableEq ι]
    (T : (ι → M) →ₗ[R] (ι → M)) :
    LinearMap.trace R (ι → M) T
      = ∑ i, LinearMap.trace R M (proj i ∘ₗ T ∘ₗ single R (fun _ => M) i) := by
  conv_lhs => rw [show T = ∑ i, (single R (fun _ : ι => M) i) ∘ₗ (proj i ∘ₗ T) from by
    ext x j; simp [Finset.sum_apply]]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.trace_comp_comm' (proj i ∘ₗ T) (single R (fun _ : ι => M) i),
    LinearMap.comp_assoc]

theorem trace_diag_indPiMap [DecidableEq (RightCosets S)] (g : G) (q : RightCosets S) :
    LinearMap.trace ℂ V (proj q ∘ₗ indPiMap ρ g ∘ₗ single ℂ (fun _ : RightCosets S => V) q)
      = subgroupExtend S ρ.character (Quotient.out q * g * (Quotient.out q)⁻¹) := by
  have hdiag : (proj q ∘ₗ indPiMap ρ g ∘ₗ single ℂ (fun _ : RightCosets S => V) q)
      = if Quotient.mk (QuotientGroup.rightRel S) (Quotient.out q * g) = q then
          ρ (subgroupPart S (Quotient.out q * g)) else 0 := by
    ext v
    simp only [coe_comp, Function.comp_apply, proj_apply, indPiMap_apply, single_apply]
    by_cases h : Quotient.mk (QuotientGroup.rightRel S) (Quotient.out q * g) = q
    · rw [if_pos h, h, Pi.single_eq_same]
    · rw [if_neg h, Pi.single_eq_of_ne h]; simp
  rw [hdiag]
  by_cases h : Quotient.mk (QuotientGroup.rightRel S) (Quotient.out q * g) = q
  · rw [if_pos h]
    have hout : Quotient.out (Quotient.mk (QuotientGroup.rightRel S) (Quotient.out q * g))
        = Quotient.out q := by rw [h]
    have hkey : (subgroupPart S (Quotient.out q * g) : G)
        = Quotient.out q * g * (Quotient.out q)⁻¹ := by rw [subgroupPart_coe, hout]
    rw [← hkey, subgroupExtend_coe]
    rfl
  · rw [if_neg h, map_zero]
    refine (subgroupExtend_of_notMem _ _ ?_).symm
    intro hmem
    refine h ?_
    conv_rhs => rw [← Quotient.out_eq q]
    refine rightCosets_mk_eq_mk_iff.mpr ?_
    rw [show Quotient.out q * (Quotient.out q * g)⁻¹
      = (Quotient.out q * g * (Quotient.out q)⁻¹)⁻¹ from by group]
    exact S.inv_mem hmem

theorem character_ind_eq_indClassFun [FiniteDimensional ℂ V] [Fintype G] :
    (Representation.ind S.subtype ρ).character = indClassFun S ρ.character := by
  classical
  have hiso : (Representation.ind S.subtype ρ).character
      = (Representation.coind S.subtype ρ).character :=
    Representation.char_iso (Representation.equivOfIso (Rep.indCoindIso (Rep.of ρ)))
  funext g
  rw [hiso]
  have hconj : LinearMap.trace ℂ (Representation.coindV S.subtype ρ)
      (Representation.coind S.subtype ρ g)
      = LinearMap.trace ℂ (RightCosets S → V) (indPiMap ρ g) := by
    rw [← coindEquivPi_conj ρ g, LinearMap.trace_conj']
  rw [Representation.character, hconj, trace_pi_eq_sum_diag,
    indClassFun_eq_sum_rightCosets ρ.character (fun s h => ρ.char_conj h s) g]
  exact Finset.sum_congr rfl fun q _ => trace_diag_indPiMap ρ g q

theorem finrank_indV [FiniteDimensional ℂ V] [Finite G] :
    Module.finrank ℂ (Representation.IndV S.subtype ρ) = S.index * Module.finrank ℂ V := by
  classical
  have : Fintype (RightCosets S) := Fintype.ofFinite _
  have hiso : Module.finrank ℂ (Representation.IndV S.subtype ρ)
      = Module.finrank ℂ (RightCosets S → V) :=
    LinearEquiv.finrank_eq
      ((Representation.equivOfIso (Rep.indCoindIso (Rep.of ρ))).toLinearEquiv.trans
        (coindEquivPi ρ))
  rw [hiso, Module.finrank_pi_fintype ℂ, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, ← Nat.card_eq_fintype_card, card_rightCosets]

theorem character_ind_one [FiniteDimensional ℂ V] [Finite G] :
    (Representation.ind S.subtype ρ).character 1 = (S.index : ℂ) * ρ.character 1 := by
  classical
  have : Fintype G := Fintype.ofFinite _
  rw [character_ind_eq_indClassFun, indClassFun_one]

end CFSG.FeitThompson.InducedCharacterConstruction
