module

public import CFSG.Open.LocalVocabulary

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.AGLEmbedding.A9Local

open Equiv CFSG.Open

abbrev Pt : Type := ZMod 3 × ZMod 3

theorem zmod_three_add_self (a : ZMod 3) : a + a + a = 0 := by revert a; decide

@[expose] def shiftPerm (f : ZMod 3 → ZMod 3) : Perm Pt where
  toFun p := (p.1, p.2 + f p.1)
  invFun p := (p.1, p.2 - f p.1)
  left_inv p := by simp
  right_inv p := by simp

@[simp] theorem shiftPerm_apply (f : ZMod 3 → ZMod 3) (p : Pt) :
    shiftPerm f p = (p.1, p.2 + f p.1) := rfl

@[simp] theorem shiftPerm_symm_apply (f : ZMod 3 → ZMod 3) (p : Pt) :
    (shiftPerm f).symm p = (p.1, p.2 - f p.1) := rfl

theorem shiftPerm_add (f g : ZMod 3 → ZMod 3) :
    shiftPerm (f + g) = shiftPerm f * shiftPerm g := by
  ext p <;> simp [add_comm, add_left_comm]

theorem shiftPerm_zero : shiftPerm 0 = 1 := by
  ext p <;> simp

theorem shiftPerm_injective : Function.Injective shiftPerm := by
  intro f g h
  funext i
  have := congrArg (fun σ : Perm Pt => (σ (i, 0)).2) h
  simpa using this

@[expose] def shiftHom : Multiplicative (ZMod 3 → ZMod 3) →* Perm Pt where
  toFun f := shiftPerm (Multiplicative.toAdd f)
  map_one' := shiftPerm_zero
  map_mul' _ _ := shiftPerm_add _ _

@[expose] def baseGroup : Subgroup (Perm Pt) := shiftHom.range

theorem mem_baseGroup_iff {g : Perm Pt} : g ∈ baseGroup ↔ ∃ f, g = shiftPerm f := by
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨Multiplicative.toAdd f, rfl⟩
  · rintro ⟨f, rfl⟩
    exact ⟨Multiplicative.ofAdd f, rfl⟩

theorem shiftPerm_mem_baseGroup (f : ZMod 3 → ZMod 3) : shiftPerm f ∈ baseGroup :=
  mem_baseGroup_iff.2 ⟨f, rfl⟩

theorem card_baseGroup : Nat.card baseGroup = 27 := by
  have hinj : Function.Injective shiftHom := fun f g h => by
    exact Multiplicative.toAdd.injective (shiftPerm_injective h)
  rw [baseGroup, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  simp [Nat.card_eq_fintype_card]

theorem isElemAbelian_baseGroup : IsElemAbelian 3 baseGroup := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨f, hf⟩ := mem_baseGroup_iff.1 a.2
    obtain ⟨g, hg⟩ := mem_baseGroup_iff.1 b.2
    apply Subtype.ext
    change (a : Perm Pt) * b = b * a
    rw [hf, hg, ← shiftPerm_add, ← shiftPerm_add, add_comm]
  · obtain ⟨f, rfl⟩ := mem_baseGroup_iff.1 hx
    rw [pow_succ, pow_two, ← shiftPerm_add, ← shiftPerm_add, ← shiftPerm_zero]
    congr 1
    funext i
    exact zmod_three_add_self (f i)

@[expose] def affPerm (l : ZMod 3) (f : ZMod 3 → ZMod 3) : Perm Pt where
  toFun p := (p.1 + l, p.2 + f p.1)
  invFun p := (p.1 - l, p.2 - f (p.1 - l))
  left_inv p := by simp
  right_inv p := by simp

@[simp] theorem affPerm_apply (l : ZMod 3) (f : ZMod 3 → ZMod 3) (p : Pt) :
    affPerm l f p = (p.1 + l, p.2 + f p.1) := rfl

@[simp] theorem affPerm_symm_apply (l : ZMod 3) (f : ZMod 3 → ZMod 3) (p : Pt) :
    (affPerm l f).symm p = (p.1 - l, p.2 - f (p.1 - l)) := rfl

theorem affPerm_mul (l l' : ZMod 3) (f f' : ZMod 3 → ZMod 3) :
    affPerm l f * affPerm l' f' = affPerm (l + l') (fun i => f' i + f (i + l')) := by
  ext p <;> simp [add_comm, add_left_comm]

theorem affPerm_zero_left (f : ZMod 3 → ZMod 3) : affPerm 0 f = shiftPerm f := by
  ext p <;> simp

theorem affPerm_one : affPerm 0 0 = 1 := by
  ext p <;> simp

theorem affPerm_inv (l : ZMod 3) (f : ZMod 3 → ZMod 3) :
    (affPerm l f)⁻¹ = affPerm (-l) (fun i => - f (i - l)) := by
  ext p <;> simp [Perm.inv_def, sub_eq_add_neg]

theorem affPerm_injective :
    Function.Injective (fun x : ZMod 3 × (ZMod 3 → ZMod 3) => affPerm x.1 x.2) := by
  rintro ⟨l, f⟩ ⟨l', f'⟩ h
  have h0 := congrArg (fun σ : Perm Pt => σ (0, 0)) h
  simp only [affPerm_apply, zero_add, Prod.mk.injEq] at h0
  obtain ⟨rfl, -⟩ := h0
  refine Prod.ext rfl (funext fun i => ?_)
  have hi := congrArg (fun σ : Perm Pt => σ (i, 0)) h
  simpa using hi

@[expose] def sylowT : Subgroup (Perm Pt) where
  carrier := {g | ∃ (l : ZMod 3) (f : ZMod 3 → ZMod 3), g = affPerm l f}
  one_mem' := ⟨0, 0, affPerm_one.symm⟩
  mul_mem' := by
    rintro _ _ ⟨l, f, rfl⟩ ⟨l', f', rfl⟩
    exact ⟨_, _, affPerm_mul l l' f f'⟩
  inv_mem' := by
    rintro _ ⟨l, f, rfl⟩
    exact ⟨_, _, affPerm_inv l f⟩

theorem affPerm_mem_sylowT (l : ZMod 3) (f : ZMod 3 → ZMod 3) : affPerm l f ∈ sylowT :=
  ⟨l, f, rfl⟩

theorem baseGroup_le_sylowT : baseGroup ≤ sylowT := by
  intro g hg
  obtain ⟨f, rfl⟩ := mem_baseGroup_iff.1 hg
  exact ⟨0, f, (affPerm_zero_left f).symm⟩

theorem card_sylowT : Nat.card sylowT = 81 := by
  have h : (sylowT : Set (Perm Pt)) =
      Set.range (fun x : ZMod 3 × (ZMod 3 → ZMod 3) => affPerm x.1 x.2) := by
    ext g
    constructor
    · rintro ⟨l, f, rfl⟩
      exact ⟨(l, f), rfl⟩
    · rintro ⟨⟨l, f⟩, rfl⟩
      exact ⟨l, f, rfl⟩
  change Nat.card (sylowT : Set (Perm Pt)) = 81
  rw [h, Nat.card_range_of_injective affPerm_injective]
  simp [Nat.card_eq_fintype_card]

theorem isPGroup_sylowT : IsPGroup 3 sylowT := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact IsPGroup.of_card (n := 4) (by rw [card_sylowT]; norm_num)

@[expose] def blockShift : Perm Pt := affPerm 1 0

@[expose] def signAt (k : ZMod 3) : Perm Pt where
  toFun p := (p.1, if p.1 = k then p.2 else -p.2)
  invFun p := (p.1, if p.1 = k then p.2 else -p.2)
  left_inv := fun ⟨i, z⟩ => by by_cases h : i = k <;> simp [h]
  right_inv := fun ⟨i, z⟩ => by by_cases h : i = k <;> simp [h]

@[simp] theorem signAt_apply (k : ZMod 3) (p : Pt) :
    signAt k p = (p.1, if p.1 = k then p.2 else -p.2) := rfl

theorem signAt_inv (k : ZMod 3) : (signAt k)⁻¹ = signAt k := by
  ext p <;> simp [Perm.inv_def, signAt]

theorem signAt_conj_shiftPerm (k : ZMod 3) (f : ZMod 3 → ZMod 3) :
    signAt k * shiftPerm f * (signAt k)⁻¹ = shiftPerm (fun i => if i = k then f i else - f i) := by
  rw [signAt_inv]
  ext p
  · simp
  · by_cases h : p.1 = k <;> simp [h, add_comm]

theorem blockShift_conj_shiftPerm (f : ZMod 3 → ZMod 3) :
    blockShift * shiftPerm f * blockShift⁻¹ = shiftPerm (fun i => f (i - 1)) := by
  ext p <;> simp [blockShift, Perm.inv_def]

theorem blockShift_inv_conj_shiftPerm (f : ZMod 3 → ZMod 3) :
    blockShift⁻¹ * shiftPerm f * blockShift = shiftPerm (fun i => f (i + 1)) := by
  ext p <;> simp [blockShift, Perm.inv_def]

theorem affPerm_conj_shiftPerm (l : ZMod 3) (f g : ZMod 3 → ZMod 3) :
    affPerm l f * shiftPerm g * (affPerm l f)⁻¹ = shiftPerm (fun i => g (i - l)) := by
  ext p
  · simp [Perm.inv_def]
  · simp only [Perm.mul_apply, Perm.inv_def, affPerm_symm_apply, shiftPerm_apply, affPerm_apply,
      sub_add_cancel]
    ring

theorem affPerm_inv_conj_shiftPerm (l : ZMod 3) (f g : ZMod 3 → ZMod 3) :
    (affPerm l f)⁻¹ * shiftPerm g * affPerm l f = shiftPerm (fun i => g (i + l)) := by
  have h := affPerm_conj_shiftPerm (-l) (fun i => - f (i - l)) g
  rw [← affPerm_inv] at h
  simpa [sub_neg_eq_add] using h

abbrev nrm : Subgroup (Perm Pt) := Subgroup.normalizer (baseGroup : Set (Perm Pt))

theorem mem_nrm_of_conj {g : Perm Pt}
    (h : ∀ f, ∃ f', g * shiftPerm f * g⁻¹ = shiftPerm f')
    (h' : ∀ f, ∃ f', g⁻¹ * shiftPerm f * g = shiftPerm f') : g ∈ nrm := by
  rw [Subgroup.mem_set_normalizer_iff]
  intro n
  simp only [SetLike.mem_coe, mem_baseGroup_iff]
  constructor
  · rintro ⟨f, rfl⟩
    exact h f
  · rintro ⟨f, hf⟩
    obtain ⟨f', hf'⟩ := h' f
    refine ⟨f', ?_⟩
    calc n = g⁻¹ * (g * n * g⁻¹) * g := by group
      _ = g⁻¹ * shiftPerm f * g := by rw [hf]
      _ = shiftPerm f' := hf'

theorem baseGroup_le_nrm : baseGroup ≤ nrm := Subgroup.le_normalizer

theorem sylowT_le_nrm : sylowT ≤ nrm := by
  rintro _ ⟨l, f, rfl⟩
  exact mem_nrm_of_conj (fun g => ⟨_, affPerm_conj_shiftPerm l f g⟩)
    (fun g => ⟨_, affPerm_inv_conj_shiftPerm l f g⟩)

theorem signAt_mem_nrm (k : ZMod 3) : signAt k ∈ nrm :=
  mem_nrm_of_conj (fun f => ⟨_, signAt_conj_shiftPerm k f⟩)
    (fun f => ⟨_, by rw [signAt_inv]; exact signAt_conj_shiftPerm k f⟩)

theorem blockShift_mem_nrm : blockShift ∈ nrm :=
  mem_nrm_of_conj (fun f => ⟨_, blockShift_conj_shiftPerm f⟩)
    (fun f => ⟨_, blockShift_inv_conj_shiftPerm f⟩)

theorem mem_alternatingGroup_of_pow_eq_one {α : Type*} [Fintype α] [DecidableEq α]
    {g : Perm α} {n : ℕ} (hn : Odd n) (h : g ^ n = 1) : g ∈ alternatingGroup α := by
  rw [Perm.mem_alternatingGroup]
  have h1 : Perm.sign g ^ n = 1 := by rw [← map_pow, h, map_one]
  rcases Int.units_eq_one_or (Perm.sign g) with h2 | h2
  · exact h2
  · rw [h2, hn.neg_one_pow] at h1
    exact absurd h1 (by decide)

theorem signAt_mem_alternatingGroup (k : ZMod 3) : signAt k ∈ alternatingGroup Pt := by
  rw [Perm.mem_alternatingGroup]
  revert k
  decide +kernel

theorem blockShift_mem_alternatingGroup : blockShift ∈ alternatingGroup Pt := by
  rw [Perm.mem_alternatingGroup]
  decide +kernel

theorem baseGroup_le_alternatingGroup : baseGroup ≤ alternatingGroup Pt := by
  intro g hg
  have := isElemAbelian_baseGroup.2 g hg
  exact mem_alternatingGroup_of_pow_eq_one (n := 3) (by decide) this

theorem sylowT_le_alternatingGroup : sylowT ≤ alternatingGroup Pt := by
  intro g hg
  obtain ⟨k, hk⟩ := isPGroup_sylowT ⟨g, hg⟩
  have : g ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
  exact mem_alternatingGroup_of_pow_eq_one (Odd.pow (by decide)) this

end CFSG.AGLEmbedding.A9Local
