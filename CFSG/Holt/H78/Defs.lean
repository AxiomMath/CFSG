module

public import CFSG.Holt.BenderBasic
public import CFSG.Holt.General.Defs

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Holt.General
open scoped Pointwise

section Defs

variable (G : Type*) [Group G] (Ω : Type*) [MulAction G Ω]

@[expose] def longInv : Set G := {t | orderOf t = 2 ∧ ∃! ω : Ω, t • ω = ω}

@[expose] def longInvAt (α : Ω) : Set G := {t | t ∈ longInv G Ω ∧ t • α = α}

@[expose] def longInvSwap (α β : Ω) : Set G := {t | t ∈ longInv G Ω ∧ t • α = β}

@[expose] def holtDelta (α β : Ω) : Set Ω := {γ | ∃ t ∈ longInvSwap G Ω α β, t • γ = γ}

@[expose] def holtDelta' (α β : Ω) : Set Ω := {γ | ∃ s ∈ longInvAt G Ω α, s • β = γ}

@[expose] def HoltStar : Prop :=
  ∀ (α : Ω) (S : Subgroup G), IsPGroup 2 S → S ≤ stabilizer G α →
    3 ≤ Nat.card (fixSet Ω S) → ∃ t ∈ longInvAt G Ω α, t ∈ Subgroup.centralizer (S : Set G)

structure IsStarGroup : Prop where
  odd_card : Odd (Nat.card Ω)
  three_le_card : 3 ≤ Nat.card Ω
  star : HoltStar G Ω

@[expose] def jHull : Subgroup G := Subgroup.closure (longInv G Ω)

@[expose] def jOddCore : Subgroup G := oddCoreOf (jHull G Ω)

@[expose] def jOrbitKernel : Subgroup G :=
  jHull G Ω ⊓ ⨅ ω : Ω, stabilizer G (orbit (jOddCore G Ω) ω)

@[expose] def factorImage {X : Type*} (L : Subgroup G) (ρ : jHull G Ω →* Equiv.Perm X) :
    Subgroup (Equiv.Perm X) :=
  (L.subgroupOf (jHull G Ω)).map ρ

end Defs

section Factors

variable {Δ : Type*}

@[expose] def IsNaturalSE (M : Subgroup (Equiv.Perm Δ)) : Prop :=
  ∃ q e : ℕ, IsBenderNormal Δ (⊤ : Subgroup M) q e

variable [Fintype Δ] [DecidableEq Δ]

@[expose] def IsHoltFactor (M : Subgroup (Equiv.Perm Δ)) : Prop :=
  (M = alternatingGroup Δ ∧ 7 ≤ Fintype.card Δ) ∨ IsNaturalSE M

@[expose] def IsOuterFactor (M : Subgroup (Equiv.Perm Δ)) : Prop :=
  M = alternatingGroup Δ ∧ Fintype.card Δ % 4 = 3

end Factors

section Mem

variable {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω]

@[simp] theorem mem_longInv {t : G} :
    t ∈ longInv G Ω ↔ orderOf t = 2 ∧ ∃! ω : Ω, t • ω = ω := Iff.rfl

@[simp] theorem mem_longInvAt {t : G} {α : Ω} :
    t ∈ longInvAt G Ω α ↔ t ∈ longInv G Ω ∧ t • α = α := Iff.rfl

@[simp] theorem mem_longInvSwap {t : G} {α β : Ω} :
    t ∈ longInvSwap G Ω α β ↔ t ∈ longInv G Ω ∧ t • α = β := Iff.rfl

@[simp] theorem mem_holtDelta {α β γ : Ω} :
    γ ∈ holtDelta G Ω α β ↔ ∃ t ∈ longInvSwap G Ω α β, t • γ = γ := Iff.rfl

@[simp] theorem mem_holtDelta' {α β γ : Ω} :
    γ ∈ holtDelta' G Ω α β ↔ ∃ s ∈ longInvAt G Ω α, s • β = γ := Iff.rfl

theorem longInv_subset_jHull : longInv G Ω ⊆ jHull G Ω := Subgroup.subset_closure

theorem mem_jHull_of_mem_longInv {t : G} (ht : t ∈ longInv G Ω) : t ∈ jHull G Ω :=
  longInv_subset_jHull ht

theorem mem_jOddCore {g : G} :
    g ∈ jOddCore G Ω ↔ ∃ h : jHull G Ω, h ∈ CFSG.pPrimeCore 2 (jHull G Ω) ∧ (h : G) = g :=
  Subgroup.mem_map

theorem jOddCore_le_jHull : jOddCore G Ω ≤ jHull G Ω := Subgroup.map_subtype_le _

theorem jOddCore_subgroupOf_jHull :
    (jOddCore G Ω).subgroupOf (jHull G Ω) = CFSG.pPrimeCore 2 (jHull G Ω) :=
  Subgroup.comap_map_eq_self_of_injective (jHull G Ω).subtype_injective _

@[simp] theorem mem_jOrbitKernel {g : G} :
    g ∈ jOrbitKernel G Ω ↔
      g ∈ jHull G Ω ∧ ∀ ω : Ω, g • orbit (jOddCore G Ω) ω = orbit (jOddCore G Ω) ω := by
  simp only [jOrbitKernel, Subgroup.mem_inf, Subgroup.mem_iInf, mem_stabilizer_iff]

theorem jOrbitKernel_le_jHull : jOrbitKernel G Ω ≤ jHull G Ω := inf_le_left

@[simp] theorem mem_factorImage {X : Type*} {L : Subgroup G} {ρ : jHull G Ω →* Equiv.Perm X}
    {x : Equiv.Perm X} :
    x ∈ factorImage G Ω L ρ ↔ ∃ h : jHull G Ω, (h : G) ∈ L ∧ ρ h = x := by
  simp only [factorImage, Subgroup.mem_map, Subgroup.mem_subgroupOf]

end Mem

section Data

variable (G : Type*) [Group G] (Ω : Type*) [MulAction G Ω]

structure HoltData where
  ι : Type
  [fintypeι : Fintype ι]
  [decEqι : DecidableEq ι]
  Ψc : ι → Type
  [fintypeΨ : ∀ i, Fintype (Ψc i)]
  [decEqΨ : ∀ i, DecidableEq (Ψc i)]
  coord : Ω → ∀ i, Ψc i
  ρ : ∀ i, jHull G Ω →* Equiv.Perm (Ψc i)
  L : ι → Subgroup G
  t : G
  t_mem : t ∈ longInv G Ω
  coord_eq_iff : ∀ ω ω' : Ω, coord ω = coord ω' ↔ ω' ∈ orbit (jOddCore G Ω) ω
  coord_surjective : Function.Surjective coord
  coord_smul : ∀ (h : jHull G Ω) (ω : Ω) (i : ι), coord ((h : G) • ω) i = ρ i h (coord ω i)
  L_le : ∀ i, L i ≤ jHull G Ω
  oddCore_le : ∀ i, jOddCore G Ω ≤ L i
  le_normalizer : ∀ i, jHull G Ω ≤ Subgroup.normalizer (L i : Set G)
  le_ker : ∀ i j, i ≠ j → (L i).subgroupOf (jHull G Ω) ≤ (ρ j).ker
  inf_ker : ∀ i, (L i).subgroupOf (jHull G Ω) ⊓ (ρ i).ker = (jOddCore G Ω).subgroupOf (jHull G Ω)
  factor : ∀ i, IsHoltFactor (factorImage G Ω (L i) (ρ i))
  sup_eq : jOddCore G Ω ⊔ (⨆ i, L i) ⊔ Subgroup.zpowers t = jHull G Ω
  inner : ∀ i, ¬ IsOuterFactor (factorImage G Ω (L i) (ρ i)) →
    ρ i ⟨t, Subgroup.subset_closure t_mem⟩ ∈ factorImage G Ω (L i) (ρ i)
  ker_outer : (∃ i, IsOuterFactor (factorImage G Ω (L i) (ρ i))) →
    jOrbitKernel G Ω = jOddCore G Ω
  ker_inner : (∀ i, ¬ IsOuterFactor (factorImage G Ω (L i) (ρ i))) →
    t ∈ jOddCore G Ω ⊔ (⨆ i, L i) ⊔ jOrbitKernel G Ω ∧
      (jOddCore G Ω ≠ ⊥ → (jOddCore G Ω).relIndex (jOrbitKernel G Ω) = 2)

attribute [instance] HoltData.fintypeι HoltData.decEqι HoltData.fintypeΨ HoltData.decEqΨ

@[expose] def HoltStructure : Prop := Nonempty (HoltData G Ω)

end Data

@[expose] def HoltTheorem1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Type) [MulAction G Ω] [Finite Ω] [FaithfulSMul G Ω],
    IsStarGroup G Ω → HoltStructure G Ω

@[expose] def HoltTheorem1Below (n d : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Type) [MulAction G Ω] [Finite Ω] [FaithfulSMul G Ω],
    (Nat.card G < n ∨ (Nat.card G = n ∧ Nat.card Ω < d)) → IsStarGroup G Ω → HoltStructure G Ω

section Constructors

variable {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω]

theorem jOrbitKernel_eq_jHull_of_isPretransitive (hO : IsPretransitive (jOddCore G Ω) Ω) :
    jOrbitKernel G Ω = jHull G Ω := by
  refine inf_eq_left.mpr (le_iInf fun ω g _ => ?_)
  rw [mem_stabilizer_iff, orbit_eq_univ, Set.smul_set_univ]

theorem orbit_jOddCore_eq_singleton (hO : jOddCore G Ω = ⊥) (ω : Ω) :
    orbit (jOddCore G Ω) ω = {ω} := by
  ext ω'
  simp only [mem_orbit_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨m, hm⟩, rfl⟩
    rw [hO, Subgroup.mem_bot] at hm
    subst hm
    exact one_smul G ω
  · rintro rfl
    exact ⟨1, one_smul _ _⟩

theorem jOrbitKernel_eq_bot [FaithfulSMul G Ω] (hO : jOddCore G Ω = ⊥) :
    jOrbitKernel G Ω = ⊥ := by
  refine eq_bot_iff.mpr fun g hg => ?_
  rw [Subgroup.mem_bot]
  refine eq_of_smul_eq_smul (α := Ω) fun ω => ?_
  have h := (mem_jOrbitKernel.mp hg).2 ω
  rw [orbit_jOddCore_eq_singleton hO, Set.smul_set_singleton,
    Set.singleton_eq_singleton_iff] at h
  rw [h, one_smul]

theorem relIndex_jOddCore_jHull_eq_two [Finite G] {t : G} (ht : orderOf t = 2)
    (hH : jHull G Ω = jOddCore G Ω ⊔ Subgroup.zpowers t) :
    (jOddCore G Ω).relIndex (jHull G Ω) = 2 := by
  have htH : t ∈ jHull G Ω := hH ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have : (CFSG.pPrimeCore 2 (jHull G Ω)).Normal := CFSG.pPrimeCore_normal
  have hsup : CFSG.pPrimeCore 2 (jHull G Ω) ⊔ Subgroup.zpowers ⟨t, htH⟩ = ⊤ := by
    apply Subgroup.map_injective (jHull G Ω).subtype_injective
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
    exact hH.symm
  have hcop : Nat.Coprime (Nat.card (CFSG.pPrimeCore 2 (jHull G Ω)))
      (Nat.card (Subgroup.zpowers (⟨t, htH⟩ : jHull G Ω))) := by
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, ht]
    exact CFSG.pPrimeCore_coprime_card.symm
  rw [Subgroup.relIndex, jOddCore_subgroupOf_jHull, ← Subgroup.relIndex_top_right, ← hsup,
    Subgroup.relIndex_sup_left, ← Subgroup.inf_relIndex_right,
    disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard hcop), Subgroup.relIndex_bot_left,
    Nat.card_zpowers, Subgroup.orderOf_mk, ht]

@[expose] def HoltData.ofIsPretransitive [Finite G] {t : G} (ht : t ∈ longInv G Ω)
    (hO : IsPretransitive (jOddCore G Ω) Ω)
    (hH : jHull G Ω = jOddCore G Ω ⊔ Subgroup.zpowers t) : HoltData G Ω where
  ι := Empty
  Ψc := Empty.elim
  fintypeΨ i := i.elim
  decEqΨ i := i.elim
  coord _ i := i.elim
  ρ i := i.elim
  L := Empty.elim
  t := t
  t_mem := ht
  coord_eq_iff ω ω' := by
    refine ⟨fun _ => ?_, fun _ => funext fun i => i.elim⟩
    rw [orbit_eq_univ]
    exact Set.mem_univ ω'
  coord_surjective _ := by
    obtain ⟨ω, -⟩ := ht.2
    exact ⟨ω, funext fun i => i.elim⟩
  coord_smul _ _ i := i.elim
  L_le i := i.elim
  oddCore_le i := i.elim
  le_normalizer i := i.elim
  le_ker i := i.elim
  inf_ker i := i.elim
  factor i := i.elim
  sup_eq := by rw [iSup_of_empty, sup_bot_eq, hH]
  inner i := i.elim
  ker_outer h := by
    obtain ⟨i, -⟩ := h
    exact i.elim
  ker_inner _ := by
    rw [jOrbitKernel_eq_jHull_of_isPretransitive hO]
    exact ⟨Subgroup.mem_sup_right (mem_jHull_of_mem_longInv ht),
      fun _ => relIndex_jOddCore_jHull_eq_two ht.1 hH⟩

end Constructors

section ConstructorFactor

variable {G : Type*} [Group G] {Ω : Type} [MulAction G Ω]

@[expose] def HoltData.ofFactor [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] {t : G}
    (ht : t ∈ longInv G Ω) (hO : jOddCore G Ω = ⊥) (L : Subgroup G) (hL : L ≤ jHull G Ω)
    (hLN : jHull G Ω ≤ Subgroup.normalizer (L : Set G))
    (hsup : L ⊔ Subgroup.zpowers t = jHull G Ω)
    (hfac : IsHoltFactor (factorImage G Ω L ((toPermHom G Ω).comp (jHull G Ω).subtype)))
    (hinner : ¬ IsOuterFactor (factorImage G Ω L ((toPermHom G Ω).comp (jHull G Ω).subtype)) →
      t ∈ L) :
    HoltData G Ω where
  ι := Unit
  Ψc _ := Ω
  coord ω _ := ω
  ρ _ := (toPermHom G Ω).comp (jHull G Ω).subtype
  L _ := L
  t := t
  t_mem := ht
  coord_eq_iff ω ω' := by
    rw [orbit_jOddCore_eq_singleton hO, Set.mem_singleton_iff]
    exact ⟨fun h => (congrFun h ()).symm, fun h => funext fun _ => h.symm⟩
  coord_surjective f := ⟨f (), rfl⟩
  coord_smul _ _ _ := rfl
  L_le _ := hL
  oddCore_le _ := hO ▸ bot_le
  le_normalizer _ := hLN
  le_ker i j hij := (hij (Subsingleton.elim i j)).elim
  inf_ker _ := by
    have hinj : Function.Injective ((toPermHom G Ω).comp (jHull G Ω).subtype) := fun a b hab =>
      Subtype.ext (eq_of_smul_eq_smul fun ω => congrArg (fun π : Equiv.Perm Ω => π ω) hab)
    rw [hO, Subgroup.bot_subgroupOf, (MonoidHom.ker_eq_bot_iff _).mpr hinj, inf_bot_eq]
  factor _ := hfac
  sup_eq := by rw [hO, bot_sup_eq, iSup_const, hsup]
  inner _ hn := Subgroup.mem_map.mpr ⟨⟨t, mem_jHull_of_mem_longInv ht⟩, hinner hn, rfl⟩
  ker_outer _ := by rw [jOrbitKernel_eq_bot hO, hO]
  ker_inner hn := ⟨Subgroup.mem_sup_left (Subgroup.mem_sup_right
      (Subgroup.mem_iSup_of_mem () (hinner (hn ())))), fun h => (h hO).elim⟩

end ConstructorFactor

end CFSG.Holt.H78
