module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.Data
public import CFSG.Quasithin.Background.SmithB42D4Pure
public import CFSG.LieType.Chevalley.TrialityCover
public import CFSG.LieType.Chevalley.EvenTrialityAutomorphismNormalForm
public import CFSG.LieType.Chevalley.TrialityExactFiniteOrder
public import CFSG.RankThree.PartOne.Q1327T.Item7D4W
public import CFSG.LieType.Chevalley.DiagonalFieldActorData
public import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4
open scoped commutatorElement

namespace Model

section Group

variable {G : Type*} [Group G]

theorem inv_four_eq {a₃ a₄ a₅ a₆ z : G} (h3 : a₃ * a₃ = 1) (h4 : a₄ * a₄ = 1)
    (h5 : a₅ * a₅ = 1) (h6 : a₆ * a₆ = 1) (hz2 : z * z = 1) (hz : ⁅a₃, a₄⁆ = z)
    (c35 : Commute a₃ a₅) (c36 : Commute a₃ a₆) (c45 : Commute a₄ a₅) (c46 : Commute a₄ a₆)
    (c56 : Commute a₅ a₆) (c5z : Commute a₅ z) (c6z : Commute a₆ z) :
    (a₃ * a₄ * a₅ * a₆)⁻¹ = a₃ * a₄ * a₅ * (a₆ * z) := by
  have i3 : a₃⁻¹ = a₃ := inv_eq_of_mul_eq_one_right h3
  have i4 : a₄⁻¹ = a₄ := inv_eq_of_mul_eq_one_right h4
  have i5 : a₅⁻¹ = a₅ := inv_eq_of_mul_eq_one_right h5
  have i6 : a₆⁻¹ = a₆ := inv_eq_of_mul_eq_one_right h6
  have hz' : z = a₃ * a₄ * a₃ * a₄ := by rw [← hz, commutatorElement_def, i3, i4]
  have key : a₄ * a₃ = a₃ * a₄ * z := by
    have h1 : a₃ * a₄ * z * (a₃ * a₄) = 1 := by
      rw [← hz2, hz']
      group
    rw [eq_inv_of_mul_eq_one_left h1, mul_inv_rev, i3, i4]
  have hPQ : Commute (a₆ * a₅) (a₄ * a₃) :=
    (c46.symm.mul_right c36.symm).mul_left (c45.symm.mul_right c35.symm)
  have hz56 : Commute z (a₅ * a₆) := c5z.symm.mul_right c6z.symm
  calc (a₃ * a₄ * a₅ * a₆)⁻¹ = a₆ * a₅ * (a₄ * a₃) := by
        rw [mul_inv_rev, mul_inv_rev, mul_inv_rev, i3, i4, i5, i6]
        group
    _ = a₄ * a₃ * (a₆ * a₅) := hPQ.eq
    _ = a₃ * a₄ * z * (a₅ * a₆) := by rw [key, c56.symm.eq]
    _ = a₃ * a₄ * (a₅ * a₆) * z := by rw [mul_assoc (a₃ * a₄) z, hz56.eq, ← mul_assoc]
    _ = a₃ * a₄ * a₅ * (a₆ * z) := by group

end Group

section Roots

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K)

local notation "C₀" => graphFixedRootGroup TwistTag.D4 K σ.toRingHom
local notation "GL" => ModGL TwistTag.D4.tag K

@[expose] def cx₁
    (hσ : σ.toRingHom ^ 3 = 1) (c : K) : C₀ :=
  ⟨ox₁ σ c, graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _ ((ox_data σ hσ).2.1.1 c)⟩

@[expose] def cx₂
    (hσ : σ.toRingHom ^ 3 = 1) (c : fixedSubfield σ) : C₀ :=
  ⟨ox₂ σ c, graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _ ((ox_data σ hσ).2.1.2.1 c)⟩

@[expose] def cx₃
    (hσ : σ.toRingHom ^ 3 = 1) (c : K) : C₀ :=
  ⟨ox₃ σ c, graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
    ((ox_data σ hσ).2.1.2.2.1 c)⟩

@[expose] def cx₄
    (hσ : σ.toRingHom ^ 3 = 1) (c : K) : C₀ :=
  ⟨ox₄ σ c, graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
    ((ox_data σ hσ).2.1.2.2.2.1 c)⟩

@[expose] def cx₅
    (hσ : σ.toRingHom ^ 3 = 1) (c : fixedSubfield σ) : C₀ :=
  ⟨ox₅ σ c, graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
    ((ox_data σ hσ).2.1.2.2.2.2.1 c)⟩

@[expose] def cx₆
    (hσ : σ.toRingHom ^ 3 = 1) (c : fixedSubfield σ) : C₀ :=
  ⟨ox₆ σ c, graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
    ((ox_data σ hσ).2.1.2.2.2.2.2 c)⟩

end Roots

section Relations

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ : σ.toRingHom ^ 3 = 1)

omit [Finite K] [CharP K 2] in
include hσ in
theorem cube (c : K) : σ (σ (σ c)) = c :=
  ringHom_apply_apply_apply_of_pow_three hσ c

theorem val_eq_of_eq {α : Type*} {p : α → Prop} {a b : Subtype p} (h : a = b) : a.val = b.val :=
  congrArg Subtype.val h

theorem cx₁_add
    (c d : K) : cx₁ σ hσ (c + d) = cx₁ σ hσ c * cx₁ σ hσ d :=
  Subtype.ext (val_eq_of_eq ((ox_data σ hσ).1.1 c d) :)

theorem cx₂_add
    (c d : fixedSubfield σ) : cx₂ σ hσ (c + d) = cx₂ σ hσ c * cx₂ σ hσ d :=
  Subtype.ext (val_eq_of_eq ((ox_data σ hσ).1.2.1 c d) :)

theorem cx₃_add
    (c d : K) : cx₃ σ hσ (c + d) = cx₃ σ hσ c * cx₃ σ hσ d :=
  Subtype.ext (val_eq_of_eq ((ox_data σ hσ).1.2.2.1 c d) :)

theorem cx₄_add
    (c d : K) : cx₄ σ hσ (c + d) = cx₄ σ hσ c * cx₄ σ hσ d :=
  Subtype.ext (val_eq_of_eq ((ox_data σ hσ).1.2.2.2.1 c d) :)

theorem cx₅_add
    (c d : fixedSubfield σ) : cx₅ σ hσ (c + d) = cx₅ σ hσ c * cx₅ σ hσ d :=
  Subtype.ext (val_eq_of_eq ((ox_data σ hσ).1.2.2.2.2.1 c d) :)

theorem cx₆_add
    (c d : fixedSubfield σ) : cx₆ σ hσ (c + d) = cx₆ σ hσ c * cx₆ σ hσ d :=
  Subtype.ext (val_eq_of_eq ((ox_data σ hσ).1.2.2.2.2.2 c d) :)

theorem cx₁_injective
    : Function.Injective (cx₁ σ hσ) := fun _ _ h =>
  (ox_data σ hσ).2.2.1 (Subtype.ext (val_eq_of_eq h :))

theorem cx₂_injective
    : Function.Injective (cx₂ σ hσ) := fun _ _ h =>
  (ox_data σ hσ).2.2.2.1 (Subtype.ext (val_eq_of_eq h :))

theorem cx₃_injective
    : Function.Injective (cx₃ σ hσ) := fun _ _ h =>
  (ox_data σ hσ).2.2.2.2.1 (Subtype.ext (val_eq_of_eq h :))

theorem cx₄_injective
    : Function.Injective (cx₄ σ hσ) := fun _ _ h =>
  (ox_data σ hσ).2.2.2.2.2.1 (Subtype.ext (val_eq_of_eq h :))

theorem cx₅_injective
    : Function.Injective (cx₅ σ hσ) := fun _ _ h =>
  (ox_data σ hσ).2.2.2.2.2.2.1 (Subtype.ext (val_eq_of_eq h :))

theorem cx₆_injective
    : Function.Injective (cx₆ σ hσ) := fun _ _ h =>
  (ox_data σ hσ).2.2.2.2.2.2.2 (Subtype.ext (val_eq_of_eq h :))

theorem cx_comm₁₄
    (s t : K) :
    ⁅cx₁ σ hσ s, cx₄ σ hσ t⁆ = cx₅ σ hσ (fixedTrace (cube σ hσ) (s * t)) :=
  Subtype.ext (val_eq_of_eq ((even_triality_trace_commutators K σ.toRingHom hσ).1 s t) :)

theorem cx_comm₃₄
    (s t : K) :
    ⁅cx₃ σ hσ s, cx₄ σ hσ t⁆ = cx₆ σ hσ (fixedTrace (cube σ hσ) (s * t)) :=
  Subtype.ext (val_eq_of_eq ((even_triality_trace_commutators K σ.toRingHom hσ).2.1 s t) :)

theorem cx_comm₂₅
    (b e : fixedSubfield σ) :
    ⁅cx₂ σ hσ b, cx₅ σ hσ e⁆ = cx₆ σ hσ (b * e) :=
  Subtype.ext (val_eq_of_eq
    ((even_triality_trace_commutators K σ.toRingHom hσ).2.2.1 b e) :)

theorem cx_comm₁₃
    (s t : K) :
    ⁅cx₁ σ hσ s, cx₃ σ hσ t⁆ = cx₄ σ hσ (σ s * σ (σ t) + σ (σ s) * σ t) *
      cx₅ σ hσ (fixedTrace (cube σ hσ) (s * σ s * σ (σ t))) *
        cx₆ σ hσ (fixedTrace (cube σ hσ) (s * σ t * σ (σ t))) :=
  Subtype.ext (CFSG.Quasithin.B42D4.ox₁_comm_ox₃ σ hσ s t)

theorem cx_comm₂₁
    (β : fixedSubfield σ) (s : K) :
    ⁅cx₂ σ hσ β, cx₁ σ hσ s⁆ = cx₃ σ hσ (β * s) * cx₄ σ hσ (β * (σ s * σ (σ s))) *
      cx₅ σ hσ (β * fixedNorm (cube σ hσ) s) * cx₆ σ hσ (β * β * fixedNorm (cube σ hσ) s) :=
  Subtype.ext (CFSG.Quasithin.B42D4.ox₂_comm_ox₁_gen σ hσ β s)

theorem cx_commute₁₅
    (a : K) (b : fixedSubfield σ) : Commute (cx₁ σ hσ a) (cx₅ σ hσ b) :=
  Subtype.ext (val_eq_of_eq
    ((even_triality_trace_commutators K σ.toRingHom hσ).2.2.2.1 a b).eq :)

theorem cx_commute₁₆
    (a : K) (b : fixedSubfield σ) : Commute (cx₁ σ hσ a) (cx₆ σ hσ b) :=
  Subtype.ext (val_eq_of_eq
    ((even_triality_trace_commutators K σ.toRingHom hσ).2.2.2.2.1 a b).eq :)

theorem cx_commute₂₃
    (a : fixedSubfield σ) (b : K) : Commute (cx₂ σ hσ a) (cx₃ σ hσ b) :=
  Subtype.ext (val_eq_of_eq
    ((even_triality_trace_commutators K σ.toRingHom hσ).2.2.2.2.2.1 a b).eq :)

theorem cx_commute₂₄
    (a : fixedSubfield σ) (b : K) : Commute (cx₂ σ hσ a) (cx₄ σ hσ b) :=
  Subtype.ext (val_eq_of_eq
    ((even_triality_trace_commutators K σ.toRingHom hσ).2.2.2.2.2.2.1 a b).eq :)

theorem cx_commute₂₆
    (a b : fixedSubfield σ) : Commute (cx₂ σ hσ a) (cx₆ σ hσ b) :=
  Subtype.ext (val_eq_of_eq
    ((even_triality_trace_commutators K σ.toRingHom hσ).2.2.2.2.2.2.2.1 a b).eq :)

theorem cx_commute₃₅
    (a : K) (b : fixedSubfield σ) : Commute (cx₃ σ hσ a) (cx₅ σ hσ b) :=
  Subtype.ext (val_eq_of_eq
    ((even_triality_trace_commutators K σ.toRingHom hσ).2.2.2.2.2.2.2.2.1 a b).eq :)

theorem cx_commute₃₆
    (a : K) (b : fixedSubfield σ) : Commute (cx₃ σ hσ a) (cx₆ σ hσ b) :=
  Subtype.ext (val_eq_of_eq
    ((even_triality_trace_commutators K σ.toRingHom hσ).2.2.2.2.2.2.2.2.2.1 a b).eq :)

theorem cx_commute₄₅
    (a : K) (b : fixedSubfield σ) : Commute (cx₄ σ hσ a) (cx₅ σ hσ b) :=
  Subtype.ext (val_eq_of_eq
    ((even_triality_trace_commutators K σ.toRingHom hσ).2.2.2.2.2.2.2.2.2.2.1 a b).eq :)

theorem cx_commute₄₆
    (a : K) (b : fixedSubfield σ) : Commute (cx₄ σ hσ a) (cx₆ σ hσ b) :=
  Subtype.ext (val_eq_of_eq
    ((even_triality_trace_commutators K σ.toRingHom hσ).2.2.2.2.2.2.2.2.2.2.2.1 a b).eq :)

theorem cx_commute₅₆
    (a b : fixedSubfield σ) : Commute (cx₅ σ hσ a) (cx₆ σ hσ b) :=
  Subtype.ext (val_eq_of_eq
    ((even_triality_trace_commutators K σ.toRingHom hσ).2.2.2.2.2.2.2.2.2.2.2.2.1 a b).eq :)

theorem mul_self_of_add {G A : Type*} [Group G] [AddGroup A] {x : A → G}
    (hx : ∀ a b, x (a + b) = x a * x b) (h2 : ∀ a : A, a + a = 0) (a : A) : x a * x a = 1 := by
  rw [← hx, h2, map_zero_of_add hx]

omit [Finite K] in
theorem fixed_add_self (a : fixedSubfield σ) : a + a = 0 :=
  Subtype.ext (CharTwo.add_self_eq_zero (a : K))

omit [Finite K] in
include hσ in
theorem norm_add_trace_eq_zero (β : fixedSubfield σ) (s : K) :
    β * β * fixedNorm (cube σ hσ) s +
      fixedTrace (cube σ hσ) (β * s * (β * (σ s * σ (σ s)))) = 0 := by
  have hβ : σ (β : K) = β := β.2
  have h3 := cube σ hσ s
  apply Subtype.ext
  change (β : K) * β * (s * σ s * σ (σ s)) +
    ((β * s * (β * (σ s * σ (σ s)))) + σ (β * s * (β * (σ s * σ (σ s)))) +
      σ (σ (β * s * (β * (σ s * σ (σ s)))))) = 0
  simp only [map_mul, hβ, h3]
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  linear_combination (2 * ((β : K) * β * (s * σ s * σ (σ s)))) * h2

theorem cx_commute₆₆
    (a b : fixedSubfield σ) : Commute (cx₆ σ hσ a) (cx₆ σ hσ b) := by
  change cx₆ σ hσ a * cx₆ σ hσ b = cx₆ σ hσ b * cx₆ σ hσ a
  rw [← cx₆_add, ← cx₆_add, add_comm]

theorem cx_comm₁₂
    (s : K) (β : fixedSubfield σ) :
    ⁅cx₁ σ hσ s, cx₂ σ hσ β⁆ = cx₃ σ hσ (s * β) * cx₄ σ hσ (σ s * σ (σ s) * β) *
      cx₅ σ hσ (fixedNorm (cube σ hσ) s * β) := by
  have h2K : ∀ a : K, a + a = 0 := fun a => CharTwo.add_self_eq_zero a
  have hinv := inv_four_eq (a₃ := cx₃ σ hσ (β * s)) (a₄ := cx₄ σ hσ (β * (σ s * σ (σ s))))
    (a₅ := cx₅ σ hσ (β * fixedNorm (cube σ hσ) s))
    (a₆ := cx₆ σ hσ (β * β * fixedNorm (cube σ hσ) s))
    (z := cx₆ σ hσ (fixedTrace (cube σ hσ) (β * s * (β * (σ s * σ (σ s))))))
    (mul_self_of_add (cx₃_add σ hσ) h2K _) (mul_self_of_add (cx₄_add σ hσ) h2K _)
    (mul_self_of_add (cx₅_add σ hσ) (fixed_add_self σ) _)
    (mul_self_of_add (cx₆_add σ hσ) (fixed_add_self σ) _)
    (mul_self_of_add (cx₆_add σ hσ) (fixed_add_self σ) _) (cx_comm₃₄ σ hσ _ _)
    (cx_commute₃₅ σ hσ _ _) (cx_commute₃₆ σ hσ _ _) (cx_commute₄₅ σ hσ _ _)
    (cx_commute₄₆ σ hσ _ _) (cx_commute₅₆ σ hσ _ _) (cx_commute₅₆ σ hσ _ _)
    (cx_commute₆₆ σ hσ _ _)
  rw [← commutatorElement_inv, cx_comm₂₁, hinv, ← cx₆_add, norm_add_trace_eq_zero σ hσ,
    map_zero_of_add (cx₆_add σ hσ), mul_one, mul_comm (β : K) s, mul_comm (β : K), mul_comm β]

end Relations

section NormalForm

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ : σ.toRingHom ^ 3 = 1)

local notation "C₀" => graphFixedRootGroup TwistTag.D4 K σ.toRingHom

theorem sixClosure_eq
    : sixClosure (cx₁ σ hσ) (cx₂ σ hσ) (cx₃ σ hσ) (cx₄ σ hσ) (cx₅ σ hσ) (cx₆ σ hσ) =
      (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf C₀ := by
  have hB := (even_triality_positive_orbit_parametrization K σ hσ).2.2.2.2.2.2.1
  apply le_antisymm
  · rw [sixClosure, Subgroup.closure_le]
    rintro g (((((⟨c, rfl⟩ | ⟨c, rfl⟩) | ⟨c, rfl⟩) | ⟨c, rfl⟩) | ⟨c, rfl⟩) | ⟨c, rfl⟩)
    · exact (ox_data σ hσ).2.1.1 c
    · exact (ox_data σ hσ).2.1.2.1 c
    · exact (ox_data σ hσ).2.1.2.2.1 c
    · exact (ox_data σ hσ).2.1.2.2.2.1 c
    · exact (ox_data σ hσ).2.1.2.2.2.2.1 c
    · exact (ox_data σ hσ).2.1.2.2.2.2.2 c
  · intro g hg
    obtain ⟨p, -, hp⟩ := hB.surjOn hg
    have hg' : sixProd (cx₁ σ hσ) (cx₂ σ hσ) (cx₃ σ hσ) (cx₄ σ hσ) (cx₅ σ hσ) (cx₆ σ hσ) p = g :=
      Subtype.ext hp
    rw [← hg']
    exact sixProd_mem_sixClosure _ _ _ _ _ _ p

theorem normal_form
    : Set.BijOn (sixProd (cx₁ σ hσ) (cx₂ σ hσ) (cx₃ σ hσ) (cx₄ σ hσ) (cx₅ σ hσ) (cx₆ σ hσ))
      Set.univ (sixClosure (cx₁ σ hσ) (cx₂ σ hσ) (cx₃ σ hσ) (cx₄ σ hσ) (cx₅ σ hσ)
        (cx₆ σ hσ) : Set C₀) := by
  have hB := (even_triality_positive_orbit_parametrization K σ hσ).2.2.2.2.2.2.1
  refine ⟨fun p _ => sixProd_mem_sixClosure _ _ _ _ _ _ p, fun p _ p' _ h =>
    hB.injOn (Set.mem_univ p) (Set.mem_univ p') (val_eq_of_eq h :), fun g hg => ?_⟩
  rw [SetLike.mem_coe, sixClosure_eq] at hg
  obtain ⟨p, -, hp⟩ := hB.surjOn hg
  exact ⟨p, Set.mem_univ p, Subtype.ext hp⟩

end NormalForm

section Torus

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ : σ.toRingHom ^ 3 = 1)

local notation "C₀" => graphFixedRootGroup TwistTag.D4 K σ.toRingHom
local notation "GL" => ModGL TwistTag.D4.tag K

abbrev inclU : (fixedSubfield σ)ˣ →* Kˣ := trialityFixedUnit K σ

abbrev normU : Kˣ →* (fixedSubfield σ)ˣ := trialityNorm σ (pow_three_equiv σ hσ)

@[expose] def torusChar : Kˣ × (fixedSubfield σ)ˣ →* (fixedSubfield σ)ˣ × Kˣ where
  toFun p := (p.2 ^ 2 * (normU σ hσ p.1)⁻¹, p.1 ^ 2 * (inclU σ p.2)⁻¹)
  map_one' := by simp
  map_mul' p p' := by
    refine Prod.ext ?_ ?_
    · simp only [Prod.snd_mul, Prod.fst_mul, map_mul, mul_pow, mul_inv]
      exact mul_mul_mul_comm _ _ _ _
    · simp only [Prod.snd_mul, Prod.fst_mul, map_mul, mul_pow, mul_inv]
      exact mul_mul_mul_comm _ _ _ _

omit [Finite K] in
theorem torusChar_injective : Function.Injective (torusChar σ hσ) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨a, b⟩ h
  have h1 : b ^ 2 = normU σ hσ a := mul_inv_eq_one.1 (congrArg Prod.fst h)
  have h2 : a ^ 2 = inclU σ b := mul_inv_eq_one.1 (congrArg Prod.snd h)
  set A : K := (a : K) with hA
  set B : K := ((b : fixedSubfield σ) : K) with hB
  have hA0 : A ≠ 0 := a.ne_zero
  have e0 : A ^ 2 = B := by
    have := congrArg Units.val h2
    rwa [Units.val_pow_eq_pow_val] at this
  have e1 : B ^ 2 = A * σ A * σ (σ A) := by
    have := congrArg (fun x : (fixedSubfield σ)ˣ => ((x : fixedSubfield σ) : K)) h1
    simp only [Units.val_pow_eq_pow_val, SubmonoidClass.coe_pow] at this
    exact this
  have hσB : σ B = B := (b : fixedSubfield σ).2
  have hσA : σ A = A := frobenius_inj K 2 (by
    rw [frobenius_def, frobenius_def, ← map_pow, e0, hσB])
  rw [hσA, hσA, ← e0] at e1
  have hA1 : A = 1 := by
    have h4 : A ^ 3 * (A - 1) = 0 := by linear_combination e1
    rcases mul_eq_zero.1 h4 with h | h
    · exact absurd (pow_eq_zero_iff (by norm_num) |>.1 h) hA0
    · exact sub_eq_zero.1 h
  have ha : a = 1 := Units.ext hA1
  have hb : b = 1 := by
    refine Units.ext (Subtype.ext ?_)
    change B = 1
    rw [← e0, hA1, one_pow]
  rw [ha, hb]
  rfl

theorem torusChar_bijective : Function.Bijective (torusChar σ hσ) :=
  (torusChar_injective σ hσ).bijective_of_nat_card_le (by
    rw [Nat.card_prod, Nat.card_prod, mul_comm])

@[expose] def torusParam : (fixedSubfield σ)ˣ × Kˣ ≃* Kˣ × (fixedSubfield σ)ˣ :=
  (MulEquiv.ofBijective (torusChar σ hσ) (torusChar_bijective σ hσ)).symm

theorem torusChar_torusParam (h : (fixedSubfield σ)ˣ × Kˣ) :
    torusChar σ hσ (torusParam σ hσ h) = h :=
  (MulEquiv.ofBijective (torusChar σ hσ) (torusChar_bijective σ hσ)).apply_symm_apply h

@[expose] def cT
    : Kˣ × (fixedSubfield σ)ˣ →* C₀ :=
  (trialityTorusHom σ).codRestrict C₀
    (trialityTorusHom_mem_graphFixedRootGroup (pow_three_equiv σ hσ))

@[expose] def ctorus
    : (fixedSubfield σ)ˣ × Kˣ →* C₀ :=
  (cT σ hσ).comp (torusParam σ hσ).toMonoidHom

theorem ctorus_injective
    : Function.Injective (ctorus σ hσ) := by
  intro h h' e
  apply (torusParam σ hσ).injective
  exact trialityTorusHom_injective (σ := σ) (val_eq_of_eq e :)

theorem ctorus_eq
    (h : (fixedSubfield σ)ˣ × Kˣ) :
    ∃ c₀ c₁ c₂ c₃ : Kˣ, TwistFixed σ c₀ c₁ c₂ c₃ ∧
      ((ctorus σ hσ h : C₀) : GL) =
        CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit TwistTag.D4.tag
          (d4Tuple c₀ c₁ c₂ c₃) ∧
      (c₀ : K) = (h.2 : K) ∧ (c₂ : K) = ((h.1 : fixedSubfield σ) : K) := by
  set p := torusParam σ hσ h with hp
  have hc := torusChar_torusParam σ hσ h
  rw [← hp] at hc
  refine ⟨_, _, _, _, twistFixed_torus σ hσ p.1 p.2, torusHom_eq σ p.1 p.2, ?_, ?_⟩
  · rw [← hc]
    rfl
  · rw [← hc]
    change ((p.1 * Units.map σ.toRingHom.toMonoidHom p.1 *
      Units.map σ.toRingHom.toMonoidHom (Units.map σ.toRingHom.toMonoidHom p.1))⁻¹ *
        inclU σ p.2 ^ 2 : Kˣ) = (((p.2 ^ 2 * (normU σ hσ p.1)⁻¹ : (fixedSubfield σ)ˣ) :
          fixedSubfield σ) : K)
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val,
      Units.coe_map, SubmonoidClass.coe_pow, Subfield.coe_mul, Subfield.coe_inv]
    rw [mul_comm]
    rfl

theorem ctorus_x₁
    (h : (fixedSubfield σ)ˣ × Kˣ) (a : K) :
    ctorus σ hσ h * cx₁ σ hσ a * (ctorus σ hσ h)⁻¹ = cx₁ σ hσ ((h.2 : K) * a) := by
  obtain ⟨c₀, c₁, c₂, c₃, hF, hc, h0, -⟩ := ctorus_eq σ hσ h
  apply Subtype.ext
  change ((ctorus σ hσ h : C₀) : GL) * ox₁ σ a * ((ctorus σ hσ h : C₀) : GL)⁻¹ =
    ox₁ σ ((h.2 : K) * a)
  rw [hc, torus_ox₁ hF, h0]

theorem ctorus_x₂
    (h : (fixedSubfield σ)ˣ × Kˣ) (a : fixedSubfield σ) :
    ctorus σ hσ h * cx₂ σ hσ a * (ctorus σ hσ h)⁻¹ =
      cx₂ σ hσ ((h.1 : fixedSubfield σ) * a) := by
  obtain ⟨c₀, c₁, c₂, c₃, hF, hc, -, h2⟩ := ctorus_eq σ hσ h
  apply Subtype.ext
  change ((ctorus σ hσ h : C₀) : GL) * pinnedX TwistTag.D4.tag K (trialityRoot 1) (a : K) *
      ((ctorus σ hσ h : C₀) : GL)⁻¹ =
    pinnedX TwistTag.D4.tag K (trialityRoot 1) (((h.1 : fixedSubfield σ) * a : fixedSubfield σ) : K)
  rw [hc, rootDiagUnit_conj_pinnedX (α := trialityRoot 1) (d4Tuple c₀ c₁ c₂ c₃)
    (isRoot_trialityRoot 1 0).1, show trialityRoot 1 = ![0, 0, 1, 0] from rfl, rootChar_d4]
  congr 1
  simp only [zpow_zero, zpow_one, one_mul, mul_one, Subfield.coe_mul, h2]

theorem ctorus_x₃
    (h : (fixedSubfield σ)ˣ × Kˣ) (a : K) :
    ctorus σ hσ h * cx₃ σ hσ a * (ctorus σ hσ h)⁻¹ =
      cx₃ σ hσ (((h.1 : fixedSubfield σ) : K) * (h.2 : K) * a) := by
  obtain ⟨c₀, c₁, c₂, c₃, hF, hc, h0, h2⟩ := ctorus_eq σ hσ h
  apply Subtype.ext
  change ((ctorus σ hσ h : C₀) : GL) * ox₃ σ a * ((ctorus σ hσ h : C₀) : GL)⁻¹ =
    ox₃ σ (((h.1 : fixedSubfield σ) : K) * (h.2 : K) * a)
  rw [hc, torus_ox₃ hF, h0, h2, mul_comm (h.2 : K)]

theorem ctorus_x₄
    (h : (fixedSubfield σ)ˣ × Kˣ) (a : K) :
    ctorus σ hσ h * cx₄ σ hσ a * (ctorus σ hσ h)⁻¹ =
      cx₄ σ hσ (((h.1 : fixedSubfield σ) : K) * σ (h.2 : K) * σ (σ (h.2 : K)) * a) := by
  obtain ⟨c₀, c₁, c₂, c₃, hF, hc, h0, h2⟩ := ctorus_eq σ hσ h
  apply Subtype.ext
  change ((ctorus σ hσ h : C₀) : GL) * ox₄ σ a * ((ctorus σ hσ h : C₀) : GL)⁻¹ =
    ox₄ σ (((h.1 : fixedSubfield σ) : K) * σ (h.2 : K) * σ (σ (h.2 : K)) * a)
  rw [hc, torus_ox₄ hF, ← hF.h1, ← hF.h0, h0, h2]
  congr 1
  ring

theorem ctorus_x₅
    (h : (fixedSubfield σ)ˣ × Kˣ) (a : fixedSubfield σ) :
    ctorus σ hσ h * cx₅ σ hσ a * (ctorus σ hσ h)⁻¹ =
      cx₅ σ hσ ((h.1 : fixedSubfield σ) * fixedNorm (cube σ hσ) (h.2 : K) * a) := by
  obtain ⟨c₀, c₁, c₂, c₃, hF, hc, h0, h2⟩ := ctorus_eq σ hσ h
  apply Subtype.ext
  change ((ctorus σ hσ h : C₀) : GL) * ox₅ σ a * ((ctorus σ hσ h : C₀) : GL)⁻¹ =
    ox₅ σ ((h.1 : fixedSubfield σ) * fixedNorm (cube σ hσ) (h.2 : K) * a)
  rw [hc]
  refine (torus_ox₅ hF a).trans (congrArg (ox₅ σ) (Subtype.ext ?_))
  change ((c₀ : K) * c₁ * c₂ * c₃) * (a : K) =
    ((h.1 : fixedSubfield σ) : K) * ((h.2 : K) * σ (h.2 : K) * σ (σ (h.2 : K))) * (a : K)
  rw [← hF.h1, ← hF.h0, h0, h2]
  ring

theorem ctorus_x₆
    (h : (fixedSubfield σ)ˣ × Kˣ) (a : fixedSubfield σ) :
    ctorus σ hσ h * cx₆ σ hσ a * (ctorus σ hσ h)⁻¹ =
      cx₆ σ hσ ((h.1 : fixedSubfield σ) * (h.1 : fixedSubfield σ) *
        fixedNorm (cube σ hσ) (h.2 : K) * a) := by
  obtain ⟨c₀, c₁, c₂, c₃, hF, hc, h0, h2⟩ := ctorus_eq σ hσ h
  apply Subtype.ext
  change ((ctorus σ hσ h : C₀) : GL) * ox₆ σ a * ((ctorus σ hσ h : C₀) : GL)⁻¹ =
    ox₆ σ ((h.1 : fixedSubfield σ) * (h.1 : fixedSubfield σ) *
      fixedNorm (cube σ hσ) (h.2 : K) * a)
  rw [hc]
  refine (torus_ox₆ hF a).trans (congrArg (ox₆ σ) (Subtype.ext ?_))
  change ((c₀ : K) * c₁ * (c₂ : K) ^ 2 * c₃) * (a : K) =
    ((h.1 : fixedSubfield σ) : K) * ((h.1 : fixedSubfield σ) : K) *
      ((h.2 : K) * σ (h.2 : K) * σ (σ (h.2 : K))) * (a : K)
  rw [← hF.h1, ← hF.h0, h0, h2]
  ring

theorem ctorus_range
    : (ctorus σ hσ).range = (graphFixedRootTorus TwistTag.D4 K σ.toRingHom).subgroupOf C₀ := by
  obtain ⟨-, ⟨eT, heT⟩, -⟩ :=
    even_triality_faithful_torus_coordinates K σ (pow_three_equiv σ hσ)
  ext g
  constructor
  · rintro ⟨h, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    have h1 : ((eT (torusParam σ hσ h) : graphFixedRootTorus TwistTag.D4 K σ.toRingHom) : GL) =
        trialityTorusHom σ (torusParam σ hσ h) := heT _ _
    change trialityTorusHom σ (torusParam σ hσ h) ∈ _
    rw [← h1]
    exact (eT _).2
  · intro hg
    rw [Subgroup.mem_subgroupOf] at hg
    obtain ⟨p, hp⟩ := eT.surjective ⟨g, hg⟩
    refine ⟨torusChar σ hσ p, Subtype.ext ?_⟩
    have h1 : ((eT p : graphFixedRootTorus TwistTag.D4 K σ.toRingHom) : GL) =
        trialityTorusHom σ p := heT _ _
    rw [hp] at h1
    change trialityTorusHom σ (torusParam σ hσ (torusChar σ hσ p)) = (g : GL)
    rw [show torusParam σ hσ (torusChar σ hσ p) = p from
      (MulEquiv.ofBijective (torusChar σ hσ) (torusChar_bijective σ hσ)).symm_apply_apply p]
    exact h1.symm

theorem normalizer_eq
    : Subgroup.normalizer
        (sixClosure (cx₁ σ hσ) (cx₂ σ hσ) (cx₃ σ hσ) (cx₄ σ hσ) (cx₅ σ hσ) (cx₆ σ hσ) : Set C₀) =
      sixClosure (cx₁ σ hσ) (cx₂ σ hσ) (cx₃ σ hσ) (cx₄ σ hσ) (cx₅ σ hσ) (cx₆ σ hσ) ⊔
        (ctorus σ hσ).range := by
  have hU := graphFixedPosUnipotent_le_graphFixedRootGroup TwistTag.D4 K σ.toRingHom
  have hH : graphFixedRootTorus TwistTag.D4 K σ.toRingHom ≤
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom := inf_le_right
  rw [sixClosure_eq, ctorus_range, ← Subgroup.subgroupOf_normalizer_eq hU,
    ← Subgroup.subgroupOf_sup hU hH, ← Subgroup.inf_subgroupOf_right, inf_comm,
    graphFixedRootGroup_inf_normalizer_graphFixedPosUnipotent σ.surjective,
    graphFixedRootBorel_eq_sup σ.surjective, sup_comm]

end Torus

section Weyl

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ : σ.toRingHom ^ 3 = 1)

local notation "C₀" => graphFixedRootGroup TwistTag.D4 K σ.toRingHom
local notation "GL" => ModGL TwistTag.D4.tag K
local notation "rA" => CFSG.Quasithin.B42D4.rA
local notation "rB" => CFSG.Quasithin.B42D4.rB
local notation "nA" => CFSG.Quasithin.B42D4.nA
local notation "nB" => CFSG.Quasithin.B42D4.nB

@[expose] def crHom
    : WeylGroup TwistTag.D4.tag →* GL where
  toFun w := canonicalRep (coxeterSystem TwistTag.D4.tag) K w
  map_one' := canonicalRep_one _ _
  map_mul' w v := CFSG.RankThree.PartOne.Q1327T.canonicalRep_mul_charTwo w v

@[expose] def cu
    : C₀ :=
  ⟨nA K, CFSG.Quasithin.B42D4.nA_mem σ⟩

@[expose] def cv
    : C₀ :=
  ⟨nB K, CFSG.Quasithin.B42D4.nB_mem σ⟩

theorem rA_mul_self
    : rA * rA = 1 :=
  CFSG.Blueprint.Chevalley.TwistTag.orbitReflection_mul_self TwistTag.D4 _

theorem rB_mul_self
    : rB * rB = 1 :=
  CFSG.Blueprint.Chevalley.TwistTag.orbitReflection_mul_self TwistTag.D4 _

theorem rA_mul_rB_pow_six
    : (rA * rB) ^ 6 = 1 := by
  refine ext_single fun i => ?_
  simp only [pow_succ, pow_zero, one_mul, mul_smul, CFSG.Quasithin.B42D4.rA_smul,
    CFSG.Quasithin.B42D4.rB_smul, one_smul]
  fin_cases i <;> exact List.ofFn_injective (by decide +kernel)

omit [Finite K] in
theorem nA_mul_self
    : nA K * nA K = 1 := by
  change crHom (K := K) rA * crHom (K := K) rA = 1
  rw [← map_mul, rA_mul_self, map_one]

omit [Finite K] in
theorem nB_mul_self
    : nB K * nB K = 1 := by
  change crHom (K := K) rB * crHom (K := K) rB = 1
  rw [← map_mul, rB_mul_self, map_one]

omit [Finite K] in
theorem nA_inv
    : (nA K)⁻¹ = nA K :=
  inv_eq_of_mul_eq_one_right nA_mul_self

omit [Finite K] in
theorem nB_inv
    : (nB K)⁻¹ = nB K :=
  inv_eq_of_mul_eq_one_right nB_mul_self

omit [Finite K] in
theorem cu_mul_self
    : cu σ * cu σ = 1 :=
  Subtype.ext nA_mul_self

omit [Finite K] in
theorem cv_mul_self
    : cv σ * cv σ = 1 :=
  Subtype.ext nB_mul_self

omit [Finite K] in
theorem cu_mul_cv_pow_six
    : (cu σ * cv σ) ^ 6 = 1 := by
  apply Subtype.ext
  change (crHom (K := K) rA * crHom (K := K) rB) ^ 6 = 1
  rw [← map_mul, ← map_pow, rA_mul_rB_pow_six, map_one]

theorem cu_x₂
    (a : fixedSubfield σ) : cu σ * cx₂ σ hσ a * cu σ = cx₅ σ hσ a := by
  apply Subtype.ext
  change nA K * pinnedX TwistTag.D4.tag K d4C (a : K) * nA K =
    pinnedX TwistTag.D4.tag K d4P (a : K)
  have h := CFSG.Quasithin.B42D4.nA_C (a : K)
  rwa [nA_inv] at h

theorem cu_x₃
    (a : K) : cu σ * cx₃ σ hσ a * cu σ = cx₄ σ hσ a := by
  apply Subtype.ext
  change nA K * ox₃ σ a * nA K = ox₄ σ a
  have h := CFSG.Quasithin.B42D4.nA_ox₃ σ a
  rwa [nA_inv] at h

theorem cu_x₆
    (a : fixedSubfield σ) : cu σ * cx₆ σ hσ a * cu σ = cx₆ σ hσ a := by
  apply Subtype.ext
  change nA K * pinnedX TwistTag.D4.tag K d4H (a : K) * nA K =
    pinnedX TwistTag.D4.tag K d4H (a : K)
  have h := CFSG.Quasithin.B42D4.nA_H (a : K)
  rwa [nA_inv] at h

theorem cv_x₁
    (a : K) : cv σ * cx₁ σ hσ a * cv σ = cx₃ σ hσ a := by
  apply Subtype.ext
  change nB K * ox₁ σ a * nB K = ox₃ σ a
  have h := CFSG.Quasithin.B42D4.nB_ox₁ σ a
  rwa [nB_inv] at h

theorem cv_x₄
    (a : K) : cv σ * cx₄ σ hσ a * cv σ = cx₄ σ hσ a := by
  apply Subtype.ext
  change nB K * ox₄ σ a * nB K = ox₄ σ a
  have h := CFSG.Quasithin.B42D4.nB_ox₄ σ a
  rwa [nB_inv] at h

theorem cv_x₅
    (a : fixedSubfield σ) : cv σ * cx₅ σ hσ a * cv σ = cx₆ σ hσ a := by
  apply Subtype.ext
  change nB K * pinnedX TwistTag.D4.tag K d4P (a : K) * nB K =
    pinnedX TwistTag.D4.tag K d4H (a : K)
  have h := CFSG.Quasithin.B42D4.nB_P (a : K)
  rwa [nB_inv] at h

omit [Finite K] in
theorem cu_inv
    : (cu σ)⁻¹ = cu σ :=
  inv_eq_of_mul_eq_one_right (cu_mul_self σ)

omit [Finite K] in
theorem cv_inv
    : (cv σ)⁻¹ = cv σ :=
  inv_eq_of_mul_eq_one_right (cv_mul_self σ)

theorem conj_symm_of_mul_self {G : Type*} [Group G] {t x y : G} (ht : t * t = 1)
    (h : t * x * t = y) : t * y * t = x := by
  rw [← h, show t * (t * x * t) * t = (t * t) * x * (t * t) by group, ht, one_mul, mul_one]

theorem rA_outer
    : rA • d4E0 = -d4E0 ∧ rA • d4E1 = -d4E1 ∧ rA • d4E3 = -d4E3 := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [CFSG.Quasithin.B42D4.rA_smul] <;>
    exact List.ofFn_injective (by decide +kernel)

omit [Finite K] in
theorem nA_ox₁_mem_neg
    (c : K) : nA K * ox₁ σ c * (nA K)⁻¹ ∈ negUnipotent TwistTag.D4.tag K := by
  obtain ⟨h0, h1, h3⟩ := rA_outer
  rw [CFSG.Quasithin.B42D4.coe_ox₁_eq, CFSG.Quasithin.B42D4.conj_mul3,
    CFSG.Quasithin.B42D4.nA_conj (by decide +kernel),
    CFSG.Quasithin.B42D4.nA_conj (by decide +kernel),
    CFSG.Quasithin.B42D4.nA_conj (by decide +kernel), h0, h1, h3]
  refine mul_mem (mul_mem ?_ ?_) ?_ <;>
    exact pinnedX_mem_rootSpan (S := {α | IsRoot TwistTag.D4.tag α ∧ height α < 0})
      ⟨CFSG.Quasithin.B42D4.isRoot_of_d4 (by decide +kernel), by decide +kernel⟩ _

include hσ in
theorem cu_mul_cv_sq_ne_one
    : (cu σ * cv σ) ^ 2 ≠ 1 := by
  intro h
  have hv6 : cv σ * cx₆ σ hσ 1 * cv σ = cx₅ σ hσ 1 :=
    conj_symm_of_mul_self (cv_mul_self σ) (cv_x₅ σ hσ 1)
  have hu5 : cu σ * cx₅ σ hσ 1 * cu σ = cx₂ σ hσ 1 :=
    conj_symm_of_mul_self (cu_mul_self σ) (cu_x₂ σ hσ 1)
  have key : (cu σ * cv σ) ^ 2 * cx₅ σ hσ 1 * ((cu σ * cv σ) ^ 2)⁻¹ = cx₂ σ hσ 1 := by
    rw [pow_two, mul_inv_rev, mul_inv_rev, cu_inv, cv_inv]
    calc cu σ * cv σ * (cu σ * cv σ) * cx₅ σ hσ 1 * (cv σ * cu σ * (cv σ * cu σ)) =
        cu σ * (cv σ * (cu σ * (cv σ * cx₅ σ hσ 1 * cv σ) * cu σ) * cv σ) * cu σ := by group
      _ = cx₂ σ hσ 1 := by rw [cv_x₅, cu_x₆, hv6, hu5]
  rw [h, one_mul, inv_one, mul_one] at key
  have hinj := (normal_form σ hσ).injOn (Set.mem_univ ((0, 0, 0, 0, 1, 0) :
    K × fixedSubfield σ × K × K × fixedSubfield σ × fixedSubfield σ))
    (Set.mem_univ ((0, 1, 0, 0, 0, 0) :
      K × fixedSubfield σ × K × K × fixedSubfield σ × fixedSubfield σ)) (by
      simp only [sixProd, map_zero_of_add (cx₁_add σ hσ), map_zero_of_add (cx₂_add σ hσ),
        map_zero_of_add (cx₃_add σ hσ), map_zero_of_add (cx₄_add σ hσ),
        map_zero_of_add (cx₅_add σ hσ), map_zero_of_add (cx₆_add σ hσ), one_mul, mul_one]
      exact key)
  have := congrArg (fun p => p.2.1) hinj
  exact zero_ne_one this

include hσ in
theorem cu_mul_cv_cube_ne_one
    : (cu σ * cv σ) ^ 3 ≠ 1 := by
  intro h
  have hv3 : cv σ * cx₃ σ hσ 1 * cv σ = cx₁ σ hσ 1 :=
    conj_symm_of_mul_self (cv_mul_self σ) (cv_x₁ σ hσ 1)
  have hu4 : cu σ * cx₄ σ hσ 1 * cu σ = cx₃ σ hσ 1 :=
    conj_symm_of_mul_self (cu_mul_self σ) (cu_x₃ σ hσ 1)
  have hinv : (cu σ * cv σ)⁻¹ = cv σ * cu σ := by rw [mul_inv_rev, cu_inv, cv_inv]
  have hconj : ∀ y, cu σ * cv σ * y * (cu σ * cv σ)⁻¹ = cu σ * (cv σ * y * cv σ) * cu σ := by
    intro y
    rw [hinv]
    group
  have key : (cu σ * cv σ) ^ 3 * cx₁ σ hσ 1 * ((cu σ * cv σ) ^ 3)⁻¹ =
      cu σ * cx₁ σ hσ 1 * cu σ := by
    have e : (cu σ * cv σ) ^ 3 * cx₁ σ hσ 1 * ((cu σ * cv σ) ^ 3)⁻¹ =
        cu σ * cv σ * (cu σ * cv σ * (cu σ * cv σ * cx₁ σ hσ 1 * (cu σ * cv σ)⁻¹) *
          (cu σ * cv σ)⁻¹) * (cu σ * cv σ)⁻¹ := by
      rw [pow_three, mul_inv_rev, mul_inv_rev]
      simp only [mul_assoc]
    rw [e, hconj (cx₁ σ hσ 1), cv_x₁, cu_x₃, hconj (cx₄ σ hσ 1), cv_x₄, hu4,
      hconj (cx₃ σ hσ 1), hv3]
  rw [h, one_mul, inv_one, mul_one] at key
  have hpos : ox₁ σ 1 ∈ posUnipotent TwistTag.D4.tag K :=
    (Subgroup.mem_inf.1 ((ox_data σ hσ).2.1.1 1)).1
  have hneg : ox₁ σ 1 ∈ negUnipotent TwistTag.D4.tag K := by
    have h1 := nA_ox₁_mem_neg σ (1 : K)
    rw [nA_inv] at h1
    have h2 := val_eq_of_eq key
    change ox₁ σ 1 = nA K * ox₁ σ 1 * nA K at h2
    rw [h2]
    exact h1
  have h0 : ox₁ σ 1 = 1 := by
    have := Subgroup.mem_inf.2 ⟨hpos, hneg⟩
    rwa [CFSG.Blueprint.Chevalley.posUnipotent_inf_negUnipotent, Subgroup.mem_bot] at this
  have h1 : cx₁ σ hσ 1 = cx₁ σ hσ 0 := by
    rw [map_zero_of_add (cx₁_add σ hσ)]
    exact Subtype.ext h0
  exact one_ne_zero (cx₁_injective σ hσ h1)

include hσ in
theorem orderOf_cu_mul_cv
    : orderOf (cu σ * cv σ) = 6 := by
  have hd : orderOf (cu σ * cv σ) ∣ 6 := orderOf_dvd_of_pow_eq_one (cu_mul_cv_pow_six σ)
  have h2 := cu_mul_cv_sq_ne_one σ hσ
  have h3 := cu_mul_cv_cube_ne_one σ hσ
  have hmem : orderOf (cu σ * cv σ) ∈ Nat.divisors 6 := Nat.mem_divisors.2 ⟨hd, by norm_num⟩
  rw [show Nat.divisors 6 = {1, 2, 3, 6} from rfl] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h
  · exact absurd (show (cu σ * cv σ) ^ 2 = 1 by rw [orderOf_eq_one_iff.1 h, one_pow]) h2
  · exact absurd (show (cu σ * cv σ) ^ 2 = 1 by rw [← h, pow_orderOf_eq_one]) h2
  · exact absurd (show (cu σ * cv σ) ^ 3 = 1 by rw [← h, pow_orderOf_eq_one]) h3
  · exact h

theorem cu_torus
    (h : (fixedSubfield σ)ˣ × Kˣ) : ∃ h', cu σ * ctorus σ hσ h * cu σ = ctorus σ hσ h' := by
  have hN := canonicalRep_orbitReflection_mem_normalizer_graphFixedRootTorus
    (σ := σ.toRingHom) (t := TwistTag.D4) ⟨0, by decide⟩
  have hmem : ctorus σ hσ h ∈ (graphFixedRootTorus TwistTag.D4 K σ.toRingHom).subgroupOf C₀ := by
    rw [← ctorus_range σ hσ]
    exact ⟨h, rfl⟩
  have h2 := (Subgroup.mem_normalizer_iff.1 hN _).1 hmem
  rw [nA_inv] at h2
  have h3 : cu σ * ctorus σ hσ h * cu σ ∈
      (graphFixedRootTorus TwistTag.D4 K σ.toRingHom).subgroupOf C₀ := h2
  rw [← ctorus_range σ hσ] at h3
  obtain ⟨h', hh'⟩ := h3
  exact ⟨h', hh'.symm⟩

theorem cv_torus
    (h : (fixedSubfield σ)ˣ × Kˣ) : ∃ h', cv σ * ctorus σ hσ h * cv σ = ctorus σ hσ h' := by
  have hN := canonicalRep_orbitReflection_mem_normalizer_graphFixedRootTorus
    (σ := σ.toRingHom) (t := TwistTag.D4) ⟨1, by decide⟩
  have hmem : ctorus σ hσ h ∈ (graphFixedRootTorus TwistTag.D4 K σ.toRingHom).subgroupOf C₀ := by
    rw [← ctorus_range σ hσ]
    exact ⟨h, rfl⟩
  have h2 := (Subgroup.mem_normalizer_iff.1 hN _).1 hmem
  rw [nB_inv] at h2
  have h3 : cv σ * ctorus σ hσ h * cv σ ∈
      (graphFixedRootTorus TwistTag.D4 K σ.toRingHom).subgroupOf C₀ := h2
  rw [← ctorus_range σ hσ] at h3
  obtain ⟨h', hh'⟩ := h3
  exact ⟨h', hh'.symm⟩

end Weyl





section Bruhat

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ : σ.toRingHom ^ 3 = 1)

local notation "C₀" => graphFixedRootGroup TwistTag.D4 K σ.toRingHom
local notation "GL" => ModGL TwistTag.D4.tag K
local notation "rA" => CFSG.Quasithin.B42D4.rA
local notation "rB" => CFSG.Quasithin.B42D4.rB
local notation "nA" => CFSG.Quasithin.B42D4.nA
local notation "nB" => CFSG.Quasithin.B42D4.nB
local notation "ιC" => Subgroup.subtype (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)

omit [Finite K] [CharP K 2] in
theorem map_closure_cu_cv
    : (Subgroup.closure ({cu σ, cv σ} : Set C₀)).map ιC =
      Subgroup.closure ({nA K, nB K} : Set GL) := by
  rw [MonoidHom.map_closure, Set.image_pair]
  rfl

omit [Finite K] in
theorem crHom_mem_closure
    {w : WeylGroup TwistTag.D4.tag} (hw : w ∈ relWeylTwist TwistTag.D4) :
    crHom (K := K) w ∈ Subgroup.closure ({nA K, nB K} : Set GL) := by
  have h : (relWeylTwist TwistTag.D4).map (crHom (K := K)) ≤
      Subgroup.closure ({nA K, nB K} : Set GL) := by
    rw [relWeylTwist_eq_closure, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
    fin_cases a
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  exact h (Subgroup.mem_map_of_mem _ hw)

omit [Finite K] in
theorem exists_crHom_eq
    {g : GL} (hg : g ∈ Subgroup.closure ({nA K, nB K} : Set GL)) :
    ∃ w ∈ relWeylTwist TwistTag.D4, crHom (K := K) w = g := by
  have h : Subgroup.closure ({nA K, nB K} : Set GL) ≤
      (relWeylTwist TwistTag.D4).map (crHom (K := K)) := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact ⟨rA, TwistTag.D4.orbitReflection_mem _, rfl⟩
    · exact ⟨rB, TwistTag.D4.orbitReflection_mem _, rfl⟩
  obtain ⟨w, hw, rfl⟩ := h hg
  exact ⟨w, hw, rfl⟩

theorem sup_closure_eq_top
    : sixClosure (cx₁ σ hσ) (cx₂ σ hσ) (cx₃ σ hσ) (cx₄ σ hσ) (cx₅ σ hσ) (cx₆ σ hσ) ⊔
      Subgroup.closure ({cu σ, cv σ} : Set C₀) = ⊤ := by
  set H := sixClosure (cx₁ σ hσ) (cx₂ σ hσ) (cx₃ σ hσ) (cx₄ σ hσ) (cx₅ σ hσ) (cx₆ σ hσ) ⊔
    Subgroup.closure ({cu σ, cv σ} : Set C₀) with hH
  have hU := graphFixedPosUnipotent_le_graphFixedRootGroup TwistTag.D4 K σ.toRingHom
  have hUH : graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ≤ H.map ιC := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hU, ← sixClosure_eq σ hσ]
    exact Subgroup.map_mono le_sup_left
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem TwistTag.D4.tag).length
  have hn₀ : crHom (K := K) w₀ ∈ H.map ιC := by
    have h1 := crHom_mem_closure (K := K) (mem_relWeylTwist_of_forall_length_le hw₀)
    rw [← map_closure_cu_cv σ] at h1
    exact Subgroup.map_mono le_sup_right h1
  have hVH : graphFixedNegUnipotent TwistTag.D4 K σ.toRingHom ≤ H.map ιC := by
    rw [← map_conj_graphFixedPosUnipotent (σ := σ.toRingHom) hw₀]
    rintro _ ⟨x, hx, rfl⟩
    change crHom (K := K) w₀ * x * (crHom (K := K) w₀)⁻¹ ∈ _
    exact mul_mem (mul_mem hn₀ (hUH hx)) (inv_mem hn₀)
  refine eq_top_iff.2 fun g _ => ?_
  have hg : (g : GL) ∈ H.map ιC := sup_le hUH hVH g.2
  obtain ⟨h, hh, e⟩ := hg
  rw [show g = h from Subtype.ext e.symm]
  exact hh

theorem borel_eq
    : sixClosure (cx₁ σ hσ) (cx₂ σ hσ) (cx₃ σ hσ) (cx₄ σ hσ) (cx₅ σ hσ) (cx₆ σ hσ) ⊔
      (ctorus σ hσ).range = (graphFixedRootBorel TwistTag.D4 K σ.toRingHom).subgroupOf C₀ := by
  rw [sixClosure_eq, ctorus_range, ← Subgroup.subgroupOf_sup
    (graphFixedPosUnipotent_le_graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (show graphFixedRootTorus TwistTag.D4 K σ.toRingHom ≤
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom from inf_le_right),
    graphFixedRootBorel_eq_sup σ.surjective, sup_comm]

theorem bruhat
    (g : C₀) : ∃ b₁ ∈ sixClosure (cx₁ σ hσ) (cx₂ σ hσ) (cx₃ σ hσ) (cx₄ σ hσ) (cx₅ σ hσ)
        (cx₆ σ hσ) ⊔ (ctorus σ hσ).range,
      ∃ w ∈ Subgroup.closure ({cu σ, cv σ} : Set C₀),
        ∃ b₂ ∈ sixClosure (cx₁ σ hσ) (cx₂ σ hσ) (cx₃ σ hσ) (cx₄ σ hσ) (cx₅ σ hσ)
          (cx₆ σ hσ) ⊔ (ctorus σ hσ).range, g = b₁ * w * b₂ := by
  have hBC : graphFixedRootBorel TwistTag.D4 K σ.toRingHom ≤
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom := inf_le_right
  have hg : (g : GL) ∈ (graphFixedRootGroup TwistTag.D4 K σ.toRingHom : Set GL) := g.2
  rw [graphFixedRootGroup_eq_iUnion σ.surjective, Set.mem_iUnion] at hg
  obtain ⟨⟨w, hw⟩, hgw⟩ := hg
  obtain ⟨x, ⟨b₁, hb₁, n, hn, rfl⟩, b₂, hb₂, e⟩ := hgw
  rw [Set.mem_singleton_iff] at hn
  subst hn
  have hnC := canonicalRep_mem_graphFixedRootGroup (σ := σ.toRingHom) hw
  refine ⟨⟨b₁, hBC hb₁⟩, ?_, ⟨_, hnC⟩, ?_, ⟨b₂, hBC hb₂⟩, ?_, Subtype.ext e.symm⟩
  · rw [borel_eq σ hσ]
    exact hb₁
  · have h1 := crHom_mem_closure (K := K) hw
    rw [← map_closure_cu_cv σ] at h1
    obtain ⟨y, hy, ey⟩ := h1
    rw [show (⟨_, hnC⟩ : C₀) = y from Subtype.ext ey.symm]
    exact hy
  · rw [borel_eq σ hσ]
    exact hb₂

theorem bruhat_disjoint
    (w : C₀) (hw : w ∈ Subgroup.closure ({cu σ, cv σ} : Set C₀))
    (w' : C₀) (hw' : w' ∈ Subgroup.closure ({cu σ, cv σ} : Set C₀))
    (b₁ : C₀) (hb₁ : b₁ ∈ sixClosure (cx₁ σ hσ) (cx₂ σ hσ) (cx₃ σ hσ) (cx₄ σ hσ) (cx₅ σ hσ)
      (cx₆ σ hσ) ⊔ (ctorus σ hσ).range)
    (b₂ : C₀) (hb₂ : b₂ ∈ sixClosure (cx₁ σ hσ) (cx₂ σ hσ) (cx₃ σ hσ) (cx₄ σ hσ) (cx₅ σ hσ)
      (cx₆ σ hσ) ⊔ (ctorus σ hσ).range)
    (h : b₁ * w * b₂ = w') : w = w' := by
  rw [borel_eq σ hσ] at hb₁ hb₂
  obtain ⟨w₁, hw₁, e₁⟩ := exists_crHom_eq (K := K)
    (map_closure_cu_cv σ ▸ Subgroup.mem_map_of_mem ιC hw)
  obtain ⟨w₂, hw₂, e₂⟩ := exists_crHom_eq (K := K)
    (map_closure_cu_cv σ ▸ Subgroup.mem_map_of_mem ιC hw')
  have hB1 : (1 : GL) ∈ (graphFixedRootBorel TwistTag.D4 K σ.toRingHom : Set GL) := one_mem _
  have m₁ : (w' : GL) ∈ graphFixedRootBruhatCell TwistTag.D4 K σ.toRingHom w₁ := by
    have := Set.mul_mem_mul (Set.mul_mem_mul (Subgroup.mem_subgroupOf.1 hb₁)
      (Set.mem_singleton (crHom (K := K) w₁))) (Subgroup.mem_subgroupOf.1 hb₂)
    have hx : (b₁ : GL) * crHom (K := K) w₁ * b₂ = ((b₁ * w * b₂ : C₀) : GL) := by
      rw [e₁]
      rfl
    rw [← h, ← hx]
    exact this
  have m₂ : (w' : GL) ∈ graphFixedRootBruhatCell TwistTag.D4 K σ.toRingHom w₂ := by
    have := Set.mul_mem_mul (Set.mul_mem_mul hB1 (Set.mem_singleton (crHom (K := K) w₂))) hB1
    have hx : 1 * crHom (K := K) w₂ * 1 = (w' : GL) := by
      rw [one_mul, mul_one, e₂]
      rfl
    rw [← hx]
    exact this
  by_cases hne : w₁ = w₂
  · subst hne
    exact Subtype.ext (e₁.symm.trans e₂)
  · exact absurd (Set.disjoint_left.1 (disjoint_graphFixedRootBruhatCell hne) m₁ m₂) id

omit [Finite K] [CharP K 2] in
theorem card_C₀
    {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 3) (hσq : ∀ c, σ c = c ^ (2 ^ f)) :
    Nat.card C₀ = (2 ^ f) ^ 12 * ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 6 - 1) *
      ((2 ^ f) ^ 8 + (2 ^ f) ^ 4 + 1) :=
  (triality_both_orientations_exact_finite_order 2 f Nat.prime_two hf K hK 1 (Or.inl rfl)
    σ.toRingHom (fun c => by rw [pow_one]; exact hσq c)).1

end Bruhat

section Automorphisms

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ : σ.toRingHom ^ 3 = 1)

local notation "C₀" => graphFixedRootGroup TwistTag.D4 K σ.toRingHom
local notation "GL" => ModGL TwistTag.D4.tag K
local notation "nA" => CFSG.Quasithin.B42D4.nA
local notation "nB" => CFSG.Quasithin.B42D4.nB

variable (K) in
@[expose] def frob : K ≃+* K :=
  letI : Algebra (ZMod 2) K := ZMod.algebra K 2
  (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) K).toRingEquiv

theorem frob_apply (c : K) : frob K c = c ^ 2 := by
  let : Algebra (ZMod 2) K := ZMod.algebra K 2
  change FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) K c = c ^ 2
  rw [FiniteField.coe_frobeniusAlgEquivOfAlgebraic, ZMod.card]

theorem orderOf_frob {f : ℕ} (hK : Nat.card K = (2 ^ f) ^ 3) : orderOf (frob K) = 3 * f := by
  let : Algebra (ZMod 2) K := ZMod.algebra K 2
  have : Fintype K := Fintype.ofFinite K
  have h2 : orderOf (frob K) = orderOf (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) K) :=
    orderOf_injective
      { toFun := AlgEquiv.toRingEquiv
        map_one' := RingEquiv.ext fun _ => rfl
        map_mul' := fun _ _ => RingEquiv.ext fun _ => rfl }
      (fun _ _ h => AlgEquiv.ext fun x => congrArg (fun e : K ≃+* K => e x) h) _
  rw [h2, FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic]
  have hc := Module.card_eq_pow_finrank (K := ZMod 2) (V := K)
  rw [ZMod.card, ← Nat.card_eq_fintype_card, hK, ← pow_mul] at hc
  have := Nat.pow_right_injective le_rfl hc
  omega

omit [Finite K] [CharP K 2] in
theorem units_map_pinnedX
    (δ : K ≃+* K) (α : Fin TwistTag.D4.tag.rank → ℤ) (c : K) :
    Units.map (entrywiseHom δ.toRingHom) (pinnedX TwistTag.D4.tag K α c) =
      pinnedX TwistTag.D4.tag K α (δ c) :=
  Units.ext (entrywise_pinnedX δ.toRingHom α c)

theorem cφ_x₁
    (a : K) : fieldActor σ (frob K) (cx₁ σ hσ a) = cx₁ σ hσ (a ^ 2) := by
  apply Subtype.ext
  rw [coe_fieldActor]
  change Units.map (entrywiseHom (frob K).toRingHom) (ox₁ σ a) = ox₁ σ (a ^ 2)
  rw [CFSG.Quasithin.B42D4.coe_ox₁_eq, CFSG.Quasithin.B42D4.coe_ox₁_eq, map_mul, map_mul,
    units_map_pinnedX, units_map_pinnedX, units_map_pinnedX, frob_apply, frob_apply, frob_apply,
    map_pow, map_pow]

theorem cφ_x₂
    (a : fixedSubfield σ) : fieldActor σ (frob K) (cx₂ σ hσ a) = cx₂ σ hσ (a ^ 2) := by
  apply Subtype.ext
  rw [coe_fieldActor]
  change Units.map (entrywiseHom (frob K).toRingHom) (pinnedX TwistTag.D4.tag K d4C (a : K)) =
    pinnedX TwistTag.D4.tag K d4C ((a ^ 2 : fixedSubfield σ) : K)
  rw [units_map_pinnedX, frob_apply, SubmonoidClass.coe_pow]

theorem cφ_x₃
    (a : K) : fieldActor σ (frob K) (cx₃ σ hσ a) = cx₃ σ hσ (a ^ 2) := by
  apply Subtype.ext
  rw [coe_fieldActor]
  change Units.map (entrywiseHom (frob K).toRingHom) (ox₃ σ a) = ox₃ σ (a ^ 2)
  rw [CFSG.Quasithin.B42D4.coe_ox₃_eq, CFSG.Quasithin.B42D4.coe_ox₃_eq, map_mul, map_mul,
    units_map_pinnedX, units_map_pinnedX, units_map_pinnedX, frob_apply, frob_apply, frob_apply,
    map_pow, map_pow]

theorem cφ_x₄
    (a : K) : fieldActor σ (frob K) (cx₄ σ hσ a) = cx₄ σ hσ (a ^ 2) := by
  apply Subtype.ext
  rw [coe_fieldActor]
  change Units.map (entrywiseHom (frob K).toRingHom) (ox₄ σ a) = ox₄ σ (a ^ 2)
  rw [CFSG.Quasithin.B42D4.coe_ox₄_eq, CFSG.Quasithin.B42D4.coe_ox₄_eq, map_mul, map_mul,
    units_map_pinnedX, units_map_pinnedX, units_map_pinnedX, frob_apply, frob_apply, frob_apply,
    map_pow, map_pow]

theorem cφ_x₅
    (a : fixedSubfield σ) : fieldActor σ (frob K) (cx₅ σ hσ a) = cx₅ σ hσ (a ^ 2) := by
  apply Subtype.ext
  rw [coe_fieldActor]
  change Units.map (entrywiseHom (frob K).toRingHom) (pinnedX TwistTag.D4.tag K d4P (a : K)) =
    pinnedX TwistTag.D4.tag K d4P ((a ^ 2 : fixedSubfield σ) : K)
  rw [units_map_pinnedX, frob_apply, SubmonoidClass.coe_pow]

theorem cφ_x₆
    (a : fixedSubfield σ) : fieldActor σ (frob K) (cx₆ σ hσ a) = cx₆ σ hσ (a ^ 2) := by
  apply Subtype.ext
  rw [coe_fieldActor]
  change Units.map (entrywiseHom (frob K).toRingHom) (pinnedX TwistTag.D4.tag K d4H (a : K)) =
    pinnedX TwistTag.D4.tag K d4H ((a ^ 2 : fixedSubfield σ) : K)
  rw [units_map_pinnedX, frob_apply, SubmonoidClass.coe_pow]

theorem cφ_u
    : fieldActor σ (frob K) (cu σ) = cu σ := by
  apply Subtype.ext
  rw [coe_fieldActor]
  exact entrywise_canonicalRep (frob K) _

theorem cφ_v
    : fieldActor σ (frob K) (cv σ) = cv σ := by
  apply Subtype.ext
  rw [coe_fieldActor]
  exact entrywise_canonicalRep (frob K) _

theorem cφ_torus
    (h : (fixedSubfield σ)ˣ × Kˣ) :
    fieldActor σ (frob K) (ctorus σ hσ h) = ctorus σ hσ (h ^ 2) := by
  obtain ⟨c₀, c₁, c₂, c₃, -, hc, -, -⟩ := ctorus_eq σ hσ h
  rw [map_pow]
  apply Subtype.ext
  rw [coe_fieldActor, Subgroup.coe_pow, hc,
    units_map_entrywiseHom_rootDiagUnit_ringEquiv, sq, ← rootDiagUnit_mul]
  congr 1
  funext i
  refine Units.ext ?_
  simp only [Units.coe_map, Pi.mul_apply, Units.val_mul]
  change frob K _ = _
  rw [frob_apply, sq]

variable {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 3) (hσq : ∀ c, σ c = c ^ (2 ^ f))

omit [CharP K 2] in
include hf hK hσq in
theorem fieldActor_injective
    : Function.Injective (fieldActor (t := TwistTag.D4) σ) := by
  intro δ₁ δ₂ h
  obtain ⟨-, huniq, -⟩ := even_triality_exact_automorphism_normal_form hf K hK σ hσq
  obtain ⟨gδ, -, hu⟩ := huniq (fieldActor σ δ₁)
  have e1 := hu (1, δ₁) (by beta_reduce; rw [map_one, one_mul])
  have e2 := hu (1, δ₂) (by beta_reduce; rw [map_one, one_mul, h])
  exact congrArg Prod.snd (e1.trans e2.symm)

include hf hK hσq in
theorem orderOf_cφ
    : orderOf (fieldActor (t := TwistTag.D4) σ (frob K)) = 3 * f := by
  rw [← fieldActorHom_apply, orderOf_injective _ (fieldActor_injective σ hf hK hσq),
    orderOf_frob hK]

include hf hK hσq in
theorem aut_eq
    (α : MulAut C₀) : ∃ (g : C₀) (k : ℕ), α = MulAut.conj g * fieldActor σ (frob K) ^ k := by
  obtain ⟨-, huniq, -, -, hcard, -⟩ := even_triality_exact_automorphism_normal_form hf K hK σ hσq
  obtain ⟨⟨g, δ⟩, hα, -⟩ := huniq α
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  have htop : Subgroup.zpowers (frob K) = ⊤ :=
    Subgroup.eq_top_of_card_eq _ (by rw [Nat.card_zpowers, orderOf_frob hK, hcard])
  have hδ : δ ∈ Submonoid.powers (frob K) := by
    rw [mem_powers_iff_mem_zpowers, htop]
    exact Subgroup.mem_top δ
  obtain ⟨k, rfl⟩ := hδ
  refine ⟨g, k, ?_⟩
  rw [hα, ← fieldActorHom_apply, ← fieldActorHom_apply, map_pow]

include hf hK hσq in
theorem cφ_pow_eq_conj
    (k : ℕ) (g : C₀) (h : fieldActor σ (frob K) ^ k = MulAut.conj g) :
    fieldActor (t := TwistTag.D4) σ (frob K) ^ k = 1 := by
  obtain ⟨-, huniq, -⟩ := even_triality_exact_automorphism_normal_form hf K hK σ hσq
  have h1 : fieldActor σ (frob K ^ k) = MulAut.conj g := by
    rw [← fieldActorHom_apply, map_pow, fieldActorHom_apply, h]
  obtain ⟨gδ, -, hu⟩ := huniq (MulAut.conj g)
  have e1 := hu (g, 1) (by beta_reduce; rw [fieldActor_one, mul_one])
  have e2 := hu (1, frob K ^ k) (by beta_reduce; rw [map_one, one_mul, h1])
  have hk : frob K ^ k = 1 := (congrArg Prod.snd (e2.trans e1.symm))
  rw [← fieldActorHom_apply, ← map_pow, hk, map_one]

end Automorphisms

section Involutions

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ : σ.toRingHom ^ 3 = 1)

local notation "C₀" => graphFixedRootGroup TwistTag.D4 K σ.toRingHom
local notation "GL" => ModGL TwistTag.D4.tag K

theorem involution_conj
    (y : C₀) (hy : orderOf y = 2) :
    ∃ g : C₀, g * y * g⁻¹ = cx₆ σ hσ 1 ∨ g * y * g⁻¹ = cx₄ σ hσ 1 := by
  have hyy : y * y = 1 := by rw [← sq, ← hy, pow_orderOf_eq_one]
  have hy1 : y ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hy
    exact absurd hy (by norm_num)
  rcases CFSG.Quasithin.B42D4.involution_conj σ hσ y hyy hy1 with ⟨g, hg, e⟩ | ⟨g, hg, e⟩
  · exact ⟨⟨g, hg⟩, Or.inl (Subtype.ext e)⟩
  · refine ⟨cu σ * cv σ * ⟨g, hg⟩, Or.inr ?_⟩
    have e' : (⟨g, hg⟩ : C₀) * y * (⟨g, hg⟩ : C₀)⁻¹ = cx₁ σ hσ 1 := Subtype.ext e
    calc cu σ * cv σ * ⟨g, hg⟩ * y * (cu σ * cv σ * ⟨g, hg⟩)⁻¹ =
        cu σ * (cv σ * ((⟨g, hg⟩ : C₀) * y * (⟨g, hg⟩ : C₀)⁻¹) * cv σ) * cu σ := by
          rw [mul_inv_rev, mul_inv_rev, cu_inv, cv_inv]
          group
      _ = cx₄ σ hσ 1 := by rw [e', cv_x₁, cu_x₃]

end Involutions

end Model

open Model in
@[expose] def modelData
    {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K)
    (hσ : σ.toRingHom ^ 3 = 1) (hσq : ∀ c, σ c = c ^ (2 ^ f)) (hK : Nat.card K = (2 ^ f) ^ 3)
    (hk : Nat.card (fixedSubfield σ) = 2 ^ f) :
    TrialityD4Data (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (2 ^ f) where
  Γ := K
  two_pow := ⟨f, hf, rfl⟩
  card_Γ := hK
  σ := σ
  σ_apply := hσq
  σ_cube := cube σ hσ
  card_Γ₀ := hk
  x₁ := cx₁ σ hσ
  x₂ := cx₂ σ hσ
  x₃ := cx₃ σ hσ
  x₄ := cx₄ σ hσ
  x₅ := cx₅ σ hσ
  x₆ := cx₆ σ hσ
  x₁_add := cx₁_add σ hσ
  x₂_add := cx₂_add σ hσ
  x₃_add := cx₃_add σ hσ
  x₄_add := cx₄_add σ hσ
  x₅_add := cx₅_add σ hσ
  x₆_add := cx₆_add σ hσ
  x₁_injective := cx₁_injective σ hσ
  x₂_injective := cx₂_injective σ hσ
  x₃_injective := cx₃_injective σ hσ
  x₄_injective := cx₄_injective σ hσ
  x₅_injective := cx₅_injective σ hσ
  x₆_injective := cx₆_injective σ hσ
  comm₁₂ := cx_comm₁₂ σ hσ
  comm₁₃ := cx_comm₁₃ σ hσ
  comm₁₄ := cx_comm₁₄ σ hσ
  comm₂₅ := cx_comm₂₅ σ hσ
  comm₃₄ := cx_comm₃₄ σ hσ
  commute₁₅ := cx_commute₁₅ σ hσ
  commute₁₆ := cx_commute₁₆ σ hσ
  commute₂₃ := cx_commute₂₃ σ hσ
  commute₂₄ := cx_commute₂₄ σ hσ
  commute₂₆ := cx_commute₂₆ σ hσ
  commute₃₅ := cx_commute₃₅ σ hσ
  commute₃₆ := cx_commute₃₆ σ hσ
  commute₄₅ := cx_commute₄₅ σ hσ
  commute₄₆ := cx_commute₄₆ σ hσ
  commute₅₆ := cx_commute₅₆ σ hσ
  normal_form := normal_form σ hσ
  torus := ctorus σ hσ
  torus_injective := ctorus_injective σ hσ
  torus_x₁ := ctorus_x₁ σ hσ
  torus_x₂ := ctorus_x₂ σ hσ
  torus_x₃ := ctorus_x₃ σ hσ
  torus_x₄ := ctorus_x₄ σ hσ
  torus_x₅ := ctorus_x₅ σ hσ
  torus_x₆ := ctorus_x₆ σ hσ
  normalizer_eq := normalizer_eq σ hσ
  u := cu σ
  v := cv σ
  u_mul_self := cu_mul_self σ
  v_mul_self := cv_mul_self σ
  orderOf_u_mul_v := orderOf_cu_mul_cv σ hσ
  u_x₂ := cu_x₂ σ hσ
  u_x₃ := cu_x₃ σ hσ
  u_x₆ := cu_x₆ σ hσ
  v_x₁ := cv_x₁ σ hσ
  v_x₄ := cv_x₄ σ hσ
  v_x₅ := cv_x₅ σ hσ
  u_torus := cu_torus σ hσ
  v_torus := cv_torus σ hσ
  sup_closure_eq_top := sup_closure_eq_top σ hσ
  card_eq := card_C₀ σ hf hK hσq
  bruhat := bruhat σ hσ
  bruhat_disjoint := bruhat_disjoint σ hσ
  φ := fieldActor σ (frob K)
  φ_x₁ := cφ_x₁ σ hσ
  φ_x₂ := cφ_x₂ σ hσ
  φ_x₃ := cφ_x₃ σ hσ
  φ_x₄ := cφ_x₄ σ hσ
  φ_x₅ := cφ_x₅ σ hσ
  φ_x₆ := cφ_x₆ σ hσ
  φ_u := cφ_u σ
  φ_v := cφ_v σ
  φ_torus := cφ_torus σ hσ
  aut_eq := aut_eq σ hf hK hσq
  φ_pow_eq_conj := cφ_pow_eq_conj σ hf hK hσq
  two_pow_orderOf_φ := by rw [orderOf_cφ σ hf hK hσq, ← pow_mul, mul_comm]
  involution_conj := involution_conj σ hσ

theorem nonempty_trialityD4Data_of_lieModel
    {X : Type} [Group X] {f : ℕ} (hf : 1 ≤ f) (h : LieModel X .trialityD4 0 2 f) :
    Nonempty (TrialityD4Data X (2 ^ f)) := by
  have hm : ChevalleyExceptionalModel X .trialityD4 2 f := by
    simp only [LieModel, classicalTags, chevalleyExceptionalTags, reeTitsTags, Finset.mem_insert,
      Finset.mem_singleton, reduceCtorEq, false_and, false_or, or_false, and_false, true_and,
      or_true] at h
    exact h
  obtain ⟨K, _, _, _, σ, -, hσq, hK, hk, ⟨e⟩⟩ := TrialityCover.triality_model hf hm.2
  have hσ : σ.toRingHom ^ 3 = 1 := RingHom.ext fun c => ringEquiv_cube_apply_eq hK hσq c
  exact ⟨(modelData hf K σ hσ hσq hK hk).ofMulEquiv e.symm⟩

end CFSG.LocalAnalysis.EvenBN.TrialityD4
