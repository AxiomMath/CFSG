module

public import CFSG.LieType.Chevalley.TwistedE6NormalForm
public import CFSG.LieType.Chevalley.C2E6StandardFixedTorus
public import CFSG.LieType.Chevalley.C2E6StandardLevi
public import CFSG.ClassicalGroups.Orthogonal.ProjectiveSimple
public import CFSG.LieType.Chevalley.C2E6ExactRootRestrictions
public import CFSG.LieType.Chevalley.C2E6StandardFixedBorelOrder
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LieType.Chevalley.GraphFixedParabolicLevi

public section

namespace CFSG.EvenSmallLie.TwoE6

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Overlap
  CFSG.LieType.Chevalley.C2E6Std
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open scoped Pointwise

local notation "C₀" => graphFixedRootGroup TwistTag.E6 K barHom

theorem map_conj_eq_of_mem_normalizer {G : Type*} [Group G] {H : Subgroup G} {c : G}
    (hc : c ∈ normalizer (H : Set G)) : H.map (MulAut.conj c).toMonoidHom = H := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (mem_normalizer_iff.1 hc x).1 hx
  · intro hy
    refine ⟨c⁻¹ * y * c, ?_, ?_⟩
    · have h := (mem_normalizer_iff.1 (inv_mem hc) y).1 hy
      rwa [inv_inv] at h
    · change c * (c⁻¹ * y * c) * c⁻¹ = y
      group

theorem card_le_card_of_ker_le {O A : Type*} [Group O] [Finite O] [Group A] [Finite A]
    (Θ : O →* A) {D : Subgroup O} (hD : Θ.ker ≤ D) (hD3 : Nat.card D ≤ 3) {d : O} (hdD : d ∈ D)
    {I : Subgroup O} (hdI : d ∉ I) : Nat.card I ≤ Nat.card A := by
  refine Nat.card_le_card_of_injective (Θ.comp I.subtype)
    ((injective_iff_map_eq_one _).2 fun x hx => ?_)
  by_contra hx1
  have hx1' : (x : O) ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hle : zpowers (x : O) ≤ D := zpowers_le.2 (hD hx)
  have h2 : 2 ≤ Nat.card (zpowers (x : O)) := by
    rw [Nat.card_zpowers]
    have h0 := orderOf_pos (x : O)
    have h1 : orderOf (x : O) ≠ 1 := fun h => hx1' (orderOf_eq_one_iff.1 h)
    omega
  have hdvd : Nat.card (zpowers (x : O)) ∣ Nat.card D := card_dvd_of_le hle
  have hD0 : 0 < Nat.card D := Nat.card_pos
  have heq : Nat.card (zpowers (x : O)) = Nat.card D := by
    have hle' := Nat.le_of_dvd hD0 hdvd
    interval_cases h : Nat.card D <;> interval_cases hz : Nat.card (zpowers (x : O)) <;> omega
  have hxD : zpowers (x : O) = D := eq_of_le_of_card_ge hle heq.ge
  exact hdI (zpowers_le.2 x.2 (hxD ▸ hdD))

theorem natCard_K_sq : Nat.card K = (2 ^ 1) ^ 2 := by
  rw [Nat.card_eq_fintype_card, card_K]
  norm_num

theorem pow_three_eq_one_of_ne_zero {c : K} (hc : c ≠ 0) : c ^ 3 = 1 := by
  have h := FiniteField.pow_card_sub_one_eq_one c hc
  rwa [card_K] at h

theorem natCard_units_K : Nat.card Kˣ = 3 := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_units, card_K]

theorem natCard_ringAut_K : Nat.card (RingAut K) = 2 :=
  (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_two K
    (by rw [natCard_K_sq]; norm_num)).1

theorem normalForm_std :
    (∃ Θ : MulAut C₀ →* RingAut K,
      Θ.ker = inner C₀ ⊔ (compatDiagAutHom TwistTag.E6 K barHom).range) ∧
    (∀ c, c ∈ orbitField TwistTag.E6 K barHom ⟨2, by decide⟩ ↔ barEquiv c = c) ∧
    (∀ c, c ∈ orbitField TwistTag.E6 K barHom ⟨3, by decide⟩ ↔ barEquiv c = c) := by
  have h : ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (2 ^ 1)) →
      (∃ Θ : MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) →* RingAut K,
        Θ.ker = inner (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ⊔
          (compatDiagAutHom TwistTag.E6 K σ.toRingHom).range) ∧
      (∀ c, c ∈ orbitField TwistTag.E6 K σ.toRingHom ⟨2, by decide⟩ ↔ σ c = c) ∧
      (∀ c, c ∈ orbitField TwistTag.E6 K σ.toRingHom ⟨3, by decide⟩ ↔ σ c = c) := by
    intro σ hσ
    obtain ⟨-, -, h2, h3, -, -, -, -, ⟨Θ, -, -, hker, -⟩, -⟩ :=
      twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two le_rfl K
        natCard_K_sq σ hσ
    exact ⟨⟨Θ, hker⟩, h2, h3⟩
  have h' := h barEquiv fun c => by
    change bar c = _
    rfl
  rw [barEquiv_toRingHom] at h'
  exact h'

abbrev DiagParam : Type :=
  (a : Fin TwistTag.E6.foldedTag.rank) → (orbitField TwistTag.E6 K barHom a)ˣ

theorem diagParam_pow_three (u : DiagParam) : u ^ 3 = 1 := by
  funext a
  refine Units.ext (Subtype.ext ?_)
  change (((u a : orbitField TwistTag.E6 K barHom a) : K)) ^ 3 = 1
  refine pow_three_eq_one_of_ne_zero fun h => (u a).ne_zero (Subtype.ext ?_)
  exact h

theorem subsingleton_units_of_fixed {a : Fin TwistTag.E6.foldedTag.rank}
    (ha : ∀ c, c ∈ orbitField TwistTag.E6 K barHom a ↔ barEquiv c = c) :
    Subsingleton (orbitField TwistTag.E6 K barHom a)ˣ := by
  refine ⟨fun u v => ?_⟩
  have key : ∀ w : (orbitField TwistTag.E6 K barHom a)ˣ, w = 1 := fun w => by
    refine Units.ext (Subtype.ext ?_)
    set c := ((w : orbitField TwistTag.E6 K barHom a) : K)
    have hc0 : c ≠ 0 := fun h => w.ne_zero (Subtype.ext h)
    have hc : c ^ 2 = c := (ha c).1 (w : orbitField TwistTag.E6 K barHom a).2
    have h1 : c * (c - 1) = 0 := by
      rw [mul_sub, mul_one, ← sq, hc, sub_self]
    rcases mul_eq_zero.1 h1 with h | h
    · exact absurd h hc0
    · exact sub_eq_zero.1 h
  rw [key u, key v]

theorem natCard_units_orbitField_le (a : Fin TwistTag.E6.foldedTag.rank) :
    Nat.card (orbitField TwistTag.E6 K barHom a)ˣ ≤ 3 := by
  rw [← natCard_units_K]
  refine Nat.card_le_card_of_injective (Units.map (orbitField TwistTag.E6 K barHom a).subtype)
    fun u v h => Units.ext (Subtype.ext ?_)
  exact congrArg Units.val h

theorem natCard_diagParam_le :
    Nat.card DiagParam ≤ 9 := by
  obtain ⟨-, h2, h3⟩ := normalForm_std
  have := subsingleton_units_of_fixed h2
  have := subsingleton_units_of_fixed h3
  rw [Nat.card_pi]
  change ∏ a : Fin 4, Nat.card (orbitField TwistTag.E6 K barHom a)ˣ ≤ 9
  rw [Fin.prod_univ_four]
  have e0 := natCard_units_orbitField_le ⟨0, by decide⟩
  have e1 := natCard_units_orbitField_le ⟨1, by decide⟩
  have e2 : Nat.card (orbitField TwistTag.E6 K barHom ⟨2, by decide⟩)ˣ ≤ 1 :=
    Finite.card_le_one_iff_subsingleton.2 inferInstance
  have e3 : Nat.card (orbitField TwistTag.E6 K barHom ⟨3, by decide⟩)ˣ ≤ 1 :=
    Finite.card_le_one_iff_subsingleton.2 inferInstance
  calc _ ≤ 3 * 3 * 1 * 1 := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul e0 e1) e2) e3
    _ = 9 := rfl

theorem exists_diagParam_ne_one_mem_inner :
    ∃ w : DiagParam, w ≠ 1 ∧ compatDiagAutHom TwistTag.E6 K barHom w ∈ inner C₀ := by
  set t₀ : C₀ := ⟨fixedTorusGen, fixedTorusGen_mem_stdGroup⟩
  have hT : fixedTorusGen ∈ graphFixedRootTorus TwistTag.E6 K barHom := by
    have h := fixedTorusGen_mem_stdTorus0
    rwa [stdTorus0_eq_stdTorus] at h
  have hA : MulAut.conj t₀ ∈ graphFixedUnipotentStabilizer TwistTag.E6 K barHom := by
    refine ⟨?_, ?_⟩
    · rw [map_conj_subgroupOf (graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _) t₀,
        map_conj_eq_of_mem_normalizer (graphFixedRootTorus_le_normalizer_graphFixedPosUnipotent hT)]
    · rw [map_conj_subgroupOf (graphFixedNegUnipotent_le_graphFixedRootGroup _ _ _) t₀,
        map_conj_eq_of_mem_normalizer (graphFixedRootTorus_le_normalizer_graphFixedNegUnipotent hT)]
  obtain ⟨w, hw⟩ := exists_conj_eq_compatDiagAutHom barHom_surjective hA
  refine ⟨w, fun h1 => ?_, ⟨t₀, hw⟩⟩
  rw [h1, map_one] at hw
  have hZ : t₀ ∈ center C₀ := by
    rw [mem_center_iff]
    intro g
    have h := congrArg (fun α : MulAut C₀ => α g) hw
    change t₀ * g * t₀⁻¹ = g at h
    calc g * t₀ = t₀ * g * t₀⁻¹ * t₀ := by rw [h]
      _ = t₀ * g := by group
  rw [center_graphFixedRootGroup_eq_bot barHom_surjective, mem_bot] at hZ
  exact fixedTorusGen_ne_one (congrArg Subtype.val hZ)

@[expose] noncomputable def diagOut :
    DiagParam →* Outer C₀ :=
  (QuotientGroup.mk' (inner C₀)).comp (compatDiagAutHom TwistTag.E6 K barHom)

theorem card_range_diagOut_le_three :
    Nat.card diagOut.range ≤ 3 := by
  obtain ⟨w, hw1, hw⟩ := exists_diagParam_ne_one_mem_inner
  have hwk : w ∈ diagOut.ker := by
    rw [MonoidHom.mem_ker, diagOut, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    exact hw
  have hk3 : 3 ≤ Nat.card diagOut.ker := by
    have hle : zpowers w ≤ diagOut.ker := zpowers_le.2 hwk
    have hw3 : orderOf w = 3 := orderOf_eq_prime (diagParam_pow_three w) hw1
    calc 3 = Nat.card (zpowers w) := by rw [Nat.card_zpowers, hw3]
      _ ≤ _ := card_le_of_le hle
  have hcard := card_eq_card_quotient_mul_card_subgroup diagOut.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange diagOut).toEquiv] at hcard
  have h9 := natCard_diagParam_le
  by_contra h
  have : 4 * 3 ≤ Nat.card diagOut.range * Nat.card diagOut.ker :=
    Nat.mul_le_mul (by omega) hk3
  omega

theorem exists_outer_hom :
    ∃ Θ : Outer C₀ →* RingAut K, Θ.ker ≤ diagOut.range := by
  obtain ⟨⟨Θ, hΘ⟩, -, -⟩ := normalForm_std
  have hinn : inner C₀ ≤ Θ.ker := hΘ ▸ le_sup_left
  refine ⟨QuotientGroup.lift (inner C₀) Θ hinn, fun x hx => ?_⟩
  obtain ⟨α, rfl⟩ := QuotientGroup.mk_surjective x
  have hα : α ∈ inner C₀ ⊔ (compatDiagAutHom TwistTag.E6 K barHom).range := by
    rw [← hΘ, MonoidHom.mem_ker]
    exact hx
  have hα' : α ∈ ((inner C₀ : Set (MulAut C₀)) *
      ((compatDiagAutHom TwistTag.E6 K barHom).range : Set (MulAut C₀))) := by
    rw [← Subgroup.normal_mul]
    exact hα
  obtain ⟨i, hi, d, ⟨u, rfl⟩, rfl⟩ := hα'
  refine ⟨u, ?_⟩
  rw [diagOut, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk_mul,
    (QuotientGroup.eq_one_iff i).2 hi, one_mul]

theorem card_le_two_of_not_mem
    {I : Subgroup (Outer C₀)} {u : DiagParam}
    (hu : diagOut u ∉ I) : Nat.card I ≤ 2 := by
  obtain ⟨Θ, hΘ⟩ := exists_outer_hom
  have : Finite (RingAut K) := Nat.finite_of_card_ne_zero (by rw [natCard_ringAut_K]; norm_num)
  rw [← natCard_ringAut_K]
  exact card_le_card_of_ker_le Θ hΘ card_range_diagOut_le_three ⟨u, rfl⟩ hu

theorem card_le_two_of_not_mem_std
    {I : Subgroup (Outer stdGroup)} {δ : MulAut stdGroup}
    (hδ : ∃ u, δ = compatDiagAutHom TwistTag.E6 K barHom u)
    (hI : (QuotientGroup.mk δ : Outer stdGroup) ∉ I) : Nat.card I ≤ 2 := by
  obtain ⟨u, rfl⟩ := hδ
  exact card_le_two_of_not_mem hI

end CFSG.EvenSmallLie.TwoE6
