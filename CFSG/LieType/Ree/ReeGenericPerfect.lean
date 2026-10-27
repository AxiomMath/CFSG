module

public import CFSG.LieType.Ree.PositiveTorusCentralizer
public import CFSG.LieType.Ree.LargeReeSylowOpposition
public import CFSG.LieType.Ree.NormalPositiveGeneration
public import CFSG.LocalAnalysis.ComponentInitial.CoprimeCommutatorFactorization

public noncomputable section

namespace CFSG.LieType.Ree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

namespace ReeTag

variable {t : ReeTag} {K : Type} [Field K] [Finite K] [CharP K t.prime] {a : ℕ}

theorem reeFixedTorus_le_normalizer_reeFixedPosUnipotent :
    t.reeFixedTorus K a ≤
      Subgroup.normalizer (t.reeFixedPosUnipotent K a : Set (ModGL t.tag K)) :=
  fun _ hh => reeFixedBorel_le_normalizer_reeFixedPosUnipotent (reeFixedTorus_le_reeFixedBorel hh)

variable (t K a) in
@[expose, instance_reducible] def reeFixedConjAction :
    MulDistribMulAction (t.reeFixedTorus K a) (t.reeFixedPosUnipotent K a) where
  smul h s := ⟨(h : ModGL t.tag K) * s * (h : ModGL t.tag K)⁻¹,
    (Subgroup.mem_normalizer_iff.1 (reeFixedTorus_le_normalizer_reeFixedPosUnipotent h.2) s).1
      s.2⟩
  one_smul s := Subtype.ext (by
    change ((1 : t.reeFixedTorus K a) : ModGL t.tag K) * s *
      ((1 : t.reeFixedTorus K a) : ModGL t.tag K)⁻¹ = s
    simp)
  mul_smul h h' s := Subtype.ext (by
    change ((h * h' : t.reeFixedTorus K a) : ModGL t.tag K) * s *
        ((h * h' : t.reeFixedTorus K a) : ModGL t.tag K)⁻¹ =
      (h : ModGL t.tag K) * ((h' : ModGL t.tag K) * s * (h' : ModGL t.tag K)⁻¹) *
        (h : ModGL t.tag K)⁻¹
    simp only [Subgroup.coe_mul]
    group)
  smul_mul h s s' := Subtype.ext (by
    change (h : ModGL t.tag K) * ((s * s' : t.reeFixedPosUnipotent K a) : ModGL t.tag K) *
        (h : ModGL t.tag K)⁻¹ =
      ((h : ModGL t.tag K) * s * (h : ModGL t.tag K)⁻¹) *
        ((h : ModGL t.tag K) * s' * (h : ModGL t.tag K)⁻¹)
    simp only [Subgroup.coe_mul]
    group)
  smul_one h := Subtype.ext (by
    change (h : ModGL t.tag K) * ((1 : t.reeFixedPosUnipotent K a) : ModGL t.tag K) *
      (h : ModGL t.tag K)⁻¹ = 1
    simp)

attribute [local instance] reeFixedConjAction

theorem fixedPointSubgroup_reeFixedConjAction_eq_bot
    (ha : 1 ≤ a)
    (hK : Nat.card K = t.prime ^ (2 * a + 1)) :
    CFSG.fixedPointSubgroup (t.reeFixedTorus K a) (t.reeFixedPosUnipotent K a) = ⊥ := by
  rw [eq_bot_iff]
  intro s hs
  have hC : (s : ModGL t.tag K) ∈ t.reeFixedPosUnipotent K a ⊓
      Subgroup.centralizer (t.reeFixedTorus K a : Set (ModGL t.tag K)) := by
    refine Subgroup.mem_inf.2 ⟨s.2, Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
    have h1 : h * (s : ModGL t.tag K) * h⁻¹ = s := congrArg Subtype.val (hs ⟨h, hh⟩)
    calc h * (s : ModGL t.tag K) = (h * (s : ModGL t.tag K) * h⁻¹) * h := by group
      _ = s * h := by rw [h1]
  rw [(ree_positive_fixed_torus_centralizer t a ha K hK).2, Subgroup.mem_bot] at hC
  exact Subgroup.mem_bot.2 (Subtype.ext hC)

theorem not_dvd_card_reeFixedTorus
    [Fact t.prime.Prime] :
    ¬ t.prime ∣ Nat.card (t.reeFixedTorus K a) := by
  have := finite_modGL (τ := t.tag) (K := K)
  intro hdvd
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' t.prime hdvd
  have h1 : g ^ (Nat.card K - 1) = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact pow_card_sub_one_eq_one_of_mem_diagonalGroup
      (torusGroup_le_diagonalGroup (Subgroup.mem_inf.1 g.2).1))
  have h2 := orderOf_dvd_of_pow_eq_one h1
  rw [hg] at h2
  exact not_dvd_natCard_sub_one (K := K) t.prime h2

theorem commutator_reeFixedPosUnipotent_reeFixedTorus
    (ha : 1 ≤ a)
    (hK : Nat.card K = t.prime ^ (2 * a + 1)) :
    ⁅t.reeFixedPosUnipotent K a, t.reeFixedTorus K a⁆ = t.reeFixedPosUnipotent K a := by
  have : Fact t.prime.Prime := ⟨by cases t <;> decide⟩
  have := finite_modGL (τ := t.tag) (K := K)
  refine le_antisymm ((Subgroup.commutator_le).2 fun u hu h hh => ?_) fun u hu => ?_
  · have h' := (Subgroup.mem_normalizer_iff.1
      (reeFixedTorus_le_normalizer_reeFixedPosUnipotent hh) u⁻¹).1 (inv_mem hu)
    rw [commutatorElement_def, mul_assoc, mul_assoc, ← mul_assoc h]
    exact mul_mem hu h'
  · have hQ : IsPGroup t.prime (t.reeFixedPosUnipotent K a) :=
      (isPGroup_posUnipotent t.prime t.tag).to_le inf_le_left
    obtain ⟨hfac, -⟩ := coprime_pgroup_commutator_factorization (A := t.reeFixedTorus K a)
      Fact.out hQ not_dvd_card_reeFixedTorus
    obtain ⟨d, hd, c, hc, hdc⟩ := hfac ⟨u, hu⟩
    rw [fixedPointSubgroup_reeFixedConjAction_eq_bot ha hK, Subgroup.mem_bot] at hc
    rw [hc, mul_one] at hdc
    have hle : actionCommutator (t.reeFixedTorus K a) (⊤ : Subgroup (t.reeFixedPosUnipotent K a)) ≤
        (⁅t.reeFixedPosUnipotent K a, t.reeFixedTorus K a⁆).comap
          (t.reeFixedPosUnipotent K a).subtype := by
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨q, -, h, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap]
      have e : (t.reeFixedPosUnipotent K a).subtype (q⁻¹ * (h • q)) =
          ⁅(q : ModGL t.tag K)⁻¹, (h : ModGL t.tag K)⁆ := by
        change (q : ModGL t.tag K)⁻¹ * ((h : ModGL t.tag K) * q * (h : ModGL t.tag K)⁻¹) = _
        rw [commutatorElement_def, inv_inv]
        group
      rw [e]
      exact Subgroup.commutator_mem_commutator (inv_mem q.2) h.2
    rw [← hdc] at hd
    exact hle hd

theorem commutator_reeGamma_eq_top
    (ha : 1 ≤ a) (hK : Nat.card K = t.prime ^ (2 * a + 1)) :
    _root_.commutator (t.reeGamma K a) = ⊤ := by
  have hUD : ∀ u ∈ t.reeFixedPosUnipotent K a,
      u ∈ (_root_.commutator (t.reeGamma K a)).map (t.reeGamma K a).subtype := by
    intro u hu
    rw [Subgroup.map_subtype_commutator]
    rw [← commutator_reeFixedPosUnipotent_reeFixedTorus ha hK] at hu
    exact Subgroup.commutator_mono reeFixedPosUnipotent_le_reeGamma
      (reeFixedTorus_le_reeFixedBorel.trans reeFixedBorel_le_reeGamma) hu
  have hle : Subgroup.closure {x | ∃ g ∈ t.reeGamma K a, ∃ u ∈ t.reeFixedPosUnipotent K a,
      g * u * g⁻¹ = x} ≤ (_root_.commutator (t.reeGamma K a)).map (t.reeGamma K a).subtype := by
    rw [Subgroup.closure_le]
    rintro _ ⟨g, hg, u, hu, rfl⟩
    obtain ⟨d, hd, hdu⟩ := hUD u hu
    refine ⟨⟨g, hg⟩ * d * ⟨g, hg⟩⁻¹,
      (inferInstance : (_root_.commutator (t.reeGamma K a)).Normal).conj_mem d hd _, ?_⟩
    rw [map_mul, map_mul, map_inv, hdu]
    rfl
  rw [ree_normal_positive_generation t a K hK] at hle
  refine eq_top_iff.2 fun x _ => ?_
  obtain ⟨d, hd, hdx⟩ := hle x.2
  rwa [show d = x from Subtype.ext hdx] at hd

theorem nontrivial_reeGamma :
    Nontrivial (t.reeGamma K a) := by
  obtain ⟨u, hu, hu1⟩ := exists_ne_one_mem_reeFixedOrbitUnipotent (K := K) (a := a) (t := t)
    ⟨0, by cases t <;> decide⟩
  exact ⟨⟨⟨u, (Subgroup.mem_inf.1 hu).2⟩, 1, fun h => hu1 (congrArg Subtype.val h)⟩⟩

theorem ree_generic_fixed_group_perfect
    (t : ReeTag) (a : ℕ) (ha : 1 ≤ a) (K : Type) [Field K]
    [Finite K] [CharP K t.prime] (hK : Nat.card K = t.prime ^ (2 * a + 1)) :
    ⁅t.reeFixedPosUnipotent K a, t.reeFixedTorus K a⁆ = t.reeFixedPosUnipotent K a ∧
    _root_.commutator (t.reeGamma K a) = ⊤ ∧
    Nontrivial (t.reeGamma K a ⧸ Subgroup.center (t.reeGamma K a)) ∧
    _root_.commutator (t.reeGamma K a ⧸ Subgroup.center (t.reeGamma K a)) = ⊤ := by
  have hcomm := commutator_reeGamma_eq_top ha hK
  refine ⟨commutator_reeFixedPosUnipotent_reeFixedTorus ha hK, hcomm, ?_, ?_⟩
  · obtain ⟨x, y, hxy⟩ := (nontrivial_reeGamma (t := t) (K := K) (a := a)).exists_pair_ne
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    have hZ : ∀ g : t.reeGamma K a, g ∈ Subgroup.center (t.reeGamma K a) := fun g => by
      rw [← QuotientGroup.eq_one_iff]
      exact Subsingleton.elim _ _
    have hbot : _root_.commutator (t.reeGamma K a) = ⊥ := by
      rw [_root_.commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact fun g _ => Subgroup.mem_centralizer_iff.2 fun h _ =>
        (Subgroup.mem_center_iff.1 (hZ g) h)
    have hx : x ∈ _root_.commutator (t.reeGamma K a) := by
      rw [hcomm]
      exact Subgroup.mem_top x
    have hy : y ∈ _root_.commutator (t.reeGamma K a) := by
      rw [hcomm]
      exact Subgroup.mem_top y
    rw [hbot, Subgroup.mem_bot] at hx hy
    exact hxy (hx.trans hy.symm)
  · rw [← derivedSeries_one, ← map_derivedSeries_eq
      (QuotientGroup.mk'_surjective (Subgroup.center (t.reeGamma K a))) 1, derivedSeries_one,
      hcomm, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]

end ReeTag

end CFSG.LieType.Ree
