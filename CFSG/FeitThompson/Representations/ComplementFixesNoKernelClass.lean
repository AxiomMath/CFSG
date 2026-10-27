module

public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.GroupTheory.FixedPointFree
public import CFSG.FeitThompson.Representations.CoprimeAutomorphismCosetPartition
import CFSG.FeitThompson.Representations.FixedPointFreeComplementOrderBounds
import CFSG.FeitThompson.Representations.CoprimePrimeAutFixedConjugacyClasses
import CFSG.FeitThompson.Foundations.CoprimeActionFittingFaithful

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open SemidirectProduct Pointwise ConjClasses

variable {H E : Type*} [Group H] [Group E] {φ : E →* MulAut H} {u : E} {x : H}

theorem conjClasses_carrier_one {G : Type*} [Group G] : (1 : ConjClasses G).carrier = {1} := by
  ext z
  rw [mem_carrier_iff_mk_eq, show (1 : ConjClasses G) = ConjClasses.mk 1 from rfl,
    mk_eq_mk_iff_isConj, isConj_comm, isConj_one_right, Set.mem_singleton_iff]

theorem conjClasses_eq_one_iff {G : Type*} [Group G] {K : ConjClasses G} :
    K = 1 ↔ K.carrier = {1} :=
  ⟨fun h => by rw [h, conjClasses_carrier_one],
    fun h => conjClasses_carrier_injective (by rw [h, conjClasses_carrier_one])⟩

theorem conjClasses_map_one {G G' : Type*} [Group G] [Group G'] (f : G →* G') :
    ConjClasses.map f (1 : ConjClasses G) = 1 := by
  rw [show (1 : ConjClasses G) = ConjClasses.mk 1 from rfl, conjClasses_map_mk, map_one]
  rfl

theorem image_conjClasses_carrier {G : Type*} [Group G] (e : MulAut G) (K : ConjClasses G) :
    e '' K.carrier = (ConjClasses.map e.toMonoidHom K).carrier :=
  (Set.image_smul (a := e) (t := K.carrier)).trans (carrier_map_mulEquiv e K).symm

theorem conjClasses_map_eq_self_iff {G : Type*} [Group G] (e : MulAut G) (K : ConjClasses G) :
    ConjClasses.map e.toMonoidHom K = K ↔ e '' K.carrier = K.carrier := by
  rw [image_conjClasses_carrier]
  exact ⟨fun h => by rw [h], fun h => conjClasses_carrier_injective h⟩

theorem inr_mul_inl_mul_inr_inv (u : E) (x : H) :
    (inr u : H ⋊[φ] E) * inl x * (inr u)⁻¹ = inl (φ u x) := by
  rw [← map_inv, ← inl_aut]

theorem conjAct_inr_smul_image_inl (u : E) (S : Set H) :
    ConjAct.toConjAct (inr u : H ⋊[φ] E) • ((inl : H →* H ⋊[φ] E) '' S)
      = (inl : H →* H ⋊[φ] E) '' (φ u '' S) := by
  ext y
  simp only [mem_conjAct_smul_set_iff, Set.mem_image]
  refine ⟨?_, ?_⟩
  · rintro ⟨z, hz, hy⟩
    refine ⟨φ u z, ⟨z, hz, rfl⟩, ?_⟩
    rw [← inr_mul_inl_mul_inr_inv, hy]
    group
  · rintro ⟨z, ⟨w, hw, rfl⟩, rfl⟩
    refine ⟨w, hw, ?_⟩
    rw [← inr_mul_inl_mul_inr_inv]
    group

instance instFiniteRangeInl [Finite H] : Finite ((inl : H →* H ⋊[φ] E).range) :=
  (Set.finite_range (inl : H → H ⋊[φ] E)).to_subtype

theorem isOfFinOrder_inr [Finite E] (u : E) : IsOfFinOrder (inr u : H ⋊[φ] E) := by
  obtain ⟨n, hn, hu⟩ := isOfFinOrder_iff_pow_eq_one.1 (isOfFinOrder_of_finite u)
  exact isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, by rw [← map_pow, hu, map_one]⟩

theorem inr_mem_normalizer_range_inl (u : E) :
    (inr u : H ⋊[φ] E) ∈ Subgroup.normalizer ((inl : H →* H ⋊[φ] E).range : Set (H ⋊[φ] E)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨?_, ?_⟩
  · rintro ⟨z, rfl⟩
    exact ⟨φ u z, (inr_mul_inl_mul_inr_inv u z).symm⟩
  · rintro ⟨z, hz⟩
    refine ⟨(φ u)⁻¹ z, ?_⟩
    have h1 : (inr u : H ⋊[φ] E) * inl ((φ u)⁻¹ z) * (inr u)⁻¹ = inl z := by
      rw [inr_mul_inl_mul_inr_inv]; simp
    rw [hz] at h1
    exact mul_left_cancel (mul_right_cancel h1)

theorem inf_centralizer_inr_eq_bot (hφ : MonoidHom.FixedPointFree (φ u : H → H)) :
    (inl : H →* H ⋊[φ] E).range ⊓ Subgroup.centralizer {(inr u : H ⋊[φ] E)} = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  rintro y hy
  obtain ⟨⟨z, rfl⟩, hc⟩ := Subgroup.mem_inf.1 hy
  have h1 : (inl z : H ⋊[φ] E) * inr u = inr u * inl z :=
    Subgroup.mem_centralizer_singleton_iff.1 hc
  have h2 : (inl (φ u z) : H ⋊[φ] E) = inl z := by
    rw [← inr_mul_inl_mul_inr_inv, ← h1]; group
  rw [hφ z (inl_inj.1 h2)]
  simp

theorem centralizerCoset_range_inl_inr (hφ : MonoidHom.FixedPointFree (φ u : H → H)) :
    centralizerCoset (inl : H →* H ⋊[φ] E).range (inr u) = {inr u} := by
  ext y
  rw [mem_centralizerCoset_iff, inf_centralizer_inr_eq_bot hφ, Subgroup.mem_bot,
    mul_inv_eq_one, Set.mem_singleton_iff]

theorem finite_of_fixedPointFree [Finite H] [Nontrivial H]
    (hφ : ∀ v : E, v ≠ 1 → MonoidHom.FixedPointFree (φ v : H → H)) : Finite E := by
  have h := coprime_card_of_fixedPointFree hφ
  have h1 : 1 < Nat.card H := Finite.one_lt_card_iff_nontrivial.2 ‹_›
  refine Nat.finite_of_card_ne_zero fun h0 => ?_
  rw [h0, Nat.coprime_zero_right] at h
  omega

theorem coprime_natCard_range_inl_orderOf_inr [Finite H] [Nontrivial H]
    (hφ : ∀ v : E, v ≠ 1 → MonoidHom.FixedPointFree (φ v : H → H)) (u : E) :
    (Nat.card ((inl : H →* H ⋊[φ] E).range)).Coprime (orderOf (inr u : H ⋊[φ] E)) := by
  rw [natCard_range_inl, orderOf_injective _ inr_injective u]
  exact (coprime_card_of_fixedPointFree hφ).coprime_dvd_right (orderOf_dvd_natCard u)

theorem exists_conj_eq_of_mem_coset_inr [Finite H] [Nontrivial H]
    (hφ : ∀ v : E, v ≠ 1 → MonoidHom.FixedPointFree (φ v : H → H)) (hu : u ≠ 1)
    {y : H ⋊[φ] E} (hy : y ∈ ((inl : H →* H ⋊[φ] E).range : Set (H ⋊[φ] E)) * {inr u}) :
    ∃ g ∈ (inl : H →* H ⋊[φ] E).range, g * inr u * g⁻¹ = y := by
  have : Finite E := finite_of_fixedPointFree hφ
  have hkey := sUnion_centralizerCosetConjugates
    (coprime_natCard_range_inl_orderOf_inr hφ u) (isOfFinOrder_inr u)
    (inr_mem_normalizer_range_inl (φ := φ) u)
  rw [← hkey, Set.mem_sUnion] at hy
  obtain ⟨S, hS, hyS⟩ := hy
  obtain ⟨g, hg, rfl⟩ := mem_centralizerCosetConjugates_iff.1 hS
  rw [mem_conjAct_smul_set_iff, centralizerCoset_range_inl_inr (hφ u hu),
    Set.mem_singleton_iff] at hyS
  exact ⟨g, hg, by rw [← hyS]; group⟩

theorem eq_one_of_isConj_apply [Finite H] [Nontrivial H]
    (hφ : ∀ v : E, v ≠ 1 → MonoidHom.FixedPointFree (φ v : H → H)) (hu : u ≠ 1)
    (hx : IsConj (φ u x) x) : x = 1 := by
  obtain ⟨c, hc⟩ := isConj_iff.1 hx
  set g : H ⋊[φ] E := inl c * inr u with hg
  have hgc : g * inl x * g⁻¹ = inl x := by
    rw [hg]
    calc inl c * inr u * inl x * (inl c * inr u)⁻¹
        = inl c * (inr u * inl x * (inr u)⁻¹) * (inl c)⁻¹ := by group
      _ = inl (c * φ u x * c⁻¹) := by rw [inr_mul_inl_mul_inr_inv]; simp
      _ = inl x := by rw [hc]
  obtain ⟨h, hh, hgh⟩ := exists_conj_eq_of_mem_coset_inr hφ hu
    (y := g) ⟨inl c, ⟨c, rfl⟩, inr u, rfl, rfl⟩
  set w : H ⋊[φ] E := h⁻¹ * inl x * h with hw
  have hconj : h * inr u * h⁻¹ * inl x * (h * inr u * h⁻¹)⁻¹ = inl x := by rw [hgh]; exact hgc
  have h2 : (inr u : H ⋊[φ] E) * w * (inr u)⁻¹ = w := by
    calc (inr u : H ⋊[φ] E) * w * (inr u)⁻¹
        = h⁻¹ * (h * inr u * h⁻¹ * inl x * (h * inr u * h⁻¹)⁻¹) * h := by rw [hw]; group
      _ = w := by rw [hconj, hw]
  have hmem : w ∈ (inl : H →* H ⋊[φ] E).range ⊓ Subgroup.centralizer {(inr u : H ⋊[φ] E)} := by
    refine Subgroup.mem_inf.2 ⟨?_, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    · rw [hw]
      exact ((inl : H →* H ⋊[φ] E).range).mul_mem
        (((inl : H →* H ⋊[φ] E).range).mul_mem
          (((inl : H →* H ⋊[φ] E).range).inv_mem hh) ⟨x, rfl⟩) hh
    · exact (mul_inv_eq_iff_eq_mul.1 h2).symm
  rw [inf_centralizer_inr_eq_bot (hφ u hu), Subgroup.mem_bot, hw] at hmem
  have hx1 : (inl x : H ⋊[φ] E) = 1 := by
    have hxc : (inl x : H ⋊[φ] E) = h * (h⁻¹ * inl x * h) * h⁻¹ := by group
    rw [hmem] at hxc
    simpa using hxc
  exact inl_inj.1 (by rw [hx1]; simp)

theorem conjClasses_map_eq_self_iff_eq_one [Finite H] [Nontrivial H]
    (hφ : ∀ v : E, v ≠ 1 → MonoidHom.FixedPointFree (φ v : H → H)) (hu : u ≠ 1)
    (K : ConjClasses H) : ConjClasses.map (φ u).toMonoidHom K = K ↔ K = 1 := by
  refine ⟨fun h => ?_, fun h => by rw [h]; exact conjClasses_map_one _⟩
  obtain ⟨y, rfl⟩ := ConjClasses.mk_surjective K
  rw [conjClasses_map_mk, mk_eq_mk_iff_isConj] at h
  rw [eq_one_of_isConj_apply hφ hu h]
  rfl

theorem conjAct_inr_smul_image_carrier_eq_iff [Finite H] [Nontrivial H]
    (hφ : ∀ v : E, v ≠ 1 → MonoidHom.FixedPointFree (φ v : H → H)) (hu : u ≠ 1)
    (K : ConjClasses H) :
    ConjAct.toConjAct (inr u : H ⋊[φ] E) • ((inl : H →* H ⋊[φ] E) '' K.carrier)
      = (inl : H →* H ⋊[φ] E) '' K.carrier ↔
      (inl : H →* H ⋊[φ] E) '' K.carrier = {1} := by
  rw [conjAct_inr_smul_image_inl, Set.image_eq_image inl_injective,
    ← conjClasses_map_eq_self_iff, conjClasses_map_eq_self_iff_eq_one hφ hu,
    show ({1} : Set (H ⋊[φ] E)) = (inl : H → H ⋊[φ] E) '' {1} by simp,
    Set.image_eq_image inl_injective]
  exact conjClasses_eq_one_iff

end CFSG.FeitThompson
