module

public import CFSG.ClassicalInvolution.AschTight.S1911FusF
public import CFSG.ClassicalInvolution.Asc77.AscSixModCent
import CFSG.ClassicalInvolution.Asc77.AscOddCoreNormalEng
public import CFSG.ClassicalInvolution.AschTight.S1911Facts
public import CFSG.ClassicalInvolution.Uniform.UStand

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T6

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {C : Subgroup G}

omit [Finite G] in
theorem conjSub_inf_eq {c : G} (hc : c ∈ C) : conjSub c (K ⊓ C) = conjSub c K ⊓ C := by
  rw [conjSub, Subgroup.map_inf_eq _ _ _ (MulAut.conj c).injective]
  change conjSub c K ⊓ conjSub c C = _
  rw [conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer hc)]

omit [Finite G] in
theorem map_conjSub_sec (c : ↥C) :
    (conjSub c ((K ⊓ C).subgroupOf C)).map C.subtype = conjSub (c : G) K ⊓ C := by
  rw [conjSub_subgroupOf, Subgroup.subgroupOf_map_subtype, conjSub_inf_eq c.2, inf_assoc,
    inf_idem]

omit [Finite G] in
theorem conjSub_sec_eq {c₁ c₂ : ↥C} (h : conjSub (c₁ : G) K = conjSub (c₂ : G) K) :
    conjSub c₁ ((K ⊓ C).subgroupOf C) = conjSub c₂ ((K ⊓ C).subgroupOf C) := by
  apply Subgroup.map_injective C.subtype_injective
  rw [map_conjSub_sec, map_conjSub_sec, h]

omit [Finite G] in
theorem conjSub_ne_of_ne_sec {c₁ c₂ : ↥C}
    (hne : conjSub c₁ ((K ⊓ C).subgroupOf C) ≠ conjSub c₂ ((K ⊓ C).subgroupOf C)) :
    conjSub (c₁ : G) K ≠ conjSub (c₂ : G) K := fun h => hne (conjSub_sec_eq h)

omit [Finite G] in
theorem mem_normalizer_conjSub_of_sec (c v : ↥C)
    (hv : (v : G) ∈ Subgroup.normalizer ((conjSub (c : G) K : Subgroup G) : Set G)) :
    v ∈ Subgroup.normalizer ((conjSub c ((K ⊓ C).subgroupOf C) : Subgroup ↥C) : Set ↥C) := by
  refine mem_normalizer_iff_conjSub_eq.mpr ?_
  apply Subgroup.map_injective C.subtype_injective
  rw [← conjSub_mul, map_conjSub_sec, map_conjSub_sec, Subgroup.coe_mul,
    conjSub_mul, conjSub_eq_of_mem_normalizer hv]

omit [Finite G] in
theorem le_conjSub_of_mem_sec (c : ↥C) {x : ↥C} (hx : x ∈ conjSub c ((K ⊓ C).subgroupOf C)) :
    (x : G) ∈ conjSub (c : G) K := by
  have h : (x : G) ∈ (conjSub c ((K ⊓ C).subgroupOf C)).map C.subtype := ⟨x, hx, rfl⟩
  rw [map_conjSub_sec] at h
  exact h.1

omit [Finite G] in
theorem le_oddCoreOf_of_normalizes_of_odd {M N : Subgroup G} (hNM : N ≤ M)
    (hn : M ≤ Subgroup.normalizer (N : Set G)) (hodd : Odd (Nat.card N)) : N ≤ oddCoreOf M :=
  CFSG.ClassicalInvolution.Asc77.AscFusion.le_oddCoreOf_of_normal_odd_gen hNM hn hodd

theorem commutator_le_oddCoreOf_sec (c₁ c₂ : ↥C)
    (h : ⁅conjSub (c₁ : G) K, conjSub (c₂ : G) K⁆ ≤ oddCoreOf (conjSub (c₁ : G) K)) :
    ⁅conjSub c₁ ((K ⊓ C).subgroupOf C), conjSub c₂ ((K ⊓ C).subgroupOf C)⁆ ≤
      oddCoreOf (conjSub c₁ ((K ⊓ C).subgroupOf C)) := by
  have hOJ : oddCoreOf (conjSub (c₁ : G) K) ≤ conjSub (c₁ : G) K := Subgroup.map_subtype_le _
  have key : ∀ y ∈ conjSub (c₂ : G) K, ∀ w ∈ conjSub (c₁ : G) K,
      y * w * y⁻¹ ∈ conjSub (c₁ : G) K := by
    intro y hy w hw
    have hc : ⁅y, w⁆ ∈ conjSub (c₁ : G) K := hOJ (h (by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator hy hw))
    have e : y * w * y⁻¹ = ⁅y, w⁆ * w := by rw [commutatorElement_def]; group
    rw [e]
    exact Subgroup.mul_mem _ hc hw
  have hJN : ∀ y ∈ conjSub (c₂ : G) K, y ∈ Subgroup.normalizer ((conjSub (c₁ : G) K : Subgroup G) :
      Set G) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · exact key y hy w
    · intro hw
      have := key y⁻¹ (Subgroup.inv_mem _ hy) _ hw
      simpa [mul_assoc] using this
  have hMN : ∀ y ∈ conjSub c₂ ((K ⊓ C).subgroupOf C), y ∈ Subgroup.normalizer
      ((conjSub c₁ ((K ⊓ C).subgroupOf C) : Subgroup ↥C) : Set ↥C) :=
    fun y hy => mem_normalizer_conjSub_of_sec c₁ y (hJN _ (le_conjSub_of_mem_sec c₂ hy))
  have hcomm : ⁅conjSub c₁ ((K ⊓ C).subgroupOf C), conjSub c₂ ((K ⊓ C).subgroupOf C)⁆ ≤
      conjSub c₁ ((K ⊓ C).subgroupOf C) ⊓
        (oddCoreOf (conjSub (c₁ : G) K)).comap C.subtype := by
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    refine ⟨?_, ?_⟩
    · have h1 : g₂ * g₁⁻¹ * g₂⁻¹ ∈ conjSub c₁ ((K ⊓ C).subgroupOf C) :=
        (Subgroup.mem_normalizer_iff.mp (hMN g₂ hg₂) _).mp (Subgroup.inv_mem _ hg₁)
      have e : ⁅g₁, g₂⁆ = g₁ * (g₂ * g₁⁻¹ * g₂⁻¹) := by rw [commutatorElement_def]; group
      rw [e]
      exact Subgroup.mul_mem _ hg₁ h1
    · have h2 := h (Subgroup.commutator_mem_commutator (le_conjSub_of_mem_sec c₁ hg₁)
        (le_conjSub_of_mem_sec c₂ hg₂))
      rw [commutatorElement_def] at h2 ⊢
      exact h2
  refine hcomm.trans (le_oddCoreOf_of_normalizes_of_odd inf_le_left ?_ ?_)
  · intro m hm
    have hmN : (m : G) ∈ Subgroup.normalizer ((oddCoreOf (conjSub (c₁ : G) K) : Subgroup G) :
        Set G) :=
      mem_normalizer_oddCore_of_mem_normalizer
        (Subgroup.le_normalizer (le_conjSub_of_mem_sec c₁ hm))
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hx1, hx2⟩
      exact ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hm hx1) (Subgroup.inv_mem _ hm),
        (Subgroup.mem_normalizer_iff.mp hmN _).mp hx2⟩
    · rintro ⟨hx1, hx2⟩
      refine ⟨?_, (Subgroup.mem_normalizer_iff.mp hmN _).mpr hx2⟩
      have := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hm) hx1) hm
      simpa [mul_assoc] using this
  · have hle : (conjSub c₁ ((K ⊓ C).subgroupOf C) ⊓
        (oddCoreOf (conjSub (c₁ : G) K)).comap C.subtype).map C.subtype ≤
          oddCoreOf (conjSub (c₁ : G) K) := by
      rintro _ ⟨x, hx, rfl⟩
      exact hx.2
    rw [Nat.card_congr (Subgroup.equivMapOfInjective _ _ C.subtype_injective).toEquiv]
    exact (oddCoreOf_odd_natCard _).of_dvd_nat (Subgroup.card_dvd_of_le hle)

omit [Finite G] in
theorem coe_eq_of_isUniqueInvolution_sec {z : G} (hI : IsUniqueInvolution K z) (c : ↥C)
    {u : ↥C} (hu : IsUniqueInvolution (conjSub c ((K ⊓ C).subgroupOf C)) u) :
    (u : G) = (c : G) * z * (c : G)⁻¹ := by
  have hsq : (u : G) * u = 1 := congrArg Subtype.val hu.sq
  have hne : (u : G) ≠ 1 := fun h => hu.ne_one (Subtype.ext h)
  exact ((hI.conj (c : G)).unique _ (le_conjSub_of_mem_sec c hu.mem) hsq).resolve_left hne

theorem hypOmegaModU_conjFamily_sec {z : G} (hK : Q3.IsClassicalMember3 K z)
    (hΩ : HypOmegaModU (.sl2 3 1) (CoreAssembly.conjClass K)) (hzC : z ∈ C)
    (hL : Q3.IsClassicalMember3 ((K ⊓ C).subgroupOf C) (⟨z, hzC⟩ : C)) :
    HypOmegaModU (.sl2 3 1) (conjFamily ((K ⊓ C).subgroupOf C)) where
  conjInvariant := by
    rintro n _ ⟨g, rfl⟩
    exact ⟨n * g, conjSub_mul _ _ _⟩
  classical := by
    rintro _ ⟨g, rfl⟩
    exact ⟨_, isClassicalMember3_iff_U.mp (hL.conj g)⟩
  omega4 := by
    rintro _ ⟨c₁, rfl⟩ _ ⟨c₂, rfl⟩ hne
    have hJne := conjSub_ne_of_ne_sec hne
    obtain ⟨h4a, h4b⟩ := hΩ.omega4 _ ⟨(c₁ : G), rfl⟩ _ ⟨(c₂ : G), rfl⟩ hJne
    have hdvd : Nat.card ↥(conjSub c₁ ((K ⊓ C).subgroupOf C) ⊓
        conjSub c₂ ((K ⊓ C).subgroupOf C)) ∣
        Nat.card ↥(conjSub (c₁ : G) K ⊓ conjSub (c₂ : G) K) := by
      rw [Nat.card_congr (Subgroup.equivMapOfInjective _ _ C.subtype_injective).toEquiv]
      apply Subgroup.card_dvd_of_le
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨le_conjSub_of_mem_sec c₁ hx.1, le_conjSub_of_mem_sec c₂ hx.2⟩
    have hval : padicValNat 2 (Nat.card ↥(conjSub c₁ ((K ⊓ C).subgroupOf C) ⊓
        conjSub c₂ ((K ⊓ C).subgroupOf C))) ≤
          padicValNat 2 (Nat.card ↥(conjSub (c₁ : G) K ⊓ conjSub (c₂ : G) K)) :=
      (padicValNat_dvd_iff_le Nat.card_pos.ne').mp (pow_padicValNat_dvd.trans hdvd)
    refine ⟨hval.trans h4a, fun h1 => ?_⟩
    have hc := h4b (le_antisymm h4a (h1 ▸ hval))
    refine le_inf (commutator_le_oddCoreOf_sec c₁ c₂ (hc.trans inf_le_left)) ?_
    rw [Subgroup.commutator_comm]
    refine commutator_le_oddCoreOf_sec c₂ c₁ ?_
    rw [Subgroup.commutator_comm]
    exact hc.trans inf_le_right
  omega5 := by
    rintro _ ⟨c₁, rfl⟩ _ ⟨c₂, rfl⟩ hne u hu v hv hnc h2 hvu
    have hI : IsUniqueInvolution K z :=
      (isClassicalMember3_iff_U.mp hK).isUniqueInvolution (MemberType.cert_sl2 3 1)
    have hJne := conjSub_ne_of_ne_sec hne
    have hu' := coe_eq_of_isUniqueInvolution_sec hI c₁ hu
    have hvJ := le_conjSub_of_mem_sec c₂ hv
    have hnc' : ¬ ∀ w ∈ conjSub (c₂ : G) K, (v : G) * w = w * v := by
      intro h
      apply hnc
      intro w hw
      exact Subtype.ext (h _ (le_conjSub_of_mem_sec c₂ hw))
    have h2' : IsPGroup 2 (Subgroup.zpowers (v : G)) := by
      have := h2.map C.subtype
      rwa [MonoidHom.map_zpowers] at this
    have hvz : (v : G) * ((c₁ : G) * z * (c₁ : G)⁻¹) = ((c₁ : G) * z * (c₁ : G)⁻¹) * v := by
      rw [← hu']
      exact congrArg Subtype.val hvu
    have hN := hΩ.omega5 _ ⟨(c₁ : G), rfl⟩ _ ⟨(c₂ : G), rfl⟩ hJne _ (hI.conj (c₁ : G)) _ hvJ
      hnc' h2' hvz
    exact mem_normalizer_conjSub_of_sec c₁ v hN

end CFSG.ClassicalInvolution.Q3.Q3T6
