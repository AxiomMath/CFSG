module

public import Mathlib
public import CFSG.GH74.KGroups.Generic
public import CFSG.GH74.KGroups.PermCheck
public import CFSG.GH74.E2.Shapes
public import CFSG.GH74.KGroups.TwoM12Aut
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutCentralizers
public meta import CFSG.GH74.KGroups.PermCheck
public import CFSG.GH74.KGroups.TwoM12Syl3Inputs
public meta import CFSG.GH74.KGroups.TwoM12Syl3Inputs
public import Certificates.Certificate2193
public import Certificates.Certificate2194
public import Certificates.Certificate2200
public import Certificates.Certificate2201
public import Certificates.Certificate3086
public import Certificates.Certificate5132

public section

namespace CFSG.GH74.KGroups.TwoM12

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.Blueprint Subgroup
open CFSG.ComponentClassification CFSG.ComponentClassification.M12Cover
open CFSG.GH74.E2 (Shape2M12)

set_option compiler.extract_closed false

@[expose] def x27Word : List ℤ :=
  [1, 2, 1, 2, 1, -2, 1, 2, 1, 2, 1, 2, 1, -2, 1, -2, 1, -2, 1, -2, 1, 2]

@[expose] def y27Word : List ℤ :=
  [1, -2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 1, -2, 1, 2, 1, -2, 1, 2, 1, 2, 1, 2, 1, -2, 1, -2, 1,
    -2, 1, -2, 1, -2]

theorem Q27_valid :
    Q27.check = true ∧ Q27.orderCertificate = 27 :=
  Certificates.certificate5132

theorem x27_eq : evalCodes [m12gA, m12gB] x27Word = x27 := by decide +kernel

theorem y27_eq : evalCodes [m12gA, m12gB] y27Word = y27 := by decide +kernel

theorem x27_mem : x27 ∈ NativeSporadic.M12 := by
  rw [← x27_eq]
  exact evalCodes_mem _ m12_gens_mem' x27Word

theorem y27_mem : y27 ∈ NativeSporadic.M12 := by
  rw [← y27_eq]
  exact evalCodes_mem _ m12_gens_mem' y27Word

@[expose] def T27 : Subgroup (Equiv.Perm (Fin 12)) := Q27.originalSubgroup

theorem T27_eq : T27 = Subgroup.closure {x27, y27} := by
  rw [T27, Q27, certificate_originalSubgroup]
  congr 1
  ext g
  simp

theorem card_T27 : Nat.card T27 = 27 := by
  rw [T27, card_group Q27 Q27_valid.1, Q27_valid.2]

theorem T27_le : T27 ≤ NativeSporadic.M12 := by
  rw [T27_eq, Subgroup.closure_le]
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl
  · exact x27_mem
  · exact y27_mem

theorem x27_mem_T27 : x27 ∈ T27 := by
  rw [T27_eq]; exact Subgroup.subset_closure (Set.mem_insert _ _)

theorem y27_mem_T27 : y27 ∈ T27 := by
  rw [T27_eq]; exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

@[expose] def xM : NativeSporadic.M12 := ⟨x27, x27_mem⟩

@[expose] def yM : NativeSporadic.M12 := ⟨y27, y27_mem⟩

theorem xyM_noncomm : xM * yM ≠ yM * xM := by decide +kernel

theorem exists_subgroup_card_27 :
    ∃ T : Subgroup (MulAut NativeSporadic.M12), Nat.card T = 27 ∧
    MulAut.conj xM ∈ T ∧ MulAut.conj yM ∈ T := by
  refine ⟨(T27.subgroupOf NativeSporadic.M12).map
    (MulAut.conj : NativeSporadic.M12 →* MulAut NativeSporadic.M12), ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective M12Cover.conj_injective, ← card_T27]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe T27_le).toEquiv
  · exact Subgroup.mem_map.2 ⟨xM, Subgroup.mem_subgroupOf.2 x27_mem_T27, rfl⟩
  · exact Subgroup.mem_map.2 ⟨yM, Subgroup.mem_subgroupOf.2 y27_mem_T27, rfl⟩

theorem exists_conj_of_card_27
    (E T : Subgroup (MulAut NativeSporadic.M12))
    (hE : Nat.card E = 27) (hT : Nat.card T = 27) :
    ∃ g : MulAut NativeSporadic.M12, ∀ q ∈ T, ∃ s ∈ E, g * s * g⁻¹ = q := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hGcard : Nat.card (MulAut NativeSporadic.M12) = 190080 := card_mulAut
  have : Finite (MulAut NativeSporadic.M12) :=
    Nat.finite_of_card_ne_zero (by rw [hGcard]; norm_num)
  have hindex : ∀ P : Subgroup (MulAut NativeSporadic.M12), Nat.card P = 27 → ¬ 3 ∣ P.index := by
    intro P hP hd
    have h1 := P.card_mul_index
    rw [hP, hGcard] at h1
    have h2 : P.index = 7040 := by omega
    rw [h2] at hd
    omega
  have hp3 : ∀ P : Subgroup (MulAut NativeSporadic.M12), Nat.card P = 27 → IsPGroup 3 P :=
    fun P hP => IsPGroup.of_card (n := 3) (by rw [hP]; norm_num)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (MulAut NativeSporadic.M12)
    ((hp3 E hE).toSylow (hindex E hE)) ((hp3 T hT).toSylow (hindex T hT))
  refine ⟨g, fun q hq => ?_⟩
  have hq' : q ∈ (((hp3 T hT).toSylow (hindex T hT) : Sylow 3 (MulAut NativeSporadic.M12)) :
      Subgroup (MulAut NativeSporadic.M12)) := hq
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hq'
  obtain ⟨s, hs, hsq⟩ := hq'
  exact ⟨s, hs, by rw [← hsq, MulAut.smul_def, MulAut.conj_apply]⟩

theorem no_abelian_order_27
    (E : Subgroup (MulAut NativeSporadic.M12))
    (hE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hcard : Nat.card E = 27) : False := by
  obtain ⟨T, hTcard, hxT, hyT⟩ := exists_subgroup_card_27
  obtain ⟨g, hg⟩ := exists_conj_of_card_27 E T hcard hTcard
  obtain ⟨s, hs, hsx⟩ := hg _ hxT
  obtain ⟨s', hs', hsy⟩ := hg _ hyT
  have hcomm : MulAut.conj xM * MulAut.conj yM = MulAut.conj yM * MulAut.conj xM := by
    rw [← hsx, ← hsy]
    calc g * s * g⁻¹ * (g * s' * g⁻¹) = g * (s * s') * g⁻¹ := by group
      _ = g * (s' * s) * g⁻¹ := by rw [hE s hs s' hs']
      _ = g * s' * g⁻¹ * (g * s * g⁻¹) := by group
  exact xyM_noncomm (M12Cover.conj_injective (by rw [map_mul, map_mul, hcomm]))

variable {K : Type} [Group K]

theorem autRank3_le_two_of_shape2M12
    [Finite K] (h : Shape2M12 K) (R : Subgroup (MulAut K))
    (hR : CFSG.GH74.E2.ElemAb 3 R) : Nat.card R ≤ 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 R := by
    intro r
    refine ⟨1, ?_⟩
    have := hR.2 r r.2
    apply Subtype.ext
    simpa using this
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  have hdvd : Nat.card R ∣ 190080 :=
    (Subgroup.card_subgroup_dvd_card R).trans (card_mulAut_dvd h)
  rw [hk] at hdvd ⊢
  by_contra hlt
  push Not at hlt
  have hk3 : 3 ≤ k := by
    by_contra hk3
    push Not at hk3
    interval_cases k <;> simp at hlt
  have hk3' : k = 3 := by
    by_contra hne
    have : 4 ≤ k := by omega
    have h81 : 3 ^ 4 ∣ 190080 := (pow_dvd_pow 3 this).trans hdvd
    exact absurd h81 (by norm_num)
  subst hk3'
  have hΘ := autEmb_injective h
  refine no_abelian_order_27 (R.map (autEmb h)) ?_ ?_
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hR.1 a ha b hb]
  · rw [Subgroup.card_map_of_injective hΘ, hk]
    norm_num

end CFSG.GH74.KGroups.TwoM12
