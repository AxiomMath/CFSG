module

public import CFSG.GH74.GLS.TwoThin.Reduction
import CFSG.Assembly.OddCoreElimination.TwoGroups
import CFSG.Assembly.OddCoreElimination.Transfer
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.NormalFourGeometry

public section

namespace CFSG.Assembly.Dichotomy

variable {G : Type*} [Group G]

private theorem tt_le_centralizer_self {p : ℕ} {V : Subgroup G} (hV : IsElemAbelian p V) :
    V ≤ Subgroup.centralizer (V : Set G) := by
  intro v hv
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  exact congrArg Subtype.val (hV.1.is_comm.comm (⟨w, hw⟩ : V) ⟨v, hv⟩)

private theorem tt_le_centralizer_singleton {p : ℕ} {V : Subgroup G} (hV : IsElemAbelian p V)
    {v : G} (hv : v ∈ V) : V ≤ Subgroup.centralizer ({v} : Set G) :=
  (tt_le_centralizer_self hV).trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hv))

private theorem tt_map_conj_centralizer_le (g x : G) :
    (Subgroup.centralizer ({x} : Set G)).map (MulAut.conj g⁻¹).toMonoidHom ≤
      Subgroup.centralizer ({(MulAut.conj g⁻¹).toMonoidHom x} : Set G) := by
  have h := Subgroup.map_centralizer_le_centralizer_image ({x} : Set G)
    (MulAut.conj g⁻¹).toMonoidHom
  rwa [Set.image_singleton] at h

variable [Finite G]

private theorem tt_pRank_centralizer_conj_le (g x : G) :
    pRank 2 (Subgroup.centralizer ({g⁻¹ * x * g} : Set G)) ≤
      pRank 2 (Subgroup.centralizer ({x} : Set G)) := by
  have h := tt_map_conj_centralizer_le g⁻¹ (g⁻¹ * x * g)
  have hx : (MulAut.conj g⁻¹⁻¹).toMonoidHom (g⁻¹ * x * g) = x := by
    simp [MulAut.conj_apply, mul_assoc]
  rw [hx] at h
  exact (CFSG.SectionRank.pRank_le_map one_lt_two _ (MulEquiv.injective _) _).trans
    (CFSG.SectionRank.pRank_mono one_lt_two h)

private theorem tt_exists_map_conj_le_sylow (S : Sylow 2 G) {P : Subgroup G} (hP : IsPGroup 2 P) :
    ∃ g : G, P.map (MulAut.conj g⁻¹).toMonoidHom ≤ S := by
  obtain ⟨T, hPT⟩ := hP.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq G T S
  refine ⟨h⁻¹, ?_⟩
  rw [inv_inv]
  rintro _ ⟨x, hx, rfl⟩
  rw [← hh, Sylow.coe_subgroup_smul]
  exact Subgroup.smul_mem_pointwise_smul x (MulAut.conj h) _ (hPT hx)

private theorem tt_exists_elemAbelian_eight_le {S : Subgroup G} (h3 : 3 ≤ pRank 2 S) :
    ∃ E : Subgroup G, E ≤ S ∧ IsElemAbelian 2 E ∧ Nat.card E = 8 := by
  rw [assembly_pRank_eq_open] at h3
  obtain ⟨E, hES, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank one_lt_two S
  have hdiv : 2 ^ 3 ∣ Nat.card E := by
    rw [hEcard]
    exact Nat.pow_dvd_pow 2 h3
  obtain ⟨F, hFcard, -, hFE⟩ := Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_two
    (H := (⊥ : Subgroup G)) (L := E) (by simp) hdiv bot_le
  exact ⟨F, hFE.trans hES,
    CFSG.LargeEvenClassification.Helpers.elementary_subgroup_of_le E F hE hFE,
    by simpa using hFcard⟩

private theorem tt_three_le_pRank_centralizer_of_mem {S A : Subgroup G} (hS : IsPGroup 2 S)
    (h3 : 3 ≤ pRank 2 S) (hAS : A ≤ S) (hSA : S ≤ Subgroup.normalizer (A : Set G))
    (hA : IsElemAbelian 2 A) (hA4 : Nat.card A = 4) {w : G}
    (hw : w ∈ S ⊓ Subgroup.centralizer (A : Set G)) (hw2 : orderOf w = 2) :
    3 ≤ pRank 2 (S ⊓ Subgroup.centralizer ({w} : Set G)) := by
  by_cases hwA : w ∈ A
  · obtain ⟨E, hES, hE, hE8⟩ := tt_exists_elemAbelian_eight_le h3
    refine (three_le_pRank_inf_centralizer hS hAS hSA hA hA4 hES hE hE8).trans
      (CFSG.SectionRank.pRank_mono one_lt_two (inf_le_inf_left S ?_))
    exact Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hwA)
  · have hcomm : A ≤ Subgroup.centralizer (Subgroup.zpowers w : Set G) :=
      Subgroup.le_centralizer_iff.mpr (Subgroup.zpowers_le.mpr hw.2)
    obtain ⟨E, -, hwE, hE, hE8, hEle⟩ :=
      CFSG.LargeEvenClassification.Helpers.commuting_disjoint_elementary_product
        (firstRank := 2) (secondRank := 1) A (Subgroup.zpowers w) hA
        (CFSG.ProperTwoGeneratedCore.involution_zpowers_elementary w hw2) (by simpa using hA4)
        (by simp [hw2]) hcomm
        (CFSG.ProperTwoGeneratedCore.involution_zpowers_disjoint A w hw2 hwA)
    refine CFSG.SectionRank.le_pRank one_lt_two (le_inf ?_ ?_) hE hE8
    · exact hEle.trans (sup_le hAS (Subgroup.zpowers_le.mpr hw.1))
    · exact tt_le_centralizer_singleton hE (hwE (Subgroup.mem_zpowers w))

private theorem tt_relIndex_centralizer_le_two {S A : Subgroup G} (hS : IsPGroup 2 S)
    (hAS : A ≤ S) (hSA : S ≤ Subgroup.normalizer (A : Set G)) (hA : IsElemAbelian 2 A)
    (hA4 : Nat.card A = 4) : (S ⊓ Subgroup.centralizer (A : Set G)).relIndex S ≤ 2 := by
  let A' := A.subgroupOf S
  have : A'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hAS).mpr hSA
  have hA' : CFSG.Open.IsElemAbelian 2 A' :=
    CFSG.RankThreeCoreUniqueness.Helpers.elementary_transport 2 A A'
      (Subgroup.subgroupOfEquivOfLe hAS).symm hA
  have hA'4 : Nat.card A' = 4 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAS).toEquiv).trans hA4
  obtain ⟨-, -, hind⟩ := CFSG.ProperTwoGeneratedCore.normal_four_centralizer_index hS A' hA' hA'4
  have heq : Subgroup.centralizer (A' : Set S) =
      (S ⊓ Subgroup.centralizer (A : Set G)).subgroupOf S := by
    ext x
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_iff]
    constructor
    · intro h
      exact ⟨x.2, fun a ha => congrArg Subtype.val (h ⟨a, hAS ha⟩ ha)⟩
    · rintro ⟨-, h⟩ y hy
      exact Subtype.ext (h y hy)
  rw [Subgroup.relIndex, ← heq]
  exact hind

end CFSG.Assembly.Dichotomy

namespace CFSG.Assembly.Dichotomy

variable {G : Type} [Group G] [Finite G]

theorem tt_two_le_pRank_involution_centralizer (hperf : commutator G = ⊤) (hrank : 3 ≤ twoRank G)
    (x : G) (hx : orderOf x = 2) : 3 ≤ pRank 2 (Subgroup.centralizer ({x} : Set G)) := by
  obtain ⟨S⟩ : Nonempty (Sylow 2 G) := inferInstance
  have hS : IsPGroup 2 (S : Subgroup G) := S.isPGroup'
  have hS3 : 3 ≤ pRank 2 (S : Subgroup G) := (pRank_sylow_eq_twoRank S).symm ▸ hrank
  obtain ⟨A, hAS, hSA, hA, hA4⟩ := exists_normal_four_of_three_le_pRank hS hS3
  have hzp : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx]; simp)
  obtain ⟨g, hg⟩ := tt_exists_map_conj_le_sylow S hzp
  have hx₁S : g⁻¹ * x * g ∈ (S : Subgroup G) := by
    apply hg
    exact ⟨x, Subgroup.mem_zpowers x, by simp⟩
  have hx₁2 : orderOf (g⁻¹ * x * g) = 2 := by
    simpa only [MulAut.conj_apply, inv_inv, hx] using (MulAut.conj g⁻¹).orderOf_eq x
  set S₀ : Subgroup G := (S : Subgroup G) ⊓ Subgroup.centralizer (A : Set G) with hS₀
  have hrel : S₀.relIndex (S : Subgroup G) ≤ 2 := tt_relIndex_centralizer_le_two hS hAS hSA hA hA4
  obtain ⟨h, hh⟩ : ∃ h : G, h⁻¹ * (g⁻¹ * x * g) * h ∈ S₀ := by
    have hrel0 : S₀.relIndex (S : Subgroup G) ≠ 0 := Subgroup.index_ne_zero_of_finite
    by_cases h1 : S₀.relIndex (S : Subgroup G) = 1
    · refine ⟨1, ?_⟩
      have hle : (S : Subgroup G) ≤ S₀ := Subgroup.relIndex_eq_one.mp h1
      simpa using hle hx₁S
    · have h2 : S₀.relIndex (S : Subgroup G) = 2 := by omega
      exact derivedInvolutionTransfer G S S₀ inf_le_left h2 _ (hperf ▸ Subgroup.mem_top _) hx₁2
  have hx₂2 : orderOf (h⁻¹ * (g⁻¹ * x * g) * h) = 2 := by
    simpa only [MulAut.conj_apply, inv_inv, hx₁2] using (MulAut.conj h⁻¹).orderOf_eq (g⁻¹ * x * g)
  have h3c := tt_three_le_pRank_centralizer_of_mem hS hS3 hAS hSA hA hA4 hh hx₂2
  have hcalc : h⁻¹ * (g⁻¹ * x * g) * h = (g * h)⁻¹ * x * (g * h) := by group
  rw [hcalc] at h3c
  exact h3c.trans ((CFSG.SectionRank.pRank_mono one_lt_two inf_le_right).trans
    (tt_pRank_centralizer_conj_le (g * h) x))

end CFSG.Assembly.Dichotomy

namespace CFSG.GH74.GLS.TwoThin

open Subgroup
open scoped commutatorElement

theorem pRank_two_subgroup_eq_open {G : Type} [Group G] [Finite G] (H : Subgroup G) :
    pRank 2 ↥H = CFSG.Open.pRank 2 H :=
  (CFSG.SectionRank.pRank_eq_open_pRank_top 2 ↥H).trans
    (CFSG.RankThreeCoreUniqueness.Helpers.pRank_subgroup_eq_internal_top 2 (by decide) H).symm

theorem commutator_eq_top_of_simple {G : Type} [Group G] (hs : IsSimpleGroup G)
    (hn : ∃ a b : G, a * b ≠ b * a) : commutator G = ⊤ := by
  rcases (inferInstance : (commutator G).Normal).eq_bot_or_eq_top with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hn
    apply hab
    have hmem : ⁅a, b⁆ ∈ commutator G := Subgroup.commutator_mem_commutator (mem_top a) (mem_top b)
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact hmem
  · exact h

theorem rankThreeCentralizers : RankThreeCentralizers := by
  intro G _ _ hs hn h3 x hx
  have hperf : commutator G = ⊤ := commutator_eq_top_of_simple hs hn
  have h3' : 3 ≤ CFSG.Assembly.twoRank G := by
    have : 3 ≤ CFSG.Open.twoRank G := by
      rw [← pRank_two_eq_twoRank G]
      exact h3
    exact this
  have := CFSG.Assembly.Dichotomy.tt_two_le_pRank_involution_centralizer hperf h3' x hx
  rw [pRank_two_subgroup_eq_open]
  exact this

end CFSG.GH74.GLS.TwoThin
