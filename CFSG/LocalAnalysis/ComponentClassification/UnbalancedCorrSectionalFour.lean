module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrConnectedDerived
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrIsolatedFourEscape
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerRankOneTwoGroups
public import CFSG.LocalAnalysis.LargeEvenClassification.IsolatedFourConsequences

public section

namespace CFSG.ComponentClassification.UnbalancedCorr

open Subgroup CFSG.LargeEvenClassification CFSG.ComponentClassification.LiteratureLocal
  CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type*} [Group G] [Finite G]

theorem four_generated_of_sylow (S : Sylow 2 G)
    (hS : ∀ U : Subgroup ↥S, ∃ X : Finset ↥S, X.card ≤ 4 ∧ closure (X : Set ↥S) = U)
    (P : Subgroup G) (hP : IsPGroup 2 P) :
    ∃ X : Finset G, X.card ≤ 4 ∧ closure (X : Set G) = P := by
  classical
  obtain ⟨g, hg⟩ := exists_conjugate_le_sylow hP S
  obtain ⟨X, hX, hXgen⟩ := hS ((CFSG.conjugate P g).subgroupOf S)
  set φ : ↥S →* G := (MulAut.conj g).toMonoidHom.comp (S : Subgroup G).subtype with hφ
  refine ⟨X.image φ, Finset.card_image_le.trans hX, ?_⟩
  rw [Finset.coe_image, ← MonoidHom.map_closure, hXgen, hφ, ← map_map,
    map_subgroupOf_eq_of_le hg]
  ext x
  rw [mem_map_equiv, mem_conjugate_iff', MulAut.conj_symm_apply,
    show g * (g⁻¹ * x * g) * g⁻¹ = x by group]

theorem card_quotient_le_sixteen_of_four_generated
    (hgen : ∀ P : Subgroup G, IsPGroup 2 P → ∃ X : Finset G, X.card ≤ 4 ∧ closure (X : Set G) = P)
    (H : Subgroup G) (R : Subgroup ↥H) [R.Normal]
    (hQ : Open.IsElemAbelian 2 (⊤ : Subgroup (↥H ⧸ R))) : Nat.card (↥H ⧸ R) ≤ 16 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let T : Sylow 2 ↥H := default
  have hQ2 : IsPGroup 2 (↥H ⧸ R) := fun q => ⟨1, by simpa using hQ.2 q (mem_top q)⟩
  have hTtop : (T : Subgroup ↥H).map (QuotientGroup.mk' R) = ⊤ := by
    have h1 := index_map_dvd (H := (T : Subgroup ↥H)) (QuotientGroup.mk'_surjective R)
    have h2 : ((T : Subgroup ↥H).map (QuotientGroup.mk' R)).index ∣
        Nat.card (↥H ⧸ R) := index_dvd_card _
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQ2
    rw [hn] at h2
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
    have hodd := Sylow.not_dvd_index T
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · rw [pow_zero] at hm
      exact index_eq_one.mp hm
    · exfalso
      apply hodd
      exact (dvd_pow_self 2 hm0.ne').trans (hm ▸ h1)
  set U := (T : Subgroup ↥H).map H.subtype
  have hUH : U ≤ H := map_subtype_le _
  have hU2 : IsPGroup 2 U := T.isPGroup'.map H.subtype
  obtain ⟨X, hX, hXgen⟩ := hgen U hU2
  obtain ⟨Y, hY, hYgen⟩ :=
    Helpers.subgroup_generators_of_ambient_generators U X hXgen
  set ψ : ↥U →* ↥H ⧸ R := (QuotientGroup.mk' R).comp (inclusion hUH)
  have hψs : Function.Surjective ψ := by
    intro q
    have hq : q ∈ (T : Subgroup ↥H).map (QuotientGroup.mk' R) := hTtop ▸ mem_top q
    obtain ⟨t, ht, rfl⟩ := hq
    exact ⟨⟨(t : G), ⟨t, ht, rfl⟩⟩, rfl⟩
  have hcomm : IsMulCommutative (↥H ⧸ R) := by
    apply IsMulCommutative.of_comm
    intro p q
    exact congrArg Subtype.val
      (@mul_comm' (⊤ : Subgroup (↥H ⧸ R)) _ hQ.1 ⟨p, mem_top p⟩ ⟨q, mem_top q⟩)
  have helem : CFSG.IsElementaryAbelian 2 (↥H ⧸ R) :=
    { toIsMulCommutative := hcomm
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun q =>
        hQ.2 q (mem_top q) }
  have hbound := Helpers.elementary_surjection_card_le_pow_generators_of_isElementaryAbelian
    Nat.prime_two helem ψ hψs Y hYgen
  rw [hY] at hbound
  exact hbound.trans (by simpa using Nat.pow_le_pow_right (by decide : 0 < 2) hX)

theorem perfect_unbalanced_triple_core_or_sectional_four
    {G : Type} [Group G] [Finite G]
    (hperf : commutator G = ⊤) (S : Sylow 2 G)
    (hunb : ∃ t : G, orderOf t = 2 ∧
      ¬ (pPrimeCore 2 (centralizer ({t} : Set G))).map (centralizer ({t} : Set G)).subtype ≤
        pPrimeCore 2 G)
    {K : Subgroup G}
    (hK : K = ⨆ (Q : Subgroup G) (_ : Q ≤ (S : Subgroup G)) (_ : 2 ≤ CFSG.pRank 2 ↥Q),
      normalizer (Q : Set G)) :
    (∃ (a x : G) (J : Subgroup G), orderOf a = 2 ∧ orderOf x = 2 ∧ a * x = x * a ∧
      GSUnbalancingTriple a x J) ∨
    K < ⊤ ∨
    ((∀ P : Subgroup G, IsPGroup 2 P → ∃ X : Finset G, X.card ≤ 4 ∧ closure (X : Set G) = P) ∧
      ∀ (H : Subgroup G) (R : Subgroup ↥H) [R.Normal],
        Open.IsElemAbelian 2 (⊤ : Subgroup (↥H ⧸ R)) → Nat.card (↥H ⧸ R) ≤ 16) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hi : ∃ (a x : G) (J : Subgroup G), orderOf a = 2 ∧ orderOf x = 2 ∧ a * x = x * a ∧
      GSUnbalancingTriple a x J
  · exact Or.inl hi
  right
  have hS2 : IsPGroup 2 ↥(S : Subgroup G) := S.isPGroup'
  have hcases : K < ⊤ ∨
      ∀ U : Subgroup ↥S, ∃ X : Finset ↥S, X.card ≤ 4 ∧ closure (X : Set ↥S) = U := by
    by_cases hrank : 3 ≤ CFSG.pRank 2 G
    · have hconn : ¬ Conn3 G := by
        intro hconn
        obtain ⟨t, ht, htn⟩ := hunb
        exact hi ((connected_derived_involution_unbalancing_triple hconn).1 t ht
          (hperf ▸ mem_top t) htn)
      obtain ⟨⟨Estar, hEstar, hEstarS⟩, -⟩ := rank_three_component_normalizer_control hrank S
      obtain ⟨-, hxor, hKlt, -⟩ :=
        perfect_group_full_core_or_isolated_four_escape hperf hrank hconn S hEstar hEstarS hK
      by_cases hKM : K ≤ rankThreeClassStabilizer Estar
      · exact Or.inl (hKlt hKM)
      · right
        have hii : ∃ V : Subgroup G, V ≤ S ∧ IsElementaryAbelian 2 V ∧ Nat.card V = 4 ∧
            CFSG.pRank 2 ↥((S : Subgroup G) ⊓ centralizer (V : Set G)) = 2 ∧
            ∃ x : G, orderOf x = 2 ∧ x ∈ centralizer (V : Set G) ∧
              x ∉ rankThreeClassStabilizer Estar := by
          by_contra hno
          exact hKM ((xor_iff_iff_not.mp hxor).mpr hno)
        obtain ⟨V, hVS, hV, hV4, hV2, -⟩ := hii
        have hV' : Open.IsElemAbelian 2 V :=
          (SectionRank.isElementaryAbelian_iff_isElemAbelian 2 V).mp hV
        have hVS4 : Nat.card ↥(V.subgroupOf S) = 4 := by
          rw [← hV4]
          exact Nat.card_congr (subgroupOfEquivOfLe hVS).toEquiv
        have hCmap : (centralizer ((V.subgroupOf S : Subgroup ↥S) : Set ↥S)).map
            (S : Subgroup G).subtype = (S : Subgroup G) ⊓ centralizer (V : Set G) := by
          ext y
          constructor
          · rintro ⟨z, hz, rfl⟩
            refine mem_inf.mpr ⟨z.2, mem_centralizer_iff.mpr fun v hv => ?_⟩
            have h1 := mem_centralizer_iff.mp hz ⟨v, hVS hv⟩ (show (⟨v, hVS hv⟩ : ↥S) ∈
              V.subgroupOf S from hv)
            exact congrArg Subtype.val h1
          · intro hy
            obtain ⟨hyS, hyC⟩ := mem_inf.mp hy
            refine ⟨⟨y, hyS⟩, mem_centralizer_iff.mpr fun v hv => ?_, rfl⟩
            exact Subtype.ext (mem_centralizer_iff.mp hyC v hv)
        have hrankC : Open.twoRank ↥(centralizer ((V.subgroupOf S : Subgroup ↥S) : Set ↥S)) =
            2 :=
          calc Open.twoRank ↥(centralizer ((V.subgroupOf S : Subgroup ↥S) : Set ↥S))
              = CFSG.pRank 2 ↥(centralizer ((V.subgroupOf S : Subgroup ↥S) : Set ↥S)) :=
                (SectionRank.pRank_eq_open_pRank_top 2 _).symm
            _ = CFSG.pRank 2 ↥((S : Subgroup G) ⊓ centralizer (V : Set G)) :=
                pRank_eq_of_mulEquiv one_lt_two
                  ((equivMapOfInjective _ _ (S : Subgroup G).subtype_injective).trans
                    (MulEquiv.subgroupCongr hCmap))
            _ = 2 := hV2
        exact Helpers.isolated_four_four_generators hS2 (V.subgroupOf S)
          (isElemAbelian_subgroupOf S hV') hVS4 hrankC
    · right
      push Not at hrank
      refine Helpers.macwilliams_four_generators hS2 fun E _ hE hE8 => ?_
      have hE' : Open.IsElemAbelian 2 (E.map (S : Subgroup G).subtype) :=
        Helpers.elementary_map E hE _
      have h3 : 3 ≤ Open.pRank 2 (⊤ : Subgroup G) :=
        SectionRank.le_pRank (p := 2) one_lt_two le_top hE'
          (by
            rw [card_map_of_injective (S : Subgroup G).subtype_injective]
            exact hE8.trans (by norm_num))
      rw [← SectionRank.pRank_eq_open_pRank_top] at h3
      omega
  rcases hcases with hKlt | hfour
  · exact Or.inl hKlt
  · have hgen := four_generated_of_sylow S hfour
    exact Or.inr ⟨hgen, fun H R _ hQ => card_quotient_le_sixteen_of_four_generated hgen H R hQ⟩

end CFSG.ComponentClassification.UnbalancedCorr
