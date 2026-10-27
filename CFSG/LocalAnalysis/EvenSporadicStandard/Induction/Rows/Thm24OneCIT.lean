module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Thm24OneUse
public import CFSG.ClassicalInvolution.Basic
import CFSG.Sporadic.Mathieu.M11
public import CFSG.Adapters.GeneralizedFitting
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.NormalizerLeNormalizerCentralizer

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78

@[expose] def CITPart2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup (CFSG.Open.genFittingFStar G)],
    (∃ a b : CFSG.Open.genFittingFStar G, a * b ≠ b * a) →
    ∀ (z : G), orderOf z = 2 → ∀ (J : Subgroup G), z ∈ J →
    CFSG.Open.IsSubnormal J (Subgroup.centralizer ({z} : Set G)) →
    ∀ (S : Sylow 2 J),
    (∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup J) ≃* QuaternionGroup (2 ^ (r - 2)))) →
    CFSG.Open.classicalInvolutionTightlyEmbedded J →
      OddLieType (CFSG.Open.genFittingFStar G) ∨
        IsSporadic (CFSG.Open.genFittingFStar G) .M11 ∨
        IsSporadic (CFSG.Open.genFittingFStar G) .M12

theorem centralizer_singleton_le_normalizer_of_stdBare {H : Type} [Group H] {A : Subgroup H}
    (hA : StdBare A) {z : H} (hz : orderOf z = 2) (hzC : z ∈ centralizer (A : Set H)) :
    centralizer ({z} : Set H) ≤ normalizer (A : Set H) := by
  intro g hg
  by_contra hgN
  have hodd := hA.2 g hgN
  have hzg : z ∈ (centralizer (A : Set H) ⊓
      (centralizer (A : Set H)).map (MulAut.conj g).toMonoidHom : Subgroup H) := by
    refine ⟨hzC, CFSG.ClassicalInvolution.mem_map_conj_iff.mpr ?_⟩
    have hcomm : z * g = g * z := Subgroup.mem_centralizer_iff.mp hg z rfl
    have : g⁻¹ * z * g = z := by rw [mul_assoc, hcomm, inv_mul_cancel_left]
    rwa [this]
  have h2 : 2 ∣ Nat.card (centralizer (A : Set H) ⊓
      (centralizer (A : Set H)).map (MulAut.conj g).toMonoidHom : Subgroup H) := by
    have := Subgroup.orderOf_dvd_natCard _ hzg
    rwa [hz] at this
  exact hodd.not_two_dvd_nat h2

theorem exists_sylow_two_of_le {H : Type} [Group H] [Finite H] {C J : Subgroup H}
    (hJC : J ≤ C) (S : Sylow 2 C) (hSJ : (S : Subgroup C).map C.subtype ≤ J) :
    ∃ S₀ : Sylow 2 J, Nonempty ((S₀ : Subgroup J) ≃* (S : Subgroup C)) := by
  set S' : Subgroup H := (S : Subgroup C).map C.subtype with hS'
  let e1 : (S'.subgroupOf J) ≃* S' := Subgroup.subgroupOfEquivOfLe hSJ
  let e2 : (S : Subgroup C) ≃* S' :=
    Subgroup.equivMapOfInjective _ C.subtype C.subtype_injective
  have hcardS' : Nat.card S' = Nat.card (S : Subgroup C) := (Nat.card_congr e2.toEquiv).symm
  have hdvd1 : Nat.card S' ∣ Nat.card J := Subgroup.card_dvd_of_le hSJ
  have hdvd2 : Nat.card J ∣ Nat.card C := Subgroup.card_dvd_of_le hJC
  have hS := S.card_eq_multiplicity
  have hJpos : 0 < Nat.card J := Nat.card_pos
  have hCpos : 0 < Nat.card C := Nat.card_pos
  have hle : (Nat.card J).factorization 2 ≤ (Nat.card C).factorization 2 :=
    (Nat.factorization_le_iff_dvd hJpos.ne' hCpos.ne').mpr hdvd2 2
  have hge : (Nat.card C).factorization 2 ≤ (Nat.card J).factorization 2 := by
    refine (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hJpos.ne').mp ?_
    rw [← hS, ← hcardS']
    exact hdvd1
  have hcard : Nat.card (S'.subgroupOf J) = 2 ^ (Nat.card J).factorization 2 := by
    rw [Nat.card_congr e1.toEquiv, hcardS', hS, le_antisymm hge hle]
  exact ⟨Sylow.ofCard (S'.subgroupOf J) hcard, ⟨e1.trans e2.symm⟩⟩

theorem sol78Thm24_1CIT_of_citPart2 (h : CITPart2) : Sol78Thm24_1CIT := by
  intro H _ _ N hN A hA hq
  obtain ⟨hF, hsimp, hnonab⟩ := hN
  rw [← CFSG.Adapters.genFittingFStar_eq_foundations] at hF
  subst hF
  set C : Subgroup H := centralizer (A : Set H) with hC
  obtain ⟨S, n, hn, ⟨e⟩⟩ := hq
  obtain ⟨u, hu2, huniq, -⟩ :=
    CFSG.ClassicalInvolution.exists_unique_involution_of_mulEquiv_quaternionGroup e
  set z : H := (((u : (S : Subgroup C)) : C) : H) with hzdef
  have hz : orderOf z = 2 := by
    have h1 : orderOf (((u : (S : Subgroup C)) : C) : H) = orderOf (u : C) :=
      Subgroup.orderOf_coe _
    have h2 : orderOf (u : C) = orderOf u := Subgroup.orderOf_coe _
    rw [hzdef, h1, h2, hu2]
  have hzC : z ∈ C := (((u : (S : Subgroup C)) : C)).2
  have hcomm : ∀ x : (S : Subgroup C), (((x : (S : Subgroup C)) : C) : H) * z =
      z * (((x : (S : Subgroup C)) : C) : H) := by
    intro x
    have hx : x * u * x⁻¹ = u :=
      huniq _ ((CFSG.ClassicalInvolution.orderOf_conj_eq x u).trans hu2)
    have hx' : x * u = u * x := by
      rw [mul_inv_eq_iff_eq_mul] at hx
      exact hx
    exact congrArg (fun y : (S : Subgroup C) => (((y : (S : Subgroup C)) : C) : H)) hx'
  set J₀ : Subgroup H := C ⊓ centralizer ({z} : Set H) with hJ₀
  have hzJ : z ∈ J₀ := ⟨hzC, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hJle : J₀ ≤ centralizer ({z} : Set H) := inf_le_right
  have hSJ : (S : Subgroup C).map C.subtype ≤ J₀ := by
    rintro y ⟨x, hx, rfl⟩
    exact ⟨x.2, Subgroup.mem_centralizer_singleton_iff.mpr (hcomm ⟨x, hx⟩)⟩
  obtain ⟨S₀, ⟨e0⟩⟩ := exists_sylow_two_of_le (inf_le_left : J₀ ≤ C) S hSJ
  have hS₀ : ∃ r : ℕ, 3 ≤ r ∧
      Nonempty ((S₀ : Subgroup J₀) ≃* QuaternionGroup (2 ^ (r - 2))) :=
    ⟨n, hn, ⟨e0.trans e⟩⟩
  have hCN : centralizer ({z} : Set H) ≤ normalizer (J₀ : Set H) := by
    intro g hg
    have h1 : g ∈ normalizer (A : Set H) :=
      centralizer_singleton_le_normalizer_of_stdBare hA.1 hz hzC hg
    have h2 : g ∈ normalizer (C : Set H) :=
      CFSG.GorensteinWalter.normalizer_le_normalizer_centralizer_subgroup A h1
    have h3 : g ∈ normalizer (centralizer ({z} : Set H) : Set H) := Subgroup.le_normalizer hg
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨h2, h3⟩
  have hsub : CFSG.Open.IsSubnormal J₀ (centralizer ({z} : Set H)) :=
    CFSG.ClassicalInvolution.isSubnormal_of_normal_subgroupOf hJle
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hJle).mpr hCN)
  have hTE : CFSG.Open.classicalInvolutionTightlyEmbedded J₀ :=
    (CFSG.ClassicalInvolution.tightlyEmbedded_iff_centralizer_le_normalizer hzJ hz hJle S₀
      hS₀).mpr hCN
  haveI := hsimp
  exact h H hnonab z hz J₀ hzJ hsub S₀ hS₀ hTE

theorem card_eq_of_isSporadic_M11 {N : Type} [Group N]
    (h : IsSporadic N .M11) : Nat.card N = 7920 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv]
  exact CFSG.Sporadic.Mathieu.card_M11

theorem card_eq_of_isSporadic_M12 {N : Type} [Group N]
    (h : IsSporadic N .M12) : Nat.card N = 95040 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv]
  exact CFSG.Sporadic.Mathieu.card_M12

theorem not_isSporadic_M11_of_not_dvd {N : Type} [Group N]
    (h : ¬ Nat.card N ∣ 95040) : ¬ IsSporadic N .M11 := fun hM => by
  rw [card_eq_of_isSporadic_M11 hM] at h
  exact h (by norm_num)

theorem not_isSporadic_M12_of_not_dvd {N : Type} [Group N]
    (h : ¬ Nat.card N ∣ 95040) : ¬ IsSporadic N .M12 := fun hM => by
  rw [card_eq_of_isSporadic_M12 hM] at h
  exact h dvd_rfl

theorem Sol78Thm24_1CIT.use
    (h : Sol78Thm24_1CIT) : Sol78Thm24_1Use := by
  intro H _ _ N hN hord A hA hq
  rcases h H N hN A hA hq with h1 | h1 | h1
  · exact h1
  · exact absurd h1 (not_isSporadic_M11_of_not_dvd hord)
  · exact absurd h1 (not_isSporadic_M12_of_not_dvd hord)

theorem sol78Thm24_1Use_of_citPart2
    (h : CITPart2) : Sol78Thm24_1Use :=
  (sol78Thm24_1CIT_of_citPart2 h).use

end CFSG.EvenSporadicStandard.Induction
