module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingModel
public import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalInvolutionOddCore
public import CFSG.LocalAnalysis.LyonsUnitaryFour.OrderThreeComplement

public section

namespace CFSG.ComponentClassification.AlternatingUnbalanced

open Equiv Subgroup

theorem exists_involution_cycle_count {n : ℕ} {t : Perm (Fin n)} (ht : orderOf t = 2) :
    ∃ r : ℕ, n = 2 * r + Nat.card {ω // t ω = ω} ∧ Perm.sign t = (-1) ^ r := by
  classical
  have h2 : t ^ 2 = 1 := by
    rw [← ht]
    exact pow_orderOf_eq_one t
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hct : ∀ c ∈ t.cycleType, c = 2 := Perm.pow_prime_eq_one_iff.1 h2
  set r := Multiset.card t.cycleType with hr
  have hrep : t.cycleType = Multiset.replicate r 2 := Multiset.eq_replicate.2 ⟨rfl, hct⟩
  have hsum : t.support.card = 2 * r := by
    rw [← Perm.sum_cycleType, hrep, Multiset.sum_replicate, smul_eq_mul, mul_comm]
  have hfix : Nat.card {ω // t ω = ω} + t.support.card = n := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    have h := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin n))) (fun ω => t ω = ω)
    rw [Finset.card_univ, Fintype.card_fin] at h
    convert h using 3
    ext ω
    simp [Perm.mem_support]
  refine ⟨r, by omega, ?_⟩
  rw [Perm.sign_of_cycleType, hrep, Multiset.sum_replicate, Multiset.card_replicate, smul_eq_mul,
    show r * 2 + r = 2 * r + r by ring, pow_add, pow_mul]
  simp

theorem alternating_generalized_fitting_unbalanced_degree {G : Type*} [Group G] [Finite G]
    [IsSimpleGroup (GeneralizedFitting.subgroup G)]
    (hnonab : ∃ a b : GeneralizedFitting.subgroup G, a * b ≠ b * a) {n : ℕ} (hn : 7 ≤ n)
    (hiso : Nonempty (GeneralizedFitting.subgroup G ≃* alternatingGroup (Fin n)))
    {z : G} (hz : orderOf z = 2) (hcore : oddCore (centralizer ({z} : Set G)) ≠ ⊥) :
    Odd n ∧ (n % 4 = 1 → GeneralizedFitting.subgroup G < ⊤) ∧
    ∀ θ : GeneralizedFitting.subgroup G ≃* alternatingGroup (Fin n),
      ∃ ρ : G →* Perm (Fin n), Function.Injective ρ ∧
        (∀ f : GeneralizedFitting.subgroup G, ρ f.val = (θ f).val) ∧
        Nat.card {ω // ρ z ω = ω} = 3 ∧
        (GeneralizedFitting.subgroup G = ⊤ → n % 4 = 3) := by
  have key : ∀ θ : GeneralizedFitting.subgroup G ≃* alternatingGroup (Fin n),
      ∃ ρ : G →* Perm (Fin n), Function.Injective ρ ∧
        (∀ f : GeneralizedFitting.subgroup G, ρ f.val = (θ f).val) ∧
        Nat.card {ω // ρ z ω = ω} = 3 ∧
        (GeneralizedFitting.subgroup G = ⊤ → n % 4 = 3) ∧ Odd n := by
    intro θ
    obtain ⟨ρ, hρ, hext, hmap, hcont, -⟩ :=
      CatalogueBAlternating.generalizedFitting_permutation_model hnonab (Or.inr hn) θ
    have ht : orderOf (ρ z) = 2 := by
      rw [orderOf_injective ρ hρ]
      exact hz
    have hCmap : (centralizer ({z} : Set G)).map ρ =
        ρ.range ⊓ centralizer ({ρ z} : Set (Perm (Fin n))) := by
      ext x
      constructor
      · rintro ⟨g, hg, rfl⟩
        refine Subgroup.mem_inf.2 ⟨⟨g, rfl⟩, ?_⟩
        rw [SetLike.mem_coe, mem_centralizer_singleton_iff] at hg
        rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hg]
      · intro hx
        obtain ⟨⟨g, rfl⟩, hx⟩ := Subgroup.mem_inf.1 hx
        refine ⟨g, ?_, rfl⟩
        rw [mem_centralizer_singleton_iff] at hx
        rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
        apply hρ
        rw [map_mul, map_mul]
        exact hx
    let e : centralizer ({z} : Set G) ≃*
        ↥(ρ.range ⊓ centralizer ({ρ z} : Set (Perm (Fin n)))) :=
      ((centralizer ({z} : Set G)).equivMapOfInjective ρ hρ).trans (MulEquiv.subgroupCongr hCmap)
    have hcore' : oddCore ↥(ρ.range ⊓ centralizer ({ρ z} : Set (Perm (Fin n)))) ≠ ⊥ := by
      rw [← LyonsUnitaryFour.oddCore_map_mulEquiv e]
      intro h
      apply hcore
      rwa [Subgroup.map_eq_bot_iff_of_injective _ e.injective] at h
    have hfix : Nat.card {ω // ρ z ω = ω} = 3 := by
      by_contra hne
      exact hcore' ((SymmetricLocal.involution_permutation_centralizer_odd_core hcont ht).1 hne)
    obtain ⟨r, hnr, hsign⟩ := exists_involution_cycle_count ht
    rw [hfix] at hnr
    refine ⟨ρ, hρ, hext, hfix, fun htop => ?_, ⟨r + 1, by omega⟩⟩
    have htA : ρ z ∈ alternatingGroup (Fin n) := by
      rw [← hmap]
      exact ⟨z, by rw [htop]; exact mem_top z, rfl⟩
    rw [Perm.mem_alternatingGroup, hsign] at htA
    have hr : Even r := by
      rcases Nat.even_or_odd r with h | h
      · exact h
      · rw [h.neg_one_pow] at htA
        exact absurd htA (by decide)
    obtain ⟨k, rfl⟩ := hr
    omega
  obtain ⟨θ₀⟩ := hiso
  obtain ⟨-, -, -, -, htop₀, hodd⟩ := key θ₀
  refine ⟨hodd, fun h1 => lt_top_iff_ne_top.2 fun htop => ?_, fun θ => ?_⟩
  · have := htop₀ htop
    omega
  · obtain ⟨ρ, hρ, hext, hfix, htop, -⟩ := key θ
    exact ⟨ρ, hρ, hext, hfix, htop⟩

end CFSG.ComponentClassification.AlternatingUnbalanced
