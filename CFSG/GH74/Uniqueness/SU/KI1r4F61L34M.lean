module

public import CFSG.GH74.Uniqueness.SU.KI1r4L34Model
public meta import CFSG.GH74.KGroups.L34Tables
public meta import CFSG.GH74.KGroups.L34Aut
public meta import CFSG.GH74.KGroups.L34
public meta import CFSG.GH74.KGroups.Checks
public import CFSG.GH74.Uniqueness.SU.KI1r4F61L34MInputs
public meta import CFSG.GH74.Uniqueness.SU.KI1r4F61L34MInputs
public import Certificates.Certificate5122
public import Certificates.Certificate5123
public import Certificates.Certificate5138

public section

namespace CFSG.GH74.Uniqueness.SU.K.R4.L34M

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.GH74.KGroups CFSG.GH74.KGroups.L34

theorem cover :
    ((elemsT QA).all fun g => !decide (g ^ 2 = 1) || decide (g = 1) || cl1.contains g ||
    cl2.contains g || cl3.contains g || cl4.contains g) = true :=
  Certificates.certificate5138.1

@[expose] def E4Wit (r u v : Equiv.Perm (Fin 42)) : Prop :=
  u ∈ QP.originalSubgroup ∧ v ∈ QP.originalSubgroup ∧ u ≠ 1 ∧ v ≠ 1 ∧ u ≠ v ∧ u ^ 2 = 1 ∧
    v ^ 2 = 1 ∧ u * v = v * u ∧ r * u = u * r ∧ r * v = v * r

theorem e4_wit
    (r u v : Equiv.Perm (Fin 42)) (hu : QP.sift u 0 = true) (hv : QP.sift v 0 = true)
    (h : (decide (u ≠ 1) && decide (v ≠ 1) && decide (u ≠ v) && decide (u ^ 2 = 1) &&
      decide (v ^ 2 = 1) && decide (u * v = v * u) && decide (r * u = u * r) &&
      decide (r * v = v * r)) = true) : E4Wit r u v := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨(mem_iff_sift QP QP_ok u).2 hu, (mem_iff_sift QP QP_ok v).2 hv, h1, h2, h3, h4, h5, h6,
    h7, h8⟩

theorem e4_0_check : QP.sift e4u0 0 = true ∧ QP.sift e4v0 0 = true ∧
    (decide (e4u0 ≠ 1) && decide (e4v0 ≠ 1) && decide (e4u0 ≠ e4v0) && decide (e4u0 ^ 2 = 1) &&
      decide (e4v0 ^ 2 = 1) && decide (e4u0 * e4v0 = e4v0 * e4u0) && decide (1 * e4u0 = e4u0 * 1) &&
      decide (1 * e4v0 = e4v0 * 1)) = true :=
  Certificates.certificate5138.2.2.1

theorem e4_0 : E4Wit 1 e4u0 e4v0 :=
  e4_wit _ _ _ e4_0_check.1 e4_0_check.2.1 e4_0_check.2.2

theorem e4_1_check : QP.sift e4u1 0 = true ∧ QP.sift e4v1 0 = true ∧
    (decide (e4u1 ≠ 1) && decide (e4v1 ≠ 1) && decide (e4u1 ≠ e4v1) && decide (e4u1 ^ 2 = 1) &&
      decide (e4v1 ^ 2 = 1) && decide (e4u1 * e4v1 = e4v1 * e4u1) && decide (rep1 * e4u1 = e4u1 * rep1) &&
      decide (rep1 * e4v1 = e4v1 * rep1)) = true :=
  Certificates.certificate5138.2.2.2.1

theorem e4_1 : E4Wit rep1 e4u1 e4v1 :=
  e4_wit _ _ _ e4_1_check.1 e4_1_check.2.1 e4_1_check.2.2

theorem e4_2_check : QP.sift e4u2 0 = true ∧ QP.sift e4v2 0 = true ∧
    (decide (e4u2 ≠ 1) && decide (e4v2 ≠ 1) && decide (e4u2 ≠ e4v2) && decide (e4u2 ^ 2 = 1) &&
      decide (e4v2 ^ 2 = 1) && decide (e4u2 * e4v2 = e4v2 * e4u2) && decide (rep2 * e4u2 = e4u2 * rep2) &&
      decide (rep2 * e4v2 = e4v2 * rep2)) = true :=
  Certificates.certificate5138.2.2.2.2.1

theorem e4_2 : E4Wit rep2 e4u2 e4v2 :=
  e4_wit _ _ _ e4_2_check.1 e4_2_check.2.1 e4_2_check.2.2

theorem e4_3_check : QP.sift e4u3 0 = true ∧ QP.sift e4v3 0 = true ∧
    (decide (e4u3 ≠ 1) && decide (e4v3 ≠ 1) && decide (e4u3 ≠ e4v3) && decide (e4u3 ^ 2 = 1) &&
      decide (e4v3 ^ 2 = 1) && decide (e4u3 * e4v3 = e4v3 * e4u3) && decide (rep3 * e4u3 = e4u3 * rep3) &&
      decide (rep3 * e4v3 = e4v3 * rep3)) = true :=
  Certificates.certificate5138.2.2.2.2.2

theorem e4_3 : E4Wit rep3 e4u3 e4v3 :=
  e4_wit _ _ _ e4_3_check.1 e4_3_check.2.1 e4_3_check.2.2

theorem nine_dvd_rep4 : 9 ∣ Nat.card ↥(QP.originalSubgroup ⊓
    Subgroup.centralizer ({rep4} : Set (Equiv.Perm (Fin 42)))) :=
  Certificates.certificate5138.2.1

theorem E4Wit.conj
    {r u v : Equiv.Perm (Fin 42)} (h : E4Wit r u v) {a : Equiv.Perm (Fin 42)}
    (ha : a ∈ QA.originalSubgroup) : E4Wit (a * r * a⁻¹) (a * u * a⁻¹) (a * v * a⁻¹) := by
  obtain ⟨hu, hv, hu1, hv1, huv, hu2, hv2, huv', hru, hrv⟩ := h
  refine ⟨QA_conj_QP a ha u hu, QA_conj_QP a ha v hv, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h1
    exact hu1 (by simpa using h1)
  · intro h1
    exact hv1 (by simpa using h1)
  · intro h1
    exact huv (by simpa using h1)
  · rw [conj_pow, hu2]
    group
  · rw [conj_pow, hv2]
    group
  · calc a * u * a⁻¹ * (a * v * a⁻¹) = a * (u * v) * a⁻¹ := by group
      _ = a * (v * u) * a⁻¹ := by rw [huv']
      _ = a * v * a⁻¹ * (a * u * a⁻¹) := by group
  · calc a * r * a⁻¹ * (a * u * a⁻¹) = a * (r * u) * a⁻¹ := by group
      _ = a * (u * r) * a⁻¹ := by rw [hru]
      _ = a * u * a⁻¹ * (a * r * a⁻¹) := by group
  · calc a * r * a⁻¹ * (a * v * a⁻¹) = a * (r * v) * a⁻¹ := by group
      _ = a * (v * r) * a⁻¹ := by rw [hrv]
      _ = a * v * a⁻¹ * (a * r * a⁻¹) := by group

theorem card_centralizer_conj
    {a : Equiv.Perm (Fin 42)} (ha : a ∈ QA.originalSubgroup)
    (r : Equiv.Perm (Fin 42)) :
    Nat.card ↥(QP.originalSubgroup ⊓
        Subgroup.centralizer ({a * r * a⁻¹} : Set (Equiv.Perm (Fin 42)))) =
      Nat.card ↥(QP.originalSubgroup ⊓
        Subgroup.centralizer ({r} : Set (Equiv.Perm (Fin 42)))) := by
  have hai : a⁻¹ ∈ QA.originalSubgroup := QA.originalSubgroup.inv_mem ha
  refine Nat.card_congr
    { toFun := fun y => ⟨a⁻¹ * y.1 * a⁻¹⁻¹, Subgroup.mem_inf.2
        ⟨QA_conj_QP a⁻¹ hai y.1 (Subgroup.mem_inf.1 y.2).1, by
          rw [Subgroup.mem_centralizer_singleton_iff]
          have := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 y.2).2
          calc a⁻¹ * y.1 * a⁻¹⁻¹ * r = a⁻¹ * (y.1 * (a * r * a⁻¹)) * a := by group
            _ = a⁻¹ * ((a * r * a⁻¹) * y.1) * a := by rw [this]
            _ = r * (a⁻¹ * y.1 * a⁻¹⁻¹) := by group⟩⟩
      invFun := fun z => ⟨a * z.1 * a⁻¹, Subgroup.mem_inf.2
        ⟨QA_conj_QP a ha z.1 (Subgroup.mem_inf.1 z.2).1, by
          rw [Subgroup.mem_centralizer_singleton_iff]
          have := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 z.2).2
          calc a * z.1 * a⁻¹ * (a * r * a⁻¹) = a * (z.1 * r) * a⁻¹ := by group
            _ = a * (r * z.1) * a⁻¹ := by rw [this]
            _ = a * r * a⁻¹ * (a * z.1 * a⁻¹) := by group⟩⟩
      left_inv := fun y => by
        apply Subtype.ext
        simp [mul_assoc]
      right_inv := fun z => by
        apply Subtype.ext
        simp [mul_assoc] }

theorem gens_mem_QA : ∀ g ∈ [PA, PB, sg0, sg1, sg2], g ∈ QA.originalSubgroup := by
  intro g hg
  rw [QA_closure']
  exact Subgroup.subset_closure hg

theorem l34_involution_cases :
    ∀ g ∈ QA.originalSubgroup, g ^ 2 = 1 →
    (∃ u v : Equiv.Perm (Fin 42), E4Wit g u v) ∨
      9 ∣ Nat.card ↥(QP.originalSubgroup ⊓
        Subgroup.centralizer ({g} : Set (Equiv.Perm (Fin 42)))) := by
  intro g hg hg2
  have h1 := forall_of_all QA QA_ok cover g hg
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    decide_eq_true_eq] at h1
  have hconj : ∀ (r : Equiv.Perm (Fin 42)) (ws : List (List ℤ)), g ∈ clList r ws →
      ∃ a ∈ QA.originalSubgroup, g = a * r * a⁻¹ := by
    intro r ws hmem
    obtain ⟨w, -, hw⟩ := List.mem_map.1 hmem
    refine ⟨evalCodes [PA, PB, sg0, sg1, sg2] w, evalCodes_mem_of_gens _ _ gens_mem_QA w, ?_⟩
    rw [← hw, tab_eq]
  rcases h1 with ((((h | h) | h) | h) | h) | h
  · exact absurd hg2 h
  · left
    subst h
    exact ⟨_, _, e4_0⟩
  · obtain ⟨a, ha, rfl⟩ := hconj rep1 words1 (List.contains_iff_mem.1 h)
    exact Or.inl ⟨_, _, e4_1.conj ha⟩
  · obtain ⟨a, ha, rfl⟩ := hconj rep2 words2 (List.contains_iff_mem.1 h)
    exact Or.inl ⟨_, _, e4_2.conj ha⟩
  · obtain ⟨a, ha, rfl⟩ := hconj rep3 words3 (List.contains_iff_mem.1 h)
    exact Or.inl ⟨_, _, e4_3.conj ha⟩
  · obtain ⟨a, ha, rfl⟩ := hconj rep4 words4 (List.contains_iff_mem.1 h)
    right
    rw [card_centralizer_conj ha rep4]
    exact nine_dvd_rep4

end CFSG.GH74.Uniqueness.SU.K.R4.L34M
