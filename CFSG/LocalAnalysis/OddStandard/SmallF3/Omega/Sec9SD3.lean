module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SD1

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t z g : G} {L S B : Subgroup G}

theorem sec9d_not_conj_z_t (h37 : Asc82Lemma37) (hT6 : Asc82Tab6M)
    (h : Sec8Base G t L S z g B) : ¬ IsConj z t := by
  intro hconj
  obtain ⟨c, hc⟩ := isConj_iff_inv_mul.mp hconj
  have hLM : IsOm6M L := sec9d_isOm6M h
  have htC : t ∈ centralizer ({t} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hlayer : layerCent L t = ⊥ := by
    have h := h37 G t L h.toSec3SettingLB z c h.pocket (by rw [hc]; exact htC)
    rw [hc] at h
    simpa [layerCent] using h
  have htN : t ∈ normalizer (L : Set G) :=
    Subgroup.centralizer_le_normalizer (L : Set G) (sec9d_t_mem_cent h)
  rcases (hT6.layer_trivial G L hLM t h.involution htN).mp hlayer with h4 | h3
  · exact (hT6.nontrivial G L hLM t h.involution htN (Or.inl h4)) (sec9d_t_mem_cent h)
  · exact (hT6.nontrivial G L hLM t h.involution htN
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h3)))))) (sec9d_t_mem_cent h)

theorem sec9d_coset_disjoint_conj (h37 : Asc82Lemma37) (h66 : Asc82Lemma66)
    (hT6 : Asc82Tab6M) (hB8 : Asc82Sec8B) (h : Sec8Base G t L S z g B) :
    ∀ b ∈ B, t * b ∉ CFSG.conjugate L g := by
  intro b hb hw
  have hLM : IsOm6M L := sec9d_isOm6M h
  have hzL : z ∈ L := h.pocket.mem
  have hz2 : orderOf z = 2 := h.pocket.1
  have hbL : b ∈ L := (h.B_le hb).1
  have hwne : t * b ≠ 1 := by
    intro hwb
    have ht_eq : t = b⁻¹ := mul_eq_one_iff_eq_inv.mp hwb
    have hb'L : b⁻¹ ∈ L := (h.B_le (B.inv_mem hb)).1
    exact sec9d_t_not_mem h (ht_eq ▸ hb'L)
  have hww : (t * b) * (t * b) = 1 := by
    have hcomm : t * b = b * t := sec9d_t_B h hb
    calc (t * b) * (t * b) = t * (b * t) * b := by group
      _ = t * (t * b) * b := by rw [← hcomm]
      _ = (t * t) * (b * b) := by group
      _ = 1 := by rw [sec9d_t_sq h, sec9d_B_sq h hb, one_mul]
  have hw2 : orderOf (t * b) = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (p := 2) (by rwa [pow_two]) hwne
  have hvL : g * (t * b) * g⁻¹ ∈ L := (mem_conjugate_iff L g (t * b)).mp hw
  have hv2 : orderOf (g * (t * b) * g⁻¹) = 2 := by
    rw [show g * (t * b) * g⁻¹ = (g⁻¹)⁻¹ * (t * b) * g⁻¹ by rw [inv_inv]]
    rw [orderOf_conjugate_eq]
    exact hw2
  have hvin : g * (t * b) * g⁻¹ ∈ conjClassIn L z :=
    hT6.inv_one_class G L hLM z (g * (t * b) * g⁻¹) hzL hvL hz2 hv2
  have hzv : IsConj z (g * (t * b) * g⁻¹) := isConj_of_mem_conjClassIn hvin
  have hvw : IsConj (g * (t * b) * g⁻¹) (t * b) :=
    isConj_iff_inv_mul.mpr ⟨g, by group⟩
  have htw : IsConj t (t * b) := by
    by_cases hb1 : b = 1
    · rw [hb1, mul_one]
    · have hb2 : orderOf b = 2 := by
        haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        exact orderOf_eq_prime (p := 2) (by rw [pow_two]; exact sec9d_B_sq h hb) hb1
      exact h66 G t L h.toSec3SettingLB h.omega6m b hb2 hbL
  exact (sec9d_not_conj_z_t h37 hT6 h) (IsConj.trans hzv (hvw.trans (IsConj.symm htw)))

end CFSG.OddStandard.SmallF3.Omega
