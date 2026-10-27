module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.BenderBranchBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.Elementary

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

section Swap

variable {G : Type} [Group G]

theorem exists_involution_of_isPGroup_ne_bot [Finite G] {P : Subgroup G} (hP : IsPGroup 2 P) (hne : P ≠ ⊥) :
    ∃ r ∈ P, r ≠ 1 ∧ r ^ 2 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hne (Subgroup.card_eq_one.mp (by simpa using hk))
  have hdvd : 2 ∣ Nat.card P := by
    rw [hk]
    exact dvd_pow_self 2 hk0
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  have hy' : orderOf (y : G) = 2 := by rw [Subgroup.orderOf_coe, hy]
  refine ⟨y, y.2, ?_, orderOf_dvd_iff_pow_eq_one.mp (by rw [hy'])⟩
  intro h1
  rw [h1, orderOf_one] at hy'
  omega

theorem mem_normalizer_inf' {A B : Subgroup G} {g : G} (hA : g ∈ Subgroup.normalizer (A : Set G))
    (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro h
  exact (and_congr (hA h) (hB h))

theorem mem_normalizer_conjugate_of {A : Subgroup G} {g s : G}
    (h : s * g * s⁻¹ ∈ Subgroup.normalizer (A : Set G)) :
    g ∈ Subgroup.normalizer ((CFSG.conjugate A s : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have h1 := Subgroup.mem_normalizer_iff.mp h (s * x * s⁻¹)
  rw [BenderBranch.mem_conjugate_iff, BenderBranch.mem_conjugate_iff]
  have e : s * (g * x * g⁻¹) * s⁻¹ = (s * g * s⁻¹) * (s * x * s⁻¹) * (s * g * s⁻¹)⁻¹ := by group
  rw [e]
  exact h1

theorem mem_or_mul_mem_of_relIndex_two {R R₀ : Subgroup G} (h : R₀.relIndex R = 2) {a t : G}
    (ha : a ∈ R) (ht : t ∈ R) (ht0 : t ∉ R₀) : a ∈ R₀ ∨ a * t ∈ R₀ := by
  obtain ⟨c, hcR, hc⟩ := Subgroup.relIndex_eq_two_iff.mp h
  by_contra hn
  push Not at hn
  obtain ⟨ha0, hat0⟩ := hn
  have h1 : t * c ∈ R₀ := by
    rcases hc t ht with h1 | h1
    · exact h1.1
    · exact absurd h1.1 ht0
  have h2 : a * t * c ∈ R₀ := by
    rcases hc (a * t) (R.mul_mem ha ht) with h2 | h2
    · exact h2.1
    · exact absurd h2.1 hat0
  apply ha0
  have : a = (a * t * c) * (t * c)⁻¹ := by group
  rw [this]
  exact R₀.mul_mem h2 (R₀.inv_mem h1)

theorem exists_central_involution_or_card_le_four [Finite G] {R R2 D : Subgroup G} {s : G}
    (hW : IsPGroup 2 ↥(D ⊔ Subgroup.zpowers s)) (hR2R : R2 ≤ R) (hRD : R ≤ D)
    (hidx : R2.relIndex R = 2) (hR2D : D ≤ Subgroup.normalizer (R2 : Set G))
    (hsD : s ∈ Subgroup.normalizer (D : Set G)) (hsR : s ∈ Subgroup.normalizer (R : Set G))
    (hs2 : s ^ 2 ∈ D) :
    Nat.card R ≤ 4 ∨ ∃ r ∈ R2, r ≠ 1 ∧ r ^ 2 = 1 ∧
      ∀ w ∈ D ⊔ Subgroup.zpowers s, w * r = r * w := by
  classical
  set Q : Subgroup G := R2 ⊓ CFSG.conjugate R2 s with hQ
  have hDQ : D ≤ Subgroup.normalizer (Q : Set G) := by
    intro d hd
    refine mem_normalizer_inf' (hR2D hd) (mem_normalizer_conjugate_of ?_)
    have hd' : s * d * s⁻¹ ∈ D := by
      have := Subgroup.mem_normalizer_iff.mp hsD d
      exact this.mp hd
    exact hR2D hd'
  have hss : s * s ∈ Subgroup.normalizer (R2 : Set G) := by
    rw [← pow_two]; exact hR2D hs2
  have hsQ : s ∈ Subgroup.normalizer (Q : Set G) := by
    rw [← BenderBranch.conjugate_eq_iff_mem_normalizer]
    have e2 : CFSG.conjugate R2 (s * s) = R2 :=
      BenderBranch.conjugate_eq_iff_mem_normalizer.mpr hss
    rw [hQ, BenderBranch.conjugate_inf, BenderBranch.conjugate_conjugate, e2, inf_comm]
  have hWQ : D ⊔ Subgroup.zpowers s ≤ Subgroup.normalizer (Q : Set G) :=
    sup_le hDQ ((Subgroup.zpowers_le).mpr hsQ)
  by_cases hQ1 : Q = ⊥
  · left
    have hconjR : CFSG.conjugate R s = R := BenderBranch.conjugate_eq_iff_mem_normalizer.mpr hsR
    have h1 : (CFSG.conjugate R2 s).relIndex R = 2 := by
      have := Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj s⁻¹).toMonoidHom) R2 R
        (MulAut.conj s⁻¹).injective
      have e : (Subgroup.map (MulAut.conj s⁻¹).toMonoidHom R2).relIndex
          (Subgroup.map (MulAut.conj s⁻¹).toMonoidHom R) = (CFSG.conjugate R2 s).relIndex R := by
        change (CFSG.conjugate R2 s).relIndex (CFSG.conjugate R s) = _
        rw [hconjR]
      rw [← e, this, hidx]
    have h2 := Subgroup.relIndex_inf_le (H := R2) (K := CFSG.conjugate R2 s) (L := R)
    rw [← hQ, hQ1, Subgroup.relIndex_bot_left, hidx, h1] at h2
    omega
  · right
    have hQW : Q ≤ D ⊔ Subgroup.zpowers s :=
      (inf_le_left.trans (hR2R.trans hRD)).trans le_sup_left
    have hne := inf_centralizer_ne_bot_of_normalizes hW hQW hWQ hQ1
    have hP2 : IsPGroup 2 ↥(Q ⊓ Subgroup.centralizer ((D ⊔ Subgroup.zpowers s : Subgroup G) :
        Set G)) := hW.to_le (inf_le_left.trans hQW)
    obtain ⟨r, hr, hr1, hr2⟩ := exists_involution_of_isPGroup_ne_bot hP2 hne
    have hrQ : r ∈ Q := hr.1
    refine ⟨r, hrQ.1, hr1, hr2, fun w hw => ?_⟩
    exact Subgroup.mem_centralizer_iff.mp hr.2 w hw

end Swap

end CFSG.QuasithinUnique
