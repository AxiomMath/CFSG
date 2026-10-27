module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Lemma65Comm

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem isKleinFour_sup_zpowers {z t : G} (hz2 : z * z = 1) (ht2 : t * t = 1) (hz1 : z ≠ 1)
    (ht1 : t ≠ 1) (hzt : z ≠ t) (hc : z * t = t * z) :
    IsKleinFour ↥(zpowers z ⊔ zpowers t) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzo : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1
  have hto : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact ht2) ht1
  have hzt' : zpowers t ≤ centralizer (zpowers z : Set G) := by
    rw [zpowers_le]
    rw [mem_centralizer_iff]
    intro x hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
    exact ((show Commute z t from hc).zpow_left k).eq
  have hdisj : Disjoint (zpowers z) (zpowers t) := by
    rw [Subgroup.disjoint_def]
    intro x hxz hxt
    rcases mem_zpowers_sq_eq_one hz2 hxz with h1 | h1
    · exact h1
    · rcases mem_zpowers_sq_eq_one ht2 hxt with h2 | h2
      · exact h2
      · exact absurd (h1.symm.trans h2) hzt
  have hcard : Nat.card ↥(zpowers z ⊔ zpowers t) = 4 := by
    have e := Nat.card_congr (prodSupEquiv hzt' hdisj).toEquiv
    rw [Nat.card_prod, Nat.card_zpowers, Nat.card_zpowers, hzo, hto] at e
    exact e.symm
  have hsq : ∀ g : ↥(zpowers z ⊔ zpowers t), g ^ 2 = 1 := by
    rintro ⟨g, hg⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer hzt' hg
    have hab : a * b = b * a := mem_centralizer_iff.1 (hzt' hb) a ha
    have ha2 : a * a = 1 := by
      rcases mem_zpowers_sq_eq_one hz2 ha with h1 | h1
      · rw [h1, one_mul]
      · rw [h1]; exact hz2
    have hb2 : b * b = 1 := by
      rcases mem_zpowers_sq_eq_one ht2 hb with h1 | h1
      · rw [h1, one_mul]
      · rw [h1]; exact ht2
    apply Subtype.ext
    show (a * b) ^ 2 = 1
    calc (a * b) ^ 2 = a * b * (a * b) := pow_two _
      _ = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hab]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [ha2, hb2, one_mul]
  refine ⟨hcard, ?_⟩
  have hdvd : Monoid.exponent ↥(zpowers z ⊔ zpowers t) ∣ 2 :=
    Monoid.exponent_dvd_of_forall_pow_eq_one hsq
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h1
  · exfalso
    have hz' : (⟨z, mem_sup_left (mem_zpowers z)⟩ : ↥(zpowers z ⊔ zpowers t)) ^
        Monoid.exponent ↥(zpowers z ⊔ zpowers t) = 1 := Monoid.pow_exponent_eq_one _
    rw [h1, pow_one] at hz'
    exact hz1 (congrArg Subtype.val hz')
  · exact h1

theorem klein_sylow_no_swap {M : Subgroup G} {z t : G} (hz2 : z * z = 1) (ht2 : t * t = 1)
    (hz1 : z ≠ 1) (ht1 : t ≠ 1) (hzt : z ≠ t) (hc : z * t = t * z) (hzM : z ∈ M) (htM : t ∈ M)
    (htc : ∀ m ∈ M, m * t = t * m) (hS2 : IsPGroup 2 ↥(zpowers z ⊔ zpowers t))
    (hmax : ∀ R : Subgroup G, IsPGroup 2 ↥R → R ≤ M → zpowers z ⊔ zpowers t ≤ R →
      R = zpowers z ⊔ zpowers t)
    {m : G} (hm : m ∈ M) : m * z * m⁻¹ ≠ z * t := by
  classical
  intro hsw
  set S := zpowers z ⊔ zpowers t with hS
  have hSM : S ≤ M := sup_le (zpowers_le.2 hzM) (zpowers_le.2 htM)
  have hzS : z ∈ S := mem_sup_left (mem_zpowers z)
  have htS : t ∈ S := mem_sup_right (mem_zpowers t)
  let Ssyl : Sylow 2 M := sylowOfMaximal M S hS2 hSM hmax
  have hK : IsKleinFour ↥S := isKleinFour_sup_zpowers hz2 ht2 hz1 ht1 hzt hc
  have : IsKleinFour ↥S := hK
  obtain ⟨e₁⟩ : Nonempty (DihedralGroup 2 ≃* ↥S) := IsKleinFour.nonempty_mulEquiv
  have e : DihedralGroup (2 ^ (2 - 1)) ≃* ↥(Ssyl : Subgroup M) :=
    e₁.trans (Subgroup.subgroupOfEquivOfLe hSM).symm
  have hcen : ∃ t' ∈ Subgroup.center M, orderOf t' = 2 := by
    refine ⟨⟨t, htM⟩, ?_, ?_⟩
    · rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (htc g g.2)
    · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact orderOf_eq_prime (by rw [pow_two]; exact Subtype.ext ht2)
        (fun h => ht1 (congrArg Subtype.val h))
  obtain ⟨N, hN, -, -, -, -, -, hinf, hbij⟩ :=
    CFSG.Semidihedral.Principal.dihedral_central_involution_normal_odd_complement Ssyl
      (n := 2) le_rfl ⟨e⟩ hcen
  let q : M →* M ⧸ N := QuotientGroup.mk' N
  let f : ↥(Ssyl : Subgroup M) →* M ⧸ N := q.comp (Ssyl : Subgroup M).subtype
  have hcommS : ∀ a b : ↥(Ssyl : Subgroup M), a * b = b * a := by
    intro a b
    apply e.symm.injective
    rw [map_mul, map_mul]
    exact mul_comm_of_exponent_two (IsKleinFour.exponent_two (G := DihedralGroup 2)) _ _
  have hq_comm : ∀ a b : M ⧸ N, a * b = b * a := by
    intro a b
    obtain ⟨s₁, rfl⟩ := hbij.2 a
    obtain ⟨s₂, rfl⟩ := hbij.2 b
    rw [← map_mul, ← map_mul, hcommS s₁ s₂]
  let m' : M := ⟨m, hm⟩
  let z' : M := ⟨z, hzM⟩
  let t' : M := ⟨t, htM⟩
  have hsw' : m' * z' * m'⁻¹ = z' * t' := Subtype.ext hsw
  have h1 : q (m' * z' * m'⁻¹) = q z' := by
    calc q (m' * z' * m'⁻¹) = q m' * q z' * (q m')⁻¹ := by simp only [map_mul, map_inv]
      _ = q z' * q m' * (q m')⁻¹ := by rw [hq_comm (q m') (q z')]
      _ = q z' := by group
  rw [hsw', map_mul] at h1
  have h2 : q t' = 1 := by
    have : q z' * q t' = q z' * 1 := by rw [h1, mul_one]
    exact mul_left_cancel this
  have h3 : t' ∈ N := (QuotientGroup.eq_one_iff t').1 h2
  have h4 : t' ∈ (Ssyl : Subgroup M) := mem_subgroupOf.2 htS
  have h5 : t' ∈ N ⊓ (Ssyl : Subgroup M) := ⟨h3, h4⟩
  rw [hinf, mem_bot] at h5
  exact ht1 (congrArg Subtype.val h5)

end CFSG.EvenSporadicStandard.Fin76b
