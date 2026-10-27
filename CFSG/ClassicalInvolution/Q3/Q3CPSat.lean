module

public import CFSG.ClassicalInvolution.Q3.Q3CPLocC

public section

namespace CFSG.ClassicalInvolution.Q3.Q3CP

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G]

abbrev satClass (K : Subgroup G) (z : G) : Set (Subgroup G) :=
  CoreAssembly.conjClass (satU (.sl2 3 1) K z)

section Dictionary

variable [Finite G] {K : Subgroup G} {z : G}

theorem satU_mem_satClass (hz : IsClassicalMember3 K z) {L : Subgroup G} {w : G}
    (hL : L ∈ conjClass3 K) (hw : IsClassicalMember3 L w) :
    satU (.sl2 3 1) L w ∈ satClass K z := by
  obtain ⟨g, rfl, rfl⟩ := conjClass3_involution hz hL hw
  exact mem_conjClass_satU_iff.mpr ⟨g, rfl⟩

omit [Finite G] in
theorem exists_raw_of_mem_satClass (hz : IsClassicalMember3 K z) {M : Subgroup G}
    (hM : M ∈ satClass K z) :
    ∃ (M₀ : Subgroup G) (w : G), M₀ ∈ conjClass3 K ∧ IsClassicalMember3 M₀ w ∧
      M = satU (.sl2 3 1) M₀ w := by
  obtain ⟨g, rfl⟩ := mem_conjClass_satU_iff.mp hM
  exact ⟨conjSub g K, g * z * g⁻¹, ⟨g, rfl⟩, hz.conj g, rfl⟩

theorem isUniqueInvolution_satU {L : Subgroup G} {w : G} (hw : IsClassicalMember3 L w) :
    IsUniqueInvolution (satU (.sl2 3 1) L w) w :=
  ((IsClassicalMemberU.ofQ3 hw).satU_member).isUniqueInvolution (MemberType.cert_sl2 3 1)

theorem satU_le_centralizer {L : Subgroup G} {w : G} (hw : IsClassicalMember3 L w) :
    satU (.sl2 3 1) L w ≤ Subgroup.centralizer ({w} : Set G) :=
  ((IsClassicalMemberU.ofQ3 hw).satU_member).le_centralizer

omit [Finite G] in
theorem le_satU_member {L : Subgroup G} {w : G} : L ≤ satU (.sl2 3 1) L w := le_satU

theorem isSylow2In_satU {L : Subgroup G} {w : G} (hw : IsClassicalMember3 L w) {P : Subgroup G}
    (hP : IsSylow2In P L) : IsSylow2In P (satU (.sl2 3 1) L w) := by
  have hm := IsClassicalMemberU.ofQ3 hw
  obtain ⟨V, hV⟩ := exists_isSylow2In (satU (.sl2 3 1) L w)
  have hc : Nat.card P = Nat.card V :=
    hm.natCard_isSylow2In_eq_of_members hm.satU_member hP hV
  exact hV.of_natCard_le hP.2.1 (hP.1.trans le_satU) (le_of_eq hc.symm)

omit [Finite G] in
theorem mem_of_isSylow2In_of_isUniqueInvolution {M P : Subgroup G} {y : G}
    (hy : IsUniqueInvolution M y) (hP : IsSylow2In P M) : y ∈ P := by
  have hc : ∀ m ∈ M, m * y = y * m := by
    intro m hm
    have hmy : m * y * m⁻¹ ∈ M := M.mul_mem (M.mul_mem hm hy.mem) (M.inv_mem hm)
    have hsq : (m * y * m⁻¹) * (m * y * m⁻¹) = 1 := by
      calc (m * y * m⁻¹) * (m * y * m⁻¹) = m * (y * y) * m⁻¹ := by group
        _ = 1 := by rw [hy.sq]; group
    rcases hy.unique _ hmy hsq with h1 | h1
    · exfalso
      apply hy.ne_one
      have : y = m⁻¹ * (m * y * m⁻¹) * m := by group
      rw [this, h1]
      group
    · calc m * y = (m * y * m⁻¹) * m := by group
        _ = y * m := by rw [h1]
  have h2 : IsPGroup 2 (Subgroup.zpowers y) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact hy.sq) hy.ne_one]
    norm_num
  have hyc : y ∈ Subgroup.centralizer (P : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun h hh => hc h (hP.1 hh)
  have hnorm : Subgroup.zpowers y ≤ Subgroup.normalizer (P : Set G) :=
    (Subgroup.zpowers_le.mpr hyc).trans (Subgroup.centralizer_le_normalizer _)
  have hsup : IsPGroup 2 ↥(Subgroup.zpowers y ⊔ P) := h2.to_sup_of_normal_right' hP.2.1 hnorm
  have hle : Subgroup.zpowers y ⊔ P ≤ M := sup_le (Subgroup.zpowers_le.mpr hy.mem) hP.1
  have heq := hP.2.2 (Subgroup.zpowers y ⊔ P) hle hsup le_sup_right
  exact heq ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers y)

end Dictionary

section Branch

variable [Finite G] [IsSimpleGroup G] {K : Subgroup G} {z : G}

theorem satClass_eq_of_involution_eq (hnab : ∃ a b : G, a * b ≠ b * a)
    (hz : IsClassicalMember3 K z) (hΔ : DeltaConnected K) (hB : ¬ BootData3 (conjClass3 K))
    (hC : LocCommuteAt K z) {M N : Subgroup G} {w : G} (hM : M ∈ satClass K z)
    (hN : N ∈ satClass K z) (hMw : IsUniqueInvolution M w) (hNw : IsUniqueInvolution N w) :
    M = N := by
  have hBz : IsUniqueInvolution (satU (.sl2 3 1) K z) z :=
    isUniqueInvolution_satU hz
  obtain ⟨a, rfl⟩ := CoreAssembly.single_class _ M hM
  obtain ⟨b, rfl⟩ := CoreAssembly.single_class _ N hN
  have hwa : w = a * z * a⁻¹ := hMw.eq (hBz.conj a)
  have hwb : w = b * z * b⁻¹ := hNw.eq (hBz.conj b)
  have hN' : conjSub (a⁻¹ * b) (satU (.sl2 3 1) K z) ∈ satClass K z := ⟨a⁻¹ * b, rfl⟩
  have hu : IsUniqueInvolution (conjSub (a⁻¹ * b) (satU (.sl2 3 1) K z)) z := by
    have h1 := hBz.conj (a⁻¹ * b)
    have : a⁻¹ * b * z * (a⁻¹ * b)⁻¹ = z := by
      have e1 : a * z * a⁻¹ = b * z * b⁻¹ := hwa.symm.trans hwb
      calc a⁻¹ * b * z * (a⁻¹ * b)⁻¹ = a⁻¹ * (b * z * b⁻¹) * a := by group
        _ = a⁻¹ * (a * z * a⁻¹) * a := by rw [e1]
        _ = z := by group
    rwa [this] at h1
  have h2 := noTwins3_of_loc hnab hz hΔ hB hC hN' hu
  have h3 : conjSub b (satU (.sl2 3 1) K z) =
      conjSub a (conjSub (a⁻¹ * b) (satU (.sl2 3 1) K z)) := by
    rw [← conjSub_mul]
    congr 1
    group
  rw [h3, h2]

theorem centralizer_le_normalizer_of_mem_satClass (hnab : ∃ a b : G, a * b ≠ b * a)
    (hz : IsClassicalMember3 K z) (hΔ : DeltaConnected K) (hB : ¬ BootData3 (conjClass3 K))
    (hC : LocCommuteAt K z) {M : Subgroup G} {w : G} (hM : M ∈ satClass K z)
    (hMw : IsUniqueInvolution M w) :
    Subgroup.centralizer ({w} : Set G) ≤ Subgroup.normalizer (M : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff] at hx
  have hΩ := hypOmegaModU_of_loc hnab hz hΔ hB hC
  have hxM : conjSub x M ∈ satClass K z := hΩ.conjInvariant x M hM
  have hu : IsUniqueInvolution (conjSub x M) w := by
    have h1 := hMw.conj x
    have : x * w * x⁻¹ = w := by
      calc x * w * x⁻¹ = (w * x) * x⁻¹ := by rw [hx]
        _ = w := by group
    rwa [this] at h1
  have := satClass_eq_of_involution_eq hnab hz hΔ hB hC hxM hM hu hMw
  exact mem_normalizer_iff_conjSub_eq.mpr this

end Branch

end CFSG.ClassicalInvolution.Q3.Q3CP
