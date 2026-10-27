module

public import CFSG.GH74.KGroups.Generic5
public import CFSG.GH74.E2.FrattiniRank

public section

namespace CFSG.GH74.KGroups

@[expose] def GenLE4 (X : Type*) [Group X] : Prop :=
  ∀ P : Subgroup X, IsPGroup 2 P → ∃ s : Finset X, s.card ≤ 4 ∧ Subgroup.closure (s : Set X) = P

theorem not_genLE4_of_elementary {C : Type*} [Group C] [Finite C] (A : Subgroup C)
    (hA : ∀ a ∈ A, a ^ 2 = 1 ∧ ∀ b ∈ A, a * b = b * a) (hcard : Nat.card A = 32) :
    ¬ GenLE4 C := by
  intro hG
  have hp : IsPGroup 2 A := IsPGroup.of_card (n := 5) (by rw [hcard]; norm_num)
  obtain ⟨s, hs, hcl⟩ := hG A hp
  have hcomm : IsMulCommutative A := by
    constructor
    constructor
    intro a b
    exact Subtype.ext ((hA a a.2).2 b b.2)
  have h2 : ∀ y : A, y ^ 2 = 1 := fun y => Subtype.ext (by simpa using (hA y y.2).1)
  have h32 := CFSG.GH74.E2.two_pow_rank_eq_card_of_exponent_two (Y := A) h2
  rw [hcard] at h32
  have hrank : Group.rank A ≤ 4 := by
    have h1 := Subgroup.rank_closure_finset_le_card s
    have h2 : Group.rank (Subgroup.closure (s : Set C)) = Group.rank A := Subgroup.rank_congr hcl
    omega
  have : 2 ^ Group.rank A ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hrank
  omega

theorem not_genLE4_double_cover {C : Type} [Group C] [Finite C]
    (hZ : Nat.card (Subgroup.center C) = 2) {G : Type} [Group G]
    (P : Subgroup G) (e : C ⧸ Subgroup.center C ≃* P) (E : Subgroup G) (hEP : E ≤ P)
    (hEcard : Nat.card E = 16) (hE2 : ∀ x ∈ E, x ^ 2 = 1) (e0 : G)
    (hconj : ∀ x ∈ E, x ≠ 1 → ∃ g ∈ P, g * e0 * g⁻¹ = x)
    (e1 e2 e3 : G) (h1 : e1 ∈ E) (h2 : e2 ∈ E) (h3 : e3 ∈ E)
    (i1 : e1 ≠ 1) (i2 : e2 ≠ 1) (i3 : e3 ≠ 1) (i12 : e1 * e2 ≠ 1) (i13 : e1 * e3 ≠ 1)
    (i23 : e2 * e3 ≠ 1) (i123 : e1 * (e2 * e3) ≠ 1) : ¬ GenLE4 C := by
  set Z : Subgroup C := Subgroup.center C with hZdef
  let π : C →* C ⧸ Z := QuotientGroup.mk' Z
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective Z
  have hker : π.ker = Z := QuotientGroup.ker_mk' Z
  have hZc : ∀ z ∈ Z, ∀ g : C, g * z = z * g := fun z hz g => Subgroup.mem_center_iff.1 hz g
  have hZ2 : ∀ z ∈ Z, z ^ 2 = 1 := fun z hz => sq_eq_one_of_card_two Z hZ z hz
  set A : Subgroup C := ((E.subgroupOf P).comap e.toMonoidHom).comap π with hAdef
  have hA := preimage_elementary_model π hπ Z hker hZc hZ2 P e E hEP hE2 e0 hconj e1 e2 e3 h1 h2 h3
    i1 i2 i3 i12 i13 i23 i123
  have hcardE' : Nat.card ((E.subgroupOf P).comap e.toMonoidHom) = 16 := by
    rw [card_comap_of_surjective e.toMonoidHom e.surjective (E.subgroupOf P)]
    have h1 : Nat.card (e.toMonoidHom.ker) = 1 := by
      rw [(MonoidHom.ker_eq_bot_iff _).2 e.injective]
      simp
    rw [h1, mul_one, ← hEcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEP).toEquiv
  have hcardA : Nat.card A = 32 := by
    rw [hAdef, card_comap_of_surjective π hπ, hcardE', hker, hZ]
  exact not_genLE4_of_elementary A hA hcardA

theorem not_genLE4_of_double_cover {K : Type} [Group K] [Finite K] (hperf : commutator K = ⊤)
    (hZ2 : IsPGroup 2 (Subgroup.center K)) (hZ : Subgroup.center K ≠ ⊥)
    (hJ : Subgroup.center (K ⧸ Subgroup.center K) = ⊥)
    (H : ∀ (C : Type) [Group C] [Finite C], Nat.card (Subgroup.center C) = 2 →
      Nonempty (C ⧸ Subgroup.center C ≃* K ⧸ Subgroup.center K) → ¬ GenLE4 C) :
    ¬ GenLE4 K := by
  intro hK
  obtain ⟨C, _, _, φ, hφ, hker, -, hcard, ⟨eC⟩⟩ := exists_double_cover hperf hZ2 hZ hJ
  exact H C hcard ⟨eC⟩ (sectional_le_of_surjective φ hφ hker 4 hK)

end CFSG.GH74.KGroups
