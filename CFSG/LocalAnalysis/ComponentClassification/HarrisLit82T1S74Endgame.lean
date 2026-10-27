module

public import CFSG.GroupTheory.FourGroupOddOrderIdentity
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourOfCommutingInvolutions

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.S74

open Subgroup

variable {G : Type} [Group G] [Finite G]

@[reducible] def conjAct (T K : Subgroup G) (hTK : T ≤ normalizer (K : Set G)) :
    MulDistribMulAction T K where
  smul t k := ⟨t * k * t⁻¹, (mem_normalizer_iff.mp (hTK t.2) k).mp k.2⟩
  one_smul k := Subtype.ext (by change (1 : G) * k * 1⁻¹ = k; group)
  mul_smul s t k := Subtype.ext (by
    change (s * t : G) * k * (s * t : G)⁻¹ = s * (t * k * (t : G)⁻¹) * (s : G)⁻¹
    group)
  smul_mul t k l := Subtype.ext (by
    change (t : G) * (k * l) * (t : G)⁻¹ = (t * k * (t : G)⁻¹) * (t * l * (t : G)⁻¹)
    group)
  smul_one t := Subtype.ext (by change (t : G) * 1 * (t : G)⁻¹ = 1; group)

omit [Finite G] in
theorem card_fixedPointSubgroup_eq {A : Type*} [Group A] {K : Subgroup G}
    [MulDistribMulAction A K] {P : Set G}
    (h : ∀ k : K, k ∈ fixedPointSubgroup A K ↔ ∀ x ∈ P, x * k * x⁻¹ = k) :
    Nat.card (fixedPointSubgroup A K) = Nat.card ↥(K ⊓ centralizer P) := by
  have heq : fixedPointSubgroup A K = (K ⊓ centralizer P).subgroupOf K := by
    ext k
    rw [h, mem_subgroupOf, mem_inf, mem_centralizer_iff]
    constructor
    · intro hk
      refine ⟨k.2, fun x hx => ?_⟩
      calc x * k = x * k * x⁻¹ * x := by group
        _ = k * x := by rw [hk x hx]
    · rintro ⟨-, hk⟩ x hx
      rw [hk x hx]
      group
  rw [heq]
  exact Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv

theorem card_mul_card_inf_centralizer_sq {K : Subgroup G} (hK : Odd (Nat.card K)) {a b : G}
    (ha : a * a = 1) (hb : b * b = 1) (hab : Commute a b) (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (hne : a ≠ b) (haK : a ∈ normalizer (K : Set G)) (hbK : b ∈ normalizer (K : Set G)) :
    Nat.card K * Nat.card ↥(K ⊓ centralizer ({a, b} : Set G)) ^ 2 =
      Nat.card ↥(K ⊓ centralizer ({a} : Set G)) * Nat.card ↥(K ⊓ centralizer ({b} : Set G)) *
        Nat.card ↥(K ⊓ centralizer ({a * b} : Set G)) := by
  classical
  set V := CFSG.GorensteinWalter.kleinFourOfCommutingInvolutions a b ha hb hab
  have hVK : IsKleinFour V :=
    CFSG.GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions a b ha hb ha1 hb1 hne hab
  have hmemV : ∀ x : G, x ∈ V ↔ x = a * b ∨ x = a ∨ x = b ∨ x = 1 := fun x => Iff.rfl
  have haV : a ∈ V := (hmemV a).2 (Or.inr (Or.inl rfl))
  have hbV : b ∈ V := (hmemV b).2 (Or.inr (Or.inr (Or.inl rfl)))
  have hVN : V ≤ normalizer (K : Set G) := fun x hx => by
    rcases (hmemV x).1 hx with rfl | rfl | rfl | rfl
    · exact mul_mem haK hbK
    · exact haK
    · exact hbK
    · exact one_mem _
  let _ : MulDistribMulAction V K := conjAct V K hVN
  let _ : Fintype V := Fintype.ofFinite V
  have h := (CFSG.GroupTheory.odd_group_four_group_centralizer_order_identity
    (A := V) (X := K) hK).1
  have hV : Nat.card (fixedPointSubgroup V K) = Nat.card ↥(K ⊓ centralizer ({a, b} : Set G)) := by
    refine card_fixedPointSubgroup_eq fun k => ⟨fun hk x hx => ?_, fun hk v => ?_⟩
    · have hxV : x ∈ V := by
        rcases hx with rfl | rfl
        · exact haV
        · exact hbV
      exact congrArg Subtype.val (hk ⟨x, hxV⟩)
    · apply Subtype.ext
      change (v : G) * k * (v : G)⁻¹ = k
      rcases (hmemV v).1 v.2 with hv | hv | hv | hv <;> rw [hv]
      · have h1 := hk a (Set.mem_insert a _)
        have h2 := hk b (Set.mem_insert_of_mem a rfl)
        calc a * b * k * (a * b)⁻¹ = a * (b * k * b⁻¹) * a⁻¹ := by group
          _ = k := by rw [h2, h1]
      · exact hk a (Set.mem_insert a _)
      · exact hk b (Set.mem_insert_of_mem a rfl)
      · group
  have hcyc : ∀ t : V, Nat.card (fixedPointSubgroup (zpowers t) K) =
      Nat.card ↥(K ⊓ centralizer ({(t : G)} : Set G)) := by
    intro t
    refine card_fixedPointSubgroup_eq fun k => ?_
    rw [CFSG.SolvableHall.mem_fixedPointSubgroup_zpowers_iff]
    constructor
    · intro hk x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact congrArg Subtype.val hk
    · intro hk
      exact Subtype.ext (hk t rfl)
  set ta : V := ⟨a, haV⟩
  set tb : V := ⟨b, hbV⟩
  have hta : ta ≠ 1 := fun h => ha1 (congrArg Subtype.val h)
  have htb : tb ≠ 1 := fun h => hb1 (congrArg Subtype.val h)
  have htab : ta ≠ tb := fun h => hne (congrArg Subtype.val h)
  have habne1 : ta * tb ≠ 1 := fun h => hne (by
    have h' := congrArg Subtype.val (mul_eq_one_iff_eq_inv.mp h)
    simpa [ta, tb, inv_eq_of_mul_eq_one_right hb] using h')
  have habnea : ta * tb ≠ ta := fun h => htb (by simpa using h)
  have habneb : ta * tb ≠ tb := fun h => hta (by simpa using h)
  have herase : Finset.univ.erase (1 : V) = {ta * tb, ta, tb} := by
    rw [← IsKleinFour.eq_finset_univ hta htb htab]
    ext x
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hx1, hx | hx | hx | hx⟩
      · exact Or.inl hx
      · exact Or.inr (Or.inl hx)
      · exact Or.inr (Or.inr hx)
      · exact absurd hx hx1
    · rintro (hx | hx | hx) <;> subst hx
      · exact ⟨habne1, Or.inl rfl⟩
      · exact ⟨hta, Or.inr (Or.inl rfl)⟩
      · exact ⟨htb, Or.inr (Or.inr (Or.inl rfl))⟩
  rw [herase, Finset.prod_insert (by simp [habnea, habneb]),
    Finset.prod_insert (by simp [htab]), Finset.prod_singleton, hcyc, hcyc, hcyc, hV] at h
  rw [h]
  simp only [ta, tb, Subgroup.coe_mul]
  ring

end CFSG.ComponentClassification.HarrisLit.T1.S74
