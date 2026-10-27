module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2Basic

public section

namespace CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2

open CFSG.Open
open scoped Pointwise

variable {G : Type*} [Group G] [Finite G] {L : Subgroup G}

omit [Finite G] in
theorem four_dvd_card_of_hasDihedralSylowTwo (hL : HasDihedralSylowTwo L) : 4 ∣ Nat.card L := by
  obtain ⟨S, n, hn, ⟨e⟩⟩ := hL
  have hS : Nat.card (S : Subgroup L) = 2 ^ n := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    rw [← pow_succ']
    congr 1
    omega
  have h4 : 4 ∣ Nat.card (S : Subgroup L) := by
    rw [hS, show 4 = 2 ^ 2 by norm_num]
    exact Nat.pow_dvd_pow 2 hn
  exact h4.trans (S : Subgroup L).card_subgroup_dvd_card

theorem exists_ne_comm_of_simple_dihedral [IsSimpleGroup L] (hL : HasDihedralSylowTwo L) :
    ∃ x y : L, x * y ≠ y * x := by
  by_contra hcomm
  simp only [not_exists, ne_eq, not_not] at hcomm
  have h4 := four_dvd_card_of_hasDihedralSylowTwo hL
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := L) 2 (dvd_trans (by norm_num) h4)
  have hn : (Subgroup.zpowers x).Normal := by
    constructor
    intro y hy g
    rw [hcomm g y]
    simpa using hy
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.zpowers x) with h | h
  · have : x = 1 := by
      have := Subgroup.mem_zpowers x
      rw [h] at this
      exact this
    rw [this, orderOf_one] at hx
    omega
  · have hcard : Nat.card (Subgroup.zpowers x) = Nat.card L := by
      rw [h, Subgroup.card_top]
    rw [Nat.card_zpowers, hx] at hcard
    have := Nat.le_of_dvd (by omega) h4
    omega

theorem eq_one_of_mem_center_of_simple_dihedral [IsSimpleGroup L] (hL : HasDihedralSylowTwo L)
    {x : G} (hx : x ∈ L) (hc : ∀ y ∈ L, x * y = y * x) : x = 1 := by
  have hZ : Subgroup.center L = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center L) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := exists_ne_comm_of_simple_dihedral hL
      apply hab
      have ha : a ∈ Subgroup.center L := h ▸ Subgroup.mem_top a
      exact (Subgroup.mem_center_iff.mp ha b).symm
  have hxZ : (⟨x, hx⟩ : L) ∈ Subgroup.center L := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact (hc y y.2).symm
  rw [hZ] at hxZ
  exact congrArg Subtype.val (Subgroup.mem_bot.mp hxZ)

theorem inner_commuting_pair [IsSimpleGroup L] (hL : HasDihedralSylowTwo L) {n : G}
    (hn2 : n ^ 2 = 1) (hin : n ∈ L ⊔ Subgroup.centralizer (L : Set G)) :
    ∃ u w : G, u ∈ L ⊓ Subgroup.centralizer ({n} : Set G) ∧
      w ∈ L ⊓ Subgroup.centralizer ({n} : Set G) ∧ u ^ 2 = 1 ∧ w ^ 2 = 1 ∧ u ≠ 1 ∧ w ≠ 1 ∧
      u ≠ w ∧ u * w = w * u := by
  have hCL : Subgroup.centralizer (L : Set G) ≤ Subgroup.normalizer (L : Set G) :=
    Subgroup.centralizer_le_normalizer _
  have hmul : n ∈ (L : Set G) * (Subgroup.centralizer (L : Set G) : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left L _ hCL]
    exact hin
  obtain ⟨l, hl, c, hc, rfl⟩ := Set.mem_mul.mp hmul
  have hcl : ∀ y ∈ L, c * y = y * c := fun y hy =>
    ((Subgroup.mem_centralizer_iff.mp hc) y hy).symm
  have hl2 : l ^ 2 = 1 := by
    have h1 : l ^ 2 * c ^ 2 = 1 := by
      rw [← hn2, pow_two, pow_two, pow_two]
      calc l * l * (c * c) = l * (l * c) * c := by group
        _ = l * (c * l) * c := by rw [hcl l hl]
        _ = l * c * (l * c) := by group
    have h2 : l ^ 2 = (c ^ 2)⁻¹ := eq_inv_of_mul_eq_one_left h1
    apply eq_one_of_mem_center_of_simple_dihedral hL (L.pow_mem hl 2)
    intro y hy
    rw [h2]
    have : c ^ 2 * y = y * c ^ 2 := by
      rw [pow_two]
      calc c * c * y = c * (c * y) := by group
        _ = c * (y * c) := by rw [hcl y hy]
        _ = (c * y) * c := by group
        _ = (y * c) * c := by rw [hcl y hy]
        _ = y * (c * c) := by group
    calc (c ^ 2)⁻¹ * y = (c ^ 2)⁻¹ * (y * c ^ 2) * (c ^ 2)⁻¹ := by group
      _ = (c ^ 2)⁻¹ * (c ^ 2 * y) * (c ^ 2)⁻¹ := by rw [this]
      _ = y * (c ^ 2)⁻¹ := by group
  obtain ⟨S, m, hm, ⟨e⟩⟩ := hL
  have hN : Even (2 ^ (m - 1)) := (Nat.even_pow' (by omega)).mpr even_two
  obtain ⟨u, w, hu, hw, hu1, hw1, huw, huw', hul, hwl⟩ :=
    exists_commuting_involutions_of_dihedral hN (by positivity) S e
      (l := (⟨l, hl⟩ : L)) (Subtype.ext hl2)
  have hcomm : ∀ v : L, v * ⟨l, hl⟩ = ⟨l, hl⟩ * v → (v : G) * (l * c) = l * c * v := by
    intro v hv
    have hv' : (v : G) * l = l * v := congrArg Subtype.val hv
    calc (v : G) * (l * c) = v * l * c := by group
      _ = l * v * c := by rw [hv']
      _ = l * (v * c) := by group
      _ = l * (c * v) := by rw [hcl v v.2]
      _ = l * c * v := by group
  refine ⟨u, w, ⟨u.2, Subgroup.mem_centralizer_singleton_iff.mpr (hcomm u hul)⟩,
    ⟨w.2, Subgroup.mem_centralizer_singleton_iff.mpr (hcomm w hwl)⟩,
    congrArg Subtype.val hu, congrArg Subtype.val hw, ?_, ?_, ?_, congrArg Subtype.val huw'⟩
  · exact fun h => hu1 (Subtype.ext h)
  · exact fun h => hw1 (Subtype.ext h)
  · exact fun h => huw (Subtype.ext h)

end CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2
