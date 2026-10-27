module

public import CFSG.Holt.Induced
public import CFSG.Holt.H78.Basic

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Holt.General
open scoped Pointwise

variable {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω]

section LongInvSection

theorem mem_longInv_subgroup_iff {K : Subgroup G} {k : K} :
    k ∈ longInv K Ω ↔ (k : G) ∈ longInv G Ω := by
  rw [mem_longInv, mem_longInv, Subgroup.orderOf_coe]
  exact Iff.rfl

theorem mem_longInvAt_subgroup_iff {K : Subgroup G} {k : K} {α : Ω} :
    k ∈ longInvAt K Ω α ↔ (k : G) ∈ longInvAt G Ω α := by
  rw [mem_longInvAt, mem_longInvAt, mem_longInv_subgroup_iff]
  exact Iff.rfl

theorem mem_longInvAt_of_mul_self {Y Δ : Type*} [Group Y] [MulAction Y Δ] {y : Y} {δ : Δ}
    (hy : y * y = 1) (hfix : ∀ ε, y • ε = ε ↔ ε = δ) (hΔ : ∃ ε : Δ, ε ≠ δ) :
    y ∈ longInvAt Y Δ δ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ε, hε⟩ := hΔ
  refine ⟨⟨orderOf_eq_prime (by rw [sq]; exact hy) ?_, δ, (hfix δ).mpr rfl,
    fun ε h => (hfix ε).mp h⟩, (hfix δ).mpr rfl⟩
  rintro rfl
  exact hε ((hfix ε).mp (one_smul Y ε))

theorem exists_mem_fixSet_of_le_stabilizer {P : Subgroup G} (hP : IsPGroup 2 P) {Λ : Set Ω}
    [Finite Λ] (hΛ : Odd (Nat.card Λ)) (hPΛ : P ≤ stabilizer G Λ) :
    ∃ ω ∈ Λ, ω ∈ fixSet Ω P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := card_modEq_card_fixSet_inter_of_le_stabilizer hP hPΛ
  have hodd : Odd (Nat.card ↥(fixSet Ω P ∩ Λ)) := by
    rw [Nat.odd_iff] at hΛ ⊢
    exact Eq.trans h.symm hΛ
  obtain ⟨⟨ω, hωP, hωΛ⟩⟩ := (Nat.card_pos_iff.mp hodd.pos).1
  exact ⟨ω, hωΛ, hωP⟩

theorem mem_of_mem_longInvAt_of_mem_stabilizer {t : G} {α : Ω} (ht : t ∈ longInvAt G Ω α)
    {Λ : Set Ω} [Finite Λ] (hΛ : Odd (Nat.card Λ)) (htΛ : t ∈ stabilizer G Λ) : α ∈ Λ := by
  obtain ⟨ω, hωΛ, hω⟩ := exists_mem_fixSet_of_le_stabilizer
    (isPGroup_zpowers_of_orderOf_eq_two ht.1.1) hΛ (Subgroup.zpowers_le.mpr htΛ)
  rw [fixSet_zpowers] at hω
  rwa [← (smul_eq_iff_of_mem_longInvAt ht ω).mp hω]

theorem inducedHom_mem_longInvAt {X : Subgroup G} {Δ : Set Ω} (hX : X ≤ stabilizer G Δ) {x : X}
    {α : Δ} (hx : (x : G) ∈ longInvAt G Ω α) (hΔ : ∃ δ : Δ, δ ≠ α) :
    inducedHom X Δ hX x ∈ longInvAt (Equiv.Perm Δ) Δ α := by
  refine mem_longInvAt_of_mul_self ?_ (fun δ => ?_) hΔ
  · rw [← map_mul, show x * x = 1 from Subtype.ext (mul_self_eq_one_of_mem_longInv hx.1),
      map_one]
  · rw [Equiv.Perm.smul_def, Subtype.ext_iff, coe_inducedHom_apply,
      smul_eq_iff_of_mem_longInvAt hx, Subtype.ext_iff]

theorem inducedHom_mem_longInv {X : Subgroup G} {Δ : Set Ω} (hX : X ≤ stabilizer G Δ)
    [Finite Δ] (hΔ : Odd (Nat.card Δ)) (h3 : 3 ≤ Nat.card Δ) {x : X}
    (hx : (x : G) ∈ longInv G Ω) : inducedHom X Δ hX x ∈ longInv (Equiv.Perm Δ) Δ := by
  obtain ⟨α, hα⟩ := exists_mem_longInvAt hx
  have hαΔ := mem_of_mem_longInvAt_of_mem_stabilizer hα hΔ (hX x.2)
  have : Nontrivial Δ := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  exact (inducedHom_mem_longInvAt hX (α := ⟨α, hαΔ⟩) hα (exists_ne _)).1

theorem mem_longInv_inducedPerm_of_eq {X : Subgroup G} {Δ : Set Ω} {hX : X ≤ stabilizer G Δ}
    [Finite Δ] (hΔ : Odd (Nat.card Δ)) (h3 : 3 ≤ Nat.card Δ) {x : X}
    (hx : (x : G) ∈ longInv G Ω) {y : inducedPerm X Δ hX}
    (hxy : inducedHom X Δ hX x = (y : Equiv.Perm Δ)) : y ∈ longInv ↥(inducedPerm X Δ hX) Δ := by
  rw [mem_longInv_subgroup_iff, ← hxy]
  exact inducedHom_mem_longInv hX hΔ h3 hx

end LongInvSection

section Lemma22

variable [Finite G]

theorem exists_isPGroup_lift_inducedPerm {p : ℕ} [Fact p.Prime] {X : Subgroup G} {Δ : Set Ω}
    {hX : X ≤ stabilizer G Δ} {R : Subgroup (inducedPerm X Δ hX)} (hR : IsPGroup p R) :
    ∃ R' : Subgroup G, R' ≤ X ∧ IsPGroup p R' ∧
      (∀ r ∈ R', ∃ y ∈ R, ∀ δ : Δ, ((y : Equiv.Perm Δ) δ : Ω) = r • (δ : Ω)) ∧
      (∀ y ∈ R, ∃ r ∈ R', ∀ δ : Δ, ((y : Equiv.Perm Δ) δ : Ω) = r • (δ : Ω)) := by
  obtain ⟨R', hR'X, hR', hR'Q⟩ := exists_inducedPerm_eq_of_isPGroup
    (hR.map (inducedPerm X Δ hX).subtype) (Subgroup.map_subtype_le R)
  refine ⟨R', hR'X, hR', fun r hr => ?_, fun y hy => ?_⟩
  · have hmem : inducedHom R' Δ (hR'X.trans hX) ⟨r, hr⟩ ∈
        R.map (inducedPerm X Δ hX).subtype := by
      rw [← hR'Q]
      exact ⟨⟨r, hr⟩, rfl⟩
    obtain ⟨y, hy, hyr⟩ := Subgroup.mem_map.mp hmem
    refine ⟨y, hy, fun δ => ?_⟩
    rw [Subgroup.coe_subtype] at hyr
    rw [hyr]
    rfl
  · have hmem : (y : Equiv.Perm Δ) ∈ inducedPerm R' Δ (hR'X.trans hX) := by
      rw [hR'Q]
      exact Subgroup.mem_map_of_mem _ hy
    exact mem_inducedPerm.mp hmem

variable [Finite Ω]

theorem isStarGroup_inducedPerm_fixSet (hG : IsStarGroup G Ω) {S X : Subgroup G}
    (hS : IsPGroup 2 S) (h3 : 3 ≤ Nat.card (fixSet Ω S))
    (hCX : Subgroup.centralizer (S : Set G) ≤ X) (hXN : X ≤ Subgroup.normalizer (S : Set G)) :
    IsStarGroup ↥(inducedPerm X (fixSet Ω S) (hXN.trans (normalizer_le_stabilizer_fixSet S)))
      ↥(fixSet Ω S) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨hG.odd_card_fixSet hS, h3, fun β R hR hRβ hR3 => ?_⟩
  obtain ⟨R', hR'X, hR', hlift, hlift'⟩ := exists_isPGroup_lift_inducedPerm hR
  have hT : IsPGroup 2 ↥(S ⊔ R') := hS.to_sup_of_normal_left' hR' (hR'X.trans hXN)
  have hR'β : R' ≤ stabilizer G (β : Ω) := fun r hr => by
    obtain ⟨y, hy, hyr⟩ := hlift r hr
    rw [mem_stabilizer_iff, ← hyr β]
    exact congrArg Subtype.val (mem_stabilizer_iff.mp (hRβ hy))
  have hTβ : S ⊔ R' ≤ stabilizer G (β : Ω) :=
    sup_le (mem_fixSet_iff_le_stabilizer.mp β.2) hR'β
  have h3T : 3 ≤ Nat.card (fixSet Ω (S ⊔ R')) := by
    refine hR3.trans (Nat.card_le_card_of_injective (fun δ => ⟨((δ : fixSet Ω S) : Ω), ?_⟩) ?_)
    · rw [fixSet_sup]
      refine ⟨(δ : fixSet Ω S).2, fun r hr => ?_⟩
      obtain ⟨y, hy, hyr⟩ := hlift r hr
      rw [← hyr]
      exact congrArg Subtype.val (δ.2 y hy)
    · intro δ δ' h
      apply Subtype.ext
      apply Subtype.ext
      simpa using congrArg Subtype.val h
  obtain ⟨t, htβ, htT⟩ := hG.star β (S ⊔ R') hT hTβ h3T
  have htX : t ∈ X := hCX (Subgroup.centralizer_le (le_sup_left : S ≤ S ⊔ R') htT)
  have : Nontrivial (fixSet Ω S) := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  refine ⟨⟨inducedHom X (fixSet Ω S) _ ⟨t, htX⟩, ⟨t, htX⟩, rfl⟩,
    mem_longInvAt_subgroup_iff.mpr (inducedHom_mem_longInvAt _ (x := ⟨t, htX⟩) htβ
      (exists_ne β)), Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
  obtain ⟨r, hr, hry⟩ := hlift' y hy
  refine Subtype.ext (Equiv.ext fun δ => Subtype.ext ?_)
  simp only [Subgroup.coe_mul, Equiv.Perm.coe_mul, Function.comp_apply, hry,
    coe_inducedHom_apply]
  rw [← mul_smul, ← mul_smul,
    Subgroup.mem_centralizer_iff.mp htT r (Subgroup.mem_sup_right hr)]

theorem isStarGroup_centralizerImage (hG : IsStarGroup G Ω) {S : Subgroup G}
    (hS : IsPGroup 2 S) (h3 : 3 ≤ Nat.card (fixSet Ω S)) :
    IsStarGroup ↥(centralizerImage Ω S) ↥(fixSet Ω S) :=
  isStarGroup_inducedPerm_fixSet hG hS h3 le_rfl (Subgroup.centralizer_le_normalizer _)

end Lemma22

section Order

variable [Finite G]

theorem card_inducedPerm_fixSet_lt {p : ℕ} [Fact p.Prime] {S X : Subgroup G} (hS : IsPGroup p S)
    (hS1 : S ≠ ⊥) (hCX : Subgroup.centralizer (S : Set G) ≤ X)
    (hXN : X ≤ Subgroup.normalizer (S : Set G)) :
    Nat.card (inducedPerm X (fixSet Ω S) (hXN.trans (normalizer_le_stabilizer_fixSet S))) <
      Nat.card X := by
  have : Nontrivial S := (Subgroup.nontrivial_iff_ne_bot S).mpr hS1
  have := hS.center_nontrivial
  obtain ⟨z, hz⟩ := exists_ne (1 : Subgroup.center S)
  have hzC : ((z : S) : G) ∈ Subgroup.centralizer (S : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp z.2 ⟨s, hs⟩)
  refine card_inducedPerm_lt (hCX hzC) (fun h1 => hz ?_) (le_fixingSubgroup_fixSet S (z : S).2)
  exact Subtype.ext (Subtype.ext h1)

theorem card_inducedPerm_fixSet_lt_card {p : ℕ} [Fact p.Prime] {S X : Subgroup G}
    (hS : IsPGroup p S) (hS1 : S ≠ ⊥) (hCX : Subgroup.centralizer (S : Set G) ≤ X)
    (hXN : X ≤ Subgroup.normalizer (S : Set G)) :
    Nat.card (inducedPerm X (fixSet Ω S) (hXN.trans (normalizer_le_stabilizer_fixSet S))) <
      Nat.card G :=
  (card_inducedPerm_fixSet_lt hS hS1 hCX hXN).trans_le (Subgroup.card_le_card_group X)

end Order

section Hull

theorem fixSet_map_subtype {K : Subgroup G} (S : Subgroup K) :
    fixSet Ω (S.map K.subtype) = fixSet Ω S := by
  ext ω
  exact ⟨fun h s hs => h _ ⟨s, hs, rfl⟩, fun h _ ⟨s, hs, hsg⟩ => hsg ▸ h s hs⟩

theorem isStarGroup_of_jHull_le (hG : IsStarGroup G Ω) {K : Subgroup G} (hK : jHull G Ω ≤ K) :
    IsStarGroup ↥K Ω := by
  refine ⟨hG.odd_card, hG.three_le_card, fun α S hS hSα hS3 => ?_⟩
  obtain ⟨t, ht, htS⟩ := hG.star α (S.map K.subtype) (hS.map _)
    (by rintro _ ⟨s, hs, rfl⟩; exact hSα hs) (by rwa [fixSet_map_subtype])
  refine ⟨⟨t, hK (mem_jHull_of_mem_longInv ht.1)⟩, mem_longInvAt_subgroup_iff.mpr ht,
    Subgroup.mem_centralizer_iff.mpr fun s hs => ?_⟩
  exact Subtype.ext (Subgroup.mem_centralizer_iff.mp htS _ ⟨s, hs, rfl⟩)

theorem isStarGroup_jHull (hG : IsStarGroup G Ω) : IsStarGroup ↥(jHull G Ω) Ω :=
  isStarGroup_of_jHull_le hG le_rfl

variable [Finite G]

end Hull

end CFSG.Holt.H78
