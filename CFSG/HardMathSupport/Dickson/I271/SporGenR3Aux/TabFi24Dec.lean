module

public import Certificates.Certificate17353

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native
open CFSG.Sporadic.Fi24.Native
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three.Native
open CFSG.Sporadic.Fi24 (R J JR jR tR cls lvl gs letters)

attribute [local instance] CFSG.Sporadic.Fi24.rAction

set_option linter.unusedSectionVars false

namespace TabFi24

@[expose] def pt0 : Fin 306936 := ⟨0, by norm_num⟩

@[expose] def pt1 : Fin 306936 := ⟨305530, by norm_num⟩

theorem pt0_ne_pt1 : pt0 ≠ pt1 := by decide

noncomputable def s0 : J :=
  (exists_jR_of_mem (cls_mul_cls_mem_JR pt0 pt1)).choose

theorem jR_s0 : jR s0 = cls pt0 * cls pt1 :=
  (exists_jR_of_mem (cls_mul_cls_mem_JR pt0 pt1)).choose_spec

theorem jR_s0_inv : (jR s0)⁻¹ = cls pt1 * cls pt0 := by
  have h0 : (cls pt0)⁻¹ = cls pt0 := inv_eq_of_mul_eq_one_right (cls_mul_self pt0)
  have h1 : (cls pt1)⁻¹ = cls pt1 := inv_eq_of_mul_eq_one_right (cls_mul_self pt1)
  rw [jR_s0, mul_inv_rev, h0, h1]

section Parts

theorem tf24_parts : ThreeAFacts := Certificates.certificate17353

theorem noncomm_01 : cls pt0 * cls pt1 ≠ cls pt1 * cls pt0 := tf24_parts.1

theorem cls_smul_self (k : Fin 306936) : cls k • k = k :=
  (smul_eq_iff_commute_R (cls k) k).2 rfl

noncomputable def pt2 : Fin 306936 := cls pt0 • pt1

theorem pt2_ne_pt1 : pt2 ≠ pt1 := fun h =>
  noncomm_01 ((smul_eq_iff_commute_R (cls pt0) pt1).1 h)

theorem pt2_ne_pt0 : pt2 ≠ pt0 := by
  intro h
  have e : cls pt2 = cls pt0 * cls pt1 * (cls pt0)⁻¹ :=
    CFSG.Sporadic.Fi24.cls_smul_R (cls pt0) pt1
  have h0 : (cls pt0)⁻¹ = cls pt0 := inv_eq_of_mul_eq_one_right (cls_mul_self pt0)
  rw [h, h0] at e
  have h1 : cls pt1 * cls pt0 = 1 := by
    calc cls pt1 * cls pt0 = (cls pt0)⁻¹ * (cls pt0 * cls pt1 * cls pt0) := by group
      _ = (cls pt0)⁻¹ * cls pt0 := by rw [← e]
      _ = 1 := inv_mul_cancel _
  have h2 : cls pt1 = (cls pt0)⁻¹ := eq_inv_of_mul_eq_one_left h1
  rw [h0] at h2
  exact noncomm_01 (by rw [h2])

def InvS (k : Fin 306936) : Prop := cls k * jR s0 * cls k = (jR s0)⁻¹

theorem scan_sound {k : Fin 306936} (hk : InvS k) : k = pt0 ∨ k = pt1 ∨ k = pt2 := by
  unfold InvS at hk
  rw [jR_s0] at hk
  exact tf24_parts.2.1 k hk

theorem s0_smul_pt0 : s0 • pt0 = pt1 := by
  rw [← CFSG.Sporadic.Fi24.jR_smul, jR_s0]
  exact cls_mul_cls_smul noncomm_01

theorem s0_smul_pt1 : s0 • pt1 = pt2 := by
  rw [← CFSG.Sporadic.Fi24.jR_smul, jR_s0, mul_smul, cls_smul_self]
  rfl

theorem invS_pt0 : InvS pt0 := by
  unfold InvS
  rw [jR_s0_inv, jR_s0]
  calc cls pt0 * (cls pt0 * cls pt1) * cls pt0 = (cls pt0 * cls pt0) * cls pt1 * cls pt0 := by
        group
    _ = cls pt1 * cls pt0 := by rw [cls_mul_self, one_mul]

noncomputable abbrev cent0 : Subgroup J := Subgroup.centralizer ({s0} : Set J)

theorem mem_cent0 {g : J} : g ∈ cent0 ↔ s0 * g = g * s0 := by
  simp [Subgroup.mem_centralizer_iff]

theorem s0_mem_cent0 : s0 ∈ cent0 := mem_cent0.2 rfl

theorem conj_inverts_of_comm {G : Type*} [Group G] {a s k : G} (hs : a * s = s * a)
    (hk : k * s * k = s⁻¹) : (a * k * a⁻¹) * s * (a * k * a⁻¹) = s⁻¹ := by
  have h1 : a⁻¹ * s * a = s := by
    rw [mul_assoc, ← hs, ← mul_assoc, inv_mul_cancel, one_mul]
  have h2 : a * s⁻¹ * a⁻¹ = s⁻¹ := by
    have h : a * s⁻¹ = s⁻¹ * a := (Commute.inv_right (show Commute a s from hs)).eq
    rw [h, mul_assoc, mul_inv_cancel, mul_one]
  calc a * k * a⁻¹ * s * (a * k * a⁻¹) = a * k * (a⁻¹ * s * a) * k * a⁻¹ := by group
    _ = a * (k * s * k) * a⁻¹ := by rw [h1]; group
    _ = a * s⁻¹ * a⁻¹ := by rw [hk]
    _ = s⁻¹ := h2

theorem invS_smul {g : J} (hg : g ∈ cent0) {k : Fin 306936} (hk : InvS k) : InvS (g • k) := by
  unfold InvS at hk ⊢
  have hab : jR g * jR s0 = jR s0 * jR g := by
    rw [← map_mul, ← map_mul, (mem_cent0.1 hg).symm]
  have key := conj_inverts_of_comm (G := R) hab hk
  rw [CFSG.Sporadic.Fi24.cls_smul]
  exact key

theorem invS_pt1 : InvS pt1 := by
  rw [← s0_smul_pt0]
  exact invS_smul s0_mem_cent0 invS_pt0

theorem invS_pt2 : InvS pt2 := by
  rw [← s0_smul_pt1]
  exact invS_smul s0_mem_cent0 invS_pt1

theorem invS_iff {k : Fin 306936} : InvS k ↔ k = pt0 ∨ k = pt1 ∨ k = pt2 :=
  ⟨scan_sound, by
    rintro (rfl | rfl | rfl)
    exacts [invS_pt0, invS_pt1, invS_pt2]⟩

theorem cent0_smul_line {g : J} (hg : g ∈ cent0) {k : Fin 306936}
    (hk : k = pt0 ∨ k = pt1 ∨ k = pt2) : g • k = pt0 ∨ g • k = pt1 ∨ g • k = pt2 :=
  invS_iff.1 (invS_smul hg (invS_iff.2 hk))

theorem mem_lvl_two_of_fix {g : J} (h0 : g • pt0 = pt0) (h1 : g • pt1 = pt1) : g ∈ lvl 2 := by
  refine mem_lvl_of_fix (by norm_num) fun t ht => ?_
  have e0 : idx 306936 g 0 = 0 := by
    rw [idx_of_lt g (by norm_num : 0 < 306936)]
    exact congrArg Fin.val h0
  have e1 : idx 306936 g 305530 = 305530 := by
    rw [idx_of_lt g (by norm_num : 305530 < 306936)]
    exact congrArg Fin.val h1
  interval_cases t
  · rw [CFSG.Sporadic.Fi24.chainBase_zero]
    exact e0
  · rw [CFSG.Sporadic.Fi24.chainBase_one]
    exact e1

theorem fix_of_mem_lvl_two {g : J} (hg : g ∈ lvl 2) : g • pt0 = pt0 ∧ g • pt1 = pt1 := by
  have hg1 : g ∈ lvl 1 := CFSG.Perm.levelGroup_anti _ (by norm_num : 1 ≤ 2) hg
  have e0 : idx 306936 g 0 = 0 := (CFSG.Sporadic.Fi24.lvl_one_iff g).2 hg1
  have e1 := (CFSG.Sporadic.Fi24.chain_facts'.2.1 1
    (by rw [CFSG.Sporadic.Fi24.chainBase_size]; norm_num) g hg1).2 hg
  rw [CFSG.Sporadic.Fi24.chainBase_one] at e1
  constructor
  · apply Fin.ext
    have := idx_of_lt g (show 0 < 306936 by norm_num)
    rw [e0] at this
    exact this.symm
  · apply Fin.ext
    have := idx_of_lt g (show 305530 < 306936 by norm_num)
    rw [e1] at this
    exact this.symm

theorem lvl_two_le_cent0 : lvl 2 ≤ cent0 := by
  intro g hg
  obtain ⟨h0, h1⟩ := fix_of_mem_lvl_two hg
  have c0 := (smul_eq_iff_commute g pt0).1 h0
  have c1 := (smul_eq_iff_commute g pt1).1 h1
  rw [mem_cent0]
  apply CFSG.Sporadic.Fi24.jR_injective
  rw [map_mul, map_mul, jR_s0]
  calc cls pt0 * cls pt1 * jR g = cls pt0 * (cls pt1 * jR g) := by rw [mul_assoc]
    _ = cls pt0 * (jR g * cls pt1) := by rw [c1]
    _ = (cls pt0 * jR g) * cls pt1 := by rw [mul_assoc]
    _ = (jR g * cls pt0) * cls pt1 := by rw [c0]
    _ = jR g * (cls pt0 * cls pt1) := by rw [mul_assoc]

theorem mem_lvl_two_of_cent0_fix {g : J} (hg : g ∈ cent0) (h0 : g • pt0 = pt0) : g ∈ lvl 2 := by
  refine mem_lvl_two_of_fix h0 ?_
  rw [← s0_smul_pt0, smul_smul, ← mem_cent0.1 hg, ← smul_smul, h0]

theorem stab_cent0 : MulAction.stabilizer cent0 pt0 = (lvl 2).subgroupOf cent0 := by
  ext ⟨g, hg⟩
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    exact mem_lvl_two_of_cent0_fix hg h
  · intro h
    exact (fix_of_mem_lvl_two h).1

theorem orbit_cent0 : MulAction.orbit cent0 pt0 = {pt0, pt1, pt2} := by
  ext p
  simp only [MulAction.mem_orbit_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨g, hg⟩, rfl⟩
    exact cent0_smul_line hg (Or.inl rfl)
  · rintro (rfl | rfl | rfl)
    · exact ⟨1, one_smul _ _⟩
    · exact ⟨⟨s0, s0_mem_cent0⟩, s0_smul_pt0⟩
    · exact ⟨⟨s0 * s0, mul_mem s0_mem_cent0 s0_mem_cent0⟩, by
        show (s0 * s0) • pt0 = pt2
        rw [mul_smul, s0_smul_pt0, s0_smul_pt1]⟩

theorem card_orbit_cent0 : Nat.card (MulAction.orbit cent0 pt0) = 3 := by
  rw [Nat.card_coe_set_eq, orbit_cent0]
  exact Set.ncard_eq_three.2 ⟨pt0, pt1, pt2, pt0_ne_pt1, pt2_ne_pt0.symm, pt2_ne_pt1.symm, rfl⟩

theorem card_lvl_two : Nat.card (lvl 2) = 14856539443200 := by
  rw [CFSG.Sporadic.Fi24.chain_facts'.2.2 2
    (by rw [CFSG.Sporadic.Fi24.chainBase_size]; norm_num), CFSG.Sporadic.Fi24.chainBase_size]
  rw [show Finset.Ico 2 6 = {2, 3, 4, 5} by decide]
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_singleton,
    CFSG.Sporadic.Fi24.tree_size_of (l := 2) rfl, CFSG.Sporadic.Fi24.tree_size_of (l := 3) rfl,
    CFSG.Sporadic.Fi24.tree_size_of (l := 4) rfl, CFSG.Sporadic.Fi24.tree_size_of (l := 5) rfl]
  norm_num

theorem card_stab_cent0 : Nat.card (MulAction.stabilizer cent0 pt0) = 14856539443200 := by
  rw [stab_cent0]
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe lvl_two_le_cent0).toEquiv).trans
    card_lvl_two

theorem card_cent0 : Nat.card cent0 = 3 * 14856539443200 := by
  have hos : Nat.card (MulAction.orbit cent0 pt0) * Nat.card (MulAction.stabilizer cent0 pt0) =
      Nat.card cent0 := by
    rw [← Nat.card_prod]
    exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup cent0 pt0)
  rw [← hos, card_orbit_cent0, card_stab_cent0]

theorem isConj_rep0_s0 : IsConj (wordElt [18]) s0 := by
  obtain ⟨g, hg⟩ := tf24_parts.2.2.1
  rw [isConj_iff]
  exact ⟨g, CFSG.Sporadic.Fi24.jR_injective (by rw [hg, jR_s0]; rfl)⟩

end Parts

end TabFi24

end CFSG.HardMathSupport.Dickson.I271
