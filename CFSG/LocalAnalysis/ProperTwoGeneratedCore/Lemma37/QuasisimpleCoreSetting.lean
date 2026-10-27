module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherAssembly
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.SubgroupNormalizers

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly

structure Setting (J : Type) [Group J] [Finite J] (Q : Sylow 2 J) (B : Subgroup J) : Prop where
  perfect : Group.IsPerfect J
  simple : IsSimpleGroup (J ⧸ Subgroup.center J)
  center_card : Nat.card (Subgroup.center J) = 2
  rank : 2 ≤ twoRank J
  sylow_le : (Q : Subgroup J) ≤ B
  proper : B ≠ ⊤
  core_le : properTwoGenCoreGamma (Q : Subgroup J) 2 ≤ B
  quaternion : ∃ j : J, j ∉ B ∧ ∃ P : Subgroup J, IsPGroup 2 P ∧ ¬ IsCyclic P ∧
    ∀ p ∈ P, p ∈ B ∧ j⁻¹ * p * j ∈ B

noncomputable def centralElt (J : Type) [Group J] : J :=
  @Classical.epsilon J ⟨1⟩ fun e => e ∈ Subgroup.center J ∧ e ≠ 1

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J}

omit [Finite J] in
theorem commute_mk_iff (a b : J) :
    Commute (a : J ⧸ Subgroup.center J) (b : J ⧸ Subgroup.center J) ↔
      a * b * a⁻¹ * b⁻¹ ∈ Subgroup.center J := by
  rw [← commutatorElement_eq_one_iff_commute, commutatorElement_def,
    ← QuotientGroup.eq_one_iff (N := Subgroup.center J)]
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]

namespace Setting

theorem exists_mem_center_ne_one (h : Setting J Q B) :
    ∃ e : J, e ∈ Subgroup.center J ∧ e ≠ 1 := by
  obtain ⟨y, hy, -⟩ := (Nat.card_eq_two_iff' (1 : Subgroup.center J)).mp h.center_card
  exact ⟨y, y.2, fun h1 => hy (Subtype.ext h1)⟩

theorem centralElt_spec (h : Setting J Q B) :
    centralElt J ∈ Subgroup.center J ∧ centralElt J ≠ 1 :=
  Classical.epsilon_spec h.exists_mem_center_ne_one

theorem centralElt_mem_center (h : Setting J Q B) : centralElt J ∈ Subgroup.center J :=
  h.centralElt_spec.1

theorem centralElt_ne_one (h : Setting J Q B) : centralElt J ≠ 1 :=
  h.centralElt_spec.2

theorem mem_center_iff (h : Setting J Q B) {x : J} :
    x ∈ Subgroup.center J ↔ x = 1 ∨ x = centralElt J := by
  constructor
  · intro hx
    by_cases hx1 : x = 1
    · exact Or.inl hx1
    right
    obtain ⟨y, -, hyu⟩ := (Nat.card_eq_two_iff' (1 : Subgroup.center J)).mp h.center_card
    have h1 := hyu ⟨x, hx⟩ fun h' => hx1 (congrArg Subtype.val h')
    have h2 := hyu ⟨centralElt J, h.centralElt_mem_center⟩ fun h' =>
      h.centralElt_ne_one (congrArg Subtype.val h')
    exact congrArg Subtype.val (h1.trans h2.symm)
  · rintro (rfl | rfl)
    · exact (Subgroup.center J).one_mem
    · exact h.centralElt_mem_center

theorem commute_centralElt (h : Setting J Q B) (x : J) : Commute x (centralElt J) :=
  Subgroup.mem_center_iff.mp h.centralElt_mem_center x

theorem centralElt_mul_self (h : Setting J Q B) : centralElt J * centralElt J = 1 := by
  rcases h.mem_center_iff.mp ((Subgroup.center J).mul_mem h.centralElt_mem_center
    h.centralElt_mem_center) with h1 | h1
  · exact h1
  · exact absurd (mul_eq_left.mp h1) h.centralElt_ne_one

theorem orderOf_centralElt (h : Setting J Q B) : orderOf (centralElt J) = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact h.centralElt_mul_self) h.centralElt_ne_one

theorem not_mem_center_iff (h : Setting J Q B) {t : J} (ht : orderOf t = 2) :
    t ∉ Subgroup.center J ↔ t ≠ centralElt J := by
  have ht1 : t ≠ 1 := fun h1 => by rw [h1, orderOf_one] at ht; exact absurd ht (by decide)
  rw [h.mem_center_iff]
  tauto

theorem center_isPGroup (h : Setting J Q B) : IsPGroup 2 (Subgroup.center J) :=
  IsPGroup.of_card (n := 1) (by rw [h.center_card, pow_one])

theorem center_le_sylow (h : Setting J Q B) : Subgroup.center J ≤ (Q : Subgroup J) :=
  h.center_isPGroup.le_sylow_of_normal Q

theorem centralElt_mem_sylow (h : Setting J Q B) : centralElt J ∈ (Q : Subgroup J) :=
  h.center_le_sylow h.centralElt_mem_center

theorem center_le (h : Setting J Q B) : Subgroup.center J ≤ B :=
  h.center_le_sylow.trans h.sylow_le

theorem centralElt_mem (h : Setting J Q B) : centralElt J ∈ B :=
  h.center_le h.centralElt_mem_center

theorem mem_center_of_mem_inf_conj (h : Setting J Q B) {g : J} (hg : g ∉ B) {t : J}
    (ht : t ∈ B ⊓ B.conjBy g⁻¹) (ht2 : orderOf t = 2) : t ∈ Subgroup.center J := by
  by_contra htZ
  have he : centralElt J ∈ B ⊓ B.conjBy g⁻¹ := by
    refine ⟨h.centralElt_mem, Subgroup.mem_map.mpr ⟨centralElt J, h.centralElt_mem, ?_⟩⟩
    change g⁻¹ * centralElt J * g⁻¹⁻¹ = centralElt J
    rw [(h.commute_centralElt g⁻¹).eq, mul_assoc, mul_inv_cancel, mul_one]
  have hne : t ≠ centralElt J := fun h' => htZ (h' ▸ h.centralElt_mem_center)
  have h2 := two_le_pRank_of_commuting_involutions ht he ht2 h.orderOf_centralElt hne
    (h.commute_centralElt t)
  have hlt := conjugate_intersection_rank_lt Q B (k := 2) (by decide) h.sylow_le h.core_le g hg
  omega

theorem eq_centralElt_of_mem_inf_conj (h : Setting J Q B) {g : J} (hg : g ∉ B) {t : J}
    (ht : t ∈ B ⊓ B.conjBy g⁻¹) (ht2 : orderOf t = 2) : t = centralElt J := by
  by_contra hne
  exact (h.not_mem_center_iff ht2).mpr hne (h.mem_center_of_mem_inf_conj hg ht ht2)

theorem normalizer_le (h : Setting J Q B) {D : Subgroup J} (hDB : D ≤ B)
    (hD : 2 ≤ CFSG.Open.pRank 2 D) : Subgroup.normalizer (D : Set J) ≤ B :=
  two_generated_core_subgroup_normalizer_le Q B h.sylow_le h.core_le D hDB hD

theorem mem_of_conj_mem (h : Setting J Q B) {t x : J} (htB : t ∈ B) (ht : orderOf t = 2)
    (htZ : t ∉ Subgroup.center J) (hx : x * t * x⁻¹ ∈ B) : x ∈ B := by
  by_contra hxB
  refine htZ (h.mem_center_of_mem_inf_conj hxB ⟨htB, Subgroup.mem_map.mpr ⟨_, hx, ?_⟩⟩ ht)
  change x⁻¹ * (x * t * x⁻¹) * x⁻¹⁻¹ = t
  group

theorem centralizer_le (h : Setting J Q B) {t : J} (htB : t ∈ B) (ht : orderOf t = 2)
    (htZ : t ∉ Subgroup.center J) : Subgroup.centralizer ({t} : Set J) ≤ B := by
  intro x hx
  refine h.mem_of_conj_mem htB ht htZ ?_
  rw [Subgroup.mem_centralizer_singleton_iff.mp hx, mul_inv_cancel_right]
  exact htB

theorem centralizer_le_of_ne (h : Setting J Q B) {t : J} (htB : t ∈ B) (ht : orderOf t = 2)
    (hte : t ≠ centralElt J) : Subgroup.centralizer ({t} : Set J) ≤ B :=
  h.centralizer_le htB ht ((h.not_mem_center_iff ht).mpr hte)

theorem mk_mem_map_iff (h : Setting J Q B) (x : J) :
    (x : J ⧸ Subgroup.center J) ∈ B.map (QuotientGroup.mk' (Subgroup.center J)) ↔ x ∈ B := by
  rw [← QuotientGroup.mk'_apply, ← Subgroup.mem_comap, Subgroup.comap_map_eq_self (by
    rw [QuotientGroup.ker_mk']
    exact h.center_le)]

theorem map_ne_top (h : Setting J Q B) :
    B.map (QuotientGroup.mk' (Subgroup.center J)) ≠ ⊤ := by
  intro htop
  apply h.proper
  rw [eq_top_iff]
  intro x _
  rw [← h.mk_mem_map_iff, htop]
  exact Subgroup.mem_top _

theorem centralizer_mk_le (h : Setting J Q B) {t : J} (htB : t ∈ B) (ht : orderOf t = 2)
    (htZ : t ∉ Subgroup.center J) :
    Subgroup.centralizer ({(t : J ⧸ Subgroup.center J)} : Set (J ⧸ Subgroup.center J)) ≤
      B.map (QuotientGroup.mk' (Subgroup.center J)) := by
  intro y hy
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  rw [h.mk_mem_map_iff]
  refine h.mem_of_conj_mem htB ht htZ ?_
  have hc := (commute_mk_iff x t).mp (Subgroup.mem_centralizer_singleton_iff.mp hy)
  have hxt : x * t * x⁻¹ = (x * t * x⁻¹ * t⁻¹) * t := by group
  rw [hxt]
  exact B.mul_mem (h.center_le hc) htB

end Setting

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
