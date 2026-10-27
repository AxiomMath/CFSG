module

public import CFSG.RankThree.PartTwo.Census.Exceptional.TwistedE6Local
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB

open CFSG.Open CFSG.RankThree.PartTwo.Census.Exceptional

namespace I1015

section Group

variable {G : Type} [Group G] [Finite G] {ι : Type*} [Fintype ι] [DecidableEq ι]

@[expose] def optFam (e : ι → G) (e₀ : G) : Option ι → G := fun o => o.elim e₀ e

theorem exists_Y_of_witness (e : ι → G) (e₀ : G) (y : ι → G) (hee : ∀ i j, Commute (e i) (e j))
    (he₀ : ∀ i, Commute (e i) e₀) (he3 : ∀ i, e i ^ 3 = 1) (he₀3 : e₀ ^ 3 = 1) (he₀1 : e₀ ≠ 1)
    (hy : ∀ i j, i ≠ j → Commute (y i) (e j)) (hy₀ : ∀ i, Commute (y i) e₀)
    (hyi : ∀ i, ¬ Commute (y i) (e i)) :
    ∃ Y : Subgroup G, Y = Subgroup.closure (Set.range (optFam e e₀)) ∧ IsElemAbelian 3 Y ∧
      3 ^ (Fintype.card ι + 1) ≤ Nat.card Y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let f : Option ι → G := optFam e e₀
  have hff : ∀ a b, Commute (f a) (f b) := by
    rintro (_ | a) (_ | b)
    · exact Commute.refl _
    · exact (he₀ b).symm
    · exact he₀ a
    · exact hee a b
  have hf3 : ∀ a, f a ^ 3 = 1 := by
    rintro (_ | a)
    · exact he₀3
    · exact he3 a
  have hpair : (Set.range f).Pairwise Commute := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ -
    exact hff i j
  set Y := Subgroup.closure (Set.range f) with hYdef
  have hYc : IsMulCommutative Y := Subgroup.isMulCommutative_closure hpair
  have hcomm : ∀ a b : Y, a * b = b * a := fun a b => mul_comm' a b
  let : CommGroup Y := { (inferInstance : Group Y) with mul_comm := hcomm }
  let f' : Option ι → Y := fun i => ⟨f i, Subgroup.subset_closure ⟨i, rfl⟩⟩
  have hgen : Subgroup.closure (Set.range f') = ⊤ := by
    rw [eq_top_iff, ← Subgroup.closure_closure_coe_preimage (k := Set.range f)]
    refine Subgroup.closure_mono ?_
    rintro x ⟨i, hi⟩
    exact ⟨i, Subtype.ext hi⟩
  let S : Option ι → Subgroup Y := fun o => o.elim
    ((Subgroup.closure (Set.range e)).subgroupOf Y)
    (fun i => (Subgroup.centralizer ({y i} : Set G)).subgroupOf Y)
  have hS : ∀ i j, i ≠ j → f' j ∈ S i := by
    rintro (_ | i) (_ | j) hij
    · exact absurd rfl hij
    · exact Subgroup.mem_subgroupOf.2 (Subgroup.subset_closure ⟨j, rfl⟩)
    · exact Subgroup.mem_subgroupOf.2
        (Subgroup.mem_centralizer_singleton_iff.2 (hy₀ i).eq.symm)
    · exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_centralizer_singleton_iff.2
        (hy i j fun h => hij (h ▸ rfl)).eq.symm)
  have hSy : ∀ i, f' i ∉ S i := by
    rintro (_ | i) h
    · exact he₀1 (eq_one_of_mem_closure e e₀ y hee he3 hy hy₀ hyi (Subgroup.mem_subgroupOf.1 h))
    · exact hyi i (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_subgroupOf.1 h)).symm
  have hSy3 : ∀ i, f' i ^ 3 ∈ S i := fun i => by
    have : f' i ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hf3 i)
    rw [this]
    exact (S i).one_mem
  have hbound := CFSG.RankThree.Theta.three_pow_card_le_card_ker_pow f' hgen S hS hSy hSy3
  refine ⟨Y, rfl, IsElemAbelian.closure_of_commute (fun a ha b hb => ?_) (fun a ha => ?_), ?_⟩
  · obtain ⟨i, rfl⟩ := ha
    obtain ⟨j, rfl⟩ := hb
    exact (hff i j).eq
  · obtain ⟨i, rfl⟩ := ha
    exact hf3 i
  · rw [← Fintype.card_option]
    exact hbound.trans (Subgroup.card_le_card_group _)

theorem mem_Y_iff (e : ι → G) (e₀ : G) (hee : ∀ i j, Commute (e i) (e j))
    (he₀ : ∀ i, Commute (e i) e₀) {z : G}
    (hz : z ∈ Subgroup.closure (Set.range (optFam e e₀))) :
    ∃ a ∈ Subgroup.closure (Set.range e), ∃ m : ℤ, z = a * e₀ ^ m := by
  induction hz using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨o, rfl⟩ := hx
    rcases o with _ | i
    · exact ⟨1, Subgroup.one_mem _, 1, by simp [optFam]⟩
    · exact ⟨e i, Subgroup.subset_closure ⟨i, rfl⟩, 0, by simp [optFam]⟩
  | one => exact ⟨1, Subgroup.one_mem _, 0, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha, m, rfl⟩ := hx
    obtain ⟨b, hb, n, rfl⟩ := hy
    refine ⟨a * b, Subgroup.mul_mem _ ha hb, m + n, ?_⟩
    have hab : Commute b (e₀ ^ m) := by
      refine Subgroup.closure_induction (p := fun b _ => Commute b (e₀ ^ m)) ?_ ?_ ?_ ?_ hb
      · rintro _ ⟨i, rfl⟩
        exact ((he₀ i).zpow_right m)
      · exact Commute.one_left _
      · intro u v _ _ hu hv
        exact hu.mul_left hv
      · intro u _ hu
        exact hu.inv_left
    calc a * e₀ ^ m * (b * e₀ ^ n) = a * (e₀ ^ m * b) * e₀ ^ n := by group
      _ = a * (b * e₀ ^ m) * e₀ ^ n := by rw [hab.eq.symm]
      _ = a * b * e₀ ^ (m + n) := by rw [zpow_add]; group
  | inv x _ hx =>
    obtain ⟨a, ha, m, rfl⟩ := hx
    refine ⟨a⁻¹, Subgroup.inv_mem _ ha, -m, ?_⟩
    have hae : Commute a (e₀ ^ m) := by
      refine Subgroup.closure_induction (p := fun b _ => Commute b (e₀ ^ m)) ?_ ?_ ?_ ?_ ha
      · rintro _ ⟨i, rfl⟩
        exact ((he₀ i).zpow_right m)
      · exact Commute.one_left _
      · intro u v _ _ hu hv
        exact hu.mul_left hv
      · intro u _ hu
        exact hu.inv_left
    calc (a * e₀ ^ m)⁻¹ = (e₀ ^ m)⁻¹ * a⁻¹ := by group
      _ = a⁻¹ * (e₀ ^ m)⁻¹ := (hae.inv_left.inv_right).eq.symm
      _ = a⁻¹ * e₀ ^ (-m) := by rw [zpow_neg]

theorem eq_one_of_mem_Y (e : ι → G) (e₀ : G) (y : ι → G) (hee : ∀ i j, Commute (e i) (e j))
    (he₀ : ∀ i, Commute (e i) e₀) (he3 : ∀ i, e i ^ 3 = 1) (he₀3 : e₀ ^ 3 = 1)
    (hy : ∀ i j, i ≠ j → Commute (y i) (e j)) (hy₀ : ∀ i, Commute (y i) e₀)
    (hyi : ∀ i, ¬ Commute (y i) (e i)) (hnc : ∃ g : G, ¬ Commute g e₀) {z : G}
    (hzc : ∀ g : G, Commute g z) (hz : z ∈ Subgroup.closure (Set.range (optFam e e₀))) :
    z = 1 := by
  obtain ⟨a, ha, m, rfl⟩ := mem_Y_iff e e₀ hee he₀ hz
  have hae : a = 1 := by
    refine eq_one_of_mem_closure e a y hee he3 hy (fun i => ?_) hyi ha
    have h1 : Commute (y i) (a * e₀ ^ m) := hzc (y i)
    have h2 : Commute (y i) (e₀ ^ m) := (hy₀ i).zpow_right m
    have h3 := h1.mul_right h2.inv_right
    rwa [mul_inv_cancel_right] at h3
  subst hae
  rw [one_mul] at hzc ⊢
  by_cases h3 : (3 : ℤ) ∣ m
  · exact zpow_eq_one_of_three_dvd he₀3 h3
  · exfalso
    obtain ⟨g, hg⟩ := hnc
    exact hg (commute_of_commute_zpow he₀3 h3 (hzc g))

end Group

end I1015

end CFSG.LocalAnalysis.GLTheoremA.CatB
