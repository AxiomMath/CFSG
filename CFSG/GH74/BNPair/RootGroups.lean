module

public import CFSG.GH74.BNPair.Statements
public import CFSG.GH74.BNPair.Basic

public section

namespace CFSG.GH74.BNPair

open scoped Pointwise

universe u

section ConjBy

variable {X : Type*} [Group X]

theorem mem_conjBy_iff {m x : X} {A : Subgroup X} : x ∈ conjBy m A ↔ m * x * m⁻¹ ∈ A := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro h
    exact ⟨m * x * m⁻¹, h, by simp [mul_assoc]⟩

theorem conjBy_mul (m m' : X) (A : Subgroup X) :
    conjBy (m * m') A = conjBy m' (conjBy m A) := by
  ext x
  rw [mem_conjBy_iff, mem_conjBy_iff, mem_conjBy_iff]
  simp [mul_assoc]

theorem conjBy_one (A : Subgroup X) : conjBy (1 : X) A = A := by
  ext x
  rw [mem_conjBy_iff]
  simp

end ConjBy

section ChainProd

variable {X : Type*} [Group X]

theorem mem_intList_iff {i j k : ℤ} : k ∈ intList i j ↔ i ≤ k ∧ k ≤ j := by
  unfold intList
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨t, ht, rfl⟩
    omega
  · rintro ⟨h1, h2⟩
    exact ⟨(k - i).toNat, by omega, by omega⟩

theorem chainProd_subset (A : ℤ → Subgroup X) (P : Subgroup X) :
    ∀ l : List ℤ, (∀ k ∈ l, A k ≤ P) → chainProd A l ⊆ P := by
  intro l
  induction l with
  | nil =>
    intro _ x hx
    simp only [chainProd, List.map_nil, List.prod_nil, Set.mem_one] at hx
    rw [hx]
    exact P.one_mem
  | cons k l ih =>
    intro h x hx
    simp only [chainProd, List.map_cons, List.prod_cons] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.1 hx
    exact P.mul_mem (h k (by simp) ha) (ih (fun k' hk' => h k' (by simp [hk'])) hb)

end ChainProd

namespace RankTwoSystem

variable {X : Type*} [Group X] {n : ℕ} (D : RankTwoSystem X n)

def PermutesRoots (m : X) : Prop :=
  (∀ i, IsRoot n i → ∃ j, IsRoot n j ∧ conjBy m (D.root i) = D.root j) ∧
    (∀ i, IsRoot n i → ∃ j, IsRoot n j ∧ conjBy m⁻¹ (D.root i) = D.root j)

theorem PermutesRoots.mul {m m' : X} (h : D.PermutesRoots m) (h' : D.PermutesRoots m') :
    D.PermutesRoots (m * m') := by
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · obtain ⟨j, hj, hij⟩ := h.1 i hi
    obtain ⟨k, hk, hjk⟩ := h'.1 j hj
    exact ⟨k, hk, by rw [conjBy_mul, hij, hjk]⟩
  · obtain ⟨j, hj, hij⟩ := h'.2 i hi
    obtain ⟨k, hk, hjk⟩ := h.2 j hj
    exact ⟨k, hk, by rw [mul_inv_rev, conjBy_mul, hij, hjk]⟩

theorem PermutesRoots.inv {m : X} (h : D.PermutesRoots m) : D.PermutesRoots m⁻¹ :=
  ⟨h.2, by simpa using h.1⟩

theorem permutesRoots_of_mem_cartan {h : X} (hB : h ∈ D.B) (hN : h ∈ D.N) :
    D.PermutesRoots h := by
  have hB' : h⁻¹ ∈ D.B := D.B.inv_mem hB
  have hN' : h⁻¹ ∈ D.N := D.N.inv_mem hN
  have key : ∀ i, IsRoot n i → conjBy h (D.root i) = D.root i := by
    intro i hi
    ext x
    rw [mem_conjBy_iff]
    constructor
    · intro hx
      have := D.roots.invariant i hi h⁻¹ ⟨hB', hN'⟩ _ hx
      have e : h⁻¹ * (h * x * h⁻¹) * h⁻¹⁻¹ = x := by group
      rwa [e] at this
    · intro hx
      exact D.roots.invariant i hi h ⟨hB, hN⟩ x hx
  refine ⟨fun i hi => ⟨i, hi, key i hi⟩, fun i hi => ⟨i, hi, ?_⟩⟩
  ext x
  rw [mem_conjBy_iff]
  constructor
  · intro hx
    have := D.roots.invariant i hi h ⟨hB, hN⟩ _ hx
    have e : h * (h⁻¹ * x * h⁻¹⁻¹) * h⁻¹ = x := by group
    rwa [e] at this
  · intro hx
    exact D.roots.invariant i hi h⁻¹ ⟨hB', hN'⟩ x hx

theorem w₁_mul_self : D.w₁ * D.w₁ = 1 :=
  D.isTits.bnCore.mul_self_eq_one D.w₁ (by simp)

theorem w₂_mul_self : D.w₂ * D.w₂ = 1 :=
  D.isTits.bnCore.mul_self_eq_one D.w₂ (by simp)

theorem exists_action₁ (m : D.N) (hm : (m : D.Weyl) = D.w₁) (i : ℤ) (hi : IsRoot n i) :
    ∃ j, IsRoot n j ∧ conjBy (m : X) (D.root i) = D.root j := by
  obtain ⟨h1, h2, h3⟩ := D.roots.action₁ m hm
  have hn := D.three_le
  obtain ⟨hi0, hin⟩ := hi
  by_cases h : i = 1
  · subst h
    exact ⟨-1, ⟨by norm_num, by simp; omega⟩, h1⟩
  by_cases h' : i = -1
  · subst h'
    exact ⟨1, ⟨by norm_num, by simp; omega⟩, h2⟩
  rcases lt_or_gt_of_ne hi0 with hneg | hpos
  · obtain ⟨k, rfl⟩ : ∃ k, i = -k := ⟨-i, by ring⟩
    exact ⟨-((n : ℤ) + 2 - k), ⟨by omega, by omega⟩, (h3 k (by omega) (by omega)).2⟩
  · exact ⟨(n : ℤ) + 2 - i, ⟨by omega, by omega⟩, (h3 i (by omega) (by omega)).1⟩

theorem exists_action₂ (m : D.N) (hm : (m : D.Weyl) = D.w₂) (i : ℤ) (hi : IsRoot n i) :
    ∃ j, IsRoot n j ∧ conjBy (m : X) (D.root i) = D.root j := by
  obtain ⟨h1, h2, h3⟩ := D.roots.action₂ m hm
  have hn := D.three_le
  obtain ⟨hi0, hin⟩ := hi
  by_cases h : i = n
  · subst h
    exact ⟨-(n : ℤ), ⟨by omega, by omega⟩, h1⟩
  by_cases h' : i = -(n : ℤ)
  · subst h'
    exact ⟨n, ⟨by omega, by omega⟩, h2⟩
  rcases lt_or_gt_of_ne hi0 with hneg | hpos
  · obtain ⟨k, rfl⟩ : ∃ k, i = -k := ⟨-i, by ring⟩
    exact ⟨-((n : ℤ) - k), ⟨by omega, by omega⟩, (h3 k (by omega) (by omega)).2⟩
  · exact ⟨(n : ℤ) - i, ⟨by omega, by omega⟩, (h3 i (by omega) (by omega)).1⟩

theorem permutesRoots_of_lift₁ (m : D.N) (hm : (m : D.Weyl) = D.w₁) : D.PermutesRoots (m : X) := by
  refine ⟨D.exists_action₁ m hm, ?_⟩
  have hm' : ((m⁻¹ : D.N) : D.Weyl) = D.w₁ := by
    rw [QuotientGroup.mk_inv, hm]
    exact inv_eq_of_mul_eq_one_right D.w₁_mul_self
  intro i hi
  simpa using D.exists_action₁ (m⁻¹) hm' i hi

theorem permutesRoots_of_lift₂ (m : D.N) (hm : (m : D.Weyl) = D.w₂) : D.PermutesRoots (m : X) := by
  refine ⟨D.exists_action₂ m hm, ?_⟩
  have hm' : ((m⁻¹ : D.N) : D.Weyl) = D.w₂ := by
    rw [QuotientGroup.mk_inv, hm]
    exact inv_eq_of_mul_eq_one_right D.w₂_mul_self
  intro i hi
  simpa using D.exists_action₂ (m⁻¹) hm' i hi

theorem permutesRoots_of_mem_N (m : D.N) : D.PermutesRoots (m : X) := by
  have key : ∀ w : D.Weyl, w ∈ Subgroup.closure ({D.w₁, D.w₂} : Set D.Weyl) →
      ∀ m : D.N, (m : D.Weyl) = w → D.PermutesRoots (m : X) := by
    intro w hw
    induction hw using Subgroup.closure_induction with
    | mem x hx =>
      intro m hm
      rcases hx with rfl | rfl
      · exact D.permutesRoots_of_lift₁ m hm
      · exact D.permutesRoots_of_lift₂ m hm
    | one =>
      intro m hm
      exact D.permutesRoots_of_mem_cartan (mk_eq_one_iff.1 hm) m.2
    | mul x y hx hy ihx ihy =>
      intro m hm
      obtain ⟨m', hm'⟩ := QuotientGroup.mk_surjective x
      have hm'' : ((m'⁻¹ * m : D.N) : D.Weyl) = y := by
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hm', hm]
        simp
      have := (ihx m' hm').mul D (ihy _ hm'')
      simpa using this
    | inv x hx ihx =>
      intro m hm
      have hm' : ((m⁻¹ : D.N) : D.Weyl) = x := by
        rw [QuotientGroup.mk_inv, hm]
        simp
      simpa using (ihx _ hm').inv D
  have hall : (m : D.Weyl) ∈ Subgroup.closure ({D.w₁, D.w₂} : Set D.Weyl) := by
    have := D.isTits.closure_eq
    simp only [Finset.coe_insert, Finset.coe_singleton] at this
    rw [this]
    trivial
  exact key _ hall m rfl

theorem conjBy_xplus_le {m : X} (hm : D.PermutesRoots m) : conjBy m D.Xplus ≤ D.Xplus := by
  have e : conjBy m D.Xplus = Subgroup.closure ((MulAut.conj m⁻¹).toMonoidHom ''
      (⋃ i ∈ {i : ℤ | IsRoot n i}, (D.root i : Set X))) := by
    unfold conjBy Xplus
    exact MonoidHom.map_closure _ _
  rw [e, Subgroup.closure_le]
  rintro _ ⟨x, hx, rfl⟩
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq] at hx
  obtain ⟨i, hi, hxi⟩ := hx
  obtain ⟨j, hj, hij⟩ := hm.1 i hi
  have : (MulAut.conj m⁻¹).toMonoidHom x ∈ conjBy m (D.root i) := ⟨x, hxi, rfl⟩
  rw [hij] at this
  exact Subgroup.subset_closure (Set.mem_iUnion₂.2 ⟨j, hj, this⟩)

theorem mem_xplus_conj_iff {m : X} (hm : D.PermutesRoots m) (x : X) :
    m * x * m⁻¹ ∈ D.Xplus ↔ x ∈ D.Xplus := by
  have h1 := D.conjBy_xplus_le hm
  have h2 := D.conjBy_xplus_le hm.inv
  constructor
  · intro h
    exact h1 (mem_conjBy_iff.2 h)
  · intro hx
    apply h2 (mem_conjBy_iff.2 _)
    have e : m⁻¹ * (m * x * m⁻¹) * m⁻¹⁻¹ = x := by group
    rw [e]
    exact hx

theorem root_le_xplus {i : ℤ} (hi : IsRoot n i) : D.root i ≤ D.Xplus :=
  fun _ hx => Subgroup.subset_closure (Set.mem_iUnion₂.2 ⟨i, hi, hx⟩)

theorem U_le_xplus : D.U ≤ D.Xplus := by
  intro u hu
  have hu' : u ∈ chainProd D.root (intList 1 n) := by
    rw [← D.roots.carrier_eq]
    exact hu
  refine chainProd_subset D.root D.Xplus _ (fun k hk => ?_) hu'
  obtain ⟨h1, h2⟩ := mem_intList_iff.1 hk
  exact D.root_le_xplus ⟨by omega, by omega⟩

theorem xplus_normal : D.Xplus.Normal := by
  rw [← Subgroup.normalizer_eq_top_iff]
  refine eq_top_iff.2 ?_
  rw [← D.isTits.gen]
  have hN : D.N ≤ Subgroup.normalizer (D.Xplus : Set X) := fun m hm =>
    Subgroup.mem_normalizer_iff.2 fun x =>
      (D.mem_xplus_conj_iff (D.permutesRoots_of_mem_N ⟨m, hm⟩) x).symm
  refine sup_le ?_ hN
  intro b hb
  have hbHU : b ∈ ((D.B ⊓ D.N : Subgroup X) : Set X) * (D.U : Set X) := by
    rw [← D.isSplit.2]
    exact hb
  obtain ⟨h, hh, u, hu, rfl⟩ := Set.mem_mul.1 hbHU
  exact Subgroup.mul_mem _ (hN hh.2) (Subgroup.le_normalizer (D.U_le_xplus hu))

end RankTwoSystem

theorem eq30_3 : Eq30_3.{u} :=
  fun _ _ _ D => D.xplus_normal

end CFSG.GH74.BNPair
