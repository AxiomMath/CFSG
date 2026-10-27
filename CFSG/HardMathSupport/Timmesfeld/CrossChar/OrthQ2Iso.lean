module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.OrthQ2Six

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open Module

section Geometry

theorem zmod3_cases : ∀ a s : ZMod 3, s ≠ 0 → a = 0 ∨ a = s ∨ a = s + s := by
  decide

theorem zmod3_ne : ∀ s : ZMod 3, s ≠ 0 → s ≠ 0 ∧ s + s ≠ 0 ∧ s ≠ s + s := by
  decide

theorem zmod3_three (s : ZMod 3) : s + s + s = 0 := by
  revert s
  decide

theorem exists_mem_ker_not_mem : ∀ φ ∈ Rset, ∀ ψ ∈ Rset, φ ≠ ψ →
    ∃ x : Z3, dot φ x = 0 ∧ dot ψ x ≠ 0 := by
  decide

theorem card_ker_inf_ker : ∀ φ ∈ Rset, ∀ ψ ∈ Rset, φ ≠ ψ →
    (Finset.univ.filter (fun z : Z3 => dot φ z = 0 ∧ dot ψ z = 0)).card = 3 := by
  decide

theorem card_lines_through_two : ∀ φ ∈ Rset, ∀ ψ ∈ Rset, φ ≠ ψ →
    (Rset.filter (fun x => dot φ x = 0 ∧ dot ψ x = 0)).card = 1 := by
  decide

theorem card_lines_avoid : ∀ φ ∈ Rset, ∀ ψ ∈ Rset, φ ≠ ψ →
    (Rset.filter (fun x => dot φ x ≠ 0 ∧ dot ψ x = 0)).card = 3 := by
  decide

theorem card_lines_not_through : ∀ φ ∈ Rset, (Rset.filter (fun x => dot φ x ≠ 0)).card = 9 := by
  decide

theorem dot_comm (φ x : Z3) : dot φ x = dot x φ := by
  simp only [dot, mul_comm]

end Geometry

section Partition

theorem sum_three_cosets {M : Type*} [AddCommMonoid M] (f : Z3 → M) (P : Z3 → Prop)
    [DecidablePred P] {x ψ : Z3} (hP : ∀ z, P (x + z) ↔ P z) (hx : dot ψ x ≠ 0) :
    ∑ z ∈ Finset.univ.filter P, f z =
      ∑ k ∈ Finset.univ.filter (fun k => P k ∧ dot ψ k = 0),
        (f k + f (x + k) + f (x + x + k)) := by
  classical
  set s := dot ψ x with hs
  set A₀ := Finset.univ.filter (fun k => P k ∧ dot ψ k = 0) with hA₀
  have hP2 : ∀ z, P (x + x + z) ↔ P z := fun z => by rw [add_assoc, hP, hP]
  have h3x : ∀ z, x + (x + x + z) = z := fun z => by
    rw [← add_assoc, ← add_assoc, three_smul_z3, zero_add]
  have h3x' : ∀ z, x + x + (x + z) = z := fun z => by
    rw [← add_assoc, three_smul_z3, zero_add]
  have hmap1 : A₀.map (addLeftEmbedding x) =
      Finset.univ.filter (fun z => P z ∧ dot ψ z = s) := by
    ext z
    simp only [hA₀, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      addLeftEmbedding_apply]
    constructor
    · rintro ⟨k, ⟨hk, hk0⟩, rfl⟩
      refine ⟨(hP k).2 hk, ?_⟩
      rw [dot_add, hk0, add_zero]
    · rintro ⟨hz, hzs⟩
      refine ⟨x + x + z, ⟨(hP _).1 (by rw [h3x]; exact hz), ?_⟩, h3x z⟩
      rw [dot_add, dot_add, hzs, ← hs]
      have := zmod3_three s
      linear_combination this
  have hmap2 : A₀.map (addLeftEmbedding (x + x)) =
      Finset.univ.filter (fun z => P z ∧ dot ψ z = s + s) := by
    ext z
    simp only [hA₀, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      addLeftEmbedding_apply]
    constructor
    · rintro ⟨k, ⟨hk, hk0⟩, rfl⟩
      refine ⟨(hP2 k).2 hk, ?_⟩
      rw [dot_add, dot_add, hk0, add_zero]
    · rintro ⟨hz, hzs⟩
      refine ⟨x + z, ⟨(hP z).2 hz, ?_⟩, h3x' z⟩
      rw [dot_add, hzs, ← hs]
      have := zmod3_three s
      linear_combination this
  obtain ⟨hs0, hss0, hsss⟩ := zmod3_ne s hx
  have hunion : Finset.univ.filter P = A₀ ∪ (A₀.map (addLeftEmbedding x) ∪
      A₀.map (addLeftEmbedding (x + x))) := by
    rw [hmap1, hmap2]
    ext z
    simp only [hA₀, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hz
      rcases zmod3_cases (dot ψ z) s hs0 with h | h | h
      · exact Or.inl ⟨hz, h⟩
      · exact Or.inr (Or.inl ⟨hz, h⟩)
      · exact Or.inr (Or.inr ⟨hz, h⟩)
    · rintro (⟨hz, -⟩ | ⟨hz, -⟩ | ⟨hz, -⟩) <;> exact hz
  have hd12 : Disjoint (A₀.map (addLeftEmbedding x)) (A₀.map (addLeftEmbedding (x + x))) := by
    rw [hmap1, hmap2, Finset.disjoint_filter]
    rintro z - ⟨-, h1⟩ ⟨-, h2⟩
    exact hsss (h1.symm.trans h2)
  have hd0 : Disjoint A₀ (A₀.map (addLeftEmbedding x) ∪ A₀.map (addLeftEmbedding (x + x))) := by
    rw [hmap1, hmap2, Finset.disjoint_union_right, hA₀, Finset.disjoint_filter,
      Finset.disjoint_filter]
    refine ⟨fun z _ h1 h2 => hs0 (h1.2 ▸ h2.2).symm, fun z _ h1 h2 => hss0 (h1.2 ▸ h2.2).symm⟩
  rw [hunion, Finset.sum_union hd0, Finset.sum_union hd12, Finset.sum_map, Finset.sum_map,
    ← add_assoc]
  simp only [addLeftEmbedding_apply, ← Finset.sum_add_distrib]

end Partition

section Idempotents

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

@[expose] noncomputable def e0 (ρ : Multiplicative Z3 →* Module.End K V) : Module.End K V :=
  ∑ z : Z3, act ρ z

@[expose] noncomputable def isoP (ρ : Multiplicative Z3 →* Module.End K V) (φ : Z3) :
    Module.End K V :=
  eN ρ φ + e0 ρ

theorem act_e0 (ρ : Multiplicative Z3 →* Module.End K V) (y : Z3) (v : V) :
    act ρ y (e0 ρ v) = e0 ρ v := by
  simp only [e0, LinearMap.sum_apply, map_sum]
  refine Finset.sum_equiv (Equiv.addLeft y) (fun _ => by simp) fun z _ => ?_
  rw [← Module.End.mul_apply, ← act_add]
  rfl

theorem e0_mem_fixOf (ρ : Multiplicative Z3 →* Module.End K V) (S : Set Z3) (v : V) :
    e0 ρ v ∈ fixOf ρ S := fun y _ => act_e0 ρ y v

theorem odd_smul [CharP K 2] {n : ℕ} (hn : Odd n) (v : V) : n • v = v :=
  odd_nsmul_eq (K := K) n hn v

theorem e0_of_mem [CharP K 2] (ρ : Multiplicative Z3 →* Module.End K V) {v : V}
    (hv : v ∈ fixOf ρ Set.univ) : e0 ρ v = v := by
  simp only [e0, LinearMap.sum_apply]
  rw [Finset.sum_congr rfl (g := fun _ => v) (fun z _ => hv z (Set.mem_univ z)),
    Finset.sum_const, Finset.card_univ]
  have : Fintype.card Z3 = 27 := by simp
  rw [this]
  exact odd_smul (K := K) (by decide) v

theorem e0_act (ρ : Multiplicative Z3 →* Module.End K V) (y : Z3) (v : V) :
    e0 ρ (act ρ y v) = e0 ρ v := by
  simp only [e0, LinearMap.sum_apply]
  refine Finset.sum_equiv (Equiv.addRight y) (fun _ => by simp) fun z _ => ?_
  rw [← Module.End.mul_apply, ← act_add]
  rfl

theorem e0_eN [CharP K 2] (ρ : Multiplicative Z3 →* Module.End K V) (φ : Z3) (hφ : φ ∈ Rset)
    (v : V) : e0 ρ (eN ρ φ v) = e0 ρ v := by
  unfold eN
  rw [LinearMap.sum_apply, map_sum]
  simp only [e0_act]
  rw [Finset.sum_const, card_N φ hφ]
  exact odd_smul (K := K) (by decide) _

theorem eN_e0 [CharP K 2] (ρ : Multiplicative Z3 →* Module.End K V) (φ : Z3) (hφ : φ ∈ Rset)
    (v : V) : eN ρ φ (e0 ρ v) = e0 ρ v :=
  eN_of_mem ρ hφ (e0_mem_fixOf ρ _ v)

theorem e0_e0 [CharP K 2] (ρ : Multiplicative Z3 →* Module.End K V) (v : V) :
    e0 ρ (e0 ρ v) = e0 ρ v :=
  e0_of_mem ρ (e0_mem_fixOf ρ _ v)

theorem eN_eN [CharP K 2] (ρ : Multiplicative Z3 →* Module.End K V) {φ : Z3} (hφ : φ ∈ Rset)
    (v : V) : eN ρ φ (eN ρ φ v) = eN ρ φ v :=
  eN_of_mem ρ hφ (eN_mem_fixOf ρ φ v)

theorem eCyc_apply_eq_sum (ρ : Multiplicative Z3 →* Module.End K V) (x : Z3) (w : V) :
    ∀ (s : Finset Z3), eCyc ρ x (∑ z ∈ s, act ρ z w) =
      ∑ z ∈ s, (act ρ z w + act ρ (x + z) w + act ρ (x + x + z) w) := by
  intro s
  rw [map_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  simp only [eCyc, LinearMap.add_apply, act_zero, Module.End.one_apply]
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← act_add, ← act_add]

theorem eCyc_eN_of_ne (ρ : Multiplicative Z3 →* Module.End K V) {φ x : Z3} (hx : dot φ x ≠ 0)
    (v : V) : eCyc ρ x (eN ρ φ v) = e0 ρ v := by
  classical
  have h1 : eN ρ φ v = ∑ z ∈ Finset.univ.filter (fun z : Z3 => dot φ z = 0), act ρ z v := by
    unfold eN
    rw [LinearMap.sum_apply]
  rw [h1, eCyc_apply_eq_sum]
  have h2 := sum_three_cosets (fun z => act ρ z v) (fun _ => True) (x := x) (ψ := φ)
    (fun _ => Iff.rfl) hx
  have h3 : Finset.univ.filter (fun _ : Z3 => True) = Finset.univ :=
    Finset.filter_true_of_mem fun _ _ => trivial
  have h4 : Finset.univ.filter (fun k : Z3 => True ∧ dot φ k = 0) =
      Finset.univ.filter (fun k : Z3 => dot φ k = 0) :=
    Finset.filter_congr fun _ _ => by simp
  rw [h3, h4] at h2
  rw [← h2]
  simp only [e0, LinearMap.sum_apply]

theorem eN_eN_of_ne [CharP K 2] (ρ : Multiplicative Z3 →* Module.End K V) {φ ψ : Z3}
    (hφ : φ ∈ Rset) (hψ : ψ ∈ Rset) (hne : φ ≠ ψ) (v : V) :
    eN ρ φ (eN ρ ψ v) = e0 ρ v := by
  classical
  obtain ⟨x, hxφ, hxψ⟩ := exists_mem_ker_not_mem φ hφ ψ hψ hne
  set w := eN ρ ψ v with hw
  have hwfix : ∀ k, dot ψ k = 0 → act ρ k w = w := fun k hk => eN_mem_fixOf ρ ψ v k hk
  have h1 : eN ρ φ w = ∑ z ∈ Finset.univ.filter (fun z : Z3 => dot φ z = 0), act ρ z w := by
    unfold eN
    rw [LinearMap.sum_apply]
  have hP : ∀ z, dot φ (x + z) = 0 ↔ dot φ z = 0 := fun z => by rw [dot_add, hxφ, zero_add]
  rw [h1, sum_three_cosets (fun z => act ρ z w) (fun z => dot φ z = 0) hP hxψ]
  have h2 : ∀ k ∈ Finset.univ.filter (fun k : Z3 => dot φ k = 0 ∧ dot ψ k = 0),
      act ρ k w + act ρ (x + k) w + act ρ (x + x + k) w = eCyc ρ x w := by
    intro k hk
    have hk0 := (Finset.mem_filter.1 hk).2.2
    rw [act_add, act_add, Module.End.mul_apply, Module.End.mul_apply, hwfix k hk0]
    simp only [eCyc, LinearMap.add_apply, act_zero, Module.End.one_apply]
  rw [Finset.sum_congr rfl h2, Finset.sum_const, card_ker_inf_ker φ hφ ψ hψ hne,
    odd_smul (K := K) (by decide), hw, eCyc_eN_of_ne ρ hxψ]

end Idempotents

end CFSG.HardMathSupport.Timmesfeld.CrossChar
