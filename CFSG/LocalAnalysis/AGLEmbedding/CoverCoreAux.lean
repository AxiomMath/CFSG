module

public import CFSG.LocalAnalysis.AGLEmbedding.SporadicAlphaData

public section

namespace CFSG.AGLEmbedding

open scoped IsMulCommutative commutatorElement

namespace CoverCore

section General

variable {G : Type*} [Group G]

theorem pow_val_add {M : Type*} [Monoid M] {p : ℕ} [NeZero p] {u : M} (hu : u ^ p = 1)
    (x y : ZMod p) : u ^ (x + y).val = u ^ x.val * u ^ y.val := by
  rw [ZMod.val_add, ← pow_eq_pow_mod _ hu, pow_add]

theorem commutatorElement_mul_center_left {z : G} (hz : z ∈ Subgroup.center G) (x y : G) :
    ⁅x * z, y⁆ = ⁅x, y⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul,
    commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hz y).symm, mul_one,
    mul_inv_cancel, one_mul]

theorem commutatorElement_mul_center_right {z : G} (hz : z ∈ Subgroup.center G) (x y : G) :
    ⁅x, y * z⁆ = ⁅x, y⁆ := by
  rw [commutatorElement_mul_right_eq_mul_conj,
    commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hz x), mul_one,
    mul_inv_cancel_right]

theorem mul_pow_eq_of_center {x y d : G} (hd : d ∈ Subgroup.center G)
    (h : y * x = d * (x * y)) (m : ℕ) : (x * y) ^ m = d ^ m.choose 2 * (x ^ m * y ^ m) := by
  have hc : ∀ (g : G) (k : ℕ), Commute g (d ^ k) := fun g k =>
    (show Commute g d from Subgroup.mem_center_iff.mp hd g).pow_right k
  have h1 : ∀ k : ℕ, y ^ k * x = d ^ k * (x * y ^ k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc y ^ (k + 1) * x = y * (d ^ k * (x * y ^ k)) := by rw [pow_succ', mul_assoc, ih]
        _ = d ^ k * (y * x * y ^ k) := by rw [(hc y k).left_comm, mul_assoc]
        _ = d ^ (k + 1) * (x * y ^ (k + 1)) := by
          rw [h, pow_succ d k, pow_succ' y k]; simp only [mul_assoc]
  induction m with
  | zero => simp
  | succ m ih =>
    have hC : (m + 1).choose 2 = m.choose 2 + m := by
      rw [Nat.choose_succ_succ, Nat.choose_one_right, add_comm]
    calc (x * y) ^ (m + 1) = d ^ m.choose 2 * (x ^ m * ((y ^ m * x) * y)) := by
          rw [pow_succ, ih]; simp only [mul_assoc]
      _ = d ^ m.choose 2 * (d ^ m * (x ^ m * (x * (y ^ m * y)))) := by
          rw [h1]; simp only [mul_assoc]; rw [(hc (x ^ m) m).left_comm]
      _ = d ^ (m + 1).choose 2 * (x ^ (m + 1) * y ^ (m + 1)) := by
          rw [hC, pow_add, pow_succ x m, pow_succ y m]; simp only [mul_assoc]

theorem mul_pow_prime_of_center {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {x y d : G}
    (hd : d ∈ Subgroup.center G) (hdp : d ^ p = 1) (h : y * x = d * (x * y)) :
    (x * y) ^ p = x ^ p * y ^ p := by
  obtain ⟨k, hk⟩ := hp.dvd_choose_self two_ne_zero (hp.two_le.lt_of_ne (Ne.symm hp2))
  rw [mul_pow_eq_of_center hd h, hk, pow_mul, hdp, one_pow, one_mul]

theorem exists_injective_hom_zmod {C : Type*} [Group C] [IsCyclic C] {p : ℕ} (hp : p.Prime)
    (hC : ∀ c : C, c ^ p = 1) : ∃ χ : C →* Multiplicative (ZMod p), Function.Injective χ := by
  have hdvd : Nat.card C ∣ p :=
    IsCyclic.exponent_eq_card (α := C) ▸ Monoid.exponent_dvd_of_forall_pow_eq_one hC
  rcases (Nat.dvd_prime hp).mp hdvd with h | h
  · have : Subsingleton C := (Nat.card_eq_one_iff_unique.mp h).1
    exact ⟨1, Function.injective_of_subsingleton _⟩
  · obtain ⟨e⟩ : Nonempty (Multiplicative (ZMod p) ≃* C) :=
      h ▸ ⟨zmodCyclicMulEquiv inferInstance⟩
    exact ⟨e.symm.toMonoidHom, e.symm.injective⟩

theorem eq_sum_of_map_add {n p : ℕ} [NeZero p] {F : (Fin n → ZMod p) → ZMod p}
    (hF : ∀ c d, F (c + d) = F c + F d) (c : Fin n → ZMod p) :
    F c = ∑ k, c k * F (Pi.single k 1) := by
  let F' : (Fin n → ZMod p) →+ ZMod p := AddMonoidHom.mk' F hF
  have hs : ∀ (k : Fin n) (x : ZMod p),
      Pi.single k x = x.val • (Pi.single k 1 : Fin n → ZMod p) :=
    fun k x => by rw [← Pi.single_smul', nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
  calc F c = F' (∑ k, Pi.single k (c k)) := by rw [Finset.univ_sum_single]; rfl
    _ = ∑ k, F' (Pi.single k (c k)) := map_sum _ _ _
    _ = ∑ k, c k * F (Pi.single k 1) := Finset.sum_congr rfl fun k _ => by
        rw [hs, map_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val]; rfl

end General

section Log

variable {K : Type} [Group K] {p : ℕ}

theorem exists_log_omega (hp : p.Prime) (hZc : IsCyclic (Subgroup.center K)) :
    ∃ f : K → ZMod p, (∀ z w, z ∈ Subgroup.center K → z ^ p = 1 → w ∈ Subgroup.center K →
      w ^ p = 1 → f (z * w) = f z + f w) ∧
      ∀ z, z ∈ Subgroup.center K → z ^ p = 1 → f z = 0 → z = 1 := by
  let Ω : Subgroup (Subgroup.center K) := (powMonoidHom p).ker
  have hΩ : ∀ c : Ω, c ^ p = 1 := fun c => Subtype.ext c.2
  obtain ⟨χ, hχ⟩ := exists_injective_hom_zmod (C := Ω) hp hΩ
  classical
  refine ⟨fun z => if h : z ∈ Subgroup.center K ∧ z ^ p = 1 then
    Multiplicative.toAdd (χ ⟨⟨z, h.1⟩, Subtype.ext h.2⟩) else 0, ?_, ?_⟩
  · intro z w hz hz' hw hw'
    have hzw : z * w ∈ Subgroup.center K ∧ (z * w) ^ p = 1 :=
      ⟨mul_mem hz hw, by
        rw [(show Commute z w from Subgroup.mem_center_iff.mp hz w |>.symm).mul_pow, hz', hw',
          one_mul]⟩
    simp only [dite_eq_left hzw, dite_eq_left (And.intro hz hz'),
      dite_eq_left (And.intro hw hw'), ← toAdd_mul, ← map_mul]
    rfl
  · intro z hz hz' h0
    simp only [dite_eq_left (And.intro hz hz'), toAdd_eq_zero] at h0
    have := hχ (h0.trans (map_one χ).symm)
    exact congrArg (fun c : Ω => ((c : Subgroup.center K) : K)) this

theorem exists_log_center (hp : p.Prime) (hZc : IsCyclic (Subgroup.center K)) :
    ∃ h : K → ZMod p, (∀ z w, z ∈ Subgroup.center K → w ∈ Subgroup.center K →
      h (z * w) = h z + h w) ∧
      ∀ z ∈ Subgroup.center K, h z = 0 → ∃ w ∈ Subgroup.center K, z = w ^ p := by
  let P : Subgroup (Subgroup.center K) := (powMonoidHom p).range
  have : IsCyclic (Subgroup.center K ⧸ P) :=
    isCyclic_of_surjective _ (QuotientGroup.mk'_surjective P)
  have hQ : ∀ q : Subgroup.center K ⧸ P, q ^ p = 1 := fun q => by
    induction q using QuotientGroup.induction_on with
    | H z => exact (QuotientGroup.eq_one_iff _).mpr ⟨z, rfl⟩
  obtain ⟨χ, hχ⟩ := exists_injective_hom_zmod hp hQ
  classical
  refine ⟨fun z => if hz : z ∈ Subgroup.center K then
    Multiplicative.toAdd (χ (QuotientGroup.mk (⟨z, hz⟩ : Subgroup.center K))) else 0, ?_, ?_⟩
  · intro z w hz hw
    simp only [dite_eq_left (mul_mem hz hw), dite_eq_left hz, dite_eq_left hw, ← toAdd_mul,
      ← map_mul]
    rfl
  · intro z hz h0
    simp only [dite_eq_left hz, toAdd_eq_zero] at h0
    obtain ⟨w, hw⟩ := (QuotientGroup.eq_one_iff _).mp (hχ (h0.trans (map_one χ).symm))
    exact ⟨w, w.2, (congrArg Subtype.val hw).symm⟩

end Log

section Lift

variable {K X : Type} [Group K] [Group X] (π : K →* X)

theorem commutatorElement_eq_of_map_eq (hker : π.ker = Subgroup.center K) {x x' y y' : K}
    (hx : π x = π x') (hy : π y = π y') : ⁅x, y⁆ = ⁅x', y'⁆ := by
  have hzx : x⁻¹ * x' ∈ Subgroup.center K := hker ▸ π.eq_iff.mp hx.symm
  have hzy : y⁻¹ * y' ∈ Subgroup.center K := hker ▸ π.eq_iff.mp hy.symm
  rw [← mul_inv_cancel_left x x', ← mul_inv_cancel_left y y',
    commutatorElement_mul_center_left hzx, commutatorElement_mul_center_right hzy]

@[expose] noncomputable def coverComm (hπ : Function.Surjective π) (u v : X) : K :=
  ⁅Function.surjInv hπ u, Function.surjInv hπ v⁆

theorem commutatorElement_eq_coverComm (hπ : Function.Surjective π)
    (hker : π.ker = Subgroup.center K) (x y : K) : ⁅x, y⁆ = coverComm π hπ (π x) (π y) :=
  commutatorElement_eq_of_map_eq π hker (Function.surjInv_eq hπ _).symm
    (Function.surjInv_eq hπ _).symm

theorem coverComm_swap (hπ : Function.Surjective π) (u v : X) :
    coverComm π hπ v u = (coverComm π hπ u v)⁻¹ :=
  (commutatorElement_inv _ _).symm

end Lift

end CoverCore

namespace ModuleSpec

variable {X : Type} [Group X] {p : ℕ} (D : ModuleSpec X p)

theorem pairwise_commute : (Set.range D.a).Pairwise Commute := by
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ -
  exact D.comm i j

instance : IsMulCommutative D.span := Subgroup.isMulCommutative_closure D.pairwise_commute

theorem mul_comm_of_mem {u v : X} (hu : u ∈ D.span) (hv : v ∈ D.span) : u * v = v * u :=
  congrArg Subtype.val (mul_comm' (⟨u, hu⟩ : D.span) ⟨v, hv⟩)

theorem a_mem_span (k : Fin D.n) : D.a k ∈ D.span := Subgroup.subset_closure ⟨k, rfl⟩

theorem pow_eq_one_of_mem {u : X} (hu : u ∈ D.span) : u ^ p = 1 := by
  induction hu using Subgroup.closure_induction with
  | mem x hx => obtain ⟨k, rfl⟩ := hx; exact D.pow k
  | one => exact one_pow p
  | mul x y hx hy ihx ihy =>
    rw [(show Commute x y from D.mul_comm_of_mem hx hy).mul_pow, ihx, ihy, one_mul]
  | inv x hx ih => rw [inv_pow, ih, inv_one]

@[expose] def elt (c : Fin D.n → ZMod p) : X :=
  ((List.finRange D.n).map fun k => D.a k ^ (c k).val).prod

theorem elt_eq_prod (c : Fin D.n → ZMod p) :
    D.elt c = ((∏ k, (⟨D.a k, D.a_mem_span k⟩ : D.span) ^ (c k).val : D.span) : X) := by
  rw [Fin.prod_univ_def, SubmonoidClass.coe_list_prod, List.map_map]
  rfl

theorem elt_mem (c : Fin D.n → ZMod p) : D.elt c ∈ D.span := by
  rw [elt_eq_prod]
  exact Subtype.property _

theorem elt_add [NeZero p] (c d : Fin D.n → ZMod p) : D.elt (c + d) = D.elt c * D.elt d := by
  simp only [elt_eq_prod, ← Subgroup.coe_mul, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  exact CoverCore.pow_val_add (Subtype.ext (D.pow k)) _ _

theorem elt_zero : D.elt 0 = 1 := by
  simp [elt]

theorem elt_neg [NeZero p] (c : Fin D.n → ZMod p) : D.elt (-c) = (D.elt c)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← elt_add, neg_add_cancel, elt_zero]

theorem elt_single [Fact (1 < p)] (k : Fin D.n) : D.elt (Pi.single k 1) = D.a k := by
  rw [elt_eq_prod, Finset.prod_eq_single k]
  · simp [ZMod.val_one]
  · intro j _ hj
    simp [hj]
  · simp

theorem elt_injective [NeZero p] : Function.Injective D.elt := by
  intro c d h
  have h0 : D.elt (c - d) = 1 := by
    rw [sub_eq_add_neg, elt_add, elt_neg, h, mul_inv_cancel]
  exact sub_eq_zero.mp (D.indep _ h0)

theorem exists_elt [Fact p.Prime] {u : X} (hu : u ∈ D.span) : ∃ c, D.elt c = u := by
  induction hu using Subgroup.closure_induction with
  | mem x hx => obtain ⟨k, rfl⟩ := hx; exact ⟨Pi.single k 1, D.elt_single k⟩
  | one => exact ⟨0, D.elt_zero⟩
  | mul x y _ _ hx hy =>
    obtain ⟨c, rfl⟩ := hx
    obtain ⟨d, rfl⟩ := hy
    exact ⟨c + d, D.elt_add c d⟩
  | inv x _ hx =>
    obtain ⟨c, rfl⟩ := hx
    exact ⟨-c, D.elt_neg c⟩

theorem elt_col (j : Fin D.m) (i : Fin D.n) :
    D.elt (fun k => D.M j k i) = D.g j * D.a i * (D.g j)⁻¹ :=
  (D.act j i).symm

end ModuleSpec

end CFSG.AGLEmbedding
