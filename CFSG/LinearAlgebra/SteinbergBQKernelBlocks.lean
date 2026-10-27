module

public import CFSG.LinearAlgebra.SteinbergBQAlternatingMatrices
public import Mathlib.LinearAlgebra.Projectivization.Cardinality
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import Mathlib.FieldTheory.Finiteness

public noncomputable section

namespace CFSG.LinearAlgebra.SteinbergBQ

open Module QuadraticMap
open TauCeti.QuadraticMap (orthogonalGroup)
open scoped LinearAlgebra.Projectivization

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem finite_linearEquiv_zmod2 [FiniteDimensional (ZMod 2) V] :
    Finite (V ≃ₗ[ZMod 2] V) := by
  have : Finite V := Module.finite_of_finite (ZMod 2)
  exact Finite.of_injective (fun e : V ≃ₗ[ZMod 2] V => (e : V → V)) fun e e' h =>
    LinearEquiv.ext (congrFun h)

@[expose] def avgMap (N : Subgroup (V ≃ₗ[ZMod 2] V)) [Finite N] : V →ₗ[ZMod 2] V :=
  letI := Fintype.ofFinite N
  ∑ n : N, ((n : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V)

section Avg

variable {N : Subgroup (V ≃ₗ[ZMod 2] V)} [Finite N]

theorem avgMap_apply (v : V) :
    letI := Fintype.ofFinite N
    avgMap N v = ∑ n : N, (n : V ≃ₗ[ZMod 2] V) v := by
  rw [avgMap, LinearMap.sum_apply]
  rfl

theorem apply_avgMap {g : V ≃ₗ[ZMod 2] V} (hg : g ∈ N) (v : V) : g (avgMap N v) = avgMap N v := by
  let := Fintype.ofFinite N
  rw [avgMap_apply, map_sum]
  exact Fintype.sum_equiv (Equiv.mulLeft ⟨g, hg⟩) _ _ fun n => rfl

theorem avgMap_mem_fixedSub (v : V) : avgMap N v ∈ fixedSub N :=
  fun _ hg => apply_avgMap hg v

theorem avgMap_apply_of_mem (hodd : Odd (Nat.card N)) {v : V} (hv : v ∈ fixedSub N) :
    avgMap N v = v := by
  let := Fintype.ofFinite N
  rw [avgMap_apply]
  have h : ∀ n : N, (n : V ≃ₗ[ZMod 2] V) v = v := fun n => hv n n.2
  simp only [h, Finset.sum_const, Finset.card_univ]
  rw [← Nat.card_eq_fintype_card]
  obtain ⟨k, hk⟩ := hodd
  rw [hk, succ_nsmul, mul_comm, mul_nsmul, two_nsmul, zmod2_vec_add_self, zero_add]

theorem avgMap_comm {g : V ≃ₗ[ZMod 2] V} (hg : ∀ n ∈ N, g * n = n * g) (v : V) :
    g (avgMap N v) = avgMap N (g v) := by
  let := Fintype.ofFinite N
  rw [avgMap_apply, avgMap_apply, map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← LinearEquiv.mul_apply, hg n n.2, LinearEquiv.mul_apply]

theorem polar_avgMap {q : QuadraticForm (ZMod 2) V} (hN : N ≤ orthogonalGroup q) (x y : V) :
    polar q (avgMap N x) y = polar q x (avgMap N y) := by
  let := Fintype.ofFinite N
  have h1 : ∀ x y, polar q x y = polarBilin q x y := fun x y => (polarBilin_apply_apply q x y).symm
  rw [h1, h1, avgMap_apply, avgMap_apply, map_sum, LinearMap.sum_apply, map_sum]
  refine Fintype.sum_equiv (Equiv.inv N) _ _ fun n => ?_
  rw [← h1, ← h1]
  have h2 := polar_map_of_mem_orthogonalGroup (hN n.2) x (((n⁻¹ : N) : V ≃ₗ[ZMod 2] V) y)
  rw [← LinearEquiv.mul_apply] at h2
  have h3 : ((n : V ≃ₗ[ZMod 2] V) * (n⁻¹ : N)) = 1 := by
    rw [Subgroup.coe_inv, mul_inv_cancel]
  rw [h3] at h2
  exact h2

end Avg

section IndexThree

variable {G : Type*} [Group G]

theorem pow_two_mem_iff_of_pow_three {N : Subgroup G} {c : G} (hc3 : c ^ 3 = 1) :
    c ^ 2 ∈ N ↔ c ∈ N := by
  refine ⟨fun h => ?_, fun h => N.pow_mem h 2⟩
  have e : c = c ^ 2 * c ^ 2 := by
    rw [← pow_add, show 2 + 2 = 3 + 1 from rfl, pow_succ, hc3, one_mul]
  rw [e]
  exact N.mul_mem h h

theorem mem_or_of_relIndex_eq_three {B N : Subgroup G} (hidx : N.relIndex B = 3) {c : G}
    (hcB : c ∈ B) (hcN : c ∉ N) (hc3 : c ^ 3 = 1) {b : G} (hb : b ∈ B) :
    b ∈ N ∨ c⁻¹ * b ∈ N ∨ (c ^ 2)⁻¹ * b ∈ N := by
  classical
  have hQ : Nat.card (↥B ⧸ N.subgroupOf B) = 3 := hidx
  have : Finite (↥B ⧸ N.subgroupOf B) := Nat.finite_of_card_ne_zero (by rw [hQ]; norm_num)
  have : Fintype (↥B ⧸ N.subgroupOf B) := Fintype.ofFinite _
  have key : ∀ x y : B, (QuotientGroup.mk x : ↥B ⧸ N.subgroupOf B) = QuotientGroup.mk y ↔
      (x : G)⁻¹ * y ∈ N := fun x y => by
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    rfl
  set x0 : ↥B ⧸ N.subgroupOf B := QuotientGroup.mk (1 : B)
  set x1 : ↥B ⧸ N.subgroupOf B := QuotientGroup.mk ⟨c, hcB⟩
  set x2 : ↥B ⧸ N.subgroupOf B := QuotientGroup.mk ⟨c ^ 2, B.pow_mem hcB 2⟩
  have h01 : x0 ≠ x1 := fun h => hcN (by simpa using (key _ _).1 h)
  have h02 : x0 ≠ x2 := fun h => hcN ((pow_two_mem_iff_of_pow_three hc3).1
    (by simpa using (key _ _).1 h))
  have h12 : x1 ≠ x2 := fun h => hcN (by
    have e : c⁻¹ * c ^ 2 = c := by group
    simpa [e] using (key _ _).1 h)
  have huniv : ({x0, x1, x2} : Finset (↥B ⧸ N.subgroupOf B)) = Finset.univ := by
    refine Finset.eq_univ_of_card _ ?_
    rw [Finset.card_insert_of_notMem (by simp [h01, h02]),
      Finset.card_pair_eq_two_iff.2 h12, ← Nat.card_eq_fintype_card, hQ]
  have hmem : (QuotientGroup.mk ⟨b, hb⟩ : ↥B ⧸ N.subgroupOf B) ∈
      ({x0, x1, x2} : Finset (↥B ⧸ N.subgroupOf B)) := by
    rw [huniv]
    exact Finset.mem_univ _
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h
  · left
    simpa using (key _ _).1 h.symm
  · exact Or.inr (Or.inl ((key _ _).1 h.symm))
  · exact Or.inr (Or.inr ((key _ _).1 h.symm))

theorem exists_mem_not_mem_of_relIndex_eq_three {B N N' : Subgroup G} (hN : N ≤ B)
    (hidx : N.relIndex B = 3) (hidx' : N'.relIndex B = 3) (hcube : ∀ g ∈ B, g ^ 3 = 1)
    (hne : N' ≠ N) : ∃ c ∈ N', c ∉ N := by
  by_contra hcon
  push Not at hcon
  have hle : N' ≤ N := hcon
  obtain ⟨c, hcN, hcN'⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne hle hne)
  have hcB : c ∈ B := hN hcN
  have hBN : B ≤ N := by
    intro b hb
    rcases mem_or_of_relIndex_eq_three hidx' hcB hcN' (hcube c hcB) hb with h | h | h
    · exact hle h
    · have e : b = c * (c⁻¹ * b) := by group
      rw [e]
      exact N.mul_mem hcN (hle h)
    · have e : b = c ^ 2 * ((c ^ 2)⁻¹ * b) := by group
      rw [e]
      exact N.mul_mem (N.pow_mem hcN 2) (hle h)
  have h1 : N.relIndex B = 1 := Subgroup.relIndex_eq_one.2 hBN
  omega

end IndexThree

theorem mem_inf_fixingSubgroup_iff {B : Subgroup (V ≃ₗ[ZMod 2] V)} {U : Submodule (ZMod 2) V}
    {g : V ≃ₗ[ZMod 2] V} :
    g ∈ B ⊓ fixingSubgroup (V ≃ₗ[ZMod 2] V) (U : Set V) ↔ g ∈ B ∧ ∀ u ∈ U, g u = u := by
  rw [Subgroup.mem_inf, mem_fixingSubgroup_iff]
  rfl

theorem relIndex_inf_fixingSubgroup_eq_three {B : Subgroup (V ≃ₗ[ZMod 2] V)} [Finite B]
    (hcomm : ∀ g ∈ B, ∀ h ∈ B, g * h = h * g) (hcube : ∀ g ∈ B, g ^ 3 = 1)
    {U : Submodule (ZMod 2) V} (hUinv : ∀ g ∈ B, ∀ u ∈ U, g u ∈ U) (hU0 : U ≠ ⊥)
    (hmin : ∀ U' : Submodule (ZMod 2) V, U' ≤ U → (∀ g ∈ B, ∀ u ∈ U', g u ∈ U') →
      U' = ⊥ ∨ U' = U)
    (hfix : ∀ u ∈ U, (∀ g ∈ B, g u = u) → u = 0) :
    (B ⊓ fixingSubgroup (V ≃ₗ[ZMod 2] V) (U : Set V)).relIndex B = 3 := by
  classical
  set K := B ⊓ fixingSubgroup (V ≃ₗ[ZMod 2] V) (U : Set V) with hKdef
  have hKmem : ∀ g, g ∈ K ↔ g ∈ B ∧ ∀ u ∈ U, g u = u := fun g => mem_inf_fixingSubgroup_iff
  have hcommute : ∀ g ∈ B, ∀ k ∈ B, ∀ v, g (k v) = k (g v) := fun g hg k hk v => by
    rw [← LinearEquiv.mul_apply, hcomm g hg k hk, LinearEquiv.mul_apply]
  have hker_inv : ∀ φ : V →ₗ[ZMod 2] V, (∀ k ∈ B, ∀ v, φ (k v) = k (φ v)) →
      ∀ k ∈ B, ∀ u ∈ U ⊓ LinearMap.ker φ, k u ∈ U ⊓ LinearMap.ker φ := by
    intro φ hφ k hk u hu
    rw [Submodule.mem_inf] at hu ⊢
    refine ⟨hUinv k hk u hu.1, ?_⟩
    rw [LinearMap.mem_ker, hφ k hk, LinearMap.mem_ker.1 hu.2, map_zero]
  have hcube_apply : ∀ g ∈ B, ∀ v, g (g (g v)) = v := fun g hg v => by
    rw [← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, ← pow_three', hcube g hg]
    rfl
  obtain ⟨g, hgB, hgK⟩ : ∃ g ∈ B, g ∉ K := by
    by_contra hcon
    push Not at hcon
    apply hU0
    rw [eq_bot_iff]
    intro u hu
    rw [Submodule.mem_bot]
    exact hfix u hu fun k hk => ((hKmem k).1 (hcon k hk)).2 u hu
  have hsum0 : ∀ h ∈ B, h ∉ K → ∀ u ∈ U, u + h u + h (h u) = 0 := by
    intro h hhB hhK u hu
    have hC : U ⊓ LinearMap.ker ((h : V →ₗ[ZMod 2] V) - LinearMap.id) = ⊥ := by
      rcases hmin (U ⊓ LinearMap.ker ((h : V →ₗ[ZMod 2] V) - LinearMap.id)) inf_le_left
        (hker_inv _ fun k hk v => by
          simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply, map_sub]
          rw [hcommute h hhB k hk]) with h0 | h1
      · exact h0
      · exfalso
        apply hhK
        refine (hKmem h).2 ⟨hhB, fun u hu => ?_⟩
        have hu' : u ∈ U ⊓ LinearMap.ker ((h : V →ₗ[ZMod 2] V) - LinearMap.id) := by
          rw [h1]
          exact hu
        have h2 := LinearMap.mem_ker.1 (Submodule.mem_inf.1 hu').2
        simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply] at h2
        exact sub_eq_zero.1 h2
    have hmem : u + h u + h (h u) ∈
        U ⊓ LinearMap.ker ((h : V →ₗ[ZMod 2] V) - LinearMap.id) := by
      refine Submodule.mem_inf.2
        ⟨add_mem (add_mem hu (hUinv h hhB u hu)) (hUinv h hhB _ (hUinv h hhB u hu)), ?_⟩
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply,
        map_add, map_add, hcube_apply h hhB]
      abel
    rw [hC, Submodule.mem_bot] at hmem
    exact hmem
  have hgsum := hsum0 g hgB hgK
  have hcases : ∀ h ∈ B, h ∉ K → (∀ u ∈ U, h u = g u) ∨ ∀ u ∈ U, h u = g (g u) := by
    intro h hhB hhK
    have hhsum := hsum0 h hhB hhK
    rcases hmin (U ⊓ LinearMap.ker ((h : V →ₗ[ZMod 2] V) - (g : V →ₗ[ZMod 2] V)))
        inf_le_left (hker_inv ((h : V →ₗ[ZMod 2] V) - (g : V →ₗ[ZMod 2] V)) fun k hk v => by
          simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, map_sub]
          rw [hcommute h hhB k hk, hcommute g hgB k hk]) with h0 | h1
    · right
      intro u hu
      have hhu := hUinv h hhB u hu
      have e1 : h (h u) = u + h u := by
        have := hhsum u hu
        rw [add_eq_zero_iff_eq_neg, zmod2_vec_neg] at this
        exact this.symm
      have e2 : g (g (h u)) = h u + g (h u) := by
        have := hgsum (h u) hhu
        rw [add_eq_zero_iff_eq_neg, zmod2_vec_neg] at this
        exact this.symm
      have e3 : h (g (g u)) = g (g (h u)) := by
        rw [hcommute h hhB g hgB, hcommute h hhB g hgB]
      have hw : h u + g (g u) ∈
          U ⊓ LinearMap.ker ((h : V →ₗ[ZMod 2] V) - (g : V →ₗ[ZMod 2] V)) := by
        refine Submodule.mem_inf.2 ⟨add_mem hhu (hUinv g hgB _ (hUinv g hgB u hu)), ?_⟩
        rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe,
          sub_eq_zero, map_add, map_add, e1, e3, e2, hcube_apply g hgB,
          show u + h u + (h u + g (h u)) = u + g (h u) + (h u + h u) by abel,
          zmod2_vec_add_self, add_zero, add_comm]
      rw [h0, Submodule.mem_bot, add_eq_zero_iff_eq_neg, zmod2_vec_neg] at hw
      exact hw
    · left
      intro u hu
      have hu' : u ∈ U ⊓ LinearMap.ker ((h : V →ₗ[ZMod 2] V) - (g : V →ₗ[ZMod 2] V)) := by
        rw [h1]
        exact hu
      have h2 := LinearMap.mem_ker.1 (Submodule.mem_inf.1 hu').2
      rw [LinearMap.sub_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe] at h2
      exact sub_eq_zero.1 h2
  have hinv_apply : ∀ (x : V ≃ₗ[ZMod 2] V) (v : V), x⁻¹ (x v) = v := fun x v => by
    rw [← LinearEquiv.mul_apply, inv_mul_cancel]
    rfl
  have hcover : ∀ b ∈ B, b ∈ K ∨ g⁻¹ * b ∈ K ∨ (g ^ 2)⁻¹ * b ∈ K := by
    intro b hb
    by_cases hbK : b ∈ K
    · exact Or.inl hbK
    rcases hcases b hb hbK with h | h
    · refine Or.inr (Or.inl ((hKmem _).2 ⟨B.mul_mem (B.inv_mem hgB) hb, fun u hu => ?_⟩))
      rw [LinearEquiv.mul_apply, h u hu, hinv_apply]
    · refine Or.inr (Or.inr ((hKmem _).2
        ⟨B.mul_mem (B.inv_mem (B.pow_mem hgB 2)) hb, fun u hu => ?_⟩))
      rw [LinearEquiv.mul_apply, h u hu, ← LinearEquiv.mul_apply g g, ← pow_two, hinv_apply]
  have hgK2 : g ^ 2 ∉ K := fun h => hgK ((pow_two_mem_iff_of_pow_three (hcube g hgB)).1 h)
  have key : ∀ x y : B, (QuotientGroup.mk x : ↥B ⧸ K.subgroupOf B) = QuotientGroup.mk y ↔
      (x : V ≃ₗ[ZMod 2] V)⁻¹ * y ∈ K := fun x y => by
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    rfl
  have : Fintype (↥B ⧸ K.subgroupOf B) := Fintype.ofFinite _
  set x0 : ↥B ⧸ K.subgroupOf B := QuotientGroup.mk (1 : B)
  set x1 : ↥B ⧸ K.subgroupOf B := QuotientGroup.mk ⟨g, hgB⟩
  set x2 : ↥B ⧸ K.subgroupOf B := QuotientGroup.mk ⟨g ^ 2, B.pow_mem hgB 2⟩
  have h01 : x0 ≠ x1 := fun h => hgK (by simpa using (key _ _).1 h)
  have h02 : x0 ≠ x2 := fun h => hgK2 (by simpa using (key _ _).1 h)
  have h12 : x1 ≠ x2 := fun h => hgK (by
    have e : g⁻¹ * g ^ 2 = g := by group
    simpa [e] using (key _ _).1 h)
  have huniv : (Finset.univ : Finset (↥B ⧸ K.subgroupOf B)) = {x0, x1, x2} := by
    ext y
    simp only [Finset.mem_univ, true_iff, Finset.mem_insert, Finset.mem_singleton]
    obtain ⟨⟨b, hb⟩, rfl⟩ := QuotientGroup.mk_surjective y
    rcases hcover b hb with h | h | h
    · exact Or.inl ((key _ _).2 (by simpa using h)).symm
    · exact Or.inr (Or.inl ((key _ _).2 h).symm)
    · exact Or.inr (Or.inr ((key _ _).2 h).symm)
  rw [Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card, ← Finset.card_univ, huniv,
    Finset.card_insert_of_notMem (by simp [h01, h02]), Finset.card_pair_eq_two_iff.2 h12]

theorem exists_minimal_invariant [FiniteDimensional (ZMod 2) V]
    {B : Subgroup (V ≃ₗ[ZMod 2] V)} {R : Submodule (ZMod 2) V}
    (hRinv : ∀ g ∈ B, ∀ v ∈ R, g v ∈ R) (hR0 : R ≠ ⊥) :
    ∃ U ≤ R, U ≠ ⊥ ∧ (∀ g ∈ B, ∀ u ∈ U, g u ∈ U) ∧
      ∀ U' : Submodule (ZMod 2) V, U' ≤ U → (∀ g ∈ B, ∀ u ∈ U', g u ∈ U') →
        U' = ⊥ ∨ U' = U := by
  classical
  have hex : ∃ n, ∃ U : Submodule (ZMod 2) V, U ≤ R ∧ U ≠ ⊥ ∧
      (∀ g ∈ B, ∀ u ∈ U, g u ∈ U) ∧ finrank (ZMod 2) U = n :=
    ⟨_, R, le_rfl, hR0, hRinv, rfl⟩
  obtain ⟨U, hUR, hU0, hUinv, hUn⟩ := Nat.find_spec hex
  refine ⟨U, hUR, hU0, hUinv, fun U' hU'U hU'inv => ?_⟩
  by_cases h : U' = ⊥
  · exact Or.inl h
  · refine Or.inr (Submodule.eq_of_le_of_finrank_le hU'U ?_)
    rw [hUn]
    by_contra hlt
    push Not at hlt
    exact Nat.find_min hex hlt ⟨U', hU'U.trans hUR, h, hU'inv, rfl⟩

structure KernelBlockHyp (q : QuadraticForm (ZMod 2) V) (B : Subgroup (V ≃ₗ[ZMod 2] V)) :
    Prop where
  comm : ∀ g ∈ B, ∀ h ∈ B, g * h = h * g
  cube : ∀ g ∈ B, g ^ 3 = 1
  odd : ∀ N ≤ B, Odd (Nat.card N)
  orth : B ≤ orthogonalGroup q
  fix : fixedSub B = ⊥

namespace KernelBlockHyp

variable {q : QuadraticForm (ZMod 2) V} {B : Subgroup (V ≃ₗ[ZMod 2] V)}

theorem apply_comm (hB : KernelBlockHyp q B) {g h : V ≃ₗ[ZMod 2] V} (hg : g ∈ B) (hh : h ∈ B)
    (v : V) : g (h v) = h (g v) := by
  rw [← LinearEquiv.mul_apply, hB.comm g hg h hh, LinearEquiv.mul_apply]

theorem apply_mem_fixedSub (hB : KernelBlockHyp q B) {N : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hNB : N ≤ B) {g : V ≃ₗ[ZMod 2] V} (hg : g ∈ B) {v : V} (hv : v ∈ fixedSub N) :
    g v ∈ fixedSub N := fun n hn => by
  rw [hB.apply_comm (hNB hn) hg, hv n hn]

theorem eq_zero_of_fixed (hB : KernelBlockHyp q B) {N : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hidx : N.relIndex B = 3) {c : V ≃ₗ[ZMod 2] V} (hcB : c ∈ B) (hcN : c ∉ N) {v : V}
    (hv : v ∈ fixedSub N) (hcv : c v = v) : v = 0 := by
  have hvB : v ∈ fixedSub B := by
    intro b hb
    rcases mem_or_of_relIndex_eq_three hidx hcB hcN (hB.cube c hcB) hb with h | h | h
    · exact hv b h
    · have e : b = c * (c⁻¹ * b) := by group
      rw [e, LinearEquiv.mul_apply, hv _ h, hcv]
    · have e : b = c ^ 2 * ((c ^ 2)⁻¹ * b) := by group
      rw [e, LinearEquiv.mul_apply, hv _ h, pow_two, LinearEquiv.mul_apply, hcv, hcv]
  rw [hB.fix] at hvB
  exact (Submodule.mem_bot _).1 hvB

theorem add_add_eq_zero (hB : KernelBlockHyp q B) {N : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hNB : N ≤ B) (hidx : N.relIndex B = 3) {c : V ≃ₗ[ZMod 2] V} (hcB : c ∈ B) (hcN : c ∉ N)
    {v : V} (hv : v ∈ fixedSub N) : v + c v + c (c v) = 0 := by
  have hc3 : c (c (c v)) = v := by
    rw [← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, ← pow_three', hB.cube c hcB]
    rfl
  refine hB.eq_zero_of_fixed hidx hcB hcN ?_ ?_
  · exact add_mem (add_mem hv (hB.apply_mem_fixedSub hNB hcB hv))
      (hB.apply_mem_fixedSub hNB hcB (hB.apply_mem_fixedSub hNB hcB hv))
  · rw [map_add, map_add, hc3]
    abel

section Proj

variable [FiniteDimensional (ZMod 2) V]

theorem finite_subgroup (N : Subgroup (V ≃ₗ[ZMod 2] V)) : Finite N := by
  have := finite_linearEquiv_zmod2 (V := V)
  infer_instance

attribute [local instance] finite_subgroup

theorem avgMap_eq_self (hB : KernelBlockHyp q B) {N : Subgroup (V ≃ₗ[ZMod 2] V)} (hNB : N ≤ B)
    {v : V} (hv : v ∈ fixedSub N) : avgMap N v = v :=
  avgMap_apply_of_mem (hB.odd N hNB) hv

theorem apply_avgMap_comm (hB : KernelBlockHyp q B) {N : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hNB : N ≤ B) {g : V ≃ₗ[ZMod 2] V} (hg : g ∈ B) (v : V) :
    g (avgMap N v) = avgMap N (g v) :=
  avgMap_comm (fun n hn => hB.comm g hg n (hNB hn)) v

theorem avgMap_eq_zero (hB : KernelBlockHyp q B) {N N' : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hNB : N ≤ B) (hidx : N.relIndex B = 3) (hN'B : N' ≤ B) (hidx' : N'.relIndex B = 3)
    (hne : N' ≠ N) {v : V} (hv : v ∈ fixedSub N') : avgMap N v = 0 := by
  obtain ⟨c, hcN', hcN⟩ := exists_mem_not_mem_of_relIndex_eq_three hNB hidx hidx' hB.cube hne
  refine hB.eq_zero_of_fixed hidx (hN'B hcN') hcN (avgMap_mem_fixedSub v) ?_
  rw [hB.apply_avgMap_comm hNB (hN'B hcN'), hv c hcN']

theorem eq_sum_avgMap (hB : KernelBlockHyp q B) (J : Finset (Subgroup (V ≃ₗ[ZMod 2] V)))
    (hJ : ∀ N, N ∈ J ↔ N ≤ B ∧ N.relIndex B = 3) (v : V) : v = ∑ N ∈ J, avgMap N v := by
  classical
  have : Finite B := finite_subgroup B
  set R : Submodule (ZMod 2) V := ⨅ N ∈ J, LinearMap.ker (avgMap N) with hRdef
  have hmemR : ∀ x, x ∈ R ↔ ∀ N ∈ J, avgMap N x = 0 := by
    intro x
    simp only [hRdef, Submodule.mem_iInf, LinearMap.mem_ker]
  have hRinv : ∀ g ∈ B, ∀ x ∈ R, g x ∈ R := by
    intro g hg x hx
    rw [hmemR] at hx ⊢
    intro N hN
    rw [← hB.apply_avgMap_comm ((hJ N).1 hN).1 hg, hx N hN, map_zero]
  have hRN : ∀ N ∈ J, ∀ x ∈ R, x ∈ fixedSub N → x = 0 := by
    intro N hN x hx hxN
    rw [← hB.avgMap_eq_self ((hJ N).1 hN).1 hxN]
    exact (hmemR x).1 hx N hN
  have hR : R = ⊥ := by
    by_contra hR0
    obtain ⟨U, hUR, hU0, hUinv, hmin⟩ := exists_minimal_invariant hRinv hR0
    have hfixU : ∀ u ∈ U, (∀ g ∈ B, g u = u) → u = 0 := fun u _ hu => by
      have h1 : u ∈ fixedSub B := hu
      rw [hB.fix] at h1
      exact (Submodule.mem_bot _).1 h1
    have hK := relIndex_inf_fixingSubgroup_eq_three hB.comm hB.cube hUinv hU0 hmin hfixU
    have hKJ : B ⊓ fixingSubgroup (V ≃ₗ[ZMod 2] V) (U : Set V) ∈ J := (hJ _).2 ⟨inf_le_left, hK⟩
    apply hU0
    rw [eq_bot_iff]
    intro u hu
    rw [Submodule.mem_bot]
    exact hRN _ hKJ u (hUR hu) fun k hk => (mem_inf_fixingSubgroup_iff.1 hk).2 u hu
  have hrem : v - ∑ N ∈ J, avgMap N v ∈ R := by
    rw [hmemR]
    intro N hN
    obtain ⟨hNB, hidx⟩ := (hJ N).1 hN
    rw [map_sub, map_sum, Finset.sum_eq_single N, hB.avgMap_eq_self hNB (avgMap_mem_fixedSub v),
      sub_self]
    · intro N' hN' hne
      obtain ⟨hN'B, hidx'⟩ := (hJ N').1 hN'
      exact hB.avgMap_eq_zero hNB hidx hN'B hidx' hne (avgMap_mem_fixedSub v)
    · exact fun h => absurd hN h
  rw [hR, Submodule.mem_bot, sub_eq_zero] at hrem
  exact hrem

end Proj

end KernelBlockHyp

theorem zmod2_aniso : ∀ a b : ZMod 2, a * a + b * b + a * b = 0 → a = 0 ∧ b = 0 := by decide

theorem exists_planes [FiniteDimensional (ZMod 2) V] {q : QuadraticForm (ZMod 2) V}
    {c : V ≃ₗ[ZMod 2] V} (hc : c ∈ orthogonalGroup q) :
    ∀ (n : ℕ) (X : Submodule (ZMod 2) V), finrank (ZMod 2) X = n →
      (∀ x ∈ X, c x ∈ X) → (∀ x ∈ X, x + c x + c (c x) = 0) →
      (∀ x ∈ X, (∀ y ∈ X, polar q x y = 0) → x = 0) →
      ∃ (k : ℕ) (P : Fin k → Submodule (ZMod 2) V), finrank (ZMod 2) X = 2 * k ∧
        (∀ i, P i ≤ X ∧ finrank (ZMod 2) (P i) = 2 ∧ (∀ x ∈ P i, q x = 0 → x = 0) ∧
          (∀ x ∈ P i, (∀ y ∈ P i, polar q x y = 0) → x = 0) ∧ ∀ x ∈ P i, c x ∈ P i) ∧
        (∀ i j, i ≠ j → ∀ x ∈ P i, ∀ y ∈ P j, polar q x y = 0) ∧
        ⨆ i, P i = X := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro X hXn hcX hsum hnd
  have hqc := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1 hc
  by_cases hX0 : X = ⊥
  · refine ⟨0, Fin.elim0, ?_, fun i => i.elim0, fun i => i.elim0, ?_⟩
    · rw [hX0, finrank_bot]
    · rw [iSup_of_empty, hX0]
  obtain ⟨v, hvX, hqv⟩ : ∃ v ∈ X, q v = 1 := by
    by_contra hcon
    push Not at hcon
    apply hX0
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_bot]
    refine hnd x hx fun y hy => ?_
    have h0 : ∀ z ∈ X, q z = 0 := fun z hz => (zmod2_eq_zero_or_one _).resolve_right (hcon z hz)
    rw [polar, h0 _ (add_mem hx hy), h0 x hx, h0 y hy, sub_zero, sub_zero]
  obtain ⟨w, hcv⟩ : ∃ w, c v = w := ⟨_, rfl⟩
  have hwX : w ∈ X := hcv ▸ hcX v hvX
  have hqw : q w = 1 := by rw [← hcv, hqc, hqv]
  have hcw : c w = v + w := by
    have h := hsum v hvX
    rw [hcv, add_eq_zero_iff_eq_neg, zmod2_vec_neg] at h
    exact h.symm
  have hqvw : q (v + w) = 1 := by rw [← hcw, hqc, hqw]
  have hvw : polar q v w = 1 := by
    rw [polar, hqvw, hqv, hqw]
    decide
  have hwv : polar q w v = 1 := by rw [polar_comm, hvw]
  have hvv : polar q v v = 0 := zmod2_polar_self q v
  have hww : polar q w w = 0 := zmod2_polar_self q w
  have hv0 : v ≠ 0 := fun h => by
    rw [h, QuadraticMap.map_zero] at hqv
    exact zero_ne_one hqv
  have hli : LinearIndependent (ZMod 2) ![v, w] := linearIndependent_pair_of_polar q hv0 hvv hvw
  set P := Submodule.span (ZMod 2) {v, w} with hPdef
  have hvP : v ∈ P := Submodule.subset_span (by simp)
  have hwP : w ∈ P := Submodule.subset_span (by simp)
  have hPdim : finrank (ZMod 2) P = 2 := finrank_span_pair hli
  have hPX : P ≤ X := by
    rw [hPdef, Submodule.span_le]
    rintro z (rfl | rfl)
    · exact hvX
    · exact hwX
  have hPaniso : ∀ x ∈ P, q x = 0 → x = 0 := by
    intro x hx hqx
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hx
    rw [q_add, QuadraticMap.map_smul, QuadraticMap.map_smul, polar_smul_left, polar_smul_right,
      hqv, hqw, hvw] at hqx
    simp only [smul_eq_mul, mul_one] at hqx
    obtain ⟨rfl, rfl⟩ := zmod2_aniso a b hqx
    rw [zero_smul, zero_smul, add_zero]
  have hPnd : ∀ x ∈ P, (∀ y ∈ P, polar q x y = 0) → x = 0 := by
    intro x hx hxP
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hx
    have h1 := hxP v hvP
    have h2 := hxP w hwP
    rw [polar_add_left, polar_smul_left, polar_smul_left, hvv, hwv, smul_zero, zero_add,
      smul_eq_mul, mul_one] at h1
    rw [polar_add_left, polar_smul_left, polar_smul_left, hvw, hww, smul_zero, add_zero,
      smul_eq_mul, mul_one] at h2
    rw [h1, h2, zero_smul, zero_smul, add_zero]
  have hPc : ∀ x ∈ P, c x ∈ P := by
    intro x hx
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hx
    rw [map_add, map_smul, map_smul, hcv, hcw]
    exact add_mem (Submodule.smul_mem _ _ hwP) (Submodule.smul_mem _ _ (add_mem hvP hwP))
  set X' : Submodule (ZMod 2) V := X ⊓ LinearMap.ker ((polarBilin q).flip v) ⊓
    LinearMap.ker ((polarBilin q).flip w) with hX'def
  have hmemX' : ∀ x, x ∈ X' ↔ x ∈ X ∧ polar q x v = 0 ∧ polar q x w = 0 := by
    intro x
    simp only [hX'def, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.flip_apply,
      polarBilin_apply_apply, and_assoc]
  have hdecX : ∀ x ∈ X, x - (polar q x w • v + polar q x v • w) ∈ X' := by
    intro x hx
    rw [hmemX']
    refine ⟨sub_mem hx (add_mem (Submodule.smul_mem _ _ hvX) (Submodule.smul_mem _ _ hwX)), ?_, ?_⟩
    · rw [polar_sub_left, polar_add_left, polar_smul_left, polar_smul_left, hvv, hwv, smul_zero,
        zero_add, smul_eq_mul, mul_one, sub_self]
    · rw [polar_sub_left, polar_add_left, polar_smul_left, polar_smul_left, hvw, hww, smul_zero,
        add_zero, smul_eq_mul, mul_one, sub_self]
  have hsplit : ∀ x : V, x = (polar q x w • v + polar q x v • w) +
      (x - (polar q x w • v + polar q x v • w)) := fun x => by abel
  have hX'X : X' ≤ X := fun x hx => ((hmemX' x).1 hx).1
  have hPX'orth : ∀ x ∈ P, ∀ y ∈ X', polar q x y = 0 := by
    intro x hx y hy
    obtain ⟨-, h1, h2⟩ := (hmemX' y).1 hy
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hx
    rw [polar_add_left, polar_smul_left, polar_smul_left, polar_comm _ v y, polar_comm _ w y, h1,
      h2, smul_zero, smul_zero, add_zero]
  have hPX'disj : P ⊓ X' = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxP, hxX'⟩
    rw [Submodule.mem_bot]
    exact hPnd x hxP fun y hy => by rw [polar_comm]; exact hPX'orth y hy x hxX'
  have hPX'sup : P ⊔ X' = X := by
    refine le_antisymm (sup_le hPX hX'X) fun x hx => ?_
    rw [hsplit x]
    exact Submodule.add_mem_sup (add_mem (Submodule.smul_mem _ _ hvP)
      (Submodule.smul_mem _ _ hwP)) (hdecX x hx)
  have hdimX' : finrank (ZMod 2) X' + 2 = n := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq P X'
    rw [hPX'sup, hPX'disj, finrank_bot, add_zero, hPdim, hXn] at h
    omega
  have hcvw : c (v + w) = v := by
    rw [map_add, hcv, hcw, add_left_comm, zmod2_vec_add_self, add_zero]
  have hcX' : ∀ x ∈ X', c x ∈ X' := by
    intro x hx
    obtain ⟨hxX, h1, h2⟩ := (hmemX' x).1 hx
    rw [hmemX']
    refine ⟨hcX x hxX, ?_, ?_⟩
    · rw [← hcvw, polar_map_of_mem_orthogonalGroup hc, polar_add_right, h1, h2, add_zero]
    · rw [← hcv, polar_map_of_mem_orthogonalGroup hc, h1]
  have hndX' : ∀ x ∈ X', (∀ y ∈ X', polar q x y = 0) → x = 0 := by
    intro x hx hxX'
    obtain ⟨hxX, h1, h2⟩ := (hmemX' x).1 hx
    refine hnd x hxX fun y hy => ?_
    rw [hsplit y, polar_add_right, polar_add_right, polar_smul_right, polar_smul_right, h1, h2,
      smul_zero, smul_zero, add_zero, zero_add]
    exact hxX' _ (hdecX y hy)
  obtain ⟨k, P', hdim', hP', horth', hsup'⟩ :=
    ih _ (by omega) X' rfl hcX' (fun x hx => hsum x (hX'X hx)) hndX'
  refine ⟨k + 1, Fin.cons P P', by omega, fun i => ?_, fun i j hij => ?_, ?_⟩
  · refine Fin.cases ?_ (fun j => ?_) i
    · exact ⟨hPX, hPdim, hPaniso, hPnd, hPc⟩
    · obtain ⟨h1, h2, h3, h4, h5⟩ := hP' j
      exact ⟨h1.trans hX'X, h2, h3, h4, h5⟩
  · induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => exact absurd rfl hij
      | succ j =>
        intro x hx y hy
        exact hPX'orth x hx y ((hP' j).1 hy)
    | succ i =>
      induction j using Fin.cases with
      | zero =>
        intro x hx y hy
        rw [polar_comm]
        exact hPX'orth y hy x ((hP' i).1 hx)
      | succ j =>
        intro x hx y hy
        exact horth' i j (fun h => hij (by rw [h])) x hx y hy
  · refine le_antisymm (iSup_le fun i => ?_) ?_
    · refine Fin.cases ?_ (fun j => ?_) i
      · exact hPX
      · exact ((hP' j).1).trans hX'X
    · rw [← hPX'sup, ← hsup']
      refine sup_le (le_iSup_of_le 0 le_rfl) (iSup_le fun j => le_iSup_of_le j.succ le_rfl)

theorem iSupIndep_of_polar {q : QuadraticForm (ZMod 2) V} {ι : Type*}
    {P : ι → Submodule (ZMod 2) V}
    (horth : ∀ i j, i ≠ j → ∀ x ∈ P i, ∀ y ∈ P j, polar q x y = 0)
    (hnd : ∀ i, ∀ x ∈ P i, (∀ y ∈ P i, polar q x y = 0) → x = 0) : iSupIndep P := by
  intro i
  rw [disjoint_iff, eq_bot_iff]
  rintro x ⟨hxi, hxj⟩
  rw [Submodule.mem_bot]
  have hle : ⨆ (j) (_ : j ≠ i), P j ≤
      LinearMap.BilinForm.orthogonal (polarBilin q) (P i) :=
    iSup₂_le fun j hji => fun y hy => (LinearMap.BilinForm.mem_orthogonal_iff).2 fun z hz => by
      rw [polarBilin_apply_apply]
      exact horth i j (Ne.symm hji) z hz y hy
  refine hnd i x hxi fun y hy => ?_
  have h := (LinearMap.BilinForm.mem_orthogonal_iff).1 (hle hxj) y hy
  rw [polarBilin_apply_apply, polar_comm] at h
  exact h

theorem card_relIndex_three_le {G : Type*} [Group G] {B : Subgroup G} [IsElementaryAbelian 3 B]
    {r : ℕ} (hB : Nat.card B = 3 ^ r) (S : Finset (Subgroup G))
    (hS : ∀ N ∈ S, N ≤ B ∧ N.relIndex B = 3) : S.card ≤ (3 ^ r - 1) / 2 := by
  classical
  have hfinB : Finite B := Nat.finite_of_card_ne_zero (by rw [hB]; positivity)
  have hcubeB : ∀ b : B, b ^ 3 = 1 := fun b =>
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 3 B) b
  have hψ : ∀ N ∈ S, ∃ ψ : ↥B →* Multiplicative (ZMod 3),
      (∃ b : B, ψ b ≠ 1) ∧ ∀ b : B, ψ b = 1 ↔ (b : G) ∈ N := by
    intro N hN
    obtain ⟨hNB, hidx⟩ := hS N hN
    obtain ⟨c, hcB, hcN⟩ : ∃ c ∈ B, c ∉ N := by
      by_contra hcon
      push Not at hcon
      have := Subgroup.relIndex_eq_one.2 hcon
      omega
    have hc3 : c ^ 3 = 1 := by
      have := hcubeB ⟨c, hcB⟩
      exact congrArg Subtype.val this
    have hQ : Nat.card (↥B ⧸ N.subgroupOf B) = 3 := hidx
    have key : ∀ x y : B, (QuotientGroup.mk x : ↥B ⧸ N.subgroupOf B) = QuotientGroup.mk y ↔
        (x : G)⁻¹ * y ∈ N := fun x y => by
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      rfl
    have hgen : ∀ x : ↥B ⧸ N.subgroupOf B,
        x ∈ Subgroup.zpowers (QuotientGroup.mk ⟨c, hcB⟩ : ↥B ⧸ N.subgroupOf B) := by
      intro x
      obtain ⟨⟨b, hb⟩, rfl⟩ := QuotientGroup.mk_surjective x
      rcases mem_or_of_relIndex_eq_three hidx hcB hcN hc3 hb with h | h | h
      · have e : (QuotientGroup.mk ⟨b, hb⟩ : ↥B ⧸ N.subgroupOf B) = QuotientGroup.mk 1 :=
          ((key _ _).2 (by simpa using h)).symm
        rw [e, QuotientGroup.mk_one]
        exact one_mem _
      · rw [← (key ⟨c, hcB⟩ ⟨b, hb⟩).2 h]
        exact Subgroup.mem_zpowers _
      · have e : (QuotientGroup.mk ⟨b, hb⟩ : ↥B ⧸ N.subgroupOf B) =
            QuotientGroup.mk (⟨c, hcB⟩ ^ 2) := ((key _ _).2 h).symm
        rw [e, QuotientGroup.mk_pow]
        exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 2
    let e := zmodMulEquivOfGenerator hgen hQ
    refine ⟨e.symm.toMonoidHom.comp (QuotientGroup.mk' (N.subgroupOf B)), ⟨⟨c, hcB⟩, ?_⟩,
      fun b => ?_⟩
    · intro h
      apply hcN
      have h1 : (QuotientGroup.mk ⟨c, hcB⟩ : ↥B ⧸ N.subgroupOf B) = 1 := by
        have := congrArg e h
        simpa using this
      simpa using (key 1 ⟨c, hcB⟩).1 h1.symm
    · have h1 : (e.symm.toMonoidHom.comp (QuotientGroup.mk' (N.subgroupOf B))) b = 1 ↔
          (QuotientGroup.mk b : ↥B ⧸ N.subgroupOf B) = 1 := by
        simp
      rw [h1, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  choose ψ hψne hψker using hψ
  let _ : CommGroup B := { (inferInstance : Group B) with mul_comm := fun x y => mul_comm' x y }
  let _ : Module (ZMod 3) (Additive B) := AddCommGroup.zmodModule fun x => by
    change Additive.ofMul (Additive.toMul x ^ 3) = 0
    rw [hcubeB, ofMul_one]
  have : Finite (Additive B) := hfinB
  have hdimA : finrank (ZMod 3) (Additive B) = r := by
    have h1 : Nat.card (Additive B) = Nat.card (ZMod 3) ^ finrank (ZMod 3) (Additive B) :=
      Module.natCard_eq_pow_finrank
    rw [Nat.card_zmod, show Nat.card (Additive B) = 3 ^ r from hB] at h1
    exact (Nat.pow_right_injective (by norm_num : 2 ≤ 3) h1).symm
  have : Module.Finite (ZMod 3) (Additive B) := Module.Finite.of_finite
  have : Finite (Module.Dual (ZMod 3) (Additive B)) := Module.finite_of_finite (ZMod 3)
  have hcardD : Nat.card (Module.Dual (ZMod 3) (Additive B)) = 3 ^ r := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 3) (V := Module.Dual (ZMod 3) (Additive B)),
      Subspace.dual_finrank_eq, hdimA, Nat.card_zmod]
  let φ : ∀ N ∈ S, Module.Dual (ZMod 3) (Additive B) := fun N hN =>
    (MonoidHom.toAdditiveLeft (ψ N hN)).toZModLinearMap 3
  have hφ : ∀ N hN (b : B), φ N hN (Additive.ofMul b) = Multiplicative.toAdd (ψ N hN b) :=
    fun N hN b => rfl
  have hφ0 : ∀ N hN, φ N hN ≠ 0 := by
    intro N hN h0
    obtain ⟨b, hb⟩ := hψne N hN
    apply hb
    have := LinearMap.congr_fun h0 (Additive.ofMul b)
    rw [hφ, LinearMap.zero_apply] at this
    exact toAdd_eq_zero.1 this
  have hφker : ∀ N hN (b : B), φ N hN (Additive.ofMul b) = 0 ↔ (b : G) ∈ N := by
    intro N hN b
    rw [hφ, toAdd_eq_zero, hψker]
  let F : S → ℙ (ZMod 3) (Module.Dual (ZMod 3) (Additive B)) := fun N =>
    Projectivization.mk (ZMod 3) (φ N N.2) (hφ0 N N.2)
  have hFinj : Function.Injective F := by
    rintro ⟨N, hN⟩ ⟨N', hN'⟩ h
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff _ _ _ _ _).1 h
    have hiff : ∀ b : B, (b : G) ∈ N ↔ (b : G) ∈ N' := by
      intro b
      rw [← hφker N hN b, ← hφker N' hN' b, ← ha, LinearMap.smul_apply, Units.smul_def,
        smul_eq_mul, mul_eq_zero, or_iff_right a.ne_zero]
    apply Subtype.ext
    ext x
    constructor
    · intro hx
      exact (hiff ⟨x, (hS N hN).1 hx⟩).1 hx
    · intro hx
      exact (hiff ⟨x, (hS N' hN').1 hx⟩).2 hx
  have : Finite (ℙ (ZMod 3) (Module.Dual (ZMod 3) (Additive B))) := by
    have : Fintype (Module.Dual (ZMod 3) (Additive B)) := Fintype.ofFinite _
    infer_instance
  calc S.card = Nat.card S := (Nat.card_eq_finsetCard S).symm
    _ ≤ Nat.card (ℙ (ZMod 3) (Module.Dual (ZMod 3) (Additive B))) :=
      Nat.card_le_card_of_injective F hFinj
    _ = (3 ^ r - 1) / 2 := by rw [Projectivization.card'', hcardD, Nat.card_zmod]

section QuotPi

variable {G : Type*} [Group G] {B : Subgroup G} [IsMulCommutative B]

@[expose] def quotPi (s : Finset (Subgroup G)) :
    ↥B →* ((N : s) → ↥B ⧸ (N : Subgroup G).subgroupOf B) :=
  MonoidHom.pi fun N => QuotientGroup.mk' ((N : Subgroup G).subgroupOf B)

theorem quotPi_apply (s : Finset (Subgroup G)) (b : B) (N : s) :
    quotPi (B := B) s b N = (QuotientGroup.mk b : ↥B ⧸ (N : Subgroup G).subgroupOf B) :=
  rfl

theorem ker_quotPi (s : Finset (Subgroup G)) :
    (quotPi (B := B) s).ker = (B ⊓ ⨅ N ∈ s, N).subgroupOf B := by
  ext b
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf, funext_iff]
  constructor
  · intro h
    refine ⟨b.2, Subgroup.mem_iInf.2 fun N => Subgroup.mem_iInf.2 fun hN => ?_⟩
    have h1 := h ⟨N, hN⟩
    rw [quotPi_apply, Pi.one_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
    exact h1
  · rintro ⟨-, h⟩ ⟨N, hN⟩
    rw [quotPi_apply, Pi.one_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 h N) hN

theorem card_quotPi_range_le [Finite B] (s : Finset (Subgroup G))
    (hs : ∀ N ∈ s, N.relIndex B = 3) :
    Nat.card (quotPi (B := B) s).range ≤ 3 ^ s.card := by
  calc Nat.card (quotPi (B := B) s).range ≤
        Nat.card ((N : s) → ↥B ⧸ (N : Subgroup G).subgroupOf B) :=
      Subgroup.card_le_card_group _
    _ = ∏ N : s, Nat.card (↥B ⧸ (N : Subgroup G).subgroupOf B) := Nat.card_pi
    _ = 3 ^ s.card := by
      rw [Finset.prod_congr rfl fun N _ => hs N.1 N.2, Finset.prod_const, Finset.card_univ,
        Fintype.card_coe]

theorem card_quotPi_range_eq [Finite B] (s : Finset (Subgroup G))
    (hs : ∀ N ∈ s, N.relIndex B = 3) (hsurj : Function.Surjective (quotPi (B := B) s)) :
    Nat.card (quotPi (B := B) s).range = 3 ^ s.card := by
  rw [MonoidHom.range_eq_top.2 hsurj, Subgroup.card_top, Nat.card_pi]
  rw [Finset.prod_congr rfl fun N _ => hs N.1 N.2, Finset.prod_const, Finset.card_univ,
    Fintype.card_coe]

theorem card_eq_card_inf_mul [Finite B] (s : Finset (Subgroup G)) :
    Nat.card B = Nat.card (B ⊓ ⨅ N ∈ s, N : Subgroup G) * Nat.card (quotPi (B := B) s).range := by
  have h1 := Subgroup.card_mul_index (quotPi (B := B) s).ker
  rw [Subgroup.index, Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv,
    ker_quotPi] at h1
  rw [← h1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]

end QuotPi

theorem card_mul_card_le_of_inf_eq_bot {G : Type*} [Group G] {B A T : Subgroup G} [Finite B]
    (hA : A ≤ B) (hT : T ≤ B) (h : A ⊓ T = ⊥) : Nat.card A * Nat.card T ≤ Nat.card B := by
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_injective
    (fun p => (⟨(p.1 : G) * p.2, B.mul_mem (hA p.1.2) (hT p.2.2)⟩ : B)) ?_
  rintro ⟨a, t⟩ ⟨a', t'⟩ heq
  have heq' : (a : G) * t = a' * t' := congrArg Subtype.val heq
  have h1 : (a' : G)⁻¹ * a = t' * (t : G)⁻¹ := by
    calc (a' : G)⁻¹ * a = (a' : G)⁻¹ * (a * t) * (t : G)⁻¹ := by group
      _ = (a' : G)⁻¹ * (a' * t') * (t : G)⁻¹ := by rw [heq']
      _ = t' * (t : G)⁻¹ := by group
  have h2 : (a' : G)⁻¹ * a ∈ A ⊓ T :=
    ⟨A.mul_mem (A.inv_mem a'.2) a.2, h1 ▸ T.mul_mem t'.2 (T.inv_mem t.2)⟩
  rw [h, Subgroup.mem_bot, inv_mul_eq_one] at h2
  have ha : a = a' := Subtype.ext h2.symm
  subst ha
  have ht : (t : G) = t' := mul_left_cancel heq'
  rw [Subtype.ext ht]

namespace KernelBlockHyp

variable {q : QuadraticForm (ZMod 2) V} {B : Subgroup (V ≃ₗ[ZMod 2] V)}

section Blocks

variable [FiniteDimensional (ZMod 2) V]

attribute [local instance] finite_subgroup

theorem finite_subgroups : Finite (Subgroup (V ≃ₗ[ZMod 2] V)) := by
  have := finite_linearEquiv_zmod2 (V := V)
  exact Finite.of_injective (fun H : Subgroup (V ≃ₗ[ZMod 2] V) => (H : Set (V ≃ₗ[ZMod 2] V)))
    SetLike.coe_injective

omit [FiniteDimensional (ZMod 2) V] in
theorem exists_mem_not_mem {N : Subgroup (V ≃ₗ[ZMod 2] V)} (hidx : N.relIndex B = 3) :
    ∃ c ∈ B, c ∉ N := by
  by_contra hcon
  push Not at hcon
  have := Subgroup.relIndex_eq_one.2 hcon
  omega

theorem eq_sum_avgMap_of_mem_iff (hB : KernelBlockHyp q B)
    {I : Finset (Subgroup (V ≃ₗ[ZMod 2] V))}
    (hI : ∀ N, N ∈ I ↔ N ≤ B ∧ N.relIndex B = 3 ∧ fixedSub N ≠ ⊥) (v : V) :
    v = ∑ N ∈ I, avgMap N v := by
  classical
  have := finite_subgroups (V := V)
  set J := (Set.toFinite {N : Subgroup (V ≃ₗ[ZMod 2] V) | N ≤ B ∧ N.relIndex B = 3}).toFinset
    with hJdef
  have hJ : ∀ N, N ∈ J ↔ N ≤ B ∧ N.relIndex B = 3 := fun N => by
    rw [hJdef, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  have hIJ : I = J.filter (fun N => fixedSub N ≠ ⊥) := by
    ext N
    rw [hI, Finset.mem_filter, hJ, and_assoc]
  conv_lhs => rw [hB.eq_sum_avgMap J hJ v]
  rw [hIJ, Finset.sum_filter]
  refine Finset.sum_congr rfl fun N _ => ?_
  split_ifs with h
  · rfl
  · push Not at h
    have := avgMap_mem_fixedSub (N := N) v
    rw [h, Submodule.mem_bot] at this
    exact this

theorem avgMap_eq_zero_of_mem_fixedSub (hB : KernelBlockHyp q B)
    {N A : Subgroup (V ≃ₗ[ZMod 2] V)} (hNB : N ≤ B) (hidx : N.relIndex B = 3) (hAB : A ≤ B)
    (hAN : ¬ A ≤ N) {x : V} (hx : x ∈ fixedSub A) : avgMap N x = 0 := by
  obtain ⟨a, haA, haN⟩ := IsConcreteLE.not_le_iff_exists.1 hAN
  refine hB.eq_zero_of_fixed hidx (hAB haA) haN (avgMap_mem_fixedSub x) ?_
  rw [hB.apply_avgMap_comm hNB (hAB haA), hx a haA]

theorem polar_eq_zero_of_ne (hB : KernelBlockHyp q B) {N N' : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hNB : N ≤ B) (hidx : N.relIndex B = 3) (hN'B : N' ≤ B) (hidx' : N'.relIndex B = 3)
    (hne : N' ≠ N) {x y : V} (hx : x ∈ fixedSub N) (hy : y ∈ fixedSub N') : polar q x y = 0 := by
  rw [← hB.avgMap_eq_self hNB hx, polar_avgMap (hNB.trans hB.orth),
    hB.avgMap_eq_zero hNB hidx hN'B hidx' hne hy, polar_zero_right]

theorem block_nondeg (hb : (polarBilin q).Nondegenerate) (hB : KernelBlockHyp q B)
    {N : Subgroup (V ≃ₗ[ZMod 2] V)} (hNB : N ≤ B) {x : V} (hx : x ∈ fixedSub N)
    (hxN : ∀ y ∈ fixedSub N, polar q x y = 0) : x = 0 := by
  refine hb.1 x fun v => ?_
  rw [polarBilin_apply_apply, ← hB.avgMap_eq_self hNB hx, polar_avgMap (hNB.trans hB.orth)]
  exact hxN _ (avgMap_mem_fixedSub v)

omit [FiniteDimensional (ZMod 2) V] in
theorem mem_of_fixes_block (hB : KernelBlockHyp q B) {N : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hidx : N.relIndex B = 3) (hN0 : fixedSub N ≠ ⊥) {g : V ≃ₗ[ZMod 2] V} (hg : g ∈ B)
    (hfix : ∀ v ∈ fixedSub N, g v = v) : g ∈ N := by
  by_contra hgN
  apply hN0
  rw [eq_bot_iff]
  intro v hv
  rw [Submodule.mem_bot]
  exact hB.eq_zero_of_fixed hidx hg hgN hv (hfix v hv)

omit [FiniteDimensional (ZMod 2) V] in
theorem apply_block_cases (hB : KernelBlockHyp q B) {N : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hidx : N.relIndex B = 3) {c : V ≃ₗ[ZMod 2] V} (hcB : c ∈ B) (hcN : c ∉ N)
    {b : V ≃ₗ[ZMod 2] V} (hb : b ∈ B) {x : V} (hx : x ∈ fixedSub N) :
    b x = x ∨ b x = c x ∨ b x = c (c x) := by
  rcases mem_or_of_relIndex_eq_three hidx hcB hcN (hB.cube c hcB) hb with h | h | h
  · exact Or.inl (hx b h)
  · right
    left
    have e : b = c * (c⁻¹ * b) := by group
    rw [e, LinearEquiv.mul_apply, hx _ h]
  · right
    right
    have e : b = c ^ 2 * ((c ^ 2)⁻¹ * b) := by group
    rw [e, LinearEquiv.mul_apply, hx _ h, pow_two, LinearEquiv.mul_apply]

theorem exists_block_planes (hb : (polarBilin q).Nondegenerate) (hB : KernelBlockHyp q B)
    {N : Subgroup (V ≃ₗ[ZMod 2] V)} (hNB : N ≤ B) (hidx : N.relIndex B = 3) :
    ∃ (k : ℕ) (P : Fin k → Submodule (ZMod 2) V), finrank (ZMod 2) (fixedSub N) = 2 * k ∧
      (∀ i, P i ≤ fixedSub N ∧ finrank (ZMod 2) (P i) = 2 ∧ (∀ x ∈ P i, q x = 0 → x = 0) ∧
        (∀ x ∈ P i, (∀ y ∈ P i, polar q x y = 0) → x = 0) ∧ ∀ g ∈ B, ∀ x ∈ P i, g x ∈ P i) ∧
      (∀ i j, i ≠ j → ∀ x ∈ P i, ∀ y ∈ P j, polar q x y = 0) ∧ ⨆ i, P i = fixedSub N := by
  obtain ⟨c, hcB, hcN⟩ := exists_mem_not_mem hidx
  obtain ⟨k, P, hk, hP, horth, hsup⟩ := exists_planes (hB.orth hcB) _ (fixedSub N) rfl
    (fun x hx => hB.apply_mem_fixedSub hNB hcB hx)
    (fun x hx => hB.add_add_eq_zero hNB hidx hcB hcN hx)
    (fun x hx hxN => hB.block_nondeg hb hNB hx hxN)
  refine ⟨k, P, hk, fun i => ?_, horth, hsup⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := hP i
  refine ⟨h1, h2, h3, h4, fun g hg x hx => ?_⟩
  rcases hB.apply_block_cases hidx hcB hcN hg (h1 hx) with h | h | h
  · rw [h]
    exact hx
  · rw [h]
    exact h5 x hx
  · rw [h]
    exact h5 _ (h5 x hx)

theorem iSup_blocks_eq_top (hB : KernelBlockHyp q B) {I : Finset (Subgroup (V ≃ₗ[ZMod 2] V))}
    (hI : ∀ N, N ∈ I ↔ N ≤ B ∧ N.relIndex B = 3 ∧ fixedSub N ≠ ⊥) :
    ⨆ N ∈ I, fixedSub N = ⊤ := by
  rw [eq_top_iff]
  intro v _
  rw [hB.eq_sum_avgMap_of_mem_iff hI v]
  exact Submodule.sum_mem _ fun N hN =>
    Submodule.mem_iSup_of_mem N (Submodule.mem_iSup_of_mem hN (avgMap_mem_fixedSub v))

theorem finrank_eq_sum_blocks (hB : KernelBlockHyp q B) {I : Finset (Subgroup (V ≃ₗ[ZMod 2] V))}
    (hI : ∀ N, N ∈ I ↔ N ≤ B ∧ N.relIndex B = 3 ∧ fixedSub N ≠ ⊥) :
    finrank (ZMod 2) V = ∑ N ∈ I, finrank (ZMod 2) (fixedSub N) := by
  classical
  let Ψ : V →ₗ[ZMod 2] ((N : I) → fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V))) :=
    LinearMap.pi fun N => (avgMap (N : Subgroup (V ≃ₗ[ZMod 2] V))).codRestrict
      (fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V))) fun v => avgMap_mem_fixedSub v
  have hΨ : ∀ v (N : I), (Ψ v N : V) = avgMap (N : Subgroup (V ≃ₗ[ZMod 2] V)) v :=
    fun v N => rfl
  have hinj : Function.Injective Ψ := by
    intro v w h
    have h' : ∀ N : I, avgMap (N : Subgroup (V ≃ₗ[ZMod 2] V)) v =
        avgMap (N : Subgroup (V ≃ₗ[ZMod 2] V)) w := fun N => by
      rw [← hΨ, ← hΨ, h]
    rw [hB.eq_sum_avgMap_of_mem_iff hI v, hB.eq_sum_avgMap_of_mem_iff hI w]
    exact Finset.sum_congr rfl fun N hN => h' ⟨N, hN⟩
  have hsurj : Function.Surjective Ψ := by
    intro x
    refine ⟨∑ N : I, (x N : V), funext fun N => Subtype.ext ?_⟩
    rw [hΨ, map_sum, Finset.sum_eq_single N]
    · exact hB.avgMap_eq_self ((hI N).1 N.2).1 (x N).2
    · intro N' _ hne
      obtain ⟨hNB, hidx, -⟩ := (hI N).1 N.2
      obtain ⟨hN'B, hidx', -⟩ := (hI N').1 N'.2
      exact hB.avgMap_eq_zero hNB hidx hN'B hidx' (fun h => hne (Subtype.ext h)) (x N').2
    · exact fun h => absurd (Finset.mem_univ N) h
  rw [(LinearEquiv.ofBijective Ψ ⟨hinj, hsurj⟩).finrank_eq, Module.finrank_pi_fintype]
  exact Finset.sum_coe_sort I fun N => finrank (ZMod 2) (fixedSub N)

theorem inf_blocks_eq_bot (hB : KernelBlockHyp q B) {I : Finset (Subgroup (V ≃ₗ[ZMod 2] V))}
    (hI : ∀ N, N ∈ I ↔ N ≤ B ∧ N.relIndex B = 3 ∧ fixedSub N ≠ ⊥) :
    B ⊓ ⨅ N ∈ I, N = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_inf] at hg
  rw [Subgroup.mem_bot]
  refine LinearEquiv.ext fun v => ?_
  rw [hB.eq_sum_avgMap_of_mem_iff hI v, map_sum]
  refine Finset.sum_congr rfl fun N hN => ?_
  exact avgMap_mem_fixedSub v g (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hg.2 N) hN)

open scoped Classical in
theorem fixedSub_eq_iSup (hB : KernelBlockHyp q B) {I : Finset (Subgroup (V ≃ₗ[ZMod 2] V))}
    (hI : ∀ N, N ∈ I ↔ N ≤ B ∧ N.relIndex B = 3 ∧ fixedSub N ≠ ⊥)
    {A : Subgroup (V ≃ₗ[ZMod 2] V)} (hAB : A ≤ B) :
    fixedSub A = ⨆ N ∈ I.filter (fun N => A ≤ N), fixedSub N := by
  refine le_antisymm (fun x hx => ?_) (iSup₂_le fun N hN => ?_)
  · rw [hB.eq_sum_avgMap_of_mem_iff hI x,
      ← Finset.sum_filter_add_sum_filter_not I (fun N => A ≤ N)]
    have h0 : ∑ N ∈ I.filter (fun N => ¬ A ≤ N), avgMap N x = 0 :=
      Finset.sum_eq_zero fun N hN => by
        obtain ⟨hNI, hAN⟩ := Finset.mem_filter.1 hN
        obtain ⟨hNB, hidx, -⟩ := (hI N).1 hNI
        exact hB.avgMap_eq_zero_of_mem_fixedSub hNB hidx hAB hAN hx
    rw [h0, add_zero]
    exact Submodule.sum_mem _ fun N hN =>
      Submodule.mem_iSup_of_mem N (Submodule.mem_iSup_of_mem hN (avgMap_mem_fixedSub x))
  · intro x hx a ha
    exact hx a ((Finset.mem_filter.1 hN).2 ha)

open scoped Classical in
theorem span_eq_iSup (hB : KernelBlockHyp q B) {I : Finset (Subgroup (V ≃ₗ[ZMod 2] V))}
    (hI : ∀ N, N ∈ I ↔ N ≤ B ∧ N.relIndex B = 3 ∧ fixedSub N ≠ ⊥)
    {A : Subgroup (V ≃ₗ[ZMod 2] V)} (hAB : A ≤ B) :
    Submodule.span (ZMod 2) {x | ∃ a ∈ A, ∃ v, x = a v + v} =
      ⨆ N ∈ I.filter (fun N => ¬ A ≤ N), fixedSub N := by
  refine le_antisymm ?_ (iSup₂_le fun N hN => fun y hy => ?_)
  · rw [Submodule.span_le]
    rintro _ ⟨a, ha, v, rfl⟩
    rw [SetLike.mem_coe, hB.eq_sum_avgMap_of_mem_iff hI (a v + v),
      ← Finset.sum_filter_add_sum_filter_not I (fun N => A ≤ N)]
    have h0 : ∑ N ∈ I.filter (fun N => A ≤ N), avgMap N (a v + v) = 0 :=
      Finset.sum_eq_zero fun N hN => by
        obtain ⟨hNI, hAN⟩ := Finset.mem_filter.1 hN
        obtain ⟨hNB, -, -⟩ := (hI N).1 hNI
        rw [map_add, ← hB.apply_avgMap_comm hNB (hAB ha), avgMap_mem_fixedSub v a (hAN ha),
          zmod2_vec_add_self]
    rw [h0, zero_add]
    exact Submodule.sum_mem _ fun N hN =>
      Submodule.mem_iSup_of_mem N (Submodule.mem_iSup_of_mem hN (avgMap_mem_fixedSub _))
  · obtain ⟨hNI, hAN⟩ := Finset.mem_filter.1 hN
    obtain ⟨hNB, hidx, -⟩ := (hI N).1 hNI
    obtain ⟨a, haA, haN⟩ := IsConcreteLE.not_le_iff_exists.1 hAN
    have h := hB.add_add_eq_zero hNB hidx (hAB haA) haN hy
    rw [add_assoc, add_eq_zero_iff_eq_neg, zmod2_vec_neg] at h
    have e : y = a (a y) + a y := by rw [add_comm]; exact h
    rw [e]
    exact Submodule.subset_span ⟨a, haA, a y, rfl⟩

open scoped Classical in
theorem isCompl_fixedSub_span (hB : KernelBlockHyp q B)
    {I : Finset (Subgroup (V ≃ₗ[ZMod 2] V))}
    (hI : ∀ N, N ∈ I ↔ N ≤ B ∧ N.relIndex B = 3 ∧ fixedSub N ≠ ⊥)
    {A : Subgroup (V ≃ₗ[ZMod 2] V)} (hAB : A ≤ B) :
    IsCompl (fixedSub A) (Submodule.span (ZMod 2) {x | ∃ a ∈ A, ∃ v, x = a v + v}) := by
  rw [hB.span_eq_iSup hI hAB]
  constructor
  · rw [Submodule.disjoint_def]
    intro x hxA hx'
    rw [hB.eq_sum_avgMap_of_mem_iff hI x]
    refine Finset.sum_eq_zero fun N hN => ?_
    obtain ⟨hNB, hidx, -⟩ := (hI N).1 hN
    by_cases hAN : A ≤ N
    · have hle : ⨆ N' ∈ I.filter (fun N => ¬ A ≤ N), fixedSub N' ≤
          LinearMap.ker (avgMap N) :=
        iSup₂_le fun N' hN' => fun y hy => by
          obtain ⟨hN'I, hAN'⟩ := Finset.mem_filter.1 hN'
          obtain ⟨hN'B, hidx', -⟩ := (hI N').1 hN'I
          exact hB.avgMap_eq_zero hNB hidx hN'B hidx' (fun h => hAN' (h ▸ hAN)) hy
      exact hle hx'
    · exact hB.avgMap_eq_zero_of_mem_fixedSub hNB hidx hAB hAN hxA
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    rw [hB.eq_sum_avgMap_of_mem_iff hI x,
      ← Finset.sum_filter_add_sum_filter_not I (fun N => A ≤ N)]
    refine Submodule.add_mem_sup ?_ (Submodule.sum_mem _ fun N hN =>
      Submodule.mem_iSup_of_mem N (Submodule.mem_iSup_of_mem hN (avgMap_mem_fixedSub x)))
    exact Submodule.sum_mem _ fun N hN => fun a ha =>
      avgMap_mem_fixedSub x a ((Finset.mem_filter.1 hN).2 ha)

open scoped Classical in
theorem polar_fixedSub_span (hB : KernelBlockHyp q B) {I : Finset (Subgroup (V ≃ₗ[ZMod 2] V))}
    (hI : ∀ N, N ∈ I ↔ N ≤ B ∧ N.relIndex B = 3 ∧ fixedSub N ≠ ⊥)
    {A : Subgroup (V ≃ₗ[ZMod 2] V)} (hAB : A ≤ B) {x y : V} (hx : x ∈ fixedSub A)
    (hy : y ∈ Submodule.span (ZMod 2) {x | ∃ a ∈ A, ∃ v, x = a v + v}) : polar q x y = 0 := by
  rw [hB.span_eq_iSup hI hAB] at hy
  have hle : ⨆ N ∈ I.filter (fun N => ¬ A ≤ N), fixedSub N ≤
      LinearMap.ker ((polarBilin q) x) :=
    iSup₂_le fun N hN => fun z hz => by
      obtain ⟨hNI, hAN⟩ := Finset.mem_filter.1 hN
      obtain ⟨hNB, hidx, -⟩ := (hI N).1 hNI
      rw [LinearMap.mem_ker, polarBilin_apply_apply, ← hB.avgMap_eq_self hNB hz,
        ← polar_avgMap (hNB.trans hB.orth),
        hB.avgMap_eq_zero_of_mem_fixedSub hNB hidx hAB hAN hx, polar_zero_left]
  have h := hle hy
  rw [LinearMap.mem_ker, polarBilin_apply_apply] at h
  exact h

open scoped Classical in
theorem fixes_span_iff (hB : KernelBlockHyp q B) {I : Finset (Subgroup (V ≃ₗ[ZMod 2] V))}
    (hI : ∀ N, N ∈ I ↔ N ≤ B ∧ N.relIndex B = 3 ∧ fixedSub N ≠ ⊥)
    {A : Subgroup (V ≃ₗ[ZMod 2] V)} (hAB : A ≤ B) (g : V ≃ₗ[ZMod 2] V) :
    (g ∈ B ∧ ∀ w ∈ Submodule.span (ZMod 2) {x | ∃ a ∈ A, ∃ v, x = a v + v}, g w = w) ↔
      g ∈ B ⊓ ⨅ N ∈ I.filter (fun N => ¬ A ≤ N), N := by
  rw [hB.span_eq_iSup hI hAB, Subgroup.mem_inf]
  constructor
  · rintro ⟨hg, hfix⟩
    refine ⟨hg, Subgroup.mem_iInf.2 fun N => Subgroup.mem_iInf.2 fun hN => ?_⟩
    obtain ⟨hNI, -⟩ := Finset.mem_filter.1 hN
    obtain ⟨-, hidx, hN0⟩ := (hI N).1 hNI
    exact hB.mem_of_fixes_block hidx hN0 hg fun v hv =>
      hfix v (Submodule.mem_iSup_of_mem N (Submodule.mem_iSup_of_mem hN hv))
  · rintro ⟨hg, hgT⟩
    refine ⟨hg, fun w hw => ?_⟩
    have hle : ⨆ N ∈ I.filter (fun N => ¬ A ≤ N), fixedSub N ≤
        LinearMap.ker ((g : V →ₗ[ZMod 2] V) - LinearMap.id) :=
      iSup₂_le fun N hN => fun z hz => by
        rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply,
          hz g (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hgT N) hN), sub_self]
    have h := hle hw
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply,
      sub_eq_zero] at h
    exact h

open scoped Classical in
theorem inf_inf_eq_bot (hB : KernelBlockHyp q B) {I : Finset (Subgroup (V ≃ₗ[ZMod 2] V))}
    (hI : ∀ N, N ∈ I ↔ N ≤ B ∧ N.relIndex B = 3 ∧ fixedSub N ≠ ⊥)
    {A : Subgroup (V ≃ₗ[ZMod 2] V)} (hAB : A ≤ B) :
    A ⊓ (B ⊓ ⨅ N ∈ I.filter (fun N => ¬ A ≤ N), N) = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_inf] at hg
  obtain ⟨hgA, hgT⟩ := hg
  obtain ⟨-, hgW⟩ := (hB.fixes_span_iff hI hAB g).2 hgT
  rw [Subgroup.mem_bot]
  refine LinearEquiv.ext fun v => ?_
  have hv : v ∈ fixedSub A ⊔ Submodule.span (ZMod 2) {x | ∃ a ∈ A, ∃ v, x = a v + v} := by
    rw [(hB.isCompl_fixedSub_span hI hAB).sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hv
  rw [map_add, hx g hgA, hgW y hy]
  rfl

end Blocks

theorem mem_map_conj_iff {g x : V ≃ₗ[ZMod 2] V} {N : Subgroup (V ≃ₗ[ZMod 2] V)} :
    x ∈ N.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ N := by
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨n, hn, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rwa [show g⁻¹ * (g * n * g⁻¹) * g = n by group]
  · intro h
    exact ⟨_, h, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩

theorem fixedSub_map_conj (g : V ≃ₗ[ZMod 2] V) (N : Subgroup (V ≃ₗ[ZMod 2] V)) :
    fixedSub (N.map (MulAut.conj g).toMonoidHom) = (fixedSub N).map (g : V →ₗ[ZMod 2] V) := by
  have hgg : ∀ v, g (g⁻¹ v) = v := fun v => by
    rw [← LinearEquiv.mul_apply, mul_inv_cancel]
    rfl
  have hgg' : ∀ v, g⁻¹ (g v) = v := fun v => by
    rw [← LinearEquiv.mul_apply, inv_mul_cancel]
    rfl
  have hsymm : ∀ v, g.symm v = g⁻¹ v := fun v => rfl
  ext x
  rw [Submodule.mem_map_equiv, mem_fixedSub, mem_fixedSub, hsymm]
  constructor
  · intro h n hn
    have h1 := h (g * n * g⁻¹) (mem_map_conj_iff.2 (by
      rwa [show g⁻¹ * (g * n * g⁻¹) * g = n by group]))
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply] at h1
    calc n (g⁻¹ x) = g⁻¹ (g (n (g⁻¹ x))) := (hgg' _).symm
      _ = g⁻¹ x := by rw [h1]
  · intro h μ hμ
    have h1 := h _ (mem_map_conj_iff.1 hμ)
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply] at h1
    calc μ x = g (g⁻¹ (μ (g (g⁻¹ x)))) := by rw [hgg, hgg]
      _ = x := by rw [h1, hgg]

end KernelBlockHyp

end CFSG.LinearAlgebra.SteinbergBQ

namespace CFSG.LinearAlgebra

open Module QuadraticMap SteinbergBQ
open TauCeti.QuadraticMap (orthogonalGroup)

open scoped Classical in
theorem binary_quadratic_three_action_canonical_kernel_blocks {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V] (q : QuadraticForm (ZMod 2) V)
    (hb : (polarBilin q).Nondegenerate) {m : ℕ} (hV : finrank (ZMod 2) V = 2 * m)
    (B : Subgroup (V ≃ₗ[ZMod 2] V)) [IsElementaryAbelian 3 B] (hBO : B ≤ orthogonalGroup q)
    {r : ℕ} (hBcard : Nat.card B = 3 ^ r) (hfix : fixedSub B = ⊥) :
    ∃ (I : Finset (Subgroup (V ≃ₗ[ZMod 2] V))) (d : Subgroup (V ≃ₗ[ZMod 2] V) → ℕ),
      (∀ N, N ∈ I ↔ N ≤ B ∧ N.relIndex B = 3 ∧ fixedSub N ≠ ⊥) ∧
      (iSupIndep (fun N : I => fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V))) ∧
        ⨆ N ∈ I, fixedSub N = ⊤ ∧
        ∀ N ∈ I, ∀ N' ∈ I, N ≠ N' → ∀ x ∈ fixedSub N, ∀ y ∈ fixedSub N', polar q x y = 0) ∧
      (∀ N ∈ I, (∀ x ∈ fixedSub N, (∀ y ∈ fixedSub N, polar q x y = 0) → x = 0) ∧
        finrank (ZMod 2) (fixedSub N) = 2 * d N ∧ 1 ≤ d N ∧
        ∀ g ∈ B, (∀ v ∈ fixedSub N, g v = v) ↔ g ∈ N) ∧
      ∑ N ∈ I, d N = m ∧
      B ⊓ ⨅ N ∈ I, N = ⊥ ∧
      r ≤ I.card ∧ I.card ≤ m ∧ I.card ≤ (3 ^ r - 1) / 2 ∧
      (m = 0 ↔ r = 0) ∧ (r = 0 → finrank (ZMod 2) V = 0 ∧ B = ⊥ ∧ I = ∅) ∧
      (∀ N ∈ I, ∃ P : Fin (d N) → Submodule (ZMod 2) V,
        (∀ i, P i ≤ fixedSub N ∧ finrank (ZMod 2) (P i) = 2 ∧ (∀ x ∈ P i, q x = 0 → x = 0) ∧
          ∀ g ∈ B, ∀ x ∈ P i, g x ∈ P i) ∧
        (∀ i j, i ≠ j → ∀ x ∈ P i, ∀ y ∈ P j, polar q x y = 0) ∧
        iSupIndep P ∧ ⨆ i, P i = fixedSub N) ∧
      (∀ g ∈ orthogonalGroup q, g ∈ Subgroup.normalizer (B : Set (V ≃ₗ[ZMod 2] V)) →
        Set.BijOn (fun N : Subgroup (V ≃ₗ[ZMod 2] V) => N.map (MulAut.conj g).toMonoidHom)
          (I : Set (Subgroup (V ≃ₗ[ZMod 2] V))) (I : Set (Subgroup (V ≃ₗ[ZMod 2] V))) ∧
        ∀ N ∈ I, fixedSub (N.map (MulAut.conj g).toMonoidHom) =
            (fixedSub N).map (g : V →ₗ[ZMod 2] V) ∧
          d (N.map (MulAut.conj g).toMonoidHom) = d N) ∧
      (∀ A ≤ B,
        fixedSub A = ⨆ N ∈ I.filter (fun N => A ≤ N), fixedSub N ∧
        Submodule.span (ZMod 2) {x | ∃ a ∈ A, ∃ v, x = a v + v} =
          ⨆ N ∈ I.filter (fun N => ¬ A ≤ N), fixedSub N ∧
        IsCompl (fixedSub A) (Submodule.span (ZMod 2) {x | ∃ a ∈ A, ∃ v, x = a v + v}) ∧
        (∀ x ∈ fixedSub A, ∀ y ∈ Submodule.span (ZMod 2) {x | ∃ a ∈ A, ∃ v, x = a v + v},
          polar q x y = 0) ∧
        (∀ g, (g ∈ B ∧ ∀ w ∈ Submodule.span (ZMod 2) {x | ∃ a ∈ A, ∃ v, x = a v + v},
          g w = w) ↔ g ∈ B ⊓ ⨅ N ∈ I.filter (fun N => ¬ A ≤ N), N) ∧
        A ⊓ (B ⊓ ⨅ N ∈ I.filter (fun N => ¬ A ≤ N), N) = ⊥ ∧
        ∀ a t : ℕ, Nat.card A = 3 ^ a →
          Nat.card (B ⊓ ⨅ N ∈ I.filter (fun N => ¬ A ≤ N), N :
            Subgroup (V ≃ₗ[ZMod 2] V)) = 3 ^ t →
          t ≤ r ∧ a ≤ r - t ∧ r - t ≤ (I.filter (fun N => ¬ A ≤ N)).card ∧
          (I.filter (fun N => ¬ A ≤ N)).card ≤ ∑ N ∈ I.filter (fun N => ¬ A ≤ N), d N ∧
          (∑ N ∈ I.filter (fun N => ¬ A ≤ N), d N = a → t = r - a)) ∧
      (m = r → I.card = r ∧ (∀ N ∈ I, d N = 1) ∧
        Function.Bijective (quotPi (B := B) I) ∧
        ∀ L ⊆ I, Nat.card (B ⊓ ⨅ N ∈ L, N : Subgroup (V ≃ₗ[ZMod 2] V)) = 3 ^ (r - L.card)) := by
  have hfinB : Finite B := Nat.finite_of_card_ne_zero (by rw [hBcard]; positivity)
  have hcube : ∀ g ∈ B, g ^ 3 = 1 := fun g hg => elemPow_eq_one_of_isElementaryAbelian g hg
  have hcomm : ∀ g ∈ B, ∀ h ∈ B, g * h = h * g := fun g hg h hh =>
    congrArg Subtype.val (mul_comm' (⟨g, hg⟩ : B) ⟨h, hh⟩)
  have hodd : ∀ N ≤ B, Odd (Nat.card N) := by
    intro N hNB
    have h1 : Nat.card N ∣ 3 ^ r := hBcard ▸ Subgroup.card_dvd_of_le hNB
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 h1
    rw [hj]
    exact Odd.pow (by decide)
  have hB : KernelBlockHyp q B := ⟨hcomm, hcube, hodd, hBO, hfix⟩
  have := KernelBlockHyp.finite_subgroups (V := V)
  obtain ⟨I, hI⟩ : ∃ I : Finset (Subgroup (V ≃ₗ[ZMod 2] V)),
      ∀ N, N ∈ I ↔ N ≤ B ∧ N.relIndex B = 3 ∧ fixedSub N ≠ ⊥ :=
    ⟨(Set.toFinite {N : Subgroup (V ≃ₗ[ZMod 2] V) |
      N ≤ B ∧ N.relIndex B = 3 ∧ fixedSub N ≠ ⊥}).toFinset, fun N => by
        rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]⟩
  obtain ⟨d, hd⟩ : ∃ d : Subgroup (V ≃ₗ[ZMod 2] V) → ℕ,
      ∀ N, d N = finrank (ZMod 2) (fixedSub N) / 2 := ⟨_, fun _ => rfl⟩
  have hplanes := fun N (hN : N ∈ I) =>
    hB.exists_block_planes hb ((hI N).1 hN).1 ((hI N).1 hN).2.1
  have hdN : ∀ N ∈ I, finrank (ZMod 2) (fixedSub N) = 2 * d N ∧ 1 ≤ d N := by
    intro N hN
    obtain ⟨k, P, hk, -⟩ := hplanes N hN
    have h0 : finrank (ZMod 2) (fixedSub N) ≠ 0 := fun h =>
      ((hI N).1 hN).2.2 (Submodule.finrank_eq_zero.1 h)
    rw [hd]
    omega
  have hindep : iSupIndep (fun N : I => fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V))) :=
    iSupIndep_of_polar (q := q)
      (fun N N' hne x hx y hy => hB.polar_eq_zero_of_ne ((hI N).1 N.2).1 ((hI N).1 N.2).2.1
        ((hI N').1 N'.2).1 ((hI N').1 N'.2).2.1 (fun h => hne (Subtype.ext h).symm) hx hy)
      fun N x hx hxN => hB.block_nondeg hb ((hI N).1 N.2).1 hx hxN
  have horth : ∀ N ∈ I, ∀ N' ∈ I, N ≠ N' → ∀ x ∈ fixedSub N, ∀ y ∈ fixedSub N',
      polar q x y = 0 := fun N hN N' hN' hne x hx y hy =>
    hB.polar_eq_zero_of_ne ((hI N).1 hN).1 ((hI N).1 hN).2.1 ((hI N').1 hN').1
      ((hI N').1 hN').2.1 (Ne.symm hne) hx hy
  have hblocks : ∀ N ∈ I, (∀ x ∈ fixedSub N, (∀ y ∈ fixedSub N, polar q x y = 0) → x = 0) ∧
      finrank (ZMod 2) (fixedSub N) = 2 * d N ∧ 1 ≤ d N ∧
      ∀ g ∈ B, (∀ v ∈ fixedSub N, g v = v) ↔ g ∈ N := by
    intro N hN
    obtain ⟨hNB, hidx, hN0⟩ := (hI N).1 hN
    exact ⟨fun x hx hxN => hB.block_nondeg hb hNB hx hxN, (hdN N hN).1, (hdN N hN).2,
      fun g hg => ⟨hB.mem_of_fixes_block hidx hN0 hg, fun hgN v hv => hv g hgN⟩⟩
  have hsum : ∑ N ∈ I, d N = m := by
    have h1 := hB.finrank_eq_sum_blocks hI
    rw [hV, Finset.sum_congr rfl fun N hN => (hdN N hN).1, ← Finset.mul_sum] at h1
    omega
  have hinf : B ⊓ ⨅ N ∈ I, N = ⊥ := hB.inf_blocks_eq_bot hI
  have hrI : r ≤ I.card := by
    have h1 := card_eq_card_inf_mul (B := B) I
    rw [hinf, Subgroup.card_bot, one_mul, hBcard] at h1
    have h2 := card_quotPi_range_le (B := B) I fun N hN => ((hI N).1 hN).2.1
    rw [← h1] at h2
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h2
  have hIm : I.card ≤ m := by
    rw [← hsum]
    have := Finset.card_nsmul_le_sum I d 1 fun N hN => (hdN N hN).2
    simpa using this
  have hI3 : I.card ≤ (3 ^ r - 1) / 2 :=
    card_relIndex_three_le hBcard I fun N hN => ⟨((hI N).1 hN).1, ((hI N).1 hN).2.1⟩
  have hBbot : r = 0 → B = ⊥ := fun hr =>
    Subgroup.eq_bot_of_card_eq B (by rw [hBcard, hr, pow_zero])
  have hV0 : (⊤ : Submodule (ZMod 2) V) = ⊥ ↔ m = 0 := by
    constructor
    · intro h
      have h1 := finrank_top (ZMod 2) V
      rw [h, finrank_bot] at h1
      omega
    · intro h
      exact Submodule.finrank_eq_zero.1 (by rw [finrank_top, hV, h])
  have hm0 : m = 0 ↔ r = 0 := by
    constructor
    · intro hm
      have hall : ∀ v : V, v = 0 := fun v => by
        have h1 : v ∈ (⊤ : Submodule (ZMod 2) V) := Submodule.mem_top
        rw [hV0.2 hm, Submodule.mem_bot] at h1
        exact h1
      have hB1 : B = ⊥ := by
        rw [eq_bot_iff]
        intro g _
        rw [Subgroup.mem_bot]
        exact LinearEquiv.ext fun v => by rw [hall v, map_zero, map_zero]
      rw [hB1, Subgroup.card_bot] at hBcard
      by_contra hr
      have h3 : 3 ^ 1 ≤ 3 ^ r := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.2 hr)
      omega
    · intro hr
      apply hV0.1
      rw [← hfix, hBbot hr]
      ext v
      simp only [Submodule.mem_top, true_iff]
      intro μ hμ
      rw [Subgroup.mem_bot] at hμ
      rw [hμ]
      rfl
  have hr0 : r = 0 → finrank (ZMod 2) V = 0 ∧ B = ⊥ ∧ I = ∅ := by
    intro hr
    have hm : m = 0 := hm0.2 hr
    refine ⟨by rw [hV, hm], hBbot hr, Finset.eq_empty_of_forall_notMem fun N hN => ?_⟩
    apply ((hI N).1 hN).2.2
    rw [eq_bot_iff]
    intro v _
    have h1 : v ∈ (⊤ : Submodule (ZMod 2) V) := Submodule.mem_top
    rwa [hV0.2 hm] at h1
  have hplanes' : ∀ N ∈ I, ∃ P : Fin (d N) → Submodule (ZMod 2) V,
      (∀ i, P i ≤ fixedSub N ∧ finrank (ZMod 2) (P i) = 2 ∧ (∀ x ∈ P i, q x = 0 → x = 0) ∧
        ∀ g ∈ B, ∀ x ∈ P i, g x ∈ P i) ∧
      (∀ i j, i ≠ j → ∀ x ∈ P i, ∀ y ∈ P j, polar q x y = 0) ∧
      iSupIndep P ∧ ⨆ i, P i = fixedSub N := by
    intro N hN
    obtain ⟨k, P, hk, hP, horthP, hsupP⟩ := hplanes N hN
    have hkd : d N = k := by
      rw [hd]
      omega
    rw [hkd]
    exact ⟨P, fun i => ⟨(hP i).1, (hP i).2.1, (hP i).2.2.1, (hP i).2.2.2.2⟩, horthP,
      iSupIndep_of_polar horthP fun i => (hP i).2.2.2.1, hsupP⟩
  have hconjI : ∀ g ∈ Subgroup.normalizer (B : Set (V ≃ₗ[ZMod 2] V)), ∀ N ∈ I,
      N.map (MulAut.conj g).toMonoidHom ∈ I := by
    intro g hg N hN
    obtain ⟨hNB, hidx, hN0⟩ := (hI N).1 hN
    have hBmap : B.map (MulAut.conj g).toMonoidHom = B := by
      ext x
      rw [KernelBlockHyp.mem_map_conj_iff]
      have h1 := Subgroup.mem_normalizer_iff.1
        ((Subgroup.normalizer (B : Set (V ≃ₗ[ZMod 2] V))).inv_mem hg) x
      rw [inv_inv] at h1
      exact h1.symm
    refine (hI _).2 ⟨?_, ?_, ?_⟩
    · rw [← hBmap]
      exact Subgroup.map_mono hNB
    · rw [← hBmap, Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]
      exact hidx
    · rw [KernelBlockHyp.fixedSub_map_conj]
      intro h
      apply hN0
      rw [eq_bot_iff]
      intro x hx
      have h1 : g x ∈ (fixedSub N).map (g : V →ₗ[ZMod 2] V) := Submodule.mem_map_of_mem hx
      rw [h, Submodule.mem_bot] at h1
      rw [Submodule.mem_bot]
      exact (map_eq_zero_iff g g.injective).1 h1
  have hnorm : ∀ g ∈ orthogonalGroup q, g ∈ Subgroup.normalizer (B : Set (V ≃ₗ[ZMod 2] V)) →
      Set.BijOn (fun N : Subgroup (V ≃ₗ[ZMod 2] V) => N.map (MulAut.conj g).toMonoidHom)
        (I : Set (Subgroup (V ≃ₗ[ZMod 2] V))) (I : Set (Subgroup (V ≃ₗ[ZMod 2] V))) ∧
      ∀ N ∈ I, fixedSub (N.map (MulAut.conj g).toMonoidHom) =
          (fixedSub N).map (g : V →ₗ[ZMod 2] V) ∧
        d (N.map (MulAut.conj g).toMonoidHom) = d N := by
    intro g _ hg
    refine ⟨⟨fun N hN => hconjI g hg N hN,
      fun N _ N' _ h => Subgroup.map_injective (MulAut.conj g).injective h,
      fun N' hN' => ⟨N'.map (MulAut.conj g⁻¹).toMonoidHom,
        hconjI g⁻¹ ((Subgroup.normalizer (B : Set (V ≃ₗ[ZMod 2] V))).inv_mem hg) N' hN', ?_⟩⟩,
      fun N _ => ⟨KernelBlockHyp.fixedSub_map_conj g N, ?_⟩⟩
    · change (N'.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = N'
      rw [Subgroup.map_map]
      have h1 : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom =
          MonoidHom.id _ := by
        ext x
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
          MonoidHom.id_apply]
        group
      rw [h1, Subgroup.map_id]
    · rw [hd, hd, KernelBlockHyp.fixedSub_map_conj, LinearEquiv.finrank_map_eq]
  have hAll : ∀ A ≤ B,
      fixedSub A = ⨆ N ∈ I.filter (fun N => A ≤ N), fixedSub N ∧
      Submodule.span (ZMod 2) {x | ∃ a ∈ A, ∃ v, x = a v + v} =
        ⨆ N ∈ I.filter (fun N => ¬ A ≤ N), fixedSub N ∧
      IsCompl (fixedSub A) (Submodule.span (ZMod 2) {x | ∃ a ∈ A, ∃ v, x = a v + v}) ∧
      (∀ x ∈ fixedSub A, ∀ y ∈ Submodule.span (ZMod 2) {x | ∃ a ∈ A, ∃ v, x = a v + v},
        polar q x y = 0) ∧
      (∀ g, (g ∈ B ∧ ∀ w ∈ Submodule.span (ZMod 2) {x | ∃ a ∈ A, ∃ v, x = a v + v},
        g w = w) ↔ g ∈ B ⊓ ⨅ N ∈ I.filter (fun N => ¬ A ≤ N), N) ∧
      A ⊓ (B ⊓ ⨅ N ∈ I.filter (fun N => ¬ A ≤ N), N) = ⊥ ∧
      ∀ a t : ℕ, Nat.card A = 3 ^ a →
        Nat.card (B ⊓ ⨅ N ∈ I.filter (fun N => ¬ A ≤ N), N :
          Subgroup (V ≃ₗ[ZMod 2] V)) = 3 ^ t →
        t ≤ r ∧ a ≤ r - t ∧ r - t ≤ (I.filter (fun N => ¬ A ≤ N)).card ∧
        (I.filter (fun N => ¬ A ≤ N)).card ≤ ∑ N ∈ I.filter (fun N => ¬ A ≤ N), d N ∧
        (∑ N ∈ I.filter (fun N => ¬ A ≤ N), d N = a → t = r - a) := by
    intro A hAB
    refine ⟨hB.fixedSub_eq_iSup hI hAB, hB.span_eq_iSup hI hAB, hB.isCompl_fixedSub_span hI hAB,
      fun x hx y hy => hB.polar_fixedSub_span hI hAB hx hy, hB.fixes_span_iff hI hAB,
      hB.inf_inf_eq_bot hI hAB, fun a t ha ht => ?_⟩
    have h1 := card_mul_card_le_of_inf_eq_bot hAB inf_le_left (hB.inf_inf_eq_bot hI hAB)
    rw [ha, ht, hBcard, ← pow_add] at h1
    have hat : a + t ≤ r := (Nat.pow_le_pow_iff_right (by norm_num)).1 h1
    have h2 := card_eq_card_inf_mul (B := B) (I.filter (fun N => ¬ A ≤ N))
    have h3 := card_quotPi_range_le (B := B) (I.filter (fun N => ¬ A ≤ N)) fun N hN =>
      ((hI N).1 (Finset.mem_filter.1 hN).1).2.1
    rw [hBcard, ht] at h2
    have h4 : 3 ^ r ≤ 3 ^ (t + (I.filter (fun N => ¬ A ≤ N)).card) := by
      rw [h2, pow_add]
      exact Nat.mul_le_mul_left _ h3
    have hrt := (Nat.pow_le_pow_iff_right (by norm_num)).1 h4
    have hJm : (I.filter (fun N => ¬ A ≤ N)).card ≤
        ∑ N ∈ I.filter (fun N => ¬ A ≤ N), d N := by
      have := Finset.card_nsmul_le_sum (I.filter (fun N => ¬ A ≤ N)) d 1 fun N hN =>
        (hdN N (Finset.mem_filter.1 hN).1).2
      simpa using this
    exact ⟨by omega, by omega, by omega, hJm, fun _ => by omega⟩
  have hk : m = r → I.card = r ∧ (∀ N ∈ I, d N = 1) ∧ Function.Bijective (quotPi (B := B) I) ∧
      ∀ L ⊆ I, Nat.card (B ⊓ ⨅ N ∈ L, N : Subgroup (V ≃ₗ[ZMod 2] V)) = 3 ^ (r - L.card) := by
    intro hmr
    have hIr : I.card = r := le_antisymm (hmr ▸ hIm) hrI
    have hd1 : ∀ N ∈ I, d N = 1 := by
      intro N hN
      have h1 : d N + ∑ N' ∈ I.erase N, d N' = ∑ N' ∈ I, d N' :=
        Finset.add_sum_erase I (fun N' => d N') hN
      have h2 := Finset.card_nsmul_le_sum (I.erase N) (fun N' => d N') 1 fun N' hN' =>
        (hdN N' (Finset.mem_of_mem_erase hN')).2
      rw [Finset.card_erase_of_mem hN, smul_eq_mul, mul_one] at h2
      have h3 := (hdN N hN).2
      have h4 : 0 < I.card := Finset.card_pos.2 ⟨N, hN⟩
      omega
    have hinj : Function.Injective (quotPi (B := B) I) := by
      rw [← MonoidHom.ker_eq_bot_iff, ker_quotPi, hinf, Subgroup.bot_subgroupOf]
    have hcardPi : Nat.card ((N : I) → ↥B ⧸ (N : Subgroup (V ≃ₗ[ZMod 2] V)).subgroupOf B) =
        3 ^ r := by
      rw [Nat.card_pi, Finset.prod_congr rfl fun N _ => ((hI N.1).1 N.2).2.1,
        Finset.prod_const, Finset.card_univ, Fintype.card_coe, hIr]
    have hbij : Function.Bijective (quotPi (B := B) I) :=
      hinj.bijective_of_nat_card_le (by rw [hcardPi, hBcard])
    refine ⟨hIr, hd1, hbij, fun L hLI => ?_⟩
    have hsurjL : Function.Surjective (quotPi (B := B) L) := by
      intro y
      obtain ⟨b, hb⟩ := hbij.2 fun N : I =>
        if h : (N : Subgroup (V ≃ₗ[ZMod 2] V)) ∈ L then y ⟨N, h⟩ else 1
      refine ⟨b, funext fun N => ?_⟩
      have h1 := congrFun hb ⟨N, hLI N.2⟩
      rw [quotPi_apply] at h1
      rw [quotPi_apply]
      exact h1.trans (by simp [N.2])
    have h1 := card_eq_card_inf_mul (B := B) L
    rw [card_quotPi_range_eq (B := B) L (fun N hN => ((hI N).1 (hLI hN)).2.1) hsurjL,
      hBcard] at h1
    have hLr : L.card ≤ r := hIr ▸ Finset.card_le_card hLI
    have h2 : 3 ^ r = 3 ^ (r - L.card) * 3 ^ L.card := by
      rw [← pow_add, Nat.sub_add_cancel hLr]
    rw [h2] at h1
    exact (Nat.eq_of_mul_eq_mul_right (by positivity) h1).symm
  exact ⟨I, d, hI, ⟨hindep, hB.iSup_blocks_eq_top hI, horth⟩, hblocks, hsum, hinf, hrI, hIm,
    hI3, hm0, hr0, hplanes', hnorm, hAll, hk⟩

end CFSG.LinearAlgebra
