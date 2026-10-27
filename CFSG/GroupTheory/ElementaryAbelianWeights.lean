module

public import Mathlib.LinearAlgebra.Eigenspace.Pi
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Field.ZMod

public section

open Module

namespace CFSG.GroupTheory.TwoWeights

variable {M : Type*} [AddCommGroup M] [Module (ZMod 3) M] {ι : Type*}

def IsWeightVector (f : ι → End (ZMod 3) M) (χ : ι → ZMod 3) (v : M) : Prop :=
  ∀ i, f i v = χ i • v

def eigIn (g : End (ZMod 3) M) (σ : ZMod 3) (N : Submodule (ZMod 3) M) : Submodule (ZMod 3) M :=
  N ⊓ LinearMap.ker (g - σ • 1)

theorem mem_eigIn {g : End (ZMod 3) M} {σ : ZMod 3} {N : Submodule (ZMod 3) M} {x : M} :
    x ∈ eigIn g σ N ↔ x ∈ N ∧ g x = σ • x := by
  simp [eigIn, Submodule.mem_inf, LinearMap.mem_ker, sub_eq_zero]

theorem exists_isWeightVector [Fintype ι] [DecidableEq ι] (f : ι → End (ZMod 3) M)
    (hc : ∀ i j, Commute (f i) (f j)) (hinv : ∀ i, f i * f i = 1)
    (N : Submodule (ZMod 3) M) (hN : N ≠ ⊥) (hNf : ∀ i, ∀ n ∈ N, f i n ∈ N) :
    ∃ (χ : ι → ZMod 3) (v : M), v ∈ N ∧ v ≠ 0 ∧ (∀ i, χ i = 1 ∨ χ i = -1) ∧
      IsWeightVector f χ v := by
  have key : ∀ s : Finset ι, ∀ N : Submodule (ZMod 3) M, N ≠ ⊥ → (∀ i, ∀ n ∈ N, f i n ∈ N) →
      ∃ v ∈ N, v ≠ 0 ∧ ∀ i ∈ s, ∃ ε : ZMod 3, (ε = 1 ∨ ε = -1) ∧ f i v = ε • v := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro N hN _
      obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN
      exact ⟨v, hv, hv0, by simp⟩
    | insert j s hj ih =>
      intro N hN hNf
      obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN
      have hjj : ∀ x, f j (f j x) = x := fun x => by
        rw [← Module.End.mul_apply, hinv j, Module.End.one_apply]
      have h1 : f j (v + f j v) = (1 : ZMod 3) • (v + f j v) := by
        rw [map_add, hjj, one_smul, add_comm]
      have h2 : f j (v - f j v) = (-1 : ZMod 3) • (v - f j v) := by
        rw [map_sub, hjj, neg_one_smul, neg_sub]
      have hsum : (v + f j v) + (v - f j v) = (2 : ZMod 3) • v := by
        rw [two_smul]; abel
      have hne : (v + f j v ≠ 0) ∨ (v - f j v ≠ 0) := by
        by_contra hcon
        rw [not_or, not_not, not_not] at hcon
        rw [hcon.1, hcon.2, zero_add] at hsum
        have : (2 : ZMod 3) • v = 0 := hsum.symm
        rcases smul_eq_zero.1 this with h | h
        · exact absurd h (by decide)
        · exact hv0 h
      have hinvar : ∀ (σ : ZMod 3) (i : ι), ∀ n ∈ eigIn (f j) σ N, f i n ∈ eigIn (f j) σ N := by
        intro σ i n hn
        rw [mem_eigIn] at hn ⊢
        obtain ⟨hnN, hk⟩ := hn
        refine ⟨hNf i n hnN, ?_⟩
        have hcomm : f j (f i n) = f i (f j n) := by
          rw [← Module.End.mul_apply, ← Module.End.mul_apply, (hc j i).eq]
        rw [hcomm, hk, map_smul]
      rcases hne with hne | hne
      · have hmem : v + f j v ∈ eigIn (f j) 1 N := mem_eigIn.2 ⟨N.add_mem hv (hNf j v hv), h1⟩
        have hN' : eigIn (f j) 1 N ≠ ⊥ := fun h => hne (by simpa [h] using hmem)
        obtain ⟨w, hw, hw0, hws⟩ := ih (eigIn (f j) 1 N) hN' (hinvar 1)
        rw [mem_eigIn] at hw
        refine ⟨w, hw.1, hw0, fun i hi => ?_⟩
        rcases Finset.mem_insert.1 hi with rfl | hi
        · exact ⟨1, Or.inl rfl, hw.2⟩
        · exact hws i hi
      · have hmem : v - f j v ∈ eigIn (f j) (-1) N :=
          mem_eigIn.2 ⟨N.sub_mem hv (hNf j v hv), h2⟩
        have hN' : eigIn (f j) (-1) N ≠ ⊥ := fun h => hne (by simpa [h] using hmem)
        obtain ⟨w, hw, hw0, hws⟩ := ih (eigIn (f j) (-1) N) hN' (hinvar (-1))
        rw [mem_eigIn] at hw
        refine ⟨w, hw.1, hw0, fun i hi => ?_⟩
        rcases Finset.mem_insert.1 hi with rfl | hi
        · exact ⟨-1, Or.inr rfl, hw.2⟩
        · exact hws i hi
  obtain ⟨v, hvN, hv0, hv⟩ := key Finset.univ N hN hNf
  choose! χ hχ using hv
  exact ⟨χ, v, hvN, hv0, fun i => (hχ i (Finset.mem_univ i)).1,
    fun i => (hχ i (Finset.mem_univ i)).2⟩

theorem three_pow_card_le [Finite M] {κ : Type*} [Fintype κ] (f : ι → End (ZMod 3) M)
    (hc : ∀ i j, Commute (f i) (f j)) (χ : κ → ι → ZMod 3) (hχ : Function.Injective χ)
    (v : κ → M) (hv0 : ∀ k, v k ≠ 0) (hv : ∀ k, IsWeightVector f (χ k) (v k)) :
    3 ^ Fintype.card κ ≤ Nat.card M := by
  classical
  have hmaps : ∀ (i j : ι) (φ : ZMod 3),
      Set.MapsTo (f i) ((f j).maxGenEigenspace φ) ((f j).maxGenEigenspace φ) := fun i j φ =>
    Module.End.mapsTo_maxGenEigenspace_of_comm (hc j i) φ
  have hind := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo f hmaps
  have hind' : iSupIndep (fun k : κ => ⨅ i, (f i).maxGenEigenspace (χ k i)) := hind.comp hχ
  have hmem : ∀ k : κ, v k ∈ ⨅ i, (f i).maxGenEigenspace (χ k i) := by
    intro k
    rw [Submodule.mem_iInf]
    intro i
    rw [Module.End.mem_maxGenEigenspace]
    refine ⟨1, ?_⟩
    have := hv k i
    simp [pow_one, this]
  have hli := hind'.linearIndependent _ hmem hv0
  have : Module.Finite (ZMod 3) M := Module.Finite.of_finite
  have hle := hli.fintype_card_le_finrank
  let _ : Fintype M := Fintype.ofFinite M
  have hcard := Module.card_eq_pow_finrank (K := ZMod 3) (V := M)
  rw [Nat.card_eq_fintype_card, hcard, ZMod.card]
  exact Nat.pow_le_pow_right (by norm_num) hle

section Aut

variable {A : Type*} [CommGroup A] {ι : Type*}

theorem exists_weight_element [Fintype ι] [DecidableEq ι] [Nontrivial A]
    (hA3 : ∀ a : A, a ^ 3 = 1) (φ : ι → A ≃* A) (hφc : ∀ i j a, φ i (φ j a) = φ j (φ i a))
    (hφ2 : ∀ i a, φ i (φ i a) = a) :
    ∃ a : A, a ≠ 1 ∧ ∃ w : ι → Bool, ∀ i, φ i a = if w i then a⁻¹ else a := by
  let _ : Module (ZMod 3) (Additive A) := AddCommGroup.zmodModule (n := 3) fun x => by
    apply Additive.toMul.injective
    show x.toMul ^ 3 = 1
    exact hA3 _
  let f : ι → End (ZMod 3) (Additive A) := fun i =>
    (MonoidHom.toAdditive (φ i).toMonoidHom).toZModLinearMap 3
  have hfa : ∀ i x, f i x = Additive.ofMul (φ i x.toMul) := fun i x => rfl
  have hc : ∀ i j, Commute (f i) (f j) := fun i j => LinearMap.ext fun x => by
    apply Additive.toMul.injective
    exact hφc i j x.toMul
  have hinv : ∀ i, f i * f i = 1 := fun i => LinearMap.ext fun x => by
    apply Additive.toMul.injective
    exact hφ2 i x.toMul
  obtain ⟨χ, x, -, hx0, hχ, hw⟩ := exists_isWeightVector f hc hinv ⊤ top_ne_bot
    (fun _ _ _ => trivial)
  refine ⟨x.toMul, fun h => hx0 (Additive.toMul.injective h), fun i => decide (χ i = -1),
    fun i => ?_⟩
  have h1 := congrArg Additive.toMul (hw i)
  rcases hχ i with h | h
  · rw [h, one_smul, hfa] at h1
    have hne : ¬ ((1 : ZMod 3) = -1) := by decide
    simpa [h, hne] using h1
  · rw [h, neg_one_smul, hfa] at h1
    simpa [h] using h1

theorem three_pow_le_card [Finite A] [Fintype ι] {κ : Type*} [Fintype κ]
    (hA3 : ∀ a : A, a ^ 3 = 1) (φ : ι → A ≃* A) (hφc : ∀ i j a, φ i (φ j a) = φ j (φ i a))
    (w : κ → ι → Bool) (hw : Function.Injective w) (a : κ → A) (ha1 : ∀ k, a k ≠ 1)
    (hwt : ∀ k i, φ i (a k) = if w k i then (a k)⁻¹ else a k) :
    3 ^ Fintype.card κ ≤ Nat.card A := by
  let _ : Module (ZMod 3) (Additive A) := AddCommGroup.zmodModule (n := 3) fun x => by
    apply Additive.toMul.injective
    show x.toMul ^ 3 = 1
    exact hA3 _
  let f : ι → End (ZMod 3) (Additive A) := fun i =>
    (MonoidHom.toAdditive (φ i).toMonoidHom).toZModLinearMap 3
  have hfa : ∀ i x, f i x = Additive.ofMul (φ i x.toMul) := fun i x => rfl
  have hc : ∀ i j, Commute (f i) (f j) := fun i j => LinearMap.ext fun x => by
    apply Additive.toMul.injective
    exact hφc i j x.toMul
  have hne : ¬ ((1 : ZMod 3) = -1) := by decide
  let χ : κ → ι → ZMod 3 := fun k i => if w k i then -1 else 1
  have hχ : Function.Injective χ := by
    intro k l hkl
    apply hw
    funext i
    have := congrFun hkl i
    simp only [χ] at this
    cases hk : w k i <;> cases hl : w l i <;> simp_all
  have hat := three_pow_card_le f hc χ hχ (fun k => Additive.ofMul (a k))
    (fun k h => ha1 k (Additive.ofMul.injective h)) (fun k i => by
      show f i (Additive.ofMul (a k)) = χ k i • Additive.ofMul (a k)
      rw [hfa]
      show Additive.ofMul (φ i (a k)) = _
      rw [hwt k i]
      cases hk : w k i <;> simp [χ, hk])
  simpa [Nat.card_congr (Additive.toMul : Additive A ≃ A)] using hat

end Aut

end CFSG.GroupTheory.TwoWeights
