module

public import Mathlib.LinearAlgebra.Eigenspace.Pi
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Field.ZMod

public section

open Module

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.WtP

theorem two_ne_zero' {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have h1 : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h1
  exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).1 h1)

theorem one_ne_neg_one' {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) : (1 : ZMod p) ≠ -1 := by
  intro h
  apply two_ne_zero' hp2
  calc (2 : ZMod p) = 1 + 1 := by norm_num
    _ = 1 + -1 := by rw [← h]
    _ = 0 := by simp




variable {p : ℕ} [Fact p.Prime] {M : Type*} [AddCommGroup M] [Module (ZMod p) M] {ι : Type*}

def IsWeightVector (f : ι → End (ZMod p) M) (χ : ι → ZMod p) (v : M) : Prop :=
  ∀ i, f i v = χ i • v

def eigIn (g : End (ZMod p) M) (σ : ZMod p) (N : Submodule (ZMod p) M) : Submodule (ZMod p) M :=
  N ⊓ LinearMap.ker (g - σ • 1)

theorem mem_eigIn {g : End (ZMod p) M} {σ : ZMod p} {N : Submodule (ZMod p) M} {x : M} :
    x ∈ eigIn g σ N ↔ x ∈ N ∧ g x = σ • x := by
  simp [eigIn, Submodule.mem_inf, LinearMap.mem_ker, sub_eq_zero]

theorem exists_isWeightVector (hp2 : p ≠ 2) [Fintype ι] [DecidableEq ι] (f : ι → End (ZMod p) M)
    (hc : ∀ i j, Commute (f i) (f j)) (hinv : ∀ i, f i * f i = 1)
    (N : Submodule (ZMod p) M) (hN : N ≠ ⊥) (hNf : ∀ i, ∀ n ∈ N, f i n ∈ N) :
    ∃ (χ : ι → ZMod p) (v : M), v ∈ N ∧ v ≠ 0 ∧ (∀ i, χ i = 1 ∨ χ i = -1) ∧
      IsWeightVector f χ v := by
  have key : ∀ s : Finset ι, ∀ N : Submodule (ZMod p) M, N ≠ ⊥ → (∀ i, ∀ n ∈ N, f i n ∈ N) →
      ∃ v ∈ N, v ≠ 0 ∧ ∀ i ∈ s, ∃ ε : ZMod p, (ε = 1 ∨ ε = -1) ∧ f i v = ε • v := by
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
      have h1 : f j (v + f j v) = (1 : ZMod p) • (v + f j v) := by
        rw [map_add, hjj, one_smul, add_comm]
      have h2 : f j (v - f j v) = (-1 : ZMod p) • (v - f j v) := by
        rw [map_sub, hjj, neg_one_smul, neg_sub]
      have hsum : (v + f j v) + (v - f j v) = (2 : ZMod p) • v := by
        rw [two_smul]; abel
      have hne : (v + f j v ≠ 0) ∨ (v - f j v ≠ 0) := by
        by_contra hcon
        rw [not_or, not_not, not_not] at hcon
        rw [hcon.1, hcon.2, zero_add] at hsum
        have : (2 : ZMod p) • v = 0 := hsum.symm
        rcases smul_eq_zero.1 this with h | h
        · exact absurd h (two_ne_zero' hp2)
        · exact hv0 h
      have hinvar : ∀ (σ : ZMod p) (i : ι), ∀ n ∈ eigIn (f j) σ N, f i n ∈ eigIn (f j) σ N := by
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

theorem pow_card_le [Finite M] {κ : Type*} [Fintype κ] (f : ι → End (ZMod p) M)
    (hc : ∀ i j, Commute (f i) (f j)) (χ : κ → ι → ZMod p) (hχ : Function.Injective χ)
    (v : κ → M) (hv0 : ∀ k, v k ≠ 0) (hv : ∀ k, IsWeightVector f (χ k) (v k)) :
    p ^ Fintype.card κ ≤ Nat.card M := by
  classical
  have hmaps : ∀ (i j : ι) (φ : ZMod p),
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
  have : Module.Finite (ZMod p) M := Module.Finite.of_finite
  have hle := hli.fintype_card_le_finrank
  let _ : Fintype M := Fintype.ofFinite M
  have hcard := Module.card_eq_pow_finrank (K := ZMod p) (V := M)
  rw [Nat.card_eq_fintype_card, hcard, ZMod.card]
  exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos hle

section Aut

variable {A : Type*} [CommGroup A] {ι : Type*}

theorem exists_weight_element (hp2 : p ≠ 2) [Fintype ι] [DecidableEq ι] [Nontrivial A]
    (hAp : ∀ a : A, a ^ p = 1) (φ : ι → A ≃* A) (hφc : ∀ i j a, φ i (φ j a) = φ j (φ i a))
    (hφ2 : ∀ i a, φ i (φ i a) = a) :
    ∃ a : A, a ≠ 1 ∧ ∃ w : ι → Bool, ∀ i, φ i a = if w i then a⁻¹ else a := by
  have _ : Module (ZMod p) (Additive A) := AddCommGroup.zmodModule (n := p) fun x => by
    apply Additive.toMul.injective
    show x.toMul ^ p = 1
    exact hAp _
  let f : ι → End (ZMod p) (Additive A) := fun i =>
    (MonoidHom.toAdditive (φ i).toMonoidHom).toZModLinearMap p
  have hfa : ∀ i (x : Additive A), f i x = Additive.ofMul (φ i x.toMul) := fun i x => rfl
  have hc : ∀ i j, Commute (f i) (f j) := fun i j => LinearMap.ext fun x => by
    apply Additive.toMul.injective
    exact hφc i j x.toMul
  have hinv : ∀ i, f i * f i = 1 := fun i => LinearMap.ext fun x => by
    apply Additive.toMul.injective
    exact hφ2 i x.toMul
  obtain ⟨χ, x, -, hx0, hχ, hw⟩ := exists_isWeightVector hp2 f hc hinv ⊤ top_ne_bot
    (fun _ _ _ => trivial)
  refine ⟨x.toMul, fun h => hx0 (Additive.toMul.injective h), fun i => decide (χ i = -1),
    fun i => ?_⟩
  have h1 := congrArg Additive.toMul (hw i)
  rcases hχ i with h | h
  · rw [h, one_smul, hfa] at h1
    have hne : ¬ ((1 : ZMod p) = -1) := one_ne_neg_one' hp2
    simpa [h, hne] using h1
  · rw [h, neg_one_smul, hfa] at h1
    simpa [h] using h1

theorem pow_le_card (hp2 : p ≠ 2) [Finite A] [Fintype ι] {κ : Type*} [Fintype κ]
    (hAp : ∀ a : A, a ^ p = 1) (φ : ι → A ≃* A) (hφc : ∀ i j a, φ i (φ j a) = φ j (φ i a))
    (w : κ → ι → Bool) (hw : Function.Injective w) (a : κ → A) (ha1 : ∀ k, a k ≠ 1)
    (hwt : ∀ k i, φ i (a k) = if w k i then (a k)⁻¹ else a k) :
    p ^ Fintype.card κ ≤ Nat.card A := by
  have _ : Module (ZMod p) (Additive A) := AddCommGroup.zmodModule (n := p) fun x => by
    apply Additive.toMul.injective
    show x.toMul ^ p = 1
    exact hAp _
  let f : ι → End (ZMod p) (Additive A) := fun i =>
    (MonoidHom.toAdditive (φ i).toMonoidHom).toZModLinearMap p
  have hfa : ∀ i (x : Additive A), f i x = Additive.ofMul (φ i x.toMul) := fun i x => rfl
  have hc : ∀ i j, Commute (f i) (f j) := fun i j => LinearMap.ext fun x => by
    apply Additive.toMul.injective
    exact hφc i j x.toMul
  have hne : ¬ ((1 : ZMod p) = -1) := one_ne_neg_one' hp2
  let χ : κ → ι → ZMod p := fun k i => if w k i then -1 else 1
  have hχ : Function.Injective χ := by
    intro k l hkl
    apply hw
    funext i
    have := congrFun hkl i
    simp only [χ] at this
    cases hk : w k i <;> cases hl : w l i <;> simp_all
  have hat := pow_card_le f hc χ hχ (fun k => Additive.ofMul (a k))
    (fun k h => ha1 k (Additive.ofMul.injective h)) (fun k i => by
      show f i (Additive.ofMul (a k)) = χ k i • Additive.ofMul (a k)
      rw [hfa]
      show Additive.ofMul (φ i (a k)) = _
      rw [hwt k i]
      cases hk : w k i <;> simp [χ, hk])
  simpa [Nat.card_congr (Additive.toMul : Additive A ≃ A)] using hat

end Aut

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.WtP
