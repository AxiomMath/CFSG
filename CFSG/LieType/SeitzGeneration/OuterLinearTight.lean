module

public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.LinearAlgebra.Semisimple
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty

public section

namespace CFSG.LieType.SeitzGeneration

open Polynomial Module

section Roots

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

theorem eq_one_of_pow_eq_one_of_noEigen {p : ℕ} (hp : p.Prime) (T : Module.End k V)
    (hT : T ^ p = 1) (hV : Nontrivial V)
    (hB : ∀ (v : V) (lam : k), T v = lam • v → v = 0) {ζ : k} (hζ : ζ ^ p = 1) : ζ = 1 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  by_contra hζ1
  have hord : orderOf ζ = p := orderOf_eq_prime hζ hζ1
  have hprim : IsPrimitiveRoot ζ p := hord ▸ IsPrimitiveRoot.orderOf ζ
  have hprod := Polynomial.X_pow_sub_one_eq_prod hp.pos hprim
  have hinj : ∀ S : Finset k,
      Function.Injective (aeval T (∏ ξ ∈ S, (X - C ξ) : k[X])) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro x y hxy
      simpa using hxy
    | insert ξ S hξ ih =>
      rw [Finset.prod_insert hξ, aeval_mul]
      have h1 : Function.Injective (aeval T (X - C ξ : k[X])) := by
        rw [injective_iff_map_eq_zero]
        intro x hx
        apply hB x ξ
        have : T x - ξ • x = 0 := by simpa using hx
        exact sub_eq_zero.mp this
      exact h1.comp ih
  have h := hinj (nthRootsFinset p (1 : k))
  rw [← hprod] at h
  have h0 : (aeval T (X ^ p - 1 : k[X])) = 0 := by simp [hT]
  rw [h0] at h
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  exact hv (h (by simp : (0 : Module.End k V) v = (0 : Module.End k V) 0))

end Roots

section Split

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

theorem apply_eq_of_pow_apply_eq {p : ℕ} (hp : p.Prime) (T : Module.End k V) (hT : T ^ p = 1)
    {i : ℕ} (hi0 : 0 < i) (hip : i < p) {v : V} (hv : (T ^ i) v = v) : T v = v := by
  have hcop : Nat.Coprime i p := Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr
    (Nat.not_dvd_of_pos_of_lt hi0 hip))
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
  have h1 : ∀ m : ℕ, ((T ^ i) ^ m) v = v := fun m => by
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, Module.End.mul_apply, hv, ih]
  have h2 : T ^ (i * m) = T := by
    have hdm := Nat.div_add_mod (i * m) p
    rw [hm] at hdm
    rw [← hdm, pow_add, pow_mul, hT, one_pow, one_mul, pow_one]
  calc T v = (T ^ (i * m)) v := by rw [h2]
    _ = ((T ^ i) ^ m) v := by rw [pow_mul]
    _ = v := h1 m

theorem exists_split_pair [FiniteDimensional k V] {p : ℕ} (hp : p.Prime) (hpk : (p : k) ≠ 0)
    (T : Module.End k V) (hT : T ^ p = 1) (hB : ∀ (v : V) (lam : k), T v = lam • v → v = 0)
    (hdim : p ≤ finrank k V) :
    ∃ A B : Module.End k V, A ^ p = 1 ∧ B ^ p = 1 ∧ A * B = B * A ∧ LinearMap.det A = 1 ∧
      LinearMap.det B = 1 ∧
      ∀ i j : ℕ, i < p → j < p → (∃ c : k, A ^ i * B ^ j = c • 1) → i = 0 ∧ j = 0 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hVnt : Nontrivial V := (Module.finrank_pos_iff (R := k)).mp (by have := hp.pos; omega)
  obtain ⟨e₀, he₀⟩ := exists_ne (0 : V)
  have hroots : ∀ ζ : k, ζ ^ p = 1 → ζ = 1 := fun ζ hζ =>
    eq_one_of_pow_eq_one_of_noEigen hp T hT hVnt hB hζ
  set orb : Fin p → V := fun i => (T ^ (i : ℕ)) e₀ with horb
  set Z : Submodule k V := Submodule.span k (Set.range orb) with hZ
  have hTmem : ∀ i : ℕ, i ≤ p → (T ^ i) e₀ ∈ Z := by
    intro i hi
    rcases Nat.lt_or_ge i p with hlt | hge
    · exact Submodule.subset_span ⟨⟨i, hlt⟩, rfl⟩
    · have : i = p := le_antisymm hi hge
      subst this
      rw [hT]
      exact Submodule.subset_span ⟨⟨0, hp.pos⟩, by simp [horb]⟩
  have hZinv : Z ∈ T.invtSubmodule := by
    rw [Module.End.mem_invtSubmodule, hZ, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    show T ((T ^ (i : ℕ)) e₀) ∈ Z
    rw [← Module.End.mul_apply, ← pow_succ']
    exact hTmem _ i.2
  have hsum : ∑ i : Fin p, orb i = 0 := by
    have hS : ∑ i : Fin p, orb i = ∑ i ∈ Finset.range p, (T ^ i) e₀ :=
      Fin.sum_univ_eq_sum_range (fun i => (T ^ i) e₀) p
    have hTS : T (∑ i ∈ Finset.range p, (T ^ i) e₀) = ∑ i ∈ Finset.range p, (T ^ i) e₀ := by
      rw [map_sum]
      have h1 : ∀ i : ℕ, T ((T ^ i) e₀) = (T ^ (i + 1)) e₀ := fun i => by
        rw [pow_succ', Module.End.mul_apply]
      simp only [h1]
      have h2 := Finset.sum_range_succ' (fun i => (T ^ i) e₀) p
      have h3 := Finset.sum_range_succ (fun i => (T ^ i) e₀) p
      simp only [pow_zero, Module.End.one_apply, hT] at h2 h3
      exact add_right_cancel (h2.symm.trans h3)
    rw [hS]
    exact hB _ 1 (by rw [one_smul]; exact hTS)
  have hZrank : finrank k Z < p := by
    have hnind : ¬ LinearIndependent k orb := by
      intro hind
      have := (Fintype.linearIndependent_iff.mp hind) (fun _ => 1) (by simpa using hsum)
        ⟨0, hp.pos⟩
      exact one_ne_zero this
    have h1 := finrank_range_le_card (R := k) orb
    have h2 : Set.finrank k (Set.range orb) ≠ Fintype.card (Fin p) := fun h =>
      hnind (linearIndependent_iff_card_eq_finrank_span.mpr h.symm)
    simp only [Fintype.card_fin] at h1 h2
    exact lt_of_le_of_ne h1 h2
  have hZtop : Z ≠ ⊤ := by
    intro h
    have := finrank_top k V
    rw [← h] at this
    omega
  have he₀Z : e₀ ∈ Z := by
    have := hTmem 0 (Nat.zero_le _)
    simpa using this
  have hsq : Squarefree (X ^ p - 1 : k[X]) := by
    have := (separable_X_pow_sub_C (1 : k) hpk one_ne_zero).squarefree
    simpa using this
  have hroot : aeval T (X ^ p - 1 : k[X]) = 0 := by simp [hT]
  have hsemi := Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsq hroot
  obtain ⟨Z', hZ'inv, hcompl⟩ := (Module.End.isSemisimple_iff.mp hsemi) Z hZinv
  have hZ'bot : Z' ≠ ⊥ := by
    intro h
    apply hZtop
    have := hcompl.sup_eq_top
    rwa [h, sup_bot_eq] at this
  obtain ⟨z₁, hz₁Z', hz₁⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hZ'bot
  have hdec : ∀ x : V, ∃ z ∈ Z, ∃ z' ∈ Z', x = z + z' := by
    intro x
    have hx : x ∈ Z ⊔ Z' := by rw [hcompl.sup_eq_top]; trivial
    obtain ⟨z, hz, z', hz', h⟩ := Submodule.mem_sup.mp hx
    exact ⟨z, hz, z', hz', h.symm⟩
  have hTZ : ∀ m : ℕ, ∀ z ∈ Z, (T ^ m) z ∈ Z := by
    intro m
    induction m with
    | zero => intro z hz; simpa using hz
    | succ m ih =>
      intro z hz
      rw [pow_succ', Module.End.mul_apply]
      exact (Module.End.mem_invtSubmodule T).mp hZinv (ih z hz)
  have hTZ' : ∀ m : ℕ, ∀ z ∈ Z', (T ^ m) z ∈ Z' := by
    intro m
    induction m with
    | zero => intro z hz; simpa using hz
    | succ m ih =>
      intro z hz
      rw [pow_succ', Module.End.mul_apply]
      exact (Module.End.mem_invtSubmodule T).mp hZ'inv (ih z hz)
  let π : V →ₗ[k] V := Z.subtype ∘ₗ Z.projectionOnto Z' hcompl
  have hπZ : ∀ z ∈ Z, π z = z := fun z hz => by
    have := Submodule.projectionOnto_apply_left hcompl ⟨z, hz⟩
    change ((Z.projectionOnto Z' hcompl) z : V) = z
    exact congrArg Subtype.val this
  have hπZ' : ∀ z ∈ Z', π z = 0 := fun z hz => by
    have := Submodule.projectionOnto_apply_right hcompl ⟨z, hz⟩
    change ((Z.projectionOnto Z' hcompl) z : V) = 0
    rw [show ((Z.projectionOnto Z' hcompl) z : V) = ((Z.projectionOnto Z' hcompl) z : V) from rfl]
    exact congrArg Subtype.val this
  have hπ : ∀ z ∈ Z, ∀ z' ∈ Z', π (z + z') = z := fun z hz z' hz' => by
    rw [map_add, hπZ z hz, hπZ' z' hz', add_zero]
  let A : Module.End k V := T * π + (1 - π)
  let B : Module.End k V := π + T * (1 - π)
  have hA : ∀ z ∈ Z, ∀ z' ∈ Z', A (z + z') = T z + z' := fun z hz z' hz' => by
    change T (π (z + z')) + ((z + z') - π (z + z')) = _
    rw [hπ z hz z' hz']
    abel
  have hBm : ∀ z ∈ Z, ∀ z' ∈ Z', B (z + z') = z + T z' := fun z hz z' hz' => by
    change π (z + z') + T ((z + z') - π (z + z')) = _
    rw [hπ z hz z' hz']
    congr 1
    congr 1
    abel
  have hApow : ∀ m : ℕ, ∀ z ∈ Z, ∀ z' ∈ Z', (A ^ m) (z + z') = (T ^ m) z + z' := by
    intro m
    induction m with
    | zero => intro z hz z' hz'; simp
    | succ m ih =>
      intro z hz z' hz'
      rw [pow_succ', Module.End.mul_apply, ih z hz z' hz', hA _ (hTZ m z hz) z' hz', pow_succ',
        Module.End.mul_apply]
  have hBpow : ∀ m : ℕ, ∀ z ∈ Z, ∀ z' ∈ Z', (B ^ m) (z + z') = z + (T ^ m) z' := by
    intro m
    induction m with
    | zero => intro z hz z' hz'; simp
    | succ m ih =>
      intro z hz z' hz'
      rw [pow_succ', Module.End.mul_apply, ih z hz z' hz', hBm z hz _ (hTZ' m z' hz'), pow_succ',
        Module.End.mul_apply]
  have hApT : A ^ p = 1 := LinearMap.ext fun x => by
    obtain ⟨z, hz, z', hz', rfl⟩ := hdec x
    rw [hApow p z hz z' hz', hT]
    rfl
  have hBpT : B ^ p = 1 := LinearMap.ext fun x => by
    obtain ⟨z, hz, z', hz', rfl⟩ := hdec x
    rw [hBpow p z hz z' hz', hT]
    rfl
  have hAB : A * B = B * A := LinearMap.ext fun x => by
    obtain ⟨z, hz, z', hz', rfl⟩ := hdec x
    have hTz : T z ∈ Z := by simpa using hTZ 1 z hz
    have hTz' : T z' ∈ Z' := by simpa using hTZ' 1 z' hz'
    rw [Module.End.mul_apply, Module.End.mul_apply, hBm z hz z' hz', hA z hz (T z') hTz',
      hA z hz z' hz', hBm (T z) hTz z' hz']

  have hdetA : LinearMap.det A = 1 := by
    apply hroots
    rw [← map_pow, hApT, map_one]
  have hdetB : LinearMap.det B = 1 := by
    apply hroots
    rw [← map_pow, hBpT, map_one]
  refine ⟨A, B, hApT, hBpT, hAB, hdetA, hdetB, ?_⟩
  rintro i j hi hj ⟨c, hc⟩
  have hB1 : (B ^ j) e₀ = e₀ := by
    have := hBpow j e₀ he₀Z 0 (Submodule.zero_mem _)
    simpa using this
  have hA1 : (A ^ i) e₀ = (T ^ i) e₀ := by
    have := hApow i e₀ he₀Z 0 (Submodule.zero_mem _)
    simpa using this
  have hev₀ : (T ^ i) e₀ = c • e₀ := by
    have h1 := congrArg (fun F : Module.End k V => F e₀) hc
    simp only [Module.End.mul_apply] at h1
    rw [hB1, hA1] at h1
    simpa using h1
  have hcpow : ∀ m : ℕ, ((T ^ i) ^ m) e₀ = c ^ m • e₀ := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, Module.End.mul_apply, hev₀, map_smul, ih, smul_smul, pow_succ]
      ring_nf
  have hc1 : c = 1 := by
    apply hroots
    have h1 := hcpow p
    rw [← pow_mul, mul_comm, pow_mul, hT, one_pow] at h1
    have h2 : (c ^ p - 1) • e₀ = 0 := by rw [sub_smul, one_smul, ← h1]; simp
    rcases smul_eq_zero.mp h2 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h he₀
  refine ⟨?_, ?_⟩
  · by_contra hi0
    have hfix : (T ^ i) e₀ = e₀ := by rw [hev₀, hc1, one_smul]
    have := apply_eq_of_pow_apply_eq hp T hT (Nat.pos_of_ne_zero hi0) hi hfix
    exact he₀ (hB e₀ 1 (by rw [one_smul]; exact this))
  · by_contra hj0
    have hB2 : (B ^ j) z₁ = (T ^ j) z₁ := by
      have := hBpow j 0 (Submodule.zero_mem _) z₁ hz₁Z'
      simpa using this
    have hA2 : (A ^ i) ((T ^ j) z₁) = (T ^ j) z₁ := by
      have := hApow i 0 (Submodule.zero_mem _) _ (hTZ' j z₁ hz₁Z')
      simpa using this
    have hev : (T ^ j) z₁ = c • z₁ := by
      have h1 := congrArg (fun F : Module.End k V => F z₁) hc
      simp only [Module.End.mul_apply] at h1
      rw [hB2, hA2] at h1
      simpa using h1
    have hfix : (T ^ j) z₁ = z₁ := by rw [hev, hc1, one_smul]
    have := apply_eq_of_pow_apply_eq hp T hT (Nat.pos_of_ne_zero hj0) hj hfix
    exact hz₁ (hB z₁ 1 (by rw [one_smul]; exact this))

end Split

section MatrixForm

open Matrix

variable {k : Type*} [Field k] {n : ℕ}

theorem exists_split_pair_matrix {p : ℕ} (hp : p.Prime) (hpk : (p : k) ≠ 0)
    (G : Matrix (Fin n) (Fin n) k) (hG : G ^ p = 1)
    (hB : ∀ (v : Fin n → k) (lam : k), G *ᵥ v = lam • v → v = 0) (hnp : p ≤ n) :
    ∃ A B : Matrix (Fin n) (Fin n) k, A ^ p = 1 ∧ B ^ p = 1 ∧ A * B = B * A ∧ A.det = 1 ∧
      B.det = 1 ∧ ∀ i j : ℕ, i < p → j < p → (∃ c : k, A ^ i * B ^ j = c • 1) →
        i = 0 ∧ j = 0 := by
  have hT : (Matrix.toLinAlgEquiv' G) ^ p = 1 := by rw [← map_pow, hG, map_one]
  have hB' : ∀ (v : Fin n → k) (lam : k), Matrix.toLinAlgEquiv' G v = lam • v → v = 0 := by
    intro v lam h
    exact hB v lam (by simpa [Matrix.toLinAlgEquiv'_apply] using h)
  have hdim : p ≤ Module.finrank k (Fin n → k) := by simpa using hnp
  obtain ⟨A, B, hA, hBp, hAB, hdA, hdB, hind⟩ :=
    exists_split_pair hp hpk (Matrix.toLinAlgEquiv' G) hT hB' hdim
  refine ⟨Matrix.toLinAlgEquiv'.symm A, Matrix.toLinAlgEquiv'.symm B, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_pow, hA, map_one]
  · rw [← map_pow, hBp, map_one]
  · rw [← map_mul, ← map_mul, hAB]
  · show (LinearMap.toMatrix' A).det = 1
    rw [LinearMap.det_toMatrix']
    exact hdA
  · show (LinearMap.toMatrix' B).det = 1
    rw [LinearMap.det_toMatrix']
    exact hdB
  · rintro i j hi hj ⟨c, hc⟩
    refine hind i j hi hj ⟨c, ?_⟩
    have := congrArg (Matrix.toLinAlgEquiv' (R := k) (n := Fin n)) hc
    simpa [map_mul, map_pow] using this

end MatrixForm

end CFSG.LieType.SeitzGeneration
