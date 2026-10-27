module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294ODEigen
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294ODCore
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

namespace I294OD

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.Open

section Private

variable {K : Type*} [Field K] {n p : ℕ}

private def conjSL (P Q : Matrix (Fin n) (Fin n) K) (hQP : Q * P = 1) (a : Fin n → K)
    (ha : ∏ j, a j = 1) : SpecialLinearGroup (Fin n) K :=
  ⟨P * diagonal a * Q, by
    rw [Matrix.det_mul_comm, ← Matrix.mul_assoc, hQP, Matrix.one_mul, Matrix.det_diagonal]
    exact ha⟩

private def conjDiag {G : Type*} [Group G] (P Q : Matrix (Fin n) (Fin n) K) (hPQ : P * Q = 1)
    (hQP : Q * P = 1) (κ : G →* (Fin n → Kˣ)) (hdet : ∀ g, ∏ j, ((κ g j : Kˣ) : K) = 1) :
    G →* SpecialLinearGroup (Fin n) K where
  toFun g := conjSL P Q hQP (fun j => ((κ g j : Kˣ) : K)) (hdet g)
  map_one' := by
    apply Subtype.ext
    show P * diagonal (fun j => ((κ 1 j : Kˣ) : K)) * Q = 1
    simp [hPQ]
  map_mul' g h := by
    apply Subtype.ext
    show P * diagonal (fun j => ((κ (g * h) j : Kˣ) : K)) * Q =
      (P * diagonal (fun j => ((κ g j : Kˣ) : K)) * Q) *
        (P * diagonal (fun j => ((κ h j : Kˣ) : K)) * Q)
    rw [conj_diagonal_mul P Q hQP]
    simp [map_mul]

private def prodHom (p n : ℕ) : (Fin n → Multiplicative (ZMod p)) →* Multiplicative (ZMod p) where
  toFun c := ∏ i, c i
  map_one' := by simp
  map_mul' c d := by simp [Finset.prod_mul_distrib]

private def delta (p n : ℕ) : Subgroup (Fin n → Multiplicative (ZMod p)) :=
  MonoidHom.ker (prodHom p n)

private theorem mem_delta {c : Fin n → Multiplicative (ZMod p)} :
    c ∈ delta p n ↔ ∏ i, c i = 1 :=
  Iff.rfl

private def diagHom (χ : Multiplicative (ZMod p) →* Kˣ) (n : ℕ) :
    (Fin n → Multiplicative (ZMod p)) →* (Fin n → Kˣ) :=
  MonoidHom.pi fun i => χ.comp (Pi.evalMonoidHom (fun _ => Multiplicative (ZMod p)) i)

private theorem prod_diagHom (χ : Multiplicative (ZMod p) →* Kˣ) (c : delta p n) :
    ∏ j, (((diagHom χ n).comp (delta p n).subtype c j : Kˣ) : K) = 1 := by
  rw [← Units.coe_prod]
  have h1 : ∏ j, ((diagHom χ n).comp (delta p n).subtype c j : Kˣ) =
      χ (∏ j, (c : Fin n → Multiplicative (ZMod p)) j) := by
    rw [map_prod]
    rfl
  rw [h1, mem_delta.1 c.2, map_one, Units.val_one]

private noncomputable def psi (χ : Multiplicative (ZMod p) →* Kˣ)
    (P Q : Matrix (Fin n) (Fin n) K) (hPQ : P * Q = 1) (hQP : Q * P = 1) :
    delta p n →* SpecialLinearGroup (Fin n) K :=
  conjDiag P Q hPQ hQP ((diagHom χ n).comp (delta p n).subtype) (prod_diagHom χ)

private theorem coe_psi (χ : Multiplicative (ZMod p) →* Kˣ)
    (P Q : Matrix (Fin n) (Fin n) K) (hPQ : P * Q = 1) (hQP : Q * P = 1) (c : delta p n) :
    (psi χ P Q hPQ hQP c : Matrix (Fin n) (Fin n) K) =
      P * diagonal (fun j => ((χ ((c : Fin n → Multiplicative (ZMod p)) j) : Kˣ) : K)) * Q :=
  rfl

private theorem isElemAbelian_delta [Fact p.Prime] :
    IsElemAbelian p (⊤ : Subgroup (delta p n)) :=
  ⟨⟨⟨fun a b => Subtype.ext (mul_comm a.1 b.1)⟩⟩,
    fun c _ => Subtype.ext (od_torus_pow (c : Fin n → Multiplicative (ZMod p)))⟩

private theorem isElemAbelian_range_psi [Fact p.Prime] (χ : Multiplicative (ZMod p) →* Kˣ)
    (P Q : Matrix (Fin n) (Fin n) K) (hPQ : P * Q = 1) (hQP : Q * P = 1) :
    IsElemAbelian p (psi χ P Q hPQ hQP).range := by
  rw [MonoidHom.range_eq_map]
  exact IsElemAbelian.map isElemAbelian_delta _

private def kappaFun (r n : ℕ) (c : Fin r → Multiplicative (ZMod p)) :
    Fin n → Multiplicative (ZMod p) :=
  fun i => if h : (i : ℕ) < r then c ⟨i, h⟩ else if (i : ℕ) = r then (∏ j, c j)⁻¹ else 1

private theorem kappaFun_one (r n : ℕ) : kappaFun (p := p) r n 1 = 1 := by
  funext i
  simp [kappaFun]

private theorem kappaFun_mul (r n : ℕ) (c d : Fin r → Multiplicative (ZMod p)) :
    kappaFun r n (c * d) = kappaFun r n c * kappaFun r n d := by
  funext i
  by_cases h1 : (i : ℕ) < r
  · simp [kappaFun, h1]
  · by_cases h2 : (i : ℕ) = r
    · simp [kappaFun, h1, h2, Finset.prod_mul_distrib]
      exact mul_comm _ _
    · simp [kappaFun, h1, h2]

private theorem prod_kappaFun {r n : ℕ} (hr : r < n) (c : Fin r → Multiplicative (ZMod p)) :
    ∏ i, kappaFun r n c i = 1 := by
  set c' : ℕ → Multiplicative (ZMod p) := fun k => if h : k < r then c ⟨k, h⟩ else 1 with hc'
  set g : ℕ → Multiplicative (ZMod p) :=
    fun k => if k < r then c' k else if k = r then (∏ j, c j)⁻¹ else 1 with hg
  have h1 : ∀ i : Fin n, kappaFun r n c i = g (i : ℕ) := by
    intro i
    by_cases h : (i : ℕ) < r
    · simp [kappaFun, hg, hc', h]
    · simp [kappaFun, hg, h]
  simp_rw [h1]
  rw [Fin.prod_univ_eq_prod_range g n]
  have hsub : Finset.range (r + 1) ⊆ Finset.range n := by
    intro x hx
    rw [Finset.mem_range] at hx ⊢
    omega
  rw [← Finset.prod_subset hsub (fun x hx hx' => by
    rw [Finset.mem_range] at hx hx'
    simp [hg, show ¬ x < r by omega, show x ≠ r by omega]), Finset.prod_range_succ]
  have h2 : ∏ k ∈ Finset.range r, g k = ∏ j : Fin r, c j := by
    have h3 : ∏ k ∈ Finset.range r, g k = ∏ k ∈ Finset.range r, c' k :=
      Finset.prod_congr rfl fun k hk => by
        have := Finset.mem_range.1 hk
        simp [hg, this]
    rw [h3, ← Fin.prod_univ_eq_prod_range c' r]
    refine Finset.prod_congr rfl fun j _ => ?_
    simp [hc', j.2]
  rw [h2]
  simp [hg]

private def kappaHom (r n : ℕ) (hr : r < n) :
    (Fin r → Multiplicative (ZMod p)) →* delta p n where
  toFun c := ⟨kappaFun r n c, mem_delta.2 (prod_kappaFun hr c)⟩
  map_one' := Subtype.ext (kappaFun_one r n)
  map_mul' c d := Subtype.ext (kappaFun_mul r n c d)

private theorem psi_kappa_eq_one (χ : Multiplicative (ZMod p) →* Kˣ) (hχ : Function.Injective χ)
    (P Q : Matrix (Fin n) (Fin n) K) (hPQ : P * Q = 1) (hQP : Q * P = 1) {r : ℕ}
    (hr : r + 2 ≤ n) (c : Fin r → Multiplicative (ZMod p))
    (h : psi χ P Q hPQ hQP (kappaHom r n (by omega) c) ∈ LinearFlag.scalars n K) : c = 1 := by
  obtain ⟨c0, -, hc0⟩ := LinearFlag.mem_scalars.1 h
  have hc0' : P * diagonal (fun j => ((χ (kappaFun r n c j) : Kˣ) : K)) * Q =
      scalar (Fin n) (c0 : K) := hc0
  have hent : ∀ j : Fin n, ((χ (kappaFun r n c j) : Kˣ) : K) = (c0 : K) := fun j =>
    entries_eq_of_conj_eq_scalar P Q hQP (fun j => ((χ (kappaFun r n c j) : Kˣ) : K)) c0 hc0' j
  have h1 : (c0 : K) = 1 := by
    have h2 := hent ⟨r + 1, by omega⟩
    have h3 : kappaFun r n c ⟨r + 1, by omega⟩ = 1 := by
      simp [kappaFun]
    rw [h3, map_one, Units.val_one] at h2
    exact h2.symm
  funext i
  have h2 := hent ⟨i, by omega⟩
  rw [h1] at h2
  have h3 : kappaFun r n c ⟨i, by omega⟩ = 1 :=
    hχ (by rw [map_one]; exact Units.val_eq_one.1 h2)
  simpa [kappaFun] using h3

private theorem exists_chi [Finite K] (hp : p.Prime) (hpK : p ∣ Nat.card K - 1) :
    ∃ χ : Multiplicative (ZMod p) →* Kˣ, Function.Injective χ := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) p (by rwa [Nat.card_units])
  have hprimU : IsPrimitiveRoot ζ p := by
    rw [← hζ]
    exact IsPrimitiveRoot.orderOf ζ
  exact ⟨(Subgroup.zpowers ζ).subtype.comp
    (AddEquiv.toMultiplicativeLeft hprimU.zmodEquivZPowers).toMonoidHom,
    Subtype.val_injective.comp (AddEquiv.toMultiplicativeLeft hprimU.zmodEquivZPowers).injective⟩

private theorem mono_conj {M P Q N : Matrix (Fin n) (Fin n) K} {π : Equiv.Perm (Fin n)}
    (hPQ : P * Q = 1) (hQP : Q * P = 1) (hMP : M * P = P * N)
    (hN : ∀ s : Fin n → K, N * diagonal s = diagonal (fun i => s (π.symm i)) * N)
    (a : Fin n → K) :
    M * (P * diagonal a * Q) = (P * diagonal (fun i => a (π.symm i)) * Q) * M := by
  have hNQ : N * Q = Q * M := by
    have h1 : Q * M * P = N := by
      rw [Matrix.mul_assoc, hMP, ← Matrix.mul_assoc, hQP, Matrix.one_mul]
    calc N * Q = (Q * M * P) * Q := by rw [h1]
      _ = Q * M * (P * Q) := by rw [Matrix.mul_assoc]
      _ = Q * M := by rw [hPQ, Matrix.mul_one]
  calc M * (P * diagonal a * Q) = (M * P) * diagonal a * Q := by simp only [Matrix.mul_assoc]
    _ = P * (N * diagonal a) * Q := by rw [hMP]; simp only [Matrix.mul_assoc]
    _ = P * (diagonal (fun i => a (π.symm i)) * N) * Q := by rw [hN]
    _ = P * diagonal (fun i => a (π.symm i)) * (N * Q) := by simp only [Matrix.mul_assoc]
    _ = P * diagonal (fun i => a (π.symm i)) * (Q * M) := by rw [hNQ]
    _ = (P * diagonal (fun i => a (π.symm i)) * Q) * M := by simp only [Matrix.mul_assoc]

end Private

theorem torus_commuting {K : Type*} [Field K] [Finite K] {p n : ℕ} (hp : p.Prime) (hn : 5 ≤ n)
    (hpK : p ∣ Nat.card K - 1) {A : Matrix (Fin n) (Fin n) K} (hA : A ^ p = 1) :
    ∃ f : (Fin 3 → Multiplicative (ZMod p)) →* SpecialLinearGroup (Fin n) K,
      Function.Injective f ∧
      (∀ x, (f x : Matrix (Fin n) (Fin n) K) * A = A * (f x : Matrix (Fin n) (Fin n) K)) ∧
      ∀ x, f x ∈ LinearFlag.scalars n K → f x = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨χ, hχ⟩ := exists_chi hp hpK
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) p (by rwa [Nat.card_units])
  have hprimU : IsPrimitiveRoot ζ p := by
    rw [← hζ]
    exact IsPrimitiveRoot.orderOf ζ
  have hprim : IsPrimitiveRoot (ζ : K) p :=
    hprimU.map_of_injective (f := Units.coeHom K) Units.val_injective
  haveI : NeZero (p : K) := hprim.neZero'
  obtain ⟨P, Q, u, hPQ, hQP, hAP⟩ := exists_eigenbasis_matrix A
    (top_le_span_eigenvectors A hprim hp.pos (NeZero.ne _) hA)
  refine ⟨(psi χ P Q hPQ hQP).comp (kappaHom 3 n (by omega)), ?_, fun x => ?_, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro x hx
    refine psi_kappa_eq_one χ hχ P Q hPQ hQP (r := 3) (by omega) x ?_
    rw [MonoidHom.comp_apply] at hx
    rw [hx]
    exact one_mem _
  · exact commute_conj_diagonal P Q hPQ hQP A u hAP _
  · intro x hx
    have := psi_kappa_eq_one χ hχ P Q hPQ hQP (r := 3) (by omega) x hx
    rw [this, map_one]

theorem torus_normalized {K : Type*} [Field K] [Finite K] {p n : ℕ} (hp : p.Prime)
    (hpK : p ∣ Nat.card K - 1) (hn : p + 3 ≤ n) {P Q N M : Matrix (Fin n) (Fin n) K}
    {π : Equiv.Perm (Fin n)} (hPQ : P * Q = 1) (hQP : Q * P = 1) (hMP : M * P = P * N)
    (hN : ∀ s : Fin n → K, N * diagonal s = diagonal (fun i => s (π.symm i)) * N) :
    ∃ T : Subgroup (SpecialLinearGroup (Fin n) K), IsElemAbelian p T ∧
      p ^ (p + 1) ≤ Nat.card (T.map (LinearFlag.proj n K)) ∧
      ∀ g ∈ T, ∃ g' ∈ T, M * (g : Matrix (Fin n) (Fin n) K) =
        (g' : Matrix (Fin n) (Fin n) K) * M := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨χ, hχ⟩ := exists_chi hp hpK
  refine ⟨(psi χ P Q hPQ hQP).range, isElemAbelian_range_psi χ P Q hPQ hQP, ?_, ?_⟩
  · set f : (Fin (p + 1) → Multiplicative (ZMod p)) →* SpecialLinearGroup (Fin n) K :=
      (psi χ P Q hPQ hQP).comp (kappaHom (p + 1) n (by omega)) with hf
    set g := (LinearFlag.proj n K).comp f with hg
    have hginj : Function.Injective g := by
      rw [injective_iff_map_eq_one]
      intro x hx
      exact psi_kappa_eq_one χ hχ P Q hPQ hQP (r := p + 1) (by omega) x
        (LinearFlag.proj_eq_one_iff.1 hx)
    have hle : g.range ≤ (psi χ P Q hPQ hQP).range.map (LinearFlag.proj n K) := by
      rintro _ ⟨x, rfl⟩
      exact ⟨f x, ⟨kappaHom (p + 1) n (by omega) x, rfl⟩, rfl⟩
    have h1 := Subgroup.card_le_of_le hle
    rw [← Nat.card_congr (MonoidHom.ofInjective hginj).toEquiv, od_card_torus] at h1
    exact h1
  · rintro _ ⟨c, rfl⟩
    let c' : delta p n := ⟨fun i => (c : Fin n → Multiplicative (ZMod p)) (π.symm i), by
      rw [mem_delta, Equiv.prod_comp π.symm (c : Fin n → Multiplicative (ZMod p))]
      exact mem_delta.1 c.2⟩
    refine ⟨psi χ P Q hPQ hQP c', ⟨c', rfl⟩, ?_⟩
    rw [coe_psi, coe_psi]
    exact mono_conj hPQ hQP hMP hN _

end I294OD

end CFSG.LocalAnalysis.RankFourTheoremC
