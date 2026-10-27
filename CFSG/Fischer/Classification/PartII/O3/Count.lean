module

public import CFSG.Fischer.Classification.PartII.O3.Witness

public section

namespace CFSG.Fischer.Classification.O3

open CFSG.Blueprint.Fischer CFSG.Fischer

variable {X : Type} [Group X] {E : Set X}

namespace Count

theorem ncard_mul_fib_eq (hS : Setting X E) {M Ξ : Set X} {x x' w₀ : X} (hx : x ∈ Ξ)
    (hx' : x' ∈ Ξ) (hxx' : x ≠ x') (hΞ : ∀ p ∈ Ξ, p ∈ E ∧ M ⊆ LocalClass E p)
    (hpw : ∀ p ∈ Ξ, ∀ q ∈ Ξ, p ≠ q → p * q ≠ q * p ∧ LocalClass E p ∩ LocalClass E q ⊆ M)
    (hfib : ∀ w ∈ M, fib E w x ⊆ Ξ) (hw₀ : w₀ ∈ M) :
    M.ncard * ((fib E w₀ x).ncard - 1) = (Ξ \ {x}).ncard * {e | IsWit E e x x'}.ncard := by
  have hP := hS.pair
  have := Pair.finite hP
  obtain ⟨hxE, hMx⟩ := hΞ x hx
  refine ncard_mul_eq_ncard_mul (fun w y => y ∈ fib E w x) (fun w hw => ?_) (fun y hy => ?_)
  · have hset : {y | y ∈ Ξ \ {x} ∧ y ∈ fib E w x} = fib E w x \ {x} := by
      ext y
      exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨hfib w hw h.1, h.2⟩, h.1⟩⟩
    rw [hset, Set.ncard_sdiff_singleton_of_mem (Pair.mem_fib_self hP hxE),
      Pair.ncard_fib_eq hP hS.hyp.center hS.hyp.simple (hMx hw₀).1
        (mem_localClass_symm hxE (hMx hw₀)) (hMx hw).1 (mem_localClass_symm hxE (hMx hw))]
  · obtain ⟨hyΞ, hyx⟩ := hy
    have hyx' : y ≠ x := hyx
    obtain ⟨hyE, hMy⟩ := hΞ y hyΞ
    obtain ⟨hxy, hDxy⟩ := hpw x hx y hyΞ (Ne.symm hyx')
    have hset : {w | w ∈ M ∧ y ∈ fib E w x} = {e | IsWit E e x y} := by
      ext w
      exact ⟨fun h => ⟨⟨hMx h.1, hMy h.1⟩, h.2.2⟩, fun h => ⟨hDxy h.1, hyE, h.2⟩⟩
    rw [hset, hS.ncard_wit_eq hxE (hΞ x' hx').1 (hpw x hx x' hx' hxx').1 hxE hyE hxy]

theorem eq_of_mem_block {M Ξ : Set X}
    (hpw : ∀ p ∈ Ξ, ∀ q ∈ Ξ, p ≠ q → p * q ≠ q * p ∧ LocalClass E p ∩ LocalClass E q ⊆ M)
    {p q z : X} (hp : p ∈ Ξ) (hq : q ∈ Ξ) (hzp : z ∈ insert p (LocalClass E p \ M))
    (hzq : z ∈ insert q (LocalClass E q \ M)) : p = q := by
  by_contra hpq
  obtain ⟨hnc, hDpq⟩ := hpw p hp q hq hpq
  rcases hzp with hzp | ⟨hzp, hzM⟩ <;> rcases hzq with hzq | ⟨hzq, -⟩
  · exact hpq (hzp.symm.trans hzq)
  · rw [hzp] at hzq
    exact hnc hzq.2.2
  · rw [hzq] at hzp
    exact hnc hzp.2.2.symm
  · exact hzM (hDpq ⟨hzp, hzq⟩)

theorem ncard_mul_block_le (hP : Pair X E) {M Ξ : Set X} {x : X} (hx : x ∈ Ξ)
    (hΞ : ∀ p ∈ Ξ, p ∈ E ∧ M ⊆ LocalClass E p)
    (hpw : ∀ p ∈ Ξ, ∀ q ∈ Ξ, p ≠ q → p * q ≠ q * p ∧ LocalClass E p ∩ LocalClass E q ⊆ M) :
    (Ξ \ {x}).ncard * (1 + ((LocalClass E x).ncard - M.ncard)) ≤
      {c | c ∈ E ∧ c * x ≠ x * c}.ncard := by
  have := Pair.finite hP
  have hxE := (hΞ x hx).1
  set U : Set X := {z | ∃ p ∈ Ξ \ {x}, z ∈ insert p (LocalClass E p \ M)}
  have hcount : (Ξ \ {x}).ncard * (1 + ((LocalClass E x).ncard - M.ncard)) = U.ncard * 1 := by
    refine ncard_mul_eq_ncard_mul (fun p z => z ∈ insert p (LocalClass E p \ M))
      (fun p hp => ?_) (fun z hz => ?_)
    · obtain ⟨hpE, hMp⟩ := hΞ p hp.1
      have hset : {z | z ∈ U ∧ z ∈ insert p (LocalClass E p \ M)} =
          insert p (LocalClass E p \ M) := by
        ext z
        exact ⟨fun h => h.2, fun h => ⟨⟨p, hp, h⟩, h⟩⟩
      have hp' : p ∉ LocalClass E p \ M := fun h => h.1.2.1 rfl
      rw [hset, Set.ncard_insert_of_notMem hp', Set.ncard_sdiff hMp,
        Pair.ncard_localClass_eq hP hpE hxE]
      omega
    · obtain ⟨p, hp, hzp⟩ := hz
      rw [Set.ncard_eq_one]
      refine ⟨p, Set.ext fun q => ⟨fun hq => ?_, fun hq => ?_⟩⟩
      · exact Set.mem_singleton_iff.2 (eq_of_mem_block hpw hq.1.1 hp.1 hq.2 hzp)
      · rw [Set.mem_singleton_iff.1 hq]
        exact ⟨hp, hzp⟩
  have hsub : U ⊆ {c | c ∈ E ∧ c * x ≠ x * c} := by
    rintro z ⟨p, ⟨hpΞ, hpx⟩, hzp⟩
    obtain ⟨hnc, hDpx⟩ := hpw p hpΞ x hx hpx
    rcases hzp with hzp | ⟨hzp, hzM⟩
    · rw [hzp]
      exact ⟨(hΞ p hpΞ).1, hnc⟩
    · refine ⟨hzp.1, fun hzx => ?_⟩
      by_cases hz : z = x
      · rw [hz] at hzp
        exact hnc hzp.2.2.symm
      · exact hzM (hDpx ⟨hzp, hzp.1, hz, hzx⟩)
  rw [hcount, mul_one]
  exact Set.ncard_le_ncard hsub

theorem le_of_count {A N k μ a F : ℕ} (h1 : μ * F = a * N) (h2 : A * N = k * F)
    (h3 : a * (1 + (k - μ)) ≤ A) (hN : 0 < N) (ha : 0 < a) (hμ : 2 ≤ μ) (hμk : μ ≤ k) :
    k ≤ μ := by
  have h4 : A * μ = k * a := by
    refine Nat.eq_of_mul_eq_mul_right hN ?_
    calc A * μ * N = μ * (A * N) := by ring
      _ = k * (μ * F) := by rw [h2]; ring
      _ = k * a * N := by rw [h1]; ring
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hμk
  rw [Nat.add_sub_cancel_left] at h3
  have h5 : a * (1 + d) * μ ≤ (μ + d) * a := h4 ▸ Nat.mul_le_mul_right μ h3
  have h6 : a * d * 2 ≤ a * d * μ := Nat.mul_le_mul_left _ hμ
  have h7 : a * d = 0 := by nlinarith
  rcases Nat.mul_eq_zero.1 h7 with h | h <;> omega

end Count

theorem Setting.false_of_ySet (hS : Setting X E) {M Ξ : Set X} {x x' : X}
    (hx : x ∈ Ξ) (hx' : x' ∈ Ξ) (hxx' : x ≠ x')
    (hΞ : ∀ p ∈ Ξ, p ∈ E ∧ M ⊆ LocalClass E p)
    (hpw : ∀ p ∈ Ξ, ∀ q ∈ Ξ, p ≠ q → p * q ≠ q * p ∧ LocalClass E p ∩ LocalClass E q ⊆ M)
    (hfib : ∀ w ∈ M, fib E w x ⊆ Ξ) (hM : 1 < M.ncard) : False := by
  have hP := hS.pair
  have := Pair.finite hP
  obtain ⟨hxE, hMx⟩ := hΞ x hx
  obtain ⟨hx'E, hMx'⟩ := hΞ x' hx'
  have hxx'c := (hpw x hx x' hx' hxx').1
  obtain ⟨w₀, hw₀⟩ : M.Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
  have h1 := Count.ncard_mul_fib_eq hS hx hx' hxx' hΞ hpw hfib hw₀
  have h2 := hS.ncard_far_mul_ncard_wit hxE hxE hx'E hxx'c (hMx hw₀).1
    (mem_localClass_symm hxE (hMx hw₀))
  have h3 := Count.ncard_mul_block_le hP hx hΞ hpw
  have hN : 0 < {e | IsWit E e x x'}.ncard :=
    (Set.ncard_pos (Set.toFinite _)).2 (hS.exists_isWit hxE hx'E hxx'c)
  have ha : 0 < (Ξ \ {x}).ncard :=
    (Set.ncard_pos (Set.toFinite _)).2 ⟨x', hx', fun h => hxx' (Set.mem_singleton_iff.1 h).symm⟩
  have hk := Count.le_of_count h1 h2 h3 hN ha hM (Set.ncard_le_ncard hMx)
  have hDx : M = LocalClass E x := Set.eq_of_subset_of_ncard_le hMx hk
  exact hxx' (Pair.eq_of_localClass_subset hP hS.hyp.center hS.hyp.simple hS.nab hxE hx'E
    (hDx ▸ hMx'))

end CFSG.Fischer.Classification.O3
