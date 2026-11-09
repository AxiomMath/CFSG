module

public import CFSG.Certificates.Kernel.O8.SBRecAbs
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchExt

public section

namespace CFSG.KC.SBLow

open CFSG.EvenSmallLie.OmegaEight.SpBranch CFSG.KC.SBRec MulAction

theorem nodupM_of_nodup : ∀ (L : List ℕ) (M : ℕ), L.Nodup → (∀ x ∈ L, M.testBit x = false) →
    (L.foldl nodupStep (true, M)).1 = true
  | [], _, _, _ => rfl
  | x :: L, M, hn, hM => by
    rw [List.foldl_cons, nodupStep]
    have hx := hM x List.mem_cons_self
    rw [hx]
    refine nodupM_of_nodup L _ (List.nodup_cons.1 hn).2 fun y hy => ?_
    rw [Nat.testBit_or, Nat.testBit_two_pow, hM y (List.mem_cons_of_mem _ hy), Bool.false_or,
      decide_eq_false_iff_not]
    rintro rfl
    exact (List.nodup_cons.1 hn).1 hy

theorem orbOKM_of {mul : ℕ → ℕ → ℕ} {inv : ℕ → ℕ} {N u : ℕ} {O : List (ℕ × ℕ)}
    (h : orbOK mul inv N u O = true) : orbOKM mul inv N u O = true := by
  unfold orbOK at h
  unfold orbOKM nodupM
  rw [Bool.and_eq_true] at h ⊢
  exact ⟨h.1, nodupM_of_nodup _ 0 (of_decide_eq_true h.2) fun x _ => Nat.zero_testBit x⟩

theorem orbClosedM_of {mul : ℕ → ℕ → ℕ} {inv : ℕ → ℕ} {gens : List ℕ} {u : ℕ} {O : List (ℕ × ℕ)}
    (h : orbClosed mul inv gens u O = true) : orbClosedM mul inv gens u O = true := by
  unfold orbClosed at h
  unfold orbClosedM
  simp only [Bool.and_eq_true, List.all_eq_true, testBit_maskOf, List.contains_iff_mem] at h ⊢
  exact h

variable {S : Type*} [Group S] {N : ℕ} {mul : ℕ → ℕ → ℕ} (Φ : CodeIso S N mul) {inv : ℕ → ℕ}
  {F : ℕ → ℕ} {z : ℕ} {H : Type*} [Group H] (Φ₁ : CodeIso H (2 * N) (extMul N mul F z))
  (h0 : mul 0 0 = 0)

include Φ h0 in
theorem zero_mul_c {y : ℕ} (hy : y < N) : mul 0 y = y := by
  rw [← Φ.f_one h0, ← Φ.f_g hy, ← Φ.map_mul, one_mul]

include Φ h0 in
theorem mul_zero_c {y : ℕ} (hy : y < N) : mul y 0 = y := by
  rw [← Φ.f_one h0, ← Φ.f_g hy, ← Φ.map_mul, mul_one]

include Φ h0 in
theorem gen_ext' (F : ℕ → ℕ) (z : ℕ) {gens : List ℕ} (hgens : ∀ g ∈ gens, g < N)
    (hG : Gen mul gens N) : Gen (extMul N mul F z) (gens ++ [N]) (2 * N) := by
  have hmul : ∀ c d, c < N → d < N → mul c d < N := fun c d hc hd => by
    rw [← Φ.f_g hc, ← Φ.f_g hd, ← Φ.map_mul]; exact Φ.lt _
  have key : ∀ c, Reach mul gens c → c < N ∧ Reach (extMul N mul F z) (gens ++ [N]) c := by
    intro c hc
    induction hc with
    | zero => exact ⟨Φ.pos, Reach.zero⟩
    | @step c g _ hg ih =>
      obtain ⟨hc, hr⟩ := ih
      have hgN := hgens _ hg
      refine ⟨hmul _ _ hc hgN, ?_⟩
      have e : extMul N mul F z c g = mul c g := by
        rw [extMul, if_pos hc, if_pos hgN]
      rw [← e]
      exact Reach.step hr (List.mem_append_left _ hg)
  intro c hc
  by_cases hcN : c < N
  · exact (key c (hG c hcN)).2
  · have h1 := (key (c - N) (hG _ (by omega))).2
    have e : extMul N mul F z (c - N) N = c := by
      rw [extMul, if_pos (by omega : c - N < N), if_neg (lt_irrefl N), Nat.sub_self,
        mul_zero_c Φ h0 (by omega)]
      omega
    rw [← e]
    exact Reach.step h1 (List.mem_append_right _ (List.mem_singleton_self N))

include Φ h0 in
theorem ext00 : extMul N mul F z 0 0 = 0 := by
  rw [extMul, if_pos Φ.pos, if_pos Φ.pos, h0]

theorem f_g₁ {c : ℕ} (hc : c < N) : Φ₁.f (Φ₁.g c) = c := Φ₁.f_g (by omega)

@[expose] noncomputable def jH : S →* H where
  toFun s := Φ₁.g (Φ.f s)
  map_one' := by rw [Φ.f_one h0, ← Φ₁.f_one (ext00 Φ h0), Φ₁.g_f]
  map_mul' s t := by
    refine Φ₁.inj ?_
    rw [Φ₁.map_mul, f_g₁ Φ₁ (Φ.lt _), f_g₁ Φ₁ (Φ.lt _), f_g₁ Φ₁ (Φ.lt _), Φ.map_mul, extMul,
      if_pos (Φ.lt s), if_pos (Φ.lt t)]

theorem f_jH (s : S) : Φ₁.f (jH Φ Φ₁ h0 s) = Φ.f s := f_g₁ Φ₁ (Φ.lt s)

theorem jH_g {c : ℕ} (hc : c < N) : jH Φ Φ₁ h0 (Φ.g c) = Φ₁.g c := by
  refine Φ₁.inj ?_
  rw [f_jH, Φ.f_g hc, f_g₁ Φ₁ hc]

variable (hFlt : ∀ a < N, F a < N)

include hFlt in
theorem X_mul_jH (s : S) : Φ₁.g N * jH Φ Φ₁ h0 s = jH Φ Φ₁ h0 (Φ.g (F (Φ.f s))) * Φ₁.g N := by
  have hN : N < 2 * N := by have := Φ.pos; omega
  have hF := hFlt _ (Φ.lt s)
  refine Φ₁.inj ?_
  rw [Φ₁.map_mul, Φ₁.map_mul, Φ₁.f_g hN, f_jH, f_jH, Φ.f_g hF, extMul, extMul, if_neg (lt_irrefl N),
    if_pos (Φ.lt s), if_pos hF, if_neg (lt_irrefl N), Nat.sub_self, zero_mul_c Φ h0 hF,
    mul_zero_c Φ h0 hF]

include hFlt in
theorem X_conj (s : S) :
    Φ₁.g N * jH Φ Φ₁ h0 s * (Φ₁.g N)⁻¹ = jH Φ Φ₁ h0 (Φ.g (F (Φ.f s))) := by
  rw [X_mul_jH Φ Φ₁ h0 hFlt, mul_inv_cancel_right]

include h0 in
theorem cases_H (h : H) : (∃ s, h = jH Φ Φ₁ h0 s) ∨ (∃ s, h = jH Φ Φ₁ h0 s * Φ₁.g N) := by
  have hN : N < 2 * N := by have := Φ.pos; omega
  by_cases hc : Φ₁.f h < N
  · refine Or.inl ⟨Φ.g (Φ₁.f h), Φ₁.inj ?_⟩
    rw [f_jH, Φ.f_g hc]
  · have hlt := Φ₁.lt h
    refine Or.inr ⟨Φ.g (Φ₁.f h - N), Φ₁.inj ?_⟩
    rw [Φ₁.map_mul, f_jH, Φ.f_g (by omega), Φ₁.f_g hN, extMul, if_pos (by omega),
      if_neg (lt_irrefl N), Nat.sub_self, mul_zero_c Φ h0 (by omega)]
    omega

variable (hinv : invOK mul inv N = true)

include Φ Φ₁ h0 hFlt hinv in
theorem mem_orbit_low {r r' c : ℕ} (hr : r < N) (hr' : r' < N) (hc : c < N)
    (hF : F r = cconj mul inv c r') (y : H) :
    y ∈ orbit (ConjAct H) (Φ₁.g r) ↔ (∃ s : S, Φ₁.f y = Φ.f (s * Φ.g r * s⁻¹)) ∨
      ∃ s : S, Φ₁.f y = Φ.f (s * Φ.g r' * s⁻¹) := by
  have hR : Φ₁.g r = jH Φ Φ₁ h0 (Φ.g r) := (jH_g Φ Φ₁ h0 hr).symm
  have hC : Φ.g (F r) = Φ.g c * Φ.g r' * (Φ.g c)⁻¹ := by
    rw [hF, cc Φ h0 hinv hc hr', Φ.g_f]
  have hXR : Φ₁.g N * Φ₁.g r * (Φ₁.g N)⁻¹ = jH Φ Φ₁ h0 (Φ.g c * Φ.g r' * (Φ.g c)⁻¹) := by
    rw [hR, X_conj Φ Φ₁ h0 hFlt, Φ.f_g hr, hC]
  have hcode : ∀ y : H, ∀ t : S, Φ₁.f y = Φ.f t ↔ y = jH Φ Φ₁ h0 t := fun y t => by
    rw [← f_jH Φ Φ₁ h0 t]
    exact Φ₁.f_eq_iff
  rw [mem_orbit_iff_conj]
  constructor
  · rintro ⟨h, rfl⟩
    rcases cases_H Φ Φ₁ h0 h with ⟨s, rfl⟩ | ⟨s, rfl⟩
    · refine Or.inl ⟨s, (hcode _ _).2 ?_⟩
      rw [hR, map_mul, map_mul, map_inv]
    · refine Or.inr ⟨s * Φ.g c, (hcode _ _).2 ?_⟩
      have e : jH Φ Φ₁ h0 s * Φ₁.g N * Φ₁.g r * (jH Φ Φ₁ h0 s * Φ₁.g N)⁻¹ =
          jH Φ Φ₁ h0 s * (Φ₁.g N * Φ₁.g r * (Φ₁.g N)⁻¹) * (jH Φ Φ₁ h0 s)⁻¹ := by group
      rw [e, hXR, ← map_inv, ← map_mul, ← map_mul]
      congr 1
      group
  · rintro (⟨s, hs⟩ | ⟨s, hs⟩)
    · rw [hcode] at hs
      refine ⟨jH Φ Φ₁ h0 s, ?_⟩
      rw [hs, hR, ← map_inv, ← map_mul, ← map_mul]
    · rw [hcode] at hs
      refine ⟨jH Φ Φ₁ h0 (s * (Φ.g c)⁻¹) * Φ₁.g N, ?_⟩
      have e : jH Φ Φ₁ h0 (s * (Φ.g c)⁻¹) * Φ₁.g N * Φ₁.g r *
          (jH Φ Φ₁ h0 (s * (Φ.g c)⁻¹) * Φ₁.g N)⁻¹ =
          jH Φ Φ₁ h0 (s * (Φ.g c)⁻¹) * (Φ₁.g N * Φ₁.g r * (Φ₁.g N)⁻¹) *
            (jH Φ Φ₁ h0 (s * (Φ.g c)⁻¹))⁻¹ := by group
      rw [e, hXR, hs, ← map_inv, ← map_mul, ← map_mul]
      congr 1
      group

variable {gensS gens₁ : List ℕ} {inv₁ : ℕ → ℕ} (hgS : ∀ g ∈ gensS, g < N) (hGS : Gen mul gensS N)
  (hinv₁ : invOK (extMul N mul F z) inv₁ (2 * N) = true) (hg₁ : ∀ g ∈ gens₁, g < 2 * N)
  (hG₁ : Gen (extMul N mul F z) gens₁ (2 * N))

include Φ Φ₁ h0 hFlt hinv hgS hGS hinv₁ hg₁ hG₁ in
theorem low_parts {CS : List (ℕ × ℕ)} (hCS : kClassOK mul inv gensS N CS = true) {r a r' b c n : ℕ}
    (hra : (r, a) ∈ CS) (hrb : (r', b) ∈ CS) (hc : c < N) (hF : F r = cconj mul inv c r')
    (hn : (r' = r ∧ n = a) ∨ (r < r' ∧ n = a + b)) (hn130 : n < 130) :
    orbOKM (extMul N mul F z) inv₁ (2 * N) r (recM (extMul N mul F z) inv₁ gens₁ r) = true ∧
      orbClosedM (extMul N mul F z) inv₁ gens₁ r (recM (extMul N mul F z) inv₁ gens₁ r) = true ∧
      (recM (extMul N mul F z) inv₁ gens₁ r).length = n ∧
      ∀ p ∈ recM (extMul N mul F z) inv₁ gens₁ r, r ≤ p.1 := by
  classical
  have hfin := Φ₁.finite
  obtain ⟨-, hparts, -⟩ := classOK_parts hCS
  obtain ⟨hr, -, -, hOA, hCA, hlA, hmA⟩ := hparts _ hra
  obtain ⟨hr', -, -, hOB, hCB, hlB, hmB⟩ := hparts _ hrb
  simp only at hr hOA hCA hlA hmA hr' hOB hCB hlB hmB
  set A := recM mul inv gensS r
  set B := recM mul inv gensS r'
  have hN : N < 2 * N := by have := Φ.pos; omega
  have hmemS : ∀ (u : ℕ) (O : List (ℕ × ℕ)), u < N → orbOK mul inv N u O = true →
      orbClosed mul inv gensS u O = true → ∀ x : ℕ,
      (∃ s : S, x = Φ.f (s * Φ.g u * s⁻¹)) ↔ x ∈ O.map Prod.fst := by
    intro u O hu hO hC x
    have hO' : orbOK mul inv N (Φ.f (Φ.g u)) O = true := by rwa [Φ.f_g hu]
    have hC' : orbClosed mul inv gensS (Φ.f (Φ.g u)) O = true := by rwa [Φ.f_g hu]
    constructor
    · rintro ⟨s, rfl⟩
      exact (Φ.mem_orbit_iff h0 hinv hgS hGS hO' hC' _).1 (mem_orbit_iff_conj.2 ⟨s, rfl⟩)
    · intro hx
      obtain ⟨g, hg⟩ := Φ.exists_conj_of_orbOK h0 hinv hO' hx
      exact ⟨g, hg.symm⟩
  have hmem : ∀ y : H, y ∈ orbit (ConjAct H) (Φ₁.g r) ↔
      Φ₁.f y ∈ A.map Prod.fst ∨ Φ₁.f y ∈ B.map Prod.fst := by
    intro y
    rw [mem_orbit_low Φ Φ₁ h0 hFlt hinv hr hr' hc hF, ← hmemS r A hr hOA hCA,
      ← hmemS r' B hr' hOB hCB]
  have hAlt : ∀ x ∈ A.map Prod.fst, x < N := fun x hx => by
    obtain ⟨s, rfl⟩ := (hmemS r A hr hOA hCA x).2 hx
    exact Φ.lt _
  have hBlt : ∀ x ∈ B.map Prod.fst, x < N := fun x hx => by
    obtain ⟨s, rfl⟩ := (hmemS r' B hr' hOB hCB x).2 hx
    exact Φ.lt _
  have himg : Φ₁.f '' orbit (ConjAct H) (Φ₁.g r) =
      ↑((A.map Prod.fst).toFinset ∪ (B.map Prod.fst).toFinset) := by
    ext x
    simp only [Set.mem_image, Finset.coe_union, Set.mem_union, Finset.mem_coe, List.mem_toFinset]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hmem y).1 hy
    · intro hx
      have hxN : x < N := hx.elim (hAlt x) (hBlt x)
      refine ⟨Φ₁.g x, (hmem _).2 ?_, f_g₁ Φ₁ hxN⟩
      rwa [f_g₁ Φ₁ hxN]
  have hcard : (orbit (ConjAct H) (Φ₁.g r)).ncard = n := by
    rw [← Set.ncard_image_of_injective _ Φ₁.inj, himg, Set.ncard_coe_finset]
    have hndA := nodup_of_orbOK hOA
    have hndB := nodup_of_orbOK hOB
    rcases hn with ⟨rfl, rfl⟩ | ⟨hlt, rfl⟩
    · rw [Finset.union_self, List.toFinset_card_of_nodup hndA, List.length_map, hlA]
    · rw [Finset.card_union_of_disjoint, List.toFinset_card_of_nodup hndA,
        List.toFinset_card_of_nodup hndB, List.length_map, List.length_map, hlA, hlB]
      refine Finset.disjoint_left.2 fun x hxA hxB => ?_
      rw [List.mem_toFinset] at hxA hxB
      obtain ⟨s, hs⟩ := (hmemS r A hr hOA hCA x).2 hxA
      obtain ⟨t, ht⟩ := (hmemS r' B hr' hOB hCB x).2 hxB
      have e : s * Φ.g r * s⁻¹ = t * Φ.g r' * t⁻¹ := Φ.inj (hs.symm.trans ht)
      have hrB : r ∈ B.map Prod.fst := by
        refine (hmemS r' B hr' hOB hCB r).1 ⟨s⁻¹ * t, ?_⟩
        have : s⁻¹ * t * Φ.g r' * (s⁻¹ * t)⁻¹ = Φ.g r := by
          have e2 : s⁻¹ * t * Φ.g r' * (s⁻¹ * t)⁻¹ = s⁻¹ * (t * Φ.g r' * t⁻¹) * s := by group
          rw [e2, ← e]
          group
        rw [this, Φ.f_g hr]
      obtain ⟨p, hp, hpe⟩ := List.mem_map.1 hrB
      have := hmB p hp
      omega
  have hsmall : (orbit (ConjAct H) (Φ₁.g r)).ncard < 130 := hcard ▸ hn130
  obtain ⟨hO, hC⟩ := recM_ok Φ₁ (ext00 Φ h0) hinv₁ hg₁ (by omega : r < 2 * N) hsmall
  have hO' : orbOK (extMul N mul F z) inv₁ (2 * N) (Φ₁.f (Φ₁.g r))
      (recM (extMul N mul F z) inv₁ gens₁ r) = true := by
    rw [f_g₁ Φ₁ hr]
    exact hO
  have hC' : orbClosed (extMul N mul F z) inv₁ gens₁ (Φ₁.f (Φ₁.g r))
      (recM (extMul N mul F z) inv₁ gens₁ r) = true := by
    rw [f_g₁ Φ₁ hr]
    exact hC
  refine ⟨orbOKM_of hO, orbClosedM_of hC, ?_, fun p hp => ?_⟩
  · rw [← Φ₁.ncard_eq (ext00 Φ h0) hinv₁ hg₁ hG₁ hO' hC', hcard]
  · obtain ⟨g, hg⟩ := Φ₁.exists_conj_of_orbOK (ext00 Φ h0) hinv₁ hO' (List.mem_map_of_mem hp)
    have hy : g * Φ₁.g r * g⁻¹ ∈ orbit (ConjAct H) (Φ₁.g r) := mem_orbit_iff_conj.2 ⟨g, rfl⟩
    rw [hmem, hg] at hy
    rcases hy with hy | hy
    · obtain ⟨q, hq, hqe⟩ := List.mem_map.1 hy
      have := hmA q hq
      omega
    · obtain ⟨q, hq, hqe⟩ := List.mem_map.1 hy
      have := hmB q hq
      rcases hn with ⟨rfl, -⟩ | ⟨hlt, -⟩ <;> omega

end CFSG.KC.SBLow

end
