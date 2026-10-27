module

public import CFSG.ClassicalInvolution.Phan.PhanS6T4Frame
public import CFSG.ClassicalInvolution.Phan.PhanS6T6Norm

public section

namespace CFSG.ClassicalInvolution.PhanB3.S.Std.T

variable {K : Type} [Field K] (M : Model K)

section Proj

variable (a b : Vec K)

@[expose] def cxa (v : Vec K) : K :=
  (her M b b * bf M v (tauV M a) - her M b a * bf M v (tauV M b)) / gram M a b

@[expose] def cxb (v : Vec K) : K :=
  (her M a a * bf M v (tauV M b) - her M a b * bf M v (tauV M a)) / gram M a b

@[expose] def cyA (v : Vec K) : K :=
  (her M b b * bf M v a - her M a b * bf M v b) / gram M a b

@[expose] def cyB (v : Vec K) : K :=
  (her M a a * bf M v b - her M b a * bf M v a) / gram M a b

@[expose] def piW (v : Vec K) : Vec K :=
  v - cxa M a b v • a - cxb M a b v • b - cyA M a b v • tauV M a - cyB M a b v • tauV M b

variable {M a b}

theorem piW_inW (haa : bf M a a = 0) (hab : bf M a b = 0) (hbb : bf M b b = 0)
    (hD : gram M a b ≠ 0) (v : Vec K) : InW M a b (piW M a b v) := by
  have hD' : her M a a * her M b b - her M a b * her M b a ≠ 0 := hD
  have hba : bf M b a = 0 := by rw [bf_comm]; exact hab
  have hAa : bf M (tauV M a) a = her M a a := by rw [bf_comm]; rfl
  have hBa : bf M (tauV M b) a = her M a b := by rw [bf_comm]; rfl
  have hAb : bf M (tauV M a) b = her M b a := by rw [bf_comm]; rfl
  have hBb : bf M (tauV M b) b = her M b b := by rw [bf_comm]; rfl
  have hAA : bf M (tauV M a) (tauV M a) = 0 := by rw [bf_tauV, haa, map_zero]
  have hAB : bf M (tauV M a) (tauV M b) = 0 := by rw [bf_tauV, hab, map_zero]
  have hBA : bf M (tauV M b) (tauV M a) = 0 := by rw [bf_tauV, hba, map_zero]
  have hBB : bf M (tauV M b) (tauV M b) = 0 := by rw [bf_tauV, hbb, map_zero]
  have haA : bf M a (tauV M a) = her M a a := rfl
  have haB : bf M a (tauV M b) = her M a b := rfl
  have hbA : bf M b (tauV M a) = her M b a := rfl
  have hbB : bf M b (tauV M b) = her M b b := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [piW, bf_sub_left, bf_smul_left, haa, hba, hAa, hBa, cxa, cxb, cyA, cyB]
    field_simp
    simp only [gram]
    ring
  · simp only [piW, bf_sub_left, bf_smul_left, hab, hbb, hAb, hBb, cxa, cxb, cyA, cyB]
    field_simp
    simp only [gram]
    ring
  · simp only [piW, bf_sub_left, bf_smul_left, haA, hbA, hAA, hBA, cxa, cxb, cyA, cyB]
    field_simp
    simp only [gram]
    ring
  · simp only [piW, bf_sub_left, bf_smul_left, haB, hbB, hAB, hBB, cxa, cxb, cyA, cyB]
    field_simp
    simp only [gram]
    ring

theorem bf_piW {x : Vec K} (hx : InW M a b x) (v : Vec K) : bf M x (piW M a b v) = bf M x v := by
  obtain ⟨h1, h2, h3, h4⟩ := hx
  simp only [piW, bf_sub_right, bf_smul_right, h1, h2, h3, h4]
  ring

end Proj

section Rational

variable {M}

theorem exists_fixed_vec {δ : K} (hδ : M.τ δ ≠ δ) {S : Submodule K (Vec K)}
    (hS : ∀ x ∈ S, tauV M x ∈ S) {z : Vec K} (hz : z ∈ S) (hz0 : z ≠ 0) :
    ∃ y ∈ S, y ≠ 0 ∧ tauV M y = y := by
  by_cases h1 : z + tauV M z = 0
  · have h2 : tauV M z = -z := eq_neg_of_add_eq_zero_right h1
    refine ⟨δ • z + tauV M (δ • z), S.add_mem (S.smul_mem _ hz) (hS _ (S.smul_mem _ hz)), ?_, ?_⟩
    · rw [tauV_smul, h2, smul_neg, ← sub_eq_add_neg, ← sub_smul]
      exact smul_ne_zero (sub_ne_zero.2 fun h => hδ h.symm) hz0
    · rw [tauV_add, tauV_tauV, add_comm]
  · exact ⟨z + tauV M z, S.add_mem hz (hS _ hz), h1, by rw [tauV_add, tauV_tauV, add_comm]⟩

end Rational

section Build

variable {M} {a b r : Vec K}

theorem bf_tauV_left (x y : Vec K) : bf M (tauV M x) y = M.τ (bf M x (tauV M y)) := by
  have := bf_tauV M x (tauV M y)
  rwa [tauV_tauV] at this

theorem exists_dual (hr0 : r ≠ 0) : ∃ v : Vec K, bf M r v = 1 := by
  by_contra h
  push Not at h
  apply hr0
  refine eq_zero_of_bf_eq_zero M fun v => ?_
  by_contra hv
  exact h ((bf M r v)⁻¹ • v) (by rw [bf_smul_right, inv_mul_cancel₀ hv])

theorem exists_s (haa : bf M a a = 0) (hab : bf M a b = 0) (hbb : bf M b b = 0)
    (hD : gram M a b ≠ 0) (hr : InW M a b r) (hτr : tauV M r = r) (hr0 : r ≠ 0) :
    ∃ s : Vec K, InW M a b s ∧ tauV M s = s ∧ bf M r s = 2 := by
  obtain ⟨v, hv⟩ := exists_dual (M := M) hr0
  have hwW : InW M a b (piW M a b v) := piW_inW haa hab hbb hD v
  have hrw : bf M r (piW M a b v) = 1 := by rw [bf_piW hr, hv]
  have htw : bf M r (tauV M (piW M a b v)) = 1 := by
    have := bf_tauV M r (piW M a b v)
    rw [hτr, hrw, map_one] at this
    exact this
  refine ⟨piW M a b v + tauV M (piW M a b v), hwW.add hwW.tau, ?_, ?_⟩
  · rw [tauV_add, tauV_tauV, add_comm]
  · rw [bf_add_right, hrw, htw, one_add_one_eq_two]

theorem exists_f (haa : bf M a a = 0) (hab : bf M a b = 0) (hbb : bf M b b = 0)
    (hD : gram M a b ≠ 0) (hr : InW M a b r) (hrr : bf M r r = 0) (hτr : tauV M r = r)
    (hr0 : r ≠ 0) :
    ∃ f : Vec K, InW M a b f ∧ tauV M f = f ∧ bf M f f = 0 ∧ bf M r f = 1 := by
  obtain ⟨s, hsW, hτs, hrs⟩ := exists_s haa hab hbb hD hr hτr hr0
  have h2 : (2 : K) ≠ 0 := M.two_ne
  obtain ⟨s1, hs1W, hτs1, hrs1⟩ : ∃ s1 : Vec K, InW M a b s1 ∧ tauV M s1 = s1 ∧
      bf M r s1 = 1 :=
    ⟨(2 : K)⁻¹ • s, hsW.smul _, by rw [tauV_smul, hτs, map_inv₀, map_ofNat],
      by rw [bf_smul_right, hrs, inv_mul_cancel₀ h2]⟩
  have hτσ : M.τ (bf M s1 s1) = bf M s1 s1 := by rw [← bf_tauV, hτs1]
  have hs1r : bf M s1 r = 1 := by rw [bf_comm]; exact hrs1
  refine ⟨s1 + (-((2 : K)⁻¹ * bf M s1 s1)) • r, hs1W.add (hr.smul _), ?_, ?_, ?_⟩
  · rw [tauV_add, hτs1, tauV_smul, hτr, map_neg, map_mul, map_inv₀, map_ofNat, hτσ]
  · simp only [bf_add_left, bf_add_right, bf_smul_left, bf_smul_right, hrr, hs1r, hrs1]
    field_simp
    ring
  · rw [bf_add_right, bf_smul_right, hrs1, hrr]
    ring

theorem exists_z [Finite K] (hq : 1 < M.q) {f : Vec K} (hτr : tauV M r = r)
    (hτf : tauV M f = f) :
    ∃ z : Vec K, z ≠ 0 ∧ InW M a b z ∧ bf M z r = 0 ∧ bf M z f = 0 ∧ tauV M z = z := by
  classical
  have := Fintype.ofFinite K
  obtain ⟨δ, hδ⟩ := exists_not_fixed M hq
  let v6 : Fin 6 → Vec K := ![a, b, tauV M a, tauV M b, r, f]
  let Λ : Vec K →ₗ[K] (Fin 6 → K) := LinearMap.pi fun i => (bfB M).flip (v6 i)
  have hker : LinearMap.ker Λ ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by simp)
  obtain ⟨z0, hz0, hz0ne⟩ := (Submodule.ne_bot_iff _).1 hker
  have hmem : ∀ x : Vec K, x ∈ LinearMap.ker Λ ↔ ∀ i, bf M x (v6 i) = 0 := by
    intro x
    rw [LinearMap.mem_ker]
    constructor
    · intro h i
      have := congrFun h i
      simpa [Λ, bfB_apply] using this
    · intro h
      funext i
      simpa [Λ, bfB_apply] using h i
  have hS : ∀ x ∈ LinearMap.ker Λ, tauV M x ∈ LinearMap.ker Λ := by
    intro x hx
    rw [hmem] at hx ⊢
    intro i
    rw [bf_tauV_left]
    have key : ∀ y : Vec K, (∃ j, tauV M (v6 i) = v6 j) → bf M x (tauV M (v6 i)) = 0 := by
      rintro y ⟨j, hj⟩
      rw [hj]
      exact hx j
    fin_cases i
    · simp only [map_eq_zero_iff _ M.τ.injective]
      exact key a ⟨2, rfl⟩
    · simp only [map_eq_zero_iff _ M.τ.injective]
      exact key a ⟨3, rfl⟩
    · simp only [map_eq_zero_iff _ M.τ.injective]
      exact key a ⟨0, by simp [v6, tauV_tauV]⟩
    · simp only [map_eq_zero_iff _ M.τ.injective]
      exact key a ⟨1, by simp [v6, tauV_tauV]⟩
    · simp only [map_eq_zero_iff _ M.τ.injective]
      exact key a ⟨4, by simp [v6, hτr]⟩
    · simp only [map_eq_zero_iff _ M.τ.injective]
      exact key a ⟨5, by simp [v6, hτf]⟩
  obtain ⟨z, hz, hz0', hτz⟩ := exists_fixed_vec hδ hS hz0 hz0ne
  rw [hmem] at hz
  refine ⟨z, hz0', ⟨hz 0, hz 1, hz 2, hz 3⟩, hz 4, hz 5, hτz⟩

end Build

section Zeta

variable {M} {a b r : Vec K}

theorem zeta_ne {f z : Vec K} (hFa : IsFF M a) (hab : bf M a b = 0) (hbb : bf M b b = 0)
    (hD : gram M a b ≠ 0) (hr : InW M a b r) (hrr : bf M r r = 0) (hrf : bf M r f = 1)
    (hz : InW M a b z) (hzr : bf M z r = 0) (hzf : bf M z f = 0) (hz0 : z ≠ 0) :
    bf M z z ≠ 0 := by
  intro hzz
  have hba : bf M b a = 0 := by rw [bf_comm]; exact hab
  have hli : ¬ LinearIndependent K ![a, b, r, z] := by
    intro hli
    have h3 := ts3 M ![a, b, r, z] hli (by
      intro i j
      fin_cases i <;> fin_cases j
      · exact hFa.1
      · exact hab
      · simpa using (bf_comm M a r).trans hr.1
      · simpa using (bf_comm M a z).trans hz.1
      · simpa using hba
      · simpa using hbb
      · simpa using (bf_comm M b r).trans hr.2.1
      · simpa using (bf_comm M b z).trans hz.2.1
      · simpa using hr.1
      · simpa using hr.2.1
      · simpa using hrr
      · simpa using (bf_comm M r z).trans hzr
      · simpa using hz.1
      · simpa using hz.2.1
      · simpa using hzr
      · simpa using hzz)
    omega
  obtain ⟨g, hg, i, hi⟩ := Fintype.not_linearIndependent_iff.1 hli
  have hg' : g 0 • a + g 1 • b + (g 2 • r + g 3 • z) = 0 := by
    simpa [Fin.sum_univ_four, add_assoc] using hg
  have hy : InW M a b (g 2 • r + g 3 • z) := (hr.smul _).add (hz.smul _)
  obtain ⟨h0, h1⟩ := coeff_zero hD hg' hy.2.2.1 hy.2.2.2
  rw [h0, h1, zero_smul, zero_smul, zero_add, zero_add] at hg'
  have h2 : g 2 = 0 := by
    have := congrArg (fun x => bf M x f) hg'
    simp only [bf_add_left, bf_smul_left, bf_zero_left, hzf] at this
    rw [hrf] at this
    simpa using this
  rw [h2, zero_smul, zero_add] at hg'
  have h3 : g 3 = 0 := (smul_eq_zero.1 hg').resolve_right hz0
  fin_cases i
  · exact hi h0
  · exact hi h1
  · exact hi h2
  · exact hi h3

end Zeta

section Exists

variable {M} {a b r : Vec K}

theorem exists_frame [Finite K] (hq : 1 < M.q) (hFa : IsFF M a) (hFb : IsFF M b)
    (hab : bf M a b = 0) (hD : gram M a b ≠ 0) (hr : InW M a b r) (hrr : bf M r r = 0)
    (hτr : tauV M r = r) (hr0 : r ≠ 0) :
    ∃ F : Frame M, F.a = a ∧ F.b = b ∧ F.r = r ∧ F.gd.ζ ≠ 0 := by
  obtain ⟨f, hfW, hτf, hff, hrf⟩ := exists_f hFa.1 hab hFb.1 hD hr hrr hτr hr0
  obtain ⟨z, hz0, hzW, hzr, hzf, hτz⟩ := exists_z (a := a) (b := b) (r := r) hq hτr hτf
  have hζ := zeta_ne hFa hab hFb.1 hD hr hrr hrf hzW hzr hzf hz0
  refine ⟨⟨a, b, f, z, r, hFa.1, hab, hFb.1, hfW.1, hfW.2.1, hfW.2.2.1, hfW.2.2.2, hzW.1,
    hzW.2.1, hzW.2.2.1, hzW.2.2.2, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, hff, ?_, ?_, hzr, hrr,
    hτf, hτz, hτr⟩, rfl, rfl, rfl, hζ⟩
  · rw [bf_comm]; exact hzf
  · rw [bf_comm]; exact hrf

end Exists

end CFSG.ClassicalInvolution.PhanB3.S.Std.T
