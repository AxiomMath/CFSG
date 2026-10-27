module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.FieldTheory.ChevalleyWarning
public import CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311.FixedBasis

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311
open QuadraticMap Module MvPolynomial

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem Q_three (Q : QuadraticForm K V) (x : Fin 3 → K) (z : Fin 3 → V) :
    Q (∑ i, x i • z i) = x 0 * x 0 * Q (z 0) + x 1 * x 1 * Q (z 1) + x 2 * x 2 * Q (z 2)
      + x 0 * x 1 * polar Q (z 0) (z 1) + x 0 * x 2 * polar Q (z 0) (z 2)
      + x 1 * x 2 * polar Q (z 1) (z 2) := by
  rw [Fin.sum_univ_three, QuadraticMap.map_add Q, QuadraticMap.map_add Q, QuadraticMap.map_smul,
    QuadraticMap.map_smul, QuadraticMap.map_smul]
  simp only [polar_add_left, polar_smul_left, polar_smul_right, smul_eq_mul]
  ring


theorem exists_comb_singular [Finite K] [CharP K 2] (σ : K ≃+* K) (Q : QuadraticForm K V)
    (z : Fin 3 → V) (hQ : ∀ i, σ (Q (z i)) = Q (z i))
    (hB : ∀ i j, σ (polar Q (z i) (z j)) = polar Q (z i) (z j)) :
    ∃ x : Fin 3 → K, x ≠ 0 ∧ (∀ i, σ (x i) = x i) ∧ Q (∑ i, x i • z i) = 0 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  let k : Subfield K := (σ : K →+* K).eqLocusField (RingHom.id K)
  have hk : ∀ a : K, a ∈ k ↔ σ a = a := fun a => Iff.rfl
  have : Finite k := inferInstance
  have : Fintype k := Fintype.ofFinite k
  have hchar : CharP k 2 := inferInstance
  let γ : Fin 3 → Fin 3 → K := fun i j =>
    if i = j then Q (z i) else if i < j then polar Q (z i) (z j) else 0
  have hγ : ∀ i j, γ i j ∈ k := by
    intro i j
    rw [hk]
    simp only [γ]
    split_ifs
    · exact hQ i
    · exact hB i j
    · simp
  let P : MvPolynomial (Fin 3) k :=
    ∑ i, ∑ j, C (⟨γ i j, hγ i j⟩ : k) * (X i * X j)
  have hdeg : P.totalDegree < Fintype.card (Fin 3) := by
    have h : P.totalDegree ≤ 2 := by
      refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun i _ => ?_)
      refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ => ?_)
      have h1 : (X i * X j : MvPolynomial (Fin 3) k).totalDegree ≤ 2 := by
        refine (totalDegree_mul _ _).trans ?_
        rw [totalDegree_X, totalDegree_X]
      refine (totalDegree_mul _ _).trans ?_
      rw [totalDegree_C, zero_add]
      exact h1
    simp only [Fintype.card_fin]
    omega
  have hdvd := char_dvd_card_solutions 2 hdeg
  by_contra hcon
  have hcon' : ∀ x : Fin 3 → k, eval x P = 0 → x = 0 := by
    intro x hx
    by_contra hne
    apply hcon
    refine ⟨fun i => (x i : K), ?_, fun i => (x i).2, ?_⟩
    · intro h0
      apply hne
      funext i
      exact Subtype.ext (congrFun h0 i)
    · have h1 : (k.subtype (eval x P)) = 0 := by rw [hx, map_zero]
      have h2 : k.subtype (eval x P) = ∑ i, ∑ j, γ i j * ((x i : K) * (x j : K)) := by
        simp [P, eval_sum, map_sum]
      rw [h2, Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three] at h1
      rw [Q_three]
      have g00 : γ 0 0 = Q (z 0) := by simp [γ]
      have g11 : γ 1 1 = Q (z 1) := by simp [γ]
      have g22 : γ 2 2 = Q (z 2) := by simp [γ]
      have g01 : γ 0 1 = polar Q (z 0) (z 1) := by
        simp [γ]
      have g02 : γ 0 2 = polar Q (z 0) (z 2) := by
        simp [γ]
      have g12 : γ 1 2 = polar Q (z 1) (z 2) := by
        simp [γ]
      have g10 : γ 1 0 = 0 := by
        simp [γ]
      have g20 : γ 2 0 = 0 := by
        simp [γ]
      have g21 : γ 2 1 = 0 := by
        simp [γ]
      rw [g00, g11, g22, g01, g02, g12, g10, g20, g21] at h1
      linear_combination h1
  have h0 : eval (0 : Fin 3 → k) P = 0 := by simp [P]
  have hpos : 0 < Fintype.card {x : Fin 3 → k // eval x P = 0} :=
    Fintype.card_pos_iff.mpr ⟨⟨0, h0⟩⟩
  have hone : Fintype.card {x : Fin 3 → k // eval x P = 0} ≤ 1 := by
    rw [Fintype.card_le_one_iff]
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    exact Subtype.ext ((hcon' x hx).trans (hcon' y hy).symm)
  have hle := Nat.le_of_dvd hpos hdvd
  omega

theorem polar_semilinear {σ : K ≃+* K} {Q : QuadraticForm K V} (T : V →ₛₗ[(σ : K →+* K)] V)
    (hTQ : ∀ v, Q (T v) = σ (Q v)) (x y : V) : polar Q (T x) (T y) = σ (polar Q x y) := by
  rw [polar, polar, ← map_add, hTQ, hTQ, hTQ, map_sub, map_sub]

theorem polar_self_char_two [CharP K 2] (Q : QuadraticForm K V) (x : V) : polar Q x x = 0 := by
  rw [polar_self]
  simp [CharTwo.two_eq_zero]

theorem polar_sum_smul_left {ι : Type*} [Fintype ι] (Q : QuadraticForm K V) (c : ι → K) (x : ι → V)
    (y : V) : polar Q (∑ i, c i • x i) y = ∑ i, c i * polar Q (x i) y := by
  have h : ∀ v, polar Q v y = (polarBilin Q).flip y v := fun v => by
    simp [LinearMap.flip_apply, polarBilin_apply_apply]
  rw [h, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← h, polar_smul_left, smul_eq_mul]

theorem polar_sum_smul_right {ι : Type*} [Fintype ι] (Q : QuadraticForm K V) (c : ι → K)
    (x : ι → V) (y : V) : polar Q y (∑ i, c i • x i) = ∑ i, c i * polar Q y (x i) := by
  rw [polar_comm, polar_sum_smul_left]
  simp [polar_comm]


structure Frame (Q : QuadraticForm K V) {σ : K ≃+* K} (T : V →ₛₗ[(σ : K →+* K)] V) (r : ℕ) where
  e : Fin r → V
  f : Fin r → V
  Te : ∀ i, T (e i) = e i
  Tf : ∀ i, T (f i) = f i
  Qe : ∀ i, Q (e i) = 0
  Qf : ∀ i, Q (f i) = 0
  ee : ∀ i j, polar Q (e i) (e j) = 0
  ff : ∀ i j, polar Q (f i) (f j) = 0
  ef : ∀ i j, polar Q (e i) (f j) = if i = j then 1 else 0


section Step

variable [Finite K] [CharP K 2] [FiniteDimensional K V] {σ : K ≃+* K} {Q : QuadraticForm K V}
  {T : V →ₛₗ[(σ : K →+* K)] V}

theorem exists_fixed_singular_of_stable (hσσ : ∀ x, σ (σ x) = x) (hσ1 : σ ≠ 1)
    (hTT : ∀ v, T (T v) = v) (hTQ : ∀ v, Q (T v) = σ (Q v)) (S : Submodule K V)
    (hS : ∀ v ∈ S, T v ∈ S) (hdim : 3 ≤ finrank K S) :
    ∃ w ∈ S, w ≠ 0 ∧ T w = w ∧ Q w = 0 := by
  classical
  let TS : S →ₛₗ[(σ : K →+* K)] S := T.restrict hS
  have hTS : ∀ v, TS (TS v) = v := fun v => Subtype.ext (hTT v)
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, σ x₀ ≠ x₀ := by
    by_contra h
    push Not at h
    exact hσ1 (RingEquiv.ext h)
  obtain ⟨b, hb⟩ := exists_fixedBasis hσσ hx₀ TS hTS
  let z : Fin 3 → V := fun i => (b (Fin.castLE hdim i) : V)
  have hz : ∀ i, T (z i) = z i := fun i => congrArg Subtype.val (hb (Fin.castLE hdim i))
  have hQz : ∀ i, σ (Q (z i)) = Q (z i) := fun i => by rw [← hTQ, hz]
  have hBz : ∀ i j, σ (polar Q (z i) (z j)) = polar Q (z i) (z j) := fun i j => by
    rw [← polar_semilinear T hTQ, hz, hz]
  obtain ⟨x, hx0, hxσ, hxQ⟩ := exists_comb_singular σ Q z hQz hBz
  refine ⟨∑ i, x i • z i, ?_, ?_, ?_, hxQ⟩
  · refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (b _).2
  · intro h0
    apply hx0
    have hli : LinearIndependent K (fun i : Fin 3 => b (Fin.castLE hdim i)) :=
      b.linearIndependent.comp _ (Fin.castLE_injective hdim)
    have h1 : ∑ i, x i • b (Fin.castLE hdim i) = 0 := Subtype.ext (by simpa [z] using h0)
    exact funext fun i => (Fintype.linearIndependent_iff.mp hli x h1) i
  · simp only [map_sum, map_smulₛₗ, RingHom.coe_coe, hz, hxσ]


def framePerp {r : ℕ} (F : Frame Q T r) : Submodule K V :=
  LinearMap.ker (LinearMap.pi fun p : Fin r ⊕ Fin r =>
    (polarBilin Q).flip (Sum.elim F.e F.f p))

theorem mem_framePerp {r : ℕ} (F : Frame Q T r) (v : V) :
    v ∈ framePerp F ↔ ∀ p : Fin r ⊕ Fin r, polar Q v (Sum.elim F.e F.f p) = 0 := by
  simp [framePerp, LinearMap.mem_ker, funext_iff]

theorem finrank_framePerp {r : ℕ} (F : Frame Q T r) :
    finrank K V ≤ finrank K (framePerp F) + 2 * r := by
  have h := LinearMap.finrank_range_add_finrank_ker (LinearMap.pi fun p : Fin r ⊕ Fin r =>
    (polarBilin Q).flip (Sum.elim F.e F.f p))
  have h2 : finrank K (LinearMap.range (LinearMap.pi fun p : Fin r ⊕ Fin r =>
      (polarBilin Q).flip (Sum.elim F.e F.f p))) ≤ 2 * r := by
    refine (Submodule.finrank_le _).trans ?_
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    omega
  unfold framePerp
  omega


theorem polar_frame_cases {r : ℕ} (F : Frame Q T r) (u : V) (j : Fin r) :
    polar Q (u - ∑ i, polar Q u (F.f i) • F.e i - ∑ i, polar Q u (F.e i) • F.f i) (F.e j) = 0 ∧
    polar Q (u - ∑ i, polar Q u (F.f i) • F.e i - ∑ i, polar Q u (F.e i) • F.f i) (F.f j) = 0 := by
  have hfe : ∀ i j, polar Q (F.f i) (F.e j) = if j = i then 1 else 0 := by
    intro i j; rw [polar_comm, F.ef]
  constructor
  · rw [polar_sub_left, polar_sub_left, polar_sum_smul_left, polar_sum_smul_left]
    simp only [F.ee, hfe, mul_zero, Finset.sum_const_zero, mul_ite, mul_one, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, sub_zero]
    ring
  · rw [polar_sub_left, polar_sub_left, polar_sum_smul_left, polar_sum_smul_left]
    simp only [F.ff, F.ef, mul_zero, Finset.sum_const_zero, mul_ite, mul_one, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, sub_zero]
    ring


theorem T_mem_framePerp (hTQ : ∀ v, Q (T v) = σ (Q v)) {r : ℕ} (F : Frame Q T r) {v : V}
    (hv : v ∈ framePerp F) : T v ∈ framePerp F := by
  rw [mem_framePerp] at hv ⊢
  intro p
  have hg : T (Sum.elim F.e F.f p) = Sum.elim F.e F.f p := by
    rcases p with i | i
    · exact F.Te i
    · exact F.Tf i
  have h1 := hv p
  calc polar Q (T v) (Sum.elim F.e F.f p) = polar Q (T v) (T (Sum.elim F.e F.f p)) := by rw [hg]
    _ = σ (polar Q v (Sum.elim F.e F.f p)) := polar_semilinear T hTQ _ _
    _ = 0 := by rw [h1, map_zero]

theorem exists_fixed_partner (hQ : (polarBilin Q).Nondegenerate) (hσσ : ∀ x, σ (σ x) = x)
    (hσ1 : σ ≠ 1) (hTT : ∀ v, T (T v) = v) (hTQ : ∀ v, Q (T v) = σ (Q v)) {r : ℕ}
    (F : Frame Q T r) {w : V} (hwS : w ∈ framePerp F) (hw0 : w ≠ 0) (hTw : T w = w)
    (hQw : Q w = 0) :
    ∃ f' ∈ framePerp F, T f' = f' ∧ Q f' = 0 ∧ polar Q w f' = 1 := by
  classical
  obtain ⟨u, hu⟩ : ∃ u, polar Q w u ≠ 0 := by
    by_contra h
    push Not at h
    exact hw0 (hQ.1 w (fun y => by simpa [polarBilin_apply_apply] using h y))
  set u' := u - ∑ i, polar Q u (F.f i) • F.e i - ∑ i, polar Q u (F.e i) • F.f i with hu'
  have hu'S : u' ∈ framePerp F := by
    rw [mem_framePerp]
    rintro (j | j)
    · exact (polar_frame_cases F u j).1
    · exact (polar_frame_cases F u j).2
  have hwe : ∀ i, polar Q w (F.e i) = 0 := fun i => (mem_framePerp F w).mp hwS (Sum.inl i)
  have hwf : ∀ i, polar Q w (F.f i) = 0 := fun i => (mem_framePerp F w).mp hwS (Sum.inr i)
  have hwu' : polar Q w u' ≠ 0 := by
    have : polar Q w u' = polar Q w u := by
      rw [hu', polar_comm Q w, polar_sub_left, polar_sub_left, polar_sum_smul_left,
        polar_sum_smul_left]
      simp only [polar_comm Q (F.e _) w, polar_comm Q (F.f _) w, hwe, hwf, mul_zero,
        Finset.sum_const_zero, sub_zero]
      rw [polar_comm]
    rw [this]; exact hu
  let TS : framePerp F →ₛₗ[(σ : K →+* K)] framePerp F :=
    T.restrict (fun v hv => T_mem_framePerp hTQ F hv)
  have hTS : ∀ v, TS (TS v) = v := fun v => Subtype.ext (hTT v)
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, σ x₀ ≠ x₀ := by
    by_contra h
    push Not at h
    exact hσ1 (RingEquiv.ext h)
  obtain ⟨b, hb⟩ := exists_fixedBasis hσσ hx₀ TS hTS
  obtain ⟨i, hi⟩ : ∃ i, polar Q w (b i : V) ≠ 0 := by
    by_contra h
    push Not at h
    apply hwu'
    have h1 : (⟨u', hu'S⟩ : framePerp F) = ∑ i, b.repr ⟨u', hu'S⟩ i • b i := (b.sum_repr _).symm
    have h2 : u' = ∑ i, b.repr ⟨u', hu'S⟩ i • (b i : V) := by
      have := congrArg (Submodule.subtype (framePerp F)) h1
      simp only [map_sum, map_smul, Submodule.subtype_apply] at this
      exact this
    rw [h2, polar_sum_smul_right]
    simp [h]
  obtain ⟨s, hs⟩ : ∃ s : V, s = (b i : V) := ⟨_, rfl⟩
  rw [← hs] at hi
  have hTs : T s = s := by rw [hs]; exact congrArg Subtype.val (hb i)
  have hsS : s ∈ framePerp F := by rw [hs]; exact (b i).2
  obtain ⟨c, hc⟩ : ∃ c, c = polar Q w s := ⟨_, rfl⟩
  rw [← hc] at hi
  have hσc : σ c = c := by
    rw [hc, ← polar_semilinear T hTQ, hTw, hTs]
  obtain ⟨f₁, hf₁⟩ : ∃ f₁, f₁ = c⁻¹ • s := ⟨_, rfl⟩
  have hTf₁ : T f₁ = f₁ := by
    rw [hf₁, map_smulₛₗ, RingHom.coe_coe, map_inv₀, hσc, hTs]
  have hwf₁ : polar Q w f₁ = 1 := by
    rw [hf₁, polar_smul_right, ← hc, smul_eq_mul, inv_mul_cancel₀ hi]
  have hσQ : σ (Q f₁) = Q f₁ := by rw [← hTQ, hTf₁]
  refine ⟨f₁ + Q f₁ • w, ?_, ?_, ?_, ?_⟩
  · refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ hwS)
    rw [hf₁]; exact Submodule.smul_mem _ _ hsS
  · rw [map_add, map_smulₛₗ, RingHom.coe_coe, hTf₁, hTw, hσQ]
  · rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, hQw, polar_smul_right,
      polar_comm Q f₁ w, hwf₁]
    simp only [smul_eq_mul, mul_zero, mul_one, zero_mul, add_zero]
    exact CharTwo.add_self_eq_zero _
  · rw [polar_add_right, hwf₁, polar_smul_right, polar_self_char_two, smul_zero, add_zero]


theorem exists_frame_succ (hQ : (polarBilin Q).Nondegenerate) (hσσ : ∀ x, σ (σ x) = x)
    (hσ1 : σ ≠ 1) (hTT : ∀ v, T (T v) = v) (hTQ : ∀ v, Q (T v) = σ (Q v)) {r : ℕ}
    (F : Frame Q T r) (hdim : 2 * r + 3 ≤ finrank K V) : Nonempty (Frame Q T (r + 1)) := by
  classical
  have h3 : 3 ≤ finrank K (framePerp F) := by
    have := finrank_framePerp F
    omega
  obtain ⟨w, hwS, hw0, hTw, hQw⟩ := exists_fixed_singular_of_stable hσσ hσ1 hTT hTQ (framePerp F)
    (fun v hv => T_mem_framePerp hTQ F hv) h3
  obtain ⟨f', hf'S, hTf', hQf', hwf'⟩ := exists_fixed_partner hQ hσσ hσ1 hTT hTQ F hwS hw0 hTw hQw
  have hwe : ∀ i, polar Q w (F.e i) = 0 := fun i => (mem_framePerp F w).mp hwS (Sum.inl i)
  have hwf : ∀ i, polar Q w (F.f i) = 0 := fun i => (mem_framePerp F w).mp hwS (Sum.inr i)
  have hfe : ∀ i, polar Q f' (F.e i) = 0 := fun i => (mem_framePerp F f').mp hf'S (Sum.inl i)
  have hff : ∀ i, polar Q f' (F.f i) = 0 := fun i => (mem_framePerp F f').mp hf'S (Sum.inr i)
  refine ⟨⟨Fin.snoc F.e w, Fin.snoc F.f f', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simpa using hTw
    · simpa using F.Te i
  · intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simpa using hTf'
    · simpa using F.Tf i
  · intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simpa using hQw
    · simpa using F.Qe i
  · intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simpa using hQf'
    · simpa using F.Qf i
  · intro i j
    refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
    · simpa using polar_self_char_two Q w
    · simpa using hwe j
    · simpa [polar_comm Q (F.e i) w] using hwe i
    · simpa using F.ee i j
  · intro i j
    refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
    · simpa using polar_self_char_two Q f'
    · simpa using hff j
    · simpa [polar_comm Q (F.f i) f'] using hff i
    · simpa using F.ff i j
  · intro i j
    refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
    · simpa using hwf'
    · simpa [(Fin.castSucc_lt_last j).ne'] using hwf j
    · simpa [polar_comm Q (F.e i) f', (Fin.castSucc_lt_last i).ne] using hfe i
    · simpa [Fin.castSucc_inj] using F.ef i j

theorem exists_frame (hQ : (polarBilin Q).Nondegenerate) (hσσ : ∀ x, σ (σ x) = x)
    (hσ1 : σ ≠ 1) (hTT : ∀ v, T (T v) = v) (hTQ : ∀ v, Q (T v) = σ (Q v)) :
    ∀ r : ℕ, 2 * r + 2 ≤ finrank K V → Nonempty (Frame Q T r) := by
  intro r
  induction r with
  | zero =>
    intro _
    exact ⟨⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
      fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩⟩
  | succ r ih =>
    intro h
    obtain ⟨F⟩ := ih (by omega)
    exact exists_frame_succ hQ hσσ hσ1 hTT hTQ F (by omega)

end Step



end CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311
