module

public import CFSG.GH74.Filter.Statements
public import CFSG.GH74.Filter.ElemAbelian
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd.Basic
public import CFSG.ClassicalGroups.Orthogonal.Simple

public section

namespace CFSG.GH74.Filter

open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin CFSG.Assembly.LowTwoRank
  QuadraticMap
open scoped commutatorElement

section Reflections

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem reflect_comm {v w : V} (h : polar Q v w = 0) :
    reflect Q v * reflect Q w = reflect Q w * reflect Q v := by
  have h1 := reflect_conj (reflect_mem_orthogonalGroup Q v) w
  rw [reflect_apply_of_polar_eq_zero h] at h1
  exact mul_inv_eq_iff_eq_mul.1 h1

theorem reflect_apply_self {v : V} (hv : Q v ≠ 0) : reflect Q v v = -v := by
  rw [reflect_apply hv, polar_self_eq_two_mul, mul_div_assoc, div_self hv, mul_one]
  module

theorem reflect_mul_reflect_mem_commutator (h2 : (2 : K) ≠ 0) {p q : V} (hpq : polar Q p q = 0)
    (hQ : Q p = Q q) (hq : Q q ≠ 0) :
    reflect Q p * reflect Q q ∈
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
  have hQd : Q (p - q) = 2 * Q q := by
    rw [sub_eq_add_neg, QuadraticMap.map_add Q, QuadraticMap.map_neg, polar_neg_right, hpq, hQ]
    ring
  have hd : Q (p - q) ≠ 0 := by rw [hQd]; exact mul_ne_zero h2 hq
  have hpol : polar Q (p - q) q = -(2 * Q q) := by
    rw [polar_sub_left, hpq, polar_self_eq_two_mul]
    ring
  have h3 : reflect Q (p - q) q = p := by
    rw [reflect_apply hd, hpol, hQd, neg_div, div_self (mul_ne_zero h2 hq)]
    module
  have h4 : ⁅reflect Q (p - q), reflect Q q⁆ = reflect Q p * reflect Q q := by
    rw [commutatorElement_def, reflect_conj (reflect_mem_orthogonalGroup Q (p - q)) q, h3,
      reflect_inv]
  rw [← h4]
  exact Subgroup.commutator_mem_commutator (reflect_mem_orthogonalGroup Q _)
    (reflect_mem_orthogonalGroup Q _)

theorem pow_apply_of_eigen {g : V ≃ₗ[K] V} {t : V} {c : K} (h : g t = c • t) (n : ℕ) :
    (g ^ n) t = c ^ n • t := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, LinearEquiv.mul_apply, h, map_smul, ih, smul_smul, pow_succ, mul_comm]

theorem prod_ofFn_pow_apply {r : ℕ} {g : Fin r → (V ≃ₗ[K] V)} {t : V} {c : Fin r → K}
    (h : ∀ i, g i t = c i • t) (a : Fin r → ℕ) :
    (List.ofFn fun i => g i ^ a i).prod t = (∏ i, c i ^ a i) • t := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [List.ofFn_succ, List.prod_cons, Fin.prod_univ_succ, LinearEquiv.mul_apply,
      ih (g := fun i => g i.succ) (c := fun i => c i.succ) (fun i => h i.succ)
        (fun i => a i.succ), map_smul, pow_apply_of_eigen (h 0), smul_smul, mul_comm]

end Reflections

section Signs

variable {K : Type*} [Field K]

theorem eq_zero_of_signs (h2 : (2 : K) ≠ 0) (a : Fin 5 → Fin 2) (c : K)
    (h0 : (-1 : K) ^ (a 0 : ℕ) = c) (h1 : (-1 : K) ^ (a 1 : ℕ) = c)
    (h2' : (-1 : K) ^ (a 2 : ℕ) = c) (h34 : (-1 : K) ^ (a 3 : ℕ) * (-1 : K) ^ (a 4 : ℕ) = c)
    (h3 : (-1 : K) ^ (a 3 : ℕ) = c) (h4 : (-1 : K) ^ (a 4 : ℕ) = c) : a = 0 := by
  have hne : (-1 : K) ≠ 1 := fun h => h2 (by linear_combination (-1 : K) * h)
  have hone : ∀ x : Fin 2, (-1 : K) ^ (x : ℕ) = 1 → x = 0 := by
    intro x hx
    fin_cases x
    · rfl
    · exact absurd (by simpa using hx) hne
  have hc0 : c ≠ 0 := by
    rw [← h3]
    exact pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)
  have hc1 : c = 1 := by
    have hcc : c * c = c := by
      calc c * c = (-1 : K) ^ (a 3 : ℕ) * (-1 : K) ^ (a 4 : ℕ) := by rw [h3, h4]
        _ = c := h34
    exact mul_right_cancel₀ hc0 (by rw [hcc, one_mul])
  subst hc1
  funext k
  fin_cases k
  · exact hone _ h0
  · exact hone _ h1
  · exact hone _ h2'
  · exact hone _ h3
  · exact hone _ h4

end Signs

section Frame

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

abbrev FrameIdx : Type := Fin 3 ⊕ Unit ⊕ Fin 3

def frameNorm (K : Type*) [Field K] : FrameIdx → K
  | .inl _ => 1
  | .inr (.inl _) => 1
  | .inr (.inr _) => -1

structure Frame7 (Q : QuadraticForm K V) where
  v : FrameIdx → V
  Q_v : ∀ i, Q (v i) = frameNorm K i
  orth : ∀ i j, i ≠ j → polar Q (v i) (v j) = 0

variable {Q : QuadraticForm K V}

theorem frameNorm_ne_zero (i : FrameIdx) : frameNorm K i ≠ 0 := by
  rcases i with i | ⟨⟩ | i <;> simp [frameNorm]

namespace Frame7

variable (F : Frame7 Q)

theorem Q_ne_zero (i : FrameIdx) : Q (F.v i) ≠ 0 := by
  rw [F.Q_v]
  exact frameNorm_ne_zero i

theorem v_ne_zero (i : FrameIdx) : F.v i ≠ 0 := fun h =>
  F.Q_ne_zero i (by rw [h, QuadraticMap.map_zero])

noncomputable def R (i : FrameIdx) : V ≃ₗ[K] V := reflect Q (F.v i)

theorem R_mem (i : FrameIdx) : F.R i ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
  reflect_mem_orthogonalGroup Q _

theorem R_mul_self (i : FrameIdx) : F.R i * F.R i = 1 := reflect_mul_self Q _

theorem R_comm (i j : FrameIdx) : F.R i * F.R j = F.R j * F.R i := by
  by_cases h : i = j
  · rw [h]
  · exact reflect_comm (F.orth i j h)

def sgn (K : Type*) [Field K] (i j : FrameIdx) : K := if i = j then -1 else 1

theorem R_apply_v (i j : FrameIdx) : F.R i (F.v j) = sgn K i j • F.v j := by
  rcases eq_or_ne i j with rfl | h
  · simp [R, sgn, reflect_apply_self (F.Q_ne_zero i)]
  · simp [R, sgn, h, reflect_apply_of_polar_eq_zero (F.orth i j h)]

def pair : Fin 5 → FrameIdx × FrameIdx :=
  ![(.inl 0, .inl 1), (.inl 0, .inl 2), (.inl 0, .inr (.inl ())),
    (.inr (.inr 0), .inr (.inr 1)), (.inr (.inr 0), .inr (.inr 2))]

noncomputable def g (k : Fin 5) : V ≃ₗ[K] V := F.R (pair k).1 * F.R (pair k).2

def eig (K : Type*) [Field K] (k : Fin 5) (j : FrameIdx) : K :=
  sgn K (pair k).2 j * sgn K (pair k).1 j

theorem g_apply_v (k : Fin 5) (j : FrameIdx) : F.g k (F.v j) = eig K k j • F.v j := by
  rw [g, LinearEquiv.mul_apply, R_apply_v, map_smul, R_apply_v, smul_smul, eig]

theorem R_mul_R_mem (h2 : (2 : K) ≠ 0) {i i' : FrameIdx} (hne : i ≠ i')
    (hν : frameNorm K i = frameNorm K i') :
    F.R i * F.R i' ∈
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ :=
  reflect_mul_reflect_mem_commutator h2 (F.orth i i' hne) (by rw [F.Q_v, F.Q_v, hν])
    (F.Q_ne_zero i')

theorem pair_ne : ∀ k : Fin 5, (pair k).1 ≠ (pair k).2 := by decide

theorem frameNorm_pair (K : Type*) [Field K] :
    ∀ k : Fin 5, frameNorm K (pair k).1 = frameNorm K (pair k).2 := by
  intro k
  fin_cases k <;> simp [pair, frameNorm]

theorem g_mem (h2 : (2 : K) ≠ 0) (k : Fin 5) :
    F.g k ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ :=
  F.R_mul_R_mem h2 (pair_ne k) (frameNorm_pair K k)

theorem g_sq (k : Fin 5) : F.g k * F.g k = 1 := by
  have hc := F.R_comm (pair k).1 (pair k).2
  calc F.g k * F.g k
      = F.R (pair k).1 * (F.R (pair k).2 * F.R (pair k).1) * F.R (pair k).2 := by
        simp only [g, mul_assoc]
    _ = F.R (pair k).1 * (F.R (pair k).1 * F.R (pair k).2) * F.R (pair k).2 := by rw [← hc]
    _ = (F.R (pair k).1 * F.R (pair k).1) * (F.R (pair k).2 * F.R (pair k).2) := by
        simp only [mul_assoc]
    _ = 1 := by rw [F.R_mul_self, F.R_mul_self, one_mul]

theorem g_comm (i j : Fin 5) : F.g i * F.g j = F.g j * F.g i := by
  have hc : ∀ a b : FrameIdx, Commute (F.R a) (F.R b) := fun a b => F.R_comm a b
  have := ((hc (pair i).1 (pair j).1).mul_right (hc (pair i).1 (pair j).2)).mul_left
    ((hc (pair i).2 (pair j).1).mul_right (hc (pair i).2 (pair j).2))
  exact this

theorem g_not_mem_scalars (h2 : (2 : K) ≠ 0) (a : Fin 5 → Fin 2) (ha : a ≠ 0) :
    (List.ofFn fun k => F.g k ^ (a k : ℕ)).prod ∉ scalars K V := by
  intro hmem
  obtain ⟨c, hc⟩ := mem_scalars.1 hmem
  have hj : ∀ j : FrameIdx, ∏ k : Fin 5, (eig K k j) ^ (a k : ℕ) = c := by
    intro j
    have h := prod_ofFn_pow_apply (g := F.g) (t := F.v j) (c := fun k => eig K k j)
      (fun k => F.g_apply_v k j) (fun k => (a k : ℕ))
    rw [hc (F.v j)] at h
    exact (smul_left_injective K (F.v_ne_zero j) h).symm
  apply ha
  refine eq_zero_of_signs h2 a c ?_ ?_ ?_ ?_ ?_ ?_
  · simpa [Fin.prod_univ_five, eig, sgn, pair] using hj (.inl 1)
  · simpa [Fin.prod_univ_five, eig, sgn, pair] using hj (.inl 2)
  · simpa [Fin.prod_univ_five, eig, sgn, pair] using hj (.inr (.inl ()))
  · simpa [Fin.prod_univ_five, eig, sgn, pair] using hj (.inr (.inr 0))
  · simpa [Fin.prod_univ_five, eig, sgn, pair] using hj (.inr (.inr 1))
  · simpa [Fin.prod_univ_five, eig, sgn, pair] using hj (.inr (.inr 2))

end Frame7

end Frame

section Pairs

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

def vecP (P : HypPair Q) (s : K) : V := P.e + s • P.f

theorem Q_vecP (P : HypPair Q) (s : K) : Q (vecP P s) = s := by
  rw [vecP, QuadraticMap.map_add Q, map_smul_eq_sq, polar_smul_right_eq, P.Q_e, P.Q_f, P.polar_ef]
  ring

theorem polar_vecP_vecP_of_orth {P P' : HypPair Q} (h : P.Orth P') (s t : K) :
    polar Q (vecP P s) (vecP P' t) = 0 := by
  simp only [vecP, polar_add_left, polar_add_right, polar_smul_left_eq, polar_smul_right_eq, h.ee,
    h.ef, h.fe, h.ff]
  ring

theorem polar_vecP_vecP_self (P : HypPair Q) (s t : K) :
    polar Q (vecP P s) (vecP P t) = s + t := by
  simp only [vecP, polar_add_left, polar_add_right, polar_smul_left_eq, polar_smul_right_eq,
    P.polar_ee, P.polar_ff, P.polar_ef, P.polar_fe]
  ring

noncomputable def Frame7.ofPairs (P : Fin 3 → HypPair Q) (hP : ∀ i j, i ≠ j → (P i).Orth (P j))
    (w : V) (hw : Q w = 1) (hwe : ∀ i, polar Q w (P i).e = 0) (hwf : ∀ i, polar Q w (P i).f = 0) :
    Frame7 Q where
  v := Sum.elim (fun i => vecP (P i) 1) (Sum.elim (fun _ => w) (fun i => vecP (P i) (-1)))
  Q_v := by
    rintro (i | ⟨⟩ | i)
    · simpa [frameNorm] using Q_vecP (P i) 1
    · simpa [frameNorm] using hw
    · simpa [frameNorm] using Q_vecP (P i) (-1)
  orth := by
    have hwp : ∀ i s, polar Q w (vecP (P i) s) = 0 := fun i s => by
      rw [vecP, polar_add_right, polar_smul_right_eq, hwe, hwf]
      ring
    have hpw : ∀ i s, polar Q (vecP (P i) s) w = 0 := fun i s => by rw [polar_comm, hwp]
    rintro (i | ⟨⟩ | i) (j | ⟨⟩ | j) hij
    · exact polar_vecP_vecP_of_orth (hP i j (fun h => hij (by rw [h]))) _ _
    · exact hpw i 1
    · by_cases h : i = j
      · subst h
        show polar Q (vecP (P i) 1) (vecP (P i) (-1)) = 0
        rw [polar_vecP_vecP_self]
        ring
      · exact polar_vecP_vecP_of_orth (hP i j h) _ _
    · exact hwp j 1
    · exact absurd rfl hij
    · exact hwp j (-1)
    · by_cases h : i = j
      · subst h
        show polar Q (vecP (P i) (-1)) (vecP (P i) 1) = 0
        rw [polar_vecP_vecP_self]
        ring
      · exact polar_vecP_vecP_of_orth (hP i j h) _ _
    · exact hpw i (-1)
    · exact polar_vecP_vecP_of_orth (hP i j (fun h => hij (by rw [h]))) _ _

end Pairs

section Models

variable (K : Type) [Field K]

noncomputable def oddRefFrame {n : ℕ} (hn : 3 ≤ n) : Frame7 (quadOdd n K) :=
  Frame7.ofPairs (fun i => oddPair K (Fin.castLE hn i))
    (fun i j hij => oddPair_orth (fun h => hij (Fin.castLE_injective hn h)))
    (Pi.single (Sum.inr (Sum.inr ())) 1)
    (by rw [quadOdd_apply]; simp)
    (fun i => by simp [oddPair_e, polar_quadOdd_single_inl])
    (fun i => by simp [oddPair_f, polar_quadOdd_single_inr_inl])

theorem plusPair_orth_three {n : ℕ} (hn : 4 ≤ n) (i : Fin 3) :
    (plusPair K (⟨3, by omega⟩ : Fin n)).Orth
      (plusPair K (⟨i.val, by have := i.isLt; omega⟩ : Fin n)) :=
  plusPair_orth (fun h => by
    have h1 := congrArg Fin.val h
    have h2 := i.isLt
    simp only at h1
    omega)

noncomputable def plusRefFrame {n : ℕ} (hn : 4 ≤ n) : Frame7 (quadPlus n K) :=
  Frame7.ofPairs (fun i => plusPair K (⟨i.val, by have := i.isLt; omega⟩ : Fin n))
    (fun i j hij => plusPair_orth (fun h => hij (Fin.ext (Fin.mk.inj h))))
    (vecP (plusPair K (⟨3, by omega⟩ : Fin n)) 1) (Q_vecP _ 1)
    (fun i => by
      have h := plusPair_orth_three K hn i
      rw [vecP, polar_add_left, polar_smul_left_eq, h.ee, h.fe]
      ring)
    (fun i => by
      have h := plusPair_orth_three K hn i
      rw [vecP, polar_add_left, polar_smul_left_eq, h.ef, h.ff]
      ring)

noncomputable def minusRefFrame {n : ℕ} (b c : K) (hn : 4 ≤ n) : Frame7 (quadMinus n K b c) :=
  Frame7.ofPairs (fun i => minusPair K b c (⟨i.val, by have := i.isLt; omega⟩ : Fin (n - 1)))
    (fun i j hij => minusPair_orth (fun h => hij (Fin.ext (Fin.mk.inj h))))
    (Pi.single (Sum.inr (Sum.inr (0 : Fin 2))) 1)
    (by rw [quadMinus_apply]; simp)
    (fun i => by simp [minusPair_e, polar_quadMinus_single_inl])
    (fun i => by simp [minusPair_f, polar_quadMinus_single_inr_inl])

end Models

section Transfer

open CFSG.SectionRank.ClassicalOdd

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

theorem not_gen4_statedProj_statedOmega {Q : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K}
    (hQ : ⇑Q = Q₀) (g : Fin 5 → ((ι → K) ≃ₗ[K] (ι → K)))
    (hg : ∀ k, g k ∈
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆)
    (hsq : ∀ k, g k * g k = 1) (hcomm : ∀ i j, g i * g j = g j * g i)
    (hker : ∀ a : Fin 5 → Fin 2, a ≠ 0 →
      (List.ofFn fun k => g k ^ (a k : ℕ)).prod ∉ scalars K (ι → K)) :
    ¬ Gen4 (StatedProj (StatedOmega Q₀)) := by
  have hΩ := statedOmega_eq_comap hQ
  let Φ : StatedOmega Q₀ →* ((ι → K) ≃ₗ[K] (ι → K)) :=
    (toLinEquiv ι K).toMonoidHom.comp (StatedOmega Q₀).subtype
  have hΦinj : Function.Injective Φ := (toLinEquiv ι K).injective.comp Subtype.val_injective
  have hmem : ∀ k, (toLinEquiv ι K).symm (g k) ∈ StatedOmega Q₀ := fun k => by
    rw [hΩ, Subgroup.mem_comap]
    simpa using hg k
  let x : Fin 5 → StatedOmega Q₀ := fun k => ⟨(toLinEquiv ι K).symm (g k), hmem k⟩
  have hΦx : ∀ k, Φ (x k) = g k := fun k => (toLinEquiv ι K).apply_symm_apply (g k)
  let π := QuotientGroup.mk' ((StatedScalars ι K).subgroupOf (StatedOmega Q₀))
  refine not_gen4_of_commuting_involutions (r := 5) le_rfl (fun k => π (x k)) ?_ ?_ ?_
  · intro k
    show π (x k) ^ 2 = 1
    rw [← map_pow]
    have : x k ^ 2 = 1 := hΦinj (by rw [map_pow, hΦx, map_one, pow_two, hsq])
    rw [this, map_one]
  · intro i j
    show π (x i) * π (x j) = π (x j) * π (x i)
    rw [← map_mul, ← map_mul]
    exact congrArg π (hΦinj (by rw [map_mul, map_mul, hΦx, hΦx, hcomm]))
  · intro a ha hone
    apply hker a ha
    have h1 : π (List.ofFn fun i => x i ^ (a i : ℕ)).prod = 1 := by
      rw [map_list_prod, List.map_ofFn]
      simpa [Function.comp_def, map_pow] using hone
    have h2 := h1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
      mem_statedScalars_iff] at h2
    have h3 : Φ (List.ofFn fun i => x i ^ (a i : ℕ)).prod =
        (List.ofFn fun k => g k ^ (a k : ℕ)).prod := by
      rw [map_list_prod, List.map_ofFn]
      simp [Function.comp_def, map_pow, hΦx]
    rw [← h3]
    exact h2

end Transfer

theorem t_POmegaOdd : S_POmegaOdd := by
  intro G _ _ n p f hp2 hn hm
  obtain ⟨⟨hp, hf, hn3, -⟩, K, _, _, hK, ⟨e⟩⟩ := hm
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := CFSG.SectionRank.ClassicalOdd.charP_of_card hK
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP p hp2
  let F := oddRefFrame K hn
  exact not_gen4_of_mulEquiv e.symm (not_gen4_statedProj_statedOmega (coe_quadOdd n K) F.g
    (F.g_mem h2) F.g_sq F.g_comm (F.g_not_mem_scalars h2))

theorem t_POmegaPlus_odd : S_POmegaPlus_odd := by
  intro G _ _ n p f hp2 hm
  obtain ⟨⟨hp, hf, hn⟩, K, _, _, hK, ⟨e⟩⟩ := hm
  have hn4 : 4 ≤ n := hn
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := CFSG.SectionRank.ClassicalOdd.charP_of_card hK
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP p hp2
  let F := plusRefFrame K hn4
  exact not_gen4_of_mulEquiv e.symm (not_gen4_statedProj_statedOmega (coe_quadPlus n K) F.g
    (F.g_mem h2) F.g_sq F.g_comm (F.g_not_mem_scalars h2))

theorem t_POmegaMinus_odd : S_POmegaMinus_odd := by
  intro G _ _ n p f hp2 hm
  obtain ⟨⟨hp, hf, hn⟩, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := hm
  have hn4 : 4 ≤ n := hn
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := CFSG.SectionRank.ClassicalOdd.charP_of_card hK
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP p hp2
  let F := minusRefFrame K b c hn4
  exact not_gen4_of_mulEquiv e.symm (not_gen4_statedProj_statedOmega (coe_quadMinus n K b c) F.g
    (F.g_mem h2) F.g_sq F.g_comm (F.g_not_mem_scalars h2))

end CFSG.GH74.Filter
