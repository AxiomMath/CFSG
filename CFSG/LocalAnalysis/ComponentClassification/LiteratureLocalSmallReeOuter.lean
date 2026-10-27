module

public import CFSG.LocalAnalysis.ComponentClassification.LiteratureLocalSmallReeAutCore
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiOppositeSylow
public import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear
public import CFSG.LocalAnalysis.ComponentClassification.LiteratureLocalSmallReeFrobenius

public noncomputable section

namespace CFSG.ComponentClassification.LiteratureLocal.SmallRee

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.Walter.Ree.Model CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

variable {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K ReeTag.G2.prime]

theorem frobeniusΓ_pow_uIn (hK : Nat.card K = 3 ^ (2 * a + 1)) (k : ℕ) (t b c : K) :
    (frobeniusΓ ^ k) (uIn hK t b c) = uIn hK (t ^ 3 ^ k) (b ^ 3 ^ k) (c ^ 3 ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', MulAut.mul_apply, ih]
    apply Subtype.ext
    rw [coe_frobeniusΓ_of_eq_smallReeU (uIn_val hK _ _ _), uIn_val, ← pow_mul, ← pow_mul,
      ← pow_mul, ← pow_succ]

section Pair

variable (hK : Nat.card K = 3 ^ (2 * a + 1)) {w₀ : WeylGroup ReeTag.G2.tag}
  (hw₀ : ∀ w, (coxeterSystem ReeTag.G2.tag).length w ≤ (coxeterSystem ReeTag.G2.tag).length w₀)
  (β : MulAut (ReeTag.G2.reeGamma K a))
  (hβU : ((ReeTag.G2.reeFixedPosUnipotent K a).subgroupOf (ReeTag.G2.reeGamma K a)).map
    β.toMonoidHom = (ReeTag.G2.reeFixedPosUnipotent K a).subgroupOf (ReeTag.G2.reeGamma K a))
  (hβV : (((ReeTag.G2.reeFixedPosUnipotent K a).subgroupOf (ReeTag.G2.reeGamma K a)).map
      (MulAut.conj (longestIn a K hw₀)).toMonoidHom).map β.toMonoidHom =
    ((ReeTag.G2.reeFixedPosUnipotent K a).subgroupOf (ReeTag.G2.reeGamma K a)).map
      (MulAut.conj (longestIn a K hw₀)).toMonoidHom)

include hβU in
theorem pair_mem_U {u : ReeTag.G2.reeGamma K a}
    (hu : (u : ModGL ReeTag.G2.tag K) ∈ ReeTag.G2.reeFixedPosUnipotent K a) :
    ((β u : ReeTag.G2.reeGamma K a) : ModGL ReeTag.G2.tag K) ∈
      ReeTag.G2.reeFixedPosUnipotent K a := by
  have h : β u ∈ ((ReeTag.G2.reeFixedPosUnipotent K a).subgroupOf
      (ReeTag.G2.reeGamma K a)).map β.toMonoidHom := ⟨u, Subgroup.mem_subgroupOf.2 hu, rfl⟩
  rw [hβU] at h
  exact Subgroup.mem_subgroupOf.1 h

include hβU in
theorem pair_surj_U (t b c : K) : ∃ v : ReeTag.G2.reeGamma K a,
    (v : ModGL ReeTag.G2.tag K) ∈ ReeTag.G2.reeFixedPosUnipotent K a ∧ β v = uIn hK t b c := by
  have h : uIn hK t b c ∈ ((ReeTag.G2.reeFixedPosUnipotent K a).subgroupOf
      (ReeTag.G2.reeGamma K a)).map β.toMonoidHom := by
    rw [hβU]
    exact Subgroup.mem_subgroupOf.2 (uIn_mem hK t b c)
  obtain ⟨v, hv, hvβ⟩ := h
  exact ⟨v, Subgroup.mem_subgroupOf.1 hv, hvβ⟩

include hK hw₀ hβU hβV in
theorem pair_torus (s : Kˣ) : ∃ s' : Kˣ, β (hIn hK s) = hIn hK s' := by
  obtain ⟨hn, -, -, -, -, -, -, -, -, -, -, -, -, -, hNUV⟩ :=
    small_Ree_Borel_coset_Sylow_action a K hK w₀ hw₀
  set U' := (ReeTag.G2.reeFixedPosUnipotent K a).subgroupOf (ReeTag.G2.reeGamma K a) with hU'
  set V' := U'.map (MulAut.conj (longestIn a K hw₀)).toMonoidHom with hV'
  have hNUV' : Subgroup.normalizer (U' : Set (ReeTag.G2.reeGamma K a)) ⊓
      Subgroup.normalizer (V' : Set (ReeTag.G2.reeGamma K a)) =
        (ReeTag.G2.reeFixedTorus K a).subgroupOf (ReeTag.G2.reeGamma K a) := hNUV
  have hmem : hIn hK s ∈ Subgroup.normalizer (U' : Set (ReeTag.G2.reeGamma K a)) ⊓
      Subgroup.normalizer (V' : Set (ReeTag.G2.reeGamma K a)) := by
    rw [hNUV']
    exact Subgroup.mem_subgroupOf.2 (by rw [hIn_val]; exact smallReeH_mem hK s)
  have h1 : β (hIn hK s) ∈ Subgroup.normalizer (U' : Set (ReeTag.G2.reeGamma K a)) ⊓
      Subgroup.normalizer (V' : Set (ReeTag.G2.reeGamma K a)) := by
    obtain ⟨h2, h3⟩ := Subgroup.mem_inf.1 hmem
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · have h4 : β (hIn hK s) ∈ (Subgroup.normalizer (U' : Set (ReeTag.G2.reeGamma K a))).map
          β.toMonoidHom := ⟨_, h2, rfl⟩
      rwa [Subgroup.map_equiv_normalizer_eq, hβU] at h4
    · have h4 : β (hIn hK s) ∈ (Subgroup.normalizer (V' : Set (ReeTag.G2.reeGamma K a))).map
          β.toMonoidHom := ⟨_, h3, rfl⟩
      rwa [Subgroup.map_equiv_normalizer_eq, hβV] at h4
  rw [hNUV'] at h1
  obtain ⟨s', hs'⟩ := exists_smallReeH_eq (Subgroup.mem_subgroupOf.1 h1)
  exact ⟨s', Subtype.ext (by rw [hIn_val, hs'])⟩

include hβU in
theorem pair_U1 (b c : K) : ∃ b' c' : K, β (uIn hK 0 b c) = uIn hK 0 b' c' := by
  obtain ⟨t', b', c', h⟩ := exists_uIn_eq hK (pair_mem_U β hβU (uIn_mem hK 0 b c))
  have h3 : uIn hK (0 : K) b c ^ 3 = 1 := by
    rw [uIn_pow_three, zero_pow (by norm_num), zero_mul, neg_zero, uIn_zero]
  have h4 := congrArg β h3
  rw [map_pow, map_one, h, uIn_pow_three, ← uIn_zero hK] at h4
  have h5 := (uIn_inj hK h4).2.2
  have h6 : t' ^ 2 * smallReeSigma a t' = 0 := by linear_combination -h5
  have ht' : t' = 0 := by
    rcases mul_eq_zero.1 h6 with h7 | h7
    · exact pow_eq_zero_iff (by norm_num) |>.1 h7
    · exact pow_eq_zero_iff (by positivity) |>.1 h7
  exact ⟨b', c', by rw [h, ht']⟩

include hK hw₀ hβU hβV in
theorem pair_semilinear : ∃ c : K, c ≠ 0 ∧ ∃ σ : K ≃+* K, ∀ x b e : K, ∃ b' e' : K,
    β (uIn hK x b e) = uIn hK (c * σ x) b' e' := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hbij, -⟩ := small_Ree_field_power_identities a K hK
  choose τ hτ using pair_torus hK hw₀ β hβU hβV
  have hfirst : ∀ x : K, ∃ ν b' e' : K, β (uIn hK x 0 0) = uIn hK ν b' e' := fun x =>
    exists_uIn_eq hK (pair_mem_U β hβU (uIn_mem hK x 0 0))
  choose ν b₁ e₁ hν using hfirst
  have hsplit : ∀ x b e : K, uIn hK x b e = uIn hK x 0 0 * uIn hK 0 b e := by
    intro x b e
    rw [uIn_mul]
    congr 1 <;> ring
  have hgen : ∀ x b e : K, ∃ b' e' : K, β (uIn hK x b e) = uIn hK (ν x) b' e' := by
    intro x b e
    obtain ⟨b', e', h⟩ := pair_U1 hK β hβU b e
    refine ⟨b₁ x + b' + smallReeSigma a (ν x) * 0,
      e₁ x + e' - b₁ x * 0 + smallReeSigma a (ν x) * 0 ^ 2, ?_⟩
    rw [hsplit, map_mul, hν, h, uIn_mul, add_zero]
  have hadd : ∀ x y : K, ν (x + y) = ν x + ν y := by
    intro x y
    have e1 : uIn hK x 0 0 * uIn hK y 0 0 =
        uIn hK (x + y) 0 0 * uIn hK 0 (smallReeSigma a x * y) (smallReeSigma a x * y ^ 2) := by
      rw [uIn_mul, uIn_mul]
      congr 1 <;> ring
    have e2 := congrArg β e1
    obtain ⟨b', e', h⟩ := pair_U1 hK β hβU (smallReeSigma a x * y) (smallReeSigma a x * y ^ 2)
    rw [map_mul, map_mul, hν, hν, hν, h, uIn_mul, uIn_mul] at e2
    have e3 := (uIn_inj hK e2).1
    rw [add_zero] at e3
    exact e3.symm
  have htor : ∀ (s : Kˣ) (x : K), ν (((s ^ (2 * 3 ^ a - 1) : Kˣ) : K) * x) =
      (((τ s) ^ (2 * 3 ^ a - 1) : Kˣ) : K) * ν x := by
    intro s x
    have e1 := congrArg β (hIn_conj_uIn hK s x 0 0)
    simp only [mul_zero] at e1
    rw [map_mul, map_mul, map_inv, hτ, hν, hIn_conj_uIn, hν] at e1
    exact (uIn_inj hK e1).1.symm
  have hinj : ∀ x : K, ν x = 0 → x = 0 := by
    intro x hx
    have h1 : β (uIn hK x 0 0) ^ 3 = 1 := by
      rw [hν, hx, uIn_pow_three, zero_pow (by norm_num), zero_mul, neg_zero, uIn_zero]
    rw [← map_pow, uIn_pow_three, ← map_one β] at h1
    have h2 := (uIn_inj hK (β.injective h1 |>.trans (uIn_zero hK).symm)).2.2
    have h6 : x ^ 2 * smallReeSigma a x = 0 := by linear_combination -h2
    rcases mul_eq_zero.1 h6 with h7 | h7
    · exact pow_eq_zero_iff (by norm_num) |>.1 h7
    · exact pow_eq_zero_iff (by positivity) |>.1 h7
  set c := ν 1 with hc
  have hc0 : c ≠ 0 := fun h => one_ne_zero (hinj 1 h)
  have hmulψ : ∀ (s : Kˣ) (y : K), c⁻¹ * ν (((s ^ (2 * 3 ^ a - 1) : Kˣ) : K) * y) =
      (c⁻¹ * ν (((s ^ (2 * 3 ^ a - 1) : Kˣ) : K))) * (c⁻¹ * ν y) := by
    intro s y
    have h1 := htor s y
    have h2 := htor s 1
    rw [mul_one] at h2
    rw [h1, h2, ← hc]
    field_simp
  have hmul : ∀ y z : K, c⁻¹ * ν (y * z) = (c⁻¹ * ν y) * (c⁻¹ * ν z) := by
    intro y z
    by_cases hy : y = 0
    · subst hy
      have h0 : ν 0 = 0 := by
        have := hadd 0 0
        rw [add_zero] at this
        linear_combination -this
      rw [zero_mul, h0, mul_zero, zero_mul]
    · obtain ⟨s, hs0⟩ := hbij.2 (Units.mk0 y hy)
      have hs : ((s ^ (2 * 3 ^ a - 1) : Kˣ) : K) = y := by
        have : s ^ (2 * 3 ^ a - 1) = Units.mk0 y hy := hs0
        rw [this, Units.val_mk0]
      rw [← hs]
      exact hmulψ s z
  let g : K →+* K :=
    { toFun := fun y => c⁻¹ * ν y
      map_one' := by rw [← hc, inv_mul_cancel₀ hc0]
      map_mul' := hmul
      map_zero' := by
        have := hadd 0 0
        rw [add_zero] at this
        have h0 : ν 0 = 0 := by linear_combination -this
        rw [h0, mul_zero]
      map_add' := fun y z => by rw [hadd, mul_add] }
  have hginj : Function.Injective g := g.injective
  let σ : K ≃+* K := RingEquiv.ofBijective g hginj.bijective_of_finite
  refine ⟨c, hc0, σ, fun x b e => ?_⟩
  obtain ⟨b', e', h⟩ := hgen x b e
  refine ⟨b', e', ?_⟩
  rw [h]
  congr 1
  change ν x = c * (c⁻¹ * ν x)
  field_simp

end Pair

section Field

variable (hK : Nat.card K = 3 ^ (2 * a + 1))
include hK

omit [CharP K ReeTag.G2.prime] in
theorem dvd_of_forall_pow_three_pow_eq {k : ℕ} (h : ∀ x : K, x ^ 3 ^ k = x) :
    2 * a + 1 ∣ k := by
  classical
  have := Fintype.ofFinite K
  have hq : ∀ x : K, x ^ 3 ^ (2 * a + 1) = x := fun x => by
    rw [← hK, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card x
  have hnm : ∀ m : ℕ, ∀ x : K, x ^ 3 ^ ((2 * a + 1) * m) = x := by
    intro m
    induction m with
    | zero => intro x; simp
    | succ m ih =>
      intro x
      rw [Nat.mul_succ, pow_add, pow_mul, ih, hq]
  set r := k % (2 * a + 1) with hr
  have hrx : ∀ x : K, x ^ 3 ^ r = x := by
    intro x
    have hk : k = (2 * a + 1) * (k / (2 * a + 1)) + r := (Nat.div_add_mod k _).symm
    have h1 := h x
    rw [hk, pow_add, pow_mul, hnm] at h1
    exact h1
  by_contra hdvd
  have hr0 : 0 < r := Nat.pos_of_ne_zero fun h0 => hdvd (Nat.dvd_of_mod_eq_zero h0)
  have hrn : r < 2 * a + 1 := Nat.mod_lt _ (by omega)
  have h3r : 3 ≤ 3 ^ r := Nat.le_self_pow (by omega) 3
  set P : Polynomial K := Polynomial.X ^ 3 ^ r - Polynomial.X with hP
  have hdeg : P.natDegree = 3 ^ r := by
    rw [hP, Polynomial.natDegree_sub_eq_left_of_natDegree_lt] <;>
      simp only [Polynomial.natDegree_X_pow, Polynomial.natDegree_X]
    omega
  have hP0 : P = 0 := by
    refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero P
      (f := fun x : K => x) (fun _ _ h => h) (fun x => ?_) ?_
    · simp [hP, hrx x]
    · rw [hdeg, ← Nat.card_eq_fintype_card, hK]
      exact Nat.pow_lt_pow_right (by norm_num) hrn
  have hc : P.coeff (3 ^ r) = 1 := by
    simp only [hP, Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_X,
      show (1 : ℕ) ≠ 3 ^ r by omega, ↓reduceIte, sub_zero]
  rw [hP0, Polynomial.coeff_zero] at hc
  exact zero_ne_one hc

@[expose] def frobRing : K ≃+* K :=
  RingEquiv.ofBijective (frobenius K ReeTag.G2.prime)
    (frobenius_inj K ReeTag.G2.prime).bijective_of_finite

omit hK in
theorem frobRing_pow_apply (k : ℕ) (x : K) : (frobRing ^ k : K ≃+* K) x = x ^ 3 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', RingAut.mul_apply, ih]
    change frobenius K ReeTag.G2.prime (x ^ 3 ^ k) = _
    rw [frobenius_def, ← pow_mul]
    rfl

theorem exists_frobRing_pow (σ : K ≃+* K) : ∃ k : ℕ, ∀ x : K, σ x = x ^ 3 ^ k := by
  obtain ⟨hcard, -⟩ := card_ringAut_and_isCyclic Nat.prime_three K hK
  have : Finite (RingAut K) := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  have hord : orderOf (frobRing : K ≃+* K) = 2 * a + 1 := by
    apply Nat.dvd_antisymm
    · apply orderOf_dvd_of_pow_eq_one
      apply RingEquiv.ext
      intro x
      rw [frobRing_pow_apply]
      have := Fintype.ofFinite K
      rw [← hK, Nat.card_eq_fintype_card]
      exact FiniteField.pow_card x
    · apply dvd_of_forall_pow_three_pow_eq hK
      intro x
      rw [← frobRing_pow_apply, pow_orderOf_eq_one]
      rfl
  have htop : Subgroup.zpowers (frobRing : K ≃+* K) = ⊤ := by
    rw [← Subgroup.card_eq_iff_eq_top, Nat.card_zpowers, hord]
    exact hcard.symm
  have hmem : σ ∈ Subgroup.zpowers (frobRing : K ≃+* K) := htop ▸ Subgroup.mem_top σ
  obtain ⟨k, hk⟩ := (mem_powers_iff_mem_zpowers.2 hmem)
  exact ⟨k, fun x => by rw [← hk, frobRing_pow_apply]⟩

end Field

section Steinberg

variable (ha : 1 ≤ a) (hK : Nat.card K = 3 ^ (2 * a + 1)) {w₀ : WeylGroup ReeTag.G2.tag}
  (hw₀ : ∀ w, (coxeterSystem ReeTag.G2.tag).length w ≤ (coxeterSystem ReeTag.G2.tag).length w₀)

include hK in
theorem frobeniusΓ_map_U :
    ((ReeTag.G2.reeFixedPosUnipotent K a).subgroupOf (ReeTag.G2.reeGamma K a)).map
      (frobeniusΓ : MulAut (ReeTag.G2.reeGamma K a)).toMonoidHom =
    (ReeTag.G2.reeFixedPosUnipotent K a).subgroupOf (ReeTag.G2.reeGamma K a) := by
  have : Finite (ModGL ReeTag.G2.tag K) := finite_modGL
  have hle : ((ReeTag.G2.reeFixedPosUnipotent K a).subgroupOf (ReeTag.G2.reeGamma K a)).map
      (frobeniusΓ : MulAut (ReeTag.G2.reeGamma K a)).toMonoidHom ≤
    (ReeTag.G2.reeFixedPosUnipotent K a).subgroupOf (ReeTag.G2.reeGamma K a) := by
    rintro _ ⟨u, hu, rfl⟩
    obtain ⟨t, b, c, rfl⟩ := exists_uIn_eq hK (Subgroup.mem_subgroupOf.1 hu)
    have h := frobeniusΓ_pow_uIn hK 1 t b c
    rw [pow_one] at h
    change frobeniusΓ (uIn hK t b c) ∈ _
    rw [h]
    exact Subgroup.mem_subgroupOf.2 (uIn_mem hK _ _ _)
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective
    (f := (frobeniusΓ : MulAut (ReeTag.G2.reeGamma K a)).toMonoidHom)
    (frobeniusΓ : MulAut (ReeTag.G2.reeGamma K a)).injective]

include hK in
theorem frobeniusΓ_map_V :
    (((ReeTag.G2.reeFixedPosUnipotent K a).subgroupOf (ReeTag.G2.reeGamma K a)).map
      (MulAut.conj (longestIn a K hw₀)).toMonoidHom).map
        (frobeniusΓ : MulAut (ReeTag.G2.reeGamma K a)).toMonoidHom =
    ((ReeTag.G2.reeFixedPosUnipotent K a).subgroupOf (ReeTag.G2.reeGamma K a)).map
      (MulAut.conj (longestIn a K hw₀)).toMonoidHom := by
  have hcomm : (frobeniusΓ : MulAut (ReeTag.G2.reeGamma K a)).toMonoidHom.comp
      (MulAut.conj (longestIn a K hw₀)).toMonoidHom =
      (MulAut.conj (longestIn a K hw₀)).toMonoidHom.comp
        (frobeniusΓ : MulAut (ReeTag.G2.reeGamma K a)).toMonoidHom := by
    ext g
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul,
      map_inv, frobeniusΓ_longestIn hw₀]
  rw [Subgroup.map_map, hcomm, ← Subgroup.map_map, frobeniusΓ_map_U hK]

include hK hw₀ in
theorem conj_hIn_map (s : Kˣ) :
    ((ReeTag.G2.reeFixedPosUnipotent K a).subgroupOf (ReeTag.G2.reeGamma K a)).map
      (MulAut.conj (hIn hK s)).toMonoidHom =
      (ReeTag.G2.reeFixedPosUnipotent K a).subgroupOf (ReeTag.G2.reeGamma K a) ∧
    (((ReeTag.G2.reeFixedPosUnipotent K a).subgroupOf (ReeTag.G2.reeGamma K a)).map
      (MulAut.conj (longestIn a K hw₀)).toMonoidHom).map (MulAut.conj (hIn hK s)).toMonoidHom =
    ((ReeTag.G2.reeFixedPosUnipotent K a).subgroupOf (ReeTag.G2.reeGamma K a)).map
      (MulAut.conj (longestIn a K hw₀)).toMonoidHom := by
  obtain ⟨hn, -, -, -, -, -, -, -, -, -, -, -, -, -, hNUV⟩ :=
    small_Ree_Borel_coset_Sylow_action a K hK w₀ hw₀
  have hmem : hIn hK s ∈ (ReeTag.G2.reeFixedTorus K a).subgroupOf (ReeTag.G2.reeGamma K a) :=
    Subgroup.mem_subgroupOf.2 (by rw [hIn_val]; exact smallReeH_mem hK s)
  have hNUV' : Subgroup.normalizer
      (((ReeTag.G2.reeFixedPosUnipotent K a).subgroupOf (ReeTag.G2.reeGamma K a) :
        Subgroup (ReeTag.G2.reeGamma K a)) : Set (ReeTag.G2.reeGamma K a)) ⊓
      Subgroup.normalizer ((((ReeTag.G2.reeFixedPosUnipotent K a).subgroupOf
        (ReeTag.G2.reeGamma K a)).map (MulAut.conj (longestIn a K hw₀)).toMonoidHom :
          Subgroup (ReeTag.G2.reeGamma K a)) : Set (ReeTag.G2.reeGamma K a)) =
        (ReeTag.G2.reeFixedTorus K a).subgroupOf (ReeTag.G2.reeGamma K a) := hNUV
  rw [← hNUV'] at hmem
  exact ⟨map_conj_eq_of_mem_normalizer (Subgroup.mem_inf.1 hmem).1,
    map_conj_eq_of_mem_normalizer (Subgroup.mem_inf.1 hmem).2⟩

include ha hK in
theorem exists_eq_conj_mul_frobeniusΓ_pow (α : MulAut (ReeTag.G2.reeGamma K a)) :
    ∃ (g : ReeTag.G2.reeGamma K a) (k : ℕ), α = MulAut.conj g * frobeniusΓ ^ k := by
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element ReeTag.G2.tag
  have : Finite (ModGL ReeTag.G2.tag K) := finite_modGL
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hn, hηξ, hfaith, htrans, -, -, hreg, hcardΩ, -, -, ⟨P, hP⟩, hstab, hUn, -, -⟩ :=
    small_Ree_Borel_coset_Sylow_action a K hK w₀ hw₀
  have := hfaith
  have := htrans
  set U' := (ReeTag.G2.reeFixedPosUnipotent K a).subgroupOf (ReeTag.G2.reeGamma K a) with hU'
  set n' := longestIn a K hw₀ with hn'
  have hq : 3 ≤ 3 ^ (2 * a + 1) := Nat.le_self_pow (by omega) 3
  have hΩ : 3 ≤ Nat.card (ReeTag.G2.reeGamma K a ⧸
      (ReeTag.G2.reeFixedBorel K a).subgroupOf (ReeTag.G2.reeGamma K a)) := by
    rw [hcardΩ]
    have : 3 ≤ (3 ^ (2 * a + 1)) ^ 3 := hq.trans (Nat.le_self_pow (by norm_num) _)
    omega
  have hUξ : (P : Subgroup (ReeTag.G2.reeGamma K a)) ≤
      MulAction.stabilizer (ReeTag.G2.reeGamma K a) (QuotientGroup.mk 1 :
        ReeTag.G2.reeGamma K a ⧸
          (ReeTag.G2.reeFixedBorel K a).subgroupOf (ReeTag.G2.reeGamma K a)) := by
    rw [hP, hstab]
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact ReeTag.reeFixedPosUnipotent_le_reeFixedBorel hx
  have hUn' : ((P : Subgroup (ReeTag.G2.reeGamma K a)).subgroupOf
      (MulAction.stabilizer (ReeTag.G2.reeGamma K a) (QuotientGroup.mk 1 :
        ReeTag.G2.reeGamma K a ⧸
          (ReeTag.G2.reeFixedBorel K a).subgroupOf (ReeTag.G2.reeGamma K a)))).Normal := by
    rw [hP, hstab]
    exact hUn
  have hw : n' • (QuotientGroup.mk 1 : ReeTag.G2.reeGamma K a ⧸
      (ReeTag.G2.reeFixedBorel K a).subgroupOf (ReeTag.G2.reeGamma K a)) ≠ QuotientGroup.mk 1 := by
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
    exact hηξ
  have htr : ∀ ω ω' : ReeTag.G2.reeGamma K a ⧸
      (ReeTag.G2.reeFixedBorel K a).subgroupOf (ReeTag.G2.reeGamma K a),
      ω ≠ QuotientGroup.mk 1 → ω' ≠ QuotientGroup.mk 1 →
        ∃ u : (P : Subgroup (ReeTag.G2.reeGamma K a)),
          (u : ReeTag.G2.reeGamma K a) • ω = ω' := by
    intro ω ω' hω hω'
    obtain ⟨u, hu, -⟩ := hreg ω ω' hω hω'
    exact ⟨⟨u, by rw [hP]; exact u.2⟩, hu⟩
  obtain ⟨hA, hinj, hprod, -⟩ :=
    Suzuki_opposite_Sylow_restriction hΩ (QuotientGroup.mk 1) P hUξ hUn' htr n' hw
  obtain ⟨g₀, β, hβ, rfl⟩ := hprod α
  set A := pairAutSubgroup (P : Subgroup (ReeTag.G2.reeGamma K a))
    ((P : Subgroup (ReeTag.G2.reeGamma K a)).map (MulAut.conj n').toMonoidHom) with hAdef
  have hmemA : ∀ γ : MulAut (ReeTag.G2.reeGamma K a), γ ∈ A ↔
      (U'.map γ.toMonoidHom = U' ∧
        (U'.map (MulAut.conj n').toMonoidHom).map γ.toMonoidHom =
          U'.map (MulAut.conj n').toMonoidHom) := by
    intro γ
    change γ ∈ (A : Set (MulAut (ReeTag.G2.reeGamma K a))) ↔ _
    rw [hAdef, hA, hP]
    rfl
  obtain ⟨hβU, hβV⟩ := (hmemA β).1 hβ
  obtain ⟨c, hc0, σ, hσ⟩ := pair_semilinear hK hw₀ β hβU hβV
  obtain ⟨k, hk⟩ := exists_frobRing_pow hK σ
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hbij, -⟩ := small_Ree_field_power_identities a K hK
  obtain ⟨s₀, hs₀0⟩ := hbij.2 (Units.mk0 c hc0)
  have hs₀ : ((s₀ ^ (2 * 3 ^ a - 1) : Kˣ) : K) = c := by
    have : s₀ ^ (2 * 3 ^ a - 1) = Units.mk0 c hc0 := hs₀0
    rw [this, Units.val_mk0]
  set γ := MulAut.conj (hIn hK s₀) * frobeniusΓ ^ k with hγ
  have hconjA : MulAut.conj (hIn hK s₀) ∈ A := (hmemA _).2 (conj_hIn_map hK hw₀ s₀)
  have hfrobA : (frobeniusΓ : MulAut (ReeTag.G2.reeGamma K a)) ∈ A :=
    (hmemA _).2 ⟨frobeniusΓ_map_U hK, frobeniusΓ_map_V hK hw₀⟩
  have hγA : γ ∈ A := mul_mem hconjA (pow_mem hfrobA k)
  set β'' := γ⁻¹ * β with hβ''
  have hβ''A : β'' ∈ A := mul_mem (inv_mem hγA) hβ
  obtain ⟨hβ''U, hβ''V⟩ := (hmemA β'').1 hβ''A
  have hT : ∀ t b e : K, ∃ b' e' : K, β'' (uIn hK t b e) = uIn hK t b' e' := by
    intro t b e
    obtain ⟨t', b', e', h⟩ := exists_uIn_eq hK (pair_mem_U β'' hβ''U (uIn_mem hK t b e))
    refine ⟨b', e', ?_⟩
    have hβeq : β = γ * β'' := by rw [hβ'']; group
    have h1 : β (uIn hK t b e) = γ (β'' (uIn hK t b e)) := by
      rw [hβeq, MulAut.mul_apply]
    rw [h, hγ, MulAut.mul_apply, frobeniusΓ_pow_uIn, MulAut.conj_apply, hIn_conj_uIn, hs₀] at h1
    obtain ⟨b₂, e₂, h2⟩ := hσ t b e
    rw [h2] at h1
    have h3 := (uIn_inj hK h1).1
    rw [← hk] at h3
    have h4 : σ t = σ t' := mul_left_cancel₀ hc0 h3
    rw [h, σ.injective h4]
  have hcore := core_fix_U hK β'' hT (pair_torus hK hw₀ β'' hβ''U hβ''V) ha
    (pair_surj_U hK β'' hβ''U)
  have hres : pairAutRestrict (P : Subgroup (ReeTag.G2.reeGamma K a))
      ((P : Subgroup (ReeTag.G2.reeGamma K a)).map (MulAut.conj n').toMonoidHom) ⟨β'', hβ''A⟩ =
      pairAutRestrict (P : Subgroup (ReeTag.G2.reeGamma K a))
        ((P : Subgroup (ReeTag.G2.reeGamma K a)).map (MulAut.conj n').toMonoidHom) 1 := by
    rw [map_one]
    apply MulEquiv.ext
    intro u
    apply Subtype.ext
    have hu : (u : ReeTag.G2.reeGamma K a) ∈ U' := by rw [← hP]; exact u.2
    obtain ⟨t, b, e, hu'⟩ := exists_uIn_eq hK (Subgroup.mem_subgroupOf.1 hu)
    change β'' (u : ReeTag.G2.reeGamma K a) = (u : ReeTag.G2.reeGamma K a)
    rw [hu', hcore]
  have h1 := congrArg Subtype.val (hinj hres)
  change β'' = 1 at h1
  have hβγ : β = γ := by
    rw [hβ''] at h1
    calc β = γ * (γ⁻¹ * β) := by group
      _ = γ := by rw [h1, mul_one]
  refine ⟨g₀ * hIn hK s₀, k, ?_⟩
  rw [hβγ, hγ, map_mul, mul_assoc]

end Steinberg

section Outer

variable (ha : 1 ≤ a) (hK : Nat.card K = 3 ^ (2 * a + 1))

include hK in
theorem dvd_of_frobeniusΓ_pow_eq_conj {k : ℕ} {g : ReeTag.G2.reeGamma K a}
    (h : (frobeniusΓ : MulAut (ReeTag.G2.reeGamma K a)) ^ k = MulAut.conj g) :
    2 * a + 1 ∣ k := by
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element ReeTag.G2.tag
  obtain ⟨hn, -, -, -, -, -, -, -, -, -, -, -, -, -, hNUV⟩ :=
    small_Ree_Borel_coset_Sylow_action a K hK w₀ hw₀
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hbij, -⟩ := small_Ree_field_power_identities a K hK
  set U' := (ReeTag.G2.reeFixedPosUnipotent K a).subgroupOf (ReeTag.G2.reeGamma K a) with hU'
  set V' := U'.map (MulAut.conj (longestIn a K hw₀)).toMonoidHom with hV'
  have hFr : (frobeniusΓ : MulAut (ReeTag.G2.reeGamma K a)) ∈ pairAutSubgroup U' V' :=
    ⟨frobeniusΓ_map_U hK, frobeniusΓ_map_V hK hw₀⟩
  have hFk := pow_mem hFr k
  have hFU : U'.map ((frobeniusΓ : MulAut (ReeTag.G2.reeGamma K a)) ^ k).toMonoidHom = U' :=
    hFk.1
  have hFV : V'.map ((frobeniusΓ : MulAut (ReeTag.G2.reeGamma K a)) ^ k).toMonoidHom = V' :=
    hFk.2
  have hnorm : ∀ X : Subgroup (ReeTag.G2.reeGamma K a),
      X.map (MulAut.conj g).toMonoidHom = X →
        g ∈ Subgroup.normalizer (X : Set (ReeTag.G2.reeGamma K a)) := by
    intro X hX
    rw [Subgroup.mem_normalizer_iff_conj_image_eq]
    have h1 := congrArg (fun H : Subgroup (ReeTag.G2.reeGamma K a) =>
      (H : Set (ReeTag.G2.reeGamma K a))) hX
    simp only [Subgroup.coe_map, MulEquiv.coe_toMonoidHom] at h1
    exact h1
  have hgU := hnorm U' (by rw [← h]; exact hFU)
  have hgV := hnorm V' (by rw [← h]; exact hFV)
  have hgH : g ∈ (ReeTag.G2.reeFixedTorus K a).subgroupOf (ReeTag.G2.reeGamma K a) := by
    have hNUV' : Subgroup.normalizer (U' : Set (ReeTag.G2.reeGamma K a)) ⊓
        Subgroup.normalizer (V' : Set (ReeTag.G2.reeGamma K a)) =
          (ReeTag.G2.reeFixedTorus K a).subgroupOf (ReeTag.G2.reeGamma K a) := hNUV
    rw [← hNUV']
    exact Subgroup.mem_inf.2 ⟨hgU, hgV⟩
  obtain ⟨s, hs⟩ := exists_smallReeH_eq (Subgroup.mem_subgroupOf.1 hgH)
  have hg : g = hIn hK s := Subtype.ext (by rw [hIn_val, hs])
  have h1 := congrArg (fun φ : MulAut (ReeTag.G2.reeGamma K a) => φ (uIn hK 1 0 0)) h
  rw [frobeniusΓ_pow_uIn, MulAut.conj_apply, hg, hIn_conj_uIn] at h1
  have h2 := (uIn_inj hK h1).1
  rw [one_pow, mul_one] at h2
  have hs1 : s = 1 := by
    apply hbij.1
    simp only [one_pow]
    exact Units.ext h2.symm
  have hg1 : g = 1 := by
    rw [hg, hs1]
    apply Subtype.ext
    rw [hIn_val, OneMemClass.coe_one]
    exact smallReeH_one
  apply dvd_of_forall_pow_three_pow_eq hK
  intro x
  have h3 := congrArg (fun φ : MulAut (ReeTag.G2.reeGamma K a) => φ (uIn hK x 0 0)) h
  rw [frobeniusΓ_pow_uIn, hg1, map_one, MulAut.one_apply] at h3
  exact (uIn_inj hK h3).1

include ha hK in
theorem outer_reeGamma_cyclic :
    IsCyclic (Outer (ReeTag.G2.reeGamma K a)) ∧
      Nat.card (Outer (ReeTag.G2.reeGamma K a)) = 2 * a + 1 := by
  set x : Outer (ReeTag.G2.reeGamma K a) :=
    QuotientGroup.mk (frobeniusΓ : MulAut (ReeTag.G2.reeGamma K a)) with hx
  have hgen : ∀ y : Outer (ReeTag.G2.reeGamma K a), y ∈ Subgroup.zpowers x := by
    intro y
    obtain ⟨α, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨g, k, rfl⟩ := exists_eq_conj_mul_frobeniusΓ_pow ha hK α
    refine ⟨k, ?_⟩
    have h1 : (QuotientGroup.mk (MulAut.conj g) : Outer (ReeTag.G2.reeGamma K a)) = 1 :=
      (QuotientGroup.eq_one_iff _).2 ⟨g, rfl⟩
    simp only [hx, zpow_natCast, QuotientGroup.mk_mul, QuotientGroup.mk_pow, h1, one_mul]
  have hord : orderOf x = 2 * a + 1 := by
    apply Nat.dvd_antisymm
    · apply orderOf_dvd_of_pow_eq_one
      rw [hx, ← QuotientGroup.mk_pow, frobeniusΓ_pow hK, QuotientGroup.mk_one]
    · have h1 : x ^ orderOf x = 1 := pow_orderOf_eq_one x
      rw [hx, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h1
      obtain ⟨g, hg⟩ := h1
      exact dvd_of_frobeniusΓ_pow_eq_conj hK hg.symm
  have htop : Subgroup.zpowers x = ⊤ := eq_top_iff.2 fun y _ => hgen y
  refine ⟨⟨⟨x, hgen⟩⟩, ?_⟩
  rw [← hord, ← Nat.card_zpowers, htop, Subgroup.card_top]

end Outer

end CFSG.ComponentClassification.LiteratureLocal.SmallRee
