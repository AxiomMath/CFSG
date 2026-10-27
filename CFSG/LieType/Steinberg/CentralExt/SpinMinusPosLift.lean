module

public import CFSG.LieType.Steinberg.CentralExt.PosLiftSplit
public import CFSG.LieType.Steinberg.CentralExt.SpinOddCentrallyClosed
public import CFSG.LieType.Steinberg.CentralExt.OrthogonalPerfect

public section

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.SpinFrame CFSG.LieType.RootSystem
open CFSG.LieType.Steinberg.SpinOdd (IsRootVec IsShort isShort_single elt elt_of_isLong
  elt_of_isShort)
open scoped commutatorElement

namespace CFSG.LieType.Steinberg.CentralExt.SpinMinusClosed

attribute [local instance] TorusLift.centerCommGroup

variable {n : ℕ} {K : Type} [Field K] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)

open _root_.Classical in
@[expose] noncomputable def x (γ : Fin (n - 1) → ℤ) (t : ShortField b c) :
    spinGroup (quadMinus n K b c) :=
  if IsLong (toStdB (n - 1) γ) then elt (minusFrame n b c) (toStdB (n - 1) γ) t.re
  else if h : ∃ q : Fin (n - 1) × Bool, toStdB (n - 1) γ = Pi.single q.1 (boolSign q.2) then
    twShortRoot n hirr h.choose.1 h.choose.2 (.ofAdd (fieldCoord t))
  else 1

theorem x_of_isLong {γ : Fin (n - 1) → ℤ} (h : IsLong (toStdB (n - 1) γ)) (t : ShortField b c) :
    x hirr γ t = elt (minusFrame n b c) (toStdB (n - 1) γ) t.re := by
  classical
  rw [x, ite_eq_left h]

theorem x_of_short {γ : Fin (n - 1) → ℤ} {i : Fin (n - 1)} {s : Bool}
    (h : toStdB (n - 1) γ = Pi.single i (boolSign s)) (t : ShortField b c) :
    x hirr γ t = twShortRoot n hirr i s (.ofAdd (fieldCoord t)) := by
  classical
  have hnl : ¬IsLong (toStdB (n - 1) γ) := by
    rw [h]
    exact (isShort_single i s).not_isLong
  have hex : ∃ q : Fin (n - 1) × Bool, toStdB (n - 1) γ = Pi.single q.1 (boolSign q.2) :=
    ⟨(i, s), h⟩
  rw [x, ite_eq_right hnl, dite_eq_left hex]
  obtain ⟨h1, h2⟩ := (single_eq_single_iff' (boolSign_ne_zero _)).mp (hex.choose_spec.symm.trans h)
  rw [h1, boolSign_injective h2]

theorem x_add (γ : Fin (n - 1) → ℤ) (s t : ShortField b c) :
    x hirr γ (s + t) = x hirr γ s * x hirr γ t := by
  classical
  unfold x
  split_ifs with h1 h2
  · rw [QuadraticAlgebra.re_add, SpinOdd.elt_add]
  · rw [fieldCoord_add, ofAdd_add, map_mul]
  · rw [mul_one]

theorem x_mem {γ : Fin (n - 1) → ℤ} (hγ : γ ∈ roots (isFiniteType_cartanB (n - 1)) ∅)
    (t : ShortField b c) : x hirr γ t ∈ minusRootGroup n hirr γ := by
  rcases exists_toStdB_eq_of_mem_roots n hγ with ⟨i, j, hij, s, u, h⟩ | ⟨i, s, h⟩
  · have hl : IsLong (toStdB (n - 1) γ) := h ▸ isLong_single_add_single hij s u
    rw [x_of_isLong hirr hl, elt_of_isLong _ hl, rootElt_eq _ hij h]
    exact longRoot_mem_minusRootGroup n hirr hij s u h _
  · rw [x_of_short hirr h]
    exact twShortRoot_mem_minusRootGroup n hirr i s h _

theorem exists_x_eq_of_mem {γ : Fin (n - 1) → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartanB (n - 1)) ∅) {g : spinGroup (quadMinus n K b c)}
    (hg : g ∈ minusRootGroup n hirr γ) : ∃ t, x hirr γ t = g := by
  rcases exists_toStdB_eq_of_mem_roots n hγ with ⟨i, j, hij, s, u, h⟩ | ⟨i, s, h⟩
  · have hl : IsLong (toStdB (n - 1) γ) := h ▸ isLong_single_add_single hij s u
    obtain ⟨a, rfl⟩ := (mem_minusRootGroup_long_iff n hirr hij s u h).mp hg
    refine ⟨algebraMap K (ShortField b c) ((repSign i j s u : K) * a), ?_⟩
    rw [x_of_isLong hirr hl, elt_of_isLong _ hl, QuadraticAlgebra.algebraMap_re,
      longRoot_eq_rootElt _ hij h]
  · obtain ⟨p, rfl⟩ := (mem_minusRootGroup_short_iff n hirr i s h).mp hg
    obtain ⟨t, ht⟩ := exists_fieldCoord_eq (b := b) (c := c) p
    exact ⟨t, by rw [x_of_short hirr h, ht]⟩

theorem x_mul_eq_one {γ : Fin (n - 1) → ℤ} (hγ : γ ∈ roots (isFiniteType_cartanB (n - 1)) ∅)
    {t : ShortField b c} (h : x hirr γ t = 1) (r : K) :
    x hirr γ (algebraMap K (ShortField b c) r * t) = 1 := by
  rcases exists_toStdB_eq_of_mem_roots n hγ with ⟨i, j, hij, s, u, h'⟩ | ⟨i, s, h'⟩
  · have hl : IsLong (toStdB (n - 1) γ) := h' ▸ isLong_single_add_single hij s u
    rw [x_of_isLong hirr hl, elt_of_isLong _ hl] at h ⊢
    have h0 : t.re = 0 := rootElt_injective _ hl (h.trans (rootElt_zero _ _).symm)
    rw [QuadraticAlgebra.re_mul, QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im,
      h0]
    simp only [mul_zero, zero_mul, add_zero]
    exact rootElt_zero _ _
  · rw [x_of_short hirr h'] at h ⊢
    have h0 : fieldCoord t = 0 := by
      have := congrArg Multiplicative.toAdd (twShortRoot_injective n hirr i s
        (h.trans (twShortRoot_ofAdd_zero n hirr i s).symm))
      simpa using this
    rw [fieldCoord_algebraMap_mul, h0, smul_zero]
    exact twShortRoot_ofAdd_zero n hirr i s

open SpinOddClosed (TorIdx chi)

@[expose] noncomputable def tor : TorIdx (n - 1) K → spinGroup (quadMinus n K b c)
  | .long _ _ h s t τ => (minusFrame n b c).longTorus h s t τ
  | .short i s τ => (minusFrame n b c).shortTorus i true (if s then τ else τ⁻¹)

theorem tor_conj_elt (p : TorIdx (n - 1) K) {γ : Fin (n - 1) → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartanB (n - 1)) ∅) (a : K) :
    tor p * elt (minusFrame n b c) (toStdB (n - 1) γ) a * (tor p)⁻¹ =
      elt (minusFrame n b c) (toStdB (n - 1) γ) (chi p γ * a) := by
  cases p with
  | long i j h s t τ =>
    exact SpinOddClosed.longTorus_conj_elt _ h s t τ (SpinOddClosed.isRootVec_of_mem hγ) a
  | short i s τ =>
    rw [tor, SpinOddClosed.shortTorus_conj_elt _ i true _ (SpinOddClosed.isRootVec_of_mem hγ) a]
    congr 2
    cases s
    · show ((((τ⁻¹ : Kˣ)) ^ (2 * (toStdB (n - 1) γ ⬝ᵥ Pi.single i (boolSign true))) : Kˣ) : K) =
        ((τ ^ (2 * (toStdB (n - 1) γ ⬝ᵥ Pi.single i (boolSign false))) : Kˣ) : K)
      rw [inv_zpow', dotProduct_single, dotProduct_single, boolSign_true, boolSign_false]
      congr 2
      ring
    · rfl

theorem planeRefl_smul_left {r : K} (hr : r ≠ 0) (a q : Fin 2 → K) :
    planeRefl b c (r • a) q = planeRefl b c a q := by
  by_cases ha : planeNorm b c a = 0
  · simp only [planeRefl, planeNorm_smul, ha, mul_zero, div_zero, zero_smul]
  · simp only [planeRefl, planeNorm_smul, polarPlane_smul_right, smul_smul]
    congr 2
    field_simp

theorem spinAction_shortTorusElt_planeVec_smul (i : Fin (n - 1)) {r : K} (hr : r ≠ 0)
    (w : Fin 2 → K) :
    spinAction (quadMinus n K b c) (shortTorusElt n hirr i (r • planeOne)) (planeVec n w) =
      planeVec n w := by
  rw [spinAction_shortTorusElt_planeVec n hirr i (smul_ne_zero hr planeOne_ne_zero),
    planeRefl_smul_left hr, planeRefl_planeRefl planeNorm_planeOne_ne_zero]

theorem tor_conj_short (p : TorIdx (n - 1) K) {γ : Fin (n - 1) → ℤ} {k : Fin (n - 1)}
    {u : Bool} (h : toStdB (n - 1) γ = Pi.single k (boolSign u)) (w : Fin 2 → K) :
    tor p * twShortRoot n hirr k u (.ofAdd w) * (tor p)⁻¹ =
      twShortRoot n hirr k u (.ofAdd (chi p γ • w)) := by
  cases p with
  | long i j hij s t τ =>
    rw [tor, longTorus_conj_twShortRoot n hirr hij s t τ k u w]
    congr 4
    rw [h, single_dotProduct, longCoroot_eq]
  | short i s τ =>
    set τ' : Kˣ := if s then τ else τ⁻¹ with hτ'
    have hτ0 : (τ' : K) ≠ 0 := τ'.ne_zero
    rw [tor, minusFrame_shortTorus_eq n hirr, conj_twShortRoot n hirr _ k u
      (spinAction_shortTorusElt_minusVec n hirr i (smul_ne_zero hτ0 planeOne_ne_zero) k u)
      (spinAction_shortTorusElt_planeVec_smul hirr i hτ0 w)]
    congr 3
    show _ = ((τ ^ (2 * (toStdB (n - 1) γ ⬝ᵥ Pi.single i (boolSign s))) : Kˣ) : K)
    rw [h, single_dotProduct, shortTorusScalar, planeNorm_smul, planeNorm_planeOne, mul_one]
    by_cases hki : k = i
    · subst hki
      rw [ite_eq_left rfl, Pi.single_eq_same]
      cases u <;> cases s <;> simp [hτ', boolSign, zpow_neg]
    · rw [ite_eq_right hki, Pi.single_eq_of_ne hki, mul_zero, mul_zero, zpow_zero,
        Units.val_one]

theorem tor_conj_x (p : TorIdx (n - 1) K) {γ : Fin (n - 1) → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartanB (n - 1)) ∅) (t : ShortField b c) :
    tor p * x hirr γ t * (tor p)⁻¹ = x hirr γ (algebraMap K (ShortField b c) (chi p γ) * t) := by
  rcases exists_toStdB_eq_of_mem_roots n hγ with ⟨i, j, hij, s, u, h⟩ | ⟨i, s, h⟩
  · have hl : IsLong (toStdB (n - 1) γ) := h ▸ isLong_single_add_single hij s u
    rw [x_of_isLong hirr hl, x_of_isLong hirr hl, tor_conj_elt p hγ, QuadraticAlgebra.re_mul,
      QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im]
    simp only [mul_zero, zero_mul, add_zero]
  · rw [x_of_short hirr h, x_of_short hirr h, tor_conj_short hirr p h, fieldCoord_algebraMap_mul]

theorem tor_comm (p p' : TorIdx (n - 1) K) :
    tor p' * tor p * (tor p')⁻¹ = (tor p : spinGroup (quadMinus n K b c)) := by
  have h : Commute (tor (b := b) (c := c) p') (tor p) := by
    cases p' with
    | long i j h s t τ =>
      cases p with
      | long k l h' u v σ =>
        exact (minusFrame n b c).commute_longTorus_longTorus h s t τ h' u v σ
      | short k u σ => exact (minusFrame n b c).commute_longTorus_shortTorus h s t τ k true _
    | short i s τ =>
      cases p with
      | long k l h' u v σ =>
        exact ((minusFrame n b c).commute_longTorus_shortTorus h' u v σ i true _).symm
      | short k u σ => exact (minusFrame n b c).commute_shortTorus_shortTorus i true _ k true _
  rw [h.eq, mul_inv_cancel_right]

theorem bruhatExtras [Finite K] (hn : 4 ≤ n) :
    BruhatExtras (minusDatum n hirr) (minusTorus n hirr) := by
  have hct := minusDatum_isCTGroupDatum n hirr hn
  have hext := minusDatum_steinbergExtras n hirr
  obtain ⟨p, _, _⟩ := TorusLift.exists_prime_charP (k := K)
  refine ⟨eq_bot_iff.2 fun x hx => ?_⟩
  obtain ⟨hxB, hxN⟩ := Subgroup.mem_inf.1 hx
  rw [Subgroup.mem_bot]
  set lev : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → ℤ := fun a => ((1 : ℤ) • epsHt n) (minusWt n a)
    with hlev
  have hneg : Graded.IdBelow (fun a => ((-1 : ℤ) • epsHt n) (minusWt n a)) 1 (mat n x) :=
    idBelow_of_mem_iSup n hirr (-1) _ (fun γ hγ => ⟨hγ.1, by
      have : ht (ι := Fin (n - 1)) γ < 0 := hγ.2
      omega⟩) hxN
  have hnegl : ∀ v, ((-1 : ℤ) • epsHt n) v = -((1 : ℤ) • epsHt n) v := fun v => by
    simp only [AddMonoidHom.smul_apply, smul_eq_mul]
    ring
  obtain ⟨t, htT, u, hu, htu⟩ := (Set.ext_iff.1 (coe_borel hct) _).1 hxB
  have htu' : t * u = x := htu
  subst htu'
  have hD : BlockDiag n (mat n t) := by
    refine Subgroup.iSup_induction _ htT (C := fun g => BlockDiag n (mat n g))
      (fun k y hy => blockDiag_mat_of_mem_minusTorus n hirr k hy) ?_ fun y z hy hz => ?_
    · rw [mat_one]
      exact blockDiag_one n
    · rw [mat_mul]
      exact blockDiag_mul n hy hz
  have hpos : Graded.IdBelow lev 1 (mat n u) :=
    idBelow_of_mem_iSup n hirr 1 _ (fun γ hγ => ⟨hγ.1, by
      have : 0 < ht (ι := Fin (n - 1)) γ := hγ.2
      omega⟩) hu
  have hlevD : ∀ a e, mat n t a e ≠ 0 → lev a = lev e := fun a e h => by
    by_cases hae : a = e
    · rw [hae]
    · obtain ⟨⟨r, rfl⟩, ⟨r', rfl⟩⟩ := hD a e hae h
      simp only [hlev, minusWt_inr_inr]
  have hmul : ∀ a e, lev a - lev e ≤ 0 → mat n (t * u) a e = mat n t a e := fun a e hae => by
    rw [mat_mul, Matrix.mul_apply, Finset.sum_eq_single e]
    · rw [hpos e e (by simp), Matrix.one_apply_eq, mul_one]
    · intro c _ hce
      by_cases h0 : mat n t a c = 0
      · rw [h0, zero_mul]
      · rw [hpos c e (by have := hlevD a c h0; omega), Matrix.one_apply_ne hce, mul_zero]
    · simp
  have ht1 : mat n t = 1 := by
    ext a e
    by_cases hae : lev a = lev e
    · rw [← hmul a e (by omega)]
      refine hneg a e ?_
      show ((-1 : ℤ) • epsHt n) (minusWt n a) - ((-1 : ℤ) • epsHt n) (minusWt n e) < 1
      rw [hnegl, hnegl]
      have h' : ((1 : ℤ) • epsHt n) (minusWt n a) = ((1 : ℤ) • epsHt n) (minusWt n e) := hae
      omega
    · have hne : a ≠ e := fun h => hae (by rw [h])
      rw [Matrix.one_apply_ne hne]
      by_contra h0
      exact hae (hlevD a e h0)
  have hxu : mat n (t * u) = mat n u := by rw [mat_mul, ht1, Matrix.one_mul]
  have hu1 : mat n u = 1 := by
    refine eq_one_of_idBelow_of_idBelow n lev hpos fun a e hae => ?_
    rw [← hxu]
    refine hneg a e ?_
    show ((-1 : ℤ) • epsHt n) (minusWt n a) - ((-1 : ℤ) • epsHt n) (minusWt n e) < 1
    rw [hnegl, hnegl]
    exact hae
  have hu' : u = 1 := eq_one_of_mat_eq_one n hirr hu1 (posPart_le_fixPosTestElt n hirr hu)
  rw [hu', mul_one] at hxu ⊢
  rw [hu', mul_one] at hxN
  have hker : t ∈ (spinMatrix (quadMinus n K b c)).ker := by
    rw [MonoidHom.mem_ker]
    exact Units.ext ht1
  rcases (mem_ker_spinMatrix_quadMinus_iff hirr t).mp hker with h | h
  · exact h
  · have hsq : t ^ 2 = 1 := Subtype.ext (by
      rw [SubmonoidClass.coe_pow, h, OneMemClass.coe_one]
      simp)
    have hU : IsPGroup p ↥(negUnipotent (minusDatum n hirr)) := by
      refine (isPGroup_iSup_posSet hext (fun γ hγ => isPGroup_minusRootGroup hirr hγ)
        (-htHom)).to_le (iSup₂_le fun γ hγ => le_iSup₂_of_le γ ⟨hγ.1, ?_⟩ le_rfl)
      exact neg_pos.2 hγ.2
    obtain ⟨k, hk⟩ := hU ⟨t, hxN⟩
    have htp : t ^ p ^ k = 1 := congrArg Subtype.val hk
    by_cases hp2 : p = 2
    · subst hp2
      have h20 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
      apply Subtype.ext
      rw [h, Submonoid.coe_one, neg_one_eq_one_of_two_eq_zero _ h20]
    · have hcop : Nat.Coprime (p ^ k) 2 :=
        Nat.Coprime.pow_left k ((Nat.coprime_primes (Fact.out) Nat.prime_two).2 hp2)
      have h1 : orderOf t ∣ Nat.gcd (p ^ k) 2 :=
        Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one htp) (orderOf_dvd_of_pow_eq_one hsq)
      rw [hcop] at h1
      exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h1)

theorem pow_eq_one_of_mem_iSup {G : Type*} [Group G] {ι : Type*} {H : ι → Subgroup G} {N : ℕ}
    (hN : ∀ i, ∀ h ∈ H i, h ^ N = 1) (hc : ∀ i j, ∀ h ∈ H i, ∀ h' ∈ H j, Commute h h')
    {g : G} (hg : g ∈ ⨆ i, H i) : g ^ N = 1 := by
  have hc1 : ∀ g ∈ ⨆ i, H i, ∀ j, ∀ h ∈ H j, Commute g h := by
    intro g hg j h hh
    exact Subgroup.iSup_induction H (C := fun g => Commute g h) hg
      (fun i g hg' => hc i j g hg' h hh) (Commute.one_left h) fun x y hx hy => hx.mul_left hy
  have hc2 : ∀ g ∈ ⨆ i, H i, ∀ g' ∈ ⨆ i, H i, Commute g g' := by
    intro g hg g' hg'
    exact Subgroup.iSup_induction H (C := fun g' => Commute g g') hg'
      (fun j h hh => hc1 g hg j h hh) (Commute.one_right g) fun x y hx hy => hx.mul_right hy
  have key := Subgroup.iSup_induction H (C := fun g => g ∈ ⨆ i, H i ∧ g ^ N = 1) hg
    (fun i h hh => ⟨Subgroup.mem_iSup_of_mem i hh, hN i h hh⟩) ⟨Subgroup.one_mem _, one_pow N⟩
    fun x y ⟨hx, hx'⟩ ⟨hy, hy'⟩ =>
      ⟨Subgroup.mul_mem _ hx hy, by rw [(hc2 x hx y hy).mul_pow, hx', hy', one_mul]⟩
  exact key.2

theorem card_shortField : Nat.card (ShortField b c) = Nat.card K ^ 2 := by
  rw [Nat.card_congr (QuadraticAlgebra.equivProd (-c) b), Nat.card_prod, pow_two]

theorem pow_eq_one_of_mem_minusTorus [Finite K] (k : Fin (n - 1))
    {g : spinGroup (quadMinus n K b c)} (hg : g ∈ minusTorus n hirr k) :
    g ^ (Nat.card (ShortField b c) - 1) = 1 := by
  have := fact_shortField hirr
  have := finite_shortField (b := b) (c := c)
  have : Fintype K := Fintype.ofFinite K
  have : Fintype (ShortField b c) := Fintype.ofFinite _
  have hK1 : 1 ≤ Nat.card K := Nat.one_le_iff_ne_zero.2 Nat.card_pos.ne'
  by_cases hk : k.val + 1 < n - 1
  · rw [minusTorus_of_lt n hirr hk] at hg
    obtain ⟨τ, rfl⟩ := hg
    rw [← map_pow]
    have hτ : τ ^ (Nat.card K - 1) = 1 := Units.ext (by
      rw [Units.val_pow_eq_pow_val, Units.val_one, Nat.card_eq_fintype_card]
      exact FiniteField.pow_card_sub_one_eq_one (τ : K) τ.ne_zero)
    have hdvd : Nat.card K - 1 ∣ Nat.card (ShortField b c) - 1 := by
      rw [card_shortField]
      exact ⟨Nat.card K + 1, by
        rw [pow_two]
        zify [Nat.one_le_iff_ne_zero.2 (Nat.mul_pos Nat.card_pos Nat.card_pos).ne', hK1]
        ring⟩
    obtain ⟨m, hm⟩ := hdvd
    rw [hm, pow_mul, hτ, one_pow, map_one]
  · rw [minusTorus_of_not_lt n hirr hk] at hg
    obtain ⟨a, ha, rfl⟩ := (mem_shortTorus_iff n hirr k).1 hg
    obtain ⟨t, ht, he⟩ := exists_shortRels_h_eq n hirr k ha
    set R := shortRels n hirr k
    rw [← he]
    have hpow : ∀ m : ℕ, R.h t ^ m = R.h (t ^ m) := by
      intro m
      induction m with
      | zero => rw [pow_zero, pow_zero, R.h_one]
      | succ m ih => rw [pow_succ, ih, pow_succ, R.h_mul (pow_ne_zero m ht) ht]
    rw [hpow, Nat.card_eq_fintype_card, FiniteField.pow_card_sub_one_eq_one t ht, R.h_one]

theorem coprime_card_torus [Finite K] {p : ℕ} [hp : Fact p.Prime] [CharP K p] :
    p.Coprime (Nat.card (⨆ k, minusTorus n hirr k : Subgroup (spinGroup (quadMinus n K b c)))) := by
  have : Fintype K := Fintype.ofFinite K
  have : Finite (spinGroup (quadMinus n K b c)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadMinus hirr)
  rw [Nat.Prime.coprime_iff_not_dvd hp.out]
  intro hdvd
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hpow : (g : spinGroup (quadMinus n K b c)) ^ (Nat.card (ShortField b c) - 1) = 1 :=
    pow_eq_one_of_mem_iSup (fun k h hh => pow_eq_one_of_mem_minusTorus hirr k hh)
      (fun i j h hh h' hh' => minusDatum_torus_commute n hirr i j h hh h' hh') g.2
  have hdvd' : p ∣ Nat.card (ShortField b c) - 1 := by
    rw [← hg]
    exact orderOf_dvd_of_pow_eq_one (Subtype.ext (by rw [Subgroup.coe_pow, hpow,
      Subgroup.coe_one]))
  obtain ⟨m, -, hm⟩ := FiniteField.card K p
  have hpK : p ∣ Nat.card K := by
    rw [Nat.card_eq_fintype_card, hm]
    exact dvd_pow_self p (PNat.ne_zero m)
  have hpF : p ∣ Nat.card (ShortField b c) := by
    rw [card_shortField]
    exact dvd_pow hpK two_ne_zero
  have hF1 : 1 ≤ Nat.card (ShortField b c) := by
    rw [card_shortField]
    exact Nat.one_le_pow _ _ Nat.card_pos
  have h1 := Nat.dvd_sub hpF hdvd'
  rw [show Nat.card (ShortField b c) - (Nat.card (ShortField b c) - 1) = 1 by omega] at h1
  exact hp.out.one_lt.ne' (Nat.dvd_one.1 h1)

section Lift

variable [Fact (∀ r : K, r ^ 2 ≠ -c + b * r)] {E : Type*} [Group E]
  {π : E →* spinGroup (quadMinus n K b c)}

variable (π) in
@[expose] def IsRootLift (γ : Fin (n - 1) → ℤ) (Y : ShortField b c → E) : Prop :=
  (∀ s t, Y (s + t) = Y s * Y t) ∧ (∀ s, π (Y s) = x hirr γ s) ∧
    (∀ s, x hirr γ s = 1 → Y s = 1) ∧
    ∀ (p : TorIdx (n - 1) K) (e : E), π e = tor p → ∀ s,
      e * Y s * e⁻¹ = Y (algebraMap K (ShortField b c) (chi p γ) * s)

variable (hcen : π.ker ≤ Subgroup.center E) (hπ : Function.Surjective π)

include hcen in
theorem commPairing_eq_zero_short [Finite K] (hF4 : Nat.card (ShortField b c) ≠ 4)
    (hF9 : Nat.card (ShortField b c) ≠ 9) {γ : Fin (n - 1) → ℤ} {k : Fin (n - 1)}
    (h : toStdB (n - 1) γ = Pi.single k (boolSign true)) :
    TorusLift.commPairing hcen hπ (x_add hirr γ) = 0 := by
  have := finite_shortField (b := b) (c := c)
  obtain ⟨p, _, _⟩ := TorusLift.exists_prime_charP (k := ShortField b c)
  set R := shortRels n hirr k
  have hx : ∀ t, x hirr γ t = R.x t := fun t => by
    rw [x_of_short hirr h, shortRels_x, twShortRoot_true]
  refine Pairing.pairing_eq_zero_of_sq p hF4 hF9
    (TorusLift.commPairing_self hcen hπ (x_add hirr γ)) fun u hu s t => ?_
  refine TorusLift.commPairing_smul hcen hπ (x_add hirr γ) (g := R.h u) (fun c' => ?_) s t
  rw [hx, hx, R.h_conj_x hu]

include hcen in
theorem commPairing_eq_zero_long (hn : 4 ≤ n) {γ : Fin (n - 1) → ℤ}
    (hl : IsLong (toStdB (n - 1) γ)) : TorusLift.commPairing hcen hπ (x_add hirr γ) = 0 := by
  obtain ⟨i, j, hij, s, t, he⟩ := hl
  obtain ⟨m, hmi, hmj⟩ := exists_ne_and_ne (show 3 ≤ n - 1 by omega) i j
  set F := (minusFrame n b c).toHypFrame
  have hl : IsLong (toStdB (n - 1) γ) := he ▸ isLong_single_add_single hij s t
  refine AddMonoidHom.ext fun c' => AddMonoidHom.ext fun d => ?_
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [TorusLift.commPairing_apply, AddMonoidHom.zero_apply, AddMonoidHom.zero_apply, toMul_zero,
    Subgroup.coe_one]
  set r : K := (repSign i j s t : K)
  set a := TorusLift.lift hπ (F.longRoot hmi.symm s true (.ofAdd (r * c'.re)))
  set b' := TorusLift.lift hπ (F.longRoot hmj (!true) t (.ofAdd 1))
  set y := TorusLift.lift hπ (x hirr γ d)
  have hx : ∀ c'' : ShortField b c, x hirr γ c'' = F.longRoot hij s t (.ofAdd (r * c''.re)) :=
    fun c'' => by rw [x_of_isLong hirr hl, elt_of_isLong _ hl, rootElt_eq _ hij he]
  have hab : π ⁅a, b'⁆ = x hirr γ c' := by
    rw [map_commutatorElement, TorusLift.map_lift, TorusLift.map_lift,
      F.commutator_longRoot_longRoot hmi.symm hmj hij s true t, mul_one, hx]
  rw [TorusLift.commutatorElement_eq_of_map_eq hcen ((TorusLift.map_lift hπ _).trans hab.symm)
    rfl, commutatorElement_eq_one_iff_mul_comm]
  refine (SpinTorus.commute_commutatorElement_of_central hcen ?_ ?_).symm
  · rw [TorusLift.map_lift, TorusLift.map_lift, hx]
    exact (F.commute_longRoot_longRoot_left hij hmi.symm s t true _ _).eq
  · rw [TorusLift.map_lift, TorusLift.map_lift, hx]
    exact (F.commute_longRoot_longRoot_right hij hmj s t (!true) _ _).eq

include hcen hπ in
theorem exists_isRootLift {γ : Fin (n - 1) → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartanB (n - 1)) ∅)
    (h0 : TorusLift.commPairing hcen hπ (x_add hirr γ) = 0) {p₀ : TorIdx (n - 1) K}
    (hp₀ : algebraMap K (ShortField b c) (chi p₀ γ) ≠ 1) : ∃ Y : ShortField b c → E,
      IsRootLift hirr π γ Y := by
  refine ⟨TorusLift.canonLift hπ (x := x hirr γ) (tor p₀)
      (algebraMap K (ShortField b c) (chi p₀ γ)),
    TorusLift.canonLift_add hcen hπ (x_add hirr γ) h0 (tor_conj_x hirr p₀ hγ) hp₀,
    TorusLift.map_canonLift hπ (x_add hirr γ) (tor_conj_x hirr p₀ hγ) hp₀,
    fun s hs => ?_,
    fun p e he s => TorusLift.conj_canonLift hcen hπ (tor_comm p₀ p) (tor_conj_x hirr p hγ) he s⟩
  have hb : (algebraMap K (ShortField b c) (chi p₀ γ) - 1)⁻¹ =
      algebraMap K (ShortField b c) ((chi p₀ γ - 1)⁻¹) := by
    rw [map_inv₀, map_sub, map_one]
  have h1 : x hirr γ ((algebraMap K (ShortField b c) (chi p₀ γ) - 1)⁻¹ * s) = 1 := by
    rw [hb]
    exact x_mul_eq_one hirr hγ hs _
  have hz : TorusLift.lift hπ (1 : spinGroup (quadMinus n K b c)) ∈ Subgroup.center E :=
    hcen (by rw [MonoidHom.mem_ker, TorusLift.map_lift])
  show ⁅TorusLift.lift hπ (tor p₀),
    TorusLift.lift hπ (x hirr γ ((algebraMap K (ShortField b c) (chi p₀ γ) - 1)⁻¹ * s))⁆ = 1
  rw [h1, commutatorElement_eq_one_iff_mul_comm]
  exact Subgroup.mem_center_iff.1 hz _

variable (π) in
open _root_.Classical in
@[expose] noncomputable def X (γ : Fin (n - 1) → ℤ) : ShortField b c → E :=
  if h : ∃ Y : ShortField b c → E, IsRootLift hirr π γ Y then h.choose else fun _ => 1

omit [Fact (∀ r : K, r ^ 2 ≠ -c + b * r)] in
theorem X_isRootLift {γ : Fin (n - 1) → ℤ} (h : ∃ Y : ShortField b c → E, IsRootLift hirr π γ Y) :
    IsRootLift hirr π γ (X hirr π γ) := by
  classical
  rw [X, dite_eq_left h]
  exact h.choose_spec

end Lift

include hirr in
theorem spinMinus_exists_section_of_pKernel [Finite K] (hn : 4 ≤ n) (hK : 4 ≤ Nat.card K)
    {p : ℕ} [Fact p.Prime] [CharP K p] {E : Type*} [Group E] [Finite E]
    {π : E →* spinGroup (quadMinus n K b c)} (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) (hpk : IsPGroup p π.ker) :
    ∃ s : spinGroup (quadMinus n K b c) →* E, ∀ g, π (s g) = g := by
  have := fact_shortField hirr
  have := finite_shortField (b := b) (c := c)
  have : Finite (spinGroup (quadMinus n K b c)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadMinus hirr)
  obtain ⟨w, hw⟩ := SpinTorus.exists_unit_sq_ne_one (F := K) hK
  have h16 : 16 ≤ Nat.card (ShortField b c) := by
    rw [card_shortField]
    nlinarith
  have hspec : ∀ γ ∈ PosLift.posRoots (minusDatum n hirr), IsRootLift hirr π γ (X hirr π γ) := by
    intro γ hγ
    have hγr : γ ∈ roots (isFiniteType_cartanB (n - 1)) ∅ := hγ.1
    have h0 : TorusLift.commPairing hcen hπ (x_add hirr γ) = 0 := by
      rcases SpinOddClosed.isRootVec_of_mem hγr with hl | ⟨k, u, he⟩
      · exact commPairing_eq_zero_long hirr hcen hπ hn hl
      · have hu : u = true := by
          by_contra hu
          have hu' : u = false := by simpa using hu
          have hpos : 0 < ht (ι := Fin (n - 1)) γ := hγ.2
          rw [ht_of_toStdB_eq_single (n - 1) he, hu', boolSign_false] at hpos
          have := k.isLt
          omega
        subst hu
        exact commPairing_eq_zero_short hirr hcen hπ (by omega) (by omega) he
    obtain ⟨p₀, hp₀⟩ := SpinOddClosed.exists_chi_sq hγr w
    have hne : algebraMap K (ShortField b c) (chi p₀ γ) ≠ 1 := by
      rw [hp₀, ← map_one (algebraMap K (ShortField b c))]
      intro h
      exact hw (Units.ext ((algebraMap K (ShortField b c)).injective h))
    exact X_isRootLift hirr (exists_isRootLift hirr hcen hπ hγr h0 hne)
  refine PosLift.exists_section_of_posLift (minusDatum_isCTGroupDatum n hirr hn)
    (minusDatum_steinbergExtras n hirr) (bruhatExtras hirr hn) rfl (p := p)
    (fun γ hγ => isPGroup_minusRootGroup hirr hγ) (coprime_card_torus hirr) hπ hcen hpk
    (x := x hirr) (fun γ hγ g => ⟨fun hg => exists_x_eq_of_mem hirr hγ.1 hg,
      fun ⟨t, ht⟩ => ht ▸ x_mem hirr hγ.1 t⟩)
    (fun γ _ => x_add hirr γ) (X := X hirr π) (fun γ hγ => (hspec γ hγ).1)
    (fun γ hγ => (hspec γ hγ).2.1) (fun γ hγ => (hspec γ hγ).2.2.1)
    (tor := fun p => TorusLift.lift hπ (tor p))
    (χ := fun p γ => algebraMap K (ShortField b c) (chi p γ))
    (fun p γ hγ c' => (hspec γ hγ).2.2.2 p _ (TorusLift.map_lift hπ _) c') ?_
  intro a ha b' hb hab
  have hD : (minusDatum n hirr).divisible = ∅ := rfl
  have hli : LinIndepPair a b' := by
    by_contra h
    rcases eq_or_eq_neg_of_not_linIndepPair (minusDatum n hirr).isFiniteType hD ha.1 hb.1 h with
      h | h
    · exact hab h.symm
    · have h2 := hb.2
      rw [h] at h2
      have : ht (-a) = -ht a := by simp [ht, Finset.sum_neg_distrib]
      rw [this] at h2
      linarith [ha.2]
  obtain ⟨hne, hne'⟩ := SpinOddClosed.toStdB_ne_of_linIndepPair hli
  obtain ⟨v, hv, h0, h1⟩ := SpinOddClosed.exists_dot_sep_rootVec
    (SpinOddClosed.isRootVec_of_mem ha.1) (SpinOddClosed.isRootVec_of_mem hb.1) hne hne'
  obtain ⟨j, hj1, hj2⟩ := SpinOddClosed.chi_eq_one (n := n - 1) (K := K) hv h0 w
  refine ⟨j, by rw [hj1, map_one], fun h => hj2 b' hb.1 h1 hw ?_⟩
  rw [← map_one (algebraMap K (ShortField b c))] at h
  exact (algebraMap K (ShortField b c)).injective h

end CFSG.LieType.Steinberg.CentralExt.SpinMinusClosed
