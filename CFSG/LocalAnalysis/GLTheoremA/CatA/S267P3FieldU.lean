module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267P3FieldSL
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267P3UniModel
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAntiunitaryTransport
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Layer
import CFSG.LocalAnalysis.GLTheoremA.CatA.H81A3LinCent
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.P3.Field

open Matrix CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.S267.P3 CFSG.LocalAnalysis.GLTheoremA.S267.P3.Lin
open CFSG.LocalAnalysis.GLTheoremA.S267.P3.Form
open CFSG.LocalAnalysis.GLTheoremA.S267.P3.Uni (suOn mem_suOn blk_mem_suOn_iff cU wU cU_det wU_det
  cU_mem cU_rel wU_mem negOne_mem_suOn cU_mul_wU_ne)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply
  unitaryInvolution_involutive)

section FixedField

variable {K : Type} [Field K] [Finite K]

theorem card_fixField_of_orderOf_three {p n : ℕ} (hp : p.Prime) (hn : 1 ≤ n)
    (hK : Nat.card K = p ^ n) {τ : K ≃+* K} (hτ : orderOf τ = 3) :
    3 ∣ n ∧ Nat.card (fixField τ) = p ^ (n / 3) := by
  classical
  obtain ⟨-, -, -, -, -, hA⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality hp hn hK
  obtain ⟨hdvd, S, hS, hcard⟩ := hA (Subgroup.zpowers τ)
  rw [Nat.card_zpowers, hτ] at hdvd hcard
  refine ⟨hdvd, ?_⟩
  have hSE : S = fixField τ := by
    refine SetLike.ext' ?_
    rw [hS]
    ext a
    simp only [Set.mem_setOf_eq, SetLike.mem_coe]
    change (∀ σ ∈ Subgroup.zpowers τ, σ a = a) ↔ τ a = a
    constructor
    · intro h
      exact h τ (Subgroup.mem_zpowers τ)
    · intro h σ hσ
      have hstab : Subgroup.zpowers τ ≤ MulAction.stabilizer (K ≃+* K) a :=
        Subgroup.zpowers_le.2 (by rw [MulAction.mem_stabilizer_iff, RingAut.smul_def]; exact h)
      have h' := hstab hσ
      rwa [MulAction.mem_stabilizer_iff, RingAut.smul_def] at h'
  rw [← hSE, hcard]

end FixedField

section UParam

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem fixField_unitary (hK : Nat.card K = (p ^ f) ^ 2) {τ : K ≃+* K} (hτ : orderOf τ = 3) :
    3 ∣ f ∧ Nat.card (fixField τ) = (p ^ (f / 3)) ^ 2 ∧
      ∀ x : K, τ x = x → unitaryInvolution K p f x = x ^ (p ^ (f / 3)) := by
  have hp := (Fact.out : p.Prime)
  have hf : 1 ≤ f := by
    by_contra h0
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    rw [hK, show f = 0 by omega, pow_zero, one_pow] at h1
    omega
  have hK' : Nat.card K = p ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨h3, hcard⟩ := card_fixField_of_orderOf_three hp (by omega) hK' hτ
  have h3f : 3 ∣ f := (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) h3)
  obtain ⟨f₀, rfl⟩ := h3f
  have hf₀ : 3 * f₀ / 3 = f₀ := by omega
  have h2f : 2 * (3 * f₀) / 3 = 2 * f₀ := by omega
  rw [h2f] at hcard
  refine ⟨⟨f₀, rfl⟩, ?_, fun x hx => ?_⟩
  · rw [hcard, hf₀, ← pow_mul, mul_comm]
  · rw [hf₀, unitaryInvolution_apply]
    have : Fintype (fixField τ) := Fintype.ofFinite _
    have hpow : (⟨x, hx⟩ : fixField τ) ^ (p ^ (2 * f₀)) = ⟨x, hx⟩ := by
      rw [← hcard, Nat.card_eq_fintype_card, FiniteField.pow_card]
    have hpow' : x ^ (p ^ (2 * f₀)) = x := congrArg Subtype.val hpow
    rw [show p ^ (3 * f₀) = p ^ (2 * f₀) * p ^ f₀ by rw [← pow_add]; ring_nf, pow_mul, hpow']

theorem exists_fix_norm_eq (hK : Nat.card K = (p ^ f) ^ 2) {τ : K ≃+* K} (hτ : orderOf τ = 3)
    {c : K} (hc : τ c = c) (hcb : unitaryInvolution K p f c = c) (hc0 : c ≠ 0) :
    ∃ b : K, τ b = b ∧ unitaryInvolution K p f b * b = c := by
  obtain ⟨-, hcard, hbar⟩ := fixField_unitary hK hτ
  haveI : CharP (fixField τ) p := Subfield.charP (fixField τ) p
  have hc' : unitaryInvolution (fixField τ) p (f / 3) ⟨c, hc⟩ = ⟨c, hc⟩ := by
    apply Subtype.ext
    rw [unitaryInvolution_apply, SubmonoidClass.coe_pow]
    change c ^ p ^ (f / 3) = c
    rw [← hbar c hc, hcb]
  obtain ⟨b₀, hb₀⟩ := CFSG.LocalAnalysis.GLTheoremA.S267.P3.Uni.exists_norm_eq_of_fixed
    (K := fixField τ) hcard hc' fun h => hc0 (congrArg Subtype.val h)
  refine ⟨b₀, b₀.2, ?_⟩
  have h1 : unitaryInvolution K p f b₀ =
      ((unitaryInvolution (fixField τ) p (f / 3) b₀ : fixField τ) : K) := by
    rw [hbar _ b₀.2, unitaryInvolution_apply, SubmonoidClass.coe_pow]
  rw [h1]
  exact congrArg Subtype.val hb₀

theorem exists_fix_norm_one (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    {τ : K ≃+* K} (hτ : orderOf τ = 3) :
    ∃ l : K, τ l = l ∧ unitaryInvolution K p f l * l = 1 ∧ l ^ 2 ≠ 1 := by
  obtain ⟨h3f, hcard, hbar⟩ := fixField_unitary hK hτ
  haveI : CharP (fixField τ) p := Subfield.charP (fixField τ) p
  have hp := (Fact.out : p.Prime)
  have hf : 1 ≤ f := by
    by_contra h0
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    rw [hK, show f = 0 by omega, pow_zero, one_pow] at h1
    omega
  have hq : 3 ≤ p ^ (f / 3) := by
    have h5 : 5 ≤ p := hp.five_le_of_ne_two_of_ne_three hp2 hp3
    have hf3 : 1 ≤ f / 3 := by
      obtain ⟨k, rfl⟩ := h3f
      omega
    calc 3 ≤ p := by omega
      _ ≤ p ^ (f / 3) := Nat.le_self_pow (by omega) p
  obtain ⟨l₀, hl₀, hl₀2⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.S267.P3.Uni.exists_norm_one_sq_ne_one (K := fixField τ) hcard hq
  refine ⟨l₀, l₀.2, ?_, fun h => hl₀2 (Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact h))⟩
  have h1 : unitaryInvolution K p f l₀ =
      ((unitaryInvolution (fixField τ) p (f / 3) l₀ : fixField τ) : K) := by
    rw [hbar _ l₀.2, unitaryInvolution_apply, SubmonoidClass.coe_pow]
  rw [h1]
  exact congrArg Subtype.val hl₀

theorem exists_norm_one_not_fix (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    {τ : K ≃+* K} (hτ : orderOf τ = 3) :
    ∃ l : K, τ l ≠ l ∧ unitaryInvolution K p f l * l = 1 := by
  classical
  obtain ⟨⟨f₀, hf₀⟩, hcard, -⟩ := fixField_unitary hK hτ
  have hp := (Fact.out : p.Prime)
  have hf0 : 1 ≤ f₀ := by
    by_contra h0
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    rw [hK, hf₀, show f₀ = 0 by omega, mul_zero, pow_zero, one_pow] at h1
    omega
  rw [hf₀, show 3 * f₀ / 3 = f₀ by omega] at hcard
  set q₀ := p ^ f₀ with hq₀
  have hq : p ^ f = q₀ ^ 3 := by rw [hf₀, hq₀, ← pow_mul, mul_comm]
  have hq₀2 : 2 ≤ q₀ := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hcardU : Nat.card Kˣ = (p ^ f) ^ 2 - 1 := by
    have := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hK]
  have hord : orderOf g = (p ^ f) ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hcardU]
  have hQ1 : 1 ≤ p ^ f := Nat.one_le_pow _ _ hp.pos
  have hQ2 : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
  have hmul : (p ^ f - 1) * (p ^ f + 1) = (p ^ f) ^ 2 - 1 := by
    zify [hQ1, Nat.one_le_pow 2 _ (by omega : 0 < p ^ f)]
    ring
  refine ⟨((g ^ (p ^ f - 1) : Kˣ) : K), fun hfix => ?_, ?_⟩
  ·
    have hl0 : ((g ^ (p ^ f - 1) : Kˣ) : K) ≠ 0 := Units.ne_zero _
    have : Fintype (fixField τ) := Fintype.ofFinite _
    have hpow : (⟨_, hfix⟩ : fixField τ) ^ (q₀ ^ 2 - 1) = 1 := by
      rw [← hcard, Nat.card_eq_fintype_card]
      exact FiniteField.pow_card_sub_one_eq_one _ fun h => hl0 (congrArg Subtype.val h)
    have hpow' : g ^ ((p ^ f - 1) * (q₀ ^ 2 - 1)) = 1 := by
      apply Units.ext
      rw [pow_mul, Units.val_pow_eq_pow_val, Units.val_one]
      exact congrArg Subtype.val hpow
    have hdvd := orderOf_dvd_of_pow_eq_one hpow'
    rw [hord, ← hmul] at hdvd
    have h1 : p ^ f + 1 ∣ q₀ ^ 2 - 1 :=
      Nat.dvd_of_mul_dvd_mul_left (by omega : 0 < p ^ f - 1) hdvd
    have h2 : 0 < q₀ ^ 2 - 1 := by
      have : 4 ≤ q₀ ^ 2 := by nlinarith
      omega
    have h3 := Nat.le_of_dvd h2 h1
    have h4 : q₀ ^ 2 ≤ q₀ ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
    rw [hq] at h3
    omega
  · rw [unitaryInvolution_apply, ← pow_succ, ← Units.val_pow_eq_pow_val, ← pow_mul, hmul, ← hord,
      pow_orderOf_eq_one, Units.val_one]

end UParam

section UData

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

abbrev aU : K := -(2 : K)⁻¹

omit [Finite K] [Fact p.Prime] [CharP K p] in
theorem aU_rel (h2 : (2 : K) ≠ 0) : 2 * (aU : K) + 1 = 0 := by
  rw [aU, mul_neg, mul_inv_cancel₀ h2, neg_add_cancel]

omit [Finite K] [Fact p.Prime] [CharP K p] in
theorem map_aU (φ : K ≃+* K) : φ (aU : K) = aU := by
  rw [aU, map_neg, map_inv₀, map_ofNat]

variable (μ : Type) [Fintype μ] [DecidableEq μ]

@[expose] noncomputable def uData (hK : Nat.card K = (p ^ f) ^ 2) (h2 : (2 : K) ≠ 0)
    (τ : K ≃+* K) (hτ3 : τ ^ 3 = 1) (b l : K) (hτb : τ b = b)
    (hb : unitaryInvolution K p f b * b = 1 - aU * aU) (hb0 : b ≠ 0)
    (hl : unitaryInvolution K p f l * l = 1) (hτl : τ l ≠ l) : FieldData K μ where
  G2 := suOn (unitaryInvolution K p f) (Fin 2)
  Gl := suOn (unitaryInvolution K p f) (Lam μ)
  Gt := suOn (unitaryInvolution K p f) (Kap μ)
  blk_top P hP Y hY := (blk_mem_suOn_iff P Y).2 ⟨hP, hY⟩
  blk_lam P hP := (blk_mem_suOn_iff P 1).2 ⟨hP, one_mem _⟩
  top_inv Y h := ((blk_mem_suOn_iff 1 Y).1 h).2
  c := cU (unitaryInvolution K p f) aU b (cU_det hb)
  c_mem := cU_mem (map_aU _) (unitaryInvolution_involutive hK b) hb
  c_rel := cU_rel (aU_rel h2) hb
  c_ne := by
    change (!![aU, b; -unitaryInvolution K p f b, aU] : Matrix (Fin 2) (Fin 2) K) 0 1 ≠ 0
    simpa using hb0
  x := l
  w := wU (unitaryInvolution K p f) l (wU_det hl)
  w_mem := wU_mem (unitaryInvolution_involutive hK l) hl
  coe_w := by
    have hl' : unitaryInvolution K p f l = l⁻¹ := eq_inv_of_mul_eq_one_left hl
    change !![l, 0; 0, unitaryInvolution K p f l] = !![l, 0; 0, l⁻¹]
    rw [hl']
  x_sq := (ne_zero_and_sq_ne_one hτl).2
  negOne_mem := negOne_mem_suOn _
  σ := τ
  σ_cube := hτ3
  σ_x := hτl
  map_Gt g hg := by
    rw [mem_suOn] at hg ⊢
    rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
    have e : ((g : Matrix (Kap μ) (Kap μ) K).map τ).map (unitaryInvolution K p f) =
        ((g : Matrix (Kap μ) (Kap μ) K).map (unitaryInvolution K p f)).map τ := by
      rw [Matrix.map_map, Matrix.map_map]
      congr 1
      funext c
      exact CFSG.LieType.Chevalley.ringEquiv_comm_of_finite _ _ c
    change (((g : Matrix (Kap μ) (Kap μ) K).map τ).map (unitaryInvolution K p f))ᵀ *
      (g : Matrix (Kap μ) (Kap μ) K).map τ = 1
    rw [e, ← Matrix.transpose_map, ← Matrix.map_mul, hg, Matrix.map_one _ (map_zero τ) (map_one τ)]
  map_c := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
    change (!![aU, b; -unitaryInvolution K p f b, aU] : Matrix (Fin 2) (Fin 2) K).map τ =
      !![aU, b; -unitaryInvolution K p f b, aU]
    have hτbar : τ (unitaryInvolution K p f b) = unitaryInvolution K p f b := by
      rw [← CFSG.LieType.Chevalley.ringEquiv_comm_of_finite, hτb]
    generalize unitaryInvolution K p f b = ub at hτbar ⊢
    ext i j
    fin_cases i <;> fin_cases j <;> simp [map_aU, hτb, hτbar]

end UData

section ULayer

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
  {μ : Type} [Fintype μ] [DecidableEq μ]

theorem uData_layer {hK : Nat.card K = (p ^ f) ^ 2} {h2 : (2 : K) ≠ 0} {τ : K ≃+* K}
    {hτ3 : τ ^ 3 = 1} {b l : K} {hτb : τ b = b}
    {hb : unitaryInvolution K p f b * b = 1 - aU * aU} {hb0 : b ≠ 0}
    {hl : unitaryInvolution K p f l * l = 1} {hτl : τ l ≠ l} (hτ : orderOf τ = 3)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) (h3 : (3 : K) ≠ 0) :
    GLAPLayer 3 (uData μ hK h2 τ hτ3 b l hτb hb hb0 hl hτl).Glσ ≠ ⊥ := by
  set D := uData μ hK h2 τ hτ3 b l hτb hb hb0 hl hτl with hD
  obtain ⟨h3f, hcardE, hbar⟩ := fixField_unitary hK hτ
  set E := fixField τ with hE
  haveI : CharP E p := Subfield.charP E p
  set f₀ := f / 3 with hf₀
  have hp := (Fact.out : p.Prime)
  have hf : 1 ≤ f := by
    by_contra h0
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    rw [hK, show f = 0 by omega, pow_zero, one_pow] at h1
    omega
  have h5 : 5 ≤ p ^ f₀ := by
    have h5p : 5 ≤ p := hp.five_le_of_ne_two_of_ne_three hp2 hp3
    have hf3 : 1 ≤ f₀ := by
      obtain ⟨k, rfl⟩ := h3f
      omega
    exact h5p.trans (Nat.le_self_pow (by omega) p)
  have hbarE : ∀ y : E, unitaryInvolution K p f (y : K) =
      ((unitaryInvolution E p f₀ y : E) : K) := fun y => by
    rw [hbar _ y.2, unitaryInvolution_apply, SubmonoidClass.coe_pow]
  have hmapE : ∀ Y : Matrix (Lam μ) (Lam μ) E,
      (Y.map E.subtype).map (unitaryInvolution K p f) =
        (Y.map (unitaryInvolution E p f₀)).map E.subtype := fun Y => by
    ext i j
    exact hbarE (Y i j)
  have hφmem : ∀ Y : ↥(suOn (unitaryInvolution E p f₀) (Lam μ)),
      Matrix.SpecialLinearGroup.map E.subtype (Y : SpecialLinearGroup (Lam μ) E) ∈ D.Gl := by
    intro Y
    have hY := mem_suOn.1 Y.2
    change Matrix.SpecialLinearGroup.map E.subtype (Y : SpecialLinearGroup (Lam μ) E) ∈
      suOn (unitaryInvolution K p f) (Lam μ)
    rw [mem_suOn, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, hmapE,
      ← Matrix.transpose_map, ← Matrix.map_mul, hY, Matrix.map_one _ (map_zero _) (map_one _)]
  set φ : ↥(suOn (unitaryInvolution E p f₀) (Lam μ)) →* ↥D.Gl :=
    ((Matrix.SpecialLinearGroup.map E.subtype).comp
      (suOn (unitaryInvolution E p f₀) (Lam μ)).subtype).codRestrict D.Gl hφmem with hφ
  have hφinj : Function.Injective φ := by
    intro a b' h
    have h' := congrArg (fun g : ↥D.Gl =>
      ((g : SpecialLinearGroup (Lam μ) K) : Matrix (Lam μ) (Lam μ) K)) h
    apply Subtype.ext
    apply Subtype.ext
    ext i j
    exact congrFun (congrFun h' i) j
  have hrange : φ.range = D.Glσ := by
    ext Y
    constructor
    · rintro ⟨Y', rfl⟩
      rw [D.mem_Glσ]
      apply Subtype.ext
      ext i j
      exact (((Y' : SpecialLinearGroup (Lam μ) E) : Matrix (Lam μ) (Lam μ) E) i j).2
    · intro hY
      rw [D.mem_Glσ] at hY
      have hent : ∀ i j,
          ((Y : SpecialLinearGroup (Lam μ) K) : Matrix (Lam μ) (Lam μ) K) i j ∈ E := fun i j => by
        have h := congrArg (fun g : SpecialLinearGroup (Lam μ) K =>
          (g : Matrix (Lam μ) (Lam μ) K) i j) hY
        exact h
      obtain ⟨Y', hY'⟩ := exists_sl_map_eq E _ hent
      have hY'mem : Y' ∈ suOn (unitaryInvolution E p f₀) (Lam μ) := by
        have hYu := mem_suOn.1 Y.2
        rw [mem_suOn]
        apply (Matrix.map_injective (f := E.subtype) Subtype.val_injective)
        dsimp only
        rw [Matrix.map_mul, Matrix.transpose_map, ← hmapE,
          Matrix.map_one _ (map_zero _) (map_one _)]
        have e1 : (Y' : Matrix (Lam μ) (Lam μ) E).map E.subtype =
            ((Y : SpecialLinearGroup (Lam μ) K) : Matrix (Lam μ) (Lam μ) K) := by
          rw [← hY', Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
        rw [e1]
        exact hYu
      exact ⟨⟨Y', hY'mem⟩, Subtype.ext hY'⟩
  have hq : CFSG.Open.IsQuasisimple ↥D.Glσ :=
    CFSG.ComponentClassification.Components.quasisimple_of_equiv
      ((MulEquiv.subgroupCongr hrange).symm.trans (MonoidHom.ofInjective hφinj).symm)
      (CFSG.LocalAnalysis.GLTheoremA.S267.P3.Uni.isQuasisimple_suOn (K := E) hcardE h5
        (by simp [Lam]))
  obtain ⟨l₀, hτl₀, hl₀, hl₀2⟩ := exists_fix_norm_one hK hp2 hp3 hτ
  have hcfix : (⟨blk μ (D.c, 1), D.blk_lam _ D.c_mem⟩ : ↥D.Gl) ∈ D.Glσ := by
    rw [D.mem_Glσ]
    change Matrix.SpecialLinearGroup.map (τ : K →+* K) (blk μ (D.c, 1)) = blk μ (D.c, 1)
    rw [FieldData.map_blk, map_one,
      show Matrix.SpecialLinearGroup.map (τ : K →+* K) D.c = D.c from D.map_c]
  have hw₀mem : wU (unitaryInvolution K p f) l₀ (wU_det hl₀) ∈ D.G2 :=
    wU_mem (unitaryInvolution_involutive hK l₀) hl₀
  have hτbar₀ : τ (unitaryInvolution K p f l₀) = unitaryInvolution K p f l₀ := by
    rw [← CFSG.LieType.Chevalley.ringEquiv_comm_of_finite, hτl₀]
  have hwfix : (⟨blk μ (wU (unitaryInvolution K p f) l₀ (wU_det hl₀), 1),
      D.blk_lam _ hw₀mem⟩ : ↥D.Gl) ∈ D.Glσ := by
    rw [D.mem_Glσ]
    change Matrix.SpecialLinearGroup.map (τ : K →+* K)
      (blk μ (wU (unitaryInvolution K p f) l₀ (wU_det hl₀), 1)) =
        blk μ (wU (unitaryInvolution K p f) l₀ (wU_det hl₀), 1)
    rw [FieldData.map_blk, map_one]
    congr 2
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
    change (!![l₀, 0; 0, unitaryInvolution K p f l₀] : Matrix (Fin 2) (Fin 2) K).map τ =
      !![l₀, 0; 0, unitaryInvolution K p f l₀]
    generalize unitaryInvolution K p f l₀ = ul at hτbar₀ ⊢
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hτl₀, hτbar₀]
  have hdvd : 3 ∣ Nat.card (↥D.Glσ ⧸ Subgroup.center ↥D.Glσ) := by
    refine CFSG.LocalAnalysis.GLTheoremA.H81.LinA3.dvd_card_quotient_center_of_not_commute
      Nat.prime_three hcfix hwfix ?_ ?_
    · apply Subtype.ext
      rw [Subgroup.coe_pow]
      change blk μ (D.c, 1) ^ 3 = 1
      rw [← map_pow, Prod.pow_mk, D.c_pow_three, one_pow, blk_one_one]
    · intro h
      have h' := congrArg (fun g : ↥D.Gl => (g : SpecialLinearGroup (Lam μ) K)) h
      simp only [Subgroup.coe_mul, ← map_mul] at h'
      have h'' := congrArg Prod.fst (blk_injective h')
      exact cU_mul_wU_ne (aU_rel h2) hb hl₀ hl₀2 h3 h''
  exact CFSG.LocalAnalysis.GLTheoremA.Y10F.glaPLayer_ne_bot_of_normal_quasisimple Nat.prime_three
    le_rfl (by rw [Subgroup.subgroupOf_self]; infer_instance) hq hdvd

end ULayer

section UIso

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
  {μ : Type} [Fintype μ] [DecidableEq μ] {n : ℕ}

theorem SUid_eq_gramSU (h : UnitaryFieldData p f K) (n : ℕ) :
    CFSG.LieType.Universal.Unitary.SUid (unitaryInvolution K p f) n =
      gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  have hmap : ∀ M : Matrix (Fin n) (Fin n) K, M.map h.bar = M.map (unitaryInvolution K p f) :=
    fun M => by
      ext i j
      rw [Matrix.map_apply, Matrix.map_apply, UnitaryFieldData.bar_apply, unitaryInvolution_apply]
  ext B
  rw [CFSG.LieType.Universal.Unitary.mem_SUid, mem_gramSU, Units.val_one, Matrix.mul_one, hmap,
    and_comm]
  rfl

theorem scalars_eq_normOneScalars (h : UnitaryFieldData p f K) (n : ℕ) (hn : 0 < n) :
    (StatedScalars (Fin n) K).subgroupOf (gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) =
      normOneScalars h (gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) n := by
  ext g
  rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range]
  constructor
  · rintro ⟨c, hc⟩
    have hg := (mem_gramSU.1 g.2)
    rw [← hc] at hg
    obtain ⟨hu, hdet⟩ := hg
    refine ⟨c, ?_, ?_, hc.symm⟩
    · have h00 := congrFun (congrFun hu ⟨0, hn⟩) ⟨0, hn⟩
      simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply,
        Matrix.mul_apply] at h00
      rw [UnitaryFieldData.norm, mul_comm]
      exact h00
    · apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_one]
      simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
        Finset.prod_const] using hdet
  · rintro ⟨c, -, -, hc⟩
    exact ⟨c, hc.symm⟩

variable {hK : Nat.card K = (p ^ f) ^ 2} {h2 : (2 : K) ≠ 0} {τ : K ≃+* K}
  {hτ3 : τ ^ 3 = 1} {b l : K} {hτb : τ b = b}
  {hb : unitaryInvolution K p f b * b = 1 - aU * aU} {hb0 : b ≠ 0}
  {hl : unitaryInvolution K p f l * l = 1} {hτl : τ l ≠ l}

@[expose] noncomputable def uTopEquiv (h : UnitaryFieldData p f K) (eι : Kap μ ≃ Fin n) :
    ↥(uData μ hK h2 τ hτ3 b l hτb hb hb0 hl hτl).Gt ≃*
      ↥(gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :=
  (CFSG.LocalAnalysis.GLTheoremA.S267.P3.Uni.suOnEquiv eι).trans
    (MulEquiv.subgroupCongr (SUid_eq_gramSU h n))

theorem map_Zt_uTopEquiv (h : UnitaryFieldData p f K) (eι : Kap μ ≃ Fin n) :
    (uData μ hK h2 τ hτ3 b l hτb hb hb0 hl hτl).Zt.map
        (uTopEquiv (hK := hK) (h2 := h2) (hτ3 := hτ3) (hτb := hτb) (hb := hb) (hb0 := hb0)
          (hl := hl) (hτl := hτl) h eι).toMonoidHom =
      normOneScalars h (gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) n := by
  have hn : 0 < n := by
    have := Fintype.card_congr eι
    simp only [Kap, Lam, Fintype.card_sum, Fintype.card_fin] at this
    omega
  rw [← scalars_eq_normOneScalars h n hn]
  exact CFSG.LocalAnalysis.GLTheoremA.S267.P3.Uni.map_center_suOnEquiv eι (SUid_eq_gramSU h n)

@[expose] noncomputable def uXEquiv (h : UnitaryFieldData p f K) (eι : Kap μ ≃ Fin n) :
    (uData μ hK h2 τ hτ3 b l hτb hb hb0 hl hτl).XD ≃*
      primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
  QuotientGroup.congr _ _ (uTopEquiv h eι) (map_Zt_uTopEquiv h eι)

theorem uXEquiv_mk (h : UnitaryFieldData p f K) (eι : Kap μ ≃ Fin n)
    (g : ↥(uData μ hK h2 τ hτ3 b l hτb hb hb0 hl hτl).Gt) :
    uXEquiv h eι ((uData μ hK h2 τ hτ3 b l hτb hb hb0 hl hτl).πD g) =
      ((uTopEquiv h eι g : gramSU h _) : primeFormP h _) :=
  QuotientGroup.congr_mk' _ _ _ (map_Zt_uTopEquiv h eι) g

theorem uTopEquiv_σt (h : UnitaryFieldData p f K) (eι : Kap μ ≃ Fin n)
    (g : ↥(uData μ hK h2 τ hτ3 b l hτb hb hb0 hl hτl).Gt) :
    uTopEquiv h eι ((uData μ hK h2 τ hτ3 b l hτb hb hb0 hl hτl).σt g) =
      primeFormFieldSU h isPrimeFormGram_one τ (uTopEquiv h eι g) := by
  apply Subtype.ext
  apply Units.ext
  change reindex eι eι (((Matrix.SpecialLinearGroup.map (τ : K →+* K)
      (g : SpecialLinearGroup (Kap μ) K)) : SpecialLinearGroup (Kap μ) K) :
        Matrix (Kap μ) (Kap μ) K) =
    (reindex eι eι ((g : SpecialLinearGroup (Kap μ) K) : Matrix (Kap μ) (Kap μ) K)).map τ
  ext i j
  rfl

theorem congr_ψD_eq_primeFormFieldHom (h : UnitaryFieldData p f K) (eι : Kap μ ≃ Fin n) :
    MulAut.congr (uXEquiv h eι) (uData μ hK h2 τ hτ3 b l hτb hb hb0 hl hτl).ψD =
      primeFormFieldHom h isPrimeFormGram_one τ := by
  ext x
  obtain ⟨A, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨g, rfl⟩ := (uTopEquiv (hK := hK) (h2 := h2) (hτ3 := hτ3) (hτb := hτb) (hb := hb)
    (hb0 := hb0) (hl := hl) (hτl := hτl) h eι).surjective A
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply]
  have e1 : (uXEquiv h eι).symm ((uTopEquiv h eι g : gramSU h _) : primeFormP h _) =
      (uData μ hK h2 τ hτ3 b l hτb hb hb0 hl hτl).πD g := by
    rw [MulEquiv.symm_apply_eq, uXEquiv_mk]
  have e2 := (uData μ hK h2 τ hτ3 b l hτb hb hb0 hl hτl).ψD_mk g
  rw [e1, e2, uXEquiv_mk, uTopEquiv_σt]
  exact (primeFormFieldAut_mk h isPrimeFormGram_one τ _).symm

end UIso

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher in
theorem modelB_primeFormP {K : Type} [Field K] [Finite K] {p f : ℕ} (h : UnitaryFieldData p f K)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) {n : ℕ} (hn : n = 4 ∨ n = 5) {τ : K ≃+* K} (hτ : orderOf τ = 3) :
    ModelB (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
      (primeFormFieldHom h isPrimeFormGram_one τ) := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  haveI : CharP K p := h.charP
  have hK : Nat.card K = (p ^ f) ^ 2 := h.card_eq_sq
  have hp := h.prime
  have hτ3 : τ ^ 3 = 1 := hτ ▸ pow_orderOf_eq_one τ
  have hτ1 : τ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hτ
    omega
  have hcast : ∀ m : ℕ, m.Prime → p ≠ m → ((m : ℕ) : K) ≠ 0 := fun m hm hne hc =>
    hne ((Nat.prime_dvd_prime_iff_eq hp hm).1 ((CharP.cast_eq_zero_iff K p m).1 hc))
  have h3 : (3 : K) ≠ 0 := by exact_mod_cast hcast 3 Nat.prime_three hp3
  have h2 : (2 : K) ≠ 0 := by exact_mod_cast hcast 2 Nat.prime_two hp2
  have hc34 : (1 : K) - aU * aU ≠ 0 := by
    intro hc
    apply h3
    have e3 : (3 : K) = 4 * (1 - aU * aU) := by
      have := aU_rel h2
      linear_combination (2 * (aU : K) - 1) * this
    rw [e3, hc, mul_zero]
  have hτc : τ ((1 : K) - aU * aU) = 1 - aU * aU := by rw [map_sub, map_one, map_mul, map_aU]
  have hbc : unitaryInvolution K p f ((1 : K) - aU * aU) = 1 - aU * aU := by
    rw [map_sub, map_one, map_mul, map_aU]
  obtain ⟨b, hτb, hb⟩ := exists_fix_norm_eq hK hτ hτc hbc hc34
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hb
    exact hc34 hb.symm
  obtain ⟨l, hτl, hl⟩ := exists_norm_one_not_fix hK hp2 hp3 hτ
  have hcard : Fintype.card (Kap (Fin (n - 4))) = n := by
    simp only [Kap, Lam, Fintype.card_sum, Fintype.card_fin]
    omega
  set eι : Kap (Fin (n - 4)) ≃ Fin n := Fintype.equivFinOfCardEq hcard with heι
  set D := uData (Fin (n - 4)) hK h2 τ hτ3 b l hτb hb hb0 hl hτl with hD
  have h5 : 5 ≤ p ^ f := by
    have h5p : 5 ≤ p := hp.five_le_of_ne_two_of_ne_three hp2 hp3
    exact h5p.trans (Nat.le_self_pow (by have := h.one_le; omega) p)
  have hl' : CFSG.Open.IsQuasisimple ↥D.Gl :=
    CFSG.LocalAnalysis.GLTheoremA.S267.P3.Uni.isQuasisimple_suOn hK h5 (by simp [Lam])
  have hZ3 : ∀ z ∈ D.Zt, z ^ 3 = 1 → z = 1 := D.hZ3_of_card (by rw [hcard]; omega)
  have hn3 : 3 ≤ n := by omega
  have hq : ¬(n = 3 ∧ p ^ f = 2) := fun h' => by omega
  set Φ := uXEquiv (hK := hK) (h2 := h2) (hτ3 := hτ3) (hτb := hτb) (hb := hb) (hb0 := hb0)
    (hl := hl) (hτl := hτl) h eι with hΦ
  have hcompat : MulAut.congr Φ D.ψD = primeFormFieldHom h isPrimeFormGram_one τ :=
    congr_ψD_eq_primeFormFieldHom (hK := hK) (h2 := h2) (hτ3 := hτ3) (hτb := hτb) (hb := hb)
      (hb0 := hb0) (hl := hl) (hτl := hτl) h eι
  have hout : D.ψD ∉ (MulAut.conj : D.XD →* MulAut D.XD).range := by
    rintro ⟨y, hy⟩
    obtain ⟨s, hs⟩ := QuotientGroup.mk_surjective (Φ y)
    have h1 : primeFormFieldHom h isPrimeFormGram_one τ =
        primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ⟨s, s.2.1⟩ := by
      rw [← hcompat, ← hy, congr_conj, ← hs, primeFormConjHom_eq_conj]
    have h2' := primeFormFieldFactor_apply h isPrimeFormGram_one hn3 hq 1 τ
    rw [map_one, one_mul, h1] at h2'
    have h3' := primeFormFieldFactor_apply h isPrimeFormGram_one hn3 hq ⟨s, s.2.1⟩ 1
    rw [map_one, mul_one, h2'] at h3'
    exact hτ1 h3'
  have hM := D.modelB h3 h2 hl' hZ3 (uData_layer hτ hp2 hp3 h3) hout
  have hc := ModelB.congr Φ hM
  rwa [hcompat] at hc

end CFSG.LocalAnalysis.GLTheoremA.S267.P3.Field

end
