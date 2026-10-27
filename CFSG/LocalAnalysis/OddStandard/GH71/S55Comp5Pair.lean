module

public import CFSG.LocalAnalysis.OddStandard.GH71.S55Comp5Gen

public section

namespace CFSG.OddStandard.GH71.S55

open Subgroup CFSG CFSG.GH74.GLS.Stage2.Signalizer.Ivk8 Matrix CFSG.Assembly.LowTwoRank

namespace C5

variable {F : Type} [Field F]

@[expose] def negUnip : Matrix (Fin 2) (Fin 2) F := !![-1, -1; 0, -1]

theorem negUnip_pow (n : ℕ) :
    (negUnip : Matrix (Fin 2) (Fin 2) F) ^ n =
      !![(-1 : F) ^ n, (-1 : F) ^ n * (n : F); 0, (-1 : F) ^ n] := by
  induction n with
  | zero => rw [pow_zero, Matrix.one_fin_two]; simp
  | succ n ih =>
    rw [pow_succ, ih, negUnip, Matrix.mul_fin_two]
    simp only [mul_neg, mul_one, mul_zero, add_zero, neg_zero, zero_add, pow_succ,
      Nat.cast_succ]
    congr 1
    ring_nf

theorem cast_eq_zero_iff_of_card [Finite F] {p : ℕ} (hp : p.Prime) (hF : Nat.card F = p)
    (n : ℕ) : (n : F) = 0 ↔ p ∣ n := by
  have : Fintype F := Fintype.ofFinite F
  have : Fact p.Prime := ⟨hp⟩
  have : CharP F p := charP_of_card_eq_prime (by rw [Fintype.card_eq_nat_card]; exact hF)
  exact CharP.cast_eq_zero_iff F p n

theorem orderOf_negUnip [Finite F] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hF : Nat.card F = p) :
    orderOf (negUnip : Matrix (Fin 2) (Fin 2) F) = 2 * p := by
  have hc := cast_eq_zero_iff_of_card hp hF
  have h2F : (2 : F) ≠ 0 := by
    intro h
    have : p ∣ 2 := (hc 2).mp (by exact_mod_cast h)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
  have hodd : Odd p := hp.odd_of_ne_two hp2
  rw [orderOf_eq_iff (by have := hp.pos; omega)]
  refine ⟨?_, fun m hm hm0 h => ?_⟩
  · have h2p : ((2 * p : ℕ) : F) = 0 := (hc _).mpr (dvd_mul_left p 2)
    rw [negUnip_pow, h2p, Matrix.one_fin_two, pow_mul]
    simp
  · rw [negUnip_pow, Matrix.one_fin_two] at h
    have h1 : (-1 : F) ^ m * (m : F) = 0 := by
      simpa using congrFun (congrFun h 0) 1
    have h0 : (-1 : F) ^ m = 1 := by
      simpa using congrFun (congrFun h 0) 0
    have hm' : (m : F) = 0 := by
      rw [h0, one_mul] at h1
      exact h1
    obtain ⟨k, rfl⟩ := (hc m).mp hm'
    have hk : k = 1 := by
      rcases Nat.lt_or_ge k 2 with hk | hk
      · interval_cases k <;> simp_all
      · nlinarith
    subst hk
    rw [mul_one, hodd.neg_one_pow] at h0
    exact h2F (by linear_combination -h0)

noncomputable def negUnipSL : SpecialLinearGroup (Fin 2) F :=
  ⟨negUnip, by simp [negUnip, det_fin_two]⟩

theorem orderOf_negUnipSL [Finite F] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hF : Nat.card F = p) :
    orderOf (specialLinearGroupEquivStatedSL 2 F negUnipSL) = 2 * p := by
  rw [MulEquiv.orderOf_eq, ← orderOf_injective _ SpecialLinearGroup.toGL_injective, ← orderOf_units]
  exact orderOf_negUnip hp hp2 hF

end C5

open C5

variable {Y : Type} [Group Y] [Finite Y]

theorem not_surj_sl2_of_no_two_p {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hno : ∀ w : Y, orderOf w ≠ 2 * p) (J : Subgroup Y) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = p) (φ : ↥J →* ↥(StatedSL 2 F)) (hφ : Function.Surjective φ) : False := by
  obtain ⟨w, hw⟩ := hφ (specialLinearGroupEquivStatedSL 2 F negUnipSL)
  have h1 : 2 * p ∣ orderOf w := by
    rw [← orderOf_negUnipSL hp hp2 hF, ← hw]
    exact orderOf_map_dvd φ w
  have h2 : orderOf (w ^ (orderOf w / (2 * p))) = 2 * p :=
    orderOf_pow_orderOf_div (orderOf_pos w).ne' h1
  apply hno ((w ^ (orderOf w / (2 * p)) : ↥J) : Y)
  rw [Subgroup.orderOf_coe, h2]

theorem not_pairSL2_of_no_two_p {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hno : ∀ w : Y, orderOf w ≠ 2 * p) (hR : NoR 2 Y) (y g : Y) : ¬ PairSL2 p y g := by
  rintro ⟨F, _, _, hF, ⟨φ, hφ⟩ | ⟨hnR, -⟩⟩
  · exact not_surj_sl2_of_no_two_p hp hp2 hno _ hF φ hφ
  · exact hnR hR

theorem not_surj_sl2_of_abelian_sylow
    (hab : ∀ S : Sylow 2 Y, ∀ a ∈ (S : Subgroup Y), ∀ b ∈ (S : Subgroup Y), a * b = b * a)
    (J : Subgroup Y) {F : Type} [Field F] [Finite F] (hF2 : ringChar F ≠ 2)
    (φ : ↥J →* ↥(StatedSL 2 F)) (hφ : Function.Surjective φ) : False := by
  open CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices in
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, b, hab'⟩ := (odd_field_two_dimensional_quaternion_matrices hF2).1
  set ι : QuaternionGroup 2 →* ↥(StatedSL 2 F) :=
    (specialLinearGroupEquivStatedSL 2 F).toMonoidHom.comp (quatHom hab') with hιdef
  have hι : Function.Injective ι :=
    (specialLinearGroupEquivStatedSL 2 F).injective.comp (quatHom_injective hF2 hab')
  obtain ⟨T⟩ : Nonempty (Sylow 2 ↥J) := inferInstance
  have hT : ∀ x ∈ (T : Subgroup ↥J), ∀ y ∈ (T : Subgroup ↥J), x * y = y * x := by
    obtain ⟨S, hS⟩ := (T.isPGroup'.map J.subtype).exists_le_sylow
    intro x hx y hy
    exact Subtype.ext (hab S _ (hS ⟨x, hx, rfl⟩) _ (hS ⟨y, hy, rfl⟩))
  have hT' : ∀ x ∈ ((T.mapSurjective hφ : Sylow 2 _) : Subgroup ↥(StatedSL 2 F)),
      ∀ y ∈ ((T.mapSurjective hφ : Sylow 2 _) : Subgroup ↥(StatedSL 2 F)), x * y = y * x := by
    rw [Sylow.coe_mapSurjective]
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hT x hx y hy]
  have hQ : IsPGroup 2 ↥ι.range := by
    refine IsPGroup.of_card (n := 3) ?_
    rw [← Nat.card_congr (MonoidHom.ofInjective hι).toEquiv, Nat.card_eq_fintype_card,
      QuaternionGroup.card]
    norm_num
  obtain ⟨P', hP'⟩ := hQ.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥(StatedSL 2 F) (T.mapSurjective hφ) P'
  have hconj : ∀ x ∈ ι.range, g⁻¹ * x * g ∈
      ((T.mapSurjective hφ : Sylow 2 _) : Subgroup ↥(StatedSL 2 F)) := by
    intro x hx
    have h1 := hP' hx
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h1
    convert h1 using 1
    rw [MulAut.smul_def, ← map_inv, MulAut.conj_apply, inv_inv]
  have hq := hT' _ (hconj _ ⟨QuaternionGroup.a 1, rfl⟩) _ (hconj _ ⟨QuaternionGroup.xa 0, rfl⟩)
  have e1 : ∀ x y : ↥(StatedSL 2 F), g⁻¹ * x * g * (g⁻¹ * y * g) = g⁻¹ * (x * y) * g := by
    intro x y; group
  rw [e1, e1] at hq
  have hq' := mul_left_cancel (mul_right_cancel hq)
  rw [← map_mul, ← map_mul] at hq'
  exact absurd (hι hq') (by decide)

theorem not_pairSL2_of_abelian_sylow {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hab : ∀ S : Sylow 2 Y, ∀ a ∈ (S : Subgroup Y), ∀ b ∈ (S : Subgroup Y), a * b = b * a)
    (hR : NoR 2 Y) (y g : Y) : ¬ PairSL2 p y g := by
  rintro ⟨F, _, _, hF, ⟨φ, hφ⟩ | ⟨hnR, -⟩⟩
  · refine not_surj_sl2_of_abelian_sylow hab _ ?_ φ hφ
    have : Fintype F := Fintype.ofFinite F
    have : Fact p.Prime := ⟨hp⟩
    have : CharP F p := charP_of_card_eq_prime (by rw [Fintype.card_eq_nat_card]; exact hF)
    rw [ringChar.eq F p]
    exact hp2
  · exact hnR hR

end CFSG.OddStandard.GH71.S55
