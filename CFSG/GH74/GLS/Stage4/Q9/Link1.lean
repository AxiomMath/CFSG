module

public import CFSG.GH74.GLS.Stage4.Q9.SettingFacts
public import CFSG.GH74.GLS.Stage4.Q9.ModelBaseBase

public section

namespace CFSG.GH74.GLS.Stage4.Q9

open Matrix

@[expose] def slEquivOfRingEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) :
    SpecialLinearGroup (Fin 2) R ≃* SpecialLinearGroup (Fin 2) S where
  toFun := SpecialLinearGroup.map e.toRingHom
  invFun := SpecialLinearGroup.map e.symm.toRingHom
  left_inv g := by
    apply Subtype.ext
    ext i j
    simp
  right_inv g := by
    apply Subtype.ext
    ext i j
    simp
  map_mul' := map_mul _

@[expose] def slConj (P : GL (Fin 2) F9) : SL2 ≃* SL2 where
  toFun g := ⟨(P : Matrix (Fin 2) (Fin 2) F9) * (g : Matrix (Fin 2) (Fin 2) F9) *
      ((P⁻¹ : GL (Fin 2) F9) : Matrix (Fin 2) (Fin 2) F9), by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.SpecialLinearGroup.det_coe, mul_one,
      ← Matrix.det_mul, Units.mul_inv, Matrix.det_one]⟩
  invFun g := ⟨((P⁻¹ : GL (Fin 2) F9) : Matrix (Fin 2) (Fin 2) F9) *
      (g : Matrix (Fin 2) (Fin 2) F9) * (P : Matrix (Fin 2) (Fin 2) F9), by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.SpecialLinearGroup.det_coe, mul_one,
      ← Matrix.det_mul, Units.inv_mul, Matrix.det_one]⟩
  left_inv g := by
    apply Subtype.ext
    show ((P⁻¹ : GL (Fin 2) F9) : Matrix (Fin 2) (Fin 2) F9) *
      ((P : Matrix (Fin 2) (Fin 2) F9) * (g : Matrix (Fin 2) (Fin 2) F9) *
        ((P⁻¹ : GL (Fin 2) F9) : Matrix (Fin 2) (Fin 2) F9)) * (P : Matrix (Fin 2) (Fin 2) F9) = g
    calc _ = (((P⁻¹ : GL (Fin 2) F9) : Matrix (Fin 2) (Fin 2) F9) *
            (P : Matrix (Fin 2) (Fin 2) F9)) * (g : Matrix (Fin 2) (Fin 2) F9) *
          (((P⁻¹ : GL (Fin 2) F9) : Matrix (Fin 2) (Fin 2) F9) *
            (P : Matrix (Fin 2) (Fin 2) F9)) := by simp only [Matrix.mul_assoc]
      _ = g := by rw [Units.inv_mul, Matrix.one_mul, Matrix.mul_one]
  right_inv g := by
    apply Subtype.ext
    show (P : Matrix (Fin 2) (Fin 2) F9) * (((P⁻¹ : GL (Fin 2) F9) : Matrix (Fin 2) (Fin 2) F9) *
      (g : Matrix (Fin 2) (Fin 2) F9) * (P : Matrix (Fin 2) (Fin 2) F9)) *
      ((P⁻¹ : GL (Fin 2) F9) : Matrix (Fin 2) (Fin 2) F9) = g
    calc _ = ((P : Matrix (Fin 2) (Fin 2) F9) *
            ((P⁻¹ : GL (Fin 2) F9) : Matrix (Fin 2) (Fin 2) F9)) * (g : Matrix (Fin 2) (Fin 2) F9) *
          ((P : Matrix (Fin 2) (Fin 2) F9) *
            ((P⁻¹ : GL (Fin 2) F9) : Matrix (Fin 2) (Fin 2) F9)) := by simp only [Matrix.mul_assoc]
      _ = g := by rw [Units.mul_inv, Matrix.one_mul, Matrix.mul_one]
  map_mul' g h := by
    apply Subtype.ext
    show (P : Matrix (Fin 2) (Fin 2) F9) * ((g : Matrix (Fin 2) (Fin 2) F9) *
        (h : Matrix (Fin 2) (Fin 2) F9)) * ((P⁻¹ : GL (Fin 2) F9) : Matrix (Fin 2) (Fin 2) F9) =
      ((P : Matrix (Fin 2) (Fin 2) F9) * (g : Matrix (Fin 2) (Fin 2) F9) *
        ((P⁻¹ : GL (Fin 2) F9) : Matrix (Fin 2) (Fin 2) F9)) *
      ((P : Matrix (Fin 2) (Fin 2) F9) * (h : Matrix (Fin 2) (Fin 2) F9) *
        ((P⁻¹ : GL (Fin 2) F9) : Matrix (Fin 2) (Fin 2) F9))
    calc _ = (P : Matrix (Fin 2) (Fin 2) F9) * (g : Matrix (Fin 2) (Fin 2) F9) *
        (((P⁻¹ : GL (Fin 2) F9) : Matrix (Fin 2) (Fin 2) F9) * (P : Matrix (Fin 2) (Fin 2) F9)) *
        (h : Matrix (Fin 2) (Fin 2) F9) *
        ((P⁻¹ : GL (Fin 2) F9) : Matrix (Fin 2) (Fin 2) F9) := by
          rw [Units.inv_mul, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]

theorem slConj_val (P : GL (Fin 2) F9) (g : SL2) :
    ((slConj P g : SL2) : Matrix (Fin 2) (Fin 2) F9) = (P : Matrix (Fin 2) (Fin 2) F9) *
      (g : Matrix (Fin 2) (Fin 2) F9) * ((P⁻¹ : GL (Fin 2) F9) : Matrix (Fin 2) (Fin 2) F9) := rfl

theorem toGL_slConj (P : GL (Fin 2) F9) (g : SL2) :
    SpecialLinearGroup.toGL (slConj P g) = P * SpecialLinearGroup.toGL g * P⁻¹ := by
  apply Units.ext
  simp [slConj_val]

theorem toGL_sigmaAut (g : SL2) :
    SpecialLinearGroup.toGL (sigmaAut g) = A0 * SpecialLinearGroup.toGL g * A0⁻¹ := by
  apply Units.ext
  simp [sigmaAut_apply_val]

theorem normalize_entries :
    ∀ a b c d : F9, a * d - b * c ≠ 0 → (b * (a + d) = 0 ∧ c * (a + d) = 0 ∧ a * a = d * d) →
      ¬ IsSquare (a * d - b * c) →
      c ≠ 0 ∧ a + d = 0 ∧ ∃ s : F9, s ≠ 0 ∧ s * s * nu = a * a + b * c := by
  decide

theorem normalize_conj :
    ∀ a b c s : F9, c ≠ 0 → s * s * nu = a * a + b * c →
      (!![1, -a / c; 0, s / c] * !![a, b; c, -a] : Matrix (Fin 2) (Fin 2) F9) =
        (s • (!![0, nu; 1, 0] : Matrix (Fin 2) (Fin 2) F9)) * !![1, -a / c; 0, s / c] := by
  decide

theorem exists_conj_to_A0 (A : GL (Fin 2) F9) (hsc : ∃ l : F9, Matrix.scalar (Fin 2) l =
    (A : Matrix (Fin 2) (Fin 2) F9) * (A : Matrix (Fin 2) (Fin 2) F9))
    (hdet : ¬ IsSquare (Matrix.det (A : Matrix (Fin 2) (Fin 2) F9))) :
    ∃ (P : GL (Fin 2) F9) (s : F9ˣ),
      P * A * P⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 2) s * A0 := by
  obtain ⟨l, hl⟩ := hsc
  set a := (A : Matrix (Fin 2) (Fin 2) F9) 0 0 with ha
  set b := (A : Matrix (Fin 2) (Fin 2) F9) 0 1 with hb
  set c := (A : Matrix (Fin 2) (Fin 2) F9) 1 0 with hc
  set d := (A : Matrix (Fin 2) (Fin 2) F9) 1 1 with hd
  have hdetA : Matrix.det (A : Matrix (Fin 2) (Fin 2) F9) = a * d - b * c := by
    rw [Matrix.det_fin_two]
  have hdet0 : a * d - b * c ≠ 0 := by
    rw [← hdetA]
    exact (Matrix.isUnit_iff_isUnit_det _).mp A.isUnit |>.ne_zero
  have hsq : b * (a + d) = 0 ∧ c * (a + d) = 0 ∧ a * a = d * d := by
    have h01 := congrFun (congrFun hl 0) 1
    have h10 := congrFun (congrFun hl 1) 0
    have h00 := congrFun (congrFun hl 0) 0
    have h11 := congrFun (congrFun hl 1) 1
    simp [Matrix.scalar_apply, Matrix.mul_apply, Fin.sum_univ_two] at h01 h10 h00 h11
    refine ⟨?_, ?_, ?_⟩
    · linear_combination (-1 : F9) * h01
    · linear_combination (-1 : F9) * h10
    · linear_combination h11 - h00
  obtain ⟨hc0, htr, s, hs0, hss⟩ :=
    normalize_entries a b c d hdet0 hsq (by rw [← hdetA]; exact hdet)
  have hd' : d = -a := by linear_combination htr
  have hPdet : Matrix.det (!![1, -a / c; 0, s / c] : Matrix (Fin 2) (Fin 2) F9) ≠ 0 := by
    rw [Matrix.det_fin_two_of]
    simp [hc0, hs0]
  let P : GL (Fin 2) F9 := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hPdet
  have hsu : IsUnit s := hs0.isUnit
  refine ⟨P, hsu.unit, ?_⟩
  have hAmat : (A : Matrix (Fin 2) (Fin 2) F9) = !![a, b; c, -a] := by
    rw [← hd']
    exact Matrix.eta_fin_two _
  have hrel := normalize_conj a b c s hc0 hss
  have hcoe : (((Matrix.GeneralLinearGroup.scalar (Fin 2) hsu.unit * A0 : GL (Fin 2) F9)) :
      Matrix (Fin 2) (Fin 2) F9) = s • (!![0, nu; 1, 0] : Matrix (Fin 2) (Fin 2) F9) := by
    rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.scalar_apply, A0, Matrix.mul_apply, Fin.sum_univ_two]
  have hPval : (P : Matrix (Fin 2) (Fin 2) F9) = !![1, -a / c; 0, s / c] := rfl
  have hmat : (P : Matrix (Fin 2) (Fin 2) F9) * (A : Matrix (Fin 2) (Fin 2) F9) =
      (((Matrix.GeneralLinearGroup.scalar (Fin 2) hsu.unit * A0 : GL (Fin 2) F9)) :
        Matrix (Fin 2) (Fin 2) F9) * (P : Matrix (Fin 2) (Fin 2) F9) := by
    rw [hAmat, hcoe, hPval]
    exact hrel
  have hPA : P * A = (Matrix.GeneralLinearGroup.scalar (Fin 2) hsu.unit * A0) * P := Units.ext hmat
  calc P * A * P⁻¹ = (Matrix.GeneralLinearGroup.scalar (Fin 2) hsu.unit * A0) * P * P⁻¹ := by
        rw [hPA]
    _ = _ := by group

theorem involution_entries :
    ∀ a b c d : F9, a * d - b * c = 1 → a * a + b * c = 1 → b * (a + d) = 0 → c * (a + d) = 0 →
      d * d + b * c = 1 → (b = 0 ∧ c = 0 ∧ a = d ∧ (a = 1 ∨ a = -1)) := by
  decide

theorem sl2_involution (M : SL2) (h : M * M = 1) : M = 1 ∨ M = minusOne := by
  have h' : (M : Matrix (Fin 2) (Fin 2) F9) * (M : Matrix (Fin 2) (Fin 2) F9) = 1 :=
    congrArg (fun x : SL2 => (x : Matrix (Fin 2) (Fin 2) F9)) h
  have hdet : Matrix.det (M : Matrix (Fin 2) (Fin 2) F9) = 1 := M.2
  rw [Matrix.det_fin_two] at hdet
  have h00 := congrFun (congrFun h' 0) 0
  have h01 := congrFun (congrFun h' 0) 1
  have h10 := congrFun (congrFun h' 1) 0
  have h11 := congrFun (congrFun h' 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq, Matrix.one_apply_ne,
    ne_eq, Fin.zero_eq_one_iff, not_false_eq_true, Fin.one_eq_zero_iff,
    OfNat.ofNat_ne_one] at h00 h01 h10 h11
  have h01' : (M : Matrix (Fin 2) (Fin 2) F9) 0 1 * ((M : Matrix (Fin 2) (Fin 2) F9) 0 0 +
      (M : Matrix (Fin 2) (Fin 2) F9) 1 1) = 0 := by linear_combination h01
  have h10' : (M : Matrix (Fin 2) (Fin 2) F9) 1 0 * ((M : Matrix (Fin 2) (Fin 2) F9) 0 0 +
      (M : Matrix (Fin 2) (Fin 2) F9) 1 1) = 0 := by linear_combination h10
  obtain ⟨hb, hc, had, ha⟩ := involution_entries _ _ _ _ hdet h00 h01' h10' (by linear_combination h11)
  rcases ha with ha | ha
  · left
    have ha' : (M : Matrix (Fin 2) (Fin 2) F9) 1 1 = 1 := by rw [← had, ha]
    apply Subtype.ext
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [hb, hc, ha, ha']
  · right
    have ha' : (M : Matrix (Fin 2) (Fin 2) F9) 1 1 = -1 := by rw [← had, ha]
    apply Subtype.ext
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [hb, hc, ha, ha', minusOne_val]

theorem link_factor {G : Type} [Group G] {K : Subgroup G} {z t : G} {F : Type} [Field F]
    (hF : Nat.card F = 9) (φ : K ≃* SpecialLinearGroup (Fin 2) F) (A : GL (Fin 2) F)
    (hA : ∀ k k' : K, (k' : G) = t * k * t⁻¹ →
      ((φ k' : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        (A : Matrix (Fin 2) (Fin 2) F) * (φ k : Matrix (Fin 2) (Fin 2) F) *
          ((A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F))
    (hdet : ¬ IsSquare (Matrix.det (A : Matrix (Fin 2) (Fin 2) F)))
    (htt : t * t = 1) (hnorm : ∀ k ∈ K, t * k * t⁻¹ ∈ K)
    (hz : z * z = 1) (hz1 : z ≠ 1) :
    ∃ ψ : K ≃* SL2, (∀ k : K, (k : G) = z → ψ k = minusOne) ∧
      (∀ k k' : K, (k' : G) = t * k * t⁻¹ → ψ k' = sigmaAut (ψ k)) := by
  have : Finite F := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = Fintype.card F9 := by
    rw [← Nat.card_eq_fintype_card, hF, card_F9]
  let e : F ≃+* F9 := FiniteField.ringEquivOfCardEq hcard
  let ψ₀ : K ≃* SL2 := φ.trans (slEquivOfRingEquiv e)
  let A' : GL (Fin 2) F9 := Matrix.GeneralLinearGroup.map e.toRingHom A
  have hmapA : (A' : Matrix (Fin 2) (Fin 2) F9) = e.toRingHom.mapMatrix (A : Matrix (Fin 2) (Fin 2) F) :=
    rfl
  have hmapinv : ((A'⁻¹ : GL (Fin 2) F9) : Matrix (Fin 2) (Fin 2) F9) =
      e.toRingHom.mapMatrix ((A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
    show (((Matrix.GeneralLinearGroup.map e.toRingHom A)⁻¹ : GL (Fin 2) F9) :
      Matrix (Fin 2) (Fin 2) F9) = _
    rw [← map_inv]
    rfl
  have hψ₀mat : ∀ k : K, ((ψ₀ k : SL2) : Matrix (Fin 2) (Fin 2) F9) =
      e.toRingHom.mapMatrix ((φ k : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) :=
    fun k => rfl
  have hA' : ∀ k k' : K, (k' : G) = t * k * t⁻¹ →
      ((ψ₀ k' : SL2) : Matrix (Fin 2) (Fin 2) F9) = (A' : Matrix (Fin 2) (Fin 2) F9) *
        (ψ₀ k : Matrix (Fin 2) (Fin 2) F9) * ((A'⁻¹ : GL (Fin 2) F9) : Matrix (Fin 2) (Fin 2) F9) := by
    intro k k' hk
    rw [hψ₀mat, hA k k' hk, map_mul, map_mul, hmapA, hmapinv, hψ₀mat]
  have hdet' : ¬ IsSquare (Matrix.det (A' : Matrix (Fin 2) (Fin 2) F9)) := by
    rw [hmapA, ← RingHom.map_det]
    rintro ⟨r, hr⟩
    apply hdet
    refine ⟨e.symm r, ?_⟩
    apply e.injective
    simpa using hr
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hcomm : ∀ g : SL2, (g : Matrix (Fin 2) (Fin 2) F9) *
      ((A' : Matrix (Fin 2) (Fin 2) F9) * (A' : Matrix (Fin 2) (Fin 2) F9)) =
      ((A' : Matrix (Fin 2) (Fin 2) F9) * (A' : Matrix (Fin 2) (Fin 2) F9)) *
        (g : Matrix (Fin 2) (Fin 2) F9) := by
    intro g
    obtain ⟨k, rfl⟩ := ψ₀.surjective g
    set k₂ : K := ⟨t * k * t⁻¹, hnorm k k.2⟩ with hk₂
    have h1 := hA' k k₂ rfl
    have h2 := hA' k₂ k (by
      show (k : G) = t * (t * k * t⁻¹) * t⁻¹
      rw [hti]
      calc (k : G) = (t * t) * k * (t * t) := by rw [htt]; group
        _ = _ := by group)
    have hA'inv1 : ((A'⁻¹ : GL (Fin 2) F9) : Matrix (Fin 2) (Fin 2) F9) *
        (A' : Matrix (Fin 2) (Fin 2) F9) = 1 := Units.inv_mul A'
    have hA'inv2 : (A' : Matrix (Fin 2) (Fin 2) F9) *
        ((A'⁻¹ : GL (Fin 2) F9) : Matrix (Fin 2) (Fin 2) F9) = 1 := Units.mul_inv A'
    rw [h1] at h2
    calc (ψ₀ k : Matrix (Fin 2) (Fin 2) F9) *
          ((A' : Matrix (Fin 2) (Fin 2) F9) * (A' : Matrix (Fin 2) (Fin 2) F9))
        = ((A' : Matrix (Fin 2) (Fin 2) F9) * ((A' : Matrix (Fin 2) (Fin 2) F9) *
            (ψ₀ k : Matrix (Fin 2) (Fin 2) F9) *
            ((A'⁻¹ : GL (Fin 2) F9) : Matrix (Fin 2) (Fin 2) F9)) *
            ((A'⁻¹ : GL (Fin 2) F9) : Matrix (Fin 2) (Fin 2) F9)) *
          ((A' : Matrix (Fin 2) (Fin 2) F9) * (A' : Matrix (Fin 2) (Fin 2) F9)) := by rw [← h2]
      _ = ((A' : Matrix (Fin 2) (Fin 2) F9) * (A' : Matrix (Fin 2) (Fin 2) F9)) *
          (ψ₀ k : Matrix (Fin 2) (Fin 2) F9) := by
        calc ((A' : Matrix (Fin 2) (Fin 2) F9) * ((A' : Matrix (Fin 2) (Fin 2) F9) *
              (ψ₀ k : Matrix (Fin 2) (Fin 2) F9) *
              ((A'⁻¹ : GL (Fin 2) F9) : Matrix (Fin 2) (Fin 2) F9)) *
              ((A'⁻¹ : GL (Fin 2) F9) : Matrix (Fin 2) (Fin 2) F9)) *
              ((A' : Matrix (Fin 2) (Fin 2) F9) * (A' : Matrix (Fin 2) (Fin 2) F9))
            = ((A' : Matrix (Fin 2) (Fin 2) F9) * (A' : Matrix (Fin 2) (Fin 2) F9)) *
              (ψ₀ k : Matrix (Fin 2) (Fin 2) F9) *
              (((A'⁻¹ : GL (Fin 2) F9) : Matrix (Fin 2) (Fin 2) F9) *
                (((A'⁻¹ : GL (Fin 2) F9) : Matrix (Fin 2) (Fin 2) F9) *
                  (A' : Matrix (Fin 2) (Fin 2) F9)) * (A' : Matrix (Fin 2) (Fin 2) F9)) := by
              simp only [Matrix.mul_assoc]
          _ = _ := by rw [hA'inv1, Matrix.mul_one, hA'inv1, Matrix.mul_one]
  obtain ⟨l, hl⟩ := exists_scalar_of_commute_sl2 (M := (A' : Matrix (Fin 2) (Fin 2) F9) *
    (A' : Matrix (Fin 2) (Fin 2) F9)) hcomm
  obtain ⟨P, s, hP⟩ := exists_conj_to_A0 A' ⟨l, hl⟩ hdet'
  refine ⟨ψ₀.trans (slConj P), ?_, ?_⟩
  · intro k hk
    have hkk : k * k = 1 := by
      apply Subtype.ext
      simpa [hk] using hz
    have hψ1 : (ψ₀.trans (slConj P)) k * (ψ₀.trans (slConj P)) k = 1 := by
      rw [← map_mul, hkk, map_one]
    rcases sl2_involution _ hψ1 with h1 | h1
    · exfalso
      have hk1 : k = 1 := by
        have := (ψ₀.trans (slConj P)).injective (h1.trans (map_one _).symm)
        exact this
      apply hz1
      rw [← hk, hk1]
      rfl
    · exact h1
  · intro k k' hk
    apply SpecialLinearGroup.toGL_injective
    have hGL1 : SpecialLinearGroup.toGL (ψ₀ k') =
        A' * SpecialLinearGroup.toGL (ψ₀ k) * A'⁻¹ := by
      apply Units.ext
      simpa using hA' k k' hk
    have hcentral : ∀ Y : GL (Fin 2) F9, Matrix.GeneralLinearGroup.scalar (Fin 2) s * Y =
        Y * Matrix.GeneralLinearGroup.scalar (Fin 2) s := by
      intro Y
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar]
      exact (Matrix.scalar_commute _ (fun r' => Commute.all _ _) _).eq
    show SpecialLinearGroup.toGL (slConj P (ψ₀ k')) = SpecialLinearGroup.toGL (sigmaAut (slConj P (ψ₀ k)))
    rw [toGL_slConj, toGL_sigmaAut, toGL_slConj, hGL1]
    calc P * (A' * SpecialLinearGroup.toGL (ψ₀ k) * A'⁻¹) * P⁻¹
        = (P * A' * P⁻¹) * (P * SpecialLinearGroup.toGL (ψ₀ k) * P⁻¹) * (P * A' * P⁻¹)⁻¹ := by
          group
      _ = (Matrix.GeneralLinearGroup.scalar (Fin 2) s * A0) *
            (P * SpecialLinearGroup.toGL (ψ₀ k) * P⁻¹) *
            (Matrix.GeneralLinearGroup.scalar (Fin 2) s * A0)⁻¹ := by rw [hP]
      _ = A0 * (P * SpecialLinearGroup.toGL (ψ₀ k) * P⁻¹) * A0⁻¹ := by
          have hc := hcentral
          calc _ = Matrix.GeneralLinearGroup.scalar (Fin 2) s * (A0 *
                (P * SpecialLinearGroup.toGL (ψ₀ k) * P⁻¹) * A0⁻¹) *
                (Matrix.GeneralLinearGroup.scalar (Fin 2) s)⁻¹ := by group
            _ = _ := by
              rw [hc, mul_assoc, mul_inv_cancel, mul_one]

theorem q9_link {G : Type} [Group G] {z : G} {K₁ K₂ : Subgroup G} {F₁ F₂ : Type} [Field F₁]
    [Field F₂] (S : Q9Setting G z K₁ K₂ F₁ F₂) :
    ∃ (ψ₁ : ↥K₁ ≃* SL2) (ψ₂ : ↥K₂ ≃* SL2),
      (∀ k : ↥K₁, (k : G) = z → ψ₁ k = minusOne) ∧ (∀ k : ↥K₂, (k : G) = z → ψ₂ k = minusOne) ∧
      (∀ k k' : ↥K₁, (k' : G) = S.t * (k : G) * S.t⁻¹ → ψ₁ k' = sigmaAut (ψ₁ k)) ∧
      (∀ k k' : ↥K₂, (k' : G) = S.t * (k : G) * S.t⁻¹ → ψ₂ k' = sigmaAut (ψ₂ k)) := by
  have htt : S.t * S.t = 1 := by
    have := pow_orderOf_eq_one S.t
    rw [S.t_ord] at this
    simpa [pow_two] using this
  have hz : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rw [S.z_ord] at this
    simpa [pow_two] using this
  have hz1 : z ≠ 1 := by
    intro h
    have := S.z_ord
    rw [h, orderOf_one] at this
    omega
  obtain ⟨ψ₁, hz₁, ht₁⟩ := link_factor (z := z) (t := S.t) S.card₁ S.φ₁ S.A S.A_act S.A_det htt
    (fun k hk => S.normal₁ S.t S.t_mem k hk) hz hz1
  obtain ⟨ψ₂, hz₂, ht₂⟩ := link_factor (z := z) (t := S.t) S.card₂ S.φ₂ S.B S.B_act S.B_det htt
    (fun k hk => S.normal₂ S.t S.t_mem k hk) hz hz1
  exact ⟨ψ₁, ψ₂, hz₁, hz₂, ht₁, ht₂⟩

end CFSG.GH74.GLS.Stage4.Q9
