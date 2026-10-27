module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisThmC9
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisE16Input
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisInputs
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisThmC5

public noncomputable section

namespace CFSG.ComponentClassification.GHarris

open CFSG Subgroup CFSG.GH74.GLS.Bg.TwoGroups CFSG.GH74.GLS.Bg.TwoGroups.L23 GL42 ThmC
open scoped Matrix

namespace ThmC.UTSylow

variable {X : Type} [Group X] [Finite X] (D : UTSylow X)

omit [Finite X] in
theorem card_T : Nat.card (D.T : Subgroup X) = 64 := by
  rw [← Nat.card_congr D.e.toEquiv, card_UT3c]

theorem F_normal (hTn : (D.T : Subgroup X).Normal) : D.F.Normal := by
  constructor
  intro f hf x
  have h := D.swap.conj_mem_E_of_normalizer_T
    ((normalizer_eq_top_iff.mpr hTn) ▸ mem_top x : x ∈ normalizer ((D.swap.T : Subgroup X) : Set X))
  rw [swap_E] at h
  exact h f hf

omit [Finite X] in
theorem Z_eq_inf : D.Z = D.E ⊓ D.F :=
  map_inf_eq _ _ _ D.toX_injective

theorem toMat_pow (A : M4c) (n : ℕ) : (A.pow n).toMat = A.toMat ^ n := by
  induction n with
  | zero => exact M4c.toMat_one
  | succ n ih => rw [M4c.pow, M4c.toMat_mul, ih, pow_succ]

abbrev thetaMat (hEn : D.E.Normal) (x : X) : M4 := (((D.theta hEn x : D.psi.range) : GL4) : M4)

omit [Finite X] in
theorem thetaMat_mulVec (hEn : D.E.Normal) (x : X) (w : D.E) :
    D.thetaMat hEn x *ᵥ Multiplicative.toAdd (D.eE w) =
      Multiplicative.toAdd (D.eE ⟨x * w * x⁻¹, (mem_normalizer_iff.mp
        (D.mem_normalizer_of_normal hEn x) w).mp w.2⟩) :=
  D.psi_mulVec ⟨x, D.mem_normalizer_of_normal hEn x⟩ w

omit [Finite X] in
theorem thetaMat_mul (hEn : D.E.Normal) (x y : X) :
    D.thetaMat hEn (x * y) = D.thetaMat hEn x * D.thetaMat hEn y := by
  rw [thetaMat, map_mul, Subgroup.coe_mul, Units.val_mul]

omit [Finite X] in
theorem thetaMat_pow (hEn : D.E.Normal) (x : X) (n : ℕ) :
    D.thetaMat hEn (x ^ n) = D.thetaMat hEn x ^ n := by
  rw [thetaMat, map_pow, SubgroupClass.coe_pow, Units.val_pow_eq_pow_val]

omit [Finite X] in
theorem thetaMat_one (hEn : D.E.Normal) : D.thetaMat hEn 1 = 1 := by
  rw [thetaMat, map_one, Subgroup.coe_one, Units.val_one]

theorem thetaMat_e0 (hEn : D.E.Normal) (hTn : (D.T : Subgroup X).Normal) (x : X) (u : UT3 F4c) :
    ∃ u' : UT3 F4c, D.thetaMat hEn x * (e0 u.b.a u.b.b).toMat =
      (e0 u'.b.a u'.b.b).toMat * D.thetaMat hEn x := by
  obtain ⟨u', hu'⟩ := D.exists_toX (hTn.conj_mem _ (D.toX_mem u) x)
  refine ⟨u', ?_⟩
  have h1 : D.thetaMat hEn (D.toX u) = (e0 u.b.a u.b.b).toMat := D.psi_toX u
  have h2 : D.thetaMat hEn (D.toX u') = (e0 u'.b.a u'.b.b).toMat := D.psi_toX u'
  rw [← h1, ← h2, ← thetaMat_mul, ← thetaMat_mul, hu', inv_mul_cancel_right]

theorem thetaMat_rows (hEn : D.E.Normal) (hTn : (D.T : Subgroup X).Normal) (x : X) :
    (M4c.ofMat (D.thetaMat hEn x)).r0 ∈ rowsW ∧ (M4c.ofMat (D.thetaMat hEn x)).r1 ∈ rowsW := by
  have hZn : D.Z.Normal := by
    rw [D.Z_eq_inf]
    have := D.F_normal hTn
    exact normal_inf_normal _ _
  have hz : ∀ c : F4c, ∀ i : Fin 4, i.val < 2 →
      (D.thetaMat hEn x *ᵥ ![0, 0, c.a, c.b]) i = 0 := by
    intro c i hi
    have hzE : D.toX ⟨0, 0, c⟩ ∈ D.E := D.toX_mem_E_iff.mpr rfl
    have hv : ![0, 0, c.a, c.b] = Multiplicative.toAdd (D.eE ⟨D.toX ⟨0, 0, c⟩, hzE⟩) := by
      rw [D.eE_toX rfl]
      rfl
    rw [hv, thetaMat_mulVec]
    have hzZ : x * D.toX ⟨0, 0, c⟩ * x⁻¹ ∈ D.Z :=
      hZn.conj_mem _ (D.toX_mem_Z_iff.mpr ⟨rfl, rfl⟩) x
    obtain ⟨w, hw, hwx⟩ := hzZ
    obtain ⟨hwa, hwb⟩ := mem_Zu.mp hw
    have hmem : D.toX w ∈ D.E := D.toX_mem_E_iff.mpr hwb
    have heq : (⟨x * D.toX ⟨0, 0, c⟩ * x⁻¹, (mem_normalizer_iff.mp
        (D.mem_normalizer_of_normal hEn x) _).mp hzE⟩ : D.E) = ⟨D.toX w, hmem⟩ :=
      Subtype.ext hwx.symm
    rw [heq, D.eE_toX hwb]
    change ![w.a.a, w.a.b, w.c.a, w.c.b] i = 0
    rw [hwa]
    fin_cases i
    · rfl
    · rfl
    · exact absurd hi (by decide)
    · exact absurd hi (by decide)
  have h2 : ∀ i : Fin 4, i.val < 2 → D.thetaMat hEn x i 2 = 0 := by
    intro i hi
    have h := hz ⟨1, 0⟩ i hi
    rw [show ![(0 : ZMod 2), 0, (⟨1, 0⟩ : F4c).a, (⟨1, 0⟩ : F4c).b] = Pi.single 2 1 by
      funext j; fin_cases j <;> rfl, Matrix.mulVec_single_one] at h
    exact h
  have h3 : ∀ i : Fin 4, i.val < 2 → D.thetaMat hEn x i 3 = 0 := by
    intro i hi
    have h := hz ⟨0, 1⟩ i hi
    rw [show ![(0 : ZMod 2), 0, (⟨0, 1⟩ : F4c).a, (⟨0, 1⟩ : F4c).b] = Pi.single 3 1 by
      funext j; fin_cases j <;> rfl, Matrix.mulVec_single_one] at h
    exact h
  have hrow : ∀ a b : ZMod 2, (⟨a, b, 0, 0⟩ : V4c) ∈ rowsW := by decide
  constructor
  · change (⟨_, _, D.thetaMat hEn x 0 2, D.thetaMat hEn x 0 3⟩ : V4c) ∈ rowsW
    rw [h2 0 (by decide), h3 0 (by decide)]
    exact hrow _ _
  · change (⟨_, _, D.thetaMat hEn x 1 2, D.thetaMat hEn x 1 3⟩ : V4c) ∈ rowsW
    rw [h2 1 (by decide), h3 1 (by decide)]
    exact hrow _ _

theorem not_order_five_seven (hO : pPrimeCore 2 X = ⊥)
    (hEn : D.E.Normal) (hTn : (D.T : Subgroup X).Normal) {x : X} {p : ℕ}
    (hp : p = 5 ∨ p = 7) (hx : orderOf x = p) : False := by
  set M := M4c.ofMat (D.thetaMat hEn x) with hM
  have hMt : M.toMat = D.thetaMat hEn x := toMat_ofMat _
  have hnorm : SetEq (e0c.map M.mul) (e0c.map fun e => e.mul M) := by
    constructor
    · intro y hy
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hy
      obtain ⟨p, q, rfl⟩ := exists_e0 e he
      obtain ⟨u', hu'⟩ := D.thetaMat_e0 hEn hTn x ⟨0, ⟨p, q⟩, 0⟩
      refine List.mem_map.mpr ⟨e0 u'.b.a u'.b.b, e0_mem _ _, M4c.toMat_injective ?_⟩
      rw [M4c.toMat_mul, M4c.toMat_mul, hMt]
      exact hu'.symm
    · intro y hy
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hy
      obtain ⟨p, q, rfl⟩ := exists_e0 e he
      obtain ⟨u', hu'⟩ := D.thetaMat_e0 hEn hTn x⁻¹ ⟨0, ⟨p, q⟩, 0⟩
      refine List.mem_map.mpr ⟨e0 u'.b.a u'.b.b, e0_mem _ _, M4c.toMat_injective ?_⟩
      rw [M4c.toMat_mul, M4c.toMat_mul, hMt]
      have hinv : D.thetaMat hEn x * D.thetaMat hEn x⁻¹ = 1 := by
        rw [← thetaMat_mul, mul_inv_cancel, thetaMat, map_one, Subgroup.coe_one, Units.val_one]
      have hinv' : D.thetaMat hEn x⁻¹ * D.thetaMat hEn x = 1 := by
        rw [← thetaMat_mul, inv_mul_cancel, thetaMat, map_one, Subgroup.coe_one, Units.val_one]
      calc D.thetaMat hEn x * (e0 u'.b.a u'.b.b).toMat =
          D.thetaMat hEn x * ((e0 u'.b.a u'.b.b).toMat * D.thetaMat hEn x⁻¹) *
            D.thetaMat hEn x := by
            simp only [Matrix.mul_assoc, hinv', Matrix.mul_one]
        _ = D.thetaMat hEn x * (D.thetaMat hEn x⁻¹ * (e0 p q).toMat) * D.thetaMat hEn x := by
            rw [← hu']
        _ = (e0 p q).toMat * D.thetaMat hEn x := by
            rw [← Matrix.mul_assoc, hinv, Matrix.one_mul]
  obtain ⟨hr0, hr1⟩ := D.thetaMat_rows hEn hTn x
  have hcert := noFiveSeven_of (c := M.r2) (d := M.r3) hr0 hr1 hnorm
  have hpow : M.pow p = M4c.one := by
    apply M4c.toMat_injective
    rw [toMat_pow, hMt, M4c.toMat_one, ← thetaMat_pow, ← hx, pow_orderOf_eq_one, thetaMat_one]
  have hM1 : M = M4c.one := by
    rcases hp with rfl | rfl
    · exact hcert.1 hpow
    · exact hcert.2 hpow
  have hθ : D.theta hEn x = 1 := by
    apply Subtype.ext
    apply Units.ext
    change D.thetaMat hEn x = 1
    rw [← hMt, hM1, M4c.toMat_one]
  have hxE : x ∈ D.E := by
    rw [← D.ker_theta hO hEn]
    exact hθ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp D.T.isPGroup' ⟨x, D.E_le_T hxE⟩
  rw [Subgroup.orderOf_mk, hx] at hk
  rcases k with _ | k
  · rcases hp with rfl | rfl <;> norm_num at hk
  · have h2 : 2 ∣ 2 ^ (k + 1) := dvd_pow_self 2 (Nat.succ_ne_zero k)
    rw [← hk] at h2
    rcases hp with rfl | rfl <;> norm_num at h2

theorem index_dvd_nine (hO : pPrimeCore 2 X = ⊥)
    (hEn : D.E.Normal) (hTn : (D.T : Subgroup X).Normal) : (D.T : Subgroup X).index ∣ 9 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : Nat.card X = 16 * Nat.card D.psi.range := by
    rw [← card_mul_index D.E, card_E, index_eq_card, Nat.card_congr (D.quotEquiv hO hEn).toEquiv]
  have h2 : Nat.card D.psi.range ∣ 20160 := card_GL4 ▸ card_subgroup_dvd_card _
  have h3 : Nat.card X = 64 * (D.T : Subgroup X).index := by
    rw [← card_mul_index (D.T : Subgroup X), card_T]
  have h4 : (D.T : Subgroup X).index ∣ 5040 := by
    have h5 : 64 * (D.T : Subgroup X).index ∣ 64 * 5040 := by
      rw [← h3, h1, show (64 * 5040 : ℕ) = 16 * 20160 by norm_num]
      exact Nat.mul_dvd_mul_left 16 h2
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h5
  have hodd : ¬ 2 ∣ (D.T : Subgroup X).index := D.T.not_dvd_index
  have hp : ∀ p : ℕ, (p = 5 ∨ p = 7) → ¬ p ∣ (D.T : Subgroup X).index := by
    intro p hp hdvd
    have hpr : p.Prime := by rcases hp with rfl | rfl <;> decide
    have : Fact p.Prime := ⟨hpr⟩
    have hX : p ∣ Nat.card X := by
      rw [h3]
      exact Dvd.dvd.mul_left hdvd 64
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hX
    exact D.not_order_five_seven hO hEn hTn hp hx
  have h16 : Nat.Coprime (D.T : Subgroup X).index 16 :=
    Nat.Coprime.pow_right 4 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd).symm
  have h315 : (D.T : Subgroup X).index ∣ 315 :=
    h16.dvd_of_dvd_mul_left (by rw [show (315 * 16 : ℕ) = 5040 by norm_num]; exact h4)
  have h5 : Nat.Coprime (D.T : Subgroup X).index 5 :=
    ((Nat.Prime.coprime_iff_not_dvd (by decide)).mpr (hp 5 (Or.inl rfl))).symm
  have h7 : Nat.Coprime (D.T : Subgroup X).index 7 :=
    ((Nat.Prime.coprime_iff_not_dvd (by decide)).mpr (hp 7 (Or.inr rfl))).symm
  have h63 : (D.T : Subgroup X).index ∣ 63 :=
    h5.dvd_of_dvd_mul_right (by rw [show (63 * 5 : ℕ) = 315 by norm_num]; exact h315)
  exact h7.dvd_of_dvd_mul_right (by rw [show (9 * 7 : ℕ) = 63 by norm_num]; exact h63)

omit [Finite X] in
theorem E_mul_self {x : X} (hx : x ∈ D.E) : x * x = 1 := by
  obtain ⟨u, hu, rfl⟩ := hx
  rw [← map_mul, (ut_mul_self_eq_one_iff u).mpr (Or.inr (mem_Eu.mp hu)), map_one]

theorem centralizer_T_le (hO : pPrimeCore 2 X = ⊥) (hEn : D.E.Normal) :
    centralizer ((D.T : Subgroup X) : Set X) ≤ D.E := by
  rw [← D.centralizer_E_eq hO hEn]
  exact centralizer_le D.E_le_T

theorem thmC_of_normal
    (hO : pPrimeCore 2 X = ⊥) (hEn : D.E.Normal) :
    letI : (pCore 2 X).Normal := pCore_normal
    centralizer (pCore 2 X : Set X) ≤ pCore 2 X ∧
      ((pCore 2 X = D.T ∧ (D.T : Subgroup X).index ∣ 9 ∧
          ∀ B : Subgroup X, B ≤ D.T → (∀ b ∈ B, b * b = 1) →
            (∀ b ∈ B, ∀ c ∈ B, b * c = c * b) → Nat.card B = 16 → B.Normal) ∨
        ((pCore 2 X : Subgroup X) ≤ D.T ∧ Nat.card (pCore 2 X) = 16 ∧
          (∀ b ∈ pCore 2 X, b * b = 1) ∧ (∀ b ∈ pCore 2 X, ∀ c ∈ pCore 2 X, b * c = c * b) ∧
          (Nonempty (X ⧸ pCore 2 X ≃* alternatingGroup (Fin 5)) ∨
            Nonempty (X ⧸ pCore 2 X ≃* Multiplicative (ZMod 3) × alternatingGroup (Fin 5))) ∧
          ∀ u ∈ pCore 2 X, ∀ v ∈ pCore 2 X, u ≠ 1 → v ≠ 1 → ∃ g : X, g⁻¹ * u * g = v)) := by
  let _ : (pCore 2 X).Normal := pCore_normal
  by_cases hTn : (D.T : Subgroup X).Normal
  ·
    have hpT : pCore 2 X = D.T := le_antisymm (D.le_T_of_normal pCore_normal pCore_isPGroup)
      (le_sSup ⟨hTn, D.T.isPGroup'⟩)
    refine ⟨?_, Or.inl ⟨hpT, D.index_dvd_nine hO hEn hTn, fun B hBT hB2 hBc h16 => ?_⟩⟩
    · rw [hpT]
      exact (D.centralizer_T_le hO hEn).trans D.E_le_T
    · rcases D.eq_E_or_F hBT hB2 hBc h16 with rfl | rfl
      · exact hEn
      · exact D.F_normal hTn
  ·
    obtain ⟨hpE, hiso, htr⟩ := D.caseB hO hEn hTn
    refine ⟨?_, Or.inr ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · rw [hpE, D.centralizer_E_eq hO hEn]
    · rw [hpE]
      exact D.E_le_T
    · rw [hpE, card_E]
    · rw [hpE]
      exact fun b hb => D.E_mul_self hb
    · rw [hpE]
      exact fun b hb c hc => D.E_comm hb hc
    · have e : X ⧸ pCore 2 X ≃* X ⧸ D.E := QuotientGroup.quotientMulEquivOfEq hpE
      rcases hiso with h | h
      · obtain ⟨e'⟩ := h
        exact Or.inl ⟨e.trans e'⟩
      · obtain ⟨e'⟩ := h
        exact Or.inr ⟨e.trans e'⟩
    · rw [hpE]
      exact htr

end ThmC.UTSylow

theorem gorensteinHaradaThmCInput_of_E16
    (hE16 : StronglyClosedE16Input) :
    GorensteinHaradaThmCInput := by
  intro X _ _ hO T hT hX
  obtain ⟨φ⟩ := hT
  let D : UTSylow X := ⟨T, (φ.trans sylLCongr).symm⟩
  have key : ∀ D' : UTSylow X, D'.T = T →
      (∀ a ∈ D'.E, ∀ g : X, g⁻¹ * a * g ∈ (D'.T : Subgroup X) → g⁻¹ * a * g ∈ D'.E) →
      D'.E.Normal := by
    intro D' hD' hcl
    subst hD'
    exact hE16 X hO D'.T ⟨φ⟩ D'.E D'.E_le_T D'.card_E (fun b hb => D'.E_mul_self hb)
      (fun b hb c hc => D'.E_comm hb hc) hcl
  rcases D.stronglyClosed_E_or_F hX with hcl | hcl
  · exact D.thmC_of_normal hO (key D rfl hcl)
  · have hcl' : ∀ a ∈ D.swap.E, ∀ g : X, g⁻¹ * a * g ∈ (D.swap.T : Subgroup X) →
        g⁻¹ * a * g ∈ D.swap.E := by
      rw [UTSylow.swap_E]
      exact hcl
    exact D.swap.thmC_of_normal hO (key D.swap rfl hcl')

end CFSG.ComponentClassification.GHarris
