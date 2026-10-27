module

public import CFSG.LieType.Steinberg.Adjoint.BaseChange
public import CFSG.LieType.Steinberg.Adjoint.Pairs
public import Mathlib.Algebra.MvPolynomial.Eval
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117

public noncomputable section

namespace CFSG.LieType.Steinberg.Adjoint

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley IsNilpotent

variable {τ : Tag}

theorem nsmul_add_nsmul_ne_zero {α β : Fin τ.rank → ℤ} (h : LinIndepPair α β) {i j : ℕ}
    (hij : i ≠ 0 ∨ j ≠ 0) : i • α + j • β ≠ 0 := by
  intro h0
  have := h i j (by rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]; exact h0)
  omega

theorem ne_neg_of_linIndep {α β : Fin τ.rank → ℤ} (h : LinIndepPair α β) {i j k l : ℕ}
    (hij : i + k ≠ 0 ∨ j + l ≠ 0) : i • α + j • β ≠ -(k • α + l • β) := by
  intro h0
  apply nsmul_add_nsmul_ne_zero h hij
  rw [add_nsmul, add_nsmul, eq_neg_iff_add_eq_zero] at *
  rw [← h0]
  abel

theorem ne_neg_of_linIndep' {α β u v : Fin τ.rank → ℤ} (h : LinIndepPair α β) {i j k l : ℕ}
    (hij : i + k ≠ 0 ∨ j + l ≠ 0) (hu : u = i • α + j • β) (hv : v = k • α + l • β) :
    u ≠ -v := by
  rw [hu, hv]
  exact ne_neg_of_linIndep h hij

namespace RootOperatorFamily'

variable (F : RootOperatorFamily τ) {D : AdjData τ} (hD : D.Valid)

open _root_.Classical in
@[expose] def eltOr (R : Type) [CommRing R] (γ : Fin τ.rank → ℤ) (c : R) :
    Module.End R (RootModule τ R) :=
  if h : IsRoot τ γ then F.elt R ⟨γ, h⟩ c else 1

theorem eltOr_of_isRoot (R : Type) [CommRing R] {γ : Fin τ.rank → ℤ} (h : IsRoot τ γ) (c : R) :
    eltOr F R γ c = F.elt R ⟨γ, h⟩ c := by
  classical
  exact dite_eq_left h

theorem eltOr_of_not_isRoot (R : Type) [CommRing R] {γ : Fin τ.rank → ℤ} (h : ¬IsRoot τ γ)
    (c : R) : eltOr F R γ c = 1 := by
  classical
  exact dite_eq_right h

@[expose] def coeff11 (α β : Root τ) : ℤ := bracketCoeff F hD α β

open _root_.Classical in
@[expose] def coeff12 (α β : Root τ) : ℤ :=
  if h : IsRoot τ (α.1 + β.1) then bracketCoeff F hD α β * bracketCoeff F hD β ⟨_, h⟩ / 2
  else 0

open _root_.Classical in
@[expose] def coeff21 (α β : Root τ) : ℤ :=
  if h : IsRoot τ (α.1 + β.1) then bracketCoeff F hD α β * bracketCoeff F hD α ⟨_, h⟩ / 2
  else 0

omit hD in
theorem isNilpotent_smul_D {R : Type} [CommRing R] (α : Root τ) (x : R) :
    IsNilpotent (x • F.D R α 1) :=
  ⟨4, by rw [smul_pow, D_one_pow F α 4, F.D_eq_zero R α 4 le_rfl, smul_zero, smul_zero]⟩

include hD

theorem bracket_smul {R : Type} [CommRing R] {β γ : Root τ} (hγ : γ.1 ≠ -β.1)
    (h : IsRoot τ (β.1 + γ.1)) (x y : R) :
    (x • F.D R β 1) * (y • F.D R γ 1) - (y • F.D R γ 1) * (x • F.D R β 1) =
      (x * y * bracketCoeff F hD β γ) • F.D R ⟨β.1 + γ.1, h⟩ 1 := by
  rw [smul_mul_smul_comm, smul_mul_smul_comm, mul_comm y x, ← smul_sub, bracket_eq F hD hγ h,
    smul_smul]

theorem commute_smul {R : Type} [CommRing R] {β γ : Root τ} (hγ : γ.1 ≠ -β.1)
    (h : ¬IsRoot τ (β.1 + γ.1)) (x y : R) : Commute (x • F.D R β 1) (y • F.D R γ 1) := by
  have hc : Commute (F.D R β 1) (F.D R γ 1) := sub_eq_zero.1 (bracket_eq_zero F hD hγ h R)
  exact (hc.smul_left x).smul_right y

omit hD in
theorem D_congr {R : Type} [CommRing R] {γ δ : Root τ} (h : γ.1 = δ.1) (k : ℕ) :
    F.D R γ k = F.D R δ k := by
  rw [Subtype.ext h]

omit F hD in
theorem two_inv_smul_two_mul_smul {R : Type} [CommRing R] [Algebra ℚ R] (y : R)
    (X : Module.End R (RootModule τ R)) : (2 : ℚ)⁻¹ • ((2 * y) • X) = y • X := by
  rw [← algebraMap_smul R ((2 : ℚ)⁻¹) ((2 * y) • X), smul_smul, ← mul_assoc,
    ← map_ofNat (algebraMap ℚ R) 2, ← map_mul, inv_mul_cancel₀ two_ne_zero, map_one, one_mul]

theorem comm_rat_of_not_isRoot_add {R : Type} [CommRing R] [Algebra ℚ R] {α β : Root τ}
    (hne' : α.1 ≠ -β.1) (h : ¬IsRoot τ (α.1 + β.1)) (c d : R) :
    F.elt R α c * F.elt R β d * F.elt R α (-c) * F.elt R β (-d) = 1 := by
  have hβα : β.1 ≠ -α.1 := fun h' => hne' (by rw [h', neg_neg])
  have hc := commute_smul F hD hβα h c d
  rw [elt_eq_exp F, elt_eq_exp F, elt_eq_exp F, elt_eq_exp F, neg_smul, neg_smul,
    commutator_exp (z := 0) (w := 0) (isNilpotent_smul_D F α c) (isNilpotent_smul_D F β d)
      IsNilpotent.zero IsNilpotent.zero (by rw [hc.eq, sub_self]) (by simp)
      (Commute.zero_right _) (Commute.zero_right _) (Commute.zero_right _) (Commute.zero_right _),
    smul_zero, exp_zero, mul_one]

theorem comm_rat_of_not_isRoot_two_add (hτ : NoG2 τ) {R : Type} [CommRing R] [Algebra ℚ R]
    {α β : Root τ} (hne : α.1 ≠ β.1) (hne' : α.1 ≠ -β.1) (h : IsRoot τ (α.1 + β.1))
    (h21 : ¬IsRoot τ (2 • α.1 + β.1)) (c d : R) :
    F.elt R α c * F.elt R β d * F.elt R α (-c) * F.elt R β (-d) =
      F.elt R ⟨_, h⟩ ((coeff11 F hD α β : R) * c * d) *
        eltOr F R (α.1 + 2 • β.1) ((coeff12 F hD α β : R) * c * d ^ 2) := by
  have hli := linIndepPair_of_ne α.2 β.2 hne hne'
  have hβα : β.1 ≠ -α.1 := fun h' => hne' (by rw [h', neg_neg])
  have hz' := bracket_smul F hD hβα h c d
  have hγα : α.1 + β.1 ≠ -α.1 := ne_neg_of_linIndep' hli (i := 1) (j := 1) (k := 1) (l := 0)
    (by omega) (by simp) (by simp)
  have hαγ : ¬IsRoot τ (α.1 + (α.1 + β.1)) := by
    rwa [show α.1 + (α.1 + β.1) = 2 • α.1 + β.1 by rw [two_nsmul]; abel]
  have haz := commute_smul F hD (β := α) (γ := ⟨_, h⟩) hγα hαγ c
    (c * d * bracketCoeff F hD α β)
  rw [elt_eq_exp F, elt_eq_exp F, elt_eq_exp F, elt_eq_exp F, neg_smul, neg_smul,
    elt_eq_exp F]
  have hγβ : α.1 + β.1 ≠ -β.1 := ne_neg_of_linIndep' hli (i := 1) (j := 1) (k := 0) (l := 1)
    (by omega) (by simp) (by simp)
  have hβγeq : β.1 + (α.1 + β.1) = α.1 + 2 • β.1 := by rw [two_nsmul]; abel
  by_cases h12 : IsRoot τ (α.1 + 2 • β.1)
  · have hβγ : IsRoot τ (β.1 + (α.1 + β.1)) := by rwa [hβγeq]
    have hw' := bracket_smul F hD (β := β) (γ := ⟨_, h⟩) hγβ hβγ d
      (c * d * bracketCoeff F hD α β)
    rw [D_congr F (show (⟨_, hβγ⟩ : Root τ).1 = (⟨_, h12⟩ : Root τ).1 from hβγeq)] at hw'
    have hγ'α : α.1 + 2 • β.1 ≠ -α.1 := ne_neg_of_linIndep' hli (i := 1) (j := 2) (k := 1)
      (l := 0) (by omega) (by simp) (by simp)
    have hαγ' : ¬IsRoot τ (α.1 + (α.1 + 2 • β.1)) := by
      have := not_isRoot_nsmul_add_nsmul hτ α.2 β.2 hne hne' (i := 2) (j := 2) (by omega)
        (by omega) (by omega)
      rwa [show 2 • α.1 + 2 • β.1 = α.1 + (α.1 + 2 • β.1) by rw [two_nsmul α.1]; abel] at this
    have hγ'γ : α.1 + 2 • β.1 ≠ -(α.1 + β.1) := ne_neg_of_linIndep' hli (i := 1) (j := 2)
      (k := 1) (l := 1) (by omega) (by simp) (by simp)
    have hγγ' : ¬IsRoot τ (α.1 + β.1 + (α.1 + 2 • β.1)) := by
      have := not_isRoot_nsmul_add_nsmul hτ α.2 β.2 hne hne' (i := 2) (j := 3) (by omega)
        (by omega) (by omega)
      rwa [show 2 • α.1 + 3 • β.1 = α.1 + β.1 + (α.1 + 2 • β.1) by
        rw [two_nsmul α.1, show (3 : ℕ) = 2 + 1 from rfl, add_nsmul, one_nsmul]; abel] at this
    have hγ'β : α.1 + 2 • β.1 ≠ -β.1 := ne_neg_of_linIndep' hli (i := 1) (j := 2) (k := 0)
      (l := 1) (by omega) (by simp) (by simp)
    have hβγ' : ¬IsRoot τ (β.1 + (α.1 + 2 • β.1)) := by
      have := not_isRoot_nsmul_add_nsmul hτ α.2 β.2 hne hne' (i := 1) (j := 3) (by omega)
        (by omega) (by omega)
      rwa [show 1 • α.1 + 3 • β.1 = β.1 + (α.1 + 2 • β.1) by
        rw [show (3 : ℕ) = 2 + 1 from rfl, add_nsmul, one_nsmul, one_nsmul]; abel] at this
    have hN' : bracketCoeff F hD β ⟨_, h⟩ = 2 ∨ bracketCoeff F hD β ⟨_, h⟩ = -2 := by
      have := bracketCoeff_natAbs F hD (β := β) (γ := ⟨_, h⟩) hγβ hβγ
      rw [stringNorm_of_isRoot (by simpa using α.2)] at this
      omega
    rw [commutator_exp (isNilpotent_smul_D F α c) (isNilpotent_smul_D F β d)
        (isNilpotent_smul_D F ⟨_, h⟩ _) (isNilpotent_smul_D F ⟨_, h12⟩ _) hz' hw' haz
        (commute_smul F hD (β := α) (γ := ⟨_, h12⟩) hγ'α hαγ' c _)
        (commute_smul F hD (β := ⟨_, h⟩) (γ := ⟨_, h12⟩) hγ'γ hγγ' _ _)
        (commute_smul F hD (β := β) (γ := ⟨_, h12⟩) hγ'β hβγ' d _),
      eltOr_of_isRoot F R h12, elt_eq_exp F, coeff12, dite_eq_left h, coeff11]
    congr 2
    · ring_nf
    · rcases hN' with hN' | hN' <;> rw [hN']
      · rw [show bracketCoeff F hD α β * 2 / 2 = bracketCoeff F hD α β by omega,
          show d * (c * d * (bracketCoeff F hD α β : R)) * ((2 : ℤ) : R) =
            2 * ((bracketCoeff F hD α β : R) * c * d ^ 2) by push_cast; ring_nf,
          two_inv_smul_two_mul_smul]
      · rw [show bracketCoeff F hD α β * -2 / 2 = -bracketCoeff F hD α β by omega,
          show d * (c * d * (bracketCoeff F hD α β : R)) * ((-2 : ℤ) : R) =
            2 * (((-bracketCoeff F hD α β : ℤ) : R) * c * d ^ 2) by push_cast; ring_nf,
          two_inv_smul_two_mul_smul]
  · have hβγ : ¬IsRoot τ (β.1 + (α.1 + β.1)) := by rwa [hβγeq]
    have hbz := commute_smul F hD (β := β) (γ := ⟨_, h⟩) hγβ hβγ d
      (c * d * bracketCoeff F hD α β)
    rw [commutator_exp (w := 0) (isNilpotent_smul_D F α c) (isNilpotent_smul_D F β d)
        (isNilpotent_smul_D F ⟨_, h⟩ _) IsNilpotent.zero hz' (by rw [hbz.eq, sub_self]) haz
        (Commute.zero_right _) (Commute.zero_right _) (Commute.zero_right _),
      eltOr_of_not_isRoot F R h12, smul_zero, exp_zero, mul_one, mul_one, coeff11]
    congr 2
    ring

theorem comm_rat_of_isRoot_two_add (hτ : NoG2 τ) {R : Type} [CommRing R] [Algebra ℚ R]
    {α β : Root τ} (hne : α.1 ≠ β.1) (hne' : α.1 ≠ -β.1) (h : IsRoot τ (α.1 + β.1))
    (h21 : IsRoot τ (2 • α.1 + β.1)) (c d : R) :
    F.elt R α c * F.elt R β d * F.elt R α (-c) * F.elt R β (-d) =
      F.elt R ⟨_, h⟩ ((coeff11 F hD α β : R) * c * d) *
        F.elt R ⟨_, h21⟩ ((coeff21 F hD α β : R) * c ^ 2 * d) := by
  have hli := linIndepPair_of_ne α.2 β.2 hne hne'
  have h12 : ¬IsRoot τ (α.1 + 2 • β.1) := fun h12 =>
    not_isRoot_add_two_and_two_add hτ α.2 β.2 hne hne' ⟨h12, h21⟩
  have hβα : β.1 ≠ -α.1 := fun h' => hne' (by rw [h', neg_neg])
  have hz' := bracket_smul F hD hβα h c d
  have hγα : α.1 + β.1 ≠ -α.1 := ne_neg_of_linIndep' hli (i := 1) (j := 1) (k := 1) (l := 0)
    (by omega) (by simp) (by simp)
  have hαγeq : α.1 + (α.1 + β.1) = 2 • α.1 + β.1 := by rw [two_nsmul]; abel
  have hαγ : IsRoot τ (α.1 + (α.1 + β.1)) := by rwa [hαγeq]
  have hu' := bracket_smul F hD (β := α) (γ := ⟨_, h⟩) hγα hαγ c
    (c * d * bracketCoeff F hD α β)
  rw [D_congr F (show (⟨_, hαγ⟩ : Root τ).1 = (⟨_, h21⟩ : Root τ).1 from hαγeq)] at hu'
  have hγβ : α.1 + β.1 ≠ -β.1 := ne_neg_of_linIndep' hli (i := 1) (j := 1) (k := 0) (l := 1)
    (by omega) (by simp) (by simp)
  have hβγ : ¬IsRoot τ (β.1 + (α.1 + β.1)) := by
    rwa [show β.1 + (α.1 + β.1) = α.1 + 2 • β.1 by rw [two_nsmul]; abel]
  have hγ''β : 2 • α.1 + β.1 ≠ -β.1 := ne_neg_of_linIndep' hli (i := 2) (j := 1) (k := 0)
    (l := 1) (by omega) (by simp) (by simp)
  have hβγ'' : ¬IsRoot τ (β.1 + (2 • α.1 + β.1)) := by
    have := not_isRoot_nsmul_add_nsmul hτ α.2 β.2 hne hne' (i := 2) (j := 2) (by omega)
      (by omega) (by omega)
    rwa [show 2 • α.1 + 2 • β.1 = β.1 + (2 • α.1 + β.1) by rw [two_nsmul β.1]; abel] at this
  have hγ''γ : 2 • α.1 + β.1 ≠ -(α.1 + β.1) := ne_neg_of_linIndep' hli (i := 2) (j := 1)
    (k := 1) (l := 1) (by omega) (by simp) (by simp)
  have hγγ'' : ¬IsRoot τ (α.1 + β.1 + (2 • α.1 + β.1)) := by
    have := not_isRoot_nsmul_add_nsmul hτ α.2 β.2 hne hne' (i := 3) (j := 2) (by omega)
      (by omega) (by omega)
    rwa [show 3 • α.1 + 2 • β.1 = α.1 + β.1 + (2 • α.1 + β.1) by
      rw [two_nsmul β.1, show (3 : ℕ) = 2 + 1 from rfl, add_nsmul, one_nsmul]; abel] at this
  have hγ''α : 2 • α.1 + β.1 ≠ -α.1 := ne_neg_of_linIndep' hli (i := 2) (j := 1) (k := 1)
    (l := 0) (by omega) (by simp) (by simp)
  have hαγ'' : ¬IsRoot τ (α.1 + (2 • α.1 + β.1)) := by
    have := not_isRoot_nsmul_add_nsmul hτ α.2 β.2 hne hne' (i := 3) (j := 1) (by omega)
      (by omega) (by omega)
    rwa [show 3 • α.1 + 1 • β.1 = α.1 + (2 • α.1 + β.1) by
      rw [show (3 : ℕ) = 2 + 1 from rfl, add_nsmul, one_nsmul, one_nsmul]; abel] at this
  have hN'' : bracketCoeff F hD α ⟨_, h⟩ = 2 ∨ bracketCoeff F hD α ⟨_, h⟩ = -2 := by
    have := bracketCoeff_natAbs F hD (β := α) (γ := ⟨_, h⟩) hγα hαγ
    rw [stringNorm_of_isRoot (by simpa using β.2)] at this
    omega
  rw [elt_eq_exp F, elt_eq_exp F, elt_eq_exp F, elt_eq_exp F, neg_smul, neg_smul,
    commutator_exp' (isNilpotent_smul_D F α c) (isNilpotent_smul_D F β d)
      (isNilpotent_smul_D F ⟨_, h⟩ _) (isNilpotent_smul_D F ⟨_, h21⟩ _) hz' hu'
      (commute_smul F hD (β := β) (γ := ⟨_, h⟩) hγβ hβγ d _)
      (commute_smul F hD (β := β) (γ := ⟨_, h21⟩) hγ''β hβγ'' d _)
      (commute_smul F hD (β := ⟨_, h⟩) (γ := ⟨_, h21⟩) hγ''γ hγγ'' _ _)
      (commute_smul F hD (β := α) (γ := ⟨_, h21⟩) hγ''α hαγ'' c _),
    elt_eq_exp F, elt_eq_exp F, coeff21, dite_eq_left h, coeff11]
  congr 2
  · ring_nf
  · rcases hN'' with hN'' | hN'' <;> rw [hN'']
    · rw [show bracketCoeff F hD α β * 2 / 2 = bracketCoeff F hD α β by omega,
        show c * (c * d * (bracketCoeff F hD α β : R)) * ((2 : ℤ) : R) =
          2 * ((bracketCoeff F hD α β : R) * c ^ 2 * d) by push_cast; ring_nf,
        two_inv_smul_two_mul_smul]
    · rw [show bracketCoeff F hD α β * -2 / 2 = -bracketCoeff F hD α β by omega,
        show c * (c * d * (bracketCoeff F hD α β : R)) * ((-2 : ℤ) : R) =
          2 * (((-bracketCoeff F hD α β : ℤ) : R) * c ^ 2 * d) by push_cast; ring_nf,
        two_inv_smul_two_mul_smul]

theorem comm_rat (hτ : NoG2 τ) {R : Type} [CommRing R] [Algebra ℚ R] {α β : Root τ}
    (hne : α.1 ≠ β.1) (hne' : α.1 ≠ -β.1) (c d : R) :
    F.elt R α c * F.elt R β d * F.elt R α (-c) * F.elt R β (-d) =
      eltOr F R (α.1 + β.1) ((coeff11 F hD α β : R) * c * d) *
        eltOr F R (α.1 + 2 • β.1) ((coeff12 F hD α β : R) * c * d ^ 2) *
          eltOr F R (2 • α.1 + β.1) ((coeff21 F hD α β : R) * c ^ 2 * d) := by
  by_cases h : IsRoot τ (α.1 + β.1)
  · by_cases h21 : IsRoot τ (2 • α.1 + β.1)
    · have h12 : ¬IsRoot τ (α.1 + 2 • β.1) := fun h12 =>
        not_isRoot_add_two_and_two_add hτ α.2 β.2 hne hne' ⟨h12, h21⟩
      rw [comm_rat_of_isRoot_two_add F hD hτ hne hne' h h21, eltOr_of_isRoot F R h,
        eltOr_of_not_isRoot F R h12, eltOr_of_isRoot F R h21, mul_one]
    · rw [comm_rat_of_not_isRoot_two_add F hD hτ hne hne' h h21, eltOr_of_isRoot F R h,
        eltOr_of_not_isRoot F R h21, mul_one]
  · have h12 : ¬IsRoot τ (α.1 + 2 • β.1) := fun h12 =>
      h (isRoot_add_of_isRoot_add_two_smul β.2 α.2 hne hne' h12)
    have h21 : ¬IsRoot τ (2 • α.1 + β.1) := fun h21 => h (by
      rw [add_comm]
      exact isRoot_add_of_isRoot_add_two_smul α.2 β.2 (Ne.symm hne)
        (fun h' => hne' (by rw [h', neg_neg])) (by rwa [add_comm]))
    rw [comm_rat_of_not_isRoot_add F hD hne' h, eltOr_of_not_isRoot F R h,
      eltOr_of_not_isRoot F R h12, eltOr_of_not_isRoot F R h21, mul_one, mul_one]

omit hD in
theorem baseChange_eltOr {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
    (γ : Fin τ.rank → ℤ) (x : R) : BaseChange f (eltOr F R γ x) (eltOr F S γ (f x)) := by
  by_cases h : IsRoot τ γ
  · rw [eltOr_of_isRoot F R h, eltOr_of_isRoot F S h]
    exact BaseChange.elt F _ x
  · rw [eltOr_of_not_isRoot F R h, eltOr_of_not_isRoot F S h]
    exact BaseChange.one

omit hD in
theorem baseChange_comm_lhs {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
    (α β : Root τ) (c d : R) :
    BaseChange f (F.elt R α c * F.elt R β d * F.elt R α (-c) * F.elt R β (-d))
      (F.elt S α (f c) * F.elt S β (f d) * F.elt S α (-f c) * F.elt S β (-f d)) := by
  have h3 := BaseChange.elt F (f := f) α (-c)
  have h4 := BaseChange.elt F (f := f) β (-d)
  rw [map_neg] at h3 h4
  exact (((BaseChange.elt F α c).mul (BaseChange.elt F β d)).mul h3).mul h4

theorem baseChange_comm_rhs {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
    (α β : Root τ) (c d : R) :
    BaseChange f (eltOr F R (α.1 + β.1) ((coeff11 F hD α β : R) * c * d) *
        eltOr F R (α.1 + 2 • β.1) ((coeff12 F hD α β : R) * c * d ^ 2) *
          eltOr F R (2 • α.1 + β.1) ((coeff21 F hD α β : R) * c ^ 2 * d))
      (eltOr F S (α.1 + β.1) ((coeff11 F hD α β : S) * f c * f d) *
        eltOr F S (α.1 + 2 • β.1) ((coeff12 F hD α β : S) * f c * f d ^ 2) *
          eltOr F S (2 • α.1 + β.1) ((coeff21 F hD α β : S) * f c ^ 2 * f d)) := by
  have h1 := baseChange_eltOr F f (α.1 + β.1) ((coeff11 F hD α β : R) * c * d)
  have h2 := baseChange_eltOr F f (α.1 + 2 • β.1) ((coeff12 F hD α β : R) * c * d ^ 2)
  have h3 := baseChange_eltOr F f (2 • α.1 + β.1) ((coeff21 F hD α β : R) * c ^ 2 * d)
  simp only [map_mul, map_pow, map_intCast] at h1 h2 h3
  exact (h1.mul h2).mul h3

open MvPolynomial in
theorem comm_formula (hτ : NoG2 τ) {S : Type} [CommRing S] {α β : Root τ} (hne : α.1 ≠ β.1)
    (hne' : α.1 ≠ -β.1) (c d : S) :
    F.elt S α c * F.elt S β d * F.elt S α (-c) * F.elt S β (-d) =
      eltOr F S (α.1 + β.1) ((coeff11 F hD α β : S) * c * d) *
        eltOr F S (α.1 + 2 • β.1) ((coeff12 F hD α β : S) * c * d ^ 2) *
          eltOr F S (2 • α.1 + β.1) ((coeff21 F hD α β : S) * c ^ 2 * d) := by
  set f₀ : MvPolynomial (Fin 2) ℤ →+* MvPolynomial (Fin 2) ℚ := map (Int.castRingHom ℚ)
  have hf₀ : Function.Injective f₀ := map_injective _ Int.cast_injective
  have hX : ∀ i, f₀ (X i) = X i := fun i => map_X _ i
  have hl₀ := baseChange_comm_lhs F f₀ α β (X 0) (X 1)
  have hr₀ := baseChange_comm_rhs F hD f₀ α β (X 0) (X 1)
  rw [hX, hX] at hl₀ hr₀
  rw [← comm_rat (R := MvPolynomial (Fin 2) ℚ) F hD hτ hne hne'] at hr₀
  have huniv := BaseChange.eq_of_injective hf₀ hl₀ hr₀
  set g : MvPolynomial (Fin 2) ℤ →+* S := eval₂Hom (Int.castRingHom S) ![c, d]
  have hg0 : g (X 0) = c := eval₂Hom_X' _ _ _
  have hg1 : g (X 1) = d := eval₂Hom_X' _ _ _
  have hl := baseChange_comm_lhs F g α β (X 0) (X 1)
  have hr := baseChange_comm_rhs F hD g α β (X 0) (X 1)
  rw [hg0, hg1] at hl hr
  rw [huniv] at hl
  exact hl.unique hr

end RootOperatorFamily'

end CFSG.LieType.Steinberg.Adjoint
