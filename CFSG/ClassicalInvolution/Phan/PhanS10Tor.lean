module

public import CFSG.ClassicalInvolution.Phan.PhanS10Inv
public import CFSG.ClassicalInvolution.Phan.PhanS10Facts

public section

namespace CFSG.ClassicalInvolution.PhanB3.S

open CFSG.LieType.Universal.Spin QuadraticMap CFSG.ClassicalInvolution.PhanB3.H
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.PhanB3
  CFSG.ClassicalInvolution.PhanD4 CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.LieType.Steinberg CFSG.ClassicalGroups.Unitary
open CFSG.ClassicalInvolution.Models.SymplecticPairs (longBlock)
open CFSG.Timmesfeld CFSG.Timmesfeld.LevisExtras CFSG.ClassicalInvolution.WeakCT
open CFSG.Assembly.LowTwoRank (StatedSp)
open scoped MatrixGroups

section Basic

variable {F K : Type} [Field F] [Field K] [Algebra F K] (D : KDat F K)

theorem two_ne_zero_of (h2 : (2 : F) ≠ 0) : (2 : K) ≠ 0 := by
  intro h
  apply h2
  apply (algebraMap F K).injective
  rw [map_ofNat, map_zero]
  exact h

theorem eq_of_add_mul_theta {a b a' b' : F} (h2 : (2 : F) ≠ 0)
    (h : algebraMap F K a + algebraMap F K b * D.θ = algebraMap F K a' + algebraMap F K b' * D.θ) :
    a = a' ∧ b = b' := by
  have h2K := two_ne_zero_of (K := K) h2
  have hb : b = b' := by
    by_contra hbb
    have hne : algebraMap F K (b - b') ≠ 0 := by
      rw [map_ne_zero_iff _ (algebraMap F K).injective]
      exact sub_ne_zero.mpr hbb
    have hθ0 : D.θ * algebraMap F K (b - b') = algebraMap F K (a' - a) := by
      rw [map_sub, map_sub]
      linear_combination h
    have hθ : D.θ = algebraMap F K ((a' - a) / (b - b')) := by
      rw [map_div₀]
      exact eq_div_of_mul_eq hne hθ0
    have hfix : D.τ D.θ = D.θ := by
      rw [hθ, D.tau_alg]
    rw [D.tau_theta] at hfix
    have h0 : D.θ = 0 := by
      have : (2 : K) * D.θ = 0 := by linear_combination -hfix
      exact (mul_eq_zero.mp this).resolve_left h2K
    have := D.theta_sq
    rw [h0] at this
    simp at this
  subst hb
  refine ⟨?_, rfl⟩
  have := add_right_cancel h
  exact (algebraMap F K).injective this

theorem vXi_eq : vXi D = emb (mk7 1 0 0 1 0 0 0 : W7 F) + D.θ • emb (mk7 0 0 0 0 0 0 1 : W7 F) := by
  funext s
  rcases s with i | i | u
  · fin_cases i <;> simp [vXi, emb]
  · fin_cases i <;> simp [vXi, emb]
  · simp [vXi, emb]

theorem vE2_eq : vE2 D = emb (mk7 0 1 0 0 (-1) 0 0 : W7 F) +
    (-D.θ) • emb (mk7 0 0 1 0 0 (-1) 0 : W7 F) := by
  funext s
  rcases s with i | i | u
  · fin_cases i <;> simp [vE2, emb]
  · fin_cases i <;> simp [vE2, emb]
  · simp [vE2, emb]

theorem actK_add_smul_emb (g : spinGroup (quadOdd 3 F)) (a b : W7 F) (c : K) :
    actK (K := K) g (emb (K := K) a + c • emb (K := K) b) =
      emb (K := K) (spinAction (quadOdd 3 F) g a) +
        c • emb (K := K) (spinAction (quadOdd 3 F) g b) := by
  rw [map_add, map_smul, actK_emb, actK_emb]

theorem actK_vXi_of_fix (g : spinGroup (quadOdd 3 F))
    (h1 : spinAction (quadOdd 3 F) g (mk7 1 0 0 1 0 0 0) = mk7 1 0 0 1 0 0 0)
    (h2 : spinAction (quadOdd 3 F) g (mk7 0 0 0 0 0 0 1) = mk7 0 0 0 0 0 0 1) :
    actK g (vXi D) = vXi D := by
  rw [vXi_eq D, actK_add_smul_emb, h1, h2]

theorem actK_vE2_of_fix (g : spinGroup (quadOdd 3 F))
    (h1 : spinAction (quadOdd 3 F) g (mk7 0 1 0 0 (-1) 0 0) = mk7 0 1 0 0 (-1) 0 0)
    (h2 : spinAction (quadOdd 3 F) g (mk7 0 0 1 0 0 (-1) 0) = mk7 0 0 1 0 0 (-1) 0) :
    actK g (vE2 D) = vE2 D := by
  rw [vE2_eq D, actK_add_smul_emb, h1, h2]

theorem tauK_rot (a b : F) :
    D.τ (algebraMap F K a + algebraMap F K b * D.θ) =
      algebraMap F K a - algebraMap F K b * D.θ := by
  rw [map_add, map_mul, D.tau_alg, D.tau_alg, D.tau_theta]
  ring

theorem tauK_rot1 (a b : F) :
    D.τ (algebraMap F K a - 2 * algebraMap F K b * D.θ) =
      algebraMap F K a + 2 * algebraMap F K b * D.θ := by
  rw [map_sub, map_mul, map_mul, D.tau_alg, D.tau_alg, D.tau_theta, map_ofNat]
  ring

theorem norm_rot (a b : F) (hab : a ^ 2 + b ^ 2 = 1) :
    (algebraMap F K a + algebraMap F K b * D.θ) *
      D.τ (algebraMap F K a + algebraMap F K b * D.θ) = 1 := by
  rw [tauK_rot]
  have h := congrArg (algebraMap F K) hab
  simp only [map_add, map_pow, map_one] at h
  linear_combination h - (algebraMap F K b) ^ 2 * D.theta_sq

theorem norm_rot1 (a b : F) (hab : a ^ 2 + 4 * b ^ 2 = 1) :
    (algebraMap F K a - 2 * algebraMap F K b * D.θ) *
      D.τ (algebraMap F K a - 2 * algebraMap F K b * D.θ) = 1 := by
  rw [tauK_rot1]
  have h := congrArg (algebraMap F K) hab
  simp only [map_add, map_mul, map_pow, map_one, map_ofNat] at h
  linear_combination h - 4 * (algebraMap F K b) ^ 2 * D.theta_sq

theorem smul_vXi_cancel {c c' : K} (h : c • vXi D = c' • vXi D) : c = c' := by
  have := congrFun h (.inl 0)
  simpa [vXi] using this

theorem smul_vE2_cancel {c c' : K} (h : c • vE2 D = c' • vE2 D) : c = c' := by
  have := congrFun h (.inl 1)
  simpa [vE2] using this

end Basic

section Node0

variable {p f : ℕ} [Fact p.Prime]
  {hK : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2} {h2 : (2 : GaloisField p f) ≠ 0}
  {C : B2Coord hK (GaloisField p f) h2} {M : ModelB3 p f h2}
  {E : PhanFamilyB3 C (spinGroup (quadOdd 3 (GaloisField p f)))}
  [Algebra (GaloisField p f) (GaloisField p (2 * f))]
  (D : KDat (GaloisField p f) (GaloisField p (2 * f)))

theorem actK_eq_of_spinAction_eq {g : spinGroup (quadOdd 3 (GaloisField p f))}
    {L : W7 (GaloisField p f) ≃ₗ[GaloisField p f] W7 (GaloisField p f)}
    (h : spinAction (quadOdd 3 (GaloisField p f)) g = L) (x : W7 (GaloisField p (2 * f))) :
    actK g x = extK L.toLinearMap x := by
  simp [actK, h]

omit [Algebra (GaloisField p f) (GaloisField p (2 * f))] in
theorem tor_zero_mem (hr : (E.ι 0).range = M.U 0) (x : normOne (unitaryInvolution
    (GaloisField p (2 * f)) p f)) : tor E 0 x ∈ M.R₀ := by
  have : tor E 0 x ∈ (E.ι 0).range := ⟨torusTwo _ x, rfl⟩
  rw [hr] at this
  exact this

theorem tor_zero_rot (hg : GoodFamily E) (h2K : (2 : GaloisField p (2 * f)) ≠ 0)
    (h4 : 4 ≤ Nat.card (GaloisField p f)) (hr : ∀ i, (E.ι i).range = M.U i)
    (N0 : Node0Facts D h2)
    (x : normOne (unitaryInvolution (GaloisField p (2 * f)) p f)) :
    ∃ (a b : GaloisField p f) (hab : a ^ 2 + b ^ 2 = 1),
      spinAction (quadOdd 3 (GaloisField p f)) (tor E 0 x) = La0 h2 (rotSL0 a b hab) := by
  obtain ⟨A, hA⟩ : spinAction (quadOdd 3 (GaloisField p f)) (tor E 0 x) ∈ (fr0 h2).La.range := by
    rw [← M.map_eq]
    exact ⟨_, tor_zero_mem (M := M) (hr 0) x, rfl⟩
  have hmem : tor E 0 x ∈ torusSub E := by
    rw [← mTor_mulSingle E 0 x]
    exact ⟨_, rfl⟩
  have hP := torus_mapsTo_P hg h2K h4 hr hmem
  obtain ⟨a, b, hab, rfl⟩ := N0.rot_of_mapsTo A (fun s z => by
    obtain ⟨s', z', h⟩ := hP s z
    exact ⟨s', z', by rw [La0, ← hA] at *; exact h⟩)
  exact ⟨a, b, hab, hA.symm⟩

theorem tor_zero_eigen (hg : GoodFamily E) (h2K : (2 : GaloisField p (2 * f)) ≠ 0)
    (h4 : 4 ≤ Nat.card (GaloisField p f)) (hr : ∀ i, (E.ι i).range = M.U i)
    (N0 : Node0Facts D h2)
    (x : normOne (unitaryInvolution (GaloisField p (2 * f)) p f)) :
    ∃ κ : GaloisField p (2 * f), κ * D.τ κ = 1 ∧
      actK (tor E 0 x) (vXi D) = κ • vXi D ∧ actK (tor E 0 x) (vE2 D) = D.τ κ • vE2 D ∧
        actK (tor E 0 x) (vE3 D) = vE3 D := by
  obtain ⟨a, b, hab, h⟩ := tor_zero_rot D hg h2K h4 hr N0 x
  refine ⟨algebraMap _ _ a + algebraMap _ _ b * D.θ, norm_rot D a b hab, ?_, ?_, ?_⟩
  · rw [actK_eq_of_spinAction_eq h, N0.rot_vXi]
  · rw [actK_eq_of_spinAction_eq h, N0.rot_vE2, tauK_rot]
  · rw [actK_eq_of_spinAction_eq h, N0.fix_vE3]

omit [Algebra (GaloisField p f) (GaloisField p (2 * f))] in
theorem eq_of_spinAction_eq_of_mem_R0 {g h : spinGroup (quadOdd 3 (GaloisField p f))}
    (hg : g ∈ M.R₀) (hh : h ∈ M.R₀)
    (e : spinAction (quadOdd 3 (GaloisField p f)) g = spinAction (quadOdd 3 (GaloisField p f)) h) :
    g = h := by
  have h1 : g⁻¹ * h ∈ M.R₀ := M.R₀.mul_mem (M.R₀.inv_mem hg) hh
  have h2' := M.inj (g⁻¹ * h) h1 (by rw [map_mul, map_inv, e, inv_mul_cancel])
  exact (inv_mul_eq_one.mp h2')

omit [Algebra (GaloisField p f) (GaloisField p (2 * f))] in
theorem tor_injective (hg : GoodFamily E) (i : Fin 3) :
    Function.Injective (tor E i) := fun _ _ h =>
  torusTwo_injective _ (hg.inj i h)

noncomputable def normOneEquiv (hτ : ∀ c, unitaryInvolution (GaloisField p (2 * f)) p f c = D.τ c) :
    normOne (unitaryInvolution (GaloisField p (2 * f)) p f) ≃
      {κ : GaloisField p (2 * f) // κ * D.τ κ = 1} where
  toFun x := ⟨(((x : normOne (unitaryInvolution (GaloisField p (2 * f)) p f)) :
      (GaloisField p (2 * f))ˣ) : GaloisField p (2 * f)), by
    have h := x.2
    rw [mem_normOne, hτ] at h
    linear_combination h⟩
  invFun κ := ⟨Units.mk0 κ.1 (fun h => by
    have := κ.2
    rw [h] at this
    simp at this), by
    rw [mem_normOne, hτ]
    simp only [Units.val_mk0]
    linear_combination κ.2⟩
  left_inv _ := Subtype.ext (Units.ext rfl)
  right_inv _ := Subtype.ext rfl

theorem exists_tor_zero_eigen (hg : GoodFamily E) (h2K : (2 : GaloisField p (2 * f)) ≠ 0)
    (h4 : 4 ≤ Nat.card (GaloisField p f)) (hr : ∀ i, (E.ι i).range = M.U i)
    (N0 : Node0Facts D h2)
    (hτ : ∀ c, unitaryInvolution (GaloisField p (2 * f)) p f c = D.τ c)
    (κ : GaloisField p (2 * f)) (hκ : κ * D.τ κ = 1) :
    ∃ x : normOne (unitaryInvolution (GaloisField p (2 * f)) p f),
      actK (tor E 0 x) (vXi D) = κ • vXi D ∧ actK (tor E 0 x) (vE2 D) = D.τ κ • vE2 D ∧
        actK (tor E 0 x) (vE3 D) = vE3 D := by
  classical
  let Φ : normOne (unitaryInvolution (GaloisField p (2 * f)) p f) →
      {κ : GaloisField p (2 * f) // κ * D.τ κ = 1} := fun x =>
    ⟨Classical.choose (tor_zero_eigen D hg h2K h4 hr N0 x),
      (Classical.choose_spec (tor_zero_eigen D hg h2K h4 hr N0 x)).1⟩
  have hspec : ∀ x, actK (tor E 0 x) (vXi D) = (Φ x).1 • vXi D ∧
      actK (tor E 0 x) (vE2 D) = D.τ (Φ x).1 • vE2 D ∧ actK (tor E 0 x) (vE3 D) = vE3 D :=
    fun x => (Classical.choose_spec (tor_zero_eigen D hg h2K h4 hr N0 x)).2
  have hinj : Function.Injective Φ := by
    intro x y hxy
    obtain ⟨a, b, hab, h⟩ := tor_zero_rot D hg h2K h4 hr N0 x
    obtain ⟨a', b', hab', h'⟩ := tor_zero_rot D hg h2K h4 hr N0 y
    have e1 : (Φ x).1 = algebraMap _ _ a + algebraMap _ _ b * D.θ := by
      apply smul_vXi_cancel D
      rw [← (hspec x).1, actK_eq_of_spinAction_eq h, N0.rot_vXi]
    have e2 : (Φ y).1 = algebraMap _ _ a' + algebraMap _ _ b' * D.θ := by
      apply smul_vXi_cancel D
      rw [← (hspec y).1, actK_eq_of_spinAction_eq h', N0.rot_vXi]
    have e3 : algebraMap _ _ a + algebraMap _ _ b * D.θ =
        algebraMap (GaloisField p f) (GaloisField p (2 * f)) a' +
          algebraMap _ _ b' * D.θ := by
      rw [← e1, ← e2, hxy]
    obtain ⟨rfl, rfl⟩ := eq_of_add_mul_theta D h2 e3
    have : tor E 0 x = tor E 0 y :=
      eq_of_spinAction_eq_of_mem_R0 (M := M) (tor_zero_mem (M := M) (hr 0) x)
        (tor_zero_mem (M := M) (hr 0) y) (by rw [h, h'])
    exact tor_injective hg 0 this
  obtain ⟨x, hx⟩ := (Finite.injective_iff_surjective_of_equiv (normOneEquiv D hτ)).1 hinj
    ⟨κ, hκ⟩
  have hc : (Φ x).1 = κ := congrArg Subtype.val hx
  refine ⟨x, ?_⟩
  have := hspec x
  rw [hc] at this
  exact this

end Node0

section Node1

variable {p f : ℕ} [Fact p.Prime]
  {hK : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2} {h2 : (2 : GaloisField p f) ≠ 0}
  {C : B2Coord hK (GaloisField p f) h2} {M : ModelB3 p f h2}
  {E : PhanFamilyB3 C (spinGroup (quadOdd 3 (GaloisField p f)))}

theorem tor_one_mem (hr : (E.ι 1).range = M.U 1)
    (x : normOne (unitaryInvolution (GaloisField p (2 * f)) p f)) :
    tor E 1 x ∈ (longBlock (GaloisField p f) 2 1).range.map M.D.θ := by
  have : tor E 1 x ∈ (E.ι 1).range := ⟨torusTwo _ x, rfl⟩
  rw [hr] at this
  exact this

theorem eq_of_spinAction_eq_of_mem_U1 (h4 : 4 ≤ Nat.card (GaloisField p f))
    {g h : spinGroup (quadOdd 3 (GaloisField p f))}
    (hg : g ∈ (longBlock (GaloisField p f) 2 1).range.map M.D.θ)
    (hh : h ∈ (longBlock (GaloisField p f) 2 1).range.map M.D.θ)
    (e : spinAction (quadOdd 3 (GaloisField p f)) g = spinAction (quadOdd 3 (GaloisField p f)) h) :
    g = h := by
  obtain ⟨-, hinj⟩ := U1_spec M.D h4
  have h1 : g⁻¹ * h ∈ (longBlock (GaloisField p f) 2 1).range.map M.D.θ :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hg) hh
  have h2' := hinj (g⁻¹ * h) h1 (by rw [map_mul, map_inv, e, inv_mul_cancel])
  exact (inv_mul_eq_one.mp h2')

variable [Algebra (GaloisField p f) (GaloisField p (2 * f))]
  (D : KDat (GaloisField p f) (GaloisField p (2 * f)))

theorem tor_one_rot (hg : GoodFamily E) (h2K : (2 : GaloisField p (2 * f)) ≠ 0)
    (h4 : 4 ≤ Nat.card (GaloisField p f)) (hr : ∀ i, (E.ι i).range = M.U i)
    (N1 : Node1Facts D h2)
    (x : normOne (unitaryInvolution (GaloisField p (2 * f)) p f)) :
    ∃ (a b : GaloisField p f) (hab : a ^ 2 + 4 * b ^ 2 = 1),
      spinAction (quadOdd 3 (GaloisField p f)) (tor E 1 x) = La1 h2 (rotSL1 a b hab) := by
  obtain ⟨hmap, -⟩ := U1_spec M.D h4
  obtain ⟨A, hA⟩ : spinAction (quadOdd 3 (GaloisField p f)) (tor E 1 x) ∈ (fr1 h2).La.range := by
    rw [← hmap]
    exact ⟨_, tor_one_mem (M := M) (hr 1) x, rfl⟩
  have hmem : tor E 1 x ∈ torusSub E := by
    rw [← mTor_mulSingle E 1 x]
    exact ⟨_, rfl⟩
  have hP := torus_mapsTo_Pp hg h2K h4 hr hmem
  obtain ⟨a, b, hab, rfl⟩ := N1.rot_of_mapsTo A (fun s z => by
    obtain ⟨s', z', h⟩ := hP s z
    exact ⟨s', z', by rw [La1, ← hA] at *; exact h⟩)
  exact ⟨a, b, hab, hA.symm⟩

theorem tor_one_eigen (hg : GoodFamily E) (h2K : (2 : GaloisField p (2 * f)) ≠ 0)
    (h4 : 4 ≤ Nat.card (GaloisField p f)) (hr : ∀ i, (E.ι i).range = M.U i)
    (N1 : Node1Facts D h2)
    (x : normOne (unitaryInvolution (GaloisField p (2 * f)) p f)) :
    ∃ ν : GaloisField p (2 * f), ν * D.τ ν = 1 ∧
      actK (tor E 1 x) (vXi D) = vXi D ∧ actK (tor E 1 x) (vE2 D) = ν • vE2 D ∧
        actK (tor E 1 x) (vE3 D) = D.τ ν • vE3 D := by
  obtain ⟨a, b, hab, h⟩ := tor_one_rot D hg h2K h4 hr N1 x
  refine ⟨algebraMap _ _ a - 2 * algebraMap _ _ b * D.θ, norm_rot1 D a b hab, ?_, ?_, ?_⟩
  · rw [actK_eq_of_spinAction_eq h, N1.fix_vXi]
  · rw [actK_eq_of_spinAction_eq h, N1.rot_vE2]
  · rw [actK_eq_of_spinAction_eq h, N1.rot_vE3, tauK_rot1]

theorem exists_tor_one_eigen (hg : GoodFamily E) (h2K : (2 : GaloisField p (2 * f)) ≠ 0)
    (h4 : 4 ≤ Nat.card (GaloisField p f)) (hr : ∀ i, (E.ι i).range = M.U i)
    (N1 : Node1Facts D h2)
    (hτ : ∀ c, unitaryInvolution (GaloisField p (2 * f)) p f c = D.τ c)
    (ν : GaloisField p (2 * f)) (hν : ν * D.τ ν = 1) :
    ∃ x : normOne (unitaryInvolution (GaloisField p (2 * f)) p f),
      actK (tor E 1 x) (vXi D) = vXi D ∧ actK (tor E 1 x) (vE2 D) = ν • vE2 D ∧
        actK (tor E 1 x) (vE3 D) = D.τ ν • vE3 D := by
  classical
  let Φ : normOne (unitaryInvolution (GaloisField p (2 * f)) p f) →
      {κ : GaloisField p (2 * f) // κ * D.τ κ = 1} := fun x =>
    ⟨Classical.choose (tor_one_eigen D hg h2K h4 hr N1 x),
      (Classical.choose_spec (tor_one_eigen D hg h2K h4 hr N1 x)).1⟩
  have hspec : ∀ x, actK (tor E 1 x) (vXi D) = vXi D ∧
      actK (tor E 1 x) (vE2 D) = (Φ x).1 • vE2 D ∧
        actK (tor E 1 x) (vE3 D) = D.τ (Φ x).1 • vE3 D :=
    fun x => (Classical.choose_spec (tor_one_eigen D hg h2K h4 hr N1 x)).2
  have hinj : Function.Injective Φ := by
    intro x y hxy
    obtain ⟨a, b, hab, h⟩ := tor_one_rot D hg h2K h4 hr N1 x
    obtain ⟨a', b', hab', h'⟩ := tor_one_rot D hg h2K h4 hr N1 y
    have e1 : (Φ x).1 = algebraMap _ _ a - 2 * algebraMap _ _ b * D.θ := by
      apply smul_vE2_cancel D
      rw [← (hspec x).2.1, actK_eq_of_spinAction_eq h, N1.rot_vE2]
    have e2 : (Φ y).1 = algebraMap _ _ a' - 2 * algebraMap _ _ b' * D.θ := by
      apply smul_vE2_cancel D
      rw [← (hspec y).2.1, actK_eq_of_spinAction_eq h', N1.rot_vE2]
    have e3 : algebraMap (GaloisField p f) (GaloisField p (2 * f)) a +
        algebraMap _ _ (-(2 * b)) * D.θ = algebraMap _ _ a' + algebraMap _ _ (-(2 * b')) * D.θ := by
      simp only [map_neg, map_mul, map_ofNat]
      linear_combination (-1 : GaloisField p (2 * f)) * (e1.symm.trans (hxy ▸ e2)) *
        (-1 : GaloisField p (2 * f))
    obtain ⟨rfl, hb⟩ := eq_of_add_mul_theta D h2 e3
    have hb' : b = b' := by
      have h2' : (2 : GaloisField p f) * b = 2 * b' := neg_injective hb
      exact mul_left_cancel₀ h2 h2'
    subst hb'
    have : tor E 1 x = tor E 1 y :=
      eq_of_spinAction_eq_of_mem_U1 (M := M) h4 (tor_one_mem (M := M) (hr 1) x)
        (tor_one_mem (M := M) (hr 1) y) (by rw [h, h'])
    exact tor_injective hg 1 this
  obtain ⟨x, hx⟩ := (Finite.injective_iff_surjective_of_equiv (normOneEquiv D hτ)).1 hinj
    ⟨ν, hν⟩
  have hc : (Φ x).1 = ν := congrArg Subtype.val hx
  refine ⟨x, ?_⟩
  have := hspec x
  rw [hc] at this
  exact this

end Node1

end CFSG.ClassicalInvolution.PhanB3.S
