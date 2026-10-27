module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84FLN
public import Certificates.Certificate320030

public section

namespace CFSG.OddStandard.SmallF3.Omega

namespace FL

open Certificates.A5GL42 (Mat4 Vec4 aN bN aO bO vecOfCode)
open Matrix

@[expose] def red : ZMod 4 →+* ZMod 2 := ZMod.castHom (by norm_num) (ZMod 2)

@[expose] def redM : M4 →+* Mat4 := red.mapMatrix

theorem redM_apply (A : M4) (i j : Fin 4) : redM A i j = red (A i j) := rfl

@[expose] def lift (x : ZMod 2) : ZMod 4 := ((x.val : ℕ) : ZMod 4)

theorem red_lift (x : ZMod 2) : red (lift x) = x := by
  revert x
  decide

@[expose] def liftM (g : Mat4) : M4 := g.map lift

theorem redM_liftM (g : Mat4) : redM (liftM g) = g := by
  ext i j
  simp [redM_apply, liftM, red_lift]

@[expose] def half (e : ZMod 4) : ZMod 4 := ((e.val / 2 : ℕ) : ZMod 4)

theorem red_eq_imp (x y : ZMod 4) (h : red x = red y) : x = y + 2 * half (x - y) := by
  revert x y
  decide

theorem exists_two_smul {M N : M4} (h : redM M = redM N) : ∃ X : M4, M = N + (2 : ℕ) • X := by
  refine ⟨(M - N).map half, ?_⟩
  ext i j
  have hij : red (M i j) = red (N i j) := by
    have := congrFun (congrFun h i) j
    simpa [redM_apply] using this
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.sub_apply]
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  exact red_eq_imp _ _ hij

theorem redM_a0 : redM a0 = aN := by
  decide +kernel

theorem redM_b0 : redM b0 = bN := by
  decide +kernel

theorem isUnit_of_red_eq_one (x : ZMod 4) (h : red x = 1) : IsUnit x := by
  have : x = 1 ∨ x = 3 := by
    revert x
    decide
  rcases this with rfl | rfl
  · exact isUnit_one
  · exact ⟨⟨3, 3, by decide, by decide⟩, rfl⟩

theorem isUnit_det_liftM {g : Mat4} (hg : g.det = 1) : IsUnit (liftM g).det := by
  apply isUnit_of_red_eq_one
  have h := RingHom.map_det red (liftM g)
  rw [show red.mapMatrix (liftM g) = g from redM_liftM g] at h
  rw [h, hg]

theorem conj_pow {G Gi : M4} (hGi : Gi * G = 1) (A : M4) (n : ℕ) :
    (G * A * Gi) ^ (n + 1) = G * A ^ (n + 1) * Gi := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, pow_succ A (n + 1)]
    calc G * A ^ (n + 1) * Gi * (G * A * Gi) = G * A ^ (n + 1) * (Gi * G) * A * Gi := by
          simp only [mul_assoc]
      _ = G * (A ^ (n + 1) * A) * Gi := by rw [hGi, mul_one]; simp only [mul_assoc]

@[expose] def SO : Finset Vec4 :=
  {vecOfCode 7, vecOfCode 11, vecOfCode 13, vecOfCode 14, vecOfCode 15}

theorem SO_inv : ∀ v ∈ SO, aO *ᵥ v ∈ SO ∧ bO *ᵥ v ∈ SO := by
  decide +kernel

theorem SO_s : vecOfCode 7 ∈ SO ∧ vecOfCode 7 ≠ 0 := by
  decide +kernel

theorem SO_t : vecOfCode 1 ∉ SO ∧ vecOfCode 1 ≠ 0 := by
  decide +kernel

theorem e12 : vecOfCode 1 ≠ vecOfCode 2 := by
  decide +kernel

theorem a_ne_one {a b : Mat4} (hb : b ^ 3 = 1) (hab : (a * b) ^ 5 = 1)
    (htrans : ∀ v w : Vec4, v ≠ 0 → w ≠ 0 →
      ∃ g ∈ Submonoid.closure ({a, b} : Set Mat4), g *ᵥ v = w) : a ≠ 1 := by
  intro ha
  subst ha
  have hb5 : b ^ 5 = 1 := by simpa using hab
  have hb2 : b ^ 2 = 1 := by
    have : b ^ 5 = b ^ 3 * b ^ 2 := by rw [← pow_add]
    rw [this, hb, one_mul] at hb5
    exact hb5
  have hb1 : b = 1 := by
    have : b ^ 3 = b ^ 2 * b := by rw [← pow_succ]
    rw [this, hb2, one_mul] at hb
    exact hb
  subst hb1
  have hg1 : ∀ g ∈ Submonoid.closure ({1, 1} : Set Mat4), g = 1 := by
    intro g hg
    induction hg using Submonoid.closure_induction with
    | mem x hx => rcases hx with rfl | rfl <;> rfl
    | one => rfl
    | mul x y _ _ hx hy => rw [hx, hy, mul_one]
  obtain ⟨g, hg, hgv⟩ := htrans (vecOfCode 1) (vecOfCode 2) (by decide +kernel)
    (by decide +kernel)
  rw [hg1 g hg, one_mulVec] at hgv
  exact e12 hgv

theorem closure_inv {a b : Mat4} (S : Set Vec4) (ha : ∀ v ∈ S, a *ᵥ v ∈ S)
    (hb : ∀ v ∈ S, b *ᵥ v ∈ S) {g : Mat4} (hg : g ∈ Submonoid.closure ({a, b} : Set Mat4)) :
    ∀ v ∈ S, g *ᵥ v ∈ S := by
  induction hg using Submonoid.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    exacts [ha, hb]
  | one =>
    intro v hv
    simpa using hv
  | mul x y _ _ hx hy =>
    intro v hv
    rw [← mulVec_mulVec]
    exact hx _ (hy v hv)

theorem conj_mul {G Gi : M4} (hGi : Gi * G = 1) (A B : M4) :
    (G * A * Gi) * (G * B * Gi) = G * (A * B) * Gi := by
  calc (G * A * Gi) * (G * B * Gi) = G * A * (Gi * G) * B * Gi := by simp only [mul_assoc]
    _ = G * (A * B) * Gi := by rw [hGi, mul_one]; simp only [mul_assoc]

theorem case_N (A B : M4) (hA2 : A * A = 1) (hB : B ^ 3 = 1) (hAB : (A * B) ^ 5 = 1) (g : Mat4)
    (G Gi : M4) (hG : redM G = g) (hG1 : G * Gi = 1) (hG2 : Gi * G = 1)
    (hga : g * redM A = aN * g) (hgb : g * redM B = bN * g) : False := by
  have hred : g * redM Gi = 1 := by
    have := congrArg redM hG1
    rwa [map_mul, hG, map_one] at this
  have hA' : (G * A * Gi) * (G * A * Gi) = 1 := by rw [conj_mul hG2, hA2, mul_one, hG1]
  have e3 : (G * B * Gi) ^ 3 = G * B ^ 3 * Gi := conj_pow hG2 B 2
  have e5 : (G * (A * B) * Gi) ^ 5 = G * (A * B) ^ 5 * Gi := conj_pow hG2 (A * B) 4
  have hB' : (G * B * Gi) ^ 3 = 1 := by rw [e3, hB, mul_one, hG1]
  have hAB' : ((G * A * Gi) * (G * B * Gi)) ^ 5 = 1 := by
    rw [conj_mul hG2, e5, hAB, mul_one, hG1]
  have hAr : redM (G * A * Gi) = redM a0 := by
    rw [redM_a0, map_mul, map_mul, hG, hga, mul_assoc, hred, mul_one]
  have hBr : redM (G * B * Gi) = redM b0 := by
    rw [redM_b0, map_mul, map_mul, hG, hgb, mul_assoc, hred, mul_one]
  obtain ⟨X, hX⟩ := exists_two_smul hAr
  obtain ⟨Y, hY⟩ := exists_two_smul hBr
  refine no_lift_N X Y ?_ ?_ ?_
  · rw [← hX]
    exact hA'
  · rw [← hY]
    simpa [pow_succ] using hB'
  · rw [← hX, ← hY]
    exact hAB'

theorem case_O (A B : M4) (g : Mat4) (hdet : g.det = 1) (hga : g * redM A = aO * g)
    (hgb : g * redM B = bO * g)
    (htrans : ∀ v w : Vec4, v ≠ 0 → w ≠ 0 →
      ∃ γ ∈ Submonoid.closure ({redM A, redM B} : Set Mat4), γ *ᵥ v = w) : False := by
  have hu : IsUnit g.det := by rw [hdet]; exact isUnit_one
  have hg1 : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  let S : Set Vec4 := {v | g *ᵥ v ∈ (SO : Set Vec4)}
  have hSa : ∀ v ∈ S, redM A *ᵥ v ∈ S := by
    intro v hv
    show g *ᵥ (redM A *ᵥ v) ∈ (SO : Set Vec4)
    rw [mulVec_mulVec, hga, ← mulVec_mulVec]
    exact (SO_inv _ hv).1
  have hSb : ∀ v ∈ S, redM B *ᵥ v ∈ S := by
    intro v hv
    show g *ᵥ (redM B *ᵥ v) ∈ (SO : Set Vec4)
    rw [mulVec_mulVec, hgb, ← mulVec_mulVec]
    exact (SO_inv _ hv).2
  obtain ⟨hs, hs0⟩ := SO_s
  obtain ⟨ht, ht0⟩ := SO_t
  have hv0 : g *ᵥ (g⁻¹ *ᵥ vecOfCode 7) = vecOfCode 7 := by
    rw [mulVec_mulVec, hg1, one_mulVec]
  have hw0 : g *ᵥ (g⁻¹ *ᵥ vecOfCode 1) = vecOfCode 1 := by
    rw [mulVec_mulVec, hg1, one_mulVec]
  have hv0ne : g⁻¹ *ᵥ vecOfCode 7 ≠ 0 := by
    intro h
    rw [h, mulVec_zero] at hv0
    exact hs0 hv0.symm
  have hw0ne : g⁻¹ *ᵥ vecOfCode 1 ≠ 0 := by
    intro h
    rw [h, mulVec_zero] at hw0
    exact ht0 hw0.symm
  obtain ⟨γ, hγ, hγv⟩ := htrans _ _ hv0ne hw0ne
  have hmem : g⁻¹ *ᵥ vecOfCode 7 ∈ S := by
    show g *ᵥ (g⁻¹ *ᵥ vecOfCode 7) ∈ (SO : Set Vec4)
    rw [hv0]
    exact hs
  have := closure_inv S hSa hSb hγ _ hmem
  rw [hγv] at this
  change g *ᵥ (g⁻¹ *ᵥ vecOfCode 1) ∈ (SO : Set Vec4) at this
  rw [hw0] at this
  exact ht this

theorem no_lift (A B : M4) (hA : A ^ 2 = 1)
    (hB : B ^ 3 = 1) (hAB : (A * B) ^ 5 = 1)
    (htrans : ∀ v w : Vec4, v ≠ 0 → w ≠ 0 →
      ∃ g ∈ Submonoid.closure ({redM A, redM B} : Set Mat4), g *ᵥ v = w) : False := by
  have hA2 : A * A = 1 := by simpa [pow_succ] using hA
  have ha : redM A * redM A = 1 := by rw [← map_mul, hA2, map_one]
  have hb : redM B ^ 3 = 1 := by rw [← map_pow, hB, map_one]
  have hab : (redM A * redM B) ^ 5 = 1 := by rw [← map_mul, ← map_pow, hAB, map_one]
  have ha1 : redM A ≠ 1 := a_ne_one hb hab htrans
  obtain ⟨g, hdet, hcase⟩ := Certificates.certificate320030.classify (redM A) (redM B) ha ha1 hb hab
  rcases hcase with ⟨hga, hgb⟩ | ⟨hga, hgb⟩
  · have hu : IsUnit (liftM g).det := isUnit_det_liftM hdet
    exact case_N A B hA2 hB hAB g (liftM g) (liftM g)⁻¹ (redM_liftM g)
      (Matrix.mul_nonsing_inv _ hu) (Matrix.nonsing_inv_mul _ hu) hga hgb
  · exact case_O A B g hdet hga hgb htrans

theorem no_lift_hom {Γ : Type*} [Group Γ] [Finite Γ] (a b : Γ)
    (ha : a ^ 2 = 1) (hb : b ^ 3 = 1) (hab : (a * b) ^ 5 = 1)
    (hgen : Subgroup.closure ({a, b} : Set Γ) = ⊤) (ρ : Γ →* M4)
    (htrans : ∀ v w : Vec4, v ≠ 0 → w ≠ 0 → ∃ γ : Γ, redM (ρ γ) *ᵥ v = w) : False := by
  have key : ∀ γ ∈ Submonoid.closure ({a, b} : Set Γ),
      redM (ρ γ) ∈ Submonoid.closure ({redM (ρ a), redM (ρ b)} : Set Mat4) := by
    intro γ hγ
    induction hγ using Submonoid.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact Submonoid.subset_closure (by simp)
      · exact Submonoid.subset_closure (by simp)
    | one =>
      rw [map_one, map_one]
      exact Submonoid.one_mem _
    | mul x y _ _ hx hy =>
      rw [map_mul, map_mul]
      exact Submonoid.mul_mem _ hx hy
  refine no_lift (ρ a) (ρ b) (by rw [← map_pow, ha, map_one]) (by rw [← map_pow, hb, map_one])
    (by rw [← map_mul, ← map_pow, hab, map_one]) ?_
  intro v w hv hw
  obtain ⟨γ, hγ⟩ := htrans v w hv hw
  refine ⟨redM (ρ γ), key γ ?_, hγ⟩
  rw [← Subgroup.closure_toSubmonoid_of_finite]
  show γ ∈ Subgroup.closure ({a, b} : Set Γ)
  rw [hgen]
  trivial

end FL

end CFSG.OddStandard.SmallF3.Omega
