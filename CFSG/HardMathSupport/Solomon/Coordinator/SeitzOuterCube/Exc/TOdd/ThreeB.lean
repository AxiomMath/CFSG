module

public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.TOdd.BModel
public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.TOdd.Shape
public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.TOdd.ThreeBAbs
public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.TOdd.ThreeBClos
public import CFSG.RankThree.PartTwo.Sec4.E27.D4StepALeavesAuxDefs

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.TOdd

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open
open CFSG.RankThree.PartTwo.Sec11 CFSG.RankThree.PartTwo.Sec19 CFSG.RankThree.PartTwo.Sec4.E27
open CFSG.ClassicalInvolution.G2D4Models
open scoped MatrixGroups


variable {ℓ f : ℕ} {X : Type} [Field X] [Finite X] {σ : X ≃+* X}

theorem threeB_orderOf_sigma (P : D4ParOdd ℓ f X σ) : orderOf σ = 3 :=
  orderOf_eq_prime P.sigma_pow_three (sigma_ne_one_odd P)

theorem threeB_card_fix (P : D4ParOdd ℓ f X σ) : Nat.card (fixSubfield σ) = ℓ ^ f := by
  have hK3 : Nat.card X = ℓ ^ (3 * f) := by rw [P.card, ← pow_mul, mul_comm]
  obtain ⟨-, hcard⟩ := CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield P.prime
    (by have := P.one_le; omega : 1 ≤ 3 * f) hK3 σ
  rw [threeB_orderOf_sigma P, Nat.mul_div_cancel_left _ (by norm_num)] at hcard
  exact hcard

theorem threeB_ringChar_ne_two (P : D4ParOdd ℓ f X σ) : ringChar X ≠ 2 := by
  haveI := P.charP
  rw [ringChar.eq X ℓ]
  exact P.ne_two

theorem threeB_delta (P : D4ParOdd ℓ f X σ) {r : ℕ} (hr : r = 1 ∨ r = 2) :
    orderOf (σ ^ r) = 3 ∧ ∀ x, x ∈ fixSubfield σ ↔ (σ ^ r) x = x := by
  have hσo := threeB_orderOf_sigma P
  rcases hr with rfl | rfl
  · exact ⟨by rw [pow_one, hσo], fun x => by rw [pow_one]; exact Iff.rfl⟩
  · refine ⟨?_, fun x => ?_⟩
    · rw [Nat.Coprime.orderOf_pow (by rw [hσo]; norm_num), hσo]
    · constructor
      · intro hx
        have hx' : σ x = x := hx
        show σ (σ x) = x
        rw [hx', hx']
      · intro hx
        have hx' : σ (σ x) = x := hx
        calc σ x = σ (σ (σ x)) := by rw [hx']
          _ = x := P.sigma_cube x

theorem threeB_conj_map_aut {T : Type*} [Group T] (φ : MulAut T) (t : T) :
    MulAut.conj (φ t) = φ * MulAut.conj t * φ⁻¹ := by
  ext u
  simp [MulAut.conj_apply, MulAut.mul_apply]

theorem threeB_tau_cube (P : D4ParOdd ℓ f X σ) : tauAut σ ^ 3 = 1 := by
  have h1 : fieldActor (t := TwistTag.D4) σ (σ ^ 3) = fieldActor σ σ ^ 3 :=
    map_pow (fieldActorHom (t := TwistTag.D4) σ) σ 3
  rw [← h1, P.sigma_pow_three, fieldActor_one]

theorem threeB_outer_shape (P : D4ParOdd ℓ f X σ) {E : Subgroup (MulAut (C0 σ))}
    (hE : IsElemAbelian 3 E) {e : MulAut (C0 σ)} (heE : e ∈ E)
    (hein : e ∉ (MulAut.conj : C0 σ →* MulAut (C0 σ)).range) :
    ∃ (g : C0 σ) (r : ℕ), (r = 1 ∨ r = 2) ∧ e = MulAut.conj g * tauAut σ ^ r := by
  obtain ⟨g, j, hgj⟩ := shape_of_mem_E_odd P hE e heE
  have hmod : tauAut σ ^ j = tauAut σ ^ (j % 3) := pow_eq_pow_mod j (threeB_tau_cube P)
  have hr : j % 3 = 1 ∨ j % 3 = 2 := by
    by_contra hcon
    have h0 : j % 3 = 0 := by omega
    apply hein
    refine ⟨g, ?_⟩
    rw [hgj, hmod, h0, pow_zero, mul_one]
  exact ⟨g, j % 3, hr, by rw [hgj, hmod]⟩

theorem threeB_tau_pow_iota (P : D4ParOdd ℓ f X σ) (n : ℕ) (A : SL(2, X)) :
    (tauAut σ ^ n) (iotaAOdd P A) =
      iotaAOdd P (Matrix.SpecialLinearGroup.map (σ ^ n).toRingHom A) := by
  induction n generalizing A with
  | zero =>
    have : Matrix.SpecialLinearGroup.map (σ ^ 0).toRingHom A = A := by
      apply Subtype.ext
      ext i j
      simp
    rw [this]
    rfl
  | succ n ih =>
    rw [pow_succ, MulAut.mul_apply, tau_iotaAOdd, ih]
    congr 1

theorem threeB_glConjSL_eq_self_of_scalar {D : GL (Fin 2) X} {c : X}
    (hc : (D : Matrix (Fin 2) (Fin 2) X) = c • 1) (A : SL(2, X)) : glConjSL D A = A := by
  apply Subtype.ext
  rw [glConjSL_coe]
  have hcomm : (D : Matrix (Fin 2) (Fin 2) X) * (A : Matrix (Fin 2) (Fin 2) X) =
      (A : Matrix (Fin 2) (Fin 2) X) * D := by
    rw [hc, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  rw [hcomm, Matrix.mul_assoc, gl_mul_inv, Matrix.mul_one]

theorem cen_le_closure_threeB_odd (P : D4ParOdd ℓ f X σ) {E : Subgroup (MulAut (C0 σ))}
    (hE : CFSG.Open.IsElemAbelian 3 E) {z : C0 σ} (hzE : MulAut.conj z ∈ E) (hz1 : z ≠ 1)
    (hzS : z ∈ Subgroup.centralizer (Asub σ : Set (C0 σ)))
    {b : C0 σ} (hbE : MulAut.conj b ∈ E) (hbz : MulAut.conj b ∉ Subgroup.zpowers (MulAut.conj z))
    {e : MulAut (C0 σ)} (heE : e ∈ E) (hein : e ∉ (MulAut.conj : C0 σ →* MulAut (C0 σ)).range) :
    cenX σ z ≤ Subgroup.closure {l | l ∈ cenX σ z ∧ ∃ y ∈ E,
      y ∉ Subgroup.zpowers (MulAut.conj z : MulAut (C0 σ)) ∧ y l = l} := by
  have hinj := conj_injective_odd P
  have hz3 : z ^ 3 = 1 := by
    apply hinj
    rw [map_pow, map_one]
    exact hE.2 _ hzE
  have hb3 : b ^ 3 = 1 := by
    apply hinj
    rw [map_pow, map_one]
    exact hE.2 _ hbE
  have hbz' : b * z = z * b := by
    apply hinj
    rw [map_mul, map_mul]
    exact congrArg Subtype.val (hE.1.is_comm.comm (⟨_, hbE⟩ : E) ⟨_, hzE⟩)
  have hbC : b ∈ cenX σ z := Subgroup.mem_centralizer_singleton_iff.mpr hbz'
  have hιinj := iotaAOdd_injective P
  have hrange : (iotaAOdd P).range = Asub σ := iotaAOdd_range P
  have hSC : ∀ A, iotaAOdd P A ∈ cenX σ z := fun A => by
    have hA : iotaAOdd P A ∈ Asub σ := hrange ▸ ⟨A, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp hzS _ hA
  have hact' : ∀ g : C0 σ, g * z = z * g →
      ∃ N : GL (Fin 2) X, ∀ A, g * iotaAOdd P A * g⁻¹ = iotaAOdd P (glConjSL N A) := by
    intro g hg
    obtain ⟨N, hN⟩ := exists_GL2_action P hzS hz3 hz1 hg
    exact ⟨N, fun A => by simpa only [bModelPsi_coe] using hN A⟩
  have hact : ∀ x ∈ cenX σ z,
      ∃ N : GL (Fin 2) X, ∀ A, x * iotaAOdd P A * x⁻¹ = iotaAOdd P (glConjSL N A) := fun x hx =>
    hact' x (Subgroup.mem_centralizer_singleton_iff.mp hx)
  have hcomm : ∀ x ∈ cenX σ z, ∀ y ∈ cenX σ z, x * y * x⁻¹ * y⁻¹ ∈ (iotaAOdd P).range := by
    intro x hx y hy
    rw [hrange]
    exact (KS11Lie6Proof.d4ThreeBCent_holds X (ℓ ^ f) σ P.card P.frob P.not_three_dvd z hzS hz3
      hz1).1 x hx y hy
  have hzIn : MulAut.conj z ∈ (MulAut.conj : C0 σ →* MulAut (C0 σ)).range := ⟨z, rfl⟩
  have hzp : ∀ y, y ∈ Subgroup.zpowers (MulAut.conj z : MulAut (C0 σ)) →
      y ∈ (MulAut.conj : C0 σ →* MulAut (C0 σ)).range := fun y hy =>
    Subgroup.zpowers_le.mpr hzIn hy
  have hS : (iotaAOdd P).range ≤ Subgroup.closure {l | l ∈ cenX σ z ∧ ∃ y ∈ E,
      y ∉ Subgroup.zpowers (MulAut.conj z : MulAut (C0 σ)) ∧ y l = l} := by
    obtain ⟨g, r, hr, hegr⟩ := threeB_outer_shape P hE heE hein
    have hez : e z = z := by
      apply hinj
      have h1 : e * MulAut.conj z = MulAut.conj z * e :=
        congrArg Subtype.val (hE.1.is_comm.comm (⟨e, heE⟩ : E) ⟨MulAut.conj z, hzE⟩)
      rw [threeB_conj_map_aut e z, h1]
      group
    have hτz : tauAut σ z = z := fieldActor_eq_self_of_mem_centralizer P hzS
    have hτrz : ∀ n : ℕ, (tauAut σ ^ n) z = z := fun n => by
      induction n with
      | zero => rfl
      | succ n ih => rw [pow_succ, MulAut.mul_apply, hτz, ih]
    have hgz : g * z = z * g := by
      have h1 : e z = g * z * g⁻¹ := by
        rw [hegr]
        show g * (tauAut σ ^ r) z * g⁻¹ = g * z * g⁻¹
        rw [hτrz]
      rw [h1] at hez
      calc g * z = g * z * g⁻¹ * g := by group
        _ = z * g := by rw [hez]
    obtain ⟨N₁, hN₁⟩ := hact' g hgz
    obtain ⟨Nb, hNb⟩ := hact' b hbz'
    obtain ⟨hδ, hF⟩ := threeB_delta P hr
    have hN₁' : ∀ A, e (iotaAOdd P A) = iotaAOdd P (glConjSL N₁
        (Matrix.SpecialLinearGroup.map (σ ^ r).toRingHom A)) := fun A => by
      have h1 : e (iotaAOdd P A) = g * (tauAut σ ^ r) (iotaAOdd P A) * g⁻¹ := by
        rw [hegr]
        rfl
      rw [h1, threeB_tau_pow_iota P r A]
      exact hN₁ _
    have hnsc : ¬ ∃ c : X, (Nb : Matrix (Fin 2) (Fin 2) X) = Matrix.scalar (Fin 2) c := by
      rintro ⟨c, hc⟩
      have hc' : (Nb : Matrix (Fin 2) (Fin 2) X) = c • 1 := by
        rw [hc, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
      have hbS : b ∈ Subgroup.centralizer (Asub σ : Set (C0 σ)) := by
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [← hrange] at hh
        obtain ⟨A, rfl⟩ := hh
        have h1 := hNb A
        rw [threeB_glConjSL_eq_self_of_scalar hc'] at h1
        calc iotaAOdd P A * b = b * iotaAOdd P A * b⁻¹ * b := by rw [h1]
          _ = b * iotaAOdd P A := by group
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
        (mem_zpowers_of_mem_centralizer_short P hzS hz3 hz1 hbS hb3 hbz')
      apply hbz
      refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
      rw [← map_zpow, hk]
    have hmain := threeB_range_le_closure (threeB_ringChar_ne_two P) (iotaAOdd P) hιinj (σ ^ r)
      hδ hF (by rw [threeB_card_fix P]; exact P.five_le) e (hE.2 e heE) b
      (hE.2 _ (E.mul_mem heE hbE)) N₁ Nb hN₁' hNb hnsc
    refine hmain.trans (Subgroup.closure_mono ?_)
    have hSCr : ∀ l ∈ (iotaAOdd P).range, l ∈ cenX σ z := by
      rintro _ ⟨A, rfl⟩
      exact hSC A
    rintro l (⟨hl, hel⟩ | ⟨hl, hel⟩)
    · exact ⟨hSCr l hl, e, heE, fun h => hein (hzp _ h), hel⟩
    · refine ⟨hSCr l hl, e * MulAut.conj b, E.mul_mem heE hbE, fun h => hein ?_, hel⟩
      have h1 := (MonoidHom.range (MulAut.conj : C0 σ →* MulAut (C0 σ))).mul_mem (hzp _ h)
        ((MonoidHom.range (MulAut.conj : C0 σ →* MulAut (C0 σ))).inv_mem ⟨b, rfl⟩)
      simpa using h1
  intro x hx
  obtain ⟨A, hA⟩ := threeB_conj_exists (three_ne_zero_odd P) (iotaAOdd P) hιinj (cenX σ z) hSC
    hact hcomm hbC hb3 x hx
  have hh : iotaAOdd P A ∈ Subgroup.closure {l | l ∈ cenX σ z ∧ ∃ y ∈ E,
      y ∉ Subgroup.zpowers (MulAut.conj z : MulAut (C0 σ)) ∧ y l = l} := hS ⟨A, rfl⟩
  have hc : (iotaAOdd P A)⁻¹ * x ∈ cenX σ z := (cenX σ z).mul_mem ((cenX σ z).inv_mem (hSC A)) hx
  have hcb : MulAut.conj b ((iotaAOdd P A)⁻¹ * x) = (iotaAOdd P A)⁻¹ * x := by
    have h1 : x * b = iotaAOdd P A * b * (iotaAOdd P A)⁻¹ * x := by
      rw [hA]
      group
    rw [MulAut.conj_apply]
    calc b * ((iotaAOdd P A)⁻¹ * x) * b⁻¹
        = (iotaAOdd P A)⁻¹ * (iotaAOdd P A * b * (iotaAOdd P A)⁻¹ * x) * b⁻¹ := by group
      _ = (iotaAOdd P A)⁻¹ * (x * b) * b⁻¹ := by rw [h1]
      _ = (iotaAOdd P A)⁻¹ * x := by group
  have hcΓ : (iotaAOdd P A)⁻¹ * x ∈ Subgroup.closure {l | l ∈ cenX σ z ∧ ∃ y ∈ E,
      y ∉ Subgroup.zpowers (MulAut.conj z : MulAut (C0 σ)) ∧ y l = l} :=
    Subgroup.subset_closure ⟨hc, MulAut.conj b, hbE, hbz, hcb⟩
  have hx' : x = iotaAOdd P A * ((iotaAOdd P A)⁻¹ * x) := by group
  rw [hx']
  exact Subgroup.mul_mem _ hh hcΓ

end CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.TOdd
