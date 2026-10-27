module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166SUBlocks
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Yardstones.Md0ec50421ce4.Definitions

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.ClassicalGroups.UnitaryFlag CFSG.SeitzReduction.UnitaryPilot
open CFSG.LocalAnalysis.ComponentInitial
open Matrix

namespace TwA5Big

section Certs


variable {n q : ℕ} {F : Type} [Field F] [Finite F]

@[expose] noncomputable def twA5Vec (c : Fin 4 → F) : Fin 6 → F :=
  ![c 0, c 0, c 1, c 2, c 3, (c 0 ^ 2 * c 1 * c 2 * c 3)⁻¹]

@[simp] theorem twA5Vec_zero (c : Fin 4 → F) : twA5Vec c 0 = c 0 := rfl

@[simp] theorem twA5Vec_one (c : Fin 4 → F) : twA5Vec c 1 = c 0 := rfl

@[simp] theorem twA5Vec_two (c : Fin 4 → F) : twA5Vec c 2 = c 1 := rfl

@[simp] theorem twA5Vec_three (c : Fin 4 → F) : twA5Vec c 3 = c 2 := rfl

@[simp] theorem twA5Vec_four (c : Fin 4 → F) : twA5Vec c 4 = c 3 := rfl

@[simp] theorem twA5Vec_five (c : Fin 4 → F) :
    twA5Vec c 5 = (c 0 ^ 2 * c 1 * c 2 * c 3)⁻¹ := rfl

theorem twA5Vec_mul (c c' : Fin 4 → F) : twA5Vec (c * c') = twA5Vec c * twA5Vec c' := by
  have h5 : (c 0 * c' 0) ^ 2 * (c 1 * c' 1) * (c 2 * c' 2) * (c 3 * c' 3) =
      (c 0 ^ 2 * c 1 * c 2 * c 3) * (c' 0 ^ 2 * c' 1 * c' 2 * c' 3) := by ring
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · show twA5Vec (c * c') 5 = twA5Vec c 5 * twA5Vec c' 5
    simp only [twA5Vec_five, Pi.mul_apply, h5, mul_inv]

theorem twA5Vec_injective : Function.Injective (twA5Vec (F := F)) := by
  intro c c' h
  have h0 : c 0 = c' 0 := by simpa using congrFun h 0
  have h2 : c 1 = c' 1 := by simpa using congrFun h 2
  have h3 : c 2 = c' 2 := by simpa using congrFun h 3
  have h4 : c 3 = c' 3 := by simpa using congrFun h 4
  funext i
  fin_cases i <;> assumption

theorem twA5Vec_one_fun : twA5Vec (1 : Fin 4 → F) = 1 := by
  funext i
  fin_cases i <;> simp [twA5Vec]

theorem twA5Vec_norm (h : UnitaryFieldData 2 n F) {c : Fin 4 → F}
    (hc : ∀ i, h.norm (c i) = 1) : ∀ i, h.norm (twA5Vec c i) = 1 := by
  have hne : ∀ i, c i ≠ 0 := fun i =>
    CFSG.GH74.Uniqueness.Bender.Frame.ne_zero_of_norm_eq_one (hc i)
  intro i
  fin_cases i
  · simpa using hc 0
  · simpa using hc 0
  · simpa using hc 1
  · simpa using hc 2
  · simpa using hc 3
  · show h.norm (twA5Vec c 5) = 1
    simp only [twA5Vec_five, norm_inv_eq h, norm_mul_eq h, pow_two, hc 0, hc 1, hc 2, hc 3,
      mul_one, one_mul, inv_one]

theorem twA5Vec_prod (h : UnitaryFieldData 2 n F) {c : Fin 4 → F}
    (hc : ∀ i, h.norm (c i) = 1) : ∏ i, twA5Vec c i = 1 := by
  have hne : ∀ i, c i ≠ 0 := fun i =>
    CFSG.GH74.Uniqueness.Bender.Frame.ne_zero_of_norm_eq_one (hc i)
  rw [Fin.prod_univ_six]
  simp only [twA5Vec_zero, twA5Vec_one, twA5Vec_two, twA5Vec_three, twA5Vec_four, twA5Vec_five]
  rw [show c 0 * c 0 * c 1 * c 2 * c 3 = c 0 ^ 2 * c 1 * c 2 * c 3 by ring]
  exact mul_inv_cancel₀ (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 (hne 0)) (hne 1))
    (hne 2)) (hne 3))

theorem norm_eq_one_of_mem_zpowers (h : UnitaryFieldData 2 n F) {ζu : Fˣ}
    (hζ : h.norm (ζu : F) = 1) {x : Fˣ} (hx : x ∈ Subgroup.zpowers ζu) :
    h.norm (x : F) = 1 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  refine (h.mem_ker_normUnits (u := ζu ^ k)).1 ?_
  rw [MonoidHom.mem_ker, map_zpow,
    show (Units.map h.normHom) ζu = 1 from (MonoidHom.mem_ker).2 ((h.mem_ker_normUnits).2 hζ)]
  simp

@[expose] noncomputable def twA5Diag (h : UnitaryFieldData 2 n F) {ζu : Fˣ}
    (hζ : h.norm (ζu : F) = 1) (c : Fin 4 → Subgroup.zpowers ζu) : unitarySU 2 n F 6 :=
  diagSU h (twA5Vec fun i => ((c i : Fˣ) : F))
    (twA5Vec_norm h fun i => norm_eq_one_of_mem_zpowers h hζ (c i).2)
    (twA5Vec_prod h fun i => norm_eq_one_of_mem_zpowers h hζ (c i).2)

theorem coe_twA5Diag (h : UnitaryFieldData 2 n F) {ζu : Fˣ} (hζ : h.norm (ζu : F) = 1)
    (c : Fin 4 → Subgroup.zpowers ζu) :
    (((twA5Diag h hζ c : unitarySU 2 n F 6) : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) =
      diagonal (twA5Vec fun i => ((c i : Fˣ) : F)) := rfl

theorem twA5Diag_mul (h : UnitaryFieldData 2 n F) {ζu : Fˣ} (hζ : h.norm (ζu : F) = 1)
    (c c' : Fin 4 → Subgroup.zpowers ζu) :
    twA5Diag h hζ (c * c') = twA5Diag h hζ c * twA5Diag h hζ c' := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_twA5Diag, Subgroup.coe_mul, Units.val_mul, coe_twA5Diag, coe_twA5Diag]
  have h1 : (fun i : Fin 4 => (((c * c') i : Fˣ) : F)) =
      (fun i => ((c i : Fˣ) : F)) * (fun i => ((c' i : Fˣ) : F)) := by
    funext i
    simp [Pi.mul_apply]
  rw [h1, twA5Vec_mul, diagonal_mul_diagonal]
  rfl

theorem twA5Diag_one (h : UnitaryFieldData 2 n F) {ζu : Fˣ} (hζ : h.norm (ζu : F) = 1) :
    twA5Diag h hζ 1 = 1 := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_twA5Diag, OneMemClass.coe_one, Units.val_one]
  have h1 : (fun i : Fin 4 => (((1 : Fin 4 → Subgroup.zpowers ζu) i : Fˣ) : F)) =
      (1 : Fin 4 → F) := by
    funext i
    simp
  rw [h1, twA5Vec_one_fun]
  simp

@[expose] noncomputable def twA5TorusHom (h : UnitaryFieldData 2 n F) {ζu : Fˣ}
    (hζ : h.norm (ζu : F) = 1) : (Fin 4 → Subgroup.zpowers ζu) →* unitarySU 2 n F 6 where
  toFun := twA5Diag h hζ
  map_one' := twA5Diag_one h hζ
  map_mul' := twA5Diag_mul h hζ

@[expose] noncomputable def twA5Torus (h : UnitaryFieldData 2 n F) {ζu : Fˣ}
    (hζ : h.norm (ζu : F) = 1) : Subgroup (unitarySU 2 n F 6) :=
  (twA5TorusHom h hζ).range

theorem twA5TorusHom_apply (h : UnitaryFieldData 2 n F) {ζu : Fˣ}
    (hζ : h.norm (ζu : F) = 1) (c : Fin 4 → Subgroup.zpowers ζu) :
    twA5TorusHom h hζ c = twA5Diag h hζ c := rfl

theorem twA5TorusHom_injective (h : UnitaryFieldData 2 n F) {ζu : Fˣ}
    (hζ : h.norm (ζu : F) = 1) : Function.Injective (twA5TorusHom h hζ) := by
  intro c c' hcc
  have h1 : (fun i => ((c i : Fˣ) : F)) = (fun i => ((c' i : Fˣ) : F)) := by
    apply twA5Vec_injective
    have h2 := congrArg (fun x : unitarySU 2 n F 6 =>
      ((x : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)) hcc
    rw [twA5TorusHom_apply, twA5TorusHom_apply] at h2
    rw [coe_twA5Diag, coe_twA5Diag] at h2
    exact Matrix.diagonal_injective h2
  funext i
  exact Subtype.ext (Units.ext (congrFun h1 i))

theorem card_twA5Torus (h : UnitaryFieldData 2 n F) {ζu : Fˣ} (hζ : h.norm (ζu : F) = 1)
    (hζo : orderOf ζu = q) : Nat.card (twA5Torus h hζ) = q ^ 4 := by
  have hdom : Nat.card (Fin 4 → Subgroup.zpowers ζu) = q ^ 4 := by
    rw [Nat.card_pi]
    simp [Nat.card_zpowers, hζo]
  rw [twA5Torus, MonoidHom.range_eq_map,
    Subgroup.card_map_of_injective (twA5TorusHom_injective h hζ), Subgroup.card_top, hdom]

@[expose] noncomputable def twA5B (h : UnitaryFieldData 2 n F) {ζu : Fˣ}
    (hζ : h.norm (ζu : F) = 1) : Subgroup (unitaryPSU h 6) :=
  ((unitaryProj h 6).comp (twA5TorusHom h hζ)).range

theorem mem_twA5B {h : UnitaryFieldData 2 n F} {ζu : Fˣ} {hζ : h.norm (ζu : F) = 1}
    {x : unitaryPSU h 6} :
    x ∈ twA5B h hζ ↔
      ∃ c : Fin 4 → Subgroup.zpowers ζu, unitaryProj h 6 (twA5TorusHom h hζ c) = x :=
  Iff.rfl

theorem exists_twA5Vec_of_mem_twA5Torus (h : UnitaryFieldData 2 n F) {ζu : Fˣ}
    (hζ : h.norm (ζu : F) = 1) {A : unitarySU 2 n F 6} (hA : A ∈ twA5Torus h hζ) :
    ∃ c : Fin 4 → Fˣ, (∀ i, c i ∈ Subgroup.zpowers ζu) ∧
      (((A : GL (Fin 6) F)) : Matrix (Fin 6) (Fin 6) F) =
        diagonal (twA5Vec fun i => (c i : F)) := by
  obtain ⟨c, rfl⟩ := hA
  exact ⟨fun i => (c i : Fˣ), fun i => (c i).2, coe_twA5Diag h hζ c⟩

theorem unitaryProj_injective_on_twA5Torus (h : UnitaryFieldData 2 n F) {ζu : Fˣ}
    (hζ : h.norm (ζu : F) = 1) (hζo : orderOf ζu = q) (hq : q.Prime) (hq6 : ¬ q ∣ 6) :
    ∀ A ∈ twA5Torus h hζ, ∀ B ∈ twA5Torus h hζ,
      unitaryProj h 6 A = unitaryProj h 6 B → A = B := by
  intro A hA B hB hAB
  have hmem : A * B⁻¹ ∈ unitaryScalars h 6 := by
    rw [← ker_unitaryProj h 6, MonoidHom.mem_ker, map_mul, map_inv, hAB, mul_inv_cancel]
  have hAB' : A * B⁻¹ ∈ twA5Torus h hζ := Subgroup.mul_mem _ hA (Subgroup.inv_mem _ hB)
  obtain ⟨c, hc⟩ := hAB'
  obtain ⟨lam, -, hlam6, hsc⟩ := mem_unitaryScalars.1 hmem
  have hentry : lam = ((c 0 : Fˣ) : F) := by
    have hmat : ((twA5TorusHom h hζ c : unitarySU 2 n F 6) : GL (Fin 6) F) =
        Matrix.GeneralLinearGroup.scalar (Fin 6) lam := by
      rw [hc]
      exact hsc
    have h3 := congrFun (congrFun (congrArg (fun x : GL (Fin 6) F =>
      ((x : Matrix (Fin 6) (Fin 6) F))) hmat) 0) 0
    simpa [twA5TorusHom, twA5Diag, coe_twA5Diag, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply] using h3.symm
  have hc0q : ((c 0 : Fˣ)) ^ q = 1 := by
    have h1 : orderOf ((c 0 : Fˣ)) ∣ Nat.card ↥(Subgroup.zpowers ζu) := by
      have h := orderOf_dvd_natCard (⟨(c 0 : Fˣ), (c 0).2⟩ : Subgroup.zpowers ζu)
      rwa [Subgroup.orderOf_mk] at h
    rw [Nat.card_zpowers, hζo] at h1
    exact orderOf_dvd_iff_pow_eq_one.1 h1
  have hlamq : lam ^ q = 1 := by
    apply Units.ext
    have h2 : (lam : F) ^ q = 1 := by
      rw [hentry]
      exact congrArg (fun u : Fˣ => (u : F)) hc0q
    simpa using h2
  have hcop : Nat.Coprime 6 q :=
    Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hq).2 hq6)
  have hdvd : orderOf lam ∣ 1 := by
    have h1 : orderOf lam ∣ 6 := orderOf_dvd_iff_pow_eq_one.2 hlam6
    have h2 : orderOf lam ∣ q := orderOf_dvd_iff_pow_eq_one.2 hlamq
    rw [← hcop]
    exact Nat.dvd_gcd h1 h2
  have hlam : lam = 1 := orderOf_eq_one_iff.1 (Nat.dvd_one.mp hdvd)
  have hone : A * B⁻¹ = 1 := by
    have h : ((A * B⁻¹ : unitarySU 2 n F 6) : GL (Fin 6) F) = 1 := by
      rw [hsc, hlam]
      simp
    exact Subtype.ext (by simpa using h)
  exact mul_inv_eq_one.1 hone

theorem twA5B_hom_injective (h : UnitaryFieldData 2 n F) {ζu : Fˣ}
    (hζ : h.norm (ζu : F) = 1) (hζo : orderOf ζu = q) (hq : q.Prime) (hq6 : ¬ q ∣ 6) :
    Function.Injective ((unitaryProj h 6).comp (twA5TorusHom h hζ)) := by
  intro c c' hcc
  have h1 : twA5TorusHom h hζ c = twA5TorusHom h hζ c' :=
    unitaryProj_injective_on_twA5Torus h hζ hζo hq hq6 _ ⟨c, rfl⟩ _ ⟨c', rfl⟩ hcc
  exact twA5TorusHom_injective h hζ h1

theorem card_twA5B (h : UnitaryFieldData 2 n F) {ζu : Fˣ} (hζ : h.norm (ζu : F) = 1)
    (hζo : orderOf ζu = q) (hq : q.Prime) (hq6 : ¬ q ∣ 6) : Nat.card (twA5B h hζ) = q ^ 4 := by
  have hdom : Nat.card (Fin 4 → Subgroup.zpowers ζu) = q ^ 4 := by
    rw [Nat.card_pi]
    simp [Nat.card_zpowers, hζo]
  rw [twA5B, MonoidHom.range_eq_map,
    Subgroup.card_map_of_injective (twA5B_hom_injective h hζ hζo hq hq6), Subgroup.card_top, hdom]

theorem twA5Torus_isElemAbelian (h : UnitaryFieldData 2 n F) {ζu : Fˣ}
    (hζ : h.norm (ζu : F) = 1) (hζo : orderOf ζu = q) :
    IsElemAbelian q (twA5Torus h hζ) := by
  constructor
  · refine ⟨⟨fun A B => ?_⟩⟩
    obtain ⟨c, hc⟩ := A.2
    obtain ⟨c', hc'⟩ := B.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hc, ← hc', ← map_mul, ← map_mul, mul_comm c c']
  · intro A hA
    obtain ⟨c, hc⟩ := hA
    rw [← hc, ← map_pow]
    have h1 : c ^ q = 1 := by
      funext i
      apply Subtype.ext
      apply Units.ext
      have h2 : ((c i : Fˣ)) ^ q = 1 := by
        have h3 : orderOf ((c i : Fˣ)) ∣ Nat.card ↥(Subgroup.zpowers ζu) := by
          have h := orderOf_dvd_natCard (⟨(c i : Fˣ), (c i).2⟩ : Subgroup.zpowers ζu)
          rwa [Subgroup.orderOf_mk] at h
        rw [Nat.card_zpowers, hζo] at h3
        exact orderOf_dvd_iff_pow_eq_one.1 h3
      exact congrArg (fun u : Fˣ => (u : F)) h2
    rw [h1, map_one]

theorem twA5B_isElemAbelian (h : UnitaryFieldData 2 n F) {ζu : Fˣ}
    (hζ : h.norm (ζu : F) = 1) (hζo : orderOf ζu = q) :
    IsElemAbelian q (twA5B h hζ) := by
  obtain ⟨hcomm, hpow⟩ := twA5Torus_isElemAbelian h hζ hζo
  constructor
  · refine ⟨⟨fun A B => ?_⟩⟩
    obtain ⟨c, hc⟩ := A.2
    obtain ⟨c', hc'⟩ := B.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hc, ← hc', ← map_mul, ← map_mul, mul_comm c c']
  · intro x hx
    obtain ⟨c, hc⟩ := hx
    rw [← hc, ← map_pow]
    show unitaryProj h 6 (twA5TorusHom h hζ (c ^ q)) = 1
    rw [map_pow, hpow (twA5TorusHom h hζ c) ⟨c, rfl⟩, map_one]

theorem diagFiveLast_mem_twA5B (h : UnitaryFieldData 2 n F) {ζu : Fˣ}
    (hζ : h.norm (ζu : F) = 1) :
    unitaryProj h 6 (diagFiveLast h (ζu : F) hζ) ∈ twA5B h hζ := by
  refine (mem_twA5B).2 ⟨fun _ => ⟨ζu, Subgroup.mem_zpowers ζu⟩, ?_⟩
  congr 1
  apply Subtype.ext
  apply Units.ext
  rw [twA5TorusHom_apply, twA5Diag, coe_diagSU, coe_diagFiveLast]
  congr 1
  funext i
  fin_cases i
  · simp [twA5Vec, diagFiveLastEntries]
  · simp [twA5Vec, diagFiveLastEntries]
  · simp [twA5Vec, diagFiveLastEntries]
  · simp [twA5Vec, diagFiveLastEntries]
  · simp [twA5Vec, diagFiveLastEntries]
  · show ((ζu : F) ^ 2 * (ζu : F) * (ζu : F) * (ζu : F))⁻¹ = ((ζu : F) ^ 5)⁻¹
    congr 1
    ring

end Certs

end TwA5Big

end CFSG.LocalAnalysis.GLTheoremA.Y10F
