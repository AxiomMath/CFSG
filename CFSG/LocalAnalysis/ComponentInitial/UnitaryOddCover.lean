module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryOddCoverSylow
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticSixCoverCore
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverHigherField
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryOddCoverComplement

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryOddCover

open Matrix CFSG.ClassicalGroups.UnitaryFlag MatrixExtension
open scoped commutatorElement

variable {K : Type} [Field K] {h : UnitaryFieldData 2 1 K} {r : ℕ}

theorem levi_injective :
    Function.Injective ((hypProj h r 1).comp ((lHom h r).comp SpecialLinearGroup.toGL)) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro A hA
  have h1 := eq_one_of_hypProj_lHom (h := h) (A := SpecialLinearGroup.toGL A) A.2 hA
  exact Subgroup.mem_bot.mpr (SpecialLinearGroup.toGL_injective (h1.trans (map_one _).symm))

variable [CharP K 2] {E : Type*} [Group E] {θ : E →* hypPSU h r 1}

omit [CharP K 2] in
theorem lHom_diagGL_conj (t : Fin r → Kˣ) (A : SpecialLinearGroup (Fin r) K) :
    ∃ B : SpecialLinearGroup (Fin r) K, lHom h r (TauCeti.diagGL t) *
      lHom h r (SpecialLinearGroup.toGL A) * (lHom h r (TauCeti.diagGL t))⁻¹ =
        lHom h r (SpecialLinearGroup.toGL B) ∧
      (B : Matrix (Fin r) (Fin r) K) = diagonal (fun i => (t i : K)) *
        (A : Matrix (Fin r) (Fin r) K) * (diagonal fun i => (t i : K))⁻¹ := by
  refine ⟨⟨(TauCeti.diagGL t : Matrix (Fin r) (Fin r) K) * A *
      ((TauCeti.diagGL t)⁻¹ : GL (Fin r) K), by
    rw [det_mul, det_mul, A.2, mul_one, ← det_mul, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, det_one]⟩, ?_, ?_⟩
  · rw [← map_inv, ← map_mul, ← map_mul]
    exact congrArg _ (Units.ext rfl)
  · change (TauCeti.diagGL t : Matrix (Fin r) (Fin r) K) * A *
      (((TauCeti.diagGL t)⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) = _
    rw [coe_units_inv, TauCeti.diagGL_coe]

include h in
theorem exists_levi_lift_of_three_le [Finite E] (hθ : Function.Surjective θ)
    (hC : θ.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 θ.ker) (hr : 3 ≤ r) :
    ∃ Y : Subgroup E, (∀ y ∈ Y, θ y = 1 → y = 1) ∧
      ∀ A : SpecialLinearGroup (Fin r) K, ∃ y ∈ Y,
        θ y = hypProj h r 1 (lHom h r (SpecialLinearGroup.toGL A)) := by
  have hK := card_eq_four h
  have := h.finite
  set ι : SpecialLinearGroup (Fin r) K →* hypPSU h r 1 :=
    (hypProj h r 1).comp ((lHom h r).comp SpecialLinearGroup.toGL) with hιdef
  have hι : Function.Injective ι := levi_injective
  have : Group.IsPerfect (SpecialLinearGroup (Fin r) K) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect hr
  have : Group.IsPerfect ι.range := Group.IsPerfect.range _
  set H := ι.range.comap θ with hH
  set Y := ⁅H, H⁆ with hY
  obtain ⟨θF, hθF, hθFι⟩ := SymplecticSixCover.exists_derivedComap_cover hθ ι hι
  have hθFker : ∀ z : Y, θF z = 1 ↔ θ z = 1 := fun z => by
    rw [← hθFι, ← map_one ι]
    exact hι.eq_iff.symm
  have : Group.IsPerfect Y := SymplecticSixCover.isPerfect_derivedComap hθ hC _
  have hcenF : θF.ker ≤ Subgroup.center Y := fun z hz => Subgroup.mem_center_iff.mpr fun g =>
    Subtype.ext (Subgroup.mem_center_iff.mp (hC ((hθFker z).mp hz)) g)
  have h2F : IsPGroup 2 θF.ker := fun z => by
    obtain ⟨n, hn⟩ := h2 ⟨(z : Y), (hθFker z).mp z.2⟩
    exact ⟨n, Subtype.ext (Subtype.ext (by
      simpa using congrArg (fun w : θ.ker => (w : E)) hn))⟩
  have hbot : θF.ker = ⊥ := by
    rcases (show r = 3 ∨ 4 ≤ r by omega) with rfl | hr4
    ·
      set α : (Fin 3 → Kˣ) →* MulAut E := (BinarySymplecticSix.liftConj hθ hC).comp
        ((hypProj h 3 1).comp ((lHom h 3).comp TauCeti.diagGL)) with hα
      have hαapp : ∀ t x, θ (α t x) = hypProj h 3 1 (lHom h 3 (TauCeti.diagGL t)) * θ x *
          (hypProj h 3 1 (lHom h 3 (TauCeti.diagGL t)))⁻¹ := fun t x =>
        BinarySymplecticSix.map_liftConj_apply hθ hC _ x
      have hαH : ∀ t, ∀ x ∈ H, α t x ∈ H := by
        rintro t x ⟨A, hxA⟩
        obtain ⟨B, hB, -⟩ := lHom_diagGL_conj (h := h) t A
        refine ⟨B, ?_⟩
        rw [hαapp, ← hxA]
        change hypProj h 3 1 (lHom h 3 (SpecialLinearGroup.toGL B)) = _
        rw [← hB]
        simp only [MonoidHom.comp_apply, map_mul, map_inv, hιdef]
      have hαY : ∀ t, ∀ x ∈ Y, α t x ∈ Y := fun t x hx => by
        have h1 : Y.map (α t).toMonoidHom ≤ Y := by
          rw [hY, Subgroup.map_commutator]
          refine Subgroup.commutator_mono ?_ ?_ <;>
            exact fun _ ⟨y, hy, hye⟩ => hye ▸ hαH t y hy
        exact h1 ⟨x, hx, rfl⟩
      let : MulDistribMulAction (Fin 3 → Kˣ) Y :=
        MulDistribMulAction.compHom Y (BinarySymplecticSix.restrictAct α Y hαY)
      have hsmul : ∀ (t : Fin 3 → Kˣ) (x : Y), ((t • x : Y) : E) = α t x := fun _ _ => rfl
      have hfix : ∀ t : Fin 3 → Kˣ, ∀ z ∈ θF.ker, t • z = z := fun t z hz => Subtype.ext (by
        rw [hsmul]
        exact BinarySymplecticSix.liftConj_apply_of_mem_ker hθ hC _ ((hθFker z).mp hz))
      have hd : ∀ (t : Fin 3 → Kˣ) (x : Y),
          ((θF (t • x) : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
            diagonal (fun i => (t i : K)) * (θF x : Matrix (Fin 3) (Fin 3) K) *
              (diagonal (fun i => (t i : K)))⁻¹ := by
        intro t x
        obtain ⟨B, hB, hBm⟩ := lHom_diagGL_conj (h := h) t (θF x)
        have h1 : ι (θF (t • x)) = ι B := by
          rw [hθFι, hsmul, hαapp, ← hθFι]
          change _ = hypProj h 3 1 (lHom h 3 (SpecialLinearGroup.toGL B))
          rw [← hB]
          simp only [MonoidHom.comp_apply, map_mul, map_inv, hιdef]
        rw [hι h1, hBm]
      exact (LinearCover.even_linear_three_diagonal_action_central_two_cover_trivial
        (by omega) θF hθF hcenF h2F hfix hd).1
    · exact LinearCover.ker_eq_bot_of_specialLinear (by omega) hr4 θF hθF hcenF h2F
  refine ⟨Y, fun y hy hy1 => ?_, fun A => ?_⟩
  · have hk : (⟨y, hy⟩ : Y) ∈ θF.ker := (hθFker _).mpr hy1
    rw [hbot, Subgroup.mem_bot] at hk
    exact congrArg Subtype.val hk
  · obtain ⟨z, hz⟩ := hθF A
    exact ⟨z, z.2, by rw [← hθFι, hz]; rfl⟩

include h in
theorem ker_eq_bot_of_sq_of_three_le [Finite E] [Group.IsPerfect E]
    (hθ : Function.Surjective θ) (hC : θ.ker ≤ Subgroup.center E)
    (hsq : ∀ c, θ c = 1 → c ^ 2 = 1) (hr : 3 ≤ r) : θ.ker = ⊥ := by
  have h2 : IsPGroup 2 θ.ker := fun c => ⟨1, Subtype.ext (by
    rw [Subgroup.coe_pow, pow_one, OneMemClass.coe_one]
    exact hsq c c.2)⟩
  obtain ⟨M₀, hM₀N, hM₀inj, hM₀surj, hM₀norm⟩ :=
    exists_radical_complement hθ hC (by omega) hsq
  obtain ⟨Y, hYinj, hYsurj⟩ := exists_levi_lift_of_three_le hθ hC h2 hr
  exact ker_eq_bot_of_lifts hθ hC h2 (by omega) M₀ hM₀N hM₀inj hM₀surj hM₀norm Y hYinj
    fun A _ => hYsurj A

include h in
theorem ker_eq_bot_of_hypPSU_of_three_le [Finite E] [Group.IsPerfect E]
    (hθ : Function.Surjective θ) (hC : θ.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 θ.ker)
    (hr : 3 ≤ r) : θ.ker = ⊥ :=
  ker_eq_bot_of_sq_reduction (fun _ hθ' hC' hsq => ker_eq_bot_of_sq_of_three_le hθ' hC' hsq hr)
    θ hθ hC h2

end CFSG.LocalAnalysis.ComponentInitial.UnitaryOddCover

namespace CFSG.LocalAnalysis.ComponentInitial

open CFSG.ClassicalGroups.UnitaryFlag

theorem even_odd_dimensional_unitary_prime_field_central_two_cover_trivial {E : Type*} {J : Type}
    [Group E] [Group J] [Finite E] [Finite J] [Group.IsPerfect E] (η : E →* J)
    (hη : Function.Surjective η) (hC : η.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 η.ker)
    {r : ℕ} (hr : 3 ≤ r) (hJ : CFSG.Blueprint.LieModel J .PSU (2 * r + 1) 2 1) :
    η.ker = ⊥ ∧ Function.Bijective η := by
  rcases hJ with ⟨-, -, K, _, _, hcard, ⟨e⟩⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · have h : UnitaryFieldData 2 1 K := ⟨Nat.prime_two, le_rfl, by rw [hcard]; norm_num⟩
    have := h.charP
    obtain ⟨R, hR⟩ := exists_isHypTransport (r := r) (ε := 1) h
    let φ : hypPSU h r 1 ≃* J := (hypPSUEquivStatedProj h hR (by omega)).trans e.symm
    set η' : E →* hypPSU h r 1 := φ.symm.toMonoidHom.comp η with hη'
    have hker : η'.ker = η.ker := by
      ext z
      exact φ.symm.map_eq_one_iff
    have hbot := UnitaryOddCover.ker_eq_bot_of_hypPSU_of_three_le (φ.symm.surjective.comp hη)
      (hker ▸ hC) (hker ▸ h2) hr
    rw [hker] at hbot
    exact ⟨hbot, (MonoidHom.ker_eq_bot_iff η).mp hbot, hη⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)

end CFSG.LocalAnalysis.ComponentInitial
