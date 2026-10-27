module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryOddCoverLargeComplement
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryOddCoverSylow

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryOddCover

open Matrix CFSG.ClassicalGroups.UnitaryFlag MatrixExtension
open scoped commutatorElement

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K} {r : ℕ}

theorem levi_injective_even :
    Function.Injective ((hypProj h r 1).comp ((lHom h r).comp SpecialLinearGroup.toGL)) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro A hA
  have h1 := eq_one_of_hypProj_lHom (h := h) (A := SpecialLinearGroup.toGL A) A.2 hA
  exact Subgroup.mem_bot.mpr (SpecialLinearGroup.toGL_injective (h1.trans (map_one _).symm))

theorem lHom_diagGL_conj_even (t : Fin r → Kˣ) (A : SpecialLinearGroup (Fin r) K) :
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

variable [CharP K 2] {E : Type*} [Group E] {θ : E →* hypPSU h r 1}

theorem exists_levi_lift_even [Finite E] (hθ : Function.Surjective θ)
    (hC : θ.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 θ.ker) (hf : 2 ≤ f) (hr : 2 ≤ r) :
    ∃ Y : Subgroup E, (∀ y ∈ Y, θ y = 1 → y = 1) ∧
      ∀ A : SpecialLinearGroup (Fin r) K, ∃ y ∈ Y,
        θ y = hypProj h r 1 (lHom h r (SpecialLinearGroup.toGL A)) := by
  have := h.finite
  have hcard : Nat.card K = 2 ^ (2 * f) := h.card
  have hK16 : 16 ≤ Nat.card K := by
    rw [hcard]
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ (2 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)
  set ι : SpecialLinearGroup (Fin r) K →* hypPSU h r 1 :=
    (hypProj h r 1).comp ((lHom h r).comp SpecialLinearGroup.toGL) with hιdef
  have hι : Function.Injective ι := levi_injective_even
  have : Group.IsPerfect (SpecialLinearGroup (Fin r) K) := by
    rcases (show r = 2 ∨ 3 ≤ r by omega) with rfl | hr3
    · have : Fintype K := Fintype.ofFinite K
      obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset K)) (n := 4)
        (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; omega)
      exact CFSG.LinearGroups.special_linear_isPerfect le_rfl (Or.inr ⟨s, hs⟩)
    · exact CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect hr3
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
    rcases (show r = 2 ∨ r = 3 ∨ 4 ≤ r by omega) with rfl | rfl | hr4
    · exact CFSG.ShultStronglyClosedTI.large_even_linear_central_two_cover_kernel_eq_bot (2 * f)
        (by omega) hcard θF hθF hcenF h2F
    ·
      set α : (Fin 3 → Kˣ) →* MulAut E := (BinarySymplecticSix.liftConj hθ hC).comp
        ((hypProj h 3 1).comp ((lHom h 3).comp TauCeti.diagGL)) with hα
      have hαapp : ∀ t x, θ (α t x) = hypProj h 3 1 (lHom h 3 (TauCeti.diagGL t)) * θ x *
          (hypProj h 3 1 (lHom h 3 (TauCeti.diagGL t)))⁻¹ := fun t x =>
        BinarySymplecticSix.map_liftConj_apply hθ hC _ x
      have hαH : ∀ t, ∀ x ∈ H, α t x ∈ H := by
        rintro t x ⟨A, hxA⟩
        obtain ⟨B, hB, -⟩ := lHom_diagGL_conj_even (h := h) t A
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
        obtain ⟨B, hB, hBm⟩ := lHom_diagGL_conj_even (h := h) t (θF x)
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

theorem ker_eq_bot_of_hypPSU_large [Finite E] [Group.IsPerfect E] (hθ : Function.Surjective θ)
    (hC : θ.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 θ.ker) (hf : 2 ≤ f) (hr : 2 ≤ r) :
    θ.ker = ⊥ := by
  obtain ⟨M₀, hM₀N, hM₀inj, hM₀surj, hM₀norm⟩ := exists_radical_complement_even hθ hC hf hr h2
  obtain ⟨Y, hYinj, hYsurj⟩ := exists_levi_lift_even hθ hC h2 hf hr
  exact ker_eq_bot_of_lifts hθ hC h2 (by omega) M₀ hM₀N hM₀inj hM₀surj hM₀norm Y hYinj
    fun A _ => hYsurj A

end CFSG.LocalAnalysis.ComponentInitial.UnitaryOddCover

namespace CFSG.LocalAnalysis.ComponentInitial

open CFSG.ClassicalGroups.UnitaryFlag

theorem even_odd_dimensional_unitary_catalog_perfect_central_two_cover_trivial {E : Type*}
    {J : Type} [Group E] [Group J] [Finite E] [Finite J] [Group.IsPerfect E] (η : E →* J)
    (hη : Function.Surjective η) (hC : η.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 η.ker)
    {r f : ℕ} (hr : 2 ≤ r) (hf : 2 ≤ f)
    (hJ : CFSG.Blueprint.LieModel J .PSU (2 * r + 1) 2 f) :
    η.ker = ⊥ ∧ Function.Bijective η := by
  rcases hJ with ⟨-, -, K, _, _, hcard, ⟨e⟩⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · have h : UnitaryFieldData 2 f K := ⟨Nat.prime_two, by omega, by rw [hcard, ← pow_mul,
      mul_comm]⟩
    have := h.charP
    obtain ⟨R, hR⟩ := exists_isHypTransport (r := r) (ε := 1) h
    let φ : hypPSU h r 1 ≃* J := (hypPSUEquivStatedProj h hR (by omega)).trans e.symm
    set η' : E →* hypPSU h r 1 := φ.symm.toMonoidHom.comp η with hη'
    have hker : η'.ker = η.ker := by
      ext z
      exact φ.symm.map_eq_one_iff
    have hbot := UnitaryOddCover.ker_eq_bot_of_hypPSU_large (φ.symm.surjective.comp hη)
      (hker ▸ hC) (hker ▸ h2) hf hr
    rw [hker] at hbot
    exact ⟨hbot, (MonoidHom.ker_eq_bot_iff η).mp hbot, hη⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)

end CFSG.LocalAnalysis.ComponentInitial
