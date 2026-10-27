module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeRecogMain

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open LinearFlag
open CFSG.QuasithinUnique.Lin2.Five (tauSp)
open CFSG.SeitzReduction.F4Pilot (statedSpMap centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG symm_mem_modelToG)
open CFSG.Quasithin (perfectCore perfectCore_perfect)
open scoped commutatorElement

section Generic

theorem mul_inv_comm_of_central {E : Type*} [Group E] {b c : E} (hb : ∀ g, g * b = b * g) :
    b * c⁻¹ = c⁻¹ * b :=
  (hb c⁻¹).symm

theorem commutatorElement_mul_of_central {E : Type*} [Group E] (c d a b : E)
    (ha : ∀ g, g * a = a * g) (hb : ∀ g, g * b = b * g) : ⁅c * a, d * b⁆ = ⁅c, d⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  calc c * a * (d * b) * (c * a)⁻¹ * (d * b)⁻¹
      = c * (a * (d * b * a⁻¹)) * c⁻¹ * (b⁻¹ * d⁻¹) := by group
    _ = c * (d * b * a⁻¹ * a) * c⁻¹ * (b⁻¹ * d⁻¹) := by rw [← ha (d * b * a⁻¹)]
    _ = c * d * (b * c⁻¹) * b⁻¹ * d⁻¹ := by group
    _ = c * d * (c⁻¹ * b) * b⁻¹ * d⁻¹ := by rw [mul_inv_comm_of_central hb]
    _ = c * d * c⁻¹ * d⁻¹ := by group

theorem injective_of_section_of_isPerfect {E P : Type*} [Group E] [Group P] [Group.IsPerfect E]
    (ρ : E →* P) (hker : ρ.ker ≤ center E) (s : P →* E) (hs : ∀ g, ρ (s g) = g) :
    Function.Injective ρ := by
  have hdec : ∀ x : E, (s (ρ x))⁻¹ * x ∈ center E := fun x => hker (by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hs, inv_mul_cancel])
  have hcomm : commutator E ≤ s.range := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    refine ⟨⁅ρ x, ρ y⁆, ?_⟩
    set a := (s (ρ x))⁻¹ * x with ha
    set b := (s (ρ y))⁻¹ * y with hb
    have hx : x = s (ρ x) * a := by rw [ha, mul_inv_cancel_left]
    have hy : y = s (ρ y) * b := by rw [hb, mul_inv_cancel_left]
    have e1 : ∀ g, g * a = a * g := fun g => mem_center_iff.1 (hdec x) g
    have e2 : ∀ g, g * b = b * g := fun g => mem_center_iff.1 (hdec y) g
    calc s ⁅ρ x, ρ y⁆ = ⁅s (ρ x), s (ρ y)⁆ := map_commutatorElement s _ _
      _ = ⁅s (ρ x) * a, s (ρ y) * b⁆ := (commutatorElement_mul_of_central _ _ _ _ e1 e2).symm
      _ = ⁅x, y⁆ := by rw [← hx, ← hy]
  rw [injective_iff_map_eq_one]
  intro x hx
  have hxs : x ∈ s.range := hcomm (by rw [Group.IsPerfect.commutator_eq_top]; exact mem_top x)
  obtain ⟨p, rfl⟩ := hxs
  rw [hs] at hx
  rw [hx, map_one]

end Generic

section Lift

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

omit [Finite K] in
theorem exists_mulEquiv_of_spThreeLinearNormalized {e : L ≃* StatedSp 3 K} {t : G} {f : ℕ}
    (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) {k : Fin 3} {b : Bool}
    (h : SpThreeLinearNormalized e t f k b) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (σ : K ≃+* F)
      (Φ : Matrix.SpecialLinearGroup (Fin (2 * 2)) F ≃* neighbourCore e k),
      Nat.card F = 2 ^ f ∧
      (∀ x : StatedSp 2 K,
        ((Φ (spModelSL 2 F (statedSpMap (σ : K →+* F) 2 (cond b (tauSp x) x))) :
          neighbourCore e k) : G) =
          ((e.symm (complSpEquiv k x : complSp K k) : L) : G)) ∧
      ∀ y : Matrix.SpecialLinearGroup (Fin (2 * 2)) F,
        t * (Φ y : G) * t⁻¹ = (Φ ((slFourEquivProj F).symm
          ((conjAut (2 * 2) F (spBlockSwapGL 2 F) * dualAut (2 * 2) F) (proj (2 * 2) F y))) :
            G) := by
  obtain ⟨F, _, _, _, σ, ρ, hN, hF, hρ, hker, -, hN1, hN3⟩ := h
  have : Group.IsPerfect (centralizerPerfectCore (modelToG e (rootTorusSp K k))) :=
    Subgroup.isPerfect_iff.2 (perfectCore_perfect _)
  set ρ' : centralizerPerfectCore (modelToG e (rootTorusSp K k)) →*
      Matrix.SpecialLinearGroup (Fin (2 * 2)) F :=
    (slFourEquivProj F).symm.toMonoidHom.comp ρ with hρ'
  have hρ's : Function.Surjective ρ' := (slFourEquivProj F).symm.surjective.comp hρ
  have hker' : ρ'.ker ≤ center (centralizerPerfectCore (modelToG e (rootTorusSp K k))) := by
    intro y hy
    apply hker
    rw [MonoidHom.mem_ker] at hy ⊢
    have h1 : (slFourEquivProj F).symm (ρ y) = 1 := hy
    rwa [MulEquiv.map_eq_one_iff] at h1
  have hF2 : Nat.card F ≠ 2 := by
    rw [hF]
    intro h2
    have : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    omega
  have hF3 : Nat.card F ≠ 3 := by
    rw [hF]
    intro h3
    have : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    omega
  have hsep : CFSG.LieType.Steinberg.CentralExt.SLClosed.Separating 3 F :=
    CFSG.LieType.Steinberg.CentralExt.SLClosed.separating_of_card (by norm_num) hF2
      (fun h' => absurd h'.1 (by norm_num)) (fun h' => hF3 h'.2)
  obtain ⟨s, hs⟩ := CFSG.LieType.Steinberg.CentralExt.SLClosed.sl_exists_section_of_separating
    (m := 3) (F := F) (by norm_num) hsep (π := ρ') hρ's hker'
  have hinj : Function.Injective ρ' := injective_of_section_of_isPerfect ρ' hker' s hs
  set Φ := (MulEquiv.ofBijective ρ' ⟨hinj, hρ's⟩).symm with hΦ
  have hΦρ : ∀ y : centralizerPerfectCore (modelToG e (rootTorusSp K k)), Φ (ρ' y) = y :=
    fun y => by
      rw [hΦ, MulEquiv.symm_apply_eq]
      rfl
  have hρproj : ∀ y : centralizerPerfectCore (modelToG e (rootTorusSp K k)),
      ρ y = proj (2 * 2) F (ρ' y) := fun y => by
    rw [hρ']
    change ρ y = slFourEquivProj F ((slFourEquivProj F).symm (ρ y))
    rw [MulEquiv.apply_symm_apply]
  refine ⟨F, inferInstance, inferInstance, inferInstance, σ, Φ, hF, fun x => ?_, fun y => ?_⟩
  · have hmem : ((e.symm (complSpEquiv k x : complSp K k) : L) : G) ∈
        centralizerPerfectCore (modelToG e (rootTorusSp K k)) :=
      modelToG_complSp_le_neighbourCore e (hKc ▸ four_le_two_pow hf) (by norm_num) k
        (symm_mem_modelToG e (complSpEquiv k x).2)
    have h1 := hN1 x ⟨_, hmem⟩ rfl
    have h2 : ρ' ⟨_, hmem⟩ = spModelSL 2 F (statedSpMap (σ : K →+* F) 2 (cond b (tauSp x) x)) := by
      apply proj_two_mul_two_injective (F := F)
      rw [← hρproj, h1, spModelPSL_apply]
    rw [← h2]
    exact congrArg Subtype.val (hΦρ ⟨_, hmem⟩)
  · obtain ⟨y₀, rfl⟩ := hρ's y
    have h0 : ((Φ (ρ' y₀) : centralizerPerfectCore (modelToG e (rootTorusSp K k))) : G) =
        (y₀ : G) := congrArg Subtype.val (hΦρ y₀)
    have h1 := hN3 y₀
    have h2 : ρ' ((centralizerPerfectCore (modelToG e (rootTorusSp K k))).normalizerMonoidHom
        ⟨t, hN⟩ y₀) = (slFourEquivProj F).symm
        ((conjAut (2 * 2) F (spBlockSwapGL 2 F) * dualAut (2 * 2) F) (proj (2 * 2) F (ρ' y₀))) := by
      rw [← hρproj, ← h1]
      rfl
    have h3 : ((Φ (ρ' ((centralizerPerfectCore (modelToG e (rootTorusSp K k))).normalizerMonoidHom
        ⟨t, hN⟩ y₀)) : centralizerPerfectCore (modelToG e (rootTorusSp K k))) : G) =
        t * (y₀ : G) * t⁻¹ := by
      rw [hΦρ, Subgroup.normalizerMonoidHom_apply_apply_coe]
    change t * ((Φ (ρ' y₀) : centralizerPerfectCore (modelToG e (rootTorusSp K k))) : G) * t⁻¹ =
      ((Φ ((slFourEquivProj F).symm ((conjAut (2 * 2) F (spBlockSwapGL 2 F) *
        dualAut (2 * 2) F) (proj (2 * 2) F (ρ' y₀)))) :
          centralizerPerfectCore (modelToG e (rootTorusSp K k))) : G)
    rw [← h2, h3, h0]

end Lift

end CFSG.SeitzReduction.SymplecticPilot
