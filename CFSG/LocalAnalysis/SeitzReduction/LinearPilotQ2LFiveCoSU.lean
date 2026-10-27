module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveCoHerm
import all CFSG.Fischer.F4

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix CFSG.Fischer

section Monomial

@[expose] def wpowF4 : Fin 3 → F4
  | 0 => 1
  | 1 => F4.ω
  | 2 => F4.ω * F4.ω

@[expose] def monoExp (a b : Fin 3) : Fin 3 → Fin 3 := ![a, b, -(a + b)]

@[expose] def monoF4 (a b k : Fin 3) : Matrix (Fin 3) (Fin 3) F4 :=
  Matrix.of fun i j => if j = i + k then wpowF4 (monoExp a b i) else 0

theorem monoF4_det : ∀ a b k : Fin 3, (monoF4 a b k).det = 1 := by
  intro a b k
  rw [Matrix.det_fin_three]
  revert a b k
  decide +kernel

theorem monoF4_mul : ∀ a b k a' b' k' : Fin 3, monoF4 a b k * monoF4 a' b' k' =
    monoF4 (a + monoExp a' b' k) (b + monoExp a' b' (1 + k)) (k + k') := by
  decide +kernel

theorem monoF4_zero : monoF4 0 0 0 = 1 := by decide +kernel

theorem monoF4_exists_inv : ∀ a b k : Fin 3, ∃ a' b' k' : Fin 3,
    monoF4 a b k * monoF4 a' b' k' = 1 := by
  decide +kernel

theorem monoF4_fix : ∀ a b k : Fin 3,
    monoF4 a b k * ((frobenius F4 2).mapMatrix (monoF4 a b k))ᵀ = 1 := by
  intro a b k
  have h : ∀ M : Matrix (Fin 3) (Fin 3) F4, (frobenius F4 2).mapMatrix M = M.map (· ^ 2) := by
    intro M
    ext i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.map_apply, frobenius_def]
  rw [h]
  revert a b k
  decide +kernel

theorem monoF4_injective : ∀ a b k a' b' k' : Fin 3, monoF4 a b k = monoF4 a' b' k' →
    a = a' ∧ b = b' ∧ k = k' := by
  decide +kernel

@[expose] def monoSL (p : Fin 3 × Fin 3 × Fin 3) : SpecialLinearGroup (Fin 3) F4 :=
  ⟨monoF4 p.1 p.2.1 p.2.2, monoF4_det _ _ _⟩

theorem monoSL_injective : Function.Injective monoSL := by
  rintro ⟨a, b, k⟩ ⟨a', b', k'⟩ h
  obtain ⟨rfl, rfl, rfl⟩ := monoF4_injective a b k a' b' k' (congrArg Subtype.val h)
  rfl

@[expose] def monoSubgroup : Subgroup (SpecialLinearGroup (Fin 3) F4) where
  carrier := Set.range monoSL
  mul_mem' := by
    rintro _ _ ⟨⟨a, b, k⟩, rfl⟩ ⟨⟨a', b', k'⟩, rfl⟩
    refine ⟨⟨a + monoExp a' b' k, b + monoExp a' b' (1 + k), k + k'⟩, Subtype.ext ?_⟩
    rw [Matrix.SpecialLinearGroup.coe_mul]
    exact (monoF4_mul a b k a' b' k').symm
  one_mem' := ⟨⟨0, 0, 0⟩, Subtype.ext monoF4_zero⟩
  inv_mem' := by
    rintro _ ⟨⟨a, b, k⟩, rfl⟩
    obtain ⟨a', b', k', h⟩ := monoF4_exists_inv a b k
    refine ⟨⟨a', b', k'⟩, ?_⟩
    symm
    refine inv_eq_of_mul_eq_one_right (Subtype.ext ?_)
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
    exact h

theorem card_monoSubgroup : Nat.card monoSubgroup = 27 := by
  have h : Nat.card monoSubgroup = Nat.card (Set.range monoSL) := rfl
  rw [h, Nat.card_range_of_injective monoSL_injective, Nat.card_eq_fintype_card]
  rfl

end Monomial

section Fix

theorem graphFieldSL_monoSL (p : Fin 3 × Fin 3 × Fin 3) :
    graphFieldSL F4 (monoSL p) = monoSL p := by
  have h1 : monoSL p * graphFieldSL F4 (monoSL p)⁻¹ = 1 := by
    apply Subtype.ext
    rw [coe_mul_graphFieldSL_inv, Matrix.SpecialLinearGroup.coe_one]
    exact monoF4_fix _ _ _
  have h2 : graphFieldSL F4 (monoSL p)⁻¹ = (monoSL p)⁻¹ := eq_inv_of_mul_eq_one_right h1
  rw [map_inv] at h2
  exact inv_injective h2

theorem twentySeven_dvd_card_eqLocus_graphFieldSL_F4 :
    27 ∣ Nat.card ((graphFieldSL F4).eqLocus (MonoidHom.id (SpecialLinearGroup (Fin 3) F4))) := by
  rw [← card_monoSubgroup]
  refine Subgroup.card_dvd_of_le ?_
  rintro _ ⟨p, rfl⟩
  exact graphFieldSL_monoSL p

theorem card_eqLocus_conj_graphFieldSL_F4 (B : SpecialLinearGroup (Fin 3) F4)
    (hB : ∀ y, B * graphFieldSL F4 (B * graphFieldSL F4 y * B⁻¹) * B⁻¹ = y) :
    Nat.card (((MulAut.conj B).toMonoidHom.comp (graphFieldSL F4)).eqLocus
        (MonoidHom.id (SpecialLinearGroup (Fin 3) F4))) =
      Nat.card ((graphFieldSL F4).eqLocus (MonoidHom.id (SpecialLinearGroup (Fin 3) F4))) := by
  have hθθ : ∀ y, graphFieldSL F4 (graphFieldSL F4 y) = y := graphFieldSL_graphFieldSL f4_sq_sq
  set θ := graphFieldSL F4 with hθdef
  set c := B * θ B with hc
  have hcC : ∀ y, c * y = y * c := by
    intro y
    have h1 := hB y
    rw [map_mul, map_mul, map_inv, hθθ] at h1
    calc c * y = (B * (θ B * y * (θ B)⁻¹) * B⁻¹) * (B * θ B) := by rw [hc]; group
      _ = y * c := by rw [h1]
  have hθc : θ c = c := by
    rw [hc, map_mul, hθθ]
    calc θ B * B = B⁻¹ * (c * B) := by rw [hc]; group
      _ = B⁻¹ * (B * c) := by rw [hcC B]
      _ = B * θ B := by rw [hc]; group
  have hc3 : c * c * c = 1 := by
    have hcZ : c ∈ Subgroup.center (SpecialLinearGroup (Fin 3) F4) :=
      Subgroup.mem_center_iff.2 fun g => (hcC g).symm
    obtain ⟨r, hr, hrc⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hcZ
    rw [Fintype.card_fin] at hr
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, ← hrc, ← map_mul,
      ← map_mul, Matrix.SpecialLinearGroup.coe_one, show r * r * r = r ^ 3 by ring, hr, map_one]
  have hB' : c * B * θ (c * B) = 1 := by
    rw [map_mul, hθc]
    calc c * B * (c * θ B) = c * (B * c) * θ B := by group
      _ = c * (c * B) * θ B := by rw [hcC B]
      _ = c * c * c := by rw [hc]; group
      _ = 1 := hc3
  obtain ⟨C, hC⟩ := exists_eq_inv_mul_graphFieldSL _ hB'
  refine Nat.card_congr (Equiv.subtypeEquiv (MulAut.conj C).toEquiv fun y => ?_)
  change B * θ y * B⁻¹ = y ↔ θ (C * y * C⁻¹) = C * y * C⁻¹
  have hBy : B * θ y * B⁻¹ = (c * B) * θ y * (c * B)⁻¹ := by
    calc B * θ y * B⁻¹ = B * θ y * B⁻¹ * c * c⁻¹ := by group
      _ = c * (B * θ y * B⁻¹) * c⁻¹ := by rw [hcC (B * θ y * B⁻¹)]
      _ = (c * B) * θ y * (c * B)⁻¹ := by group
  rw [hBy, hC, map_mul, map_mul, map_inv]
  constructor
  · intro h
    calc θ C * θ y * (θ C)⁻¹ = C * ((C⁻¹ * θ C) * θ y * (C⁻¹ * θ C)⁻¹) * C⁻¹ := by group
      _ = C * y * C⁻¹ := by rw [h]
  · intro h
    calc (C⁻¹ * θ C) * θ y * (C⁻¹ * θ C)⁻¹ = C⁻¹ * (θ C * θ y * (θ C)⁻¹) * C := by group
      _ = C⁻¹ * (C * y * C⁻¹) * C := by rw [h]
      _ = y := by group

end Fix

section Transport

theorem sLThreeGraphFieldFixInput : SLThreeGraphFieldFixInput := by
  intro F _ _ hF B hB
  have : Finite F := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = Fintype.card F4 := by
    rw [F4.card, ← Nat.card_eq_fintype_card, hF]
  set ι : F ≃+* F4 := FiniteField.ringEquivOfCardEq hcard with hι
  set Φ : SpecialLinearGroup (Fin 3) F ≃* SpecialLinearGroup (Fin 3) F4 :=
    { toFun := Matrix.SpecialLinearGroup.map ι.toRingHom
      invFun := Matrix.SpecialLinearGroup.map ι.symm.toRingHom
      left_inv := fun M => by
        ext i j
        simp [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
      right_inv := fun M => by
        ext i j
        simp [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
      map_mul' := fun M N => map_mul _ M N } with hΦ
  have hΦapply : ∀ (M : SpecialLinearGroup (Fin 3) F) i j, (Φ M) i j = ι (M i j) := fun M i j => by
    simp [hΦ, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
  have hΦθ : ∀ M, Φ (graphFieldSL F M) = graphFieldSL F4 (Φ M) := by
    intro M
    ext i j
    rw [hΦapply, graphFieldSL_apply, graphFieldSL_apply, ← map_inv, hΦapply, map_pow]
  have hΦα : ∀ y, Φ (B * graphFieldSL F y * B⁻¹) = Φ B * graphFieldSL F4 (Φ y) * (Φ B)⁻¹ := by
    intro y
    rw [map_mul, map_mul, map_inv, hΦθ]
  have hB' : ∀ y, Φ B * graphFieldSL F4 (Φ B * graphFieldSL F4 y * (Φ B)⁻¹) * (Φ B)⁻¹ = y := by
    intro y
    obtain ⟨z, rfl⟩ := Φ.surjective y
    rw [← hΦα, ← hΦα, hB z]
  have hcardΦ : Nat.card (((MulAut.conj B).toMonoidHom.comp (graphFieldSL F)).eqLocus
        (MonoidHom.id (SpecialLinearGroup (Fin 3) F))) =
      Nat.card (((MulAut.conj (Φ B)).toMonoidHom.comp (graphFieldSL F4)).eqLocus
        (MonoidHom.id (SpecialLinearGroup (Fin 3) F4))) := by
    refine Nat.card_congr (Equiv.subtypeEquiv Φ.toEquiv fun y => ?_)
    change B * graphFieldSL F y * B⁻¹ = y ↔
      Φ B * graphFieldSL F4 (Φ y) * (Φ B)⁻¹ = Φ y
    rw [← hΦα]
    exact Φ.injective.eq_iff.symm
  rw [hcardΦ, card_eqLocus_conj_graphFieldSL_F4 _ hB']
  exact twentySeven_dvd_card_eqLocus_graphFieldSL_F4

end Transport

end CFSG.SeitzReduction.LinearPilot
