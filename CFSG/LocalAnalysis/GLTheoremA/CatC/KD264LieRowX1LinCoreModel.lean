module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.PumpDefChar

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Model

open CFSG.Open

abbrev F4 : Type := GaloisField 2 2

noncomputable instance : Fintype F4 := Fintype.ofFinite F4

theorem card_F4 : Fintype.card F4 = 4 := by
  rw [← Nat.card_eq_fintype_card, GaloisField.card 2 2 (by norm_num)]
  norm_num

theorem finrank_F4 : Module.finrank (ZMod 2) F4 = 2 := GaloisField.finrank 2 (by norm_num)

theorem exists_omega : ∃ ω : F4, ω ≠ 1 ∧ ω ^ 3 = 1 ∧ ω ^ 2 + ω + 1 = 0 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hcard : Fintype.card F4ˣ = 3 := by
    rw [Fintype.card_units, card_F4]
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card 3 (by rw [hcard])
  have hu3 : u ^ 3 = 1 := by rw [← hu]; exact pow_orderOf_eq_one u
  have hu1 : u ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hu
    norm_num at hu
  refine ⟨(u : F4), fun h => hu1 (Units.ext h), by rw [← Units.val_pow_eq_pow_val, hu3, Units.val_one],
    ?_⟩
  have hne : (u : F4) - 1 ≠ 0 := fun h => hu1 (Units.ext (by simpa [sub_eq_zero] using h))
  have h3 : ((u : F4) - 1) * ((u : F4) ^ 2 + (u : F4) + 1) = 0 := by
    have : ((u : F4) ^ 3 = 1) := by rw [← Units.val_pow_eq_pow_val, hu3, Units.val_one]
    linear_combination this
  exact (mul_eq_zero.1 h3).resolve_left hne

@[expose] noncomputable def omega : F4 := Classical.choose exists_omega

theorem omega_ne_one : omega ≠ 1 := (Classical.choose_spec exists_omega).1

theorem omega_cube : omega ^ 3 = 1 := (Classical.choose_spec exists_omega).2.1

theorem omega_quad : omega ^ 2 + omega + 1 = 0 := (Classical.choose_spec exists_omega).2.2

theorem omega_sq : omega ^ 2 = omega + 1 := by
  have h := omega_quad
  have h2 : (2 : F4) = 0 := CharTwo.two_eq_zero
  linear_combination h - (omega + 1) * h2

theorem char_two_neg (x : F4) : -x = x := CharTwo.neg_eq x

theorem li_one_omega : LinearIndependent (ZMod 2) ![(1 : F4), omega] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have hZ : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  rcases hZ s with rfl | rfl <;> rcases hZ t with rfl | rfl
  · exact ⟨rfl, rfl⟩
  · exfalso
    simp only [zero_smul, one_smul, zero_add] at hst
    have h0 : omega = 0 := hst
    have h3 := omega_cube
    rw [h0] at h3
    norm_num at h3
  · exfalso
    simp only [one_smul, zero_smul, add_zero] at hst
    exact one_ne_zero hst
  · exfalso
    simp only [one_smul] at hst
    have h1 : omega = 1 := (eq_neg_of_add_eq_zero_right hst).trans (char_two_neg 1)
    exact omega_ne_one h1

@[expose] noncomputable def basisF4 : Module.Basis (Fin 2) (ZMod 2) F4 :=
  Module.Basis.mk (v := ![(1 : F4), omega]) li_one_omega (by
    have hspan : Submodule.span (ZMod 2) (Set.range ![(1 : F4), omega]) = ⊤ :=
      li_one_omega.span_eq_top_of_card_eq_finrank (by rw [finrank_F4, Fintype.card_fin])
    exact hspan.ge)

theorem basisF4_zero : basisF4 0 = 1 := by
  simp [basisF4]

theorem basisF4_one : basisF4 1 = omega := by
  simp [basisF4]

theorem F4_eq_comb (x : F4) :
    x = (basisF4.repr x 0) • (1 : F4) + (basisF4.repr x 1) • omega := by
  conv_lhs => rw [← basisF4.sum_repr x]
  rw [Fin.sum_univ_two, basisF4_zero, basisF4_one]

theorem smul_decomp (x : F4) (c : Fin 2 → F4) :
    x • c = (basisF4.repr x 0) • c + (basisF4.repr x 1) • (omega • c) := by
  conv_lhs => rw [F4_eq_comb x]
  rw [add_smul, smul_assoc, smul_assoc, one_smul]

@[expose] noncomputable def F4lin : GL (Fin 2) F4 →* ((Fin 2 → F4) ≃ₗ[F4] (Fin 2 → F4)) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv F4 (Fin 2 → F4)).toMonoidHom.comp
    (Matrix.GeneralLinearGroup.toLin : GL (Fin 2) F4 ≃* _).toMonoidHom

@[expose] noncomputable def actZ : GL (Fin 2) F4 →* ((Fin 2 → F4) ≃ₗ[ZMod 2] (Fin 2 → F4)) :=
  MonoidHom.mk' (fun A => (F4lin A).restrictScalars (ZMod 2)) (fun A B => by
    apply LinearEquiv.ext
    intro c
    rw [map_mul]
    rfl)

theorem actZ_apply (A : GL (Fin 2) F4) (c : Fin 2 → F4) : actZ A c = F4lin A c := rfl

theorem actZ_injective : Function.Injective actZ := by
  rw [injective_iff_map_eq_one]
  intro A hA
  have hcoe : ∀ c : Fin 2 → F4, Matrix.mulVec (A : Matrix (Fin 2) (Fin 2) F4) c = c := by
    intro c
    have h1 : actZ A c = c := by
      rw [hA]
      rfl
    have h2 : actZ A c = Matrix.mulVec (A : Matrix (Fin 2) (Fin 2) F4) c := by
      rw [actZ_apply]
      rfl
    rw [← h2, h1]
  apply Units.ext
  rw [Units.val_one]
  have hlin : Matrix.toLin' (A : Matrix (Fin 2) (Fin 2) F4) = LinearMap.id := by
    apply LinearMap.ext
    intro c
    rw [Matrix.toLin'_apply, hcoe c, LinearMap.id_apply]
  calc (A : Matrix (Fin 2) (Fin 2) F4)
      = LinearMap.toMatrix' (Matrix.toLin' (A : Matrix (Fin 2) (Fin 2) F4)) :=
        (LinearMap.toMatrix'_toLin' _).symm
    _ = 1 := by rw [hlin, LinearMap.toMatrix'_id]

theorem commutant_lemma (h : (Fin 2 → F4) ≃ₗ[ZMod 2] (Fin 2 → F4))
    (hω : ∀ c, h (omega • c) = omega • h c) : ∃ A : GL (Fin 2) F4, actZ A = h := by
  let hF : (Fin 2 → F4) →ₗ[F4] (Fin 2 → F4) :=
    { toFun := h
      map_add' := h.map_add
      map_smul' := fun x c => by
        simp only [RingHom.id_apply]
        rw [smul_decomp x c, map_add, map_smul, map_smul, hω, smul_decomp x (h c)] }
  have hbij : Function.Bijective hF := ⟨h.injective, h.surjective⟩
  let e : (Fin 2 → F4) ≃ₗ[F4] (Fin 2 → F4) := LinearEquiv.ofBijective hF hbij
  refine ⟨Matrix.GeneralLinearGroup.toLin.symm ((LinearMap.GeneralLinearGroup.generalLinearEquiv
    F4 (Fin 2 → F4)).symm e), ?_⟩
  apply LinearEquiv.ext
  intro c
  rw [actZ_apply]
  show (LinearMap.GeneralLinearGroup.generalLinearEquiv F4 (Fin 2 → F4))
    (Matrix.GeneralLinearGroup.toLin (Matrix.GeneralLinearGroup.toLin.symm
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv F4 (Fin 2 → F4)).symm e))) c = h c
  rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  rfl

theorem center_sl_F4 : Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F4) = ⊥ := by
  rw [← CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center, eq_bot_iff]
  intro A hA
  obtain ⟨c, hc, hAc⟩ := (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.mem_scalars).1 hA
  have h2 : (2 : F4) = 0 := CharTwo.two_eq_zero
  have hc2 : (c : F4) ^ 2 = 1 := by
    have := congrArg (fun u : F4ˣ => (u : F4)) hc
    simpa [Units.val_pow_eq_pow_val] using this
  have hc1 : (c : F4) = 1 := by
    have hsq : ((c : F4) - 1) ^ 2 = 0 := by linear_combination hc2 + (1 - (c : F4)) * h2
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hsq
    exact sub_eq_zero.1 this
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [hAc, hc1]
  ext i j
  simp [Matrix.scalar_apply, Matrix.one_apply]

theorem isQuasisimple_sl_F4 : CFSG.Open.IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) F4) := by
  refine ⟨?_, ?_⟩
  · have hP := CFSG.LinearGroups.special_linear_isPerfect (K := F4) (n := 2) le_rfl
      (Or.inr ⟨Finset.univ, by rw [Finset.card_univ, card_F4]⟩)
    exact Group.isPerfect_def.1 hP
  · have hS : IsSimpleGroup (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 2 F4) :=
      CFSG.LocalAnalysis.GLTheoremB.MovingAround.PumpDefChar.isSimpleGroup_projectiveSL le_rfl
        (by rw [GaloisField.card 2 2 (by norm_num)]; norm_num)
    exact (MulEquiv.isSimpleGroup_congr (QuotientGroup.quotientMulEquivOfEq
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center 2 F4))).1 hS

@[expose] noncomputable def mtilde : Matrix.SpecialLinearGroup (Fin 2) F4 :=
  ⟨!![0, 1; 1, 1], by
    rw [Matrix.det_fin_two_of]
    have h2 : (2 : F4) = 0 := CharTwo.two_eq_zero
    linear_combination (-1 : F4) * h2⟩

theorem mtilde_ne_one : mtilde ≠ 1 := by
  intro h
  have := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) F4 => (A : Matrix (Fin 2) (Fin 2) F4) 0 1) h
  simp [mtilde] at this

theorem mtilde_cube : mtilde ^ 3 = 1 := by
  have h2 : (1 : F4) + 1 = 0 := CharTwo.add_self_eq_zero 1
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
  show (!![(0 : F4), 1; 1, 1]) ^ 3 = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, h2]

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Model

end
