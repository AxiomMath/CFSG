module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeAut
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.Lie.D4Levi

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.Lie

open CFSG.EvenSmallLie.OmegaEight CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Steinberg CFSG.LieType.CurtisTits CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.LocalAnalysis.ComponentInitial

theorem cidx_injective : Function.Injective cidx := by
  intro a b h
  rcases a with i | i <;> rcases b with j | j <;> simp only [cidx] at h
  · exact congrArg _ (Fin.ext h)
  · have := i.isLt; omega
  · have := j.isLt; omega
  · exact congrArg _ (Fin.ext (by omega))

theorem vecK_two_pow_cidx (K : Type) [Field K] (c : Fin 4 ⊕ Fin 4) :
    vecK K (2 ^ cidx c) = Pi.single c 1 := by
  funext d
  by_cases h : d = c
  · subst h
    simp [vecK, ind]
  · have h' : ¬ cidx c = cidx d := fun e => h (cidx_injective e).symm
    simp [vecK, ind, h, h']

@[expose] noncomputable def xRoot (K : Type) [Field K] : ℕ → spinGroup (quadPlus 4 K)
  | 0 => (plusFrame 4 K three_le_four).longRoot (by decide : (1 : Fin 4) ≠ 0) false true (.ofAdd 1)
  | 1 => (plusFrame 4 K three_le_four).longRoot (by decide : (0 : Fin 4) ≠ 1) false true (.ofAdd 1)
  | 2 => (plusFrame 4 K three_le_four).longRoot (by decide : (2 : Fin 4) ≠ 1) false true (.ofAdd 1)
  | 3 => (plusFrame 4 K three_le_four).longRoot (by decide : (1 : Fin 4) ≠ 2) false true (.ofAdd 1)
  | 4 => (plusFrame 4 K three_le_four).longRoot (by decide : (3 : Fin 4) ≠ 2) false true (.ofAdd 1)
  | 5 => (plusFrame 4 K three_le_four).longRoot (by decide : (2 : Fin 4) ≠ 3) false true (.ofAdd 1)
  | 6 => (plusFrame 4 K three_le_four).longRoot (by decide : (3 : Fin 4) ≠ 2) true true (.ofAdd 1)
  | 7 => (plusFrame 4 K three_le_four).longRoot (by decide : (3 : Fin 4) ≠ 2) false false (.ofAdd 1)
  | _ => 1

theorem spinAction_xRoot (K : Type) [Field K] {r : ℕ} (hr : r < 8) :
    spinAction (quadPlus 4 K) (xRoot K r) =
      eichler (quadPlus 4 K) (vecK K (pair0 r).1) (vecK K (pair0 r).2) := by
  have e1 : vecK K 1 = Pi.single (Sum.inl 0) 1 := by
    simpa [cidx] using vecK_two_pow_cidx K (Sum.inl 0)
  have e2 : vecK K 2 = Pi.single (Sum.inl 1) 1 := by
    simpa [cidx] using vecK_two_pow_cidx K (Sum.inl 1)
  have e4 : vecK K 4 = Pi.single (Sum.inl 2) 1 := by
    simpa [cidx] using vecK_two_pow_cidx K (Sum.inl 2)
  have e8 : vecK K 8 = Pi.single (Sum.inl 3) 1 := by
    simpa [cidx] using vecK_two_pow_cidx K (Sum.inl 3)
  have e16 : vecK K 16 = Pi.single (Sum.inr 0) 1 := by
    simpa [cidx] using vecK_two_pow_cidx K (Sum.inr 0)
  have e32 : vecK K 32 = Pi.single (Sum.inr 1) 1 := by
    simpa [cidx] using vecK_two_pow_cidx K (Sum.inr 1)
  have e64 : vecK K 64 = Pi.single (Sum.inr 2) 1 := by
    simpa [cidx] using vecK_two_pow_cidx K (Sum.inr 2)
  have e128 : vecK K 128 = Pi.single (Sum.inr 3) 1 := by
    simpa [cidx] using vecK_two_pow_cidx K (Sum.inr 3)
  interval_cases r
  · rw [show pair0 0 = (1, 32) from rfl, e1, e32, xRoot,
      HypFrame.spinAction_longRoot_eq_eichler, one_smul]
    rfl
  · rw [show pair0 1 = (2, 16) from rfl, e2, e16, xRoot,
      HypFrame.spinAction_longRoot_eq_eichler, one_smul]
    rfl
  · rw [show pair0 2 = (2, 64) from rfl, e2, e64, xRoot,
      HypFrame.spinAction_longRoot_eq_eichler, one_smul]
    rfl
  · rw [show pair0 3 = (4, 32) from rfl, e4, e32, xRoot,
      HypFrame.spinAction_longRoot_eq_eichler, one_smul]
    rfl
  · rw [show pair0 4 = (4, 128) from rfl, e4, e128, xRoot,
      HypFrame.spinAction_longRoot_eq_eichler, one_smul]
    rfl
  · rw [show pair0 5 = (8, 64) from rfl, e8, e64, xRoot,
      HypFrame.spinAction_longRoot_eq_eichler, one_smul]
    rfl
  · rw [show pair0 6 = (4, 8) from rfl, e4, e8, xRoot,
      HypFrame.spinAction_longRoot_eq_eichler, one_smul]
    rfl
  · rw [show pair0 7 = (64, 128) from rfl, e64, e128, xRoot,
      HypFrame.spinAction_longRoot_eq_eichler, one_smul]
    rfl

theorem range_eq_zpowers_of_card_two {K : Type} {G : Type*} [Field K] [Finite K] [Group G]
    (hK : Nat.card K = 2) (f : Multiplicative K →* G) :
    f.range = Subgroup.zpowers (f (.ofAdd 1)) := by
  apply le_antisymm
  · rintro _ ⟨c, rfl⟩
    rcases eq_zero_or_eq_one_of_card_eq_two hK (Multiplicative.toAdd c) with h | h
    · have hc : c = 1 := by rw [← ofAdd_toAdd c, h, ofAdd_zero]
      rw [hc, f.map_one]
      exact one_mem _
    · have hc : c = .ofAdd 1 := by rw [← ofAdd_toAdd c, h]
      rw [hc]
      exact Subgroup.mem_zpowers _
  · rw [Subgroup.zpowers_le]
    exact ⟨_, rfl⟩

section RootGroups

variable {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
include hK

theorem rootGroup_single_eq_zpowers (k : Fin 4) :
    (plusDatum 4 K three_le_four).rootGroup (Pi.single k 1) =
      Subgroup.zpowers (xRoot K (2 * k)) := by
  change plusRootGroup 4 K three_le_four (Pi.single k 1) = _
  fin_cases k
  · rw [plusRootGroup_eq three_le_four (by decide : (1 : Fin 4) ≠ 0) false true (by decide),
      range_eq_zpowers_of_card_two hK]
    rfl
  · rw [plusRootGroup_eq three_le_four (by decide : (2 : Fin 4) ≠ 1) false true (by decide),
      range_eq_zpowers_of_card_two hK]
    rfl
  · rw [plusRootGroup_eq three_le_four (by decide : (3 : Fin 4) ≠ 2) false true (by decide),
      range_eq_zpowers_of_card_two hK]
    rfl
  · rw [plusRootGroup_eq three_le_four (by decide : (3 : Fin 4) ≠ 2) true true (by decide),
      range_eq_zpowers_of_card_two hK]
    rfl

theorem rootGroup_neg_single_eq_zpowers (k : Fin 4) :
    (plusDatum 4 K three_le_four).rootGroup (-Pi.single k 1) =
      Subgroup.zpowers (xRoot K (2 * k + 1)) := by
  change plusRootGroup 4 K three_le_four (-Pi.single k 1) = _
  fin_cases k
  · rw [plusRootGroup_eq three_le_four (by decide : (0 : Fin 4) ≠ 1) false true (by decide),
      range_eq_zpowers_of_card_two hK]
    rfl
  · rw [plusRootGroup_eq three_le_four (by decide : (1 : Fin 4) ≠ 2) false true (by decide),
      range_eq_zpowers_of_card_two hK]
    rfl
  · rw [plusRootGroup_eq three_le_four (by decide : (2 : Fin 4) ≠ 3) false true (by decide),
      range_eq_zpowers_of_card_two hK]
    rfl
  · rw [plusRootGroup_eq three_le_four (by decide : (3 : Fin 4) ≠ 2) false false (by decide),
      range_eq_zpowers_of_card_two hK]
    rfl

end RootGroups

@[expose] noncomputable def spinElem :
    spinGroup (quadPlus 4 F2) →* orthElementaryGroup (quadPlus 4 F2) :=
  (spinAction (quadPlus 4 F2)).codRestrict (orthElementaryGroup (quadPlus 4 F2)) fun g =>
    (range_spinAction_quadPlus three_le_four).le ⟨g, rfl⟩

theorem spinElem_bijective : Function.Bijective spinElem := by
  refine ⟨fun g h hgh => ?_, fun e => ?_⟩
  · have := isCentral_cliffordAlgebra_quadPlus F2 4
    have hker := ker_spinAction_eq_bot_of_isCentral (quadPlus 4 F2) (CharTwo.two_eq_zero (R := F2))
    have hinj : Function.Injective (spinAction (quadPlus 4 F2)) :=
      (MonoidHom.ker_eq_bot_iff _).mp hker
    exact hinj (congrArg Subtype.val hgh)
  · have he : (e : (Fin 4 ⊕ Fin 4 → F2) ≃ₗ[F2] (Fin 4 ⊕ Fin 4 → F2)) ∈
        (spinAction (quadPlus 4 F2)).range := by
      rw [range_spinAction_quadPlus three_le_four]
      exact e.2
    obtain ⟨g, hg⟩ := he
    exact ⟨g, Subtype.ext hg⟩

theorem spinElem_xRoot {r : ℕ} (hr : r < 8) : spinElem (xRoot F2 r) = eichGen F2 r :=
  Subtype.ext (spinAction_xRoot F2 hr)

@[expose] noncomputable def spinOmegaEquiv :
    spinGroup (quadPlus 4 F2) ≃* omegaT :=
  (MulEquiv.ofBijective spinElem spinElem_bijective).trans omegaElementaryEquiv.symm

theorem spinOmegaEquiv_xRoot {r : ℕ} (hr : r < 8) :
    spinOmegaEquiv (xRoot F2 r) = ⟨gen r, gen_mem_omegaT hr⟩ := by
  change omegaElementaryEquiv.symm (spinElem (xRoot F2 r)) = _
  rw [MulEquiv.symm_apply_eq, spinElem_xRoot hr]
  change eichGen F2 r = (elementaryOmega1Equiv card_F2).symm (omegaRestrictEquiv _)
  rw [MulEquiv.eq_symm_apply]
  apply Subtype.ext
  change act0 card_F2 (eichGen F2 r) = omegaRes ⟨gen r, gen_mem_omegaT hr⟩
  rw [act0_eichGen card_F2 hr, omegaRes_gen hr]

@[expose] noncomputable def autSpin :
    autT →* MulAut (spinGroup (quadPlus 4 F2)) :=
  (MulAut.congr spinOmegaEquiv.symm).toMonoidHom.comp autEquiv.toMonoidHom

theorem autSpin_bijective : Function.Bijective autSpin :=
  (MulAut.congr spinOmegaEquiv.symm).bijective.comp autEquiv.bijective

theorem spinOmegaEquiv_autSpin (a : autT)
    (x : spinGroup (quadPlus 4 F2)) :
    spinOmegaEquiv (autSpin a x) = autEquiv a (spinOmegaEquiv x) := by
  change spinOmegaEquiv (spinOmegaEquiv.symm (autEquiv a (spinOmegaEquiv x))) = _
  rw [MulEquiv.apply_symm_apply]

theorem autEquiv_of_mem_omegaT {w : Equiv.Perm (Fin 360)}
    (hw : w ∈ omegaT) : autEquiv ⟨w, omegaT_le_autT hw⟩ = MulAut.conj ⟨w, hw⟩ := by
  ext g
  rw [autEquiv_apply, MulAut.conj_apply]
  rfl

theorem autSpin_omegaT {w : Equiv.Perm (Fin 360)} (hw : w ∈ omegaT) :
    autSpin ⟨w, omegaT_le_autT hw⟩ = MulAut.conj (spinOmegaEquiv.symm ⟨w, hw⟩) := by
  refine MulEquiv.ext fun x => ?_
  apply spinOmegaEquiv.injective
  rw [spinOmegaEquiv_autSpin, autEquiv_of_mem_omegaT, MulAut.conj_apply, MulAut.conj_apply, map_mul,
    map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem autSpin_xRoot {a : Equiv.Perm (Fin 360)} (ha : a ∈ autT)
    {r r' : ℕ} (hr : r < 8) (hr' : r' < 8) (h : a * gen r * a⁻¹ = gen r') :
    autSpin ⟨a, ha⟩ (xRoot F2 r) = xRoot F2 r' := by
  apply spinOmegaEquiv.injective
  rw [spinOmegaEquiv_autSpin, spinOmegaEquiv_xRoot hr, spinOmegaEquiv_xRoot hr']
  apply Subtype.ext
  rw [autEquiv_apply]
  exact h

end CFSG.AGLEmbeddingD2.McLaughlin.Lie
