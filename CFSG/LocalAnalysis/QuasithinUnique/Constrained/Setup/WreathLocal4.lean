module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathLocal3
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathPlaneSL
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathA3Sel

public section

namespace CFSG.QuasithinUnique.Setup.Wreath

open scoped Pointwise commutatorElement
open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Campbell

theorem sl2_pow_three_of_odd (g : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))
    (hg : Odd (orderOf g)) : g ^ 3 = 1 := by
  have h6 : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) = 6 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  have hd : orderOf g ∣ 3 * 2 := by
    have := orderOf_dvd_natCard g
    rwa [h6] at this
  exact orderOf_dvd_iff_pow_eq_one.mp (hg.coprime_two_right.dvd_of_dvd_mul_right hd)

theorem exists_sl2_cube :
    ∃ A : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)), Nat.card ↥A = 3 ∧
      ∀ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2), g ^ 3 = 1 → g ∈ A := by
  refine ⟨(cubeSubgroup V4').map slEquivAut.symm.toMonoidHom, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective slEquivAut.symm.injective, card_cubeSubgroup]
  · intro g hg
    refine ⟨slEquivAut g, mem_cubeSubgroup.mpr ?_, by simp⟩
    rw [← map_pow, hg, map_one]

theorem sl2_normal_two_eq_bot (N : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)))
    [N.Normal] (hN : IsPGroup 2 ↥N) : N = ⊥ := by
  have : (N.map slEquivAut.toMonoidHom).Normal :=
    Subgroup.Normal.map ‹_› _ slEquivAut.surjective
  have h1 : N.map slEquivAut.toMonoidHom = ⊥ :=
    eq_bot_of_normal_isPGroup _ (hN.of_surjective (slEquivAut.toMonoidHom.subgroupMap N)
      (slEquivAut.toMonoidHom.subgroupMap_surjective N))
  exact (Subgroup.map_eq_bot_iff_of_injective _ slEquivAut.injective).mp h1

theorem oddOrderSubgroup_top_eq_subgroupOf {G : Type*} [Group G] [Finite G] (P : Subgroup G) :
    oddOrderSubgroup (⊤ : Subgroup ↥P) = (oddOrderSubgroup P).subgroupOf P := by
  rw [← oddOrderSubgroup_top_map P]
  exact (Subgroup.comap_map_eq_self_of_injective P.subtype_injective _).symm

theorem thompsonJ_baumann_eq {H : Type*} [Group H] [Finite H] (R : Subgroup H) :
    thompsonJ (elemBaumannIn 2 R) = thompsonJ R := by
  rw [← elemThompsonIn_two_eq]
  exact elemThompsonIn_baumann

section Finite

variable {H : Type*} [Group H] [Finite H] {R M V W F : Subgroup H} {r : ℕ} {I : Fin r → Subgroup H}
  {Pm : Subgroup (Equiv.Perm (Fin r))} (h : WreathHyp R M V W F I Pm)

namespace WreathHyp

include h

omit [Finite H] in
theorem isKleinFour_I (j : Fin r) : IsKleinFour ↥(I j) := by
  refine ⟨h.I_card j, ?_⟩
  have hfin : Finite ↥(I j) := Nat.finite_of_card_ne_zero (by rw [h.I_card j]; norm_num)
  have hnt : Nontrivial ↥(I j) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [h.I_card j]; norm_num)
  rw [Monoid.exponent_eq_prime_iff Nat.prime_two]
  intro g hg
  refine orderOf_eq_prime ?_ hg
  apply Subtype.ext
  simpa using h.W_elem.2 (g : H) (h.I_le j g.2)

omit [Finite H] in
theorem isElemAbelian_I (j : Fin r) : CFSG.Open.IsElemAbelian 2 (I j) :=
  isElemAbelian_mono h.W_elem (h.I_le j)

theorem W_le_S : W ≤ elemBaumannIn 2 R := by
  obtain ⟨t, hTC⟩ := internal_S3_wreath_transfer h
  exact hTC.W_le_S

variable {h} {i : Fin r} {P : Subgroup H} (hP : h.IsSelected i P)

include hP

theorem IsSelected.I_le_P (j : Fin r) : I j ≤ P :=
  (h.I_le j).trans (h.W_le_S.trans hP.S_le)

theorem IsSelected.map_rho_le_B : P.map h.rho ≤ h.B := by
  let _ := h.cg
  rw [hP.map_rho]
  exact sup_le (h.Dat_le_B i) inf_le_right

theorem IsSelected.piH_eq_one {x : H} (hx : x ∈ P) : h.piH x = 1 :=
  (h.piH_eq_one_iff x).mpr (hP.map_rho_le_B ⟨x, hx, rfl⟩)

theorem IsSelected.le_normalizer_I (j : Fin r) : P ≤ Subgroup.normalizer ((I j : Subgroup H) : Set H) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have h1 := h.map_conj_plane x j
  rw [hP.piH_eq_one hx] at h1
  have h2 : x * y * x⁻¹ ∈ (I j).map (MulAut.conj x).toMonoidHom ↔ y ∈ I j :=
    WreathHyp.mem_map_conj_iff
  rw [h1] at h2
  exact h2.symm

theorem IsSelected.exists_induce (σ : MulAut ↥(I i)) :
    ∃ p : ↥P, ∀ u : ↥(I i), ((σ u : ↥(I i)) : H) = (p : H) * (u : H) * (p : H)⁻¹ := by
  let _ := h.cg
  have hF := h.planeFamily
  obtain ⟨t, ht⟩ := h.exists_t
  let e : ↥(planesIn W I i) ≃* ↥(I i) := Subgroup.subgroupOfEquivOfLe (h.I_le i)
  let σ' : MulAut ↥(planesIn W I i) := (MulAut.congr e).symm σ
  have hg : hF.blockAut (Pi.mulSingle i σ') ∈ h.Dat i ⊔ h.T0 :=
    blockAut_single_mem_sup hF ht i σ'
  rw [← hP.map_rho] at hg
  obtain ⟨p, hpP, hp⟩ := hg
  refine ⟨⟨p, hpP⟩, fun u => ?_⟩
  have hu : ((u : H)) ∈ I i := u.2
  have hx : (⟨(u : H), h.I_le i u.2⟩ : ↥W) ∈ planesIn W I i := hu
  have h1 := congrArg (fun a : MulAut ↥W => ((a ⟨(u : H), h.I_le i u.2⟩ : ↥W) : H)) hp
  simp only [h.rho_apply] at h1
  rw [hF.blockAut_apply _ hx] at h1
  simp only [Pi.mulSingle_eq_same] at h1
  show ((σ u : ↥(I i)) : H) = p * (u : H) * p⁻¹
  rw [h1]
  rfl

end WreathHyp

end Finite

end CFSG.QuasithinUnique.Setup.Wreath
