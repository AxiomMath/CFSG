module

public import CFSG.GF2Type.SmithTypeE.E7.ClsBlocks

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.E7

open CFSG.SmithD6 CFSG.GF2Type.SmithTypeE.DMod

@[expose] noncomputable def swapLam : V12 →ₗ[ZMod 2] ZMod 2 where
  toFun v := v.1 5 + v.2 5
  map_add' v w := by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
    ring
  map_smul' c v := by
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

@[expose] def swapVec : V12 := (Pi.single 5 1, Pi.single 5 1)

@[expose] noncomputable def swapLin : V12 →ₗ[ZMod 2] V12 :=
  LinearMap.id + LinearMap.smulRight swapLam swapVec

theorem swapLin_apply (v : V12) : swapLin v = v + swapLam v • swapVec := rfl

theorem swapLam_swapVec : swapLam swapVec = 0 := by
  show (Pi.single 5 1 : Fin 6 → ZMod 2) 5 + (Pi.single 5 1 : Fin 6 → ZMod 2) 5 = 0
  simp only [Pi.single_eq_same]
  decide

theorem swapLin_involutive : Function.Involutive swapLin := by
  intro v
  have h1 : swapLam (swapLin v) = swapLam v := by
    rw [swapLin_apply, map_add, map_smul, swapLam_swapVec, smul_zero, add_zero]
  rw [swapLin_apply, h1, swapLin_apply, add_assoc, ← add_smul, CharTwo.add_self_eq_zero,
    zero_smul, add_zero]

@[expose] noncomputable def swapR : V12 ≃ₗ[ZMod 2] V12 :=
  LinearEquiv.ofInvolutive swapLin swapLin_involutive

theorem swapR_apply (v : V12) : swapR v = v + swapLam v • swapVec := rfl

theorem swapR_swapR (v : V12) : swapR (swapR v) = v := swapLin_involutive v

theorem swapR_fst_apply (v : V12) (i : Fin 6) :
    (swapR v).1 i = v.1 i + (v.1 5 + v.2 5) * (if i = 5 then 1 else 0) := by
  rw [swapR_apply]
  simp [swapVec, swapLam, Pi.single_apply]

theorem swapR_snd_apply (v : V12) (i : Fin 6) :
    (swapR v).2 i = v.2 i + (v.1 5 + v.2 5) * (if i = 5 then 1 else 0) := by
  rw [swapR_apply]
  simp [swapVec, swapLam, Pi.single_apply]

theorem swapR_mul_self : swapR * swapR = 1 := by
  refine LinearEquiv.ext fun v => ?_
  show swapR (swapR v) = v
  exact swapR_swapR v

theorem swapR_inv : swapR⁻¹ = swapR := inv_eq_of_mul_eq_one_right swapR_mul_self

theorem swapB_swapVec (v : V12) : B12 v swapVec = swapLam v := by
  simp [B12, swapVec, swapLam, Pi.single_apply, mul_ite, ite_mul, Finset.sum_add_distrib]

theorem q12_swapVec : q12 swapVec = 1 := by
  simp [swapVec, q12_apply, Pi.single_apply]

theorem swapR_iso (v : V12) : q12 (swapR v) = q12 v := by
  rw [swapR_apply, q12_add, q12_smul, B12_smul_right, q12_swapVec, swapB_swapVec, mul_one]
  have ht : ∀ t : ZMod 2, t + t * t = 0 := by decide
  rw [add_assoc, ht, add_zero]

theorem swapR_mem : swapR ∈ IsoGrp := mem_isoGrp.mpr swapR_iso

section Gamma

theorem omegaPlus_eq_comm : CFSG.Open.timmesfeldOmegaPlus 6 = ⁅IsoGrp, IsoGrp⁆ := rfl

theorem conj_mem_omegaPlus {s g : V12 ≃ₗ[ZMod 2] V12} (hs : s ∈ IsoGrp)
    (hg : g ∈ CFSG.Open.timmesfeldOmegaPlus 6) :
    s * g * s⁻¹ ∈ CFSG.Open.timmesfeldOmegaPlus 6 := by
  have hmap : IsoGrp.map (MulAut.conj s).toMonoidHom ≤ IsoGrp := by
    rintro _ ⟨y, hy, rfl⟩
    exact mul_mem (mul_mem hs hy) (inv_mem hs)
  have hle : (CFSG.Open.timmesfeldOmegaPlus 6).map (MulAut.conj s).toMonoidHom ≤
      CFSG.Open.timmesfeldOmegaPlus 6 := by
    rw [omegaPlus_eq_comm, Subgroup.map_commutator]
    exact Subgroup.commutator_mono hmap hmap
  exact hle (Subgroup.mem_map_of_mem _ hg)

@[expose] noncomputable def omegaSwap :
    ↥(CFSG.Open.timmesfeldOmegaPlus 6) ≃* ↥(CFSG.Open.timmesfeldOmegaPlus 6) where
  toFun g := ⟨swapR * g.1 * swapR⁻¹, conj_mem_omegaPlus swapR_mem g.2⟩
  invFun g := ⟨swapR⁻¹ * g.1 * swapR⁻¹⁻¹, conj_mem_omegaPlus (inv_mem swapR_mem) g.2⟩
  left_inv g := by
    apply Subtype.ext
    show swapR⁻¹ * (swapR * g.1 * swapR⁻¹) * swapR⁻¹⁻¹ = g.1
    group
  right_inv g := by
    apply Subtype.ext
    show swapR * (swapR⁻¹ * g.1 * swapR⁻¹⁻¹) * swapR⁻¹ = g.1
    group
  map_mul' g h := by
    apply Subtype.ext
    show swapR * (g.1 * h.1) * swapR⁻¹ = (swapR * g.1 * swapR⁻¹) * (swapR * h.1 * swapR⁻¹)
    group

@[expose] noncomputable def gammaSwap : MulAut TD6 :=
  omegaTD6.symm.trans (omegaSwap.trans omegaTD6)

theorem sig_gammaSwap (x : TD6) : sig (gammaSwap x) = swapR * sig x * swapR := by
  have h : (gammaSwap x : TD6) = omegaTD6 (omegaSwap (omegaTD6.symm x)) := rfl
  rw [sig, h, MulEquiv.symm_apply_apply]
  show swapR * (omegaTD6.symm x).1 * swapR⁻¹ = swapR * (omegaTD6.symm x).1 * swapR
  rw [swapR_inv]

theorem sig_gammaSwap_apply (x : TD6) (v : V12) :
    sig (gammaSwap x) v = swapR (sig x (swapR v)) := by
  rw [sig_gammaSwap, LinearEquiv.mul_apply, LinearEquiv.mul_apply]

end Gamma

section Planes

theorem swapR_mem_Wp_of_F {x : V12} (hx : x ∈ planeSub 0) : swapR x ∈ Wp := by
  rw [mem_F_iff] at hx
  show (∀ i : Fin 6, i ≠ 5 → (swapR x).1 i = 0) ∧ (swapR x).2 5 = 0
  refine ⟨fun i hi => ?_, ?_⟩
  · rw [swapR_fst_apply, hx]
    simp [hi]
  · rw [swapR_snd_apply, hx]
    simp [CharTwo.add_self_eq_zero]

theorem swapR_mem_F_of_Wp {y : V12} (hy : y ∈ Wp) : swapR y ∈ planeSub 0 := by
  rw [mem_F_iff]
  obtain ⟨h1, h2⟩ : (∀ i : Fin 6, i ≠ 5 → y.1 i = 0) ∧ y.2 5 = 0 := hy
  funext i
  rw [swapR_fst_apply]
  by_cases hi : i = 5
  · subst hi
    simp [h2, CharTwo.add_self_eq_zero]
  · simp [hi, h1 i hi]

theorem gammaSwap_UFix_Wp : (UFix Wp).map gammaSwap.toMonoidHom = K0 := by
  ext g
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨h, hh, rfl⟩ x hx
    have hh' : ∀ y ∈ Wp, sig h y = y := mem_UFix.mp hh
    show sig (gammaSwap h) x = x
    rw [sig_gammaSwap_apply, hh' (swapR x) (swapR_mem_Wp_of_F hx), swapR_swapR]
  · intro hg
    have hg' : ∀ x ∈ planeSub 0, sig g x = x := mem_K0.mp hg
    refine ⟨gammaSwap.symm g, mem_UFix.mpr ?_, MulEquiv.apply_symm_apply gammaSwap g⟩
    intro y hy
    have key := sig_gammaSwap_apply (gammaSwap.symm g) (swapR y)
    rw [MulEquiv.apply_symm_apply, swapR_swapR] at key
    have h1 : sig g (swapR y) = swapR y := hg' (swapR y) (swapR_mem_F_of_Wp hy)
    have h3 : swapR (sig (gammaSwap.symm g) y) = swapR y := key.symm.trans h1
    calc sig (gammaSwap.symm g) y = swapR (swapR (sig (gammaSwap.symm g) y)) :=
          (swapR_swapR _).symm
      _ = swapR (swapR y) := by rw [h3]
      _ = y := swapR_swapR y

end Planes

end CFSG.GF2Type.SmithTypeE.E7
