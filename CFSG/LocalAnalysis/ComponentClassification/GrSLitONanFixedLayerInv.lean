module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.ONAut
public import CFSG.Sporadic.ONOddCore.SylowEight
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitOddQuotient
public import CFSG.LocalAnalysis.OddStandard.Solomon75Thm11Quot
public import CFSG.LocalAnalysis.SteinbergBSONInvolutionLocalComponents
public import CFSG.LocalAnalysis.ComponentInitial.SolvableCoreComponents

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedGS
open CFSG.Blueprint.NativeSporadic (IsSporadic)
open CFSG.ONSchreier CFSG.Sporadic.ONOddCore CFSG.EvenSporadicStandard.Solomon78

variable {G : Type} [Group G] [Finite G]

theorem onL_exists_involution_ne_onz :
    ∃ y ∈ onL, orderOf y = 2 ∧ y ≠ onz := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard8 : Nat.card omegaP = 8 := card_omegaP
  have homegaP_le : omegaP ≤ Pv := by
    rw [← omegaT_map]
    exact (Subgroup.map_subtype_le omegaT).trans onT_le
  have hne : omegaP ≠ ⊥ := by
    intro h
    rw [h] at hcard8
    simp at hcard8
  obtain ⟨e, he, he1⟩ := (Subgroup.bot_or_exists_ne_one omegaP).resolve_left hne
  have hePv : e ∈ Pv := homegaP_le he
  haveI : CFSG.IsElementaryAbelian 2 omegaP := omegaP_elementary
  have he2 : e ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian e he
  have hePv2 : orderOf (⟨e, hePv⟩ : Pv) = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact orderOf_eq_prime he2 he1
  obtain ⟨g, hg⟩ := pv_conj_zP (⟨e, hePv⟩ : Pv) hePv2
  let gp : Equiv.Perm (Fin N) := (g : Pv)
  let A : Subgroup (Equiv.Perm (Fin N)) := omegaP.map (MulAut.conj gp⁻¹).toMonoidHom
  have heq : e = gp * onz * gp⁻¹ := by
    have := congrArg (fun p : Pv => (p : Equiv.Perm (Fin N))) hg
    simpa [gp, zP] using this
  have honzA : onz ∈ A := by
    have hconj : (MulAut.conj gp⁻¹) e = onz := by
      rw [MulAut.conj_apply, inv_inv, heq]
      group
    rw [← hconj]
    exact Subgroup.mem_map_of_mem _ he
  have hA_le_Pv : A ≤ Pv := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    change gp⁻¹ * x * gp ∈ Pv
    exact Pv.mul_mem (Pv.mul_mem (Pv.inv_mem g.2) (homegaP_le hx)) g.2
  have hAelem : CFSG.IsElementaryAbelian 2 A :=
    CFSG.IsElementaryAbelian.map (p := 2) (A := omegaP) (MulAut.conj gp⁻¹).toMonoidHom
  have hA_le_cent : A ≤ Subgroup.centralizer ({onz} : Set (Equiv.Perm (Fin N))) := by
    haveI : IsMulCommutative A := hAelem.toIsMulCommutative
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (mul_comm' (⟨y, hy⟩ : A) (⟨onz, honzA⟩ : A))
  have hA_onM : A ≤ onM := by
    rw [onM_eq_centralizer_z]
    exact le_inf hA_le_Pv hA_le_cent
  have hcardA : Nat.card A = 8 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj gp⁻¹).injective, hcard8]
  have hrel : onL.relIndex A ≤ 2 := by
    have h := Subgroup.relIndex_le_of_le_right (H := onL) (K := A) (L := onM) hA_onM
      (by rw [onL_relIndex]; norm_num)
    rwa [onL_relIndex] at h
  have hcard_inf : 4 ≤ Nat.card ↥(A ⊓ onL) := by
    have hmul := Subgroup.relIndex_mul_card (H := onL) (K := A)
    have h4 : 4 * 2 ≤ Nat.card ↥(onL ⊓ A) * 2 := by
      calc 4 * 2 = 8 := by norm_num
        _ = Nat.card A := hcardA.symm
        _ = onL.relIndex A * Nat.card ↥(onL ⊓ A) := hmul.symm
        _ = Nat.card ↥(onL ⊓ A) * onL.relIndex A := Nat.mul_comm _ _
        _ ≤ Nat.card ↥(onL ⊓ A) * 2 := Nat.mul_le_mul_left _ hrel
    have h' := Nat.le_of_mul_le_mul_right h4 (by norm_num : (0 : ℕ) < 2)
    simpa [inf_comm] using h'
  have hex : ∃ y ∈ A ⊓ onL, y ≠ 1 ∧ y ≠ onz := by
    by_contra h
    push Not at h
    have hle : A ⊓ onL ≤ Subgroup.zpowers onz := by
      intro y hy
      by_cases h1 : y = 1
      · rw [h1]; exact Subgroup.one_mem _
      · rw [h y hy h1]; exact Subgroup.mem_zpowers onz
    have hcardle : Nat.card ↥(A ⊓ onL) ≤ 2 := by
      have h' := Subgroup.card_le_of_le hle
      rwa [Nat.card_zpowers, orderOf_onz] at h'
    omega
  obtain ⟨y0, hy0, hy01, hy0z⟩ := hex
  refine ⟨y0, hy0.2, ?_, hy0z⟩
  exact orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian y0 hy0.1) hy01

theorem exists_involution_pLayer_centralizer_zP :
    ∃ y ∈ pLayer (Subgroup.centralizer ({zP} : Set Pv)) 2,
      orderOf y = 2 ∧ (y : Pv) ≠ zP := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨y0, hy0L, hy02, hy0z⟩ := onL_exists_involution_ne_onz
  have hLq : IsQuasisimple (onL.subgroupOf onM) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe onL_le_M).symm
      CFSG.LocalAnalysis.SteinbergBS.onL_isQuasisimple.1
  have hnotle : ¬ onL.subgroupOf onM ≤ pPrimeCore 2 onM := by
    intro hle
    have hdvd : Nat.card (onL.subgroupOf onM) ∣ Nat.card (pPrimeCore 2 onM) :=
      Subgroup.card_dvd_of_le hle
    rw [card_L_subgroupOf] at hdvd
    have hodd : Odd (Nat.card (pPrimeCore 2 onM)) :=
      Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := onM))
    have heven : 2 ∣ Nat.card (pPrimeCore 2 onM) :=
      (show 2 ∣ 80640 by norm_num).trans hdvd
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr heven)
  have hLp : IsPComponent 2 (onL.subgroupOf onM) :=
    CFSG.LocalAnalysis.ComponentInitial.isPComponent_of_isComponent_of_not_le 2
      ⟨hLq, (Subgroup.normal_of_characteristic (H := onL.subgroupOf onM)).isSubnormal⟩ hnotle
  have hle_layer : onL.subgroupOf onM ≤ pLayer onM 2 :=
    le_sSup (show onL.subgroupOf onM ∈ {L : Subgroup onM | IsPComponent 2 L} from hLp)
  set M : Subgroup Pv := Subgroup.centralizer ({zP} : Set Pv) with hMdef
  have hMmem : ∀ x : onM, (⟨x.1, onM_le x.2⟩ : Pv) ∈ M := by
    intro x
    rw [hMdef, CFSG.ONSchreier.centralizer_zP, Subgroup.mem_subgroupOf]
    exact onM_le_centralizer_z x.2
  have hinvM : ∀ y : M, (y : Equiv.Perm (Fin N)) ∈ onM := by
    intro y
    rw [onM_eq_centralizer_z, Subgroup.mem_inf]
    refine ⟨y.1.2, ?_⟩
    have hy : (y : Pv) ∈ Subgroup.centralizer ({zP} : Set Pv) := by
      rw [← hMdef]
      exact y.2
    rw [CFSG.ONSchreier.centralizer_zP, Subgroup.mem_subgroupOf] at hy
    exact hy
  let eM : onM ≃* M :=
    { toFun := fun x => ⟨⟨x.1, onM_le x.2⟩, hMmem x⟩
      invFun := fun y => ⟨(y : Equiv.Perm (Fin N)), hinvM y⟩
      left_inv := fun x => Subtype.ext rfl
      right_inv := fun y => Subtype.ext rfl
      map_mul' := fun x y => Subtype.ext (Subtype.ext rfl) }
  have hplat : (pLayer onM 2).map eM.toMonoidHom = pLayer M 2 :=
    FixedLayerPComponent.map_pLayer_mulEquiv 2 eM
  let x0 : onM := ⟨y0, onL_le_M hy0L⟩
  have hx0 : x0 ∈ pLayer onM 2 :=
    hle_layer (by rw [Subgroup.mem_subgroupOf]; exact hy0L)
  have hx0coe : ((eM x0 : Pv) : Equiv.Perm (Fin N)) = y0 := rfl
  refine ⟨eM x0, ?_, ?_, ?_⟩
  · have h := Subgroup.mem_map_of_mem eM.toMonoidHom hx0
    rwa [hplat] at h
  · rw [MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe x0]
    exact hy02
  · intro h
    exact hy0z (by
      have h2 := congrArg (fun p : Pv => (p : Equiv.Perm (Fin N))) h
      rwa [hx0coe] at h2)

theorem exists_involution_gsFixedLayer_on
    {P : Subgroup G} (hON : IsSporadic (↥P ⧸ pPrimeCore 2 ↥P) .ONan) {x : G} (hxP : x ∈ P)
    (hx : orderOf x = 2) :
    ∃ y ∈ gsFixedLayer P x, orderOf y = 2 ∧ y ≠ x := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let U : Subgroup ↥P := pPrimeCore 2 ↥P
  have hUnorm : U.Normal := pPrimeCore_normal
  haveI : U.Normal := hUnorm
  have hUodd : Odd (Nat.card U) :=
    Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := ↥P))
  let x' : ↥P := ⟨x, hxP⟩
  have hx' : orderOf x' = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact hx
  let xbar : (↥P) ⧸ U := QuotientGroup.mk' U x'
  have hxbar1 : xbar ≠ 1 := by
    intro h
    have hmem : x' ∈ U := (QuotientGroup.eq_one_iff x').mp h
    have hdvd : orderOf x' ∣ Nat.card U := Subgroup.orderOf_dvd_natCard U hmem
    rw [hx'] at hdvd
    exact (Nat.not_even_iff_odd.mpr hUodd) (even_iff_two_dvd.mpr hdvd)
  have hxbar : orderOf xbar = 2 := by
    have hdvd : orderOf xbar ∣ 2 := by
      rw [← hx']
      exact orderOf_map_dvd (QuotientGroup.mk' U) x'
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · exact absurd (orderOf_eq_one_iff.mp h1) hxbar1
    · exact h2
  obtain ⟨φ⟩ := on_equiv_Pv hON
  have hφx : orderOf (φ xbar) = 2 := by
    rw [MulEquiv.orderOf_eq, hxbar]
  obtain ⟨g, hgx⟩ := pv_conj_zP (φ xbar) hφx
  let ψ : (↥P) ⧸ U ≃* Pv := φ.trans (MulAut.conj g⁻¹)
  have hψx : ψ xbar = zP := by
    show (MulAut.conj g⁻¹) (φ xbar) = zP
    rw [hgx, MulAut.conj_apply]
    group
  obtain ⟨y0, hy0mem, hy0ord, hy0ne⟩ := exists_involution_pLayer_centralizer_zP
  have hCx : (Subgroup.centralizer ({x} : Set G)).subgroupOf P
      = Subgroup.centralizer ({x'} : Set ↥P) := by
    ext y
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      exact Subtype.ext (by simpa using h)
    · intro h
      simpa using congrArg (fun z : ↥P => (z : G)) h
  have hCA : Subgroup.centralizer ({xbar} : Set ((↥P) ⧸ U))
      = ((Subgroup.centralizer ({x} : Set G)).subgroupOf P).map (QuotientGroup.mk' U) := by
    rw [hCx]
    exact CFSG.ComponentClassification.AschbacherToolkit.centralizer_quotient_odd U hUodd x' hx'
  let eC : Subgroup.centralizer ({xbar} : Set ((↥P) ⧸ U)) ≃*
      Subgroup.centralizer ({zP} : Set Pv) :=
    { toFun := fun a => ⟨ψ a, by
        rw [Subgroup.mem_centralizer_singleton_iff]
        have ha : (a : (↥P) ⧸ U) * xbar = xbar * (a : (↥P) ⧸ U) := by
          have h' : (a : (↥P) ⧸ U) ∈ Subgroup.centralizer ({xbar} : Set ((↥P) ⧸ U)) := a.2
          rwa [Subgroup.mem_centralizer_singleton_iff] at h'
        calc ψ (a : (↥P) ⧸ U) * zP = ψ (a : (↥P) ⧸ U) * ψ xbar := by rw [hψx]
          _ = ψ ((a : (↥P) ⧸ U) * xbar) := by rw [map_mul]
          _ = ψ (xbar * (a : (↥P) ⧸ U)) := by rw [ha]
          _ = ψ xbar * ψ (a : (↥P) ⧸ U) := by rw [map_mul]
          _ = zP * ψ (a : (↥P) ⧸ U) := by rw [hψx]⟩
      invFun := fun m => ⟨ψ.symm m, by
        rw [Subgroup.mem_centralizer_singleton_iff]
        apply ψ.injective
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hψx]
        have hm : (m : Pv) * zP = zP * (m : Pv) := by
          have h' : (m : Pv) ∈ Subgroup.centralizer ({zP} : Set Pv) := m.2
          rwa [Subgroup.mem_centralizer_singleton_iff] at h'
        rw [hm]⟩
      left_inv := fun a => Subtype.ext (MulEquiv.symm_apply_apply ψ (a : (↥P) ⧸ U))
      right_inv := fun m => Subtype.ext (MulEquiv.apply_symm_apply ψ (m : Pv))
      map_mul' := fun a b => Subtype.ext (map_mul ψ (a : (↥P) ⧸ U) (b : (↥P) ⧸ U)) }
  let ybar : Subgroup.centralizer ({xbar} : Set ((↥P) ⧸ U)) :=
    eC.symm (⟨y0, hy0mem⟩ : pLayer (Subgroup.centralizer ({zP} : Set Pv)) 2)
  have hybar_coe : (ybar : (↥P) ⧸ U) = ψ.symm (y0 : Pv) := rfl
  have hψybar : ψ (ybar : (↥P) ⧸ U) = (y0 : Pv) := by
    rw [hybar_coe, MulEquiv.apply_symm_apply]
  have hybar_mem : ybar ∈ pLayer (Subgroup.centralizer ({xbar} : Set ((↥P) ⧸ U))) 2 := by
    have h1 : eC ybar ∈
        (pLayer (Subgroup.centralizer ({xbar} : Set ((↥P) ⧸ U))) 2).map eC.toMonoidHom := by
      rw [FixedLayerPComponent.map_pLayer_mulEquiv 2 eC, MulEquiv.apply_symm_apply]
      exact hy0mem
    obtain ⟨a, ha, hae⟩ := Subgroup.mem_map.mp h1
    rw [show a = ybar from eC.injective hae] at ha
    exact ha
  have hybar_ord : orderOf ybar = 2 := by
    have h1 : orderOf (eC ybar) = 2 := by
      rw [MulEquiv.apply_symm_apply]
      exact hy0ord
    rwa [MulEquiv.orderOf_eq] at h1
  have hybar_ordQ : orderOf (ybar : (↥P) ⧸ U) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact hybar_ord
  have hybar_ne : (ybar : (↥P) ⧸ U) ≠ xbar := by
    intro h
    apply hy0ne
    have h1 : ψ (ybar : (↥P) ⧸ U) = zP := by rw [h, hψx]
    rwa [hψybar] at h1
  let f : ((Subgroup.centralizer ({x} : Set G)).subgroupOf P) →*
      Subgroup.centralizer ({xbar} : Set ((↥P) ⧸ U)) :=
    { toFun := fun c => ⟨QuotientGroup.mk' U (c : ↥P), by
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hc : (c : ↥P) * x' = x' * (c : ↥P) := by
          have h0 : (c : ↥P) ∈ Subgroup.centralizer ({x'} : Set ↥P) := by
            rw [← hCx]
            exact c.2
          rwa [Subgroup.mem_centralizer_singleton_iff] at h0
        change QuotientGroup.mk' U (c : ↥P) * QuotientGroup.mk' U x' =
          QuotientGroup.mk' U x' * QuotientGroup.mk' U (c : ↥P)
        rw [← map_mul, ← map_mul, hc]⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun a b => by apply Subtype.ext; simp }
  have hf : Function.Surjective f := by
    intro a
    have ha : (a : (↥P) ⧸ U) ∈
        ((Subgroup.centralizer ({x} : Set G)).subgroupOf P).map (QuotientGroup.mk' U) := by
      rw [← hCA]
      exact a.2
    obtain ⟨c, hc, hca⟩ := Subgroup.mem_map.mp ha
    exact ⟨⟨c, hc⟩, Subtype.ext hca⟩
  have hker : ¬ 2 ∣ Nat.card ↥f.ker := by
    have hker_eq : f.ker = U.subgroupOf ((Subgroup.centralizer ({x} : Set G)).subgroupOf P) := by
      ext c
      constructor
      · intro hc
        have h2 : QuotientGroup.mk' U (c : ↥P) = 1 := by
          have h3 : (f c : (↥P) ⧸ U) = 1 := by
            rw [MonoidHom.mem_ker.mp hc]
            rfl
          exact h3
        exact Subgroup.mem_subgroupOf.mpr ((QuotientGroup.eq_one_iff (c : ↥P)).mp h2)
      · intro hc
        have h2 : QuotientGroup.mk' U (c : ↥P) = 1 :=
          (QuotientGroup.eq_one_iff (c : ↥P)).mpr (Subgroup.mem_subgroupOf.mp hc)
        exact MonoidHom.mem_ker.mpr (Subtype.ext h2)
    have hcard : Nat.card ↥f.ker =
        Nat.card ↥(U ⊓ ((Subgroup.centralizer ({x} : Set G)).subgroupOf P)) := by
      rw [hker_eq, CFSG.ONSchreier.card_subgroupOf ((Subgroup.centralizer ({x} : Set G)).subgroupOf P) U,
        inf_comm]
    have hdvd : Nat.card ↥f.ker ∣ Nat.card ↥U := by
      rw [hcard]
      exact Subgroup.card_dvd_of_le inf_le_left
    intro h2
    exact (Nat.not_even_iff_odd.mpr hUodd) (even_iff_two_dvd.mpr (h2.trans hdvd))
  have hplatC : (pLayer ((Subgroup.centralizer ({x} : Set G)).subgroupOf P) 2).map f
      = pLayer (Subgroup.centralizer ({xbar} : Set ((↥P) ⧸ U))) 2 :=
    CFSG.ComponentClassification.UnbalancingLocal.Correspondence.map_pLayer_of_coprime_kernel
      f hf hker
  let Mlift : Subgroup ↥P :=
    (pLayer ((Subgroup.centralizer ({x} : Set G)).subgroupOf P) 2).map
      ((Subgroup.centralizer ({x} : Set G)).subgroupOf P).subtype
  have hybar_in : (ybar : (↥P) ⧸ U) ∈ Mlift.map (QuotientGroup.mk' U) := by
    have h : ybar ∈ (pLayer ((Subgroup.centralizer ({x} : Set G)).subgroupOf P) 2).map f := by
      rw [hplatC]
      exact hybar_mem
    obtain ⟨m, hm, hme⟩ := Subgroup.mem_map.mp h
    have hcoe : QuotientGroup.mk' U ((m : (Subgroup.centralizer ({x} : Set G)).subgroupOf P) : ↥P)
        = (ybar : (↥P) ⧸ U) := by
      have h3 := congrArg (fun a : Subgroup.centralizer ({xbar} : Set ((↥P) ⧸ U)) =>
        (a : (↥P) ⧸ U)) hme
      simpa [f] using h3
    rw [← hcoe]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ hm)
  obtain ⟨s, hsM, hsmk, hsord⟩ :=
    CFSG.OddStandard.Solomon75.exists_involution_lift_of_odd (X := ↥P) (N := U)
      (M := Mlift) hUodd hybar_in hybar_ordQ
  refine ⟨(s : G), ?_, ?_, ?_⟩
  · have hs1 : (s : G) ∈ Mlift.map P.subtype := Subgroup.mem_map_of_mem P.subtype hsM
    rw [CFSG.ComponentClassification.UnbalancedCorr.map_pLayer_subgroupOf_eq] at hs1
    simpa only [gsFixedLayer] using hs1
  · rw [Subgroup.orderOf_coe]
    exact hsord
  · intro h
    apply hybar_ne
    have hsx : s = x' := Subtype.ext h
    rw [hsx] at hsmk
    exact hsmk.symm

end CFSG.ComponentClassification.GrSLit.L34Sec5S
