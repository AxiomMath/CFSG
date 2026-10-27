module

public import Certificates.Certificate22223
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4L34Cert
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourExactModel
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_6_13
public import CFSG.Sporadic.SuzOddCore.InvCentralizers

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.CF23L34

open CFSG.Sporadic.SuzOddCore CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34
open CFSG.ComponentClassification.GrSLit.L34Facts

structure SuzFusParts : Prop where
  inv₁ : isInvA 1782 suzY1Arr suzGensInv[0]! = true
  inv₂ : isInvA 1782 suzY2Arr suzGensInv[1]! = true
  invM : isInvA 1782 suzMArr (invCand 1782 suzMArr) = true
  mem₁ : inM suzY1Arr = true
  mem₂ : inM suzY2Arr = true
  memM : inM suzMArr = true
  comm₁ : commutesA suzY1Arr (tArr 0) = true
  comm₂ : commutesA suzY2Arr (tArr 0) = true
  rels : ∀ w ∈ coverWs ++ [zOne, zTwo, zThree],
    eqA 1782 (evalFW 1782 suzGens suzGensInv w) (idA 1782) = true
  conj : eqA 1782 (compA 1782 (compA 1782 suzMArr (tArr 0)) (invCand 1782 suzMArr))
    (compA 1782 (tArr 0) suzY1Arr) = true
  ne : eqA 1782 suzY1Arr (idA 1782) = false

theorem suzFusParts : SuzFusParts := by
  have h := Certificates.certificate22223
  simp only [suzFusOK, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

@[expose] def sY1 : Equiv.Perm (Fin 1782) := permOfArr 1782 suzY1Arr

@[expose] def sY2 : Equiv.Perm (Fin 1782) := permOfArr 1782 suzY2Arr

@[expose] def sMm : Equiv.Perm (Fin 1782) := permOfArr 1782 suzMArr

@[expose] def sGen (i : Fin 2) : Equiv.Perm (Fin 1782) := if i = 0 then sY1 else sY2

theorem sGen_zero : sGen 0 = sY1 := by rw [sGen, if_pos rfl]

theorem sGen_one : sGen 1 = sY2 := by rw [sGen, if_neg (by decide)]

theorem isSimpleGroup_S : IsSimpleGroup ↥PSL3Four.S := by
  obtain ⟨θ, -⟩ := PSL3Four.exact_model.2.1
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) PSL3Four.F4) :=
    BenderSuzuki.External.huppert_II_6_13 3 (by norm_num) (Or.inl (by norm_num))
      (Or.inl (by norm_num))
  exact (θ.symm.trans (QuotientGroup.quotientMulEquivOfEq
    (LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center 3
      PSL3Four.F4))).isSimpleGroup


theorem rep_sGen (i : Fin 2) :
    Rep 1782 suzGens[i.val]! (sGen i) ∧ Rep 1782 suzGensInv[i.val]! (sGen i)⁻¹ := by
  rcases Fin.exists_fin_two.mp ⟨i, rfl⟩ with rfl | rfl
  · rw [sGen_zero]
    exact rep_permOfArr suzFusParts.inv₁
  · rw [sGen_one]
    exact rep_permOfArr suzFusParts.inv₂

theorem rep_evalFW : ∀ w : List (Fin 2 × Bool),
    Rep 1782 (evalFW 1782 suzGens suzGensInv w)
      (List.prod (w.map fun x => cond x.2 (sGen x.1) (sGen x.1)⁻¹))
  | [] => by simpa [evalFW] using (rep_idA (n := 1782))
  | (i, b) :: w => by
    rw [evalFW, List.map_cons, List.prod_cons]
    refine rep_compA ?_ (rep_evalFW w)
    cases b
    · exact (rep_sGen i).2
    · exact (rep_sGen i).1

theorem lift_sGen_eq_one {w : List (Fin 2 × Bool)} (hw : w ∈ coverWs ++ [zOne, zTwo, zThree]) :
    FreeGroup.lift sGen (FreeGroup.mk w) = 1 := by
  rw [FreeGroup.lift_mk]
  exact eq_of_eqA (rep_evalFW w) rep_idA (suzFusParts.rels w hw)

theorem lift_sGen_coverWs : ∀ r ∈ wordSet coverWs, FreeGroup.lift sGen r = 1 := by
  intro r hr
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
  exact lift_sGen_eq_one (List.mem_append_left _ hw)

@[expose] def lam : Cover →* Equiv.Perm (Fin 1782) := PresentedGroup.toGroup lift_sGen_coverWs

theorem lam_of (i : Fin 2) : lam (PresentedGroup.of i) = sGen i := PresentedGroup.toGroup.of _

theorem lam_z₁ : lam z₁ = 1 := lift_sGen_eq_one (by simp)

theorem lam_z₂ : lam z₂ = 1 := lift_sGen_eq_one (by simp)

theorem lam_z₃ : lam z₃ = 1 := lift_sGen_eq_one (by simp)

theorem sY1_ne_one : sY1 ≠ 1 := by
  intro h
  have := (eqA_iff (rep_permOfArr suzFusParts.inv₁).1 rep_idA).2 h
  rw [suzFusParts.ne] at this
  exact Bool.false_ne_true this

@[expose] def suzL : Subgroup (Equiv.Perm (Fin 1782)) := lam.range

theorem sY1_mem : sY1 ∈ suzL := ⟨PresentedGroup.of 0, by rw [lam_of, sGen_zero]⟩

theorem sGen_mem_centM
    (i : Fin 2) : sGen i ∈ centM (suzInv 0) := by
  have key : ∀ {t r : Array ℕ}, isInvA 1782 t r = true → inM t = true →
      commutesA t (tArr 0) = true → permOfArr 1782 t ∈ centM (suzInv 0) := by
    intro t r hinv hM hc
    have hrep := (rep_permOfArr hinv).1
    exact ⟨Subgroup.mem_centralizer_singleton_iff.2
      ((commutesA_iff hrep (rep_suzInv (by norm_num))).1 hc), (inM_iff hrep).1 hM⟩
  rcases Fin.exists_fin_two.mp ⟨i, rfl⟩ with rfl | rfl
  · rw [sGen_zero]
    exact key suzFusParts.inv₁ suzFusParts.mem₁ suzFusParts.comm₁
  · rw [sGen_one]
    exact key suzFusParts.inv₂ suzFusParts.mem₂ suzFusParts.comm₂

theorem suzL_le_centM :
    suzL ≤ centM (suzInv 0) := by
  rw [suzL, MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of, MonoidHom.map_closure,
    Subgroup.closure_le]
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  rw [SetLike.mem_coe, lam_of]
  exact sGen_mem_centM i

theorem sMm_mem : sMm ∈ suzM :=
  (inM_iff (rep_permOfArr suzFusParts.invM).1).1 suzFusParts.memM

theorem sMm_conj :
    sMm * suzInv 0 * sMm⁻¹ = suzInv 0 * sY1 :=
  eq_of_eqA (rep_compA (rep_compA (rep_permOfArr suzFusParts.invM).1 (rep_suzInv (by norm_num)))
    (rep_permOfArr suzFusParts.invM).2)
    (rep_compA (rep_suzInv (by norm_num)) (rep_permOfArr suzFusParts.inv₁).1) suzFusParts.conj

theorem sY1_mul_self :
    sY1 * sY1 = 1 := by
  have ht := suzInv_sq (i := 0) (by norm_num)
  have hc : sY1 * suzInv 0 = suzInv 0 * sY1 :=
    Subgroup.mem_centralizer_singleton_iff.1 (suzL_le_centM sY1_mem).1
  have h1 : (suzInv 0 * sY1) * (suzInv 0 * sY1) = 1 := by
    rw [← sMm_conj]
    calc sMm * suzInv 0 * sMm⁻¹ * (sMm * suzInv 0 * sMm⁻¹) =
        sMm * (suzInv 0 * suzInv 0) * sMm⁻¹ := by group
      _ = 1 := by rw [ht]; group
  calc sY1 * sY1 = suzInv 0 * suzInv 0 * (sY1 * sY1) := by rw [ht, one_mul]
    _ = suzInv 0 * (suzInv 0 * sY1) * sY1 := by group
    _ = suzInv 0 * (sY1 * suzInv 0) * sY1 := by rw [hc]
    _ = (suzInv 0 * sY1) * (suzInv 0 * sY1) := by group
    _ = 1 := h1

section Iso


theorem ker_sigma_le_ker_lam : sigma.ker ≤ lam.ker := by
  rw [← range_zHom]
  rintro _ ⟨d, rfl⟩
  rw [MonoidHom.mem_ker, zHom_apply, map_mul, map_mul, map_pow, map_pow, map_pow, lam_z₁, lam_z₂,
    lam_z₃]
  simp

theorem isSimpleGroup_quot : IsSimpleGroup (Cover ⧸ sigma.ker) := by
  have := isSimpleGroup_S
  exact ((QuotientGroup.quotientKerEquivRange sigma).trans
    (MulEquiv.subgroupCongr range_sigma)).isSimpleGroup

@[expose] def lamBar : Cover ⧸ sigma.ker →* Equiv.Perm (Fin 1782) :=
  QuotientGroup.lift sigma.ker lam ker_sigma_le_ker_lam

theorem lamBar_injective : Function.Injective lamBar := by
  have := isSimpleGroup_quot
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal lamBar.ker with h | h
  · exact (MonoidHom.ker_eq_bot_iff _).1 h
  · exfalso
    apply sY1_ne_one
    have hmem : ((PresentedGroup.of 0 : Cover) : Cover ⧸ sigma.ker) ∈ lamBar.ker :=
      h ▸ Subgroup.mem_top _
    rw [MonoidHom.mem_ker, lamBar, QuotientGroup.lift_mk, lam_of, sGen_zero] at hmem
    exact hmem

theorem range_lamBar : lamBar.range = suzL := by
  ext y
  constructor
  · rintro ⟨q, rfl⟩
    obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨c, rfl⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c, rfl⟩

@[expose] def suzLEquiv : ↥PSL3Four.S ≃* ↥suzL :=
  ((MulEquiv.subgroupCongr range_sigma).symm.trans
    (QuotientGroup.quotientKerEquivRange sigma).symm).trans
    ((MonoidHom.ofInjective lamBar_injective).trans (MulEquiv.subgroupCongr range_lamBar))

theorem isSimpleGroup_suzL : IsSimpleGroup ↥suzL := by
  have := isSimpleGroup_S
  exact suzLEquiv.symm.isSimpleGroup

theorem card_suzL : Nat.card suzL = 20160 := by
  rw [← Nat.card_congr suzLEquiv.toEquiv, PSL3Four.card_S]

theorem mul_self_symm {u : Equiv.Perm (Fin 1782)} (hu : u ∈ suzL) (hu2 : u * u = 1) :
    ((suzLEquiv.symm ⟨u, hu⟩ : ↥PSL3Four.S) : Equiv.Perm (Fin 42)) *
      (suzLEquiv.symm ⟨u, hu⟩ : ↥PSL3Four.S) = 1 := by
  have e : (⟨u, hu⟩ : ↥suzL) * ⟨u, hu⟩ = 1 := Subtype.ext hu2
  have := congrArg (fun y => ((suzLEquiv.symm y : ↥PSL3Four.S) : Equiv.Perm (Fin 42))) e
  simpa only [map_mul, map_one, Subgroup.coe_mul, Subgroup.coe_one] using this

theorem symm_ne_one {u : Equiv.Perm (Fin 1782)} (hu : u ∈ suzL) (hu1 : u ≠ 1) :
    ((suzLEquiv.symm ⟨u, hu⟩ : ↥PSL3Four.S) : Equiv.Perm (Fin 42)) ≠ 1 := by
  intro h
  apply hu1
  have e : suzLEquiv.symm ⟨u, hu⟩ = 1 := Subtype.ext h
  have := congrArg (fun y => ((suzLEquiv y : ↥suzL) : Equiv.Perm (Fin 1782))) e
  simpa only [MulEquiv.apply_symm_apply, map_one, Subgroup.coe_one] using this

theorem exists_conj_suzL {u u' : Equiv.Perm (Fin 1782)}
    (hu : u ∈ suzL) (hu' : u' ∈ suzL) (hu2 : u * u = 1) (hu'2 : u' * u' = 1) (hu1 : u ≠ 1)
    (hu'1 : u' ≠ 1) : ∃ y ∈ suzL, y * u * y⁻¹ = u' := by
  set v := suzLEquiv.symm ⟨u, hu⟩ with hv
  set v' := suzLEquiv.symm ⟨u', hu'⟩ with hv'
  obtain ⟨y, hyS, hy⟩ := CatFactsL4U4.conj_of_mul_mem_S (PSL3Four.S_le_R v.2)
    (PSL3Four.S_le_R v'.2) (mul_self_symm hu hu2) (mul_self_symm hu' hu'2) (symm_ne_one hu hu1)
    (symm_ne_one hu' hu'1) (mul_mem (inv_mem v.2) v'.2)
  refine ⟨suzLEquiv ⟨y, hyS⟩, (suzLEquiv ⟨y, hyS⟩).2, ?_⟩
  have e : (⟨y, hyS⟩ : ↥PSL3Four.S) * v * (⟨y, hyS⟩ : ↥PSL3Four.S)⁻¹ = v' :=
    Subtype.ext hy
  have := congrArg (fun z => ((suzLEquiv z : ↥suzL) : Equiv.Perm (Fin 1782))) e
  simpa only [map_mul, map_inv, hv, hv', MulEquiv.apply_symm_apply, Subgroup.coe_mul,
    Subgroup.coe_inv] using this

end Iso

end CFSG.ComponentClassification.GSThmB.CF23L34
