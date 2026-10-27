module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenWreathAbs
public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenSwapBridge
public import CFSG.LocalAnalysis.OddStandard.AltStdSecFarMain

public section

namespace CFSG.OddStandard.AltStdSec.SwapPattern

open Subgroup Equiv Equiv.Perm CFSG.OddStandard.AltStdBal

variable {G : Type} [Group G] [Finite G] {L Q : Subgroup G} {z u : G}

theorem exists_hom_of_permOf_eq_τ₀ (h : Setting G L 10) (d : Cyc L Q z) (T : ShapeTwo L Q z u)
    (e : L ≃* alternatingGroup (Fin 10))
    (hP : ∀ (y : G) (hy : y ∈ centralizer ({z} : Set G)), (permOf h d e hy).IsSwap →
      ¬ IsConj z y)
    {x : G} (hx : x ∈ centralizer ({z} : Set G)) (hτ : permOf h d e hx = τ₀) :
    ∃ ι' : Perm (Fin 10) →* G, CentData z ι' ∧ NoSwapConj z ι' ∧
      (∀ σ, sign σ = 1 → ι' σ = swapIotaHom h d T e σ) ∧ x = ι' τ₀ := by
  obtain hx' | hx' := eq_swapIota_or h d T e hx
  · rw [hτ] at hx'
    exact ⟨swapIotaHom h d T e, centData_swapIotaHom h d T e,
      noSwapConj_swapIotaHom h d T e hP, fun σ _ => rfl,
      by simpa [swapIotaHom_apply] using hx'⟩
  · rw [hτ] at hx'
    obtain ⟨ι', hC', h1, h2⟩ := (centData_swapIotaHom h d T e).exists_twist
    refine ⟨ι', hC',
      (noSwapConj_swapIotaHom h d T e hP).twist (centData_swapIotaHom h d T e) h1 h2, h1, ?_⟩
    rw [h2 τ₀ sign_τ₀]
    simpa [swapIotaHom_apply] using hx'

theorem twoSecComp_eq_diagSub (h : Setting G L 10) (d : Cyc L Q z) (T : ShapeTwo L Q z u)
    (e : L ≃* alternatingGroup (Fin 10)) {ι' : Perm (Fin 10) →* G}
    (hι' : ∀ σ, sign σ = 1 → ι' σ = swapIotaHom h d T e σ) {x : G} (hx : x = ι' τ₀) :
    twoSecComp e x (fixFin τ₀) = diagSub (ι := ι') hx := by
  have hmem_fix : ∀ i : Fin 10, i ∈ fixFin τ₀ ↔ i ≠ 8 ∧ i ≠ 9 := by
    intro i
    rw [mem_fixFin, τ₀]
    constructor
    · intro h
      refine ⟨fun h8 => ?_, fun h9 => ?_⟩
      · subst h8
        rw [Equiv.swap_apply_left] at h
        exact (by decide : (9 : Fin 10) ≠ 8) h
      · subst h9
        rw [Equiv.swap_apply_right] at h
        exact (by decide : (8 : Fin 10) ≠ 9) h
    · rintro ⟨h8, h9⟩
      exact Equiv.swap_apply_of_ne_of_ne h8 h9
  have haltSub : ∀ g : Perm (Fin 10), g ∈ altSub (fixFin τ₀) ↔ sign g = 1 ∧ g ∈ stab2 8 9 := by
    intro g
    rw [mem_altSub, mem_stab2]
    constructor
    · rintro ⟨hs, hfix⟩
      exact ⟨hs, hfix 8 (by rw [hmem_fix]; decide), hfix 9 (by rw [hmem_fix]; decide)⟩
    · rintro ⟨hs, h8, h9⟩
      refine ⟨hs, fun i hi => ?_⟩
      rw [hmem_fix] at hi
      by_cases hi8 : i = 8
      · subst hi8; exact h8
      · have hi9 : i = 9 := by
          by_contra hi9
          exact hi ⟨hi8, hi9⟩
        subst hi9; exact h9
  apply le_antisymm
  · intro y hy
    unfold twoSecComp at hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨c, hc, rfl⟩ := hy
    rw [Subgroup.mem_subgroupOf] at hc
    obtain ⟨ha, hmem⟩ := mem_corr.1 hc
    obtain ⟨hsign, hstab⟩ := (haltSub _).1 hmem
    obtain ⟨ρ, hρ⟩ := mem_stab2_iff_exists_liftS8.1 hstab
    have hsignρ : sign ρ = 1 := by rw [← sign_liftS8, hρ]; exact hsign
    have hρalt : ρ ∈ alternatingGroup (Fin 8) := Perm.mem_alternatingGroup.2 hsignρ
    obtain ⟨hw, hwe⟩ :=
      swapIota_mem_of_even h d T e (σ := liftS8 ρ)
        (by rw [Perm.mem_alternatingGroup, sign_liftS8]; exact hsignρ)
    have heq : e ⟨↑(swapIota h d T e (liftS8 ρ)), hw⟩ = e ⟨(c : G), ha⟩ := by
      apply Subtype.ext
      rw [hwe, hρ]
    have hcval : (c : G) = ↑(swapIota h d T e (liftS8 ρ)) :=
      (congrArg Subtype.val (e.injective heq)).symm
    have hlift : liftS8Centralizer (ι := ι') hx ρ = c := by
      apply Subtype.ext
      simpa only [liftS8Centralizer_apply, hι' (liftS8 ρ) (by rw [sign_liftS8]; exact hsignρ),
        swapIotaHom_apply] using hcval.symm
    refine Subgroup.mem_map.2 ⟨ρ, hρalt, ?_⟩
    show QuotientGroup.mk' (zpowers (selfC x)) (liftS8Centralizer (ι := ι') hx ρ) =
      QuotientGroup.mk' (zpowers (selfC x)) c
    rw [hlift]
  · intro y hy
    unfold diagSub at hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨ρ, hρalt, rfl⟩ := hy
    have hsignρ : sign ρ = 1 := Perm.mem_alternatingGroup.1 hρalt
    have hsignt : sign (liftS8 ρ) = 1 := by rw [sign_liftS8]; exact hsignρ
    obtain ⟨hw, hwe⟩ :=
      swapIota_mem_of_even h d T e (σ := liftS8 ρ)
        (by rw [Perm.mem_alternatingGroup, sign_liftS8]; exact hsignρ)
    have hlift : (liftS8Centralizer (ι := ι') hx ρ : G) = ↑(swapIota h d T e (liftS8 ρ)) := by
      simp only [liftS8Centralizer_apply, hι' (liftS8 ρ) hsignt, swapIotaHom_apply]
    have ha : (liftS8Centralizer (ι := ι') hx ρ : G) ∈ L := by
      rw [hlift]; exact hw
    have hsub : (⟨(liftS8Centralizer (ι := ι') hx ρ : G), ha⟩ : L) =
        ⟨↑(swapIota h d T e (liftS8 ρ)), hw⟩ := Subtype.ext hlift
    have hmem : ↑(e ⟨(liftS8Centralizer (ι := ι') hx ρ : G), ha⟩) ∈ altSub (fixFin τ₀) := by
      rw [hsub, hwe]
      exact (haltSub (liftS8 ρ)).2 ⟨hsignt, liftS8_mem_stab2 ρ⟩
    refine Subgroup.mem_map.2 ⟨liftS8Centralizer (ι := ι') hx ρ,
      Subgroup.mem_subgroupOf.2 (mem_corr.2 ⟨ha, hmem⟩), ?_⟩
    show QuotientGroup.mk' (zpowers (selfC x)) (liftS8Centralizer (ι := ι') hx ρ) =
      (sigmaX (ι := ι') hx ρ)
    rfl

theorem false_of_wreathOutcome_exact (h : Setting G L 10) (d : Cyc L Q z) (T : ShapeTwo L Q z u)
    (e : L ≃* alternatingGroup (Fin 10)) {x : G} (hx : x ∈ centralizer ({z} : Set G))
    (hτ : permOf h d e hx = τ₀)
    (hP : ∀ (y : G) (hy : y ∈ centralizer ({z} : Set G)), (permOf h d e hy).IsSwap →
      ¬ IsConj z y)
    (hzx : z ∈ centralizer ({x} : Set G))
    (hW : WreathOutcome (QuotientGroup.mk ⟨z, hzx⟩ : TwoSec x)
      (twoSecComp e x (fixFin (permOf h d e hx))) 8) : False := by
  haveI : IsSimpleGroup G := h.std.simple
  have hτsw : (permOf h d e hx).IsSwap := by rw [hτ]; exact isSwap_τ₀
  obtain ⟨hxmul, hxz, hx1⟩ := swap_elt_facts h d T e hx hτsw
  have hx2 : orderOf x = 2 := orderOf_eq_prime (by rw [pow_two]; exact hxmul) hx1
  have hzC : z ∈ centralizer ({z} : Set G) := mem_centralizer_singleton_iff.2 rfl
  have hzxC : z * x ∈ centralizer ({z} : Set G) := mul_mem hzC hx
  have hperm_zx : permOf h d e hzxC = τ₀ := by
    rw [permOf_mul h d e hzC hx hzxC, permOf_self h d e hzC, one_mul, hτ]
  have hfus : ¬ IsConj z (z * x) := hP (z * x) hzxC (by rw [hperm_zx]; exact isSwap_τ₀)
  obtain ⟨ι', hC', hN', hι', hxι'⟩ := exists_hom_of_permOf_eq_τ₀ h d T e hP hx hτ
  have hO : CFSG.oddCore (TwoSec x) = ⊥ := oddCore_twoSec_eq_bot h hx2
  have hE := exactShape_twoSec h d T e (by norm_num) hx hτsw hfus hzx
  have hdiag : twoSecComp e x (fixFin (permOf h d e hx)) = diagSub (ι := ι') hxι' := by
    rw [hτ]
    exact twoSecComp_eq_diagSub h d T e hι' hxι'
  have hzbar : (QuotientGroup.mk ⟨z, hzx⟩ : TwoSec x) = zbar hC' hxι' := by
    unfold zbar
    rw [show (⟨z, hzx⟩ : ↥(centralizer ({x} : Set G))) =
      ⟨z, z_mem_centralizer_of_eq hC' hxι'⟩ from Subtype.ext rfl]
  have hE' : ExactShape (zbar hC' hxι') (diagSub (ι := ι') hxι') 8 := by
    have h := hE
    rw [hzbar, hdiag] at h
    exact h
  obtain ⟨K, hK⟩ := WreathK.exists_of_wreathOutcome hW
  have hK' : WreathK (zbar hC' hxι') (diagSub (ι := ι') hxι') K := by
    have h := hK
    rw [hzbar, hdiag] at h
    exact h
  exact false_of_wreath_abstract h.std.nonab hC' hN' hxι' hO hE' hK'

end CFSG.OddStandard.AltStdSec.SwapPattern
