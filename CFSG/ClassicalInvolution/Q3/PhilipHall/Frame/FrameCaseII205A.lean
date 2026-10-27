module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseII205Defs
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf36Outer
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf7C207

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameSimple FrameCore)

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3.Q3T6D
  CFSG.ClassicalInvolution.Q3
open scoped commutatorElement

open Out


section Gen

variable {G : Type} [Group G] [Finite G]

theorem le_join_of_psi {X M V : Subgroup G} (ψ : ↥X →* P3)
    (hker : ψ.ker = (oddCoreOf X ⊔ M).subgroupOf X)
    (hsign : ∀ x, Equiv.Perm.sign (ψ x).1 = Equiv.Perm.sign (ψ x).2)
    {v : G} (hvX : v ∈ X) (hvV : v ∈ V) (hvv : v * v ∈ M) (hv1 : ψ ⟨v, hvX⟩ ≠ 1) :
    X ≤ oddCoreOf X ⊔ (V ⊔ (M ⊔ sec20O2 X)) := by
  set A : Subgroup G := M ⊔ sec20O2 X with hAdef
  set T : Subgroup G := oddCoreOf X ⊔ (V ⊔ A) with hTdef
  have hAT : A ≤ T := (le_sup_right : A ≤ V ⊔ A).trans le_sup_right
  have hOT : oddCoreOf X ≤ T := le_sup_left
  have hVT : V ≤ T := (le_sup_left : V ≤ V ⊔ A).trans le_sup_right
  have hMT : M ≤ T := (le_sup_left : M ≤ A).trans hAT
  have hO2T : sec20O2 X ≤ T := (le_sup_right : sec20O2 X ≤ A).trans hAT
  have hNT : oddCoreOf X ⊔ M ≤ T := sup_le hOT hMT
  have hvker : (⟨v * v, X.mul_mem hvX hvX⟩ : ↥X) ∈ ψ.ker := by
    rw [hker, Subgroup.mem_subgroupOf]
    exact (le_sup_right : M ≤ oddCoreOf X ⊔ M) hvv
  have hv2 : ψ ⟨v, hvX⟩ * ψ ⟨v, hvX⟩ = 1 := by
    rw [← map_mul]
    exact hvker
  have hvs : Equiv.Perm.sign (ψ ⟨v, hvX⟩).1 = -1 ∧ Equiv.Perm.sign (ψ ⟨v, hvX⟩).2 = -1 := by
    have h1 : (ψ ⟨v, hvX⟩).1 * (ψ ⟨v, hvX⟩).1 = 1 := congrArg Prod.fst hv2
    have h2 : (ψ ⟨v, hvX⟩).2 * (ψ ⟨v, hvX⟩).2 = 1 := congrArg Prod.snd hv2
    by_cases hc : (ψ ⟨v, hvX⟩).1 = 1
    · have hs : Equiv.Perm.sign (ψ ⟨v, hvX⟩).2 = 1 := by rw [← hsign, hc]; simp
      have hc2 : (ψ ⟨v, hvX⟩).2 = 1 := perm3_eq_one_of_even_invol _ h2 hs
      exact absurd (Prod.ext hc hc2) hv1
    · have h1s := sign_of_invol _ hc h1
      exact ⟨h1s, by rw [← hsign]; exact h1s⟩
  have hodd : ∀ g : ↥X, Equiv.Perm.sign (ψ g).1 = 1 → ∃ y : ↥X, (y : G) ∈ T ∧ ψ y = ψ g := by
    intro g hg1
    have hg2 : Equiv.Perm.sign (ψ g).2 = 1 := by rw [← hsign]; exact hg1
    have hg3 : ψ g ^ 3 = 1 := Prod.ext (cube_of_sign _ hg1) (cube_of_sign _ hg2)
    have hord0 : orderOf g ≠ 0 := (orderOf_pos g).ne'
    obtain ⟨e, r, hr2, hre⟩ := Nat.exists_eq_pow_mul_and_not_dvd hord0 2 (by norm_num)
    have hdvd : 2 ^ e ∣ orderOf g := ⟨r, hre⟩
    have hy_ord : orderOf (g ^ (2 ^ e)) = r := by
      rw [orderOf_pow_of_dvd (by positivity) hdvd, hre, Nat.mul_div_cancel_left _ (by positivity)]
    have hr_odd : Odd r := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hr2)
    refine ⟨(g ^ (2 ^ e)) ^ (2 ^ e), ?_, ?_⟩
    · have hy0 : Odd (orderOf (((g ^ (2 ^ e) : ↥X)) : G)) := by
        rw [Subgroup.orderOf_coe, hy_ord]
        exact hr_odd
      have hy0T : (((g ^ (2 ^ e) : ↥X)) : G) ∈ sec20O2 X :=
        Subgroup.subset_closure ⟨(g ^ (2 ^ e)).2, hy0⟩
      have := Subgroup.pow_mem _ hy0T (2 ^ e)
      exact hO2T (by simpa using this)
    · rw [map_pow, map_pow, ← pow_mul]
      have hmod : (2 ^ e * 2 ^ e) % 3 = 1 := by
        rw [← pow_add, ← two_mul, pow_mul]
        norm_num [Nat.pow_mod]
      calc ψ g ^ (2 ^ e * 2 ^ e)
          = ψ g ^ (3 * ((2 ^ e * 2 ^ e) / 3) + (2 ^ e * 2 ^ e) % 3) := by
            rw [Nat.div_add_mod]
        _ = ψ g := by rw [hmod, pow_add, pow_mul, hg3, one_pow, one_mul, pow_one]
  have hcover : ∀ g : ↥X, ∃ y : ↥X, (y : G) ∈ T ∧ ψ y = ψ g := by
    intro g
    rcases Int.units_eq_one_or (Equiv.Perm.sign (ψ g).1) with h1 | h1
    · exact hodd g h1
    · have h2 : Equiv.Perm.sign (ψ g).2 = -1 := by rw [← hsign]; exact h1
      obtain ⟨y', hy'T, hy'⟩ := hodd (g * ⟨v, hvX⟩⁻¹) (by
        rw [map_mul, map_inv]
        simp only [Prod.fst_mul, Prod.fst_inv, map_mul, map_inv, h1, hvs.1]
        norm_num)
      refine ⟨y' * ⟨v, hvX⟩, ?_, ?_⟩
      · exact T.mul_mem hy'T (hVT hvV)
      · rw [map_mul, hy', map_mul, map_inv, inv_mul_cancel_right]
  intro x hx
  obtain ⟨y, hyT, hy⟩ := hcover ⟨x, hx⟩
  have hk : (⟨x, hx⟩ * y⁻¹ : ↥X) ∈ ψ.ker := by
    show ψ _ = 1
    rw [map_mul, map_inv, hy, mul_inv_cancel]
  rw [hker, Subgroup.mem_subgroupOf] at hk
  have hxy : x = (x * (y : G)⁻¹) * y := by group
  rw [hxy]
  exact T.mul_mem (hNT hk) hyT

end Gen

section Main

variable {G : Type} [Group G] [Finite G] [FrameCore G] {K K' J : Subgroup G} {S : Sylow 2 G}
  {R R' W V : Subgroup G} {z t : G}

theorem aConf_le_centralizer_W (d : Std20Frame K K' J S R R' W V z t) {a : G}
    (conf : AConf3 S K K' J z a) : W ≤ Subgroup.centralizer ({a} : Set G) := by
  rw [d.late_hW]
  refine sup_le (fun w hw => Subgroup.mem_centralizer_singleton_iff.mpr
    (d.cent_comm_WK conf.hA.1 hw).symm) (fun w hw => Subgroup.mem_centralizer_singleton_iff.mpr ?_)
  exact (commutes_of_mem_centModOddCore S.isPGroup'
    (mem_centModOddCore_of_mem_centralizerModOdd conf.hA) conf.hA.1.1 hw.2 (d.hWS hw.1)).symm

@[expose] def centModSub (X N : Subgroup G) (a : G) (hN : X ≤ Subgroup.normalizer (N : Set G)) :
    Subgroup G where
  carrier := {y | y ∈ X ∧ a * y * a⁻¹ * y⁻¹ ∈ N}
  one_mem' := ⟨X.one_mem, by simp⟩
  mul_mem' := by
    rintro y₁ y₂ ⟨h₁, c₁⟩ ⟨h₂, c₂⟩
    refine ⟨X.mul_mem h₁ h₂, ?_⟩
    have e : a * (y₁ * y₂) * a⁻¹ * (y₁ * y₂)⁻¹ =
        (a * y₁ * a⁻¹ * y₁⁻¹) * (y₁ * (a * y₂ * a⁻¹ * y₂⁻¹) * y₁⁻¹) := by group
    rw [e]
    exact N.mul_mem c₁ ((Subgroup.mem_normalizer_iff.mp (hN h₁) _).mp c₂)
  inv_mem' := by
    rintro y ⟨h, c⟩
    refine ⟨X.inv_mem h, ?_⟩
    have e : a * y⁻¹ * a⁻¹ * y⁻¹⁻¹ = y⁻¹ * (a * y * a⁻¹ * y⁻¹)⁻¹ * y⁻¹⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hN (X.inv_mem h)) _).mp (N.inv_mem c)

theorem frame20ACentX_of_gen (d : Std20Frame K K' J S R R' W V z t) {a : G}
    (conf : AConf3 S K K' J z a)
    (hcL : a ∈ centralizerModOdd (S : Subgroup G)
      (K ⊔ K' ⊔ sec20O2 (sec20X (CoreAssembly.conjClass K) z K K')))
    (hgen : sec20X (CoreAssembly.conjClass K) z K K' ≤
      oddCoreOf (sec20X (CoreAssembly.conjClass K) z K K') ⊔
        (V ⊔ (K ⊔ K' ⊔ sec20O2 (sec20X (CoreAssembly.conjClass K) z K K')))) :
    ∀ x ∈ sec20X (CoreAssembly.conjClass K) z K K',
      a * x * a⁻¹ * x⁻¹ ∈ oddCoreOf (sec20X (CoreAssembly.conjClass K) z K K') := by
  intro x hx
  set X := sec20X (CoreAssembly.conjClass K) z K K' with hXdef
  set L := K ⊔ K' ⊔ sec20O2 X with hLdef
  have hXz : X ≤ Subgroup.centralizer ({z} : Set G) :=
    sec20X_le_centralizer (le_sup_left.trans d.sup_le_centralizer_z)
      (le_sup_right.trans d.sup_le_centralizer_z)
  have haX : a ∈ Subgroup.normalizer (X : Set G) :=
    le_normalizer_sec20X d.hyp.conjInvariant d.viol.hzK d.twins (d.hSz conf.hA.1.1)
  have haO : a ∈ Subgroup.normalizer (oddCoreOf X : Set G) :=
    mem_normalizer_oddCore_of_mem_normalizer haX
  have hXO : X ≤ Subgroup.normalizer (oddCoreOf X : Set G) :=
    fun y hy => mem_normalizer_oddCore_of_mem_normalizer (Subgroup.le_normalizer hy)
  have hO2X : sec20O2 X ≤ X := (Subgroup.closure_le _).mpr fun y hy => hy.1
  have hLX : L ≤ X := sup_le le_sec20X_pair hO2X
  have hXL : X ≤ Subgroup.normalizer (L : Set G) := by
    intro y hy
    have h1 : y ∈ Subgroup.normalizer ((K ⊔ K' : Subgroup G) : Set G) :=
      le_normalizer_sup_pair d.hyp.conjInvariant d.viol.hzK d.twins d.ne (hXz hy)
    have h2 : y ∈ Subgroup.normalizer (sec20O2 X : Set G) :=
      Asc77.T3CII.mem_normalizer_of_conjSub_le (conjSub_sec20O2_le (Subgroup.le_normalizer hy))
    rw [mem_normalizer_iff_conjSub_eq] at h1 h2 ⊢
    rw [hLdef, conjSub_sup, h1, h2]
  have hOL : oddCoreOf L ≤ oddCoreOf X :=
    AscFusion.le_oddCoreOf_of_normal_odd ((oddCoreOf_le_self L).trans hLX)
      (fun c hc => mem_normalizer_oddCore_of_mem_normalizer (hXL hc)) (oddCoreOf_odd_natCard L)
  set T := centModSub X (oddCoreOf X) a hXO with hTdef
  have hOT : oddCoreOf X ≤ T := fun o ho => ⟨oddCoreOf_le_self X ho,
    (oddCoreOf X).mul_mem ((Subgroup.mem_normalizer_iff.mp haO o).mp ho) ((oddCoreOf X).inv_mem ho)⟩
  have hLT : L ≤ T := fun l hl => ⟨hLX hl, by
    have := hcL.2.2.2 l hl
    rw [commutatorElement_def] at this
    exact hOL this⟩
  have tw : Twin20 (CoreAssembly.conjClass K) K K' z (S : Subgroup G) V :=
    ⟨d.hyp.conjInvariant, d.viol.hzK, d.twins, d.ne, d.hSz, d.hV, d.hVS,
      Sec6Gen.isPGroup_of_mem_USet d.late_hΩ d.hV⟩
  have hVX : V ≤ X := tw.hVX
  have hWa := aConf_le_centralizer_W d conf
  have hVT : V ≤ T := fun v hv => ⟨hVX hv, by
    have hc : v * a = a * v := Subgroup.mem_centralizer_singleton_iff.mp (hWa (d.hVW hv))
    have : a * v * a⁻¹ * v⁻¹ = 1 := by rw [← hc]; group
    rw [this]
    exact (oddCoreOf X).one_mem⟩
  have hKT : K ⊔ K' ≤ T := (le_sup_left : K ⊔ K' ≤ L).trans hLT
  have hO2T : sec20O2 X ≤ T := (le_sup_right : sec20O2 X ≤ L).trans hLT
  have hXT : X ≤ T := hgen.trans (sup_le hOT (sup_le hVT (sup_le hKT hO2T)))
  exact (hXT hx).2

theorem frame20ACentX'_of_cent (hC : Frame203Cent) : Frame20ACentX' := by
  intro G _ _ _ K K' J S R R' W V z t d a conf hcL
  obtain ⟨ψ, hker, hsign, -, v, hvX, hvV, hvv, hv1⟩ :=
    frame203Psi_of hC frame203Outer G K K' J S R R' W V z t d
  exact frame20ACentX_of_gen d conf hcL (le_join_of_psi ψ hker hsign hvX hvV hvv hv1)

end Main

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
