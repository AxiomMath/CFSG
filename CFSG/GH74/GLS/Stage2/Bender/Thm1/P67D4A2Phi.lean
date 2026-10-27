module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4A2Central
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4A2Root
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4A2Sl2
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4A2CardU

public noncomputable section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4 CFSG.Timmesfeld.RankTwo
  CFSG.GH74.GLS.SP CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage2.OddAut
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.CentralExt.TrialityClosed CFSG.GH74.GLS.Stage2.Signalizer.Odd87
  CFSG.LocalAnalysis.ComponentInitial

variable {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {d : Kˣ} {q : ℕ}

theorem A2Std.cube_apply (h : A2Std σ d q) : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c :=
  sigma_three_of_card (σ := σ.toRingHom) h.card (fun c => h.frob c)

theorem A2Core.cube_apply (h : A2Core σ d q) :
    ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c :=
  sigma_three_of_card (σ := σ.toRingHom) h.card (fun c => h.frob c)

@[expose] def A2Core.a2Equiv (h : A2Core σ d q) :
    twistedGroup σ.toRingHom ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
  (Subgroup.equivMapOfInjective (twistedGroup σ.toRingHom) (adjointGroup d4 K).subtype
    Subtype.val_injective).trans
    (MulEquiv.subgroupCongr h.twisted_eq)

@[expose, reducible] def a2Equiv (h : A2Std σ d q) :
    twistedGroup σ.toRingHom ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
  A2Core.a2Equiv h.toCore

theorem A2Core.coe_a2Equiv (h : A2Core σ d q) (x : twistedGroup σ.toRingHom) :
    ((a2Equiv h x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) : ModGL TwistTag.D4.tag K) =
      (((x : twistedGroup σ.toRingHom) : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) :=
  rfl

theorem A2Core.coe_a2Equiv_symm (h : A2Core σ d q)
    (y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
    ((((a2Equiv h).symm y : twistedGroup σ.toRingHom) : adjointGroup d4 K) :
      ModGL TwistTag.D4.tag K) = (y : ModGL TwistTag.D4.tag K) := by
  have := coe_a2Equiv h ((a2Equiv h).symm y)
  rw [MulEquiv.apply_symm_apply] at this
  exact this.symm

@[expose] def A2Core.a2Phi (h : A2Core σ d q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
    MulAut (twistedGroup σ.toRingHom) :=
  ((a2Equiv h).trans φ).trans (a2Equiv h).symm

@[expose, reducible] def a2Phi (h : A2Std σ d q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
    MulAut (twistedGroup σ.toRingHom) :=
  A2Core.a2Phi h.toCore φ

theorem A2Core.coe_a2Phi (h : A2Core σ d q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K))
    (x : twistedGroup σ.toRingHom) :
    (((a2Phi h φ x : twistedGroup σ.toRingHom) : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) =
      a2Conj σ d (((x : twistedGroup σ.toRingHom) : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) := by
  show ((((a2Equiv h).symm (φ (a2Equiv h x)) : twistedGroup σ.toRingHom) : adjointGroup d4 K) :
    ModGL TwistTag.D4.tag K) = _
  rw [coe_a2Equiv_symm, hφ, coe_a2Equiv]

theorem A2Core.a2Phi_eq_iff (h : A2Core σ d q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K))
    (x : twistedGroup σ.toRingHom) :
    a2Phi h φ x = x ↔
      a2Conj σ d (((x : twistedGroup σ.toRingHom) : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) =
        (((x : twistedGroup σ.toRingHom) : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) := by
  rw [← coe_a2Phi h φ hφ x]
  constructor
  · intro hx
    rw [hx]
  · intro hx
    exact Subtype.ext (Subtype.ext (Units.ext (congrArg Units.val hx)))

theorem a2Phi_eq_iff (h : A2Std σ d q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K))
    (x : twistedGroup σ.toRingHom) :
    a2Phi h φ x = x ↔
      a2Conj σ d (((x : twistedGroup σ.toRingHom) : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) =
        (((x : twistedGroup σ.toRingHom) : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) :=
  A2Core.a2Phi_eq_iff h.toCore φ hφ x

theorem d43Long_hexPos_of_isRoot {k : ℤ} (hk : CFSG.GH74.BNPair.IsRoot 6 k) : d43Long (hexPos k) ↔ k % 2 = 0 := by
  obtain ⟨h0, h6⟩ := hk
  rcases lt_or_gt_of_ne h0 with hneg | hpos
  · have hpos' : 1 ≤ -k := by omega
    have e := hexPos_neg hpos' (by omega : -k ≤ 6)
    rw [neg_neg] at e
    have h1 := d43Long_hexPos hpos' (by omega : -k ≤ 6)
    rw [e]
    have : d43Long (-hexPos (-k)) ↔ d43Long (hexPos (-k)) := by
      change (3 : ℤ) ∣ (-hexPos (-k)) (1 : Fin 2) ↔ (3 : ℤ) ∣ (hexPos (-k)) (1 : Fin 2)
      simp
    rw [this, h1]
    omega
  · exact d43Long_hexPos (by omega) (by omega)

theorem A2Core.a2_mem_H (h : A2Core σ d q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K))
    {x : twistedGroup σ.toRingHom} (hx : x ∈ ⨆ i, hHat σ.toRingHom i) :
    a2Phi h φ x ∈ ⨆ i, hHat σ.toRingHom i := by
  refine Subgroup.iSup_induction (C := fun x => a2Phi h φ x ∈ ⨆ i, hHat σ.toRingHom i)
    (fun i => hHat σ.toRingHom i) hx ?_ ?_ ?_
  · intro i y hy
    have hy' : ((y : twistedGroup σ.toRingHom) : adjointGroup d4 K) ∈ hHatE σ.toRingHom i := hy
    obtain ⟨g', hg', hg'eq⟩ := a2_torus_stable h i hy'
    have e : (((a2Phi h φ y : twistedGroup σ.toRingHom) : adjointGroup d4 K)) = g' :=
      Subtype.ext ((coe_a2Phi h φ hφ y).trans hg'eq.symm)
    exact Subgroup.mem_iSup_of_mem i (by
      change ((a2Phi h φ y : twistedGroup σ.toRingHom) : adjointGroup d4 K) ∈ hHatE σ.toRingHom i
      rw [e]; exact hg')
  · rw [map_one]; exact one_mem _
  · intro x y hx hy
    rw [map_mul]
    exact mul_mem hx hy

theorem A2Core.a2_mem_root (h : A2Core σ d q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K))
    {k : ℤ} (hk : CFSG.GH74.BNPair.IsRoot 6 k) {x : twistedGroup σ.toRingHom}
    (hx : x ∈ hexGroup (twistedX σ.toRingHom) k) :
    a2Phi h φ x ∈ hexGroup (twistedX σ.toRingHom) k := by
  have hγ : IsRoot .G2 (hexPos k) := isRoot_hexPos hk.1 hk.2
  have hx' : ((x : twistedGroup σ.toRingHom) : adjointGroup d4 K) ∈
      twistedRootSubgroupD4 σ.toRingHom (hexPos k) := hx
  obtain ⟨g', hg', hg'eq⟩ := a2_root_stable h hγ hx'
  have e : (((a2Phi h φ x : twistedGroup σ.toRingHom) : adjointGroup d4 K)) = g' :=
    Subtype.ext ((coe_a2Phi h φ hφ x).trans hg'eq.symm)
  change ((a2Phi h φ x : twistedGroup σ.toRingHom) : adjointGroup d4 K) ∈
    twistedRootSubgroupD4 σ.toRingHom (hexPos k)
  rw [e]; exact hg'

theorem A2Core.a2_weyl_one_fix (h : A2Core σ d q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K)) :
    a2Phi h φ (nHat σ.toRingHom (1 : Fin 2)) = nHat σ.toRingHom (1 : Fin 2) := by
  rw [a2Phi_eq_iff h φ hφ]
  exact a2_weyl_one h

theorem A2Core.a2_r₂_mem (h : A2Core σ d q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K)) :
    (nHat σ.toRingHom (0 : Fin 2))⁻¹ * a2Phi h φ (nHat σ.toRingHom (0 : Fin 2)) ∈ ⨆ i, hHat σ.toRingHom i := by
  obtain ⟨t, ht, hteq⟩ := a2_weyl_zero h
  set y : twistedGroup σ.toRingHom := (nHat σ.toRingHom (0 : Fin 2))⁻¹ * a2Phi h φ (nHat σ.toRingHom (0 : Fin 2))
    with hy
  have hmat := coe_a2Phi h φ hφ (nHat σ.toRingHom (0 : Fin 2))
  have e1 : ((a2Phi h φ (nHat σ.toRingHom (0 : Fin 2)) : twistedGroup σ.toRingHom) : adjointGroup d4 K) =
      nHatE K (ng 0) * t := by
    apply Subtype.ext
    rw [hmat]
    exact hteq
  have e2 : ((y : twistedGroup σ.toRingHom) : adjointGroup d4 K) = t := by
    rw [hy]
    change ((nHat σ.toRingHom (0 : Fin 2) : twistedGroup σ.toRingHom) : adjointGroup d4 K)⁻¹ *
      ((a2Phi h φ (nHat σ.toRingHom (0 : Fin 2)) : twistedGroup σ.toRingHom) : adjointGroup d4 K) = t
    rw [e1]
    show (nHatE K (ng 0))⁻¹ * (nHatE K (ng 0) * t) = t
    group
  exact Subgroup.mem_iSup_of_mem (ng 0) (by
    change ((y : twistedGroup σ.toRingHom) : adjointGroup d4 K) ∈ hHatE σ.toRingHom (ng 0)
    rw [e2]; exact ht)

theorem A2Core.a2_even_fix (h : A2Core σ d q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K))
    {k : ℤ} (hk : CFSG.GH74.BNPair.IsRoot 6 k) (hk2 : k % 2 = 0)
    {x : twistedGroup σ.toRingHom} (hx : x ∈ hexGroup (twistedX σ.toRingHom) k)
    (hfix : a2Phi h φ x = x) : x = 1 := by
  have hγ : IsRoot .G2 (hexPos k) := isRoot_hexPos hk.1 hk.2
  have hl : d43Long (hexPos k) := (d43Long_hexPos_of_isRoot hk).2 hk2
  have hx' : ((x : twistedGroup σ.toRingHom) : adjointGroup d4 K) ∈
      twistedRootSubgroupD4 σ.toRingHom (hexPos k) := hx
  have := a2_long_fix h hγ hl hx' ((a2Phi_eq_iff h φ hφ x).1 hfix)
  exact Subtype.ext this

theorem A2Core.a2_odd_fix (h : A2Core σ d q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K))
    {k : ℤ} (hk : CFSG.GH74.BNPair.IsRoot 6 k) (hk2 : k % 2 ≠ 0) :
    ∃ x ∈ hexGroup (twistedX σ.toRingHom) k, x ≠ 1 ∧ a2Phi h φ x = x := by
  have hγ : IsRoot .G2 (hexPos k) := isRoot_hexPos hk.1 hk.2
  have hs : ¬ d43Long (hexPos k) := fun hl => hk2 ((d43Long_hexPos_of_isRoot hk).1 hl)
  obtain ⟨g, hg, hg1, hgfix⟩ := a2_short_fix h hγ hs
  have hgΓ : g ∈ twistedGroup σ.toRingHom := twistedRootSubgroupD4_le_twistedGroup σ.toRingHom hγ hg
  refine ⟨⟨g, hgΓ⟩, hg, fun he => hg1 (congrArg Subtype.val he), ?_⟩
  rw [a2Phi_eq_iff h φ hφ]
  exact hgfix

theorem A2Core.a2_hZ (h : A2Core σ d q) {g : twistedGroup σ.toRingHom}
    (hcomm : ∀ i, CFSG.GH74.BNPair.IsRoot 6 i → ∀ x ∈ hexGroup (twistedX σ.toRingHom) i,
      g * x = x * g) : g = 1 := by
  have hZ := twistedGroup_center_eq_bot_of_card (σ := σ.toRingHom) h.two_le h.card
    (fun c => h.frob c)
  have hle : (⨆ β ∈ (twistedDatum σ.toRingHom).roots,
      (twistedDatum σ.toRingHom).rootGroup β) ≤ Subgroup.centralizer ({g} : Set _) := by
    refine iSup₂_le fun β hβ => ?_
    rw [twistedDatum_roots] at hβ
    obtain ⟨i, hi, rfl⟩ := isRoot_iff.1 hβ
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro g' hg'
    rw [Set.mem_singleton_iff] at hg'
    subst hg'
    exact hcomm i (mem_hexIdx_iff.1 hi) z hz
  have hg : g ∈ Subgroup.center (twistedGroup σ.toRingHom) := by
    rw [Subgroup.mem_center_iff]
    intro z
    have hz : z ∈ ⨆ β ∈ (twistedDatum σ.toRingHom).roots,
        (twistedDatum σ.toRingHom).rootGroup β := by
      rw [iSup_twistedDatum_rootGroup]; trivial
    have := (Subgroup.mem_centralizer_iff.1 (hle hz)) g (Set.mem_singleton g)
    exact this.symm
  rw [hZ] at hg
  exact Subgroup.mem_bot.1 hg

theorem a2_hZ (h : A2Std σ d q) {g : twistedGroup σ.toRingHom}
    (hcomm : ∀ i, CFSG.GH74.BNPair.IsRoot 6 i → ∀ x ∈ hexGroup (twistedX σ.toRingHom) i,
      g * x = x * g) : g = 1 :=
  A2Core.a2_hZ h.toCore hcomm

omit
  [Finite K] in
theorem a2_mem_hHatE_iSup (x : twistedGroup σ.toRingHom) (hx : x ∈ ⨆ i, hHat σ.toRingHom i) :
    ((x : twistedGroup σ.toRingHom) : adjointGroup d4 K) ∈ ⨆ i, hHatE σ.toRingHom i := by
  refine Subgroup.iSup_induction (C := fun x : twistedGroup σ.toRingHom =>
    ((x : twistedGroup σ.toRingHom) : adjointGroup d4 K) ∈ ⨆ i, hHatE σ.toRingHom i)
    (fun i => hHat σ.toRingHom i) hx ?_ ?_ ?_
  · intro i y hy
    exact Subgroup.mem_iSup_of_mem i hy
  · exact one_mem _
  · intro x y hx hy
    exact mul_mem hx hy

theorem A2Core.a2_hz (h : A2Core σ d q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K))
    (x : twistedGroup σ.toRingHom) (hx : x ∈ ⨆ i, hHat σ.toRingHom i) :
    a2Phi h φ ((nHat σ.toRingHom (1 : Fin 2) * nHat σ.toRingHom (0 : Fin 2)) ^ 3 * x) ≠
      (nHat σ.toRingHom (1 : Fin 2) * nHat σ.toRingHom (0 : Fin 2)) ^ 3 * x := by
  intro hfix
  rw [a2Phi_eq_iff h φ hφ] at hfix
  exact a2_central_weyl h (a2_mem_hHatE_iSup x hx) hfix

theorem a2_hz (h : A2Std σ d q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K))
    (x : twistedGroup σ.toRingHom) (hx : x ∈ ⨆ i, hHat σ.toRingHom i) :
    a2Phi h φ ((nHat σ.toRingHom (1 : Fin 2) * nHat σ.toRingHom (0 : Fin 2)) ^ 3 * x) ≠
      (nHat σ.toRingHom (1 : Fin 2) * nHat σ.toRingHom (0 : Fin 2)) ^ 3 * x :=
  A2Core.a2_hz h.toCore φ hφ x hx

theorem A2Core.a2_foldData (h : A2Core σ d q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K)) :
    FoldData (d4RGD2 σ.toRingHom h.cube_apply) (a2Phi h φ) where
  mem_H x hx := a2_mem_H h φ hφ hx
  mem_root k hk x hx := a2_mem_root h φ hφ hk hx
  r₁_mem := by
    rw [a2_weyl_one_fix h φ hφ, inv_mul_cancel]
    exact one_mem _
  r₂_mem := a2_r₂_mem h φ hφ
  even_fix k hk hk2 x hx hfix := a2_even_fix h φ hφ hk hk2 hx hfix
  odd_fix k hk hk2 := a2_odd_fix h φ hφ hk hk2

theorem a2_foldData (h : A2Std σ d q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K)) :
    FoldData (d4RGD2 σ.toRingHom h.cube_apply) (a2Phi h φ) :=
  A2Core.a2_foldData h.toCore φ hφ

theorem A2Core.a2_foldFix_not_solvable (h : A2Core σ d q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K)) :
    ¬ Group.IsSolvable ↥(foldFix (a2Phi h φ)) := by
  intro hsolv
  obtain ⟨S, hS, hSfix⟩ := a2_not_solvable h
  apply hS
  have hle : S ≤ foldFix (a2Phi h φ) := fun x hx => (a2Phi_eq_iff h φ hφ x).2 (hSfix x hx)
  have : Group.IsSolvable ↥(S.subgroupOf (foldFix (a2Phi h φ))) :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.subtype (S.subgroupOf (foldFix (a2Phi h φ))))
      Subtype.val_injective
  exact Group.isSolvable_of_isSolvable_injective
    (f := (Subgroup.subgroupOfEquivOfLe hle).symm.toMonoidHom) (MulEquiv.injective _)

theorem A2Core.a2_foldFix_map (h : A2Core σ d q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (_hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K)) :
    (foldFix (a2Phi h φ)).map (a2Equiv h).toMonoidHom = fixSub φ := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_fixSub]
    have hx' : a2Phi h φ x = x := hx
    have := congrArg (a2Equiv h) hx'
    change (a2Equiv h) ((a2Equiv h).symm (φ (a2Equiv h x))) = a2Equiv h x at this
    rw [MulEquiv.apply_symm_apply] at this
    exact this
  · intro hy
    have hy' : φ y = y := hy
    refine ⟨(a2Equiv h).symm y, ?_, (a2Equiv h).apply_symm_apply y⟩
    show a2Phi h φ ((a2Equiv h).symm y) = (a2Equiv h).symm y
    show (a2Equiv h).symm (φ (a2Equiv h ((a2Equiv h).symm y))) = (a2Equiv h).symm y
    rw [MulEquiv.apply_symm_apply, hy']

theorem a2_foldFix_map (h : A2Std σ d q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (_hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K)) :
    (foldFix (a2Phi h φ)).map (a2Equiv h).toMonoidHom = fixSub φ :=
  A2Core.a2_foldFix_map h.toCore φ _hφ

theorem A2Core.a2_card_foldRoot (h : A2Core σ d q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K))
    {k : ℤ} (hk : CFSG.GH74.BNPair.IsRoot 3 k) :
    Nat.card ↥(foldRoot (a2Phi h φ) (hexGroup (twistedX σ.toRingHom)) k) = q := by
  have hk' : CFSG.GH74.BNPair.IsRoot 6 (foldIdx k) := isRoot_foldIdx hk
  have hγ : IsRoot .G2 (hexPos (foldIdx k)) := isRoot_hexPos hk'.1 hk'.2
  have hs : ¬ d43Long (hexPos (foldIdx k)) := fun hl =>
    foldIdx_odd hk.1 ((d43Long_hexPos_of_isRoot hk').1 hl)
  refine Eq.trans (Nat.card_congr (Equiv.ofBijective
    (fun x : ↥(foldRoot (a2Phi h φ) (hexGroup (twistedX σ.toRingHom)) k) =>
      (⟨⟨((x.1 : twistedGroup σ.toRingHom) : adjointGroup d4 K), x.2.1⟩,
        (a2Phi_eq_iff h φ hφ x.1).1 x.2.2⟩ :
        {g : ↥(twistedRootSubgroupD4 σ.toRingHom (hexPos (foldIdx k))) //
          a2Conj σ d ((g : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) =
            ((g : adjointGroup d4 K) : ModGL TwistTag.D4.tag K)})) ⟨?_, ?_⟩))
    (a2_short_fix_card h hγ hs)
  · intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z => (z.1.1 : adjointGroup d4 K)) hxy
  · rintro ⟨g, hg⟩
    have hΓ : (g : adjointGroup d4 K) ∈ twistedGroup σ.toRingHom :=
      twistedRootSubgroupD4_le_twistedGroup σ.toRingHom hγ g.2
    refine ⟨⟨⟨g.1, hΓ⟩, g.2, ?_⟩, rfl⟩
    exact (a2Phi_eq_iff h φ hφ ⟨g.1, hΓ⟩).2 hg

theorem a2_card_foldRoot (h : A2Std σ d q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K))
    {k : ℤ} (hk : CFSG.GH74.BNPair.IsRoot 3 k) :
    Nat.card ↥(foldRoot (a2Phi h φ) (hexGroup (twistedX σ.toRingHom)) k) = q :=
  A2Core.a2_card_foldRoot h.toCore φ hφ hk

theorem A2Core.a2_card_U_fix (h : A2Core σ d q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K))
    {r₁' r₂' : twistedGroup σ.toRingHom}
    (R' : RGD2 3 ((⨆ i, hHat σ.toRingHom i) ⊓ foldFix (a2Phi h φ)) r₁' r₂'
      ((posUnipotent (g2Shape (twistedX σ.toRingHom))) ⊓ foldFix (a2Phi h φ))
      (foldRoot (a2Phi h φ) (hexGroup (twistedX σ.toRingHom)))) :
    Nat.card ↥((posUnipotent (g2Shape (twistedX σ.toRingHom))) ⊓ foldFix (a2Phi h φ)) = q ^ 3 := by
  have : Finite (twistedGroup σ.toRingHom) := Finite.of_equiv _ (a2Equiv h).symm.toEquiv
  exact R'.card_U_of_card_root (fun k hk1 hk3 => a2_card_foldRoot h φ hφ (k := k) ⟨by omega, by omega⟩)

theorem a2_card_U_fix (h : A2Std σ d q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K))
    {r₁' r₂' : twistedGroup σ.toRingHom}
    (R' : RGD2 3 ((⨆ i, hHat σ.toRingHom i) ⊓ foldFix (a2Phi h φ)) r₁' r₂'
      ((posUnipotent (g2Shape (twistedX σ.toRingHom))) ⊓ foldFix (a2Phi h φ))
      (foldRoot (a2Phi h φ) (hexGroup (twistedX σ.toRingHom)))) :
    Nat.card ↥((posUnipotent (g2Shape (twistedX σ.toRingHom))) ⊓ foldFix (a2Phi h φ)) = q ^ 3 :=
  A2Core.a2_card_U_fix h.toCore φ hφ R'

