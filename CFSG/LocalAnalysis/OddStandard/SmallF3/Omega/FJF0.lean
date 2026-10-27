module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GXDef
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeZ2
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3ClTwoU43Aut
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.M6ZCnt
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFSimCard

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private theorem fj_mem_omega_of_four_plus (hQ : Q.Nondegenerate) {u : OGroup Q}
    (huu : u * u = 1) (hu : invType u = (4, 1)) : u ∈ omegaGroup hQ := by
  rw [involution_mem_omegaGroup_iff hQ huu]
  have hd : invDim u = 4 := congrArg Prod.fst hu
  have hs : invSign u = 1 := congrArg Prod.snd hu
  rw [hd, hs]
  exact ⟨by decide, by decide⟩

private theorem fj_simAct_four_plus (hQ : Q.Nondegenerate) (γ : simGroup Q) {u : OGroup Q}
    (huu : u * u = 1) (hu : invType u = (4, 1)) :
    simAct Q γ u * simAct Q γ u = 1 ∧ invType (simAct Q γ u) = (4, 1) := by
  obtain ⟨c, hc⟩ := γ.2
  have hEq : simAct Q γ u = simConj hc u := Subtype.ext (by rw [coe_simAct, coe_simConj])
  rw [hEq]
  obtain ⟨h1, h2⟩ := invType_simConj hQ hc huu
  refine ⟨h1, ?_⟩
  rw [h2]
  have hd : invDim u = 4 := congrArg Prod.fst hu
  have hs : invSign u = 1 := congrArg Prod.snd hu
  rw [hd, hs]
  refine Prod.ext rfl ?_
  change toSign c ^ 4 * 1 = 1
  rw [mul_one, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Int.units_sq]

theorem fj_exists_fixed_involution_six_minus (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hs : quadSign Q = -1)
    (α : MulAut (omegaGroup hQ)) (hα : α * α = 1) :
    ∃ e : omegaGroup hQ, orderOf e = 2 ∧ α e = e ∧ e ∉ center (omegaGroup hQ) := by
  classical
  obtain ⟨γ, -, hγ⟩ := cl_exists_simil_of_mulAut_six_minus hQ hdim hs α hα
  have hcard := m6z_card_four_plus_six_minus hQ hdim hs
  haveI : Finite {u : OGroup Q // u * u = 1 ∧ invType u = (4, 1)} :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  letI : Fintype {u : OGroup Q // u * u = 1 ∧ invType u = (4, 1)} := Fintype.ofFinite _
  let φ : {u : OGroup Q // u * u = 1 ∧ invType u = (4, 1)} →
      {u : OGroup Q // u * u = 1 ∧ invType u = (4, 1)} :=
    fun u => ⟨simAct Q γ u.1, fj_simAct_four_plus hQ γ u.2.1 u.2.2⟩
  have hφφ : ∀ u, φ (φ u) = u := by
    intro u
    apply Subtype.ext
    have hu := fj_mem_omega_of_four_plus hQ u.2.1 u.2.2
    have h1 : (((α ⟨u.1, hu⟩ : omegaGroup hQ)) : OGroup Q) = simAct Q γ u.1 := hγ ⟨u.1, hu⟩
    have h2 := hγ (α ⟨u.1, hu⟩)
    rw [h1] at h2
    have h3 : α (α ⟨u.1, hu⟩) = ⟨u.1, hu⟩ := by
      have := congrArg (fun m : MulAut (omegaGroup hQ) => m ⟨u.1, hu⟩) hα
      simpa using this
    rw [h3] at h2
    exact h2.symm
  let π' : Equiv.Perm {u : OGroup Q // u * u = 1 ∧ invType u = (4, 1)} :=
    ⟨φ, φ, hφφ, hφφ⟩
  have hπ' : π' ^ 2 ^ 1 = 1 := by
    rw [pow_one, sq]
    exact Equiv.ext fun u => hφφ u
  have hodd : ¬ 2 ∣ Fintype.card {u : OGroup Q // u * u = 1 ∧ invType u = (4, 1)} := by
    rw [← Nat.card_eq_fintype_card, hcard]
    norm_num
  obtain ⟨a, ha⟩ := Equiv.Perm.exists_fixed_point_of_prime hodd hπ'
  have hfix : simAct Q γ a.1 = a.1 := congrArg Subtype.val ha
  have hu0 := fj_mem_omega_of_four_plus hQ a.2.1 a.2.2
  let e : omegaGroup hQ := ⟨a.1, hu0⟩
  have he_sq : e * e = 1 := Subtype.ext a.2.1
  have hne1 : e ≠ 1 := by
    intro h1
    have h2 := a.2.2
    rw [show a.1 = 1 from congrArg Subtype.val h1, invType_one] at h2
    exact absurd (congrArg Prod.fst h2) (by decide)
  refine ⟨e, orderOf_eq_prime (by rwa [pow_two]) hne1, ?_, ?_⟩
  · apply Subtype.ext
    rw [hγ e]
    exact hfix
  · intro hc
    have hpi : piOrth Q ∈ omegaGroup hQ := ff_piOrth_mem_omegaGroup_six_minus hQ hdim hs
    let p : omegaGroup hQ := ⟨piOrth Q, hpi⟩
    have hp1 : p ≠ 1 := fun h =>
      piOrth_ne_one (by omega) (congrArg Subtype.val h)
    have hpc : p ∈ center (omegaGroup hQ) :=
      Subgroup.mem_center_iff.mpr fun g =>
        Subtype.ext (Subgroup.mem_center_iff.mp (piOrth_mem_center (Q := Q)) (g : OGroup Q))
    obtain ⟨y, -, huniq⟩ :=
      (Nat.card_eq_two_iff' (1 : center (omegaGroup hQ))).mp
        (natCard_center_omegaGroup_six_minus hQ hdim hs)
    have h1 : (⟨e, hc⟩ : center (omegaGroup hQ)) = y :=
      huniq _ (fun h => hne1 (congrArg Subtype.val h))
    have h2 : (⟨p, hpc⟩ : center (omegaGroup hQ)) = y :=
      huniq _ (fun h => hp1 (congrArg Subtype.val h))
    have hep' : e = p := congrArg Subtype.val (h1.trans h2.symm)
    have hep : a.1 = piOrth Q := congrArg Subtype.val hep'
    have h6 : invDim a.1 = Module.finrank (ZMod 3) V := (invDim_eq_finrank_iff a.2.1).mpr hep
    have h4 : invDim a.1 = 4 := congrArg Prod.fst a.2.2
    omega

theorem asc82CoreF0_of (hS : Asc82SchurU43) : Asc82CoreF0 := by
  intro Y _ _ hY hT σ hσ
  obtain ⟨V, i1, i2, i3, Q, hQ, hdim, hs, ⟨f⟩⟩ := hS Y hY hT
  letI := i1
  letI := i2
  letI := i3
  have hσσ : ∀ y : Y, σ (σ y) = y := fun y => by
    have h := congrArg (fun m : MulAut Y => m y) hσ
    simpa using h
  let α : MulAut (omegaGroup hQ) := f.symm.trans (σ.trans f)
  have hαα : α * α = 1 := by
    apply MulEquiv.ext
    intro w
    change f (σ (f.symm (f (σ (f.symm w))))) = w
    rw [MulEquiv.symm_apply_apply, hσσ, MulEquiv.apply_symm_apply]
  obtain ⟨e, he2, hαe, hec⟩ := fj_exists_fixed_involution_six_minus hQ hdim hs α hαα
  refine ⟨f.symm e, (MulEquiv.orderOf_eq f.symm e).trans he2, ?_, ?_⟩
  · have h : f (σ (f.symm e)) = e := hαe
    calc σ (f.symm e) = f.symm (f (σ (f.symm e))) := (MulEquiv.symm_apply_apply f _).symm
      _ = f.symm e := by rw [h]
  · intro hc
    apply hec
    rw [Subgroup.mem_center_iff]
    intro g
    have h := congrArg f (Subgroup.mem_center_iff.mp hc (f.symm g))
    simpa [map_mul] using h

end CFSG.OddStandard.SmallF3.Omega
