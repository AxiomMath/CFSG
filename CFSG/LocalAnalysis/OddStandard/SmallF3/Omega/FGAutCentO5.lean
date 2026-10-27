module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGAutCentTrans
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGAutCentInv2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGClosureFive
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFCenter

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem fg_lift_invol_five (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 5)
    (h2 : 2 ≤ Module.finrank (ZMod 3) V) {x : ProjSim Q} (hx2 : x * x = 1) (hx1 : x ≠ 1) :
    ∃ s : OGroup Q, s * s = 1 ∧ 0 < Module.finrank (ZMod 3) (fixSp s) ∧
      0 < Module.finrank (ZMod 3) (commSp s) ∧ ffSimOmegaAct hQ h2 x = projAut hQ s := by
  obtain ⟨y, hy⟩ := fg_simInGStar_of_odd hQ (by omega) (by rw [hdim]; decide) x
  obtain ⟨A, rfl⟩ := QuotientGroup.mk_surjective y
  have hαA : ffSimOmegaAct hQ h2 x = projAut hQ A := by
    rw [← hy, ffSimOmegaAct_projOrthToProjSim]
    rfl
  have hy' : projOrthToProjSim Q (toProj Q A) = x := hy
  have hy2 : toProj Q A * toProj Q A = 1 :=
    projOrthToProjSim_injective (by rw [map_mul, hy', hx2, map_one])
  have hAAmem : A * A ∈ piGroup Q :=
    (QuotientGroup.eq_one_iff (A * A)).mp (by
      show toProj Q (A * A) = 1
      rw [map_mul]
      exact hy2)
  have hAA : A * A = 1 := by
    rcases mem_piGroup_iff.mp hAAmem with h | h
    · exact h
    · exfalso
      have hEven := ((exists_mul_self_eq_piOrth_iff hQ).mp ⟨A, h⟩).1
      rw [hdim] at hEven
      exact (by norm_num : ¬ Even (5 : ℕ)) hEven
  have hA1 : A ≠ 1 := by
    intro h1
    apply hx1
    rw [← hy', h1, map_one, map_one]
  have hAπ : A ≠ piOrth Q := by
    intro hπ'
    apply hx1
    rw [← hy', hπ', toProj_piOrth, map_one]
  have hfix_ne : fixSp A ≠ ⊥ := by
    intro hfix
    apply hAπ
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    have htop : commSp A = ⊤ := by
      have hc : fixSp A ⊔ commSp A = ⊤ := codisjoint_iff.mp
        (isCompl_fixSp_commSp (Q := Q) hAA).2
      rwa [hfix, bot_sup_eq] at hc
    have hv : v ∈ commSp A := by rw [htop]; exact Submodule.mem_top
    rw [mem_commSp_iff hAA] at hv
    rw [coe_piOrth_apply]
    exact hv
  have hcomm_ne : commSp A ≠ ⊥ := fun h => hA1 ((commSp_eq_bot_iff hAA).mp h)
  refine ⟨A, hAA, ?_, ?_, hαA⟩
  · rw [Nat.pos_iff_ne_zero]
    intro h0
    exact hfix_ne (Submodule.finrank_eq_zero.mp h0)
  · rw [Nat.pos_iff_ne_zero]
    intro h0
    exact hcomm_ne (Submodule.finrank_eq_zero.mp h0)

theorem fg_aut_cent_om5 {G : Type} [Group G] [Finite G] {L : Subgroup G} (hL : IsOm5Q L)
    {x : G} (hx : orderOf x = 2) (hxN : x ∈ normalizer (L : Set G)) {X : Subgroup G}
    (hX : IsComponentIn X (L ⊓ centralizer ({x} : Set G))) {R : Subgroup G}
    (hR : R ≤ normalizer (L : Set G) ⊓ centralizer (X : Set G)) :
    (centralizer (L : Set G)).relIndex R ≤ 2 := by
  obtain ⟨V, _, _, _, Q, hQ, hdim, hsgn, ⟨e⟩⟩ := ff_isOmegaStar_center_five hL
  have h : (Module.finrank (ZMod 3) V = 5 ∧ quadSign Q = 1) ∨
      (Module.finrank (ZMod 3) V = 6 ∧ (quadSign Q = 1 ∨ quadSign Q = -1)) := Or.inl ⟨hdim, hsgn⟩
  have h2 : 2 ≤ Module.finrank (ZMod 3) V := by omega
  have hx2 : x * x = 1 := by
    rw [← pow_two]
    exact hx ▸ pow_orderOf_eq_one x
  have hodd : Odd (Nat.card (Subgroup.center ↥L)) := by
    rw [ff_center_eq_oddCore_five hL]
    exact ff_odd_card_oddCore ↥L
  have hLp : commutator ↥L = ⊤ := hL.1.1.commutator_eq_top
  have hRN : R ≤ normalizer (L : Set G) := hR.trans inf_le_left
  have hRC : R ≤ centralizer (X : Set G) := hR.trans inf_le_right
  by_cases hx1 : ffTheta hQ h e ⟨x, hxN⟩ = 1
  · have hxC : x ∈ centralizer (L : Set G) :=
      (ffTheta_eq_one_iff hQ h e hLp ⟨x, hxN⟩).mp hx1
    have hLle : L ≤ centralizer ({x} : Set G) := fun l hl =>
      mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hxC l hl)
    rw [inf_eq_left.mpr hLle] at hX
    have hXL : X = L := hX.eq_of_isQuasisimple hL.1
    rw [hXL] at hRC
    rw [Subgroup.relIndex_eq_one.mpr hRC]
    norm_num
  · have hθ2 : ffTheta hQ h e ⟨x, hxN⟩ * ffTheta hQ h e ⟨x, hxN⟩ = 1 := by
      rw [← map_mul]
      have hxx : (⟨x, hxN⟩ : ↥(normalizer (L : Set G))) * ⟨x, hxN⟩ = 1 := Subtype.ext hx2
      rw [hxx, map_one]
    obtain ⟨s, hs, hF, hC, hαs⟩ := fg_lift_invol_five hQ hdim h2 hθ2 hx1
    have hJ := fg_isComponentIn_rho hQ h e h2 hodd hx2 hxN hX
    have hJ' : IsComponentIn ((X.subgroupOf L).map (fgRho hQ e)) (fixSub (projAut hQ s)) := by
      rw [← hαs]
      exact hJ
    have hAJ := fg_thetaR_centralizes hQ h e hR
    rw [fg_relIndex_eq_card_range hQ h e hLp hRN]
    rcases fg_cent_invol hQ (Or.inl hdim) hs hF hC hJ' hAJ
        (fun h6 => absurd h6 (by omega)) with
      h1 | ⟨h6, -, -, -⟩ | ⟨h6, -, -, -⟩
    · exact h1
    · omega
    · omega

end CFSG.OddStandard.SmallF3.Omega
