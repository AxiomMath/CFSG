module

public import CFSG.ClassicalInvolution.Q3.Q3P21S6
public import CFSG.ClassicalInvolution.Q3.Q3TPSChart
public import CFSG.ClassicalInvolution.Q3.Q3TY6
public import CFSG.ClassicalInvolution.Q3.Q3TY20
public import CFSG.ClassicalInvolution.Q3.Q3WStd
public import CFSG.ClassicalInvolution.RouteD.TypeF4Nodes
public import CFSG.ClassicalInvolution.RouteD.TypeF4Lift
public import CFSG.ClassicalInvolution.RouteD.TypeCBlock
public import CFSG.ClassicalInvolution.Asc77.SU4Model
public import CFSG.ClassicalInvolution.Q3.Q3P21S4
public import CFSG.ClassicalInvolution.Q3.Q3TY11
public import CFSG.ClassicalInvolution.Q3.Q3TY32
public import CFSG.ClassicalInvolution.Q3.Q3URDict
public import CFSG.ClassicalInvolution.Q3.Q3URStd

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3P21

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted CFSG.ClassicalInvolution.Q3.Q3W
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.Models.TwistedPairs (TwistedB2BlockPair spinMinusModel
  four_le_card_shortField')
open CFSG.ClassicalInvolution.Models (longRootSetU)
open CFSG.ClassicalInvolution.Phan (Su)
open scoped MatrixGroups

variable {G : Type} [Group G]

section Node

variable [Finite G]

theorem exists_shortNode_of_linear3 {Ω : Set (Subgroup G)} {z : G} {K : Subgroup G}
    (c : Q3TP.TCtxS3 .PSU 4 Ω K z) {N K₂ : Subgroup G} {t : G} (hNt : IsClassicalMember3 N t)
    (hK₂ : K₂ ∈ centralizingMembers Ω {z}) (hK₂K : K₂ ≠ K) (hK₂Q : ¬ locImg Ω z K₂ ≤ c.d.Q₁)
    (hpair : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W N K₂)
    (ht : t * z * t⁻¹ = z) (hlin : TauLinear3 c ht) :
    ∃ Us : Subgroup G, Us ≤ ⁅Us, Us⁆ ∧ Commutes K Us ∧
      Us ≤ Subgroup.centralizer ({t} : Set G) ∧
      ∃ W, TwistedB2BlockPair (minusCoeffs_irr 3 1) W K₂ Us := by
  classical
  obtain ⟨φ, hfund, hlinφ⟩ := hlin
  have hirr := minusCoeffs_irr 3 1
  have := fact_shortField hirr
  have := finite_shortField (b := (minusCoeffs 3 1).1) (c := (minusCoeffs 3 1).2)
  have hg6 : SpinMinus6Generated (minusCoeffs_irr 3 1) :=
    spinMinus6Generated_galois (p := 3) (f := 1) (by norm_num)
  have ht2 : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [hNt.orderOf_eq_two, pow_two] at this
  obtain ⟨R₀, hR₀, hK₂R⟩ := c.exists_fund_of_ne hK₂ hK₂K hK₂Q
  have hR : R₀.map φ.toMonoidHom ∈ longRootSetU (K := GaloisField 3 (2 * 1)) (p := 3) (f := 1)
      (by norm_num : 2 ≤ 4) := (hfund R₀).mp hR₀
  set ψ' : Su (GaloisField 3 (2 * 1)) 3 1 4 →* locQuot Ω z :=
    c.d.ψ.comp φ.symm.toMonoidHom with hψ'
  have hψ'φ : ∀ r, ψ' (φ r) = c.d.ψ r := fun r => by simp [hψ']
  have hker' : ψ'.ker ≤ Subgroup.center (Su (GaloisField 3 (2 * 1)) 3 1 4) := by
    intro y hy
    have h1 : φ.symm y ∈ c.d.ψ.ker := hy
    have h2 := c.d.ker_le h1
    have : y = φ (φ.symm y) := by simp
    rw [this]
    rw [Subgroup.mem_center_iff] at h2 ⊢
    intro w
    apply φ.symm.injective
    rw [map_mul, map_mul]
    simpa using h2 (φ.symm w)
  have hRmap : (R₀.map φ.toMonoidHom).map ψ' = locImg Ω z K₂ := by
    rw [Subgroup.map_map, hK₂R]
    congr 1
    ext r
    simp [hψ']
  obtain ⟨θ, hθr, hθτ⟩ := Q3TPS.exists_chart3 c.hΩ.conjInvariant hNt (le_centralizingLayer hK₂) ht
    hpair
  set τ : locQuot Ω z ≃* locQuot Ω z := Gaps.locAut c.hΩ.conjInvariant ht with hτdef
  have hτ : ∀ x, τ (τ x) = x := Gaps.locAut_locAut c.hΩ.conjInvariant ht ht2
  obtain ⟨S, W, hpairS, hRS, hfix⟩ := exists_fixed_shortPair_linear_three hg6 ψ' hker' τ hτ hR θ
    (hθr.trans hRmap.symm) hθτ hlinφ
  have hSperf : S.map ψ' ≤ ⁅S.map ψ', S.map ψ'⁆ := by
    obtain ⟨θ₀, -, -, -, -, hV⟩ := hpairS
    have := range_perfect_of_sl2 (four_le_card_shortField' (b := (minusCoeffs 3 1).1)
      (c := (minusCoeffs 3 1).2)) (θ₀.comp (spinMinusModel hirr).sb)
    rwa [MonoidHom.range_comp, hV] at this
  obtain ⟨A, hAp, hAm⟩ := exists_perfect_lift c.hP1 hSperf
  set Yl : Subgroup G := locLayer Ω z with hYl
  let Us : Subgroup G := A.map Yl.subtype
  have hUsimg : locImg Ω z Us = S.map ψ' := by rw [locImg_map_subtype, hAm]
  have hUsY : Us ≤ Yl := Subgroup.map_subtype_le _
  have hUsperf : Us ≤ ⁅Us, Us⁆ := by
    rw [← Subgroup.map_commutator]
    exact Subgroup.map_mono hAp
  have hKY : K ≤ Yl := le_centralizingLayer c.hKz
  have hK₂Y : K₂ ≤ Yl := le_centralizingLayer hK₂
  refine ⟨Us, hUsperf, ?_, ?_, ?_⟩
  · exact RouteD.Gaps.commutes_symm
      (commutes_of_commutes_locImg_perfect c.hP1 hUsY hKY hUsperf fun x hx y hy => by
        rw [hUsimg] at hx
        obtain ⟨s, -, rfl⟩ := hx
        exact (c.d.comm₀ y (c.hQ₀ hy) _ ⟨φ.symm s, rfl⟩).symm)
  · refine (Q3TY.locAut_fixed_iff_of_perfect3 c.hΩ.conjInvariant c.hP1 ht hUsY hUsperf).2
      fun a ha => ?_
    rw [hUsimg] at ha
    obtain ⟨y, hy, rfl⟩ := ha
    exact hfix y hy
  · have hpairX : TwistedB2BlockPair (minusCoeffs_irr 3 1) W (locImg Ω z K₂) (locImg Ω z Us) := by
      rw [hUsimg, ← hRmap]
      exact hpairS
    obtain ⟨zL, hzL⟩ := c.hΩ.classical K₂ hK₂.1
    have hK₂12 : ∀ a ∈ K₂, a ^ 12 = 1 := pow_twelve_of_exact hzL (c.hex _ hK₂.1)
    exact Q3TY.twistedB2BlockPair_of_locImg3 hirr hg6 c.hP1 c.hO3 hK₂Y hUsY hK₂12 hUsperf hpairX

end Node

end CFSG.ClassicalInvolution.Q3.Q3P21
