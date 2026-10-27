module

public import CFSG.ClassicalInvolution.Q3.Q3TPSGN
public import CFSG.ClassicalInvolution.Q3.Q3TPSLift
public import CFSG.ClassicalInvolution.Q3.Q3TPSNorm
public import CFSG.ClassicalInvolution.RouteD.TwinYStatements
public import CFSG.ClassicalInvolution.WeakCT.DLWeakAgree

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TPS

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W
open CFSG.ClassicalInvolution.RouteD.TwinY (IsTwinAt)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair diagConj2)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (SymplecticBlockPair planeGroup longBlock
  shortBlock mem_fundamentalSubgroups_PSp_iff exists_planeGroup_eq_conj_longBlock coords
  mem_coords range_longBlock eq_one_of_mem_center_of_mem_suppGroup longBlock_injective)
open CFSG.ClassicalInvolution.Q3.Q3TP (TCtxS3 nonempty_tctxS3 yData3S_psp2)
open scoped MatrixGroups

local notation "F₃" => GaloisField 3 1


theorem inj_longBlock_conj {X : Type} [Group X] (ρ : StatedSp 2 F₃ →* X)
    (hρ : ρ.ker ≤ Subgroup.center (StatedSp 2 F₃)) (c : StatedSp 2 F₃) :
    Function.Injective (ρ.comp ((MulAut.conj c).toMonoidHom.comp (longBlock F₃ 2 1))) := by
  rw [injective_iff_map_eq_one]
  intro s hs
  have h1 : (MulAut.conj c).toMonoidHom (longBlock F₃ 2 1 s) ∈ ρ.ker := hs
  have h2 : c * longBlock F₃ 2 1 s * c⁻¹ ∈ Subgroup.center (StatedSp 2 F₃) := hρ h1
  have h3 := Models.SymplecticPairs.mem_center_of_conj_mem_center h2
  have h4 : longBlock F₃ 2 1 s = 1 := by
    refine eq_one_of_mem_center_of_mem_suppGroup h3 ?_ (S := coords (1 : Fin 2))
      (t := Sum.inl (0 : Fin 2)) (by simp [mem_coords])
    rw [← range_longBlock]
    exact ⟨s, rfl⟩
  exact longBlock_injective (K := F₃) (n := 2) (1 : Fin 2) (h4.trans (map_one _).symm)

theorem twinSp2ShortNodePair3 (h3 : OddThreeFreeInput) :
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
      ∀ (K : Subgroup G) (z : G), RouteD3Setup K z →
        LocalShapeC3 2 (CompData.model .PSp 2) (conjClass3 K) z →
        ∀ N K₂ : Subgroup G, N ∈ conjClass3 K →
          K₂ ∈ centralizingMembers (conjClass3 K) {z} → K₂ ≠ K →
          (∀ T : Subgroup G, IsTwinAt (conjClass3 K) K T z → K₂ ≠ T) →
          Commutes K K₂ → (∃ W, LinearBlockStandardPair F₃ W K N) →
          (∃ W, LinearBlockStandardPair F₃ W N K₂) →
          ∃ Us : Subgroup G, Commutes K Us ∧ Commutes N Us ∧
            ∃ W, SymplecticBlockPair F₃ W K₂ Us := by
  intro G _ _ _ hnab K z hR hshape N K₂ hNΩ hK₂ hK₂K hnotTwin hKK₂ hp1 hp2
  classical
  have hΩ := hR.inClass
  have hsingle : ∀ L ∈ conjClass3 K, ∃ g : G, L = conjSub g K := fun L hL => by
    obtain ⟨g, hg⟩ := hL
    exact ⟨g, hg.symm⟩
  have hadmP := Q3Z.statedLieAdmissible_psp2
  have h2 : (2 : F₃) ≠ 0 := Ring.two_ne_zero ringChar_galoisField_three_ne_two
  have h01 : (0 : Fin 2) ≠ 1 := zero_ne_one
  obtain ⟨c⟩ := nonempty_tctxS3 yData3S_psp2 h3 hR hshape
  obtain ⟨l⟩ := nonempty_layerS3 c
  obtain ⟨T₁, hT₁, hT₁img⟩ := c.exists_twin
  have hT₁tw : IsTwinAt (conjClass3 K) K T₁ z :=
    ⟨hT₁, c.twin_ne hT₁ hT₁img.le, fun M hM hMT => c.commutes_T_of_ne hT₁ hT₁img.le hM hMT,
      fun M hM hMK => c.commutes_K_of_ne hM hMK⟩
  have hnQ₁ : ¬ locImg (conjClass3 K) z K₂ ≤ c.d.Q₁ := fun h =>
    hnotTwin T₁ hT₁tw (c.eq_of_locImg_le_Q₁ hK₂ hT₁ h hT₁img.le)
  obtain ⟨R, hRf, hK₂R⟩ := c.exists_fund_of_ne hK₂ hK₂K hnQ₁
  obtain ⟨P, hP, rfl⟩ := (mem_fundamentalSubgroups_PSp_iff hadmP R).mp hRf
  have hK₂Θ : K₂ = (planeGroup P).map l.Θ := l.eq_member hK₂ hP hK₂R
  obtain ⟨z₁, hz₁⟩ := hΩ.classical N hNΩ
  obtain ⟨W₁, hW₁⟩ := hp1
  have hcomm : z * z₁ = z₁ * z := RouteD.Gaps.standardPair_involutions_commute h2 hW₁
    hR.cls.mem hz₁.mem hR.cls.orderOf_eq_two hz₁.orderOf_eq_two
  have hzz : z₁ * z * z₁⁻¹ = z := by
    rw [← hcomm, mul_inv_cancel_right]
  have hz₁sq : z₁ * z₁ = 1 := by
    rw [← pow_two]
    have := pow_orderOf_eq_one z₁
    rwa [hz₁.orderOf_eq_two] at this
  have hτ : ∀ x, Gaps.locAut hΩ.conjInvariant hzz (Gaps.locAut hΩ.conjInvariant hzz x) = x :=
    fun x => Gaps.locAut_locAut hΩ.conjInvariant hzz hz₁sq x
  obtain ⟨θ, hθrange, hθτ⟩ := exists_chart3 hΩ.conjInvariant hz₁ (le_centralizingLayer hK₂) hzz hp2
  obtain ⟨g₀, hg₀⟩ := exists_planeGroup_eq_conj_longBlock hP (1 : Fin 2)
  let ψ' : StatedSp 2 F₃ →* locQuot (conjClass3 K) z := c.d.ψ.comp (MulAut.conj g₀).toMonoidHom
  have hker' : ψ'.ker ≤ Subgroup.center (StatedSp 2 F₃) :=
    WeakCT.ker_comp_mulEquiv_le_center c.d.ker_le _
  have hnorm' : ψ'.range.Normal := by
    have : ψ'.range = c.d.ψ.range := WeakCT.range_comp_mulEquiv c.d.ψ (MulAut.conj g₀)
    rw [this]
    exact TCtxS3.normal_range c
  have hθ' : θ.range = (longBlock F₃ 2 1).range.map ψ' := by
    rw [hθrange, hK₂R, hg₀]
    exact (WeakCT.map_comp_mulEquiv c.d.ψ (MulAut.conj g₀) _).symm
  obtain ⟨g₁, hg₁L, hg₁fix⟩ := exists_fixed_shortRoot3 ψ' hker' hnorm'
    (Gaps.locAut hΩ.conjInvariant hzz) hτ θ hθ' hθτ h01
  set g : StatedSp 2 F₃ := g₀ * g₁ with hgdef
  have hgL : conjSub g (longBlock F₃ 2 1).range = planeGroup P := by
    rw [hgdef, conjSub_mul, hg₀]
    congr 1
  let ρ : SL(2, F₃) →* G := l.Θ.comp ((MulAut.conj g).toMonoidHom.comp (shortBlock F₃ h01))
  have hUs : (conjSub g (shortBlock F₃ h01).range).map l.Θ = ρ.range := by
    ext u
    constructor
    · rintro ⟨_, ⟨_, ⟨B, rfl⟩, rfl⟩, rfl⟩
      exact ⟨B, rfl⟩
    · rintro ⟨B, rfl⟩
      exact ⟨_, ⟨_, ⟨B, rfl⟩, rfl⟩, rfl⟩
  have hstep : ∀ Bg : SL(2, F₃), Bg ^ 3 = 1 → ∀ n ∈ N, Commute (ρ Bg) n := by
    intro Bg hB3 n hn
    set x : StatedSp 2 F₃ := g * shortBlock F₃ h01 Bg * g⁻¹ with hxdef
    have hρx : ρ Bg = l.Θ x := rfl
    have hs3 : ρ Bg ^ 3 = 1 := by rw [← map_pow, hB3, map_one]
    have hsK : ∀ k ∈ K, ρ Bg * k * (ρ Bg)⁻¹ = k := by
      intro k hk
      rw [hρx, mul_inv_eq_iff_eq_mul]
      exact l.commutes_K x hk
    have hx3 : x ^ 3 = 1 := by
      have : x = (MulAut.conj g).toMonoidHom (shortBlock F₃ h01 Bg) := rfl
      rw [this, ← map_pow, ← map_pow, hB3, map_one, map_one]
    have hfix : Gaps.locAut hΩ.conjInvariant hzz (c.d.ψ x) = c.d.ψ x := by
      have h1 := hg₁fix (g₁ * shortBlock F₃ h01 Bg * g₁⁻¹) ⟨shortBlock F₃ h01 Bg, ⟨Bg, rfl⟩, rfl⟩
      have e : g₀ * (g₁ * shortBlock F₃ h01 Bg * g₁⁻¹) * g₀⁻¹ = x := by
        rw [hxdef, hgdef]
        group
      have h2 : ψ' (g₁ * shortBlock F₃ h01 Bg * g₁⁻¹) = c.d.ψ x := by
        show c.d.ψ (g₀ * (g₁ * shortBlock F₃ h01 Bg * g₁⁻¹) * g₀⁻¹) = c.d.ψ x
        rw [e]
      rw [h2] at h1
      exact h1
    have hconj := l.conj_fixed hzz hx3 hfix
    have hsz : ρ Bg * z₁ * (ρ Bg)⁻¹ = z₁ := by
      rw [hρx]
      have h' : z₁ * l.Θ x = l.Θ x * z₁ := mul_inv_eq_iff_eq_mul.mp hconj
      calc l.Θ x * z₁ * (l.Θ x)⁻¹ = z₁ * l.Θ x * (l.Θ x)⁻¹ := by rw [h']
        _ = z₁ := mul_inv_cancel_right _ _
    have hnorm := TCtxS3.normalizes_of_cube_one c hsingle hNΩ hz₁ hs3 hsz
    have hcent := centralizes_of_cube_one hs3 ⟨W₁, hW₁⟩ hsK hnorm
    exact mul_inv_eq_iff_eq_mul.mp (hcent n hn)
  have hcentral : ∀ B : SL(2, F₃), ∀ n ∈ N, Commute (ρ B) n := by
    intro B
    have hB : B ∈ Subgroup.closure (Set.range (CFSG.LieType.Steinberg.sl2Upper (k := F₃)) ∪
        Set.range CFSG.LieType.Steinberg.sl2Lower) := CFSG.LieType.Steinberg.Sp.mem_closure_sl2 B
    refine Subgroup.closure_induction (p := fun B _ => ∀ n ∈ N, Commute (ρ B) n) ?_ ?_ ?_ ?_ hB
    · rintro B (⟨c₀, rfl⟩ | ⟨c₀, rfl⟩)
      · exact hstep _ (sl2Upper_pow_three c₀)
      · exact hstep _ (sl2Lower_pow_three c₀)
    · intro n _
      rw [map_one]
      exact Commute.one_left n
    · intro a b _ _ ha hb n hn
      rw [map_mul]
      exact (ha n hn).mul_left (hb n hn)
    · intro a _ ha n hn
      rw [map_inv]
      exact (ha n hn).inv_left
  refine ⟨(conjSub g (shortBlock F₃ h01).range).map l.Θ, ?_, ?_, ?_⟩
  · rintro k hk _ ⟨x, _, rfl⟩
    exact (l.commutes_K x hk).symm
  · rintro n hn _ hu
    rw [hUs] at hu
    obtain ⟨B, rfl⟩ := hu
    exact (hcentral B n hn).symm
  · refine ⟨l.Θ.range, l.Θ, g⁻¹, rfl, l.ker_le, ?_, ?_, ?_⟩
    · simpa [inv_inv] using inj_longBlock_conj l.Θ l.ker_le g
    · rw [inv_inv]
      show (conjSub g (longBlock F₃ 2 1).range).map l.Θ = K₂
      rw [hgL]
      exact hK₂Θ.symm
    · rw [inv_inv]
      rfl

end CFSG.ClassicalInvolution.Q3.Q3TPS
