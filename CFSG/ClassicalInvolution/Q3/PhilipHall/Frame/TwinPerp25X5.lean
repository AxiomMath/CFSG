module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinLayer
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25X2

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P.Asc77.P25S.X

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q8P.Asc77.P25R
  CFSG.ClassicalInvolution.Q8P.Asc77 CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open scoped commutatorElement

section Lift

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_inf_centralizer_fixed {Y F : Subgroup G} (hF2 : IsPGroup 2 F)
    (hFY : ∀ e ∈ F, conjSub e Y = Y) {x : ↥Y ⧸ classicalInvolutionOddCore ↥Y}
    (hfix : ∀ e (he : e ∈ F), C25Y.layerAut Y (hFY e he) x = x) :
    ∃ (y : G) (hy : y ∈ Y), y ∈ Subgroup.centralizer (F : Set G) ∧
      (QuotientGroup.mk ⟨y, hy⟩ : ↥Y ⧸ classicalInvolutionOddCore ↥Y) = x := by
  classical
  obtain ⟨x₀, rfl⟩ := QuotientGroup.mk_surjective x
  have hOodd : Odd (Nat.card (oddCoreOf Y)) := by
    unfold oddCoreOf
    rw [Subgroup.card_map_of_injective Y.subtype_injective]
    exact CFSG.ComponentClassification.OddCore.odd_card ↥Y
  have hAN : ∀ a ∈ F, ∀ n ∈ oddCoreOf Y, a * n * a⁻¹ ∈ oddCoreOf Y := by
    intro a ha n hn
    have h1 : a * n * a⁻¹ ∈ conjSub a (oddCoreOf Y) := Generic.conj_mem_conjSub hn
    rwa [← Thompson.oddCoreOf_conjSub_eq, hFY a ha] at h1
  have hx : ∀ a ∈ F, (x₀ : G)⁻¹ * (a * x₀ * a⁻¹) ∈ oddCoreOf Y := by
    intro a ha
    have h1 := hfix a ha
    rw [C25Y.layerAut_mk, QuotientGroup.eq] at h1
    refine Subgroup.mem_map.mpr ⟨_, (classicalInvolutionOddCore ↥Y).inv_mem h1, ?_⟩
    simp [C25Y.coe_conjOnSub, mul_assoc]
  obtain ⟨n, hn, hfixn⟩ := exists_fixed_mem_coset_of_isPGroup hF2 hOodd hAN hx
  have hnY : n ∈ Y := Subgroup.map_subtype_le _ hn
  have hx₁Y : (x₀ : G) * n ∈ Y := Y.mul_mem x₀.2 hnY
  refine ⟨(x₀ : G) * n, hx₁Y, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro e he
    have := hfixn e he
    calc e * ((x₀ : G) * n) = e * ((x₀ : G) * n) * e⁻¹ * e := by group
      _ = (x₀ : G) * n * e := by rw [this]
  · rw [QuotientGroup.eq]
    obtain ⟨n', hn', hn'n⟩ := Subgroup.mem_map.mp hn
    have e : (⟨(x₀ : G) * n, hx₁Y⟩ : ↥Y)⁻¹ * x₀ = n'⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [show ((n' : ↥Y) : G) = n from hn'n]
      group
    rw [e]
    exact (classicalInvolutionOddCore ↥Y).inv_mem hn'

end Lift



section Mixed

variable {G : Type} [Group G] [Finite G] [CoreLike G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G}
  {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ : G}

theorem mem_trivialOnQuot_of_mem_A (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {a : G}
    (ha : a ∈ cA S R R') : a ∈ trivialOnQuot K ∧ a ∈ trivialOnQuot K' := by
  have hs : Hyp23Setting Ω K K' z := hyp.std.setting
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hcpg : IsPGroup 2 (Subgroup.zpowers a) :=
    S.isPGroup'.to_le (Subgroup.zpowers_le.mpr ha.1)
  have hcent := Subgroup.mem_centralizer_iff.mp ha.2
  refine ⟨?_, ?_⟩
  · refine (Q3.PhilipHall.Frame.TwinLayer.mem_trivialOnQuot_iff_exists_sylow hΩ hyp.std.1.quot2 hcpg
      hs.stand.mem).mpr ⟨R, T7C.isSylow2In_of_mem_RSet_of_le hΩ hs.stand.mem hyp.hR.1 hyp.hR.2.1, ?_⟩
    exact fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr
      (hcent x (Subgroup.mem_sup_left hx))
  · refine (Q3.PhilipHall.Frame.TwinLayer.mem_trivialOnQuot_iff_exists_sylow hΩ hyp.std.1.quot2 hcpg
      hs.hK'.1).mpr ⟨R', T7C.isSylow2In_of_mem_RSet_of_le hΩ hs.hK'.1 hyp.hR'.1 hyp.hR'.2.1, ?_⟩
    exact fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr
      (hcent x (Subgroup.mem_sup_right hx))

theorem mem_trivialOnQuot_of_good (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) (hQ : QTFAt hyp) {b e : G}
    (hbA : b ∈ cA S R R') (hb2 : b * b = 1) (hb1 : b ≠ 1) (hbbad : BadElt z b)
    (heA : e ∈ cA S R R') (heb : e ∈ Subgroup.centralizer ({b} : Set G))
    (hgood : z ∈ zStarOf (Subgroup.centralizer ({e * z} : Set G))) :
    e ∈ trivialOnQuot (TwinDisc.coreLayer Ω b) := by
  classical
  have hzA : z ∈ cA S R R' := (z_facts hyp).1
  have hz2 : z * z = 1 := hyp.std.setting.hz.sq
  have hz1 : z ≠ 1 := hyp.std.setting.hz.ne_one
  have hzS : ∀ s ∈ (S : Subgroup G), s * z = z * s := hyp.hzS
  have hΩ : HypOmegaGen Ω := hyp.std.1.stand.hyp
  have hb2' : IsPGroup 2 (Subgroup.zpowers b) := isPGroup_zpowers_of_sq_eq_one hb2
  set E := Subgroup.zpowers e ⊔ Subgroup.zpowers z with hE
  have heE : e ∈ E := Subgroup.mem_sup_left (Subgroup.mem_zpowers e)
  have hzE : z ∈ E := Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  have hEA : E ≤ cA S R R' :=
    sup_le (Subgroup.zpowers_le.mpr heA) (Subgroup.zpowers_le.mpr hzA)
  have hE2 : IsPGroup 2 E := S.isPGroup'.to_le (hEA.trans inf_le_left)
  have hEb : E ≤ Subgroup.centralizer ({b} : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr heb) (Subgroup.zpowers_le.mpr
      (Subgroup.mem_centralizer_singleton_iff.mpr (hzS b hbA.1).symm))
  have hQb := hQ hbA hb2 hb1 hbbad
  have hzY := hQb.zY
  have hzb : z ∈ Subgroup.centralizer ({b} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hzS b hbA.1).symm
  have hEY : ∀ x ∈ E, conjSub x (TwinDisc.coreLayer Ω b) = TwinDisc.coreLayer Ω b := fun x hx =>
    TwinDisc.conjSub_coreLayer hΩ hb2' (hEb hx)
  set lam := CX.layerHom (TwinDisc.coreLayer Ω b) E hEY with hlam
  have hlamact : ∀ e : E, lam e = actOf hyp hb2 ⟨e, hEb e.2⟩ := fun e => rfl
  have hexp : ∀ x : E, lam x * lam x = 1 := fun x => by
    rw [hlamact]
    exact hQb.exp2 x (hEA x.2) (hEb x.2)
  let z₀ : E := ⟨z, hzE⟩
  let e₀ : E := ⟨e, heE⟩
  have hlamz : lam z₀ = MulAut.conj (QuotientGroup.mk ⟨z, hzY⟩ :
      ↥(TwinDisc.coreLayer Ω b) ⧸ classicalInvolutionOddCore ↥(TwinDisc.coreLayer Ω b)) := by
    rw [hlamact]
    exact actW_eq_conj hΩ hb2' hzb hzY
  set F := Subgroup.zpowers (e * z) with hF
  have hezE : e * z ∈ E := E.mul_mem heE hzE
  have hFE : F ≤ E := Subgroup.zpowers_le.mpr hezE
  have hF2 : IsPGroup 2 F := hE2.to_le hFE
  have hFb : F ≤ Subgroup.centralizer ({b} : Set G) := hFE.trans hEb
  have hFY : ∀ g ∈ F, conjSub g (TwinDisc.coreLayer Ω b) = TwinDisc.coreLayer Ω b := fun g hg =>
    TwinDisc.conjSub_coreLayer hΩ hb2' (hFb hg)
  have hzF : z ∈ Subgroup.centralizer (F : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact hzS g ((hEA (hFE hg)).1)
  have hgoodF : z ∈ zStarOf (Subgroup.centralizer (F : Set G)) := by
    rw [hF, centralizer_zpowers]
    exact hgood
  have hlamF : ∀ g (hg : g ∈ F), ∃ k : ℤ,
      C25Y.layerAut (TwinDisc.coreLayer Ω b) (hFY g hg) = (lam (e₀ * z₀)) ^ k := by
    intro g hg
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨k, ?_⟩
    have h1 : (⟨g, hFE hg⟩ : E) = (e₀ * z₀) ^ k := by
      apply Subtype.ext
      simp only [Subgroup.coe_zpow, Subgroup.coe_mul]
      exact hk.symm
    rw [← map_zpow, ← h1]
    rfl
  by_cases hβ1 : lam e₀ = 1
  · have htriv : ∀ g (hg : g ∈ Subgroup.zpowers e), ∀ y, C25Y.layerAut (TwinDisc.coreLayer Ω b)
        (TwinDisc.conjSub_coreLayer hΩ hb2' ((Subgroup.zpowers_le.mpr heb) hg)) y = y := by
      intro g hg y
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hg
      have h1 : (⟨g, Subgroup.mem_sup_left hg⟩ : E) = e₀ ^ k := by
        apply Subtype.ext
        simp only [Subgroup.coe_zpow]
        exact hk.symm
      have h2 : lam ⟨g, Subgroup.mem_sup_left hg⟩ = 1 := by rw [h1, map_zpow, hβ1, one_zpow]
      have := congrArg (fun φ => φ y) h2
      simpa [hlam, CX.layerHom_apply] using this
    exact le_trivialOnQuot_of_layerAut_trivial (fun x hx => TwinDisc.conjSub_coreLayer hΩ hb2'
      ((Subgroup.zpowers_le.mpr heb) hx)) htriv (Subgroup.mem_zpowers e)
  · exfalso
    have hez2 : lam (e₀ * z₀) * lam (e₀ * z₀) = 1 := hexp _
    by_cases hβz : lam e₀ = lam z₀
    ·
      have hez1 : lam (e₀ * z₀) = 1 := by
        rw [map_mul, hβz]
        exact hexp _
      refine not_mem_zStarOf_of_layerAut_trivial hF2 hFY hzF hzY hz2 hz1 hQb.center ?_ hgoodF
      intro g hg y
      obtain ⟨k, hk⟩ := hlamF g hg
      rw [hk, hez1, one_zpow, MulAut.one_apply]
    ·
      have hne1 : lam (e₀ * z₀) ≠ 1 := by
        intro h
        apply hβz
        rw [map_mul] at h
        calc lam e₀ = lam e₀ * lam z₀ * (lam z₀)⁻¹ := by group
          _ = (lam z₀)⁻¹ := by rw [h, one_mul]
          _ = lam z₀ := by
            rw [inv_eq_of_mul_eq_one_right (hexp z₀)]
      have hnez : lam (e₀ * z₀) ≠ MulAut.conj (QuotientGroup.mk ⟨z, hzY⟩ :
          ↥(TwinDisc.coreLayer Ω b) ⧸ classicalInvolutionOddCore ↥(TwinDisc.coreLayer Ω b)) := by
        rw [← hlamz]
        intro h
        apply hβ1
        rw [map_mul] at h
        calc lam e₀ = lam e₀ * lam z₀ * (lam z₀)⁻¹ := by group
          _ = 1 := by rw [h, mul_inv_cancel]
      obtain ⟨xb, hxbfix, hxbz, hxbc⟩ := hQb.refl (e * z) (Subgroup.mul_mem _ heA hzA) (hEb hezE)
        hne1 hnez
      refine not_mem_zStarOf_of_fix_of_normalizes hF2 hFY hzY hz2 (x := xb) ?_ hxbz hxbc hgoodF
      intro g hg
      obtain ⟨k, hk⟩ := hlamF g hg
      rw [hk]
      have hstab : lam (e₀ * z₀) ∈
          MulAction.stabilizer (MulAut (↥(TwinDisc.coreLayer Ω b) ⧸
            classicalInvolutionOddCore ↥(TwinDisc.coreLayer Ω b))) xb := hxbfix
      exact (MulAction.stabilizer _ xb).zpow_mem hstab k

end Mixed

end CFSG.ClassicalInvolution.Q8P.Asc77.P25S.X
