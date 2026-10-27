module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23ExU16

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement

section U22

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem q8_exists_inv_conj {P : Subgroup Y} (φ : ↥P ≃* QuaternionGroup 2) {b : Y} (hb : b ∈ P)
    (hb2 : b * b ≠ 1) : ∃ y ∈ P, y * b * y⁻¹ = b⁻¹ := by
  have key : ∀ q : QuaternionGroup 2, q * q ≠ 1 → ∃ y : QuaternionGroup 2, y * q * y⁻¹ = q⁻¹ := by
    decide
  have hq : φ ⟨b, hb⟩ * φ ⟨b, hb⟩ ≠ 1 := by
    intro h
    apply hb2
    have : (⟨b, hb⟩ * ⟨b, hb⟩ : ↥P) = 1 := φ.injective (by rw [← map_mul] at h; rw [h, map_one])
    exact congrArg Subtype.val this
  obtain ⟨y0, hy0⟩ := key _ hq
  refine ⟨((φ.symm y0 : ↥P) : Y), (φ.symm y0).2, ?_⟩
  have : φ.symm y0 * ⟨b, hb⟩ * (φ.symm y0)⁻¹ = (⟨b, hb⟩ : ↥P)⁻¹ := by
    apply φ.injective
    rw [map_mul, map_mul, map_inv, map_inv, MulEquiv.apply_symm_apply]
    exact hy0
  exact congrArg Subtype.val this

theorem mem_normalizer_of_maps_gens {S₀ : Set Y} {y : Y}
    (h : ∀ s ∈ S₀, y * s * y⁻¹ ∈ Subgroup.closure S₀) :
    y ∈ Subgroup.normalizer ((Subgroup.closure S₀ : Subgroup Y) : Set Y) := by
  have hle : Subgroup.closure S₀ ≤ (Subgroup.closure S₀).comap (MulAut.conj y).toMonoidHom := by
    rw [Subgroup.closure_le]
    intro s hs
    exact h s hs
  exact Subgroup.mem_normalizer_fintype fun x hx => hle hx

theorem hyp51_ut_uet (hc : P23Cfg n Y R S t K' W u e g)
    (v2 : Hyp51At (Subgroup.closure ({u * e, u, t} : Set Y)) (u * e))
    (v5 : Hyp51At (Subgroup.closure ({u * e, u, t} : Set Y)) u) :
    Hyp51At (Subgroup.closure ({u * e, u, t} : Set Y)) (u * t) ∧
      Hyp51At (Subgroup.closure ({u * e, u, t} : Set Y)) (u * e * t) := by
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hK : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hz' : IsUniqueInvolution K' t := isUniqueInvolution_of_mem_twinSet hz hc.std.hK'
  obtain ⟨R₁, R₁', b₁, b', hR₁, hR₁', hRD, hR'D, hcomm, hb₁R, hb'R', ob₁, ob', hub, hne_ue⟩ :=
    e_decomp hc
  have hNe := normalizer_le_centralizer_e hd
  have hR₁e : R₁ ≤ Subgroup.centralizer ({e} : Set Y) := hRD.2.trans hNe
  have ht1 := hz.ne_one
  have ht2 := hz.sq
  obtain ⟨φ⟩ := members_sylow_q8 hc.std.perp _ hK R₁ hR₁
  obtain ⟨y, hyR, hyb⟩ := q8_exists_inv_conj φ hb₁R (by rw [ob₁]; exact ht1)
  have hyt : y * t = t * y :=
    Subgroup.mem_centralizer_singleton_iff.mp (le_centralizer_of_unique hz (hR₁.1 hyR))
  have hye : y * e = e * y := Subgroup.mem_centralizer_singleton_iff.mp (hR₁e hyR)
  have hyb' : y * b' = b' * y := hcomm y hyR b' hb'R'
  have hb't : b' * t = t * b' :=
    Subgroup.mem_centralizer_singleton_iff.mp (le_centralizer_of_unique hz' (hR₁'.1 hb'R'))
  have hinv : b₁⁻¹ = b₁ * t := by
    apply inv_eq_of_mul_eq_one_right
    calc b₁ * (b₁ * t) = (b₁ * b₁) * t := by group
      _ = t * t := by rw [ob₁]
      _ = 1 := ht2
  have hyb'' : y * b' * y⁻¹ = b' := by
    calc y * b' * y⁻¹ = (b' * y) * y⁻¹ := by rw [hyb']
      _ = b' := by group
  have hyt' : y * t * y⁻¹ = t := by
    calc y * t * y⁻¹ = (t * y) * y⁻¹ := by rw [hyt]
      _ = t := by group
  have hye' : y * e * y⁻¹ = e := by
    calc y * e * y⁻¹ = (e * y) * y⁻¹ := by rw [hye]
      _ = e := by group
  have hyu : y * u * y⁻¹ = u * t := by
    calc y * u * y⁻¹ = (y * b₁ * y⁻¹) * (y * b' * y⁻¹) := by rw [hub]; group
      _ = (b₁ * t) * b' := by rw [hyb, hinv, hyb'']
      _ = b₁ * (t * b') := by group
      _ = b₁ * (b' * t) := by rw [hb't]
      _ = u * t := by rw [hub]; group
  have hueB : u * e ∈ Subgroup.closure ({u * e, u, t} : Set Y) := Subgroup.subset_closure (by simp)
  have huB : u ∈ Subgroup.closure ({u * e, u, t} : Set Y) := Subgroup.subset_closure (by simp)
  have htB : t ∈ Subgroup.closure ({u * e, u, t} : Set Y) := Subgroup.subset_closure (by simp)
  have heB : e ∈ Subgroup.closure ({u * e, u, t} : Set Y) := by
    have h := Subgroup.mul_mem _ (Subgroup.inv_mem _ huB) hueB
    rwa [show u⁻¹ * (u * e) = e by group] at h
  have hyN : y ∈ Subgroup.normalizer
      ((Subgroup.closure ({u * e, u, t} : Set Y) : Subgroup Y) : Set Y) := by
    refine mem_normalizer_of_maps_gens fun s hs => ?_
    rcases hs with h | h | h
    · rw [h]
      have : y * (u * e) * y⁻¹ = (y * u * y⁻¹) * (y * e * y⁻¹) := by group
      rw [this, hyu, hye']
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ huB htB) heB
    · rw [h, hyu]; exact Subgroup.mul_mem _ huB htB
    · rw [h, hyt']; exact htB
  have h5 := ExactLayer.hyp51At_of_normalizes hyN v5
  have h2 := ExactLayer.hyp51At_of_normalizes hyN v2
  rw [hyu] at h5
  have hconj : y * (u * e) * y⁻¹ = (y * u * y⁻¹) * (y * e * y⁻¹) := by group
  have hcte : t * e = e * t := T7K.comm_e_of_mem_W hd hd.hzW
  have e' : u * t * e = u * e * t := by
    calc u * t * e = u * (t * e) := by group
      _ = u * (e * t) := by rw [hcte]
      _ = u * e * t := by group
  rw [hconj, hyu, hye', e'] at h2
  exact ⟨h5, h2⟩

theorem p23Hyp51_B (hD4 : TwinCentRes.ModelFactD42) (hM12 : TwinCentRes.ModelFactM12)
    (hT : TwinThmE.T4Supply) (hcit : CIT3Below n) (hP : TL4.TightBelowRPlus 3 n)
    (hc : P23Cfg n Y R S t K' W u e g) :
    Hyp51 (Subgroup.closure ({u * e, u, t} : Set Y)) := by
  obtain ⟨v1, v2, v3, v4, v5⟩ := p23_hyp51_vertices hD4 hM12 hT hcit hP hc
  have hut2 := hyp51_ut_uet hc v2 v5
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have cue : u * e = e * u := T7K.comm_e_of_mem_W hd hd.huW
  have cut : u * t = t * u := comm_ut hc
  have cte : t * e = e * t := T7K.comm_e_of_mem_W hd hd.hzW
  have hBeq : Subgroup.closure ({u * e, u, t} : Set Y) = Subgroup.closure ({u, t, e} : Set Y) := by
    refine le_antisymm ((Subgroup.closure_le _).mpr ?_) ((Subgroup.closure_le _).mpr ?_)
    · intro a ha
      rcases ha with h | h | h
      · rw [h]
        exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
      · rw [h]; exact Subgroup.subset_closure (by simp)
      · rw [h]; exact Subgroup.subset_closure (by simp)
    · intro a ha
      rcases ha with h | h | h
      · rw [h]; exact Subgroup.subset_closure (by simp)
      · rw [h]; exact Subgroup.subset_closure (by simp)
      · have : a = u⁻¹ * (u * e) := by rw [h]; group
        rw [this]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.subset_closure (by simp)))
          (Subgroup.subset_closure (by simp))
  refine ⟨B_isElemAbelian hc, B_natCard hc, ?_⟩
  intro c hcB hc1
  have hcB' : c ∈ Subgroup.closure ({u, t, e} : Set Y) := hBeq ▸ hcB
  have hcases := enum8 u t e cut cue cte hd.hu2 hz.sq hd.he2 c hcB'
  rcases hcases with h | h | h | h | h | h | h | h
  · exact absurd h hc1
  · rw [h]; exact v5
  · rw [h]; exact v1
  · rw [h]; exact v3
  · rw [h]; exact hut2.1
  · rw [h]; exact v2
  · rw [h, cte]; exact v4
  · have : u * t * e = u * e * t := by
      calc u * t * e = u * (t * e) := by group
        _ = u * (e * t) := by rw [cte]
        _ = u * e * t := by group
    rw [h, this]; exact hut2.2

theorem p23Alpha_proved (hD4 : TwinCentRes.ModelFactD42) (hM12 : TwinCentRes.ModelFactM12)
    (hT : TwinThmE.T4Supply) (hcit : CIT3Below n) (hP : TL4.TightBelowRPlus 3 n) :
    P23Alpha n := by
  intro Y _ _ R S t K' W u e g hc _
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hD := T7A.isElemAbelian2_closure_pair hd.hu2 hz.sq hd.hu1 hz.ne_one hd.huz (comm_ut hc)
  have hle : Subgroup.closure ({u, t} : Set Y) ≤ Subgroup.closure ({u * e, u, t} : Set Y) :=
    Subgroup.closure_mono (by intro x hx; rcases hx with rfl | rfl <;> simp)
  exact lemma54_odd_and_eq (p23Hyp51_B hD4 hM12 hT hcit hP hc) hle hD

end U22

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
