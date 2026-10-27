module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.H81Orth.Types
public import CFSG.LocalAnalysis.GLTheoremA.CatA.H81Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.H81Orth.Layer

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H81Orth

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.Classical2 CFSG.Open CFSG.ClassicalGroups.Orthogonal QuadraticMap
open scoped commutatorElement

section Perfect

variable {G : Type*} [Group G]

theorem commutatorElement_mul_mul_of_commute {J : Subgroup G} {a b c d : G} (ha : a ∈ J)
    (hb : b ∈ J) (hdJ : d ∈ J) (hc : ∀ k ∈ J, k * c = c * k) (hd : ∀ k ∈ J, k * d = d * k) :
    ⁅c * a, d * b⁆ = ⁅a, b⁆ := by
  have hc1 : ∀ Y ∈ J, c * Y * c⁻¹ = Y := fun Y hY => by rw [← hc Y hY, mul_inv_cancel_right]
  have hd1 : ∀ Y ∈ J, d * Y * d⁻¹ = Y := fun Y hY => by rw [← hd Y hY, mul_inv_cancel_right]
  have hY : a * (d * b) * a⁻¹ ∈ J := J.mul_mem (J.mul_mem ha (J.mul_mem hdJ hb)) (J.inv_mem ha)
  have hZ : a * b * a⁻¹ * b⁻¹ ∈ J :=
    J.mul_mem (J.mul_mem (J.mul_mem ha hb) (J.inv_mem ha)) (J.inv_mem hb)
  calc ⁅c * a, d * b⁆ = c * (a * (d * b) * a⁻¹) * c⁻¹ * (b⁻¹ * d⁻¹) := by
        rw [commutatorElement_def]; group
    _ = a * (d * b) * a⁻¹ * (b⁻¹ * d⁻¹) := by rw [hc1 _ hY]
    _ = (a * d) * b * a⁻¹ * b⁻¹ * d⁻¹ := by group
    _ = (d * a) * b * a⁻¹ * b⁻¹ * d⁻¹ := by rw [hd a ha]
    _ = d * (a * b * a⁻¹ * b⁻¹) * d⁻¹ := by group
    _ = ⁅a, b⁆ := by rw [hd1 _ hZ, commutatorElement_def]

theorem forall_mem_apply_eq_of_perfect {J : Subgroup G} (hJ : ⁅J, J⁆ = J) (α : MulAut G)
    (hα : ∀ j ∈ J, α j * j⁻¹ ∈ J ∧ ∀ k ∈ J, k * (α j * j⁻¹) = (α j * j⁻¹) * k) :
    ∀ j ∈ J, α j = j := by
  let C : Subgroup G :=
    { carrier := {g | α g = g}
      one_mem' := map_one α
      mul_mem' := fun {a b} ha hb => by
        show α (a * b) = a * b
        rw [map_mul, ha, hb]
      inv_mem' := fun {a} ha => by
        show α a⁻¹ = a⁻¹
        rw [map_inv, ha] }
  have hle : ⁅J, J⁆ ≤ C := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    show α ⁅a, b⁆ = ⁅a, b⁆
    obtain ⟨hcJ, hc⟩ := hα a ha
    obtain ⟨hdJ, hd⟩ := hα b hb
    have hac : α a = (α a * a⁻¹) * a := by group
    have hbd : α b = (α b * b⁻¹) * b := by group
    rw [map_commutatorElement, hac, hbd]
    exact commutatorElement_mul_mul_of_commute ha hb hdJ hc hd
  intro j hj
  exact hle (by rw [hJ]; exact hj)

end Perfect

section Choice

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ}

theorem oddOrderIsometry_of_mem (hQ : (polarBilin Q).Nondegenerate) (hpK : (p : K) ≠ 0)
    {Pt : Subgroup ↥(orthDerived Q)} (hPt : IsElemAbelian p Pt) {a : ↥(orthDerived Q)}
    (ha : a ∈ Pt) : OddOrderIsometry Q p (a : V ≃ₗ[K] V) where
  mem := orthDerived_le_orthogonalGroup' Q a.2
  pow_eq_one := by
    have := hPt.2 a ha
    exact congrArg Subtype.val this
  cast_ne_zero := hpK
  regular := fun v hv => eq_zero_of_polar_eq_zero hQ hv

theorem coe_mul_comm_of_mem {Pt : Subgroup ↥(orthDerived Q)} (hPt : IsElemAbelian p Pt)
    {a b : ↥(orthDerived Q)} (ha : a ∈ Pt) (hb : b ∈ Pt) :
    (a : V ≃ₗ[K] V) * b = b * a := by
  haveI := hPt.1
  have h := congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : ↥Pt) ⟨b, hb⟩)
  exact congrArg Subtype.val h

theorem h81Choice_of_config [Finite (ProjOrthDerived Q)] (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) (hK : ringChar K ≠ 2)
    (hK3 : Nat.card K ≠ 3) (hp : p.Prime) (hp2 : p ≠ 2) (hpK : (p : K) ≠ 0)
    {Pt : Subgroup ↥(orthDerived Q)} (hPt : IsElemAbelian p Pt)
    (hinj : ∀ a ∈ Pt, ∀ b ∈ Pt, projT Q a = projT Q b → a = b)
    {yy zz : ↥(orthDerived Q)} (hyy : yy ∈ Pt) (hzz : zz ∈ Pt) (hyy1 : yy ≠ 1)
    (hzy : zz ∉ Subgroup.zpowers yy)
    (hR : finrank K (othersSpace (yy : V ≃ₗ[K] V).toLinearMap (X - 1)) = 2)
    (hW : 5 ≤ finrank K (fixedSpace (yy : V ≃ₗ[K] V)))
    (hWz : finrank K (fixedSpace ((yy : V ≃ₗ[K] V) * (zz : V ≃ₗ[K] V))) = 3 ∨
      finrank K (fixedSpace ((yy : V ≃ₗ[K] V) * (zz : V ≃ₗ[K] V))) = 4)
    (hker : ∀ a ∈ Pt, (∀ v ∈ fixedSpace (yy : V ≃ₗ[K] V), (a : V ≃ₗ[K] V) v = v) →
      a ∈ Subgroup.zpowers yy)
    (hzR : ∀ v, (zz : V ≃ₗ[K] V) ((yy : V ≃ₗ[K] V) v - v) = (yy : V ≃ₗ[K] V) v - v)
    (hmove : ∃ t ∈ Pt, ∃ u ∈ fixedSpace ((yy : V ≃ₗ[K] V) * (zz : V ≃ₗ[K] V)),
      (t : V ≃ₗ[K] V) u ≠ u)
    {JType : Subgroup (ProjOrthDerived Q) → Prop}
    (hType : p ∣ Nat.card ↥(fixedComponentImage Q (yy : V ≃ₗ[K] V)) →
      JType (fixedComponentImage Q (yy : V ≃ₗ[K] V)))
    (hAut : ∀ α : MulAut (ProjOrthDerived Q), α ^ p = 1 →
      (∀ j ∈ fixedComponentImage Q (yy : V ≃ₗ[K] V), α j = j) →
        ∃ k : ℤ, α = MulAut.conj (projT Q yy ^ k)) :
    H81Choice p (Pt.map (projT Q)) JType := by
  classical
  haveI : Finite V := Module.finite_of_finite K
  haveI : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have hy := oddOrderIsometry_of_mem hQ hpK hPt hyy
  have hz := oddOrderIsometry_of_mem hQ hpK hPt hzz
  have hyyp : yy ^ p = 1 := hPt.2 yy hyy
  have hzzp : zz ^ p = 1 := hPt.2 zz hzz
  have hodd : Odd (Nat.card K) := by
    have := Fintype.ofFinite K
    by_contra h
    apply hK
    rw [FiniteField.even_card_iff_char_two, ← Nat.card_eq_fintype_card]
    exact Nat.not_odd_iff.mp h
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hRne : othersSpace (yy : V ≃ₗ[K] V).toLinearMap (X - 1) ≠ ⊥ := fun h => by
    rw [h, finrank_bot] at hR
    exact absurd hR (by norm_num)
  set JH := fixedComponentImage Q (yy : V ≃ₗ[K] V) with hJH
  have hJq : CFSG.IsQuasisimple ↥JH := isQuasisimple_fixedComponentImage hy hRne hodd hW
  have hJq' : CFSG.Open.IsQuasisimple ↥JH := ⟨hJq.1.commutator_eq_top, hJq.2.1⟩
  obtain ⟨u, hu, hzu⟩ : ∃ u ∈ fixedSpace (yy : V ≃ₗ[K] V), (zz : V ≃ₗ[K] V) u ≠ u := by
    by_contra h
    push Not at h
    exact hzy (hker zz hzz h)
  have hzC : (zz : V ≃ₗ[K] V) ∈ isometryCentralizer Q (yy : V ≃ₗ[K] V) :=
    ⟨hz.mem, Subgroup.mem_centralizer_singleton_iff.mpr (coe_mul_comm_of_mem hPt hzz hyy)⟩
  have hpJ : p ∣ Nat.card ↥JH :=
    dvd_card_fixedComponentImage hy hp hp2 hK hRne hzC hz.pow_eq_one hu hzu
  have hdvd : p ∣ Nat.card (↥JH ⧸ Subgroup.center ↥JH) :=
    CFSG.dvd_card_quotient_center_of_quasisimple hJq hp hpJ
  have hcent : Subgroup.centralizer {projT Q yy} = centralizerImage Q (yy : V ≃ₗ[K] V) :=
    centralizer_projT_eq hQ hT hp hp2 hyy1 hyyp
  refine ⟨projT Q yy, ⟨yy, hyy, rfl⟩, ?_, JH, ?_, ?_, hType hpJ, ?_, ?_⟩
  · intro h
    exact hyy1 (hinj yy hyy 1 (Subgroup.one_mem _) (by rw [h, map_one]))
  · rw [hcent]
    exact glaPComponent_fixedComponentImage hy hp hJq' hdvd
  · intro L hL
    rw [hcent] at hL
    exact eq_fixedComponentImage_of_glaPComponent hy hp2 hp h2 hR hJq hL
  · refine ⟨projT Q zz, ⟨zz, hzz, rfl⟩, ?_, ?_⟩
    · intro hmem
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
      apply hzy
      have h1 : yy ^ k = zz := hinj _ (Pt.zpow_mem hyy k) _ hzz (by rw [map_zpow, hk])
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, h1⟩
    · obtain ⟨t, htP, u', hu', htu'⟩ := hmove
      have htO := oddOrderIsometry_of_mem hQ hpK hPt htP
      have htC : (t : V ≃ₗ[K] V) ∈ isometryCentralizer Q ((yy : V ≃ₗ[K] V) * zz) := by
        refine ⟨htO.mem, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
        rw [← mul_assoc, coe_mul_comm_of_mem hPt htP hyy, mul_assoc,
          coe_mul_comm_of_mem hPt htP hzz, mul_assoc]
      have hzz1 : zz ≠ 1 := fun h => hzy (h ▸ Subgroup.one_mem _)
      exact glaPLayer_ne_bot_of_mul hQ hT hy hz (coe_mul_comm_of_mem hPt hyy hzz) hzR hp hp2
        hzz1 hK hodd hK3 hRne hWz htC htO.pow_eq_one hu' htu'
  · intro α hα hcore
    refine hAut α hα (forall_mem_apply_eq_of_perfect (Subgroup.isPerfect_iff.mp hJq.1) α
      fun j hj => ?_)
    have h1 : α j * j⁻¹ ∈ (GLAPPrimeCore p ↥JH).map JH.subtype := hcore j hj
    obtain ⟨c, hc, hce⟩ := h1
    have hcZ := glaPPrimeCore_le_center_of_dvd_card hp hJq' hpJ hc
    refine ⟨hce ▸ c.2, fun k hk => ?_⟩
    rw [← hce]
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hcZ) ⟨k, hk⟩)

end Choice

end CFSG.LocalAnalysis.GLTheoremA.H81Orth
