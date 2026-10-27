module

public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.TOdd.Full3A
public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.TOdd.ThreeB

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.TOdd

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.LieType.Seitz CFSG.Open TauCeti CFSG.RankThree.PartOne.CTP
open CFSG.RankThree.PartTwo.Sec19 CFSG.RankThree.PartTwo.Sec11 CFSG.RankThree.PartTwo.Sec4.E27


variable {ℓ f : ℕ} {X : Type} [Field X] [Finite X] {σ : X ≃+* X}

theorem cen_map_conj_odd (σ : X ≃+* X) (h x : C0 σ) :
    (cenX σ (h * x * h⁻¹)).map (MulAut.conj h⁻¹).toMonoidHom = cenX σ x := by
  ext k
  constructor
  · rintro ⟨c, hc, rfl⟩
    have hc' : c * (h * x * h⁻¹) = (h * x * h⁻¹) * c := Subgroup.mem_centralizer_singleton_iff.1 hc
    rw [Subgroup.mem_centralizer_singleton_iff]
    show (MulAut.conj h⁻¹ c) * x = x * (MulAut.conj h⁻¹ c)
    rw [MulAut.conj_apply, inv_inv]
    calc h⁻¹ * c * h * x = h⁻¹ * (c * (h * x * h⁻¹)) * h := by group
      _ = h⁻¹ * ((h * x * h⁻¹) * c) * h := by rw [hc']
      _ = x * (h⁻¹ * c * h) := by group
  · intro hk
    have hk' : k * x = x * k := Subgroup.mem_centralizer_singleton_iff.1 hk
    refine ⟨h * k * h⁻¹, Subgroup.mem_centralizer_singleton_iff.2 ?_, ?_⟩
    · calc h * k * h⁻¹ * (h * x * h⁻¹) = h * (k * x) * h⁻¹ := by group
        _ = h * (x * k) * h⁻¹ := by rw [hk']
        _ = h * x * h⁻¹ * (h * k * h⁻¹) := by group
    · show MulAut.conj h⁻¹ (h * k * h⁻¹) = k
      rw [MulAut.conj_apply, inv_inv]
      group

theorem map_congr_conj_inv_map (h : C0 σ) (E : Subgroup (MulAut (C0 σ))) :
    (E.map (MulAut.congr (MulAut.conj h)).toMonoidHom).map
      (MulAut.congr (MulAut.conj h⁻¹)).toMonoidHom = E := by
  have hid : ∀ y : MulAut (C0 σ),
      (MulAut.congr (MulAut.conj h⁻¹)) ((MulAut.congr (MulAut.conj h)) y) = y := by
    intro y
    rw [CFSG.RankThree.PartTwo.Sec19.congr_apply_eq, CFSG.RankThree.PartTwo.Sec19.congr_apply_eq]
    simp [map_inv]
    group
  ext z
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    show (MulAut.congr (MulAut.conj h⁻¹)) ((MulAut.congr (MulAut.conj h)) y) ∈ E
    rw [hid]
    exact hy
  · intro hz
    exact ⟨(MulAut.congr (MulAut.conj h)) z, ⟨z, hz, rfl⟩, hid z⟩

theorem cen_le_closure_model_odd (P : D4ParOdd ℓ f X σ) {E : Subgroup (MulAut (C0 σ))}
    (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 27) {x : C0 σ}
    (hx : MulAut.conj x ∈ E) (hx1 : x ≠ 1) {b : C0 σ} (hbE : MulAut.conj b ∈ E)
    (hbx : MulAut.conj b ∉ Subgroup.zpowers (MulAut.conj x))
    {e : MulAut (C0 σ)} (heE : e ∈ E)
    (hein : e ∉ (MulAut.conj : C0 σ →* MulAut (C0 σ)).range) :
    cenX σ x ≤ Subgroup.closure {l | l ∈ cenX σ x ∧ ∃ y ∈ E,
      y ∉ Subgroup.zpowers (MulAut.conj x : MulAut (C0 σ)) ∧ y l = l} := by
  haveI : Finite (C0 σ) := finite_C0
  have hx3 : x ^ 3 = 1 := pow_three_of_conj_mem P hE hx
  obtain ⟨g, hg | hg⟩ := KS11Lie6Proof.d4ThreeConj_holds X (ℓ ^ f) σ P.card P.frob
    P.not_three_dvd x hx3 hx1
  · exact cen_le_closure_classX_odd P hE hcard hx hx1 ⟨hx3, hx1, g, hg⟩ hbE hbx
  ·
    set φ : MulAut (C0 σ) := MulAut.conj g with hφ
    set E' : Subgroup (MulAut (C0 σ)) := E.map (MulAut.congr φ).toMonoidHom with hE'
    have hE'ab : IsElemAbelian 3 E' := CFSG.Open.IsElemAbelian.map hE _
    have hcj : ∀ k : C0 σ, (MulAut.congr φ) (MulAut.conj k) = MulAut.conj (g * k * g⁻¹) :=
      fun k => CFSG.RankThree.PartTwo.Sec4.E27.congr_conj_conj g k
    have hx'E : MulAut.conj (g * x * g⁻¹) ∈ E' := ⟨MulAut.conj x, hx, hcj x⟩
    have hb'E : MulAut.conj (g * b * g⁻¹) ∈ E' := ⟨MulAut.conj b, hbE, hcj b⟩
    have hx'1 : g * x * g⁻¹ ≠ 1 := fun h1 =>
      hx1 ((MulAut.conj g).injective (by rw [MulAut.conj_apply, h1, map_one]))
    have hb'x : MulAut.conj (g * b * g⁻¹) ∉ Subgroup.zpowers (MulAut.conj (g * x * g⁻¹)) := by
      rintro ⟨k, hk⟩
      apply hbx
      refine ⟨k, (MulAut.congr φ).injective ?_⟩
      simp only at hk
      rw [map_zpow, hcj, hcj, ← hk]
    have he'E : (MulAut.congr φ) e ∈ E' := ⟨e, heE, rfl⟩
    have he'in : (MulAut.congr φ) e ∉ (MulAut.conj : C0 σ →* MulAut (C0 σ)).range := by
      rintro ⟨k, hk⟩
      apply hein
      refine ⟨g⁻¹ * k * g, (MulAut.congr φ).injective ?_⟩
      show (MulAut.congr φ) (MulAut.conj (g⁻¹ * k * g)) = (MulAut.congr φ) e
      rw [hcj, ← hk]
      congr 1
      group
    have key := cen_le_closure_threeB_odd P hE'ab hx'E hx'1 hg hb'E hb'x he'E he'in
    have hback := stepOK_map (MulAut.conj g⁻¹) key
    have hb : E'.map (MulAut.congr (MulAut.conj g⁻¹)).toMonoidHom = E :=
      map_congr_conj_inv_map g E
    have hc : (MulAut.congr (MulAut.conj g⁻¹)) (MulAut.conj (g * x * g⁻¹)) = MulAut.conj x := by
      rw [CFSG.RankThree.PartTwo.Sec4.E27.congr_conj_conj]
      congr 1
      group
    rw [cen_map_conj_odd σ g x, hb, hc] at hback
    exact hback

end CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.TOdd
