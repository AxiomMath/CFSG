module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7Cover

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.ZTwo

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL

section Sylow

theorem exists_commuting_conj {C : Type} [Group C] [Finite C] (O : Subgroup C) [hN : O.Normal]
    (hO : Odd (Nat.card O)) {e x : C} (he : e * e = 1) (hx : x * x = 1)
    (hex : e * x * e⁻¹ * x⁻¹ ∈ O) :
    ∃ d : C, (d * x * d⁻¹) * e = e * (d * x * d⁻¹) ∧ (d * x * d⁻¹) * x⁻¹ ∈ O := by
  classical
  set π : C →* C ⧸ O := QuotientGroup.mk' O with hπ
  have hcomm : π e * π x = π x * π e := by
    have : π (e * x * e⁻¹ * x⁻¹) = 1 := (QuotientGroup.eq_one_iff _).mpr hex
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at this
    calc π e * π x = π e * π x * (π e)⁻¹ * (π x)⁻¹ * (π x * π e) := by group
      _ = π x * π e := by rw [this, one_mul]
  have hAcomm : ∀ a ∈ Subgroup.closure ({π e, π x} : Set (C ⧸ O)),
      ∀ b ∈ Subgroup.closure ({π e, π x} : Set (C ⧸ O)), a * b = b * a := by
    intro a ha b hb
    refine Subgroup.closure_induction₂ (k := ({π e, π x} : Set (C ⧸ O)))
      (p := fun a b _ _ => a * b = b * a) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ha hb
    · rintro a b (rfl | rfl) (rfl | rfl)
      · rfl
      · exact hcomm
      · exact hcomm.symm
      · rfl
    · intro x _; rw [one_mul, mul_one]
    · intro x _; rw [one_mul, mul_one]
    · intro x y z _ _ _ h1 h2
      rw [mul_assoc, h2, ← mul_assoc, h1, mul_assoc]
    · intro y z x _ _ _ h1 h2
      rw [← mul_assoc, h1, mul_assoc, h2, ← mul_assoc]
    · intro x y _ _ h
      calc x⁻¹ * y = x⁻¹ * (y * x) * x⁻¹ := by group
        _ = x⁻¹ * (x * y) * x⁻¹ := by rw [h]
        _ = y * x⁻¹ := by group
    · intro x y _ _ h
      calc x * y⁻¹ = y⁻¹ * (y * x) * y⁻¹ := by group
        _ = y⁻¹ * (x * y) * y⁻¹ := by rw [h]
        _ = y⁻¹ * x := by group
  set A : Subgroup (C ⧸ O) := Subgroup.closure ({π e, π x} : Set (C ⧸ O)) with hA
  set D : Subgroup C := A.comap π with hD
  have heD : e ∈ D := Subgroup.subset_closure (Or.inl rfl)
  have hxD : x ∈ D := Subgroup.subset_closure (Or.inr rfl)
  have he2 : IsPGroup 2 (Subgroup.zpowers e) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one he
  have hx2 : IsPGroup 2 (Subgroup.zpowers x) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hx
  obtain ⟨P, hP, heP⟩ := IsSylow2In.exists_ge he2 (Subgroup.zpowers_le.mpr heD)
  obtain ⟨d, hdD, hxd⟩ := exists_conj_of_isSylow2In hP hx2 (Subgroup.zpowers_le.mpr hxD)
  have hxP : d⁻¹ * x * d ∈ P := by
    have := hxd (Subgroup.mem_zpowers x)
    rwa [mem_conjSub_iff] at this
  have heP' : e ∈ P := heP (Subgroup.mem_zpowers e)
  have hdA : π d ∈ A := hdD
  have hπx : π x ∈ A := Subgroup.subset_closure (Or.inr rfl)
  have hπe : π e ∈ A := Subgroup.subset_closure (Or.inl rfl)
  have hπy : π (d⁻¹ * x * d) ∈ A := by
    rw [map_mul, map_mul, map_inv]
    exact A.mul_mem (A.mul_mem (A.inv_mem hdA) hπx) hdA
  have hPy : d⁻¹ * x * d ∈ P := hxP
  refine ⟨d⁻¹, ?_, ?_⟩
  · rw [inv_inv]
    have hc : π e * π (d⁻¹ * x * d) = π (d⁻¹ * x * d) * π e := hAcomm _ hπe _ hπy
    have h1 : e * (d⁻¹ * x * d) * e⁻¹ * (d⁻¹ * x * d)⁻¹ ∈ O := by
      rw [← QuotientGroup.eq_one_iff (N := O)]
      show π _ = 1
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
      calc π e * π (d⁻¹ * x * d) * (π e)⁻¹ * (π (d⁻¹ * x * d))⁻¹
          = (π (d⁻¹ * x * d) * π e) * (π e)⁻¹ * (π (d⁻¹ * x * d))⁻¹ := by rw [hc]
        _ = 1 := by group
    have h2 : e * (d⁻¹ * x * d) * e⁻¹ * (d⁻¹ * x * d)⁻¹ ∈ P :=
      P.mul_mem (P.mul_mem (P.mul_mem heP' hPy) (P.inv_mem heP')) (P.inv_mem hPy)
    have h3 := eq_one_of_isPGroup_of_mem_odd hO h1
      (hP.2.1.to_le (Subgroup.zpowers_le.mpr h2))
    calc d⁻¹ * x * d * e
        = (e * (d⁻¹ * x * d) * e⁻¹ * (d⁻¹ * x * d)⁻¹)⁻¹ * (e * (d⁻¹ * x * d)) := by group
      _ = e * (d⁻¹ * x * d) := by rw [h3]; group
  · rw [inv_inv]
    rw [← QuotientGroup.eq_one_iff (N := O)]
    show π _ = 1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    have hc : π x * π d = π d * π x := hAcomm _ hπx _ hdA
    calc (π d)⁻¹ * π x * π d * (π x)⁻¹ = (π d)⁻¹ * (π d * π x) * (π x)⁻¹ := by
          rw [mul_assoc (π d)⁻¹, ← hc]
      _ = 1 := by group

end Sylow

section Basic


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem t_e_mem_rLayer (hc : P23Cfg n Y R S t K' W u e g) :
    t ∈ rLayer (Om R) e ∧ e ∈ rLayer (Om R) e := by
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hd := hc.data
  have hK : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  obtain ⟨R₁, R₁', b₁, b', hR₁, hR₁', hRD, hR'D, hcomm, hb₁R, hb'R', ob₁, ob', hub, hne_ue⟩ :=
    e_decomp hc
  have hNe := normalizer_le_centralizer_e hd
  have hR₁e : R₁ ≤ Subgroup.centralizer ({e} : Set Y) := hRD.2.trans hNe
  have hR₁'e : R₁' ≤ Subgroup.centralizer ({e} : Set Y) := hR'D.2.trans hNe
  have hR₁E : R₁ ≤ rLayer (Om R) e := F7C.le_rLayer (mem_RSet_of_isSylow2In hK hR₁) hR₁e
  have hR₁'E : R₁' ≤ rLayer (Om R) e :=
    F7C.le_rLayer (mem_RSet_of_isSylow2In hc.std.hK'.1 hR₁') hR₁'e
  have hgN : g ∈ Subgroup.normalizer (W : Set Y) := T7K.g_mem_normalizer hd
  have hgC : g ∈ Subgroup.centralizer ({e} : Set Y) := hNe hgN
  have hJ₃ : conjSub g (tightCore R) ∈ Om R := hΩ.conjInvariant g _ hK
  have hR₃ : IsSylow2In (conjSub g R₁) (conjSub g (tightCore R)) := hR₁.conj g
  have hR₃e : conjSub g R₁ ≤ Subgroup.centralizer ({e} : Set Y) := by
    rintro _ ⟨x, hx, rfl⟩
    have e1 : (MulAut.conj g).toMonoidHom x = g * x * g⁻¹ := rfl
    rw [e1]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hgC (hR₁e hx)) (Subgroup.inv_mem _ hgC)
  have hR₃E : conjSub g R₁ ≤ rLayer (Om R) e :=
    F7C.le_rLayer (mem_RSet_of_isSylow2In hJ₃ hR₃) hR₃e
  have htR : t ∈ R₁ := involution_mem_sylow hΩ hK hz hR₁
  refine ⟨hR₁E htR, ?_⟩
  have hb₁E : b₁ ∈ rLayer (Om R) e := hR₁E hb₁R
  have hb'E : b' ∈ rLayer (Om R) e := hR₁'E hb'R'
  have hgb : g * b₁ * g⁻¹ ∈ rLayer (Om R) e := hR₃E (conj_mem_conjSub hb₁R)
  have hsq : (g * b₁ * g⁻¹) * (g * b₁ * g⁻¹) = u * e := by
    rw [← hd.hgt, ← ob₁]
    group
  have hee : e = (b₁ * b')⁻¹ * ((g * b₁ * g⁻¹) * (g * b₁ * g⁻¹)) := by
    rw [hsq, hub]
    group
  have hmem := Subgroup.mul_mem (rLayer (Om R) e)
    (Subgroup.inv_mem _ (Subgroup.mul_mem _ hb₁E hb'E)) (Subgroup.mul_mem _ hgb hgb)
  rwa [← hee] at hmem

end Basic

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.ZTwo
