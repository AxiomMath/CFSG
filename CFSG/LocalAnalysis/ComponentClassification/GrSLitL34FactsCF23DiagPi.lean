module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23DiagJB

public section

namespace CFSG.ComponentClassification.GSThmB.CF23Diag

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.CatFactsL4U4

variable {H : Type} [Group H] [Finite H] (h : Hyp52 H) (hKa : conjugate h.K h.a ≠ h.K)

include hKa in
theorem exists_iota : ∃ ι : OddBar h.J →* Vbar h, Function.Injective ι ∧
    (∀ (j : H) (hjB : j ∈ GSLit.fixedLayer h.J h.B) (hjJ : j ∈ h.J),
      ι (⟨j, hjJ⟩ : ↥h.J) = psi h ⟨j, B5a.fixedLayer_le_V h hjB⟩) ∧
    ι.range = (delta h hKa).range := by
  obtain ⟨e, he⟩ := exists_oddBar_JB_equiv h
  have hker : (psiJB h).ker = pPrimeCore 2 ↥(GSLit.fixedLayer h.J h.B) :=
    le_antisymm (ker_psi_le h _) (oddJB_le_ker h hKa)
  set ι₀ := QuotientGroup.lift (pPrimeCore 2 ↥(GSLit.fixedLayer h.J h.B)) (psiJB h)
    (oddJB_le_ker h hKa) with hι₀d
  have hι₀ : Function.Injective ι₀ := by
    intro x y hxy
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    rw [QuotientGroup.eq, ← hker, MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one]
    exact hxy
  have hι₀mk : ∀ j : ↥(GSLit.fixedLayer h.J h.B), ι₀ (QuotientGroup.mk j) = psiJB h j :=
    fun j => rfl
  refine ⟨ι₀.comp e.symm.toMonoidHom, hι₀.comp e.symm.injective, fun j hjB hjJ => ?_, ?_⟩
  · have h1 := he ⟨j, hjB⟩ hjJ
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← h1, MulEquiv.symm_apply_apply, hι₀mk]
    rfl
  · refine le_antisymm ?_ ?_
    · rintro _ ⟨x, rfl⟩
      obtain ⟨j, hj⟩ := QuotientGroup.mk_surjective (e.symm x)
      refine range_psiJB_le h hKa ⟨j, ?_⟩
      show psiJB h j = ι₀ (e.symm x)
      rw [← hj, hι₀mk]
    · intro y hy
      obtain ⟨j, rfl⟩ := range_delta_le_psiJB h hKa hy
      refine ⟨e (j : ↥(GSLit.fixedLayer h.J h.B) ⧸ pPrimeCore 2 _), ?_⟩
      rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply, hι₀mk]

include hKa in
theorem exists_pi {ι : OddBar h.J →* Vbar h} (hι : Function.Injective ι)
    (hr : ι.range = (delta h hKa).range) :
    ∃ π : OddBar h.K →* OddBar h.J, Function.Surjective π ∧ π.ker ≤ center (OddBar h.K) ∧
      ∀ x, ι (π x) = deltaBar h hKa x := by
  have hmem : ∀ x, deltaBar h hKa x ∈ ι.range := fun x => by
    rw [hr, ← range_deltaBar]
    exact ⟨x, rfl⟩
  set π : OddBar h.K →* OddBar h.J :=
    (MonoidHom.ofInjective hι).symm.toMonoidHom.comp ((deltaBar h hKa).codRestrict ι.range hmem)
    with hπd
  have hπ : ∀ x, ι (π x) = deltaBar h hKa x := by
    intro x
    have h1 := MonoidHom.ofInjective_apply hι (x := π x)
    rw [← h1, hπd, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
    rfl
  refine ⟨π, fun y => ?_, fun x hx => ker_deltaBar_le h hKa ?_, hπ⟩
  · obtain ⟨x, hx⟩ : ι y ∈ (deltaBar h hKa).range := by
      rw [range_deltaBar, ← hr]
      exact ⟨y, rfl⟩
    exact ⟨x, hι (by rw [hπ, hx])⟩
  · rw [MonoidHom.mem_ker] at hx ⊢
    rw [← hπ, hx, map_one]

include hKa in
theorem exists_conj_eq_mul {d : H} (hdV : d ∈ h.V) (hda : d * h.a = h.a * d) (hd2 : d * d = 1)
    {k : ↥h.K} (hk2 : psi h ⟨k, h.K_le_V k.2⟩ * psi h ⟨k, h.K_le_V k.2⟩ = 1)
    (hdk : psi h ⟨d, hdV⟩ = delta h hKa k) : ∃ g ∈ h.V, g⁻¹ * h.a * g = h.a * d := by
  set u := psi h ⟨k, h.K_le_V k.2⟩ with hu
  set kV : ↥h.V := ⟨k, h.K_le_V k.2⟩ with hkV
  set dV : ↥h.V := ⟨d, hdV⟩ with hdV'
  set cV : ↥h.V := dV⁻¹ * sigmaV h kV⁻¹ * kV with hcV
  have hcH : (cV : H) = (h.a * d)⁻¹ * ((k : H)⁻¹ * h.a * k) := by
    show d⁻¹ * (h.a⁻¹ * (k : H)⁻¹ * h.a) * k = _
    group
  have hs2 : sigmaBar h u * sigmaBar h u = 1 := by rw [← map_mul, hk2, map_one]
  have hcomm : u * sigmaBar h u = sigmaBar h u * u := by
    rw [hu, sigmaBar_K h k.2]
    exact psi_comm h hKa k.2 (conjA_mem_Ka h k.2)
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hk2
  have hsi : (sigmaBar h u)⁻¹ = sigmaBar h u := inv_eq_of_mul_eq_one_right hs2
  have hc1 : psi h cV = 1 := by
    simp only [hcV, map_mul, map_inv]
    rw [← sigmaBar_psi, hdk, delta_eq, ← hu, mul_inv_rev, hui, hsi]
    calc sigmaBar h u * u * sigmaBar h u * u = sigmaBar h u * (u * sigmaBar h u) * u := by group
      _ = sigmaBar h u * (sigmaBar h u * u) * u := by rw [hcomm]
      _ = (sigmaBar h u * sigmaBar h u) * (u * u) := by group
      _ = 1 := by rw [hs2, hk2, one_mul]
  have hcO : (cV : H) ∈ oddCoreIn h.V := (psi_eq_one_iff h cV).1 hc1
  have ha2 := a_sq h
  have hd' : h.a * d * (h.a * d) = 1 := by
    calc h.a * d * (h.a * d) = h.a * (d * h.a) * d := by group
      _ = h.a * (h.a * d) * d := by rw [hda]
      _ = (h.a * h.a) * (d * d) := by group
      _ = 1 := by rw [ha2, hd2, one_mul]
  have hdc : h.a * d * (cV : H) = (k : H)⁻¹ * h.a * k := by
    rw [hcH]
    group
  have hdc2 : h.a * d * (cV : H) * (h.a * d * (cV : H)) = 1 := by
    rw [hdc]
    calc (k : H)⁻¹ * h.a * k * ((k : H)⁻¹ * h.a * k) = (k : H)⁻¹ * (h.a * h.a) * k := by group
      _ = 1 := by rw [ha2]; group
  obtain ⟨n, hn⟩ := exists_zpow_conj_eq_of_odd hd' hdc2 (odd_orderOf_of_mem_oddCoreIn hcO)
  refine ⟨(k : H) * (cV : H) ^ n, mul_mem (h.K_le_V k.2) (zpow_mem cV.2 n), ?_⟩
  calc ((k : H) * (cV : H) ^ n)⁻¹ * h.a * ((k : H) * (cV : H) ^ n) =
      ((cV : H) ^ n)⁻¹ * ((k : H)⁻¹ * h.a * k) * (cV : H) ^ n := by group
    _ = ((cV : H) ^ n)⁻¹ * (h.a * d * cV) * (cV : H) ^ n := by rw [hdc]
    _ = h.a * d := hn

end CFSG.ComponentClassification.GSThmB.CF23Diag
