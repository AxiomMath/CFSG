module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2012Lift
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L208g2YKey

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L2012

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Bg CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage2.Final
  CFSG.GH74.GLS.Stage2.Final.Thm6.L208g2 CFSG.GH74.GLS.Stage2.Final.Thm6.SL2Bound
  CFSG.GH74.GLS.Stage2.Final.Thm6.L20

section Basic

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} {q : ℕ}
  {L₁ L₂ : Subgroup (CentralizerBar z)} {K₁ K₂ : Subgroup G}

theorem pairK₁
    (hP : Stage1Pair G z S q L₁ L₂) (hK : CompData z K₁ K₂ L₁ L₂) (hq9 : q ≠ 9) : Pair K₁ K₂ q q where
  odd := hP.odd
  gt := hP.gt3
  odd' := hP.odd
  hm := hasSL2Model_comp₁ hP hK hq9
  hm' := hasSL2Model_comp₂ hP hK hq9
  comm := hK.comm
  inf := compData_card_inf hP hK hq9

theorem pairK₂
    (hP : Stage1Pair G z S q L₁ L₂) (hK : CompData z K₁ K₂ L₁ L₂) (hq9 : q ≠ 9) : Pair K₂ K₁ q q where
  odd := hP.odd
  gt := hP.gt3
  odd' := hP.odd
  hm := hasSL2Model_comp₂ hP hK hq9
  hm' := hasSL2Model_comp₁ hP hK hq9
  comm := fun a ha b hb => (hK.comm b hb a ha).symm
  inf := by rw [inf_comm]; exact compData_card_inf hP hK hq9

end Basic

section Four

variable {G : Type} [Group G]

theorem four_descr {U : Subgroup G} (hU4 : IVK.IsFourSubgroup U) {z t : G} (hzU : z ∈ U) (htU : t ∈ U)
    (hz1 : z ≠ 1) (ht1 : t ≠ 1) (htz : t ≠ z) (hUsq : ∀ u ∈ U, u * u = 1) :
    ∀ u ∈ U, u = 1 ∨ u = z ∨ u = t ∨ u = z * t := by
  classical
  intro u hu
  have hzz : z * z = 1 := hUsq z hzU
  have : Finite ↥U := Nat.finite_of_card_ne_zero (by rw [hU4.2]; omega)
  have := Fintype.ofFinite ↥U
  have hc4 : Fintype.card ↥U = 4 := by rw [← Nat.card_eq_fintype_card]; exact hU4.2
  have hztU : z * t ∈ U := mul_mem hzU htU
  have hzt1 : z * t ≠ 1 := by
    intro h
    apply htz
    calc t = z⁻¹ * (z * t) := by group
      _ = z⁻¹ := by rw [h, mul_one]
      _ = z := inv_eq_of_mul_eq_one_right hzz
  have hztz : z * t ≠ z := by
    intro h
    exact ht1 (mul_left_cancel (a := z) (h.trans (mul_one z).symm))
  have hztt : z * t ≠ t := by
    intro h
    exact hz1 (mul_right_cancel (b := t) (h.trans (one_mul t).symm))
  have n1 : (1 : ↥U) ∉ ({⟨z, hzU⟩, ⟨t, htU⟩, ⟨z * t, hztU⟩} : Finset ↥U) := by
    simp [Subtype.ext_iff, hz1.symm, ht1.symm, hzt1.symm]
  have n2 : (⟨z, hzU⟩ : ↥U) ∉ ({⟨t, htU⟩, ⟨z * t, hztU⟩} : Finset ↥U) := by
    simp [Subtype.ext_iff, htz.symm, hztz.symm]
  have n3 : (⟨t, htU⟩ : ↥U) ∉ ({⟨z * t, hztU⟩} : Finset ↥U) := by
    simp [Subtype.ext_iff, hztt.symm]
  let S4 : Finset ↥U := {1, ⟨z, hzU⟩, ⟨t, htU⟩, ⟨z * t, hztU⟩}
  have hS4 : S4.card = 4 := by
    simp only [S4]
    rw [Finset.card_insert_of_notMem n1, Finset.card_insert_of_notMem n2,
      Finset.card_insert_of_notMem n3, Finset.card_singleton]
  have hS : S4 = Finset.univ := Finset.eq_univ_of_card S4 (by rw [hS4, hc4])
  have hmem : (⟨u, hu⟩ : ↥U) ∈ S4 := by rw [hS]; exact Finset.mem_univ _
  simp only [S4, Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff] at hmem
  simpa using hmem

theorem four_sq {U : Subgroup G} (hU4 : IVK.IsFourSubgroup U) : ∀ u ∈ U, u * u = 1 := by
  intro u hu
  have := hU4.1
  have := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := U) u hu
  simpa [pow_two] using this

end Four


section Main

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} {q : ℕ}
  {L₁ L₂ : Subgroup (CentralizerBar z)} {K₁ K₂ : Subgroup G}

theorem U_le_sup (hP : Stage1Pair G z S q L₁ L₂) (hK : CompData z K₁ K₂ L₁ L₂) (hSC : S ≤ Cen z)
    {U : Subgroup G} (hLU : U ≤ LC z) (hUS : U ≤ S) (hU4 : IVK.IsFourSubgroup U) :
    ∀ u ∈ U, u ∈ K₁ ⊔ K₂ := by
  intro u hu
  have huC : u ∈ Cen z := hSC (hUS hu)
  have hbar : toBar z ⟨u, huC⟩ ∈ L₁ ⊔ L₂ := by
    rw [hP.prod.1]
    exact ⟨⟨u, huC⟩, Subgroup.mem_subgroupOf.mpr (hLU hu), rfl⟩
  have := hK.mem_layer u huC (four_sq hU4 u hu) hbar
  rwa [hK.layer] at this

theorem z_mem_inf
    (hP : Stage1Pair G z S q L₁ L₂) (hK : CompData z K₁ K₂ L₁ L₂) (hq9 : q ≠ 9) (hz : z ∈ K₁ ⊔ K₂) :
    z ∈ K₁ ⊓ K₂ := by
  have p₁ := pairK₁ hP hK hq9
  have p₂ := pairK₂ hP hK hq9
  have hz₂ : z ∈ K₂ := p₁.mem_of_cen hz fun c hc =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hK.le₁ hc)).symm
  have hz₁ : z ∈ K₁ := p₂.mem_of_cen (by rw [sup_comm]; exact hz) fun c hc =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hK.le₂ hc)).symm
  exact ⟨hz₁, hz₂⟩

theorem exists_ab
    (hP : Stage1Pair G z S q L₁ L₂) (hK : CompData z K₁ K₂ L₁ L₂) (hq9 : q ≠ 9) (hz : z ∈ K₁ ⊔ K₂)
    (hz1 : z ≠ 1) {t : G} (ht : t ∈ K₁ ⊔ K₂) (ht2 : t * t = 1) (ht1 : t ≠ 1) (htz : t ≠ z) :
    ∃ a₁ ∈ K₁, ∃ a₂ ∈ K₂, t = a₁ * a₂ ∧ a₁ * a₁ = z ∧ a₂ * a₂ = z := by
  have p₁ := pairK₁ hP hK hq9
  have p₂ := pairK₂ hP hK hq9
  have hzI := z_mem_inf hP hK hq9 hz
  obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := p₁.exists_mul ht
  have hc12 : a₁ * a₂ = a₂ * a₁ := p₁.comm a₁ ha₁ a₂ ha₂
  have hprod : (a₁ * a₁) * (a₂ * a₂) = 1 := by
    calc (a₁ * a₁) * (a₂ * a₂) = a₁ * (a₁ * a₂) * a₂ := by group
      _ = a₁ * (a₂ * a₁) * a₂ := by rw [hc12]
      _ = (a₁ * a₂) * (a₁ * a₂) := by group
      _ = 1 := ht2
  have hI : a₁ * a₁ ∈ K₁ ⊓ K₂ := by
    refine ⟨K₁.mul_mem ha₁ ha₁, ?_⟩
    have : a₁ * a₁ = (a₂ * a₂)⁻¹ := eq_inv_of_mul_eq_one_left hprod
    rw [this]
    exact K₂.inv_mem (K₂.mul_mem ha₂ ha₂)
  have hsq : a₁ * a₁ = a₂ * a₂ := by
    have h1 := p₁.sq_of_mem_inf hI
    have : a₂ * a₂ = (a₁ * a₁)⁻¹ := eq_inv_of_mul_eq_one_right hprod
    rw [this]
    exact (inv_eq_of_mul_eq_one_right h1).symm
  have hcases : ∀ x ∈ K₁ ⊓ K₂, x = 1 ∨ x = z := fun x hx => p₁.inf_cases hzI hz1 hx
  have ha₁2 : a₁ * a₁ ≠ 1 := by
    intro h1
    have h2 : a₂ * a₂ = 1 := by rw [← hsq]; exact h1
    have h3 : a₂ ∈ K₁ ⊓ K₂ := p₁.mem_inf_of_sq ha₂ h2
    have h4 : a₁ ∈ K₂ ⊓ K₁ := p₂.mem_inf_of_sq ha₁ h1
    rw [inf_comm] at h4
    have h5 : a₁ * a₂ ∈ K₁ ⊓ K₂ := (K₁ ⊓ K₂).mul_mem h4 h3
    rcases hcases _ h5 with h | h
    · exact ht1 h
    · exact htz h
  have hz' : a₁ * a₁ = z := (hcases _ hI).resolve_left ha₁2
  exact ⟨a₁, ha₁, a₂, ha₂, rfl, hz', hsq.symm.trans hz'⟩

omit [Finite G] in
theorem exists_inverting {K K' : Subgroup G} {r r' : ℕ} (p : Pair K K' r r') {a : G} (ha : a ∈ K)
    (ha2 : a * a ≠ 1) (hI : a * a ∈ K ⊓ K') :
    ∃ y ∈ K, y * y = a * a ∧ y * a * y⁻¹ = a⁻¹ := by
  obtain ⟨F, iF, fF, e, hFq⟩ := sl2Equiv_of_model p.hm
  have hodd : Odd (Nat.card F) := hFq ▸ p.odd
  have h3 : 3 < Nat.card F := hFq ▸ p.gt
  set a' : ↥K := ⟨a, ha⟩ with ha'
  have hcen2 : a' * a' ∈ center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (p.comm g g.2 (a * a) hI.2)
  have hncen : a' ∉ center ↥K := by
    intro hc
    have hc' : ∀ c ∈ K, c * a = a * c := fun c hc'' => by
      have := Subgroup.mem_center_iff.1 hc ⟨c, hc''⟩
      exact congrArg Subtype.val this
    exact ha2 (p.sq_of_mem_inf ⟨ha, p.cen ha hc'⟩)
  have hea : e a' * e a' = CFSG.Semidihedral.OddFieldSL2.minusIdentity F :=
    sq_eq_minusIdentity e hodd hcen2 hncen
  have hecen : e a' * e a' ∈ center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    rw [← map_mul, mem_center_equiv_iff e]
    simpa using hcen2
  let α : MulAut (Matrix.SpecialLinearGroup (Fin 2) F) := MulAut.conj (e a')
  have hα2 : α * α = 1 := by
    apply MulEquiv.ext
    intro x
    show e a' * (e a' * x * (e a')⁻¹) * (e a')⁻¹ = x
    have hc := Subgroup.mem_center_iff.1 hecen
    calc e a' * (e a' * x * (e a')⁻¹) * (e a')⁻¹ = (e a' * e a') * x * (e a' * e a')⁻¹ := by group
      _ = x := by rw [← hc x]; group
  have hα1 : α ≠ 1 := by
    intro h
    apply hncen
    have hc : e a' ∈ center (Matrix.SpecialLinearGroup (Fin 2) F) := by
      rw [Subgroup.mem_center_iff]
      intro x
      have := congrArg (fun γ : MulAut (Matrix.SpecialLinearGroup (Fin 2) F) => γ x) h
      simp only [α, MulAut.conj_apply, MulAut.one_apply] at this
      calc x * e a' = (e a' * x * (e a')⁻¹) * e a' := by rw [this]
        _ = e a' * x := by group
    rw [mem_center_equiv_iff e] at hc
    simpa using hc
  obtain ⟨x, hx2, hαx⟩ := IVK.exists_inverted_sl hodd h3 α hα2 hα1
  have hxx : x * x = CFSG.Semidihedral.OddFieldSL2.minusIdentity F := by
    apply Subtype.ext
    simp [CFSG.Semidihedral.OddFieldSL2.minusIdentity, hx2]
  set y' : ↥K := e.symm x with hy'
  have hyy : y' * y' = a' * a' := by
    apply e.injective
    rw [map_mul, map_mul, hy', MulEquiv.apply_symm_apply, hxx, hea]
  have hay : a' * y' * a'⁻¹ = y'⁻¹ := by
    apply e.injective
    simp only [map_mul, map_inv, hy', MulEquiv.apply_symm_apply]
    have : α x = e a' * x * (e a')⁻¹ := rfl
    rw [← this, hαx]
  refine ⟨(y' : G), y'.2, ?_, ?_⟩
  · exact congrArg Subtype.val hyy
  · have h1 : y' * a' * y'⁻¹ = a'⁻¹ := by
      have e1 : y' * a' = a' * y'⁻¹ := by
        have : y' * a' * y' = a' := by
          have h2 : a' * y' = y'⁻¹ * a' := by
            calc a' * y' = (a' * y' * a'⁻¹) * a' := by group
              _ = y'⁻¹ * a' := by rw [hay]
          calc y' * a' * y' = y' * (a' * y') := by group
            _ = y' * (y'⁻¹ * a') := by rw [h2]
            _ = a' := by group
        calc y' * a' = (y' * a' * y') * y'⁻¹ := by group
          _ = a' * y'⁻¹ := by rw [this]
      calc y' * a' * y'⁻¹ = a' * y'⁻¹ * y'⁻¹ := by rw [e1]
        _ = a' * (y' * y')⁻¹ := by group
        _ = a' * (a' * a')⁻¹ := by rw [hyy]
        _ = a'⁻¹ := by group
    exact congrArg Subtype.val h1

theorem exists_y₀
    (hP : Stage1Pair G z S q L₁ L₂) (hK : CompData z K₁ K₂ L₁ L₂) (hq9 : q ≠ 9)
    {U : Subgroup G} (hUsup : ∀ u ∈ U, u ∈ K₁ ⊔ K₂) (hU4 : IVK.IsFourSubgroup U)
    {t : G} (hzU : z ∈ U) (htU : t ∈ U) (hz1 : z ≠ 1) (ht1 : t ≠ 1) (htz : t ≠ z) :
    ∃ y ∈ K₁ ⊔ K₂, y * y = 1 ∧ y ∉ U ∧ ∀ u ∈ U, y * u = u * y := by
  have hUsq := four_sq hU4
  have hz2 : z * z = 1 := hUsq z hzU
  have p₁ := pairK₁ hP hK hq9
  have p₂ := pairK₂ hP hK hq9
  have hzI := z_mem_inf hP hK hq9 (hUsup z hzU)
  obtain ⟨a₁, ha₁, a₂, ha₂, rfl, ha₁z, ha₂z⟩ :=
    exists_ab hP hK hq9 (hUsup z hzU) hz1 (hUsup t htU) (hUsq t htU) ht1 htz
  have hz1' : a₁ * a₁ ≠ 1 := by rw [ha₁z]; exact hz1
  have hI₁ : a₁ * a₁ ∈ K₁ ⊓ K₂ := by rw [ha₁z]; exact hzI
  have hI₂ : a₂ * a₂ ∈ K₂ ⊓ K₁ := by rw [ha₂z, inf_comm]; exact hzI
  obtain ⟨y₁, hy₁, hy₁sq, hy₁a⟩ := exists_inverting p₁ ha₁ hz1' hI₁
  obtain ⟨y₂, hy₂, hy₂sq, hy₂a⟩ := exists_inverting p₂ ha₂ (by rw [ha₂z]; exact hz1) hI₂
  have hy₁₂ : y₁ * y₂ = y₂ * y₁ := p₁.comm y₁ hy₁ y₂ hy₂
  have ha₁₂ : a₁ * a₂ = a₂ * a₁ := p₁.comm a₁ ha₁ a₂ ha₂
  have hy₁a₂ : y₁ * a₂ = a₂ * y₁ := p₁.comm y₁ hy₁ a₂ ha₂
  have hy₂a₁ : y₂ * a₁ = a₁ * y₂ := (p₁.comm a₁ ha₁ y₂ hy₂).symm
  have hzc : ∀ c ∈ Cen z, c * z = z * c := fun c hc => Subgroup.mem_centralizer_singleton_iff.mp hc
  have hC₁ : ∀ c ∈ K₁, c ∈ Cen z := fun c hc => hK.le₁ hc
  have hC₂ : ∀ c ∈ K₂, c ∈ Cen z := fun c hc => hK.le₂ hc
  have ha₁inv : a₁⁻¹ = a₁ * z := by
    calc a₁⁻¹ = a₁ * (a₁ * a₁)⁻¹ := by group
      _ = a₁ * z := by rw [ha₁z, inv_eq_of_mul_eq_one_right hz2]
  have ha₂inv : a₂⁻¹ = a₂ * z := by
    calc a₂⁻¹ = a₂ * (a₂ * a₂)⁻¹ := by group
      _ = a₂ * z := by rw [ha₂z, inv_eq_of_mul_eq_one_right hz2]
  have hy₁a' : y₁ * a₁ = a₁⁻¹ * y₁ := by
    calc y₁ * a₁ = (y₁ * a₁ * y₁⁻¹) * y₁ := by group
      _ = a₁⁻¹ * y₁ := by rw [hy₁a]
  have hy₂a' : y₂ * a₂ = a₂⁻¹ * y₂ := by
    calc y₂ * a₂ = (y₂ * a₂ * y₂⁻¹) * y₂ := by group
      _ = a₂⁻¹ * y₂ := by rw [hy₂a]
  have hy₁sq' : y₁ * y₁ = z := hy₁sq.trans ha₁z
  have hy₂sq' : y₂ * y₂ = z := hy₂sq.trans ha₂z
  have hy₀C : y₁ * y₂ ∈ Cen z := (Cen z).mul_mem (hC₁ y₁ hy₁) (hC₂ y₂ hy₂)
  have hy₀z : (y₁ * y₂) * z = z * (y₁ * y₂) := hzc _ hy₀C
  have hy₀t : (y₁ * y₂) * (a₁ * a₂) = (a₁ * a₂) * (y₁ * y₂) := by
    have hzc₁ : ∀ c ∈ K₁, z * c = c * z := fun c hc => (hzc c (hC₁ c hc)).symm
    have h1 : (y₁ * y₂) * (a₁ * a₂) = (y₁ * a₁) * (y₂ * a₂) := by
      calc (y₁ * y₂) * (a₁ * a₂) = y₁ * (y₂ * a₁) * a₂ := by group
        _ = y₁ * (a₁ * y₂) * a₂ := by rw [hy₂a₁]
        _ = (y₁ * a₁) * (y₂ * a₂) := by group
    rw [h1, hy₁a', hy₂a', ha₁inv, ha₂inv]
    have e1 : (a₁ * z * y₁) * (a₂ * z * y₂) = (a₁ * a₂) * (z * z) * (y₁ * y₂) := by
      have hz₁ : y₁ * (a₂ * z) = (a₂ * z) * y₁ := by
        calc y₁ * (a₂ * z) = (y₁ * a₂) * z := by group
          _ = (a₂ * y₁) * z := by rw [hy₁a₂]
          _ = a₂ * (y₁ * z) := by group
          _ = a₂ * (z * y₁) := by rw [hzc y₁ (hC₁ y₁ hy₁)]
          _ = (a₂ * z) * y₁ := by group
      calc (a₁ * z * y₁) * (a₂ * z * y₂) = a₁ * z * (y₁ * (a₂ * z)) * y₂ := by group
        _ = a₁ * z * ((a₂ * z) * y₁) * y₂ := by rw [hz₁]
        _ = a₁ * (z * a₂) * (z * (y₁ * y₂)) := by group
        _ = a₁ * (a₂ * z) * (z * (y₁ * y₂)) := by rw [← hzc a₂ (hC₂ a₂ ha₂)]
        _ = (a₁ * a₂) * (z * z) * (y₁ * y₂) := by group
    rw [e1, hz2, mul_one]
  have hy₀a : (y₁ * y₂) * a₁ = a₁⁻¹ * (y₁ * y₂) := by
    calc (y₁ * y₂) * a₁ = y₁ * (y₂ * a₁) := by group
      _ = y₁ * (a₁ * y₂) := by rw [hy₂a₁]
      _ = (y₁ * a₁) * y₂ := by group
      _ = a₁⁻¹ * y₁ * y₂ := by rw [hy₁a']
      _ = a₁⁻¹ * (y₁ * y₂) := by group
  refine ⟨y₁ * y₂, (K₁ ⊔ K₂).mul_mem (Subgroup.mem_sup_left hy₁) (Subgroup.mem_sup_right hy₂), ?_, ?_, ?_⟩
  · calc (y₁ * y₂) * (y₁ * y₂) = (y₁ * y₁) * (y₂ * y₂) := by
          calc (y₁ * y₂) * (y₁ * y₂) = y₁ * (y₂ * y₁) * y₂ := by group
            _ = y₁ * (y₁ * y₂) * y₂ := by rw [← hy₁₂]
            _ = (y₁ * y₁) * (y₂ * y₂) := by group
      _ = 1 := by rw [hy₁sq', hy₂sq', hz2]
  · intro hmem
    have hdescr := four_descr hU4 hzU htU hz1 ht1 htz hUsq (y₁ * y₂) hmem
    have hcomm_a₁ : (y₁ * y₂) * a₁ = a₁ * (y₁ * y₂) := by
      rcases hdescr with h | h | h | h
      · rw [h]; group
      · rw [h]; exact (hzc a₁ (hC₁ a₁ ha₁)).symm
      · rw [h]
        calc (a₁ * a₂) * a₁ = a₁ * (a₂ * a₁) := by group
          _ = a₁ * (a₁ * a₂) := by rw [← ha₁₂]
          _ = a₁ * (a₁ * a₂) := rfl
      · rw [h]
        calc z * (a₁ * a₂) * a₁ = z * (a₁ * (a₂ * a₁)) := by group
          _ = z * (a₁ * (a₁ * a₂)) := by rw [← ha₁₂]
          _ = (z * a₁) * (a₁ * a₂) := by group
          _ = (a₁ * z) * (a₁ * a₂) := by rw [← hzc a₁ (hC₁ a₁ ha₁)]
          _ = a₁ * (z * (a₁ * a₂)) := by group
    rw [hy₀a] at hcomm_a₁
    have : a₁⁻¹ = a₁ := mul_right_cancel hcomm_a₁
    have h2 : a₁ * a₁ = 1 := by
      calc a₁ * a₁ = a₁⁻¹⁻¹ * a₁ := by group
        _ = 1 := by rw [this]; group
    exact hz1' h2
  · intro u hu
    rcases four_descr hU4 hzU htU hz1 ht1 htz hUsq u hu with h | h | h | h
    · rw [h]; group
    · rw [h]; exact hy₀z
    · rw [h]; exact hy₀t
    · rw [h]
      calc (y₁ * y₂) * (z * (a₁ * a₂)) = ((y₁ * y₂) * z) * (a₁ * a₂) := by group
        _ = (z * (y₁ * y₂)) * (a₁ * a₂) := by rw [hy₀z]
        _ = z * ((y₁ * y₂) * (a₁ * a₂)) := by group
        _ = z * ((a₁ * a₂) * (y₁ * y₂)) := by rw [hy₀t]
        _ = (z * (a₁ * a₂)) * (y₁ * y₂) := by group

end Main

end CFSG.GH74.GLS.Stage2.Final.Thm6.L2012
