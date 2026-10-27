module

public import CFSG.HardMathSupport.Solomon.Coordinator.I19_5_2Crit
public import CFSG.HardMathSupport.Solomon.Coordinator.I19_5_2A6Perm
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3AutIso

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Models CFSG.QuasithinUnique.A6Facts
  CFSG.QuasithinUnique.Setup.X3Aut Equiv Pointwise

set_option maxRecDepth 100000

theorem tAddI_eq : tAddI = (tSq * tAdd * tSq⁻¹)⁻¹ := by decide +kernel

theorem tAdd_mem : tAdd ∈ autA6 := Subgroup.subset_closure (by simp)

theorem tSq_mem : tSq ∈ autA6 := Subgroup.subset_closure (by simp)

theorem tAddI_mem : tAddI ∈ autA6 := by
  rw [tAddI_eq]
  exact autA6.inv_mem (autA6.mul_mem (autA6.mul_mem tSq_mem tAdd_mem) (autA6.inv_mem tSq_mem))

theorem tau_mem (ab : Fin 3 × Fin 3) : tau ab ∈ autA6 :=
  autA6.mul_mem (autA6.pow_mem tAdd_mem _) (autA6.pow_mem tAddI_mem _)

@[expose] def transAut : Subgroup ↥autA6 where
  carrier := {x | ∃ ab, (x : Perm (Fin 10)) = tau ab}
  mul_mem' := fun {a b} ⟨ab, ha⟩ ⟨cd, hb⟩ => by
    obtain ⟨ef, h⟩ := tau_mul ab cd
    exact ⟨ef, by rw [Subgroup.coe_mul, ha, hb, h]⟩
  one_mem' := by
    obtain ⟨ab, h⟩ := tau_one
    exact ⟨ab, h⟩
  inv_mem' := fun {a} ⟨ab, ha⟩ => by
    obtain ⟨cd, h⟩ := tau_inv ab
    exact ⟨cd, by rw [Subgroup.coe_inv, ha, h]⟩

theorem transAut_card : Nat.card transAut = 9 := by
  have : Nat.card (Fin 3 × Fin 3) = 9 := by simp
  rw [← this]
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun ab => (⟨⟨tau ab, tau_mem ab⟩, ab, rfl⟩ : transAut)) ⟨?_, ?_⟩)
  · intro ab cd h
    exact tau_inj _ _ (congrArg (fun x : transAut => ((x : ↥autA6) : Perm (Fin 10))) h)
  · rintro ⟨x, ab, hab⟩
    exact ⟨ab, Subtype.ext (Subtype.ext hab.symm)⟩

theorem factorization_three : (Nat.card ↥autA6).factorization 3 = 2 := by
  rw [card_autA6]
  have hp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  apply le_antisymm
  · by_contra hlt
    have : 3 ^ 3 ∣ 1440 := (Nat.Prime.pow_dvd_iff_le_factorization hp.out (by norm_num)).mpr
      (by omega)
    omega
  · exact (Nat.Prime.pow_dvd_iff_le_factorization hp.out (by norm_num)).mp (by norm_num)

theorem central_aut {D : Subgroup ↥autA6} (hD : Nat.card D = 9) {y : ↥autA6}
    (hy : y ∈ Subgroup.centralizer (D : Set ↥autA6)) (hcop : Nat.Coprime 3 (orderOf y)) :
    y = 1 := by
  have hp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfin : Finite ↥autA6 := inferInstance
  let PT : Sylow 3 ↥autA6 := Sylow.ofCard transAut (by rw [transAut_card, factorization_three]; norm_num)
  let DT : Sylow 3 ↥autA6 := Sylow.ofCard D (by rw [hD, factorization_three]; norm_num)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥autA6 PT DT
  have hmem : ∀ p ∈ transAut, g * p * g⁻¹ ∈ D := by
    intro p hp'
    have hp'' : p ∈ (PT : Subgroup ↥autA6) := hp'
    have h1 : MulAut.conj g • p ∈ (MulAut.conj g • (PT : Subgroup ↥autA6)) :=
      Subgroup.smul_mem_pointwise_smul _ _ _ hp''
    have h2 : (MulAut.conj g • (PT : Subgroup ↥autA6)) = (DT : Subgroup ↥autA6) := by
      rw [← Sylow.coe_subgroup_smul, hg]
    rw [h2] at h1
    have h3 : g * p * g⁻¹ ∈ (DT : Subgroup ↥autA6) := by
      simpa [MulAut.smul_def, MulAut.conj_apply] using h1
    exact h3
  have hcomm : ∀ p ∈ transAut, Commute (g⁻¹ * y * g) p := by
    intro p hp'
    have h := Subgroup.mem_centralizer_iff.mp hy _ (hmem p hp')
    show g⁻¹ * y * g * p = p * (g⁻¹ * y * g)
    calc g⁻¹ * y * g * p = g⁻¹ * (y * (g * p * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * p * g⁻¹) * y) * g := by rw [h]
      _ = p * (g⁻¹ * y * g) := by group
  have hA : (⟨tAdd, tAdd_mem⟩ : ↥autA6) ∈ transAut := ⟨(1, 0), tAdd_eq_tau⟩
  have hB : (⟨tAddI, tAddI_mem⟩ : ↥autA6) ∈ transAut := ⟨(0, 1), tAddI_eq_tau⟩
  have hc1 : Commute (((g⁻¹ * y * g : ↥autA6)) : Perm (Fin 10)) tAdd :=
    congrArg Subtype.val (hcomm _ hA)
  have hc2 : Commute (((g⁻¹ * y * g : ↥autA6)) : Perm (Fin 10)) tAddI :=
    congrArg Subtype.val (hcomm _ hB)
  obtain ⟨t, hte⟩ := exists_tau_of_commute hc1 hc2
  have h9 : (g⁻¹ * y * g) ^ 9 = 1 := by
    apply Subtype.ext
    simp only [Subgroup.coe_pow, hte, Subgroup.coe_one]
    exact tau_pow_nine t
  have hy9 : y ^ 9 = 1 := by
    have : y ^ 9 = g * ((g⁻¹ * y * g) ^ 9) * g⁻¹ := by
      have h := conj_pow (a := g⁻¹) (b := y) (i := 9)
      rw [inv_inv] at h
      rw [h]; group
    rw [this, h9]; group
  have hdvd : orderOf y ∣ 3 ^ 2 := by
    have := orderOf_dvd_of_pow_eq_one hy9
    simpa using this
  have := Nat.Coprime.eq_one_of_dvd (hcop.symm.pow_right 2) hdvd
  exact orderOf_eq_one_iff.mp this

theorem isLocallyBalancedAbs_A6 :
    CFSG.HardMathSupport.Timmesfeld.Coordinator.IsLocallyBalancedAbs 3 2
      (alternatingGroup (Fin 6)) := by
  refine isLocallyBalancedAbs_three_two_of_central ?_
  intro D _ hD y hy hcop
  have hD' : Nat.card (D.map thetaEquiv.symm.toMonoidHom) = 9 := by
    rw [← hD]
    exact Subgroup.card_map_of_injective thetaEquiv.symm.injective
  have hy' : thetaEquiv.symm y ∈ Subgroup.centralizer
      ((D.map thetaEquiv.symm.toMonoidHom : Subgroup ↥autA6) : Set ↥autA6) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨d, hd, rfl⟩
    have := Subgroup.mem_centralizer_iff.mp hy d hd
    simpa only [MulEquiv.coe_toMonoidHom, map_mul] using congrArg thetaEquiv.symm this
  have hcop' : Nat.Coprime 3 (orderOf (thetaEquiv.symm y)) := by
    rwa [MulEquiv.orderOf_eq]
  have h1 := central_aut hD' hy' hcop'
  simpa using h1

end CFSG.HardMathSupport.Solomon.Coordinator
