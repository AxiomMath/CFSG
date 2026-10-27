module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyAtlas
public import CFSG.LocalAnalysis.ComponentClassification.CentralCoverLemmasBActionKernel
public import CFSG.Sporadic.SmallOddCore.HSAut

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup CFSG.ComponentClassification CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier
  CFSG.Blueprint CFSG.Blueprint.NativeSporadic

namespace SAFyHOuter

section Abstract

variable {H : Type*} [Group H] {E : Subgroup H} {Q : Type*} [Group Q]

theorem sq_eq_one_of_mem_center (hZ : Nat.card (center E) = 2) {z : E} (hz : z ∈ center E) :
    z ^ 2 = 1 := by
  have h : (⟨z, hz⟩ : center E) ^ 2 = 1 := by
    rw [← hZ]
    exact pow_card_eq_one'
  exact congrArg Subtype.val h

theorem exists_order_three_of_fixed [E.Normal] (π : E →* Q) (hπ : Function.Surjective π)
    (hker : π.ker = center E) (hZ : Nat.card (center E) = 2) {w : H} {ρ : Q}
    (hρ : orderOf ρ = 3) (hfix : CentralCover.fullAction π hπ hker w ρ = ρ) :
    ∃ r ∈ E, orderOf r = 3 ∧ r * w = w * r := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e, rfl⟩ := hπ ρ
  have hρ3 : π e ^ 3 = 1 := by rw [← hρ]; exact pow_orderOf_eq_one _
  have hρ1 : π e ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hρ
    omega
  have he3 : e ^ 3 ∈ center E := by
    rw [← hker, MonoidHom.mem_ker, map_pow, hρ3]
  have he6 : (e ^ 3) ^ 2 = 1 := sq_eq_one_of_mem_center hZ he3
  set a : E := MulAut.conjNormal w e with ha
  have hπa : π a = π e := by
    rw [ha, ← CentralCover.fullAction_apply π hπ hker, hfix]
  have hc : e⁻¹ * a ∈ center E := by
    rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hπa, inv_mul_cancel]
  have hc2 : (e⁻¹ * a) ^ 2 = 1 := sq_eq_one_of_mem_center hZ hc
  have hcomm : Commute e (e⁻¹ * a) := mem_center_iff.mp hc e
  have hae : a = e * (e⁻¹ * a) := by group
  have hr1 : e ^ 4 ≠ 1 := by
    intro h
    apply hρ1
    have h4 : π e ^ 4 = 1 := by rw [← map_pow, h, map_one]
    calc π e = π e ^ 4 * (π e ^ 3)⁻¹ := by group
      _ = 1 := by rw [h4, hρ3]; group
  have hr3 : (e ^ 4) ^ 3 = 1 := by
    calc (e ^ 4) ^ 3 = ((e ^ 3) ^ 2) ^ 2 := by group
      _ = 1 := by rw [he6, one_pow]
  have hfixr : MulAut.conjNormal w (e ^ 4) = e ^ 4 := by
    rw [map_pow, ← ha]
    calc a ^ 4 = (e * (e⁻¹ * a)) ^ 4 := by rw [← hae]
      _ = e ^ 4 * (e⁻¹ * a) ^ 4 := hcomm.mul_pow 4
      _ = e ^ 4 := by
        rw [show (e⁻¹ * a) ^ 4 = ((e⁻¹ * a) ^ 2) ^ 2 by group, hc2, one_pow, mul_one]
  refine ⟨((e ^ 4 : E) : H), (e ^ 4).2, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime hr3 hr1
  · have h1 := congrArg Subtype.val hfixr
    rw [MulAut.conjNormal_apply] at h1
    calc ((e ^ 4 : E) : H) * w = (w * ((e ^ 4 : E) : H) * w⁻¹) * w := by rw [h1]
      _ = w * ((e ^ 4 : E) : H) := by group

end Abstract

section HS

theorem exists_fixed_order_three
    (α : MulAut ↥hsP)
    (hα2 : α * α = 1) (hαin : α ∉ OuterAutomorphisms.inner ↥hsP) :
    ∃ ρ : ↥hsP, orderOf ρ = 3 ∧ α ρ = ρ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hM := hs_autModel
  obtain ⟨-, -, -, hrows, hcover, -, hmap, -⟩ := hs_involution_centralizers
  set t : Equiv.Perm (Fin 3850) := hM.elt α with ht
  have htR : t ∈ hsR := hM.elt_mem α
  have hconj : ∀ p : ↥hsP, ((α p : ↥hsP) : Equiv.Perm (Fin 3850)) = t * p * t⁻¹ :=
    hM.elt_spec α
  have htt : t * t = 1 := by
    have h := congrArg hM.hom hα2
    rw [map_mul, map_one] at h
    exact h
  have htP : t ∉ hsP := by
    intro h
    refine hαin ⟨⟨t, h⟩, ?_⟩
    ext p
    simp [hconj]
  have ht2 : orderOf t = 2 := by
    refine orderOf_eq_prime (by rw [sq]; exact htt) fun h1 => htP ?_
    rw [h1]
    exact hsP.one_mem
  obtain ⟨r, hr, g, hg, htg⟩ := hcover t htR ht2
  obtain ⟨-, -, hout, -, hcard, -⟩ := hrows r hr
  have hτP : tp 3850 r.rep ∉ hsP := fun hmem => htP (by
    rw [htg]
    exact hsP.mul_mem (hsP.mul_mem hg hmem) (hsP.inv_mem hg))
  have hro : r.outer = true := hout.2 hτP
  have h3 : 3 ∣ r.centOrder := by
    have hmem : (r.outer, r.classSize, r.centOrder) ∈
        hsRows.map (fun r => (r.outer, r.classSize, r.centOrder)) := List.mem_map_of_mem hr
    rw [hmap] at hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨ho, -⟩ | ⟨ho, -⟩ | ⟨-, -, hc⟩ | ⟨-, -, hc⟩
    · exact absurd (ho.symm.trans hro) (by decide)
    · exact absurd (ho.symm.trans hro) (by decide)
    · rw [hc]; norm_num
    · rw [hc]; norm_num
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 3 (hcard ▸ h3)
  have hcP : (c : Equiv.Perm (Fin 3850)) ∈ hsP := (mem_inf.mp c.2).1
  have hcC : (tp 3850 r.rep) * (c : Equiv.Perm (Fin 3850)) =
      (c : Equiv.Perm (Fin 3850)) * tp 3850 r.rep :=
    (mem_centralizer_singleton_iff.mp (mem_inf.mp c.2).2).symm
  have hc3 : orderOf (c : Equiv.Perm (Fin 3850)) = 3 := by rw [Subgroup.orderOf_coe]; exact hc
  set ρ0 : Equiv.Perm (Fin 3850) := g * c * g⁻¹ with hρ0
  have hρP : ρ0 ∈ hsP := hsP.mul_mem (hsP.mul_mem hg hcP) (hsP.inv_mem hg)
  have hρ3 : orderOf ρ0 = 3 := by
    rw [hρ0]
    exact (MulEquiv.orderOf_eq (MulAut.conj g) _).trans hc3
  have hρt : ρ0 * t = t * ρ0 := by
    rw [htg, hρ0]
    calc g * c * g⁻¹ * (g * tp 3850 r.rep * g⁻¹) = g * (c * tp 3850 r.rep) * g⁻¹ := by group
      _ = g * (tp 3850 r.rep * c) * g⁻¹ := by rw [hcC]
      _ = g * tp 3850 r.rep * g⁻¹ * (g * c * g⁻¹) := by group
  refine ⟨⟨ρ0, hρP⟩, ?_, ?_⟩
  · rw [← Subgroup.orderOf_coe]
    exact hρ3
  · apply Subtype.ext
    rw [hconj]
    show t * ρ0 * t⁻¹ = ρ0
    rw [← hρt, mul_inv_cancel_right]

end HS

end SAFyHOuter

theorem hsOuterThree :
    HSOuterThree := by
  intro H _ _ E hE w hw hwE
  have := hE.normal
  have := hE.perfect
  obtain ⟨ψ⟩ := hE.quotient
  have ψ' : ↥E ⧸ center ↥E ≃* NativeSporadic.HS := ψ
  let f : ↥E ⧸ center ↥E ≃* hsP := ψ'.trans hsPermEquiv
  let π : ↥E →* hsP := f.toMonoidHom.comp (QuotientGroup.mk' (center ↥E))
  have hπ : Function.Surjective π := f.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = center ↥E := by
    ext x
    simp only [MonoidHom.mem_ker, π, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      QuotientGroup.mk'_apply]
    rw [map_eq_one_iff _ f.injective, QuotientGroup.eq_one_iff]
  have hα2 : CentralCover.fullAction π hπ hker w * CentralCover.fullAction π hπ hker w = 1 := by
    rw [← map_mul, hw, map_one]
  have hαin : CentralCover.fullAction π hπ hker w ∉ OuterAutomorphisms.inner ↥hsP :=
    CentralCover.fullAction_notMem_inner π hπ hker hE.centralizer_le hwE
  obtain ⟨ρ, hρ, hρα⟩ := SAFyHOuter.exists_fixed_order_three _ hα2 hαin
  exact SAFyHOuter.exists_order_three_of_fixed π hπ hker hE.card_center hρ hρα

end CFSG.EvenSporadicStandard.TwoHS
