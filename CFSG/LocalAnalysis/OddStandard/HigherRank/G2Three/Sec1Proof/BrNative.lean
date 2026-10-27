module

public import CFSG.LocalAnalysis.EvenBN.LinearThree.Excl27G2Facts
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Frame

public section

namespace CFSG.OddStandard.HigherRank.G2Three.Sec1Proof

open CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.Blueprint.Chevalley CFSG.LieType.Ree Subgroup
open CFSG.RankThree.PartTwo.Census.Carrier.G2Three

abbrev NG : Type := ↥(adjointGroup ReeTag.G2.tag (ZMod 3))


noncomputable abbrev phiN : MulAut NG := ReeTag.G2.finiteExceptionalAut (ZMod 3)


theorem center_NG : Subgroup.center NG = ⊥ :=
  CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := Tag.G2) (K := ZMod 3)

theorem conj_inj_NG : Function.Injective (MulAut.conj : NG →* MulAut NG) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← center_NG]
  intro y hy
  rw [Subgroup.mem_center_iff]
  intro x
  have h1 := congrArg (fun φ : MulAut NG => φ x) (MonoidHom.mem_ker.1 hy)
  simp only [MulAut.conj_apply, MulAut.one_apply] at h1
  calc x * y = y * x * y⁻¹ * y := by rw [h1]
    _ = y * x := by group

theorem card_NG : Nat.card NG = 4245696 :=
  (Nat.card_congr adjointEquivR3.toEquiv).trans card_R3

theorem aut_cases_NG (α : MulAut NG) :
    (∃ g, α = MulAut.conj g) ∨ ∃ g, α = MulAut.conj g * phiN :=
  CFSG.LocalAnalysis.EvenBN.LinearThree.G2Three.aut_cases (K := ZMod 3)
    (by rw [Nat.card_zmod]) α

theorem phiN_mul_self : phiN * phiN = 1 := by
  have h := CFSG.LocalAnalysis.EvenBN.LinearThree.G2Three.phi_sq (K := ZMod 3)
    (by rw [Nat.card_zmod])
  rwa [pow_two] at h

theorem phiN_not_inner : phiN ∉ innerAut NG := by
  simpa only [innerAut] using
    (CFSG.LocalAnalysis.EvenBN.LinearThree.G2Three.phi_not_mem_range (K := ZMod 3)
      (by rw [Nat.card_zmod]))

theorem phiN_mul_conj (g : NG) : phiN * MulAut.conj g = MulAut.conj (phiN g) * phiN := by
  have h := CFSG.LocalAnalysis.EvenBN.LinearThree.G2Three.mulAut_mul_conj_mul_inv phiN g
  rw [show phiN⁻¹ = phiN from inv_eq_of_mul_eq_one_right phiN_mul_self] at h
  calc phiN * MulAut.conj g
      = phiN * MulAut.conj g * (phiN * phiN) := by rw [phiN_mul_self, mul_one]
    _ = phiN * MulAut.conj g * phiN * phiN := by group
    _ = MulAut.conj (phiN g) * phiN := by rw [h]

private theorem card_innerAut_aux : Nat.card (innerAut NG) = 4245696 :=
  (Nat.card_congr (MonoidHom.ofInjective conj_inj_NG).toEquiv).symm.trans card_NG

private theorem innerAut_index : (innerAut NG).index = 2 := by
  rw [Subgroup.index_eq_two_iff_exists_notMem_and]
  refine ⟨phiN, phiN_not_inner, fun b => ?_⟩
  rcases aut_cases_NG b with ⟨g, rfl⟩ | ⟨g, rfl⟩
  · exact Or.inr ⟨g, rfl⟩
  · refine Or.inl ?_
    rw [mul_assoc, phiN_mul_self, mul_one]
    exact ⟨g, rfl⟩

theorem card_mulAut_NG : Nat.card (MulAut NG) = 8491392 := by
  have h := Subgroup.card_mul_index (innerAut NG)
  rw [card_innerAut_aux, innerAut_index] at h
  rw [← h]

theorem normal_innerAut_NG : (innerAut NG).Normal :=
  ⟨fun n hn θ => by
    obtain ⟨g, rfl⟩ := hn
    rw [CFSG.LocalAnalysis.EvenBN.LinearThree.G2Three.mulAut_mul_conj_mul_inv]
    exact ⟨θ g, rfl⟩⟩

theorem card_innerAut_NG : Nat.card (innerAut NG) = 4245696 := card_innerAut_aux

theorem orderOf_conj_NG (g : NG) : orderOf (MulAut.conj g) = orderOf g :=
  orderOf_injective (MulAut.conj : NG →* MulAut NG) conj_inj_NG g

private theorem centEl_innerAut_conj (a : NG) :
    centEl (innerAut NG) (MulAut.conj a) =
      (Subgroup.centralizer {a}).map (MulAut.conj : NG →* MulAut NG) := by
  ext x
  constructor
  · intro hx
    simp only [centEl, Subgroup.mem_inf] at hx
    obtain ⟨hxInn, hxcent⟩ := hx
    obtain ⟨g, rfl⟩ := hxInn
    refine ⟨g, Subgroup.mem_centralizer_singleton_iff.mpr ?_, rfl⟩
    have h2 : MulAut.conj (g * a) = MulAut.conj (a * g) := by
      rw [map_mul, map_mul]
      exact Subgroup.mem_centralizer_singleton_iff.mp hxcent
    exact conj_inj_NG h2
  · rintro ⟨g, hg, rfl⟩
    simp only [centEl, Subgroup.mem_inf]
    refine ⟨⟨g, rfl⟩, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp hg]

theorem invol_conj_NG : ∀ u ∈ invols (innerAut NG), ∀ v ∈ invols (innerAut NG),
    ∃ l ∈ innerAut NG, v = l * u * l⁻¹ := by
  intro u hu v hv
  obtain ⟨hu_mem, hu_ord⟩ := hu
  obtain ⟨hv_mem, hv_ord⟩ := hv
  obtain ⟨a, rfl⟩ := hu_mem
  obtain ⟨b, rfl⟩ := hv_mem
  have ha2 : orderOf a = 2 := by rw [← orderOf_conj_NG a]; exact hu_ord
  have hb2 : orderOf b = 2 := by rw [← orderOf_conj_NG b]; exact hv_ord
  let e : NG ≃* H3 := adjointEquivR3
  obtain ⟨g₁, hg₁⟩ := exists_conj_of_sylow (t := tH) (S := S2H) card_R3 card_S2H
    exists_conj_of_mem_S2H (s := e a) (by rw [MulEquiv.orderOf_eq]; exact ha2)
  obtain ⟨g₂, hg₂⟩ := exists_conj_of_sylow (t := tH) (S := S2H) card_R3 card_S2H
    exists_conj_of_mem_S2H (s := e b) (by rw [MulEquiv.orderOf_eq]; exact hb2)
  let c : NG := e.symm (g₂ * g₁⁻¹)
  have hc : e c = g₂ * g₁⁻¹ := e.apply_symm_apply _
  have hbc : b = c * a * c⁻¹ := by
    apply e.injective
    calc e b = g₂ * tH * g₂⁻¹ := hg₂
      _ = (g₂ * g₁⁻¹) * (g₁ * tH * g₁⁻¹) * (g₂ * g₁⁻¹)⁻¹ := by group
      _ = (g₂ * g₁⁻¹) * e a * (g₂ * g₁⁻¹)⁻¹ := by rw [hg₁]
      _ = e c * e a * (e c)⁻¹ := by rw [hc]
      _ = e (c * a * c⁻¹) := by simp only [map_mul, map_inv]
  refine ⟨MulAut.conj c, ⟨c, rfl⟩, ?_⟩
  rw [hbc]
  simp only [map_mul, map_inv]

theorem card_cent_NG : ∀ u ∈ invols (innerAut NG), Nat.card (centEl (innerAut NG) u) = 576 := by
  intro u hu
  obtain ⟨hu_mem, hu_ord⟩ := hu
  obtain ⟨a, rfl⟩ := hu_mem
  have ha2 : orderOf a = 2 := by rw [← orderOf_conj_NG a]; exact hu_ord
  rw [centEl_innerAut_conj a, Subgroup.card_map_of_injective conj_inj_NG]
  exact CFSG.LocalAnalysis.EvenBN.LinearThree.G2Three.card_centralizer_of_orderOf_eq_two
    (K := ZMod 3) (by rw [Nat.card_zmod]) ha2

end CFSG.OddStandard.HigherRank.G2Three.Sec1Proof
