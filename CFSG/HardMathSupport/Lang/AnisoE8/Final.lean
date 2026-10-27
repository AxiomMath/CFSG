module

public import CFSG.HardMathSupport.Lang.AnisoE8.D8Family
public import CFSG.HardMathSupport.Lang.AnisoE8.ElementE1
public import CFSG.HardMathSupport.Lang.AnisoE8.D8Planes
public import CFSG.HardMathSupport.Lang.AnisoF4.Final

public noncomputable section

namespace CFSG.HardMathSupport.Lang.AnisoE8

open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.LieType.CurtisTits CFSG.ComponentClassification.CatLeafProof CFSG.LieType.SeitzGeneration
  CFSG.TauCetiBridge TauCeti

set_option linter.unusedSectionVars false

theorem dvd_pow_four_add_one_of_orderOf_eq_eight {p : ℕ} (hp : p.Prime) {q : ℕ}
    (he : orderOf ((q : ℕ) : ZMod p) = 8) : p ∣ q ^ 4 + 1 := by
  have := Fact.mk hp
  set x : ZMod p := ((q : ℕ) : ZMod p) with hx
  have h8 : x ^ 8 = 1 := he ▸ pow_orderOf_eq_one x
  have h4 : x ^ 4 ≠ 1 := by
    intro h
    have h' := orderOf_dvd_of_pow_eq_one h
    rw [he] at h'
    norm_num at h'
  have hsq : x ^ 4 * x ^ 4 = 1 := by rw [← pow_add]; exact h8
  have hneg : x ^ 4 = -1 := (mul_self_eq_one_iff.1 hsq).resolve_left h4
  rw [← ZMod.natCast_eq_zero_iff]
  have h1 : ((q ^ 4 + 1 : ℕ) : ZMod p) = x ^ 4 + 1 := by push_cast; rfl
  rw [h1, hneg]
  exact neg_add_cancel _


theorem closure_centralizers_eq_top_E8_eight {K : Type} [Field K] [Finite K] {p : ℕ}
    [hpF : Fact p.Prime] (he : orderOf ((Nat.card K : ℕ) : ZMod p) = 8)
    (E₀ : Subgroup (adjointGroup .E8 K)) (hE₀p : ∀ x ∈ E₀, x ^ p = 1)
    (hE₀c : Nat.card E₀ = p ^ 2) :
    Subgroup.closure {k | ∃ x ∈ E₀, x ≠ 1 ∧ Commute k x} = ⊤ := by
  have hfam := exists_e8D8_family K
  obtain ⟨Ψ, hker, hrange⟩ := exists_psi_D8_E8_of_family hfam
  obtain ⟨ρ, hρ, hcomm, hψ⟩ := hfam
  have hp2 : p ≠ 2 := ne_two_of_orderOf_eq_eight hpF.out he
  have hpq : p ∣ Nat.card K ^ 4 + 1 := dvd_pow_four_add_one_of_orderOf_eq_eight hpF.out he
  obtain ⟨e, heA, heo, hec⟩ := exists_e1_E8_eight_of_family hp2 hpq ρ hρ hcomm hψ
  have hle : (⨆ k : Fin 7, e8D8Chain K k.castSucc) ≤ ⨆ k, e8D8Chain K k :=
    iSup_le fun k => le_iSup (e8D8Chain K) k.castSucc
  have heX : e ∈ ⨆ k, e8D8Chain K k := hle heA
  obtain ⟨g, hgX, hge⟩ :=
    exists_conj_plane_d8_of_family ⟨ρ, hρ, hcomm, hψ⟩ he heX heo E₀ hE₀p hE₀c
  have hE₁p : ∀ x ∈ E₀.map (MulAut.conj g).toMonoidHom, x ^ p = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hE₀p x hx, map_one]
  have hE₁c : Nat.card (E₀.map (MulAut.conj g).toMonoidHom) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hE₀c]
  have he1 : e ≠ 1 := by
    intro h
    rw [h, orderOf_one] at heo
    exact hpF.out.one_lt.ne heo
  apply AnisoF4.closure_centralizers_eq_top_of_map_conj g E₀
  apply eq_top_of_d8Chain_le_of_delta_le
  · exact iSup_d8Chain_le_closure_centralizers hpF.out he Ψ hker hrange _ hgX hE₁p hE₁c
  · intro y hy
    exact Subgroup.subset_closure ⟨e, hge, he1, (hec y hy).symm⟩


theorem seitzExcAnisotropicE8Class_eight : SeitzExcAnisotropicE8Class 8 := by
  intro d p hp _ _ _ E hE hcard hS
  obtain ⟨hin, -, ⟨-, q, hdq, -, hord⟩, -, -⟩ := hS
  obtain ⟨d₁, hv⟩ := d
  simp only at hdq
  subst hdq
  obtain ⟨K, _, _, hKq, -, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e8 q hv
  have : Fact p.Prime := ⟨hp⟩
  have he : orderOf ((Nat.card K : ℕ) : ZMod p) = 8 := by rw [hKq]; exact hord
  exact CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.planeGen_of_native_closure e
    center_adjointGroup_eq_bot (fun E₀ hE₀p hE₀c => closure_centralizers_eq_top_E8_eight he E₀
      hE₀p hE₀c) hE hcard hin

end CFSG.HardMathSupport.Lang.AnisoE8
