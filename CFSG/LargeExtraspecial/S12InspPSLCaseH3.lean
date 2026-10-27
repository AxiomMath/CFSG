module

public import CFSG.LargeExtraspecial.S12InspPSLCaseH2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module Submodule QuadraticMap CFSG.RankThree.OrthogonalInvolutions S12InspPSL

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

namespace PSLPair

variable {g : G} {t : S.O} (P : S.PSLPair g t)

theorem false_of_eq_add (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    (hn : 5 ≤ S.width) (ht : t ∈ S.Lbar g) (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2)
    (hS : S.S12Standing g t) (ha : S.cl (g * S.z * g⁻¹) = P.c + P.c') : False := by
  have htX : t ∈ S.Xbar12 g := subset_Xbar12 (mem_Ebar12_of_mem_Lbar ht htA)
  have hcard := psl_card_Lbar_le_two_mul (P.relIndex_le_two hS (by omega))
  have hge := S.card_Lbar_ge haQ hne
  have h16 : 2 ^ 4 ≤ 2 ^ (S.width - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨ℓ, ⟨hℓX, hℓ⟩, hℓ1, hℓt⟩ : ∃ ℓ ∈ S.Xbar12 g ⊓ S.Lbar g, ℓ ≠ 1 ∧ ℓ ≠ t := by
    by_contra hcon
    push Not at hcon
    have := psl_card_le_two_of_subset (K := S.Xbar12 g ⊓ S.Lbar g) (t := t) fun x hx => by
      by_cases h1 : x = 1
      · exact Or.inl h1
      · exact Or.inr (hcon x hx h1)
    omega
  obtain ⟨e, he, he1⟩ := P.exists_polar_c'
  obtain ⟨⟨h₁, hh₁, hℓh₁⟩, hspan⟩ :=
    P.exists_mixed haQ hne (by omega) htA htX ha hℓ hℓX hℓ1 hℓt he he1
  have hℓc' := (fix_of_mem_Lbar haQ ha hℓ hℓX).2
  set h := (ℓ : S.Qt ≃ₗ[ZMod 2] S.Qt) e - e with hhdef
  have hhH : h ∈ P.H := by
    refine ⟨P.W.sub_mem (P.apply_mem hℓX he) he, ?_⟩
    change polar S.q P.c' h = 0
    rw [hhdef, polar_sub_right, ← hℓc', psl_polar_apply_apply, hℓc', sub_self]
  have hc'e : polar S.q P.c' e = 1 := by rw [polar_comm]; exact he1
  have hc'c : polar S.q P.c' P.c = 0 := by rw [polar_comm]; exact P.polar_c_c'
  set T := span (ZMod 2) ({P.c, h, h₁, e} : Set S.Qt) with hTdef
  have hcT : P.c ∈ T := subset_span (by simp)
  have hhT : h ∈ T := subset_span (by simp)
  have hh₁T : h₁ ∈ T := subset_span (by simp)
  have heT : e ∈ T := subset_span (by simp)
  obtain ⟨u, huW, huT⟩ : ∃ u ∈ P.W, u ∉ T := by
    by_contra hcon
    push Not at hcon
    have := finrank_mono (show P.W ≤ T from hcon)
    have h4 : finrank (ZMod 2) T ≤ 4 := S.s12_finrank_span_le_four P.c h h₁ e
    rw [P.dim] at this
    omega
  set u₂ := u + polar S.q u P.c' • e with hu₂def
  have hu₂W : u₂ ∈ P.W := P.W.add_mem huW (P.W.smul_mem _ he)
  have hu₂c' : polar S.q P.c' u₂ = 0 := by
    rw [hu₂def, polar_add_right, polar_smul_right, hc'e, polar_comm S.q P.c' u, smul_eq_mul,
      mul_one, CharTwo.add_self_eq_zero]
  have hu₂T : u₂ ∉ T := fun h2 => huT (by
    have : u = u₂ - polar S.q u P.c' • e := by rw [hu₂def, add_sub_cancel_right]
    rw [this]
    exact T.sub_mem h2 (T.smul_mem _ heT))
  obtain ⟨ψ₁, hψ₁, hψ₁1⟩ := exists_functional hu₂T
  have hT₂ : h ∉ span (ZMod 2) ({P.c, e, u₂} : Set S.Qt) := by
    intro hmem
    obtain ⟨a, z, hz, hza⟩ := Submodule.mem_span_insert.mp hmem
    obtain ⟨b, d, rfl⟩ := mem_span_pair.mp hz
    have hb : b = 0 := by
      have h0 : polar S.q P.c' h = 0 := hhH.2
      rw [hza, polar_add_right, polar_add_right, polar_smul_right, polar_smul_right,
        polar_smul_right, hc'c, hc'e, hu₂c'] at h0
      simpa using h0
    subst hb
    rcases zmod2_cases d with rfl | rfl
    · apply hspan
      rw [hza, zero_smul, zero_smul, add_zero, add_zero]
      exact smul_mem _ _ (mem_span_singleton_self _)
    · apply hu₂T
      have : u₂ = h - a • P.c := by
        rw [hza, zero_smul, zero_add, one_smul, add_sub_cancel_left]
      rw [this]
      exact T.sub_mem hhT (T.smul_mem _ hcT)
  obtain ⟨ψ₂, hψ₂, hψ₂1⟩ := exists_functional hT₂
  have hψ₂c : ψ₂ P.c = 0 := hψ₂ _ (subset_span (by simp))
  have hψ₂e : ψ₂ e = 0 := hψ₂ _ (subset_span (by simp))
  have hψ₂u : ψ₂ u₂ = 0 := hψ₂ _ (subset_span (by simp))
  obtain ⟨x₁, hx₁, hx₁w⟩ := P.lift ψ₁ h₁ hh₁.1 (hψ₁ _ hh₁T)
  obtain ⟨x₂, hx₂, hx₂w⟩ := P.lift ψ₂ u₂ hu₂W hψ₂u
  set f := x₁ * x₂ with hfdef
  have hfX : f ∈ S.Xbar12 g := (S.Xbar12 g).mul_mem hx₁ hx₂
  have hfw : ∀ w ∈ P.W, (f : S.Qt ≃ₗ[ZMod 2] S.Qt) w =
      (x₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((x₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) w) := fun w _ => by
    rw [hfdef, Subgroup.coe_mul, LinearEquiv.mul_apply]
  have hfe : (f : S.Qt ≃ₗ[ZMod 2] S.Qt) e = e := by
    rw [hfw e he, hx₂w e he, hψ₂e, zero_smul, add_zero, hx₁w e he, hψ₁ e heT, zero_smul,
      add_zero]
  have hfc : (f : S.Qt ≃ₗ[ZMod 2] S.Qt) P.c = P.c := by
    rw [hfw P.c P.hc, hx₂w P.c P.hc, hψ₂c, zero_smul, add_zero, hx₁w P.c P.hc, hψ₁ _ hcT,
      zero_smul, add_zero]
  have hh₁c' : polar S.q h₁ P.c' = 0 := by rw [polar_comm]; exact hh₁.2
  have hu₂c'' : polar S.q u₂ P.c' = 0 := by rw [polar_comm]; exact hu₂c'
  have hfc' : (f : S.Qt ≃ₗ[ZMod 2] S.Qt) P.c' = P.c' := by
    refine P.apply_c'_eq hfX fun w hw => ?_
    rw [hfw w hw, hx₂w w hw, hx₁w _ (P.W.add_mem hw (P.W.smul_mem _ hu₂W)), polar_add_left,
      polar_add_left, polar_smul_left, polar_smul_left, hh₁c', hu₂c'', smul_zero, smul_zero,
      add_zero, add_zero]
  have hv : h + u₂ ∈ P.W := P.W.add_mem hhH.1 hu₂W
  have hψ₂v : ψ₂ (h + u₂) = 1 := by rw [map_add, hψ₂1, hψ₂u, add_zero]
  have hψ₁v : ψ₁ (h + u₂) = 1 := by rw [map_add, hψ₁ h hhT, hψ₁1, zero_add]
  have hx₂v : (x₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) (h + u₂) = h := by
    rw [hx₂w _ hv, hψ₂v, one_smul, add_assoc, self_add_self, add_zero]
  have hx₂h : (x₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) h = h + u₂ := by
    rw [hx₂w h hhH.1, hψ₂1, one_smul]
  have hfv : (f : S.Qt ≃ₗ[ZMod 2] S.Qt) (h + u₂) = h := by
    rw [hfw _ hv, hx₂v, hx₁w h hhH.1, hψ₁ h hhT, zero_smul, add_zero]
  have hfh : (f : S.Qt ≃ₗ[ZMod 2] S.Qt) h = h + u₂ + h₁ := by
    rw [hfw h hhH.1, hx₂h, hx₁w _ hv, hψ₁v, one_smul]
  have hfN : f ∈ normalizer (S.Lbar g : Set S.O) := by
    rw [mem_normalizer_Lbar_iff_fix haQ hne (by omega) (Xbar12_le_Mbar hfX), ha, map_add, hfc,
      hfc']
  have hℓ' : f * ℓ * f⁻¹ ∈ S.Lbar g := (mem_normalizer_iff.mp hfN ℓ).mp hℓ
  have hcomm : ℓ * (f * ℓ * f⁻¹) = (f * ℓ * f⁻¹) * ℓ :=
    congrArg Subtype.val ((S.isElementaryAbelian_Lbar haQ).is_comm.comm ⟨ℓ, hℓ⟩ ⟨_, hℓ'⟩)
  have hev := congrArg (fun y : S.O => (y : S.Qt ≃ₗ[ZMod 2] S.Qt) e) hcomm
  simp only [Subgroup.coe_mul, LinearEquiv.mul_apply] at hev
  have hfie : ((f⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) e = e := by
    conv_lhs => rw [← hfe]
    exact psl_inv_apply_apply f e
  have hfih : ((f⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) h = h + u₂ := by
    conv_lhs => rw [← hfv]
    exact psl_inv_apply_apply f _
  have hℓe : (ℓ : S.Qt ≃ₗ[ZMod 2] S.Qt) e = h + e := by rw [hhdef, sub_add_cancel]
  have hδ := P.comm_H_le haQ hne (by omega) ha hℓ hℓX _ (P.H.add_mem hhH ⟨hu₂W, hu₂c'⟩)
  set δ := (ℓ : S.Qt ≃ₗ[ZMod 2] S.Qt) (h + u₂) - (h + u₂) with hδdef
  have hℓv : (ℓ : S.Qt ≃ₗ[ZMod 2] S.Qt) (h + u₂) = h + u₂ + δ := by
    rw [hδdef, add_sub_cancel]
  have hfδ : (f : S.Qt ≃ₗ[ZMod 2] S.Qt) δ = δ := by
    rw [mem_span_singleton_iff] at hδ
    rcases hδ with h0 | h0 <;> rw [h0]
    · exact map_zero _
    · exact hfc
  rw [hfie, hℓe, map_add, hfh, hfe] at hev
  have hL : (ℓ : S.Qt ≃ₗ[ZMod 2] S.Qt) (h + u₂ + h₁ + e) = h + u₂ + δ + (h₁ + P.c) + (h + e) := by
    rw [map_add, map_add, hℓv, hℓh₁, hℓe]
  have hR : (f : S.Qt ≃ₗ[ZMod 2] S.Qt) ((ℓ : S.Qt ≃ₗ[ZMod 2] S.Qt)
      (((f⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (h + e))) = h + δ + (h + u₂ + h₁ + e) := by
    rw [map_add, hfih, hfie, map_add, hℓv, hℓe, map_add, map_add, hfv, hfδ, map_add, hfh, hfe]
  rw [hL, hR] at hev
  apply P.c_ne
  have key : h + u₂ + δ + (h₁ + P.c) + (h + e) = (h + δ + (h + u₂ + h₁ + e)) + P.c := by abel
  rw [key] at hev
  exact add_eq_left.mp hev

end PSLPair

end Setting

end CFSG.LargeExtraspecial
