module

public import CFSG.LargeExtraspecial.S13EightD
public import CFSG.LargeExtraspecial.S13EightC

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S13

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.S10

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {K : Subgroup S.O}

namespace Hyp13

theorem exists_config (hCE : CentralExtInput.{u}) (Y : Hyp13 S g K) {σ : S.O}
    (hσ : σ ∈ S.Lbar g) (hσE : σ ∉ Ebar S g K)
    (hpts : ∀ v ∈ Vt S g σ, v ≠ 0 → ∃ m : S.M, v = S.cl ((m : G) * g * S.z * ((m : G) * g)⁻¹) ∧
      σ ∈ S.Lbar ((m : G) * g) ∧ Vt S g σ ≤ S.clSub (S.QG ⊓ S.Qa ((m : G) * g)))
    (hVP : Vt S g σ ≤ S.clSub (S.QG ⊓ S.Qa g)) (h3 : finrank (ZMod 2) (Vt S g σ) = 3)
    {k : S.O} (hk : k ∈ K) (hk1 : k ≠ 1) {c : S.M}
    (hcU : S.cl ((c : G) * g * S.z * ((c : G) * g)⁻¹) ∉
      Vt S g σ ⊔ (Vt S g σ).map (k : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap)
    (ha : S.cl (g * S.z * g⁻¹) ∈ perp S (Fbar S ((c : G) * g) K)) :
    ∃ pE pU pX pF : S.M,
      S.cl ((pE : G) * g * S.z * ((pE : G) * g)⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa g) ∧
      S.cl ((pX : G) * g * S.z * ((pX : G) * g)⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa g) ∧
      S.cl ((pX : G) * g * S.z * ((pX : G) * g)⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa ((pE : G) * g)) ∧
      S.cl ((pX : G) * g * S.z * ((pX : G) * g)⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa ((pU : G) * g)) ∧
      S.cl ((pF : G) * g * S.z * ((pF : G) * g)⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa g) ∧
      S.cl ((pF : G) * g * S.z * ((pF : G) * g)⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa ((pE : G) * g)) ∧
      S.cl ((pF : G) * g * S.z * ((pF : G) * g)⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa ((pU : G) * g)) ∧
      S.cl ((pX : G) * g * S.z * ((pX : G) * g)⁻¹) ∉ S.clSub (S.QG ⊓ S.Qa ((pF : G) * g)) ∧
      LinearIndependent (ZMod 2) ![S.cl (g * S.z * g⁻¹),
        S.cl ((pE : G) * g * S.z * ((pE : G) * g)⁻¹),
        S.cl ((pU : G) * g * S.z * ((pU : G) * g)⁻¹),
        S.cl ((pX : G) * g * S.z * ((pX : G) * g)⁻¹)] := by
  obtain ⟨me, mF, x, pU, ⟨heV, hea, hσe, hVe⟩, ⟨hfV, hσF, hVF⟩, ⟨hxV, hxP, hxe, hxF⟩,
    ⟨hua, huF, hue, hperpu, hneu⟩⟩ := Y.exists_pre_config hCE hσ hσE hpts hVP h3 hk hk1 hcU ha
  set V := Vt S g σ with hV
  set a := S.cl (g * S.z * g⁻¹) with hadef
  set pe := S.cl ((me : G) * g * S.z * ((me : G) * g)⁻¹) with hpe
  set px := S.cl ((x : G) * g * S.z * ((x : G) * g)⁻¹) with hpx
  set pu := S.cl ((pU : G) * g * S.z * ((pU : G) * g)⁻¹) with hpu
  have ha0 : a ≠ 0 := cl_conj_z_ne_zero S Y.haQ Y.hne
  have hpe0 : pe ≠ 0 := pt_ne_zero Y.H me
  have hpu0 : pu ≠ 0 := pt_ne_zero Y.H pU
  have hape : a ≠ pe := fun h => hea (h ▸ Submodule.mem_span_singleton_self _)
  have haV : a ∈ V := cl_a_mem_Vt hσ
  have hax : a ∈ S.clSub (S.QG ⊓ S.Qa ((x : G) * g)) := mem_clSub_base_symm Y.H hxP
  have hex : pe ∈ S.clSub (S.QG ⊓ S.Qa ((x : G) * g)) := cl_mem_clSub_symm Y.H hxe
  have hau : a ∈ S.clSub (S.QG ⊓ S.Qa ((pU : G) * g)) := mem_clSub_base_symm Y.H hua
  have hVlink : IsLinked S g V := fun v hv hv0 => by
    obtain ⟨m, h1, -, h2⟩ := hpts v hv hv0
    exact ⟨m, h1, h2⟩
  set U₀ := Submodule.span (ZMod 2) ({a, pe} : Set S.Qt) with hU₀
  have hU₀V : U₀ ≤ V :=
    Submodule.span_le.mpr (Set.insert_subset haV (Set.singleton_subset_iff.mpr heV))
  have hU₀x : U₀ ≤ S.clSub (S.QG ⊓ S.Qa ((x : G) * g)) :=
    Submodule.span_le.mpr (Set.insert_subset hax (Set.singleton_subset_iff.mpr hex))
  set V₁ := U₀ ⊔ (ZMod 2) ∙ px with hV₁
  have hV₁link : IsLinked S g V₁ := (hVlink.mono hU₀V).sup_pt Y.H hU₀x
  have haV₁ : a ∈ V₁ := Submodule.mem_sup_left (Submodule.subset_span (Set.mem_insert _ _))
  have hpeV₁ : pe ∈ V₁ :=
    Submodule.mem_sup_left (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))
  have hpxV₁ : px ∈ V₁ := Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  have hV₁a : V₁ ≤ S.clSub (S.QG ⊓ S.Qa g) :=
    sup_le (hU₀V.trans hVP) ((Submodule.span_singleton_le_iff_mem _ _).mpr hxP)
  have hV₁e : V₁ ≤ S.clSub (S.QG ⊓ S.Qa ((me : G) * g)) :=
    sup_le (hU₀V.trans hVe) ((Submodule.span_singleton_le_iff_mem _ _).mpr hxe)
  have hV₁3 : 3 ≤ finrank (ZMod 2) V₁ :=
    three_le_finrank_of_mem haV₁ hpeV₁ hpxV₁ ha0 hpe0 hape fun h => hxV (hU₀V h)
  have Yu : Hyp13 S ((pU : G) * g) K := Y.mul rfl
  set Fu := Fbar S ((pU : G) * g) K with hFu
  have huFu : pu ∈ Fu := cl_mem_Fbar Yu.H
  have hFuK : ∀ k' ∈ K, ∀ v ∈ Fu, (k' : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ Fu :=
    fun k' hk' v hv => apply_mem_Fbar_of_mem_K hk' hv
  have hFperp := Y.Fbar_le_perp hFuK hperpu
  have hperp : ∀ u ∈ Fbar S g K, ∀ v ∈ Fu, polar S.q u v = 0 := fun u hu v hv => by
    rw [QuadraticMap.polar_comm]
    exact hFperp hu v hv
  have h13 := timmesfeld_13_3 hCE Y (rfl : (pU : G) * g = (pU : G) * g) hperp hneu
  have hline : ∀ w ∈ Fu, w ∈ S.clSub (S.QG ⊓ S.Qa g) → w = 0 ∨ w = pu := fun w hw hwa =>
    eq_of_mem_finrank_one h13 (Submodule.mem_inf.mpr ⟨huFu, hua⟩) hpu0
      (Submodule.mem_inf.mpr ⟨hw, hwa⟩)
  have hV₁perp : 2 ≤ finrank (ZMod 2) (V₁ ⊓ perp S Fu : Submodule (ZMod 2) S.Qt) := by
    set kp := (k : S.Qt ≃ₗ[ZMod 2] S.Qt) pu with hkp
    have hle : V₁ ⊓ perp S ((ZMod 2) ∙ kp) ≤ V₁ ⊓ perp S Fu := by
      intro v hv
      obtain ⟨hvV, hvk⟩ := Submodule.mem_inf.mp hv
      refine Submodule.mem_inf.mpr ⟨hvV, ?_⟩
      rw [hFu, ← Yu.span_pair_eq huFu hpu0 hk hk1]
      exact mem_perp_of_span_pair (polar_eq_zero_of_mem_clSub Y.hne hua (hV₁a hvV))
        (hvk kp (Submodule.mem_span_singleton_self _))
    have h1 := finrank_inf_perp_ge V₁ ((ZMod 2) ∙ kp)
    have h2 := Submodule.finrank_mono hle
    have h3' : finrank (ZMod 2) ((ZMod 2) ∙ kp) ≤ 1 := by
      have := finrank_span_le_card (R := ZMod 2) ({kp} : Set S.Qt)
      simpa using this
    omega
  obtain ⟨β, hβW, hβa⟩ : ∃ v ∈ V₁ ⊓ perp S Fu, v ∉ (ZMod 2) ∙ a := by
    by_contra hcon
    push Not at hcon
    have h1 := Submodule.finrank_mono
      (show V₁ ⊓ perp S Fu ≤ (ZMod 2) ∙ a from fun v hv => hcon v hv)
    rw [finrank_span_singleton ha0] at h1
    omega
  have hβ0 : β ≠ 0 := fun h => hβa (h ▸ zero_mem _)
  obtain ⟨hβV₁, hβperp⟩ := Submodule.mem_inf.mp hβW
  have hfa : a ≠ S.cl ((mF : G) * g * S.z * ((mF : G) * g)⁻¹) := by
    intro h
    apply hxF
    rw [clSub_eq_of_pt_eq_base Y.H h.symm]
    exact hxP
  have hσu : (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) pu = pu := fix_of_mem_Lbar_inf hfa hσ hσF hua huF
  have hβD : β ∉ Fbar S g K ⊔ Fu := by
    intro h
    obtain ⟨φ, hφ, ψ, hψ, hsum⟩ := Submodule.mem_sup.mp h
    have hψeq : ψ = β - φ := by rw [← hsum]; abel
    have hψa : ψ ∈ S.clSub (S.QG ⊓ S.Qa g) := by
      rw [hψeq]
      exact sub_mem (hV₁a hβV₁) (Y.Fbar_le_clSub hφ)
    have hσψ : (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) ψ = ψ := by
      rcases hline ψ hψ hψa with h0 | h0
      · rw [h0, map_zero]
      · rw [h0, hσu]
    have hσβ := S.sub_mem_span_of_mem_clSub hσe (hV₁e hβV₁)
    have e1 : (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) β - β = (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) φ - φ := by
      rw [← hsum, map_add, hσψ]
      abel
    rw [e1] at hσβ
    have hφF : (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) φ - φ ∈ Fbar S g K :=
      sub_mem (apply_mem_Fbar_of_mem_Lbar Y.H hσ hφ) hφ
    have hσφ : (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) φ = φ := by
      rcases mem_span_cl_iff.mp hσβ with h1 | h1
      · exact sub_eq_zero.mp h1
      · exfalso
        have h1' : (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) φ - φ = pe := h1
        exact hea (Y.Fbar_inf_Vt_le hσ hσE hpts (Submodule.mem_inf.mpr ⟨h1' ▸ hφF, heV⟩))
    have hφa := Y.mem_span_of_fix_Fbar hσ hσE hφ hσφ
    rcases hline ψ hψ hψa with h0 | h0
    · apply hβa
      rw [← hsum, h0, add_zero]
      exact hφa
    · apply hue
      have e2 : pu = β - φ := by rw [← hsum, h0]; abel
      rw [e2]
      exact sub_mem (hV₁e hβV₁)
        ((Submodule.span_singleton_le_iff_mem _ _).mpr (hVe haV) hφa)
  obtain ⟨mβ, hβeq, hV₁β⟩ := hV₁link β hβV₁ hβ0
  subst hβeq
  have Yβ : Hyp13 S ((mβ : G) * g) K := Y.mul rfl
  have hFβperp := Yβ.Fbar_le_perp hFuK hβperp
  have hperpe : ∀ u ∈ Fbar S ((mβ : G) * g) K, ∀ v ∈ Fu, polar S.q u v = 0 :=
    fun u hu v hv => by
      rw [QuadraticMap.polar_comm]
      exact hFβperp hu v hv
  have hnee : Fu ≠ Fbar S ((mβ : G) * g) K := by
    intro h
    have h1 : S.cl ((mβ : G) * g * S.z * ((mβ : G) * g)⁻¹) ∈ Fu := h ▸ cl_mem_Fbar Yβ.H
    rcases hline _ h1 (hV₁a hβV₁) with h2 | h2
    · exact hβ0 h2
    · exact hue (h2 ▸ hV₁e hβV₁)
  have hub := Y.mem_clSub_of_not_mem_Dbar hCE (c := pU) hperp hneu huFu hua hpu0
    (hV₁a hβV₁) hβD hperpe hnee
  have hβu := cl_mem_clSub_symm Y.H hub
  have hβU₀ : S.cl ((mβ : G) * g * S.z * ((mβ : G) * g)⁻¹) ∉ U₀ := by
    intro h
    rcases mem_span_pair_cases h with h1 | h1 | h1 | h1
    · exact hβ0 h1
    · exact hβa (by rw [h1]; exact Submodule.mem_span_singleton_self _)
    · apply hue
      apply cl_mem_clSub_symm Y.H
      show pe ∈ S.clSub (S.QG ⊓ S.Qa ((pU : G) * g))
      rw [← h1]
      exact hβu
    · apply hue
      apply cl_mem_clSub_symm Y.H
      show pe ∈ S.clSub (S.QG ⊓ S.Qa ((pU : G) * g))
      have e2 : pe = S.cl ((mβ : G) * g * S.z * ((mβ : G) * g)⁻¹) - a := by rw [h1]; abel
      rw [e2]
      exact sub_mem hβu hau
  have hβF : S.cl ((mβ : G) * g * S.z * ((mβ : G) * g)⁻¹) ∉
      S.clSub (S.QG ⊓ S.Qa ((mF : G) * g)) := by
    intro h
    obtain ⟨w, hw, y, hy, hwy⟩ := Submodule.mem_sup.mp hβV₁
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hy
    have h01 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
    rcases h01 t with rfl | rfl
    · rw [zero_smul, add_zero] at hwy
      exact hβU₀ (hwy ▸ hw)
    · rw [one_smul] at hwy
      apply hxF
      have e2 : px = S.cl ((mβ : G) * g * S.z * ((mβ : G) * g)⁻¹) - w := by rw [← hwy]; abel
      rw [e2]
      exact sub_mem h (hVF (hU₀V hw))
  have hU₀e : U₀ ≤ S.clSub (S.QG ⊓ S.Qa ((me : G) * g)) := hU₀V.trans hVe
  have hli : LinearIndependent (ZMod 2) ![a, pe, pu,
      S.cl ((mβ : G) * g * S.z * ((mβ : G) * g)⁻¹)] := by
    refine linearIndependent_four ha0 hea (fun h => hue (hU₀e h)) fun h => hβF ?_
    refine (Submodule.span_le.mpr ?_) h
    intro v hv
    rcases hv with rfl | rfl | rfl
    · exact hVF haV
    · exact hVF heV
    · exact huF
  exact ⟨me, pU, mβ, mF, hVP heV, hV₁a hβV₁, hV₁e hβV₁, hβu, hVP hfV, hVe hfV,
    cl_mem_clSub_symm Y.H huF, hβF, hli⟩

end Hyp13

end CFSG.LargeExtraspecial.S13
