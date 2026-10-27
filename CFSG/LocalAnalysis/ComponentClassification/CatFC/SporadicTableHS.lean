module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.SporadicTableBasic
public import CFSG.Sporadic.SmallOddCore.HSLocal
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.SporadicTableDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19HSAutOuter
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentSporHS
public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineL34

public section

set_option linter.unusedSectionVars false

namespace CFSG.ComponentClassification.CatFC

open CFSG Subgroup CFSG.Blueprint
open CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Th.Native
open CFSG.QuasithinUnique.Id2519 (fixSubgroup fixSubgroup_eq_map)
open CFSG.QuasithinUnique.Id2519.SporHS (fix_data fixEquiv hsRows_cases)
open CFSG.QuasithinUnique.Id2519.HSAut
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

section HSRow


theorem hs_fixedSubgroup_rows_outer {S : Type} [Group S] (e : S ≃* NativeSporadic.HS)
    {σ : MulAut S} (hσ : orderOf σ = 2) (hout : σ ∉ (MulAut.conj : S →* MulAut S).range) :
    ∃ r ∈ hsRows, r.outer = true ∧ Nonempty (fixedSubgroup σ ≃*
      ↥(hsP ⊓ centralizer ({tp 3850 r.rep} : Set (Equiv.Perm (Fin 3850))))) := by
  set θ : S ≃* hsP := e.trans hsPermEquiv
  set α : MulAut hsP := MulAut.congr θ σ
  have hσ2 : σ * σ = 1 := by rw [← sq, ← hσ, pow_orderOf_eq_one]
  have hα2 : α * α = 1 := by
    rw [show α * α = MulAut.congr θ (σ * σ) from (map_mul (MulAut.congr θ) σ σ).symm, hσ2,
      map_one]
  have hα1 : α ≠ 1 := by
    intro h
    have : σ = 1 := (MulAut.congr θ).injective (by rw [map_one]; exact h)
    rw [this, orderOf_one] at hσ
    exact absurd hσ (by norm_num)
  obtain ⟨r, hr, g, hg, x, hxform, hxg, h3⟩ := fix_data α hα2 hα1
  obtain ⟨-, -, -, hrows, -, -, -, -⟩ := hs_involution_centralizers
  have hxP : (x : Equiv.Perm (Fin 3850)) ∉ hsP := fun hx =>
    not_forall_congr_eq_conj θ hout ⟨x, hx⟩ fun p => Subtype.ext (hxform p)
  have hrep : tp 3850 r.rep ∉ hsP := fun h => hxP (by
    rw [hxg]
    exact hsP.mul_mem (hsP.mul_mem hg h) (hsP.inv_mem hg))
  have hmap : fixSubgroup α = (fixSubgroup σ).map θ.toMonoidHom :=
    fixSubgroup_eq_map θ σ α fun y => by simp [α, MulAut.congr_apply]
  have hfix : fixedSubgroup σ = fixSubgroup σ := by
    ext y
    exact Iff.rfl
  refine ⟨r, hr, ((hrows r hr).2.2.1).2 hrep, ⟨?_⟩⟩
  exact ((MulEquiv.subgroupCongr hfix).trans
    (((fixSubgroup σ).equivMapOfInjective θ.toMonoidHom θ.injective).trans
      (MulEquiv.subgroupCongr hmap.symm))).trans (fixEquiv h3)

theorem hs_outer_card_quotient {S : Type} [Group S] [Finite S] (e : S ≃* NativeSporadic.HS)
    {σ : MulAut S} (hσ : orderOf σ = 2) (hout : σ ∉ (MulAut.conj : S →* MulAut S).range)
    {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D) :
    Nat.card (D ⧸ center D) = 20160 ∨ Nat.card (D ⧸ center D) ∣ 1920 := by
  obtain ⟨r, hr, hrout, ⟨φ⟩⟩ := hs_fixedSubgroup_rows_outer e hσ hout
  obtain ⟨-, -, -, hrows, -, -, hmap, -⟩ := hs_involution_centralizers
  have hcardC := (hrows r hr).2.2.2.2.1
  have hdvd := SeitzReduction.SporadicRefine.card_quotient_center_dvd_card_fixedSubgroup D
  rw [Nat.card_congr φ.toEquiv, hcardC] at hdvd
  have hmem : (r.outer, r.classSize, r.centOrder) ∈
      [(false, 5775, 7680), (false, 15400, 2880), (true, 1100, 40320), (true, 23100, 1920)] := by
    rw [← hmap]
    exact List.mem_map_of_mem
      (f := fun r : ClassRow => (r.outer, r.classSize, r.centOrder)) hr
  have hc : r.centOrder = 40320 ∨ r.centOrder = 1920 := by
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hmem
    rcases hmem with ⟨h1, -, -⟩ | ⟨h1, -, -⟩ | ⟨-, -, h3⟩ | ⟨-, -, h3⟩
    · exact absurd (h1.symm.trans hrout) (by decide)
    · exact absurd (h1.symm.trans hrout) (by decide)
    · exact Or.inl h3
    · exact Or.inr h3
  rcases hsRows_cases hr with h | ⟨-, -, h, -⟩ | ⟨hrep, h⟩ | h
  · omega
  · omega
  ·
    have hC : hsP ⊓ centralizer ({tp 3850 r.rep} : Set (Equiv.Perm (Fin 3850))) = outerC := by
      rw [hrep]
      rfl
    let ψ : fixedSubgroup σ ≃* outerC := φ.trans (MulEquiv.subgroupCongr hC)
    set B : Subgroup outerC := D.map ψ.toMonoidHom with hBdef
    have hB : IsComponent B := LocalCores.isComponent_map_mulEquiv ψ hD
    have hcD : Nat.card (D ⧸ center D) = Nat.card (B ⧸ center B) :=
      SeitzReduction.TwistedE6Pilot.card_quotient_center_eq_of_mulEquiv
        (D.equivMapOfInjective ψ.toMonoidHom ψ.injective)
    left
    rw [hcD]
    have hBperf : ⁅B, B⁆ = B := Subgroup.isPerfect_iff.mp hB.1.1
    have hBle : B ≤ commutator ↥outerC := by
      rw [← hBperf, _root_.commutator_def]
      exact Subgroup.commutator_mono le_top le_top
    have hE : IsSimpleGroup ↥(commutator ↥outerC) := commutator_simple'
    have hnt : Nontrivial B := LocalCores.isQuasisimple_nontrivial hB.1
    have hsub := hB.2.subgroupOf (K := commutator ↥outerC)
    rcases hsub.eq_bot_or_top_of_isSimpleGroup hE with h0 | h1
    · exfalso
      have hB1 : B = ⊥ := by
        rw [Subgroup.subgroupOf_eq_bot, disjoint_iff, inf_eq_left.2 hBle] at h0
        exact h0
      rw [hB1] at hnt
      exact (not_nontrivial_iff_subsingleton.2 inferInstance) hnt
    · have hBeq : B = commutator ↥outerC := le_antisymm hBle (Subgroup.subgroupOf_eq_top.1 h1)
      rw [hBeq, card_quotient_center_of_simple
        (nonabelian_of_simple_of_card_ne_prime (by rw [card_commutator']; norm_num)),
        card_commutator']
  · right
    rw [h] at hdvd
    exact hdvd

theorem sporadic_rows_hs {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.Carrier .HS)
    {σ : MulAut S} (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)}
    (hD : IsComponent D) :
    (σ ∈ (MulAut.conj : S →* MulAut S).range →
        SporadicInnerRow .HS (Nat.card (D ⧸ center D))) ∧
      (σ ∉ (MulAut.conj : S →* MulAut S).range →
        SporadicOuterRow .HS (Nat.card (D ⧸ center D))) := by
  refine ⟨fun hin => inner_row_of_centralizer hS hna hσ hD hin
      (P := fun c => c = 360) (fun u hu B hB => ?_), fun hout => ?_⟩
  · obtain ⟨hs, hna', hc⟩ := cti_hs_involution_local_components_simple_order_360 ⟨e⟩ hu
      (isComponentOf_map_centralizer hB)
    have : IsSimpleGroup ↥(B.map (centralizer ({u} : Set S)).subtype) := hs
    rw [← card_quotient_center_map_centralizer B, card_quotient_center_of_simple hna', hc]
  · exact hs_outer_card_quotient e hσ hout hD

end HSRow

end CFSG.ComponentClassification.CatFC
