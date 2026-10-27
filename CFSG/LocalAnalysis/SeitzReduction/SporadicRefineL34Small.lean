module

public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineL34
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporMathieu
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporAut
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporLocal
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19TabJ2
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporRu
public import CFSG.Sporadic.Schreier.SteinbergBSLyOuterTrivial

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.SporadicRefine

open CFSG Subgroup CFSG.Blueprint
open CFSG.Sporadic.Schreier
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.RestrictedStd.Spor (CompsSatisfy transportAut
  transportAut_mul_self transportAut_not_mem_inner fixSubTransportEquiv mem_inner_of_mulEquiv
  compsSatisfy_centralizer_of_mulEquiv isoInvariant_not_three_dvd isoInvariant_card_dvd
  isoInvariant_card_quotient_center compsSatisfy_of_isQuasisimple)

theorem orderOf_eq_two_of_conj_of_simple {S : Type} [Group S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) {s : S} (hσ : orderOf (MulAut.conj s) = 2) :
    orderOf s = 2 := by
  have := hS
  rw [← orderOf_injective _
    (ComponentClassification.CatLeaf.mulAut_conj_injective_of_simple hna) s]
  exact hσ

theorem three_dvd_card_of_card_quotient_center {G : Type*} [Group G] {D : Subgroup G}
    (hcard : Nat.card (D ⧸ center D) = 20160) : 3 ∣ Nat.card D :=
  (show 3 ∣ 20160 by norm_num).trans (hcard ▸ card_quotient_dvd_card _)

theorem fixedSubgroup_eq_fixSub' {S : Type*} [Group S] (σ : MulAut S) :
    fixedSubgroup σ = fixSub σ := by
  ext x
  exact Iff.rfl

theorem transportAut_ne_one {G H : Type*} [Group G] [Group H] (e : G ≃* H) {σ : MulAut G}
    (hσ : orderOf σ = 2) : transportAut e σ ≠ 1 := by
  intro h
  have h1 : σ = 1 := by
    ext x
    have := congrArg (fun φ : MulAut H => e.symm (φ (e x))) h
    simpa [transportAut] using this
  rw [h1, orderOf_one] at hσ
  exact absurd hσ (by norm_num)

section M22


theorem m22_false_of_l34 {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.M22) {σ : MulAut S}
    (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D)
    (hcard : Nat.card (D ⧸ center D) = 20160) : False := by
  by_cases hin : σ ∈ (MulAut.conj : S →* MulAut S).range
  · obtain ⟨s, rfl⟩ := hin
    have hs := orderOf_eq_two_of_conj_of_simple hS hna hσ
    let φ := MulEquiv.subgroupCongr (fixedSubgroup_conj_eq_centralizerOf s)
    have h : Nat.card (D.map φ.toMonoidHom) ∣ 384 :=
      compsSatisfy_centralizer_of_mulEquiv NativeSporadic.M22 (isoInvariant_card_dvd 384)
        ComponentClassification.RestrictedStd.Spor.m22_centralizerIn_comps e s hs _
        (LocalCores.isComponent_map_mulEquiv φ hD)
    rw [card_map_of_injective φ.injective] at h
    have h2 : 20160 ∣ 384 := hcard ▸ (card_quotient_dvd_card _).trans h
    norm_num at h2
  · have hσ2 : σ * σ = 1 := by rw [← sq, ← hσ, pow_orderOf_eq_one]
    let φ := (MulEquiv.subgroupCongr (fixedSubgroup_eq_fixSub' σ)).trans
      (fixSubTransportEquiv e σ)
    have h : ¬ 3 ∣ Nat.card (D.map φ.toMonoidHom) :=
      ComponentClassification.RestrictedStd.Spor.m22_outer_comps (transportAut e σ)
        (transportAut_mul_self e hσ2) (transportAut_not_mem_inner e hin) _
        (LocalCores.isComponent_map_mulEquiv φ hD)
    rw [card_map_of_injective φ.injective] at h
    exact h (three_dvd_card_of_card_quotient_center hcard)

end M22

section M23


theorem m23_false_of_l34 {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.M23) {σ : MulAut S}
    (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D)
    (hcard : Nat.card (D ⧸ center D) = 20160) : False := by
  obtain ⟨s, rfl⟩ := mem_inner_of_mulEquiv e (fun β => by
    obtain ⟨h, hh⟩ := QuasithinUnique.Ch1.m23_all_inner β
    exact ⟨h, hh.symm⟩) σ
  have hs := orderOf_eq_two_of_conj_of_simple hS hna hσ
  let φ := MulEquiv.subgroupCongr (fixedSubgroup_conj_eq_centralizerOf s)
  have h : ¬ 3 ∣ Nat.card (D.map φ.toMonoidHom) :=
    compsSatisfy_centralizer_of_mulEquiv NativeSporadic.M23 isoInvariant_not_three_dvd
      ComponentClassification.RestrictedStd.Spor.m23_centralizerIn_comps e s hs _
      (LocalCores.isComponent_map_mulEquiv φ hD)
  rw [card_map_of_injective φ.injective] at h
  exact h (three_dvd_card_of_card_quotient_center hcard)

end M23

section M24


theorem m24_false_of_l34 {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.M24) {σ : MulAut S}
    (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D)
    (hcard : Nat.card (D ⧸ center D) = 20160) : False := by
  obtain ⟨s, rfl⟩ := mem_inner_of_mulEquiv e (fun β => by
    obtain ⟨h, hh⟩ := QuasithinUnique.Ch1.m24_all_inner β
    exact ⟨h, hh.symm⟩) σ
  have hs := orderOf_eq_two_of_conj_of_simple hS hna hσ
  let φ := MulEquiv.subgroupCongr (fixedSubgroup_conj_eq_centralizerOf s)
  have h : ¬ 3 ∣ Nat.card (D.map φ.toMonoidHom) :=
    compsSatisfy_centralizer_of_mulEquiv NativeSporadic.M24 isoInvariant_not_three_dvd
      ComponentClassification.RestrictedStd.Spor.m24_centralizerIn_comps e s hs _
      (LocalCores.isComponent_map_mulEquiv φ hD)
  rw [card_map_of_injective φ.injective] at h
  exact h (three_dvd_card_of_card_quotient_center hcard)

end M24

section J2


theorem j2_false_of_l34 {S : Type} [Group S] (e : S ≃* NativeSporadic.J2) {σ : MulAut S}
    (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)}
    (hcard : Nat.card (D ⧸ center D) = 20160) : False := by
  set θ := e.trans ComponentClassification.J2Cover.nativeEquivP
  have hσ2 : σ * σ = 1 := by rw [← sq, ← hσ, pow_orderOf_eq_one]
  have hc : Nat.card (fixedSubgroup σ) = Nat.card (fixSub (transportAut θ σ)) :=
    Nat.card_congr ((MulEquiv.subgroupCongr (fixedSubgroup_eq_fixSub' σ)).trans
      (fixSubTransportEquiv θ σ)).toEquiv
  have hdvd := card_quotient_center_dvd_card_fixedSubgroup D
  rw [hcard, hc] at hdvd
  rcases QuasithinUnique.Id2519.Tab.j2_fixSub_card (transportAut θ σ)
      (transportAut_mul_self θ hσ2) (transportAut_ne_one θ hσ) with h | h | h <;>
    rw [h] at hdvd <;> norm_num at hdvd

end J2

section Ru


theorem ru_false_of_l34 {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.Ru) {σ : MulAut S}
    (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D)
    (hcard : Nat.card (D ⧸ center D) = 20160) : False := by
  set θ := e.trans Sporadic.RuSchreier.ruEquivP
  obtain ⟨s, rfl⟩ := mem_inner_of_mulEquiv θ Sporadic.RuSchreier.mulAut_inner σ
  have hs := orderOf_eq_two_of_conj_of_simple hS hna hσ
  let φ := MulEquiv.subgroupCongr (fixedSubgroup_conj_eq_centralizerOf s)
  have h : ¬ 3 ∣ Nat.card (D.map φ.toMonoidHom) :=
    compsSatisfy_centralizer_of_mulEquiv Sporadic.RuSchreier.ruP isoInvariant_not_three_dvd
      ComponentClassification.RestrictedStd.Spor.ru_centralizerIn_comps θ s hs _
      (LocalCores.isComponent_map_mulEquiv φ hD)
  rw [card_map_of_injective φ.injective] at h
  exact h (three_dvd_card_of_card_quotient_center hcard)

end Ru

section Ly


theorem ly_false_of_l34 {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.Carrier .Ly) {σ : MulAut S}
    (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D)
    (hcard : Nat.card (D ⧸ center D) = 20160) : False := by
  have hall : ∀ β : MulAut (NativeSporadic.Carrier .Ly),
      ∃ h : NativeSporadic.Carrier .Ly, β = MulAut.conj h := by
    intro β
    have hβ : β ∈ ComponentClassification.OuterAutomorphisms.inner NativeSporadic.Ly := by
      rw [ComponentClassification.RestrictedStd.Spor.lyOuterTrivialInput]
      trivial
    obtain ⟨h, hh⟩ := hβ
    exact ⟨h, hh.symm⟩
  have hin : σ ∈ (MulAut.conj : S →* MulAut S).range := mem_inner_of_mulEquiv e hall σ
  obtain ⟨s, rfl⟩ := hin
  have hs := orderOf_eq_two_of_conj_of_simple hS hna hσ
  obtain ⟨hq, -, ⟨eA⟩⟩ := Sporadic.LySchreier.involution_centralizers_quasisimple ⟨e⟩ s hs
  have hcardC : Nat.card (centralizer ({s} : Set S) ⧸ center (centralizer ({s} : Set S))) =
      19958400 := by
    rw [Nat.card_congr eA.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin]
    norm_num [Nat.factorial]
  let φ := MulEquiv.subgroupCongr (fixedSubgroup_conj_eq_centralizerOf s)
  have h : Nat.card ((D.map φ.toMonoidHom) ⧸ center (D.map φ.toMonoidHom)) = 19958400 :=
    compsSatisfy_of_isQuasisimple hq (isoInvariant_card_quotient_center {19958400}) hcardC _
      (LocalCores.isComponent_map_mulEquiv φ hD)
  obtain ⟨ψ⟩ := nonempty_quotient_center_map_equiv φ D
  rw [← Nat.card_congr ψ.toEquiv, hcard] at h
  norm_num at h

end Ly

end CFSG.SeitzReduction.SporadicRefine
