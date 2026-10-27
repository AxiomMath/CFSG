module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KBModel
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KBFix
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KBCore

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.ComponentClassification.PSL3Four

theorem unitary_E (hexp : ∀ x ∈ R, x ^ 27 = 1 → x ^ 3 = 1)
    {Y : Type} [Group Y] {α : MulAut Y} (χ : Y ≃* ↥S)
    (hχ : MulAut.congr χ α = Cls3.conjIso (rrR 3)) :
    ∃ E : Subgroup Y, E ≤ fixSub α ∧ IsElementaryAbelian 3 ↥E ∧ Nat.card E = 9 ∧
      ∀ c ∈ fixSub α, c ∈ normalizer (E : Set Y) := by
  have hmap := map_fixSub_r₄ χ hχ
  have hle : C₄ ≤ S := fun d hd => (Subgroup.mem_inf.1 hd).2
  let e : ↥(fixSub α) ≃* ↥C₄ :=
    ((χ.subgroupMap (fixSub α)).trans (MulEquiv.subgroupCongr hmap)).trans
      (Subgroup.subgroupOfEquivOfLe hle)
  obtain ⟨E', hEn, hE9, hEea⟩ := exists_normal_E hexp e
  have hinj := Subgroup.subtype_injective (fixSub α)
  have hsub : (E'.map (fixSub α).subtype).subgroupOf (fixSub α) = E' :=
    Subgroup.comap_map_eq_self_of_injective hinj E'
  refine ⟨E'.map (fixSub α).subtype, Subgroup.map_subtype_le E', ?_, ?_, ?_⟩
  · exact Transport.isElementaryAbelian_of_mulEquiv (E'.equivMapOfInjective _ hinj) hEea
  · rw [Subgroup.card_map_of_injective hinj]; exact hE9
  · intro c hc
    have hN : ((E'.map (fixSub α).subtype).subgroupOf (fixSub α)).Normal := by
      rw [hsub]; exact hEn
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le E')).1 hN hc



theorem unitary_P_le (hexp : ∀ x ∈ R, x ^ 27 = 1 → x ^ 3 = 1)
    (hfix : ∀ y ∈ R, y ∉ S → y ^ 3 = 1 → r₄ * y = y * r₄ →
      ∃ d ∈ C₄, (y * (d * y * d⁻¹)) ^ 3 ≠ 1)
    {Y : Type} [Group Y] {α : MulAut Y} (χ : Y ≃* ↥S)
    (hχ : MulAut.congr χ α = Cls3.conjIso (rrR 3))
    {P : Subgroup (MulAut Y)} (hP : IsPGroup 3 ↥P) (hPc : ∀ e ∈ P, e * α = α * e)
    (hPn : ∀ c ∈ fixSub α, MulAut.conj c ∈ normalizer (P : Set (MulAut Y))) :
    Nat.card P ≤ 9 := by
  have hmap := map_fixSub_r₄ χ hχ
  have hΘα : toR χ α = r₄R := by
    show Cls3.conjIso.symm (MulAut.congr χ α) = r₄R
    rw [hχ]
    exact MulEquiv.symm_apply_apply _ _
  have key := core_fix hexp hfix (P := P.map (toR χ).toMonoidHom) (hP.map _) ?_ ?_
  · rwa [Subgroup.card_map_of_injective (toR χ).injective] at key
  · rintro x ⟨p, hp, rfl⟩
    show toR χ p * r₄R = r₄R * toR χ p
    rw [← hΘα, ← map_mul, ← map_mul, hPc p hp]
  · intro d hd
    have hdS : (d : Equiv.Perm (Fin 42)) ∈ S := (Subgroup.mem_inf.1 hd).2
    set s : ↥S := ⟨d, hdS⟩ with hs
    have hc : χ.symm s ∈ fixSub α := by
      have hs' : s ∈ (fixSub α).map χ.toMonoidHom := by
        rw [hmap]
        exact Subgroup.mem_subgroupOf.2 hd
      obtain ⟨c, hc, hcs⟩ := hs'
      have : c = χ.symm s := by rw [← hcs]; exact (MulEquiv.symm_apply_apply χ c).symm
      rw [← this]
      exact hc
    have h2 := Subgroup.mem_map_of_mem (toR χ).toMonoidHom (hPn _ hc)
    rw [Transport.map_normalizer] at h2
    have h3 : (toR χ).toMonoidHom (MulAut.conj (χ.symm s)) = d := by
      show toR χ (MulAut.conj (χ.symm s)) = d
      rw [toR_conj, MulEquiv.apply_symm_apply]
      rfl
    rwa [h3] at h2

theorem cent_Y
    (hcent : ∀ x ∈ R, x ≠ 1 → x ^ 3 = 1 → ∃ d ∈ C₁, d * x ≠ x * d)
    {Y : Type} [Group Y] (ψ : Y ≃* ↥S) (t : Y) (ht : orderOf t = 2)
    {X : Subgroup (MulAut Y)} (hX : IsPGroup 3 ↥X)
    (hXc : X ≤ centralizer ({MulAut.conj t} : Set (MulAut Y)))
    (hXn : ∀ c ∈ centralizer ({MulAut.conj t} : Set (MulAut Y)),
      c ∈ normalizer (X : Set (MulAut Y))) : X = ⊥ := by
  have hΘt : toR ψ (MulAut.conj t) = Rinc (ψ t) := toR_conj ψ t
  have hc2 : orderOf (Rinc (ψ t)) = 2 := by
    rw [show Rinc (ψ t) = ⟨((ψ t : ↥S) : Equiv.Perm (Fin 42)), S_le_R (ψ t).2⟩ from rfl,
      Subgroup.orderOf_mk, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ht]
  have hcI := isConj_r₁_of_mem_S (c := Rinc (ψ t)) (ψ t).2 hc2
  have key := core_cent hcent hcI (X := X.map (toR ψ).toMonoidHom) (hX.map _) ?_ ?_
  · exact (Subgroup.map_eq_bot_iff_of_injective X (toR ψ).injective).1 key
  · rintro x ⟨p, hp, rfl⟩
    have hp' := Subgroup.mem_centralizer_singleton_iff.1 (hXc hp)
    show toR ψ p * Rinc (ψ t) = Rinc (ψ t) * toR ψ p
    rw [← hΘt, ← map_mul, ← map_mul, hp']
  · intro g hg
    have hg' : (toR ψ).symm g ∈ centralizer ({MulAut.conj t} : Set (MulAut Y)) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply (toR ψ).injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hΘt]
      exact hg
    have h2 := Subgroup.mem_map_of_mem (toR ψ).toMonoidHom (hXn _ hg')
    rw [Transport.map_normalizer] at h2
    have h3 : (toR ψ).toMonoidHom ((toR ψ).symm g) = g := MulEquiv.apply_symm_apply _ _
    rwa [h3] at h2

theorem kb813_of_model (h : KB813Model) : KB813 := by
  intro Y _ _ hY
  obtain ⟨ψ⟩ := CFSG.ComponentClassification.CatFactsSmall.nonempty_equiv_psl34_of_lieModel hY
  refine ⟨?_, ?_, ?_⟩
  · rw [pRank_eq_of_mulEquiv' ψ 2]
    exact four_le_pRank_S_of_e16 h.e16
  · intro t ht X hX hXc hXn
    exact cent_Y h.cent ψ t ht hX hXc hXn
  · intro α hα2 hU
    obtain ⟨χ, hχ⟩ := exists_mulEquiv_r₄ ψ hα2 (card_of_unitaryFix hU)
    exact ⟨unitary_E h.exp27 χ hχ, fun P hP hPc hPn => unitary_P_le h.exp27 h.fix χ hχ hP hPc hPn⟩


end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
