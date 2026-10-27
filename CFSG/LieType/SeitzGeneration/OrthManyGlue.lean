module

public import CFSG.LieType.SeitzGeneration.OrthDfourProp
public import CFSG.LieType.SeitzGeneration.OrthHyperRoot
public import CFSG.LieType.SeitzGeneration.OrthNonsplitTools

public section

namespace CFSG.LieType.SeitzGeneration

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.PartOne.CTP
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical
  CFSG.Open OrthNS OrthBlk
open CFSG.RankThree.Classical2 (orthDerived)

section TwoMore

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem polar_self_apply_eq_zero {x : V ≃ₗ[K] V}
    (hx : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {e : V} {τ : K} (hτ : τ ≠ 0)
    (hrel : x (x e) = τ • x e - e) (he : Q e = 0) : polar Q e (x e) = 0 := by
  have hQ := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hx
  have h1 : Q (x (x e)) = 0 := by rw [hQ, hQ, he]
  rw [hrel] at h1
  have h2 : Q (τ • x e - e) = Q e + τ ^ 2 * Q (x e) - τ * polar Q e (x e) := by
    have : τ • x e - e = -(e - τ • x e) := by abel
    rw [this, QuadraticMap.map_neg]
    exact map_sub_smul' e (x e) τ
  rw [h2, hQ, he] at h1
  have h3 : τ * polar Q e (x e) = 0 := by linear_combination -h1
  exact (mul_eq_zero.mp h3).resolve_left hτ


end TwoMore

section ProvedPivot

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem subset_rootSet_of_mixed {H : Subgroup (V ≃ₗ[K] V)}
    (hH : H ≤ TauCeti.QuadraticMap.orthogonalGroup Q) {Y : Submodule K V}
    (hY : PolarNondegOn Q Y) (hY4 : 4 ≤ finrank K Y)
    (hYH : ∀ e ∈ Y, ∀ w ∈ Y, eichler Q e w ∈ H) {s : V} (hs : ∀ y ∈ Y, polar Q s y = 0)
    (hmix : ∃ w ∈ rootSet Q H s, ∃ y ∈ Y, ∃ r : V, w = y + r ∧ (∀ z ∈ Y, polar Q z r = 0) ∧
      ∃ e ∈ Y, ∃ f ∈ Y, eichler Q e f y ≠ y) :
    ∀ y ∈ Y, y ∈ rootSet Q H s := by
  obtain ⟨w, hw, y, hyY, r, rfl, hr, e, heY, f, hfY, hne⟩ := hmix
  have hg := hYH e heY f hfY
  have hgs : eichler Q e f s = s :=
    eichler_apply_of_polar_eq_zero (hs e heY) (hs f hfY)
  have hgr : eichler Q e f r = r :=
    eichler_apply_of_polar_eq_zero (by rw [polar_comm]; exact hr e heY)
      (by rw [polar_comm]; exact hr f hfY)
  have h1 := rootSet_map hH hg hw
  rw [hgs, map_add, hgr] at h1
  have h2 := AddSubgroup.sub_mem _ h1 hw
  have h3 : eichler Q e f y + r - (y + r) = eichler Q e f y - y := by abel
  rw [h3] at h2
  have hdY : eichler Q e f y - y ∈ Y := by
    by_cases h : Q e = 0 ∧ polar Q e f = 0
    · rw [eichler_apply h.1 h.2]
      have : y + polar Q y e • f - (polar Q y f + Q f * polar Q y e) • e - y =
          polar Q y e • f - (polar Q y f + Q f * polar Q y e) • e := by abel
      rw [this]
      exact Y.sub_mem (Y.smul_mem _ hfY) (Y.smul_mem _ heY)
    · exact absurd (by rw [eichler_of_not h]; rfl) hne
  have hd0 : eichler Q e f y - y ≠ 0 := sub_ne_zero.mpr hne
  refine mem_of_invariant_of_ne_zero hY hY4 (rootSet Q H s) ?_ h2 hdY hd0
  intro x hx z hz _ _ m hm _
  have hgx := hYH x hx z hz
  have hfix : eichler Q x z s = s :=
    eichler_apply_of_polar_eq_zero (hs x hx) (hs z hz)
  have := rootSet_map hH hgx hm
  rwa [hfix] at this

end ProvedPivot

section ProvedGlue

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem isRootCenter_of_pieces {H : Subgroup (V ≃ₗ[K] V)} {V₀ P : Submodule K V}
    {ι : Type} [Nonempty ι] (R : ι → Submodule K V)
    (hP0 : OrthSep Q P V₀) (hPR : ∀ i, OrthSep Q P (R i))
    (hspan : (⊤ : Submodule K V) ≤ V₀ ⊔ P ⊔ ⨆ i, R i)
    (hEich : ∀ i, ∀ e ∈ V₀ ⊔ P ⊔ R i, ∀ w ∈ V₀ ⊔ P ⊔ R i, eichler Q e w ∈ H)
    {t : V} (htP : t ∈ P) (ht0 : t ≠ 0) (htQ : Q t = 0) : IsRootCenter Q H t := by
  classical
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  refine ⟨ht0, htQ, fun w hw => ?_⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp (hspan (Submodule.mem_top (x := w)))
  have htb : polar Q t b = 0 := by
    refine Submodule.iSup_induction R (motive := fun b => polar Q t b = 0) hb ?_ ?_ ?_
    · intro i b hb'
      exact hPR i t htP b hb'
    · exact polar_zero_right Q t
    · intro x y hx hy
      rw [polar_add_right, hx, hy, add_zero]
  have hta : polar Q t a = 0 := by
    rw [polar_add_right, htb, add_zero] at hw
    exact hw
  have haR : a ∈ rootSet Q H t := by
    refine ⟨hta, hEich i₀ t ?_ a ?_⟩
    · exact Submodule.mem_sup_left (Submodule.mem_sup_right htP)
    · exact Submodule.mem_sup_left ha
  have hbR : b ∈ rootSet Q H t := by
    refine Submodule.iSup_induction R (motive := fun b => b ∈ rootSet Q H t) hb ?_
      (AddSubgroup.zero_mem _) (fun x y hx hy => AddSubgroup.add_mem _ hx hy)
    intro i b hb'
    exact ⟨hPR i t htP b hb', hEich i t (Submodule.mem_sup_left (Submodule.mem_sup_right htP)) b
      (Submodule.mem_sup_right hb')⟩
  exact ((rootSet Q H t).add_mem haR hbR).2

theorem elementaryGroup_le_of_pieces (hQ : (polarBilin Q).Nondegenerate)
    {H : Subgroup (V ≃ₗ[K] V)} (hH : H ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    {V₀ P : Submodule K V} (hP : PolarNondegOn Q P) (h3 : 3 ≤ finrank K P)
    {ι : Type} [Nonempty ι] (R : ι → Submodule K V)
    (hP0 : OrthSep Q P V₀) (hPR : ∀ i, OrthSep Q P (R i))
    (hspan : (⊤ : Submodule K V) ≤ V₀ ⊔ P ⊔ ⨆ i, R i)
    (hEich : ∀ i, ∀ e ∈ V₀ ⊔ P ⊔ R i, ∀ w ∈ V₀ ⊔ P ⊔ R i, eichler Q e w ∈ H) :
    elementaryGroup Q ≤ H := by
  obtain ⟨s, hsP, hs0, hsQ⟩ := exists_singular_of_three_le_any (Q := Q) h3
  obtain ⟨f, hfP, hfQ, hsf⟩ := exists_partner_of_polarNondegOn hP hsP hs0 hsQ
  have hf0 : f ≠ 0 := fun h0 => by
    rw [h0, polar_zero_right] at hsf
    exact zero_ne_one hsf
  exact elementaryGroup_le_of_hypPair hQ hH ⟨s, f, hsQ, hfQ, hsf⟩
    (isRootCenter_of_pieces R hP0 hPR hspan hEich hsP hs0 hsQ)
    (isRootCenter_of_pieces R hP0 hPR hspan hEich hfP hf0 hfQ)

end ProvedGlue

section ProvedRestrict

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem eichler_mem_of_restricted_plane {U : Submodule K V} (hU : PolarNondegOn Q U)
    (hEU : orthDerived (Q.comp U.subtype) = elementaryGroup (Q.comp U.subtype))
    (E : Subgroup (orthDerived Q))
    (hstab : ∀ x : E, ((x : orthDerived Q) : V ≃ₗ[K] V) ∈ stab U)
    (hΩ : elementaryGroup Q ≤ orthDerived Q)
    (ρ : E →* orthDerived (Q.comp U.subtype))
    (hρ : ∀ (x : E) (u : U), (((ρ x : orthDerived (Q.comp U.subtype)) : U ≃ₗ[K] U) u : V) =
      ((x : orthDerived Q) : V ≃ₗ[K] V) u)
    (hgen : Subgroup.closure {h : orthDerived (Q.comp U.subtype) |
      ∃ x : E, x ≠ 1 ∧ h * ρ x = ρ x * h} = ⊤) :
    ∀ e ∈ U, ∀ w ∈ U, eichler Q e w ∈ orthCentralizerSpan Q E := by
  classical
  let φ : orthDerived (Q.comp U.subtype) →* (V ≃ₗ[K] V) :=
    (extU hU).comp (orthDerived (Q.comp U.subtype)).subtype
  have hle : Subgroup.closure {h : orthDerived (Q.comp U.subtype) |
      ∃ x : E, x ≠ 1 ∧ h * ρ x = ρ x * h} ≤ (orthCentralizerSpan Q E).comap φ := by
    rw [Subgroup.closure_le]
    rintro h ⟨x, hx1, hhx⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    have hhE : extU hU (h : U ≃ₗ[K] U) ∈ eichlerGroupOn Q U :=
      extU_mem_eichlerGroupOn hU (hEU ▸ h.2)
    have hΩmem : extU hU (h : U ≃ₗ[K] U) ∈ orthDerived Q :=
      hΩ (eichlerGroupOn_le_elementaryGroup U hhE)
    refine mem_orthCentralizerSpan_of_commute (a := (x : orthDerived Q)) hΩmem x.2
      (fun h1 => hx1 (Subtype.ext h1)) ?_
    have hc : Commute (extU hU (h : U ≃ₗ[K] U)) ((x : orthDerived Q) : V ≃ₗ[K] V) := by
      refine commute_of_mem_eichlerGroupOn hU hhE (orthDerived_mem_orthogonalGroup) (hstab x) ?_
      intro u hu
      have hxu : ((x : orthDerived Q) : V ≃ₗ[K] V) u ∈ U := ((mem_stab.mp (hstab x)) u hu).1
      rw [extU_apply_mem hU _ hxu, extU_apply_mem hU _ hu]
      have e1 : (⟨((x : orthDerived Q) : V ≃ₗ[K] V) u, hxu⟩ : U) =
          ((ρ x : orthDerived (Q.comp U.subtype)) : U ≃ₗ[K] U) ⟨u, hu⟩ :=
        Subtype.ext (hρ x ⟨u, hu⟩).symm
      rw [e1]
      have e2 := hρ x ((h : U ≃ₗ[K] U) ⟨u, hu⟩)
      rw [← e2]
      exact congrArg (fun y : orthDerived (Q.comp U.subtype) =>
        (((y : U ≃ₗ[K] U) ⟨u, hu⟩ : U) : V)) hhx
    exact hc.eq
  intro e he w hw
  have hmem : eichler (Q.comp U.subtype) ⟨e, he⟩ ⟨w, hw⟩ ∈
      orthDerived (Q.comp U.subtype) := by
    rw [hEU]
    exact eichler_mem_elementaryGroup _ _ _
  have htop : (⟨eichler (Q.comp U.subtype) ⟨e, he⟩ ⟨w, hw⟩, hmem⟩ : orthDerived (Q.comp U.subtype))
      ∈ Subgroup.closure {h : orthDerived (Q.comp U.subtype) |
        ∃ x : E, x ≠ 1 ∧ h * ρ x = ρ x * h} := by
    rw [hgen]
    exact Subgroup.mem_top _
  have := Subgroup.mem_comap.mp (hle htop)
  have e3 : φ ⟨eichler (Q.comp U.subtype) ⟨e, he⟩ ⟨w, hw⟩, hmem⟩ = eichler Q e w :=
    extU_eichler hU ⟨e, he⟩ ⟨w, hw⟩
  rwa [e3] at this

end ProvedRestrict

end CFSG.LieType.SeitzGeneration
