module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142TLayerDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142TInd

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I142T

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.I142N
open scoped commutatorElement

theorem goodA_orbit_of_stab {S : Type} [Group S] [Finite S] (E : Subgroup (MulAut S))
    {X : Subgroup S} (hXE : ∀ a : ↥E, X.map (E.subtype a).toMonoidHom = X)
    {K₀ : Subgroup S} (hK₀ : IsComponentOf K₀ X)
    (hq : ∀ (B : Subgroup ↥E)
      (hinv : ∀ a : ↥B, K₀.map ((E.subtype.comp B.subtype) a).toMonoidHom = K₀),
      (∀ a : ↥E, K₀.map (E.subtype a).toMonoidHom = K₀ → a ∈ B) →
        GoodA (quotAct (E.subtype.comp B.subtype) K₀ hinv) ⊤) :
    GoodA E.subtype (sSup (orbitOf E.subtype K₀)) := by
  classical
  haveI : Finite (Subgroup S) := Finite.of_injective (fun H : Subgroup S => (H : Set S))
    (fun H K h => SetLike.coe_injective h)
  haveI : Fintype ↥(orbitOf E.subtype K₀) := Fintype.ofFinite _
  set ρ : ↥E →* MulAut S := E.subtype with hρ
  set O := orbitOf ρ K₀ with hOdef
  have hcomp : ∀ K ∈ O, IsComponentOf K X :=
    fun K hK => isComponentOf_orbit (ρ := ρ) hXE hK₀ hK
  have hO : ∀ K ∈ O, ∀ a : ↥E, K.map (ρ a).toMonoidHom ∈ O := fun K hK a => orbitOf_map_mem ρ hK a
  set σ := orbitAct ρ O hO with hσ
  set i₀ : ↥O := ⟨K₀, mem_orbitOf_self ρ K₀⟩ with hi₀
  have hcomm' : ∀ i j : ↥O, i ≠ j → ∀ x ∈ i.1, ∀ y ∈ j.1, Commute x y := by
    intro i j hij x hx y hy
    rcases isComponent_commute_or_eq (hcomp i.1 i.2) (hcomp j.1 j.2) with h | h
    · exact absurd (Subtype.ext h) hij
    · have hxy : ⁅x, y⁆ = 1 := by
        have := Subgroup.commutator_mem_commutator hx hy
        rw [h, Subgroup.mem_bot] at this
        exact this
      exact commutatorElement_eq_one_iff_mul_comm.1 hxy
  have hmap : ∀ (a : ↥E) (K : ↥O), K.1.map (ρ a).toMonoidHom = (σ a K).1 := fun a K => rfl
  have htrans : ∀ K' : ↥O, ∃ a : ↥E, σ a i₀ = K' := by
    intro K'
    obtain ⟨a, ha⟩ := K'.2
    exact ⟨a, Subtype.ext ha⟩
  have hinv₀ : ∀ a : ↥(stabSub σ i₀),
      K₀.map ((ρ.comp (stabSub σ i₀).subtype) a).toMonoidHom = K₀ := by
    intro a
    have ha : σ (a : ↥E) i₀ = i₀ := (mem_stabSub σ i₀ _).1 a.2
    have h1 := congrArg Subtype.val ha
    exact h1
  have hB : ∀ a : ↥E, K₀.map (E.subtype a).toMonoidHom = K₀ → a ∈ stabSub σ i₀ := by
    intro a ha
    rw [mem_stabSub]
    apply Subtype.ext
    show (σ a i₀).1 = K₀
    rw [← hmap a i₀]
    exact ha
  have hqK : CFSG.Open.IsQuasisimple ↥K₀ := hK₀.2.2
  have hT : GoodA (quotAct (ρ.comp (stabSub σ i₀).subtype) K₀ hinv₀) ⊤ :=
    hq (stabSub σ i₀) hinv₀ hB
  have hsig : ∀ P : Subgroup (↥K₀ ⧸ Subgroup.center ↥K₀),
      P ≤ fixA (quotAct (ρ.comp (stabSub σ i₀).subtype) K₀ hinv₀) → ⁅P, P⁆ = P →
        P ≤ GLALayer (fixA (quotAct (ρ.comp (stabSub σ i₀).subtype) K₀ hinv₀)) := by
    intro P hP hPp
    have := hT P (by rwa [inf_top_eq]) hPp
    rwa [inf_top_eq] at this
  have hgood0 : GoodA ρ (⨆ K : ↥O, K.1) :=
    goodA_iSup_transitive ρ (fun K : ↥O => K.1) hcomm' σ hmap i₀ htrans
      (goodA_of_component (ρ.comp (stabSub σ i₀).subtype) K₀ hinv₀ hqK hsig)
  rw [sSup_eq_iSup']
  exact hgood0

theorem goodA_glaLayer_of_orbits {S : Type} [Group S] [Finite S] (E : Subgroup (MulAut S))
    {X : Subgroup S} (hXE : ∀ a : ↥E, X.map (E.subtype a).toMonoidHom = X)
    (horb : ∀ K₀ : Subgroup S, IsComponentOf K₀ X →
      GoodA E.subtype (sSup (orbitOf E.subtype K₀))) :
    GoodA E.subtype (GLALayer X) := by
  classical
  haveI : Finite (Subgroup S) := Finite.of_injective (fun H : Subgroup S => (H : Set S))
    (fun H K h => SetLike.coe_injective h)
  let ι := {O : Set (Subgroup S) // ∃ K, IsComponentOf K X ∧ O = orbitOf E.subtype K}
  haveI : Finite ι := Subtype.finite
  haveI : Fintype ι := Fintype.ofFinite ι
  have hmemO : ∀ O : ι, ∀ K ∈ O.1, IsComponentOf K X := by
    rintro ⟨O, K₁, hK₁, rfl⟩ K hK
    exact isComponentOf_orbit hXE hK₁ hK
  have hOinv : ∀ O : ι, ∀ K ∈ O.1, ∀ a : ↥E, K.map (E.subtype a).toMonoidHom ∈ O.1 := by
    rintro ⟨O, K₁, hK₁, rfl⟩ K hK a
    exact orbitOf_map_mem _ hK a
  let H : ι → Subgroup S := fun O => sSup O.1
  have hcomm : ∀ i j : ι, i ≠ j → ∀ x ∈ H i, ∀ y ∈ H j, Commute x y := by
    intro i j hij x hx y hy
    have hdisj : ∀ K ∈ i.1, ∀ K' ∈ j.1, K ≠ K' := by
      intro K hK' K' hK'' hKK
      subst hKK
      obtain ⟨K₁, _, hi⟩ := i.2
      obtain ⟨K₂, _, hj⟩ := j.2
      apply hij
      apply Subtype.ext
      rw [hi, hj]
      rw [hi] at hK'
      rw [hj] at hK''
      exact orbitOf_eq_of_common E.subtype hK' hK''
    have hc := commutator_sSup_eq_bot (fun K hK => hmemO i K hK) (fun K hK => hmemO j K hK) hdisj
    have hxy : ⁅x, y⁆ = 1 := by
      have := Subgroup.commutator_mem_commutator hx hy
      rw [hc, Subgroup.mem_bot] at this
      exact this
    exact commutatorElement_eq_one_iff_mul_comm.1 hxy
  have hinv : ∀ (a : ↥E) (i : ι), (H i).map (E.subtype a).toMonoidHom = H i := by
    intro a i
    exact sSup_orbit_map E.subtype i.1 (fun K hK b => hOinv i K hK b) a
  have hfac : ∀ i : ι, GoodA E.subtype (H i) := by
    intro i
    obtain ⟨K₁, hK₁, hi⟩ := i.2
    have := horb K₁ hK₁
    rw [← hi] at this
    exact this
  have hG := goodA_iSup_coord E.subtype H hcomm hinv hfac
  have hL : GLALayer X = ⨆ i : ι, H i := by
    refine layer_eq_iSup_orbits E.subtype hXE (fun i : ι => i.1) ?_ ?_
    · intro K hK
      exact ⟨⟨orbitOf E.subtype K, K, hK, rfl⟩, mem_orbitOf_self _ K⟩
    · intro i K hK
      exact hmemO i K hK
  rw [hL]
  exact hG

section Cert


theorem layerFixTyped_holds : LayerFixTyped := by
  classical
  intro S _ _ p hp hp2 E hE X hXE hK
  have hcE : ∀ a b : ↥E, a * b = b * a := fun a b => (hE.1.is_comm).comm a b
  constructor
  · refine goodA_glaLayer_of_orbits E hXE ?_
    intro K₀ hK₀
    refine goodA_orbit_of_stab E hXE hK₀ ?_
    intro B hinv _
    set ρB := E.subtype.comp B.subtype with hρB
    set σ := quotAct ρB K₀ hinv with hσ
    have hc : ∀ a b : ↥B, a * b = b * a := fun a b => Subtype.ext (hcE a.1 b.1)
    have he : ∀ a : ↥B, a ^ p = 1 := by
      intro a
      apply Subtype.ext
      apply Subtype.ext
      exact hE.2 (a.1 : MulAut S) (a.1).2
    have hEab : IsElemAbelian p σ.range := isElemAbelian_range p σ hc he
    have hCP : CPlus (↥K₀ ⧸ Subgroup.center ↥K₀) := hK K₀ hK₀
    have hG := goodA_all I142M.compTypesCyc_holds I142M.titsCentSolv_holds p hp hp2
      (Nat.card σ.range) (↥K₀ ⧸ Subgroup.center ↥K₀) hCP σ.range hEab le_rfl
    intro P hP hPp
    rw [inf_top_eq] at hP ⊢
    have hP' : P ≤ fixA σ.range.subtype ⊓ ⊤ := by
      rw [inf_top_eq]
      exact (fixA_eq_range σ) ▸ hP
    have h3 := hG P hP' hPp
    rw [inf_top_eq] at h3
    exact (fixA_eq_range σ).symm ▸ h3
  · refine typesA_glaLayer_of_orbits E hXE ?_
    intro K₀ hK₀
    refine typesA_orbit_of_stab E hXE hK₀ ?_
    intro B hinv _
    set ρB := E.subtype.comp B.subtype with hρB
    set σ := quotAct ρB K₀ hinv with hσ
    have hc : ∀ a b : ↥B, a * b = b * a := fun a b => Subtype.ext (hcE a.1 b.1)
    have he : ∀ a : ↥B, a ^ p = 1 := by
      intro a
      apply Subtype.ext
      apply Subtype.ext
      exact hE.2 (a.1 : MulAut S) (a.1).2
    have hEab : IsElemAbelian p σ.range := isElemAbelian_range p σ hc he
    have hCP : CPlus (↥K₀ ⧸ Subgroup.center ↥K₀) := hK K₀ hK₀
    have hT := typesA_all I142M.compTypesCyc_holds I142M.titsCentSolv_holds p hp hp2
      (Nat.card σ.range) (↥K₀ ⧸ Subgroup.center ↥K₀) hCP σ.range hEab le_rfl
    intro K hK'
    rw [inf_top_eq] at hK'
    exact hT K ((fixA_subtype_eq_centFix σ.range) ▸ ((fixA_eq_range σ) ▸ hK'))

end Cert

end CFSG.LocalAnalysis.GLTheoremA.I142T
