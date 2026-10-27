module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.KGen
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.RowFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RowLink
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.Prelim

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction.Fi

open Subgroup Cover CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction.Hyp

variable {D : Type} [Group D]

theorem canLoc_eq_of_oddCentralExt (hD : Even (Nat.card (center D))) {G : Type} [Group G]
    [Finite G] {K₁ N₀ : Subgroup G} (hK : CFSG.IsQuasisimple ↥K₁)
    (hIsK : IsOddCentralExt D (↥K₁ ⧸ CFSG.oddCore ↥K₁)) (hcan : CanLoc K₁ N₀) : N₀ = K₁ := by
  have : Group.IsPerfect ↥K₁ := hK.1
  have hev : Even (Nat.card ↥(center ↥K₁)) :=
    even_card_center_of_cover (QuotientGroup.mk' (CFSG.oddCore ↥K₁))
      (QuotientGroup.mk'_surjective _)
      (by
        rw [QuotientGroup.ker_mk']
        exact oddCore_le_center hK)
      (oddCentralExt_even_card_center hD hIsK)
  rcases hcan with ⟨-, h⟩ | ⟨hodd, -⟩
  · exact h
  · exact absurd hev (Nat.not_even_iff_odd.2 hodd)

theorem solStd_of_centralizer_eq {L : Type} [Group L] {u : L} {K : Subgroup L}
    (hK : K = centralizer ({u} : Set L)) (hu2 : orderOf u = 2) (hq : CFSG.IsQuasisimple ↥K)
    (hZ : Nat.card (center ↥K) = 2) : SolStd K := by
  have huK : u ∈ K := by
    rw [hK]
    exact mem_centralizer_singleton_iff.2 rfl
  have hu1 : u ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hu2
    omega
  have huc : (⟨u, huK⟩ : ↥K) ∈ center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : (g : L) ∈ centralizer ({u} : Set L) := hK ▸ g.2
    exact Subtype.ext (mem_centralizer_singleton_iff.1 hg)
  have hne : (⟨u, huK⟩ : ↥K) ≠ 1 := fun h => hu1 (congrArg Subtype.val h)
  have h2 := (Nat.card_eq_two_iff' (1 : ↥(center ↥K))).1 hZ
  have hC : ∀ x ∈ centralizer (K : Set L), x = 1 ∨ x = u := by
    intro x hx
    have hxK : x ∈ K := by
      rw [hK]
      exact mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hx u huK).symm
    have hxc : (⟨x, hxK⟩ : ↥K) ∈ center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (mem_centralizer_iff.1 hx g g.2)
    by_cases hx1 : x = 1
    · exact Or.inl hx1
    · refine Or.inr ?_
      have hx1' : (⟨⟨x, hxK⟩, hxc⟩ : ↥(center ↥K)) ≠ 1 := fun h =>
        hx1 (congrArg (fun z : ↥(center ↥K) => ((z : ↥K) : L)) h)
      have hu1' : (⟨⟨u, huK⟩, huc⟩ : ↥(center ↥K)) ≠ 1 := fun h =>
        hne (congrArg (fun z : ↥(center ↥K) => (z : ↥K)) h)
      have := h2.unique hx1' hu1'
      exact congrArg (fun z : ↥(center ↥K) => ((z : ↥K) : L)) this
  have hnc : ¬ IsMulCommutative ↥K := not_isMulCommutative_of_quasisimple hq
  refine ⟨⟨fun g hbot => ?_, fun g hg => ?_⟩, u, hu2, ?_⟩
  ·
    apply hnc
    have h1 : K.map (MulAut.conj g).toMonoidHom ≤ centralizer (K : Set L) := by
      rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
      exact hbot
    refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    have ha : g * (a : L) * g⁻¹ ∈ centralizer (K : Set L) :=
      h1 ⟨a, a.2, by simp⟩
    have hb : g * (b : L) * g⁻¹ ∈ centralizer (K : Set L) :=
      h1 ⟨b, b.2, by simp⟩
    have hcomm : (g * (a : L) * g⁻¹) * (g * (b : L) * g⁻¹) =
        (g * (b : L) * g⁻¹) * (g * (a : L) * g⁻¹) := by
      rcases hC _ ha with h | h <;> rcases hC _ hb with h' | h' <;> rw [h, h'] <;> simp
    have : (a : L) * b = b * a := by
      have h3 : g * ((a : L) * b) * g⁻¹ = g * ((b : L) * a) * g⁻¹ := by
        calc g * ((a : L) * b) * g⁻¹ = (g * (a : L) * g⁻¹) * (g * (b : L) * g⁻¹) := by group
          _ = (g * (b : L) * g⁻¹) * (g * (a : L) * g⁻¹) := hcomm
          _ = g * ((b : L) * a) * g⁻¹ := by group
      simpa using h3
    exact this
  ·
    have hbot : centralizer (K : Set L) ⊓ (centralizer (K : Set L)).map (MulAut.conj g).toMonoidHom
        = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [Subgroup.mem_bot]
      by_contra hx1
      have hxu : x = u := (hC x hx.1).resolve_left hx1
      have h1 : g⁻¹ * x * g ∈ centralizer (K : Set L) :=
        (Cover.mem_map_conj_iff _ g x).1 hx.2
      have h1' : g⁻¹ * u * g ∈ centralizer (K : Set L) := hxu ▸ h1
      have hne1 : g⁻¹ * u * g ≠ 1 := by
        intro h
        apply hu1
        calc u = g * (g⁻¹ * u * g) * g⁻¹ := by group
          _ = 1 := by rw [h]; group
      have h3 : g⁻¹ * u * g = u := (hC _ h1').resolve_left hne1
      apply hg
      have : g ∈ K := by
        rw [hK]
        refine mem_centralizer_singleton_iff.2 ?_
        calc g * u = g * (g⁻¹ * u * g) := by rw [h3]
          _ = u * g := by group
      exact Subgroup.le_normalizer this
    rw [hbot, Subgroup.card_bot]
    exact odd_one
  · have hle : K ≤ centralizer ({u} : Set L) := hK.le
    refine isCompIn_of_normal hle hq ?_
    have : K.subgroupOf (centralizer ({u} : Set L)) = ⊤ := Subgroup.subgroupOf_eq_top.2 hK.ge
    rw [this]
    infer_instance

theorem fiStdRow_of_list {S : List TauCeti.SporadicName} {n : ℕ} (hZ : Nat.card (center D) = 2)
    (hnc : ¬ IsMulCommutative D) (hn : n ≤ Nat.card D)
    (hloc : ∀ s' ∈ S, ∀ (G : Type) [Group G] [Finite G] (L K : Subgroup G) (u : G),
      OddCover s' L → fiLoc n G L K u → SolomonLocalQ L K u) :
    ∀ (G : Type) [Group G] [Finite G] (L K₁ T : Subgroup G) (s : G),
      (∃ s'' ∈ S, OddCover s'' L) → T ≠ ⊥ → Sol78Link5bData K₁ L T s →
        CFSG.IsQuasisimple ↥K₁ → IsOddCentralExt D (↥K₁ ⧸ CFSG.oddCore ↥K₁) →
          SolStd (K₁.subgroupOf L) ∧ twoAdic (autCentralizer L K₁) ≤ 2 := by
  intro G _ _ L K₁ T s ⟨s'', hs'', hcov⟩ hT hdata hq hK
  obtain ⟨u, hQ⟩ := fiLoc_of_oddCentralExt_quot hZ hnc hn hdata.le_left hq hK
  have hl := hloc s'' hs'' G L K₁ u hcov hQ
  exact ⟨hl.standard_in_L, hl.autCentralizer_two⟩

theorem fiStdRow_of {s' : TauCeti.SporadicName} {n : ℕ} (hZ : Nat.card (center D) = 2)
    (hnc : ¬ IsMulCommutative D) (hn : n ≤ Nat.card D)
    (hloc : ∀ (G : Type) [Group G] [Finite G] (L K : Subgroup G) (u : G), OddCover s' L →
      fiLoc n G L K u → SolomonLocalQ L K u) :
    ∀ (G : Type) [Group G] [Finite G] (L K₁ T : Subgroup G) (s : G),
      (∃ s'' ∈ [s'], OddCover s'' L) → T ≠ ⊥ → Sol78Link5bData K₁ L T s →
        CFSG.IsQuasisimple ↥K₁ → IsOddCentralExt D (↥K₁ ⧸ CFSG.oddCore ↥K₁) →
          SolStd (K₁.subgroupOf L) ∧ twoAdic (autCentralizer L K₁) ≤ 2 :=
  fiStdRow_of_list (S := [s']) hZ hnc hn fun s'' hs'' => by
    rcases List.mem_singleton.1 hs'' with rfl
    exact hloc

theorem fiFourA_of_list {S : List TauCeti.SporadicName} {n : ℕ} (hD : Even (Nat.card (center D)))
    (hZ : Nat.card (center D) = 2) (hnc : ¬ IsMulCommutative D) (hn : n ≤ Nat.card D)
    (hpair : ∀ s' ∈ S, ∀ (G : Type) [Group G] [Finite G] (L K : Subgroup G) (u : G),
      OddCover s' L → fiLoc n G L K u →
        Group.IsSolvable ↥(autCentralizer L K) ∧ twoAdic (autCentralizer L K) ≤ 2)
    (hfix : ∀ (K₂ : Type) [Group K₂] [Finite K₂], Group.IsPerfect K₂ →
      (∃ (X : Type) (_ : Group X), IsOddCentralExt D X ∧
        Nonempty ((K₂ ⧸ center K₂) ≃* (X ⧸ center X))) → InvolutionFixesElem K₂ 16) :
    FourAFacts (IsOddCentralExt D) S := by
  refine fourAFacts_of_lamProfile False 2 4 le_rfl ?_ ?_ ?_
  · intro G _ _ L K₁ N₀ T s ⟨s'', hs'', hcov⟩ hT hdata hq hK hcan
    obtain ⟨u, hQ⟩ := fiLoc_of_oddCentralExt_quot hZ hnc hn hdata.le_left hq hK
    obtain ⟨hsol, htwo⟩ := hpair s'' hs'' G L K₁ u hcov hQ
    have hN₀ : N₀ = K₁ := canLoc_eq_of_oddCentralExt hD hq hK hcan
    subst hN₀
    exact ⟨hsol, htwo, elemBound_of_twoAdic (m := 2) htwo, fun h => h.elim⟩
  · intro K₂ _ _ hperf hex α hα1 hα2
    exact not_lamProfile_of_fixesElem False (hfix K₂ hperf hex) (by norm_num : 2 * 4 < 16) α hα1
      hα2
  · intro G _ _ K₁ N₀ hq hK hcan
    rintro ⟨hsolv, -⟩
    have hN₀ : N₀ = K₁ := canLoc_eq_of_oddCentralExt hD hq hK hcan
    subst hN₀
    have himg : (N₀.subgroupOf N₀).map (QuotientGroup.mk' (center ↥N₀)) = ⊤ := by
      rw [Subgroup.subgroupOf_self, Subgroup.map_top, MonoidHom.range_eq_top]
      exact QuotientGroup.mk'_surjective _
    rw [himg] at hsolv
    have hsolv' : Group.IsSolvable (↥N₀ ⧸ center ↥N₀) :=
      Group.isSolvable_of_surjective (f := (Subgroup.topEquiv (G := ↥N₀ ⧸ center ↥N₀)).toMonoidHom)
        (Subgroup.topEquiv (G := ↥N₀ ⧸ center ↥N₀)).surjective
    have := hq.2.1
    obtain ⟨a, b, hab⟩ := hq.2.2
    exact hab (IsSimpleGroup.comm_iff_isSolvable.2 hsolv' a b)

theorem fiFourA_of {s' : TauCeti.SporadicName} {n : ℕ} (hD : Even (Nat.card (center D)))
    (hZ : Nat.card (center D) = 2) (hnc : ¬ IsMulCommutative D) (hn : n ≤ Nat.card D)
    (hpair : ∀ (G : Type) [Group G] [Finite G] (L K : Subgroup G) (u : G), OddCover s' L →
      fiLoc n G L K u → Group.IsSolvable ↥(autCentralizer L K) ∧ twoAdic (autCentralizer L K) ≤ 2)
    (hfix : ∀ (K₂ : Type) [Group K₂] [Finite K₂], Group.IsPerfect K₂ →
      (∃ (X : Type) (_ : Group X), IsOddCentralExt D X ∧
        Nonempty ((K₂ ⧸ center K₂) ≃* (X ⧸ center X))) → InvolutionFixesElem K₂ 16) :
    FourAFacts (IsOddCentralExt D) [s'] :=
  fiFourA_of_list (S := [s']) hD hZ hnc hn
    (fun s'' hs'' => by
      rcases List.mem_singleton.1 hs'' with rfl
      exact hpair) hfix

end CFSG.EvenSporadicStandard.Induction.Fi
