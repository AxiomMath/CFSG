module

public import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.Bridge
public import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.Transport
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerActorSection
public import CFSG.Quasithin.Background.B1MoreElevenD

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF

open CFSG.RankThree.FFModules
open scoped commutatorElement

section Transfer

variable {X : Type} [Group X] {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
variable {ρ : Representation (ZMod 2) X W} {H : Subgroup X} {U : Submodule (ZMod 2) W}
variable {hU : IsInvariant ρ H U}

theorem cenOn_eq_of_between {B B' : Subgroup X} (h1 : cenOn ρ B U ≤ B') (h2 : B' ≤ B) :
    cenOn ρ B' U = cenOn ρ B U := by
  apply le_antisymm
  · intro g hg
    exact ⟨h2 hg.1, hg.2⟩
  · intro g hg
    exact ⟨h1 hg, hg.2⟩

theorem exists_sub_imgBin {B : Subgroup X} (hBH : B ≤ H)
    (Bb : Subgroup (MulAut (Multiplicative ↥U))) (hle : Bb ≤ imgBin ρ H U hU B) :
    ∃ B' : Subgroup X, cenOn ρ B U ≤ B' ∧ B' ≤ B ∧ imgBin ρ H U hU B' = Bb := by
  refine ⟨(Bb.comap (resBin ρ H U hU)).map H.subtype ⊓ B, ?_, inf_le_right, ?_⟩
  · intro g hg
    obtain ⟨hgB, hgU⟩ := mem_cenOn.1 hg
    refine ⟨⟨⟨g, hBH hgB⟩, ?_, rfl⟩, hgB⟩
    change resBin ρ H U hU ⟨g, hBH hgB⟩ ∈ Bb
    rw [(resBin_eq_one_iff (hU := hU) ⟨g, hBH hgB⟩).2 hgU]
    exact Bb.one_mem
  · ext x
    rw [mem_imgBin]
    constructor
    · rintro ⟨b, ⟨⟨h, hh, hhb⟩, hbB⟩, rfl⟩
      have : h = b := Subtype.ext hhb
      subst this
      exact hh
    · intro hx
      obtain ⟨b, hbB, rfl⟩ := mem_imgBin.1 (hle hx)
      exact ⟨b, ⟨⟨b, hx, rfl⟩, hbB⟩, rfl⟩

theorem card_binU (U : Submodule (ZMod 2) W) :
    Nat.card (Multiplicative ↥U) = Nat.card U :=
  Nat.card_congr (Multiplicative.toAdd : Multiplicative ↥U ≃ ↥U)

theorem isBestOffender_imgBin [Finite X] [Finite W] {B : Subgroup X} (hBH : B ≤ H)
    (hbest : IsBestOffenderOn ρ B U) (hnt : ¬ B ≤ cenOn ρ B U)
    (hstrict : ∀ B' : Subgroup X, cenOn ρ B U ≤ B' → B' < B → ¬ B' ≤ cenOn ρ B U →
      Nat.card B' * Nat.card (fixOn ρ B' U) < Nat.card B * Nat.card (fixOn ρ B U)) :
    CFSG.QuasithinUnique.Setup.Family.IsBestOffender (imgBin ρ H U hU H)
      (imgBin ρ H U hU B) := by
  have hcpos : 0 < Nat.card (cenOn ρ B U) := Nat.card_pos
  refine ⟨imgBin_mono hBH, fun h => hnt ((imgBin_eq_bot_iff hBH).1 h),
    isElemAbelian2_imgBin hBH hbest.1, ?_, ?_⟩
  · have hoff := hbest.isOffenderOn.2
    rw [← card_imgBin_mul_card_cenOn (hU := hU) hBH, ← card_fixV_imgBin (hU := hU) hBH] at hoff
    rw [card_binU]
    refine Nat.le_of_mul_le_mul_right ?_ hcpos
    calc Nat.card U * Nat.card (cenOn ρ B U)
        ≤ Nat.card (imgBin ρ H U hU B) * Nat.card (cenOn ρ B U) *
            Nat.card (CFSG.Quasithin.fixV (imgBin ρ H U hU B)) := hoff
      _ = _ := by ring
  · intro Bb hle hne1 hne2
    obtain ⟨B', h1, h2, h3⟩ := exists_sub_imgBin (hU := hU) hBH Bb hle
    have hlt : B' < B := lt_of_le_of_ne h2 fun h => hne2 (by rw [← h3, h])
    have hnc : ¬ B' ≤ cenOn ρ B U := fun h => hne1 (by
      rw [← h3]
      exact (imgBin_eq_bot_iff (h2.trans hBH)).2 fun g hg => ⟨hg, (h hg).2⟩)
    have key := hstrict B' h1 hlt hnc
    have e1 := card_imgBin_mul_card_cenOn (hU := hU) (h2.trans hBH)
    rw [cenOn_eq_of_between h1 h2, h3] at e1
    have e2 := card_imgBin_mul_card_cenOn (hU := hU) hBH
    rw [← e1, ← e2, ← card_fixV_imgBin (hU := hU) (h2.trans hBH), h3,
      ← card_fixV_imgBin (hU := hU) hBH] at key
    refine Nat.lt_of_mul_lt_mul_right (a := Nat.card (cenOn ρ B U)) ?_
    calc Nat.card Bb * Nat.card (CFSG.Quasithin.fixV Bb) * Nat.card (cenOn ρ B U)
        = Nat.card Bb * Nat.card (cenOn ρ B U) * Nat.card (CFSG.Quasithin.fixV Bb) := by ring
      _ < _ := key
      _ = _ := by ring

theorem commutator_imgBin_ne_bot {K B : Subgroup X} (hKH : K ≤ H) (hBH : B ≤ H)
    (hmove : ∃ b ∈ B, ∃ k ∈ K, ∃ u ∈ U, ρ b (ρ k u) ≠ ρ k (ρ b u)) :
    ⁅imgBin ρ H U hU K, imgBin ρ H U hU B⁆ ≠ ⊥ := by
  obtain ⟨b, hb, k, hk, u, hu, hne⟩ := hmove
  intro h
  have hx := resBin_mem_imgBin (hU := hU) hk (hKH hk)
  have hy := resBin_mem_imgBin (hU := hU) hb (hBH hb)
  have hc := Subgroup.commutator_mem_commutator hx hy
  rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
  apply hne
  have := congrArg (fun f : MulAut (Multiplicative ↥U) =>
    ((Multiplicative.toAdd (f (Multiplicative.ofAdd ⟨u, hu⟩)) : ↥U) : W)) hc
  simpa [MulAut.mul_apply, resBin_apply_val] using this.symm

theorem imgBin_isSubnormal {K : Subgroup X} (hKH : K ≤ H)
    (hK : ∀ h ∈ H, ∀ k ∈ K, h * k * h⁻¹ ∈ K) :
    CFSG.Open.IsSubnormal (imgBin ρ H U hU K) (imgBin ρ H U hU H) := by
  refine CFSG.Open.IsSubnormal.step (imgBin_mono hKH) ⟨fun n hn g => ?_⟩
    (CFSG.Open.IsSubnormal.refl _)
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  simpa using imgBin_normal (hU := hU) hK (g : MulAut (Multiplicative ↥U)) g.2 _ hn

theorem isComp_imgBin {K : Subgroup X} (hKH : K ≤ H) (hKq : CFSG.IsQuasisimple K)
    (hKU : ¬ K ≤ cenOn ρ K U) (hK : ∀ h ∈ H, ∀ k ∈ K, h * k * h⁻¹ ∈ K) :
    CFSG.QuasithinUnique.Setup.Family.IsComp (imgBin ρ H U hU K) (imgBin ρ H U hU H) :=
  ⟨imgBin_mono hKH, imgBin_isSubnormal hKH hK,
    CFSG.Quasithin.B1Red.isQuasisimple_to_open (imgBin_isQuasisimple hKH hKq hKU)⟩

end Transfer

section SectionClauses

open CFSG.QuasithinUnique.Setup.X1

variable {V : Type} [CommGroup V] [Finite V] {L A : Subgroup (MulAut V)}

theorem irrSection_sq (hV : ∀ v : V, v * v = 1) (sec : IrrSection V L A) (w : sec.W) :
    w * w = 1 := by
  obtain ⟨v, rfl⟩ := sec.π_surjective w
  rw [← map_mul]
  have : v * v = 1 := Subtype.ext (hV _)
  rw [this, map_one]

theorem irrSection_isIrrOn (sec : IrrSection V L A) :
    IsIrrOn (sec.τW.comp (Subgroup.inclusion le_sup_left)).range := by
  refine ⟨sec.nontrivial, fun S hS => sec.irreducible S fun x hx u hu => ?_⟩
  exact hS _ ⟨⟨x, hx⟩, rfl⟩ u hu

theorem irrSection_range_le_normalizer (sec : IrrSection V L A)
    (hAn : A ≤ Subgroup.normalizer (L : Set (MulAut V))) :
    (sec.τW.comp (Subgroup.inclusion le_sup_right)).range ≤
      Subgroup.normalizer ((sec.τW.comp (Subgroup.inclusion le_sup_left)).range :
        Set (MulAut sec.W)) := by
  have key : ∀ g ∈ (sec.τW.comp (Subgroup.inclusion le_sup_right)).range,
      ∀ h ∈ (sec.τW.comp (Subgroup.inclusion le_sup_left)).range,
        g * h * g⁻¹ ∈ (sec.τW.comp (Subgroup.inclusion le_sup_left)).range := by
    rintro _ ⟨⟨a, ha⟩, rfl⟩ _ ⟨⟨l, hl⟩, rfl⟩
    have hl' : a * l * a⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 (hAn ha) l).1 hl
    refine ⟨⟨a * l * a⁻¹, hl'⟩, ?_⟩
    simp only [MonoidHom.comp_apply, Subgroup.inclusion]
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨key g hg h, fun h' => ?_⟩
  have := key g⁻¹ (Subgroup.inv_mem _ hg) _ h'
  simpa [mul_assoc] using this

end SectionClauses

theorem exists_irrSection {X : Type} [Group X] [Finite X]
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) X W) (K A : Subgroup X)
    (hKq : CFSG.IsQuasisimple K) (hA2 : CFSG.IsElementaryAbelian 2 A)
    (hAK : A ≤ Subgroup.normalizer (K : Set X)) (hKA : ⁅K, A⁆ = K)
    (hKnt : ¬ K ≤ cenOn ρ K ⊤) (hb : IsBestOffenderOn ρ A ⊤) :
    ∃ (W' : Type) (_ : CommGroup W') (_ : Finite W') (Lb Eb : Subgroup (MulAut W')),
      (∀ w : W', w * w = 1) ∧
      CFSG.QuasithinUnique.Setup.X1.IsIrrOn Lb ∧ CFSG.IsQuasisimple ↥Lb ∧
      Eb ≠ ⊥ ∧ CFSG.Quasithin.IsElemAbelian2 Eb ∧ CFSG.Quasithin.IsQuadratic Eb ∧
      Eb ≤ Subgroup.normalizer (Lb : Set (MulAut W')) ∧
      Nat.card W' ≤ Nat.card Eb * Nat.card (CFSG.Quasithin.fixV Eb) ∧
      ∃ ψ : K →* ↥Lb, Function.Surjective ψ := by
  obtain ⟨B, hBA, hinv, hKU, hBU, hBbest, hBquad, hmove, hstrict⟩ :=
    exists_strictMin_moving K A hA2 hAK hKA hKnt hb
  set U := commOn ρ K ⊤ with hUdef
  have hKH : K ≤ K ⊔ B := le_sup_left
  have hBH : B ≤ K ⊔ B := le_sup_right
  have hHn : K ⊔ B ≤ Subgroup.normalizer (K : Set X) :=
    sup_le Subgroup.le_normalizer (hBA.trans hAK)
  have hK : ∀ h ∈ K ⊔ B, ∀ k ∈ K, h * k * h⁻¹ ∈ K :=
    fun h hh k hk => (Subgroup.mem_normalizer_iff.1 (hHn hh) k).1 hk
  have hmove' : ∃ b ∈ B, ∃ k ∈ K, ∃ u ∈ U, ρ b (ρ k u) ≠ ρ k (ρ b u) := by
    have : ¬ B ≤ cenOn ρ B U := hBU
    obtain ⟨b, hb, hbn⟩ := Set.not_subset.1 this
    obtain ⟨k, hk, u, hu, h⟩ := hmove b hb hbn
    exact ⟨b, hb, k, hk, u, hu, h⟩
  have hLG := isComp_imgBin (hU := hinv) hKH hKq hKU hK
  have hAG := isBestOffender_imgBin (hU := hinv) hBH hBbest hBU hstrict
  have hne := commutator_imgBin_ne_bot (hU := hinv) hKH hBH hmove'
  obtain ⟨hAn, hLL, ⟨sec⟩⟩ := CFSG.QuasithinUnique.Setup.Layer.Actor.irreducibleSectionProp
    (Multiplicative ↥U) (binU_sq U) _ _ _ hLG hAG hne
  refine ⟨sec.W, sec.commGroup, sec.finite, _, _, irrSection_sq (binU_sq U) sec, irrSection_isIrrOn sec,
    sec.lbar_quasisimple, sec.abar_ne_bot, sec.abar_elem, sec.abar_quadratic,
    irrSection_range_le_normalizer sec hAn, sec.abar_offender, ?_⟩
  let f : K →* ↥(imgBin ρ (K ⊔ B) U hinv K) :=
    (resBinOn (hU := hinv) hKH).codRestrict _ fun k => by
      rw [← range_resBinOn (hU := hinv) hKH]
      exact ⟨k, rfl⟩
  have hf : Function.Surjective f := by
    rintro ⟨y, hy⟩
    rw [← range_resBinOn (hU := hinv) hKH] at hy
    obtain ⟨k, rfl⟩ := hy
    exact ⟨k, rfl⟩
  exact ⟨((sec.τW.comp (Subgroup.inclusion le_sup_left)).rangeRestrict).comp f,
    (MonoidHom.rangeRestrict_surjective _).comp hf⟩

end CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
