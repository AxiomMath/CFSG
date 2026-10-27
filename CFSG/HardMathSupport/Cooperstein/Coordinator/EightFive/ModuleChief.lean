module

public import CFSG.Quasithin.Background.FixVLattice
public import CFSG.Quasithin.Background.B1Restrict

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive

open CFSG.Quasithin

variable {V : Type*} [CommGroup V]

@[expose] def IsChiefFac (H : Subgroup (MulAut V)) (Y₀ Y₁ : Subgroup V) : Prop :=
  Y₀ < Y₁ ∧ H ≤ stabSub Y₀ ∧ H ≤ stabSub Y₁ ∧
    ∀ Z : Subgroup V, H ≤ stabSub Z → Y₀ ≤ Z → Z ≤ Y₁ → Z = Y₀ ∨ Z = Y₁

@[expose] def IsCentralSec (L : Subgroup (MulAut V)) (Y₀ Y₁ : Subgroup V) : Prop :=
  ∀ l ∈ L, ∀ y ∈ Y₁, l y * y⁻¹ ∈ Y₀

theorem IsChiefFac.lt {H : Subgroup (MulAut V)} {Y₀ Y₁ : Subgroup V} (h : IsChiefFac H Y₀ Y₁) :
    Y₀ < Y₁ :=
  h.1

theorem IsChiefFac.le {H : Subgroup (MulAut V)} {Y₀ Y₁ : Subgroup V} (h : IsChiefFac H Y₀ Y₁) :
    Y₀ ≤ Y₁ :=
  h.1.le

theorem IsChiefFac.stab₀ {H : Subgroup (MulAut V)} {Y₀ Y₁ : Subgroup V} (h : IsChiefFac H Y₀ Y₁) :
    H ≤ stabSub Y₀ :=
  h.2.1

theorem IsChiefFac.stab₁ {H : Subgroup (MulAut V)} {Y₀ Y₁ : Subgroup V} (h : IsChiefFac H Y₀ Y₁) :
    H ≤ stabSub Y₁ :=
  h.2.2.1

theorem IsChiefFac.eq_or_eq {H : Subgroup (MulAut V)} {Y₀ Y₁ : Subgroup V}
    (h : IsChiefFac H Y₀ Y₁) {Z : Subgroup V} (hZ : H ≤ stabSub Z) (h₀ : Y₀ ≤ Z) (h₁ : Z ≤ Y₁) :
    Z = Y₀ ∨ Z = Y₁ :=
  h.2.2.2 Z hZ h₀ h₁

theorem IsChiefFac.eq_or_eq_of_invariant {H : Subgroup (MulAut V)} {Y₀ Y₁ : Subgroup V}
    (h : IsChiefFac H Y₀ Y₁) {J : Subgroup V} (hJ : ∀ x ∈ H, ∀ w ∈ J, x w ∈ J) (h₀ : Y₀ ≤ J)
    (h₁ : J ≤ Y₁) : J = Y₀ ∨ J = Y₁ :=
  h.eq_or_eq (B1.le_stabSub_of_invariant hJ) h₀ h₁

theorem isCentralSec_iff_commSub_le {L : Subgroup (MulAut V)} {Y₀ Y₁ : Subgroup V} :
    IsCentralSec L Y₀ Y₁ ↔ commSub Y₁ L ≤ Y₀ := by
  constructor
  · intro h
    rw [commSub, Subgroup.closure_le]
    rintro _ ⟨l, hl, y, hy, rfl⟩
    exact h l hl y hy
  · intro h l hl y hy
    exact h (Subgroup.subset_closure ⟨l, hl, y, hy, rfl⟩)

theorem isCentralSec_bot_iff {L : Subgroup (MulAut V)} {Y : Subgroup V} :
    IsCentralSec L ⊥ Y ↔ Y ≤ fixV L := by
  constructor
  · intro h y hy l hl
    have := h l hl y hy
    rwa [Subgroup.mem_bot, mul_inv_eq_one] at this
  · intro h l hl y hy
    rw [h hy l hl, mul_inv_cancel]
    exact Subgroup.one_mem _

theorem mul_inv_mem_of_perfect {L : Subgroup (MulAut V)} (hL : commutator ↥L = ⊤) {S T : Set V}
    {Z : Subgroup V} (hST : ∀ l ∈ L, ∀ s ∈ S, l s * s⁻¹ ∈ T)
    (hTZ : ∀ l ∈ L, ∀ t ∈ T, l t * t⁻¹ ∈ Z) : ∀ l ∈ L, ∀ s ∈ S, l s * s⁻¹ ∈ Z := by
  let δ : ↥L →* (↥S → V ⧸ Z) :=
    { toFun := fun l s => (((l : MulAut V) s * (s : V)⁻¹ : V) : V ⧸ Z)
      map_one' := by
        funext s
        change (((1 : MulAut V) (s : V) * (s : V)⁻¹ : V) : V ⧸ Z) = 1
        rw [MulAut.one_apply, mul_inv_cancel, QuotientGroup.mk_one]
      map_mul' := fun a b => by
        funext s
        change (((a : MulAut V) ((b : MulAut V) (s : V)) * (s : V)⁻¹ : V) : V ⧸ Z) =
          (((a : MulAut V) s * (s : V)⁻¹ : V) : V ⧸ Z) * (((b : MulAut V) s * (s : V)⁻¹ : V) : V ⧸ Z)
        set t : V := (b : MulAut V) s * (s : V)⁻¹ with ht
        have hbs : (b : MulAut V) s = t * s := (inv_mul_cancel_right _ _).symm
        have h1 : (a : MulAut V) ((b : MulAut V) s) * (s : V)⁻¹ =
            (a : MulAut V) t * ((a : MulAut V) s * (s : V)⁻¹) := by
          rw [hbs, map_mul, mul_assoc]
        have h2 : (((a : MulAut V) t : V) : V ⧸ Z) = ((t : V) : V ⧸ Z) := by
          rw [QuotientGroup.eq]
          have h3 := Z.inv_mem (hTZ a a.2 t (hST b b.2 s s.2))
          rwa [mul_inv_rev, inv_inv, mul_comm] at h3
        rw [h1, QuotientGroup.mk_mul, h2, mul_comm] }
  intro l hl s hs
  have hc : (⟨l, hl⟩ : ↥L) ∈ commutator ↥L := by
    rw [hL]
    exact Subgroup.mem_top _
  have hmem := Abelianization.commutator_subset_ker δ hc
  have := congrFun (MonoidHom.mem_ker.1 hmem) ⟨s, hs⟩
  exact (QuotientGroup.eq_one_iff _).1 this

theorem IsCentralSec.trans_of_perfect {L : Subgroup (MulAut V)} (hL : commutator ↥L = ⊤)
    {Y₀ Y₁ Y₂ : Subgroup V} (h₁ : IsCentralSec L Y₀ Y₁) (h₂ : IsCentralSec L Y₁ Y₂) :
    IsCentralSec L Y₀ Y₂ :=
  mul_inv_mem_of_perfect hL (S := Y₂) (T := Y₁) h₂ h₁

theorem le_fixV_of_perfect {L : Subgroup (MulAut V)} (hL : commutator ↥L = ⊤)
    {Y₀ Y₁ : Subgroup V} (h₀ : Y₀ ≤ fixV L) (h₁ : IsCentralSec L Y₀ Y₁) : Y₁ ≤ fixV L :=
  isCentralSec_bot_iff.1 ((isCentralSec_bot_iff.2 h₀).trans_of_perfect hL h₁)

theorem commSub_commV_of_perfect {L : Subgroup (MulAut V)} (hL : commutator ↥L = ⊤) :
    commSub (commV L) L = commV L := by
  refine le_antisymm ?_ ?_
  · rw [commV_eq_commSub]
    exact commSub_mono le_top le_rfl
  · rw [commV, Subgroup.closure_le]
    rintro _ ⟨l, hl, v, rfl⟩
    exact mul_inv_mem_of_perfect hL (S := Set.univ) (T := commV L) (Z := commSub (commV L) L)
      (fun l hl s _ => Subgroup.subset_closure ⟨l, hl, s, rfl⟩)
      (fun l hl t ht => Subgroup.subset_closure ⟨l, hl, t, ht, rfl⟩) l hl v (Set.mem_univ v)

theorem not_le_fixV_commV_of_perfect {L : Subgroup (MulAut V)} (hL : commutator ↥L = ⊤)
    (hV : commV L ≠ ⊥) : ¬ commV L ≤ fixV L := by
  intro h
  apply hV
  rw [← commSub_commV_of_perfect hL]
  exact commSub_eq_bot_iff.2 h

theorem apply_mem_commV_of_mem_normalizer {L : Subgroup (MulAut V)} {h : MulAut V}
    (hh : h ∈ Subgroup.normalizer (L : Set (MulAut V))) {u : V} (hu : u ∈ commV L) :
    h u ∈ commV L :=
  CFSG.Quasithin.commV_apply_mem_of_mem_normalizer hh hu

theorem le_stabSub_commV {H L : Subgroup (MulAut V)}
    (hN : H ≤ Subgroup.normalizer (L : Set (MulAut V))) : H ≤ stabSub (commV L) :=
  B1.le_stabSub_of_invariant fun _ hh _ hu => apply_mem_commV_of_mem_normalizer (hN hh) hu

theorem le_stabSub_fixV {H L : Subgroup (MulAut V)}
    (hN : H ≤ Subgroup.normalizer (L : Set (MulAut V))) : H ≤ stabSub (fixV L) :=
  CFSG.Quasithin.FixVLat.le_stabSub_fixV_of_le_normalizer hN

theorem le_stabSub_inf {H : Subgroup (MulAut V)} {Y Y' : Subgroup V} (h : H ≤ stabSub Y)
    (h' : H ≤ stabSub Y') : H ≤ stabSub (Y ⊓ Y') := fun g hg u => by
  simp only [Subgroup.mem_inf]
  rw [h hg u, h' hg u]

theorem le_stabSub_bot (H : Subgroup (MulAut V)) : H ≤ stabSub (⊥ : Subgroup V) := fun g _ u => by
  simp only [Subgroup.mem_bot]
  exact ⟨fun h => g.injective (h.trans (map_one g).symm), fun h => by rw [h, map_one]⟩

section Finite

variable [Finite V]

theorem finite_subgroup : Finite (Subgroup V) :=
  Finite.of_injective (fun Y : Subgroup V => (Y : Set V)) SetLike.coe_injective

theorem exists_isChiefFac_of_lt {H : Subgroup (MulAut V)} {Y' Y₁ : Subgroup V} (h : Y' < Y₁)
    (hY' : H ≤ stabSub Y') (hY₁ : H ≤ stabSub Y₁) : ∃ Y₀, Y' ≤ Y₀ ∧ IsChiefFac H Y₀ Y₁ := by
  have := finite_subgroup (V := V)
  obtain ⟨Y₀, ⟨hY₀, hY'₀, hY₀₁⟩, hmax⟩ := Set.exists_max_image
    {Z : Subgroup V | H ≤ stabSub Z ∧ Y' ≤ Z ∧ Z < Y₁} (fun Z => Nat.card Z) (Set.toFinite _)
    ⟨Y', hY', le_rfl, h⟩
  refine ⟨Y₀, hY'₀, hY₀₁, hY₀, hY₁, fun Z hZ h₀ h₁ => ?_⟩
  by_cases hZ₁ : Z = Y₁
  · exact Or.inr hZ₁
  · left
    have hcard := hmax Z ⟨hZ, hY'₀.trans h₀, lt_of_le_of_ne h₁ hZ₁⟩
    exact (Subgroup.eq_of_le_of_card_ge h₀ hcard).symm

theorem exists_isChiefFac_of_perfect {H L : Subgroup (MulAut V)} (hL : commutator ↥L = ⊤)
    {Y : Subgroup V} (hY : H ≤ stabSub Y) (hYL : ¬ Y ≤ fixV L) :
    ∃ Y₀ Y₁ : Subgroup V, IsChiefFac H Y₀ Y₁ ∧ Y₁ ≤ Y ∧ ¬ IsCentralSec L Y₀ Y₁ := by
  have := finite_subgroup (V := V)
  obtain ⟨Y₁, ⟨hY₁, hY₁Y, hY₁L⟩, hmin⟩ := Set.exists_min_image
    {Z : Subgroup V | H ≤ stabSub Z ∧ Z ≤ Y ∧ ¬ Z ≤ fixV L} (fun Z => Nat.card Z)
    (Set.toFinite _) ⟨Y, hY, le_rfl, hYL⟩
  have hbot : ⊥ < Y₁ := by
    refine bot_lt_iff_ne_bot.2 fun h => hY₁L ?_
    rw [h]
    exact bot_le
  obtain ⟨Y₀, -, hchief⟩ := exists_isChiefFac_of_lt hbot (le_stabSub_bot H) hY₁
  refine ⟨Y₀, Y₁, hchief, hY₁Y, fun hc => hY₁L (le_fixV_of_perfect hL ?_ hc)⟩
  by_contra hY₀L
  have hcard := hmin Y₀ ⟨hchief.stab₀, hchief.le.trans hY₁Y, hY₀L⟩
  exact hchief.lt.ne (Subgroup.eq_of_le_of_card_ge hchief.le hcard)

end Finite

end CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive
