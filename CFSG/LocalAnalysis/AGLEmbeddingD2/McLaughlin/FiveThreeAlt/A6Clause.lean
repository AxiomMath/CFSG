module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.FiveThreeAlt.A6Module
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.Bridge

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.FiveThreeAlt

open CFSG CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThree.FFModules CFSG.AGLEmbedding
  CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open scoped commutatorElement

variable {X : Type} [Group X] {T : Subgroup X} (hV : IsElemAbelian 2 (gnV T))

@[expose] def elt (w : Additive (IntMod (gnV T) hV)) : X := (Additive.toMul w).val

theorem elt_mem (w : Additive (IntMod (gnV T) hV)) : elt hV w ∈ gnV T :=
  (Additive.toMul w).val_mem

theorem elt_injective : Function.Injective (elt hV) := fun _ _ h =>
  Additive.toMul.injective (IntMod.val_injective h)

@[simp] theorem elt_add (a b : Additive (IntMod (gnV T) hV)) :
    elt hV (a + b) = elt hV a * elt hV b := rfl

@[simp] theorem elt_zero : elt hV (0 : Additive (IntMod (gnV T) hV)) = 1 := rfl

@[simp] theorem elt_neg (a : Additive (IntMod (gnV T) hV)) : elt hV (-a) = (elt hV a)⁻¹ := rfl

theorem elt_sub (a b : Additive (IntMod (gnV T) hV)) :
    elt hV (a - b) = elt hV a * (elt hV b)⁻¹ := by
  rw [sub_eq_add_neg, elt_add, elt_neg]

theorem exists_elt {v : X} (hv : v ∈ gnV T) : ∃ w, elt hV w = v :=
  ⟨Additive.ofMul (IntMod.mk hV ⟨v, hv⟩), rfl⟩

variable [Module (ZMod 2) (Additive (IntMod (gnV T) hV))]

theorem elt_gnRep (g : X) (w : Additive (IntMod (gnV T) hV)) :
    elt hV (gnRep hV (QuotientGroup.mk g) w) = g * elt hV w * g⁻¹ :=
  gnConj_apply_val hV g _

@[expose] def subOf (N : Submodule (ZMod 2) (Additive (IntMod (gnV T) hV))) : Subgroup X where
  carrier := elt hV '' N
  one_mem' := ⟨0, N.zero_mem, rfl⟩
  mul_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a + b, N.add_mem ha hb, rfl⟩
  inv_mem' := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨-a, N.neg_mem ha, rfl⟩

theorem mem_subOf {N : Submodule (ZMod 2) (Additive (IntMod (gnV T) hV))} {g : X} :
    g ∈ subOf hV N ↔ ∃ w ∈ N, elt hV w = g := Iff.rfl

theorem elt_mem_subOf {N : Submodule (ZMod 2) (Additive (IntMod (gnV T) hV))}
    {w : Additive (IntMod (gnV T) hV)} : elt hV w ∈ subOf hV N ↔ w ∈ N := by
  constructor
  · rintro ⟨w', hw', h⟩
    rwa [← elt_injective hV h]
  · intro h
    exact ⟨w, h, rfl⟩

theorem subOf_le_gnV (N : Submodule (ZMod 2) (Additive (IntMod (gnV T) hV))) :
    subOf hV N ≤ gnV T := by
  rintro _ ⟨w, -, rfl⟩
  exact elt_mem hV w

theorem subOf_le_subOf_iff {N₁ N₂ : Submodule (ZMod 2) (Additive (IntMod (gnV T) hV))} :
    subOf hV N₁ ≤ subOf hV N₂ ↔ N₁ ≤ N₂ := by
  constructor
  · intro h w hw
    exact (elt_mem_subOf hV).mp (h ((elt_mem_subOf hV).mpr hw))
  · rintro h _ ⟨w, hw, rfl⟩
    exact ⟨w, h hw, rfl⟩

theorem card_subOf (N : Submodule (ZMod 2) (Additive (IntMod (gnV T) hV))) :
    Nat.card (subOf hV N) = Nat.card N := by
  change Nat.card ↥(elt hV '' (N : Set (Additive (IntMod (gnV T) hV)))) = _
  rw [Nat.card_image_of_injective (elt_injective hV)]
  rfl

theorem zmod_two_eq (c : ZMod 2) : c = 0 ∨ c = 1 := by
  revert c
  decide

@[expose] def modOf (W' : Subgroup X) : Submodule (ZMod 2) (Additive (IntMod (gnV T) hV)) where
  carrier := {w | elt hV w ∈ W'}
  add_mem' := by
    intro a b ha hb
    change elt hV (a + b) ∈ W'
    rw [elt_add]
    exact W'.mul_mem ha hb
  zero_mem' := by
    change elt hV 0 ∈ W'
    rw [elt_zero]
    exact W'.one_mem
  smul_mem' := by
    intro c w hw
    rcases zmod_two_eq c with rfl | rfl
    · change elt hV ((0 : ZMod 2) • w) ∈ W'
      rw [zero_smul, elt_zero]
      exact W'.one_mem
    · change elt hV ((1 : ZMod 2) • w) ∈ W'
      rw [one_smul]
      exact hw

theorem subOf_modOf {W' : Subgroup X} (h : W' ≤ gnV T) : subOf hV (modOf hV W') = W' := by
  ext g
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact hw
  · intro hg
    obtain ⟨w, rfl⟩ := exists_elt hV (h hg)
    exact ⟨w, hg, rfl⟩

theorem modOf_subOf (N : Submodule (ZMod 2) (Additive (IntMod (gnV T) hV))) :
    modOf hV (subOf hV N) = N := by
  ext w
  exact elt_mem_subOf hV

theorem commutator_gnV_le (L' : Subgroup X) : ⁅gnV T, L'⁆ ≤ gnV T :=
  Subgroup.commutator_le_left _ _

theorem subOf_commOn (L : Subgroup (X ⧸ gnC T)) :
    subOf hV (commOn (gnRep hV) L ⊤) = ⁅gnV T, L.comap (QuotientGroup.mk' (gnC T))⁆ := by
  apply le_antisymm
  · have hle : commOn (gnRep hV) L ⊤ ≤ modOf hV ⁅gnV T, L.comap (QuotientGroup.mk' (gnC T))⁆ := by
      rw [commOn, Submodule.span_le]
      rintro _ ⟨a, ha, u, -, rfl⟩
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective a
      change elt hV (gnRep hV (QuotientGroup.mk g) u - u) ∈
        ⁅gnV T, L.comap (QuotientGroup.mk' (gnC T))⁆
      rw [elt_sub, elt_gnRep, Subgroup.commutator_comm]
      have hc := Subgroup.commutator_mem_commutator
        (show g ∈ L.comap (QuotientGroup.mk' (gnC T)) from ha) (elt_mem hV u)
      rwa [commutatorElement_def] at hc
    calc subOf hV (commOn (gnRep hV) L ⊤)
        ≤ subOf hV (modOf hV ⁅gnV T, L.comap (QuotientGroup.mk' (gnC T))⁆) :=
          (subOf_le_subOf_iff hV).mpr hle
      _ = ⁅gnV T, L.comap (QuotientGroup.mk' (gnC T))⁆ := subOf_modOf hV (commutator_gnV_le _)
  · rw [Subgroup.commutator_le]
    intro v hv g hg
    obtain ⟨w, rfl⟩ := exists_elt hV hv
    refine ⟨-(gnRep hV (QuotientGroup.mk g) w - w), Submodule.neg_mem _
      (Submodule.subset_span ⟨QuotientGroup.mk g, hg, w, Submodule.mem_top, rfl⟩), ?_⟩
    rw [elt_neg, elt_sub, elt_gnRep, commutatorElement_def]
    group

theorem subOf_fixOn (L : Subgroup (X ⧸ gnC T))
    (N : Submodule (ZMod 2) (Additive (IntMod (gnV T) hV))) :
    subOf hV (fixOn (gnRep hV) L N) =
      subOf hV N ⊓ Subgroup.centralizer (L.comap (QuotientGroup.mk' (gnC T)) : Set X) := by
  ext g
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨⟨w, (mem_fixOn.mp hw).1, rfl⟩, ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
    have h1 := (mem_fixOn.mp hw).2 (QuotientGroup.mk h) hh
    have e := congrArg (elt hV) h1
    rw [elt_gnRep] at e
    calc h * elt hV w = h * elt hV w * h⁻¹ * h := by group
      _ = elt hV w * h := by rw [e]
  · rintro ⟨⟨w, hw, rfl⟩, hc⟩
    refine ⟨w, mem_fixOn.mpr ⟨hw, fun l hl => ?_⟩, rfl⟩
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective l
    apply elt_injective hV
    rw [elt_gnRep]
    have h1 := Subgroup.mem_centralizer_iff.mp hc h hl
    rw [h1]
    group

theorem isInvariant_modOf (L : Subgroup (X ⧸ gnC T)) {W' : Subgroup X}
    (hW' : L.comap (QuotientGroup.mk' (gnC T)) ≤ Subgroup.normalizer (W' : Set X)) :
    CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant (gnRep hV) L (modOf hV W') := by
  intro l hl w hw
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective l
  change elt hV (gnRep hV (QuotientGroup.mk h) w) ∈ W'
  rw [elt_gnRep]
  exact (Subgroup.mem_normalizer_iff.mp (hW' hl) _).mp hw

theorem a6_clause_of_offender [Finite X] (L : Subgroup (X ⧸ gnC T))
    (eL : ↥L ≃* alternatingGroup (Fin 6)) {A : Subgroup X} (hA : IsMaxElemAbelian T A)
    (hAb : IsBestOffender (gnRep hV) (A.map (QuotientGroup.mk' (gnC T))))
    (hAN : A.map (QuotientGroup.mk' (gnC T)) ≤ Subgroup.normalizer (L : Set (X ⧸ gnC T)))
    (hLA : ⁅L, A.map (QuotientGroup.mk' (gnC T))⁆ = L) :
    HasIrreducibleCommutatorQuotient (L.comap (QuotientGroup.mk' (gnC T))) (gnV T) ∧
      (⁅gnV T, L.comap (QuotientGroup.mk' (gnC T))⁆ ⊓
          Subgroup.centralizer (L.comap (QuotientGroup.mk' (gnC T)) : Set X)).relIndex
        ⁅gnV T, L.comap (QuotientGroup.mk' (gnC T))⁆ = 2 ^ 4 := by
  classical
  set ρ := gnRep hV with hρ
  set L' := L.comap (QuotientGroup.mk' (gnC T)) with hL'
  have hinj : Function.Injective ρ := gnRep_injective hV
  have hA2 := isElementaryAbelian_map_mk hA
  have hfaith : ∀ a ∈ A.map (QuotientGroup.mk' (gnC T)), (∀ v, ρ a v = v) → a = 1 :=
    fun a _ h => hinj (by rw [map_one]; exact LinearMap.ext h)
  have hb : IsBestOffenderOn ρ (A.map (QuotientGroup.mk' (gnC T))) ⊤ :=
    (isBestOffender_iff_on ρ _ hfaith).mp ⟨hA2, hAb⟩
  obtain ⟨hirr, hdim⟩ := a6_commOn_quot ρ hinj eL hA2 hAN hLA hb
  set U := commOn ρ L ⊤ with hU
  set C := fixOn ρ L U with hC
  have hUs : subOf hV U = ⁅gnV T, L'⁆ := subOf_commOn hV L
  have hCs : subOf hV C = ⁅gnV T, L'⁆ ⊓ Subgroup.centralizer (L' : Set X) := by
    rw [hC, subOf_fixOn, hUs]
  have hCU : C ≤ U := fun v hv => (mem_fixOn.mp hv).1
  have hcard : ∀ N : Submodule (ZMod 2) (Additive (IntMod (gnV T) hV)),
      Nat.card N = 2 ^ Module.finrank (ZMod 2) N := by
    intro N
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  refine ⟨⟨?_, fun W' hW1 hW2 hW3 => ?_⟩, ?_⟩
  · rw [← hCs, ← hUs]
    refine lt_of_le_of_ne ((subOf_le_subOf_iff hV).mpr hCU) fun h => ?_
    have h1 := congrArg (fun H : Subgroup X => Nat.card H) h
    rw [card_subOf, card_subOf, hcard, hcard, hdim] at h1
    have h2 := Nat.pow_right_injective (le_refl 2) h1
    omega
  · rw [← hCs] at hW1
    rw [← hUs] at hW2
    rw [← hCs, ← hUs]
    have hW'V : W' ≤ gnV T := hW2.trans (subOf_le_gnV hV U)
    have hinv := isInvariant_modOf hV L hW3
    have h1 : C ≤ modOf hV W' := by
      rw [← modOf_subOf hV C]
      intro w hw
      exact hW1 hw
    have h2 : modOf hV W' ≤ U := by
      rw [← modOf_subOf hV U]
      intro w hw
      exact hW2 hw
    rcases hirr _ hinv h1 h2 with h | h
    · left
      rw [← h, subOf_modOf hV hW'V]
    · right
      rw [← h, subOf_modOf hV hW'V]
  · rw [← hCs, ← hUs]
    have hle : subOf hV C ≤ subOf hV U := (subOf_le_subOf_iff hV).mpr hCU
    have h1 := Subgroup.relIndex_mul_card (subOf hV C) (subOf hV U)
    rw [inf_eq_left.mpr hle, card_subOf, card_subOf, hcard, hcard, hdim, pow_add] at h1
    exact Nat.eq_of_mul_eq_mul_right (pow_pos (by norm_num : 0 < 2) _) (h1.trans (mul_comm _ _))

end CFSG.AGLEmbeddingD2.McLaughlin.FiveThreeAlt
