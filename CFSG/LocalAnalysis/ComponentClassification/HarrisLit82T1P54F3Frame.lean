module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54Defs
public import CFSG.Fischer.Classification.Recognition.PSU6

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P54.F3

open CFSG Subgroup Assembly.LowTwoRank
open scoped MatrixGroups

section Core

variable {X B : Type} [Group X] [Group B] [Finite X] [Finite B] {f : X →* B}

theorem map_subtype_pPrimeCore_eq (hk : ¬ 2 ∣ Nat.card f.ker) (L : Subgroup X) :
    (pPrimeCore 2 ↥L).map L.subtype =
      L ⊓ ((pPrimeCore 2 ↥(L.map f)).map (L.map f).subtype).comap f := by
  have hc := GSThmB.OddQuot.comap_pPrimeCore_of_surjective (f.subgroupMap L)
    (f.subgroupMap_surjective L) (GSThmB.OddQuot.not_two_dvd_card_ker_subgroupMap f hk L)
  ext x
  rw [mem_map, mem_inf, mem_comap, mem_map]
  constructor
  · rintro ⟨l, hl, rfl⟩
    have hl' : f.subgroupMap L l ∈ pPrimeCore 2 ↥(L.map f) := by
      rw [← hc] at hl
      exact hl
    exact ⟨l.2, f.subgroupMap L l, hl', rfl⟩
  · rintro ⟨hxL, y, hy, hyx⟩
    refine ⟨⟨x, hxL⟩, ?_, rfl⟩
    rw [← hc, mem_comap]
    have h1 : f.subgroupMap L ⟨x, hxL⟩ = y := Subtype.ext hyx.symm
    rw [h1]
    exact hy

theorem exists_lift_solvableTwoComponent (hf : Function.Surjective f) (hk : ¬ 2 ∣ Nat.card f.ker)
    {u : X} (hu : u * u = 1) {Y : Subgroup B}
    (hY : IsSolvableTwoComponentIn Y (centralizer {f u})) :
    ∃ J : Subgroup X, IsSolvableTwoComponentIn J (centralizer {u}) ∧ J.map f = Y ∧
      (∀ w ∈ centralizer ({u} : Set X), f w ∈ Y → w ∈ J) ∧
      Nonempty (↥J ⧸ pPrimeCore 2 ↥J ≃* ↥Y ⧸ pPrimeCore 2 ↥Y) := by
  have hCm := Frame.map_centralizer hf hk hu
  rw [← hCm] at hY
  obtain ⟨hYC, hYs, hYO, hYq⟩ := hY
  have hJC : centralizer ({u} : Set X) ⊓ Y.comap f ≤ centralizer {u} := inf_le_left
  have hJY : (centralizer ({u} : Set X) ⊓ Y.comap f).map f = Y := by
    refine le_antisymm ?_ fun y hy => ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact hx.2
    · obtain ⟨c, hc, rfl⟩ := hYC hy
      exact ⟨c, ⟨hc, hy⟩, rfl⟩
  have hJsub : (centralizer ({u} : Set X) ⊓ Y.comap f).subgroupOf (centralizer {u}) =
      (Y.subgroupOf ((centralizer ({u} : Set X)).map f)).comap
        (f.subgroupMap (centralizer {u})) := by
    ext x
    rw [mem_subgroupOf, mem_comap, mem_subgroupOf, mem_inf, mem_comap]
    exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
  have hJs : ((centralizer ({u} : Set X) ⊓ Y.comap f).subgroupOf (centralizer {u})).IsSubnormal :=
    hJsub ▸ hYs.comap _
  have hO : (pPrimeCore 2 ↥(centralizer ({u} : Set X) ⊓ Y.comap f)).map
      (centralizer ({u} : Set X) ⊓ Y.comap f).subtype =
        (pPrimeCore 2 ↥(centralizer ({u} : Set X))).map (centralizer ({u} : Set X)).subtype := by
    have hF : (pPrimeCore 2 ↥((centralizer ({u} : Set X) ⊓ Y.comap f).map f)).map
        ((centralizer ({u} : Set X) ⊓ Y.comap f).map f).subtype =
          (pPrimeCore 2 ↥Y).map Y.subtype :=
      congrArg (fun H : Subgroup B => (pPrimeCore 2 ↥H).map H.subtype) hJY
    have hOY : (pPrimeCore 2 ↥((centralizer ({u} : Set X)).map f)).map
        ((centralizer ({u} : Set X)).map f).subtype ≤ Y := hYO ▸ map_subtype_le _
    rw [map_subtype_pPrimeCore_eq hk, map_subtype_pPrimeCore_eq hk (centralizer {u}), hF, hYO]
    refine le_antisymm (inf_le_inf_right _ hJC) ?_
    rintro x ⟨hxC, hxO⟩
    exact ⟨⟨hxC, hOY hxO⟩, hxO⟩
  obtain ⟨⟨e₁⟩, -⟩ := Frame.nonempty_quot_equivs_of_map_eq hk hJY
  refine ⟨_, ⟨hJC, hJs, hO, ?_⟩, hJY, fun w hw hwY => ⟨hw, hwY⟩, ⟨e₁⟩⟩
  rcases hYq with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact .inl ⟨e₁.trans e⟩
  · exact .inr ⟨e₁.trans e⟩

end Core

@[expose] def Concl3 (X : Type) [Group X] (t : X) : Prop :=
  ∃ u : X, orderOf u = 2 ∧ u ∉ Open.fusionZStar X ∧ ∃ J₁ J₂ : Subgroup X,
    IsSolvableTwoComponentIn J₁ (centralizer {u}) ∧ u ∈ J₁ ∧
    Nonempty (↥J₁ ⧸ pPrimeCore 2 ↥J₁ ≃* SL(2, ZMod 3)) ∧
    ((IsTwoComponentIn J₂ (centralizer {u}) ∧ ∃ (τ' : StatedLieTag) (n' : ℕ),
        Blueprint.LieModel (↥J₂ ⧸ Open.fusionZStar ↥J₂) τ' n' 3 1) ∨
      (IsSolvableTwoComponentIn J₂ (centralizer {u}) ∧
        Nonempty (↥J₂ ⧸ pPrimeCore 2 ↥J₂ ≃* SL(2, ZMod 3)))) ∧
    J₁ ≠ J₂ ∧ (t ∈ J₂ ∨ t * u ∈ J₂)

section Lift

variable {X B : Type} [Group X] [Group B] [Finite X] [Finite B] {f : X →* B}

theorem Concl3.of_map (hf : Function.Surjective f) (hk : ¬ 2 ∣ Nat.card f.ker) {t : X}
    (ht : t * t = 1) (htZ : f t ∈ center B) (h : Concl3 B (f t)) : Concl3 X t := by
  obtain ⟨b, hb2, hbZ, Y₁, Y₂, hY₁, hbY, ⟨e₁⟩, hY₂, hne, htY⟩ := h
  obtain ⟨u, hu2, rfl, hut⟩ := Frame.exists_involution_lift_commute hf hk ht htZ hb2
  have huu : u * u = 1 := by rw [← sq, ← hu2, pow_orderOf_eq_one]
  have htu : t ∈ centralizer ({u} : Set X) := mem_centralizer_singleton_iff.mpr hut.symm
  have huc : u ∈ centralizer ({u} : Set X) := mem_centralizer_singleton_iff.mpr rfl
  have htu2 : t * u * (t * u) = 1 := by
    calc t * u * (t * u) = t * (u * t) * u := by group
      _ = t * (t * u) * u := by rw [hut]
      _ = 1 := by rw [← mul_assoc, ht, one_mul, huu]
  obtain ⟨J₁, hJ₁, hJY₁, hmem₁, ⟨q₁⟩⟩ := exists_lift_solvableTwoComponent hf hk huu hY₁
  have huZ : u ∉ Open.fusionZStar X := fun h => hbZ ((Frame.mem_fusionZStar_iff_map hf hk).mp h)
  rcases hY₂ with ⟨hY₂, τ', n', hlie⟩ | ⟨hY₂, ⟨e₂⟩⟩
  · obtain ⟨J₂, hJ₂, hJY₂, hmem₂, -, ⟨z₂⟩⟩ := Frame.exists_lift_twoComponent hf hk huu hY₂
    refine ⟨u, hu2, huZ, J₁, J₂, hJ₁, hmem₁ u huc hbY, ⟨q₁.trans e₁⟩,
      .inl ⟨hJ₂, τ', n', GSThmB.OddQuot.lieModel_of_equiv z₂.symm hlie⟩,
      fun h => hne (by rw [← hJY₁, ← hJY₂, h]), ?_⟩
    rcases htY with h1 | h1
    · exact .inl (hmem₂ t htu (exists_orderOf_eq_two_pow ht) h1)
    · refine .inr (hmem₂ (t * u) (mul_mem htu huc) (exists_orderOf_eq_two_pow htu2) ?_)
      rw [map_mul]
      exact h1
  · obtain ⟨J₂, hJ₂, hJY₂, hmem₂, ⟨q₂⟩⟩ := exists_lift_solvableTwoComponent hf hk huu hY₂
    refine ⟨u, hu2, huZ, J₁, J₂, hJ₁, hmem₁ u huc hbY, ⟨q₁.trans e₁⟩,
      .inr ⟨hJ₂, ⟨q₂.trans e₂⟩⟩, fun h => hne (by rw [← hJY₁, ← hJY₂, h]), ?_⟩
    rcases htY with h1 | h1
    · exact .inl (hmem₂ t htu h1)
    · refine .inr (hmem₂ (t * u) (mul_mem htu huc) ?_)
      rw [map_mul]
      exact h1

end Lift

end CFSG.ComponentClassification.HarrisLit.T1.P54.F3
