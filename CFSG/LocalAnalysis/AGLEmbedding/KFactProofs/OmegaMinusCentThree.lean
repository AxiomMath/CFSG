module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.OmegaMinusCentModel
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.OmegaMinusCentRank

public section

namespace CFSG.AGLEmbedding.OmegaMinusCent

open CFSG.Open CFSG.ClassicalGroups.Orthogonal

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem exists_pullback_subgroup {L G : Type*} [Group L] [Group G] {H : Subgroup G} (e : L ≃* H)
    {Y : Subgroup G} (hYH : Y ≤ H) :
    ∃ Y' : Subgroup L, (∀ g : L, g ∈ Y' ↔ ((e g : H) : G) ∈ Y) ∧ Nat.card Y' = Nat.card Y := by
  set f : L →* G := H.subtype.comp e.toMonoidHom with hf
  have hinj : Function.Injective f := H.subtype_injective.comp e.injective
  have hrange : Y ≤ f.range := fun y hy =>
    ⟨e.symm ⟨y, hYH hy⟩, by simp [hf]⟩
  refine ⟨Y.comap f, fun g => Iff.rfl, ?_⟩
  have h1 : (Y.comap f).map f = Y := by
    rw [Subgroup.map_comap_eq]
    exact inf_eq_right.2 hrange
  calc Nat.card (Y.comap f) = Nat.card ((Y.comap f).map f) :=
        (Subgroup.card_map_of_injective hinj).symm
    _ = Nat.card Y := by rw [h1]

theorem omegaMinusThreeCent {L : Type} [Group L] {m : ℕ} (hm : 5 ≤ m)
    {d : TauCeti.ValidLieTypeIndex} (hd : IsOmegaMinusTwoIndex m d)
    (he : Nonempty (L ≃* CatGroup d)) {x : L} (hx : orderOf x = 3) :
    (∃ E : Subgroup L, E ≤ Subgroup.centralizer {x} ∧ IsElemAbelian 3 E ∧
        Nat.card E = 3 ^ 4) ∧
      ∃ Y : Subgroup L, Y ≤ Subgroup.centralizer {x} ∧ IsPGroup 3 Y ∧ Nat.card Y = 3 ^ 5 := by
  obtain ⟨e⟩ := omegaMinusModel hd he
  have hx' : x ^ 3 = 1 := hx ▸ pow_orderOf_eq_one x
  have hx3 : (((e x : elementaryGroup (minusForm m))) : MinusSpace m ≃ₗ[ZMod 2] MinusSpace m) ^ 3
      = 1 := by
    have h : (e x) ^ 3 = 1 := by rw [← map_pow, hx', map_one]
    simpa using congrArg Subtype.val h
  obtain ⟨P, P', hPP'⟩ := exists_orth_hypPair (m := m) (by omega)
  have key := exists_three_groups (nondegenerate_minusForm m) hm (finrank_minusSpace (by omega))
    (fun T hT => finrank_le_minusForm hT) hPP'
    (elementaryGroup_le_orthogonalGroup _ (e x).2) hx3
  have pull : ∀ n : ℕ, n ≤ 5 → ∃ Y : Subgroup L, Y ≤ Subgroup.centralizer {x} ∧
      (∀ g ∈ Y, g ^ 3 = 1) ∧ (∀ g ∈ Y, ∀ h ∈ Y, g * h = h * g) ∧ Nat.card Y = 3 ^ n := by
    intro n hn
    obtain ⟨Y, hYE, hYc, hY3, hYcomm, hcard⟩ := key n hn
    obtain ⟨Y', hmem, hcard'⟩ := exists_pullback_subgroup e hYE
    have hinj : ∀ a b : L, ((e a : elementaryGroup (minusForm m)) :
        MinusSpace m ≃ₗ[ZMod 2] MinusSpace m) = (e b : _) → a = b := fun a b h =>
      e.injective (Subtype.ext h)
    refine ⟨Y', fun g hg => ?_, fun g hg => ?_, fun g hg h hh => ?_, by rw [hcard', hcard]⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      have := Subgroup.mem_centralizer_iff.1 (hYc ((hmem g).1 hg)) _ rfl
      exact hinj _ _ (by simpa using this)
    · apply hinj
      simpa using hY3 _ ((hmem g).1 hg)
    · apply hinj
      simpa using hYcomm _ ((hmem g).1 hg) _ ((hmem h).1 hh)
  obtain ⟨E, hEc, hE3, hEcomm, hEcard⟩ := pull 4 (by norm_num)
  obtain ⟨Y, hYc, -, -, hYcard⟩ := pull 5 le_rfl
  refine ⟨⟨E, hEc, ⟨⟨⟨fun a b => Subtype.ext (hEcomm a.1 a.2 b.1 b.2)⟩⟩, hE3⟩, hEcard⟩,
    Y, hYc, IsPGroup.of_card hYcard, hYcard⟩

end CFSG.AGLEmbedding.OmegaMinusCent
