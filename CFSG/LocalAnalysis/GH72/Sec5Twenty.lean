module

public import CFSG.LocalAnalysis.GH72.Sec5DBasic
public import CFSG.LocalAnalysis.GH72.Sec2

public section

namespace CFSG.GH72

open Subgroup G5d

namespace Sec4Setting

variable {G : Type} [Group G] [Finite G] (𝔖 : Sec4Setting G) {A : Subgroup G}
  (hAS : A ≤ 𝔖.S) (hA : IsE16 A) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)

include hp hp2 in
private theorem odd_card_of_isPGroup' {P : Subgroup G} (hPp : IsPGroup p P) :
    Odd (Nat.card P) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := hPp.exists_card_eq
  rw [hn]
  exact (hp.odd_of_ne_two hp2).pow

omit [Finite G] in
private theorem le_C_of_le_centralizer {P : Subgroup G} (hc : A ≤ centralizer (P : Set G))
    {a : G} (ha : a ∈ A) : P ≤ C a := by
  intro g hg
  rw [mem_centralizer_singleton_iff]
  exact mem_centralizer_iff.mp (hc ha) g hg

private theorem le_O_C_of_mem_X {P : Subgroup G} (hc : A ≤ centralizer (P : Set G))
    (hPgen : XYGenerated (𝔖.X A) (𝔖.Y A) P)
    (h410 : ∀ x ∈ 𝔖.X A, x ≠ 1 → ∀ a ∈ A, a ∉ 𝔖.Y A → O (C x) ⊓ C a ≤ O (C a))
    {x : G} (hx : x ∈ 𝔖.X A) (hx1 : x ≠ 1) : P ≤ O (C x) := by
  rw [hPgen]
  refine xySupOf_le (X₀ := 𝔖.X A) (Y₀ := 𝔖.Y A) fun x' hx' hx'1 y _ _ => ?_
  by_cases hxx : x' = x
  · subst hxx
    exact inf_le_left.trans inf_le_right
  · refine le_trans ?_ (h410 x' hx' hx'1 x hx.1 (not_mem_Y_of_mem_X 𝔖 hx hx1))
    exact le_inf (inf_le_left.trans inf_le_right)
      (inf_le_left.trans (inf_le_left.trans (le_C_of_le_centralizer hc hx.1)))

private theorem le_O_C_of_mem_Y {P : Subgroup G} (hc : A ≤ centralizer (P : Set G))
    (hPgen : XYGenerated (𝔖.X A) (𝔖.Y A) P)
    (h410 : ∀ y ∈ 𝔖.Y A, y ≠ 1 → ∀ a ∈ A, a ∉ 𝔖.X A → O (C y) ⊓ C a ≤ O (C a))
    {y : G} (hy : y ∈ 𝔖.Y A) (hy1 : y ≠ 1) : P ≤ O (C y) := by
  rw [hPgen]
  refine xySupOf_le (X₀ := 𝔖.X A) (Y₀ := 𝔖.Y A) fun x _ _ y' hy' hy'1 => ?_
  by_cases hyy : y' = y
  · subst hyy
    exact inf_le_right
  · refine le_trans ?_ (h410 y' hy' hy'1 y hy.1 (not_mem_X_of_mem_Y 𝔖 hy hy1))
    exact le_inf inf_le_right (inf_le_left.trans (inf_le_left.trans (le_C_of_le_centralizer hc hy.1)))

include hAS hA hp hp2 in
theorem prop_5_20_of
    (h54 : (∃ D : Subgroup G, IsPGroup p D ∧ A ≤ normalizer (D : Set G) ∧
      ¬ A ≤ centralizer (D : Set G) ∧ XYGenerated (𝔖.X A) (𝔖.Y A) D) →
      ∃ H, 𝔖.IsCovering p A H)
    (h46 : ∀ P₁ P₂ : Subgroup G, IsMaxInvIn p A ⊤ P₁ → IsMaxInvIn p A ⊤ P₂ →
      ∃ g ∈ normalizer (A : Set G), P₁.map (MulAut.conj g).toMonoidHom = P₂)
    (h410 : (∀ x ∈ 𝔖.X A, x ≠ 1 → ∀ a ∈ A, a ∉ 𝔖.Y A → O (C x) ⊓ C a ≤ O (C a)) ∧
      (∀ y ∈ 𝔖.Y A, y ≠ 1 → ∀ a ∈ A, a ∉ 𝔖.X A → O (C y) ⊓ C a ≤ O (C a)))
    (h414 : ∀ H : Subgroup G, H ≠ ⊤ → A ≤ H → Covers H (𝔖.M₀ A) (O (𝔖.M A)) →
      Covers H (𝔖.N₀ A) (O (𝔖.N A)) → ∀ D : Subgroup G, D ≤ H → Odd (Nat.card D) →
      A ≤ normalizer (D : Set G) → (XYGenerated (𝔖.X A) (𝔖.Y A) D ↔ D ≤ O H))
    (P : Subgroup G) (hPp : IsPGroup p P) (hAP : A ≤ normalizer (P : Set G))
    (hPgen : XYGenerated (𝔖.X A) (𝔖.Y A) P) (Q : Subgroup G) (hQP : Q ≤ P)
    (hAQ : A ≤ normalizer (Q : Set G)) : XYGenerated (𝔖.X A) (𝔖.Y A) Q := by
  have hQodd : Odd (Nat.card Q) := odd_card_of_isPGroup' hp hp2 (hPp.to_le hQP)
  by_cases hc : A ≤ centralizer (P : Set G)
  ·
    refine le_antisymm ?_ (xySupOf_le (X₀ := 𝔖.X A) (Y₀ := 𝔖.Y A) fun _ _ _ _ _ _ =>
      inf_le_left.trans inf_le_left)
    by_cases hXY : ∃ x ∈ 𝔖.X A, x ≠ 1 ∧ ∃ y ∈ 𝔖.Y A, y ≠ 1
    · obtain ⟨x, hx, hx1, y, hy, hy1⟩ := hXY
      refine le_trans ?_ (le_xySupOf (X₀ := 𝔖.X A) (Y₀ := 𝔖.Y A)
        (f := fun x y => Q ⊓ O (C x) ⊓ O (C y)) hx hx1 hy hy1)
      exact le_inf (le_inf le_rfl (hQP.trans (𝔖.le_O_C_of_mem_X hc hPgen h410.1 hx hx1)))
        (hQP.trans (𝔖.le_O_C_of_mem_Y hc hPgen h410.2 hy hy1))
    ·
      have hP1 : P = ⊥ := by
        rw [hPgen, eq_bot_iff]
        exact xySupOf_le (X₀ := 𝔖.X A) (Y₀ := 𝔖.Y A) fun x hx hx1 y hy hy1 =>
          absurd ⟨x, hx, hx1, y, hy, hy1⟩ hXY
      rw [hP1, le_bot_iff] at hQP
      rw [hQP]
      exact bot_le
  ·
    obtain ⟨H, ⟨hHloc, hAH, R, hR, hRH⟩, hHM, hHN⟩ := h54 ⟨P, hPp, hAP, hc, hPgen⟩
    obtain ⟨R', hR', hPR'⟩ := exists_isMaxInvIn_ge le_top hPp hAP
    obtain ⟨g, hg, hgR⟩ := h46 R R' hR hR'
    set f : G →* G := (MulAut.conj g).toMonoidHom with hf
    have hH'top : H.map f ≠ ⊤ := by
      intro htop
      apply ne_top_of_isPLocal 𝔖 hp hp2 hHloc
      have h := congrArg (map (MulAut.conj g⁻¹).toMonoidHom) htop
      rwa [map_map, show (MulAut.conj g⁻¹).toMonoidHom.comp f = MonoidHom.id G by
        ext x; change g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x; group, map_id,
        map_top_of_surjective _ (MulAut.conj g⁻¹).surjective] at h
    have hAH' : A ≤ H.map f := by
      rw [← mem_normalizer_iff_map_conj_eq.mp hg]
      exact map_mono hAH
    have hH'M : Covers (H.map f) (𝔖.M₀ A) (O (𝔖.M A)) := by
      have h := covers_map_conj hHM g
      rwa [G4b.mem_normalizer_iff_map_conj_eq'.mp (G4b.normalizer_le_normalizer_M₀ 𝔖 hAS hA hg),
        G4b.mem_normalizer_iff_map_conj_eq'.mp (normalizer_le_normalizer_O_M 𝔖 hAS hA hg)] at h
    have hH'N : Covers (H.map f) (𝔖.N₀ A) (O (𝔖.N A)) := by
      have h := covers_map_conj hHN g
      rwa [G4b.mem_normalizer_iff_map_conj_eq'.mp (G4b.normalizer_le_normalizer_N₀ 𝔖 hAS hA hg),
        G4b.mem_normalizer_iff_map_conj_eq'.mp (normalizer_le_normalizer_O_N 𝔖 hAS hA hg)] at h
    have hPH' : P ≤ H.map f := hPR'.trans (hgR ▸ map_mono hRH)
    have hPO : P ≤ O (H.map f) := (h414 _ hH'top hAH' hH'M hH'N P hPH'
      (odd_card_of_isPGroup' hp hp2 hPp) hAP).mp hPgen
    exact (h414 _ hH'top hAH' hH'M hH'N Q (hQP.trans hPH') hQodd hAQ).mpr (hQP.trans hPO)

end Sec4Setting

end CFSG.GH72
