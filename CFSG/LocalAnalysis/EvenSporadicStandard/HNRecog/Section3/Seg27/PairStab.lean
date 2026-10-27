module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Seg27.Perm

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

@[expose] def seg27PairStab (p q : Fin 8) : Subgroup (Equiv.Perm (Fin 8)) where
  carrier := {g | (g p = p ∧ g q = q) ∨ (g p = q ∧ g q = p)}
  mul_mem' := by
    intro g h hg hh
    simp only [Set.mem_setOf_eq, Equiv.Perm.coe_mul, Function.comp_apply] at hg hh ⊢
    rcases hh with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hg with ⟨g1, g2⟩ | ⟨g1, g2⟩ <;>
      simp [h1, h2, g1, g2]
  one_mem' := by simp
  inv_mem' := by
    intro g hg
    simp only [Set.mem_setOf_eq] at hg ⊢
    rcases hg with ⟨g1, g2⟩ | ⟨g1, g2⟩
    · left
      exact ⟨by rw [Equiv.Perm.inv_eq_iff_eq, g1], by rw [Equiv.Perm.inv_eq_iff_eq, g2]⟩
    · right
      exact ⟨by rw [Equiv.Perm.inv_eq_iff_eq, g2], by rw [Equiv.Perm.inv_eq_iff_eq, g1]⟩

theorem seg27_mem_pairStab {p q : Fin 8} {g : Equiv.Perm (Fin 8)} :
    g ∈ seg27PairStab p q ↔ (g p = p ∧ g q = q) ∨ (g p = q ∧ g q = p) :=
  Iff.rfl

private theorem seg27_pairStab_apply_mem_left {p q : Fin 8} {g : Equiv.Perm (Fin 8)}
    (hg : g ∈ seg27PairStab p q) : g p ∈ ({p, q} : Set (Fin 8)) := by
  rcases (seg27_mem_pairStab.mp hg) with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact Set.mem_insert_iff.mpr (Or.inl h1)
  · exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr h1))

theorem seg27_card_box_le {p₀ q₀ p₁ q₁ : Fin 8} (h01 : p₀ ≠ q₀) (h02 : p₀ ≠ p₁) (h03 : p₀ ≠ q₁)
    (h12 : q₀ ≠ p₁) (h13 : q₀ ≠ q₁) (h23 : p₁ ≠ q₁) :
    Nat.card (alternatingGroup (Fin 8) ⊓ seg27PairStab p₀ q₀ ⊓ seg27PairStab p₁ q₁ :
      Subgroup (Equiv.Perm (Fin 8))) ≤ 48 := by
  let B : Subgroup (Equiv.Perm (Fin 8)) :=
    alternatingGroup (Fin 8) ⊓ seg27PairStab p₀ q₀ ⊓ seg27PairStab p₁ q₁
  let S : Set (Fin 8) := {p₀, q₀, p₁, q₁}
  let x₀ : Fin 8 × Fin 8 := (p₀, p₁)
  change Nat.card B ≤ 48
  have hcardB : Nat.card B =
      Nat.card (MulAction.stabilizer B x₀) * (MulAction.orbit B x₀).ncard := by
    rw [← MulAction.index_stabilizer B x₀]
    exact (Subgroup.card_mul_index (H := MulAction.stabilizer B x₀)).symm
  have horbit : (MulAction.orbit B x₀).ncard ≤ 4 := by
    have hsub : MulAction.orbit B x₀ ⊆
        ({p₀, q₀} : Set (Fin 8)) ×ˢ ({p₁, q₁} : Set (Fin 8)) := by
      rintro y ⟨g, rfl⟩
      have hgm : (g : Equiv.Perm (Fin 8)) ∈ alternatingGroup (Fin 8) ∧
          (g : Equiv.Perm (Fin 8)) ∈ seg27PairStab p₀ q₀ ∧
          (g : Equiv.Perm (Fin 8)) ∈ seg27PairStab p₁ q₁ := by
        have h := (g : B).2
        simp only [B, Subgroup.mem_inf] at h
        exact ⟨h.1.1, h.1.2, h.2⟩
      rw [Set.mem_prod]
      refine ⟨?_, ?_⟩
      · show (g • x₀).1 ∈ ({p₀, q₀} : Set (Fin 8))
        simpa [x₀, Subgroup.smul_def, Equiv.Perm.smul_def] using
          seg27_pairStab_apply_mem_left hgm.2.1
      · show (g • x₀).2 ∈ ({p₁, q₁} : Set (Fin 8))
        simpa [x₀, Subgroup.smul_def, Equiv.Perm.smul_def] using
          seg27_pairStab_apply_mem_left hgm.2.2
    calc (MulAction.orbit B x₀).ncard
        ≤ (({p₀, q₀} : Set (Fin 8)) ×ˢ ({p₁, q₁} : Set (Fin 8))).ncard :=
          Set.ncard_le_ncard hsub
      _ = ({p₀, q₀} : Set (Fin 8)).ncard * ({p₁, q₁} : Set (Fin 8)).ncard := Set.ncard_prod
      _ = 2 * 2 := by rw [Set.ncard_pair h01, Set.ncard_pair h23]
      _ = 4 := by norm_num
  have hstab : Nat.card (MulAction.stabilizer B x₀) ≤ 12 := by
    have hmem_fix : ∀ g : ↥(MulAction.stabilizer B x₀),
        (g : Equiv.Perm (Fin 8)) ∈ seg27AltFix S := by
      intro g
      have hgm : (g : Equiv.Perm (Fin 8)) ∈ alternatingGroup (Fin 8) ∧
          (g : Equiv.Perm (Fin 8)) ∈ seg27PairStab p₀ q₀ ∧
          (g : Equiv.Perm (Fin 8)) ∈ seg27PairStab p₁ q₁ := by
        have h := g.1.2
        simp only [B, Subgroup.mem_inf] at h
        exact ⟨h.1.1, h.1.2, h.2⟩
      have hgx : (g : B) • x₀ = x₀ := g.2
      have hfix0 : (g : Equiv.Perm (Fin 8)) p₀ = p₀ := by
        show ((g : B) : Equiv.Perm (Fin 8)) p₀ = p₀
        have h := congrArg Prod.fst hgx
        simpa [x₀, Subgroup.smul_def, Equiv.Perm.smul_def] using h
      have hfix1 : (g : Equiv.Perm (Fin 8)) p₁ = p₁ := by
        show ((g : B) : Equiv.Perm (Fin 8)) p₁ = p₁
        have h := congrArg Prod.snd hgx
        simpa [x₀, Subgroup.smul_def, Equiv.Perm.smul_def] using h
      have hq0 : (g : Equiv.Perm (Fin 8)) q₀ = q₀ := by
        rcases (seg27_mem_pairStab.mp hgm.2.1) with ⟨-, h2⟩ | ⟨h1, -⟩
        · exact h2
        · exact absurd (h1.symm.trans hfix0) (Ne.symm h01)
      have hq1 : (g : Equiv.Perm (Fin 8)) q₁ = q₁ := by
        rcases (seg27_mem_pairStab.mp hgm.2.2) with ⟨-, h2⟩ | ⟨h1, -⟩
        · exact h2
        · exact absurd (h1.symm.trans hfix1) (Ne.symm h23)
      rw [seg27_mem_altFix]
      refine ⟨hgm.1, ?_⟩
      intro x hx
      simp only [S, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact hfix0
      · exact hq0
      · exact hfix1
      · exact hq1
    have hinj : Function.Injective (fun g : ↥(MulAction.stabilizer B x₀) =>
        (⟨(g : Equiv.Perm (Fin 8)), hmem_fix g⟩ : ↥(seg27AltFix S))) := by
      intro a b hab
      have h1 : a.1.1 = b.1.1 := by
        have h := congrArg (fun z : ↥(seg27AltFix S) => (z : Equiv.Perm (Fin 8))) hab
        simpa using h
      have h2 : a.1 = b.1 := Subtype.ext h1
      exact Subtype.ext h2
    have hle : Nat.card (MulAction.stabilizer B x₀) ≤ Nat.card (seg27AltFix S) :=
      Nat.card_le_card_of_injective _ hinj
    have hcard12 : Nat.card (seg27AltFix S) = 12 := by
      rw [show S = ({p₀, q₀, p₁, q₁} : Set (Fin 8)) from rfl]
      exact seg27_card_altFix_four h01 h02 h03 h12 h13 h23
    rwa [hcard12] at hle
  calc Nat.card B
      = Nat.card (MulAction.stabilizer B x₀) * (MulAction.orbit B x₀).ncard := hcardB
    _ ≤ 12 * 4 := Nat.mul_le_mul hstab horbit
    _ = 48 := by norm_num

end CFSG.EvenSporadicStandard.HNRecog.Section3
