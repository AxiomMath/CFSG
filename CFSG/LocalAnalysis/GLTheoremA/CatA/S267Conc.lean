module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267Omega268
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267Trans
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267Cover

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA

@[expose] def S267Conc268Cov (p : ℕ) {A : Type} [Group A] [Finite A] (L : Subgroup A) : Prop :=
  ∃ B E D : Subgroup A, IsElemAbelian p B ∧ Nat.card B = p ^ 4 ∧ E ≤ B ∧ Nat.card E = p ^ 3 ∧
    D ≤ E ∧ Nat.card D = p ^ 2 ∧
    (∃ U : Subgroup A, U ≠ ⊥ ∧ IsPGroup 2 U ∧ B ≤ Subgroup.normalizer (U : Set A)) ∧
    (∃ U : Subgroup A, U ≠ ⊥ ∧ IsPGroup 2 U ∧ D ≤ Subgroup.normalizer (U : Set A) ∧
      CoversMod p (Subgroup.normalizer (U : Set A)) (GLAPLayer p (L ⊓ Subgroup.centralizer (D : Set A)))) ∧
    GLAPComponent p (L ⊓ Subgroup.centralizer (D : Set A))
      (GLAPLayer p (L ⊓ Subgroup.centralizer (D : Set A))) ∧
    (∀ b ∈ B, CentMod p (GLAPLayer p (L ⊓ Subgroup.centralizer (D : Set A))) b ↔ b ∈ D) ∧
    GLAPLayer p (GLAPLayer p (L ⊓ Subgroup.centralizer (D : Set A)) ⊓
      Subgroup.centralizer (E : Set A)) ≠ ⊥

section Quot

variable {A : Type} [Group A] [Finite A]

theorem conc268cov_of_quot {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (N : Subgroup A) [N.Normal]
    (hN : ¬ p ∣ Nat.card N) (K₀ : Subgroup A) (hNK : N ≤ K₀) (hKn : K₀.Normal)
    (h : S267Conc268 p (K₀.map (QuotientGroup.mk' N))) : S267Conc268Cov p K₀ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set π : A →* A ⧸ N := QuotientGroup.mk' N with hπ
  have hker : ¬ p ∣ Nat.card π.ker := by rw [hπ, QuotientGroup.ker_mk']; exact hN
  obtain ⟨B', E', D', hBel, hBc, hEB, hEc, hDE, hDc, ⟨T', hT0, hT2, hTn⟩, ⟨U', hU0, hU2, hDU, hJU⟩,
    hcomp, hBJ, hcm, hlay⟩ := h
  obtain ⟨B₁, hB₁el, hB₁map, hB₁card⟩ := exists_elemAbelian_lift N hN hBel
  have hB₁p : IsPGroup p B₁ := isPGroup_of_isElemAbelian hB₁el
  have hB₁c : ∀ x ∈ B₁, ∀ y ∈ B₁, x * y = y * x := fun x hx y hy => isElemAbelian_commute hB₁el hx hy
  have hB₁K : B₁ ≤ Subgroup.normalizer (K₀ : Set A) := by
    intro g _; rw [Subgroup.normalizer_eq_top_iff.2 hKn]; exact Subgroup.mem_top _
  set D₁ : Subgroup A := B₁ ⊓ D'.comap π with hD₁
  set E₁ : Subgroup A := B₁ ⊓ E'.comap π with hE₁
  have hD₁B : D₁ ≤ B₁ := inf_le_left
  have hE₁B : E₁ ≤ B₁ := inf_le_left
  have hDmap : D₁.map π = D' := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩; exact hx.2
    · intro y hy
      obtain ⟨b, hb, rfl⟩ : y ∈ B₁.map π := by rw [hB₁map]; exact hEB (hDE hy)
      exact ⟨b, ⟨hb, hy⟩, rfl⟩
  have hEmap : E₁.map π = E' := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩; exact hx.2
    · intro y hy
      obtain ⟨b, hb, rfl⟩ : y ∈ B₁.map π := by rw [hB₁map]; exact hEB hy
      exact ⟨b, ⟨hb, hy⟩, rfl⟩
  have hD₁p : IsPGroup p D₁ := hB₁p.to_le hD₁B
  have hE₁p : IsPGroup p E₁ := hB₁p.to_le hE₁B
  have hD₁c : Nat.card D₁ = p ^ 2 := by
    rw [← hDc, ← hDmap]; exact (card_map_of_isPGroup hp π hker hD₁p).symm
  have hE₁c : Nat.card E₁ = p ^ 3 := by
    rw [← hEc, ← hEmap]; exact (card_map_of_isPGroup hp π hker hE₁p).symm
  have hDE₁ : D₁ ≤ E₁ := by
    intro x hx
    exact ⟨hD₁B hx, hDE (by rw [← hDmap]; exact ⟨x, hx, rfl⟩)⟩
  have hmapC : (K₀ ⊓ Subgroup.centralizer (D₁ : Set A)).map π =
      K₀.map π ⊓ Subgroup.centralizer (D' : Set (A ⧸ N)) := by
    rw [map_inf_centralizer hp π hker hD₁p (hD₁B.trans hB₁K), hDmap]
  have hJ'c := hcomp
  have hJ'c' : GLAPComponent p (K₀.map π ⊓ Subgroup.centralizer ((D₁.map π : Subgroup (A ⧸ N)) : Set (A ⧸ N)))
      (GLAPLayer p (K₀.map π ⊓ Subgroup.centralizer (D' : Set (A ⧸ N)))) := by
    rw [hDmap]; exact hcomp
  obtain ⟨J, hJ, hJmap, hBJ'⟩ := exists_glaPComponent_lift_invariant hp π hker hB₁p hB₁K hB₁c
    (D' := D') (by rw [hB₁map]; exact hDE.trans hEB) hcomp (by rw [hB₁map]; exact hBJ)
  have hlayer : GLAPLayer p (K₀ ⊓ Subgroup.centralizer (D₁ : Set A)) = J := by
    apply glaPLayer_eq_of_map hp π hker hJ
    rw [hJmap, hmapC]
  refine ⟨B₁, E₁, D₁, hB₁el, by rw [hB₁card, hBc], hE₁B, hE₁c, hDE₁, hD₁c, ?_, ?_, ?_, ?_, ?_⟩
  ·
    obtain ⟨T, hT2', hBT, hTmap, -, -⟩ := exists_twoGroup_lift hp hp2 N hN hT2 hB₁p
      (by rw [hB₁map]; exact hTn)
    exact ⟨T, fun h => hT0 (by rw [← hTmap, h, Subgroup.map_bot]), hT2', hBT⟩
  ·
    obtain ⟨T, hT2', hTmap, hDT, hcov⟩ := covers_of_lift hp hp2 N hN hU2 (M := K₀) (D := D₁) (J := J)
      hNK hD₁p hJ (by rw [hDmap]; exact hDU) (by rw [hJmap]; exact hJU)
    exact ⟨T, fun h => hU0 (by rw [← hTmap, h, Subgroup.map_bot]), hT2', hDT, by rw [hlayer]; exact hcov⟩
  · rw [hlayer]; exact hJ
  · rw [hlayer]
    intro b hb
    rw [centMod_iff, mem_centModSubgroup_map_iff hp π hker (hBJ' hb), hJmap, ← centMod_iff,
      hcm (π b) (by rw [← hB₁map]; exact ⟨b, hb, rfl⟩)]
    simp only [hD₁, Subgroup.mem_inf, Subgroup.mem_comap]
    exact ⟨fun h => ⟨hb, h⟩, fun h => h.2⟩
  · rw [hlayer, ← glaPLayer_map_ne_bot_iff hp π hker, map_inf_centralizer hp π hker hE₁p (hE₁B.trans hBJ'),
      hJmap, hEmap]
    exact hlay

end Quot

end CFSG.LocalAnalysis.GLTheoremA.S267

end
