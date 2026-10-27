module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.QuadModel
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ExtensionPCore
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.PairModelCore
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.BarMNormalizer
public import CFSG.RankThree.PartTwo.Sec19.Item19Res3ProofAsc93

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open CFSG.AGLEmbedding CFSG.RankThree.PartTwo.Sec19 Equiv Equiv.Perm

section Core

variable {Q : Type*} [Group Q]

theorem exists_quadAction {C B : Subgroup Q} (hBC : B ≤ C) {n : ℕ} (hn : 2 ≤ n)
    (φ : ↥C ≃* AltW (Fin n) (Fin 4))
    (hB : (B.subgroupOf C).map φ.toMonoidHom = wN d8 (Fin n)) :
    ∃ ρ : ↥B →* Perm (Fin n), Function.Surjective ρ ∧ IsPGroup 2 ρ.ker := by
  have hι : 2 ≤ Fintype.card (Fin n) := by simpa using hn
  obtain ⟨ρ, hρs, hρk⟩ := exists_blockAction (D := d8) wreathHyp_d8 (by decide) hι
  set ψ := sectionEquiv hBC φ (wN d8 (Fin n)) hB with hψ
  refine ⟨ρ.comp ψ.toMonoidHom, hρs.comp ψ.surjective, ?_⟩
  rw [← MonoidHom.comap_ker]
  exact hρk.comap_of_injective ψ.toMonoidHom ψ.injective

theorem quotient_of_quadData {C B : Subgroup Q} (hBC : B ≤ C) {n : ℕ} (hn : n = 3 ∨ 5 ≤ n)
    (φ : ↥C ≃* AltW (Fin n) (Fin 4))
    (hB : (B.subgroupOf C).map φ.toMonoidHom = wN d8 (Fin n)) :
    Nonempty (↥B ⧸ CFSG.pCore 2 ↥B ≃* Perm (Fin n)) := by
  obtain ⟨ρ, hρs, hρk⟩ := exists_quadAction hBC (by omega) φ hB
  exact ⟨quotientPCoreOfKer (pCore_perm_eq_bot (by omega)) ρ hρs hρk⟩

end Core

variable {G : Type} [Group G]

@[expose] def QuadBlockData (X S L : Subgroup G) (n : ℕ) : Prop :=
  ∃ φ : ↥(barM X L) ≃* AltW (Fin n) (Fin 4),
    ((barM X (Subgroup.normalizer (S : Set G) ⊓ L)).subgroupOf (barM X L)).map
      φ.toMonoidHom = wN d8 (Fin n)

@[expose] def QuadBlockDataAct (X S L : Subgroup G) (n : ℕ) : Prop :=
  ∃ φ : ↥(barM X L) ≃* AltW (Fin n) (Fin 4),
    ((barM X (Subgroup.normalizer (S : Set G) ⊓ L)).subgroupOf (barM X L)).map
      φ.toMonoidHom = wN d8 (Fin n) ∧
    ∀ y ∈ barM X (Subgroup.normalizer (S : Set G) ⊓ Subgroup.normalizer (L : Set G)),
      ∃ σ ∈ wStab (Fin n) (Fin 4), ∀ l l' : ↥(barM X L),
        (l' : ↥X ⧸ CFSG.pCore 2 ↥X) = y * l * y⁻¹ →
          ((φ l' : AltW (Fin n) (Fin 4)) : Perm (Fin n × Fin 4)) =
            σ * ((φ l : AltW (Fin n) (Fin 4)) : Perm (Fin n × Fin 4)) * σ⁻¹

theorem QuadBlockDataAct.toQuadBlockData {X S L : Subgroup G} {n : ℕ}
    (h : QuadBlockDataAct X S L n) : QuadBlockData X S L n := by
  obtain ⟨φ, hN, -⟩ := h
  exact ⟨φ, hN⟩

theorem nineThreeSevenNat_of_quadBlockData {X S L : Subgroup G} {n : ℕ} (hn : n = 3 ∨ 5 ≤ n)
    (hirr : HasIrreducibleCommutatorQuotient L (blockV S L)) (D : QuadBlockData X S L n) :
    NineThreeSevenNat X S L := by
  obtain ⟨φ, hN⟩ := D
  have hBC : barM X (Subgroup.normalizer (S : Set G) ⊓ L) ≤ barM X L :=
    barM_mono inf_le_right
  refine ⟨hirr, n, by omega, ?_, quotient_of_quadData hBC hn φ hN⟩
  have e : Fin n × Fin 4 ≃ Fin (4 * n) :=
    Fintype.equivFinOfCardEq (by simp [Fintype.card_prod, mul_comm])
  exact ⟨φ.trans (Equiv.altCongrHom e)⟩

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
