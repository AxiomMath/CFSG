module

public import CFSG.ClassicalInvolution.WeakCT.DLLevis
public import CFSG.ClassicalInvolution.WeakCT.SpPair
public import CFSG.ClassicalInvolution.WeakCT.TwistedRankOne

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.Timmesfeld CFSG.Timmesfeld.LevisExtras CFSG.ClassicalInvolution.WeakCT
open CFSG.ClassicalInvolution.Models.SymplecticPairs (SymplecticBlockStandardPair longBlock
  shortBlock longBlock_injective shortBlock_injective)
open CFSG.Assembly.LowTwoRank (StatedSp)
open scoped MatrixGroups

section Sp

variable {K : Type} [Group K] {D : UniversalRootDatum K} {F : Type} [Field F] [Finite F]
  {x : (Fin D.rank → ℤ) → F → K}
  {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
  {O : Steinberg.CommOrder (Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}

theorem exists_symplecticBlockStandardPair_rankOne (hF : 4 ≤ Nat.card F) (h2 : (2 : F) ≠ 0)
    (hE : Steinberg.ChevalleyExtras D F x C O) (hdiv : D.divisible = ∅) {i j : Fin D.rank}
    (hcij : D.cartan i j = -2) (hcji : D.cartan j i = -1) :
    ∃ W, SymplecticBlockStandardPair F W (rankOne D.rootGroup j) (rankOne D.rootGroup i) := by
  obtain ⟨φ, hφ, -, hv⟩ := exists_sp4Levi hF h2 hE hdiv hcij hcji
  have hset : ∀ γ ∈ D.roots, (D.rootGroup γ : Set K) = Set.range (x γ) := fun γ hγ =>
    Set.ext fun g => (hE.param γ hγ).1 g
  have hΦ := isCTRootSystem D.isFiniteType D.divisible
  have hneg : ∀ l : Fin D.rank, -Pi.single l 1 ∈ D.roots := fun l =>
    CFSG.LieType.Steinberg.OfCartan.neg_mem_roots D.isFiniteType (hΦ.single_mem l)
  have hrk : ∀ (k : Fin 2) (l : Fin D.rank),
      (∀ c, φ (spBlock F k (tv 0 1 c)) = x (Pi.single l 1) c) →
      (∀ c, φ (spBlock F k (tv 1 0 c)) = x (-Pi.single l 1) c) →
      rankOne D.rootGroup l = (φ.comp (spBlock F k)).range := by
    intro k l hu hl
    refine rankOne_eq_range_of_param (φ.comp (spBlock F k)) ?_ ?_ ?_ ?_
    · intro c
      change φ (spBlock F k (tv 0 1 c)) ∈ _
      rw [hu c]
      have : x (Pi.single l 1) c ∈ Set.range (x (Pi.single l 1)) := ⟨c, rfl⟩
      rw [← hset _ (hΦ.single_mem l)] at this
      exact this
    · intro c
      change φ (spBlock F k (tv 1 0 c)) ∈ _
      rw [hl c]
      have : x (-Pi.single l 1) c ∈ Set.range (x (-Pi.single l 1)) := ⟨c, rfl⟩
      rw [← hset _ (hneg l)] at this
      exact this
    · intro g hg
      have : g ∈ Set.range (x (Pi.single l 1)) := by rw [← hset _ (hΦ.single_mem l)]; exact hg
      obtain ⟨c, rfl⟩ := this
      exact ⟨c, hu c⟩
    · intro g hg
      have : g ∈ Set.range (x (-Pi.single l 1)) := by rw [← hset _ (hneg l)]; exact hg
      obtain ⟨c, rfl⟩ := this
      exact ⟨c, hl c⟩
  have hL := hrk 1 j (fun c => (hv c).2.2.1) (fun c => (hv c).2.2.2)
  have hS := hrk 0 i (fun c => (hv c).1) (fun c => (hv c).2.1)
  refine ⟨φ.range, φ, 1, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · rw [(MonoidHom.ker_eq_bot_iff _).mpr hφ]
    exact bot_le
  · exact hφ.comp ((MulAut.conj (1 : StatedSp 2 F)⁻¹).injective.comp
      (longBlock_injective (K := F) (n := 2) 1))
  · exact hφ.comp ((MulAut.conj (1 : StatedSp 2 F)⁻¹).injective.comp
      (shortBlock_injective (K := F) (zero_ne_one : (0 : Fin 2) ≠ 1)))
  · rw [CFSG.ClassicalInvolution.Models.SymplecticPairs.map_conj_one, hL, MonoidHom.range_comp,
      spBlock_one_eq_longBlock]
  · rw [CFSG.ClassicalInvolution.Models.SymplecticPairs.map_conj_one, hS, MonoidHom.range_comp,
      spBlock_zero_eq_shortBlock]

end Sp

end CFSG.ClassicalInvolution.RouteD
