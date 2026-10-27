module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1426Alt

public section

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator
open scoped commutatorElement

namespace CFSG.LocalAnalysis.GLTheoremA

@[expose] def KD1426Concl {Y : Type} [Group Y] (K B : Subgroup Y) : Prop :=
  Nat.card B = 3 ^ 4 ∧ ∃ A T : Subgroup Y, A ≤ B ∧ IsElemAbelian 3 A ∧ Nat.card A = 9 ∧
    GLAPComponent 3 (K ⊓ Subgroup.centralizer (A : Set Y))
      (GLAPLayer 3 (K ⊓ Subgroup.centralizer (A : Set Y))) ∧
    catalogIs (PSimple 3 (GLAPLayer 3 (K ⊓ Subgroup.centralizer (A : Set Y)))) k3NoA10 ∧
    (∀ b ∈ B, b ∈ Subgroup.centralizer
        ((GLAPLayer 3 (K ⊓ Subgroup.centralizer (A : Set Y)) : Subgroup Y) : Set Y) ↔ b ∈ A) ∧
    T ≤ GLAPLayer 3 (K ⊓ Subgroup.centralizer (A : Set Y)) ∧ IsElemAbelian 2 T ∧
    Nat.card T = 4 ∧ B ≤ Subgroup.normalizer (T : Set Y) ∧ ⁅B, T⁆ = T ∧
    GLAPPrimeCore 3 ↥(GLAPLayer 3 (K ⊓ Subgroup.centralizer (A : Set Y))) = ⊥

@[expose] def KD1426SporS : Prop :=
  ∀ (s : TauCeti.SporadicName), (s = TauCeti.SporadicName.M12 ∨ s = TauCeti.SporadicName.M22) →
    ∀ (Y : Type) [Group Y] [Finite Y] (K B : Subgroup Y), K.Normal → CFSG.Open.IsQuasisimple ↥K →
      CatalogCentralIsogeny 3 ↥K (TauCeti.CFSGIndex.sporadic s) →
      GLAPPrimeCore 3 ↥K = ⊥ → fullCoverLevel 3 ↥K = 3 →
      IsElemAbelian 3 B → K ⊔ B = ⊤ → 3 ^ 4 ≤ Nat.card B → IsMaxRankIn 3 B ⊤ →
      B ⊓ Subgroup.centralizer (K : Set Y) ≠ ⊥ →
      (∀ E : Subgroup Y, E ≤ B → IsElemAbelian 3 E → Nat.card E = 3 ^ 3 →
        GLAPLayer 3 (K ⊓ Subgroup.centralizer (E : Set Y)) = ⊥) →
      (catalogIs (↥K ⧸ Subgroup.center ↥K) isM12 → ∃ U : Subgroup Y, U ≤ K ∧ U ≠ ⊥ ∧
        IsPGroup 2 U ∧ B ≤ Subgroup.normalizer (U : Set Y)) →
      KD1426Concl K B

theorem kd1426Spor_of_S (h : KD1426SporS) : KD1426Spor := by
  intro Y _ _ K B hKn hq hcat hcore hlev hB hKB hcard hmax hC hH hM
  obtain ⟨i, hi, ⟨eK⟩⟩ := hcat
  cases i with
  | cyclic p hp => exact False.elim hi
  | alternating n h' => exact False.elim hi
  | lie d => exact False.elim hi
  | sporadic s =>
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    let π : K →* (TauCeti.CFSGIndex.sporadic s).Group :=
      eK.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
    have hπ : Function.Surjective π := eK.surjective.comp (QuotientGroup.mk'_surjective _)
    have hker : π.ker = Subgroup.center K := by
      ext x
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    have hp : IsPGroup 3 π.ker := by
      rw [hker]
      exact KD264Z.isPGroup_center_of_pPrimeCore Nat.prime_three hcore
    exact h s hi Y K B hKn hq ⟨π, hπ, hker.le, hp⟩ hcore hlev hB hKB hcard hmax hC hH hM

theorem kd1426Cat_of_S (h : KD1426SporS) (hL : KD1426Lie) : KD1426Cat :=
  kd1426Cat_of_parts kd1426Alt_holds (kd1426Spor_of_S h) hL

end CFSG.LocalAnalysis.GLTheoremA

end
