module

public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
public import CFSG.Open.GriessAllModelsStatement
import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusLinPrimeGlue
import CFSG.LocalAnalysis.GLTheoremA.PComp
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagData
import CFSG.Quasithin.Background.E1Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Lin

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.ComponentInitial LinearFlag Matrix

theorem odd_card_center_of_pCore_eq_bot {X : Type} [Group X] [Finite X]
    (h : CFSG.pCore 2 X = ⊥) : Odd (Nat.card (Subgroup.center X)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center X) 2
    (even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hne))
  have hz' : orderOf (z : X) = 2 := by rw [Subgroup.orderOf_coe, hz]
  have hn : (Subgroup.zpowers (z : X)).Normal := ⟨fun n hn g => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    have hc : Commute g (z : X) := Subgroup.mem_center_iff.mp z.2 g
    rw [(hc.zpow_right k).eq, mul_inv_cancel_right]
    exact zpow_mem (Subgroup.mem_zpowers _) k⟩
  have hp : IsPGroup 2 (Subgroup.zpowers (z : X)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz', pow_one])
  have hle : Subgroup.zpowers (z : X) ≤ CFSG.pCore 2 X := le_sSup ⟨hn, hp⟩
  rw [h] at hle
  have h1 : (z : X) = 1 := (Subgroup.mem_bot).mp (hle (Subgroup.mem_zpowers _))
  rw [h1, orderOf_one] at hz'
  norm_num at hz'

theorem exists_cover_of_isQuasisimple
    (hGA : GriessAllModelsStatement) {X : Type} [Group X]
    [Finite X] (hX : Open.IsQuasisimple X) (hodd : Odd (Nat.card (Subgroup.center X))) {n : ℕ}
    (hn : 2 ≤ n) {K : Type} [Field K] [Finite K] [CharP K 2]
    (e : X ⧸ Subgroup.center X ≃* projectiveSL n K) :
    ∃ ρ : SpecialLinearGroup (Fin n) K →* X, Function.Surjective ρ ∧
      ρ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin n) K) ∧
      ∀ g, e (QuotientGroup.mk (ρ g)) = proj n K g := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hL : IsComponentOf (⊤ : Subgroup X) ⊤ :=
    CFSG.LocalAnalysis.GLTheoremA.isComponentOf_top_of_isQuasisimple hX
  let eT : ↥(⊤ : Subgroup X) ≃* X := Subgroup.topEquiv
  have hcT : (Subgroup.center ↥(⊤ : Subgroup X)).map eT.toMonoidHom = Subgroup.center X :=
    Subgroup.map_center_eq eT
  have hcard : Nat.card (Subgroup.center ↥(⊤ : Subgroup X)) = Nat.card (Subgroup.center X) := by
    rw [← hcT]
    exact (Subgroup.card_map_of_injective eT.injective).symm
  let eQ : ↥(⊤ : Subgroup X) ⧸ Subgroup.center ↥(⊤ : Subgroup X) ≃*
      X ⧸ Subgroup.center X := QuotientGroup.congr _ _ eT hcT
  obtain ⟨ρ₀, hs, hk, hρ₀⟩ := ToralCensus.exists_cover_of_oddCenter
    (oddCenterLinear_of_griess hGA) (kFactCoverLinear_of_griess hGA) hL (hcard ▸ hodd) hn
    (eQ.trans e)
  refine ⟨eT.toMonoidHom.comp ρ₀, eT.surjective.comp hs, ?_, fun g => ?_⟩
  · intro g hg
    apply hk
    rw [MonoidHom.mem_ker] at hg ⊢
    exact eT.injective (by simpa using hg)
  · have h := hρ₀ g
    rw [MulEquiv.trans_apply, show eQ (QuotientGroup.mk (ρ₀ g)) =
      QuotientGroup.mk (eT (ρ₀ g)) from QuotientGroup.congr_mk _ _ eT hcT (ρ₀ g)] at h
    exact h

structure LinCover {A : Type} [Group A] (Y P : Subgroup A) (n : ℕ) (K : Type) [Field K]
    (I : Set ℕ) where
  σ : SpecialLinearGroup (Fin n) K →* ↥Y
  e : ↥Y ⧸ Subgroup.center ↥Y ≃* projectiveSL n K
  surjective : Function.Surjective σ
  ker_le_center : σ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin n) K)
  compat : ∀ g, e (QuotientGroup.mk (σ g)) = proj n K g
  comap_eq : (P.subgroupOf Y).comap σ = flagStabilizer n K I

theorem exists_linCover
    (hGA : GriessAllModelsStatement) {A : Type} [Group A] [Finite A] {Y P : Subgroup A}
    (hY : Open.IsQuasisimple ↥Y) (hodd : Odd (Nat.card (Subgroup.center ↥Y))) {n : ℕ}
    (hn : 2 ≤ n) {K : Type} [Field K] [Finite K] [CharP K 2]
    (e : ↥Y ⧸ Subgroup.center ↥Y ≃* projectiveSL n K) (hpar : IsParabolicTwo Y P) :
    ∃ (I : Set ℕ) (_ : LinCover Y P n K I), (∀ i ∈ I, 1 ≤ i ∧ i < n) ∧ (P ≠ Y → I.Nonempty) := by
  obtain ⟨ρ, hρs, -, hρ⟩ := exists_cover_of_isQuasisimple hGA hY hodd hn e
  obtain ⟨σ, e', I, hσs, hσ, hI, hcomap, hne, -⟩ :=
    exists_comap_eq_flagStabilizer hodd (by omega) e hρs hρ hpar
  obtain ⟨-, hσk⟩ := ToralCensus.surjective_and_ker_le_of_compat hY.1 e' σ hσ
  exact ⟨I, ⟨σ, e', hσs, hσk, hσ, hcomap⟩, hI, fun hPY => hne fun h => hPY h⟩

namespace LinCover

variable {A : Type} [Group A] {Y P : Subgroup A} {n : ℕ} {K : Type} [Field K] {I : Set ℕ}
  (C : LinCover Y P n K I)

theorem mem_flag_iff (g : SpecialLinearGroup (Fin n) K) :
    g ∈ flagStabilizer n K I ↔ ((C.σ g : ↥Y) : A) ∈ P := by
  rw [← C.comap_eq]
  rfl

@[expose] noncomputable def toP : ↥(flagStabilizer n K I) →* ↥P :=
  (((Y.subtype).comp C.σ).comp (flagStabilizer n K I).subtype).codRestrict P
    fun q => (C.mem_flag_iff q.1).mp q.2

@[simp] theorem coe_toP (x : ↥(flagStabilizer n K I)) :
    ((C.toP x : ↥P) : A) = ((C.σ x : ↥Y) : A) := rfl

theorem toP_surjective (hPY : P ≤ Y) : Function.Surjective C.toP := by
  rintro ⟨w, hw⟩
  obtain ⟨g, hg⟩ := C.surjective ⟨w, hPY hw⟩
  have hgQ : g ∈ flagStabilizer n K I := by
    rw [C.mem_flag_iff, hg]
    exact hw
  exact ⟨⟨g, hgQ⟩, Subtype.ext (by rw [coe_toP, hg])⟩

@[expose] noncomputable def toHat : ↥(flagStabilizer n K I) →* ↥P ⧸ CFSG.pCore 2 ↥P :=
  (QuotientGroup.mk' (CFSG.pCore 2 ↥P)).comp C.toP

theorem toHat_surjective (hPY : P ≤ Y) : Function.Surjective C.toHat :=
  (QuotientGroup.mk'_surjective _).comp (C.toP_surjective hPY)

end LinCover

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Lin
