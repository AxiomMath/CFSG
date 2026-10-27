module

public import CFSG.HardMathSupport.Solomon.Coordinator.SignalizerFunctor
public import CFSG.RankThree.PartTwo.Sec20.Step208MSPairProof
public import CFSG.HardMathSupport.Solomon.Proving.Basic

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.UniquenessMaximal

section General

variable {G : Type*} [Group G]

theorem le_bClosure (B L : Subgroup G) : L ≤ bClosure B L :=
  le_iSup₂_of_le (1 : G) B.one_mem (by rw [gLBConj_one])

theorem coreIn_le_glbCore [Finite G] (p k : ℕ) (P X : Subgroup G) :
    coreIn p k P X ≤ GLBCore p k P :=
  iSup₂_le fun Q hQ => inf_le_right.trans (le_sSup ⟨Q, hQ.1, hQ.2, rfl⟩)

theorem psiOf_le_glbCore [Finite G] (p : ℕ) (B : Subgroup G) (b : G) :
    psiOf p B b ≤ GLBCore p 3 B := by
  refine sSup_le ?_
  rintro L ⟨-, -, hL⟩
  calc L ≤ bClosure B L := le_bClosure B L
    _ = coreIn p 3 B (bClosure B L) := hL
    _ ≤ GLBCore p 3 B := coreIn_le_glbCore p 3 B _

theorem psiStarGroup_le_glbCore [Finite G] {p n : ℕ} (hp : p.Prime) {B : Subgroup G}
    (hB : IsElemAbelian p B) (hcard : Nat.card B = p ^ n) (hn : 4 ≤ n) :
    psiStarGroup p B ≤ GLBCore p 3 B := by
  have hcore : ∀ X : Subgroup G, B ≤ X → GLAPPrimeCoreOf p X ≤ GLBCore p 3 B := fun X hBX =>
    CFSG.HardMathSupport.Solomon.Proving.le_glbCore_three_of_coprime_invariant hp hB hcard hn
      (hBX.trans (le_normalizer_glaPPrimeCoreOf p X)) (not_dvd_card_glaPPrimeCoreOf hp X)
  have hBC : B ≤ Subgroup.centralizer (B : Set G) := fun x hx => by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact elemAbelian_comm hB hy hx
  refine iSup₂_le fun b hb => iSup_le fun _ => ?_
  refine sup_le (sup_le (psiOf_le_glbCore p B b) (hcore _ ?_)) (hcore _ hBC)
  intro x hx
  exact Subgroup.mem_centralizer_singleton_iff.2 (elemAbelian_comm hB hx hb)

theorem le_glaPPrimeCoreOf_normalizer {p : ℕ} {X : Subgroup G}
    (hX : Nat.Coprime p (Nat.card X)) :
    X ≤ GLAPPrimeCoreOf p (Subgroup.normalizer (X : Set G)) := by
  have hle : X ≤ Subgroup.normalizer (X : Set G) := Subgroup.le_normalizer
  have hcard : Nat.card (X.subgroupOf (Subgroup.normalizer (X : Set G))) = Nat.card X :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  have h1 : X.subgroupOf (Subgroup.normalizer (X : Set G)) ≤
      GLAPPrimeCore p ↥(Subgroup.normalizer (X : Set G)) :=
    le_sSup ⟨Subgroup.normal_in_normalizer, hcard ▸ hX⟩
  have h2 := Subgroup.map_mono (f := (Subgroup.normalizer (X : Set G)).subtype) h1
  rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hle] at h2

end General

variable {G : Type} [Group G] [Finite G] {m p : ℕ}

theorem isKGroupCat_glaDelta (hbridge : CFSG.RankThree.PartOne.TauCetiCatalogBridge)
    (hK : CFSG.Open.IsKProper G) (hp : p.Prime) (hpG : p ∣ Nat.card G) {D : Subgroup G} (hD : D ≠ ⊥) :
    CFSG.SectionRank.IsKGroupCat ↥(GLADelta p D) := by
  have hne : GLADelta p D ≠ ⊤ := by
    intro htop
    apply not_dvd_card_glaDelta hp hD
    rw [htop, Subgroup.card_top]
    exact hpG
  exact CFSG.RankThree.PartTwo.Sec20.isKGroupCat_of_ne_top hbridge hK hne

theorem exists_preUniquenessSubgroup_of_caseOne (hSF : SignalizerFunctorTheoremK)
    (hbridge : CFSG.RankThree.PartOne.TauCetiCatalogBridge) (hS : GLStanding G m p)
    (hI : GLCaseOne G p) :
    ∃ B : Subgroup G, IsBOneMax p B ∧ ∃ M₀ : Subgroup G, IsPreUniquenessSubgroup p B M₀ := by
  obtain ⟨B, hB1, hbal, hΛ⟩ := hI
  have hp := hS.prime
  have hBel : IsElemAbelian p B := hB1.1.1
  have hBcard : Nat.card B = p ^ m := hS.card_eq hB1
  have hm4 := hS.four_le
  have hrank : p ^ (2 + 2) ≤ Nat.card B := hBcard ▸ Nat.pow_le_pow_right hp.pos (by omega)
  have hpG : p ∣ Nat.card G := hS.beta.2.2.1
  obtain ⟨⟨hcop, -⟩, -⟩ := thetaClosure_complete hSF hp (by norm_num) hBel hrank hbal
    (fun D hD => isKGroupCat_glaDelta hbridge hS.kProper hp hpG (hD.ne_bot hp (by norm_num)))
  refine ⟨B, hB1, Subgroup.normalizer (thetaClosure p 2 B : Set G), ?_, ?_, ?_⟩
  · rw [hΛ]
    exact (psiStarGroup_le_glbCore hp hBel hBcard hm4).trans
      (glbCore_le_normalizer_thetaClosure hp (by norm_num) hBel hbal)
  · exact glbCore_le_normalizer_thetaClosure hp (by norm_num) hBel hbal
  · obtain ⟨D, hDB, hDpl, hDeven⟩ := hB1.2
    have hDθ : GLADelta p D ≤ thetaClosure p 2 B :=
      le_iSup₂_of_le D ⟨hDB, hDpl.1, hDpl.2⟩ le_rfl
    have hdvd : Nat.card (GLADelta p D) ∣
        Nat.card (GLAPPrimeCoreOf p (Subgroup.normalizer (thetaClosure p 2 B : Set G))) :=
      Subgroup.card_dvd_of_le (hDθ.trans (le_glaPPrimeCoreOf_normalizer hcop))
    exact even_iff_two_dvd.2 ((even_iff_two_dvd.1 hDeven).trans hdvd)

end CFSG.HardMathSupport.Solomon.Coordinator
