module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Lemma68
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.UCentJ2
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.UCentJ3
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.WFactsJ2
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.WJ3

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic

namespace J2

open CFSG.Sporadic.Schreier (j2P j2PermEquiv)

theorem uLabelClass_P :
    ULabelClass ↥ComponentClassification.J2Cover.Models.P uMulJ2 uIdxJ2 :=
  ULabelClass.of_mulEquiv
    ((j2PermEquiv.symm.trans ComponentClassification.J2Cover.nativeEquivP).trans
      (MulEquiv.subgroupCongr ComponentClassification.J2Cover.Models.P_eq_autP.symm))
    uLabelClass_j2P

theorem eLabelling_of_isSporadic {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G}
    {T₀ E : Subgroup G}
    (h : InnerConfig G L z t T₀) (hE : EConfig L T₀ E t) (hL : IsSporadic L .J2) :
    ∃ eltE : ℕ → G, ELabelling E t uMulJ2 uIdxJ2 eltE := by
  obtain ⟨e⟩ := hL
  obtain ⟨T, Ex, tx, hM⟩ := pinModel_P
  exact eLabelling_of_model h hE
    (((MulEquiv.subgroupCongr ComponentClassification.J2Cover.Models.P_eq_autP).trans
      ComponentClassification.J2Cover.nativeEquivP.symm).trans e.symm) hM rootFactsClass_P
    uLabelClass_P

end J2

namespace J3

open CFSG.Sporadic.Schreier (j3P j3PermEquiv)

theorem eLabelling_of_isSporadic {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G}
    {T₀ E : Subgroup G}
    (h : InnerConfig G L z t T₀) (hE : EConfig L T₀ E t) (hL : IsSporadic L .J3) :
    ∃ eltE : ℕ → G, ELabelling E t uMulJ3 uIdxJ3 eltE := by
  obtain ⟨e⟩ := hL
  obtain ⟨T, Ex, tx, hM⟩ := pinModel_j3P
  exact eLabelling_of_model h hE (j3PermEquiv.symm.trans e.symm) hM rootFactsClass_j3P
    uLabelClass_j3P

end J3

section Final

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T₀ E : Subgroup G}
  {Q : Sylow 2 G} {x β : G} {B : Subgroup G}

theorem t_mem_of_maximal (hconf : Rest6Config L z t T₀ E Q x β B) {S : Subgroup G}
    (hS2 : IsPGroup 2 S) (hSC : S ≤ centralizer (E : Set G))
    (hSmax : ∀ R : Subgroup G, IsPGroup 2 R → R ≤ centralizer (E : Set G) → S ≤ R → R = S) :
    t ∈ S := by
  have hcfg := hconf.cfg
  have hE := hconf.econfig
  have htE : t ∈ E := hE.t_mem
  have hzE : zpowers t ≤ E := zpowers_le.2 htE
  have hzpC : zpowers t ≤ centralizer (E : Set G) := by
    rw [zpowers_le]
    exact mem_centralizer_iff.2 fun e he => hcfg.t_central e (hE.le he)
  have hZ2 : IsPGroup 2 (zpowers t) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hcfg.t_order]; norm_num)
  have hSn : S ≤ normalizer ((zpowers t : Subgroup G) : Set G) :=
    (hSC.trans (centralizer_le hzE)).trans (centralizer_le_normalizer _)
  have hR2 : IsPGroup 2 (S ⊔ zpowers t : Subgroup G) := hS2.to_sup_of_normal_right' hZ2 hSn
  have := hSmax _ hR2 (sup_le hSC hzpC) le_sup_left
  rw [← this]
  exact mem_sup_right (mem_zpowers t)

theorem ucent_of_label (hconf : Rest6Config L z t T₀ E Q x β B) {S : Subgroup G}
    (hS2 : IsPGroup 2 S) (hSC : S ≤ centralizer (E : Set G))
    (hSmax : ∀ R : Subgroup G, IsPGroup 2 R → R ≤ centralizer (E : Set G) → S ≤ R → R = S)
    (hD8 : Nonempty (S ≃* DihedralGroup 4)) {mulE : ℕ → ℕ → ℕ} {tI : ℕ} {eltE : ℕ → G}
    (hlab : ELabelling E t mulE tI eltE) (hspec : UTableSpec mulE tI) :
    ∀ u ∈ S ⊔ E, u * u = 1 → u ∉ zpowers t →
      ∃ X : Subgroup G, X ≤ S ⊔ E ∧ Nonempty (E ≃* X) ∧ u ∉ X ∧ ∀ x ∈ X, u * x = x * u :=
  exists_X_of_spec hD8.some hlab (t_mem_of_maximal hconf hS2 hSC hSmax)
    (fun _ hs e he => (mem_centralizer_iff.1 (hSC hs) e he).symm) hspec

end Final

theorem fin76bUCent :
    Fin76bUCent := by
  intro G _ _ L z t T₀ E Q x β B hconf hW S hS2 hSC hSmax hzS hD8 hBS
  rcases hconf.sporadic with hL | hL
  · obtain ⟨eltE, hlab⟩ := J2.eLabelling_of_isSporadic hconf.cfg hconf.econfig hL
    exact ucent_of_label hconf hS2 hSC hSmax hD8 hlab J2.uSpec_j2
  · obtain ⟨eltE, hlab⟩ := J3.eLabelling_of_isSporadic hconf.cfg hconf.econfig hL
    exact ucent_of_label hconf hS2 hSC hSmax hD8 hlab J3.uSpec_j3

end CFSG.EvenSporadicStandard.Fin76b
