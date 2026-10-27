module

public import CFSG.LieType.OutStructureFiveDispatch
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineTenCompGen

public section

namespace CFSG.LieType.OutStructure

open CFSG.ComponentClassification.OuterAutomorphisms

theorem isPClosedMod_of_not_outFiveExceptional
    {X : Type} [Group X] [Finite X] (hK : CFSG.Open.IsKGroup X) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) {L : Subgroup X} (hL : CFSG.IsComponent L) (hLn : L.Normal)
    (hne : ¬ OutFiveExceptional (↥L ⧸ Subgroup.center ↥L) p) :
    CFSG.LocalAnalysis.RankThreeUC.AGL81C.IsPClosedMod p
      (L ⊔ Subgroup.centralizer (L : Set X)) := by
  have := hLn
  have : Fact p.Prime := ⟨hp⟩
  have : Group.IsPerfect ↥L := hL.1.1
  have : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hL.1.2.1
  have hq : CFSG.Open.IsQuasisimple ↥L := ⟨Group.isPerfect_def.mp hL.1.1, hL.1.2.1⟩
  have hnab : ∃ a b : ↥L ⧸ Subgroup.center ↥L, a * b ≠ b * a :=
    CFSG.LocalAnalysis.RankThreeUC.S15.K7145Proof.quotient_center_nonabelian hq
  have hcat : CFSG.Open.IsCatalogGroup (↥L ⧸ Subgroup.center ↥L) :=
    CFSG.LocalAnalysis.RankThreeUC.S15.K7145Proof.isCatalogGroup_quotient_center hK L hq
  have hOut := (sylow_normal_outer_five_or_exceptional hL.1.2.1 hnab hcat hp hp5).resolve_right hne
  have hOutL : ∀ S : Sylow p (Outer ↥L), (S : Subgroup (Outer ↥L)).Normal :=
    CFSG.LocalAnalysis.RankThreeTheoremC.SevenFourTwo.sylow_normal_of_injective
      (centerQuotient_outer_injective ↥L) hOut
  obtain ⟨R⟩ : Nonempty (Sylow p X) := inferInstance
  exact CFSG.LocalAnalysis.RankThreeTheoremC.SevenFourTwo.isPClosedMod_of_normal_sup_sylow R
    (CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.normal_sup_sup_centralizer_of_outer L R hOutL)

theorem OutFiveExceptional.of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B) {p : ℕ}
    (h : OutFiveExceptional B p) : OutFiveExceptional A p := by
  rcases h with ⟨N, r, f, hcl, hN, hℓ⟩ | ⟨N, r, f, hcl, hN, hℓ⟩
  · exact Or.inl ⟨N, r, f, CFSG.SectionRank.statedClassicalModel_of_mulEquiv e hcl, hN, hℓ⟩
  · exact Or.inr ⟨N, r, f, CFSG.SectionRank.statedClassicalModel_of_mulEquiv e hcl, hN, hℓ⟩

end CFSG.LieType.OutStructure

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open CFSG.LocalAnalysis.RankThreeUC.S15 Subgroup

theorem nineTenPClosed_of_exceptional
    (hex : ∀ (G : Type) [Group G] [Finite G] (M Q H E : Subgroup G) (p : ℕ),
      NineSettingGen G M p Q H E 2 → H ∈ H2Fam M Q → p ∉ sigmaM G M → 3 < p →
      ∀ C : Subgroup (StarGroup p H), CFSG.IsComponent C → 2 ≤ CFSG.Open.pRank 3 C →
        CFSG.LieType.OutStructure.OutFiveExceptional (↥C ⧸ Subgroup.center ↥C) p →
        IsPClosedMod p ((C ⊔ centralizer (C : Set (StarGroup p H))).subgroupOf
          (normalizer (C : Set (StarGroup p H))))) :
    ∀ (G : Type) [Group G] [Finite G] (M Q H E : Subgroup G) (p : ℕ),
      NineSettingGen G M p Q H E 2 → H ∈ H2Fam M Q → p ∉ sigmaM G M → 3 < p →
      ∀ C : Subgroup (StarGroup p H), CFSG.IsComponent C → 2 ≤ CFSG.Open.pRank 3 C →
        IsPClosedMod p ((C ⊔ centralizer (C : Set (StarGroup p H))).subgroupOf
          (normalizer (C : Set (StarGroup p H)))) := by
  intro G _ _ M Q H E p h hH2 hp hp3 C hC h3C
  by_cases hexC : CFSG.LieType.OutStructure.OutFiveExceptional (↥C ⧸ Subgroup.center ↥C) p
  · exact hex G M Q H E p h hH2 hp hp3 C hC h3C hexC
  have hp5 : 5 ≤ p := by
    have hp4 : p ≠ 4 := by
      rintro rfl
      exact (by decide : ¬ Nat.Prime 4) h.prime
    omega
  let N : Subgroup (StarGroup p H) := normalizer (C : Set (StarGroup p H))
  have hKN : CFSG.Open.IsKGroup ↥N := h.isKGroup_star.subgroup N
  have hcomp : CFSG.IsComponent (C.subgroupOf N) :=
    CFSG.LocalCores.component_overgroup hC Subgroup.le_normalizer
  have hnorm : (C.subgroupOf N).Normal := Subgroup.normal_in_normalizer
  let e : ↥(C.subgroupOf N) ≃* ↥C := Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer
  have hne : ¬ CFSG.LieType.OutStructure.OutFiveExceptional
      (↥(C.subgroupOf N) ⧸ Subgroup.center ↥(C.subgroupOf N)) p := fun hE =>
    hexC (hE.of_mulEquiv (QuotientGroup.congr (center ↥(C.subgroupOf N)) (center ↥C) e
      (Subgroup.map_center_eq e)).symm)
  have hres := CFSG.LieType.OutStructure.isPClosedMod_of_not_outFiveExceptional hKN h.prime hp5
    hcomp hnorm hne
  have heq : (C.subgroupOf N) ⊔ centralizer (C.subgroupOf N : Set ↥N) =
      (C ⊔ centralizer (C : Set (StarGroup p H))).subgroupOf N := by
    rw [CFSG.centralizer_subgroupOf_eq C N Subgroup.le_normalizer]
    rw [Subgroup.subgroupOf_sup Subgroup.le_normalizer
      (Subgroup.centralizer_le_normalizer (C : Set (StarGroup p H)))]
  rw [heq] at hres
  exact hres

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
