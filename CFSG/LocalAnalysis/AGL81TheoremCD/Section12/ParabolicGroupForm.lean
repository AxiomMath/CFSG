module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.KFactParabolicWCent
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThreeThreeCasesN
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenDefs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CDefs

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.AGLEmbedding

variable {G : Type} [Group G] [Finite G]

section WCentSubgroup

variable {A : Type} [Group A]

private def wCentNormalizer (P : Subgroup A) : Subgroup A where
  carrier := {b | b ∈ Subgroup.normalizer (P : Set A) ∧
    CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.WCent P b}
  one_mem' := by
    refine ⟨Subgroup.one_mem _, ?_⟩
    intro w _ _
    simp
  mul_mem' := by
    rintro b₁ b₂ ⟨hb₁P, hb₁W⟩ ⟨hb₂P, hb₂W⟩
    refine ⟨Subgroup.mul_mem _ hb₁P hb₂P, ?_⟩
    intro w hw hwW
    have h₁ := hb₁W w hw hwW
    have h₂ := hb₂W w hw hwW
    have hb₁O : b₁ ∈ Subgroup.normalizer (pCoreOf 2 P : Set A) :=
      CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 P hb₁P
    have hconj : b₁ * (b₂ * w * b₂⁻¹ * w⁻¹) * b₁⁻¹ ∈ pCoreOf 2 P :=
      (Subgroup.mem_normalizer_iff.mp hb₁O _).mp h₂
    have heq : b₁ * b₂ * w * (b₁ * b₂)⁻¹ * w⁻¹ =
        b₁ * (b₂ * w * b₂⁻¹ * w⁻¹) * b₁⁻¹ * (b₁ * w * b₁⁻¹ * w⁻¹) := by
      group
    rw [heq]
    exact Subgroup.mul_mem _ hconj h₁
  inv_mem' := by
    rintro b ⟨hbP, hbW⟩
    refine ⟨Subgroup.inv_mem _ hbP, ?_⟩
    intro w hw hwW
    have h := hbW w hw hwW
    have hbO : b⁻¹ ∈ Subgroup.normalizer (pCoreOf 2 P : Set A) :=
      Subgroup.inv_mem _ (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 P hbP)
    have hconj : b⁻¹ * (b * w * b⁻¹ * w⁻¹)⁻¹ * b ∈ pCoreOf 2 P :=
      (by simpa using (Subgroup.mem_normalizer_iff.mp hbO _).mp (Subgroup.inv_mem (pCoreOf 2 P) h))
    have heq : b⁻¹ * w * b⁻¹⁻¹ * w⁻¹ = b⁻¹ * (b * w * b⁻¹ * w⁻¹)⁻¹ * b := by
      group
    rw [heq]
    exact hconj

end WCentSubgroup

omit [Finite G] in
private theorem barM_le_of_generators {M Y : Subgroup G} {S : Set G}
    (hY : Y = Subgroup.closure S) {B : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)}
    (hgen : ∀ x ∈ S, ∃ hxM : x ∈ M,
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨x, hxM⟩ ∈ B) :
    barM M Y ≤ B := by
  rintro z ⟨m, hm, rfl⟩
  have hmY : (m : G) ∈ Y := hm
  have hmS : (m : G) ∈ Subgroup.closure S := by rwa [hY] at hmY
  have hP : ∃ hmM : (m : G) ∈ M,
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨(m : G), hmM⟩ ∈ B :=
    Subgroup.closure_induction (k := S)
      (p := fun x _ => ∃ hxM : x ∈ M,
        QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨x, hxM⟩ ∈ B)
      (fun x hx => hgen x hx)
      ⟨M.one_mem, by
        have h : (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) (1 : ↥M) = 1 := map_one _
        change (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) (1 : ↥M) ∈ B
        rw [h]
        exact B.one_mem⟩
      (fun x y _ _ hpx hpy => by
        obtain ⟨hxM, hx⟩ := hpx
        obtain ⟨hyM, hy⟩ := hpy
        refine ⟨M.mul_mem hxM hyM, ?_⟩
        have heq : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨x * y, M.mul_mem hxM hyM⟩ =
            QuotientGroup.mk' (CFSG.pCore 2 ↥M) (⟨x, hxM⟩ * ⟨y, hyM⟩) := rfl
        rw [heq, map_mul]
        exact B.mul_mem hx hy)
      (fun x _ hpx => by
        obtain ⟨hxM, hx⟩ := hpx
        refine ⟨M.inv_mem hxM, ?_⟩
        have heq : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨x⁻¹, M.inv_mem hxM⟩ =
            QuotientGroup.mk' (CFSG.pCore 2 ↥M) (⟨x, hxM⟩)⁻¹ := rfl
        rw [heq, map_inv]
        exact B.inv_mem hx)
      hmS
  obtain ⟨hmM, hmem⟩ := hP
  have heq : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨(m : G), hmM⟩ =
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) m :=
    congrArg _ (Subtype.ext rfl)
  rwa [heq] at hmem

theorem commutator_mem_pCoreOf_M_of_isParabolicTwo (hWc : KFactParabolicWCentSolvable)
    {M H L Y : Subgroup G} {d : ℕ} (hdo : Odd d) (hL : IsTwoPrimeComponent M L)
    (hYHM : Y ≤ H ⊓ M) (hYgen : Y = oPPrimeHull d Y) (hperf : ⁅Y, Y⁆ = Y)
    (hYL : Y ≤ Subgroup.normalizer (L : Set G))
    (hYJ : ∀ b ∈ Y, ∀ x ∈ jZero H L, b * x * b⁻¹ * x⁻¹ ∈ pCoreOf 2 (jZero H L))
    (hcl : IsClassicalTwoOrG2 (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)))
    (hpar : IsParabolicTwo (barM M L) (barM M (H ⊓ L))) :
    ∀ b ∈ Y, ∀ l ∈ L, b * l * b⁻¹ * l⁻¹ ∈ pCoreOf 2 M := by
  have hYM : Y ≤ M := hYHM.trans inf_le_right
  have hYS : Y = Subgroup.closure {x : G | x ∈ Y ∧ ∃ k : ℕ, orderOf x = d ^ k} := by
    simpa only [oPPrimeHull] using hYgen
  let B : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M) :=
    Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ⊓
      wCentNormalizer (barM M (H ⊓ L))
  have hgen : ∀ x ∈ {x : G | x ∈ Y ∧ ∃ k : ℕ, orderOf x = d ^ k},
      ∃ hxM : x ∈ M, QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨x, hxM⟩ ∈ B := by
    intro x hx
    have hxM : x ∈ H ⊓ M := hYHM hx.1
    have hxo : Odd (orderOf x) := by
      obtain ⟨k, hk⟩ := hx.2
      rw [hk]
      exact hdo.pow
    obtain ⟨-, hNY, hNP, hW⟩ :=
      CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.bar_action_of_mem_normalizer
        hL.le hxM (hYL hx.1) hxo (hYJ x hx.1)
    exact ⟨hxM.2, ⟨hNY, hNP, hW⟩⟩
  have hle : barM M Y ≤ B := barM_le_of_generators hYS hgen
  have hperfbar : ⁅barM M Y, barM M Y⁆ = barM M Y := by
    have h1 : ⁅Y.subgroupOf M, Y.subgroupOf M⁆ = Y.subgroupOf M := by
      apply Subgroup.map_subtype_inj.mp
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hYM, hperf]
    rw [show barM M Y = (Y.subgroupOf M).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) from rfl,
      ← Subgroup.map_commutator (H₁ := Y.subgroupOf M) (H₂ := Y.subgroupOf M)
        (f := QuotientGroup.mk' (CFSG.pCore 2 ↥M)), h1]
  have hcent : ∀ r ∈ barM M Y, ∀ y ∈ barM M L, r * y = y * r :=
    hWc (↥M ⧸ CFSG.pCore 2 ↥M) (barM M L) (barM M (H ⊓ L)) B
      hL.component.2.2
      (CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.pCoreOf_barM_eq_bot hL)
      hcl hpar (fun b hb => hb.1) (fun b hb => hb.2.1) (fun b hb => hb.2.2)
      (barM M Y) hle hperfbar
  intro b hbY l hl
  have hbM : b ∈ M := (hYHM hbY).2
  have hbYbar : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hbM⟩ ∈ barM M Y :=
    Subgroup.mem_map.mpr ⟨⟨b, hbM⟩, hbY, rfl⟩
  exact CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.commutator_mem_pCoreOf_of_centralizes
    hL.le hbM (fun y hy => hcent _ hbYbar y hy) l hl

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
