module

public import CFSG.LocalAnalysis.ComponentClassification.GS79bSec5.FieldStandardProductUnique
import CFSG.LocalAnalysis.ComponentClassification.GS79bSec5.FieldStandardCentralizerRank
import CFSG.LocalAnalysis.ComponentClassification.GS79bSec5.FieldStandardPerfectPair
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62BSplitLocal
import CFSG.GroupTheory.Fitting.LayerProjection
import CFSG.GroupTheory.ElemAbelianClosure

public section

open Subgroup
open CFSG.LocalAnalysis.ComponentInitial LinearFlag FieldFourCover
open CFSG.LocalAnalysis.EvenBN.LinearThree
open CFSG.OddStandard.Seitz77 (Datum)

namespace CFSG.ComponentClassification.GS79bSec5

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {d : Datum A}

theorem pRank_centralizer_le_of_mulEquiv {K : Type} [Field K] [Finite K]
    (e : (A ⧸ center A) ≃* projectiveSL 3 K) {f : ℕ} (hf : 2 ≤ f) (hKc : Nat.card K = 2 ^ f) :
    CFSG.Open.pRank 2 (centralizer ({d.t} : Set G)) ≤ 2 * f + 1 := by
  have hX : CFSG.Blueprint.LieModel (A ⧸ center A) .PSL 3 2 f :=
    CFSG.SeitzReduction.LinearPilot.lieModel_of_mulEquiv_projectiveSL le_rfl (by omega) hKc e
  have h1 := pRank_le_two_mul_add_pRank_inf_centralizer_of_psl_three ⟨d.sector.standard.1.1⟩ hf hX
    (CFSG.EvenSmallLie.centralizer_le_normalizer_of_standard d.sector.standard d.t_mem_K
      d.sector.t_order)
  have h2 : CFSG.Open.pRank 2 (centralizer (A : Set G)) ≤ 1 := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    exact CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62BSplit.pRank_le_one_of_cyclic_sylow
      Nat.prime_two d.R d.sector.cyclic
  have h3 := CFSG.SectionRank.pRank_mono (p := 2) (by norm_num)
    (inf_le_right : centralizer ({d.t} : Set G) ⊓ centralizer (A : Set G) ≤ centralizer (A : Set G))
  omega

theorem false_of_nonswap_of_covers {K : Type} [Field K] [Finite K] [CharP K 2]
    (e : (A ⧸ center A) ≃* projectiveSL 3 K) {f : ℕ} (hf : 3 ≤ f) (hKc : Nat.card K = 2 ^ f)
    {X Y : Subgroup G}
    (πX : X →* projectiveSL 3 K) (hπX : Function.Surjective πX) (hkX : πX.ker ≤ center X)
    (hoX : Odd (Nat.card πX.ker))
    (πY : Y →* projectiveSL 3 K) (hπY : Function.Surjective πY) (hkY : πY.ker ≤ center Y)
    (hoY : Odd (Nat.card πY.ker))
    (htX : d.t ∈ normalizer (X : Set G)) (htY : d.t ∈ normalizer (Y : Set G))
    (hXY : Y ≤ centralizer (X : Set G)) (hXYinv : ∀ z ∈ X ⊓ Y, z * z = 1 → z = 1) : False := by
  have hrank := pRank_centralizer_le_of_mulEquiv (d := d) e (by omega) hKc
  have hprod : ∀ {E F : Subgroup G} {a b : ℕ}, E ≤ X ⊓ centralizer ({d.t} : Set G) →
      F ≤ Y ⊓ centralizer ({d.t} : Set G) → (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) →
      (∀ x ∈ E, x * x = 1) → Nat.card E = 2 ^ a → (∀ x ∈ F, ∀ y ∈ F, x * y = y * x) →
      (∀ x ∈ F, x * x = 1) → Nat.card F = 2 ^ b → a + b ≤ 2 * f + 1 := by
    intro E F a b hE hF hEc hE2 hEcard hFc hF2 hFcard
    have hEF : ∀ x ∈ E, ∀ y ∈ F, x * y = y * x := fun x hx y hy =>
      mem_centralizer_iff.1 (hXY (hF hy).1) x (hE hx).1
    have hinf : E ⊓ F = ⊥ := by
      rw [eq_bot_iff]
      rintro z ⟨hzE, hzF⟩
      exact hXYinv z ⟨(hE hzE).1, (hF hzF).1⟩ (hE2 z hzE)
    have hJcard : Nat.card ↥(E ⊔ F) = 2 ^ (a + b) := by
      rw [CFSG.LocalAnalysis.EvenBN.LinearThree.card_sup_of_commute hEF hinf, hEcard, hFcard,
        ← pow_add]
    have hJle : E ⊔ F ≤ centralizer ({d.t} : Set G) :=
      sup_le (fun x hx => (hE hx).2) fun y hy => (hF hy).2
    have hJab : CFSG.Open.IsElemAbelian 2 (E ⊔ F) :=
      CFSG.Open.IsElemAbelian.sup_of_commute (isElemAbelian_two_of_forall hEc hE2)
        (isElemAbelian_two_of_forall hFc hF2) hEF
    have hJrank : a + b ≤ CFSG.Open.pRank 2 (centralizer ({d.t} : Set G)) :=
      CFSG.SectionRank.le_pRank (p := 2) (by norm_num) hJle hJab hJcard
    omega
  have hq : Nat.card K ^ 2 = 2 ^ (2 * f) := by rw [hKc, ← pow_mul, mul_comm]
  have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
  rcases exists_fixed_four_of_mem_normalizer hf hKc πX hπX hkX hoX htX d.t_mul_self with
    ⟨EX, hEX, hEXc, hEX2, hEXcard⟩ | ⟨DX, hDX, hDXp, hcX, VX, hVX, hVXc, hVX2, hVXcard⟩ <;>
    rcases exists_fixed_four_of_mem_normalizer hf hKc πY hπY hkY hoY htY d.t_mul_self with
      ⟨EY, hEY, hEYc, hEY2, hEYcard⟩ | ⟨DY, hDY, hDYp, hcY, VY, hVY, hVYc, hVY2, hVYcard⟩
  ·
    have := hprod hEX hEY hEXc hEX2 (hEXcard.trans hq) hEYc hEY2 (hEYcard.trans hq)
    omega
  ·
    have := hprod hEX (hVY.trans hDY) hEXc hEX2 (hEXcard.trans hq) hVYc hVY2 (hVYcard.trans h4)
    omega
  · have := hprod (hVX.trans hDX) hEY hVXc hVX2 (hVXcard.trans h4) hEYc hEY2 (hEYcard.trans hq)
    omega
  ·
    let φ : ↥A →* projectiveSL 3 K := e.toMonoidHom.comp (QuotientGroup.mk' (center ↥A))
    have hφker : φ.ker = center ↥A :=
      (MonoidHom.ker_comp_of_injective _ _ e.injective).trans (QuotientGroup.ker_mk' _)
    have himg : ∀ {D : Subgroup G}, D ≤ A → ⁅D, D⁆ = D → (∃ c ∈ D, orderOf c = 2) →
        ⁅(D.subgroupOf A).map φ, (D.subgroupOf A).map φ⁆ = (D.subgroupOf A).map φ ∧
          (D.subgroupOf A).map φ ≠ ⊥ := by
      rintro D hDA hDp ⟨c, hcD, hc2⟩
      have hsub : ⁅D.subgroupOf A, D.subgroupOf A⁆ = D.subgroupOf A := by
        apply Subgroup.map_injective A.subtype_injective
        rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hDA, hDp]
      refine ⟨by rw [← Subgroup.map_commutator, hsub], fun hbot => ?_⟩
      have hle : D.subgroupOf A ≤ center ↥A := by
        rw [← hφker]
        exact (Subgroup.map_eq_bot_iff _).1 hbot
      have hD : D = ⊥ := by
        rw [← Subgroup.map_subgroupOf_eq_of_le hDA,
          CFSG.GroupTheory.eq_bot_of_commutator_eq_self_of_le_centralizer hsub
            (hle.trans (Subgroup.center_le_centralizer _)), Subgroup.map_bot]
      rw [hD, Subgroup.mem_bot] at hcD
      rw [hcD, orderOf_one] at hc2
      exact absurd hc2 (by norm_num)
    obtain ⟨hBp, hB1⟩ := himg (perfect_le_of_le_centralizer_of_mulEquiv (d := d) e hDXp
      fun y hy => (hDX hy).2) hDXp hcX
    obtain ⟨hCp, hC1⟩ := himg (perfect_le_of_le_centralizer_of_mulEquiv (d := d) e hDYp
      fun y hy => (hDY hy).2) hDYp hcY
    refine false_of_commute_perfect_of_odd_central_psl_three (F := K)
      (MonoidHom.id (projectiveSL 3 K)) (by rw [MonoidHom.ker_id]; exact bot_le)
      (by rw [MonoidHom.ker_id, Subgroup.card_bot]; exact odd_one) hBp hCp hB1 hC1 ?_
    intro b hb c hc
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hb
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hc
    have hxy : x * y = y * x := Subtype.ext <| mem_centralizer_iff.1
      (hXY (hDY (Subgroup.mem_subgroupOf.1 hy)).1) (x : G) (hDX (Subgroup.mem_subgroupOf.1 hx)).1
    rw [← map_mul, ← map_mul, hxy]

theorem false_of_nonswap_of_mulEquiv {K : Type} [Field K] [Finite K] [CharP K 2]
    (e : (A ⧸ center A) ≃* projectiveSL 3 K) {f : ℕ} (hf : 3 ≤ f) (hKc : Nat.card K = 2 ^ f)
    {P₁ P₂ : Subgroup G} (h₁₂ : P₂ ≤ centralizer (P₁ : Set G))
    (hZ : Odd (Nat.card (center ↥(P₁ ⊔ P₂))))
    (he₁ : Nonempty (↥P₁ ⧸ center ↥P₁ ≃* projectiveSL 3 K))
    (he₂ : Nonempty (↥P₂ ⧸ center ↥P₂ ≃* projectiveSL 3 K))
    (ht₁ : P₁.map (MulAut.conj d.t).toMonoidHom = P₁)
    (ht₂ : P₂.map (MulAut.conj d.t).toMonoidHom = P₂) : False := by
  obtain ⟨e₁⟩ := he₁
  obtain ⟨e₂⟩ := he₂
  have h₂₁ : P₁ ≤ centralizer (P₂ : Set G) := le_centralizer_iff.1 h₁₂
  have hcen : ∀ {z : G} (hz : z ∈ P₁ ⊔ P₂), z ∈ centralizer (P₁ : Set G) →
      z ∈ centralizer (P₂ : Set G) → (⟨z, hz⟩ : ↥(P₁ ⊔ P₂)) ∈ center ↥(P₁ ⊔ P₂) := by
    intro z hz h₁ h₂
    have hzC : z ∈ centralizer ((P₁ ⊔ P₂ : Subgroup G) : Set G) :=
      zpowers_le.1 (le_centralizer_sup_of_le_centralizers (zpowers_le.2 h₁) (zpowers_le.2 h₂))
    exact mem_center_iff.2 fun w => Subtype.ext (mem_centralizer_iff.1 hzC (w : G) w.2)
  have hZC : ∀ {P : Subgroup G} (z : center ↥P), (z : G) ∈ centralizer (P : Set G) := fun z =>
    mem_centralizer_iff.2 fun y hy => congrArg Subtype.val (mem_center_iff.1 z.2 ⟨y, hy⟩)
  have hoZ : ∀ {P : Subgroup G} (hP : P ≤ P₁ ⊔ P₂),
      (∀ z : center ↥P, (z : G) ∈ centralizer (P₁ : Set G) ∧ (z : G) ∈ centralizer (P₂ : Set G)) →
      Odd (Nat.card (center ↥P)) := fun hP h =>
    Odd.of_dvd_nat hZ <| Subgroup.card_dvd_of_injective
      (((inclusion hP).comp (center _).subtype).codRestrict _ fun z =>
        hcen (hP z.1.2) (h z).1 (h z).2)
      fun _ _ hab => Subtype.ext <| Subtype.ext <|
        congrArg (fun x : center ↥(P₁ ⊔ P₂) => (x : G)) hab
  let πX : P₁ →* projectiveSL 3 K := e₁.toMonoidHom.comp (QuotientGroup.mk' (center ↥P₁))
  let πY : P₂ →* projectiveSL 3 K := e₂.toMonoidHom.comp (QuotientGroup.mk' (center ↥P₂))
  have hkerX : πX.ker = center ↥P₁ :=
    (MonoidHom.ker_comp_of_injective _ _ e₁.injective).trans (QuotientGroup.ker_mk' _)
  have hkerY : πY.ker = center ↥P₂ :=
    (MonoidHom.ker_comp_of_injective _ _ e₂.injective).trans (QuotientGroup.ker_mk' _)
  refine false_of_nonswap_of_covers (d := d) e hf hKc πX
    (e₁.surjective.comp (QuotientGroup.mk'_surjective _)) hkerX.le ?_ πY
    (e₂.surjective.comp (QuotientGroup.mk'_surjective _)) hkerY.le ?_
    (CFSG.SeitzReduction.F4Pilot.mem_normalizer_iff_map_conj_toMonoidHom.2 ht₁)
    (CFSG.SeitzReduction.F4Pilot.mem_normalizer_iff_map_conj_toMonoidHom.2 ht₂) h₁₂
    fun z hz hzz => congrArg Subtype.val <| CFSG.CGT.Timmesfeld75.eq_one_of_mul_self_of_odd_card
      hZ (hcen (mem_sup_left hz.1) (h₁₂ hz.2) (h₂₁ hz.1)) (Subtype.ext hzz)
  · rw [hkerX]
    exact hoZ le_sup_left fun z => ⟨hZC z, h₂₁ z.1.2⟩
  · rw [hkerY]
    exact hoZ le_sup_right fun z => ⟨h₁₂ z.1.2, hZC z⟩

end CFSG.ComponentClassification.GS79bSec5

end
