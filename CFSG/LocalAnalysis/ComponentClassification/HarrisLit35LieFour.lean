module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit35LieOdd
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit35LieOrder
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10LinRow

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.L35

open CFSG Subgroup GrSLit.L34Facts CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatLeafProof.X10Lin
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem eq_of_mem_linTuples {d k e : ℕ} (hd : 4 ≤ d)
    (hT : ((.PSL : StatedLieTag), 2, e) ∈ linTuples d k) : d = 4 ∧ (e = k ∨ e = 2 * k) := by
  simp only [linTuples, linInnerTuples, graphTuples, orthTuples, Set.mem_ofPred_eq,
    Prod.mk.injEq, reduceCtorEq, true_and, false_and, and_false, or_false, false_or] at hT
  rcases hT with (⟨j, -, hj3, -, hj2, -⟩ | ⟨⟨i, rfl⟩, hd2, he⟩) |
      (⟨hd3, -⟩ | ⟨hd4, he⟩ | ⟨-, h24, -⟩) | ⟨j, -, hd2, -⟩
  · omega
  · exact ⟨by omega, Or.inr he⟩
  · omega
  · exact ⟨hd4, he⟩
  · omega
  · omega

theorem eq_of_mem_linUTuples {d k e : ℕ} (hd : 4 ≤ d)
    (hT : ((.PSL : StatedLieTag), 2, e) ∈ linUTuples d k) : d = 4 ∧ (e = k ∨ e = 2 * k) := by
  simp only [linUTuples, linUInnerTuples, graphTuples, orthTuples, Set.mem_ofPred_eq,
    Prod.mk.injEq, reduceCtorEq, true_and, false_and, and_false, or_false, false_or] at hT
  rcases hT with (⟨-, h⟩ | ⟨⟨i, rfl⟩, hd2, he⟩) | ⟨hd3, -⟩ | ⟨hd4, he⟩ | ⟨-, h24, -⟩
  · exact h.elim
  · exact ⟨by omega, Or.inr he⟩
  · omega
  · exact ⟨hd4, he⟩
  · omega

namespace Config

variable {G : Type} [Group G] [Finite G] {p : ℕ} {w v : G} {L K : Subgroup G}

theorem card_center_dvd_of_surjective (h : Config G p w v L K) {B : Type} [Group B] [Finite B]
    (φ : ↥L →* B) (hφ : Function.Surjective φ) (hw : φ ⟨w, h.w_mem_L⟩ = 1) {f : ℕ}
    (hf : 1 ≤ f) (h5 : 5 ≤ p ^ f) (hLsl : IsSLTwoOver (p ^ f) (↥L ⧸ pPrimeCore 2 ↥L))
    (hB : Blueprint.LieModel (B ⧸ center B) .PSL 2 p f) :
    Nat.card ↥(center B) ∣ Nat.card ↥(pPrimeCore 2 ↥L) := by
  obtain ⟨-, hQZ, hQm, -⟩ := Lemma47.sl2_facts h.prime h.ne_two hf h5 hLsl
  have hcB := GSThmB.card_of_lieModel_psl_two h.ne_two hB
  have hcQ := GSThmB.card_of_lieModel_psl_two h.ne_two hQm
  have hA : 0 < Open.ordA 1 (p ^ f) := by
    rw [← hcB]
    exact Nat.card_pos
  have hL1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥L)
  have hL2 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (center (↥L ⧸ pPrimeCore 2 ↥L))
  rw [hcQ, hQZ] at hL2
  have hB1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center B)
  rw [hcB] at hB1
  have hK1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv] at hK1
  have hw2 : orderOf (⟨⟨w, h.w_mem_L⟩, MonoidHom.mem_ker.mpr hw⟩ : ↥φ.ker) = 2 := by
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, h.orderOf_w]
  have h2K : 2 ∣ Nat.card ↥φ.ker := hw2 ▸ orderOf_dvd_natCard _
  obtain ⟨j, hj⟩ := h2K
  have key : Open.ordA 1 (p ^ f) * (Nat.card ↥(center B) * j) =
      Open.ordA 1 (p ^ f) * Nat.card ↥(pPrimeCore 2 ↥L) := by
    have h1 : Nat.card ↥L = Open.ordA 1 (p ^ f) * Nat.card ↥(center B) * (2 * j) := by
      rw [hK1, hB1, hj]
    have h2 : Nat.card ↥L = Open.ordA 1 (p ^ f) * 2 * Nat.card ↥(pPrimeCore 2 ↥L) := by
      rw [hL1, hL2]
    have h3 := h1.symm.trans h2
    have h4 : 2 * (Open.ordA 1 (p ^ f) * (Nat.card ↥(center B) * j)) =
        2 * (Open.ordA 1 (p ^ f) * Nat.card ↥(pPrimeCore 2 ↥L)) :=
      calc 2 * (Open.ordA 1 (p ^ f) * (Nat.card ↥(center B) * j))
          = Open.ordA 1 (p ^ f) * Nat.card ↥(center B) * (2 * j) := by ring
        _ = Open.ordA 1 (p ^ f) * 2 * Nat.card ↥(pPrimeCore 2 ↥L) := h3
        _ = 2 * (Open.ordA 1 (p ^ f) * Nat.card ↥(pPrimeCore 2 ↥L)) := by ring
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h4
  exact ⟨j, (Nat.eq_of_mul_eq_mul_left hA key).symm⟩

theorem four_of_partialCover (h : Config G p w v L K) {n k : ℕ} (hn : 2 ≤ n)
    (hm : Blueprint.LieModel (↥K ⧸ Open.fusionZStar ↥K) .PSL (2 * n) p k ∨
      Blueprint.LieModel (↥K ⧸ Open.fusionZStar ↥K) .PSU (2 * n) p k) :
    n = 2 ∧ (IsSLTwoOver (p ^ k) (↥L ⧸ pPrimeCore 2 ↥L) ∨
      IsSLTwoOver (p ^ (2 * k)) (↥L ⧸ pPrimeCore 2 ↥L)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨eZ⟩ := h.nonempty_bar_equiv
  have hq := h.quasisimple_quot
  have : IsSimpleGroup ((↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K)) := hq.2.1
  have hsq : quotAut h.tau * quotAut h.tau = 1 := by
    ext y
    exact h.quotAut_tau_sq y
  have hσ2 : orderOf (quotAut h.tau) = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hsq) h.quotAut_tau_ne_one
  obtain ⟨τ, hτ, hmS⟩ : ∃ τ : StatedLieTag, (τ = .PSL ∨ τ = .PSU) ∧
      Blueprint.LieModel ((↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K)) τ (2 * n)
        p k := by
    rcases hm with hm | hm
    · exact ⟨.PSL, Or.inl rfl, GSThmB.OddQuot.lieModel_of_equiv eZ hm⟩
    · exact ⟨.PSU, Or.inr rfl, GSThmB.OddQuot.lieModel_of_equiv eZ hm⟩
  have hadm := N36.admissible_of_lieModel' hmS
  set F := fixedSubgroup (quotAut h.tau) with hFdef
  have hc : IsTwoComponentIn (hatOf K L) F := h.isTwoComponentIn_hat h.compLK
  have hpc := (isTwoComponentIn_iff hc.1).mp hc
  have hqL : IsQuasisimple ↥((hatOf K L).subgroupOf F) :=
    fixedTwoComponentsQuasisimple_lin h.ne_two hτ hadm hmS (quotAut h.tau) hsq
      h.quotAut_tau_ne_one _ hpc
  have hcomp : IsComponent ((hatOf K L).subgroupOf F) := by
    obtain ⟨-, -, hsub, -⟩ := hpc
    exact ⟨hqL, hsub⟩
  obtain ⟨f, hf, hs5, hLsl⟩ := h.slTwo
  obtain ⟨-, -, hQm, -⟩ := Lemma47.sl2_facts h.prime h.ne_two hf hs5 hLsl
  let g : ↥L →* ↥((hatOf K L).subgroupOf F) :=
    (subgroupOfEquivOfLe hc.1).symm.toMonoidHom.comp (hatHom h.L_le)
  have hg : Function.Surjective g :=
    (subgroupOfEquivOfLe hc.1).symm.surjective.comp (hatHom_surjective h.L_le)
  obtain ⟨e⟩ := h.nonempty_centralQuot_of_quasisimple hqL g hg
  have hLm : Blueprint.LieModel (↥((hatOf K L).subgroupOf F) ⧸
      center ↥((hatOf K L).subgroupOf F)) .PSL 2 p f := GSThmB.OddQuot.lieModel_of_equiv e hQm
  have hgw : g ⟨w, h.w_mem_L⟩ = 1 := by
    apply (subgroupOfEquivOfLe hc.1).injective
    rw [map_one]
    apply Subtype.ext
    change QuotientGroup.mk (QuotientGroup.mk (⟨w, h.w_mem_K⟩ : ↥K)) =
      (1 : (↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K))
    exact (QuotientGroup.eq_one_iff _).mpr h.wbar_mem_center
  have hZodd : ¬ 2 ∣ Nat.card ↥(center ↥((hatOf K L).subgroupOf F)) := by
    intro h2
    have hd := h.card_center_dvd_of_surjective g hg hgw hf hs5 hLsl hLm
    exact (Nat.prime_two.coprime_iff_not_dvd.mp pPrimeCore_coprime_card) (h2.trans hd)
  have hcases : ∃ T : Set (StatedLieTag × ℕ × ℕ),
      ComponentCases p T ((hatOf K L).subgroupOf F) ∧
      (∀ {t m e}, (t, m, e) ∈ T → IsClassicalTag t) ∧
      (∀ {e}, ((.PSL : StatedLieTag), 2, e) ∈ T → 2 * n = 4 ∧ (e = k ∨ e = 2 * k)) := by
    rcases hτ with rfl | rfl
    · exact ⟨linTuples (2 * n) k, psl_component_cases h.prime h.ne_two hadm hmS hσ2 hcomp,
        isClassicalTag_of_mem_linTuples, fun hT => eq_of_mem_linTuples (by omega) hT⟩
    · exact ⟨linUTuples (2 * n) k, psu_component_cases h.ne_two hadm hmS hσ2 hcomp,
        isClassicalTag_of_mem_linUTuples, fun hT => eq_of_mem_linUTuples (by omega) hT⟩
  obtain ⟨T, hC, hcl, hpsl⟩ := hcases
  rcases hC with ⟨z, hzL, hzc, hzz, hz1⟩ | ⟨t, m, e', hT, hadm', hm'⟩
  ·
    exfalso
    apply hZodd
    have hzZ : (⟨z, hzL⟩ : ↥((hatOf K L).subgroupOf F)) ∈ center _ :=
      mem_center_iff.2 fun y => Subtype.ext (hzc y y.2).symm
    have hz2 : orderOf (⟨⟨z, hzL⟩, hzZ⟩ : ↥(center ↥((hatOf K L).subgroupOf F))) = 2 := by
      refine orderOf_eq_prime ?_ ?_
      · rw [pow_two]
        exact Subtype.ext (Subtype.ext hzz)
      · intro h1
        apply hz1
        have h2 := congrArg Subtype.val (congrArg Subtype.val h1)
        exact h2
    have hd := orderOf_dvd_natCard (⟨⟨z, hzL⟩, hzZ⟩ : ↥(center ↥((hatOf K L).subgroupOf F)))
    rwa [hz2] at hd
  · by_cases hpm : t = .PSL ∧ m = 2
    · obtain ⟨rfl, rfl⟩ := hpm
      obtain ⟨hd4, he'⟩ := hpsl hT
      have h1 := (lieOrder_of_lieModel_classical (Or.inl rfl) h.ne_two (by norm_num) hm').2
      have h2 := (lieOrder_of_lieModel_classical (Or.inl rfl) h.ne_two (by norm_num) hLm).2
      have hfe : f = e' := by
        have h3 := h2.symm.trans h1
        simpa [CatLeaf.lieSylowExponent] using h3
      subst hfe
      refine ⟨by omega, ?_⟩
      rcases he' with rfl | rfl
      · exact Or.inl hLsl
      · exact Or.inr hLsl
    · exfalso
      have hrank : t = .PSL → 3 ≤ m := by
        intro ht
        subst ht
        have : 2 ≤ m := hadm'.2.2.1
        have : m ≠ 2 := fun hm2 => hpm ⟨rfl, hm2⟩
        omega
      exact false_of_pslTwo_of_classical h.ne_two (hcl hT) hrank hadm' hm' hLm

end Config

end CFSG.ComponentClassification.HarrisLit.L35
