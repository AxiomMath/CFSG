module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.L28.ThreeQuotient.Rank
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294OuterDiag
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherLinearAutNormal

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.L28.ThreeQuotient

open CFSG CFSG.Open Subgroup
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.RankFourTheoremC (IsLinearOrUnitaryAt)
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
open scoped commutatorElement

theorem ringAut_comm {F : Type} [Field F] [Finite F] (σ τ : F ≃+* F) : σ * τ = τ * σ := by
  obtain ⟨r, f, hr, -, -, hF⟩ := CFSG.LocalAnalysis.RankFourTheoremC.exists_char_pow_card F
  have := (card_ringAut_and_isCyclic hr F hF).2
  exact IsCyclic.commGroup.mul_comm σ τ

theorem commutatorElement_mem_linearAutGroup {n : ℕ} {F : Type} [Field F] [Finite F]
    (hn : 3 ≤ n) (α β : MulAut (projectiveSL n F)) : ⁅α, β⁆ ∈ linearAutGroup n F := by
  haveI := linearAutGroup_normal_of_three_le (K := F) hn
  obtain ⟨-, hgen⟩ := automorphism_generation (K := F) hn
  obtain ⟨A, σ, ε, -, rfl⟩ := hgen α
  obtain ⟨B, τ, η, -, rfl⟩ := hgen β
  have hfd : ∀ ρ, Commute (fieldAut n F ρ) (dualAut n F) := fun ρ =>
    (dualAut_mul_fieldAut ρ).symm
  have hff : Commute (fieldAut n F σ) (fieldAut n F τ) := by
    change _ * _ = _ * _
    rw [← map_mul, ← map_mul, ringAut_comm]
  have huv : Commute (fieldAut n F σ * dualAut n F ^ ε) (fieldAut n F τ * dualAut n F ^ η) :=
    (hff.mul_right ((hfd σ).pow_right η)).mul_left
      (((hfd τ).pow_right ε).symm.mul_right ((Commute.refl _).pow_pow ε η))
  have hc : ∀ C : GL (Fin n) F, QuotientGroup.mk' (linearAutGroup n F) (conjAut n F C) = 1 :=
    fun C => (QuotientGroup.eq_one_iff _).2 (conjAut_mem_linearAutGroup C)
  have e1 : QuotientGroup.mk' (linearAutGroup n F) (conjAut n F A * fieldAut n F σ *
      dualAut n F ^ ε) = QuotientGroup.mk' (linearAutGroup n F) (fieldAut n F σ *
      dualAut n F ^ ε) := by rw [mul_assoc, map_mul, hc, one_mul]
  have e2 : QuotientGroup.mk' (linearAutGroup n F) (conjAut n F B * fieldAut n F τ *
      dualAut n F ^ η) = QuotientGroup.mk' (linearAutGroup n F) (fieldAut n F τ *
      dualAut n F ^ η) := by rw [mul_assoc, map_mul, hc, one_mul]
  rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement, e1, e2,
    ← map_commutatorElement, commutatorElement_eq_one_iff_mul_comm.2 huv, map_one]

theorem commutatorElement_mem_psuConj_range {p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) (hq : 2 < p ^ f) (α β : MulAut (unitaryPSU h 3)) :
    ⁅α, β⁆ ∈ (psuConj h).range := by
  haveI : (psuConj h).range.Normal := (stdPinnedPSU3_stable hq).normal
  haveI := h.finite
  obtain ⟨A, σ, rfl⟩ := exists_psuConj_mul_psuField hq α
  obtain ⟨B, τ, rfl⟩ := exists_psuConj_mul_psuField hq β
  have hff : Commute (psuField h σ) (psuField h τ) := by
    change _ * _ = _ * _
    rw [← map_mul, ← map_mul, ringAut_comm]
  have hc : ∀ C : unitaryIsom3 h, QuotientGroup.mk' (psuConj h).range (psuConj h C) = 1 :=
    fun C => (QuotientGroup.eq_one_iff _).2 ⟨C, rfl⟩
  rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement, map_mul,
    map_mul, hc, hc, one_mul, one_mul, ← map_commutatorElement,
    commutatorElement_eq_one_iff_mul_comm.2 hff, map_one]

theorem card_le_nine_of_le_psuConj_range {p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) (h30 : (3 : K) ≠ 0) {B : Subgroup (MulAut (unitaryPSU h 3))}
    (hB : IsElemAbelian 3 B) (hBN : B ≤ (psuConj h).range) : Nat.card B ≤ 9 := by
  set N := (psuConj h).range with hN
  set ψ : unitaryIsom3 h →* GL (Fin 3) K ⧸ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 3) K :=
    (QuotientGroup.mk' _).comp (unitaryIsom3 h).subtype
  have hk : (psuConj h).ker = ψ.ker := by
    ext A
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, psuConj_eq_one_iff]
    change _ ↔ QuotientGroup.mk' _ (A : GL (Fin 3) K) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  set χ : N →* GL (Fin 3) K ⧸ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 3) K :=
    (QuotientGroup.kerLift ψ).comp ((QuotientGroup.quotientMulEquivOfEq hk).toMonoidHom.comp
      (QuotientGroup.quotientKerEquivRange (psuConj h)).symm.toMonoidHom)
  have hχ : Function.Injective χ :=
    (QuotientGroup.kerLift_injective ψ).comp
      ((QuotientGroup.quotientMulEquivOfEq hk).injective.comp
        (QuotientGroup.quotientKerEquivRange (psuConj h)).symm.injective)
  set E := ((B ⊓ N).subgroupOf N).map χ
  have hcardE : Nat.card E = Nat.card (B ⊓ N : Subgroup _) := by
    rw [Subgroup.card_map_of_injective hχ]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hB.1.1.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have h99 : Nat.card (B ⊓ N : Subgroup _) ≤ 9 := by
    rw [← hcardE]
    refine card_le_nine_of_pgl3 h30 E ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact hBc _ (Subgroup.mem_subgroupOf.mp hx).1 _ (Subgroup.mem_subgroupOf.mp hy).1
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow]
      have : x ^ 3 = 1 := Subtype.ext (by
        rw [Subgroup.coe_pow, Subgroup.coe_one]
        exact hB.2 _ (Subgroup.mem_subgroupOf.mp hx).1)
      rw [this, map_one]
  rwa [inf_eq_left.2 hBN] at h99

theorem three_ne_zero_of_dvd_card_sub_one {F : Type} [Field F] [Finite F]
    (h3F : 3 ∣ Nat.card F - 1) : (3 : F) ≠ 0 := by
  obtain ⟨r, f, hr, hchar, hf, hF⟩ := CFSG.LocalAnalysis.RankFourTheoremC.exists_char_pow_card F
  haveI := hchar
  refine od_three_ne_zero_of_charP hr ?_
  rintro rfl
  rw [hF] at h3F
  exact od_not_three_dvd_three_pow_sub_one hf h3F

variable {X : Type} [Group X] [Finite X]

theorem map_commutator_le {L : Type*} [Group L] (ρ : X →* MulAut L) (D : Subgroup (MulAut L))
    (hD : ∀ α β : MulAut L, ⁅α, β⁆ ∈ D) : Subgroup.map ρ ⁅(⊤ : Subgroup X), ⊤⁆ ≤ D := by
  rw [Subgroup.map_commutator]
  exact (Subgroup.commutator_le.2 fun α _ β _ => hD α β)

theorem false_of_commutator_le {L : Type*} [Group L] (ρ : X →* MulAut L)
    (hρ : Function.Injective ρ) (D : Subgroup (MulAut L)) (hD : ∀ α β : MulAut L, ⁅α, β⁆ ∈ D)
    (hD9 : ∀ B : Subgroup (MulAut L), IsElemAbelian 3 B → B ≤ D → Nat.card B ≤ 9)
    (S : Sylow 3 X) {Q₀ : Subgroup X} (hDS : ShapeData (S : Subgroup X) Q₀)
    (hS : (S : Subgroup X) ≤ ⁅(⊤ : Subgroup X), ⊤⁆) : False := by
  obtain ⟨E, hES, hE, hEcard, -⟩ := hDS.exists_omega
  have hle : E.map ρ ≤ D :=
    (Subgroup.map_mono (hES.trans hS)).trans (map_commutator_le ρ D hD)
  have h9 := hD9 _ (CFSG.SectionRank.isElemAbelian_map hE ρ) hle
  rw [Subgroup.card_map_of_injective hρ, hEcard] at h9
  norm_num at h9

theorem false_of_linearOrUnitary (K : Subgroup X) [K.Normal]
    (hKC : Subgroup.centralizer (K : Set X) = ⊥) [IsSimpleGroup K]
    (hnab : ∃ a b : K, a * b ≠ b * a) (S : Sylow 3 X) {Q₀ : Subgroup X}
    (hDS : ShapeData (S : Subgroup X) Q₀) (hS : (S : Subgroup X) ≤ ⁅(⊤ : Subgroup X), ⊤⁆)
    (hLU : IsLinearOrUnitaryAt 3 K) : False := by
  have hrank := hDS.pRank_le_three S
  have hρ : Function.Injective (MulAut.conjNormal : X →* MulAut K) :=
    i294_conjNormal_injective hKC
  rcases hLU with ⟨n, F, _, _, h3n, h3F, ⟨e⟩⟩ | ⟨n, q, F, _, _, hFq, h3n, h3q, ⟨e⟩⟩
  ·
    have hn0 : n ≠ 0 := by
      rintro rfl
      haveI : Subsingleton (StatedProj (StatedSL 0 F)) := inferInstance
      exact od_false_of_zero_dim hnab e
    by_cases hn3 : n = 3
    · subst hn3
      let e' : K ≃* projectiveSL 3 F :=
        e.trans (CFSG.LocalAnalysis.RankFourTheoremC.l212in_projectiveSLEquivStated 3 F).symm
      have h30 := three_ne_zero_of_dvd_card_sub_one h3F
      refine false_of_commutator_le
        ((MulAut.congr e').toMonoidHom.comp (MulAut.conjNormal : X →* MulAut K))
        ((MulAut.congr e').injective.comp hρ) (linearAutGroup 3 F)
        (commutatorElement_mem_linearAutGroup le_rfl) (fun B hB hBD => ?_) S hDS hS
      have h := card_inf_linearAutGroup_three_le h30 hB
      rwa [inf_eq_left.2 hBD] at h
    · have hn6 : 6 ≤ n := by omega
      have h4 := odFour_le_pRank_psl Nat.prime_three hn6 h3F
      have h1 : CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedSL n F))) ≤
          CFSG.Open.pRank 3 (⊤ : Subgroup X) :=
        CFSG.SectionRank.pRank_top_le_of_injective (by norm_num)
          (K.subtype.comp e.symm.toMonoidHom) (K.subtype_injective.comp e.symm.injective)
      omega
  ·
    have hn0 : n ≠ 0 := by
      rintro rfl
      haveI : Subsingleton (StatedProj (StatedSU 0 q F)) := inferInstance
      exact od_false_of_zero_dim hnab e
    obtain ⟨r, m, hr, hchar, -, hFr⟩ := CFSG.LocalAnalysis.RankFourTheoremC.exists_char_pow_card F
    haveI : Fact r.Prime := ⟨hr⟩
    haveI := hchar
    obtain ⟨f, -, hqf⟩ : ∃ f ≤ m, q = r ^ f := by
      refine (Nat.dvd_prime_pow hr).1 ?_
      rw [← hFr, hFq]
      exact dvd_pow_self q two_ne_zero
    subst hqf
    have hf : 1 ≤ f := by
      rcases Nat.eq_zero_or_pos f with rfl | hf
      · exfalso
        rw [pow_zero] at hFq
        have : Nat.card F = 1 := by rw [hFq]; norm_num
        have h2 : 1 < Nat.card F := Finite.one_lt_card
        omega
      · exact hf
    have hU : UnitaryFieldData r f F := ⟨hr, hf, by rw [hFq, ← pow_mul, mul_comm]⟩
    by_cases hn3 : n = 3
    · subst hn3
      by_cases hq2 : r ^ f = 2
      · exact uniThree_two_false hFq hf hq2 hnab e
      · have hq : 2 < r ^ f := by
          have hq1 : 1 < r ^ f := Nat.one_lt_pow (by omega) hr.one_lt
          omega
        have hr3 : r ≠ 3 := by
          rintro rfl
          have h1 : 3 ∣ 3 ^ f := dvd_pow_self 3 (by omega)
          have := (Nat.dvd_add_right h1).1 h3q
          omega
        have h30 : (3 : F) ≠ 0 := od_three_ne_zero_of_charP hr hr3
        let e' : K ≃* unitaryPSU hU 3 := e.trans (unitaryPSUEquiv hU (by norm_num)).symm
        exact false_of_commutator_le
          ((MulAut.congr e').toMonoidHom.comp (MulAut.conjNormal : X →* MulAut K))
          ((MulAut.congr e').injective.comp hρ) (psuConj hU).range
          (commutatorElement_mem_psuConj_range hU hq)
          (fun B hB hBD => card_le_nine_of_le_psuConj_range hU h30 hB hBD) S hDS hS
    · have hn6 : 6 ≤ n := by omega
      have h4 := odFour_le_pRank_psu hU Nat.prime_three hn6 h3q
      have h1 : CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedSU n (r ^ f) F))) ≤
          CFSG.Open.pRank 3 (⊤ : Subgroup X) :=
        CFSG.SectionRank.pRank_top_le_of_injective (by norm_num)
          (K.subtype.comp e.symm.toMonoidHom) (K.subtype_injective.comp e.symm.injective)
      omega

end CFSG.LocalAnalysis.RankThreeTheoremC.L28.ThreeQuotient
