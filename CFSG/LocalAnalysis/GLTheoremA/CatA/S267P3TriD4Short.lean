module

public import CFSG.RankThree.PartTwo.Sec11.KS11Lie4ProofD4
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
import CFSG.LocalAnalysis.GLTheoremA.PartI.KD26h.Glue
import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.P3

open CFSG.LieType.Chevalley
open CFSG.Blueprint.Chevalley (TwistTag ModGL entrywiseHom)
open CFSG.Open (GLAPLayer)
open CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof (d4Outer d4ShortSL2)

theorem triD4_SL2_hom_ext {F : Type*} [Field F] {G : Type*} [Group G] {φ ψ : SL2 F →* G}
    (hu : ∀ s, φ (uSL s) = ψ (uSL s)) (hv : ∀ s, φ (vSL s) = ψ (vSL s)) : φ = ψ :=
  MonoidHom.eq_of_eqOn_dense
    (CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower (K := F)) fun g hg => by
      rcases hg with ⟨c, rfl⟩ | ⟨c, rfl⟩
      · exact hu c
      · exact hv c

theorem triD4_map_neg_one {E F : Type*} [Field E] [Field F] (f : E →+* F) :
    Matrix.SpecialLinearGroup.map f (-1 : SL2 E) = -1 :=
  Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.map_apply_coe, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
      Matrix.SpecialLinearGroup.coe_one, map_neg, map_one])

theorem triD4_exists_sl2_map_eq {E F : Type*} [Field E] [Field F] (ι : E →+* F) (B : SL2 F)
    (h : ∀ i j, ∃ c, ι c = (B : Matrix (Fin 2) (Fin 2) F) i j) :
    ∃ B' : SL2 E, Matrix.SpecialLinearGroup.map ι B' = B := by
  choose c hc using h
  have hNB : ι.mapMatrix (Matrix.of c) = (B : Matrix (Fin 2) (Fin 2) F) := by
    ext i j
    simp [hc]
  have hdet : (Matrix.of c).det = 1 := by
    apply ι.injective
    rw [RingHom.map_det, hNB, B.2, map_one]
  exact ⟨⟨Matrix.of c, hdet⟩, Subtype.ext hNB⟩

theorem triD4_three_dvd_sq_sub_one {Q : ℕ} (hQ3 : ¬ 3 ∣ Q) : 3 ∣ Q ^ 2 - 1 := by
  have hQ : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (by
    rintro rfl
    exact hQ3 (dvd_zero 3)))
  refine (Nat.modEq_iff_dvd' hQ).1 ?_
  have h : Q % 3 = 1 ∨ Q % 3 = 2 := by omega
  unfold Nat.ModEq
  rw [Nat.pow_mod]
  rcases h with h | h <;> simp [h]

theorem triD4_sigma_cube {K : Type} [Field K] [Finite K] {Q : ℕ} (hK : Nat.card K = Q ^ 3)
    {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ Q) : σ ^ 3 = 1 := by
  have : Fintype K := Fintype.ofFinite K
  refine RingEquiv.ext fun c => ?_
  change σ (σ (σ c)) = c
  have h1 : Q * (Q * Q) = Fintype.card K := by
    rw [← Nat.card_eq_fintype_card, hK]
    ring
  rw [hσ, hσ, hσ, ← pow_mul, ← pow_mul, h1, FiniteField.pow_card]

theorem triD4_card_fixField {K : Type} [Field K] [Finite K] {Q : ℕ} (hK : Nat.card K = Q ^ 3)
    {δ : K ≃+* K} (hδ3 : δ ^ 3 = 1) (hδ1 : δ ≠ 1) :
    Nat.card (RingHom.eqLocusField δ.toRingHom (RingHom.id K)) = Q := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : CharP K (ringChar K) := ringChar.charP K
  obtain ⟨n, hp, hn⟩ := FiniteField.card K (ringChar K)
  have hQ : Q ∣ ringChar K ^ (n : ℕ) := by
    rw [← hn, ← Nat.card_eq_fintype_card, hK]
    exact dvd_pow_self Q (by norm_num)
  obtain ⟨f, -, rfl⟩ := (Nat.dvd_prime_pow hp).1 hQ
  have hK' : Nat.card K = ringChar K ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have hf : 1 ≤ 3 * f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · have h1 : 1 < Nat.card K := Finite.one_lt_card
      rw [hK', h0] at h1
      simp at h1
    · omega
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf δ = 3 := orderOf_eq_prime hδ3 hδ1
  obtain ⟨-, -, -, -, -, hA⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality hp hf hK'
  obtain ⟨-, S, hS, hcard⟩ := hA (Subgroup.zpowers δ)
  rw [Nat.card_zpowers, hord, Nat.mul_div_cancel_left _ (by norm_num : 0 < 3)] at hcard
  have hSE : S = RingHom.eqLocusField δ.toRingHom (RingHom.id K) := by
    refine SetLike.ext' ?_
    rw [hS]
    ext a
    simp only [Set.mem_ofPred_eq, SetLike.mem_coe]
    change (∀ τ ∈ Subgroup.zpowers δ, τ a = a) ↔ δ a = a
    constructor
    · intro h
      exact h δ (Subgroup.mem_zpowers δ)
    · intro h τ hτ
      have hstab : Subgroup.zpowers δ ≤ MulAction.stabilizer (K ≃+* K) a :=
        Subgroup.zpowers_le.2 (by rw [MulAction.mem_stabilizer_iff, RingAut.smul_def]; exact h)
      have h' := hstab hτ
      rwa [MulAction.mem_stabilizer_iff, RingAut.smul_def] at h'
  rw [← hSE, hcard]

theorem triD4_mem_orbitField {K : Type} [Field K] {σ : K ≃+* K} (hσ : σ ^ 3 = 1) (c : K) :
    c ∈ orbitField TwistTag.D4 K σ.toRingHom d4Outer := by
  have h3 : ∀ c : K, σ (σ (σ c)) = c := fun c => by
    change (σ ^ 3) c = c
    rw [hσ]
    rfl
  rw [orbitField_D4_zero_eq_top σ h3]
  exact Subfield.mem_top c

section Entrywise


theorem triD4_mem_d4ShortSL2 {K : Type} [Field K] {σ : K →+* K}
    {x : graphFixedRootGroup TwistTag.D4 K σ} :
    x ∈ d4ShortSL2 K σ ↔ ∃ g, orbitRankOneHom TwistTag.D4 K σ d4Outer g = x :=
  Iff.rfl

theorem triD4_entrywise_orbitRankOneHom {t : TwistTag} {K : Type} [Field K] [Finite K]
    (σ δ : K ≃+* K) (a : Fin t.foldedTag.rank) (g : SL2 (orbitField t K σ.toRingHom a)) :
    Units.map (entrywiseHom δ.toRingHom) (orbitRankOneHom t K σ.toRingHom a g) =
      orbitRankOneHom t K σ.toRingHom a
        (Matrix.SpecialLinearGroup.map (orbitFieldRestrict t σ δ a).toRingHom g) := by
  have h : (Units.map (entrywiseHom δ.toRingHom)).comp (orbitRankOneHom t K σ.toRingHom a) =
      (orbitRankOneHom t K σ.toRingHom a).comp
        (Matrix.SpecialLinearGroup.map (orbitFieldRestrict t σ δ a).toRingHom) := by
    refine triD4_SL2_hom_ext (fun s => ?_) (fun s => ?_)
    · rw [MonoidHom.comp_apply, MonoidHom.comp_apply, orbitRankOneHom_uSL, map_uSL,
        orbitRankOneHom_uSL,
        units_map_entrywiseHom_orbitX (σ := σ.toRingHom) (ringEquiv_comm_of_finite σ δ)]
      rfl
    · rw [MonoidHom.comp_apply, MonoidHom.comp_apply, orbitRankOneHom_vSL, map_vSL,
        orbitRankOneHom_vSL,
        units_map_entrywiseHom_orbitY (σ := σ.toRingHom) (ringEquiv_comm_of_finite σ δ)]
      rfl
  exact DFunLike.congr_fun h g

end Entrywise

section Short


theorem triD4_fieldActor_mem_short {K : Type} [Field K] [Finite K] {σ δ : K ≃+* K}
    {x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hx : x ∈ CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.d4ShortSL2 K σ.toRingHom) :
    fieldActor σ δ x ∈ CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.d4ShortSL2 K σ.toRingHom := by
  obtain ⟨g, hg⟩ := triD4_mem_d4ShortSL2.1 hx
  refine triD4_mem_d4ShortSL2.2
    ⟨Matrix.SpecialLinearGroup.map (orbitFieldRestrict TwistTag.D4 σ δ d4Outer).toRingHom g, ?_⟩
  rw [← triD4_entrywise_orbitRankOneHom, hg, coe_fieldActor]

theorem triD4_exists_short_involution {K : Type} [Field K] [Finite K] (hK2 : ringChar K ≠ 2)
    {σ : K ≃+* K} (hσ : σ ^ 3 = 1) :
    ∃ t ∈ CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.d4ShortSL2 K σ.toRingHom, t ≠ 1 ∧ t ^ 2 = 1 ∧
      (∀ x ∈ CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.d4ShortSL2 K σ.toRingHom, x * t = t * x) ∧
      ∀ δ : K ≃+* K, fieldActor σ δ t = t := by
  have hmem : orbitRankOneHom TwistTag.D4 K σ.toRingHom d4Outer (-1) ∈
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    range_orbitRankOneHom_le d4Outer ⟨-1, rfl⟩
  refine ⟨⟨_, hmem⟩, triD4_mem_d4ShortSL2.2 ⟨-1, rfl⟩, fun h => ?_, Subtype.ext ?_,
    fun x hx => Subtype.ext ?_, fun δ => Subtype.ext ?_⟩
  ·
    have h1 : orbitRankOneHom TwistTag.D4 K σ.toRingHom d4Outer (-1) =
        orbitRankOneHom TwistTag.D4 K σ.toRingHom d4Outer 1 := by
      rw [map_one]
      exact congrArg Subtype.val h
    have h2 := orbitRankOneHom_injective_D4 hσ d4Outer h1
    have h3 : (-1 : K) = 1 := by
      have h4 := congrArg (fun A : SL2 (orbitField TwistTag.D4 K σ.toRingHom d4Outer) =>
        ((A : Matrix (Fin 2) (Fin 2) (orbitField TwistTag.D4 K σ.toRingHom d4Outer)) 0 0 : K)) h2
      simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
        Matrix.neg_apply, Matrix.one_apply_eq] at h4
      exact h4
    exact Ring.neg_one_ne_one_of_char_ne_two hK2 h3
  · change orbitRankOneHom TwistTag.D4 K σ.toRingHom d4Outer (-1) ^ 2 = 1
    rw [← map_pow, neg_one_sq, map_one]
  ·
    obtain ⟨g, hg⟩ := triD4_mem_d4ShortSL2.1 hx
    change (x : ModGL TwistTag.D4.tag K) * orbitRankOneHom TwistTag.D4 K σ.toRingHom d4Outer (-1) =
      orbitRankOneHom TwistTag.D4 K σ.toRingHom d4Outer (-1) * x
    rw [← hg, ← map_mul, ← map_mul, mul_neg_one, neg_one_mul]
  ·
    rw [coe_fieldActor]
    change Units.map (entrywiseHom δ.toRingHom)
        (orbitRankOneHom TwistTag.D4 K σ.toRingHom d4Outer (-1)) =
      orbitRankOneHom TwistTag.D4 K σ.toRingHom d4Outer (-1)
    rw [triD4_entrywise_orbitRankOneHom, triD4_map_neg_one]

theorem triD4_nonempty_mulEquiv_short_fix {K : Type} [Field K] [Finite K] {σ δ : K ≃+* K}
    (hσ : σ ^ 3 = 1) (E : Subfield K) (hE : ∀ c, c ∈ E ↔ δ c = c) :
    Nonempty (SL2 E ≃* ↥(d4ShortSL2 K σ.toRingHom ⊓
      CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (fieldActor σ δ))) := by
  obtain ⟨ι, hι⟩ : ∃ ι : E →+* orbitField TwistTag.D4 K σ.toRingHom d4Outer,
      ∀ c, (ι c : K) = c :=
    ⟨Subfield.inclusion fun c _ => triD4_mem_orbitField hσ c, fun c => rfl⟩
  obtain ⟨φ, hφ⟩ : ∃ φ : SL2 E →* graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      ∀ g, (φ g : ModGL TwistTag.D4.tag K) =
        orbitRankOneHom TwistTag.D4 K σ.toRingHom d4Outer (Matrix.SpecialLinearGroup.map ι g) :=
    ⟨((orbitRankOneHom TwistTag.D4 K σ.toRingHom d4Outer).comp
      (Matrix.SpecialLinearGroup.map ι)).codRestrict _
        fun g => range_orbitRankOneHom_le d4Outer ⟨_, rfl⟩, fun g => rfl⟩
  have hinjR := orbitRankOneHom_injective_D4 hσ d4Outer
  have hδι : ∀ g : SL2 E, Matrix.SpecialLinearGroup.map
      (orbitFieldRestrict TwistTag.D4 σ δ d4Outer).toRingHom (Matrix.SpecialLinearGroup.map ι g) =
        Matrix.SpecialLinearGroup.map ι g := by
    intro g
    refine Matrix.SpecialLinearGroup.ext _ _ fun i j => Subtype.ext ?_
    change δ (ι ((g : Matrix (Fin 2) (Fin 2) E) i j) : K) =
      (ι ((g : Matrix (Fin 2) (Fin 2) E) i j) : K)
    rw [hι]
    exact (hE _).1 (Subtype.prop _)
  have hinj : Function.Injective φ := by
    intro g g' h
    have h1 := congrArg Subtype.val h
    rw [hφ, hφ] at h1
    have h2 := hinjR h1
    refine Matrix.SpecialLinearGroup.ext _ _ fun i j => Subtype.ext ?_
    have h3 := congrArg (fun A : SL2 (orbitField TwistTag.D4 K σ.toRingHom d4Outer) =>
      ((A : Matrix (Fin 2) (Fin 2) (orbitField TwistTag.D4 K σ.toRingHom d4Outer)) i j : K)) h2
    simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
      hι] at h3
    exact h3
  have hrange : φ.range = d4ShortSL2 K σ.toRingHom ⊓
      CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (fieldActor σ δ) := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      refine Subgroup.mem_inf.2 ⟨triD4_mem_d4ShortSL2.2 ⟨_, (hφ g).symm⟩, ?_⟩
      rw [CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup]
      apply Subtype.ext
      rw [coe_fieldActor, hφ, triD4_entrywise_orbitRankOneHom, hδι]
    · intro hx
      obtain ⟨hxS, hxF⟩ := Subgroup.mem_inf.1 hx
      obtain ⟨g, hg⟩ := triD4_mem_d4ShortSL2.1 hxS
      rw [CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup] at hxF
      have hgfix : Matrix.SpecialLinearGroup.map
          (orbitFieldRestrict TwistTag.D4 σ δ d4Outer).toRingHom g = g := by
        apply hinjR
        rw [← triD4_entrywise_orbitRankOneHom, hg, ← coe_fieldActor σ δ x, hxF]
      have hent : ∀ i j, ∃ c, ι c = (g : Matrix (Fin 2) (Fin 2) _) i j := by
        intro i j
        have h1 : δ ((g : Matrix (Fin 2) (Fin 2) (orbitField TwistTag.D4 K σ.toRingHom d4Outer))
            i j : K) =
            ((g : Matrix (Fin 2) (Fin 2) (orbitField TwistTag.D4 K σ.toRingHom d4Outer)) i j : K) :=
          congrArg (fun A : SL2 (orbitField TwistTag.D4 K σ.toRingHom d4Outer) =>
            ((A : Matrix (Fin 2) (Fin 2) (orbitField TwistTag.D4 K σ.toRingHom d4Outer)) i j : K))
            hgfix
        exact ⟨⟨_, (hE _).2 h1⟩, Subtype.ext (hι _)⟩
      obtain ⟨g', hg'⟩ := triD4_exists_sl2_map_eq ι g hent
      exact MonoidHom.mem_range.2 ⟨g', Subtype.ext (by rw [hφ, hg', hg])⟩
  exact ⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)⟩

theorem triD4_glaPLayer_short_fix {K : Type} [Field K] [Finite K] {Q : ℕ} {σ δ : K ≃+* K}
    (hK : Nat.card K = Q ^ 3) (hσ : ∀ c, σ c = c ^ Q) (hQ : 4 ≤ Q) (hQ3 : ¬ 3 ∣ Q)
    (hδ3 : δ ^ 3 = 1) (hδ1 : δ ≠ 1) :
    GLAPLayer 3 (CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.d4ShortSL2 K σ.toRingHom ⊓
      CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (fieldActor σ δ)) ≠ ⊥ := by
  have hE := triD4_card_fixField hK hδ3 hδ1
  obtain ⟨e⟩ := triD4_nonempty_mulEquiv_short_fix (triD4_sigma_cube hK hσ)
    (RingHom.eqLocusField δ.toRingHom (RingHom.id K)) fun _ => Iff.rfl
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hq : CFSG.IsQuasisimple ↥(d4ShortSL2 K σ.toRingHom ⊓
      CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (fieldActor σ δ)) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e
      (CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.isQuasisimple_sl2 (by rw [hE]; exact hQ))
  have h3 : 3 ∣ Nat.card ↥(d4ShortSL2 K σ.toRingHom ⊓
      CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (fieldActor σ δ)) := by
    rw [← Nat.card_congr e.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hE]
    exact dvd_mul_of_dvd_right (triD4_three_dvd_sq_sub_one hQ3) _
  exact CFSG.LocalAnalysis.GLTheoremA.glaPLayer_ne_bot_of_block Nat.prime_three le_rfl hq
    (fun g hg f hf => mul_mem (mul_mem hg hf) (inv_mem hg)) h3

end Short

end CFSG.LocalAnalysis.GLTheoremA.S267.P3
