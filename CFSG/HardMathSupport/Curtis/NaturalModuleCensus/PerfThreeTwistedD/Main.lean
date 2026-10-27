module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.PerfThreeTwistedD.NaturalModule
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltPlusD.FlagLink
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltSplit.SpinMinus
public import CFSG.HardMathSupport.Curtis.Coordinator.PerfThreeLinear
import CFSG.LargeExtraspecial.DW2AOutOrth
import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.StatedOmegaScalars

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus

open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.AGLEmbedding
open CFSG.AGLEmbedding.LieOut CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime
  CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.Steinberg
  CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.Steinberg.CentralExt
  CFSG.LieType.BorelTits Matrix

theorem commutator_eq_self_of_top_commutator {X : Type*} [Group X] (A : Subgroup X)
    (h : ⁅(⊤ : Subgroup ↥A), (⊤ : Subgroup ↥A)⁆ = ⊤) : ⁅A, A⁆ = A := by
  have h1 := Subgroup.map_commutator (⊤ : Subgroup ↥A) ⊤ A.subtype
  rw [h, Subgroup.map_top, Subgroup.range_subtype] at h1
  exact h1.symm

section

variable {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}

theorem eq_one_of_mem_statedScalars_statedOmega_two (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (hn : 2 ≤ n) {A : StatedOmega (StatedQuadMinus n F b c)}
    (hA : (A : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) ∈
      StatedScalars (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) : A = 1 :=
  CFSG.HardMathSupport.Curtis.NaturalModuleCensus.eq_one_of_mem_statedScalars_statedQuadMinus_omega hirr hn hA

end

variable {Y : Type} [Group Y] [Finite Y] {L J : Subgroup Y}

theorem exists_perfect_three_of_sl2_hom
    (hZ : ∀ z : ↥L, z ∈ Subgroup.center ↥L → (z : Y) ∈ J)
    {K : Type} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
    {H : Fin D.rank → Subgroup K} {π : K →* ↥L ⧸ Subgroup.center ↥L} {M : ℕ}
    (h : BorelQuotient D n H π M) {π' : K →* ↥L ⧸ Subgroup.center ↥L}
    (hker : π'.ker = π.ker) {i : Fin D.rank}
    (hiJ : (rankOne D.rootGroup i).map π' ≤ quotImage L J)
    {k : Type} [Field k] [Finite k] [CharP k 2] {φ : Matrix.SpecialLinearGroup (Fin 2) k →* K}
    (hφ : Function.Injective φ) (hφR : φ.range ≤ rankOne D.rootGroup i)
    (hk : Nat.card k = 4) :
    ∃ X : Subgroup Y, X ≤ J ∧ ⁅X, X⁆ = X ∧ 3 ∣ Nat.card X := by
  have hk4 : 4 ≤ Nat.card k := hk.ge
  set G := Matrix.SpecialLinearGroup (Fin 2) k with hG
  set ρ : G →* (↥L ⧸ Subgroup.center ↥L) := π'.comp φ with hρ
  have hker_ρ : ρ.ker ≤ Subgroup.center G := by
    intro g hg
    have hg1 : π' (φ g) = 1 := hg
    have hc : φ g ∈ Subgroup.center K := h.ker_central _ (hker ▸ hg1)
    rw [Subgroup.mem_center_iff]
    intro t
    apply hφ
    rw [map_mul, map_mul]
    exact Subgroup.mem_center_iff.1 hc (φ t)
  have hρJ : ρ.range ≤ quotImage L J := by
    refine le_trans ?_ hiJ
    rw [hρ, MonoidHom.range_comp]
    exact Subgroup.map_mono hφR
  have hcenter : Subgroup.center G = ⊥ := sl2_center_eq_bot
  have hker_bot : ρ.ker = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    have := hker_ρ hg
    rw [hcenter] at this
    exact this
  have hGcard : Nat.card G = Nat.card k * (Nat.card k ^ 2 - 1) := card_sl2
  have hG60 : Nat.card G = 60 := by rw [hGcard, hk]; norm_num
  have hp3 : 3 ∣ Nat.card ρ.range := by
    have hc := Subgroup.card_ker_mul_card_range ρ
    rw [hker_bot, Subgroup.card_bot, one_mul, hG60] at hc
    rw [hc]
    norm_num
  have hcq : Nat.card (G ⧸ Subgroup.center G) = Nat.card G := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center G)
    have h1 : Nat.card (Subgroup.center G) = 1 := by rw [hcenter, Subgroup.card_bot]
    rw [h1, mul_one] at h
    exact h.symm
  have hno : NoAp 3 (G ⧸ Subgroup.center G) := by
    refine NoAp.of_card_lt ?_
    rw [hcq, hG60, Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  obtain ⟨X, hXJ, hXq, h3X, -⟩ :=
    exists_quasisimple_of_cover hZ ρ hρJ hker_ρ (isQuasisimple_sl2 hk4) hp3 hno
  exact ⟨X, hXJ, commutator_eq_self_of_top_commutator X hXq.1, h3X⟩

theorem false_of_threePerf_shortNode
    (hperf : ∀ U : Subgroup Y, U ≤ J → ⁅U, U⁆ = U → Nat.Coprime 3 (Nat.card U))
    (h : CompParabE L J) {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (hn4 : 4 ≤ n)
    (hcard : Nat.card F = 2)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* StatedProj (StatedOmega (StatedQuadMinus n F b c)))
    (π' : spinGroup (quadMinus n F b c) →* ↥L ⧸ Subgroup.center ↥L)
    (hker : π'.ker = (e.symm.toMonoidHom.comp (spinToStatedProj (quadMinus n F b c)
        (range_spinMatrix_quadMinus hn4 hirr))).ker)
    (k : Fin (n - 1)) (hk : ¬ k.val + 1 < n - 1)
    (hle : (rankOne (minusDatum n hirr).rootGroup k).map π' ≤ quotImage L J) : False := by
  have : Finite (spinGroup (quadMinus n F b c)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadMinus hirr)
  have hB := borelQuotient_spinMinus hirr hn4 e
  obtain ⟨hJL, T, hT, hNT⟩ := h.parab
  have hZ : ∀ z : ↥L, z ∈ Subgroup.center ↥L → (z : Y) ∈ J :=
    fun z hz => center_le_of_normalizer_le hT hNT hz
  have := fact_shortField hirr
  have := finite_shortField (b := b) (c := c)
  have : CharP (ShortField b c) 2 :=
    charP_of_injective_algebraMap (algebraMap F (ShortField b c)).injective 2
  have hkcard : Nat.card (ShortField b c) = 4 := by
    rw [SpinMinusClosed.card_shortField, hcard]; norm_num
  obtain ⟨Θ, hU, hL⟩ := CFSG.Timmesfeld.RankTwo.exists_hom_of_rankOneRels (shortRels n hirr k)
  have hinj : Function.Injective Θ := by
    refine sl2_injective_of_upper_ne_one hkcard.ge Θ ?_
    rw [hU, ← (shortRels n hirr k).x_zero]
    intro h1
    exact one_ne_zero (shortRels_x_injective hirr k h1)
  obtain ⟨X, hXJ, hXp, hX3⟩ := exists_perfect_three_of_sl2_hom hZ hB hker hle hinj
    (range_le_rankOne_of_hasSL2Node (fun t => by
      rw [hU]; exact (mem_minusRootGroup_single_iff hirr hk _).2 ⟨t, rfl⟩)
      (fun t => by
      rw [hL]; exact (mem_minusRootGroup_neg_single_iff hirr hk _).2 ⟨t, rfl⟩)) hkcard
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 (hperf X hXJ hXp) hX3

theorem false_of_fixPerfThree_pomegaMinus_two
    (hperf : ∀ U : Subgroup Y, U ≤ J → ⁅U, U⁆ = U → Nat.Coprime 3 (Nat.card U))
    (hC : CompParabE L J) (hZ : Subgroup.center ↥L = ⊥)
    {x : Y} (hxL : x ∈ L) (hxp : x ^ 3 = 1) (hfix : ∀ l ∈ L, x * l * x⁻¹ = l → l ∈ J)
    {n : ℕ} (hmodel : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .POmegaMinus n 2 1) :
    False := by
  obtain ⟨⟨-, hf, hn⟩, F, hF, hFfin, hcard, b, c, hirr, ⟨e⟩⟩ := hmodel
  have hcard2 : Nat.card F = 2 := by simpa using hcard
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card]; simpa using hcard)
  have hn4 : 4 ≤ n := by omega
  obtain ⟨hJL, T, hT, hNT⟩ := hC.parab
  have hNJ := normalizer_barSylow_le_quotImage hT hNT
  have hshort : ∀ π' : spinGroup (quadMinus n F b c) →* ↥L ⧸ Subgroup.center ↥L,
      π'.ker = (e.symm.toMonoidHom.comp (spinToStatedProj (quadMinus n F b c)
        (range_spinMatrix_quadMinus hn4 hirr))).ker →
      ∀ k : Fin (n - 1), ¬ k.val + 1 < n - 1 →
        ¬ (CFSG.LieType.CurtisTits.rankOne (minusDatum n hirr).rootGroup k).map π' ≤
          quotImage L J :=
    fun π' hker k hk hle => false_of_threePerf_shortNode hperf hC hirr hn4 hcard2 e π' hker k hk hle
  obtain ⟨W, hWQ, hWdim, hWstab⟩ :=
    exists_stab_of_overgroup hirr hn4 e (barSylow hT) (quotImage L J) hNJ hshort
  have hxJ : x ∈ J := hfix x hxL (by simp)
  have hxbJ : (QuotientGroup.mk (⟨x, hxL⟩ : ↥L) : ↥L ⧸ Subgroup.center ↥L) ∈ quotImage L J :=
    mem_quotImage.2 ⟨⟨x, hxL⟩, hxJ, rfl⟩
  obtain ⟨M0, hM0⟩ := QuotientGroup.mk_surjective
    (e (QuotientGroup.mk (⟨x, hxL⟩ : ↥L) : ↥L ⧸ Subgroup.center ↥L))
  have hMW := fun w hw => hWstab _ hxbJ M0 hM0 w hw
  have hMQ := preserves_of_mem_statedOmega (Q₀ := StatedQuadMinus n F b c) M0.2
  have hM3 : (M0 : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) ^ 3 = 1 := by
    have h1 : (QuotientGroup.mk (M0 ^ 3) :
        StatedProj (StatedOmega (StatedQuadMinus n F b c))) = 1 := by
      rw [QuotientGroup.mk_pow, hM0, ← map_pow, ← QuotientGroup.mk_pow]
      have : (⟨x, hxL⟩ : ↥L) ^ 3 = 1 := Subtype.ext hxp
      rw [this]
      simp
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
    have := eq_one_of_mem_statedScalars_statedOmega_two hirr (by omega) h1
    simpa using congrArg Subtype.val this
  have hC' : ∀ g ∈ StatedOmega (StatedQuadMinus n F b c),
      g * (M0 : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) =
        (M0 : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) * g →
      ∀ w ∈ W, (g : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
        (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) *ᵥ w ∈ W := by
    intro g hg hcomm w hw
    set gΩ : ↥(StatedOmega (StatedQuadMinus n F b c)) := ⟨g, hg⟩ with hgΩ
    set y : ↥L ⧸ Subgroup.center ↥L := e.symm (QuotientGroup.mk gΩ) with hydef
    have hy : y ∈ quotImage L J := by
      obtain ⟨l, hl⟩ := QuotientGroup.mk_surjective y
      have hcomm' : (QuotientGroup.mk gΩ : StatedProj (StatedOmega (StatedQuadMinus n F b c))) *
          e (QuotientGroup.mk (⟨x, hxL⟩ : ↥L)) = e (QuotientGroup.mk (⟨x, hxL⟩ : ↥L)) *
          QuotientGroup.mk gΩ := by
        rw [← hM0, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
        congr 1
        exact Subtype.ext hcomm
      have hy' : y * QuotientGroup.mk (⟨x, hxL⟩ : ↥L) = QuotientGroup.mk (⟨x, hxL⟩ : ↥L) * y := by
        apply e.injective
        rw [map_mul, map_mul, hydef, MulEquiv.apply_symm_apply]
        exact hcomm'
      rw [← hl, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul] at hy'
      have hmem := QuotientGroup.eq.1 hy'
      rw [hZ, Subgroup.mem_bot] at hmem
      have hlx : l * ⟨x, hxL⟩ = ⟨x, hxL⟩ * l := by
        exact inv_mul_eq_one.1 hmem
      have hfl : x * (l : Y) * x⁻¹ = l := by
        have := congrArg Subtype.val hlx
        simp only [Subgroup.coe_mul] at this
        rw [← this, mul_assoc, mul_inv_cancel, mul_one]
      exact mem_quotImage.2 ⟨l, hfix l l.2 hfl, hl⟩
    exact hWstab y hy gΩ (by simp [hydef]) w hw
  refine false_of_invariant_totSingular_two (K := F) (ι := Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
    hcard2 (quadMinusForm n F b c hirr) ?_ W hWQ ?_
    (M0 : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) hMQ hM3 hMW hC'
  · simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  · rw [hWdim]
    omega

theorem isClassicalOrG2Index_of_idxTwistedD {i : TauCeti.LieTypeIndex} (h : IdxTwistedD i) :
    IsClassicalOrG2Index i := by
  cases i <;> first | exact h | exact h.elim

section Void

open CFSG.HardMathSupport.Curtis.Coordinator
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)


theorem fixPerfThreeVoid_twistedD (hGA : CFSG.Open.GriessAllModelsStatement) :
    FixPerfThreeVoid (IsLieOf IdxTwistedD) := by
  intro Y _ _ L J u hyp hX
  obtain ⟨⟨d, hv⟩, hd, ⟨e⟩⟩ := hX
  have hidx2 := isClassicalOrG2IndexTwo_of_fixPerfThreeHyp hyp ⟨d, hv⟩
    (isClassicalOrG2Index_of_idxTwistedD hd) e
  cases d
  case twistedD r q =>
    have hp2 : q.p = 2 := hd
    have hcard : q.card = 2 := hidx2
    have hexp : q.exponent = 1 := by
      have hpos := q.exponent_pos
      by_contra hne
      have h2 : 2 ≤ q.exponent := by omega
      have : 2 ^ 2 ≤ 2 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) h2
      rw [TauCeti.PrimePower.card_def, hp2] at hcard
      omega
    have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even r q hv hp2 e
    rw [hp2, hexp] at hm
    have hq : CFSG.Open.IsQuasisimple ↥L := hyp.parab.comp.2.2
    have : Group.IsPerfect ↥L := Group.isPerfect_def.mpr hq.1
    have hZ1 : Nat.card (Subgroup.center ↥L) = 1 := by
      obtain ⟨hd', hA, h2A⟩ := ToralCensus.rest_index (P := IdxTwistedD)
        (Or.inr (Or.inr (Or.inl rfl))) hd
      exact ToralCensus.card_center_eq_one_of_index hGA ⟨.twistedD r q, hv⟩ hd' hA h2A e
        hyp.parab.odd
    have hZ : Subgroup.center ↥L = ⊥ := Subgroup.eq_bot_of_card_eq _ hZ1
    have hout : ¬ 3 ∣ Nat.card (Outer ↥L) := by
      intro h3
      have hP := CFSG.LargeExtraspecial.DW.isPGroup_outer_POmegaMinus
        (X := ↥L ⧸ Subgroup.center ↥L) (n := r) (Or.inl ⟨by decide, hm⟩)
      obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hP
      have h3' := h3.trans (card_outer_dvd_card_outer_centerQuotient ↥L)
      rw [hk] at h3'
      have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3')
      omega
    have hu := mem_sup_centralizer_of_not_dvd_card_outer (p := 3) (k := 1) Nat.prime_three hout
      hyp.norm (by simpa using hyp.pow)
    obtain ⟨l, hl3, hlfix⟩ := exists_decomp_of_mem_sup_centralizer hu hyp.pow hyp.fix
    have hl3' : l ^ 3 = 1 := by rwa [hZ, Subgroup.mem_bot] at hl3
    refine false_of_fixPerfThree_pomegaMinus_two hyp.perf (CompParab.toE hyp.parab) hZ (x := (l : Y)) l.2
      (by exact congrArg Subtype.val hl3') (fun l' hl' hcomm => ?_) hm
    have h1 : (⟨l', hl'⟩ : ↥L) * l = l * ⟨l', hl'⟩ := by
      apply Subtype.ext
      have : (l : Y) * l' * (l : Y)⁻¹ = l' := hcomm
      simp only [Subgroup.coe_mul]
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this.symm
    exact Subgroup.mem_subgroupOf.1 (hlfix ⟨l', hl'⟩ h1)
  all_goals exact hd.elim

end Void

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus
