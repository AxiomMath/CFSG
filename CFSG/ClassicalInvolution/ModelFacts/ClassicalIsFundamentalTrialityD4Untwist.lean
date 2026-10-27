module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Reduce
public import CFSG.LieType.AlgebraicGroups.RationalInnerInvolutionReduction
public import CFSG.LieType.AlgebraicGroups.ToralCentralizerIdentity
public import CFSG.LieType.Chevalley.RationalToralSignDiagramD4
public import CFSG.LieType.Chevalley.E6ToralGraphInvolution
public import CFSG.LieType.Chevalley.ToralCentralizerQuotient
public import CFSG.LieType.Steinberg.BruhatTwist
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate3952
public import CFSG.LieType.AlgebraicGroups.RationalInnerInvolutionFixedComponents
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGeneralLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinInteraction

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.ToralSign
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Words

variable {τ : Tag} {k : Type} [Field k]

theorem wordWeylMatrix_mul_inv_canonicalRep_mem_torusGroup (l : List (Fin τ.rank)) :
    wordWeylMatrix τ k l * (canonicalRep (coxeterSystem τ) k (wordElt τ l))⁻¹ ∈
      torusGroup τ k := by
  refine mem_torusGroup_of_mapsRootLines_one (mul_mem (wordWeylMatrix_mem_monomialSubgroup l)
    (inv_mem (canonicalRep_mem_monomialSubgroup k _))) ?_
  have h := (mapsRootLines_wordWeylMatrix (k := k) l).mul
    (mapsRootLines_canonicalRep (R := k) (wordElt τ l)).inv
  rwa [mul_inv_cancel] at h

theorem wordWeylMatrix_mem_toralCentralizer (hk : ringChar k ≠ 2)
    (χ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ) {l : List (Fin τ.rank)}
    (hl : wordElt τ l ∈ kernelPosStabilizer χ) :
    wordWeylMatrix τ k l ∈ toralCentralizer τ k (signCharTuple χ) := by
  have hωa : wordElt τ l ∈ rootCharStabilizer (signCharTuple (k := k) χ) :=
    (mem_rootCharStabilizer_signCharTuple hk χ).2 (kernelPosStabilizer_le hl)
  have hnZ : canonicalRep (coxeterSystem τ) k (wordElt τ l) ∈
      toralCentralizer τ k (signCharTuple χ) := canonicalRep_mem_toralCentralizer hωa
  have h := mul_mem (torusGroup_le_toralCentralizer (signCharTuple (k := k) χ)
    (wordWeylMatrix_mul_inv_canonicalRep_mem_torusGroup (k := k) l)) hnZ
  rwa [inv_mul_cancel_right] at h

variable [IsAlgClosed k]

theorem exists_mul_wordWeylMatrix (hk : ringChar k ≠ 2)
    (χ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ) (ls : List (List (Fin τ.rank)))
    (hΩ : ∀ w ∈ kernelPosStabilizer χ, ∃ l ∈ ls, wordElt τ l = w) {c : ModGL τ k}
    (hc : c ∈ toralCentralizer τ k (signCharTuple χ)) :
    ∃ l ∈ ls, ∃ m ∈ toralRootGroup τ k (signCharTuple χ), c = m * wordWeylMatrix τ k l := by
  have ha : ∀ i, signCharTuple (k := k) χ i = 1 ∨ signCharTuple (k := k) χ i = -1 :=
    signCharTuple_sign χ
  obtain ⟨-, -, ⟨hMZ, hMn, -, -, eW, heW⟩, -⟩ :=
    exceptional_toral_centralizer_identity_component τ k hk (signCharTuple χ) ha
  obtain ⟨q, hq⟩ := eW.surjective (QuotientGroup.mk ⟨c, hc⟩)
  obtain ⟨⟨w, hw⟩, rfl⟩ := QuotientGroup.mk_surjective q
  have hwχ : w ∈ charStabilizer χ := (mem_rootCharStabilizer_signCharTuple hk χ).1 hw
  obtain ⟨u, hu, hωΩ⟩ := exists_mul_mem_kernelPosStabilizer hwχ
  set ω := w * u with hω_def
  have huW : u ∈ kernelReflectionGroup (signCharTuple (k := k) χ) := by
    rw [kernelReflectionGroup_signCharTuple hk]
    exact hu
  have hωa : ω ∈ rootCharStabilizer (signCharTuple (k := k) χ) :=
    (mem_rootCharStabilizer_signCharTuple hk χ).2 (kernelPosStabilizer_le hωΩ)
  have hmk : (QuotientGroup.mk ⟨w, hw⟩ : rootCharStabilizerSubgroup (signCharTuple (k := k) χ) ⧸
      (kernelReflectionGroup (signCharTuple (k := k) χ)).subgroupOf
        (rootCharStabilizerSubgroup (signCharTuple (k := k) χ))) =
        QuotientGroup.mk ⟨ω, hωa⟩ := by
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    change w⁻¹ * (w * u) ∈ kernelReflectionGroup (signCharTuple (k := k) χ)
    rw [inv_mul_cancel_left]
    exact huW
  rw [hmk, heW, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hq
  change (canonicalRep (coxeterSystem τ) k ω)⁻¹ * c ∈ toralRootGroup τ k (signCharTuple χ) at hq
  obtain ⟨l, hl, hlω⟩ := hΩ ω hωΩ
  have hNZ : wordWeylMatrix τ k l ∈ toralCentralizer τ k (signCharTuple χ) :=
    wordWeylMatrix_mem_toralCentralizer hk χ (by rw [hlω]; exact hωΩ)
  have hh₀ : wordWeylMatrix τ k l * (canonicalRep (coxeterSystem τ) k ω)⁻¹ ∈ torusGroup τ k := by
    rw [← hlω]
    exact wordWeylMatrix_mul_inv_canonicalRep_mem_torusGroup l
  refine ⟨l, hl, (wordWeylMatrix τ k l * (canonicalRep (coxeterSystem τ) k ω)⁻¹)⁻¹ *
    (wordWeylMatrix τ k l * ((canonicalRep (coxeterSystem τ) k ω)⁻¹ * c) *
      (wordWeylMatrix τ k l)⁻¹), mul_mem
    (inv_mem (le_sup_left (a := torusGroup τ k) hh₀))
    ((Subgroup.mem_normalizer_iff.1 (toralCentralizer_le_normalizer _ hNZ) _).1 hq), ?_⟩
  group

theorem untwistAt_of_forall_words (hk : ringChar k ≠ 2) (F : ModGL τ k →* ModGL τ k)
    (χ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ) (ls : List (List (Fin τ.rank)))
    (hΩ : ∀ w ∈ kernelPosStabilizer χ, ∃ l ∈ ls, wordElt τ l = w)
    (hu : ∀ l ∈ ls, ∃ u ∈ toralCentralizer τ k (signCharTuple χ),
      u * wordWeylMatrix τ k l * (F u)⁻¹ ∈ toralRootGroup τ k (signCharTuple χ)) :
    UntwistAt F (signCharTuple χ) := by
  intro c hc
  obtain ⟨l, hl, m, hm, rfl⟩ := exists_mul_wordWeylMatrix hk χ ls hΩ hc
  obtain ⟨u, huZ, hum⟩ := hu l hl
  refine ⟨u, huZ, ?_⟩
  have hmem : u * m * u⁻¹ ∈ toralRootGroup τ k (signCharTuple χ) :=
    (Subgroup.mem_normalizer_iff.1 (toralCentralizer_le_normalizer _ huZ) m).1 hm
  have : u * (m * wordWeylMatrix τ k l) * (F u)⁻¹ =
      (u * m * u⁻¹) * (u * wordWeylMatrix τ k l * (F u)⁻¹) := by group
  rw [this]
  exact mul_mem hmem hum

end Words

section Frobenius

variable (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [CharP k p]

theorem entrywiseFrobGL_weylElt_one {τ : Tag} (e : ℕ) (i : Fin τ.rank) :
    entrywiseFrobGL τ k p e (weylElt τ k i 1) = weylElt τ k i 1 := by
  rw [entrywiseFrobGL, weylElt_eq_xUnit_mul, map_mul, map_mul, units_map_entrywiseHom_xUnit,
    units_map_entrywiseHom_yUnit]
  simp

theorem frobTwistGL_diagramMap_weylElt_one (t : TwistTag) (e : ℕ) (i : Fin t.tag.rank) :
    frobTwistGL t.tag k p e (diagramMap t k) (weylElt t.tag k i 1) =
      weylElt t.tag k (t.perm i) 1 := by
  rw [frobTwistGL_apply, entrywiseFrobGL_weylElt_one, diagramMap_mul_weylElt_one,
    mul_inv_cancel_right]

theorem frobTwistGL_diagramMap_wordWeylMatrix (t : TwistTag) (e : ℕ) (l : List (Fin t.tag.rank)) :
    frobTwistGL t.tag k p e (diagramMap t k) (wordWeylMatrix t.tag k l) =
      wordWeylMatrix t.tag k (l.map t.perm) := by
  rw [wordWeylMatrix, wordWeylMatrix, map_list_prod, List.map_map, ← List.map_reverse,
    List.map_map]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  exact frobTwistGL_diagramMap_weylElt_one p t e i

end Frobenius

section D4

theorem klein_relations {W : Type*} [Group W] {s0 s1 s2 s3 : W}
    (h1 : s1 * s1 = 1) (h0 : s0 * s0 = 1) (h2 : s2 * s2 = 1) (h3 : s3 * s3 = 1)
    (c03 : s0 * s3 = s3 * s0) (c13 : s1 * s3 = s3 * s1) :
    (s2 * s3 * s1 * s2) * (s2 * s1 * s0 * s2) = s2 * s0 * s3 * s2 ∧
    (s2 * s1 * s0 * s2) * (s2 * s3 * s0 * s2) = s2 * s3 * s1 * s2 ∧
    (s2 * s3 * s0 * s2) * (s2 * s3 * s1 * s2) = s2 * s0 * s1 * s2 := by
  refine ⟨?_, ?_, ?_⟩
  · calc (s2 * s3 * s1 * s2) * (s2 * s1 * s0 * s2)
        = s2 * s3 * (s1 * (s2 * s2) * s1) * s0 * s2 := by group
      _ = s2 * s3 * s0 * s2 := by rw [h2, mul_one, h1, mul_one]
      _ = s2 * (s3 * s0) * s2 := by group
      _ = s2 * s0 * s3 * s2 := by rw [← c03]; group
  · calc (s2 * s1 * s0 * s2) * (s2 * s3 * s0 * s2)
        = s2 * s1 * (s0 * (s2 * s2) * s3 * s0) * s2 := by group
      _ = s2 * s1 * (s0 * s3 * s0) * s2 := by rw [h2, mul_one]
      _ = s2 * s1 * (s3 * s0 * s0) * s2 := by rw [c03]
      _ = s2 * s1 * s3 * s2 := by rw [mul_assoc s3, h0, mul_one]
      _ = s2 * s3 * s1 * s2 := by rw [mul_assoc s2 s1, c13, ← mul_assoc]
  · calc (s2 * s3 * s0 * s2) * (s2 * s3 * s1 * s2)
        = s2 * s3 * s0 * (s2 * s2) * s3 * s1 * s2 := by group
      _ = s2 * (s3 * (s0 * s3)) * s1 * s2 := by rw [h2, mul_one]; group
      _ = s2 * (s3 * (s3 * s0)) * s1 * s2 := by rw [c03]
      _ = s2 * s0 * s1 * s2 := by rw [← mul_assoc s3, h3, one_mul]

abbrev d4Node (a : ℕ) (h : a < 4 := by decide) : Fin Tag.D4.rank := ⟨a, h⟩

theorem d4_word_relations :
    ToralSign.wordElt .D4 [d4Node 2, d4Node 1, d4Node 3, d4Node 2] *
        ToralSign.wordElt .D4 [d4Node 2, d4Node 0, d4Node 1, d4Node 2] =
        ToralSign.wordElt .D4 [d4Node 2, d4Node 3, d4Node 0, d4Node 2] ∧
      ToralSign.wordElt .D4 [d4Node 2, d4Node 0, d4Node 1, d4Node 2] *
        ToralSign.wordElt .D4 [d4Node 2, d4Node 0, d4Node 3, d4Node 2] =
        ToralSign.wordElt .D4 [d4Node 2, d4Node 1, d4Node 3, d4Node 2] ∧
      ToralSign.wordElt .D4 [d4Node 2, d4Node 0, d4Node 3, d4Node 2] *
        ToralSign.wordElt .D4 [d4Node 2, d4Node 1, d4Node 3, d4Node 2] =
        ToralSign.wordElt .D4 [d4Node 2, d4Node 1, d4Node 0, d4Node 2] := by
  have hs : ∀ i : Fin Tag.D4.rank, (coxeterSystem .D4).simple i * (coxeterSystem .D4).simple i =
      1 := fun i => CoxeterSystem.simple_mul_simple_self _ i
  have c03 : (coxeterSystem .D4).simple (d4Node 0) * (coxeterSystem .D4).simple (d4Node 3) =
      (coxeterSystem .D4).simple (d4Node 3) * (coxeterSystem .D4).simple (d4Node 0) :=
    CFSG.LieType.Steinberg.simple_mul_simple_comm (isFiniteType_cartan .D4) (by decide)
  have c13 : (coxeterSystem .D4).simple (d4Node 1) * (coxeterSystem .D4).simple (d4Node 3) =
      (coxeterSystem .D4).simple (d4Node 3) * (coxeterSystem .D4).simple (d4Node 1) :=
    CFSG.LieType.Steinberg.simple_mul_simple_comm (isFiniteType_cartan .D4) (by decide)
  have c01 : (coxeterSystem .D4).simple (d4Node 0) * (coxeterSystem .D4).simple (d4Node 1) =
      (coxeterSystem .D4).simple (d4Node 1) * (coxeterSystem .D4).simple (d4Node 0) :=
    CFSG.LieType.Steinberg.simple_mul_simple_comm (isFiniteType_cartan .D4) (by decide)
  obtain ⟨r1, r2, r3⟩ := klein_relations (hs (d4Node 1)) (hs (d4Node 0)) (hs (d4Node 2))
    (hs (d4Node 3)) c03 c13
  refine ⟨?_, ?_, ?_⟩
  · simpa [ToralSign.wordElt, CoxeterSystem.wordProd, mul_assoc] using r1
  · simpa [ToralSign.wordElt, CoxeterSystem.wordProd, mul_assoc] using r2
  · simpa [ToralSign.wordElt, CoxeterSystem.wordProd, mul_assoc, c01] using r3

end D4

section Untwist

variable (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [CharP k p]

theorem exists_untwist_word (hk : ringChar k ≠ 2) (e : ℕ)
    (χ : Multiplicative (Fin TwistTag.D4.tag.rank → ℤ) →* ℤˣ)
    {a l : List (Fin TwistTag.D4.tag.rank)} (ha : wordElt TwistTag.D4.tag a ∈ kernelPosStabilizer χ)
    (hrel : wordElt TwistTag.D4.tag a * wordElt TwistTag.D4.tag l =
      wordElt TwistTag.D4.tag (a.map TwistTag.D4.perm)) :
    ∃ u ∈ toralCentralizer TwistTag.D4.tag k (signCharTuple χ),
      u * wordWeylMatrix TwistTag.D4.tag k l *
        (frobTwistGL TwistTag.D4.tag k p e (diagramMap TwistTag.D4 k) u)⁻¹ ∈
          toralRootGroup TwistTag.D4.tag k (signCharTuple χ) := by
  refine ⟨wordWeylMatrix TwistTag.D4.tag k a, wordWeylMatrix_mem_toralCentralizer hk χ ha, ?_⟩
  rw [frobTwistGL_diagramMap_wordWeylMatrix p TwistTag.D4 e a]
  refine Subgroup.mem_sup_left (mem_torusGroup_of_mapsRootLines_one
    (mul_mem (mul_mem (wordWeylMatrix_mem_monomialSubgroup a)
      (wordWeylMatrix_mem_monomialSubgroup l))
      (inv_mem (wordWeylMatrix_mem_monomialSubgroup _))) ?_)
  have h := ((mapsRootLines_wordWeylMatrix (k := k) a).mul
    (mapsRootLines_wordWeylMatrix (k := k) l)).mul
    (mapsRootLines_wordWeylMatrix (k := k) (a.map TwistTag.D4.perm)).inv
  rwa [hrel, mul_inv_cancel] at h

theorem untwistAt_d4 [IsAlgClosed k] (hp : p ≠ 2) (e : ℕ) :
    ∀ r ∈ d4SignDiagramReps,
      UntwistAt (frobTwistGL TwistTag.D4.tag k p e (diagramMap TwistTag.D4 k))
        (signCharTuple (signMaskChar TwistTag.D4.tag r.mask)) := by
  have hk : ringChar k ≠ 2 := by
    rw [ringChar.eq k p]
    exact hp
  obtain ⟨-, -, h4⟩ := rational_toral_sign_diagram_arithmetic
  intro r hr
  have hset := h4.coe_kernelPosStabilizer r hr
  have hΩ : ∀ w ∈ kernelPosStabilizer (signMaskChar TwistTag.D4.tag r.mask),
      ∃ l ∈ r.omegaWords, wordElt TwistTag.D4.tag l = w := fun w hw =>
    (Set.ext_iff.1 hset w).1 hw
  have hmem : ∀ l ∈ r.omegaWords,
      wordElt TwistTag.D4.tag l ∈ kernelPosStabilizer (signMaskChar TwistTag.D4.tag r.mask) :=
    fun l hl => (Set.ext_iff.1 hset (wordElt TwistTag.D4.tag l)).2 ⟨l, hl, rfl⟩
  refine untwistAt_of_forall_words hk _ _ r.omegaWords hΩ fun l hl => ?_
  have hnil : l = [] → ∃ u ∈ toralCentralizer TwistTag.D4.tag k
      (signCharTuple (signMaskChar TwistTag.D4.tag r.mask)),
      u * wordWeylMatrix TwistTag.D4.tag k l *
        (frobTwistGL TwistTag.D4.tag k p e (diagramMap TwistTag.D4 k) u)⁻¹ ∈
          toralRootGroup TwistTag.D4.tag k (signCharTuple (signMaskChar TwistTag.D4.tag r.mask)) :=
    fun hl0 => ⟨1, one_mem _, by
      subst hl0
      simp [wordWeylMatrix]⟩
  obtain ⟨R1, R2, R3⟩ := d4_word_relations
  rcases List.mem_cons.1 (hr : r ∈ ⟨0, 1, 1, d4OmegaWords0⟩ :: [⟨4, 3, 4, d4OmegaWords4⟩]) with
    rfl | hr
  ·
    exact hnil (List.mem_singleton.1 hl)
  ·
    obtain rfl : r = ⟨4, 3, 4, d4OmegaWords4⟩ := List.mem_singleton.1 hr
    have hl' : l = [] ∨ l = d4Word4_1 ∨ l = d4Word4_2 ∨ l = d4Word4_3 := by
      rcases List.mem_cons.1 hl with h | h
      · exact Or.inl h
      rcases List.mem_cons.1 h with h | h
      · exact Or.inr (Or.inl h)
      rcases List.mem_cons.1 h with h | h
      · exact Or.inr (Or.inr (Or.inl h))
      rcases List.mem_cons.1 h with h | h
      · exact Or.inr (Or.inr (Or.inr h))
      exact absurd h List.not_mem_nil
    have hmem1 := hmem d4Word4_1 (by simp [d4OmegaWords4])
    have hmem2 := hmem d4Word4_2 (by simp [d4OmegaWords4])
    have hmem3 := hmem d4Word4_3 (by simp [d4OmegaWords4])
    rcases hl' with rfl | rfl | rfl | rfl
    · exact hnil rfl
    · exact exists_untwist_word p hk e _ hmem3 R1
    · exact exists_untwist_word p hk e _ hmem1 R2
    · exact exists_untwist_word p hk e _ hmem2 R3

end Untwist

end CFSG.ClassicalInvolution.ModelFacts
