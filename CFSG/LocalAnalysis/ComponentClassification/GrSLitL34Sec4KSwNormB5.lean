module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4KSwNormB4
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4KSwNormB3
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5TW

public section

namespace CFSG.ComponentClassification.GrSLit.KSw

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {G : Type} [Group G] [Finite G]

theorem false_of_caseB
    (hMax : MaximalTwoComponentInput)
    (hS : SchreierFor Blueprint.Catalog)
    (hCoset : ∀ (G : Type) [Group G] [Finite G] (J S : Subgroup G), ⁅J, J⁆ = J →
      IsL34Type (J ⧸ Open.fusionZStar J) → zStarIn J = oddIn J →
      S ≤ normalizer (J : Set G) → IsPGroup 2 S → IsSylowTwoIn (S ⊓ J) J →
      ∀ s ∈ S, ∃ y ∈ S, s⁻¹ * y ∈ withKernel J ∧ y * y ∈ coreActionKernel J)
    (hG2 : L34Lemma43TwistedStep) {a x : G} {J S A : Subgroup G}
    (hset : L34Sec4Setting G a x J S) (hcent : ∀ s ∈ S, s * a = a * s)
    (hrun : L34Sec4Running J A) (h3 : IsThreeConnected (S ⊓ withKernel J))
    (hZ1 : S ⊓ zStarIn J = ⊥) {W : Subgroup G} (hW : W ≠ ⊥) (hWodd : Odd (Nat.card W))
    (hWB : ∀ B : Subgroup G, B ≤ S ⊓ withKernel J → IsAbelianTwoOfRank 3 B → wGroup B = W)
    (hNJ : normalizer (J : Set G) ≤ normalizer (W : Set G)) {K : Subgroup G}
    (hKM : K ≤ normalizer (W : Set G))
    (hKc : IsPComponent 2 (K.subgroupOf (normalizer (W : Set G))))
    (hKL : IsL34Type (K ⧸ Open.fusionZStar K))
    (hsup : J ⊔ oddIn (normalizer (W : Set G)) = K ⊔ oddIn (normalizer (W : Set G)))
    {T : Subgroup G} (hTsyl : IsSylowTwoIn T (normalizer (W : Set G))) (hST : S ≤ T)
    (hTN : ¬ T ≤ normalizer (K : Set G)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hbase, hU3, hL34, hmax, hSsyl, haS, -⟩ := id hset
  obtain ⟨hsimple, hnab, hK, -, hUo, -, -, -⟩ := id hbase
  have : IsSimpleGroup G := hsimple
  have ha2 : orderOf a = 2 := hU3.1
  have hJa : J ≤ centralizer ({a} : Set G) := hU3.2.2.2.1
  have hJc := hU3.2.2.2.2.1
  set M : Subgroup G := normalizer (W : Set G) with hM
  have hgs : GSMaximalSetting G a J := ⟨hsimple, hnab, hK, hUo, ha2, hJa, hJc, hmax,
    GrS5.three_le_pRank_of_l34 hL34, Sol78.not_psp4_of_l34 hL34, Or.inl ⟨hL34, hset.1⟩⟩
  have hs : SingleComponentSetting G a J W K :=
    { toGSMaximalSetting := hgs, ne_bot := hW, odd_card := hWodd, normalizer_le := hNJ,
      normalizer_ne_top := GrS4.normalizer_ne_top_of_odd hW hWodd ha2, le_normalizer := hKM,
      isPComponent_K := hKc, sup_eq := hsup }
  have hT2 := GrS4.isPGroup_of_isSylowTwoIn hTsyl
  have hTM := hTsyl.1
  have haT : a ∈ T := hST haS
  have hKper : ⁅K, K⁆ = K := commutator_eq_of_isPComponent hKM hKc
  have hTQ := inf_coreKernel_eq_bot hMax hS hbase hs hL34 hT2 hTM haT hTN
  obtain ⟨t, htT, htK, httK, hr2⟩ := eq_or_eq_of_mem hMax hS hbase hs hL34 hTsyl haT hTN
  have hQ : ∀ y ∈ T, y ∈ coreActionKernel K → y ∈ coreActionKernel (conjugate K t) → y = 1 := by
    intro y hyT hyK hyKt
    have h1 : y ∈ T ⊓ HeSN.coreKernel M K :=
      mem_inf.mpr ⟨hyT, HeSN.mem_coreKernel.mpr fun m hm => by
        rcases hr2 m hm with e | e <;> rw [e] <;> assumption⟩
    rw [hTQ, mem_bot] at h1
    exact h1
  have hH1 : ∀ e ∈ T, ∀ e' ∈ T, conjugate K e = K ∨ conjugate K e' = K ∨
      conjugate K e = conjugate K e' := by
    intro e he e' he'
    rcases hr2 e (hTM he) with h1 | h1
    · exact Or.inl h1
    · rcases hr2 e' (hTM he') with h2 | h2
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr (h1.trans h2.symm))
  have hTZ : T ⊓ zStarIn K = ⊥ := inf_zStarIn_eq_bot_of_zOne hs hSsyl hZ1 hT2
  have hWT := GrS5S.l34TSylowWStep_of_certs hMax G a x J S A hset hcent
    (fun h => (h hZ1).elim) hrun h3 W hW hWodd hWB hNJ K hKM hKc hKL (Or.inl hsup) T hTsyl hST
    hH1 (Or.inl hTZ)
  obtain ⟨F, hFP, hF, s, hsS, hss, hsF, hsn⟩ := GrS5S.exists_eight_not_isolated hset h3
  have hTG := exists_sylow_of_wT hTsyl hWT (hFP.trans (inf_le_left.trans hST)) hF
    (hST (mem_inf.mp hsS).1) hss hsF hsn
  have hKC := odd_card_inf_coreActionKernel hs hSsyl hZ1
  have hKZ := zStarIn_eq_oddIn_of_zOne hs hSsyl hZ1
  have hidx := HeSN.relIndex_eq_two (hTM htT) htK httK hr2
  have hM₀n : M ≤ normalizer ((M ⊓ normalizer (K : Set G) : Subgroup G) : Set G) :=
    (normal_subgroupOf_iff_le_normalizer inf_le_left).mp (Subgroup.normal_of_index_eq_two hidx)
  obtain ⟨R₁, hR₁⟩ := RankProjectiveAction.exists_sylow_inf_of_le_normalizer hTsyl.1 hTsyl.2
    (inf_le_left : M ⊓ normalizer (K : Set G) ≤ M) hM₀n
  have hTN₀ : T ⊓ (M ⊓ normalizer (K : Set G)) = T ⊓ normalizer (K : Set G) := by
    rw [← inf_assoc, inf_of_le_left hTM]
  have hsyl₀ : IsSylowTwoIn (T ⊓ normalizer (K : Set G)) (M ⊓ normalizer (K : Set G)) :=
    ⟨le_inf (inf_le_left.trans hTM) inf_le_right, R₁, hTN₀ ▸ hR₁⟩
  obtain ⟨R₂, hR₂⟩ := RankProjectiveAction.exists_sylow_inf_of_le_normalizer hsyl₀.1 hsyl₀.2
    (le_inf hKM le_normalizer : K ≤ M ⊓ normalizer (K : Set G)) inf_le_right
  have hTK : IsSylowTwoIn (T ⊓ K) K := by
    refine ⟨inf_le_right, R₂, ?_⟩
    rw [hR₂, inf_assoc, inf_of_le_right (le_normalizer : K ≤ normalizer (K : Set G))]
  have hTKZ : T ⊓ K ⊓ zStarIn K = ⊥ := eq_bot_iff.mpr fun y hy => by
    have h1 : y ∈ T ⊓ zStarIn K :=
      mem_inf.mpr ⟨(mem_inf.mp (mem_inf.mp hy).1).1, (mem_inf.mp hy).2⟩
    rwa [hTZ] at h1
  obtain ⟨E, -, hET, hE, hEc, -⟩ := L34Facts.l34ElementaryCenterFact G K (T ⊓ K) hKper hKL hTK
    fun y hy => by
      rw [hTKZ, mem_bot] at hy
      rw [hy, one_mul]
  rw [hTKZ, card_bot, mul_one] at hEc
  have hinv : ∀ y ∈ M, orderOf y = 2 → y ∈ normalizer (K : Set G) := fun y hy hy2 =>
    mem_normalizer_of_orderOf_eq_two hnab hKM hKc hKC hTsyl hTG hWT htT htK httK hr2 hET hE hEc
      hy hy2
  obtain ⟨u, huT, huK, hu4, -, -⟩ := exists_order_four hCoset hKM hKc hKL hKZ hKC hT2 hTM hTK
    htT htK httK hQ hinv
  have hOK : ¬ oddIn K ≤ J := FW.not_oddIn_le_of_not_le hMax hs fun h => hTN (hTM.trans h)
  refine hG2 G a x J S A hset hcent hrun h3 hZ1 W hW hWodd hWB hNJ K hKM hKc hKL hsup hOK T
    hTsyl hST hTG t htT htK hr2 hQ hinv ⟨u, huT, huK, hu4⟩ ?_
  rintro u' hu'T hu'K hu'4 ⟨F', hF'T, hF', w, hwT, hww, hwF, hwn⟩
  exact false_of_witness_order_four hnab hTsyl hTG hWT htT htK httK hr2 hinv hu'T hu'K hu'4
    hF'T hF' hwT hww hwF hwn

end CFSG.ComponentClassification.GrSLit.KSw
