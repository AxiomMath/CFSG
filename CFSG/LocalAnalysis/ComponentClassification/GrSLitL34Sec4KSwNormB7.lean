module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4KSwNormB6
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4FWN1
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4FWN1Inv
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS

@[expose] def L34Lemma43TwistedNarrowStep : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (a x : G) (J S A : Subgroup G), L34Sec4Setting G a x J S →
    (∀ s ∈ S, s * a = a * s) → L34Sec4Running J A → IsThreeConnected (S ⊓ withKernel J) →
    S ⊓ zStarIn J = ⊥ →
    ∀ W : Subgroup G, W ≠ ⊥ → Odd (Nat.card W) →
      (∀ B : Subgroup G, B ≤ S ⊓ withKernel J → IsAbelianTwoOfRank 3 B → wGroup B = W) →
      normalizer (J : Set G) ≤ normalizer (W : Set G) →
      ∀ K : Subgroup G, K ≤ normalizer (W : Set G) →
        IsPComponent 2 (K.subgroupOf (normalizer (W : Set G))) →
        IsL34Type (K ⧸ Open.fusionZStar K) →
        J ⊔ oddIn (normalizer (W : Set G)) = K ⊔ oddIn (normalizer (W : Set G)) →
        ¬ oddIn K ≤ J →
        ∀ T : Subgroup G, IsSylowTwoIn T (normalizer (W : Set G)) → S ≤ T →
          (∃ P : Sylow 2 G, (P : Subgroup G) = T) →
          ∀ t ∈ T, t ∉ normalizer (K : Set G) →
          (∀ m ∈ normalizer (W : Set G), conjugate K m = K ∨ conjugate K m = conjugate K t) →
          (∀ y ∈ T, y ∈ coreActionKernel K → y ∈ coreActionKernel (conjugate K t) → y = 1) →
          (∀ y ∈ normalizer (W : Set G), orderOf y = 2 → y ∈ normalizer (K : Set G)) →
          (∃ u ∈ T, u ∉ normalizer (K : Set G) ∧ u ^ 4 = 1) →
          (∀ u ∈ T, u ∉ normalizer (K : Set G) → u ^ 4 = 1 →
            ¬ ∃ F ≤ T ⊓ centralizer ({u} : Set G), IsEightGroup F ∧
              ∃ w ∈ T ⊓ centralizer ({u} : Set G), w * w = 1 ∧ (∀ e ∈ F, w * e = e * w) ∧
                w ∉ F) →
          (a ∈ conjugate K t ∨ t * a * t⁻¹ ∉ withKernel K) →
          (a ∈ conjugate K t → ¬ oddIn J ≤ centralizer (J : Set G)) →
          (a ∈ conjugate K t → ∀ y ∈ K ⊔ conjugate K t ⊔ oddIn (normalizer (W : Set G)),
            y * y = 1 → y ≠ 1 → ∃ g ∈ normalizer (W : Set G), g⁻¹ * y * g = a ∨
              (g⁻¹ * y * g)⁻¹ * a * (t⁻¹ * a * t) ∈ oddIn (normalizer (W : Set G))) →
          (∀ w ∈ T ⊓ normalizer (K : Set G), w * w ∈ K ⊔ conjugate K t) →
          (∀ v ∈ T, v ∉ normalizer (K : Set G) → v * v ∉ withKernel K) →
          (∀ v ∈ T, v ∉ normalizer (K : Set G) →
            (∀ y ∈ T, y ∉ normalizer (K : Set G) → orderOf v ≤ orderOf y) →
            ∃ g : G, g⁻¹ * v * g ∈ T ⊓ normalizer (K : Set G)) →
          False

theorem l34Lemma43TwistedStep_of_narrow
    (hMax : MaximalTwoComponentInput) (h : L34Lemma43TwistedNarrowStep) :
    L34Lemma43TwistedStep := by
  intro G _ _ a x J S A hset hcent hrun h3 hZ1 W hW hWodd hWB hNJ K hKM hKc hKL hsup hOK T hTsyl
    hST hTG t htT htK hr2 hQ hinv hu hno
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
  have htM := hTM htT
  have hKt : conjugate K t ≠ K := fun e => htK (mem_normalizer_of_conjugate_eq e)
  have hKne : ∀ {v : G}, v ∈ M → v ∉ normalizer (K : Set G) → conjugate K v = conjugate K t :=
    fun {v} hv hvK => (hr2 v hv).resolve_left fun e => hvK (mem_normalizer_of_conjugate_eq e)
  have hsqN : ∀ v ∈ M, v * v ∈ normalizer (K : Set G) := by
    intro v hv
    by_cases hvK : v ∈ normalizer (K : Set G)
    · exact mul_mem hvK hvK
    · rcases hr2 (v * v) (mul_mem hv hv) with h1 | h1
      · exact mem_normalizer_of_conjugate_eq h1
      · exfalso
        apply hvK
        apply mem_normalizer_of_conjugate_eq
        have h3 : conjugate (conjugate K v) v = conjugate K v := by
          rw [conjugate_conjugate, h1, hKne hv hvK]
        have h4 := congrArg (fun H => conjugate H v⁻¹) h3
        simpa only [conjugate_conjugate, mul_inv_cancel_right, mul_inv_cancel, conjugate_one]
          using h4
  have hNKt : ∀ y ∈ M, y ∈ normalizer (K : Set G) →
      y ∈ normalizer (conjugate K t : Set G) := by
    intro y hy hyK
    apply mem_normalizer_of_conjugate_eq
    rw [conjugate_conjugate]
    rcases hr2 (t * y) (mul_mem htM hy) with h1 | h1
    · exfalso
      apply htK
      rw [show t = t * y * y⁻¹ by group]
      exact mul_mem (mem_normalizer_of_conjugate_eq h1) (inv_mem hyK)
    · exact h1
  have hconjN : ∀ {y : G}, y ∈ normalizer (conjugate K t : Set G) →
      t * y * t⁻¹ ∈ normalizer (K : Set G) := by
    intro y hy
    have h1 : conjugate K (t * y) = conjugate K t := by
      rw [← conjugate_conjugate]
      exact conjugate_eq_of_mem_normalizer hy
    exact mem_normalizer_of_conjugate_eq (by
      rw [← conjugate_conjugate, h1, conjugate_conjugate, mul_inv_cancel, conjugate_one])
  have htt : t * t ∈ normalizer (K : Set G) := hsqN t htM
  have hidx := HeSN.relIndex_eq_two htM htK htt hr2
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
  have hKC := KSw.odd_card_inf_coreActionKernel hs hSsyl hZ1
  have haK : a ∈ coreActionKernel K := GrS4.mem_coreActionKernel_of_singleComponentSetting hMax hs
  have hZJ := KSw.zStarIn_eq_oddIn_of_inf_eq_bot hSsyl hZ1
  have hE1 : a ∈ conjugate K t ∨ t * a * t⁻¹ ∉ withKernel K := by
    by_cases hin : t * a * t⁻¹ ∈ withKernel K
    · exact Or.inl (KSw.mem_conjugate_of_conj_mem_withKernel hKM hKc hKC hT2 hTM hTK htT htK hQ
        haT haK (hconjN (hNKt a (hTM haT) (mem_coreActionKernel.mp haK).1)) hin)
    · exact Or.inr hin
  have hE2 : a ∈ conjugate K t → ¬ oddIn J ≤ centralizer (J : Set G) := fun haKt =>
    FW.not_oddIn_le_centralizer hMax hs hL34 hZJ htM hKt haKt
  have hE3 : a ∈ conjugate K t → ∀ y ∈ K ⊔ conjugate K t ⊔ oddIn M, y * y = 1 → y ≠ 1 →
      ∃ g ∈ M, g⁻¹ * y * g = a ∨ (g⁻¹ * y * g)⁻¹ * a * (t⁻¹ * a * t) ∈ oddIn M := by
    intro haKt y hy hy2 hy1
    obtain ⟨g, hg, h1 | h1 | h1⟩ :=
      FW.exists_conj_of_involution_mem_sup hs hL34 hZJ htM hKt haKt hr2 hy hy2 hy1
    · exact ⟨g, hg, Or.inl h1⟩
    · refine ⟨g * t⁻¹, mul_mem hg (inv_mem htM), Or.inl ?_⟩
      rw [show (g * t⁻¹)⁻¹ * y * (g * t⁻¹) = t * (g⁻¹ * y * g) * t⁻¹ by group, h1]
      group
    · exact ⟨g, hg, Or.inr h1⟩
  have hE4 : ∀ w ∈ T ⊓ normalizer (K : Set G), w * w ∈ K ⊔ conjugate K t := fun w hw =>
    KSw.sq_mem_sup_conjugate hKM hKc hKL hKC hT2 hTM hTK htT htK hQ (mem_inf.mp hw).1
      (mem_inf.mp hw).2 (hNKt w (hTM (mem_inf.mp hw).1) (mem_inf.mp hw).2)
  have hE5 : ∀ v ∈ T, v ∉ normalizer (K : Set G) → v * v ∉ withKernel K := by
    intro v hvT hvK
    have hKv := hKne (hTM hvT) hvK
    exact KSw.sq_not_mem_withKernel hKM hKc hKC hT2 hTM hTK hvT hvK (hsqN v (hTM hvT))
      (fun y hyT hy1 hy2 => hQ y hyT hy1 (hKv ▸ hy2)) hinv
  have hU : (T ⊓ normalizer (K : Set G)).relIndex T = 2 := by
    rw [relIndex_eq_two_iff]
    refine ⟨t, htT, fun b hb => ?_⟩
    simp only [mem_inf, hb, mul_mem hb htT, true_and]
    by_cases hbK : b ∈ normalizer (K : Set G)
    · exact Or.inr ⟨hbK, fun h2 => htK (by
        rw [show t = b⁻¹ * (b * t) by group]
        exact mul_mem (inv_mem hbK) h2)⟩
    · refine Or.inl ⟨?_, hbK⟩
      apply mem_normalizer_of_conjugate_eq
      rw [← conjugate_conjugate, hKne (hTM hb) hbK, conjugate_conjugate]
      exact conjugate_eq_of_mem_normalizer htt
  have hTidx : ¬ 2 ∣ T.index := by
    obtain ⟨P₀, hP₀⟩ := hTG
    rw [← hP₀]
    exact P₀.not_dvd_index
  have hE6 : ∀ v ∈ T, v ∉ normalizer (K : Set G) →
      (∀ y ∈ T, y ∉ normalizer (K : Set G) → orderOf v ≤ orderOf y) →
      ∃ g : G, g⁻¹ * v * g ∈ T ⊓ normalizer (K : Set G) := fun v hvT hvK hmin =>
    FW.exists_conj_mem_of_least_order hnab hT2 hTidx inf_le_left hU hvT
      (fun h1 => hvK (mem_inf.mp h1).2)
      (fun y hyT hyU => hmin y hyT fun h1 => hyU (mem_inf.mpr ⟨hyT, h1⟩))
  exact h G a x J S A hset hcent hrun h3 hZ1 W hW hWodd hWB hNJ K hKM hKc hKL hsup hOK T hTsyl
    hST hTG t htT htK hr2 hQ hinv hu hno hE1 hE2 hE3 hE4 hE5 hE6

end CFSG.ComponentClassification.GrSLit
