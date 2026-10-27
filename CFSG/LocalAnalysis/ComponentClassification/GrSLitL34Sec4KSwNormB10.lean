module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4KSwNormB9
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS

@[expose] def L34Lemma43TwistedUnitaryStep : Prop :=
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
          (a ∈ conjugate K t → ∀ v ∈ T, v ∉ normalizer (K : Set G) →
            (∀ y ∈ T, y ∉ normalizer (K : Set G) → orderOf v ≤ orderOf y) →
            ¬ ∃ F ≤ T ⊓ centralizer ({v * v} : Set G), IsEightGroup F ∧
              ∃ w ∈ T ⊓ centralizer ({v * v} : Set G), w * w = 1 ∧
                (∀ e ∈ F, w * e = e * w) ∧ w ∉ F) →
          False

theorem l34Lemma43TwistedNarrowStep_of_unitary
    (hMax : MaximalTwoComponentInput) (h : L34Lemma43TwistedUnitaryStep) :
    L34Lemma43TwistedNarrowStep := by
  intro G _ _ a x J S A hset hcent hrun h3 hZ1 W hW hWodd hWB hNJ K hKM hKc hKL hsup hOK T hTsyl
    hST hTG t htT htK hr2 hQ hinv hu hno hE1 hE2 hE3 hE4 hE5 hE6
  refine h G a x J S A hset hcent hrun h3 hZ1 W hW hWodd hWB hNJ K hKM hKc hKL hsup hOK T hTsyl
    hST hTG t htT htK hr2 hQ hinv hu hno hE1 hE2 hE3 hE4 hE5 hE6 ?_
  intro haKt v hvT hvK hmin hwit
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
  have hKne : ∀ {y : G}, y ∈ M → y ∉ normalizer (K : Set G) → conjugate K y = conjugate K t :=
    fun {y} hy hyK => (hr2 y hy).resolve_left fun e => hyK (mem_normalizer_of_conjugate_eq e)
  have hsqN : ∀ y ∈ M, y * y ∈ normalizer (K : Set G) := by
    intro y hy
    by_cases hyK : y ∈ normalizer (K : Set G)
    · exact mul_mem hyK hyK
    · rcases hr2 (y * y) (mul_mem hy hy) with h1 | h1
      · exact mem_normalizer_of_conjugate_eq h1
      · exfalso
        apply hyK
        apply mem_normalizer_of_conjugate_eq
        have h3 : conjugate (conjugate K y) y = conjugate K y := by
          rw [conjugate_conjugate, h1, hKne hy hyK]
        have h4 := congrArg (fun H => conjugate H y⁻¹) h3
        simpa only [conjugate_conjugate, mul_inv_cancel_right, mul_inv_cancel, conjugate_one]
          using h4
  have hidx := HeSN.relIndex_eq_two htM htK (hsqN t htM) hr2
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
  have hTZ : T ⊓ zStarIn K = ⊥ := KSw.inf_zStarIn_eq_bot_of_zOne hs hSsyl hZ1 hT2
  have hH1 : ∀ e ∈ T, ∀ e' ∈ T, conjugate K e = K ∨ conjugate K e' = K ∨
      conjugate K e = conjugate K e' := by
    intro e he e' he'
    rcases hr2 e (hTM he) with h1 | h1
    · exact Or.inl h1
    · rcases hr2 e' (hTM he') with h2 | h2
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr (h1.trans h2.symm))
  have hWT := GrS5S.l34TSylowWStep_of_certs hMax G a x J S A hset hcent
    (fun h => (h hZ1).elim) hrun h3 W hW hWodd hWB hNJ K hKM hKc hKL (Or.inl hsup) T hTsyl hST
    hH1 (Or.inl hTZ)
  have hTidx : ¬ 2 ∣ T.index := by
    obtain ⟨P₀, hP₀⟩ := hTG
    rw [← hP₀]
    exact P₀.not_dvd_index
  have hnorm : ∀ y ∈ T, y ∉ normalizer (K : Set G) → t * y * t⁻¹ ∉ normalizer (K : Set G) := by
    intro y hyT hyK hN
    have h1 : conjugate K (t * y) = conjugate K t := by
      rw [show t * y = t * y * t⁻¹ * t by group, ← conjugate_conjugate,
        conjugate_eq_of_mem_normalizer hN]
    have h3 : conjugate K (y * y) = conjugate K t := by
      rw [← conjugate_conjugate, hKne (hTM hyT) hyK, conjugate_conjugate, h1]
    exact hKt (by rw [← h3]; exact conjugate_eq_of_mem_normalizer (hsqN y (hTM hyT)))
  have haext : IsExtremalIn T a := KSw.isExtremalIn_of_isSylowTwoIn
    (GrS4.isSylowTwoIn_of_le hSsyl (fun s hs => mem_centralizer_singleton_iff.mpr (hcent s hs))
      (GrS4.centralizer_le_normalizer_of_gsMaximalSetting hMax hgs)) hST hT2 haT
  have hv4 : v ^ 4 = 1 := by
    obtain ⟨u, huT, huK, hu4⟩ := hu
    have hle : orderOf v ≤ 4 := (hmin u huT huK).trans
      (Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hu4))
    obtain ⟨n, hn⟩ := hT2 ⟨v, hvT⟩
    have hdvd : orderOf v ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one (by
      have := congrArg Subtype.val hn
      simpa using this)
    obtain ⟨k, -, hkv⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    have hk2 : k ≤ 2 := by
      by_contra hk2
      push Not at hk2
      have h8 : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
      rw [hkv] at hle
      omega
    rw [← orderOf_dvd_iff_pow_eq_one, hkv]
    exact Nat.pow_dvd_pow 2 hk2
  have hvvvv : v * v * (v * v) = 1 := by
    rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two] at hv4
    exact hv4
  have hvv : v * v ≠ 1 := fun h1 => hvK (hinv v (hTM hvT)
    (orderOf_eq_prime (by rw [pow_two]; exact h1) fun h2 => hvK (h2 ▸ one_mem _)))
  obtain ⟨g, hg⟩ := hE6 v hvT hvK hmin
  exact KSw.false_of_sq_witness hKM hKc hKL hKC hTsyl hTidx hTK hTZ hWT htT htK hr2 hnorm haK
    haext (hE3 haKt) hE4 hE5 hvT hvK hvv hvvvv hg hwit

end CFSG.ComponentClassification.GrSLit
