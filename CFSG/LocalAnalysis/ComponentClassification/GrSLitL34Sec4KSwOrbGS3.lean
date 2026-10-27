module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4KSwOrb
import CFSG.LocalAnalysis.ComponentClassification.FooteLitThm32Tools
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Fixed
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrTwoLocalTools
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.ComponentClassification.GrSLit.KSwOrb

open CFSG Subgroup CFSG.ComponentClassification CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def movedConjugates (M K : Subgroup G) (w : G) : Set (Subgroup G) :=
  {L | (∃ m ∈ M, L = conjugate K m) ∧ w ∈ normalizer (L : Set G) ∧ w ∉ coreActionKernel L}

theorem conjugate_conjugate_mul (K : Subgroup G) (m m' : G) :
    conjugate (conjugate K m') m = conjugate K (m' * m) := by
  ext y
  rw [mem_conjugate_iff, mem_conjugate_iff, mem_conjugate_iff,
    show m' * m * y * (m' * m)⁻¹ = m' * (m * y * m⁻¹) * m'⁻¹ by group]

theorem conjugate_one (K : Subgroup G) : conjugate K 1 = K := by
  ext y
  rw [mem_conjugate_iff, one_mul, inv_one, mul_one]

theorem mem_normalizer_conjugate_iff {L : Subgroup G} {m x : G} :
    x ∈ normalizer (conjugate L m : Set G) ↔ m * x * m⁻¹ ∈ normalizer (L : Set G) := by
  rw [mem_normalizer_iff, mem_normalizer_iff]
  constructor
  · intro h y
    have h1 := h (m⁻¹ * y * m)
    rw [mem_conjugate_iff, mem_conjugate_iff,
      show m * (m⁻¹ * y * m) * m⁻¹ = y by group,
      show m * (x * (m⁻¹ * y * m) * x⁻¹) * m⁻¹ = m * x * m⁻¹ * y * (m * x * m⁻¹)⁻¹ by group]
      at h1
    exact h1
  · intro h y
    rw [mem_conjugate_iff, mem_conjugate_iff]
    have h1 := h (m * y * m⁻¹)
    rw [show m * x * m⁻¹ * (m * y * m⁻¹) * (m * x * m⁻¹)⁻¹ = m * (x * y * x⁻¹) * m⁻¹ by group]
      at h1
    exact h1

theorem mem_coreActionKernel_conjugate_iff {L : Subgroup G} {m x : G} :
    x ∈ coreActionKernel (conjugate L m) ↔ m * x * m⁻¹ ∈ coreActionKernel L := by
  constructor
  · intro h
    have h1 : m⁻¹ * (m * x * m⁻¹) * m⁻¹⁻¹ ∈ coreActionKernel (conjugate L m) := by
      rwa [show m⁻¹ * (m * x * m⁻¹) * m⁻¹⁻¹ = x by group]
    have h2 := FooteLit.mem_coreActionKernel_conjugate h1
    rwa [conjugate_conjugate_mul, mul_inv_cancel, conjugate_one] at h2
  · exact FooteLit.mem_coreActionKernel_conjugate

theorem movedConjugates_conj {M K : Subgroup G} {m : G} (hm : m ∈ M) (w : G) :
    movedConjugates M K (m⁻¹ * w * m) = (fun L => conjugate L m) '' movedConjugates M K w := by
  ext L
  constructor
  · rintro ⟨⟨m', hm', rfl⟩, hN, hC⟩
    refine ⟨conjugate K (m' * m⁻¹), ⟨⟨m' * m⁻¹, mul_mem hm' (inv_mem hm), rfl⟩, ?_, ?_⟩, ?_⟩
    · have h1 := mem_normalizer_conjugate_iff.mp hN
      rw [show m' * (m⁻¹ * w * m) * m'⁻¹ = (m' * m⁻¹) * w * (m' * m⁻¹)⁻¹ by group] at h1
      exact mem_normalizer_conjugate_iff.mpr h1
    · intro h1
      apply hC
      have h2 := mem_coreActionKernel_conjugate_iff.mp h1
      rw [show (m' * m⁻¹) * w * (m' * m⁻¹)⁻¹ = m' * (m⁻¹ * w * m) * m'⁻¹ by group] at h2
      exact mem_coreActionKernel_conjugate_iff.mpr h2
    · show conjugate (conjugate K (m' * m⁻¹)) m = conjugate K m'
      rw [conjugate_conjugate_mul, inv_mul_cancel_right]
  · rintro ⟨L', ⟨⟨m', hm', rfl⟩, hN, hC⟩, rfl⟩
    refine ⟨⟨m' * m, mul_mem hm' hm, conjugate_conjugate_mul K m m'⟩, ?_, ?_⟩
    · apply mem_normalizer_conjugate_iff.mpr
      rwa [show m * (m⁻¹ * w * m) * m⁻¹ = w by group]
    · intro h1
      apply hC
      have h2 := mem_coreActionKernel_conjugate_iff.mp h1
      rwa [show m * (m⁻¹ * w * m) * m⁻¹ = w by group] at h2

theorem ncard_movedConjugates_conj {M K : Subgroup G} {m : G} (hm : m ∈ M) (w : G) :
    (movedConjugates M K (m⁻¹ * w * m)).ncard = (movedConjugates M K w).ncard := by
  rw [movedConjugates_conj hm w]
  refine Set.ncard_image_of_injective _ fun L L' h => ?_
  have h1 := congrArg (fun H => conjugate H m⁻¹) h
  simp only [conjugate_conjugate_mul, mul_inv_cancel, conjugate_one] at h1
  exact h1

variable [Finite G]

theorem movedConjugates_mul {M K : Subgroup G} (hKM : K ≤ M)
    (hKc : IsPComponent 2 (K.subgroupOf M)) {k w : G} (hk : k ∈ K) (hkC : k ∉ coreActionKernel K)
    (hw : w ∈ coreActionKernel K) :
    movedConjugates M K (k * w) = insert K (movedConjugates M K w) ∧
      K ∉ movedConjugates M K w := by
  have hwN : w ∈ normalizer (K : Set G) := (mem_coreActionKernel.mp hw).1
  have hkN : k ∈ normalizer (K : Set G) := le_normalizer hk
  refine ⟨?_, fun h => h.2.2 hw⟩
  ext L
  rw [Set.mem_insert_iff]
  by_cases hLK : L = K
  · subst hLK
    refine ⟨fun _ => Or.inl rfl, fun _ => ⟨⟨1, one_mem _, (conjugate_one L).symm⟩,
      mul_mem hkN hwN, fun h => hkC ?_⟩⟩
    have := mul_mem h (inv_mem hw)
    rwa [mul_inv_cancel_right] at this
  ·
    have hL : ∀ m ∈ M, L = conjugate K m → k ∈ coreActionKernel L := by
      rintro m hm rfl
      have hLM : conjugate K m ≤ M := UnbalancedCorr.conjugate_le_of_mem hKM hm
      have hLc : IsPComponent 2 ((conjugate K m).subgroupOf M) :=
        UnbalancedCorr.isPComponent_conjugate_subgroupOf hm hKc
      obtain ⟨-, hKN⟩ := GrS5.commutator_le_of_ne hLM hKM hLc hKc hLK
      have hcomm := GrS5.commutator_le_inf_oddIn hLM hKM hLc hKc hLK
      refine mem_coreActionKernel.mpr ⟨hKN hk, fun j hj => ?_⟩
      have h1 : j⁻¹ * k⁻¹ * j * k ∈ ⁅conjugate K m, K⁆ := by
        rw [show j⁻¹ * k⁻¹ * j * k = ⁅j⁻¹, k⁻¹⁆ by rw [commutatorElement_def, inv_inv, inv_inv]]
        exact commutator_mem_commutator (inv_mem hj) (inv_mem hk)
      exact (hcomm h1 |> mem_inf.mp).1
    constructor
    · rintro ⟨⟨m, hm, hLeq⟩, hN, hC⟩
      have hkL := hL m hm hLeq
      refine Or.inr ⟨⟨m, hm, hLeq⟩, ?_, fun h => hC (mul_mem hkL h)⟩
      have := mul_mem (inv_mem (mem_coreActionKernel.mp hkL).1) hN
      rwa [inv_mul_cancel_left] at this
    · rintro (h | ⟨⟨m, hm, hLeq⟩, hN, hC⟩)
      · exact absurd h hLK
      have hkL := hL m hm hLeq
      refine ⟨⟨m, hm, hLeq⟩, mul_mem (mem_coreActionKernel.mp hkL).1 hN, fun h => hC ?_⟩
      have := mul_mem (inv_mem hkL) h
      rwa [inv_mul_cancel_left] at this

theorem ne_conj_of_mul {M K : Subgroup G} (hKM : K ≤ M) (hKc : IsPComponent 2 (K.subgroupOf M))
    {k w : G} (hk : k ∈ K) (hkC : k ∉ coreActionKernel K) (hw : w ∈ coreActionKernel K)
    {m : G} (hm : m ∈ M) : k * w ≠ m⁻¹ * w * m := by
  intro h
  obtain ⟨h1, h2⟩ := movedConjugates_mul hKM hKc hk hkC hw
  have h3 := ncard_movedConjugates_conj (K := K) hm w
  rw [← h, h1, Set.ncard_insert_of_notMem h2 (Set.toFinite _)] at h3
  omega

end CFSG.ComponentClassification.GrSLit.KSwOrb

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification CFSG.ComponentClassification.UnbalancedLayer

@[expose] def L34Lemma43UnitaryCentreStep : Prop :=
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
        IsSylowTwoIn S (normalizer (W : Set G)) → (∃ P : Sylow 2 G, (P : Subgroup G) = S) →
        S ≤ normalizer (K : Set G) → ¬ normalizer (W : Set G) ≤ normalizer (K : Set G) →
        ¬ oddIn K ≤ J →
        ∀ g : G, g⁻¹ * a * g ∈ S → IsL34Unitary J (g⁻¹ * a * g) →
          (¬ ∃ m ∈ normalizer (W : Set G), g⁻¹ * a * g = m⁻¹ * a * m) →
          ∀ y ∈ S ⊓ J, y * (g⁻¹ * a * g) = g⁻¹ * a * g * y → y * y ≠ 1 →
            y * y ∈ conjugate J g

theorem l34Lemma43UnitaryStep_of_centre
    (hMax : MaximalTwoComponentInput) (hGS3 : L34Lemma43UnitaryCentreStep) :
    L34Lemma43UnitaryStep := by
  intro G _ _ a x J S A hset hcent hrun h3 hZ1 W hW hWodd hWB hNJ K hKM hKc hKL hsup hSM hSyl
    hSK hKn hOK g hgS hU
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hno
  obtain ⟨hbase, hU3, hL34, hmax, hS, haS, -⟩ := id hset
  obtain ⟨hsimple, hnab, hK, -, hUo, -, -, -⟩ := id hbase
  have ha2 : orderOf a = 2 := hU3.1
  have hJa : J ≤ centralizer ({a} : Set G) := hU3.2.2.2.1
  have hJc := hU3.2.2.2.2.1
  have hJper : ⁅J, J⁆ = J := UnbalancedCorr.commutator_eq_of_isPComponent hJa hJc
  have hS2 : IsPGroup 2 S := GrS4.isPGroup_of_isSylowTwoIn hS
  have hP : IsSylowTwoIn (S ⊓ J) J := GrS4.isSylowTwoIn_inf hS
  have hZc : IsCyclic ↥(S ⊓ zStarIn J) := by
    rw [hZ1]
    exact isCyclic_of_subsingleton
  have hgs : GSMaximalSetting G a J := ⟨hsimple, hnab, hK, hUo, ha2, hJa, hJc, hmax,
    GrS5.three_le_pRank_of_l34 hL34, Sol78.not_psp4_of_l34 hL34, Or.inl ⟨hL34, hset.1⟩⟩
  have hs : SingleComponentSetting G a J W K :=
    { toGSMaximalSetting := hgs, ne_bot := hW, odd_card := hWodd, normalizer_le := hNJ,
      normalizer_ne_top := GrS4.normalizer_ne_top_of_odd hW hWodd ha2, le_normalizer := hKM,
      isPComponent_K := hKc, sup_eq := hsup }
  have hCaN : centralizer ({a} : Set G) ≤ normalizer (J : Set G) :=
    GrS5S.centralizer_le_normalizer_of_sec4 hMax hset
  set b : G := g⁻¹ * a * g with hbdef
  obtain ⟨y, hyP, hyb, hy2, hy4⟩ := GrS5S.exists_sq_ne_one_of_unitary hJper hL34 hP hgS hU hZc
  have hzJg : y * y ∈ conjugate J g := hGS3 G a x J S A hset hcent hrun h3 hZ1 W hW hWodd hWB hNJ
    K hKM hKc hKL hsup hSM hSyl hSK hKn hOK g hgS hU hno y hyP hyb hy2
  have hbN : b ∈ normalizer ((S ⊓ J : Subgroup G) : Set G) :=
    UnbalancedLayer.normalizer_inf_mem (le_normalizer hgS) hU.1
  obtain ⟨-, -, -, -, -, -, -, hconjinv⟩ :=
    L34Facts.l34UnitaryCentralizerFact G J (S ⊓ J) b hJper hL34 hU hP hbN
  have hzb : y * y * b = b * (y * y) := by
    rw [mul_assoc, hyb, ← mul_assoc, hyb, mul_assoc]
  obtain ⟨q, -, hzq⟩ := hconjinv (y * y) (mul_mem hyP hyP) (by
    rw [show y * y * b * (y * y * b) = y * y * (b * (y * y)) * b by group, ← hzb,
      show y * y * (y * y * b) * b = y * y * (y * y) * (b * b) by group, hy4, hU.2.1, one_mul])
  obtain ⟨h, hbh, hSh⟩ := GrS5S.exists_conj_of_le_centralizer hS2 hcent hSyl
    (P := S ⊓ centralizer ({b} : Set G)) (hS2.to_le inf_le_left) inf_le_right
  have hyS' : h⁻¹ * y * h ∈ S :=
    hSh y (mem_inf.mpr ⟨(mem_inf.mp hyP).1, mem_centralizer_singleton_iff.mpr hyb⟩)
  have hz' : h⁻¹ * (y * y) * h = h⁻¹ * y * h * (h⁻¹ * y * h) := by group
  have hz'S : h⁻¹ * (y * y) * h ∈ S := by rw [hz']; exact mul_mem hyS' hyS'
  have hz'K : h⁻¹ * (y * y) * h ∈ withKernel J := by
    rw [hz']
    exact L34Facts.outSquare G J hJper hL34 _ (hS.1 hyS') (hS2.to_le (zpowers_le.mpr hyS'))
  set z' : G := h⁻¹ * (y * y) * h with hz'def
  have haK : a ∈ coreActionKernel J := GrS4.mem_coreActionKernel_of_le_centralizer hJa
  have hz'a : (g * q * h)⁻¹ * a * (g * q * h) = z' * a := by
    calc (g * q * h)⁻¹ * a * (g * q * h) = h⁻¹ * (q⁻¹ * b * q) * h := by rw [hbdef]; group
      _ = h⁻¹ * (y * y * b) * h := by rw [← hzq]
      _ = z' * (h⁻¹ * b * h) := by rw [hz'def]; group
      _ = z' * a := by rw [hbh]
  have hz'aS : z' * a ∈ S := mul_mem hz'S haS
  have hz'aK : z' * a ∈ withKernel J := mul_mem hz'K (mem_sup_right haK)
  obtain ⟨m, hm, hmz⟩ := GrS5S.exists_conj_of_mem_withKernel hset hcent h3 hWB hNJ hSyl
    (g := g * q * h) (hz'a ▸ hz'aS) (hz'a ▸ hz'aK)
  have hgh : g * h ∈ normalizer (J : Set G) := by
    refine hCaN (mem_centralizer_singleton_iff.mpr ?_)
    calc g * h * a = g * (h * (h⁻¹ * b * h)) := by rw [hbh]; group
      _ = a * (g * h) := by rw [hbdef]; group
  have hz'J : z' ∈ J := by
    have h1 := (mem_normalizer_iff.mp (inv_mem hgh) (g * (y * y) * g⁻¹)).mp
      (mem_conjugate_iff.mp hzJg)
    rwa [show (g * h)⁻¹ * (g * (y * y) * g⁻¹) * (g * h)⁻¹⁻¹ = z' by rw [hz'def]; group] at h1
  have hz'1 : z' ≠ 1 := fun h1 => hy2 (by
    calc y * y = h * z' * h⁻¹ := by rw [hz'def]; group
      _ = 1 := by rw [h1]; group)
  have hz'C : z' ∉ coreActionKernel K := by
    intro h1
    have h2 : z' ∈ coreActionKernel J := KSw.mem_coreActionKernel_of_mem_kernel hs h1
      (le_normalizer hz'J)
    have hZJ : zStarIn J = J ⊓ coreActionKernel J := GSThmB.map_fusionZStar_eq J
    have h3 : z' ∈ S ⊓ zStarIn J := by
      rw [hZJ]
      exact mem_inf.mpr ⟨hz'S, mem_inf.mpr ⟨hz'J, h2⟩⟩
    rw [hZ1, mem_bot] at h3
    exact hz'1 h3
  have haKK : a ∈ coreActionKernel K := GrS4.mem_coreActionKernel_of_singleComponentSetting hMax hs
  exact KSwOrb.ne_conj_of_mul hKM hKc (GrS4.le_of_singleComponentSetting hs hz'J) hz'C haKK hm
    (hz'a ▸ hmz)

end CFSG.ComponentClassification.GrSLit
