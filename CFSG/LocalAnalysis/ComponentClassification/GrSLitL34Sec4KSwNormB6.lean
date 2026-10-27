module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4KSwNormB4
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsOutSquare
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4KSwNormB3
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5TW

public section

namespace CFSG.ComponentClassification.GrSLit.KSw

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS

variable {G : Type} [Group G] [Finite G]

theorem zStarIn_eq_oddIn_of_inf_eq_bot {J S : Subgroup G}
    (hSsyl : IsSylowTwoIn S (normalizer (J : Set G))) (hZ1 : S ⊓ zStarIn J = ⊥) :
    zStarIn J = oddIn J := by
  refine le_antisymm ?_ (GrS4.oddIn_le_zStarIn J)
  refine GrSLit.le_map_pPrimeCore (map_subtype_le _) (fun k hk z hz => ?_)
    (odd_card_zStarIn_of_inf_eq_bot hSsyl hZ1)
  have : (Open.fusionZStar ↥J).Characteristic := inferInstance
  exact (mem_normalizer_iff.mp
    (normalizer_le_normalizer_map_of_characteristic J (Open.fusionZStar ↥J) (le_normalizer hk))
    z).mp hz

theorem sq_not_mem_withKernel {W K T : Subgroup G} (hKM : K ≤ normalizer (W : Set G))
    (hKc : IsPComponent 2 (K.subgroupOf (normalizer (W : Set G))))
    (hKC : Odd (Nat.card ↥(K ⊓ coreActionKernel K))) (hT2 : IsPGroup 2 T)
    (hTM : T ≤ normalizer (W : Set G)) (hTK : IsSylowTwoIn (T ⊓ K) K) {v : G} (hvT : v ∈ T)
    (hvK : v ∉ normalizer (K : Set G)) (hvvK : v * v ∈ normalizer (K : Set G))
    (hQ : ∀ y ∈ T, y ∈ coreActionKernel K → y ∈ coreActionKernel (conjugate K v) → y = 1)
    (hinv : ∀ y ∈ normalizer (W : Set G), orderOf y = 2 → y ∈ normalizer (K : Set G)) :
    v * v ∉ withKernel K := by
  intro hin
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hvM := hTM hvT
  have hKv : conjugate K v ≠ K := fun e => hvK (mem_normalizer_of_conjugate_eq e)
  have hKvK : K ≤ normalizer (conjugate K v : Set G) :=
    (GrS5.commutator_le_of_ne (conjugate_le_of_mem hKM hvM)
      hKM (isPComponent_conjugate_subgroupOf hvM hKc) hKc hKv).2
  have hck : ∀ k ∈ K, v⁻¹ * k * v ∈ coreActionKernel K := fun k hk =>
    conj_mem_coreActionKernel_of_ne hKM hKc hk hvM hKv
  have hKk : ∀ k ∈ K, conjugate K (v * k) = conjugate K v := fun k hk => by
    rw [← conjugate_conjugate, conjugate_eq_of_mem_normalizer (hKvK hk)]
  obtain ⟨k, hk, p, hp, hkp⟩ :=
    exists_mul_of_mem_sup_kernel' hT2 hTK hKC (mul_mem hvT hvT) hvvK hin
  have hkT := (mem_inf.mp hk).1
  have hkK := (mem_inf.mp hk).2
  have hyT : v * k⁻¹ ∈ T := mul_mem hvT (inv_mem hkT)
  have hyK : v * k⁻¹ ∉ normalizer (K : Set G) := fun hy => hvK (by
    rw [show v = v * k⁻¹ * k by group]
    exact mul_mem hy (le_normalizer hkK))
  have hyy : v * k⁻¹ * (v * k⁻¹) = k * (p * (v⁻¹ * k⁻¹ * v)) * k⁻¹ := by
    calc v * k⁻¹ * (v * k⁻¹) = v * v * (v⁻¹ * k⁻¹ * v) * k⁻¹ := by group
      _ = k * p * (v⁻¹ * k⁻¹ * v) * k⁻¹ := by rw [hkp]
      _ = k * (p * (v⁻¹ * k⁻¹ * v)) * k⁻¹ := by group
  have hyyK : v * k⁻¹ * (v * k⁻¹) ∈ coreActionKernel K := by
    rw [hyy]
    exact UnbalancedLayer.conj_mem_coreActionKernel (le_normalizer hkK)
      (mul_mem (mem_inf.mp hp).2 (hck _ (inv_mem hkK)))
  have hyyKv := HeSN.mem_kernel_conjugate (hKk _ (inv_mem hkK)) hyyK (by group)
  have hy1 := hQ _ (mul_mem hyT hyT) hyyK hyyKv
  have hy2 : orderOf (v * k⁻¹) = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hy1) fun h1 => hyK (h1 ▸ one_mem _)
  exact hyK (hinv _ (hTM hyT) hy2)

theorem mem_conjugate_of_conj_mem_withKernel {W K T : Subgroup G}
    (hKM : K ≤ normalizer (W : Set G))
    (hKc : IsPComponent 2 (K.subgroupOf (normalizer (W : Set G))))
    (hKC : Odd (Nat.card ↥(K ⊓ coreActionKernel K))) (hT2 : IsPGroup 2 T)
    (hTM : T ≤ normalizer (W : Set G)) (hTK : IsSylowTwoIn (T ⊓ K) K) {t : G} (htT : t ∈ T)
    (htK : t ∉ normalizer (K : Set G))
    (hQ : ∀ y ∈ T, y ∈ coreActionKernel K → y ∈ coreActionKernel (conjugate K t) → y = 1)
    {y : G} (hyT : y ∈ T) (hyK : y ∈ coreActionKernel K)
    (hyN : t * y * t⁻¹ ∈ normalizer (K : Set G)) (hy : t * y * t⁻¹ ∈ withKernel K) :
    y ∈ conjugate K t := by
  have htM := hTM htT
  have hKt : conjugate K t ≠ K := fun e => htK (mem_normalizer_of_conjugate_eq e)
  obtain ⟨k, hk, p, hp, hkp⟩ := exists_mul_of_mem_sup_kernel' hT2 hTK hKC
    (mul_mem (mul_mem htT hyT) (inv_mem htT)) hyN hy
  have hk'K : t⁻¹ * k * t ∈ conjugate K t := by
    rw [mem_conjugate_iff, show t * (t⁻¹ * k * t) * t⁻¹ = k by group]
    exact (mem_inf.mp hk).2
  have hy' : y = t⁻¹ * k * t * (t⁻¹ * p * t) := by
    calc y = t⁻¹ * (t * y * t⁻¹) * t := by group
      _ = t⁻¹ * (k * p) * t := by rw [hkp]
      _ = t⁻¹ * k * t * (t⁻¹ * p * t) := by group
  have hp'Kt : t⁻¹ * p * t ∈ coreActionKernel (conjugate K t) := by
    rw [FooteLit.mem_coreActionKernel_conjugate_iff, show t * (t⁻¹ * p * t) * t⁻¹ = p by group]
    exact (mem_inf.mp hp).2
  have hk'cK : t⁻¹ * k * t ∈ coreActionKernel K :=
    HeSN.le_coreActionKernel_of_ne hKM (conjugate_le_of_mem hKM htM) hKc
      (isPComponent_conjugate_subgroupOf htM hKc) (Ne.symm hKt) hk'K
  have hp'K : t⁻¹ * p * t ∈ coreActionKernel K := by
    have e : t⁻¹ * p * t = (t⁻¹ * k * t)⁻¹ * y := by
      rw [hy']
      group
    rw [e]
    exact mul_mem (inv_mem hk'cK) hyK
  have hp'T : t⁻¹ * p * t ∈ T := mul_mem (mul_mem (inv_mem htT) (mem_inf.mp hp).1) htT
  have h1 := hQ _ hp'T hp'K hp'Kt
  rw [hy', h1, mul_one]
  exact hk'K

theorem sq_mem_sup_conjugate
    {W K T : Subgroup G} (hKM : K ≤ normalizer (W : Set G))
    (hKc : IsPComponent 2 (K.subgroupOf (normalizer (W : Set G))))
    (hKL : IsL34Type (K ⧸ Open.fusionZStar K)) (hKC : Odd (Nat.card ↥(K ⊓ coreActionKernel K)))
    (hT2 : IsPGroup 2 T) (hTM : T ≤ normalizer (W : Set G)) (hTK : IsSylowTwoIn (T ⊓ K) K)
    {t : G} (htT : t ∈ T) (htK : t ∉ normalizer (K : Set G))
    (hQ : ∀ y ∈ T, y ∈ coreActionKernel K → y ∈ coreActionKernel (conjugate K t) → y = 1)
    {w : G} (hwT : w ∈ T) (hwK : w ∈ normalizer (K : Set G))
    (hwKt : w ∈ normalizer (conjugate K t : Set G)) : w * w ∈ K ⊔ conjugate K t := by
  have htM := hTM htT
  have hKt : conjugate K t ≠ K := fun e => htK (mem_normalizer_of_conjugate_eq e)
  have hKper : ⁅K, K⁆ = K := commutator_eq_of_isPComponent hKM hKc
  have hKtNK : conjugate K t ≤ normalizer (K : Set G) :=
    (GrS5.commutator_le_of_ne hKM (conjugate_le_of_mem hKM htM) hKc
      (isPComponent_conjugate_subgroupOf htM hKc) (Ne.symm hKt)).2
  have hKKt : K ≤ coreActionKernel (conjugate K t) :=
    HeSN.le_coreActionKernel_of_ne (conjugate_le_of_mem hKM htM) hKM
      (isPComponent_conjugate_subgroupOf htM hKc) hKc hKt
  have hKtK : conjugate K t ≤ coreActionKernel K :=
    HeSN.le_coreActionKernel_of_ne hKM (conjugate_le_of_mem hKM htM) hKc
      (isPComponent_conjugate_subgroupOf htM hKc) (Ne.symm hKt)
  have hw2 : IsPGroup 2 ↥(zpowers w) := hT2.to_le (zpowers_le.mpr hwT)
  obtain ⟨k, hk, p, hp, hkp⟩ := exists_mul_of_mem_sup_kernel' hT2 hTK hKC (mul_mem hwT hwT)
    (mul_mem hwK hwK) (L34Facts.outSquare G K hKper hKL w hwK hw2)
  have h1 : conjugate K (t * w) = conjugate K t := by
    rw [← conjugate_conjugate]
    exact conjugate_eq_of_mem_normalizer hwKt
  have htwK : t * w * t⁻¹ ∈ normalizer (K : Set G) := mem_normalizer_of_conjugate_eq (by
    rw [← conjugate_conjugate, h1, conjugate_conjugate, mul_inv_cancel, conjugate_one])
  have htwT : t * w * t⁻¹ ∈ T := mul_mem (mul_mem htT hwT) (inv_mem htT)
  have htw2 : IsPGroup 2 ↥(zpowers (t * w * t⁻¹)) := hT2.to_le (zpowers_le.mpr htwT)
  have hsq := L34Facts.outSquare G K hKper hKL (t * w * t⁻¹) htwK htw2
  rw [show t * w * t⁻¹ * (t * w * t⁻¹) = t * (w * w) * t⁻¹ by group] at hsq
  have htw2T : t * (w * w) * t⁻¹ ∈ T := mul_mem (mul_mem htT (mul_mem hwT hwT)) (inv_mem htT)
  have htw2K : t * (w * w) * t⁻¹ ∈ normalizer (K : Set G) := by
    rw [show t * (w * w) * t⁻¹ = t * w * t⁻¹ * (t * w * t⁻¹) by group]
    exact mul_mem htwK htwK
  obtain ⟨k₁, hk₁, p₁, hp₁, hkp₁⟩ := exists_mul_of_mem_sup_kernel' hT2 hTK hKC htw2T htw2K hsq
  have hk'Kt : t⁻¹ * k₁ * t ∈ conjugate K t := by
    rw [mem_conjugate_iff, show t * (t⁻¹ * k₁ * t) * t⁻¹ = k₁ by group]
    exact (mem_inf.mp hk₁).2
  have hp₁' : t⁻¹ * p₁ * t ∈ coreActionKernel (conjugate K t) := by
    rw [FooteLit.mem_coreActionKernel_conjugate_iff, show t * (t⁻¹ * p₁ * t) * t⁻¹ = p₁ by group]
    exact (mem_inf.mp hp₁).2
  have hww : w * w = t⁻¹ * k₁ * t * (t⁻¹ * p₁ * t) := by
    calc w * w = t⁻¹ * (t * (w * w) * t⁻¹) * t := by group
      _ = t⁻¹ * (k₁ * p₁) * t := by rw [hkp₁]
      _ = t⁻¹ * k₁ * t * (t⁻¹ * p₁ * t) := by group
  set k' : G := t⁻¹ * k₁ * t with hk'
  set d : G := (k * k')⁻¹ * (w * w) with hd
  have hdK : d ∈ coreActionKernel K := by
    have e : d = k'⁻¹ * p := by
      rw [hd, hkp]
      group
    rw [e]
    exact mul_mem (inv_mem (hKtK hk'Kt)) (mem_inf.mp hp).2
  have hdKt : d ∈ coreActionKernel (conjugate K t) := by
    have e : d = k'⁻¹ * k⁻¹ * k' * (t⁻¹ * p₁ * t) := by
      rw [hd, hww]
      group
    rw [e]
    have hc : k'⁻¹ * k⁻¹ * k' ∈ K := by
      have := (mem_normalizer_iff.mp (hKtNK (inv_mem hk'Kt)) k⁻¹).mp (inv_mem (mem_inf.mp hk).2)
      rwa [inv_inv] at this
    exact mul_mem (hKKt hc) hp₁'
  have hdT : d ∈ T := by
    have hk'T : k' ∈ T := mul_mem (mul_mem (inv_mem htT) (mem_inf.mp hk₁).1) htT
    exact mul_mem (inv_mem (mul_mem (mem_inf.mp hk).1 hk'T)) (mul_mem hwT hwT)
  have hd1 := hQ d hdT hdK hdKt
  have e : w * w = k * k' := by
    have := hd1
    rw [hd, inv_mul_eq_one] at this
    exact this.symm
  rw [e]
  exact mul_mem (mem_sup_left (mem_inf.mp hk).2) (mem_sup_right hk'Kt)

end CFSG.ComponentClassification.GrSLit.KSw
