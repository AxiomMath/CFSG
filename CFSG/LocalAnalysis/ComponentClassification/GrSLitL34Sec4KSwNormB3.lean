module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4KSwNormB2
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeSNFour
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitGoldschmidt
import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeSNConn
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.ComponentClassification.GrSLit.KSw

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS

variable {G : Type} [Group G] [Finite G]

theorem zStarIn_eq_oddIn_of_zOne {a : G} {J W K S : Subgroup G}
    (hs : SingleComponentSetting G a J W K) (hSsyl : IsSylowTwoIn S (normalizer (J : Set G)))
    (hZ1 : S ⊓ zStarIn J = ⊥) : zStarIn K = oddIn K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm ?_ (GrS4.oddIn_le_zStarIn K)
  have hodd : Odd (Nat.card ↥(zStarIn K)) := by
    by_contra hodd
    have h2 : 2 ∣ Nat.card ↥(zStarIn K) := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥(zStarIn K)) 2 h2
    have hy2 : orderOf (y : G) = 2 := by rw [Subgroup.orderOf_coe, hy]
    have hP : IsPGroup 2 (zpowers (y : G)) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy2, pow_one])
    have h1 := inf_zStarIn_eq_bot_of_zOne hs hSsyl hZ1 hP
    have h3 : (y : G) ∈ zpowers (y : G) ⊓ zStarIn K := mem_inf.mpr ⟨mem_zpowers _, y.2⟩
    rw [h1, mem_bot] at h3
    rw [h3, orderOf_one] at hy2
    exact absurd hy2 (by norm_num)
  refine GrSLit.le_map_pPrimeCore (map_subtype_le _) (fun k hk z hz => ?_) hodd
  have : (Open.fusionZStar ↥K).Characteristic := inferInstance
  exact (mem_normalizer_iff.mp
    (normalizer_le_normalizer_map_of_characteristic K (Open.fusionZStar ↥K) (le_normalizer hk))
    z).mp hz

theorem mem_normalizer_of_orderOf_eq_two [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    {W K T : Subgroup G} (hKM : K ≤ normalizer (W : Set G))
    (hKc : IsPComponent 2 (K.subgroupOf (normalizer (W : Set G))))
    (hKC : Odd (Nat.card ↥(K ⊓ coreActionKernel K)))
    (hTsyl : IsSylowTwoIn T (normalizer (W : Set G))) (hTG : ∃ P : Sylow 2 G, (P : Subgroup G) = T)
    (hWT : ∀ F : Subgroup G, F ≤ T → IsEightGroup F →
      (∃ t ∈ T, t * t = 1 ∧ (∀ e ∈ F, t * e = e * t) ∧ t ∉ F) → wGroup F = W)
    {t : G} (htT : t ∈ T) (htK : t ∉ normalizer (K : Set G))
    (httK : t * t ∈ normalizer (K : Set G))
    (hr2 : ∀ m ∈ normalizer (W : Set G), conjugate K m = K ∨ conjugate K m = conjugate K t)
    {E : Subgroup G} (hET : E ≤ T ⊓ K) (hE : IsElemTwo E) (hE16 : Nat.card E = 16)
    {y : G} (hyM : y ∈ normalizer (W : Set G)) (hy2 : orderOf y = 2) :
    y ∈ normalizer (K : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P₀, hP₀⟩ := hTG
  have hT2 := GrS4.isPGroup_of_isSylowTwoIn hTsyl
  have hTM := hTsyl.1
  set M : Subgroup G := normalizer (W : Set G) with hM
  set M₀ : Subgroup G := M ⊓ normalizer (K : Set G) with hM₀
  have hidx := HeSN.relIndex_eq_two (hTM htT) htK httK hr2
  have hidx' : (M₀.subgroupOf M).index = 2 := hidx
  have hmul : ∀ x ∈ M, ∀ y ∈ M, (x * y ∈ M₀ ↔ (x ∈ M₀ ↔ y ∈ M₀)) := fun x hx y hy => by
    have h1 := Subgroup.mul_mem_iff_of_index_two hidx' (a := ⟨x, hx⟩) (b := ⟨y, hy⟩)
    simpa [mem_subgroupOf] using h1
  have hconj : ∀ m ∈ M, ∀ x ∈ M₀, m * x * m⁻¹ ∈ M₀ := by
    intro m hm x hx
    have hxM := (mem_inf.mp hx).1
    rw [hmul _ (mul_mem hm hxM) _ (inv_mem hm), hmul _ hm _ hxM]
    have h1 := hmul m hm m⁻¹ (inv_mem hm)
    rw [mul_inv_cancel] at h1
    have h2 := h1.mp (one_mem _)
    exact ⟨fun h3 => h2.mp (h3.mpr hx), fun h3 => ⟨fun _ => hx, fun _ => h2.mpr h3⟩⟩
  have key : ∀ s ∈ T, orderOf s = 2 → s ∈ M₀ := by
    intro s hsT hs2
    by_contra hsM₀
    have hss : s * s = 1 := by rw [← pow_two, ← hs2, pow_orderOf_eq_one]
    have hsK : conjugate K s ≠ K := fun e =>
      hsM₀ (mem_inf.mpr ⟨hTM hsT, mem_normalizer_of_conjugate_eq e⟩)
    have hU : (T ⊓ M₀).relIndex T = 2 := by
      rw [relIndex_eq_two_iff]
      refine ⟨s, hsT, fun b hb => ?_⟩
      have h1 := hmul b (hTM hb) s (hTM hsT)
      simp only [mem_inf, hb, mul_mem hb hsT, true_and]
      by_cases hbM : b ∈ M₀
      · exact Or.inr ⟨hbM, fun h2 => hsM₀ ((h1.mp h2).mp hbM)⟩
      · exact Or.inl ⟨h1.mpr ⟨fun h2 => absurd h2 hbM, fun h2 => absurd h2 hsM₀⟩, hbM⟩
    rcases goldschmidtTransferInput_holds G P₀ s (hP₀ ▸ hsT) hs2 with hall | hres
    · obtain ⟨g, hgU, hgext⟩ := hall (T ⊓ M₀) (by rw [hP₀]; exact inf_le_left)
        (by rw [hP₀]; exact hU)
      rw [hP₀] at hgext
      obtain ⟨F, hFT, hF, w, hwT, hww, hwF, hwn⟩ := exists_witness_of_involution hKM hKc hKC hT2
        hTM hsT hss hsK hET hE hE16
      obtain ⟨m, hmM, hm⟩ := exists_conj_of_witness hT2 hWT hgext hFT hF hwT hww hwF hwn
      apply hsM₀
      have h1 := hconj m hmM _ (mem_inf.mp hgU).2
      rwa [hm, show m * (m⁻¹ * s * m) * m⁻¹ = s by group] at h1
    · exact hres (HeSN.mem_twoResidualOf_top' hnab s)
  obtain ⟨n, hnM, hny⟩ := hTsyl.exists_conj_le (zpowers_le.mpr hyM) (HeSN.isPGroup_zpowers hy2)
  have hny2 : orderOf (n * y * n⁻¹) = 2 := by
    rw [← hy2]
    exact (SemiconjBy.orderOf_eq n (show n * y = n * y * n⁻¹ * n by group)).symm
  have h1 := hconj n⁻¹ (inv_mem hnM) _ (key _ (hny y (mem_zpowers y)) hny2)
  rw [show n⁻¹ * (n * y * n⁻¹) * n⁻¹⁻¹ = y by group] at h1
  exact (mem_inf.mp h1).2

theorem exists_mul_of_mem_sup_kernel' {K T : Subgroup G} (hT2 : IsPGroup 2 T)
    (hTK : IsSylowTwoIn (T ⊓ K) K) (hKC : Odd (Nat.card ↥(K ⊓ coreActionKernel K))) {x : G}
    (hxT : x ∈ T) (hxN : x ∈ normalizer (K : Set G)) (hx : x ∈ K ⊔ coreActionKernel K) :
    ∃ k ∈ T ⊓ K, ∃ p ∈ T ⊓ coreActionKernel K, x = k * p := by
  have hDK : T ⊓ normalizer (K : Set G) ⊓ K = T ⊓ K := by
    rw [inf_assoc, inf_of_le_right (le_normalizer : K ≤ normalizer (K : Set G))]
  obtain ⟨k, hk, p, hp, hkp⟩ := exists_mul_of_mem_sup_kernel (hT2.to_le inf_le_left)
    (inf_le_right : T ⊓ normalizer (K : Set G) ≤ _) (hDK ▸ hTK) hKC (mem_inf.mpr ⟨hxT, hxN⟩) hx
  exact ⟨k, hDK ▸ hk, p, mem_inf.mpr ⟨(mem_inf.mp (mem_inf.mp hp).1).1, (mem_inf.mp hp).2⟩, hkp⟩

theorem exists_order_four
    (hCoset : ∀ (G : Type) [Group G] [Finite G] (J S : Subgroup G), ⁅J, J⁆ = J →
      IsL34Type (J ⧸ Open.fusionZStar J) → zStarIn J = oddIn J →
      S ≤ normalizer (J : Set G) → IsPGroup 2 S → IsSylowTwoIn (S ⊓ J) J →
      ∀ s ∈ S, ∃ y ∈ S, s⁻¹ * y ∈ withKernel J ∧ y * y ∈ coreActionKernel J)
    {W K T : Subgroup G} (hKM : K ≤ normalizer (W : Set G))
    (hKc : IsPComponent 2 (K.subgroupOf (normalizer (W : Set G))))
    (hKL : IsL34Type (K ⧸ Open.fusionZStar K)) (hKZ : zStarIn K = oddIn K)
    (hKC : Odd (Nat.card ↥(K ⊓ coreActionKernel K))) (hT2 : IsPGroup 2 T)
    (hTM : T ≤ normalizer (W : Set G)) (hTK : IsSylowTwoIn (T ⊓ K) K) {t : G} (htT : t ∈ T)
    (htK : t ∉ normalizer (K : Set G)) (httK : t * t ∈ normalizer (K : Set G))
    (hQ : ∀ x ∈ T, x ∈ coreActionKernel K → x ∈ coreActionKernel (conjugate K t) → x = 1)
    (hinv : ∀ y ∈ normalizer (W : Set G), orderOf y = 2 → y ∈ normalizer (K : Set G)) :
    ∃ u ∈ T, u ∉ normalizer (K : Set G) ∧ u ^ 4 = 1 ∧ u * u ≠ 1 ∧
      u * u ∈ normalizer (K : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htM := hTM htT
  have hKt : conjugate K t ≠ K := fun e => htK (mem_normalizer_of_conjugate_eq e)
  have hKtK : K ≤ normalizer (conjugate K t : Set G) :=
    (GrS5.commutator_le_of_ne (conjugate_le_of_mem hKM htM)
      hKM (isPComponent_conjugate_subgroupOf htM hKc) hKc hKt).2
  have hck : ∀ k ∈ K, t⁻¹ * k * t ∈ coreActionKernel K := fun k hk =>
    conj_mem_coreActionKernel_of_ne hKM hKc hk htM hKt
  have hcK : ∀ {g x : G}, g ∈ normalizer (K : Set G) → x ∈ coreActionKernel K →
      g * x * g⁻¹ ∈ coreActionKernel K :=
    fun hg hx => UnbalancedLayer.conj_mem_coreActionKernel hg hx
  have hKk : ∀ k ∈ K, conjugate K (t * k) = conjugate K t := fun k hk => by
    rw [← conjugate_conjugate, conjugate_eq_of_mem_normalizer (hKtK hk)]
  by_cases hin : t * t ∈ K ⊔ coreActionKernel K
  ·
    exfalso
    obtain ⟨k, hk, p, hp, hkp⟩ :=
      exists_mul_of_mem_sup_kernel' hT2 hTK hKC (mul_mem htT htT) httK hin
    have hkT := (mem_inf.mp hk).1
    have hkK := (mem_inf.mp hk).2
    have hyT : t * k⁻¹ ∈ T := mul_mem htT (inv_mem hkT)
    have hyK : t * k⁻¹ ∉ normalizer (K : Set G) := fun hy => htK (by
      rw [show t = t * k⁻¹ * k by group]
      exact mul_mem hy (le_normalizer hkK))
    have hyy : t * k⁻¹ * (t * k⁻¹) = k * (p * (t⁻¹ * k⁻¹ * t)) * k⁻¹ := by
      calc t * k⁻¹ * (t * k⁻¹) = t * t * (t⁻¹ * k⁻¹ * t) * k⁻¹ := by group
        _ = k * p * (t⁻¹ * k⁻¹ * t) * k⁻¹ := by rw [hkp]
        _ = k * (p * (t⁻¹ * k⁻¹ * t)) * k⁻¹ := by group
    have hyyK : t * k⁻¹ * (t * k⁻¹) ∈ coreActionKernel K := by
      rw [hyy]
      exact hcK (le_normalizer hkK) (mul_mem (mem_inf.mp hp).2 (hck _ (inv_mem hkK)))
    have hyyKt := HeSN.mem_kernel_conjugate (hKk _ (inv_mem hkK)) hyyK (by group)
    have hy1 := hQ _ (mul_mem hyT hyT) hyyK hyyKt
    have hy2 : orderOf (t * k⁻¹) = 2 :=
      orderOf_eq_prime (by rw [pow_two]; exact hy1) fun h1 => hyK (h1 ▸ one_mem _)
    exact hyK (hinv _ (hTM hyT) hy2)
  ·
    have hD2 : IsPGroup 2 ↥(T ⊓ normalizer (K : Set G)) := hT2.to_le inf_le_left
    have hDK : IsSylowTwoIn (T ⊓ normalizer (K : Set G) ⊓ K) K := by
      rwa [inf_assoc, inf_of_le_right (le_normalizer : K ≤ normalizer (K : Set G))]
    obtain ⟨y₀, hy₀S, hd, hy₀y₀⟩ := hCoset G K (T ⊓ normalizer (K : Set G))
      (commutator_eq_of_isPComponent hKM hKc) hKL hKZ inf_le_right hD2 hDK (t * t)
      (mem_inf.mpr ⟨mul_mem htT htT, httK⟩)
    have hy₀N := (mem_inf.mp hy₀S).2
    have hy₀K : y₀ ∉ K ⊔ coreActionKernel K := fun h => hin (by
      have := mul_mem h (inv_mem hd)
      rwa [mul_inv_rev, inv_inv, mul_inv_cancel_left] at this)
    obtain ⟨k, hk, p, hp, hkp⟩ := exists_mul_of_mem_sup_kernel' hT2 hTK hKC
      (mul_mem (inv_mem (mul_mem htT htT)) (mem_inf.mp hy₀S).1)
      (mul_mem (inv_mem httK) hy₀N) hd
    have hkT := (mem_inf.mp hk).1
    have hkK := (mem_inf.mp hk).2
    have hpK := (mem_inf.mp hp).2
    have hy₀ : y₀ = t * t * (k * p) := (inv_mul_eq_iff_eq_mul.mp hkp)
    set c : G := p⁻¹ * (k⁻¹ * (t⁻¹ * k * t) * k) with hc
    have hcK' : c ∈ coreActionKernel K := by
      refine mul_mem (inv_mem hpK) ?_
      have h1 := hcK (inv_mem (le_normalizer hkK)) (hck k hkK)
      rwa [inv_inv] at h1
    have hu2 : t * k * (t * k) = y₀ * c := by
      rw [hy₀, hc]
      group
    have huT : t * k ∈ T := mul_mem htT hkT
    have huK : t * k ∉ normalizer (K : Set G) := fun hu => htK (by
      rw [show t = t * k * k⁻¹ by group]
      exact mul_mem hu (inv_mem (le_normalizer hkK)))
    have hu4K : t * k * (t * k) * (t * k * (t * k)) ∈ coreActionKernel K := by
      rw [hu2, show y₀ * c * (y₀ * c) = y₀ * y₀ * (y₀⁻¹ * c * y₀⁻¹⁻¹) * c by group]
      exact mul_mem (mul_mem hy₀y₀ (hcK (inv_mem hy₀N) hcK')) hcK'
    have hu4Kt := HeSN.mem_kernel_conjugate (hKk k hkK) hu4K (by group)
    have hu4 := hQ _ (mul_mem (mul_mem huT huT) (mul_mem huT huT)) hu4K hu4Kt
    refine ⟨t * k, huT, huK, ?_, fun h1 => hy₀K ?_, ?_⟩
    · rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
      exact hu4
    · rw [hu2] at h1
      rw [eq_inv_of_mul_eq_one_left h1]
      exact mem_sup_right (inv_mem hcK')
    · rw [hu2]
      exact mul_mem hy₀N (mem_coreActionKernel.mp hcK').1

end CFSG.ComponentClassification.GrSLit.KSw
