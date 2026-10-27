module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58SubDefs

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.LocalCores CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X] {h : Hyp52 X} {y : X}

namespace Hyp52

namespace SubStdAux

abbrev W1 (h : Hyp52 X) (y : X) : Subgroup X := h.W ⊓ h.secSub y

theorem W1_le_G0 : W1 h y ≤ h.secG0 y := inf_le_right.trans (h.secSub_le_G0 y)

theorem B_le_W1 (hc : h.SecCond y) : h.B ≤ W1 h y := le_inf le_normalizer hc.B_le_secSub

abbrev Wp1 (h : Hyp52 X) (y : X) : Subgroup ↥(h.secSubImg y) :=
  normalizer ((h.subB y : Subgroup ↥(h.secSubImg y)) : Set ↥(h.secSubImg y))

theorem mem_Wp1_iff {z : ↥(h.secSubImg y)} :
    z ∈ Wp1 h y ↔ (z : h.secBar y) ∈ normalizer (h.secImage y h.B : Set (h.secBar y)) := by
  show z ∈ normalizer ((h.subB y : Subgroup ↥(h.secSubImg y)) : Set ↥(h.secSubImg y)) ↔ _
  rw [normalizer_subB, mem_subgroupOf]

@[expose] noncomputable def sigma1 (h : Hyp52 X) (y : X) : ↥(W1 h y) →* Wbar h.B :=
  (wbarMk h.B).comp (inclusion inf_le_left)

@[expose] noncomputable def psi1 (h : Hyp52 X) (y : X) : ↥(W1 h y) →* ↥(h.secSubImg y) :=
  ((h.secMk y).comp (inclusion (W1_le_G0 (h := h) (y := y)))).codRestrict _ fun w =>
    mem_map_of_mem (h.secMk y) (show (⟨w, W1_le_G0 w.2⟩ : ↥(h.secG0 y)) ∈
      (h.secSub y).subgroupOf (h.secG0 y) from w.2.2)

@[expose] noncomputable def phi1 (h : Hyp52 X) (y : X) : ↥(W1 h y) →* ↥(Wp1 h y) :=
  (psi1 h y).codRestrict _ fun w =>
    mem_Wp1_iff.mpr (secMk_mem_normalizer (W1_le_G0 w.2) w.2.1)

@[expose] noncomputable def rho1 (h : Hyp52 X) (y : X) : ↥(W1 h y) →* Wbar (h.subB y) :=
  (wbarMk (h.subB y)).comp (phi1 h y)

theorem phi1_coe (w : ↥(W1 h y)) :
    ((phi1 h y w : ↥(h.secSubImg y)) : h.secBar y) = h.secMk y ⟨w, W1_le_G0 w.2⟩ := rfl

theorem phi1_surjective (hc : h.SecCond y) : Function.Surjective (phi1 h y) := by
  rintro ⟨⟨z, hzH⟩, hzN⟩
  have hzN' : z ∈ normalizer (h.secImage y h.B : Set (h.secBar y)) := mem_Wp1_iff.mp hzN
  rw [hc.normalizer_secB] at hzN'
  have hz : z ∈ h.secImage y (normalizer (h.B : Set X) ⊓ h.secSub y) := by
    rw [secImage_inf ((h.secB0_le_B y).trans le_normalizer)]
    exact mem_inf.mpr ⟨hzN', hzH⟩
  obtain ⟨g, hg, rfl⟩ := mem_map.mp hz
  exact ⟨⟨g, hg⟩, rfl⟩

theorem rho1_surjective (hc : h.SecCond y) : Function.Surjective (rho1 h y) :=
  (QuotientGroup.mk'_surjective _).comp (phi1_surjective hc)

theorem ker_sigma1_le (hc : h.SecCond y) : (sigma1 h y).ker ≤ (rho1 h y).ker := by
  intro w hw
  rw [MonoidHom.mem_ker] at hw ⊢
  have h1 : inclusion (inf_le_left : W1 h y ≤ h.W) w ∈ oddTwoCore ↥h.W := by
    rw [← QuotientGroup.eq_one_iff]
    exact hw
  have h2 := B5a.mem_oddTwoCore_of_injective _ (inclusion_injective _) h1
  have h3 := B5a.map_mem_oddTwoCore (phi1 h y) (phi1_surjective hc) h2
  show QuotientGroup.mk' _ (phi1 h y w) = 1
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact h3

theorem oddTwoCore_Wp1_le (hc : h.SecCond y) :
    (oddTwoCore ↥(Wp1 h y)).map (Wp1 h y).subtype ≤
      coreActionKernel ((h.secImage y h.V).subgroupOf (h.secSubImg y)) := by
  obtain ⟨hK1, hK1c⟩ := hc.isPComponent_subL (Or.inl rfl)
  obtain ⟨hK2, hK2c⟩ := hc.isPComponent_subL (Or.inr rfl)
  have hV : (h.secImage y h.V).subgroupOf (h.secSubImg y) =
      (h.secImage y h.K).subgroupOf (h.secSubImg y) ⊔
        (h.secImage y (conjugate h.K h.a)).subgroupOf (h.secSubImg y) := by
    rw [← subgroupOf_sup (secImage_K_le hc) (secImage_mono (conjugate_K_le_secSub hc)),
      secImage_conjugate h.K hc.a_mem_G0, secImage_V hc]
  have hRn : (((oddTwoCore ↥(Wp1 h y)).map (Wp1 h y).subtype).subgroupOf (Wp1 h y)).Normal := by
    rw [show ((oddTwoCore ↥(Wp1 h y)).map (Wp1 h y).subtype).subgroupOf (Wp1 h y) =
      oddTwoCore ↥(Wp1 h y) from comap_map_eq_self_of_injective (Wp1 h y).subtype_injective _]
    infer_instance
  have : Group.IsSolvable ↥(oddTwoCore ↥(Wp1 h y)) := B5a.isSolvable_oddTwoCore _
  have hRs : Group.IsSolvable ↥((oddTwoCore ↥(Wp1 h y)).map (Wp1 h y).subtype) :=
    Group.isSolvable_of_surjective ((Wp1 h y).subtype.subgroupMap_surjective _)
  have hRV : (oddTwoCore ↥(Wp1 h y)).map (Wp1 h y).subtype ≤
      normalizer (((h.secImage y h.V).subgroupOf (h.secSubImg y) : Subgroup ↥(h.secSubImg y)) :
        Set ↥(h.secSubImg y)) := by
    refine (map_subtype_le _).trans fun z hz => ?_
    have h1 : (z : h.secBar y) ∈ normalizer (h.secImage y h.V : Set (h.secBar y)) := by
      rw [← layerIn_secW hc]
      exact OddQuot.le_normalizer_layerIn _ (mem_Wp1_iff.mp hz)
    rw [← subgroupOf_normalizer_eq (secImage_V_le hc)]
    exact h1
  rw [hV] at hRV ⊢
  exact B5a.le_coreActionKernel_of_isSolvable hK1 hK2 hK1c hK2c (map_subtype_le _) hRn hRs hRV

theorem mem_coreActionKernel_of_mem_ker_rho1 (hc : h.SecCond y) {w : ↥(W1 h y)}
    (hw : w ∈ (rho1 h y).ker) : (w : X) ∈ coreActionKernel h.V := by
  rw [MonoidHom.mem_ker] at hw
  have h1 : phi1 h y w ∈ oddTwoCore ↥(Wp1 h y) := by
    rw [← QuotientGroup.eq_one_iff]
    exact hw
  have h2 : (phi1 h y w : ↥(h.secSubImg y)) ∈
      coreActionKernel ((h.secImage y h.V).subgroupOf (h.secSubImg y)) :=
    oddTwoCore_Wp1_le hc (mem_map_of_mem _ h1)
  rw [B5a.coreActionKernel_subgroupOf (secImage_V_le hc), mem_subgroupOf] at h2
  have : Group.IsPerfect h.V := isPerfect_V
  exact mem_coreActionKernel_of_secMk (h.V_le_G0 y) (h.V_le_centralizer_secB0 y) (W1_le_G0 w.2)
    (OddQuot.le_normalizer_layerIn _ w.2.1) h2

theorem B_le_ker_sigma1_rho1 :
    h.B.subgroupOf (W1 h y) ≤ (sigma1 h y).ker ⊓ (rho1 h y).ker := by
  have hB2 := B5a.isPGroup_B h
  intro b hb
  refine mem_inf.mpr ⟨?_, ?_⟩
  · rw [MonoidHom.mem_ker]
    show QuotientGroup.mk' _ (inclusion (inf_le_left : W1 h y ≤ h.W) b) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    refine B5a.le_oddTwoCore (M := h.B.subgroupOf h.W) normal_in_normalizer (fun m hm => ?_) hb
    obtain ⟨k, hk⟩ := hB2 ⟨m, hm⟩
    refine ⟨k, ?_⟩
    have hk' : m ^ 2 ^ k = 1 := by
      apply Subtype.ext
      have h5 := congrArg Subtype.val hk
      simpa using h5
    rw [hk']
    exact one_mem _
  · rw [MonoidHom.mem_ker]
    show QuotientGroup.mk' _ (phi1 h y b) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    have hBbar : IsPGroup 2 (h.subB y) :=
      ((hB2.comap_subtype (K := h.secG0 y)).map (h.secMk y)).comap_subtype
    have hbB : phi1 h y b ∈ (h.subB y).subgroupOf (Wp1 h y) := by
      refine mem_subgroupOf.mpr (mem_subgroupOf.mpr ?_)
      exact mem_map_of_mem (h.secMk y) (show (⟨b, W1_le_G0 b.2⟩ : ↥(h.secG0 y)) ∈
        h.B.subgroupOf (h.secG0 y) from hb)
    refine B5a.le_oddTwoCore (M := (h.subB y).subgroupOf (Wp1 h y)) normal_in_normalizer
      (fun m hm => ?_) hbB
    obtain ⟨k, hk⟩ := hBbar ⟨m, hm⟩
    refine ⟨k, ?_⟩
    have hk' : m ^ 2 ^ k = 1 := by
      have h5 : ((m : ↥(h.secSubImg y))) ^ 2 ^ k = 1 := by
        have h6 := congrArg Subtype.val hk
        simpa using h6
      exact Subtype.ext (by rw [SubmonoidClass.coe_pow, OneMemClass.coe_one]; exact h5)
    rw [hk']
    exact one_mem _

theorem odd_card_map_ker_rho1 (hc : h.SecCond y) :
    Odd (Nat.card ((rho1 h y).ker.map (sigma1 h y).rangeRestrict)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Kρ := (rho1 h y).ker with hKρ
  set σr := (sigma1 h y).rangeRestrict with hσr
  have hle : σr.ker ≤ Kρ := by
    rw [MonoidHom.ker_rangeRestrict]
    exact ker_sigma1_le hc
  have h1 := B5a.card_map_mul_card_ker hle
  set B' := h.B.subgroupOf (W1 h y) with hB'
  have hBW : h.B ≤ W1 h y := B_le_W1 hc
  have hcB : Nat.card B' = Nat.card h.B := Nat.card_congr (subgroupOfEquivOfLe hBW).toEquiv
  have hBσ : B' ≤ σr.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    exact (B_le_ker_sigma1_rho1).trans inf_le_left
  obtain ⟨j, hj⟩ := Subgroup.card_dvd_of_le hBσ
  set Kρ' := Kρ.map (W1 h y).subtype with hKρ'
  have hBK : h.B ≤ Kρ' := by
    intro b hb
    exact ⟨⟨b, hBW hb⟩, ((B_le_ker_sigma1_rho1).trans inf_le_right) hb, rfl⟩
  have hKC : Kρ' ≤ h.W ⊓ coreActionKernel h.V := by
    rintro _ ⟨w, hw, rfl⟩
    exact mem_inf.mpr ⟨w.2.1, mem_coreActionKernel_of_mem_ker_rho1 hc hw⟩
  obtain ⟨R, hR⟩ := h.B_sylow_kernel
  have hodd : ¬ 2 ∣ h.B.relIndex (h.W ⊓ coreActionKernel h.V) := by
    rw [relIndex, ← hR]
    exact R.not_dvd_index
  have hrel := Subgroup.relIndex_mul_relIndex h.B Kρ' _ hBK hKC
  have hodd' : ¬ 2 ∣ h.B.relIndex Kρ' := fun h2 => hodd (hrel ▸ dvd_mul_of_dvd_left h2 _)
  have h2 := Subgroup.relIndex_mul_card (H := h.B) (K := Kρ')
  rw [inf_of_le_left hBK] at h2
  have hcK : Nat.card Kρ' = Nat.card Kρ :=
    (Nat.card_congr (Kρ.equivMapOfInjective _ (W1 h y).subtype_injective).toEquiv).symm
  have hBpos : 0 < Nat.card h.B := Nat.card_pos
  have h3 : Nat.card (Kρ.map σr) * j = h.B.relIndex Kρ' := by
    apply Nat.eq_of_mul_eq_mul_right hBpos
    calc Nat.card (Kρ.map σr) * j * Nat.card h.B = Nat.card (Kρ.map σr) * Nat.card σr.ker := by
          rw [hj, hcB]; ring
      _ = Nat.card Kρ := h1
      _ = h.B.relIndex Kρ' * Nat.card h.B := by rw [h2, hcK]
  have h4 : ¬ 2 ∣ Nat.card (Kρ.map σr) := fun h5 => hodd' (h3 ▸ dvd_mul_of_dvd_left h5 _)
  exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h4)

@[expose] noncomputable def tau1 (hc : h.SecCond y) :
    ↥(sigma1 h y).range →* Wbar (h.subB y) :=
  (QuotientGroup.lift (sigma1 h y).rangeRestrict.ker (rho1 h y)
    (by rw [MonoidHom.ker_rangeRestrict]; exact ker_sigma1_le hc)).comp
    (QuotientGroup.quotientKerEquivOfSurjective _
      (sigma1 h y).rangeRestrict_surjective).symm.toMonoidHom

theorem tau1_apply (hc : h.SecCond y) (w : ↥(W1 h y)) :
    tau1 hc ((sigma1 h y).rangeRestrict w) = rho1 h y w := by
  have he : (QuotientGroup.quotientKerEquivOfSurjective (sigma1 h y).rangeRestrict
      (sigma1 h y).rangeRestrict_surjective).symm ((sigma1 h y).rangeRestrict w) =
      (QuotientGroup.mk w : ↥(W1 h y) ⧸ (sigma1 h y).rangeRestrict.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [tau1, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, he, QuotientGroup.lift_mk]

theorem tau1_surjective (hc : h.SecCond y) : Function.Surjective (tau1 hc) := by
  intro z
  obtain ⟨w, rfl⟩ := rho1_surjective hc z
  exact ⟨_, tau1_apply hc w⟩

theorem ker_tau1 (hc : h.SecCond y) :
    (tau1 hc).ker = (rho1 h y).ker.map (sigma1 h y).rangeRestrict := by
  have hle : (sigma1 h y).rangeRestrict.ker ≤ (rho1 h y).ker := by
    rw [MonoidHom.ker_rangeRestrict]
    exact ker_sigma1_le hc
  ext r
  obtain ⟨w, rfl⟩ := (sigma1 h y).rangeRestrict_surjective r
  rw [MonoidHom.mem_ker, tau1_apply, B5a.mem_map_iff_of_ker_le hle, MonoidHom.mem_ker]

theorem odd_card_ker_tau1 (hc : h.SecCond y) : Odd (Nat.card (tau1 hc).ker) := by
  rw [ker_tau1 hc]
  exact odd_card_map_ker_rho1 hc

theorem JB_le_range (hc : h.SecCond y) :
    wbarImage h.B (GSLit.fixedLayer h.J h.B) ≤ (sigma1 h y).range := by
  rintro _ ⟨j, hj, rfl⟩
  have hjV : (j : X) ∈ h.V := B5a.fixedLayer_le_V h hj
  exact ⟨⟨j, j.2, V_le_secSub hc hjV⟩, rfl⟩

theorem ker_tau1_le_centralizer (hc : h.SecCond y) : (tau1 hc).ker ≤
    centralizer (((wbarImage h.B (GSLit.fixedLayer h.J h.B)).subgroupOf (sigma1 h y).range :
      Subgroup ↥(sigma1 h y).range) : Set ↥(sigma1 h y).range) := by
  rw [ker_tau1 hc]
  rintro _ ⟨w, hw, rfl⟩
  have hwK := mem_coreActionKernel_of_mem_ker_rho1 hc hw
  have hOVW : oddCoreIn h.V ≤ oddCoreIn h.W :=
    B5a.oddCoreIn_le_of_le_normalizer V_le_W (OddQuot.le_normalizer_layerIn _)
  rw [mem_centralizer_iff]
  intro l hl
  obtain ⟨j, hj, hjl⟩ := mem_map.mp
    (show (l : Wbar h.B) ∈ wbarImage h.B (GSLit.fixedLayer h.J h.B) from hl)
  have hjV : (j : X) ∈ h.V := B5a.fixedLayer_le_V h hj
  set w' : ↥h.W := inclusion (inf_le_left : W1 h y ≤ h.W) w with hw'
  have h1 : ((j : X))⁻¹ * (w : X)⁻¹ * j * w ∈ oddCoreIn h.W :=
    hOVW ((mem_coreActionKernel.mp hwK).2 j hjV)
  obtain ⟨o, ho, hoe⟩ := mem_map.mp h1
  have h2 : o = j⁻¹ * w'⁻¹ * j * w' :=
    Subtype.ext (by simp only [coe_mul, coe_inv, hw', coe_inclusion]; exact hoe)
  have h3 : wbarMk h.B (j⁻¹ * w'⁻¹ * j * w') = 1 := by
    rw [← h2, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact Hyp52.pPrimeCore_le_oddTwoCore _ ho
  apply Subtype.ext
  show (l : Wbar h.B) * sigma1 h y w = sigma1 h y w * l
  rw [← hjl]
  show wbarMk h.B j * wbarMk h.B w' = wbarMk h.B w' * wbarMk h.B j
  simp only [map_mul, map_inv] at h3
  calc wbarMk h.B j * wbarMk h.B w' = wbarMk h.B w' * wbarMk h.B j *
        ((wbarMk h.B j)⁻¹ * (wbarMk h.B w')⁻¹ * wbarMk h.B j * wbarMk h.B w') := by group
    _ = wbarMk h.B w' * wbarMk h.B j := by rw [h3, mul_one]

theorem sigma1_a_ne_one (hc : h.SecCond y) :
    sigma1 h y ⟨h.a, h.a_mem_normalizer, hc.a_mem_secSub⟩ ≠ 1 :=
  secSigma_a_ne_one hc

theorem even_card_centralizer_range (hc : h.SecCond y) :
    Even (Nat.card (centralizer (((wbarImage h.B (GSLit.fixedLayer h.J h.B)).subgroupOf
      (sigma1 h y).range : Subgroup ↥(sigma1 h y).range) : Set ↥(sigma1 h y).range))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set t : ↥(sigma1 h y).range := (sigma1 h y).rangeRestrict
    ⟨h.a, h.a_mem_normalizer, hc.a_mem_secSub⟩ with ht
  have htC : t ∈ centralizer (((wbarImage h.B (GSLit.fixedLayer h.J h.B)).subgroupOf
      (sigma1 h y).range : Subgroup ↥(sigma1 h y).range) : Set ↥(sigma1 h y).range) := by
    rw [mem_centralizer_iff]
    intro l hl
    obtain ⟨j, hj, hjl⟩ := mem_map.mp
      (show (l : Wbar h.B) ∈ wbarImage h.B (GSLit.fixedLayer h.J h.B) from hl)
    apply Subtype.ext
    show (l : Wbar h.B) * sigma1 h y ⟨h.a, h.a_mem_normalizer, hc.a_mem_secSub⟩ =
      sigma1 h y ⟨h.a, h.a_mem_normalizer, hc.a_mem_secSub⟩ * l
    rw [← hjl]
    show wbarMk h.B j * wbarMk h.B ⟨h.a, h.a_mem_normalizer⟩ =
      wbarMk h.B ⟨h.a, h.a_mem_normalizer⟩ * wbarMk h.B j
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp
      (h.J_le (((GSLit.fixedLayer_le_inf h.J h.B).trans inf_le_left) hj))
  have ht2 : orderOf t = 2 := by
    apply orderOf_eq_prime
    · rw [ht, ← map_pow]
      have h1 : (⟨h.a, h.a_mem_normalizer, hc.a_mem_secSub⟩ : ↥(W1 h y)) ^ 2 = 1 := by
        apply Subtype.ext
        rw [coe_pow, ← h.orderOf_a, pow_orderOf_eq_one]
        rfl
      rw [h1, map_one]
    · intro h1
      apply sigma1_a_ne_one hc
      have h2 := congrArg Subtype.val h1
      exact h2
  rw [even_iff_two_dvd, ← ht2]
  have h3 := orderOf_dvd_natCard (⟨t, htC⟩ : centralizer (((wbarImage h.B
    (GSLit.fixedLayer h.J h.B)).subgroupOf (sigma1 h y).range : Subgroup ↥(sigma1 h y).range) :
      Set ↥(sigma1 h y).range))
  rwa [Subgroup.orderOf_mk] at h3

theorem fixedLayer_subJ_subB (hc : h.SecCond y) :
    GSLit.fixedLayer (h.subJ y) (h.subB y) =
      (h.secImage y (GSLit.fixedLayer h.J h.B)).subgroupOf (h.secSubImg y) := by
  rw [B5a.fixedLayer_subgroupOf (h.secImage_secJ0_le y) (h.secImage_B_le y), secFixedLayer_B hc]

theorem map_tau1_eq (hc : h.SecCond y) :
    ((wbarImage h.B (GSLit.fixedLayer h.J h.B)).subgroupOf (sigma1 h y).range).map
      (tau1 hc) = wbarImage (h.subB y)
        ((h.secImage y (GSLit.fixedLayer h.J h.B)).subgroupOf (h.secSubImg y)) := by
  ext z
  constructor
  · rintro ⟨l, hl, rfl⟩
    obtain ⟨j, hj, hjl⟩ := mem_map.mp
      (show (l : Wbar h.B) ∈ wbarImage h.B (GSLit.fixedLayer h.J h.B) from hl)
    have hjV : (j : X) ∈ h.V := B5a.fixedLayer_le_V h hj
    have hjW1 : (j : X) ∈ W1 h y := ⟨j.2, V_le_secSub hc hjV⟩
    have hl' : l = (sigma1 h y).rangeRestrict ⟨j, hjW1⟩ := Subtype.ext (by rw [← hjl]; rfl)
    rw [hl', tau1_apply]
    show wbarMk (h.subB y) (phi1 h y ⟨j, hjW1⟩) ∈ _
    refine mem_map_of_mem (wbarMk (h.subB y)) (mem_subgroupOf.mpr (mem_subgroupOf.mpr ?_))
    exact mem_map_of_mem (h.secMk y) (show (⟨j, W1_le_G0 hjW1⟩ : ↥(h.secG0 y)) ∈
      (GSLit.fixedLayer h.J h.B).subgroupOf (h.secG0 y) from hj)
  · rintro ⟨p, hp, rfl⟩
    have hp' : ((p : ↥(h.secSubImg y)) : h.secBar y) ∈
        h.secImage y (GSLit.fixedLayer h.J h.B) := mem_subgroupOf.mp (mem_subgroupOf.mp hp)
    obtain ⟨j, hj, hjp⟩ := mem_map.mp hp'
    have hjV : (j : X) ∈ h.V := B5a.fixedLayer_le_V h hj
    have hjW1 : (j : X) ∈ W1 h y := ⟨V_le_W hjV, V_le_secSub hc hjV⟩
    refine ⟨(sigma1 h y).rangeRestrict ⟨j, hjW1⟩, ?_, ?_⟩
    · exact mem_map_of_mem (wbarMk h.B) (show (⟨j, V_le_W hjV⟩ : ↥h.W) ∈
        (GSLit.fixedLayer h.J h.B).subgroupOf h.W from hj)
    · rw [tau1_apply]
      show wbarMk (h.subB y) (phi1 h y ⟨j, hjW1⟩) = wbarMk (h.subB y) p
      congr 1
      apply Subtype.ext
      apply Subtype.ext
      rw [phi1_coe]
      exact hjp

theorem tau1_a (hc : h.SecCond y) :
    tau1 hc ((sigma1 h y).rangeRestrict ⟨h.a, h.a_mem_normalizer, hc.a_mem_secSub⟩) =
      wbarMk (h.subB y) ⟨hc.subA, hc.subA_mem_normalizer⟩ := by
  rw [tau1_apply]
  rfl

end SubStdAux

theorem SecCond.isStandard_subBar (hc : h.SecCond y) :
    IsStandardSubgroup (wbarImage (h.subB y) (GSLit.fixedLayer (h.subJ y) (h.subB y))) := by
  rw [SubStdAux.fixedLayer_subJ_subB hc]
  have h1 := B5a.isStandardSubgroup_subgroupOf (SubStdAux.JB_le_range hc) h.isStandard_bar
    (SubStdAux.even_card_centralizer_range hc)
  have h2 := B5a.isStandardSubgroup_map (SubStdAux.tau1_surjective hc) h1
    (SubStdAux.odd_card_ker_tau1 hc) (SubStdAux.ker_tau1_le_centralizer hc)
  rwa [SubStdAux.map_tau1_eq hc] at h2

theorem SecCond.isComponent_subBar (hc : h.SecCond y) :
    wbarImage (h.subB y) (GSLit.fixedLayer (h.subJ y) (h.subB y)) ≤
        centralizer ({wbarMk (h.subB y) ⟨hc.subA, hc.subA_mem_normalizer⟩} :
          Set (Wbar (h.subB y))) ∧
      IsComponent ((wbarImage (h.subB y) (GSLit.fixedLayer (h.subJ y) (h.subB y))).subgroupOf
        (centralizer ({wbarMk (h.subB y) ⟨hc.subA, hc.subA_mem_normalizer⟩} :
          Set (Wbar (h.subB y))))) := by
  rw [SubStdAux.fixedLayer_subJ_subB hc]
  obtain ⟨hLC, hcomp⟩ := h.isComponent_bar
  have htH : wbarMk h.B ⟨h.a, h.a_mem_normalizer⟩ ∈ (SubStdAux.sigma1 h y).range :=
    ⟨⟨h.a, h.a_mem_normalizer, hc.a_mem_secSub⟩, rfl⟩
  obtain ⟨h1, h2⟩ :=
    B5a.isComponent_subgroupOf_centralizer htH (SubStdAux.JB_le_range hc) hLC hcomp
  have hteq : (⟨wbarMk h.B ⟨h.a, h.a_mem_normalizer⟩, htH⟩ : ↥(SubStdAux.sigma1 h y).range) =
      (SubStdAux.sigma1 h y).rangeRestrict ⟨h.a, h.a_mem_normalizer, hc.a_mem_secSub⟩ := rfl
  have ht : (⟨wbarMk h.B ⟨h.a, h.a_mem_normalizer⟩, htH⟩ : ↥(SubStdAux.sigma1 h y).range) *
      ⟨wbarMk h.B ⟨h.a, h.a_mem_normalizer⟩, htH⟩ = 1 := by
    apply Subtype.ext
    show wbarMk h.B ⟨h.a, h.a_mem_normalizer⟩ * wbarMk h.B ⟨h.a, h.a_mem_normalizer⟩ = 1
    rw [← map_mul]
    have h3 : (⟨h.a, h.a_mem_normalizer⟩ : ↥h.W) * ⟨h.a, h.a_mem_normalizer⟩ = 1 := by
      apply Subtype.ext
      show h.a * h.a = 1
      rw [← pow_two, ← h.orderOf_a, pow_orderOf_eq_one]
    rw [h3, map_one]
  obtain ⟨h4, h5⟩ := B5a.isComponent_map_centralizer (SubStdAux.tau1_surjective hc)
    (SubStdAux.odd_card_ker_tau1 hc) (SubStdAux.ker_tau1_le_centralizer hc) ht h1 h2
  rw [hteq, SubStdAux.tau1_a hc, SubStdAux.map_tau1_eq hc] at h4 h5
  exact ⟨h4, h5⟩

end Hyp52

end CFSG.ComponentClassification.GSThmB
