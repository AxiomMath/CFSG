module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SONanConfig
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SKernelClosure
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SONanGluing
public import CFSG.GroupTheory.Frattini.PSubgroupLift
public import CFSG.GroupTheory.CoprimeActionSupport.NormalPSubgroupMeetsCenter
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open CFSG.Blueprint.NativeSporadic (IsSporadic)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ONPar
open CFSG.ClassicalInvolution.Balance (TwoBalancedWrt)
open scoped commutatorElement

private theorem false_of_onan_normal_component_core
    (hGold : GoldschmidtStronglyClosedInput)
    {G : Type} [Group G] [Finite G] {t : G} {P W M : Subgroup G}
    (hM : M = normalizer (W : Set G)) (htM : t ∈ M)
    (hsimple : IsSimpleGroup G)
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (ht2 : orderOf t = 2)
    (hPM : P ≤ M)
    (hPt : P ≤ centralizer ({t} : Set G))
    (hPON : IsSporadic (↥P ⧸ pPrimeCore 2 ↥P) .ONan)
    (hPperf : Group.IsPerfect ↥P)
    (hWGroupEq : ∀ E : Subgroup G, E ≤ centralizer ({t} : Set G) →
      IsElemTwo E → 8 ≤ Nat.card E → wGroup E = W)
    (hBal : ∀ S : Subgroup G, IsSylowTwoIn S M → t ∈ S →
      ∀ E : Subgroup G, E ≤ S → IsElemTwo E → TwoBalancedWrt E)
    {L : Subgroup (↥M ⧸ pPrimeCore 2 ↥M)} (hLn : L.Normal)
    (hZ : center ↥L = ⊥)
    (hPL : (P.subgroupOf M).map (QuotientGroup.mk' (pPrimeCore 2 ↥M)) = L)
    (hcent : ∀ x ∈ L, QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨t, htM⟩ * x =
      x * QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨t, htM⟩) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let X := ↥M ⧸ pPrimeCore 2 ↥M
  let π : ↥M →* X := QuotientGroup.mk' (pPrimeCore 2 ↥M)
  let HM : Subgroup ↥M := L.comap π
  let KM : Subgroup ↥M := (Subgroup.centralizer (L : Set X)).comap π
  let H : Subgroup G := HM.map M.subtype
  let K : Subgroup G := KM.map M.subtype
  have hHMle : H ≤ M := Subgroup.map_subtype_le HM
  have hKMle : K ≤ M := Subgroup.map_subtype_le KM
  have hHMnorm : HM.Normal := hLn.comap π
  have hKMnorm : KM.Normal := by
    have : L.Normal := hLn
    exact Subgroup.Normal.comap (Subgroup.normal_centralizer (H := L)) π
  have hHsub : H.subgroupOf M = HM := by
    show (HM.map M.subtype).comap M.subtype = HM
    exact Subgroup.comap_map_eq_self_of_injective M.subtype_injective HM
  have hKsub : K.subgroupOf M = KM := by
    show (KM.map M.subtype).comap M.subtype = KM
    exact Subgroup.comap_map_eq_self_of_injective M.subtype_injective KM
  have hMH : M ≤ normalizer (H : Set G) := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hHMle).mp ?_
    rwa [hHsub]
  have hMK : M ≤ normalizer (K : Set G) := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hKMle).mp ?_
    rwa [hKsub]
  have hPH : P ≤ H := by
    intro p hp
    refine Subgroup.mem_map.mpr ⟨⟨p, hPM hp⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap, ← hPL]
    exact Subgroup.mem_map.mpr ⟨⟨p, hPM hp⟩, Subgroup.mem_subgroupOf.mpr hp, rfl⟩
  have hOH : oddIn M ≤ H := by
    intro x hx
    rw [oddIn] at hx
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hx
    refine Subgroup.mem_map.mpr ⟨m, ?_, rfl⟩
    rw [Subgroup.mem_comap, QuotientGroup.mk'_apply]
    rw [(QuotientGroup.eq_one_iff (N := pPrimeCore 2 ↥M) m).mpr hm]
    exact L.one_mem
  have hH_eq : H = P ⊔ oddIn M := by
    refine le_antisymm ?_ (sup_le hPH hOH)
    intro x hx
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hx
    have hmL : π m ∈ L := hm
    rw [← hPL] at hmL
    obtain ⟨pm, hpsub, hπp⟩ := Subgroup.mem_map.mp hmL
    have hpP : (pm : ↥M).1 ∈ P := Subgroup.mem_subgroupOf.mp hpsub
    have hker : m * pm⁻¹ ∈ pPrimeCore 2 ↥M := by
      have h1 : (QuotientGroup.mk' (pPrimeCore 2 ↥M)) (m * pm⁻¹) = 1 := by
        rw [map_mul, map_inv, hπp]
        exact mul_inv_cancel _
      exact (QuotientGroup.eq_one_iff (m * pm⁻¹)).mp h1
    have hodd : M.subtype (m * pm⁻¹) ∈ oddIn M := by
      rw [oddIn]
      exact Subgroup.mem_map.mpr ⟨m * pm⁻¹, hker, rfl⟩
    have hpp : M.subtype pm ∈ P := by simpa using hpP
    have hmul := Subgroup.mul_mem_sup (S := oddIn M) (T := P) hodd hpp
    rw [sup_comm] at hmul
    have heq : M.subtype (m * pm⁻¹) * M.subtype pm = M.subtype m := by
      rw [← map_mul]
      congr 1
      group
    rwa [heq] at hmul
  obtain ⟨R₀⟩ := Sylow.nonempty (p := 2) (G := ↥P)
  let R : Subgroup G := (R₀ : Subgroup ↥P).map P.subtype
  have hR : IsSylowTwoIn R P :=
    ⟨Subgroup.map_subtype_le _, R₀,
      (Subgroup.comap_map_eq_self_of_injective P.subtype_injective R₀).symm⟩
  have hR2 : IsPGroup 2 R := hR.isPGroup
  have hRAW : R ≤ P := hR.1
  have htt : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [ht2] at h
    simpa [pow_two] using h
  have hRt : ∀ r ∈ R, r * t = t * r := fun r hr =>
    mem_centralizer_singleton_iff.mp (hPt (hRAW hr))
  have htc : t ∈ centralizer (R : Set G) :=
    Subgroup.mem_centralizer_iff.mpr (fun r hr => hRt r hr)
  have htNR : t ∈ normalizer (R : Set G) :=
    Subgroup.centralizer_le_normalizer (R : Set G) htc
  have hzt2 : IsPGroup 2 ↥(zpowers t) := (isElemTwo_zpowers htt).isPGroup
  let T : Subgroup G := R ⊔ zpowers t
  have hTM : T ≤ M := sup_le (hRAW.trans hPM) (zpowers_le.mpr htM)
  have hT2 : IsPGroup 2 T := hR2.to_sup_of_normal_left' hzt2 (zpowers_le.mpr htNR)
  let TM : Subgroup ↥M := T.subgroupOf M
  have hTM2 : IsPGroup 2 TM := hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTM).symm
  obtain ⟨S₁, hTMS₁⟩ := hTM2.exists_le_sylow
  let S : Subgroup G := (S₁ : Subgroup ↥M).map M.subtype
  have hS : IsSylowTwoIn S M :=
    ⟨Subgroup.map_subtype_le _, S₁,
      (Subgroup.comap_map_eq_self_of_injective M.subtype_injective S₁).symm⟩
  have hST : T ≤ S := by
    intro x hx
    exact Subgroup.mem_map.mpr ⟨⟨x, hTM hx⟩, hTMS₁ (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  have hRS : R ≤ S := (le_sup_left : R ≤ T).trans hST
  have hztS : t ∈ S := hST (mem_sup_right (mem_zpowers t))
  have hSM : S ≤ M := hS.1
  have hS2 : IsPGroup 2 S := hS.isPGroup
  have hB : ∀ E : Subgroup G, E ≤ S → IsElemTwo E → TwoBalancedWrt E :=
    hBal S hS hztS
  have hHcard : Nat.card H = Nat.card (pPrimeCore 2 ↥M) * Nat.card L := by
    have h1 := CFSG.GroupTheory.card_comap_eq_card_ker_mul_card (f := π)
      (QuotientGroup.mk'_surjective (pPrimeCore 2 ↥M)) L
    have hHcard' : Nat.card H = Nat.card ↥(L.comap π) := by
      show Nat.card ↥(HM.map M.subtype) = Nat.card ↥(L.comap π)
      rw [Subgroup.card_map_of_injective M.subtype_injective]
    rw [hHcard', h1]
    have hker : π.ker = pPrimeCore 2 ↥M := QuotientGroup.ker_mk' (pPrimeCore 2 ↥M)
    rw [hker]
  have hPcard : Nat.card P = Nat.card ↥(P ⊓ oddIn M) * Nat.card L := by
    let f : ↥P →* X := π.comp (Subgroup.inclusion hPM)
    have hfrange : f.range = L := by
      ext x
      constructor
      · rintro ⟨p, rfl⟩
        rw [← hPL]
        exact Subgroup.mem_map.mpr ⟨Subgroup.inclusion hPM p,
          Subgroup.mem_subgroupOf.mpr p.2, rfl⟩
      · intro hx
        rw [← hPL] at hx
        obtain ⟨pm, hpmsub, hpm⟩ := Subgroup.mem_map.mp hx
        refine ⟨⟨(pm : ↥M).1, Subgroup.mem_subgroupOf.mp hpmsub⟩, ?_⟩
        show π (Subgroup.inclusion hPM ⟨(pm : ↥M).1, Subgroup.mem_subgroupOf.mp hpmsub⟩) = x
        have hinc : Subgroup.inclusion hPM
            ⟨(pm : ↥M).1, Subgroup.mem_subgroupOf.mp hpmsub⟩ = pm := by
          apply Subtype.ext
          rfl
        rw [hinc]
        exact hpm
    have hker : f.ker = (oddIn M).subgroupOf P := by
      ext p
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, oddIn]
      constructor
      · intro hp
        have hmem : Subgroup.inclusion hPM p ∈ pPrimeCore 2 ↥M := by
          rw [← QuotientGroup.ker_mk' (pPrimeCore 2 ↥M), MonoidHom.mem_ker]
          exact hp
        exact Subgroup.mem_map.mpr ⟨Subgroup.inclusion hPM p, hmem, rfl⟩
      · intro hp
        obtain ⟨m, hm, hmp⟩ := Subgroup.mem_map.mp hp
        show (QuotientGroup.mk' (pPrimeCore 2 ↥M)) (Subgroup.inclusion hPM p) = 1
        have hincl : Subgroup.inclusion hPM p = m := by
          apply Subtype.ext
          exact hmp.symm
        rw [hincl]
        exact (QuotientGroup.eq_one_iff m).mpr hm
    calc Nat.card ↥P = Nat.card ↥f.ker * Nat.card ↥f.range :=
          (Subgroup.card_ker_mul_card_range f).symm
      _ = Nat.card ↥((oddIn M).subgroupOf P) * Nat.card ↥L := by rw [hker, hfrange]
      _ = Nat.card ↥(P ⊓ oddIn M) * Nat.card ↥L := by
          rw [← Subgroup.card_map_of_injective P.subtype_injective
            (K := (oddIn M).subgroupOf P), Subgroup.subgroupOf_map_subtype, inf_comm]
  have hOodd : Odd (Nat.card (pPrimeCore 2 ↥M)) :=
    Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := ↥M))
  have hRH : R ≤ H := hRAW.trans hPH
  have hRrelH : ¬ 2 ∣ R.relIndex H := by
    have hPrelOdd : Odd (P.relIndex H) := by
      have hmul := Subgroup.relIndex_mul_card (H := P) (K := H)
      rw [inf_of_le_left hPH] at hmul
      have hmul' : P.relIndex H * Nat.card ↥(P ⊓ oddIn M) = Nat.card (pPrimeCore 2 ↥M) := by
        apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥L))
        calc (P.relIndex H * Nat.card ↥(P ⊓ oddIn M)) * Nat.card L
            = P.relIndex H * (Nat.card ↥(P ⊓ oddIn M) * Nat.card L) := by ring
          _ = P.relIndex H * Nat.card P := by rw [hPcard]
          _ = Nat.card H := hmul
          _ = Nat.card (pPrimeCore 2 ↥M) * Nat.card L := hHcard
      exact Odd.of_dvd_nat hOodd ⟨_, hmul'.symm⟩
    have hRrelP : ¬ 2 ∣ R.relIndex P := by
      obtain ⟨-, Q, hQ⟩ := hR
      have hnot := Q.not_dvd_index
      rw [hQ] at hnot
      exact hnot
    rw [← Subgroup.relIndex_mul_relIndex R P H hRAW hPH]
    intro h2
    rcases (Nat.prime_two.dvd_mul).mp h2 with h | h
    · exact hRrelP h
    · exact hPrelOdd.not_two_dvd_nat h
  have hRHsyl : CFSG.ABGLocalTools.IsSylowOf 2 R H :=
    CFSG.ABGLocalTools.isSylowOf_iff.mpr ⟨hRH, hR2, hRrelH⟩
  have hSMsyl : CFSG.ABGLocalTools.IsSylowOf 2 S M := by
    obtain ⟨-, Q, hQ⟩ := hS
    exact ⟨Q, by rw [hQ, Subgroup.subgroupOf_map_subtype, inf_of_le_left hSM]⟩
  have hSHsyl : CFSG.ABGLocalTools.IsSylowOf 2 (S ⊓ H) H :=
    hSMsyl.inf_of_le_normalizer hHMle hMH
  have hRSH : R ≤ S ⊓ H := le_inf hRS hRH
  have hSH2 : IsPGroup 2 ↥(S ⊓ H) := hS2.to_le (inf_le_left : S ⊓ H ≤ S)
  have hSHeq : S ⊓ H = R :=
    CFSG.ABGLocalTools.IsSylowOf.eq_of_le hRHsyl hRSH inf_le_right hSH2
  have hSNH : S ≤ normalizer (H : Set G) := hSM.trans hMH
  have hSNR : S ≤ normalizer (R : Set G) := by
    intro s hs
    rw [← hSHeq, Subgroup.mem_normalizer_iff_map_conj_eq,
      Subgroup.map_inf _ _ _ (MulAut.conj s).injective,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (S.le_normalizer hs),
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hSNH hs)]
  let A₀ : Subgroup G := omSub (sqSub R)
  obtain ⟨hA₀e, hA₀card⟩ := omSub_sqSub_of_on hPON hR
  have hA₀R : A₀ ≤ R := omSub_sqSub_le R
  have hA₀P : A₀ ≤ P := hA₀R.trans hRAW
  have hA₀S : A₀ ≤ S := hA₀R.trans hRS
  have hA₀H : A₀ ≤ H := hA₀P.trans hPH
  have hA₀8 : 8 ≤ Nat.card A₀ := by
    change 8 ≤ Nat.card (omSub (sqSub R))
    exact le_of_eq hA₀card.symm
  have hSA₀ : S ≤ normalizer (A₀ : Set G) := fun s hs =>
    mem_normalizer_omSub_sqSub (hSNR hs)
  have hA₀C : A₀ ≤ centralizer ({t} : Set G) := hA₀P.trans hPt
  have hOddInOdd : Odd (Nat.card (oddIn M)) := by
    rw [oddIn, Subgroup.card_map_of_injective M.subtype_injective]
    exact hOodd
  have hA₀infOdd : A₀ ⊓ oddIn M = ⊥ := by
    refine Subgroup.inf_eq_bot_of_coprime ?_
    have h2 : Nat.Coprime 2 (Nat.card (oddIn M)) := Nat.coprime_two_left.mpr hOddInOdd
    have h8 : Nat.card A₀ = 2 ^ 3 := by rw [hA₀card]; norm_num
    rw [h8]
    exact h2.pow_left 3
  have hA₀K : A₀ ⊓ K = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxA : x ∈ A₀ := (mem_inf.mp hx).1
    have hxK : x ∈ K := (mem_inf.mp hx).2
    have hxH : x ∈ H := hA₀H hxA
    obtain ⟨m, hmH, rfl⟩ := Subgroup.mem_map.mp hxH
    have hmK : m ∈ KM := (Subgroup.mem_map_iff_mem M.subtype_injective).mp hxK
    have hπL : π m ∈ L := hmH
    have hπC : π m ∈ centralizer (L : Set X) := hmK
    have hZinf : L ⊓ centralizer (L : Set X) = ⊥ := by
      rw [CFSG.GroupTheory.inf_centralizer_eq_map_center L, hZ, Subgroup.map_bot]
    have hπbot : π m ∈ (⊥ : Subgroup X) := by
      rw [← hZinf]
      exact mem_inf.mpr ⟨hπL, hπC⟩
    have hπ1 : π m = 1 := Subgroup.mem_bot.mp hπbot
    have hmO : m ∈ pPrimeCore 2 ↥M := by
      have hker : (QuotientGroup.mk' (pPrimeCore 2 ↥M)).ker = pPrimeCore 2 ↥M :=
        QuotientGroup.ker_mk' (pPrimeCore 2 ↥M)
      rw [← hker, MonoidHom.mem_ker]
      exact hπ1
    have hxO : M.subtype m ∈ oddIn M := by
      rw [oddIn]
      exact Subgroup.mem_map.mpr ⟨m, hmO, rfl⟩
    have hxbot : M.subtype m ∈ (⊥ : Subgroup G) := by
      rw [← hA₀infOdd]
      exact mem_inf.mpr ⟨hxA, hxO⟩
    exact hxbot
  let B : Subgroup G := S ⊓ K
  have hBS : B ≤ S := inf_le_left
  have hBK : B ≤ K := inf_le_right
  have hSNK : S ≤ normalizer (K : Set G) := hSM.trans hMK
  have hSNB : S ≤ normalizer (B : Set G) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff_map_conj_eq,
      Subgroup.map_inf _ _ _ (MulAut.conj s).injective,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (S.le_normalizer hs),
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hSNK hs)]
  have hBN : (B.subgroupOf S).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hBS).mpr hSNB
  have hB2 : IsPGroup 2 B := hS2.to_le hBS
  have htK : t ∈ K := by
    refine Subgroup.mem_map.mpr ⟨⟨t, htM⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap]
    exact Subgroup.mem_centralizer_iff.mpr (fun x hx => (hcent x hx).symm)
  have htB : t ∈ B := mem_inf.mpr ⟨hztS, htK⟩
  have hBne : B ≠ ⊥ := by
    intro h
    rw [h] at htB
    have ht1 : t = 1 := Subgroup.mem_bot.mp htB
    have h2 := ht2
    rw [ht1, orderOf_one] at h2
    omega
  have hBNne : (B.subgroupOf S) ≠ ⊥ := by
    intro h
    apply hBne
    rw [← Subgroup.map_subgroupOf_eq_of_le hBS, h, Subgroup.map_bot]
  obtain ⟨x, hxne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (CFSG.GroupTheory.CoprimeActionSupport.NormalPSubgroupMeetsCenter.inf_center_ne_bot
      hS2 (B.subgroupOf S) hBNne)
  let z0 : ↥S := x.1
  have hz0B : (z0 : G) ∈ B := Subgroup.mem_subgroupOf.mp x.2.1
  have hz0c : (z0 : G) ∈ centralizer (S : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hc := Subgroup.mem_center_iff.mp x.2.2 ⟨s, hs⟩
    exact congrArg Subtype.val hc
  have hz0ne : (z0 : G) ≠ 1 := by
    intro h
    apply hxne
    apply Subtype.ext
    apply Subtype.ext
    exact h
  let D : Subgroup G := zpowers (z0 : G)
  have hDleB : D ≤ B := zpowers_le.mpr hz0B
  have hDleS : D ≤ S := hDleB.trans hBS
  have hD2 : IsPGroup 2 D := hS2.to_le hDleS
  have hDne : D ≠ ⊥ := by
    intro h
    have h1 : (z0 : G) ∈ (⊥ : Subgroup G) := h ▸ mem_zpowers (z0 : G)
    exact hz0ne (Subgroup.mem_bot.mp h1)
  have hDnt : Nontrivial ↥D := (Subgroup.nontrivial_iff_ne_bot D).mpr hDne
  obtain ⟨k, hkpos, hkcard⟩ := hD2.nontrivial_iff_card.mp hDnt
  have h2dvd : 2 ∣ Nat.card ↥D := by
    rw [hkcard]
    exact dvd_pow_self 2 (Nat.ne_of_gt hkpos)
  obtain ⟨zD, hzDord⟩ := exists_prime_orderOf_dvd_card' (G := ↥D) 2 h2dvd
  let z : G := (zD : G)
  have hzord : orderOf z = 2 := by
    show orderOf (zD : G) = 2
    rw [Subgroup.orderOf_coe, hzDord]
  have hz2 : z * z = 1 := by
    rw [← pow_two]
    have h := pow_orderOf_eq_one z
    rwa [hzord] at h
  have hzS : z ∈ S := hDleS zD.2
  have hzB : z ∈ B := hDleB zD.2
  have hzK : z ∈ K := hBK hzB
  have hzcent : z ∈ centralizer (S : Set G) := (zpowers_le.mpr hz0c) zD.2
  have hzc : ∀ y ∈ S, z * y = y * z := by
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp hzcent y hy).symm
  have hzA₀ : z ∉ A₀ := by
    intro hz
    have hmem : z ∈ A₀ ⊓ K := mem_inf.mpr ⟨hz, hzK⟩
    rw [hA₀K] at hmem
    have hz1 : z = 1 := Subgroup.mem_bot.mp hmem
    have h2 := hzord
    rw [hz1, orderOf_one] at h2
    omega
  let A₁ : Subgroup G := A₀ ⊔ zpowers z
  have hzcA₀ : z ∈ centralizer (A₀ : Set G) :=
    Subgroup.mem_centralizer_iff.mpr (fun a ha =>
      Subgroup.mem_centralizer_iff.mp hzcent a (hA₀S ha))
  have hzpowC : zpowers z ≤ centralizer (A₀ : Set G) := zpowers_le.mpr hzcA₀
  have hA₁e : IsElemTwo A₁ :=
    hA₀e.sup (isElemTwo_zpowers hz2)
      (fun a ha b hb => Subgroup.mem_centralizer_iff.mp (hzpowC hb) a ha)
  have hinter : A₀ ⊓ zpowers z = ⊥ := by
    have hle : A₀ ⊓ zpowers z ≤ zpowers z := inf_le_right
    have hdvd : Nat.card ↥(A₀ ⊓ zpowers z) ∣ Nat.card ↥(zpowers z) :=
      Subgroup.card_dvd_of_le hle
    have hzpowcard : Nat.card ↥(zpowers z) = 2 := by rw [Nat.card_zpowers, hzord]
    have hne : Nat.card ↥(A₀ ⊓ zpowers z) ≠ 2 := by
      intro h2
      have heq : A₀ ⊓ zpowers z = zpowers z := by
        apply Subgroup.eq_of_le_of_card_ge hle
        rw [h2, hzpowcard]
      have hzint : z ∈ A₀ ⊓ zpowers z := by
        rw [heq]
        exact mem_zpowers z
      exact hzA₀ (mem_inf.mp hzint).1
    have hdvd2 : Nat.card ↥(A₀ ⊓ zpowers z) ∣ 2 := by rwa [hzpowcard] at hdvd
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h1 | h2
    · exact Subgroup.card_eq_one.mp h1
    · exact absurd h2 hne
  have hA₁card : Nat.card A₁ = 8 * 2 := by
    have h := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer A₀
      (zpowers z) (hzpowC.trans (Subgroup.centralizer_le_normalizer (A₀ : Set G)))
      (disjoint_iff.mpr hinter)
    rw [h, hA₀card, Nat.card_zpowers, hzord]
  have hA₁16 : 16 ≤ Nat.card A₁ := by norm_num [hA₁card]
  have hA₁C : A₁ ≤ centralizer ({t} : Set G) := by
    refine sup_le hA₀C (zpowers_le.mpr ?_)
    exact mem_centralizer_singleton_iff.mpr (hzc t hztS)
  have h3 : IsThreeConnected S :=
    isThreeConnected_of_normal_eight hS2 hA₀S hSA₀ hA₀e hA₀card hzS hzc hz2 hzA₀
  have hSylA₁ : IsSylowTwoIn S (normalizer (wGroup A₁)) := by
    rw [hWGroupEq A₁ hA₁C hA₁e (by omega), ← hM]
    exact hS
  obtain ⟨hSylG, -⟩ :=
    sylow_and_fusion_of_threeConnected_in hB hA₁e hA₁16 hSylA₁ h3
  have hSinfOdd : S ⊓ oddIn M = ⊥ := by
    refine Subgroup.inf_eq_bot_of_coprime ?_
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2) (G := ↥S)).mp hS2
    rw [hk]
    exact (Nat.coprime_two_left.mpr hOddInOdd).pow_left k
  have hHK : ⁅H, K⁆ ≤ oddIn M := by
    rw [Subgroup.commutator_le]
    intro h hh k hk
    obtain ⟨m, hmH, rfl⟩ := Subgroup.mem_map.mp hh
    obtain ⟨n, hmK, rfl⟩ := Subgroup.mem_map.mp hk
    have hπh : π m ∈ L := hmH
    have hπk : π n ∈ centralizer (L : Set X) := hmK
    have hcommπ : π ⁅m, n⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_def]
      have hc : π m * π n = π n * π m :=
        Subgroup.mem_centralizer_iff.mp hπk (π m) hπh
      rw [hc]
      group
    have hmO : ⁅m, n⁆ ∈ pPrimeCore 2 ↥M := by
      have hker : (QuotientGroup.mk' (pPrimeCore 2 ↥M)).ker = pPrimeCore 2 ↥M :=
        QuotientGroup.ker_mk' (pPrimeCore 2 ↥M)
      rw [← hker, MonoidHom.mem_ker]
      exact hcommπ
    rw [← map_commutatorElement (f := M.subtype)]
    exact Subgroup.mem_map.mpr ⟨⁅m, n⁆, hmO, rfl⟩
  have hKA : ∀ b ∈ S ⊓ K, ∀ e ∈ A₀, b * e = e * b := by
    intro b hb e he
    have hbS : b ∈ S := (mem_inf.mp hb).1
    have hbK : b ∈ K := (mem_inf.mp hb).2
    have hcomm_mem : ⁅b, e⁆ ∈ S ⊓ oddIn M := by
      refine mem_inf.mpr ⟨?_, ?_⟩
      · rw [commutatorElement_def]
        exact S.mul_mem (S.mul_mem (S.mul_mem hbS (hA₀S he)) (S.inv_mem hbS))
          (S.inv_mem (hA₀S he))
      · have hmem : ⁅e, b⁆ ∈ ⁅H, K⁆ :=
          Subgroup.commutator_mem_commutator (hPH (hA₀P he)) hbK
        have hinv : ⁅b, e⁆ = ⁅e, b⁆⁻¹ := by
          rw [commutatorElement_def, commutatorElement_def]
          group
        rw [hinv]
        exact hHK ((⁅H, K⁆).inv_mem hmem)
    have h1 : ⁅b, e⁆ = 1 := by
      rw [hSinfOdd] at hcomm_mem
      exact Subgroup.mem_bot.mp hcomm_mem
    rw [commutatorElement_def] at h1
    have hbe : b * e * b⁻¹ = e := by
      calc b * e * b⁻¹ = b * e * b⁻¹ * e⁻¹ * e := by group
        _ = 1 * e := by rw [h1]
        _ = e := by group
    calc b * e = (b * e * b⁻¹) * b := by group
      _ = e * b := by rw [hbe]
  have hMK' : normalizer (wGroup A₁) ≤ normalizer (K : Set G) := by
    rw [hWGroupEq A₁ hA₁C hA₁e (by omega), ← hM]
    exact hMK
  have hcl : ∀ x ∈ S ⊓ K, ∀ g : G, g⁻¹ * x * g ∈ S → g⁻¹ * x * g ∈ S ⊓ K :=
    conj_mem_inf_of_threeConnected_in hB hA₁e hA₁16 hSylA₁ h3
      hA₀S hSA₀ hA₀e hA₀8 hMK' hKA hA₀K
  have hPperf : ⁅P, P⁆ = P := by
    have : Group.IsPerfect ↥P := hPperf
    exact Subgroup.commutator_eq_self
  have hPeven : Even (Nat.card P) := by
    rw [even_iff_two_dvd]
    have h8dvd : 8 ∣ Nat.card P := by
      have h := Subgroup.card_dvd_of_le hA₀P
      rwa [show Nat.card A₀ = 8 from hA₀card] at h
    exact (show 2 ∣ 8 by norm_num).trans h8dvd
  have hKodd : K ≤ oddIn M :=
    le_oddIn_of_stronglyClosed_inf hGold hsimple hnonab hSylG hSM hHMle hKMle
      hMH hMK hOH hHK hPH hPperf hPeven hcl
  have htOdd : t ∈ oddIn M := hKodd htK
  have h2dvdOdd : 2 ∣ Nat.card (oddIn M) := by
    rw [← ht2]
    exact Subgroup.orderOf_dvd_natCard (oddIn M) htOdd
  exact hOddInOdd.not_two_dvd_nat h2dvdOdd

theorem false_of_onan_normal_component (hGold : GoldschmidtStronglyClosedInput)
    {G : Type} [Group G] [Finite G] {t : G} {P W M : Subgroup G} (hc : ONanWConfig G t P W)
    (hM : M = normalizer (W : Set G)) (htM : t ∈ M)
    {L : Subgroup (↥M ⧸ pPrimeCore 2 ↥M)} (_hL : IsComponent L) (hLn : L.Normal)
    (hZ : center ↥L = ⊥) (_hLON : IsSporadic ↥L .ONan)
    (hPL : (P.subgroupOf M).map (QuotientGroup.mk' (pPrimeCore 2 ↥M)) = L)
    (hcent : ∀ x ∈ L, QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨t, htM⟩ * x =
      x * QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨t, htM⟩) : False := by
  classical
  exact false_of_onan_normal_component_core hGold hM htM hc.base.1 hc.base.2.1 hc.order_two
    (by simpa [← hM] using hc.le_normalizer') hc.le_centralizer
    hc.isSporadic_pPrimeCore hc.isPerfect hc.wGroup_eq
    (fun _ _ _ _ _ hE => twoBalancedWrt_of_gwTwoBalanced hc.gwTwoBalanced hE)
    hLn hZ hPL hcent

end CFSG.ComponentClassification.GrSLit.L34Sec5S
