module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuB1Uniq
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuCentA

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard CFSG.BenderSuzuki.PFAppendixIII

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_of_odd_of_le_sup_of_isPGroup {P W Y : Subgroup G} (hP : IsPGroup 2 P)
    (hPW : P ≤ normalizer (W : Set G)) (hY : Odd (Nat.card Y)) (hYle : Y ≤ P ⊔ W) : Y ≤ W := by
  intro y hy
  obtain ⟨p, hp, w, hw, rfl⟩ := CFSG.Goldschmidt.G37.mem_sup_of_le_normalizer hPW (hYle hy)
  obtain ⟨k, hk⟩ := hP ⟨p, hp⟩
  have hpk : p ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hpow : ∀ n : ℕ, ∃ w' ∈ W, (p * w) ^ n = p ^ n * w' := by
    intro n
    induction n with
    | zero => exact ⟨1, one_mem _, by simp⟩
    | succ n ih =>
      obtain ⟨w', hw', he⟩ := ih
      refine ⟨p⁻¹ * w' * p * w, mul_mem ?_ hw, ?_⟩
      · simpa using (mem_normalizer_iff.mp (hPW (inv_mem hp)) w').mp hw'
      · rw [pow_succ, he, pow_succ]
        group
  obtain ⟨w', hw', he⟩ := hpow (2 ^ k)
  rw [hpk, one_mul] at he
  have hodd : Odd (orderOf (p * w)) := hY.of_dvd_nat (Subgroup.orderOf_dvd_natCard Y hy)
  have hcop : Nat.Coprime (2 ^ k) (orderOf (p * w)) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
  have h := Nat.gcd_eq_gcd_ab (2 ^ k) (orderOf (p * w))
  rw [hcop.gcd_eq_one, Nat.cast_one] at h
  have e : p * w = ((p * w) ^ 2 ^ k) ^ (Nat.gcdA (2 ^ k) (orderOf (p * w))) *
      ((p * w) ^ orderOf (p * w)) ^ (Nat.gcdB (2 ^ k) (orderOf (p * w))) := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, ← h, zpow_one]
  rw [e, pow_orderOf_eq_one, one_zpow, mul_one, he]
  exact zpow_mem hw' _

omit [Finite G] in
theorem conj_mem_centralizer_of_mem_normalizer_b1 {Q : Subgroup G} {n c : G}
    (hn : n ∈ normalizer (Q : Set G)) (hc : c ∈ centralizer (Q : Set G)) :
    n * c * n⁻¹ ∈ centralizer (Q : Set G) := by
  rw [mem_centralizer_iff]
  intro x hx
  have hx' : n⁻¹ * x * n ∈ Q := by
    simpa using (mem_normalizer_iff.mp (inv_mem hn) x).mp hx
  have h1 := mem_centralizer_iff.mp hc _ hx'
  calc x * (n * c * n⁻¹) = n * ((n⁻¹ * x * n) * c) * n⁻¹ := by group
    _ = n * (c * (n⁻¹ * x * n)) * n⁻¹ := by rw [h1]
    _ = n * c * n⁻¹ * x := by group

namespace Sec3.SzR

variable {L T R R₂ : Subgroup G} {y d : G}

theorem exists_odd_le_normalizer_centralizer_gmsA
    (hS : SzR G L T R 1 y d)
    (h34 : NoStronglyClosedAbelian G) (hR₂ : IsR₂ L T R R₂ d)
    (h4 : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4) :
    ∃ D : Subgroup G, Odd (Nat.card D) ∧
      centralizer (gmsA L T : Set G) ≤ normalizer (D : Set G) ∧
      centralizer (gmsA L T : Set G) ≤ D ⊔ R := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer (gmsA L T : Set G) with hCdef
  have hRC : R ≤ C := fun r hr =>
    mem_centralizer_iff.mpr fun b hb => (hS.commute_gmsA hr hb).symm
  have hAR : gmsA L T ≤ R := gmsA_le_T.trans hS.T_le
  have hcomm : ∀ g ∈ normalizer (R : Set G), g ∈ C → ∀ x ∈ R,
      g * x * g⁻¹ * x⁻¹ ∈ gmsA L T := fun g hgN hgC x hx =>
    hS.conj_mul_inv_mem_gmsA_of_commute h34 hR₂ h4 hgN
      (fun b hb => (mem_centralizer_iff.mp hgC b hb).symm) hx
  have hDV : ∀ g ∈ normalizer (R : Set G), g ∈ C → g ∈ normalizer (gmsV L T : Set G) := by
    intro g hgN hgC
    refine mem_normalizer_of_conj_mem_of_finite fun s hs => ?_
    have e1 : g * s * g⁻¹ = (g * s * g⁻¹ * s⁻¹) * s := by group
    rw [e1]
    exact mul_mem (mem_sup_left (hcomm g hgN hgC s (hS.gmsV_le_R hs))) hs
  set R' : Subgroup C := R.subgroupOf C with hR'
  set A' : Subgroup C := (gmsA L T).subgroupOf C with hA'
  have hA'R' : A' ≤ R' := fun x hx => hAR hx
  have hA'cent : ∀ a ∈ A', ∀ c : C, c * a = a * c := fun a ha c =>
    Subtype.ext (mem_centralizer_iff.mp c.2 a ha).symm
  have : A'.Normal := ⟨fun a ha c => by
    have h1 : c * a * c⁻¹ = a := by rw [hA'cent a ha c]; group
    rw [h1]
    exact ha⟩
  have hR'2 : IsPGroup 2 R' := hS.isR.isPGroup.comap_subtype
  have hR'idx : ¬ 2 ∣ R'.index := by
    intro hdvd
    have hnS : ¬ IsSylowOf 2 R' ⊤ := fun h =>
      (isSylowOf_iff.mp h).2.2 (by rwa [relIndex_top_right])
    obtain ⟨P, hRP, z, hzP, hzN, hzR⟩ := exists_mem_normalizer_of_not_isSylowOf hR'2 hnS
    have hzN' : (z : G) ∈ normalizer (R : Set G) :=
      mem_normalizer_of_conj_mem_of_finite fun x hx =>
        (mem_normalizer_iff.mp hzN ⟨x, hRC hx⟩).mp hx
    have hPm : IsPGroup 2 ((P : Subgroup C).map C.subtype) := P.isPGroup'.map C.subtype
    have hQP : R ⊔ zpowers (z : G) ≤ (P : Subgroup C).map C.subtype := by
      refine sup_le (fun x hx => ⟨⟨x, hRC hx⟩, hRP (show (⟨x, hRC hx⟩ : C) ∈ R' from hx),
        rfl⟩) ?_
      rw [zpowers_le]
      exact ⟨z, hzP, rfl⟩
    have hQV : R ⊔ zpowers (z : G) ≤ normalizer (gmsV L T : Set G) :=
      sup_le hS.isR.le_normalizer_gmsV (zpowers_le.mpr (hDV _ hzN' z.2))
    have heq := hS.isSylowOf_normalizer.eq_of_le le_sup_left hQV (hPm.to_le hQP)
    apply hzR
    have hz : (z : G) ∈ R ⊔ zpowers (z : G) := mem_sup_right (mem_zpowers _)
    rw [heq] at hz
    exact hz
  set PR : Sylow 2 C := hR'2.toSylow hR'idx with hPR
  have hPRc : (PR : Subgroup C) = R' := IsPGroup.toSylow_coe hR'2 hR'idx
  set π := QuotientGroup.mk' A' with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective A'
  set S : Sylow 2 (C ⧸ A') := PR.mapSurjective hπs with hSdef
  have hSc : (S : Subgroup (C ⧸ A')) = R'.map π := by
    rw [hSdef, Sylow.coe_mapSurjective, hPRc]
  have hNS : normalizer (S : Set (C ⧸ A')) ≤ centralizer (S : Set (C ⧸ A')) := by
    intro q hq
    obtain ⟨c, rfl⟩ := hπs q
    have hcN : (c : G) ∈ normalizer (R : Set G) := by
      refine mem_normalizer_of_conj_mem_of_finite fun x hx => ?_
      have hxC := hRC hx
      have h1 : π (c * ⟨x, hxC⟩ * c⁻¹) ∈ (S : Subgroup (C ⧸ A')) := by
        rw [map_mul, map_mul, map_inv]
        refine (mem_normalizer_iff.mp hq _).mp ?_
        rw [hSc]
        exact ⟨⟨x, hxC⟩, hx, rfl⟩
      rw [hSc] at h1
      obtain ⟨r, hr, hrπ⟩ := h1
      have h2 : r⁻¹ * (c * ⟨x, hxC⟩ * c⁻¹) ∈ A' := QuotientGroup.eq.mp hrπ
      have h3 : c * ⟨x, hxC⟩ * c⁻¹ ∈ R' := by
        have e1 : c * ⟨x, hxC⟩ * c⁻¹ = r * (r⁻¹ * (c * ⟨x, hxC⟩ * c⁻¹)) := by group
        rw [e1]
        exact mul_mem hr (hA'R' h2)
      exact h3
    rw [mem_centralizer_iff]
    intro s hs
    have hs' : s ∈ (S : Subgroup (C ⧸ A')) := hs
    rw [hSc] at hs'
    obtain ⟨r, hr, rfl⟩ := hs'
    rw [← map_mul, ← map_mul]
    refine QuotientGroup.eq.mpr ?_
    have hrR : (r : G) ∈ R := hr
    have h1 := hcomm (c : G)⁻¹ (inv_mem hcN) (inv_mem c.2) (r : G)⁻¹ (inv_mem hrR)
    have e1 : (((r * c)⁻¹ * (c * r) : C) : G) =
        (c : G)⁻¹ * (r : G)⁻¹ * (c : G)⁻¹⁻¹ * (r : G)⁻¹⁻¹ := by
      simp only [coe_mul, coe_inv]
      group
    show (((r * c)⁻¹ * (c * r) : C) : G) ∈ gmsA L T
    rw [e1]
    exact h1
  obtain ⟨K, hKn, hK2, -, -, -, hKc, -, -, -, -⟩ :=
    CFSG.GroupTheory.burnside_normal_complement S hNS
  set Kt := K.comap π with hKt
  have : Kt.Normal := hKn.comap π
  set φ : Kt →* K := (π.comp Kt.subtype).codRestrict K fun x => x.2 with hφ
  have hφker : φ.ker = A'.subgroupOf Kt := by
    ext x
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    constructor
    · intro h
      have h1 : π (x : C) = 1 := congrArg Subtype.val h
      exact (QuotientGroup.eq_one_iff _).mp h1
    · intro h
      exact Subtype.ext ((QuotientGroup.eq_one_iff _).mpr h)
  have hφs : Function.Surjective φ := by
    rintro ⟨k, hk⟩
    obtain ⟨c, rfl⟩ := hπs k
    exact ⟨⟨c, hk⟩, rfl⟩
  have hA''idx : (A'.subgroupOf Kt).index = Nat.card K := by
    rw [← hφker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hφs, card_top]
  have hA''2 : IsPGroup 2 (A'.subgroupOf Kt) :=
    (hS.isR.isPGroup.to_le hAR).comap_subtype.comap_subtype
  have hA''nd : ¬ 2 ∣ (A'.subgroupOf Kt).index := by rw [hA''idx]; exact hK2
  set PA : Sylow 2 Kt := hA''2.toSylow hA''nd with hPA
  have hPAc : (PA : Subgroup Kt) = A'.subgroupOf Kt := IsPGroup.toSylow_coe hA''2 hA''nd
  have hNA : normalizer (PA : Set Kt) ≤ centralizer (PA : Set Kt) := by
    intro k _
    rw [mem_centralizer_iff]
    intro a ha
    have ha' : a ∈ (PA : Subgroup Kt) := ha
    rw [hPAc] at ha'
    exact Subtype.ext (hA'cent (a : C) ha' (k : C)).symm
  obtain ⟨D, -, hD2, -, -, hDchar, hDc, -, -, -, -⟩ :=
    CFSG.GroupTheory.burnside_normal_complement PA hNA
  have := hDchar
  set D' := D.map Kt.subtype with hD'
  refine ⟨D'.map C.subtype, ?_, ?_, ?_⟩
  · rw [card_map_of_injective C.subtype_injective, hD',
      card_map_of_injective Kt.subtype_injective]
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hD2)
  ·
    intro c hc
    refine mem_normalizer_of_conj_mem_of_finite fun x hx => ?_
    obtain ⟨x', hx', rfl⟩ := hx
    have h1 : (⟨c, hc⟩ : C) * x' * (⟨c, hc⟩ : C)⁻¹ ∈ D' :=
      (inferInstance : D'.Normal).conj_mem x' hx' _
    exact ⟨_, h1, rfl⟩
  ·
    intro c hc
    obtain ⟨⟨⟨k, hk⟩, ⟨s, hs⟩⟩, hks⟩ := hKc.2 (π ⟨c, hc⟩)
    have hks' : k * s = π ⟨c, hc⟩ := hks
    have hs' : s ∈ (S : Subgroup (C ⧸ A')) := hs
    rw [hSc] at hs'
    obtain ⟨r, hr, rfl⟩ := hs'
    have hkt : (⟨c, hc⟩ : C) * r⁻¹ ∈ Kt := by
      show π ((⟨c, hc⟩ : C) * r⁻¹) ∈ K
      rw [map_mul, map_inv, ← hks', mul_inv_cancel_right]
      exact hk
    obtain ⟨⟨⟨δ, hδ⟩, ⟨α, hα⟩⟩, hδα⟩ := hDc.2 ⟨_, hkt⟩
    have hδα' : δ * α = ⟨_, hkt⟩ := hδα
    have hαA : ((α : C) : G) ∈ gmsA L T := by
      have h1 : α ∈ (PA : Subgroup Kt) := hα
      rw [hPAc] at h1
      exact h1
    have hδD : ((δ : C) : G) ∈ D'.map C.subtype := ⟨(δ : C), ⟨δ, hδ, rfl⟩, rfl⟩
    have h1 : ((δ : C) : G) * ((α : C) : G) = c * (r : G)⁻¹ := by
      have := congrArg (fun z : Kt => ((z : C) : G)) hδα'
      simpa using this
    have e1 : c = ((δ : C) : G) * (((α : C) : G) * (r : G)) := by
      rw [← mul_assoc, h1, inv_mul_cancel_right]
    rw [e1]
    exact mul_mem (mem_sup_left hδD) (mem_sup_right (mul_mem (hAR hαA) hr))

end Sec3.SzR

namespace SzMinCounter

variable {L T R R₂ : Subgroup G} {y d : G}

theorem centralizer_gmsA_eq_sup
    (hM : SzMinCounter G L 1) (hS : Sec3.SzR G L T R 1 y d)
    (h34 : NoStronglyClosedAbelian G) (hR₂ : Sec3.IsR₂ L T R R₂ d)
    (h4 : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4) :
    centralizer (gmsA L T : Set G) = R ⊔ AS76b.oddCoreIn (centralizer (L : Set G)) := by
  obtain ⟨D, hDodd, hCD, hCDR⟩ := hS.exists_odd_le_normalizer_centralizer_gmsA h34 hR₂ h4
  have hRC : R ≤ centralizer (gmsA L T : Set G) := fun r hr =>
    mem_centralizer_iff.mpr fun b hb => (hS.commute_gmsA hr hb).symm
  have hAL : gmsA L T ≤ L := inf_le_left.trans inf_le_right
  have hWC : AS76b.oddCoreIn (centralizer (L : Set G)) ≤ centralizer (gmsA L T : Set G) :=
    (AS76b.oddCoreIn_le _).trans (centralizer_le hAL)
  have hDW : D ≤ AS76b.oddCoreIn (centralizer (L : Set G)) :=
    hM.le_oddCoreIn_of_le_normalizer_gmsV hS.sec3 hS.foundation hS.oddCenter h4 hDodd
      ((hS.gmsV_le_R.trans hRC).trans hCD)
  exact le_antisymm (hCDR.trans (sup_le (le_sup_of_le_right hDW) le_sup_left))
    (sup_le hRC hWC)

theorem le_normalizer_oddCoreIn_of_szR
    (hM : SzMinCounter G L 1) (hS : Sec3.SzR G L T R 1 y d)
    (h4 : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4) :
    R ≤ normalizer (AS76b.oddCoreIn (centralizer (L : Set G)) : Set G) :=
  hS.isR.le_normalizer_gmsV.trans
    (hM.normalizer_gmsV_le hS.sec3 hS.foundation hS.oddCenter h4)

theorem le_oddCoreIn_of_le_centralizer_gmsA
    (hM : SzMinCounter G L 1)
    (hS : Sec3.SzR G L T R 1 y d) (h34 : NoStronglyClosedAbelian G)
    (hR₂ : Sec3.IsR₂ L T R R₂ d)
    (h4 : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4) {Y : Subgroup G}
    (hY : Odd (Nat.card Y)) (hYC : Y ≤ centralizer (gmsA L T : Set G)) :
    Y ≤ AS76b.oddCoreIn (centralizer (L : Set G)) :=
  le_of_odd_of_le_sup_of_isPGroup hS.isR.isPGroup (hM.le_normalizer_oddCoreIn_of_szR hS h4) hY
    (hYC.trans (hM.centralizer_gmsA_eq_sup hS h34 hR₂ h4).le)

theorem normalizer_le_normalizer_oddCoreIn_of_gmsA_le
    (hM : SzMinCounter G L 1)
    (hS : Sec3.SzR G L T R 1 y d) (h34 : NoStronglyClosedAbelian G)
    (hR₂ : Sec3.IsR₂ L T R R₂ d)
    (h4 : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4) {Q : Subgroup G}
    (hAQ : gmsA L T ≤ Q)
    (hQW : Q ≤ centralizer (AS76b.oddCoreIn (centralizer (L : Set G)) : Set G)) :
    normalizer (Q : Set G) ≤ normalizer (AS76b.oddCoreIn (centralizer (L : Set G)) : Set G) := by
  have hWQ := le_centralizer_iff.mp hQW
  intro n hn
  refine AS76b.mem_normalizer_of_map_conj_le
    (hM.le_oddCoreIn_of_le_centralizer_gmsA hS h34 hR₂ h4 ?_ ?_)
  · rw [card_map_of_injective (MulAut.conj n).injective]
    exact AS76b.odd_card_oddCoreIn _
  · rintro _ ⟨w, hw, rfl⟩
    exact centralizer_le hAQ (conj_mem_centralizer_of_mem_normalizer_b1 hn (hWQ hw))

theorem centralizer_eq_sup_of_gmsA_le
    (hM : SzMinCounter G L 1) (hS : Sec3.SzR G L T R 1 y d)
    (h34 : NoStronglyClosedAbelian G) (hR₂ : Sec3.IsR₂ L T R R₂ d)
    (h4 : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4) {Q : Subgroup G}
    (hAQ : gmsA L T ≤ Q)
    (hQW : Q ≤ centralizer (AS76b.oddCoreIn (centralizer (L : Set G)) : Set G)) :
    centralizer (Q : Set G) =
      (R ⊓ centralizer (Q : Set G)) ⊔ AS76b.oddCoreIn (centralizer (L : Set G)) := by
  set W := AS76b.oddCoreIn (centralizer (L : Set G)) with hW
  have hWQ : W ≤ centralizer (Q : Set G) := le_centralizer_iff.mp hQW
  refine le_antisymm (fun c hc => ?_) (sup_le inf_le_right hWQ)
  have hcA : c ∈ R ⊔ W := by
    rw [← hM.centralizer_gmsA_eq_sup hS h34 hR₂ h4]
    exact centralizer_le hAQ hc
  obtain ⟨r, hr, w, hw, rfl⟩ :=
    CFSG.Goldschmidt.G37.mem_sup_of_le_normalizer (hM.le_normalizer_oddCoreIn_of_szR hS h4) hcA
  have hrQ : r ∈ centralizer (Q : Set G) := by
    have e1 : r = (r * w) * w⁻¹ := by group
    rw [e1]
    exact mul_mem hc (inv_mem (hWQ hw))
  exact mul_mem (mem_sup_left (mem_inf.mpr ⟨hr, hrQ⟩)) (mem_sup_right hw)

end SzMinCounter

end CFSG.ComponentClassification.GMS78
