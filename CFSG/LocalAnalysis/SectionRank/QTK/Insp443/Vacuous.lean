module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.Config
public import CFSG.Quasithin.Vol2.Ch4Sec4F4411A
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.SectionRank.QTK.Insp443

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13.Ch4 CFSG.Quasithin.H13.Ch4.E443
  CFSG.QuasithinUnique
open scoped commutatorElement

@[expose] def TwoLocalsSolvable (S : Type) [Group S] : Prop :=
  ∀ Q : Subgroup S, Q ≠ ⊥ → IsPGroup 2 Q →
    Group.IsSolvable (Subgroup.normalizer (Q : Set S))

namespace Hyp

variable {G : Type} [Group G] [Finite G] {T M L B Tp VB K : Subgroup G}

theorem eight_le_card_VB (h : Hyp G T M L B Tp VB K) : 8 ≤ Nat.card VB := by
  by_contra h8
  push Not at h8
  have hP : IsPGroup 2 VB := IsElemAbelian.isPGroup (⟨VB_comm h, VB_sq h⟩ : IsElemAbelian 2 VB)
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP
  have hn2 : n ≤ 2 := by
    have h2n : 2 ^ n < 8 := by rwa [hn] at h8
    have h2n' : 2 ^ n < 2 ^ 3 := by simpa using h2n
    have hn3 : n < 3 :=
      (Nat.pow_lt_pow_iff_right (by norm_num : 1 < (2 : ℕ))).mp h2n'
    omega
  have hidx : ((⊥ : Subgroup G).subgroupOf VB).index ≤ 4 := by
    rw [Subgroup.bot_subgroupOf VB, Subgroup.index_bot, hn]
    calc 2 ^ n ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) hn2
      _ = 4 := by norm_num
  have hbotN : ∀ H : Subgroup G, H ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) :=
    fun H _ _ => by
      rw [Subgroup.normalizer_eq_top (⊥ : Subgroup G)]
      exact Subgroup.mem_top _
  have hmem := commutator_mem_of_perfect_of_index_le_four
    (L := perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G)))
    (V := VB) (W := ⊥) (LB_perfect h) (LB_le_normalizer_VB h) (hbotN _) (hbotN _) hidx
  have hcommLV : ⁅perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G)), VB⁆ = ⊥ := by
    rw [eq_bot_iff]
    exact Subgroup.commutator_le.mpr fun l hl v hv => by
      simpa [commutatorElement_def] using hmem l hl v hv
  have hcomm : ⁅VB, perfectCore (conjClosure L T ⊓
      Subgroup.centralizer (B : Set G))⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact hcommLV
  have hVB : VB = ⊥ := by rw [VB_eq_commutator h, hcomm]
  exact h.setting.hyp.VB_ne_bot hVB

private theorem subgroupOf_inf_center_eq_bot (h : Hyp G T M L B Tp VB K) :
    VB.subgroupOf K ⊓ Subgroup.center ↥K = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxV, hxZ⟩ := hx
  have hx2 : x ^ 2 = 1 := by
    apply Subtype.ext
    have h2 := VB_sq h (x : G) hxV
    simpa using h2
  have h1 : orderOf x = 1 :=
    Nat.eq_one_of_dvd_coprimes (Nat.coprime_two_left.mpr (odd_card_center h))
      (orderOf_dvd_of_pow_eq_one hx2)
      (Subgroup.orderOf_dvd_natCard (Subgroup.center ↥K) hxZ)
  exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp h1)

private theorem isElemAbelian_image (h : Hyp G T M L B Tp VB K) :
    IsElemAbelian 2 ((VB.subgroupOf K).map
      (QuotientGroup.mk' (Subgroup.center ↥K))) :=
  ((show IsElemAbelian 2 VB from ⟨VB_comm h, VB_sq h⟩).subgroupOf K).map _

private theorem eight_le_card_image (h : Hyp G T M L B Tp VB K) :
    8 ≤ Nat.card ((VB.subgroupOf K).map
      (QuotientGroup.mk' (Subgroup.center ↥K))) := by
  classical
  let Z : Subgroup ↥K := Subgroup.center ↥K
  let π : ↥K →* (↥K ⧸ Z) := QuotientGroup.mk' Z
  let φ : ↥VB →* (↥K ⧸ Z) := π.comp (Subgroup.inclusion h.VB_le)
  have hdisj : VB.subgroupOf K ⊓ Z = ⊥ := by
    simpa [Z] using subgroupOf_inf_center_eq_bot h
  have hφinj : Function.Injective φ := by
    intro x y hxy
    have h1 : φ (x * y⁻¹) = 1 := by
      rw [map_mul, map_inv, hxy, mul_inv_cancel]
    have hxV : Subgroup.inclusion h.VB_le (x * y⁻¹) ∈ VB.subgroupOf K := by
      rw [Subgroup.mem_subgroupOf, Subgroup.coe_inclusion]
      exact VB.mul_mem x.2 (VB.inv_mem y.2)
    have hxZ : Subgroup.inclusion h.VB_le (x * y⁻¹) ∈ Z := by
      apply (QuotientGroup.eq_one_iff (N := Z) _).mp
      simpa [φ, π] using h1
    have hbot : Subgroup.inclusion h.VB_le (x * y⁻¹) ∈ (⊥ : Subgroup ↥K) := by
      rw [← hdisj]
      exact ⟨hxV, hxZ⟩
    have hxy1 : x * y⁻¹ = 1 := by
      apply Subgroup.inclusion_injective h.VB_le
      simpa using (Subgroup.mem_bot.mp hbot)
    calc x = x * y⁻¹ * y := by group
      _ = 1 * y := by rw [hxy1]
      _ = y := one_mul y
  have hrange : (VB.subgroupOf K).map (QuotientGroup.mk' (Subgroup.center ↥K)) = φ.range := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨⟨(y : G), hy⟩, ?_⟩
      show π (Subgroup.inclusion h.VB_le ⟨(y : G), hy⟩) = π y
      congr 1
    · rintro ⟨v, rfl⟩
      refine ⟨Subgroup.inclusion h.VB_le v, ?_, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr (by simpa [Subgroup.coe_inclusion] using v.2)
  have hcard : Nat.card ↥VB =
      Nat.card ((VB.subgroupOf K).map (QuotientGroup.mk' (Subgroup.center ↥K))) := by
    rw [hrange]
    exact Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv
  rw [← hcard]
  exact eight_le_card_VB h

theorem false_of_card_elemAbelian_le_four (h : Hyp G T M L B Tp VB K)
    (hS : ∀ E : Subgroup (↥K ⧸ Subgroup.center ↥K), IsElemAbelian 2 E → Nat.card E ≤ 4) :
    False := by
  have h8 := eight_le_card_image h
  have h4 := hS ((VB.subgroupOf K).map (QuotientGroup.mk' (Subgroup.center ↥K)))
    (isElemAbelian_image h)
  omega

theorem false_of_twoLocalsSolvable (h : Hyp G T M L B Tp VB K)
    (hS : TwoLocalsSolvable (↥K ⧸ Subgroup.center ↥K)) : False := by
  classical
  let Z : Subgroup ↥K := Subgroup.center ↥K
  let π : ↥K →* (↥K ⧸ Z) := QuotientGroup.mk' Z
  let E : Subgroup (↥K ⧸ Z) := (VB.subgroupOf K).map π
  have hE : IsElemAbelian 2 E := isElemAbelian_image h
  have h8 : 8 ≤ Nat.card E := eight_le_card_image h
  have hEne : E ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at h8
    omega
  have hE2 : IsPGroup 2 E := hE.isPGroup
  haveI : Group.IsSolvable ↥(Subgroup.normalizer (E : Set (↥K ⧸ Z))) :=
    hS E hEne hE2
  let LB : Subgroup G := perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G))
  let ψ : ↥LB →* (↥K ⧸ Z) := π.comp (Subgroup.inclusion h.LB_le)
  have hFnorm : ψ.range ≤ Subgroup.normalizer (E : Set (↥K ⧸ Z)) := by
    rintro _ ⟨l, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hzV : (z : G) ∈ VB := hz
      have hconj : (Subgroup.inclusion h.LB_le l) * z *
          (Subgroup.inclusion h.LB_le l)⁻¹ ∈ VB.subgroupOf K := by
        simpa only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv,
          Subgroup.coe_inclusion] using
          (Subgroup.mem_normalizer_iff.mp (LB_le_normalizer_VB h l.2) (z : G)).mp hzV
      refine ⟨(Subgroup.inclusion h.LB_le l) * z * (Subgroup.inclusion h.LB_le l)⁻¹,
        hconj, ?_⟩
      simp [ψ, map_mul]
    · rintro ⟨z, hz, hzeq⟩
      have hzV : (z : G) ∈ VB := hz
      have hlinv : (l : G)⁻¹ ∈ Subgroup.normalizer (VB : Set G) :=
        Subgroup.inv_mem _ (LB_le_normalizer_VB h l.2)
      have hconj : (Subgroup.inclusion h.LB_le l)⁻¹ * z *
          Subgroup.inclusion h.LB_le l ∈ VB.subgroupOf K := by
        simpa only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv,
          Subgroup.coe_inclusion, inv_inv] using
          (Subgroup.mem_normalizer_iff.mp hlinv (z : G)).mp hzV
      refine ⟨(Subgroup.inclusion h.LB_le l)⁻¹ * z * Subgroup.inclusion h.LB_le l,
        hconj, ?_⟩
      have hy : y = (ψ l)⁻¹ * π z * ψ l := by
        rw [hzeq]
        group
      rw [hy]
      simp [ψ, map_mul]
  let N := Subgroup.normalizer (E : Set (↥K ⧸ Z))
  haveI : Group.IsSolvable N := hS E hEne hE2
  let ψ' : ↥LB →* N := ψ.codRestrict N (fun l => hFnorm ⟨l, rfl⟩)
  have hLBperf : ⁅LB, LB⁆ = LB := LB_perfect h
  haveI : Group.IsPerfect ↥LB := Subgroup.isPerfect_iff.mpr hLBperf
  have hψ' : ψ' = 1 := CFSG.ComponentClassification.SolvableKernelContainment.hom_eq_one ψ'
  have hψ1 : ∀ l : ↥LB, ψ l = 1 := by
    intro l
    have h : ((ψ' l : N) : ↥K ⧸ Z) = 1 := by
      rw [hψ']
      rfl
    simpa [ψ'] using h
  have hLBZ : LB.subgroupOf K ≤ Z := by
    intro x hx
    have hxLB : (x : G) ∈ LB := Subgroup.mem_subgroupOf.mp hx
    have h1 : π (Subgroup.inclusion h.LB_le ⟨(x : G), hxLB⟩) = 1 := by
      simpa [ψ] using hψ1 ⟨(x : G), hxLB⟩
    have harg : (Subgroup.inclusion h.LB_le ⟨(x : G), hxLB⟩ : ↥K) = x :=
      Subtype.ext rfl
    rw [harg] at h1
    exact (QuotientGroup.eq_one_iff (N := Z) x).mp h1
  have hLBcomm : IsMulCommutative ↥LB := by
    have hincl : ∀ a : ↥LB, Subgroup.inclusion h.LB_le a ∈ LB.subgroupOf K := by
      intro a
      exact Subgroup.mem_subgroupOf.mpr (by simpa [Subgroup.coe_inclusion] using a.2)
    refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    have hc := Subgroup.mem_center_iff.mp (hLBZ (hincl a)) (Subgroup.inclusion h.LB_le b)
    simpa [Subgroup.coe_inclusion] using (congrArg Subtype.val hc).symm
  have hLBbot : LB = ⊥ := by
    haveI : IsMulCommutative ↥LB := hLBcomm
    haveI : Subsingleton ↥LB := Group.IsPerfect.subsingleton_of_isMulCommutative
    exact Subgroup.eq_bot_of_subsingleton LB
  have hVBbot : VB = ⊥ := by
    rw [VB_eq_commutator h]
    change ⁅VB, LB⁆ = ⊥
    rw [hLBbot, Subgroup.commutator_bot_right]
  exact h.setting.hyp.VB_ne_bot hVBbot

theorem exists_images (h : Hyp G T M L B Tp VB K) :
    ∃ E Y : Subgroup (↥K ⧸ Subgroup.center ↥K), IsElemAbelian 2 E ∧ 8 ≤ Nat.card E ∧
      ⁅Y, Y⁆ = Y ∧ Y ≤ Subgroup.normalizer (E : Set (↥K ⧸ Subgroup.center ↥K)) ∧ E ≤ Y ∧
      E = ⁅E, Y⁆ := by
  classical
  let Z : Subgroup ↥K := Subgroup.center ↥K
  let π : ↥K →* (↥K ⧸ Z) := QuotientGroup.mk' Z
  let E : Subgroup (↥K ⧸ Z) := (VB.subgroupOf K).map π
  let LB : Subgroup G := perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G))
  let ψ : ↥LB →* (↥K ⧸ Z) := π.comp (Subgroup.inclusion h.LB_le)
  let Y : Subgroup (↥K ⧸ Z) := ψ.range
  have hE : IsElemAbelian 2 E := by simpa [E, Z, π] using isElemAbelian_image h
  have h8 : 8 ≤ Nat.card E := by simpa [E, Z, π] using eight_le_card_image h
  have hYperf : ⁅Y, Y⁆ = Y := by
    change ⁅ψ.range, ψ.range⁆ = ψ.range
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def,
      CFSG.Quasithin.H13.Ch4.E443.F4411.commutator_eq_top_of_perfect (LB_perfect h),
      Subgroup.map_top]
  have hψrange : ψ.range = (LB.subgroupOf K).map π := by
    ext x
    constructor
    · rintro ⟨l, rfl⟩
      refine ⟨Subgroup.inclusion h.LB_le l, ?_, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr (by simpa using l.2)
    · rintro ⟨k, hk, rfl⟩
      refine ⟨⟨(k : G), Subgroup.mem_subgroupOf.mp hk⟩, ?_⟩
      exact congrArg π (Subtype.ext rfl)
  have hFnorm : Y ≤ Subgroup.normalizer (E : Set (↥K ⧸ Z)) := by
    rintro _ ⟨l, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hzV : (z : G) ∈ VB := hz
      have hconj : (Subgroup.inclusion h.LB_le l) * z *
          (Subgroup.inclusion h.LB_le l)⁻¹ ∈ VB.subgroupOf K := by
        simpa only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv,
          Subgroup.coe_inclusion] using
          (Subgroup.mem_normalizer_iff.mp (LB_le_normalizer_VB h l.2) (z : G)).mp hzV
      refine ⟨(Subgroup.inclusion h.LB_le l) * z * (Subgroup.inclusion h.LB_le l)⁻¹,
        hconj, ?_⟩
      simp [ψ, map_mul]
    · rintro ⟨z, hz, hzeq⟩
      have hzV : (z : G) ∈ VB := hz
      have hlinv : (l : G)⁻¹ ∈ Subgroup.normalizer (VB : Set G) :=
        Subgroup.inv_mem _ (LB_le_normalizer_VB h l.2)
      have hconj : (Subgroup.inclusion h.LB_le l)⁻¹ * z *
          Subgroup.inclusion h.LB_le l ∈ VB.subgroupOf K := by
        simpa only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv,
          Subgroup.coe_inclusion, inv_inv] using
          (Subgroup.mem_normalizer_iff.mp hlinv (z : G)).mp hzV
      refine ⟨(Subgroup.inclusion h.LB_le l)⁻¹ * z * Subgroup.inclusion h.LB_le l,
        hconj, ?_⟩
      have hy : y = (ψ l)⁻¹ * π z * ψ l := by
        rw [hzeq]
        group
      rw [hy]
      simp [ψ, map_mul]
  have hEY : E ≤ Y := by
    change E ≤ ψ.range
    rw [hψrange]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono K (VB_le_LB h))
  have hVBsub : VB.subgroupOf K = ⁅VB.subgroupOf K, LB.subgroupOf K⁆ := by
    apply Subgroup.map_injective K.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr h.VB_le, inf_eq_left.mpr h.LB_le]
    exact VB_eq_commutator h
  have hEeq : E = ⁅E, Y⁆ := by
    dsimp [E, Y]
    rw [hψrange, ← Subgroup.map_commutator, ← hVBsub]
  exact ⟨E, Y, hE, h8, hYperf, hFnorm, hEY, hEeq⟩

theorem false_of_perfCentral (h : Hyp G T M L B Tp VB K)
    (hS : CFSG.Quasithin.H13.Ch4.E443.F4411.PerfCentral
      (↥K ⧸ Subgroup.center ↥K)) : False := by
  obtain ⟨E, Y, hE, h8, hYperf, hFnorm, -, hEeq⟩ := exists_images h
  have hEbot : E = ⊥ := by rw [hEeq, hS E Y hE.isPGroup hYperf hFnorm]
  rw [hEbot, Subgroup.card_bot] at h8
  omega

end Hyp

theorem For.of_twoLocalsSolvable {P : (S : Type) → [Group S] → Prop}
    (hP : ∀ (S : Type) [Group S] [Finite S], P S → TwoLocalsSolvable S) : For P := by
  intro G _ _ T M L B Tp VB K hH hPK
  exact (Hyp.false_of_twoLocalsSolvable hH (hP _ hPK)).elim

theorem For.of_card_elemAbelian_le_four {P : (S : Type) → [Group S] → Prop}
    (hP : ∀ (S : Type) [Group S] [Finite S], P S →
      ∀ E : Subgroup S, IsElemAbelian 2 E → Nat.card E ≤ 4) : For P := by
  intro G _ _ T M L B Tp VB K hH hPK
  exact (Hyp.false_of_card_elemAbelian_le_four hH (hP _ hPK)).elim

theorem For.of_perfCentral {P : (S : Type) → [Group S] → Prop}
    (hP : ∀ (S : Type) [Group S] [Finite S], P S →
      CFSG.Quasithin.H13.Ch4.E443.F4411.PerfCentral S) : For P := by
  intro G _ _ T M L B Tp VB K hH hPK
  exact (Hyp.false_of_perfCentral hH (hP _ hPK)).elim

end CFSG.SectionRank.QTK.Insp443
