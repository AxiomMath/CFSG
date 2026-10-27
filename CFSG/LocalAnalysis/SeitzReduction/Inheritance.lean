module

public import CFSG.LocalAnalysis.SeitzReduction.PerfectCentralizer
import CFSG.FeitThompson.OddOrderTheorem
import CFSG.Walter.Cited.OddQuotient
import CFSG.Dihedral.DisconnectedInvolutionGraph.OddCore
import CFSG.LocalAnalysis.ComponentClassification.M12CoverKernelBasic
import CFSG.LocalAnalysis.EvenSmallLie.Setup
import CFSG.GroupTheory.LocalCores.Layer.CentralExtension

public section

namespace CFSG.SeitzReduction

open Subgroup CFSG.Open
open CFSG.ComponentClassification.M12Cover.CyclicKernel
  (eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two)
open CFSG.ComponentClassification.PerfectAutomorphisms (hom_eq_id_of_central_displacement)

section TwoSubgroups

variable {X : Type*} [Group X] [Finite X]

theorem card_le_two_of_card_inf_centralizer_le_two {S : Subgroup X} (hS : IsPGroup 2 S)
    {t : X} (htS : t ∈ S) (ht : orderOf t = 2)
    (h : Nat.card (S ⊓ centralizer ({t} : Set X) : Subgroup X) ≤ 2) : Nat.card S ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htC : zpowers t ≤ S ⊓ centralizer ({t} : Set X) :=
    zpowers_le.2 ⟨htS, mem_centralizer_singleton_iff.2 rfl⟩
  have hCeq : S ⊓ centralizer ({t} : Set X) = zpowers t :=
    (eq_of_le_of_card_ge htC (by rw [Nat.card_zpowers, ht]; exact h)).symm
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht
    exact absurd ht (by decide)
  have : Nontrivial S := ⟨⟨⟨t, htS⟩, 1, fun h1 => ht1 (congrArg Subtype.val h1)⟩⟩
  have := hS.center_nontrivial
  obtain ⟨z, hz⟩ := exists_ne (1 : center S)
  have hzC : ((z : S) : X) ∈ S ⊓ centralizer ({t} : Set X) := by
    refine ⟨(z : S).2, mem_centralizer_singleton_iff.2 ?_⟩
    exact (congrArg Subtype.val (mem_center_iff.1 z.2 ⟨t, htS⟩)).symm
  rw [hCeq] at hzC
  rcases eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two ht hzC with h1 | h1
  · exact absurd (Subtype.ext (Subtype.ext h1)) hz
  · have hSC : S ≤ S ⊓ centralizer ({t} : Set X) := fun s hs => by
      refine ⟨hs, mem_centralizer_singleton_iff.2 ?_⟩
      rw [← h1]
      exact congrArg Subtype.val (mem_center_iff.1 z.2 ⟨s, hs⟩)
    exact (card_le_of_le hSC).trans h

theorem card_le_two_of_forall_le_inf_centralizer {K : Subgroup X} {t : X} (htK : t ∈ K)
    (ht : orderOf t = 2)
    (h : ∀ U : Subgroup X, IsPGroup 2 U → U ≤ K ⊓ centralizer ({t} : Set X) → Nat.card U ≤ 2)
    {U : Subgroup X} (hU : IsPGroup 2 U) (hUK : U ≤ K) : Nat.card U ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set tK : K := ⟨t, htK⟩ with htKdef
  have htK2 : orderOf tK = 2 := by rw [htKdef, orderOf_mk, ht]
  have hp : IsPGroup 2 (zpowers tK) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, htK2, pow_one])
  obtain ⟨S, hS⟩ := hp.exists_le_sylow
  have hS2 : IsPGroup 2 ((S : Subgroup K).map K.subtype) := S.isPGroup'.map _
  have htS : t ∈ (S : Subgroup K).map K.subtype := ⟨tK, hS (mem_zpowers tK), rfl⟩
  have hcardS : Nat.card S ≤ 2 := by
    rw [← card_map_of_injective K.subtype_injective]
    exact card_le_two_of_card_inf_centralizer_le_two hS2 htS ht
      (h _ (hS2.to_le inf_le_left) (inf_le_inf_right _ (map_subtype_le _)))
  obtain ⟨T, hT⟩ := (hU.comap_subtype (K := K)).exists_le_sylow
  calc Nat.card U = Nat.card (U.subgroupOf K) :=
        (Nat.card_congr (subgroupOfEquivOfLe hUK).toEquiv).symm
    _ ≤ Nat.card T := card_le_of_le hT
    _ = Nat.card S := Nat.card_congr (Sylow.equiv T S).toEquiv
    _ ≤ 2 := hcardS

theorem perfect_eq_bot_of_forall_card_le_two {K P : Subgroup X}
    (h : ∀ U : Subgroup X, IsPGroup 2 U → U ≤ K → Nat.card U ≤ 2) (hPK : P ≤ K)
    (hP : ⁅P, P⁆ = P) : P = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S⟩ : Nonempty (Sylow 2 P) := inferInstance
  have hScard : Nat.card S ≤ 2 := by
    rw [← card_map_of_injective P.subtype_injective]
    exact h _ (S.isPGroup'.map _) ((map_subtype_le _).trans hPK)
  have hScyc : IsCyclic (S : Subgroup P) := by
    refine isCyclic_of_card_dvd_prime (p := 2) ?_
    obtain ⟨k, hk⟩ := S.isPGroup'.exists_card_eq
    rw [hk] at hScard ⊢
    rcases k with _ | _ | k
    · exact one_dvd _
    · exact dvd_refl _
    · exfalso
      have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      rw [pow_succ, pow_succ] at hScard
      omega
  obtain ⟨-, -, -, ⟨hn, hodd, hidx, -⟩, -⟩ := CFSG.cyclic_sylow_normal_odd_complement S hScyc
  have hq : IsPGroup 2 (P ⧸ pPrimeCore 2 P) := by
    obtain ⟨k, hk⟩ := S.isPGroup'.exists_card_eq
    exact IsPGroup.of_card (n := k) (by rw [← index_eq_card, hidx, hk])
  have := hq.isNilpotent
  have hPtop : ⁅(⊤ : Subgroup P), (⊤ : Subgroup P)⁆ = ⊤ := by
    have := Group.isPerfect_def.mp (isPerfect_iff.mpr hP)
    rwa [_root_.commutator_def] at this
  have htop : pPrimeCore 2 P = ⊤ := by
    have := perfect_le_ker (QuotientGroup.mk' (pPrimeCore 2 P)) hPtop
    rw [QuotientGroup.ker_mk'] at this
    exact top_le_iff.mp this
  have hPodd : Odd (Nat.card P) := by
    rw [htop, card_top] at hodd
    exact hodd
  exact perfect_eq_bot_of_le (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hPodd) hP le_rfl

theorem exists_conj_eq_of_forall_card_le_two {K : Subgroup X}
    (h : ∀ U : Subgroup X, IsPGroup 2 U → U ≤ K → Nat.card U ≤ 2) {t u : X} (htK : t ∈ K)
    (ht : orderOf t = 2) (huK : u ∈ K) (hu : orderOf u = 2) :
    ∃ k ∈ K, k * t * k⁻¹ = u := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have key : ∀ v : K, orderOf v = 2 → ∃ S : Sylow 2 K, (S : Subgroup K) = zpowers v := by
    intro v hv
    have hp : IsPGroup 2 (zpowers v) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hv, pow_one])
    obtain ⟨S, hS⟩ := hp.exists_le_sylow
    refine ⟨S, (eq_of_le_of_card_ge hS ?_).symm⟩
    rw [Nat.card_zpowers, hv, ← card_map_of_injective K.subtype_injective]
    exact h _ (S.isPGroup'.map _) (map_subtype_le _)
  set tK : K := ⟨t, htK⟩ with htKdef
  set uK : K := ⟨u, huK⟩ with huKdef
  have htK2 : orderOf tK = 2 := by rw [htKdef, orderOf_mk, ht]
  have huK2 : orderOf uK = 2 := by rw [huKdef, orderOf_mk, hu]
  obtain ⟨St, hSt⟩ := key tK htK2
  obtain ⟨Su, hSu⟩ := key uK huK2
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq K St Su
  have hmem : k * tK * k⁻¹ ∈ (Su : Subgroup K) := by
    rw [← hk, Sylow.coe_subgroup_smul]
    have : tK ∈ (St : Subgroup K) := hSt ▸ mem_zpowers tK
    have h2 := smul_mem_pointwise_smul tK (MulAut.conj k) (St : Subgroup K) this
    simpa [MulAut.smul_def, MulAut.conj_apply] using h2
  rw [hSu] at hmem
  refine ⟨k, k.2, ?_⟩
  rcases eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two huK2 hmem with h1 | h1
  · exfalso
    have : tK = 1 := by
      calc tK = k⁻¹ * (k * tK * k⁻¹) * k := by group
        _ = 1 := by rw [h1]; group
    rw [this, orderOf_one] at htK2
    exact absurd htK2 (by decide)
  · exact congrArg Subtype.val h1

end TwoSubgroups

section Inheritance

variable {H : Type*} [Group H] [Finite H]

private theorem isQuasisimple_native_of_open {Q : Type*} [Group Q]
    (hQ : CFSG.Open.IsQuasisimple Q) : CFSG.IsQuasisimple Q :=
  ⟨⟨hQ.1⟩, hQ.2,
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian Q hQ⟩

theorem ne_bot_of_isQuasisimple {X : Type*} [Group X] {D : Subgroup X}
    (hDq : CFSG.Open.IsQuasisimple D) : D ≠ ⊥ :=
  (nontrivial_iff_ne_bot D).mp
    (CFSG.LocalCores.isQuasisimple_nontrivial (isQuasisimple_native_of_open hDq))

omit [Finite H] in
theorem orderOf_mk_oddCore_of_odd (hO : Odd (Nat.card (oddCore H))) {t : H}
    (ht : orderOf t = 2) : orderOf (QuotientGroup.mk' (oddCore H) t) = 2 := by
  refine orderOf_eq_prime (by rw [← map_pow, ← ht, pow_orderOf_eq_one, map_one]) ?_
  intro h1
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  have h2 := (oddCore H).orderOf_dvd_natCard h1
  rw [ht] at h2
  exact (Nat.not_even_iff_odd.2 hO) (even_iff_two_dvd.2 h2)

theorem orderOf_mk_oddCore {t : H} (ht : orderOf t = 2) :
    orderOf (QuotientGroup.mk' (oddCore H) t) = 2 :=
  orderOf_mk_oddCore_of_odd CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_odd ht

theorem oddCore_subgroupOf_le_center {D : Subgroup H} (hDq : CFSG.Open.IsQuasisimple D) :
    (oddCore H).subgroupOf D ≤ center D := by
  have hO : Odd (Nat.card (oddCore H)) := CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_odd
  rcases CFSG.LocalCores.quasisimple_normal_subgroups (isQuasisimple_native_of_open hDq)
    (N := (oddCore H).subgroupOf D) inferInstance with h | h
  · exfalso
    have hDO : D ≤ oddCore H := fun d hd => by
      have : (⟨d, hd⟩ : D) ∈ (oddCore H).subgroupOf D := h ▸ mem_top _
      exact mem_subgroupOf.1 this
    have hDodd : Odd (Nat.card D) := hO.of_dvd_nat (card_dvd_of_le hDO)
    exact ne_bot_of_isQuasisimple hDq (perfect_eq_bot_of_le
      (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hDodd) (isPerfect_iff.mp ⟨hDq.1⟩) le_rfl)
  · exact h

theorem isQuasisimple_map_oddCore {D : Subgroup H} (hDq : CFSG.Open.IsQuasisimple D) :
    CFSG.Open.IsQuasisimple (D.map (QuotientGroup.mk' (oddCore H))) := by
  set π := QuotientGroup.mk' (oddCore H) with hπ
  have hker : (π.subgroupMap D).ker ≤ center D := by
    intro x hx
    apply oddCore_subgroupOf_le_center hDq
    rw [mem_subgroupOf]
    have h1 : π (x : H) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  have h := CFSG.LocalCores.isQuasisimple_of_surjective (isQuasisimple_native_of_open hDq)
    (π.subgroupMap D) (π.subgroupMap_surjective D) hker
  exact ⟨h.1.commutator_eq_top, h.2.1⟩

omit [Finite H] in
theorem map_oddCore_le_centralizer {t : H} {D : Subgroup H}
    (hDt : D ≤ centralizer ({t} : Set H)) :
    D.map (QuotientGroup.mk' (oddCore H)) ≤
      centralizer ({QuotientGroup.mk' (oddCore H) t} : Set (H ⧸ oddCore H)) := by
  rintro _ ⟨d, hd, rfl⟩
  rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
    mem_centralizer_singleton_iff.1 (hDt hd)]

theorem map_oddCore_normal {t : H} (ht : orderOf t = 2) {D : Subgroup H}
    (hDt : D ≤ centralizer ({t} : Set H))
    (hDn : (D.subgroupOf (centralizer ({t} : Set H))).Normal) :
    ((D.map (QuotientGroup.mk' (oddCore H))).subgroupOf
      (centralizer ({QuotientGroup.mk' (oddCore H) t} : Set (H ⧸ oddCore H)))).Normal := by
  have hO : Odd (Nat.card (oddCore H)) := CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_odd
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  refine ⟨fun x hx c => ?_⟩
  rw [mem_subgroupOf] at hx ⊢
  obtain ⟨d, hd, hdx⟩ := hx
  obtain ⟨c', hc', hcc'⟩ := CFSG.Walter.Suzuki.centralizer_mk_le_map (oddCore H) hO htt c.2
  have hmem : c' * d * c'⁻¹ ∈ D := by
    have := hDn.conj_mem ⟨d, hDt hd⟩ (mem_subgroupOf.2 hd) ⟨c', hc'⟩
    rwa [mem_subgroupOf] at this
  refine ⟨c' * d * c'⁻¹, hmem, ?_⟩
  simp only [coe_mul, coe_inv, map_mul, map_inv]
  rw [hdx, hcc']

theorem card_le_two_of_le_centralizer_inf {t : H} (ht : orderOf t = 2) {D : Subgroup H}
    (hDt : D ≤ centralizer ({t} : Set H))
    (hDn : (D.subgroupOf (centralizer ({t} : Set H))).Normal)
    (hDq : CFSG.Open.IsQuasisimple D)
    (hsyl : ∀ U : Subgroup H, IsPGroup 2 U →
      U ≤ centralizer ({t} : Set H) ⊓ centralizer (D : Set H) → Nat.card U ≤ 2)
    {V : Subgroup (H ⧸ oddCore H)} (hV : IsPGroup 2 V)
    (hVD : V ≤ centralizer (D.map (QuotientGroup.mk' (oddCore H)) : Set (H ⧸ oddCore H)) ⊓
      centralizer ({QuotientGroup.mk' (oddCore H) t} : Set (H ⧸ oddCore H))) :
    Nat.card V ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO : Odd (Nat.card (oddCore H)) := CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_odd
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  set π := QuotientGroup.mk' (oddCore H) with hπ
  set A := centralizer ({t} : Set H) ⊓ V.comap π with hA
  have hAV : A.map π = V := by
    apply le_antisymm
    · rintro _ ⟨a, ha, rfl⟩
      exact ha.2
    · intro v hv
      obtain ⟨c, hc, rfl⟩ :=
        CFSG.Walter.Suzuki.centralizer_mk_le_map (oddCore H) hO htt (hVD hv).2
      exact ⟨c, ⟨hc, hv⟩, rfl⟩
  by_contra hlt
  push Not at hlt
  obtain ⟨k, hk⟩ := hV.exists_card_eq
  have h4V : 2 ^ 2 ∣ Nat.card V := by
    rw [hk]
    refine pow_dvd_pow 2 ?_
    by_contra hk2
    push Not at hk2
    interval_cases k <;> simp_all
  have h4A : 2 ^ 2 ∣ Nat.card A := h4V.trans (hAV ▸ card_map_dvd A π)
  obtain ⟨W⟩ : Nonempty (Sylow 2 A) := inferInstance
  have h4W : 2 ^ 2 ∣ Nat.card W := W.pow_dvd_card_of_pow_dvd_card h4A
  have hW2 : IsPGroup 2 ((W : Subgroup A).map A.subtype) := W.isPGroup'.map _
  have hWA : (W : Subgroup A).map A.subtype ≤ A := map_subtype_le _
  have hWcard : Nat.card ((W : Subgroup A).map A.subtype) = Nat.card W :=
    card_map_of_injective A.subtype_injective
  have hCN : centralizer ({t} : Set H) ≤ normalizer (D : Set H) :=
    le_normalizer_of_normal_subgroupOf hDt
  have : Group.IsPerfect D := ⟨hDq.1⟩
  have hWD : (W : Subgroup A).map A.subtype ≤ centralizer (D : Set H) := by
    intro w hw
    have hwC : w ∈ centralizer ({t} : Set H) := (hWA hw).1
    have hwV : π w ∈ V := (hWA hw).2
    have hid := hom_eq_id_of_central_displacement
      (D.normalizerMonoidHom ⟨w, hCN hwC⟩).toMonoidHom (fun d => by
        apply oddCore_subgroupOf_le_center hDq
        rw [mem_subgroupOf, ← QuotientGroup.eq_one_iff]
        have hcomm : π d * π w = π w * π d :=
          mem_centralizer_iff.1 (hVD hwV).1 (π d) ⟨d, d.2, rfl⟩
        have e : (((d⁻¹ * (D.normalizerMonoidHom ⟨w, hCN hwC⟩).toMonoidHom d : D) : H) :
            H ⧸ oddCore H) = (π d)⁻¹ * (π w * π d * (π w)⁻¹) := by
          simp [hπ, normalizerMonoidHom_apply_apply_coe]
        rw [e, ← hcomm, mul_inv_cancel_right, inv_mul_cancel])
    rw [mem_centralizer_iff]
    intro d hd
    have h1 := congrArg (fun f : D →* D => ((f ⟨d, hd⟩ : D) : H)) hid
    simp only [MulEquiv.coe_toMonoidHom, normalizerMonoidHom_apply_apply_coe,
      MonoidHom.id_apply] at h1
    calc d * w = w * d * w⁻¹ * w := by rw [h1]
      _ = w * d := by group
  have h1 := hsyl _ hW2 (le_inf (fun w hw => (hWA hw).1) hWD)
  rw [hWcard] at h1
  have h2 := Nat.le_of_dvd Nat.card_pos h4W
  omega

theorem card_le_two_of_le_centralizer_map_oddCore {t : H} (ht : orderOf t = 2) {D : Subgroup H}
    (hDt : D ≤ centralizer ({t} : Set H))
    (hDn : (D.subgroupOf (centralizer ({t} : Set H))).Normal)
    (hDq : CFSG.Open.IsQuasisimple D)
    (hsyl : ∀ U : Subgroup H, IsPGroup 2 U →
      U ≤ centralizer ({t} : Set H) ⊓ centralizer (D : Set H) → Nat.card U ≤ 2)
    {U : Subgroup (H ⧸ oddCore H)} (hU : IsPGroup 2 U)
    (hUD : U ≤ centralizer (D.map (QuotientGroup.mk' (oddCore H)) : Set (H ⧸ oddCore H))) :
    Nat.card U ≤ 2 := by
  have htK : QuotientGroup.mk' (oddCore H) t ∈
      centralizer (D.map (QuotientGroup.mk' (oddCore H)) : Set (H ⧸ oddCore H)) :=
    mem_centralizer_iff.2 fun x hx =>
      mem_centralizer_singleton_iff.1 (map_oddCore_le_centralizer hDt hx)
  exact card_le_two_of_forall_le_inf_centralizer htK (orderOf_mk_oddCore ht)
    (fun V hV hVK => card_le_two_of_le_centralizer_inf ht hDt hDn hDq hsyl hV hVK) hU hUD

theorem standardComponentIsStandard_map_oddCore {t : H} (ht : orderOf t = 2) {D : Subgroup H}
    (hDt : D ≤ centralizer ({t} : Set H))
    (hDn : (D.subgroupOf (centralizer ({t} : Set H))).Normal)
    (hDq : CFSG.Open.IsQuasisimple D)
    (hsyl : ∀ U : Subgroup H, IsPGroup 2 U →
      U ≤ centralizer ({t} : Set H) ⊓ centralizer (D : Set H) → Nat.card U ≤ 2) :
    standardComponentIsStandard (D.map (QuotientGroup.mk' (oddCore H))) := by
  set π := QuotientGroup.mk' (oddCore H) with hπ
  set Dbar := D.map π with hDbar
  set tbar := π t with htbar
  set K := centralizer (Dbar : Set (H ⧸ oddCore H)) with hK
  have htbar2 : orderOf tbar = 2 := orderOf_mk_oddCore ht
  have hle : Dbar ≤ centralizer ({tbar} : Set (H ⧸ oddCore H)) := map_oddCore_le_centralizer hDt
  have htK : tbar ∈ K :=
    mem_centralizer_iff.2 fun x hx => mem_centralizer_singleton_iff.1 (hle hx)
  have hK2 : ∀ U : Subgroup (H ⧸ oddCore H), IsPGroup 2 U → U ≤ K → Nat.card U ≤ 2 :=
    fun U hU hUK => card_le_two_of_le_centralizer_map_oddCore ht hDt hDn hDq hsyl hU hUK
  have hDbarq : CFSG.Open.IsQuasisimple Dbar := isQuasisimple_map_oddCore hDq
  have hnorm := map_oddCore_normal ht hDt hDn
  have hCtN : centralizer ({tbar} : Set (H ⧸ oddCore H)) ≤ normalizer (Dbar : Set _) :=
    le_normalizer_of_normal_subgroupOf hle
  have hKN : K ≤ normalizer (Dbar : Set (H ⧸ oddCore H)) := centralizer_le_normalizer _
  have hNDK : normalizer (Dbar : Set (H ⧸ oddCore H)) ≤ normalizer (K : Set _) := by
    intro h hh
    rw [mem_normalizer_iff]
    intro x
    constructor
    · exact fun hx => CFSG.EvenSmallLie.conj_mem_centralizer_of_mem_normalizer hh hx
    · intro hx
      have h1 := CFSG.EvenSmallLie.conj_mem_centralizer_of_mem_normalizer (inv_mem hh) hx
      rwa [show h⁻¹ * (h * x * h⁻¹) * h⁻¹⁻¹ = x by group] at h1
  have hNKD : normalizer (K : Set (H ⧸ oddCore H)) ≤ normalizer (Dbar : Set _) := by
    intro h hh
    have hu : h * tbar * h⁻¹ ∈ K := (mem_normalizer_iff.1 hh tbar).1 htK
    have hu2 : orderOf (h * tbar * h⁻¹) = 2 := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, htbar2]
    obtain ⟨k, hk, hkt⟩ := exists_conj_eq_of_forall_card_le_two hK2 htK htbar2 hu hu2
    have hy : k⁻¹ * h ∈ centralizer ({tbar} : Set (H ⧸ oddCore H)) := by
      rw [mem_centralizer_singleton_iff]
      calc k⁻¹ * h * tbar = k⁻¹ * (h * tbar * h⁻¹) * h := by group
        _ = k⁻¹ * (k * tbar * k⁻¹) * h := by rw [hkt]
        _ = tbar * (k⁻¹ * h) := by group
    rw [show h = k * (k⁻¹ * h) by group]
    exact mul_mem (hKN hk) (hCtN hy)
  refine ⟨hDbarq, ?_, ?_, le_antisymm hNKD hNDK, ?_⟩
  ·
    have h2 : orderOf (⟨tbar, htK⟩ : K) = 2 := by rw [orderOf_mk, htbar2]
    exact even_iff_two_dvd.2 (h2 ▸ orderOf_dvd_natCard _)
  ·
    intro h hh
    by_contra hodd
    rw [Nat.not_odd_iff_even] at hodd
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.1 hodd)
    have hu2 : orderOf (u : H ⧸ oddCore H) = 2 := by rw [orderOf_coe, hu]
    have huK : (u : H ⧸ oddCore H) ∈ K := u.2.1
    obtain ⟨v, hvK, hvu⟩ := u.2.2
    have e : h * v * h⁻¹ = u := by simpa [MulAut.conj_apply] using hvu
    have hv2 : orderOf v = 2 := by
      rw [← hu2, ← e, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
    obtain ⟨k, hk, hkt⟩ := exists_conj_eq_of_forall_card_le_two hK2 htK htbar2 huK hu2
    obtain ⟨k', hk', hk't⟩ := exists_conj_eq_of_forall_card_le_two hK2 htK htbar2 hvK hv2
    have hy : k⁻¹ * h * k' ∈ centralizer ({tbar} : Set (H ⧸ oddCore H)) := by
      rw [mem_centralizer_singleton_iff]
      calc k⁻¹ * h * k' * tbar = k⁻¹ * (h * (k' * tbar * k'⁻¹) * h⁻¹) * (h * k') := by group
        _ = k⁻¹ * (u : H ⧸ oddCore H) * (h * k') := by rw [hk't, e]
        _ = k⁻¹ * (k * tbar * k⁻¹) * (h * k') := by rw [hkt]
        _ = tbar * (k⁻¹ * h * k') := by group
    apply hh
    rw [show h = k * (k⁻¹ * h * k') * k'⁻¹ by group]
    exact mul_mem (mul_mem (le_normalizer hk) (hNDK (hCtN hy))) (inv_mem (le_normalizer hk'))
  ·
    intro h hcomm
    have hle' : Dbar.map (MulAut.conj h).toMonoidHom ≤ K := by
      rw [commutator_comm] at hcomm
      exact commutator_eq_bot_iff_le_centralizer.1 hcomm
    have hperf : ⁅Dbar.map (MulAut.conj h).toMonoidHom, Dbar.map (MulAut.conj h).toMonoidHom⁆ =
        Dbar.map (MulAut.conj h).toMonoidHom := by
      rw [← map_commutator, isPerfect_iff.mp ⟨hDbarq.1⟩]
    have hbot := perfect_eq_bot_of_forall_card_le_two hK2 hle' hperf
    rw [map_eq_bot_iff_of_injective _ (MulAut.conj h).injective] at hbot
    exact ne_bot_of_isQuasisimple hDbarq hbot

theorem isComponentOf_map_oddCore {t : H} (ht : orderOf t = 2) {D : Subgroup H}
    (hDt : D ≤ centralizer ({t} : Set H))
    (hDn : (D.subgroupOf (centralizer ({t} : Set H))).Normal)
    (hDq : CFSG.Open.IsQuasisimple D) :
    CFSG.Open.IsComponentOf (D.map (QuotientGroup.mk' (oddCore H)))
      (centralizer ({QuotientGroup.mk' (oddCore H) t} : Set (H ⧸ oddCore H))) :=
  ⟨map_oddCore_le_centralizer hDt,
    CFSG.Open.IsSubnormal.step (map_oddCore_le_centralizer hDt) (map_oddCore_normal ht hDt hDn)
      (CFSG.Open.IsSubnormal.refl _),
    isQuasisimple_map_oddCore hDq⟩

end Inheritance

section Neighbour

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem inheritance_hyp_subgroupOf {H : Subgroup G} {t : G} (htH : t ∈ H) (ht : orderOf t = 2)
    {D : Subgroup G} (hDH : D ≤ H) (hDt : D ≤ centralizer ({t} : Set G))
    (hDn : ∀ c ∈ H ⊓ centralizer ({t} : Set G), ∀ d ∈ D, c * d * c⁻¹ ∈ D)
    (hDq : CFSG.Open.IsQuasisimple D)
    (hsyl : ∀ U : Subgroup G, IsPGroup 2 U →
      U ≤ H ⊓ centralizer ({t} : Set G) ⊓ centralizer (D : Set G) → Nat.card U ≤ 2) :
    orderOf (⟨t, htH⟩ : H) = 2 ∧
      D.subgroupOf H ≤ centralizer ({⟨t, htH⟩} : Set H) ∧
      ((D.subgroupOf H).subgroupOf (centralizer ({⟨t, htH⟩} : Set H))).Normal ∧
      CFSG.Open.IsQuasisimple (D.subgroupOf H) ∧
      ∀ U : Subgroup H, IsPGroup 2 U →
        U ≤ centralizer ({⟨t, htH⟩} : Set H) ⊓ centralizer (D.subgroupOf H : Set H) →
        Nat.card U ≤ 2 := by
  have hDt' : D.subgroupOf H ≤ centralizer ({⟨t, htH⟩} : Set H) := fun d hd =>
    mem_centralizer_singleton_iff.2 (Subtype.ext (mem_centralizer_singleton_iff.1
      (hDt (mem_subgroupOf.1 hd))))
  refine ⟨by rw [orderOf_mk, ht], hDt', ⟨fun n hn c => ?_⟩, ?_, fun U hU hUC => ?_⟩
  · rw [mem_subgroupOf, mem_subgroupOf] at hn ⊢
    have hc : ((c : H) : G) ∈ H ⊓ centralizer ({t} : Set G) :=
      ⟨(c : H).2, mem_centralizer_singleton_iff.2
        (congrArg Subtype.val (mem_centralizer_singleton_iff.1 c.2))⟩
    simpa using hDn _ hc _ hn
  · have hn := CFSG.LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hDH).symm
      (isQuasisimple_native_of_open hDq)
    exact ⟨hn.1.commutator_eq_top, hn.2.1⟩
  · rw [← card_map_of_injective H.subtype_injective]
    refine hsyl _ (hU.map _) ?_
    rintro _ ⟨u, hu, rfl⟩
    refine ⟨⟨u.2, mem_centralizer_singleton_iff.2
      (congrArg Subtype.val (mem_centralizer_singleton_iff.1 (hUC hu).1))⟩, ?_⟩
    show (u : G) ∈ centralizer (D : Set G)
    rw [mem_centralizer_iff]
    intro d hd
    exact congrArg Subtype.val (mem_centralizer_iff.1 (hUC hu).2 ⟨d, hDH hd⟩
      (mem_subgroupOf.2 hd))

theorem inheritance_subgroupOf {H : Subgroup G} {t : G} (htH : t ∈ H)
    (ht : orderOf t = 2) {D : Subgroup G} (hDH : D ≤ H) (hDt : D ≤ centralizer ({t} : Set G))
    (hDn : ∀ c ∈ H ⊓ centralizer ({t} : Set G), ∀ d ∈ D, c * d * c⁻¹ ∈ D)
    (hDq : CFSG.Open.IsQuasisimple D)
    (hsyl : ∀ U : Subgroup G, IsPGroup 2 U →
      U ≤ H ⊓ centralizer ({t} : Set G) ⊓ centralizer (D : Set G) → Nat.card U ≤ 2) :
    CFSG.Open.IsComponentOf ((D.subgroupOf H).map (QuotientGroup.mk' (oddCore H)))
        (centralizer ({QuotientGroup.mk' (oddCore H) ⟨t, htH⟩} : Set (H ⧸ oddCore H))) ∧
      (∀ U : Subgroup (H ⧸ oddCore H), IsPGroup 2 U →
        U ≤ centralizer ((D.subgroupOf H).map (QuotientGroup.mk' (oddCore H)) :
          Set (H ⧸ oddCore H)) → Nat.card U ≤ 2) ∧
      standardComponentIsStandard ((D.subgroupOf H).map (QuotientGroup.mk' (oddCore H))) := by
  obtain ⟨ht', hDt', hDn', hDq', hsyl'⟩ :=
    inheritance_hyp_subgroupOf htH ht hDH hDt hDn hDq hsyl
  exact ⟨isComponentOf_map_oddCore ht' hDt' hDn' hDq',
    fun U hU hUD => card_le_two_of_le_centralizer_map_oddCore ht' hDt' hDn' hDq' hsyl' hU hUD,
    standardComponentIsStandard_map_oddCore ht' hDt' hDn' hDq' hsyl'⟩

omit [Finite G] in
theorem mem_centralizer_of_le_centralizer_singleton {X : Subgroup G} {t : G}
    (hXt : X ≤ centralizer ({t} : Set G)) : t ∈ centralizer (X : Set G) :=
  mem_centralizer_iff.2 fun _ hx => mem_centralizer_singleton_iff.1 (hXt hx)

omit [Finite G] in
theorem layer_centralizer_normalized {L X : Subgroup G} {t : G}
    (hLt : centralizer ({t} : Set G) ≤ normalizer (L : Set G)) {c : G}
    (hc : c ∈ centralizer (X : Set G) ⊓ centralizer ({t} : Set G)) {d : G}
    (hd : d ∈ inSubgroup layer (L ⊓ centralizer (X : Set G))) :
    c * d * c⁻¹ ∈ inSubgroup layer (L ⊓ centralizer (X : Set G)) := by
  set Y := L ⊓ centralizer (X : Set G) with hY
  have hcL := hLt hc.2
  have hcN : c ∈ normalizer (Y : Set G) := by
    rw [mem_normalizer_iff]
    intro y
    rw [hY, mem_inf, mem_inf, ← mem_normalizer_iff.1 hcL y]
    refine and_congr_right fun _ => ?_
    exact mem_normalizer_iff.1 (le_normalizer hc.1) y
  obtain ⟨y, hy, rfl⟩ := hd
  have hchar := (Subgroup.characteristic_iff_map_eq.1 CFSG.LocalCores.layer_characteristic)
    (Y.normalizerMonoidHom ⟨c, hcN⟩)
  refine ⟨(Y.normalizerMonoidHom ⟨c, hcN⟩) y, ?_, ?_⟩
  · rw [← hchar]
    exact mem_map_of_mem _ hy
  · simp [normalizerMonoidHom_apply_apply_coe]

theorem standard_inheritance {L : Subgroup G} (hL : standardComponentIsStandard L) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {X : Subgroup G}
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hD : D = inSubgroup layer (L ⊓ centralizer (X : Set G)))
    (hDq : CFSG.Open.IsQuasisimple D)
    (hsyl : ∀ U : Subgroup G, IsPGroup 2 U →
      U ≤ centralizer (X : Set G) ⊓ centralizer ({t} : Set G) ⊓ centralizer (D : Set G) →
      Nat.card U ≤ 2) :
    CFSG.Open.IsComponentOf
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))))
        (centralizer ({QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩} :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))))) ∧
      (∀ U : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
        IsPGroup 2 U →
        U ≤ centralizer ((D.subgroupOf (centralizer (X : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
        Nat.card U ≤ 2) ∧
      standardComponentIsStandard ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) := by
  have hDY : D ≤ L ⊓ centralizer (X : Set G) := hD ▸ map_subtype_le _
  refine inheritance_subgroupOf htX ht (hDY.trans inf_le_right)
    (hDY.trans (inf_le_left.trans (le_centralizer_of_mem_centralizer htC)))
    (fun c hc d hd => ?_) hDq hsyl
  rw [hD] at hd ⊢
  exact layer_centralizer_normalized
    (CFSG.EvenSmallLie.centralizer_le_normalizer_of_standard hL htC ht) hc hd

end Neighbour

end CFSG.SeitzReduction
