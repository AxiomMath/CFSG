module

public import CFSG.LocalAnalysis.EvenBN.GMSK.CatSporadicBase
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporMathieu
public import CFSG.Sporadic.J1
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporCaseJ4
public import CFSG.Sporadic.Schreier.J4SNoComp
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverExternalOuter
public import CFSG.Sporadic.SmallOddCore.J3Aut
public import CFSG.Sporadic.SmallOddCore.HSLocal
public import CFSG.Sporadic.SmallOddCore.HSAut
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporMcL
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporMcLOuter
public import CFSG.Sporadic.SmallOddCore.HeLocal
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporRu
public import CFSG.Sporadic.SuzOddCore.CTIComponents
public import CFSG.Sporadic.SuzOddCore.SmallAut
public import CFSG.Sporadic.HeldB.AutModel
public import CFSG.Sporadic.HeldB.OuterFixedCore

public section

namespace CFSG.LocalAnalysis.EvenBN.GMSK.Sporadic

open Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.RestrictedStd.Spor
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem m11_fixedRootFree :
    SporadicFixedRootFree .M11 := by
  have hSL : ∀ n : ℕ, 2 ≤ n → ∀ (K : Type) [Field K] [Fintype K], Fintype.card K = 2 ^ n →
      ¬ Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) ∣ 48 := by
    intro n hn K _ _ hK h
    rw [card_sl2 hK] at h
    have := lt_of_sl2Order_dvd (by norm_num) (show 48 < 2 ^ 6 by norm_num) h
    interval_cases n <;> norm_num at h
  refine sporadicFixedRootFree_of_comps (isoInvariant_card_dvd 48) (isoInvariant_card_dvd 48) hSL
    hSL (fun G _ _ ⟨e⟩ t ht => compsSatisfy_centralizer_of_mulEquiv _ (isoInvariant_card_dvd 48)
      m11_centralizerIn_comps e t ht) (outer_comps_of_forall_inner (fun β => ?_) _)
  change β ∈ inner NativeSporadic.M11
  rw [CFSG.Sporadic.Schreier.inner_eq_top_of_card_le CFSG.Sporadic.Schreier.m11_center_eq_bot'
    CFSG.Sporadic.Schreier.m11_mulAut_card]
  trivial

theorem m12_fixedRootFieldFour : SporadicFixedRootFieldFour .M12 :=
  sporadicFixedRootFieldFour_of_card CFSG.Sporadic.Mathieu.card_M12 fun n hn h => by
    have := lt_of_sl2Order_dvd (by norm_num) (show 95040 < 2 ^ 17 by norm_num) h
    interval_cases n <;> first | rfl | norm_num at h

theorem sl2_fails_not_three_dvd : ∀ n : ℕ, 2 ≤ n → ∀ (K : Type) [Field K] [Fintype K],
    Fintype.card K = 2 ^ n → ¬ ¬ 3 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) :=
  fun _ _ _ _ _ hK => sl2_not_not_three_dvd hK

theorem m22_fixedRootFree :
    SporadicFixedRootFree .M22 := by
  have hSL : ∀ n : ℕ, 2 ≤ n → ∀ (K : Type) [Field K] [Fintype K], Fintype.card K = 2 ^ n →
      ¬ Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) ∣ 384 := by
    intro n hn K _ _ hK h
    rw [card_sl2 hK] at h
    have := lt_of_sl2Order_dvd (by norm_num) (show 384 < 2 ^ 9 by norm_num) h
    interval_cases n <;> norm_num at h
  refine sporadicFixedRootFree_of_comps (isoInvariant_card_dvd 384) isoInvariant_not_three_dvd
    hSL sl2_fails_not_three_dvd (fun G _ _ ⟨e⟩ t ht => compsSatisfy_centralizer_of_mulEquiv _
      (isoInvariant_card_dvd 384) m22_centralizerIn_comps e t ht)
    (fun G _ _ _ ⟨e⟩ β hβ2 hβ => ?_)
  exact CompsSatisfy.of_mulEquiv isoInvariant_not_three_dvd (fixSubTransportEquiv e β)
    (m22_outer_comps _ (transportAut_mul_self e (mul_self_eq_one_of_orderOf_eq_two hβ2))
      (transportAut_not_mem_inner e hβ))

theorem m23_fixedRootFree :
    SporadicFixedRootFree .M23 := by
  refine sporadicFixedRootFree_of_comps isoInvariant_not_three_dvd isoInvariant_not_three_dvd
    sl2_fails_not_three_dvd sl2_fails_not_three_dvd (fun G _ _ ⟨e⟩ t ht =>
      compsSatisfy_centralizer_of_mulEquiv _ isoInvariant_not_three_dvd m23_centralizerIn_comps e
        t ht) (outer_comps_of_forall_inner (fun β => ?_) _)
  change β ∈ inner NativeSporadic.M23
  rw [CFSG.Sporadic.Schreier.inner_eq_top_of_card_le CFSG.Sporadic.Schreier.m23_center_eq_bot'
    CFSG.Sporadic.Schreier.m23_mulAut_card]
  trivial

theorem m24_fixedRootFree :
    SporadicFixedRootFree .M24 := by
  refine sporadicFixedRootFree_of_comps isoInvariant_not_three_dvd isoInvariant_not_three_dvd
    sl2_fails_not_three_dvd sl2_fails_not_three_dvd (fun G _ _ ⟨e⟩ t ht =>
      compsSatisfy_centralizer_of_mulEquiv _ isoInvariant_not_three_dvd m24_centralizerIn_comps e
        t ht) (outer_comps_of_forall_inner (fun β => ?_) _)
  change β ∈ inner NativeSporadic.M24
  rw [CFSG.Sporadic.Schreier.inner_eq_top_of_card_le CFSG.Sporadic.Schreier.m24_center_eq_bot'
    CFSG.Sporadic.Schreier.m24_mulAut_card]
  trivial

theorem j1_fixedRootFieldFour : SporadicFixedRootFieldFour .J1 :=
  sporadicFixedRootFieldFour_of_card CFSG.Sporadic.J1.card_J1 fun n hn h => by
    have := lt_of_sl2Order_dvd (by norm_num) (show 175560 < 2 ^ 18 by norm_num) h
    interval_cases n <;> first | rfl | norm_num at h

theorem j4_fixedRootFree :
    SporadicFixedRootFree .J4 := by
  refine sporadicFixedRootFree_of_comps (Qi := fun _ _ => False) (Qo := fun _ _ => False)
    (fun _ _ _ _ _ h => h) (fun _ _ _ _ _ h => h) (fun _ _ _ _ _ _ h => h)
    (fun _ _ _ _ _ _ h => h) (fun G _ _ hG t ht B hB => j4NoComponentsInput G hG t ht B hB)
    (fun G _ _ _ ⟨e⟩ β hβ2 hβ => ?_)
  exfalso
  have eJ : G ≃* CFSG.Sporadic.J4.J :=
    e.trans (CFSG.Sporadic.J4.seedEquiv CFSG.Sporadic.J4.j4Facts.mat)
  have hcard : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer G) =
      Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer CFSG.Sporadic.J4.J) :=
    @CFSG.Sporadic.J4Schreier.card_outer_congr G CFSG.Sporadic.J4.J _
      (Subgroup.toGroup CFSG.Sporadic.J4.J) eJ
  have hodd : Odd (Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer G)) := by
    rw [hcard]
    exact CFSG.Sporadic.J4Schreier.CTU_J4_outer_automorphism_group_odd_order
  exact hβ (mem_inner_of_odd_card_outer hodd (mul_self_eq_one_of_orderOf_eq_two hβ2))

open CFSG.Sporadic.SmallOddCore (AutModel) in
theorem autModel_map_eqLocus {M : Type*} [Group M] {P R : Subgroup M} (hm : AutModel P R)
    (β : MulAut P) :
    (β.toMonoidHom.eqLocus (MonoidHom.id P)).map P.subtype =
      P ⊓ centralizer ({hm.hom β} : Set M) := by
  ext y
  simp only [mem_map, mem_inf, mem_centralizer_singleton_iff, coe_subtype]
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hp' : β p = p := hp
    have e := hm.elt_spec β p
    rw [hp', ← hm.hom_apply] at e
    refine ⟨p.2, ?_⟩
    calc (p : M) * hm.hom β = hm.hom β * p * (hm.hom β)⁻¹ * hm.hom β := by rw [← e]
      _ = hm.hom β * p := by group
  · rintro ⟨hy, hyx⟩
    refine ⟨⟨y, hy⟩, Subtype.ext ?_, rfl⟩
    change ((β ⟨y, hy⟩ : P) : M) = y
    rw [hm.elt_spec, ← hm.hom_apply, ← hyx, mul_inv_cancel_right]

open CFSG.Sporadic.SmallOddCore (AutModel) in
theorem autModel_hom_mem_iff {M : Type*} [Group M] {P R : Subgroup M} (hm : AutModel P R)
    (β : MulAut P) : hm.hom β ∈ P ↔ β ∈ inner P := by
  constructor
  · intro hx
    refine ⟨⟨hm.hom β, hx⟩, MulEquiv.ext fun p => Subtype.ext ?_⟩
    change ((⟨hm.hom β, hx⟩ : P) : M) * p * ((⟨hm.hom β, hx⟩ : P) : M)⁻¹ = ((β p : P) : M)
    rw [hm.elt_spec, ← hm.hom_apply]
  · rintro ⟨g, rfl⟩
    rw [hm.hom_apply, hm.elt_eq (hm.le g.2) fun p => rfl]
    exact g.2

open CFSG.Sporadic.SmallOddCore (AutModel) in
theorem autModel_exists_row {M : Type*} [Group M] {P R : Subgroup M} (hm : AutModel P R)
    {ι : Type*} (rows : List ι) (rep : ι → M) (cent : ι → ℕ) (out : ι → Bool)
    (hcover : ∀ t ∈ R, orderOf t = 2 → ∃ r ∈ rows, ∃ g ∈ P, t = g * rep r * g⁻¹)
    (hrows : ∀ r ∈ rows, (out r = true ↔ rep r ∉ P) ∧
      Nat.card ↥(P ⊓ centralizer ({rep r} : Set M)) = cent r)
    {D : Type} [Group D] (e : D ≃* P) (α : MulAut D) (hα : orderOf α = 2) :
    ∃ r ∈ rows, Nat.card (α.toMonoidHom.eqLocus (MonoidHom.id D)) = cent r ∧
      (out r = true ↔ α ∉ inner D) := by
  set β := MulAut.congr e α
  have hβ : orderOf β = 2 := (orderOf_congr e α).trans hα
  have hx2 : orderOf (hm.hom β) = 2 := by rw [orderOf_injective _ hm.hom_injective, hβ]
  obtain ⟨r, hr, g, hg, hxg⟩ := hcover _ (hm.elt_mem β) hx2
  rw [← hm.hom_apply] at hxg
  obtain ⟨hout, hcent⟩ := hrows r hr
  refine ⟨r, hr, ?_, ?_⟩
  · rw [card_eqLocus_congr e α, ← card_map_of_injective P.subtype_injective,
      autModel_map_eqLocus hm β, hxg, CFSG.Sporadic.SmallOddCore.inf_centralizer_conj P hg,
      card_map_of_injective (MulAut.conj g).injective, hcent]
  · rw [hout, ← congr_mem_inner_iff e α, ← autModel_hom_mem_iff hm, hxg]
    constructor
    · intro h hmem
      apply h
      have := P.mul_mem (P.mul_mem (P.inv_mem hg) hmem) hg
      rwa [show g⁻¹ * (g * rep r * g⁻¹) * g = rep r by group] at this
    · intro h hmem
      exact h (P.mul_mem (P.mul_mem hg hmem) (P.inv_mem hg))

theorem IsRankOneFixedRoot.false_of_card_centralizer_eq_twelve {D : Type} [Group D] [Finite D]
    {n : ℕ} {α : MulAut D} {S : Subgroup D} (h : IsRankOneFixedRoot n α S) {t : D}
    (hαt : MulAut.conj t = α) (ht : orderOf t = 2)
    (h12 : Nat.card (centralizer (S : Set D)) = 12) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  subst hαt
  set X := centralizer (S : Set D) with hX
  have hSt : S ≤ centralizer ({t} : Set D) := eqLocus_conj t ▸ h.2.2.1
  have htX : t ∈ X := by
    rw [hX, mem_centralizer_iff]
    intro s hs
    exact mem_centralizer_singleton_iff.1 (hSt hs)
  set t' : X := ⟨t, htX⟩
  have ht' : orderOf t' = 2 := by rw [Subgroup.orderOf_mk]; exact ht
  have hT : IsPGroup 2 (zpowers t') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht', pow_one])
  obtain ⟨P, hP⟩ := hT.exists_le_sylow
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp P.isPGroup'
  have hcop := P.card_coprime_index
  have hmul := (P : Subgroup X).card_mul_index
  rw [h12, hk] at hmul
  rw [hk] at hcop
  have h2P : 2 ∣ Nat.card (P : Subgroup X) := by
    have := orderOf_dvd_natCard (⟨t', hP (mem_zpowers t')⟩ : (P : Subgroup X))
    rwa [Subgroup.orderOf_mk, ht'] at this
  rw [hk] at h2P
  have hk2 : k = 2 := by
    have hk12 : 2 ^ k ∣ 12 := ⟨_, hmul.symm⟩
    have hle : k ≤ 3 := by
      by_contra hc
      have : 2 ^ 4 ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
      have := Nat.le_of_dvd (by norm_num) (this.trans hk12)
      norm_num at this
    interval_cases k
    · norm_num at h2P
    · exfalso
      have hi : (P : Subgroup X).index = 6 := by omega
      rw [hi] at hcop
      norm_num at hcop
    · rfl
    · exfalso
      omega
  rw [hk2] at hk
  have hPc : IsMulCommutative (P : Subgroup X) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) hk
  set Q := (P : Subgroup X).map X.subtype
  have hQle : Q ≤
      (MulAut.conj t).toMonoidHom.eqLocus (MonoidHom.id D) ⊓ centralizer (S : Set D) := by
    rintro _ ⟨x, hx, rfl⟩
    refine mem_inf.2 ⟨?_, x.2⟩
    rw [eqLocus_conj, mem_centralizer_singleton_iff]
    have hcomm := hPc.is_comm.comm (⟨x, hx⟩ : (P : Subgroup X)) ⟨t', hP (mem_zpowers t')⟩
    exact congrArg (fun z : (P : Subgroup X) => ((z : X) : D)) hcomm
  have hQp : IsPGroup 2 Q := P.isPGroup'.map X.subtype
  have hQcard : Nat.card Q = 4 := by
    rw [card_map_of_injective X.subtype_injective, hk]
    norm_num
  have := (h.2.2.2.2.2 Q hQle hQp).1
  omega

open CFSG.Sporadic.SmallOddCore
  (cti_j2_involution_local_components_ambient_centralizer_order_twelve) in
theorem j2_fixedRootFree :
    SporadicFixedRootFree .J2 := by
  intro D _ _ hD hs n α S h
  obtain ⟨e⟩ := hs
  by_cases hα : α ∈ inner D
  · obtain ⟨t, ht, hαt⟩ :=
      exists_involution_of_mem_inner (h.center_eq_bot_of_isSimpleGroup hD) h.2.1 hα
    have hcomp : CFSG.Assembly.IsComponentOf S (centralizer ({t} : Set D)) := by
      have := h.isComponentOf
      rwa [← hαt, eqLocus_conj] at this
    exact h.false_of_card_centralizer_eq_twelve hαt ht
      (cti_j2_involution_local_components_ambient_centralizer_order_twelve ⟨e⟩ ht hcomp)
  · set e' : D ≃* CFSG.ComponentClassification.J2Cover.P :=
      e.trans CFSG.ComponentClassification.J2Cover.nativeEquivP
    have hβ2 : orderOf (MulAut.congr e' α) = 2 := (orderOf_congr e' α).trans h.2.1
    have hβout : MulAut.congr e' α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner
        CFSG.ComponentClassification.J2Cover.P :=
      fun hb => hα ((congr_mem_inner_iff e' α).1 hb)
    obtain ⟨g, hg⟩ :=
      CFSG.ComponentClassification.J2Cover.External.exists_conj_beta_of_outer hβ2 hβout
    have hcard : Nat.card (α.toMonoidHom.eqLocus (MonoidHom.id D)) = 336 := by
      rw [card_eqLocus_congr e' α, eqLocus_eq_fixSub, hg]
      exact CFSG.ComponentClassification.J2Cover.External.card_fixSub_conj_beta g
    obtain ⟨hdvd, -⟩ := h.two_pow_dvd (a := 0) (by simp)
    rw [hcard] at hdvd
    have := lt_of_sl2Order_dvd (by norm_num) (show 336 < 2 ^ 9 by norm_num) hdvd
    have := h.1
    interval_cases n <;> norm_num at hdvd

theorem j3_fixedRootFree :
    SporadicFixedRootFree .J3 := by
  intro D _ _ hD hs n α S h
  obtain ⟨e⟩ := hs
  obtain ⟨-, -, -, hrows, hcover, -, hmap, -⟩ :=
    CFSG.Sporadic.SmallOddCore.ctuc_j3_all_involution_fixed_subgroups_odd_core_trivial
  obtain ⟨r, hr, hcard, hout⟩ := autModel_exists_row CFSG.Sporadic.SmallOddCore.j3_autModel
    CFSG.Sporadic.SmallOddCore.j3Rows (fun r => CFSG.Sporadic.SmallOddCore.tp 6156 r.rep)
    CFSG.Sporadic.SmallOddCore.ClassRow.centOrder CFSG.Sporadic.SmallOddCore.ClassRow.outer
    hcover (fun r hr => ⟨(hrows r hr).2.2.1, (hrows r hr).2.2.2.2.1⟩)
    (e.trans CFSG.Sporadic.Schreier.j3PermEquiv) α h.2.1
  have hmem := List.mem_map_of_mem (f := fun r : CFSG.Sporadic.SmallOddCore.ClassRow =>
    (r.outer, r.classSize, r.centOrder)) hr
  rw [hmap] at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
  have := h.1
  rcases hmem with ⟨-, -, hc⟩ | ⟨-, -, hc⟩
  · rw [hc] at hcard
    obtain ⟨hdvd, h2, -⟩ := h.two_pow_dvd (a := 7) (by rw [hcard]; norm_num)
    rw [hcard] at hdvd
    have := lt_of_sl2Order_dvd (by norm_num) (show 1920 < 2 ^ 11 by norm_num) hdvd
    interval_cases n <;> revert hdvd h2 <;> norm_num
  · rw [hc] at hcard
    obtain ⟨hdvd, -⟩ := h.two_pow_dvd (a := 0) (by simp)
    rw [hcard] at hdvd
    have := lt_of_sl2Order_dvd (by norm_num) (show 2448 < 2 ^ 12 by norm_num) hdvd
    interval_cases n <;> norm_num at hdvd

theorem hs_fixedRootFree :
    SporadicFixedRootFree .HS := by
  intro D _ _ hD hs n α S h
  obtain ⟨e⟩ := hs
  have := h.1
  by_cases hα : α ∈ inner D
  · obtain ⟨t, ht, hαt⟩ :=
      exists_involution_of_mem_inner (h.center_eq_bot_of_isSimpleGroup hD) h.2.1 hα
    have hcomp : CFSG.Assembly.IsComponentOf S (centralizer ({t} : Set D)) := by
      have := h.isComponentOf
      rwa [← hαt, eqLocus_conj] at this
    obtain ⟨-, -, h360⟩ :=
      CFSG.Sporadic.SmallOddCore.cti_hs_involution_local_components_simple_order_360 ⟨e⟩ ht hcomp
    rw [h.card] at h360
    have := lt_of_sl2Order_eq (by omega) (show 360 < 2 ^ 9 by norm_num) h360
    interval_cases n <;> norm_num at h360
  · obtain ⟨-, -, -, hrows, hcover, -, hmap, -⟩ :=
      CFSG.Sporadic.SmallOddCore.hs_involution_centralizers
    obtain ⟨r, hr, hcard, hout⟩ := autModel_exists_row CFSG.Sporadic.SmallOddCore.hs_autModel
      CFSG.Sporadic.SmallOddCore.hsRows (fun r => CFSG.Sporadic.SmallOddCore.tp 3850 r.rep)
      CFSG.Sporadic.SmallOddCore.ClassRow.centOrder CFSG.Sporadic.SmallOddCore.ClassRow.outer
      hcover (fun r hr => ⟨(hrows r hr).2.2.1, (hrows r hr).2.2.2.2.1⟩)
      (e.trans CFSG.Sporadic.Schreier.hsPermEquiv) α h.2.1
    have hmem := List.mem_map_of_mem (f := fun r : CFSG.Sporadic.SmallOddCore.ClassRow =>
      (r.outer, r.classSize, r.centOrder)) hr
    rw [hmap] at hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨ho, -, -⟩ | ⟨ho, -, -⟩ | ⟨-, -, hc⟩ | ⟨-, -, hc⟩
    · exact absurd (hout.2 hα) (by rw [ho]; simp)
    · exact absurd (hout.2 hα) (by rw [ho]; simp)
    · rw [hc] at hcard
      obtain ⟨hdvd, -, h2⟩ := h.two_pow_dvd (a := 7) (by rw [hcard]; norm_num)
      have h2 := h2 hα
      rw [hcard] at hdvd
      have := lt_of_sl2Order_dvd (by norm_num) (show 40320 < 2 ^ 16 by norm_num) hdvd
      interval_cases n <;> revert hdvd h2 <;> norm_num
    · rw [hc] at hcard
      obtain ⟨hdvd, -, h2⟩ := h.two_pow_dvd (a := 7) (by rw [hcard]; norm_num)
      have h2 := h2 hα
      rw [hcard] at hdvd
      have := lt_of_sl2Order_dvd (by norm_num) (show 1920 < 2 ^ 11 by norm_num) hdvd
      interval_cases n <;> revert hdvd h2 <;> norm_num

theorem mcl_fixedRootFree :
    SporadicFixedRootFree .McL := by
  have hSLi : ∀ n : ℕ, 2 ≤ n → ∀ (K : Type) [Field K] [Fintype K], Fintype.card K = 2 ^ n →
      ¬ Nonempty (Matrix.SpecialLinearGroup (Fin 2) K ⧸
        center (Matrix.SpecialLinearGroup (Fin 2) K) ≃* mclX) := by
    intro n hn K _ _ hK ⟨θ⟩
    have h1 := Nat.card_congr θ.toEquiv
    have hX : Nat.card mclX = 20160 := CFSG.Sporadic.SmallOddCore.card_mclX
    rw [card_sl2_quotient_center (by omega) hK, hX] at h1
    have := lt_of_sl2Order_eq (by omega) (show 20160 < 2 ^ 15 by norm_num) h1
    interval_cases n <;> norm_num at h1
  have hSLo : ∀ n : ℕ, 2 ≤ n → ∀ (K : Type) [Field K] [Fintype K], Fintype.card K = 2 ^ n →
      ¬ Nat.card (Matrix.SpecialLinearGroup (Fin 2) K ⧸
        center (Matrix.SpecialLinearGroup (Fin 2) K)) ∈ ({7920} : Set ℕ) := by
    intro n hn K _ _ hK h
    rw [Set.mem_singleton_iff, card_sl2_quotient_center (by omega) hK] at h
    have := lt_of_sl2Order_eq (by omega) (show 7920 < 2 ^ 13 by norm_num) h
    interval_cases n <;> norm_num at h
  exact sporadicFixedRootFree_of_comps (isoInvariant_quotient_center_equiv mclX)
    (isoInvariant_card_quotient_center _) hSLi hSLo (fun G _ _ ⟨e⟩ t ht => mcl_inner_comps e t ht)
    (fun G _ _ _ ⟨e⟩ β hβ2 hβ => mcl_outer_comps e β (mul_self_eq_one_of_orderOf_eq_two hβ2) hβ)

theorem he_fixedRootFree :
    SporadicFixedRootFree .He := by
  intro D _ _ hD hs n α S h
  obtain ⟨e⟩ := hs
  have := h.1
  by_cases hα : α ∈ inner D
  · obtain ⟨t, ht, hαt⟩ :=
      exists_involution_of_mem_inner (h.center_eq_bot_of_isSimpleGroup hD) h.2.1 hα
    have hcomp : CFSG.Assembly.IsComponentOf S (centralizer ({t} : Set D)) := by
      have := h.isComponentOf
      rwa [← hαt, eqLocus_conj] at this
    have h20160 :=
      CFSG.Sporadic.SmallOddCore.cti_he_involution_local_components_simple_quotient_order ⟨e⟩ ht
        hcomp
    rw [h.card_quotient_center] at h20160
    have := lt_of_sl2Order_eq (by omega) (show 20160 < 2 ^ 15 by norm_num) h20160
    interval_cases n <;> norm_num at h20160
  · set θ : D ≃* CFSG.Sporadic.HeldB.heP := e.trans CFSG.Sporadic.HeldB.heEquivP
    have hγ2 : orderOf (MulAut.congr θ α) = 2 := (orderOf_congr θ α).trans h.2.1
    have hγout : MulAut.congr θ α ∉
        (MulAut.conj : CFSG.Sporadic.HeldB.heP →* MulAut CFSG.Sporadic.HeldB.heP).range :=
      fun hb => hα ((congr_mem_inner_iff θ α).1 hb)
    obtain ⟨x, hx, hxP, hx2⟩ := CFSG.Sporadic.HeldB.exists_heConjR_eq
      CFSG.Sporadic.HeldB.ctbh_full_automorphism_permutation_model.1 _ hγ2 hγout
    obtain ⟨g, hg, hxg⟩ := CFSG.Sporadic.HeldB.exists_conj_heAutU x.2 hxP hx2
    have hfix : (MulAut.congr θ α).toMonoidHom.eqLocus (MonoidHom.id CFSG.Sporadic.HeldB.heP) =
        CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup
          (CFSG.Sporadic.HeldB.heConjR x) := by
      rw [hx]
      ext y
      rfl
    have hcard : Nat.card (α.toMonoidHom.eqLocus (MonoidHom.id D)) = 15120 := by
      rw [card_eqLocus_congr θ α, hfix,
        Nat.card_congr (CFSG.Sporadic.HeldB.fixedSubgroupEquivOfConj x hg _ hxg).toEquiv,
        CFSG.Sporadic.HeldB.card_heP_centralizer_heAutU]
    obtain ⟨hdvd, -, h2⟩ := h.two_pow_dvd (a := 4) (by rw [hcard]; norm_num)
    have h2 := h2 hα
    rw [hcard] at hdvd
    have := lt_of_sl2Order_dvd (by norm_num) (show 15120 < 2 ^ 14 by norm_num) hdvd
    interval_cases n <;> revert hdvd h2 <;> norm_num

theorem ru_fixedRootFree :
    SporadicFixedRootFree .Ru :=
  sporadicFixedRootFree_of_comps isoInvariant_not_three_dvd isoInvariant_not_three_dvd
    sl2_fails_not_three_dvd sl2_fails_not_three_dvd (fun _ _ _ ⟨e⟩ t ht =>
      compsSatisfy_centralizer_of_mulEquiv _ isoInvariant_not_three_dvd ru_centralizerIn_comps
        (e.trans CFSG.Sporadic.RuSchreier.ruEquivP) t ht)
    (outer_comps_of_forall_inner (s := .Ru) (mem_inner_of_mulEquiv
      CFSG.Sporadic.RuSchreier.ruEquivP CFSG.Sporadic.RuSchreier.mulAut_inner) _)

theorem coe_mulAut_conj_mk {G : Type*} [Group G] {M : Subgroup G} {g : G} (hg : g ∈ M) (m : M) :
    ((MulAut.conj (⟨g, hg⟩ : M) m : M) : G) = g * m * g⁻¹ := rfl

open CFSG.Sporadic.SuzOddCore in
theorem suz_outer_card
    {D : Type} [Group D] (e : D ≃* NativeSporadic.Suz)
    (α : MulAut D) (hα : orderOf α = 2) (hout : α ∉ inner D) :
    Nat.card (α.toMonoidHom.eqLocus (MonoidHom.id D)) = 190080 ∨
      Nat.card (α.toMonoidHom.eqLocus (MonoidHom.id D)) = 1209600 := by
  set θ : D ≃* suzM := e.trans suzEquivM
  set β := MulAut.congr θ α
  have hβ : orderOf β = 2 := (orderOf_congr θ α).trans hα
  have hβout : β ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner suzM :=
    fun hb => hout ((congr_mem_inner_iff θ α).1 hb)
  obtain ⟨x, hx⟩ := suzConjT_bijective.2 β
  have hx2 : orderOf (x : Equiv.Perm (Fin 1782)) = 2 := by
    rw [Subgroup.orderOf_coe, ← orderOf_injective suzConjT suzConjT_bijective.1, hx, hβ]
  have hxM : (x : Equiv.Perm (Fin 1782)) ∉ suzM := by
    intro hm
    apply hβout
    refine ⟨⟨x, hm⟩, ?_⟩
    rw [← hx]
    refine MulEquiv.ext fun m => Subtype.ext ?_
    rw [suzConjT_apply, coe_mulAut_conj_mk]
  have hmap : (β.toMonoidHom.eqLocus (MonoidHom.id suzM)).map suzM.subtype =
      suzM ⊓ centralizer ({(x : Equiv.Perm (Fin 1782))} : Set _) := by
    ext y
    simp only [mem_map, mem_inf, mem_centralizer_singleton_iff, coe_subtype]
    constructor
    · rintro ⟨m, hm, rfl⟩
      have hm' : β m = m := hm
      rw [← hx] at hm'
      have h1 := congrArg Subtype.val hm'
      rw [suzConjT_apply] at h1
      refine ⟨m.2, ?_⟩
      calc (m : Equiv.Perm (Fin 1782)) * x = x * m * (x : Equiv.Perm (Fin 1782))⁻¹ * x := by
            rw [h1]
        _ = x * m := by group
    · rintro ⟨hy, hyx⟩
      refine ⟨⟨y, hy⟩, ?_, rfl⟩
      change β ⟨y, hy⟩ = ⟨y, hy⟩
      rw [← hx]
      apply Subtype.ext
      rw [suzConjT_apply]
      change (x : Equiv.Perm (Fin 1782)) * y * (x : Equiv.Perm (Fin 1782))⁻¹ = y
      rw [← hyx, mul_inv_cancel_right]
  obtain ⟨i, ⟨hi, c, hc, hcx⟩, -⟩ := suzT_involution_class x.2 hx2
  obtain ⟨-, -, -, -, -, h0, h1, -, -, -, hDE, -, -, -, -, -, -, hE2, hE3, -⟩ :=
    CTUC_Suz_four_exact_involution_centralizers
  have hi2 : 2 ≤ i := by
    by_contra hlt
    have hmem : suzInv i ∈ suzM := by
      interval_cases i
      · exact h0
      · exact h1
    exact hxM (hcx ▸ suzT_conj_mem' hc hmem)
  have hconj : (suzM ⊓ centralizer ({suzInv i} : Set _)).map (MulAut.conj c).toMonoidHom =
      suzM ⊓ centralizer ({(x : Equiv.Perm (Fin 1782))} : Set _) := by
    rw [← hcx]
    ext y
    simp only [mem_map, mem_inf, mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    constructor
    · rintro ⟨z, ⟨hzM, hzt⟩, rfl⟩
      refine ⟨suzT_conj_mem' hc hzM, ?_⟩
      calc c * z * c⁻¹ * (c * suzInv i * c⁻¹) = c * (z * suzInv i) * c⁻¹ := by group
        _ = c * (suzInv i * z) * c⁻¹ := by rw [hzt]
        _ = c * suzInv i * c⁻¹ * (c * z * c⁻¹) := by group
    · rintro ⟨hyM, hyt⟩
      refine ⟨c⁻¹ * y * c, ⟨?_, ?_⟩, by group⟩
      · have := suzT_conj_mem' (suzT.inv_mem hc) hyM
        rwa [inv_inv] at this
      · calc c⁻¹ * y * c * suzInv i = c⁻¹ * (y * (c * suzInv i * c⁻¹)) * c := by group
          _ = c⁻¹ * ((c * suzInv i * c⁻¹) * y) * c := by rw [hyt]
          _ = suzInv i * (c⁻¹ * y * c) := by group
  have hcard : Nat.card (α.toMonoidHom.eqLocus (MonoidHom.id D)) = Nat.card (invE i) := by
    rw [card_eqLocus_congr θ α, ← card_map_of_injective suzM.subtype_injective, hmap, ← hconj,
      card_map_of_injective (MulAut.conj c).injective, (hDE i hi).2, centM, inf_comm]
  interval_cases i
  · exact Or.inl (hcard.trans hE2)
  · exact Or.inr (hcard.trans hE3)

theorem suz_fixedRootFree :
    SporadicFixedRootFree .Suz := by
  intro D _ _ hD hs n α S h
  obtain ⟨e⟩ := hs
  have := h.1
  by_cases hα : α ∈ inner D
  · refine h.false_of_inner_comps hD hα (isoInvariant_card_quotient_center {20160})
      (fun K _ _ hK h' => ?_) (fun t ht B hB => ?_)
    · rw [Set.mem_singleton_iff, card_sl2_quotient_center (by omega) hK] at h'
      have := lt_of_sl2Order_eq (by omega) (show 20160 < 2 ^ 15 by norm_num) h'
      interval_cases n <;> norm_num at h'
    · exact CFSG.Sporadic.SuzOddCore.CTI_Suz_involution_local_components_simple_quotient_order e
        t ht B hB
  · rcases suz_outer_card e α h.2.1 hα with hcard | hcard
    · obtain ⟨hdvd, -, h2⟩ := h.two_pow_dvd (a := 7) (by rw [hcard]; norm_num)
      have h2 := h2 hα
      rw [hcard] at hdvd
      have := lt_of_sl2Order_dvd (by norm_num) (show 190080 < 2 ^ 18 by norm_num) hdvd
      interval_cases n <;> revert hdvd h2 <;> norm_num
    · obtain ⟨hdvd, -, h2⟩ := h.two_pow_dvd (a := 8) (by rw [hcard]; norm_num)
      have h2 := h2 hα
      rw [hcard] at hdvd
      have := lt_of_sl2Order_dvd (by norm_num) (show 1209600 < 2 ^ 21 by norm_num) hdvd
      interval_cases n <;> revert hdvd h2 <;> norm_num

end CFSG.LocalAnalysis.EvenBN.GMSK.Sporadic
