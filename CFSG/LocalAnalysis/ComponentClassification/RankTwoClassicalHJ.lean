module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalM12
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalJ2
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicActionHom
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ2
public import CFSG.Sporadic.J2
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.RankThree.PartTwo.KFacts.KS14MultCore
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicGenCensus
public import CFSG.Monster.Code.Weights

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.Blueprint
open CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.RankTwoSporadic
open CFSG.ComponentClassification.AschbacherTightEmbedding
open scoped commutatorElement

theorem carrier_j2_not_comm :
    ¬ ∀ a b : NativeSporadic.Carrier .J2, a * b = b * a := by
  intro hc
  have hs : IsSimpleGroup (NativeSporadic.Carrier .J2) := CFSG.Sporadic.J2.fam_j2_simplicity.2.2
  have hf : Finite (NativeSporadic.Carrier .J2) := CFSG.Sporadic.J2.fam_j2_simplicity.1
  let _ : CommGroup (NativeSporadic.Carrier .J2) :=
    { (inferInstance : Group (NativeSporadic.Carrier .J2)) with mul_comm := hc }
  have hp := IsSimpleGroup.prime_card (α := NativeSporadic.Carrier .J2)
  have hcard : Nat.card (NativeSporadic.Carrier .J2) = 604800 := CFSG.Sporadic.J2.card_J2
  rw [hcard] at hp
  norm_num at hp

theorem isPerfect_carrier_j2 :
    Group.IsPerfect (NativeSporadic.Carrier .J2) := by
  have hs : IsSimpleGroup (NativeSporadic.Carrier .J2) := CFSG.Sporadic.J2.fam_j2_simplicity.2.2
  rw [Group.isPerfect_def]
  rcases hs.eq_bot_or_eq_top_of_normal (commutator (NativeSporadic.Carrier .J2)) with h | h
  · exfalso
    apply carrier_j2_not_comm
    intro a b
    have h1 : ⁅a, b⁆ ∈ commutator (NativeSporadic.Carrier .J2) :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h, Subgroup.mem_bot] at h1
    exact commutatorElement_eq_one_iff_mul_comm.1 h1
  · exact h

theorem card_alternatingGroup_five : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

theorem center_eq_bot_of_a5 {L : Type} [Group L] [Finite L] (hq : CFSG.Open.IsQuasisimple L)
    (hZ : Odd (Nat.card (center L))) (hA5 : Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 5))) :
    center L = ⊥ ∧ Nat.card L = 60 := by
  obtain ⟨e⟩ := hA5
  have hcard : Nat.card (L ⧸ center L) = 60 := by
    rw [Nat.card_congr e.toEquiv, card_alternatingGroup_five]
  have : Group.IsPerfect L := (Group.isPerfect_def).2 hq.1
  have hbot : center L = ⊥ := by
    refine CFSG.RankThree.PartTwo.KFacts.KS14.eq_bot_of_isPerfect_of_sylow_comm le_rfl ?_
    intro p hp hpZ P
    have : Fact p.Prime := ⟨hp⟩
    refine CFSG.RankThree.PartTwo.KFacts.KS14.sylow_comm_of_not_sq_dvd le_rfl ?_ P
    rw [hcard]
    intro hdvd
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hZ) (even_iff_two_dvd.mpr hpZ)
    have hp7 : p ≤ 7 := by
      have h1 := Nat.le_of_dvd (by norm_num) hdvd
      nlinarith
    interval_cases p <;> first | omega | exact absurd hp (by norm_num)
  refine ⟨hbot, ?_⟩
  rw [(center L).card_eq_card_quotient_mul_card_subgroup, hcard, hbot, card_bot]

section Action

variable {H : Type} [Group H]

theorem mem_of_commute_five
    {X : Subgroup H} [hXn : X.Normal] (hJ : NativeSporadic.IsSporadic X .J2)
    (hC : centralizer (X : Set H) = ⊥) {t x : H} (ht : t ^ 2 = 1) (hx : x ∈ X)
    (hx5 : orderOf x = 5) (htx : t * x = x * t) : t ∈ X := by
  obtain ⟨f⟩ := hJ
  have hperf : commutator ↥X = ⊤ := by
    have := isPerfect_carrier_j2
    exact (Group.isPerfect_def).mp
      (Group.IsPerfect.ofSurjective (f := f.symm.toMonoidHom) f.symm.surjective)
  have hZ : center ↥X = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [mem_bot]
    have hzC : (z : H) ∈ centralizer (X : Set H) := by
      rw [mem_centralizer_iff]
      intro y hy
      exact congrArg Subtype.val (mem_center_iff.mp hz ⟨y, hy⟩)
    rw [hC, mem_bot] at hzC
    exact Subtype.ext hzC
  let e : ↥X ⧸ center ↥X ≃* NativeSporadic.Carrier .J2 :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans (QuotientGroup.quotientBot.trans f)
  obtain ⟨ψ, hψ⟩ := exists_isActionHom J2.j2AutModel hperf e
  have hN : ∀ h : H, h ∈ normalizer (X : Set H) := fun h => by
    rw [normalizer_eq_top_iff.mpr hXn]
    exact mem_top h
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro a ha
    rw [MonoidHom.mem_ker, hψ.eq_one_iff, hC, mem_bot] at ha
    exact (mem_bot).mpr (Subtype.ext ha)
  set t' := ψ ⟨t, hN t⟩ with ht'
  set x' := ψ ⟨x, hN x⟩ with hx'
  have hx'P : x' ∈ J2Cover.P.subgroupOf J2Cover.R := hψ.map_mem x hx
  have ht'2 : (t' : Equiv.Perm (Fin 315)) ^ 2 = 1 := by
    have h1 : (⟨t, hN t⟩ : normalizer (X : Set H)) ^ 2 = 1 := Subtype.ext (by simpa using ht)
    have h2 : t' ^ 2 = 1 := by rw [ht', ← map_pow, h1, map_one]
    simpa using congrArg Subtype.val h2
  have hcomm : (t' : Equiv.Perm (Fin 315)) * x' = x' * t' := by
    have h1 : t' * x' = x' * t' := by
      rw [ht', hx', ← map_mul, ← map_mul]
      exact congrArg ψ (Subtype.ext htx)
    simpa using congrArg Subtype.val h1
  have ho : orderOf (x' : Equiv.Perm (Fin 315)) = 5 := by
    rw [Subgroup.orderOf_coe, hx', orderOf_injective ψ hinj, Subgroup.orderOf_mk, hx5]
  have hmem := J2Std.mem_P_of_commute t'.2 ht'2 (mem_subgroupOf.mp hx'P) ho hcomm
  obtain ⟨b, hb, hbt⟩ := hψ.exists_eq t' (mem_subgroupOf.mpr hmem)
  have hbt' := hinj hbt
  have : b = t := congrArg Subtype.val hbt'
  rw [← this]
  exact hb

end Action

@[expose] def StdIn (X₀ : Type) [Group X₀] : Prop :=
  ∀ (y : X₀) (V Λ : Subgroup X₀), orderOf y = 5 → IsPGroup 2 V → 4 ≤ Nat.card V →
    V ≤ centralizer ({y} : Set X₀) → y ∈ Λ → Nat.card Λ = 60 → V ≤ centralizer (Λ : Set X₀) →
    ∃ c ∈ ⁅centralizer ({y} : Set X₀), centralizer ({y} : Set X₀)⁆, ∃ v ∈ V,
      c * v * c⁻¹ ∉ centralizer (Λ : Set X₀)

theorem centralizer_singleton_map_equiv {X₀ X₁ : Type*} [Group X₀] [Group X₁] (e : X₀ ≃* X₁)
    (y : X₀) : (centralizer ({y} : Set X₀)).map e.toMonoidHom = centralizer ({e y} : Set X₁) := by
  ext x
  obtain ⟨x, rfl⟩ := e.surjective x
  rw [mem_map_equiv, MulEquiv.symm_apply_apply, mem_centralizer_singleton_iff,
    mem_centralizer_singleton_iff]
  constructor
  · intro h
    rw [← map_mul, ← map_mul, h]
  · intro h
    apply e.injective
    rw [map_mul, map_mul, h]

theorem stdIn_of_equiv {X₀ X₁ : Type} [Group X₀] [Group X₁] (h : StdIn X₁) (e : X₀ ≃* X₁) :
    StdIn X₀ := by
  intro y V Λ hy hV2 hV4 hVy hyΛ hΛ hVΛ
  have hcV : Nat.card (V.map e.toMonoidHom) = Nat.card V := card_map_of_injective e.injective
  have hcΛ : Nat.card (Λ.map e.toMonoidHom) = Nat.card Λ := card_map_of_injective e.injective
  have hC := centralizer_singleton_map_equiv e y
  have hCΛ := centralizer_map_equiv e Λ
  obtain ⟨c, hc, v', hv', hcv⟩ := h (e y) (V.map e.toMonoidHom) (Λ.map e.toMonoidHom)
    (by rw [MulEquiv.orderOf_eq, hy]) (hV2.map _)
    (by rw [hcV]; exact hV4) (by rw [← hC]; exact map_mono hVy) ⟨y, hyΛ, rfl⟩
    (by rw [hcΛ]; exact hΛ) (by rw [hCΛ]; exact map_mono hVΛ)
  rw [← hC, ← map_commutator] at hc
  obtain ⟨c₀, hc₀, rfl⟩ := hc
  obtain ⟨v, hv, rfl⟩ := hv'
  refine ⟨c₀, hc₀, v, hv, fun hmem => hcv ?_⟩
  rw [hCΛ]
  exact ⟨c₀ * v * c₀⁻¹, hmem, by simp⟩

theorem stdIn_gJ (hJ : J2Std.J2StdFacts) :
    StdIn CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.GJ :=
  fun y V Λ hy => hJ y hy V Λ

theorem stdIn_of_isSporadic
    (hJ : J2Std.J2StdFacts) {X₀ : Type} [Group X₀] (h : NativeSporadic.IsSporadic X₀ .J2) :
    StdIn X₀ := by
  obtain ⟨f⟩ := h
  exact stdIn_of_equiv (stdIn_gJ hJ) (f.trans J2Cover.nativeEquivP)

theorem comm_of_central_displacements {Q : Type*} [Group Q] {a b x α β : Q}
    (h1 : a * x * a⁻¹ = α * x) (h2 : b * x * b⁻¹ = β * x) (hαa : Commute α a)
    (hαb : Commute α b) (hβa : Commute β a) (hβb : Commute β b) (hαβ : Commute α β) :
    ⁅a, b⁆ * x = x * ⁅a, b⁆ := by
  have h1' : a⁻¹ * x * a = α⁻¹ * x := by
    have : x = a⁻¹ * (α * x) * a := by rw [← h1]; group
    calc a⁻¹ * x * a = a⁻¹ * (α⁻¹ * (α * x)) * a := by group
      _ = α⁻¹ * (a⁻¹ * (α * x) * a) := by
          rw [show a⁻¹ * (α⁻¹ * (α * x)) * a = (a⁻¹ * α⁻¹) * ((α * x) * a) by group,
            ← (hαa.inv_inv).eq]
          group
      _ = α⁻¹ * x := by rw [← this]
  have h2' : b⁻¹ * x * b = β⁻¹ * x := by
    have : x = b⁻¹ * (β * x) * b := by rw [← h2]; group
    calc b⁻¹ * x * b = b⁻¹ * (β⁻¹ * (β * x)) * b := by group
      _ = β⁻¹ * (b⁻¹ * (β * x) * b) := by
          rw [show b⁻¹ * (β⁻¹ * (β * x)) * b = (b⁻¹ * β⁻¹) * ((β * x) * b) by group,
            ← (hβb.inv_inv).eq]
          group
      _ = β⁻¹ * x := by rw [← this]
  have key : ⁅a, b⁆ * x * ⁅a, b⁆⁻¹ = x := by
    calc ⁅a, b⁆ * x * ⁅a, b⁆⁻¹ = a * (b * (a⁻¹ * (b⁻¹ * x * b) * a) * b⁻¹) * a⁻¹ := by
          rw [commutatorElement_def]; group
      _ = a * (b * (a⁻¹ * (β⁻¹ * x) * a) * b⁻¹) * a⁻¹ := by rw [h2']
      _ = a * (b * (β⁻¹ * (a⁻¹ * x * a)) * b⁻¹) * a⁻¹ := by
          rw [show a⁻¹ * (β⁻¹ * x) * a = (a⁻¹ * β⁻¹) * x * a by group,
            ← (hβa.inv_inv).eq]
          group
      _ = a * (b * (β⁻¹ * (α⁻¹ * x)) * b⁻¹) * a⁻¹ := by rw [h1']
      _ = a * (β⁻¹ * α⁻¹ * (b * x * b⁻¹)) * a⁻¹ := by
          rw [show b * (β⁻¹ * (α⁻¹ * x)) * b⁻¹ = (b * β⁻¹) * (α⁻¹ * x) * b⁻¹ by group,
            ← hβb.inv_left.eq,
            show β⁻¹ * b * (α⁻¹ * x) * b⁻¹ = β⁻¹ * ((b * α⁻¹) * x * b⁻¹) by group,
            ← hαb.inv_left.eq]
          group
      _ = a * (β⁻¹ * α⁻¹ * (β * x)) * a⁻¹ := by rw [h2]
      _ = a * (α⁻¹ * x) * a⁻¹ := by
          rw [show β⁻¹ * α⁻¹ * (β * x) = β⁻¹ * (α⁻¹ * β) * x by group,
            (hαβ.inv_left).eq]
          group
      _ = α⁻¹ * (a * x * a⁻¹) := by
          rw [show a * (α⁻¹ * x) * a⁻¹ = (a * α⁻¹) * x * a⁻¹ by group,
            ← hαa.inv_left.eq]
          group
      _ = x := by rw [h1]; group
  calc ⁅a, b⁆ * x = ⁅a, b⁆ * x * ⁅a, b⁆⁻¹ * ⁅a, b⁆ := by group
    _ = x * ⁅a, b⁆ := by rw [key]

section Quotient

variable {Q : Type} [Group Q] [Finite Q]

local notation "O" => standardComponentOddCore Q
local notation "π" => QuotientGroup.mk' (standardComponentOddCore Q)

omit [Finite Q] in
theorem map_normalClosure_mk' (M : Subgroup Q) :
    (normalClosure (M : Set Q)).map π = rankTwoX (M.map π) := by
  rw [map_normalClosure _ _ (QuotientGroup.mk'_surjective _), rankTwoX, coe_map]

theorem oddCore_le_centralizer_normalClosure {M : Subgroup Q} (hH : RankTwoHyp Q M) :
    O ≤ centralizer (normalClosure (M : Set Q) : Set Q) := by
  rw [← le_centralizer_iff]
  exact normalClosure_le_normal (le_centralizer_iff.mp (oddCore_le_of_rankTwoHyp hH))

theorem inf_oddCore_eq_bot {M : Subgroup Q} (hH : RankTwoHyp Q M) (hZ : center ↥M = ⊥) :
    M ⊓ O = ⊥ := by
  rw [eq_bot_iff]
  intro m hm
  obtain ⟨hmM, hmO⟩ := mem_inf.mp hm
  have hc : (⟨m, hmM⟩ : ↥M) ∈ center ↥M := by
    rw [mem_center_iff]
    intro z
    exact Subtype.ext ((mem_centralizer_iff.mp (oddCore_le_of_rankTwoHyp hH hmO)) z z.2)
  rw [hZ, mem_bot] at hc
  exact (mem_bot).mpr (congrArg Subtype.val hc)

omit [Finite Q] in
theorem mk'_injOn_of_inf {M : Subgroup Q} (hMO : M ⊓ O = ⊥) {x y : Q} (hx : x ∈ M)
    (hy : y ∈ M) (h : π x = π y) : x = y := by
  have h1 : x⁻¹ * y ∈ M ⊓ O := by
    rw [mem_inf]
    refine ⟨mul_mem (inv_mem hx) hy, ?_⟩
    rw [← QuotientGroup.ker_mk' O, MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  rw [hMO, mem_bot, inv_mul_eq_one] at h1
  exact h1

omit [Finite Q] in
theorem card_map_mk'_of_inf {M : Subgroup Q} (hMO : M ⊓ O = ⊥) :
    Nat.card (M.map π) = Nat.card M :=
  (Nat.card_congr (Equiv.ofBijective ((QuotientGroup.mk' O).subgroupMap M)
    ⟨fun x y hxy => Subtype.ext (mk'_injOn_of_inf hMO x.2 y.2 (congrArg Subtype.val hxy)),
      (QuotientGroup.mk' O).subgroupMap_surjective M⟩)).symm

theorem commutator_lift {M : Subgroup Q} (hH : RankTwoHyp Q M) {x : Q} (hxM : x ∈ M)
    {c : Q ⧸ O} (hc : c ∈ ⁅rankTwoX (M.map π) ⊓ centralizer ({π x} : Set (Q ⧸ O)),
      rankTwoX (M.map π) ⊓ centralizer ({π x} : Set (Q ⧸ O))⁆) :
    ∃ c' ∈ centralizer ({x} : Set Q), π c' = c := by
  set B := normalClosure (M : Set Q) with hBdef
  have hOB := oddCore_le_centralizer_normalClosure hH
  set C := B ⊓ (centralizer ({π x} : Set (Q ⧸ O))).comap π with hCdef
  have hCmap : C.map π = rankTwoX (M.map π) ⊓ centralizer ({π x} : Set (Q ⧸ O)) := by
    rw [← map_normalClosure_mk' M]
    apply le_antisymm
    · rintro _ ⟨a, ⟨haB, haC⟩, rfl⟩
      exact ⟨⟨a, haB, rfl⟩, haC⟩
    · rintro _ ⟨⟨a, haB, rfl⟩, haC⟩
      exact ⟨a, ⟨haB, haC⟩, rfl⟩
  have hxB : x ∈ B := subset_normalClosure hxM
  have hdisp : ∀ a ∈ C, a * x * a⁻¹ * x⁻¹ ∈ O ∧ a * x * a⁻¹ * x⁻¹ ∈ B := by
    intro a ha
    obtain ⟨haB, haC⟩ := mem_inf.mp ha
    refine ⟨?_, mul_mem (mul_mem (mul_mem haB hxB) (inv_mem haB)) (inv_mem hxB)⟩
    rw [← QuotientGroup.ker_mk' O, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv,
      map_inv]
    have h := mem_centralizer_singleton_iff.mp (mem_comap.mp haC)
    rw [h]
    group
  have hCx : ⁅C, C⁆ ≤ centralizer ({x} : Set Q) := by
    rw [commutator_le]
    intro a ha b hb
    obtain ⟨hαO, hαB⟩ := hdisp a ha
    obtain ⟨hβO, -⟩ := hdisp b hb
    have haB := (mem_inf.mp ha).1
    have hbB := (mem_inf.mp hb).1
    have hcomm : ∀ {o : Q}, o ∈ O → ∀ {y : Q}, y ∈ B → Commute o y := fun ho _ hy =>
      ((mem_centralizer_iff.mp (hOB ho)) _ hy).symm
    rw [mem_centralizer_singleton_iff]
    exact comm_of_central_displacements (α := a * x * a⁻¹ * x⁻¹) (β := b * x * b⁻¹ * x⁻¹)
      (by group) (by group) (hcomm hαO haB) (hcomm hαO hbB) (hcomm hβO haB) (hcomm hβO hbB)
      (hcomm hβO hαB).symm
  rw [← hCmap, ← map_commutator] at hc
  obtain ⟨c', hc', rfl⟩ := hc
  exact ⟨c', hCx hc', rfl⟩

omit [Finite Q] in
theorem isPGroup_of_isElemAbelian {R : Subgroup Q} (hR : IsElemAbelian 2 R) : IsPGroup 2 R :=
  CFSG.Open.IsElemAbelian.isPGroup hR

omit [Finite Q] in
theorem card_map_mk'_mul (E : Subgroup Q) :
    Nat.card (E.map π) * Nat.card ↥(E ⊓ O) = Nat.card E := by
  set f := (QuotientGroup.mk' O).subgroupMap E
  have hker : Nat.card f.ker = Nat.card ↥(E ⊓ O) := by
    rw [← card_map_of_injective E.subtype_injective]
    suffices h : f.ker.map E.subtype = E ⊓ O by rw [h]
    ext q
    constructor
    · rintro ⟨e, he, rfl⟩
      refine ⟨e.2, ?_⟩
      have : π e = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp he)
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    · rintro ⟨hqE, hqO⟩
      refine ⟨⟨q, hqE⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, MonoidHom.mem_ker]
      apply Subtype.ext
      change π q = 1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hqO
  rw [f.ker.card_eq_card_quotient_mul_card_subgroup,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f
      ((QuotientGroup.mk' O).subgroupMap_surjective E)).toEquiv, hker]

theorem centralizer_rankTwoX_eq_bot {M : Subgroup Q} (hH : RankTwoHyp Q M) :
    centralizer (rankTwoX (M.map π) : Set (Q ⧸ O)) = ⊥ :=
  centralizer_normalClosure_eq_bot (rankTwoHyp_map hH) standardComponentOddCore_quotient_eq_bot

theorem map_le_rankTwoX
    {M R : Subgroup Q} (hH : RankTwoHyp Q M)
    (hJ2 : NativeSporadic.IsSporadic (rankTwoX (M.map π)) .J2) (hR : IsElemAbelian 2 R)
    (hRM : R ≤ centralizer (M : Set Q)) (hZM : center ↥M = ⊥) {x : Q} (hxM : x ∈ M)
    (hx5 : orderOf x = 5) : R.map π ≤ rankTwoX (M.map π) := by
  have hMO := inf_oddCore_eq_bot hH hZM
  have hXn : (rankTwoX (M.map π)).Normal := normalClosure_normal
  have hx'X : π x ∈ rankTwoX (M.map π) := le_normalClosure (mem_map_of_mem _ hxM)
  have hx'5 : orderOf (π x) = 5 := by
    have h := orderOf_injective ((QuotientGroup.mk' O).comp M.subtype)
      (fun a b hab => Subtype.ext (mk'_injOn_of_inf hMO a.2 b.2 hab)) ⟨x, hxM⟩
    rw [Subgroup.orderOf_mk, hx5] at h
    simpa using h
  rintro _ ⟨r, hr, rfl⟩
  refine mem_of_commute_five hJ2 (centralizer_rankTwoX_eq_bot hH) ?_ hx'X hx'5 ?_
  · rw [← map_pow, hR.2 r hr, map_one]
  · rw [← map_mul, ← map_mul, (mem_centralizer_iff.mp (hRM hr) x hxM)]

theorem exists_conj_not_mem_centralizer
    (hJ : J2Std.J2StdFacts) {M R : Subgroup Q}
    (hH : RankTwoHyp Q M) (hJ2 : NativeSporadic.IsSporadic (rankTwoX (M.map π)) .J2)
    (hR : IsElemAbelian 2 R) (hR4 : 4 ≤ Nat.card R) (hRM : R ≤ centralizer (M : Set Q))
    (hZM : center ↥M = ⊥) (hM60 : Nat.card M = 60) {x : Q} (hxM : x ∈ M)
    (hx5 : orderOf x = 5) :
    ∃ c ∈ centralizer ({x} : Set Q), ∃ r ∈ R, c * r * c⁻¹ ∉ centralizer (M : Set Q) := by
  have hMO := inf_oddCore_eq_bot hH hZM
  set X := rankTwoX (M.map π) with hXdef
  have hMX : M.map π ≤ X := le_normalClosure
  have hx'X : π x ∈ X := hMX (mem_map_of_mem _ hxM)
  have hx'5 : orderOf (π x) = 5 := by
    have h := orderOf_injective ((QuotientGroup.mk' O).comp M.subtype)
      (fun a b hab => Subtype.ext (mk'_injOn_of_inf hMO a.2 b.2 hab)) ⟨x, hxM⟩
    rw [Subgroup.orderOf_mk, hx5] at h
    simpa using h
  have hRX := map_le_rankTwoX hH hJ2 hR hRM hZM hxM hx5
  have hR2 := isPGroup_of_isElemAbelian hR
  have hstd := stdIn_of_isSporadic hJ hJ2
  set y : ↥X := ⟨π x, hx'X⟩ with hy
  set V := (R.map π).subgroupOf X with hV
  set Λ := (M.map π).subgroupOf X with hΛ
  have hcardV : Nat.card V = Nat.card R := by
    rw [hV, Nat.card_congr (subgroupOfEquivOfLe hRX).toEquiv, card_map_mk'_of_two hR2]
  have hcardΛ : Nat.card Λ = 60 := by
    rw [hΛ, Nat.card_congr (subgroupOfEquivOfLe hMX).toEquiv, card_map_mk'_of_inf hMO, hM60]
  have hVy : V ≤ centralizer ({y} : Set ↥X) := by
    intro v hv
    rw [mem_centralizer_singleton_iff]
    obtain ⟨r, hr, hrv⟩ := mem_subgroupOf.mp hv
    apply Subtype.ext
    change (v : Q ⧸ O) * π x = π x * v
    rw [← hrv, ← map_mul, ← map_mul, (mem_centralizer_iff.mp (hRM hr) x hxM)]
  have hVΛ : V ≤ centralizer (Λ : Set ↥X) := by
    intro v hv
    rw [mem_centralizer_iff]
    intro l hl
    obtain ⟨r, hr, hrv⟩ := mem_subgroupOf.mp hv
    obtain ⟨m, hm, hml⟩ := mem_subgroupOf.mp hl
    apply Subtype.ext
    change (l : Q ⧸ O) * v = v * l
    rw [← hrv, ← hml, ← map_mul, ← map_mul, (mem_centralizer_iff.mp (hRM hr) m hm)]
  obtain ⟨c, hc, v, hv, hcv⟩ := hstd y V Λ (by rw [Subgroup.orderOf_mk, hx'5])
    (hR2.map _ |>.comap_subtype) (hcardV ▸ hR4) hVy (mem_subgroupOf.mpr (mem_map_of_mem _ hxM))
    hcardΛ hVΛ
  have hcmap : (c : Q ⧸ O) ∈ ⁅X ⊓ centralizer ({π x} : Set (Q ⧸ O)),
      X ⊓ centralizer ({π x} : Set (Q ⧸ O))⁆ := by
    have hK : (centralizer ({y} : Set ↥X)).map X.subtype =
        X ⊓ centralizer ({π x} : Set (Q ⧸ O)) := by
      ext z
      rw [mem_map, mem_inf]
      constructor
      · rintro ⟨w, hw, rfl⟩
        rw [mem_centralizer_singleton_iff] at hw
        exact ⟨w.2, mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hw)⟩
      · rintro ⟨hzX, hzC⟩
        exact ⟨⟨z, hzX⟩, mem_centralizer_singleton_iff.mpr
          (Subtype.ext (mem_centralizer_singleton_iff.mp hzC)), rfl⟩
    rw [← hK, ← map_commutator]
    exact ⟨c, hc, rfl⟩
  obtain ⟨c', hc'x, hc'π⟩ := commutator_lift hH hxM hcmap
  obtain ⟨r, hr, hrv⟩ := mem_subgroupOf.mp hv
  refine ⟨c', hc'x, r, hr, fun hmem => hcv ?_⟩
  rw [mem_centralizer_iff]
  intro l hl
  obtain ⟨m, hm, hml⟩ := mem_subgroupOf.mp hl
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [← hc'π, ← hrv, ← hml, ← map_inv, ← map_mul, ← map_mul, ← map_mul, ← map_mul,
    (mem_centralizer_iff.mp hmem m hm)]

theorem le_normalClosure_of_elem
    {M R : Subgroup Q} (hH : RankTwoHyp Q M)
    (hJ2 : NativeSporadic.IsSporadic (rankTwoX (M.map π)) .J2) (hR : IsElemAbelian 2 R)
    (hRM : R ≤ centralizer (M : Set Q)) (hZM : center ↥M = ⊥) {x : Q} (hxM : x ∈ M)
    (hx5 : orderOf x = 5) : R ≤ normalClosure (M : Set Q) := by
  intro r hr
  have hrX : π r ∈ rankTwoX (M.map π) :=
    map_le_rankTwoX hH hJ2 hR hRM hZM hxM hx5 (mem_map_of_mem _ hr)
  have hrBO : r ∈ normalClosure (M : Set Q) ⊔ O := by
    rw [← map_normalClosure_mk'] at hrX
    have h1 : r ∈ ((normalClosure (M : Set Q)).map π).comap π := mem_comap.mpr hrX
    rwa [comap_map_eq, QuotientGroup.ker_mk'] at h1
  exact mem_of_mem_sup odd_card_standardComponentOddCore
    (oddCore_le_centralizer_normalClosure hH) hrBO (k := 1) (by rw [pow_one]; exact hR.2 r hr)

theorem mem_oddCore_of_central {M : Subgroup Q} (hH : RankTwoHyp Q M) {z : Q}
    (hzc : ∀ w ∈ normalClosure (M : Set Q), z * w = w * z) : z ∈ O := by
  have h1 : π z ∈ centralizer (rankTwoX (M.map π) : Set (Q ⧸ O)) := by
    rw [mem_centralizer_iff]
    intro w hw
    rw [← map_normalClosure_mk'] at hw
    obtain ⟨w', hw', rfl⟩ := hw
    rw [← map_mul, ← map_mul, hzc w' hw']
  rw [centralizer_rankTwoX_eq_bot hH, mem_bot] at h1
  rwa [← QuotientGroup.ker_mk' O, MonoidHom.mem_ker]

omit [Finite Q] in
theorem card_normalClosure {M : Subgroup Q}
    (hJ2 : NativeSporadic.IsSporadic (rankTwoX (M.map π)) .J2) :
    Nat.card (normalClosure (M : Set Q)) =
      604800 * Nat.card ↥(normalClosure (M : Set Q) ⊓ O) := by
  rw [← card_map_mk'_mul, map_normalClosure_mk']
  obtain ⟨f⟩ := hJ2
  rw [Nat.card_congr f.toEquiv]
  exact congrArg (· * _) CFSG.Sporadic.J2.card_J2

theorem card_rankTwoX_le
    (h5 : Asc08Lemma310) {M R : Subgroup Q} (hH : RankTwoHyp Q M)
    (hA5 : Nonempty (rankTwoQuot M ≃* alternatingGroup (Fin 5)))
    (hZ : Odd (Nat.card (center ↥M))) (hR : IsSylowOf 2 R (centralizer (M : Set Q)))
    (hno : ∀ x : Q, ¬ rightConjugate R x ≤ M) : Nat.card (rankTwoX (M.map π)) ≤ 604800 := by
  obtain ⟨e⟩ := hA5
  rcases h5 (Q ⧸ O) (M.map π) (rankTwoHyp_map hH) standardComponentOddCore_quotient_eq_bot
      ⟨(quotCenterMap hH).symm.trans e⟩ (odd_card_center_map hH hZ) (R.map π)
      (isSylowOf_map hH hR) (not_conj_le_map hH hR.isPGroup hno) with hJ | ⟨hM, -⟩
  · obtain ⟨f⟩ := hJ
    rw [Nat.card_congr f.toEquiv]
    exact CFSG.Sporadic.J2.card_J2.le
  · obtain ⟨f⟩ := hM
    rw [Nat.card_congr f.toEquiv]
    have h : Nat.card (NativeSporadic.Carrier .M12) = 95040 := CFSG.Sporadic.Mathieu.card_M12
    rw [h]
    norm_num

omit [Finite Q] in
theorem normal_sup_of_card [Finite Q] {M E : Subgroup Q} (hE : E ≤ normalClosure (M : Set Q))
    (hX : Nat.card (rankTwoX (M.map π)) ≤ 604800) (hcard : 604800 ≤ Nat.card (E.map π)) :
    (E ⊔ O).Normal := by
  have hle : E.map π ≤ rankTwoX (M.map π) := by
    rw [← map_normalClosure_mk']
    exact map_mono hE
  have heq : E.map π = rankTwoX (M.map π) := eq_of_le_of_card_ge hle (hX.trans hcard)
  have hn : (E.map π).Normal := by
    rw [heq]
    exact normalClosure_normal
  have h1 := hn.comap π
  rwa [comap_map_eq, QuotientGroup.ker_mk'] at h1

end Quotient

end CFSG.ComponentClassification.RankTwoClassical
