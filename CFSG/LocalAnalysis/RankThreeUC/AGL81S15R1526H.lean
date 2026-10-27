module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsPair
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15LiftDefs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Oracles
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1526P0a
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinTransport
import CFSG.GroupTheory.LocalCores.PrimeSetCore

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup KFactsPair
open scoped commutatorElement

section PComponentNormal

variable {X : Type} [Group X] [Finite X]

theorem isPComponent_of_normal_aux1 (p : ℕ) (Y : Type) [Group Y] :
    CFSG.pPrimeCore p Y = CFSG.piCore {q : Nat.Primes | ¬ (q : ℕ) ∣ p} Y := by
  unfold CFSG.pPrimeCore CFSG.piCore CFSG.IsPiSubgroup
  congr 1
  ext N
  simp only [Set.mem_setOf_eq, and_congr_right_iff]
  intro _
  constructor
  · intro h q hqN hqp
    have h1 : (q : ℕ) ∣ Nat.gcd p (Nat.card N) := Nat.dvd_gcd hqp hqN
    rw [h] at h1
    exact q.2.one_lt.ne' (Nat.dvd_one.1 h1)
  · intro h
    exact Nat.coprime_of_dvd fun k hk hkp hkN => h ⟨k, hk⟩ hkN hkp

theorem isPComponent_of_normal_aux2 (p : ℕ) {N : Subgroup X} (hN : N.Normal) :
    (CFSG.pPrimeCore p ↥N).map N.subtype = N ⊓ CFSG.pPrimeCore p X := by
  rw [isPComponent_of_normal_aux1, isPComponent_of_normal_aux1]
  exact CFSG.LocalCores.prime_set_core_normal_intersection _ hN

theorem isPComponent_of_normal {N I : Subgroup X} [N.Normal] (hIN : I ≤ N) {p : ℕ}
    (h : CFSG.IsPComponent p (I.subgroupOf N)) : CFSG.IsPComponent p I := by
  obtain ⟨K, hK, hsub, hmap, hmin⟩ := h
  have hC := isPComponent_of_normal_aux2 p (X := X) (inferInstance : N.Normal)
  have hle : CFSG.pPrimeCore p ↥N ≤ (CFSG.pPrimeCore p X).comap N.subtype := fun n hn => by
    have h1 : (n : X) ∈ (CFSG.pPrimeCore p ↥N).map N.subtype := ⟨n, hn, rfl⟩
    rw [hC] at h1
    exact h1.2
  let f : (↥N ⧸ CFSG.pPrimeCore p ↥N) →* (X ⧸ CFSG.pPrimeCore p X) :=
    QuotientGroup.map _ _ N.subtype hle
  have hf : Function.Injective f := by
    refine (injective_iff_map_eq_one f).2 fun x hx => ?_
    obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective x
    have hn : (n : X) ∈ CFSG.pPrimeCore p X := (QuotientGroup.eq_one_iff _).1 hx
    have h1 : (n : X) ∈ (CFSG.pPrimeCore p ↥N).map N.subtype := by
      rw [hC]
      exact ⟨n.2, hn⟩
    obtain ⟨m, hm, hmn⟩ := h1
    have hmn' : m = n := Subtype.ext hmn
    subst hmn'
    exact (QuotientGroup.eq_one_iff _).2 hm
  have hfmk : ∀ S : Subgroup ↥N,
      (S.map (QuotientGroup.mk' (CFSG.pPrimeCore p ↥N))).map f =
        (S.map N.subtype).map (QuotientGroup.mk' (CFSG.pPrimeCore p X)) := fun S => by
    rw [Subgroup.map_map, Subgroup.map_map]
    rfl
  have hIsub : I.IsSubnormal := by
    have := hsub.trans' (inferInstance : N.Normal).isSubnormal
    rwa [Subgroup.map_subgroupOf_eq_of_le hIN] at this
  have hKI : K.map f = I.map (QuotientGroup.mk' (CFSG.pPrimeCore p X)) := by
    rw [← hmap, hfmk, Subgroup.map_subgroupOf_eq_of_le hIN]
  refine ⟨I.map (QuotientGroup.mk' (CFSG.pPrimeCore p X)),
    ⟨?_, hIsub.map (QuotientGroup.mk'_surjective _)⟩, hIsub, rfl, ?_⟩
  · rw [← hKI]
    exact CFSG.IsQuasisimple.of_mulEquiv (K.equivMapOfInjective f hf).symm hK.1
  · intro J hJI hJsub hJmap
    have hJN : J ≤ N := hJI.le.trans hIN
    have hlt : J.subgroupOf N < I.subgroupOf N := by
      refine lt_of_le_of_ne (Subgroup.comap_mono hJI.le) fun heq => hJI.ne ?_
      have := congrArg (fun S : Subgroup ↥N => S.map N.subtype) heq
      simpa only [Subgroup.map_subgroupOf_eq_of_le hJN,
        Subgroup.map_subgroupOf_eq_of_le hIN] using this
    refine hmin _ hlt hJsub.subgroupOf ?_
    apply Subgroup.map_injective hf
    rw [hKI, hfmk, Subgroup.map_subgroupOf_eq_of_le hJN]
    exact hJmap

end PComponentNormal

section LThreeLifts

open CFSG.ComponentClassification.CatalogueBPrimeJoin (primeResidual primeResidual_map_surjective
  primeResidual_eq_top_of_corefree_quasisimple primeResidual_characteristic
  pComponent_iff_subnormal_generated_quasisimple)

variable {X : Type} [Group X] [Finite X]

noncomputable def isPComponent_of_isLThree_barHom (L : Subgroup X) : ↥L →* ↥(barO2 L) :=
  ((QuotientGroup.mk' (CFSG.pCore 2 X)).domRestrict L).codRestrict (barO2 L)
    fun x => ⟨x, x.2, rfl⟩

theorem isPComponent_of_isLThree_aux1 (L : Subgroup X) :
    Function.Surjective (isPComponent_of_isLThree_barHom L) := by
  rintro ⟨y, z, hz, rfl⟩
  exact ⟨⟨z, hz⟩, rfl⟩

theorem isPComponent_of_isLThree_aux3 (L : Subgroup X) :
    IsPGroup 2 (isPComponent_of_isLThree_barHom L).ker := by
  intro g
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := X))
    ⟨(g : ↥L).1, (QuotientGroup.eq_one_iff _).1
      (congrArg Subtype.val (MonoidHom.mem_ker.1 g.2))⟩
  refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
  simpa using congrArg Subtype.val hk

theorem isPComponent_of_isLThree_aux4 {L : Subgroup X} (h : IsLThreeOfExp 1 ↥(barO2 L)) {p : ℕ}
    [Fact p.Prime] (hp : p = 3 ∨ p = 7) :
    CFSG.pPrimeCore p ↥L = (isPComponent_of_isLThree_barHom L).ker := by
  have hsimple := isSimpleGroup_of_isLThreeOfExp_one h
  have hcard := card_eq_of_isLThreeOfExp_one h
  have hp168 : p ∣ 168 := by rcases hp with rfl | rfl <;> norm_num
  have hsurj := isPComponent_of_isLThree_aux1 L
  apply le_antisymm
  · have hN : ((CFSG.pPrimeCore p ↥L).map (isPComponent_of_isLThree_barHom L)).Normal :=
      (inferInstance : (CFSG.pPrimeCore p ↥L).Normal).map _ hsurj
    rcases hN.eq_bot_or_eq_top with hbot | htop
    · exact (Subgroup.map_eq_bot_iff _).1 hbot
    · exfalso
      have h1 := Subgroup.card_map_dvd (CFSG.pPrimeCore p ↥L) (isPComponent_of_isLThree_barHom L)
      rw [htop, Subgroup.card_top, hcard] at h1
      have h2 := Nat.Coprime.coprime_dvd_right h1
        (CFSG.pPrimeCore_coprime_card (p := p) (G := ↥L))
      exact (Fact.out : p.Prime).one_lt.ne' (Nat.eq_one_of_dvd_one
        (h2.gcd_eq_one ▸ Nat.dvd_gcd (dvd_refl p) hp168))
  · refine le_sSup ⟨MonoidHom.normal_ker _, ?_⟩
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 (isPComponent_of_isLThree_aux3 L)
    rw [ha]
    refine Nat.Coprime.pow_right a ?_
    rcases hp with rfl | rfl <;> norm_num

theorem isPComponent_of_isLThree_aux6 {S : Type} [Group S] [Finite S] (hs : IsSimpleGroup S)
    (hc : Nat.card S = 168) : CFSG.IsQuasisimple S := by
  have hn : ∃ a b : S, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    letI : CommGroup S := { ‹Group S› with mul_comm := hcon }
    have := IsSimpleGroup.prime_card (α := S)
    rw [hc] at this
    exact absurd this (by norm_num)
  have hz : Subgroup.center S = ⊥ := by
    rcases (inferInstance : (Subgroup.center S).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hn
      exact hab (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b) a)
  let e : S ⧸ Subgroup.center S ≃* S :=
    (QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot
  refine ⟨?_, e.isSimpleGroup, ?_⟩
  · refine Group.isPerfect_def.mpr ?_
    rcases (inferInstance : (_root_.commutator S).Normal).eq_bot_or_eq_top with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hn
      have hmem : ⁅a, b⁆ ∈ _root_.commutator S :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
      exact hab hmem
    · exact h
  · obtain ⟨a, b, hab⟩ := hn
    exact ⟨e.symm a, e.symm b, fun hcomm => hab (by simpa using congrArg e hcomm)⟩

theorem isPComponent_of_isLThree_aux5 {L : Subgroup X} (hL : IsC2 L)
    (h : IsLThreeOfExp 1 ↥(barO2 L)) {p : ℕ} [Fact p.Prime] (hp : p = 3 ∨ p = 7) :
    primeResidual p ↥L = ⊤ := by
  have hsimple := isSimpleGroup_of_isLThreeOfExp_one h
  have hcard := card_eq_of_isLThreeOfExp_one h
  have hsurj := isPComponent_of_isLThree_aux1 L
  have hp168 : p ∣ 168 := by rcases hp with rfl | rfl <;> norm_num
  have hq := isPComponent_of_isLThree_aux6 hsimple hcard
  have hcore : CFSG.pPrimeCore p ↥(barO2 L) = ⊥ := by
    rcases (inferInstance : (CFSG.pPrimeCore p ↥(barO2 L)).Normal).eq_bot_or_eq_top with h0 | h0
    · exact h0
    · exfalso
      have h1 := CFSG.pPrimeCore_coprime_card (p := p) (G := ↥(barO2 L))
      rw [h0, Subgroup.card_top, hcard] at h1
      exact (Fact.out : p.Prime).one_lt.ne'
        (Nat.eq_one_of_dvd_one (h1.gcd_eq_one ▸ Nat.dvd_gcd (dvd_refl p) hp168))
  haveI : (primeResidual p ↥L).Characteristic := primeResidual_characteristic p ↥L
  haveI : (primeResidual p ↥L).Normal := inferInstance
  have htop : (primeResidual p ↥L).map (isPComponent_of_isLThree_barHom L) = ⊤ := by
    rw [primeResidual_map_surjective p _ hsurj]
    exact primeResidual_eq_top_of_corefree_quasisimple p hq hcore
  set J := primeResidual p ↥L with hJdef
  have hodd : ∀ x : ↥L, Odd (orderOf x) → x ∈ J := by
    intro x hx
    have hxmem : isPComponent_of_isLThree_barHom L x ∈
        J.map (isPComponent_of_isLThree_barHom L) := by
      rw [htop]
      trivial
    obtain ⟨j, hj, hjx⟩ := hxmem
    have hk : j⁻¹ * x ∈ (isPComponent_of_isLThree_barHom L).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hjx, inv_mul_cancel]
    obtain ⟨m, hm⟩ := isPComponent_of_isLThree_aux3 L ⟨_, hk⟩
    have hm' : (j⁻¹ * x) ^ (2 ^ m) = 1 := by simpa using congrArg Subtype.val hm
    let q := QuotientGroup.mk' J
    have hqj : q j = 1 := (QuotientGroup.eq_one_iff j).2 hj
    have hqx : q x = q (j⁻¹ * x) := by rw [map_mul, map_inv, hqj, inv_one, one_mul]
    have hpow : (q x) ^ (2 ^ m) = 1 := by rw [hqx, ← map_pow, hm', map_one]
    have h1 : orderOf (q x) ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hpow
    have h2 : Odd (orderOf (q x)) := hx.of_dvd_nat (orderOf_map_dvd q x)
    have h3 : orderOf (q x) = 1 :=
      Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right m (Nat.coprime_two_right.2 h2)) h1
    exact (QuotientGroup.eq_one_iff x).1 (orderOf_eq_one_iff.1 h3)
  rw [eq_top_iff]
  intro y _
  have hy : (y : X) ∈ oddHull L := by
    rw [hL.2.1]
    exact y.2
  have hle : oddHull L ≤ J.map L.subtype := by
    refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨hxL, hxodd⟩
    refine ⟨⟨x, hxL⟩, hodd _ ?_, rfl⟩
    rwa [Subgroup.orderOf_mk]
  obtain ⟨j, hj, hjy⟩ := hle hy
  have hjy' : j = y := Subtype.ext hjy
  exact hjy' ▸ hj

noncomputable def isPComponent_of_isLThree_quotEquiv {L : Subgroup X}
    (h : IsLThreeOfExp 1 ↥(barO2 L)) {p : ℕ} [Fact p.Prime] (hp : p = 3 ∨ p = 7) :
    (↥L ⧸ CFSG.pPrimeCore p ↥L) ≃* ↥(barO2 L) :=
  (QuotientGroup.quotientMulEquivOfEq (isPComponent_of_isLThree_aux4 h hp)).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (isPComponent_of_isLThree_aux1 L))

theorem isPComponent_of_isLThree_aux7 {L : Subgroup X} (h : IsLThreeOfExp 1 ↥(barO2 L)) {p : ℕ}
    [Fact p.Prime] (hp : p = 3 ∨ p = 7) : CFSG.IsQuasisimple (↥L ⧸ CFSG.pPrimeCore p ↥L) :=
  CFSG.IsQuasisimple.of_mulEquiv (isPComponent_of_isLThree_quotEquiv h hp)
    (isPComponent_of_isLThree_aux6 (isSimpleGroup_of_isLThreeOfExp_one h)
      (card_eq_of_isLThreeOfExp_one h))

theorem isPComponent_of_isLThree {L : Subgroup X} (hL : IsC2 L) (h : IsLThreeOfExp 1 ↥(barO2 L))
    {p : ℕ} (hp : p = 3 ∨ p = 7) : CFSG.IsPComponent p L := by
  haveI : Fact p.Prime := ⟨by rcases hp with rfl | rfl <;> norm_num⟩
  have h1 : L.IsSubnormal := hL.1.mathlib Subgroup.IsSubnormal.top
  have h2 : primeResidual p ↥L = ⊤ := isPComponent_of_isLThree_aux5 hL h hp
  exact (pComponent_iff_subnormal_generated_quasisimple p L).2
    ⟨h1, h2, isPComponent_of_isLThree_aux7 h hp⟩

end LThreeLifts

section FinalLifts

open CFSG.ComponentClassification.CatalogueBPrimeJoin (primeResidual_eq_top_of_equiv
  quasisimple_primeCore_quotient_of_equiv pComponent_subgroupOf_iff)

variable {G : Type} [Group G] [Finite G]

theorem isPComponent_inf_of_isLThree {M K : Subgroup G} {L : Subgroup ↥M} (hL : IsC2 L)
    (h : IsLThreeOfExp 1 ↥(barO2 L)) (hLK : L.map M.subtype ≤ K) (hKM : K ≤ M) :
    CFSG.IsPComponent 3 ((L.map M.subtype).subgroupOf K) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp3 : (3 : ℕ) = 3 ∨ (3 : ℕ) = 7 := Or.inl rfl
  have hsub : L.IsSubnormal := hL.1.mathlib Subgroup.IsSubnormal.top
  let e : ↥L ≃* ↥(L.map M.subtype) := L.equivMapOfInjective M.subtype M.subtype_injective
  rw [pComponent_subgroupOf_iff 3 (L.map M.subtype) K hLK]
  refine ⟨?_, primeResidual_eq_top_of_equiv 3 e (isPComponent_of_isLThree_aux5 hL h hp3),
    quasisimple_primeCore_quotient_of_equiv 3 e (isPComponent_of_isLThree_aux7 h hp3)⟩
  have hcomap : (L.map M.subtype).subgroupOf K = L.comap (Subgroup.inclusion hKM) := by
    ext x
    constructor
    · rintro ⟨y, hy, hyx⟩
      have hyx' : y = Subgroup.inclusion hKM x := Subtype.ext hyx
      rwa [hyx'] at hy
    · intro hx
      exact ⟨Subgroup.inclusion hKM x, hx, rfl⟩
  rw [hcomap]
  exact hsub.comap _

theorem isLThreeTwoPow_quotient_pPrimeCore {M : Subgroup G} {L : Subgroup ↥M} (hL : IsC2 L)
    (h : IsLThreeOfExp 1 ↥(barO2 L)) :
    IsLThreeTwoPow (↥(L.map M.subtype) ⧸ CFSG.pPrimeCore 3 ↥(L.map M.subtype)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let e : ↥L ≃* ↥(L.map M.subtype) := L.equivMapOfInjective M.subtype M.subtype_injective
  let e2 : (↥L ⧸ CFSG.pPrimeCore 3 ↥L) ≃*
      (↥(L.map M.subtype) ⧸ CFSG.pPrimeCore 3 ↥(L.map M.subtype)) :=
    QuotientGroup.congr _ _ e (CFSG.pPrimeCore_map_iso 3 e)
  let f := e2.symm.trans (isPComponent_of_isLThree_quotEquiv h (Or.inl rfl : (3 : ℕ) = 3 ∨ (3 : ℕ) = 7))
  have h' := h
  rcases h' with ⟨-, d, q, hq, hd, ⟨g⟩⟩ | ⟨h2, -⟩
  · exact Or.inr ⟨d, ⟨q, hq, hd⟩, ⟨f.trans g⟩⟩
  · omega

end FinalLifts

end CFSG.LocalAnalysis.RankThreeUC.S15
