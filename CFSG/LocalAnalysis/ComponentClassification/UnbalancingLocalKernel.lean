module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalSection
public import CFSG.LocalAnalysis.LyonsUnitaryFour.CentralHall
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.ComponentClassification.UnbalancingLocal

open Subgroup
open scoped commutatorElement

variable {K : Type*} [Group K] [Finite K]

theorem corefree_quasisimple_small_quotient_action_kernel (hcore : pPrimeCore 2 K = ⊥)
    {Q : Subgroup K} [hQn : Q.Normal] (hQ : IsQuasisimple Q)
    (hT : ∃ T : Sylow 2 (K ⧸ Q), (T : Subgroup (K ⧸ Q)) ≤ center (K ⧸ Q)) :
    IsPGroup 2 (center Q) ∧ ⁅pCore 2 K, Q⁆ = ⊥ ∧ pCore 2 K ⊓ Q = (center Q).map Q.subtype ∧
      centralizer (Q : Set K) = pCore 2 K ∧ (conjQuotAction Q (center Q)).ker = pCore 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := pCore 2 K with hPdef
  set Z := (center Q).map Q.subtype with hZdef
  have hZn : Z.Normal := inferInstance
  have hZQ : Z ≤ Q := map_subtype_le _
  have hZcent : ∀ z ∈ Z, ∀ q ∈ Q, q * z = z * q := by
    rintro _ ⟨z, hz, rfl⟩ q hq
    exact congrArg Subtype.val (mem_center_iff.mp hz ⟨q, hq⟩)
  have : IsMulCommutative Z := isMulCommutative_iff.mpr fun a b =>
    Subtype.ext (hZcent a a.2 b (hZQ b.2)).symm
  have hZp : IsPGroup 2 Z := isPGroup_of_nilpotent_normal Z hZn inferInstance hcore
  have hZcp : IsPGroup 2 (center Q) :=
    hZp.of_equiv ((center Q).equivMapOfInjective Q.subtype Q.subtype_injective).symm
  have hZP : Z ≤ P := le_sSup ⟨hZn, hZp⟩
  have hPQ : ⁅P, Q⁆ = ⊥ := by
    have : Group.IsNilpotent P := (pCore_isPGroup (p := 2) (G := K)).isNilpotent
    have h := (LocalCores.component_solvable_centralizer (R := P) inferInstance
      (pCore_normal (p := 2) (G := K)).isSubnormal).1 Q ⟨hQ, hQn.isSubnormal⟩
    rwa [commutator_comm] at h
  have hPC : P ≤ centralizer (Q : Set K) := commutator_eq_bot_iff_le_centralizer.mp hPQ
  have hPQZ : P ⊓ Q = Z := by
    apply le_antisymm
    · rintro x ⟨hxP, hxQ⟩
      exact ⟨⟨x, hxQ⟩, mem_center_iff.mpr fun g => Subtype.ext
        (mem_centralizer_iff.mp (hPC hxP) g g.2), rfl⟩
    · exact le_inf hZP hZQ
  set C := centralizer (Q : Set K) with hCdef
  obtain ⟨T, hTc⟩ := hT
  set idx := (T : Subgroup (K ⧸ Q)).index with hidxdef
  have hidx : ¬ 2 ∣ idx := T.not_dvd_index
  obtain ⟨M, hMcard, -, -, hMmem, hMchar, -⟩ :=
    LyonsUnitaryFour.central_hall_direct_complement (T : Subgroup (K ⧸ Q)) hTc
      T.card_coprime_index
  set W := C ⊓ M.comap (QuotientGroup.mk' Q) with hWdef
  have hZW : Z ≤ W := by
    refine le_inf (fun z hz => mem_centralizer_iff.mpr fun q hq => hZcent z hz q hq)
      (fun z hz => ?_)
    change QuotientGroup.mk' Q z ∈ M
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff z).mpr (hZQ hz)]
    exact one_mem M
  have hWQ : ∀ w ∈ W, w ∈ Q → w ∈ Z := by
    rintro w ⟨hwC, -⟩ hwQ
    exact ⟨⟨w, hwQ⟩, mem_center_iff.mpr fun g => Subtype.ext
      (mem_centralizer_iff.mp hwC g g.2), rfl⟩
  set ZW := Z.subgroupOf W with hZWdef
  have hZWc : ZW ≤ center W := by
    intro z hz
    refine mem_center_iff.mpr fun w => Subtype.ext ?_
    exact (mem_centralizer_iff.mp (mem_inf.mp w.2).1 z (hZQ (mem_subgroupOf.mp hz))).symm
  let f : W →* K ⧸ Q := (QuotientGroup.mk' Q).comp W.subtype
  have hfker : f.ker = ZW := by
    ext w
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    change QuotientGroup.mk' Q (w : K) = 1 ↔ (w : K) ∈ Z
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact ⟨fun h => hWQ w w.2 h, fun h => hZQ h⟩
  have hfrange : f.range ≤ M := by
    rintro _ ⟨w, rfl⟩
    exact (mem_inf.mp w.2).2
  have hZWidx : ZW.index ∣ idx := by
    rw [← hfker, index_ker, hidxdef, ← hMcard]
    exact card_dvd_of_le hfrange
  have hZWodd : ¬ 2 ∣ ZW.index := fun h => hidx (h.trans hZWidx)
  have hZWcop : Nat.Coprime (Nat.card ZW) ZW.index := by
    have hZWp : IsPGroup 2 ZW := hZp.comap_of_injective W.subtype W.subtype_injective
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hZWp
    rw [hn]
    exact Nat.Coprime.pow_left n (Nat.prime_two.coprime_iff_not_dvd.mpr hZWodd)
  obtain ⟨W₀, hW₀card, -, -, -, hW₀char, -⟩ :=
    LyonsUnitaryFour.central_hall_direct_complement ZW hZWc hZWcop
  have hW₀n : (W₀.map W.subtype).Normal := inferInstance
  have hW₀cop : Nat.Coprime 2 (Nat.card (W₀.map W.subtype)) := by
    rw [card_map_of_injective W.subtype_injective, hW₀card]
    exact Nat.prime_two.coprime_iff_not_dvd.mpr hZWodd
  have hW₀bot : W₀.map W.subtype = ⊥ := by
    have h : W₀.map W.subtype ≤ pPrimeCore 2 K := le_sSup ⟨hW₀n, hW₀cop⟩
    rwa [hcore, le_bot_iff] at h
  have hZWtop : ZW = ⊤ := by
    rw [← index_eq_one, ← hW₀card, ← card_map_of_injective W.subtype_injective, hW₀bot,
      card_bot]
  have hWZ : ∀ w ∈ W, w ∈ Z := fun w hw => by
    have hmem : (⟨w, hw⟩ : W) ∈ ZW := by
      rw [hZWtop]
      exact mem_top _
    exact mem_subgroupOf.mp hmem
  have hCp : IsPGroup 2 C := by
    intro c
    obtain ⟨a, m, hm, hcard⟩ := Nat.exists_eq_two_pow_mul_odd (Nat.card_pos (α := C)).ne'
    refine ⟨a, ?_⟩
    set d := c ^ (2 ^ a) with hd
    have hdm : d ^ m = 1 := by
      rw [hd, ← pow_mul, ← hcard, pow_card_eq_one']
    have hdm' : (d : K) ^ m = 1 := by
      rw [← Subgroup.coe_pow, hdm, Subgroup.coe_one]
    have hdM : QuotientGroup.mk' Q (d : K) ∈ M := by
      rw [hMmem, ← orderOf_dvd_iff_pow_eq_one]
      have h1 : orderOf (QuotientGroup.mk' Q (d : K)) ∣ m :=
        orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hdm', map_one])
      have h2 : orderOf (QuotientGroup.mk' Q (d : K)) ∣ Nat.card T * idx := by
        rw [card_mul_index]
        exact orderOf_dvd_natCard _
      have hcop : Nat.Coprime (orderOf (QuotientGroup.mk' Q (d : K))) (Nat.card T) := by
        obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp T.isPGroup'
        rw [hn]
        exact Nat.Coprime.pow_right n (Nat.coprime_two_right.mpr (hm.of_dvd_nat h1))
      exact hcop.dvd_of_dvd_mul_left h2
    have hdZ : (d : K) ∈ Z := hWZ d ⟨d.2, hdM⟩
    obtain ⟨b, hb⟩ := hZp ⟨d, hdZ⟩
    have hdb : d ^ (2 ^ b) = 1 :=
      Subtype.ext (congrArg Subtype.val hb : ((d : K) ^ (2 ^ b)) = 1)
    have hord : orderOf d = 1 :=
      Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left b (Nat.coprime_two_left.mpr hm))
        (orderOf_dvd_of_pow_eq_one hdb) (orderOf_dvd_of_pow_eq_one hdm)
    exact orderOf_eq_one_iff.mp hord
  have hCP : C = P := le_antisymm (le_sSup ⟨inferInstance, hCp⟩) hPC
  have hker : (conjQuotAction Q (center Q)).ker = C := by
    ext k
    rw [MonoidHom.mem_ker, conjQuotAction_eq_one_iff]
    constructor
    · intro hk
      have hcen : ∀ q : Q, (⟨⁅(q : K), k⁆, hZQ (hk q q.2)⟩ : Q) ∈ center Q := fun q => by
        obtain ⟨z, hz, hzq⟩ := hk q q.2
        rwa [show z = ⟨⁅(q : K), k⁆, hZQ (hk q q.2)⟩ from Subtype.ext hzq] at hz
      let δ : Q →* center Q := MonoidHom.mk'
        (fun q => ⟨⟨⁅(q : K), k⁆, hZQ (hk q q.2)⟩, hcen q⟩) (fun a b => by
          apply Subtype.ext
          apply Subtype.ext
          change ⁅((a * b : Q) : K), k⁆ = ⁅(a : K), k⁆ * ⁅(b : K), k⁆
          have hb := hZcent _ (hk b b.2)
          calc ⁅((a * b : Q) : K), k⁆ = (a : K) * ⁅(b : K), k⁆ * (k * (a : K)⁻¹ * k⁻¹) := by
                rw [Subgroup.coe_mul, commutatorElement_def, commutatorElement_def]
                group
            _ = ⁅(b : K), k⁆ * (a : K) * (k * (a : K)⁻¹ * k⁻¹) := by rw [hb a a.2]
            _ = ⁅(b : K), k⁆ * ⁅(a : K), k⁆ := by
                rw [commutatorElement_def (a : K)]
                group
            _ = ⁅(a : K), k⁆ * ⁅(b : K), k⁆ := (hb _ (hZQ (hk a a.2))).symm)
      have hδ : ∀ q : Q, δ q = 1 := fun q => by
        have htop : (⊤ : Subgroup Q) ≤ δ.ker := by
          rw [← Group.isPerfect_def.mp hQ.1]
          exact Abelianization.commutator_subset_ker δ
        exact htop (mem_top q)
      refine mem_centralizer_iff.mpr fun q hq => ?_
      have h1 := congrArg (fun z : center Q => ((z : Q) : K)) (hδ ⟨q, hq⟩)
      change ⁅q, k⁆ = 1 at h1
      exact commutatorElement_eq_one_iff_mul_comm.mp h1
    · intro hkC q hq
      rw [commutatorElement_eq_one_iff_mul_comm.mpr (mem_centralizer_iff.mp hkC q hq)]
      exact one_mem _
  exact ⟨hZcp, hPQ, hPQZ, hCP, hker.trans hCP⟩

end CFSG.ComponentClassification.UnbalancingLocal
