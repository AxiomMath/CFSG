module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore
public import Mathlib.GroupTheory.Transfer
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.Positivity.Finset

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup

namespace L415

variable {G : Type*} [Group G] [Finite G]

theorem exists_odd_normal_of_central_sylow {H : Type*} [Group H] [Finite H] (P : Sylow 2 H)
    (hP : (P : Subgroup H) ≤ center H) :
    ∃ K : Subgroup H, K.Normal ∧ Odd (Nat.card K) ∧ ∀ h : H, Odd (orderOf h) → h ∈ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP' : normalizer (P : Subgroup H) ≤ centralizer ((P : Subgroup H) : Set H) := by
    intro g _
    rw [mem_centralizer_iff]
    intro x hx
    exact (mem_center_iff.mp (hP hx) g).symm
  refine ⟨(MonoidHom.transferSylow P hP').ker, inferInstance, ?_, fun h hh => ?_⟩
  · have hcomp := MonoidHom.ker_transferSylow_isComplement' P hP'
    have h1 : (P : Subgroup H).index = Nat.card (MonoidHom.transferSylow P hP').ker :=
      hcomp.index_eq_card
    rw [← h1]
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp P.not_dvd_index)
  · rw [MonoidHom.mem_ker]
    have h1 : orderOf (MonoidHom.transferSylow P hP' h) ∣ orderOf h := orderOf_map_dvd _ h
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp P.isPGroup') (MonoidHom.transferSylow P hP' h)
    rw [hk] at h1
    have hk1 : 2 ^ k = 1 :=
      Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hh)) h1
    rwa [hk1, orderOf_eq_one_iff] at hk

theorem isPGroup_quot_of_central {P : Subgroup G} [P.Normal] (hP : IsPGroup 2 P)
    (hGP : IsPGroup 2 ((G ⧸ P) ⧸ pPrimeCore 2 (G ⧸ P)))
    (hodd : ∀ g : G, Odd (orderOf g) → ∀ x ∈ P, g * x = x * g) :
    IsPGroup 2 (G ⧸ pPrimeCore 2 G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Sodd : Set G := {g : G | Odd (orderOf g)} with hSodd
  have hconjodd : ∀ x ∈ Group.conjugatesOfSet Sodd, x ∈ Sodd := by
    intro x hx
    obtain ⟨a, ha, hax⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    obtain ⟨c, rfl⟩ := isConj_iff.mp hax
    have h1 := MulEquiv.orderOf_eq (MulAut.conj c) a
    simp only [MulAut.conj_apply] at h1
    show Odd (orderOf (c * a * c⁻¹))
    rw [h1]
    exact ha
  set H := normalClosure Sodd with hH
  have hHC : H ≤ centralizer (P : Set G) :=
    normalClosure_le_normal fun g hg => mem_centralizer_iff.mpr fun x hx => (hodd g hg x hx).symm
  have hodd_core : ∀ q : G ⧸ P, Odd (orderOf q) → q ∈ pPrimeCore 2 (G ⧸ P) := by
    intro q hq
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hGP) (QuotientGroup.mk q)
    have h1 : orderOf (QuotientGroup.mk q : (G ⧸ P) ⧸ pPrimeCore 2 (G ⧸ P)) ∣ orderOf q :=
      orderOf_map_dvd (QuotientGroup.mk' _) q
    rw [hk] at h1
    have hk1 : 2 ^ k = 1 :=
      Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hq)) h1
    rw [hk1, orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at hk
    exact hk
  have hON : ((pPrimeCore 2 (G ⧸ P)).comap (QuotientGroup.mk' P)).Normal := by
    have := pPrimeCore_normal (p := 2) (G := G ⧸ P)
    infer_instance
  have hHmap : H ≤ (pPrimeCore 2 (G ⧸ P)).comap (QuotientGroup.mk' P) :=
    normalClosure_le_normal fun g hg =>
      hodd_core _ (Odd.of_dvd_nat hg (orderOf_map_dvd (QuotientGroup.mk' P) g))
  let φ : ↥H →* G ⧸ P := (QuotientGroup.mk' P).comp H.subtype
  have hker : φ.ker = P.subgroupOf H := by
    ext x
    simp [φ, MonoidHom.mem_ker, mem_subgroupOf, QuotientGroup.eq_one_iff]
  have hrange_odd : Odd (Nat.card φ.range) := by
    have hle : φ.range ≤ pPrimeCore 2 (G ⧸ P) := by
      rintro _ ⟨x, rfl⟩
      exact hHmap x.2
    exact Odd.of_dvd_nat (Nat.coprime_two_left.mp pPrimeCore_coprime_card)
      (Subgroup.card_dvd_of_le hle)
  have hcardH := Subgroup.card_ker_mul_card_range φ
  rw [hker] at hcardH
  have hZp : IsPGroup 2 ↥(P.subgroupOf H) := hP.comap_subtype
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card.mp hZp)
  have hZcard : Nat.card ↥(P.subgroupOf H) = 2 ^ (Nat.card ↥H).factorization 2 := by
    rw [← hcardH, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd (fun h2 => (Nat.not_even_iff_odd.mpr hrange_odd)
        (even_iff_two_dvd.mpr h2)), add_zero, ha, Nat.Prime.factorization_pow Nat.prime_two]
    simp
  let Z : Sylow 2 ↥H := Sylow.ofCard (P.subgroupOf H) hZcard
  have hZc : (Z : Subgroup ↥H) ≤ center ↥H := by
    intro x hx
    rw [mem_center_iff]
    intro g
    apply Subtype.ext
    have hx' : (x : G) ∈ P := hx
    exact ((mem_centralizer_iff.mp (hHC g.2)) x hx').symm
  obtain ⟨K, hKn, hKodd, hKmem⟩ := exists_odd_normal_of_central_sylow Z hZc
  have hHK : H ≤ K.map H.subtype := by
    refine (closure_le _).mpr fun x hx => ?_
    have hxS := hconjodd x hx
    have hxH : x ∈ H := subset_normalClosure hxS
    refine ⟨⟨x, hxH⟩, hKmem _ ?_, rfl⟩
    rw [Subgroup.orderOf_mk]
    exact hxS
  have hHodd : Odd (Nat.card H) := by
    have h1 := Subgroup.card_le_of_le hHK
    rw [Subgroup.card_map_of_injective H.subtype_injective] at h1
    have h2 : Nat.card K ≤ Nat.card ↥H := Subgroup.card_le_card_group K
    have h3 : Nat.card K = Nat.card ↥H := le_antisymm h2 h1
    rw [← h3]
    exact hKodd
  have hHO : H ≤ pPrimeCore 2 G :=
    le_sSup ⟨inferInstance, Nat.coprime_two_left.mpr hHodd⟩
  rw [IsPGroup.iff_orderOf]
  intro q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨b, m', hm', hgo⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
  have hgb : g ^ (2 ^ b) ∈ Sodd := by
    show Odd (orderOf (g ^ (2 ^ b)))
    rw [orderOf_pow_of_dvd (by positivity) (by rw [hgo]; exact Dvd.intro m' rfl), hgo,
      Nat.mul_div_cancel_left _ (by positivity)]
    exact hm'
  have h1 : (QuotientGroup.mk g : G ⧸ pPrimeCore 2 G) ^ (2 ^ b) = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hHO (subset_normalClosure hgb)
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h1)
  exact ⟨k, hk⟩

end L415

end CFSG.ComponentClassification.HarrisLit
