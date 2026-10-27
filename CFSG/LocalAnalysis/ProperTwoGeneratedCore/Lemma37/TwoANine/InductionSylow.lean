module

public import CFSG.CharacterTheory.Semidihedral.Principal.PrimewiseScalarInvolution
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.BalanceSignalizer

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine

open Subgroup CFSG.Semidihedral.Principal.PrimewiseScalar

section General

variable {X : Type*} [Group X]

theorem odd_card_of_isPGroup [Finite X] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {P : Subgroup X}
    (hP : IsPGroup p P) : Odd (Nat.card P) := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP
  rw [hn]
  exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow

theorem mem_map_conj_iff {P : Subgroup X} {g y : X} :
    y ∈ P.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * y * g ∈ P := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

theorem mem_normalizer_subgroupOf_of_mem {C Y : Subgroup X} {c : C}
    (hc : (c : X) ∈ normalizer (Y : Set X)) : c ∈ normalizer (Y.subgroupOf C : Set C) :=
  Subgroup.mem_normalizer_iff.mpr fun d => by
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact Subgroup.mem_normalizer_iff.mp hc d

theorem inf_mem_normalizer {A B : Subgroup X} {g : X} (hA : g ∈ normalizer (A : Set X))
    (hB : g ∈ normalizer (B : Set X)) : g ∈ normalizer ((A ⊓ B : Subgroup X) : Set X) :=
  Subgroup.mem_normalizer_iff.mpr fun y => and_congr (Subgroup.mem_normalizer_iff.mp hA y)
    (Subgroup.mem_normalizer_iff.mp hB y)

theorem odd_card_sup_of_le_normalizer [Finite X] {H N : Subgroup X}
    (hHN : H ≤ normalizer (N : Set X)) (hH : Odd (Nat.card H)) (hN : Odd (Nat.card N)) :
    Odd (Nat.card (H ⊔ N : Subgroup X)) := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hHN
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hHN
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient H N hHN
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf (H ⊔ N)),
    ← Nat.card_congr e.toEquiv,
    Nat.card_congr (subgroupOfEquivOfLe (le_sup_right : N ≤ H ⊔ N)).toEquiv]
  exact (Odd.of_dvd_nat hH (Subgroup.card_quotient_dvd_card _)).mul hN

end General

section OddCore

variable {X : Type} [Group X]

theorem odd_card_oddCoreOf [Finite X] (C : Subgroup X) : Odd (Nat.card (oddCoreOf C)) := by
  rw [oddCoreOf, Subgroup.card_map_of_injective C.subtype_injective]
  exact Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card

theorem oddCoreOf_le (C : Subgroup X) : oddCoreOf C ≤ C :=
  Subgroup.map_subtype_le _

theorem le_normalizer_oddCoreOf (C : Subgroup X) : C ≤ normalizer (oddCoreOf C : Set X) := by
  calc C = (⊤ : Subgroup C).map C.subtype := by
        rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    _ = (normalizer (CFSG.pPrimeCore 2 C : Set C)).map C.subtype := by
        rw [Subgroup.normalizer_eq_top]
    _ ≤ _ := Subgroup.le_normalizer_map _

theorem le_oddCoreOf {C Y : Subgroup X} (hY : Y ≤ C) (hYn : C ≤ normalizer (Y : Set X))
    (hodd : Odd (Nat.card Y)) : Y ≤ oddCoreOf C := by
  have hnormal : (Y.subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hY).mpr hYn
  have hcop : Nat.Coprime 2 (Nat.card (Y.subgroupOf C)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hY).toEquiv]
    exact Nat.coprime_two_left.mpr hodd
  have hle : Y.subgroupOf C ≤ CFSG.pPrimeCore 2 C := le_sSup ⟨hnormal, hcop⟩
  rw [← Subgroup.map_subgroupOf_eq_of_le hY]
  exact Subgroup.map_mono hle

theorem le_pPrimeCore_of_normal [Finite X] {N : Subgroup X} (hN : N.Normal)
    (hodd : Odd (Nat.card N)) : N ≤ CFSG.pPrimeCore 2 X :=
  le_sSup ⟨hN, Nat.coprime_two_left.mpr hodd⟩

end OddCore

section Sylow

variable {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]

omit [Finite X] [Fact p.Prime] in
theorem isPGroup_of_isSylowOf {K P : Subgroup X} (hP : IsSylowOf K p P) : IsPGroup p P := by
  obtain ⟨Q, rfl⟩ := hP
  exact Q.isPGroup'.map K.subtype

omit [Finite X] [Fact p.Prime] in
theorem le_isSylowOf_of_le_normalizer {K P Q : Subgroup X} (hP : IsSylowOf K p P)
    (hQ : IsPGroup p Q) (hQK : Q ≤ K) (hKQ : K ≤ normalizer (Q : Set X)) : Q ≤ P := by
  obtain ⟨P₀, rfl⟩ := hP
  have : (Q.subgroupOf K).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hQK).mpr hKQ
  have hQ' : IsPGroup p (Q.subgroupOf K) := hQ.comap_subtype
  rw [← Subgroup.map_subgroupOf_eq_of_le hQK]
  exact Subgroup.map_mono (hQ'.le_sylow_of_normal P₀)

theorem card_le_of_isSylowOf {K P Q : Subgroup X} (hP : IsSylowOf K p P) (hQ : IsPGroup p Q)
    (hQK : Q ≤ K) : Nat.card Q ≤ Nat.card P := by
  obtain ⟨Q₁, hQ₁⟩ := (hQ.comap_subtype (K := K)).exists_le_sylow
  rw [card_isSylowOf hP, ← Sylow.card_eq_multiplicity Q₁,
    ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQK).toEquiv]
  exact Subgroup.card_le_of_le hQ₁

theorem isSylowOf_of_card_eq {K P Q : Subgroup X} (hP : IsSylowOf K p P) (hQK : Q ≤ K)
    (hcard : Nat.card Q = Nat.card P) : IsSylowOf K p Q := by
  refine ⟨Sylow.ofCard (Q.subgroupOf K) ?_, ?_⟩
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQK).toEquiv, hcard, card_isSylowOf hP]
  · rw [Sylow.coe_ofCard, Subgroup.map_subgroupOf_eq_of_le hQK]

theorem exists_map_conj_eq_of_isSylowOf {K P Q : Subgroup X} (hP : IsSylowOf K p P)
    (hQ : IsSylowOf K p Q) : ∃ k ∈ K, P.map (MulAut.conj k).toMonoidHom = Q := by
  obtain ⟨P₀, rfl⟩ := hP
  obtain ⟨Q₀, rfl⟩ := hQ
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq K P₀ Q₀
  have hk' : (P₀ : Subgroup K).map (MulAut.conj k).toMonoidHom = Q₀ := by
    rw [← hk, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  refine ⟨k, k.2, ?_⟩
  rw [← hk', Subgroup.map_map, Subgroup.map_map]
  rfl

theorem exists_mem_inv_mul_mem_normalizer {K P : Subgroup X} (hP : IsSylowOf K p P) {g : X}
    (hg : g ∈ normalizer (K : Set X)) : ∃ k ∈ K, k⁻¹ * g ∈ normalizer (P : Set X) := by
  have hPK : P ≤ K := le_of_isSylowOf hP
  have hP'K : P.map (MulAut.conj g).toMonoidHom ≤ K := by
    rintro _ ⟨x, hx, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hg x).mp (hPK hx)
  obtain ⟨k, hkK, hk⟩ := exists_map_conj_eq_of_isSylowOf hP (isSylowOf_of_card_eq hP hP'K
    (Subgroup.card_map_of_injective (MulAut.conj g).injective))
  refine ⟨k, hkK, Subgroup.mem_normalizer_iff.mpr fun y => ?_⟩
  have h1 : y ∈ P ↔ g * y * g⁻¹ ∈ P.map (MulAut.conj g).toMonoidHom := by
    rw [mem_map_conj_iff, show g⁻¹ * (g * y * g⁻¹) * g = y by group]
  rw [h1, ← hk, mem_map_conj_iff, show (k⁻¹ * g) * y * (k⁻¹ * g)⁻¹ = k⁻¹ * (g * y * g⁻¹) * k by
    group]

theorem lt_inf_normalizer_of_lt {P R : Subgroup X} (hR : IsPGroup p R) (hPR : P < R) :
    P < R ⊓ normalizer (P : Set X) := by
  have : Group.IsNilpotent R := hR.isNilpotent
  have hlt : P.subgroupOf R < ⊤ :=
    lt_top_iff_ne_top.mpr fun h => hPR.ne (le_antisymm hPR.le (Subgroup.subgroupOf_eq_top.mp h))
  obtain ⟨r, hr, hrP⟩ := IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
  refine lt_of_le_of_ne (le_inf hPR.le Subgroup.le_normalizer) fun h => hrP ?_
  have hrN : (r : X) ∈ normalizer (P : Set X) := Subgroup.mem_normalizer_iff.mpr fun y => by
    constructor
    · intro hy
      have h' := (Subgroup.mem_normalizer_iff.mp hr ⟨y, hPR.le hy⟩).mp
        (Subgroup.mem_subgroupOf.mpr hy)
      exact Subgroup.mem_subgroupOf.mp h'
    · intro hy
      have hyR : y ∈ R := by
        have h2 := R.mul_mem (R.mul_mem (R.inv_mem r.2) (hPR.le hy)) r.2
        rwa [show (r : X)⁻¹ * (r * y * (r : X)⁻¹) * r = y by group] at h2
      exact Subgroup.mem_subgroupOf.mp ((Subgroup.mem_normalizer_iff.mp hr ⟨y, hyR⟩).mpr
        (Subgroup.mem_subgroupOf.mpr hy))
  have hrmem : (r : X) ∈ R ⊓ normalizer (P : Set X) := ⟨r.2, hrN⟩
  rw [← h] at hrmem
  exact Subgroup.mem_subgroupOf.mpr hrmem

theorem isSylowOf_of_isSylowOf_inf_normalizer {K P : Subgroup X} (hPK : P ≤ K)
    (hP : IsSylowOf (K ⊓ normalizer (P : Set X)) p P) : IsSylowOf K p P := by
  obtain ⟨Q₀, hQ₀⟩ := ((isPGroup_of_isSylowOf hP).comap_subtype (K := K)).exists_le_sylow
  have hPQ : P ≤ (Q₀ : Subgroup K).map K.subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hPK]
    exact Subgroup.map_mono hQ₀
  have hQp : IsPGroup p ((Q₀ : Subgroup K).map K.subtype) := Q₀.isPGroup'.map _
  rcases hPQ.lt_or_eq with hlt | heq
  · have h1 := Subgroup.card_lt_of_lt (lt_inf_normalizer_of_lt hQp hlt)
    have h2 := card_le_of_isSylowOf hP (hQp.to_le inf_le_left)
      (inf_le_inf_right _ (Subgroup.map_subtype_le _))
    exact absurd h1 (not_lt.mpr h2)
  · exact ⟨Q₀, heq.symm⟩

theorem exists_isSylowOf_le_normalizer {K S : Subgroup X} (hK : Odd (Nat.card K))
    (hS : IsPGroup 2 S) (hSK : S ≤ normalizer (K : Set X)) :
    ∃ P : Subgroup X, IsSylowOf K p P ∧ S ≤ normalizer (P : Set X) := by
  have : Subgroup.Normalizes S K := ⟨hSK⟩
  have : Fact (IsPGroup 2 S) := ⟨hS⟩
  obtain ⟨Q, hQ⟩ := CFSG.exists_invariant_sylow_of_pgroup_operator_coprime (G := K) (A := S)
    (r := 2) (p := p) (Nat.coprime_two_left.mpr hK)
  refine ⟨(Q : Subgroup K).map K.subtype, ⟨Q, rfl⟩, fun s hs =>
    Subgroup.mem_normalizer_iff.mpr fun y => ⟨?_, ?_⟩⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨(⟨s, hs⟩ : S) • x, (hQ.invariant ⟨s, hs⟩ x).mp hx, ?_⟩
    rw [Subgroup.coe_subtype, Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
  · rintro ⟨x, hx, hxy⟩
    rw [Subgroup.coe_subtype] at hxy
    have hyK : y ∈ K := by
      have h1 := (Subgroup.mem_normalizer_iff.mp (hSK (S.inv_mem hs)) x).mp x.2
      rwa [hxy, inv_inv, show s⁻¹ * (s * y * s⁻¹) * s = y by group] at h1
    refine ⟨⟨y, hyK⟩, (hQ.invariant ⟨s, hs⟩ ⟨y, hyK⟩).mpr ?_, rfl⟩
    have h2 : ((⟨s, hs⟩ : S) • (⟨y, hyK⟩ : K) : K) = x := by
      apply Subtype.ext
      rw [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
      exact hxy.symm
    rw [h2]
    exact hx

end Sylow

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine
