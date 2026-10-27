module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Defs
public import CFSG.GroupTheory.ABGLocalTools.Constraint
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem odd_card_oddCoreIn [Finite G] (K : Subgroup G) : Odd (Nat.card (oddCoreIn K)) := by
  rw [oddCoreIn, CFSG.inSubgroup, Subgroup.card_map_of_injective K.subtype_injective]
  exact CFSG.ABGLocalTools.odd_card_oddCore

theorem odd_orderOf_of_mem_oddCoreIn [Finite G] {K : Subgroup G} {x : G}
    (hx : x ∈ oddCoreIn K) : Odd (orderOf x) := by
  rw [oddCoreIn, CFSG.inSubgroup, Subgroup.mem_map] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  have hdvd : orderOf y ∣ Nat.card (CFSG.oddCore ↥K) := Subgroup.orderOf_dvd_natCard _ hy
  have hodd : Odd (Nat.card (CFSG.oddCore ↥K)) := CFSG.ABGLocalTools.odd_card_oddCore
  have hxy : orderOf x = orderOf y := by
    rw [← hyx]
    exact Subgroup.orderOf_coe y
  rw [hxy]
  exact hodd.of_dvd_nat hdvd

theorem le_oddCoreIn_of_normal [Finite G] {K N : Subgroup G} (hNK : N ≤ K)
    (hN : (N.subgroupOf K).Normal) (hodd : Odd (Nat.card N)) : N ≤ oddCoreIn K := by
  intro x hx
  rw [oddCoreIn, CFSG.inSubgroup, Subgroup.mem_map]
  refine ⟨⟨x, hNK hx⟩, ?_, rfl⟩
  have hcard : Nat.card (N.subgroupOf K) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNK).toEquiv
  have hodd' : Odd (Nat.card (N.subgroupOf K)) := by rw [hcard]; exact hodd
  exact CFSG.ABGLocalTools.le_oddCore_of_normal hN hodd' (Subgroup.mem_subgroupOf.mpr hx)

theorem oddCoreIn_normal [Finite G] (K : Subgroup G) :
    oddCoreIn K ≤ K ∧ ((oddCoreIn K).subgroupOf K).Normal := by
  refine ⟨Subgroup.map_subtype_le _, ?_⟩
  have h : (oddCoreIn K).subgroupOf K = CFSG.oddCore ↥K := by
    rw [oddCoreIn, CFSG.inSubgroup]
    exact Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
  rw [h]
  infer_instance

theorem conj_mem_oddCoreIn [Finite G] {K : Subgroup G} {n : G} (hn : n ∈ normalizer (K : Set G))
    {x : G} (hx : x ∈ oddCoreIn K) : n * x * n⁻¹ ∈ oddCoreIn K := by
  set N : Subgroup G := (oddCoreIn K).map (MulAut.conj n).toMonoidHom with hN
  have hxN : n * x * n⁻¹ ∈ N := by
    rw [hN]
    exact Subgroup.mem_map_of_mem (f := (MulAut.conj n).toMonoidHom) hx
  have hNK : N ≤ K := by
    intro y hy
    rw [hN, Subgroup.mem_map] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    change n * z * n⁻¹ ∈ K
    exact (Subgroup.mem_normalizer_iff.mp hn z).mp ((oddCoreIn_normal K).1 hz)
  have hoddN : Odd (Nat.card N) := by
    rw [hN, Subgroup.card_map_of_injective (MulAut.conj n).injective]
    exact odd_card_oddCoreIn K
  have hNnorm : (N.subgroupOf K).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hNK]
    intro a b ha hb
    rw [hN, Subgroup.mem_map] at ha ⊢
    obtain ⟨z, hz, rfl⟩ := ha
    have hbK : n⁻¹ * b * n ∈ K := by
      have h1 : n * (n⁻¹ * b * n) * n⁻¹ = b := by group
      exact (Subgroup.mem_normalizer_iff.mp hn (n⁻¹ * b * n)).mpr (h1.symm ▸ hb)
    refine ⟨(n⁻¹ * b * n) * z * (n⁻¹ * b * n)⁻¹, ?_, ?_⟩
    · exact ((Subgroup.normal_subgroupOf_iff (oddCoreIn_normal K).1).mp
        (oddCoreIn_normal K).2 z (n⁻¹ * b * n) hz hbK)
    · change n * ((n⁻¹ * b * n) * z * (n⁻¹ * b * n)⁻¹) * n⁻¹ = b * (n * z * n⁻¹) * b⁻¹
      group
  exact le_oddCoreIn_of_normal hNK hNnorm hoddN hxN

theorem oddCoreIn_le_of_normal [Finite G] {K M : Subgroup G} (hKM : K ≤ M)
    (hK : (K.subgroupOf M).Normal) : oddCoreIn K ≤ oddCoreIn M := by
  have hMn : M ≤ normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKM).mp hK
  apply le_oddCoreIn_of_normal ((oddCoreIn_normal K).1.trans hKM) _ (odd_card_oddCoreIn K)
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer ((oddCoreIn_normal K).1.trans hKM)]
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    exact conj_mem_oddCoreIn (hMn hm) hy
  · intro hy
    have h := conj_mem_oddCoreIn (hMn (M.inv_mem hm)) hy
    convert h using 1
    group

private theorem transfer_ker_le_oddCoreIn [Finite G] {K : Subgroup G} (P : Sylow 2 ↥K)
    (hPc : Subgroup.normalizer (P : Set ↥K) ≤ Subgroup.centralizer (P : Set ↥K)) :
    ((MonoidHom.transferSylow P hPc).ker.map K.subtype ≤ oddCoreIn K) ∧
      ∀ x ∈ K, Odd (orderOf x) → x ∈ (MonoidHom.transferSylow P hPc).ker.map K.subtype := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTodd : Odd (Nat.card (MonoidHom.transferSylow P hPc).ker) :=
    Nat.not_even_iff_odd.mp fun h =>
      MonoidHom.not_dvd_card_ker_transferSylow P hPc (Even.two_dvd h)
  have hTle : (MonoidHom.transferSylow P hPc).ker.map K.subtype ≤ oddCoreIn K := by
    apply le_oddCoreIn_of_normal (Subgroup.map_subtype_le _)
    · have hEq : (((MonoidHom.transferSylow P hPc).ker.map K.subtype).subgroupOf K)
          = (MonoidHom.transferSylow P hPc).ker :=
        Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
      rw [hEq]
      infer_instance
    · rw [Subgroup.card_map_of_injective K.subtype_injective]
      exact hTodd
  refine ⟨hTle, fun x hxK hxodd => ?_⟩
  refine Subgroup.mem_map.mpr ⟨⟨x, hxK⟩, ?_, rfl⟩
  rw [MonoidHom.mem_ker]
  have hcop : Nat.Coprime 2 (orderOf (⟨x, hxK⟩ : ↥K)) := by
    rw [Nat.coprime_two_left, Subgroup.orderOf_mk]
    exact hxodd
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd (P.isPGroup'.orderOf_coprime hcop _)
    (orderOf_map_dvd (MonoidHom.transferSylow P hPc) _))

private theorem normalizer_sylow_le_centralizer [Finite G] {K Z : Subgroup G} (P : Sylow 2 ↥K)
    (hP : (P : Subgroup ↥K).map K.subtype = Z)
    (hcomm : ∀ k ∈ K, ∀ z ∈ Z, z * k = k * z) :
    Subgroup.normalizer (P : Set ↥K) ≤ Subgroup.centralizer (P : Set ↥K) := by
  intro n _
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  apply Subtype.ext
  have hzZ : ((z : ↥K) : G) ∈ Z := by
    rw [← hP, Subgroup.mem_map]
    exact ⟨z, hz, rfl⟩
  exact hcomm (n : G) n.2 ((z : ↥K) : G) hzZ

theorem mem_oddCoreIn_iff_of_central_sylow [Finite G] {K Z : Subgroup G} (hZ : IsSylow2Of Z K)
    (hcomm : ∀ k ∈ K, ∀ z ∈ Z, z * k = k * z) {x : G} :
    x ∈ oddCoreIn K ↔ x ∈ K ∧ Odd (orderOf x) := by
  constructor
  · intro hx
    exact ⟨(oddCoreIn_normal K).1 hx, odd_orderOf_of_mem_oddCoreIn hx⟩
  · rintro ⟨hxK, hxodd⟩
    obtain ⟨P, hP⟩ := hZ.exists_sylow
    have hdata := transfer_ker_le_oddCoreIn P (normalizer_sylow_le_centralizer P hP hcomm)
    exact hdata.1 (hdata.2 x hxK hxodd)

theorem sup_oddCoreIn_of_central_sylow [Finite G] {K Z : Subgroup G} (hZ : IsSylow2Of Z K)
    (hcomm : ∀ k ∈ K, ∀ z ∈ Z, z * k = k * z) : Z ⊔ oddCoreIn K = K := by
  apply le_antisymm
  · exact sup_le hZ.1 (oddCoreIn_normal K).1
  · intro k hk
    obtain ⟨P, hP⟩ := hZ.exists_sylow
    have hPc := normalizer_sylow_le_centralizer P hP hcomm
    have hTle := (transfer_ker_le_oddCoreIn P hPc).1
    obtain ⟨⟨o, z⟩, hoz, -⟩ :=
      (MonoidHom.ker_transferSylow_isComplement' P hPc).existsUnique ⟨k, hk⟩
    have hoO : (((o : (MonoidHom.transferSylow P hPc).ker) : ↥K) : G) ∈ oddCoreIn K :=
      hTle (Subgroup.mem_map.mpr ⟨(o : ↥K), o.2, rfl⟩)
    have hzZ : (((z : P) : ↥K) : G) ∈ Z := by
      rw [← hP, Subgroup.mem_map]
      exact ⟨(z : P), z.2, rfl⟩
    have hozG : ((o : ↥K) : G) * ((z : ↥K) : G) = k := congrArg Subtype.val hoz
    have hzco : ((z : ↥K) : G) * ((o : ↥K) : G) = ((o : ↥K) : G) * ((z : ↥K) : G) :=
      hcomm ((o : ↥K) : G) (o : ↥K).2 ((z : ↥K) : G) hzZ
    rw [← hozG, ← hzco]
    exact Subgroup.mul_mem_sup hzZ hoO

theorem commute_of_normal_two_odd [Finite G] {K P O : Subgroup G} (hPK : P ≤ K) (hOK : O ≤ K)
    (hPn : (P.subgroupOf K).Normal) (hOn : (O.subgroupOf K).Normal) (hP : IsPGroup 2 P)
    (hO : Odd (Nat.card O)) : ∀ p ∈ P, ∀ o ∈ O, p * o = o * p := by
  intro p hp o ho
  have hdis : Disjoint (P.subgroupOf K) (O.subgroupOf K) := by
    rw [Subgroup.disjoint_def]
    intro x hxP hxO
    have hdvdP : orderOf (x : G) ∣ Nat.card P := Subgroup.orderOf_dvd_natCard P hxP
    have hdvdO : orderOf (x : G) ∣ Nat.card O := Subgroup.orderOf_dvd_natCard O hxO
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hP
    have hdvd2 : orderOf (x : G) ∣ 2 ^ m := by rw [← hm]; exact hdvdP
    have hcop : Nat.Coprime (orderOf (x : G)) (Nat.card O) :=
      Nat.Coprime.coprime_dvd_left hdvd2 (Nat.Coprime.pow_left m (Nat.coprime_two_left.mpr hO))
    apply Subtype.ext
    exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop hdvdO)
  have hcomm := Subgroup.commute_of_normal_of_disjoint (P.subgroupOf K) (O.subgroupOf K) hPn hOn
    hdis ⟨p, hPK hp⟩ ⟨o, hOK ho⟩ (Subgroup.mem_subgroupOf.mpr hp) (Subgroup.mem_subgroupOf.mpr ho)
  exact Subtype.ext_iff.mp hcomm

end CFSG.OddStandard.SmallF3.Omega
