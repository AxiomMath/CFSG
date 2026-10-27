module

public import CFSG.GH74.Generic.BProg.B2.Defs
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.GH74.Generic.BProg.B2.SD.TwoA7

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.GH74.Uniqueness
  CFSG.ABGLocalTools CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup

@[expose] def QbarSylow {G : Type} [Group G] (M K Q : Subgroup G) : Prop :=
  IsSylowOf 2 (barIn M Q) (centralizer ((barIn M K : Subgroup (Mbar M)) : Set (Mbar M)))

namespace Syl

theorem isSylowOf_inf_of_isSubnormal {X : Type*} [Group X] [Finite X] {P : Subgroup X}
    (hP : IsSylowOf 2 P ⊤) {H : Subgroup X} (hH : H.IsSubnormal) :
    IsSylowOf 2 (P ⊓ H) H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  induction hH with
  | top => simpa using hP
  | step H K hHK _ hN ih =>
    have h1 := ih.inf_of_le_normalizer hHK
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hHK).mp hN)
    rwa [inf_assoc, inf_eq_right.mpr hHK] at h1

theorem isSylowOf_inf_of_isSubnormal_of_le {X : Type*} [Group X] [Finite X] {T C J : Subgroup X}
    (hT : IsSylowOf 2 T C) (hJC : J ≤ C) (hJ : J.IsSubnormal) :
    IsSylowOf 2 (T ⊓ J) J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := hT.exists_sylow_eq_subgroupOf
  have hS' : IsSylowOf 2 (S : Subgroup ↥C) ⊤ := by
    rw [isSylowOf_iff]
    exact ⟨le_top, S.isPGroup', by rw [Subgroup.relIndex_top_right]; exact S.not_dvd_index⟩
  have hJ' : (J.subgroupOf C).IsSubnormal := hJ.comap C.subtype
  have key := isSylowOf_inf_of_isSubnormal hS' hJ'
  have e : T.subgroupOf C ⊓ J.subgroupOf C = (T ⊓ J).subgroupOf C :=
    (Subgroup.comap_inf _ _ _).symm
  rw [hS, e] at key
  have h2 := (isSylowOf_map_subtype_iff C).2 key
  rwa [Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.2 (inf_le_right.trans hJC), inf_eq_left.2 hJC] at h2

theorem eq_one_of_two_pow_of_mem_pPrimeCore {Y : Type} [Group Y] [Finite Y] {c : Y}
    (hc : c ∈ pPrimeCore 2 Y) {n : ℕ} (hcn : c ^ (2 ^ n) = 1) : c = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : orderOf c ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hcn
  have h2 : orderOf c ∣ Nat.card (pPrimeCore 2 Y) := Subgroup.orderOf_dvd_natCard _ hc
  have h3 : orderOf c = 1 :=
    Nat.eq_one_of_dvd_coprimes ((CFSG.pPrimeCore_coprime_card (p := 2) (G := Y)).pow_left n) h1 h2
  exact orderOf_eq_one_iff.1 h3

theorem isSylowOf_barIn_inf {G : Type} [Group G] [Finite G] {M K Q : Subgroup G}
    (hQS : QbarSylow M K Q) {J : Subgroup (Mbar M)} (hJ : IsComponent J)
    (hJK : ∀ j ∈ J, ∀ k ∈ (barIn M K : Subgroup (Mbar M)), j * k = k * j) :
    IsSylowOf 2 (barIn M Q ⊓ J) J := by
  have hT : IsSylowOf 2 (barIn M Q)
      (centralizer ((barIn M K : Subgroup (Mbar M)) : Set (Mbar M))) := hQS
  exact isSylowOf_inf_of_isSubnormal_of_le hT
    (fun j hj => Subgroup.mem_centralizer_iff.2 fun k hk => (hJK j hj k hk).symm) hJ.2

end Syl

variable {G : Type} [Group G] [Finite G]

theorem exists_u {x : G} {K A M P Q H : Subgroup G} (hs : Stage2Setup G x K A M P Q)
    (h1 : Stage2Concl1Core x K M Q H) (hQS : QbarSylow M K Q) (J : Subgroup (Mbar M))
    (hJ : IsComponent J) (hdc : IsDoubleCoverOfAlt ↥J 7)
    (hJK : ∀ j ∈ J, ∀ k ∈ (barIn M K : Subgroup (Mbar M)), j * k = k * j) :
    ∃ u : G, u ∈ Q ∧ orderOf u = 2 ∧ ∃ hu : u ∈ M,
      (QuotientGroup.mk (⟨u, hu⟩ : ↥M) : Mbar M) ∈ J ∧
      ∀ j ∈ J, (QuotientGroup.mk (⟨u, hu⟩ : ↥M) : Mbar M) * j =
        j * (QuotientGroup.mk (⟨u, hu⟩ : ↥M) : Mbar M) := by
  have _h1 := h1
  have hSyl : IsSylowOf 2 (barIn M Q ⊓ J) J := Syl.isSylowOf_barIn_inf hQS hJ hJK
  obtain ⟨S, hS⟩ := hSyl.exists_sylow_eq_subgroupOf
  have hc2 : Nat.card ↥(center ↥J) = 2 := hdc.2.1
  have hZ2 : IsPGroup 2 ↥(center ↥J) := IsPGroup.of_card (n := 1) (by rw [hc2, pow_one])
  have hZS : center ↥J ≤ (S : Subgroup ↥J) := hZ2.le_sylow_of_normal S
  obtain ⟨z, hz1⟩ : ∃ z : ↥(center ↥J), z ≠ 1 := by
    obtain ⟨y, hy, -⟩ := (Nat.card_eq_two_iff' (1 : ↥(center ↥J))).1 hc2
    exact ⟨y, hy⟩
  have hzz : z * z = 1 := by
    have := pow_card_eq_one' (G := ↥(center ↥J)) (x := z)
    rwa [hc2, pow_two] at this
  have hzJ : ((z : ↥J) : Mbar M) ∈ barIn M Q ⊓ J := by
    have : (z : ↥J) ∈ (S : Subgroup ↥J) := hZS z.2
    rw [hS] at this
    exact this
  obtain ⟨qm, hqm, hqz⟩ := hzJ.1
  have hqQ : (qm : G) ∈ Q := hqm
  have hQP : Q ≤ P := by rw [hs.Q_eq]; exact inf_le_left
  have hmk : (QuotientGroup.mk qm : Mbar M) = ((z : ↥J) : Mbar M) := hqz
  have hu1 : (qm : G) ≠ 1 := by
    intro h
    have h0 : qm = 1 := Subtype.ext h
    apply hz1
    have h2 : ((z : ↥J) : Mbar M) = 1 := by
      rw [← hmk, h0]
      exact QuotientGroup.mk_one _
    exact Subtype.ext (Subtype.ext h2)
  have hsq : (qm : G) * (qm : G) = 1 := by
    have hmem : qm * qm ∈ pPrimeCore 2 ↥M := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, hmk]
      exact congrArg (fun w : ↥(center ↥J) => ((w : ↥J) : Mbar M)) hzz
    obtain ⟨n, hn⟩ := hs.sylowP.isPGroup (⟨(qm : G), hQP hqQ⟩ : ↥P)
    have hn' : (qm : G) ^ (2 ^ n) = 1 := by simpa using congrArg Subtype.val hn
    have hqn : qm ^ (2 ^ n) = 1 := Subtype.ext (by simpa using hn')
    have hpow : (qm * qm) ^ (2 ^ n) = 1 := by
      rw [← pow_two, ← pow_mul, mul_comm, pow_mul, hqn, one_pow]
    exact congrArg Subtype.val (Syl.eq_one_of_two_pow_of_mem_pPrimeCore hmem hpow)
  have hord : orderOf (qm : G) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hsq) hu1
  refine ⟨qm, hqQ, hord, qm.2, ?_, ?_⟩
  · show (QuotientGroup.mk qm : Mbar M) ∈ J
    rw [hmk]
    exact (z : ↥J).2
  · intro j hj
    show (QuotientGroup.mk qm : Mbar M) * j = j * (QuotientGroup.mk qm : Mbar M)
    rw [hmk]
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.1 z.2 ⟨j, hj⟩)).symm

end CFSG.GH74.Generic.BProg.B2.SD.TwoA7
