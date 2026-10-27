module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34Basics
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34Struct

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem l34abel_eq_one_of_mk {x : G} {c : ↥(centralizer ({x} : Set G))} {n : ℕ}
    (hc : (c : G) ^ 3 ^ n = 1)
    (h1 : QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) 3) c = 1) :
    c = 1 := by
  have hcO : c ∈ primeComplementCore (G := centralizer ({x} : Set G)) 3 :=
    (QuotientGroup.eq_one_iff _).mp h1
  have h2 : orderOf c ∣ Nat.card (primeComplementCore (G := centralizer ({x} : Set G)) 3) := by
    have := orderOf_dvd_natCard
      (⟨c, hcO⟩ : primeComplementCore (G := centralizer ({x} : Set G)) 3)
    rwa [Subgroup.orderOf_mk] at this
  have h3 : orderOf c ∣ 3 ^ n := orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hc))
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
    (Nat.Coprime.pow_left n (primeComplementCore_coprime 3)) h3 h2)

theorem l34abel_mk_self_mem (x : G) (J : Subgroup G) :
    QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) 3)
      ⟨x, mem_centralizer_singleton_iff.mpr rfl⟩ ∈ reducedCentralizerOfJ x J := by
  rw [r1s_reducedCentralizerOfJ_eq, mem_centralizer_iff]
  intro h _
  obtain ⟨c, rfl⟩ :=
    QuotientGroup.mk'_surjective (primeComplementCore (G := centralizer ({x} : Set G)) 3) h
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (mem_centralizer_singleton_iff.mp c.2)

theorem l34abel_not_mem {M : Subgroup G} {x : G} {J : Subgroup G}
    (hK1 : KFactL34TwoSignalizer) (hK2 : KFactL34Three) (hJ : IsL34Normal M x J)
    (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1) : x ∉ J := by
  intro hxJ
  have hxC : x ∈ centralizer ({x} : Set G) := mem_centralizer_singleton_iff.mpr rfl
  have h : QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) 3)
      ⟨x, hxC⟩ ∈ r1sBar x J ⊓ reducedCentralizerOfJ x J :=
    ⟨⟨⟨x, hxC⟩, Subgroup.mem_subgroupOf.mpr hxJ, rfl⟩, l34abel_mk_self_mem x J⟩
  rw [l34_bar_inf_reducedCentralizer_eq_bot hK1 hK2 hJ, Subgroup.mem_bot] at h
  exact hx1 (congrArg Subtype.val (l34abel_eq_one_of_mk (n := 1) (by rwa [pow_one]) h))

theorem l34abel_mem_sup {M : Subgroup G} {P : Sylow 3 G} {x : G} {J : Subgroup G}
    (hJ : IsL34Normal M x J) (hR1 : L34Prop34 3 P J x) {b : GenericReduced 3 x}
    (hb : b ^ 3 = 1) : b ∈ r1sBar x J ⊔ reducedCentralizerOfJ x J := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  set O : Subgroup C := primeComplementCore (G := C) 3 with hO
  obtain ⟨hPC, -, -, hΩ, -⟩ := hR1
  have hJn := r1sBar_normal_l34 hJ
  have hDn := l34_reducedCentralizer_normal hJ
  have hNn : (r1sBar x J ⊔ reducedCentralizerOfJ x J).Normal := Subgroup.sup_normal _ _
  set Pb : Sylow 3 (GenericReduced 3 x) :=
    (P.subtype hPC).mapSurjective (QuotientGroup.mk'_surjective O) with hPb
  have hb3 : IsPGroup 3 (zpowers b) := by
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
      (orderOf_dvd_of_pow_eq_one (show b ^ 3 ^ 1 = 1 by rwa [pow_one]))
    exact IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])
  obtain ⟨R, hR⟩ := hb3.exists_le_sylow
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq (GenericReduced 3 x) Pb R
  have hbR : b ∈ (R : Subgroup (GenericReduced 3 x)) := hR (mem_zpowers b)
  rw [← hy, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hbR
  obtain ⟨pb, hpb, hpbb⟩ := hbR
  rw [hPb, Sylow.coe_mapSurjective, Sylow.coe_subtype] at hpb
  obtain ⟨c, hcP, rfl⟩ := hpb
  have hcP' : (c : G) ∈ (P : Subgroup G) := Subgroup.mem_subgroupOf.mp hcP
  have hpbb' : (MulAut.conj y) (QuotientGroup.mk' O c) = b := hpbb
  have hc3 : (c : G) ^ 3 = 1 := by
    have h1 : QuotientGroup.mk' O (c ^ 3) = 1 := by
      have h2 : (MulAut.conj y) (QuotientGroup.mk' O c ^ 3) = 1 := by rw [map_pow, hpbb', hb]
      rw [map_pow]
      exact (MulEquiv.map_eq_one_iff _).mp h2
    obtain ⟨n, hn⟩ := P.isPGroup' ⟨c, hcP'⟩
    have hn' : (c : G) ^ 3 ^ n = 1 := by simpa using congrArg Subtype.val hn
    have h4 : ((c ^ 3 : C) : G) ^ 3 ^ n = 1 := by
      rw [Subgroup.coe_pow, ← pow_mul, mul_comm, pow_mul, hn', one_pow]
    simpa using congrArg Subtype.val (l34abel_eq_one_of_mk h4 h1)
  have hW : ((P : Subgroup G) ⊓ J) ⊔ zpowers x ≤
      ((r1sBar x J ⊔ reducedCentralizerOfJ x J).comap (QuotientGroup.mk' O)).map C.subtype := by
    refine sup_le (fun j hj => ?_) ?_
    · exact ⟨⟨j, hJ.le_centralizer hj.2⟩,
        mem_sup_left ⟨⟨j, hJ.le_centralizer hj.2⟩, Subgroup.mem_subgroupOf.mpr hj.2, rfl⟩, rfl⟩
    · rw [zpowers_le]
      exact ⟨⟨x, mem_centralizer_singleton_iff.mpr rfl⟩, mem_sup_right (l34abel_mk_self_mem x J),
        rfl⟩
  obtain ⟨c', hc'N, hc'c⟩ := hW (hΩ c hcP' hc3)
  have hcc : c' = c := Subtype.ext hc'c
  subst hcc
  rw [← hpbb']
  exact hNn.conj_mem _ hc'N y

theorem l34abel_pow_three_of_mem_bar {M : Subgroup G} {x : G} {J : Subgroup G}
    (hK1 : KFactL34TwoSignalizer) (hK2 : KFactL34Three) (hJ : IsL34Normal M x J)
    {a : GenericReduced 3 x} (ha : a ∈ r1sBar x J) (h3 : ∃ n : ℕ, a ^ 3 ^ n = 1) :
    a ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n, hn⟩ := h3
  obtain ⟨c, hc⟩ := exists_orderOf_eq_prime_pow_iff.mpr
    (⟨n, Subtype.ext (by simpa using hn)⟩ : ∃ m : ℕ, (⟨a, ha⟩ : ↥(r1sBar x J)) ^ 3 ^ m = 1)
  have hz : IsPGroup 3 (zpowers (⟨a, ha⟩ : ↥(r1sBar x J))) :=
    IsPGroup.of_card (n := c) (by rw [Nat.card_zpowers, hc])
  obtain ⟨T, hT⟩ := hz.exists_le_sylow
  have h := (r1sBar_sylow_facts_l34 hK1 hK2 hJ T).1.2 _ (hT (mem_zpowers _))
  simpa using congrArg Subtype.val h

theorem l34abel_comm_of_le (hK1 : KFactL34TwoSignalizer) {X : Type} [Group X] [Finite X]
    {K : Subgroup X} (hKt : IsRankThreeL34 ↥K) {A : Subgroup X} (hA : IsPGroup 3 A) (hAK : A ≤ K)
    {a b : X} (ha : a ∈ A) (hb : b ∈ A) : a * b = b * a := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨T, hT⟩ := (hA.comap_subtype (K := K)).exists_le_sylow
  have := (hK1 ↥K hKt T).1.1
  have h := (IsMulCommutative.is_comm (M := (T : Subgroup K))).comm
    ⟨⟨a, hAK ha⟩, hT (show (⟨a, hAK ha⟩ : K) ∈ A.comap K.subtype from ha)⟩
    ⟨⟨b, hAK hb⟩, hT (show (⟨b, hAK hb⟩ : K) ∈ A.comap K.subtype from hb)⟩
  exact congrArg (fun t : (T : Subgroup K) => ((t : K) : X)) h

end CFSG.LocalAnalysis.RankThreeTheoremC
