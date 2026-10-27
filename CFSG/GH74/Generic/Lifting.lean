module

public import CFSG.GH74.Generic.OuterInvolution

public section

namespace CFSG.GH74.Generic

open CFSG CFSG.GH74 CFSG.GH74.L5U5 Subgroup

theorem exists_lift_twoSubgroup {C : Type*} [Group C] [Finite C] (N : Subgroup C) [N.Normal]
    (Pb : Subgroup (C ⧸ N)) (hP : IsPGroup 2 Pb) :
    ∃ P : Subgroup C, IsPGroup 2 P ∧ P.map (QuotientGroup.mk' N) = Pb := by
  classical
  let Q : Subgroup C := Pb.comap (QuotientGroup.mk' N)
  let g : Q →* Pb := ((QuotientGroup.mk' N).comp Q.subtype).codRestrict Pb fun q => q.2
  have hg : Function.Surjective g := fun p => by
    obtain ⟨c, hc⟩ := QuotientGroup.mk'_surjective N (p : C ⧸ N)
    exact ⟨⟨c, show QuotientGroup.mk' N c ∈ Pb by rw [hc]; exact p.2⟩, Subtype.ext hc⟩
  obtain ⟨S⟩ : Nonempty (Sylow 2 Q) := inferInstance
  have hSg : (S : Subgroup Q).map g = ⊤ := by
    have h2 : (⊤ : Subgroup Pb) = (S.mapSurjective hg : Subgroup Pb) :=
      (S.mapSurjective hg).is_maximal' (hP.to_subgroup ⊤) le_top
    rw [Sylow.coe_mapSurjective] at h2
    exact h2.symm
  refine ⟨(S : Subgroup Q).map Q.subtype, S.isPGroup'.map Q.subtype, ?_⟩
  ext c
  constructor
  · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    exact s.2
  · intro hc
    have : (⟨c, hc⟩ : Pb) ∈ (S : Subgroup Q).map g := hSg ▸ Subgroup.mem_top _
    obtain ⟨s, hs, hsc⟩ := this
    refine ⟨s, ⟨s, hs, rfl⟩, ?_⟩
    exact congrArg Subtype.val hsc

theorem eq_one_of_isPGroup_of_mem_pPrimeCore {C : Type*} [Group C] [Finite C] {P : Subgroup C}
    (hP : IsPGroup 2 P) {n : C} (hnP : n ∈ P) (hnN : n ∈ pPrimeCore 2 C) : n = 1 := by
  obtain ⟨k, hk⟩ := hP ⟨n, hnP⟩
  have hk' : n ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have h1 : orderOf n ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have h2 : orderOf n ∣ Nat.card (pPrimeCore 2 C) := Subgroup.orderOf_dvd_natCard _ hnN
  have hcop : Nat.Coprime 2 (Nat.card (pPrimeCore 2 C)) := pPrimeCore_coprime_card
  have : Nat.Coprime (orderOf n) (2 ^ k) :=
    (Nat.Coprime.pow_right k (hcop.coprime_dvd_right h2).symm)
  exact orderOf_eq_one_iff.1 (this.eq_one_of_dvd h1)

theorem lift_twoSubgroup_injOn {C : Type*} [Group C] [Finite C] {P : Subgroup C}
    (hP : IsPGroup 2 P) {a b : C} (ha : a ∈ P) (hb : b ∈ P)
    (h : (QuotientGroup.mk a : C ⧸ pPrimeCore 2 C) = QuotientGroup.mk b) : a = b := by
  have hmem : b⁻¹ * a ∈ pPrimeCore 2 C := (QuotientGroup.eq).1 h.symm
  have := eq_one_of_isPGroup_of_mem_pPrimeCore hP (Subgroup.mul_mem _ (Subgroup.inv_mem _ hb) ha)
    hmem
  rw [inv_mul_eq_one] at this
  exact this.symm

variable {G : Type} [Group G] [Finite G]

theorem exists_involution_lift (x : G) {ub : CentralizerBar x} (hu2 : ub * ub = 1) :
    ∃ (u : G) (hu : u ∈ centralizer ({x} : Set G)), u * u = 1 ∧ barOf hu = ub := by
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  have hP : IsPGroup 2 (Subgroup.zpowers ub) := by
    rintro ⟨a, ha⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    refine ⟨1, Subtype.ext ?_⟩
    change (ub ^ n) ^ (2 ^ 1) = 1
    rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
      show ub ^ 2 = 1 by rw [sq]; exact hu2, one_zpow]
  obtain ⟨P, hP2, hPmap⟩ := exists_lift_twoSubgroup (pPrimeCore 2 ↥C) _ hP
  have hub : ub ∈ P.map (QuotientGroup.mk' (pPrimeCore 2 ↥C)) := hPmap ▸ Subgroup.mem_zpowers ub
  obtain ⟨u₀, hu₀P, hu₀⟩ := hub
  refine ⟨(u₀ : G), u₀.2, ?_, ?_⟩
  ·
    have hmem : u₀ * u₀ ∈ P := Subgroup.mul_mem _ hu₀P hu₀P
    have h1 : (QuotientGroup.mk (u₀ * u₀) : CentralizerBar x) = QuotientGroup.mk 1 := by
      have e : (QuotientGroup.mk' (pPrimeCore 2 ↥C)) u₀ = ub := hu₀
      rw [QuotientGroup.mk_one]
      change (QuotientGroup.mk' (pPrimeCore 2 ↥C)) (u₀ * u₀) = 1
      rw [map_mul, e, hu2]
    have := lift_twoSubgroup_injOn hP2 hmem (Subgroup.one_mem _) h1
    simpa using congrArg Subtype.val this
  · exact hu₀

end CFSG.GH74.Generic
