module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.R3Lift2

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.EvenSporadicStandard.M23Std

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z : G} {F L1 N : Subgroup G}

namespace OutSetup

variable (S : OutSetup L z F L1 N)

include S

theorem false_of_base (hcr : CentRank z)
    (hCG : Nat.card (centralizer ({z} : Set G)) = 1774080) (hnc : ∀ x ∈ L1, ¬ IsConj z x)
    {B : Subgroup (Xbar L1)}
    (hBL : ∀ q ∈ B, q * q = 1 → q ≠ 1 → 128 ∣ Nat.card (centralizer ({q} : Set (Xbar L1))))
    {P : Subgroup G} (hP : IsPGroup 2 P) (hL1P : L1 ≤ P) (hPX : P ≤ normalizer (L1 : Set G))
    {y : G} (hyP : y ∈ P) (hy2 : y * y = 1) (hconj : IsConj z y)
    (hyB : (QuotientGroup.mk ⟨y, hPX hyP⟩ : Xbar L1) ∈ B) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases h1 : (QuotientGroup.mk ⟨y, hPX hyP⟩ : Xbar L1) = 1
  · rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
    exact hnc y (S.mem_L1_of_mem_centralizer hP hL1P hyP h1) hconj
  · set q : Xbar L1 := QuotientGroup.mk ⟨y, hPX hyP⟩ with hq
    have hq2 : q * q = 1 := by
      rw [hq, ← QuotientGroup.mk_mul]
      have : (⟨y, hPX hyP⟩ : ↥(normalizer (L1 : Set G))) * ⟨y, hPX hyP⟩ = 1 :=
        Subtype.ext hy2
      rw [this]
      exact QuotientGroup.mk_one _
    have h128 := hBL q hyB hq2 h1
    set C : Subgroup (Xbar L1) := centralizer ({q} : Set (Xbar L1)) with hC
    have hqC : q ∈ C := mem_centralizer_singleton_iff.2 rfl
    obtain ⟨Qs⟩ := (inferInstance : Nonempty (Sylow 2 ↥C))
    have hcardC : 7 ≤ (Nat.card C).factorization 2 := by
      have hne : Nat.card C ≠ 0 := Nat.card_pos.ne'
      exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne).1
        (by simpa using h128)
    have hQs : 128 ≤ Nat.card Qs := by
      rw [Sylow.card_eq_multiplicity Qs]
      calc 128 = 2 ^ 7 := by norm_num
        _ ≤ 2 ^ (Nat.card C).factorization 2 := Nat.pow_le_pow_right (by norm_num) hcardC
    set c : ↥C := ⟨q, hqC⟩ with hcdef
    have hcc : ∀ g : ↥C, g * c = c * g := fun g => Subtype.ext
      (mem_centralizer_singleton_iff.1 g.2)
    have hc2 : c * c = 1 := Subtype.ext hq2
    have hc1 : c ≠ 1 := fun h => h1 (congrArg Subtype.val h)
    have hNn : (zpowers c).Normal := ⟨fun n hn g => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
      have : g * c ^ k * g⁻¹ = c ^ k := by
        rw [mul_inv_eq_iff_eq_mul]
        exact ((Commute.zpow_right (show Commute g c from hcc g) k)).eq
      rw [this]
      exact Subgroup.zpow_mem_zpowers c k⟩
    have hNp : IsPGroup 2 (zpowers c) :=
      IsPGroup.of_card (n := 1) (by rw [card_zpowers_invol hc2 hc1]; norm_num)
    have hcQ : c ∈ (Qs : Subgroup ↥C) :=
      IsPGroup.le_sylow_of_normal hNp Qs (Subgroup.mem_zpowers c)
    set Pb : Subgroup (Xbar L1) := (Qs : Subgroup ↥C).map C.subtype with hPb
    have hPbp : IsPGroup 2 Pb := Qs.isPGroup'.map _
    have hqPb : q ∈ Pb := ⟨c, hcQ, rfl⟩
    have hPbC : Pb ≤ C := by
      rintro _ ⟨g, -, rfl⟩
      exact g.2
    have h64 := S.card_le_sixtyfour hcr hCG (hPX hyP) hy2 hconj hPbp hqPb
    have hinf : Pb ⊓ centralizer ({q} : Set (Xbar L1)) = Pb := inf_eq_left.2 hPbC
    have hcard : Nat.card Pb = Nat.card Qs :=
      Subgroup.card_map_of_injective (K := (Qs : Subgroup ↥C)) (f := C.subtype)
        C.subtype_injective
    rw [hinf, hcard] at h64
    omega

end OutSetup

end CFSG.EvenSporadicStandard.M22Std
