module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11AutQTKer

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

private theorem aqt_twoCoreIn_le (X : Subgroup G) : twoCoreIn X ≤ X := by
  unfold twoCoreIn CFSG.inSubgroup
  exact Subgroup.map_subtype_le _

private theorem aqt_mem_twoCoreIn_iff {X : Subgroup G} {x : G} (hx : x ∈ X) :
    x ∈ twoCoreIn X ↔ (⟨x, hx⟩ : ↥X) ∈ CFSG.pCore 2 ↥X := by
  unfold twoCoreIn CFSG.inSubgroup
  constructor
  · rintro ⟨y, hy, hyx⟩
    have : y = ⟨x, hx⟩ := Subtype.ext hyx
    rwa [this] at hy
  · intro h
    exact ⟨⟨x, hx⟩, h, rfl⟩

private theorem aqt_pow4_of_pow_two_pow (y : SL23) (n : ℕ) (h : y ^ 2 ^ n = 1) : y ^ 4 = 1 := by
  have hcard : y ^ 24 = 1 := by
    rw [← aqt_card_sl23]
    exact pow_card_eq_one'
  have hd1 : orderOf y ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one h
  have hd2 : orderOf y ∣ 24 := orderOf_dvd_of_pow_eq_one hcard
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd1
  have hj3 : j ≤ 3 := by
    by_contra hlt
    push Not at hlt
    have h4 : 2 ^ 4 ∣ 2 ^ j := pow_dvd_pow 2 (by omega)
    have h24 : 2 ^ j ∣ 24 := by rw [← hj]; exact hd2
    have : 2 ^ 4 ∣ 24 := h4.trans h24
    norm_num at this
  have h8 : y ^ 8 = 1 := by
    apply orderOf_dvd_iff_pow_eq_one.mp
    rw [hj]
    exact (pow_dvd_pow 2 hj3 : 2 ^ j ∣ 2 ^ 3)
  exact (by decide : ∀ w : SL23, w ^ 8 = 1 → w ^ 4 = 1) y h8

theorem aqt_twoCore_eq {K : Subgroup G} {Ψ : SL23 × SL23 →* G} (hrange : Ψ.range = K)
    (hker : ∀ A B : SL23, Ψ (A, B) = 1 ↔ (A = 1 ∧ B = 1) ∨ (A = -1 ∧ B = -1)) :
    twoCoreIn K = (sl23Q8.prod sl23Q8).map Ψ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := sl23Q8_normal
  have hQtN : (sl23Q8.prod sl23Q8).Normal := inferInstance
  have hPK : (sl23Q8.prod sl23Q8).map Ψ ≤ K := by
    rw [← hrange]
    exact Subgroup.map_le_range Ψ (sl23Q8.prod sl23Q8)
  have hsurj : ∀ k ∈ K, ∃ v : SL23 × SL23, Ψ v = k := by
    intro k hk
    rw [← hrange] at hk
    exact hk
  have hP4 : ∀ x ∈ (sl23Q8.prod sl23Q8).map Ψ, x ^ 4 = 1 := by
    rintro _ ⟨⟨A, B⟩, hq, rfl⟩
    have hA : A ^ 4 = 1 := (Subgroup.mem_prod.mp hq).1
    have hB : B ^ 4 = 1 := (Subgroup.mem_prod.mp hq).2
    have h4 : ((A, B) : SL23 × SL23) ^ 4 = 1 :=
      Prod.ext (by simpa using hA) (by simpa using hB)
    rw [← map_pow, h4, map_one]
  have hP2 : IsPGroup 2 ((sl23Q8.prod sl23Q8).map Ψ) :=
    fun g => ⟨2, Subtype.ext (by simpa using hP4 g g.2)⟩
  have hPnorm : (((sl23Q8.prod sl23Q8).map Ψ).subgroupOf K).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨v, hv⟩ := hsurj g g.2
    obtain ⟨q, hq, hqn⟩ := Subgroup.mem_map.mp (show (n : G) ∈ (sl23Q8.prod sl23Q8).map Ψ from hn)
    show ((g * n * g⁻¹ : ↥K) : G) ∈ (sl23Q8.prod sl23Q8).map Ψ
    have h : ((g * n * g⁻¹ : ↥K) : G) = Ψ (v * q * v⁻¹) := by
      simp only [map_mul, map_inv, hv, hqn, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [h]
    exact Subgroup.mem_map_of_mem Ψ (hQtN.conj_mem q hq v)
  have hPle : (sl23Q8.prod sl23Q8).map Ψ ≤ twoCoreIn K := by
    have hP2' : IsPGroup 2 (((sl23Q8.prod sl23Q8).map Ψ).subgroupOf K) := hP2.comap_subtype
    have hle : ((sl23Q8.prod sl23Q8).map Ψ).subgroupOf K ≤ CFSG.pCore 2 ↥K :=
      le_sSup ⟨hPnorm, hP2'⟩
    calc (sl23Q8.prod sl23Q8).map Ψ
        = (((sl23Q8.prod sl23Q8).map Ψ).subgroupOf K).map K.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hPK).symm
      _ ≤ (CFSG.pCore 2 ↥K).map K.subtype := Subgroup.map_mono hle
      _ = twoCoreIn K := rfl
  have hleP : twoCoreIn K ≤ (sl23Q8.prod sl23Q8).map Ψ := by
    intro x hx
    have hxK : x ∈ K := aqt_twoCoreIn_le K hx
    have hxP : (⟨x, hxK⟩ : ↥K) ∈ CFSG.pCore 2 ↥K := (aqt_mem_twoCoreIn_iff hxK).mp hx
    obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (G := ↥K) (p := 2) ⟨⟨x, hxK⟩, hxP⟩
    have hxk : x ^ 2 ^ k = 1 := by
      have h := congrArg (fun y : ↥(CFSG.pCore 2 ↥K) => (((y : ↥K) : G))) hk
      simpa using h
    obtain ⟨⟨s, t⟩, hu⟩ := hsurj x hxK
    have hw : Ψ (s ^ 2 ^ k, t ^ 2 ^ k) = 1 := by
      have e : (s ^ 2 ^ k, t ^ 2 ^ k) = (s, t) ^ 2 ^ k := rfl
      rw [e, map_pow, hu, hxk]
    have hsq : s ^ 2 ^ (k + 1) = 1 ∧ t ^ 2 ^ (k + 1) = 1 := by
      have hneg : (-1 : SL23) ^ 2 = 1 := by decide
      rw [pow_succ, pow_mul, pow_mul]
      rcases (hker _ _).mp hw with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]
        simp
      · rw [h1, h2]
        exact ⟨hneg, hneg⟩
    have hs4 : s ^ 4 = 1 := aqt_pow4_of_pow_two_pow s _ hsq.1
    have ht4 : t ^ 4 = 1 := aqt_pow4_of_pow_two_pow t _ hsq.2
    exact ⟨(s, t), Subgroup.mem_prod.mpr ⟨hs4, ht4⟩, hu⟩
  exact le_antisymm hleP hPle

end CFSG.OddStandard.SmallF3.Omega
