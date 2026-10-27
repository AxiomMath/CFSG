module

public import CFSG.LargeExtraspecial.S3Thompson

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup

variable {G : Type} [Group G]

@[expose] noncomputable def oTwoCent (x : G) : Subgroup G :=
  (CFSG.pCore 2 (centralizer ({x} : Set G))).map (centralizer ({x} : Set G)).subtype

theorem oTwoCent_le_centralizer (x : G) : oTwoCent x ≤ centralizer ({x} : Set G) := by
  rintro _ ⟨y, -, rfl⟩
  exact y.2

theorem isPGroup_oTwoCent (x : G) : IsPGroup 2 (oTwoCent x) :=
  CFSG.pCore_isPGroup.map _

theorem conj_mem_oTwoCent {x c y : G} (hc : c ∈ centralizer ({x} : Set G))
    (hy : y ∈ oTwoCent x) : c * y * c⁻¹ ∈ oTwoCent x := by
  obtain ⟨y', hy', rfl⟩ := hy
  exact ⟨⟨c, hc⟩ * y' * ⟨c, hc⟩⁻¹, CFSG.pCore_normal.conj_mem _ hy' _, rfl⟩

theorem le_oTwoCent {x : G} {P : Subgroup G} (hPC : P ≤ centralizer ({x} : Set G))
    (hPn : ∀ c ∈ centralizer ({x} : Set G), ∀ p ∈ P, c * p * c⁻¹ ∈ P) (hP2 : IsPGroup 2 P) :
    P ≤ oTwoCent x := by
  set C := centralizer ({x} : Set G)
  have hn : (P.subgroupOf C).Normal := ⟨fun n hn g => by
    rw [mem_subgroupOf] at hn ⊢
    exact hPn g g.2 n hn⟩
  have hle : P.subgroupOf C ≤ CFSG.pCore 2 C :=
    le_sSup ⟨hn, hP2.comap_of_injective C.subtype C.subtype_injective⟩
  intro y hy
  exact ⟨⟨y, hPC hy⟩, hle (by rwa [mem_subgroupOf]), rfl⟩

theorem eq_one_of_mem_of_odd [Finite G] {N P : Subgroup G} (hN : Odd (Nat.card N))
    (hP : IsPGroup 2 P) {y : G} (hyN : y ∈ N) (hyP : y ∈ P) : y = 1 := by
  have h1 : orderOf y ∣ Nat.card N := by
    simpa using orderOf_dvd_natCard (⟨y, hyN⟩ : N)
  obtain ⟨k, hk⟩ := hP ⟨y, hyP⟩
  have h2 : orderOf y ∣ 2 ^ k := by
    have := orderOf_dvd_of_pow_eq_one hk
    simpa using this
  have hcop : Nat.Coprime (Nat.card N) (2 ^ k) := (Nat.coprime_two_right.mpr hN).pow_right k
  have h3 : orderOf y ∣ 1 := hcop ▸ Nat.dvd_gcd h1 h2
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)

namespace Setting

variable (S : Setting G)

@[expose] def ZInOTwo (x : G) : Prop := S.z ∈ oTwoCent x

@[expose] def AschbacherHyp : Prop := ∀ x ∈ S.QG, x ≠ 1 → S.ZInOTwo x

theorem zInOTwo_of_le {x : G} {P : Subgroup G} (hPC : P ≤ centralizer ({x} : Set G))
    (hPn : ∀ c ∈ centralizer ({x} : Set G), ∀ p ∈ P, c * p * c⁻¹ ∈ P) (hP2 : IsPGroup 2 P)
    (hz : S.z ∈ P) : S.ZInOTwo x :=
  le_oTwoCent hPC hPn hP2 hz

theorem zInOTwo_of_centralizer_le {x : G} (hx : x ∈ S.QG)
    (hC : centralizer ({x} : Set G) ≤ S.M) : S.ZInOTwo x := by
  refine S.zInOTwo_of_le (P := S.QG ⊓ centralizer ({x} : Set G)) inf_le_right ?_
    (S.isPGroup_QG.to_le inf_le_left) (mem_inf.mpr ⟨S.z_mem_QG, ?_⟩)
  · intro c hc p hp
    obtain ⟨hpQ, hpC⟩ := mem_inf.mp hp
    exact mem_inf.mpr ⟨S.conj_mem_QG (hC hc) hpQ, mul_mem (mul_mem hc hpC) (inv_mem hc)⟩
  · rw [mem_centralizer_singleton_iff]
    exact (S.z_comm_QG hx).symm

end Setting

end CFSG.LargeExtraspecial
