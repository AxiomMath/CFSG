module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S5Prf

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Final.Thm4
open scoped commutatorElement

section Ord

variable {G : Type} [Group G]

@[expose] noncomputable def ordq (J : Subgroup G) : ℕ := Nat.card (↥J ⧸ Subgroup.center ↥J)

end Ord

section Proj

variable {G : Type} [Group G] [Finite G]

theorem proj_onto {K L J : Subgroup G} (hKL : ∀ a ∈ K, ∀ b ∈ L, a * b = b * a)
    (hJ : CFSG.IsQuasisimple ↥J) (hJle : J ≤ K ⊔ L) (hJL : ¬ J ≤ L) :
    ordq J ≤ ordq K ∧
      (ordq K ≤ ordq J → ∀ a ∈ K, ∃ a' ∈ K, ∃ b ∈ L, a' * b ∈ J ∧ CenK K (a⁻¹ * a')) := by
  classical
  unfold ordq
  have hcomm : ∀ (a : ↥K) (b : ↥L), Commute (K.subtype a) (L.subtype b) := fun a b =>
    hKL a a.2 b b.2
  let φ : ↥K × ↥L →* G := MonoidHom.noncommCoprod K.subtype L.subtype hcomm
  have hφ : ∀ x : ↥K × ↥L, φ x = (x.1 : G) * (x.2 : G) := fun x => by simp [φ]
  have hrange : ∀ g ∈ K ⊔ L, ∃ x : ↥K × ↥L, φ x = g := by
    intro g hg
    obtain ⟨a, ha, b, hb, rfl⟩ := CFSG.GH74.Uniqueness.SU.SU1.mem_sup_of_commute hKL hg
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), by rw [hφ]⟩
  let Jt : Subgroup (↥K × ↥L) := J.comap φ
  let θ : ↥K × ↥L →* (↥K ⧸ Subgroup.center ↥K) :=
    (QuotientGroup.mk' (Subgroup.center ↥K)).comp (MonoidHom.fst ↥K ↥L)
  have hθ : ∀ x : ↥K × ↥L, θ x = QuotientGroup.mk x.1 := fun x => rfl
  let NG : Subgroup G := (Jt ⊓ θ.ker).map φ
  have hNJ : NG ≤ J := by
    rintro _ ⟨x, ⟨hxJ, -⟩, rfl⟩
    exact hxJ
  have hNnormal : (NG.subgroupOf J).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hNJ]
    intro n j hn hj
    obtain ⟨x, ⟨hxJ, hxk⟩, rfl⟩ := hn
    obtain ⟨y, hy⟩ := hrange j (hJle hj)
    have hyJ : y ∈ Jt := by
      show φ y ∈ J
      rw [hy]
      exact hj
    refine ⟨y * x * y⁻¹, ⟨Jt.mul_mem (Jt.mul_mem hyJ hxJ) (Jt.inv_mem hyJ), ?_⟩, ?_⟩
    · have hxk' : θ x = 1 := hxk
      show θ (y * x * y⁻¹) = 1
      rw [map_mul, map_mul, map_inv, hxk', mul_one, mul_inv_cancel]
    · rw [map_mul, map_mul, map_inv, hy]
  have hJperf : ⁅J, J⁆ = J := Subgroup.isPerfect_iff.mp hJ.1
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hJ hNnormal with htop | hcen
  · exfalso
    set ZK : Subgroup G := (Subgroup.center ↥K).map K.subtype with hZK
    have hJZL : J ≤ ZK ⊔ L := by
      intro j hj
      have hjN : j ∈ NG := by
        have h1 : (⟨j, hj⟩ : ↥J) ∈ NG.subgroupOf J := by
          rw [htop]
          exact Subgroup.mem_top _
        exact h1
      obtain ⟨x, ⟨-, hxk⟩, rfl⟩ := hjN
      have hx1 : x.1 ∈ Subgroup.center ↥K := by
        have : θ x = 1 := hxk
        rwa [hθ, QuotientGroup.eq_one_iff] at this
      rw [hφ]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨x.1, hx1, rfl⟩)
        (Subgroup.mem_sup_right x.2.2)
    refine hJL (perfect_le_of_sup (A := L) (B := ZK) hJperf (by rwa [sup_comm] at hJZL) ?_ ?_)
    · rintro _ ⟨z, hz, rfl⟩ _ ⟨z', hz', rfl⟩
      exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz' z)
    · rintro a ha _ ⟨z, hz, rfl⟩
      exact (hKL z z.2 a ha).symm
  · set Zg : Subgroup G := (Subgroup.center ↥J).map J.subtype with hZg
    have hNZ : ∀ x ∈ Jt, θ x = 1 → φ x ∈ Zg := by
      intro x hxJ hxk
      have hmem : φ x ∈ NG := ⟨x, ⟨hxJ, hxk⟩, rfl⟩
      have h1 : (⟨φ x, hNJ hmem⟩ : ↥J) ∈ NG.subgroupOf J := hmem
      exact ⟨⟨φ x, hNJ hmem⟩, hcen h1, rfl⟩
    have hJrange : J ≤ φ.range := fun j hj => by
      obtain ⟨y, hy⟩ := hrange j (hJle hj)
      exact ⟨y, hy⟩
    have hmapJt : Jt.map φ = J := by
      rw [Subgroup.map_comap_eq]
      exact inf_eq_right.2 hJrange
    have h1 : (Zg.comap φ).relIndex Jt = Nat.card (↥J ⧸ Subgroup.center ↥J) := by
      rw [Subgroup.relIndex_comap, hmapJt]
      unfold Subgroup.relIndex
      rw [hZg]
      change (Subgroup.comap J.subtype (Subgroup.map J.subtype (Subgroup.center ↥J))).index = _
      rw [Subgroup.comap_map_eq_self_of_injective J.subtype_injective]
      rfl
    have h2 : θ.ker.relIndex Jt = Nat.card (Jt.map θ) := Subgroup.relIndex_ker Jt θ
    have h3 : (Zg.comap φ).relIndex Jt ∣ θ.ker.relIndex Jt := by
      have hle : θ.ker ⊓ Jt ≤ Zg.comap φ := fun x ⟨hk, hJt⟩ => hNZ x hJt hk
      have := Subgroup.relIndex_dvd_of_le_left Jt hle
      rwa [Subgroup.inf_relIndex_right] at this
    rw [h1, h2] at h3
    have h4 : Nat.card (Jt.map θ) ≤ Nat.card (↥K ⧸ Subgroup.center ↥K) :=
      Subgroup.card_le_card_group _
    have hpos : 0 < Nat.card (Jt.map θ) := Nat.card_pos
    have h5 : Nat.card (↥J ⧸ Subgroup.center ↥J) ≤ Nat.card (Jt.map θ) := Nat.le_of_dvd hpos h3
    refine ⟨h5.trans h4, fun hord a ha => ?_⟩
    have h6 : Nat.card (Jt.map θ) = Nat.card (↥K ⧸ Subgroup.center ↥K) :=
      le_antisymm h4 (hord.trans h5)
    have htopθ : Jt.map θ = ⊤ := (Subgroup.card_eq_iff_eq_top _).1 h6
    have hmem : (QuotientGroup.mk (⟨a, ha⟩ : ↥K) : ↥K ⧸ Subgroup.center ↥K) ∈ Jt.map θ := by
      rw [htopθ]
      exact Subgroup.mem_top _
    obtain ⟨x, hxJ, hx⟩ := hmem
    have hx' : (QuotientGroup.mk x.1 : ↥K ⧸ Subgroup.center ↥K) = QuotientGroup.mk ⟨a, ha⟩ := hx
    have hcen' : (⟨a, ha⟩ : ↥K)⁻¹ * x.1 ∈ Subgroup.center ↥K := QuotientGroup.eq.1 hx'.symm
    refine ⟨(x.1 : G), x.1.2, (x.2 : G), x.2.2, ?_, ⟨?_, fun k hk => ?_⟩⟩
    · have : φ x ∈ J := hxJ
      rwa [hφ] at this
    · exact K.mul_mem (K.inv_mem ha) x.1.2
    · have := Subgroup.mem_center_iff.1 hcen' ⟨k, hk⟩
      exact congrArg Subtype.val this

end Proj

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
