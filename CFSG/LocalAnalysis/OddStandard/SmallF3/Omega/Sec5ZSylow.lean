module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Sylow
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.CtxCommute

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

theorem sec5z_isSylow2Of_trans {S S' K H : Subgroup G} (hS : IsSylow2Of S H) (hSK : S ≤ K)
    (hKH : K ≤ H) (hS' : IsSylow2Of S' K) : IsSylow2Of S' H := by
  refine ⟨hS'.1.trans hKH, hS'.2.1, fun hd => ?_⟩
  have hK : ¬ 2 ∣ K.relIndex H := fun hd' => hS.2.2 (by
    rw [← Subgroup.relIndex_mul_relIndex S K H hSK hKH]
    exact Dvd.dvd.mul_left hd' _)
  rw [← Subgroup.relIndex_mul_relIndex S' K H hS'.1 hKH] at hd
  rcases (Nat.Prime.dvd_mul Nat.prime_two).mp hd with h1 | h1
  · exact hS'.2.2 h1
  · exact hK h1

variable {t z : G} {L S : Subgroup G}

theorem sec5z_exists_sylow_ctx (h : Sec5Ctx G t L S z) {A : Subgroup G} (hA2 : IsPGroup 2 A)
    (hAt : A ≤ centralizer ({t} : Set G)) (hAz : A ≤ centralizer ({z} : Set G)) :
    ∃ S' : Subgroup G, A ≤ S' ∧ Asc82Notation t L S' z := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K : Subgroup G := centralizer ({t} : Set G) ⊓ centralizer ({z} : Set G) with hK
  have hSK : S ≤ K := fun s hs =>
    ⟨h.sylow.1 hs, Subgroup.mem_centralizer_singleton_iff.mpr (h.central s hs)⟩
  obtain ⟨S', hS', hAS'⟩ := exists_isSylow2Of_ge hA2 (le_inf hAt hAz)
  have hSyl : IsSylow2Of S' (centralizer ({t} : Set G)) :=
    sec5z_isSylow2Of_trans h.sylow hSK inf_le_left hS'
  have hzK : z ∈ K := hSK h.mem_S
  have hcomm : ∀ a ∈ S', ∀ b ∈ zpowers z, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    have haz : Commute a z := Subgroup.mem_centralizer_singleton_iff.mp (hS'.1 ha).2
    exact (Commute.zpow_right haz k).eq
  have hz2 : IsPGroup 2 (zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h.pocket.1]; norm_num)
  have hsup : IsPGroup 2 ↥(S' ⊔ zpowers z) :=
    CFSG.OddStandard.SmallF3.HarrisU33.isPGroup_sup_of_commute hcomm hS'.2.1 hz2
  have hle : S' ⊔ zpowers z ≤ K := sup_le hS'.1 (Subgroup.zpowers_le.mpr hzK)
  have heq : S' ⊔ zpowers z = S' := IsSylow2Of.eq_of_le hS' hle hsup le_sup_left
  have hzS' : z ∈ S' := by
    rw [← heq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  exact ⟨S', hAS', hSyl, hzS',
    fun s hs => Subgroup.mem_centralizer_singleton_iff.mp (hS'.1 hs).2, h.pocket⟩

end CFSG.OddStandard.SmallF3.Omega
