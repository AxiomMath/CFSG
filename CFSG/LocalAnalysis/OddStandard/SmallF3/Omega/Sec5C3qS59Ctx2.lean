module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5C3qS59Cnt
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5C3qS59Pair

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec5c3q_sup_eq [Finite G] {A C : Subgroup G} {a : G} (hCA : C ≤ A) (haA : a ∈ A)
    (haC : a ∉ C) (hA : Nat.card A = 64) (hC : Nat.card C = 32) : A = zpowers a ⊔ C := by
  have hDA : zpowers a ⊔ C ≤ A := sup_le (Subgroup.zpowers_le.mpr haA) hCA
  have hCD : C ≤ zpowers a ⊔ C := le_sup_right
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hCD
  have hdvd : Nat.card (zpowers a ⊔ C : Subgroup G) ∣ 64 := by
    have := Subgroup.card_dvd_of_le hDA
    rwa [hA] at this
  have hle : Nat.card (zpowers a ⊔ C : Subgroup G) ≤ 64 := Nat.le_of_dvd (by norm_num) hdvd
  have hpos : 0 < Nat.card (zpowers a ⊔ C : Subgroup G) := Nat.card_pos
  have hne32 : Nat.card (zpowers a ⊔ C : Subgroup G) ≠ 32 := by
    intro h32
    have hCD' : C = zpowers a ⊔ C := Subgroup.eq_of_le_of_card_ge hCD (by rw [h32, hC])
    apply haC
    rw [hCD']
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers a)
  have hD64 : Nat.card (zpowers a ⊔ C : Subgroup G) = 64 := by
    rw [hC] at hk
    omega
  exact (Subgroup.eq_of_le_of_card_ge hDA (by rw [hD64, hA])).symm

variable [Finite G] {t : G} {L S : Subgroup G} {z r : G} {B A : Subgroup G}
  {φ : (Fin 6 → ZMod 2) → G}

theorem sec5c3q_s59_ctx2 (hy : Sec5B59Hyp) (h52a : Asc82Lemma52a) (hZ : Asc82ZExists)
    (tab56 : Asc82Tab56) (n1 : Asc82E64Kind3) (n2 : Asc82Kind2Split)
    (hR : Sec5RCtx G t L S z r B A) (hm : Sec5Model58 t L z r A φ) {g₀ : G}
    (hg₀ : g₀⁻¹ * t * g₀ = t * z) :
    ∃ a : G, Sec5RCtx G (t * z) (CFSG.conjugate L g₀) S z a (A ⊓ CFSG.conjugate L g₀) A := by
  obtain ⟨a, haA, haL, ha2, ⟨g, hg⟩, β, hβ⟩ := sec5c3q_s59_outer_a hy hZ tab56 hR hm hg₀
  have h' := sec5_step56_ctx hy.h52b hy.h53 hy.h37 hZ hy.tab hR.toSec5Ctx hg₀
  have hL1 : IsOm6Z2 (CFSG.conjugate L g₀) := h'.toSec5Setting.isOm6Z2
  have htzZ : t * z ∈ centerIn (CFSG.conjugate L g₀) :=
    sec5_t_mem_centerIn hy.h52b h'.toSec5Setting
  have htzL1 : t * z ∈ CFSG.conjugate L g₀ := (sec5_mem_centerIn_iff.mp htzZ).1
  have htzA : t * z ∈ A := A.mul_mem hm.mem_A.1 hm.mem_A.2.2
  have htzB : t * z ∈ A ⊓ CFSG.conjugate L g₀ := Subgroup.mem_inf.mpr ⟨htzA, htzL1⟩
  have hcard := sec5c3q_s59_card_inter hy h52a hZ n1 hR hm hg₀ haA haL
  have hB : IsElemAb2 (A ⊓ CFSG.conjugate L g₀) 5 :=
    ⟨⟨IsMulCommutative.of_comm fun x y => Subtype.ext (sec5c3q_A_comm hm
        (Subgroup.mem_inf.mp x.2).1 (Subgroup.mem_inf.mp y.2).1),
      fun x hx => by rw [pow_two]; exact sec5c3q_A_sq hm (Subgroup.mem_inf.mp hx).1⟩,
      by rw [hcard]; norm_num⟩
  have hBle : A ⊓ CFSG.conjugate L g₀ ≤ CFSG.conjugate L g₀ ⊓ centralizer ({a} : Set G) := by
    intro x hx
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hx).2, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact sec5c3q_A_comm hm (Subgroup.mem_inf.mp hx).1 haA
  obtain ⟨hsplit1, hsplit2⟩ := n2 G (CFSG.conjugate L g₀) hL1 (t * z) htzZ h'.involution a ha2
    ⟨β, hβ⟩ (A ⊓ CFSG.conjugate L g₀) hBle hB htzB
  have haC : a ∉ A ⊓ CFSG.conjugate L g₀ := fun h => haL (Subgroup.mem_inf.mp h).2
  exact ⟨a,
    { toSec5Ctx := h'
      conj_r := ⟨g, hg⟩
      type_r := ⟨β, hβ⟩
      B_le := hBle
      B_E32 := hB
      B_split := ⟨htzB, hsplit1, hsplit2⟩
      A_eq := sec5c3q_sup_eq inf_le_left haA haC hm.perm.card_A hcard
      A_le := hR.A_le }⟩

end CFSG.OddStandard.SmallF3.Omega
