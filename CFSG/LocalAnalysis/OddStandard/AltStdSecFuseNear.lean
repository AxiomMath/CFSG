module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecFuseFar
public import CFSG.LocalAnalysis.OddStandard.AltStdSecFuseNearDef

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup CFSG.OddStandard.AltStdBal

theorem nearOnlyFalse12_of_nearCount (hc : NearCount12) : NearOnlyFalse12 := by
  intro G _ _ L n Q z h d hQ2 hE hn12 e hnearY hnear
  subst hn12
  obtain ⟨R, hRC, hRp, hRmax⟩ := exists_maximal_two_subgroup (centralizer ({z} : Set G))
  obtain ⟨x, y₀, hy₀R, hy₀L, hy₀1, hy₀2, hy₀c, hxz, -, hconj, hconj'⟩ :=
    exists_common_involution_norm h d hQ2 hE hRC hRp hRmax
  have hzR : z ∈ R := mem_of_maximal d hRC hRp hRmax
  have hy₀ord : orderOf y₀ = 2 := orderOf_eq_prime (by rw [sq]; exact hy₀2) hy₀1
  have hy₀Y : y₀ ∈ FusionSet L z := ⟨hy₀L, hy₀ord, x, by rw [hxz]; exact (hy₀c z hzR).symm⟩
  have hy₀Ω : y₀ ∈ omegaG L R z := ⟨hy₀L, hy₀R, Or.inr hy₀Y⟩
  have hS : ∀ l : L, embL e l ∈ nearSet 12 (ppOf e R) ↔ (l : G) ∈ omegaG L R z := by
    intro l
    constructor
    · rintro (hl1 | ⟨hlP, hl2, hl1, hf, -⟩)
      · have : l = 1 := embL_injective e (by simpa using hl1)
        subst this
        exact ⟨one_mem _, one_mem _, Or.inl rfl⟩
      · obtain ⟨l', hl'R, hl'⟩ := (mem_ppOf e).1 hlP
        have hll' : l' = l := embL_injective e hl'
        subst hll'
        have hll : l' * l' = 1 := embL_injective e (by rw [map_mul, map_one]; exact hl2)
        have hl'1 : l' ≠ 1 := fun h1 => hl1 (by rw [h1, map_one])
        have hl'2 : orderOf (l' : G) = 2 := by
          refine orderOf_eq_prime ?_ (fun h1 => hl'1 (Subtype.ext h1))
          rw [sq]
          exact congrArg Subtype.val hll
        exact ⟨l'.2, hl'R, Or.inr (hnearY _ l'.2 hl'2 ((isNear_coe_iff e l').2 hf))⟩
    · rintro ⟨-, hlR, hl⟩
      rcases hl with hl1 | hlY
      · have : l = 1 := Subtype.ext hl1
        subst this
        exact Or.inl (by simp)
      · right
        have hl'1 : l ≠ 1 := fun h1 => by
          have : (l : G) = 1 := by rw [h1]; rfl
          rw [this] at hlY
          exact absurd hlY.2.1 (by simp)
        have hsq : (l : G) * l = 1 := by
          rw [← sq]
          exact hlY.2.1 ▸ pow_orderOf_eq_one _
        refine ⟨(mem_ppOf e).2 ⟨l, hlR, rfl⟩, ?_, ?_,
          (isNear_coe_iff e l).1 (hnear _ hlY), ?_⟩
        · rw [← map_mul]
          have : l * l = 1 := Subtype.ext hsq
          rw [this, map_one]
        · exact fun h1 => hl'1 (embL_injective e (by rw [h1, map_one]))
        · exact Equiv.Perm.mem_alternatingGroup.1 (embL_mem_alt e l)
  have hS' : ∀ p ∈ nearSet 12 (ppOf e R), ∃ l : L, embL e l = p := by
    rintro p (hp | ⟨hp, -⟩)
    · exact ⟨1, by rw [map_one, hp]⟩
    · obtain ⟨l', -, hl'⟩ := (mem_ppOf e).1 hp
      exact ⟨l', hl'⟩
  have key := prodCnt_transport e h d hQ2 hE hRC hzR hy₀R hy₀L hy₀c hxz hconj hconj'
    (nearSet 12 (ppOf e R)) hS hS'
  refine hc (ppOf e R) (ppOf_le_alt e R) (ppOf_isPGroup e hRp)
    (fun P' hP'A hP' hle => ppOf_maximal e h d hQ2 hE hRC hzR hRmax P' hP'A hP' hle)
    (embL e ⟨y₀, hy₀L⟩) ((mem_ppOf e).2 ⟨⟨y₀, hy₀L⟩, hy₀R, rfl⟩)
    ((hS ⟨y₀, hy₀L⟩).2 hy₀Ω)
    (fun h1' => hy₀1 (congrArg Subtype.val (embL_injective e (h1'.trans (map_one _).symm))))
    ?_ key
  rintro p hp
  obtain ⟨l', hl'R, rfl⟩ := (mem_ppOf e).1 hp
  rw [← map_mul, ← map_mul]
  exact congrArg (embL e) (Subtype.ext (hy₀c l' hl'R))

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {Q : Subgroup G} {z : G}

end CFSG.OddStandard.AltStdSec
