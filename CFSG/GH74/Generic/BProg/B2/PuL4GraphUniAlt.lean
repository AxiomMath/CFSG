module

public import CFSG.GH74.Generic.BProg.B2.PuL4GraphLin

public section

namespace CFSG.GH74.Generic.BProg.B2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank

namespace PuL4GraphUniAlt

open CFSG.GH74.Generic.BProg.B2.GenLocL4Gen4

theorem false_of_sp_cover {N : Type} [Group N] [Finite N] {H : Subgroup N} {t : N} {L : Subgroup N}
    (hs : ShapeInCent H t L) (htH : t ∉ H) {F : Type} [Field F] [Finite F] (h2 : (2 : F) ≠ 0)
    (σ : StatedSp 2 F →* ↥L) (hker : σ.ker ≤ center (StatedSp 2 F))
    (hN : SectionalTwoRankLE N 4) : False := by
  obtain ⟨φ, hφc⟩ := PuL4GraphLin.exists_q8q8_sp h2
  have ht2 : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [hs.inv, pow_two] at this
  have hLC : L ≤ H ⊓ centralizer ({t} : Set N) := hs.comp.1
  let g₁ : QuaternionGroup 2 × QuaternionGroup 2 →* N := L.subtype.comp (σ.comp φ)
  let g₂ : Multiplicative (ZMod 2) →* N :=
    { toFun := fun x => if x = 1 then 1 else t
      map_one' := by simp
      map_mul' := by
        have hc : ∀ x : Multiplicative (ZMod 2), x = 1 ∨ x = Multiplicative.ofAdd 1 := by decide
        have hs11 : Multiplicative.ofAdd (1 : ZMod 2) * Multiplicative.ofAdd 1 = 1 := by decide
        have hne : Multiplicative.ofAdd (1 : ZMod 2) ≠ 1 := by decide
        intro x y
        rcases hc x with rfl | rfl <;> rcases hc y with rfl | rfl
        · simp
        · simp
        · simp
        · simp [hs11, hne, ht2] }
  have hcomm : ∀ m n, Commute (g₁ m) (g₂ n) := by
    intro m n
    have hm : ((σ (φ m) : L) : N) * t = t * ((σ (φ m) : L) : N) :=
      Subgroup.mem_centralizer_singleton_iff.1 (hLC (σ (φ m)).2).2
    by_cases hn : n = 1
    · simp [g₂, hn]
    · simp only [g₂, MonoidHom.coe_mk, OneHom.coe_mk, hn, ite_false]
      exact hm
  let f := g₁.noncommCoprod g₂ hcomm
  have hT : SectionalTwoRankLE ↥(⊤ : Subgroup N) 4 := SectionalTwoRankLE.subgroup ⊤ hN
  refine not_sectionalTwoRankLE_of_char (⊤ : Subgroup N) f (fun _ => Subgroup.mem_top _)
    PuL4GraphLin.psi5 PuL4GraphLin.psi5_sq ?_ (r := 4)
    (by have := PuL4GraphLin.two_pow_le_card_psi5; omega) hT
  rintro ⟨⟨a, b⟩, ε⟩ hk
  have hc : ∀ x : Multiplicative (ZMod 2), x = 1 ∨ x = Multiplicative.ofAdd 1 := by decide
  have hfk : f ((a, b), ε) = g₁ (a, b) * g₂ ε := by
    simp only [f, MonoidHom.noncommCoprod_apply]
  rcases hc ε with rfl | rfl
  · have h1 : ((σ (φ (a, b)) : L) : N) = 1 := by
      have h0 : g₂ 1 = 1 := map_one g₂
      rw [hfk, h0, mul_one] at hk
      exact hk
    have h2' : σ (φ (a, b)) = 1 := Subtype.ext h1
    have h4 := hker (show φ (a, b) ∈ σ.ker from h2')
    rcases hφc _ h4 with h5 | h5
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h5
      exact PuL4GraphLin.psi5_eq_one_of (Or.inl rfl) (Or.inl rfl) rfl
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h5
      exact PuL4GraphLin.psi5_eq_one_of (Or.inr rfl) (Or.inr rfl) rfl
  · exfalso
    have hne : Multiplicative.ofAdd (1 : ZMod 2) ≠ 1 := by decide
    have h0 : g₂ (Multiplicative.ofAdd 1) = t := by simp [g₂, hne]
    rw [hfk, h0] at hk
    have ht' : t = (g₁ (a, b))⁻¹ := eq_inv_of_mul_eq_one_right hk
    have hmem : t ∈ L := by
      rw [ht']
      exact L.inv_mem (σ (φ (a, b))).2
    exact htH (hLC hmem).1

end PuL4GraphUniAlt

end CFSG.GH74.Generic.BProg.B2
