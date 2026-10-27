module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec7Gen
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec7Out
public import CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialProductPerfect
public import CFSG.LocalAnalysis.EvenBN.Common.SwapUnique
public import CFSG.Fischer.Classification.Recognition.Basic

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

variable {G : Type} [Group G] [Finite G] {d : Data G} {A : Subgroup G}

namespace Data.Hyp

theorem map_conj_eq_of_le_centralizer (htA : A ≤ centralizer ({d.t} : Set G)) :
    A.map (MulAut.conj d.t).toMonoidHom = A := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    have := mem_centralizer_singleton_iff.1 (htA ha)
    have e : d.t * a * d.t⁻¹ = a := by rw [← this]; group
    simpa [MulAut.conj_apply, e] using ha
  · intro hx
    refine ⟨x, hx, ?_⟩
    have := mem_centralizer_singleton_iff.1 (htA hx)
    simp [MulAut.conj_apply, ← this]

theorem t_not_mem_centralizer_sup (hU : d.UnitaryProductData A) :
    d.t ∉ centralizer ((A ⊔ A.map (MulAut.conj d.t).toMonoidHom : Subgroup G) : Set G) := by
  intro htD
  have hA : A ≤ A ⊔ A.map (MulAut.conj d.t).toMonoidHom := le_sup_left
  have htA : A ≤ centralizer ({d.t} : Set G) := fun a ha => by
    rw [mem_centralizer_singleton_iff]
    exact mem_centralizer_iff.1 htD a (hA ha)
  have hAt := map_conj_eq_of_le_centralizer htA
  have hc := hU.comm
  rw [hAt, hU.perfect] at hc
  exact hU.ne_bot hc


theorem odd_card_centralizer_sup (h : d.Hyp) (hU : d.UnitaryProductData A) :
    Odd (Nat.card (centralizer ((A ⊔ A.map (MulAut.conj d.t).toMonoidHom : Subgroup G) :
      Set G))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set D : Subgroup G := A ⊔ A.map (MulAut.conj d.t).toMonoidHom with hD
  by_contra hodd
  have heven : 2 ∣ Nat.card (centralizer (D : Set G)) :=
    even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 hodd)
  obtain ⟨⟨z, hzD⟩, hzord⟩ := exists_prime_orderOf_dvd_card' 2 heven
  have hz2 : orderOf z = 2 := by rw [← hzord, orderOf_mk]
  have hzC : z ∈ centralizer (d.L : Set G) :=
    Subgroup.centralizer_le (show (d.L : Set G) ⊆ D from hU.L_le) hzD
  have htD : d.t ∈ normalizer (D : Set G) := by
    rw [mem_normalizer_iff]
    intro y
    have hAt : (A.map (MulAut.conj d.t).toMonoidHom).map (MulAut.conj d.t).toMonoidHom = A := by
      rw [Subgroup.map_map]
      have : ((MulAut.conj d.t).toMonoidHom.comp (MulAut.conj d.t).toMonoidHom) =
          (MonoidHom.id G) := by
        ext w
        have htt : d.t * d.t = 1 := h.t_mul_t
        have hti : d.t⁻¹ = d.t := h.t_inv
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
          MonoidHom.id_apply, hti]
        calc d.t * (d.t * w * d.t) * d.t = (d.t * d.t) * w * (d.t * d.t) := by group
          _ = w := by rw [htt]; group
      rw [this, Subgroup.map_id]
    have hDt : D.map (MulAut.conj d.t).toMonoidHom = D := by
      rw [hD, Subgroup.map_sup, hAt, sup_comm]
    constructor
    · intro hy
      rw [← hDt]
      exact ⟨y, hy, rfl⟩
    · intro hy
      rw [← hDt] at hy
      obtain ⟨w, hw, hwy⟩ := hy
      have : w = y := by
        have : d.t * w * d.t⁻¹ = d.t * y * d.t⁻¹ := hwy
        simpa using this
      rwa [← this]
  set X : Subgroup G := centralizer (d.L : Set G) ⊓ normalizer (D : Set G) with hX
  have htX : zpowers d.t ≤ X := zpowers_le.2 ⟨h.t_mem, htD⟩
  have hsyl : CFSG.ABGLocalTools.IsSylowOf 2 (zpowers d.t) X :=
    h.isSylowOf_zpowers_t.of_le htX inf_le_left
  have hzN : z ∈ normalizer (D : Set G) := centralizer_le_normalizer D hzD
  have hzX : z ∈ X := ⟨hzC, hzN⟩
  have hzp : IsPGroup 2 (zpowers z) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hz2, pow_one]
  obtain ⟨c, hcX, hc⟩ := Common.SwapUnique.exists_conj_le_of_isSylowOf hsyl (zpowers_le.2 hzX) hzp
  have hzt : c * z * c⁻¹ ∈ zpowers d.t := hc z (mem_zpowers z)
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hzt
  have hczord : orderOf (c * z * c⁻¹) = 2 := by
    have := orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective z
    simpa [MulAut.conj_apply, hz2] using this
  have hcz : c * z * c⁻¹ = d.t := by
    have hmod := zpow_mod_orderOf d.t k
    rw [h.t_two] at hmod
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · exfalso
      have h0' : k % ((2 : ℕ) : ℤ) = 0 := by exact_mod_cast h0
      rw [h0', zpow_zero] at hmod
      rw [← hk, ← hmod, orderOf_one] at hczord
      exact absurd hczord (by norm_num)
    · have h1' : k % ((2 : ℕ) : ℤ) = 1 := by exact_mod_cast h1
      rw [h1', zpow_one] at hmod
      rw [← hk, ← hmod]
  apply t_not_mem_centralizer_sup hU
  rw [mem_centralizer_iff]
  intro y hy
  have hy' : c⁻¹ * y * c ∈ D := by
    have := (mem_normalizer_iff.1 ((normalizer (D : Set G)).inv_mem hcX.2) y).1 hy
    simpa using this
  have E := mem_centralizer_iff.1 hzD _ hy'
  rw [← hcz]
  calc y * (c * z * c⁻¹) = c * ((c⁻¹ * y * c) * z) * c⁻¹ := by group
    _ = c * (z * (c⁻¹ * y * c)) * c⁻¹ := by rw [E]
    _ = c * z * c⁻¹ * y := by group

theorem perfect_le_sup (h : d.Hyp) (hU : d.UnitaryProductData A) (M : Subgroup G)
    (hM : ⁅M, M⁆ = M)
    (hMN : M ≤ normalizer ((A ⊔ A.map (MulAut.conj d.t).toMonoidHom : Subgroup G) : Set G)) :
    M ≤ A ⊔ A.map (MulAut.conj d.t).toMonoidHom := by
  have hq : CFSG.Open.IsQuasisimple ↥A := h.isQuasisimple hU
  have hq' : CFSG.Open.IsQuasisimple ↥(A.map (MulAut.conj d.t).toMonoidHom) :=
    CFSG.Fischer.Classification.Recognition.isQuasisimple_map_mulEquiv (MulAut.conj d.t) hq
  have h₁₂ : A.map (MulAut.conj d.t).toMonoidHom ≤ centralizer (A : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 (by rw [commutator_comm]; exact hU.comm)
  haveI : Group.IsPerfect ↥A := ⟨hq.1⟩
  haveI := isSolvable_outer_SU52
  haveI hOutL : Group.IsSolvable (Outer ↥d.L) :=
    CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_equiv d.η.symm
  obtain ⟨e⟩ := h.quotient_equiv hU
  haveI hOutQ : Group.IsSolvable (Outer (↥A ⧸ center ↥A)) :=
    CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_equiv e.symm
  haveI hOutA : Group.IsSolvable (Outer ↥A) :=
    CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_centerQuotient ↥A
  have hOutB : Group.IsSolvable (Outer ↥(A.map (MulAut.conj d.t).toMonoidHom)) :=
    CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_equiv
      (A.equivMapOfInjective (MulAut.conj d.t).toMonoidHom (MulAut.conj d.t).injective)
  exact EvenBN.Sp4.BothTrivialProduct.perfect_le_of_le_normalizer_sup hq hq' h₁₂ hOutA hOutB
    (h.odd_card_centralizer_sup hU) hM hMN

end Data.Hyp

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
