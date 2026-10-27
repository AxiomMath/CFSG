module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.FiGiven
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Fi23Pair
public import CFSG.Sporadic.Fi24.Simple

public section

set_option linter.unusedSectionVars false

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78

variable {H : Type} [Group H] [Finite H] {N L : Subgroup H}

theorem not_oddCover_of_card_le {s : TauCeti.SporadicName} (hN : FStarSimple N)
    (hidx : N.index ≤ 2) (hstd : SolStd L) (hle : Nat.card ↥N ≤ Nat.card (Carrier s)) :
    ¬ OddCover s L := by
  intro hcov
  have hLN : L ≤ N := le_of_isPerfect_of_index_le_two hN.normal hidx hcov.1.1
  obtain ⟨t, ht2, hcomp⟩ := hstd.2
  have hLt : L ≤ centralizer ({t} : Set H) := hcomp.le
  have hnot : ¬ N ≤ centralizer ({t} : Set H) := by
    intro hle
    refine hN.not_mem_centralizer_of_orderOf_eq_two ht2 (mem_centralizer_iff.2 fun g hg => ?_)
    exact mem_centralizer_singleton_iff.1 (hle hg)
  obtain ⟨n, hnN, hnt⟩ : ∃ n ∈ N, n ∉ centralizer ({t} : Set H) := by
    by_contra hcon
    exact hnot fun n hn => by_contra fun h => hcon ⟨n, hn, h⟩
  have hlt : L.subgroupOf N < ⊤ := by
    refine lt_top_iff_ne_top.2 fun h => hnt (hLt ?_)
    have : (⟨n, hnN⟩ : ↥N) ∈ L.subgroupOf N := h ▸ Subgroup.mem_top _
    exact this
  obtain ⟨e'⟩ := hcov.2.2
  have hQc : Nat.card (↥L ⧸ center ↥L) = Nat.card (Carrier s) := Nat.card_congr e'.toEquiv
  have hQL : Nat.card (↥L ⧸ center ↥L) ≤ Nat.card ↥L :=
    Nat.card_le_card_of_surjective _ QuotientGroup.mk_surjective
  have hLs : Nat.card (L.subgroupOf N) = Nat.card ↥L :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLN).toEquiv
  have hltc : Nat.card (L.subgroupOf N) < Nat.card ↥N := by
    have := Subgroup.card_lt_of_lt hlt
    simpa using this
  omega

section Certificates


theorem card_carrier_row :
    Nat.card (Carrier .Fi22) = 64561751654400 ∧ Nat.card (Carrier .Fi23) = 4089470473293004800 ∧
      Nat.card (Carrier .Fi24Prime) = 1255205709190661721292800 :=
  ⟨CFSG.Sporadic.Fi22.card_Fi22, CFSG.Sporadic.Fi23.card_Fi23,
    CFSG.Sporadic.Fi24.card_Fi24prime⟩

theorem not_oddCover_fi22 {s : TauCeti.SporadicName} (hN : FStarSimple N)
    (hNs : IsSporadic ↥N .Fi22) (hidx : N.index ≤ 2) (hstd : SolStd L) (hs : s ∈ fiTypes) :
    ¬ OddCover s L := by
  obtain ⟨e⟩ := hNs
  obtain ⟨h22, h23, h24⟩ := card_carrier_row
  have hN22 : Nat.card ↥N = 64561751654400 := by rw [Nat.card_congr e.toEquiv]; exact h22
  have hs' : s = .Fi22 ∨ s = .Fi23 ∨ s = .Fi24Prime := by simpa [fiTypes] using hs
  refine not_oddCover_of_card_le hN hidx hstd ?_
  rcases hs' with rfl | rfl | rfl <;> omega

theorem not_oddCover_fi23_of_ge {s : TauCeti.SporadicName} (hN : FStarSimple N)
    (hNs : IsSporadic ↥N .Fi23) (hidx : N.index ≤ 2) (hstd : SolStd L)
    (hs : s = .Fi23 ∨ s = .Fi24Prime) : ¬ OddCover s L := by
  obtain ⟨e⟩ := hNs
  obtain ⟨h22, h23, h24⟩ := card_carrier_row
  have hN23 : Nat.card ↥N = 4089470473293004800 := by rw [Nat.card_congr e.toEquiv]; exact h23
  refine not_oddCover_of_card_le hN hidx hstd ?_
  rcases hs with rfl | rfl <;> omega

theorem mem_of_isSporadic_fi23 (hN : FStarSimple N) (hNs : IsSporadic ↥N .Fi23) (t : H) :
    t ∈ N := by
  obtain ⟨e⟩ := hNs
  have hinn : ∀ α : MulAut ↥N, ∃ n : ↥N, α = MulAut.conj n :=
    AllInner.of_mulEquiv e.symm CFSG.Sporadic.FischerOddCore.fi23_mulAut_eq_conj
  have := hN.normal
  obtain ⟨n, hn⟩ := hinn (MulAut.conjNormal t)
  have hc : (n : H)⁻¹ * t ∈ centralizer (N : Set H) := by
    refine mem_centralizer_iff.2 fun x hx => ?_
    have h1 := congrArg (fun α : MulAut ↥N => ((α ⟨x, hx⟩ : ↥N) : H)) hn
    simp only [MulAut.conjNormal_apply, MulAut.conj_apply] at h1
    have h1' : (n : H) * x * (n : H)⁻¹ = t * x * t⁻¹ := h1.symm
    calc x * ((n : H)⁻¹ * t) = (n : H)⁻¹ * ((n : H) * x * (n : H)⁻¹) * t := by group
      _ = (n : H)⁻¹ * (t * x * t⁻¹) * t := by rw [h1']
      _ = (n : H)⁻¹ * t * x := by group
  have hmem := hN.centralizer_le hc
  have : t = (n : H) * ((n : H)⁻¹ * t) := by group
  rw [this]
  exact N.mul_mem n.2 hmem

theorem not_oddCover_fi22_of_fi23 (hN : FStarSimple N) (hNs : IsSporadic ↥N .Fi23)
    (hidx : N.index ≤ 2) (hstd : SolStd L) : ¬ OddCover .Fi22 L := by
  intro hcov
  have hLN : L ≤ N := le_of_isPerfect_of_index_le_two hN.normal hidx hcov.1.1
  obtain ⟨t, ht2, hcomp⟩ := hstd.2
  have hLt : L ≤ centralizer ({t} : Set H) := hcomp.le
  have htN : t ∈ N := mem_of_isSporadic_fi23 hN hNs t
  obtain ⟨e'⟩ := hcov.2.2
  obtain ⟨h22, -, -⟩ := card_carrier_row
  have hQc : Nat.card (↥L ⧸ center ↥L) = 64561751654400 := by
    rw [Nat.card_congr e'.toEquiv]; exact h22
  have hLcard : Nat.card ↥L = 64561751654400 * Nat.card (center ↥L) := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup (center ↥L)
    rw [hQc] at this
    exact this
  set X : Subgroup H := N ⊓ centralizer ({t} : Set H) with hX
  have hLX : L ≤ X := fun x hx => ⟨hLN hx, hLt hx⟩
  have hXle : Nat.card ↥X ≤ 129123503308800 := fi23_card_inf_centralizer_le hNs htN ht2
  have hLXc : Nat.card ↥L ≤ Nat.card ↥X := Subgroup.card_le_of_le hLX
  have hZ1 : Nat.card (center ↥L) = 1 := by
    have hodd := hcov.odd_center
    obtain ⟨k, hk⟩ := hodd
    have hpos : 0 < Nat.card (center ↥L) := Nat.card_pos
    rw [hLcard] at hLXc
    omega
  have hLc : Nat.card ↥L = 64561751654400 := by rw [hLcard, hZ1]
  by_cases hXL : Nat.card ↥X = Nat.card ↥L
  ·
    have hXeq : L = X := Subgroup.eq_of_le_of_card_ge hLX hXL.le
    have htL : t ∈ L := by
      rw [hXeq]
      exact ⟨htN, mem_centralizer_singleton_iff.2 rfl⟩
    have hz : (⟨t, htL⟩ : ↥L) ∈ center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (mem_centralizer_singleton_iff.1 (hLt g.2))
    have hbot : center ↥L = ⊥ := Subgroup.eq_bot_of_card_eq _ hZ1
    rw [hbot, Subgroup.mem_bot] at hz
    have : t = 1 := congrArg Subtype.val hz
    rw [this, orderOf_one] at ht2
    omega
  ·
    obtain ⟨e⟩ := hNs
    let ψ : ↥N ≃* CFSG.Sporadic.Fi23.J := e.trans CFSG.Sporadic.Fi23.fi23EquivJ
    have hx2 : orderOf (ψ ⟨t, htN⟩) = 2 := by
      rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, ht2]
    have hXlt : Nat.card ↥L < Nat.card ↥X := lt_of_le_of_ne hLXc (Ne.symm hXL)
    have hXc : Nat.card ↥X = 129123503308800 := by
      obtain ⟨m, hm⟩ : Nat.card ↥L ∣ Nat.card ↥X := Subgroup.card_dvd_of_le hLX
      have hm2 : m = 2 := by
        have : 1 < m := by
          by_contra h
          push Not at h
          interval_cases m <;> omega
        have h3 : m ≤ 2 := by
          by_contra h
          push Not at h
          have : Nat.card ↥L * 3 ≤ Nat.card ↥L * m := Nat.mul_le_mul_left _ h
          omega
        omega
      rw [hm, hm2, hLc]
    have hcard : Nat.card ↥(centralizer ({ψ ⟨t, htN⟩} : Set CFSG.Sporadic.Fi23.J)) =
        129123503308800 := by
      rw [← @fi23_card_inf_centralizer_eq H CFSG.Sporadic.Fi23.J _ (inferInstance) N ψ t htN]
      exact hXc
    have hXq : CFSG.IsQuasisimple ↥X :=
      @isQuasisimple_inf_centralizer_of_isConj H CFSG.Sporadic.Fi23.J _ (inferInstance) N ψ t htN
        CFSG.Sporadic.Fi23.d (fi23J_isConj_d_of_card hx2 hcard) isQuasisimple_centralizer_d
    have hidx2 : (L.subgroupOf X).index = 2 := by
      have h1 := Subgroup.card_mul_index (L.subgroupOf X)
      have h2 : Nat.card (L.subgroupOf X) = Nat.card ↥L :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLX).toEquiv
      rw [h2, hLc] at h1
      omega
    have hnorm : (L.subgroupOf X).Normal := Subgroup.normal_of_index_eq_two hidx2
    have : Group.IsPerfect ↥X := hXq.1
    have hle := le_of_isPerfect_of_index_le_two hnorm hidx2.le
      (show Group.IsPerfect ↥(⊤ : Subgroup ↥X) from
        Group.IsPerfect.ofSurjective (f := (Subgroup.topEquiv (G := ↥X)).symm.toMonoidHom)
          (Subgroup.topEquiv (G := ↥X)).symm.surjective)
    have htop : L.subgroupOf X = ⊤ := top_le_iff.1 hle
    rw [htop, Subgroup.index_top] at hidx2
    omega

end Certificates

end CFSG.EvenSporadicStandard.Induction
