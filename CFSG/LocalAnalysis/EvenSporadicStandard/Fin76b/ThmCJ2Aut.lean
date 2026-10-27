module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.ThmCJ2TX
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.ThmCData
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverModelsBridge

public section

namespace CFSG.EvenSporadicStandard.Fin76b.J2

open CFSG.ComponentClassification CFSG.ComponentClassification.J2Cover.Models

theorem S_le_autP :
    S ≤ J2Cover.P := by
  rw [← P_eq_autP]
  exact S_le_P

theorem bOut_mem_R :
    bOut ∈ J2Cover.R := by
  rw [bOut_eq_permU]
  exact J2Cover.R.mul_mem
    (J2Cover.R.mul_mem (J2Cover.P_le_R J2Cover.permB_mem) J2Cover.permU_mem_R)
    (J2Cover.R.inv_mem (J2Cover.P_le_R J2Cover.permB_mem))

theorem TX_le_R :
    TX ≤ J2Cover.R := by
  intro x hx
  rcases mem_TX_iff.1 hx with h | h
  · exact J2Cover.P_le_R (S_le_autP h)
  · have h' := J2Cover.R.mul_mem (J2Cover.P_le_R (S_le_autP h)) (J2Cover.R.inv_mem bOut_mem_R)
    simpa using h'

@[expose] noncomputable def TXAut :
    Subgroup (MulAut J2Cover.P) :=
  (TX.subgroupOf J2Cover.R).map J2Cover.rConj

theorem mem_TXAut_iff
    {α : MulAut J2Cover.P} :
    α ∈ TXAut ↔ ∃ r : J2Cover.R, (r : Perm315) ∈ TX ∧ J2Cover.rConj r = α := by
  simp only [TXAut, Subgroup.mem_map, Subgroup.mem_subgroupOf]

theorem card_TXAut :
    Nat.card TXAut = 256 := by
  rw [TXAut, Subgroup.card_map_of_injective J2Cover.rConj_injective,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe TX_le_R).toEquiv, card_TX]

theorem isPGroup_TXAut :
    IsPGroup 2 TXAut := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact IsPGroup.of_card (n := 8) (by rw [card_TXAut]; norm_num)

theorem index_TXAut :
    TXAut.index = 4725 := by
  have h := TXAut.card_mul_index
  rw [card_TXAut, J2Cover.card_mulAut_P] at h
  omega

theorem rConj_eq_conj (p : J2Cover.P) :
    J2Cover.rConj ⟨(p : Perm315), J2Cover.P_le_R p.2⟩ = MulAut.conj p := by
  refine MulEquiv.ext fun g => Subtype.ext ?_
  rw [J2Cover.rConj_apply, MulAut.conj_apply]
  rfl

theorem coe_elt_four_mul_self :
    (elt 4 : Perm315) * (elt 4 : Perm315) = 1 := by
  have h4sq : (elt 4 : S) * elt 4 = 1 := by
    rw [← sq]
    have := pow_orderOf_eq_one (elt 4)
    rwa [orderOf_elt_four] at this
  have h := congrArg Subtype.val h4sq
  simpa using h

theorem coe_elt_four_ne_one :
    (elt 4 : Perm315) ≠ 1 := by
  intro h
  have h' : (elt 4 : S) = 1 := Subtype.ext (h.trans (Subgroup.coe_one S).symm)
  have := orderOf_elt_four
  rw [h', orderOf_one] at this
  omega

theorem mul_self_eq_one_of_coe
    {t : J2Cover.P} (ht : (t : Perm315) = (elt 4 : Perm315)) : t * t = 1 := by
  refine Subtype.ext ?_
  rw [Subgroup.coe_mul, ht, coe_elt_four_mul_self, Subgroup.coe_one]

theorem ne_one_of_coe
    {t : J2Cover.P} (ht : (t : Perm315) = (elt 4 : Perm315)) : t ≠ 1 := by
  intro h
  exact coe_elt_four_ne_one (by rw [← ht, h, Subgroup.coe_one])

theorem fourth_power_of_coe
    {t : J2Cover.P} (ht : (t : Perm315) = (elt 4 : Perm315)) (y : Perm315) (hy : y ∈ J2Cover.P)
    (hy5 : y = (elt 5 : Perm315)) :
    (⟨y, hy⟩ : J2Cover.P) * ⟨y, hy⟩ * (⟨y, hy⟩ * ⟨y, hy⟩) = t := by
  refine Subtype.ext ?_
  simp only [Subgroup.coe_mul]
  rw [ht]
  change y * y * (y * y) = _
  rw [hy5, coe_elt_mul 5 (d := 5) (by norm_num), mulIdx_five_five,
    coe_elt_mul 32 (d := 32) (by norm_num), mulIdx_thirtytwo_thirtytwo]

theorem conj_mem_TXAut
    {t : J2Cover.P} (ht : (t : Perm315) = (elt 4 : Perm315)) :
    MulAut.conj t ∈ TXAut := by
  refine mem_TXAut_iff.2 ⟨⟨(t : Perm315), J2Cover.P_le_R t.2⟩, ?_, rConj_eq_conj t⟩
  change (t : Perm315) ∈ TX
  rw [ht]
  exact S_le_TX (elt 4).2

theorem central_TXAut_iff
    {t : J2Cover.P}
    (ht : (t : Perm315) = (elt 4 : Perm315)) :
    ∀ α ∈ TXAut, (∀ β ∈ TXAut, β * α = α * β) ↔ (α = 1 ∨ α = MulAut.conj t) := by
  intro α hα
  obtain ⟨r, hr, rfl⟩ := mem_TXAut_iff.1 hα
  have hcen := central_TX_iff hr
  constructor
  · intro hall
    have hcomm : ∀ y ∈ TX, y * (r : Perm315) = (r : Perm315) * y := by
      intro y hy
      have hyR := TX_le_R hy
      have h1 := hall (J2Cover.rConj ⟨y, hyR⟩) (mem_TXAut_iff.2 ⟨⟨y, hyR⟩, hy, rfl⟩)
      rw [← map_mul, ← map_mul] at h1
      exact congrArg Subtype.val (J2Cover.rConj_injective h1)
    rcases hcen.1 hcomm with h | h
    · left
      have : r = 1 := Subtype.ext h
      rw [this, map_one]
    · right
      have : r = ⟨(t : Perm315), J2Cover.P_le_R t.2⟩ := Subtype.ext (h.trans ht.symm)
      rw [this]
      exact rConj_eq_conj t
  · intro h
    have h' : (r : Perm315) = 1 ∨ (r : Perm315) = (elt 4 : Perm315) := by
      rcases h with h | h
      · exact Or.inl (congrArg Subtype.val (J2Cover.rConj_injective (h.trans (map_one _).symm)))
      · refine Or.inr ?_
        have h2 := J2Cover.rConj_injective (h.trans (rConj_eq_conj t).symm)
        exact (congrArg Subtype.val h2).trans ht
    have hcomm := hcen.2 h'
    intro β hβ
    obtain ⟨r', hr', rfl⟩ := mem_TXAut_iff.1 hβ
    rw [← map_mul, ← map_mul]
    exact congrArg J2Cover.rConj (Subtype.ext (hcomm _ hr'))

theorem outerData_aux
    (x : Perm315)
    (hx : x = (elt 4 : Perm315)) : OuterData ↥J2Cover.P := by
  have hxP : x ∈ J2Cover.P := hx ▸ S_le_autP (elt 4).2
  have hy5 : (elt 5 : Perm315) ∈ J2Cover.P := S_le_autP (elt 5).2
  have := J2Cover.finite_mulAut_P
  refine OuterData.of_sylow TXAut isPGroup_TXAut (by rw [index_TXAut]; decide) ?_
  have ht : ((⟨x, hxP⟩ : J2Cover.P) : Perm315) = (elt 4 : Perm315) := hx
  exact ⟨⟨x, hxP⟩, mul_self_eq_one_of_coe ht, ne_one_of_coe ht,
    ⟨⟨(elt 5 : Perm315), hy5⟩, fourth_power_of_coe ht _ hy5 rfl⟩, conj_mem_TXAut ht,
    central_TXAut_iff ht⟩

theorem outerData_autP :
    OuterData ↥J2Cover.P :=
  outerData_aux (elt 4 : Perm315) rfl

end CFSG.EvenSporadicStandard.Fin76b.J2
