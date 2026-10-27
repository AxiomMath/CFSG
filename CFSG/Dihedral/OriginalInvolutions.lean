module

public import CFSG.Dihedral.OriginalPresentation
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GWLemma21Trichotomy

public noncomputable section

namespace CFSG.DihedralBlueprint.OriginalData

open GorensteinWalter

variable {G : Type} [Group G] [Finite G] (d : OriginalData G)

theorem sylow_le_centralizer : (d.S : Subgroup G) ≤ d.C := by
  rw [d.decomposition]
  exact le_sup_right

theorem centralizer_le_normalizer : d.C ≤ d.N := by
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer d.R_le).mp d.R_normal

theorem centralizer_card : Nat.card d.C = Nat.card d.R * 2 ^ d.n := by
  let R := d.R.subgroupOf d.C
  let S := (d.S : Subgroup G).subgroupOf d.C
  let _ : R.Normal := d.R_normal
  have hsup : R ⊔ S = ⊤ := by
    rw [← Subgroup.subgroupOf_sup d.R_le d.sylow_le_centralizer,
      ← d.decomposition, Subgroup.subgroupOf_self]
  have hinf : R ⊓ S = ⊥ := by
    ext x
    change (x.val ∈ d.R ∧ x.val ∈ (d.S : Subgroup G)) ↔ x = 1
    rw [← Subgroup.mem_inf, d.disjoint, Subgroup.mem_bot]
    change x.val = ((1 : d.C) : G) ↔ x = 1
    exact Subtype.val_inj
  have hindex : R.index = Nat.card S := by
    calc
      R.index = R.relIndex (R ⊔ S) := by rw [hsup, Subgroup.relIndex_top_right]
      _ = R.relIndex S := Subgroup.relIndex_sup_left S R
      _ = Nat.card S := by
        have h := Subgroup.relIndex_mul_card R S
        rwa [hinf, Subgroup.card_bot, mul_one] at h
  rw [← R.card_mul_index, hindex,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe d.R_le).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe d.sylow_le_centralizer).toEquiv,
    d.order_S]

theorem t_order : orderOf d.t = 2 := by
  have hn := d.three_le
  have heq : d.n - 1 = (d.n - 2) + 1 := by omega
  have hdiv : 2 ^ (d.n - 2) ∣ 2 ^ (d.n - 1) := pow_dvd_pow 2 (by omega)
  have hdiv' : 2 ^ (d.n - 2) ∣ orderOf d.r := by rwa [d.order_r]
  rw [t, orderOf_pow_of_dvd (pow_ne_zero _ (by decide)) hdiv',
    d.order_r, heq, pow_succ, Nat.mul_div_right _ (pow_pos (by decide) _)]

theorem sylow_dihedral : Nonempty (d.S ≃* DihedralGroup (2 ^ (d.n - 1))) :=
  d.sylow_mulEquiv_dihedral

theorem has_dihedral_sylow (d : OriginalData G) : HasDihedralSylowTwo G := by
  have hn := d.three_le
  intro P
  obtain ⟨e⟩ := d.sylow_dihedral
  exact ⟨d.n - 1, by omega, ⟨(Sylow.equiv P d.S).trans e⟩⟩

theorem card_eight_le (d : OriginalData G) : 8 ≤ Nat.card G := by
  have hS : 8 ≤ Nat.card (d.S : Subgroup G) := by
    rw [d.order_S]
    calc
      8 = 2 ^ 3 := by decide
      _ ≤ 2 ^ d.n := Nat.pow_le_pow_right (by decide) d.three_le
  exact hS.trans (d.S : Subgroup G).card_le_card_group

theorem involutions_conjugate (d : OriginalData G) [IsSimpleGroup G] (x y : G)
    (hx : orderOf x = 2) (hy : orderOf y = 2) :
    ∃ g : G, g * x * g⁻¹ = y := by
  have hno {k : ℕ} (hk : k < 8) (hk1 : k ≠ 1) :
      ¬ ∃ N : Subgroup G, N.Normal ∧ N.index = k := by
    rintro ⟨N, hN, hindex⟩
    let _ := hN
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hbot | htop
    · rw [hbot, Subgroup.index_bot] at hindex
      have := d.card_eight_le
      omega
    · rw [htop, Subgroup.index_top] at hindex
      exact hk1 hindex.symm
  have hinv {z : G} (hz : orderOf z = 2) :
      BenderSuzuki.PFAppendixIII.IsInvolution z := by
    refine ⟨?_, ?_⟩
    · intro heq
      simp [heq] at hz
    · simpa only [hz] using pow_orderOf_eq_one z
  rcases gw_lemma_2_1 d.has_dihedral_sylow with hfirst | hsecond | hthird
  · exact hfirst.2.1 x y (hinv hx) (hinv hy)
  · exact (hno (by decide : 2 < 8) (by decide) hsecond.1).elim
  · exact (hno (by decide : 4 < 8) (by decide) hthird.1).elim

end CFSG.DihedralBlueprint.OriginalData
