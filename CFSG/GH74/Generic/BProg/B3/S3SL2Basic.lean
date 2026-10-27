module

public import CFSG.GH74.GLS.TwoThin.G.OrdersB2
public import CFSG.GH74.GLS.C3.Layer1.BkIv81Aux

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup
open scoped commutatorElement

namespace S3SL2Basic

variable {Y : Type} [Group Y]

@[expose] noncomputable def actH (H : Subgroup Y) {s : Y} (hs : s ∈ normalizer (H : Set Y)) :
    MulAut ↥H where
  toFun h := ⟨s * h * s⁻¹, (mem_normalizer_iff.1 hs _).1 h.2⟩
  invFun h := ⟨s⁻¹ * h * s, by simpa using (mem_normalizer_iff.1 (inv_mem hs) (h : Y)).1 h.2⟩
  left_inv h := Subtype.ext (by simp [mul_assoc])
  right_inv h := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

theorem actH_apply (H : Subgroup Y) {s : Y} (hs : s ∈ normalizer (H : Set Y)) (h : ↥H) :
    ((actH H hs h : ↥H) : Y) = s * h * s⁻¹ := rfl

theorem actH_mul_self (H : Subgroup Y) {s : Y} (hs : s ∈ normalizer (H : Set Y)) (hss : s * s = 1) :
    actH H hs * actH H hs = 1 := by
  ext h
  have h1 : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  simp only [actH_apply, h1, mul_assoc, MulAut.mul_apply, MulAut.one_apply]
  rw [← mul_assoc, hss, one_mul, mul_one]

theorem actH_eq_iff (H : Subgroup Y) {s : Y} (hs : s ∈ normalizer (H : Set Y)) (h : ↥H) :
    actH H hs h = h ↔ s * (h : Y) = (h : Y) * s := by
  constructor
  · intro h1
    have h2 := congrArg Subtype.val h1
    rw [actH_apply] at h2
    calc s * (h : Y) = s * (h : Y) * s⁻¹ * s := by group
      _ = (h : Y) * s := by rw [h2]
  · intro h1
    refine Subtype.ext ?_
    rw [actH_apply, h1]
    group

theorem eq_of_centralizes {H Lb : Subgroup Y} {s : Y} (hQ : CFSG.IsQuasisimple ↥H)
    (hcen : ∀ h ∈ H, s * h = h * s) (hLb : IsPCompIn 2 (centralizer ({s} : Set Y) ⊓ H) Lb)
    (hnc : ∃ a ∈ Lb, ∃ b ∈ Lb, a * b ≠ b * a) : Lb = H := by
  have hC : centralizer ({s} : Set Y) ⊓ H = H := by
    refine inf_eq_right.2 fun h hh => ?_
    rw [mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    rw [hg]
    exact hcen h hh
  rw [hC] at hLb
  obtain ⟨hLH, K, -, hsub, -, -⟩ := hLb
  rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hQ hsub with htop | hcent
  · exact le_antisymm hLH (Subgroup.subgroupOf_eq_top.1 htop)
  · exfalso
    obtain ⟨a, ha, b, hb, hab⟩ := hnc
    have ha' : (⟨a, hLH ha⟩ : ↥H) ∈ center ↥H := hcent (show (⟨a, hLH ha⟩ : ↥H) ∈ Lb.subgroupOf H from ha)
    exact hab (congrArg Subtype.val (Subgroup.mem_center_iff.1 ha' ⟨b, hLH hb⟩).symm)

theorem sl2_card_data {Lb : Type} [Group Lb] (h : HasSL2Model Lb (fun q => Odd q ∧ 5 ≤ q)) :
    ∃ q : ℕ, Odd q ∧ 5 ≤ q ∧ Nat.card Lb = q * (q ^ 2 - 1) := by
  obtain ⟨F, _, _, ⟨hodd, h5⟩, ⟨e⟩⟩ := h
  refine ⟨Nat.card F, hodd, h5, ?_⟩
  rw [Nat.card_congr e.toEquiv]
  exact TwoThin.card_statedSL_two F

theorem sl2_card_ge {q : ℕ} (h5 : 5 ≤ q) : 120 ≤ q * (q ^ 2 - 1) := by
  have h1 : 25 ≤ q ^ 2 := by nlinarith
  have h2 : 24 ≤ q ^ 2 - 1 := by omega
  calc 120 = 5 * 24 := by norm_num
    _ ≤ q * (q ^ 2 - 1) := Nat.mul_le_mul h5 h2

theorem perfect_subgroupOf {H Lb : Subgroup Y} {s : Y}
    (hLb : IsPCompIn 2 (centralizer ({s} : Set Y) ⊓ H) Lb) :
    ⁅Lb.subgroupOf H, Lb.subgroupOf H⁆ = Lb.subgroupOf H := by
  have hperf : ⁅Lb, Lb⁆ = Lb := GLS.C3.Layer1.Bk.perfect_of_isPCompIn hLb
  have hLH : Lb ≤ H := hLb.1.trans inf_le_right
  apply Subgroup.map_injective H.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hLH, hperf]


theorem exists_noncomm_of_perfect {Lb : Subgroup Y} (hperf : ⁅Lb, Lb⁆ = Lb) (h : 1 < Nat.card Lb) :
    ∃ a ∈ Lb, ∃ b ∈ Lb, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  have h1 : Lb ≤ ⊥ := by
    conv_lhs => rw [← hperf]
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact hcon a ha b hb
  have h2 : Lb = ⊥ := le_bot_iff.1 h1
  have h3 : Nat.card Lb = 1 := by rw [h2]; exact Subgroup.card_bot
  omega

end S3SL2Basic

end CFSG.GH74.Generic.BProg.B3
