module

public import CFSG.LocalAnalysis.EvenBN.U5.CaseBPSylow
public import CFSG.LocalAnalysis.EvenBN.Common.SwapUnique

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Blueprint
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient
open scoped MatrixGroups

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

namespace CaseBData


theorem hgen_even_card_L (hd : d.Hyp) : Even (Nat.card d.L) := by
  have h1 : Nat.card d.P ∣ Nat.card d.L := Subgroup.card_dvd_of_le d.P_le_L
  rw [d.card_P] at h1
  have h0 : f ≠ 0 := by have := hd.two_le; omega
  exact even_iff_two_dvd.2 ((dvd_pow (dvd_pow_self 2 h0) (by norm_num)).trans h1)

theorem hgen_hcomm (hB : d.CaseBHyp) (c : d.CaseBData) (h52 : CaseBData.Sec52 c) :
    ⁅c.Nc, c.Nc.map (MulAut.conj d.t⁻¹).toMonoidHom⁆ = ⊥ := by
  rw [hB.hyp.t_inv', commutator_comm]
  exact commutator_eq_bot_iff_le_centralizer.2 h52.commute

theorem hgen_range_diag (hB : d.CaseBHyp) (c : d.CaseBData) (h52 : CaseBData.Sec52 c) :
    (Common.diagonalHom c.Nc d.t (hgen_hcomm hB c h52)).range = d.L := by
  have htinv : d.t⁻¹ = d.t := hB.hyp.t_inv'
  have hdiag : ∀ x : G, x * (d.t⁻¹ * x * d.t) = x * (d.t * x * d.t⁻¹) := fun x => by rw [htinv]
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, rfl⟩
    rw [Common.diagonalHom_apply, hdiag]
    exact h52.diag_mem x x.2
  · intro y hy
    obtain ⟨x, hx, hxy⟩ := h52.diag_surj y hy
    refine ⟨⟨x, hx⟩, ?_⟩
    rw [Common.diagonalHom_apply, hdiag]
    exact hxy

theorem hgen_card_Nc (hB : d.CaseBHyp) (c : d.CaseBData) (h52 : CaseBData.Sec52 c) :
    Nat.card c.Nc = Nat.card d.L * Nat.card (center c.Nc) :=
  Common.SwapUnique.card_eq_mul_card_center_of_diagonal hB.hyp.setting.center_eq_bot
    (hgen_hcomm hB c h52) (hgen_range_diag hB c h52)

theorem hgen_Qc_le_Nc (c : d.CaseBData) : c.Qc ≤ c.Nc :=
  (sec52_sylow_Qc_le_Kc c).trans le_sup_left

theorem hgen_isSylowOf_Qc_Nc (hB : d.CaseBHyp) (c : d.CaseBData) (h52 : CaseBData.Sec52 c) :
    IsSylowOf 2 c.Qc c.Nc := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfac : (Nat.card c.Nc).factorization 2 = (Nat.card d.L).factorization 2 := by
    rw [hgen_card_Nc hB c h52, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne',
      Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd
        (fun h2 => (Nat.not_even_iff_odd.2 h52.odd_center) (even_iff_two_dvd.2 h2)), add_zero]
  refine CFSG.ABGLocalTools.isSylowOf_of_card (hgen_Qc_le_Nc c) ?_
  rw [hfac, ← (isSylowOf_P d).card_eq, d.card_P, sec52_card_Qc hB c]

theorem hgen_t_not_mem_S (hB : d.CaseBHyp) (c : d.CaseBData) : d.t ∉ c.S := by
  intro ht
  have h1 : d.t ∈ d.L₁ ⊓ centralizer ({d.t} : Set G) :=
    Subgroup.mem_inf.2 ⟨c.S_le_L₁ hB ht, mem_centralizer_singleton_iff.2 rfl⟩
  rw [hB.L₁_inf_centralizer_t] at h1
  exact hB.hyp.t_not_mem_L ((sup_le (d.pull_le_L _) (d.pull_le_L _) : d.A₃ ⊔ d.N₁ ≤ d.L) h1)

theorem hgen_tP_inf_S_le (hB : d.CaseBHyp) (c : d.CaseBData) : d.tP ⊓ c.S ≤ d.P := by
  intro x hx
  obtain ⟨hxt, hxS⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨m, hm, hxm | hxm⟩ := hB.hyp.exists_of_mem_zpowers_sup d.P_le_L hxt
  · rw [hxm]
    exact hm
  · exfalso
    apply hgen_t_not_mem_S hB c
    have : d.t = x * m⁻¹ := by rw [hxm]; group
    rw [this]
    exact mul_mem hxS (inv_mem (c.P_le_S hm))

theorem hgen_Qt_mem (hB : d.CaseBHyp) (c : d.CaseBData) {x : G} (hx : x ∈ c.Qc) :
    d.t⁻¹ * x * d.t ∈ c.Qt := by
  refine ⟨x, hx, ?_⟩
  change d.t * x * d.t⁻¹ = d.t⁻¹ * x * d.t
  rw [hB.hyp.t_inv']

theorem hgen_Qt_surj (hB : d.CaseBHyp) (c : d.CaseBData) {z : G} (hz : z ∈ c.Qt) :
    ∃ x ∈ c.Qc, z = d.t⁻¹ * x * d.t := by
  obtain ⟨x, hx, rfl⟩ := hz
  refine ⟨x, hx, ?_⟩
  change d.t * x * d.t⁻¹ = d.t⁻¹ * x * d.t
  rw [hB.hyp.t_inv']

theorem hgen_delta_mem_P (hB : d.CaseBHyp) (c : d.CaseBData) (h11 : CaseBData.Sec52Sylow hB c)
    {x : G} (hx : x ∈ c.Qc) : x * (d.t⁻¹ * x * d.t) ∈ d.P := by
  rw [← h11.map_δ]
  exact Subgroup.mem_map.2 ⟨⟨x, sec52_sylow_Qc_le_Kc c hx⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩

theorem hgen_mem_P (hB : d.CaseBHyp) (c : d.CaseBData) (h11 : CaseBData.Sec52Sylow hB c)
    {p : G} (hp : p ∈ d.P) : ∃ w ∈ c.Qc, p = w * (d.t⁻¹ * w * d.t) := by
  rw [← h11.map_δ] at hp
  obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hp
  exact ⟨w, Subgroup.mem_subgroupOf.1 hw, rfl⟩

theorem hgen_normalizer_S_tP_le (hB : d.CaseBHyp) (c : d.CaseBData)
    (h11 : CaseBData.Sec52Sylow hB c) :
    c.S ⊓ normalizer (d.tP : Set G) ≤ d.P ⊔ CFSG.centerIn c.Qt := by
  intro g hg
  obtain ⟨hgS, hgN⟩ := Subgroup.mem_inf.1 hg
  have hcomm := sec52_sylow_comm hB c
  have hgS' : g ∈ c.Qc ⊔ c.Qt := by rw [← h11.S_eq]; exact hgS
  obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_of_mem_sup_of_commute hcomm hgS'
  have hQK : ∀ {x : G}, x ∈ c.Qc → x ∈ c.Kc := fun hx => sec52_sylow_Qc_le_Kc c hx
  have hQtK : ∀ {x : G}, x ∈ c.Qt → x ∈ c.Kt := fun hx => sec52_sylow_Qt_le_Kt c hx
  obtain ⟨a', ha'def⟩ : ∃ a' : G, a' = d.t⁻¹ * a * d.t := ⟨_, rfl⟩
  have ha' : a' ∈ c.Qt := by rw [ha'def]; exact hgen_Qt_mem hB c ha
  have hy : a'⁻¹ * b ∈ c.Qt := mul_mem (inv_mem ha') hb
  have hyc : ∀ z ∈ c.Qt, (a'⁻¹ * b) * z = z * (a'⁻¹ * b) := by
    intro z hz
    obtain ⟨x, hx, hzx⟩ := hgen_Qt_surj hB c hz
    obtain ⟨x', hx'def⟩ : ∃ x' : G, x' = d.t⁻¹ * x * d.t := ⟨_, rfl⟩
    have hx' : x' ∈ c.Qt := by rw [hx'def]; exact hgen_Qt_mem hB c hx
    rw [hzx, ← hx'def]
    have hδx : x * x' ∈ d.P := by rw [hx'def]; exact hgen_delta_mem_P hB c h11 hx
    have hconjP : g * (x * x') * g⁻¹ ∈ d.P := by
      have h1 : g * (x * x') * g⁻¹ ∈ d.tP :=
        (mem_normalizer_iff.1 hgN _).1 ((le_sup_right : d.P ≤ d.tP) hδx)
      have h2 : g * (x * x') * g⁻¹ ∈ c.S :=
        mul_mem (mul_mem hgS (c.P_le_S hδx)) (inv_mem hgS)
      exact hgen_tP_inf_S_le hB c (Subgroup.mem_inf.2 ⟨h1, h2⟩)
    obtain ⟨w, hw, hwe⟩ := hgen_mem_P hB c h11 hconjP
    obtain ⟨m, hmdef⟩ : ∃ m : G, m = b * x' * b⁻¹ := ⟨_, rfl⟩
    have hmQt : m ∈ c.Qt := by rw [hmdef]; exact mul_mem (mul_mem hb hx') (inv_mem hb)
    have hxb : x * b = b * x := hcomm x hx b hb
    have ham : a * m = m * a := hcomm a ha m hmQt
    have hma : m * a⁻¹ = a⁻¹ * m := by
      calc m * a⁻¹ = a⁻¹ * (a * m) * a⁻¹ := by group
        _ = a⁻¹ * (m * a) * a⁻¹ := by rw [ham]
        _ = a⁻¹ * m := by group
    have hcomp : g * (x * x') * g⁻¹ = (a * x * a⁻¹) * m := by
      rw [hab]
      calc a * b * (x * x') * (a * b)⁻¹ = a * (b * x) * x' * b⁻¹ * a⁻¹ := by group
        _ = a * (x * b) * x' * b⁻¹ * a⁻¹ := by rw [← hxb]
        _ = a * x * (b * x' * b⁻¹) * a⁻¹ := by group
        _ = a * x * (m * a⁻¹) := by rw [hmdef]; group
        _ = (a * x * a⁻¹) * m := by rw [hma]; group
    have hKw : w ∈ c.Kc := hQK hw
    have huniq := eq_of_mul_eq_mul_of_inf_eq_bot (c.Kc_inf_Kt hB)
      (hQK (mul_mem (mul_mem ha hx) (inv_mem ha))) hKw (hQtK hmQt)
      (c.conj_mem_Kt hB hKw) (hcomp.symm.trans hwe)
    obtain ⟨hw1, hw2⟩ := huniq
    have hmeq : b * x' * b⁻¹ = a' * x' * a'⁻¹ := by
      rw [← hmdef, hw2, ← hw1, ha'def, hx'def]
      group
    calc a'⁻¹ * b * x' = a'⁻¹ * (b * x' * b⁻¹) * b := by group
      _ = a'⁻¹ * (a' * x' * a'⁻¹) * b := by rw [hmeq]
      _ = x' * (a'⁻¹ * b) := by group
  have hycenter : a'⁻¹ * b ∈ CFSG.centerIn c.Qt :=
    Subgroup.mem_inf.2 ⟨hy, mem_centralizer_iff.2 fun z hz => (hyc z hz).symm⟩
  have hga : g = (a * (d.t⁻¹ * a * d.t)) * (a'⁻¹ * b) := by
    rw [hab, ← ha'def]
    group
  rw [hga]
  exact Subgroup.mul_mem_sup (hgen_delta_mem_P hB c h11 ha) hycenter

theorem hGen (hB : d.CaseBHyp) (c : d.CaseBData) (h11 : CaseBData.Sec52Sylow hB c)
    (h52 : CaseBData.Sec52 c) : c.Hc = d.L ⊔ d.V := by
  have hd := hB.hyp
  have htinv : d.t⁻¹ = d.t := hd.t_inv'
  have hcomm := hgen_hcomm hB c h52
  haveI : Group.IsPerfect c.Nc := ⟨h52.quasisimple.1⟩
  have hrange := hgen_range_diag hB c h52
  have hcard := hgen_card_Nc hB c h52
  have heven : Even (Nat.card (c.Nc ⧸ center c.Nc)) := by
    have h1 : Nat.card c.Nc = Nat.card (c.Nc ⧸ center c.Nc) * Nat.card (center c.Nc) :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup (center c.Nc)
    have h2 : Nat.card (c.Nc ⧸ center c.Nc) = Nat.card d.L :=
      Nat.eq_of_mul_eq_mul_right Nat.card_pos (h1.symm.trans hcard)
    rw [h2]
    exact hgen_even_card_L hd
  have hsyl := hgen_isSylowOf_Qc_Nc hB c h52
  have key := CFSG.LocalAnalysis.odd_center_two_factor_diagonal_normalizer_generation hd.t_two
    h52.odd_center h52.quasisimple.2 heven hcomm hsyl.le hsyl.exists_sylow_eq_subgroupOf
  simp only at key
  obtain ⟨-, -, -, -, hgen⟩ := key
  have hδN : ((fun a : G => a * (d.t⁻¹ * a * d.t)) '' (c.Nc : Set G)) = (d.L : Set G) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have := h52.diag_mem x hx
      rw [htinv] at this ⊢
      exact this
    · intro hy
      obtain ⟨x, hx, hxy⟩ := h52.diag_surj y hy
      refine ⟨x, hx, ?_⟩
      show x * (d.t⁻¹ * x * d.t) = y
      rw [htinv]
      rw [htinv] at hxy
      exact hxy
  have hδU : closure ((fun a : G => a * (d.t⁻¹ * a * d.t)) '' (c.Qc : Set G)) = d.P := by
    have : ((fun a : G => a * (d.t⁻¹ * a * d.t)) '' (c.Qc : Set G)) = (d.P : Set G) := by
      ext p
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact hgen_delta_mem_P hB c h11 hx
      · intro hp
        obtain ⟨w, hw, rfl⟩ := hgen_mem_P hB c h11 hp
        exact ⟨w, hw, rfl⟩
    rw [this, closure_eq]
  have hPl : c.Qc ⊔ c.Qc.map (MulAut.conj d.t⁻¹).toMonoidHom = c.S := by
    rw [htinv, h11.S_eq]
    rfl
  have htP : d.P ⊔ zpowers d.t = d.tP := sup_comm _ _
  rw [hδN, hδU, hPl, htP, htinv] at hgen
  have hgen' : closure ((d.L : Set G) ∪
      ((c.S ⊓ normalizer (d.tP : Set G) : Subgroup G) : Set G)) = c.Hc := hgen
  have hZV : CFSG.centerIn c.Qt ≤ d.V := by
    rw [h11.V_eq]
    exact le_sup_right
  apply le_antisymm
  · rw [← hgen', closure_le]
    rintro x (hx | hx)
    · exact Subgroup.mem_sup_left hx
    · have hx' := hgen_normalizer_S_tP_le hB c h11 hx
      exact (sup_le (d.P_le_L.trans le_sup_left) (hZV.trans le_sup_right)) hx'
  · refine sup_le ?_ ?_
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := h52.diag_surj y hy
      exact mul_mem (Subgroup.mem_sup_left hx) (Subgroup.mem_sup_right ⟨x, hx, rfl⟩)
    · rw [h11.V_eq]
      exact sup_le (inf_le_left.trans ((hgen_Qc_le_Nc c).trans le_sup_left))
        (inf_le_left.trans ((Subgroup.map_mono (hgen_Qc_le_Nc c)).trans le_sup_right))

end CaseBData

end Data

namespace CaseBParts

theorem hGen : HGenStatement :=
  fun _ _ _ _ _ _ _ _ hB c h11 h52 => Data.CaseBData.hGen hB c h11 h52

end CaseBParts

end CFSG.LocalAnalysis.EvenBN.U5
