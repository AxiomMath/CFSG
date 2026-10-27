module

public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Gen5
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.L287

public section

namespace CFSG.GH74.GLS.Stage1.Thm2.Recip

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage1.Thm6
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {x y : G} {L J : Subgroup G} {a : G}

theorem FailB.x_ne_y (h : FailB G x y L J a) : x ≠ y := by
  intro hxy
  subst hxy
  by_cases hLJ : L = J
  · apply h.haL
    have : a ∈ L := hLJ ▸ h.ha
    exact le_normalizer this
  · exact h.haL ((le_cSec_of_ne h.cfg.hJ.1 h.cfg.hL.1 (fun e => hLJ e.symm) h.ha).1)

theorem FailB.exists_pow (h : FailB G x y L J a) :
    ∃ m : ℕ, 2 ≤ m ∧ orderOf a = 2 ^ m ∧ y = a ^ (2 ^ (m - 1)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp h.ha2) ⟨a, Subgroup.mem_zpowers a⟩
  have hm' : orderOf a = 2 ^ m := by simpa using hm
  have ha1 : a ≠ 1 := fun h1 => h.hay (h1 ▸ one_mem _)
  have hm2 : 2 ≤ m := by
    by_contra hlt
    push Not at hlt
    interval_cases m
    · exact ha1 (orderOf_eq_one_iff.mp (by simpa using hm'))
    · have ha2 : orderOf a = 2 := by simpa using hm'
      have : a = y := h.cfg.hJ.eq_of_involution h.cfg.hy h.ha ha2
      exact h.hay (this ▸ mem_zpowers y)
  refine ⟨m, hm2, hm', ?_⟩
  have hpos : orderOf a ≠ 0 := (orderOf_pos a).ne'
  have h2 : 2 ∣ orderOf a := by
    rw [hm']
    exact dvd_pow_self 2 (by omega)
  have hord : orderOf (a ^ (orderOf a / 2)) = 2 := orderOf_pow_orderOf_div hpos h2
  have hmem : a ^ (orderOf a / 2) ∈ J := pow_mem h.ha _
  have hy' := h.cfg.hJ.eq_of_involution h.cfg.hy hmem hord
  rw [← hy', hm']
  congr 1
  rw [show 2 ^ m = 2 * 2 ^ (m - 1) by rw [← pow_succ']; congr 1; omega]
  omega

theorem FailB.not_fAut (hBal : IG_balance_fAut) (h : FailB G x y L J a) :
    ¬ InducesFAut x J ∧ ¬ InducesFAut y L := by
  have key : ¬ (InducesFAut x J ∨ InducesFAut y L) := fun hf =>
    h.haL ((lemma_28_3 hBal G x y L J h.cfg hf).2.2.2 h.hxJ a h.ha h.ha2 h.hay h.hax)
  exact ⟨fun hx => key (Or.inl hx), fun hy => key (Or.inr hy)⟩

theorem FailB.swap (hBal : IG_balance_fAut) (h44 : II4_44) (hAut : II4_Aut) (h327 : IG_3_27)
    (h : FailB G x y L J a) : ∃ g : G, g⁻¹ * x * g = y ∧ g⁻¹ * y * g = x := by
  have hyN := lemma_28_7 hBal h44 hAut h327 G x y L J h.cfg h.hxJ
  obtain ⟨hfx, hfy⟩ := h.not_fAut hBal
  exact (lemma_28_4 h44 hAut G h.cfg.simple x h.cfg.hx L h.cfg.hL y h.cfg.hy hyN hfy).2 J
    h.cfg.hJ h.hxJ hfx

theorem FailB.sq_mem_normalizer (hyN : y ∈ normalizer (L : Set G)) (h : FailB G x y L J a) :
    a * a ∈ normalizer (L : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm2, hm, -⟩ := h.exists_pow
  have hy1 := mul_self_eq_one_of_orderOf_eq_two h.cfg.hy
  by_contra hna
  have hdvd : 2 ∣ orderOf a := by
    rw [hm]
    exact dvd_pow_self 2 (by omega)
  have hlt : orderOf (a * a) < orderOf a := by
    rw [← pow_two, orderOf_pow_of_dvd (by norm_num) hdvd]
    exact Nat.div_lt_self (orderOf_pos a) (by norm_num)
  by_cases hbyz : a * a ∈ zpowers y
  · rcases eq_one_or_eq_of_mem_zpowers hy1 hbyz with h1 | h1
    · have h2 : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h1)
      have h3 : orderOf a ≤ 2 := Nat.le_of_dvd (by norm_num) h2
      have h4 : 4 ≤ orderOf a := by
        rw [hm]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
      omega
    · exact hna (h1 ▸ hyN)
  · have hb2 : IsPGroup 2 ↥(zpowers (a * a)) :=
      h.ha2.to_le (zpowers_le.mpr (mul_mem (mem_zpowers a) (mem_zpowers a)))
    have hcomm : Commute (a * a) x := (h.hax.mul_left h.hax)
    have hle := h.hmin (a * a) (mul_mem h.ha h.ha) hb2 hbyz hcomm hna
    omega

structure Setup (G : Type) [Group G] [Finite G] (x y : G) (L J : Subgroup G) (a : G)
    (Py P : Subgroup G) (w : G) : Prop where
  hFB : FailB G x y L J a
  hyN : y ∈ normalizer (L : Set G)
  hnfx : ¬ InducesFAut x J
  hnfy : ¬ InducesFAut y L
  a2N : a * a ∈ normalizer (L : Set G)
  hPy : IsSylow2In Py (centralizer ({x} : Set G) ⊓ centralizer ({y} : Set G))
  haPy : a ∈ Py
  hP : IsSylow2In P (centralizer ({x} : Set G))
  hPyP : Py ≤ P
  hwP : w ∈ P ⊓ L
  hwPy : w ∉ Py
  hw4 : orderOf w = 4
  hwinv : y * w * y⁻¹ = w⁻¹

theorem exists_setup (hBal : IG_balance_fAut) (h44 : II4_44) (hAut : II4_Aut) (h327 : IG_3_27)
    (h : FailB G x y L J a) : ∃ (Py P : Subgroup G) (w : G), Setup G x y L J a Py P w := by
  have hyN := lemma_28_7 hBal h44 hAut h327 G x y L J h.cfg h.hxJ
  obtain ⟨hfx, hfy⟩ := h.not_fAut hBal
  have hy1 := mul_self_eq_one_of_orderOf_eq_two h.cfg.hy
  have haW : a ∈ centralizer ({x} : Set G) ⊓ centralizer ({y} : Set G) :=
    ⟨mem_centralizer_singleton_iff.mpr h.hax, h.cfg.hJ.1.1 h.ha⟩
  obtain ⟨Py, hPy, hAPy⟩ := exists_isSylow2In_of_le h.ha2 (zpowers_le.mpr haW)
  have haPy : a ∈ Py := hAPy (mem_zpowers a)
  have hPyle : Py ≤ centralizer ({x} : Set G) := hPy.1.trans inf_le_left
  obtain ⟨P, hP, hPyP⟩ := exists_isSylow2In_of_le hPy.2.1 hPyle
  have hyW : y ∈ centralizer ({x} : Set G) ⊓ centralizer ({y} : Set G) :=
    ⟨mem_centralizer_singleton_iff.mpr h.cfg.comm.symm, mem_centralizer_singleton_iff.mpr rfl⟩
  have hyPy : y ∈ Py := mem_of_isSylow2In_of_central hPy hyW
    (fun g hg => (mem_centralizer_singleton_iff.mp hg.2).symm) hy1
  have hE₀ : pLayerOf 2 (centralizer ({x} : Set G)) ≤ centralizer ({x} : Set G) :=
    TwoThin.pLayerOf_le 2 _
  have hLE : L ≤ pLayerOf 2 (centralizer ({x} : Set G)) := le_sSup h.cfg.hL.1
  have hS1 := isSylow2In_inf_normal hP hE₀ (fun g hg => mem_normalizer_pLayerOf hg)
  have hS2 := isSylow2In_inf_normal hS1 hLE (fun g hg => pLayerOf_le_normalizer h.cfg.hL.1 hg)
  have hPL : P ⊓ pLayerOf 2 (centralizer ({x} : Set G)) ⊓ L = P ⊓ L := by
    rw [inf_assoc, inf_eq_right.mpr hLE]
  rw [hPL] at hS2
  have hyP : y ∈ P := hPyP hyPy
  have hyPL : ∀ r ∈ P ⊓ L, y * r * y⁻¹ ∈ P ⊓ L := fun r hr =>
    Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem hyP hr.1) (inv_mem hyP),
      (mem_normalizer_iff.mp hyN r).mp hr.2⟩
  obtain ⟨w, hwS, hw4, hwinv⟩ := exists_inverted_of_sylow h44 hAut h.cfg.simple h.cfg.hx h.cfg.hL
    h.cfg.hy hyN hfy hS2 hyPL
  refine ⟨Py, P, w, h, hyN, hfx, hfy, h.sq_mem_normalizer hyN, hPy, haPy, hP, hPyP, hwS, ?_, hw4,
    hwinv⟩
  intro hwPy
  have hc : w * y = y * w := mem_centralizer_singleton_iff.mp (hPy.1 hwPy).2
  have hww : w = w⁻¹ := by
    calc w = y * w * y⁻¹ := by rw [← hc]; group
      _ = w⁻¹ := hwinv
  have hw2 : w * w = 1 := mul_eq_one_iff_eq_inv.mpr hww
  have hdvd : orderOf w ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hw2)
  rw [hw4] at hdvd
  norm_num at hdvd

end CFSG.GH74.GLS.Stage1.Thm2.Recip
