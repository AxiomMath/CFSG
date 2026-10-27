module

public import CFSG.GH74.GLS.C3.Prop121.Card7H1
public import CFSG.GH74.GLS.C3.Prop121.Card7H2
public import Mathlib.Data.List.Sublists
public import Mathlib.Data.List.ProdSigma
public import Mathlib.Data.List.Nodup
public meta import CFSG.GH74.GLS.C3.Prop121.Card7H1
public meta import Batteries.Data.List.Basic
public meta import Mathlib.Algebra.Group.End
public meta import Mathlib.GroupTheory.Perm.Sign
public meta import Mathlib.GroupTheory.Perm.Basic
public meta import Mathlib.GroupTheory.Perm.Fin
public meta import Mathlib.Logic.Equiv.Fin.Basic
public meta import Mathlib.Logic.Equiv.Option
public meta import Mathlib.Data.List.FinRange
public import CFSG.GH74.GLS.C3.Prop121.Card7H3Inputs
public meta import CFSG.GH74.GLS.C3.Prop121.Card7H3Inputs
public import Certificates.Certificate5080
public import Certificates.Certificate5082

public section

namespace CFSG.GH74.GLS.C3.Prop121.Card7.HC

open Subgroup Equiv Perm CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model CFSG.GH74.GLS.Layer3

theorem classesCheck_true : classesCheck = true :=
  Certificates.certificate5082.1

theorem powCheck_true : powCheck = true :=
  Certificates.certificate5082.2.1

theorem ryCheck_true : ryCheck = true :=
  Certificates.certificate5082.2.2

theorem mem_B0L {σ : P11} : σ ∈ B0L ↔ σ ∈ HL ∧ σ * T1 = T1 * σ := by
  simp [B0L]

theorem mem_IL {σ : P11} : σ ∈ IL ↔ σ ∈ HL ∧ σ * T1 = T1 * σ ∧ σ * σ = 1 ∧ σ ≠ 1 := by
  simp only [IL, B0L, List.mem_filter, decide_eq_true_eq, and_assoc]

theorem B0L_nodup : B0L.Nodup := HL_nodup.filter _

theorem IL_nodup : IL.Nodup := B0L_nodup.filter _

theorem mem_cl96 {σ : P11} : σ ∈ cl96 ↔ σ ∈ IL ∧ ccL T1 σ = 96 := by
  simp [cl96]

theorem mem_cl48 {σ : P11} : σ ∈ cl48 ↔ σ ∈ IL ∧ ccL T1 σ = 48 := by
  simp [cl48]

theorem cl96_nodup : cl96.Nodup := IL_nodup.filter _

theorem cl48_nodup : cl48.Nodup := IL_nodup.filter _

theorem ev_mem_IL
    (a : H11) (h1 : a * tau1 = tau1 * a) (h2 : IsInv a) : ev a ∈ IL := by
  rw [ev_isInv] at h2
  rw [ev_comm_iff, ev_tau1] at h1
  exact mem_IL.2 ⟨HL_complete a, h1, h2.1, h2.2⟩

theorem exists_of_mem_IL {σ : P11} (h : σ ∈ IL) :
    ∃ a : H11, ev a = σ ∧ a * tau1 = tau1 * a ∧ IsInv a := by
  obtain ⟨h0, h1, h2, h3⟩ := mem_IL.1 h
  refine ⟨mkH σ (HL_hp σ h0), ev_mkH _ _, ?_, ?_⟩
  · rw [ev_comm_iff, ev_mkH, ev_tau1]; exact h1
  · rw [ev_isInv, ev_mkH]; exact ⟨h2, h3⟩

theorem exists_of_mem_B0L {σ : P11} (h : σ ∈ B0L) :
    ∃ a : H11, ev a = σ ∧ a * tau1 = tau1 * a := by
  obtain ⟨h0, h1⟩ := mem_B0L.1 h
  refine ⟨mkH σ (HL_hp σ h0), ev_mkH _ _, ?_⟩
  rw [ev_comm_iff, ev_mkH, ev_tau1]; exact h1

theorem zpowers_iff (a b : H11) (ha : ev a ∈ IL) (hb : ev b ∈ IL) :
    ystar ∈ zpowers (a * b) ↔ yPow (ev a * ev b) = true := by
  have hpow : (ev a * ev b) ^ 12 = 1 :=
    of_decide_eq_true (List.all_eq_true.1 (List.all_eq_true.1 powCheck_true _ ha) _ hb)
  have hg12 : (a * b) ^ 12 = 1 := ev_injective (by rw [map_pow, map_mul, hpow, map_one])
  have h12 : (a * b) ^ (12 : ℤ) = 1 := by
    have := hg12
    rw [← zpow_natCast] at this
    simpa using this
  unfold yPow
  rw [List.any_eq_true]
  constructor
  · intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h
    have hk' : (a * b) ^ ((k % 12).toNat) = ystar := by
      have h1 : (a * b) ^ k = (a * b) ^ ((k % 12).toNat) := by
        have h3 : ((k % 12).toNat : ℤ) = k % 12 :=
          Int.toNat_of_nonneg (Int.emod_nonneg k (by norm_num))
        rw [← zpow_natCast (a * b) ((k % 12).toNat), h3]
        calc (a * b) ^ k = (a * b) ^ (12 * (k / 12) + k % 12) := by rw [Int.mul_ediv_add_emod]
          _ = ((a * b) ^ (12 : ℤ)) ^ (k / 12) * (a * b) ^ (k % 12) := by rw [zpow_add, zpow_mul]
          _ = (a * b) ^ (k % 12) := by rw [h12, one_zpow, one_mul]
      rw [← h1, hk]
    refine ⟨(k % 12).toNat, List.mem_range.2 ?_, ?_⟩
    · omega
    · rw [decide_eq_true_iff]
      have := congrArg ev hk'
      rwa [map_pow, map_mul, ev_ystar] at this
  · rintro ⟨k, -, hk⟩
    rw [decide_eq_true_iff] at hk
    have : (a * b) ^ k = ystar := ev_injective (by rw [map_pow, map_mul, ev_ystar]; exact hk)
    rw [← this]
    exact Subgroup.npow_mem_zpowers _ _

theorem Y11_mem_IL : Y11 ∈ IL := by
  have h : (decide (Y11 ∈ IL)) = true := by
    have h := classesCheck_true
    simp only [classesCheck, Bool.and_eq_true] at h
    exact h.2
  exact of_decide_eq_true h

theorem classes_cover
    (b : P11) (hb : b ∈ IL) : ∃ c ∈ classes, b ∈ c.2 := by
  have h := classesCheck_true
  simp only [classesCheck, Bool.and_eq_true] at h
  have h1 := List.all_eq_true.1 h.1.1 b hb
  obtain ⟨c, hc, hbc⟩ := List.any_eq_true.1 h1
  exact ⟨c, hc, of_decide_eq_true hbc⟩

theorem classes_conj
    (c : P11 × List P11) (hc : c ∈ classes) (b : P11) (hb : b ∈ c.2) :
    ∃ g ∈ B0L, g * c.1 * g⁻¹ = b := by
  have h := classesCheck_true
  simp only [classesCheck, Bool.and_eq_true] at h
  have h1 := List.all_eq_true.1 (List.all_eq_true.1 h.1.2 c hc) b hb
  obtain ⟨g, hg, hgb⟩ := List.any_eq_true.1 h1
  exact ⟨g, hg, of_decide_eq_true hgb⟩

theorem ry_field (X' : Set H11)
    (hX1 : ∀ a ∈ X', a * tau1 = tau1 * a ∧ IsInv a) (hX2 : ystar ∉ X')
    (hX3 : ∀ a ∈ X', ∀ g : H11, g * tau1 = tau1 * g → g * a * g⁻¹ ∈ X')
    (h96 : Nat.card {b : H11 // b ∈ X' ∧ ccard H11 tau1 b = 96} = 6)
    (h48 : Nat.card {b : H11 // b ∈ X' ∧ ccard H11 tau1 b = 48} = 12) :
    Nat.card {p : H11 × H11 // p.1 ∈ X' ∧ (p.2 * tau1 = tau1 * p.2 ∧ IsInv p.2 ∧ p.2 ∉ X') ∧
      ystar ∈ zpowers (p.1 * p.2)} = 156 := by
  classical
  obtain ⟨inS, hinS⟩ : ∃ inS : P11 → Prop, ∀ σ, inS σ ↔ ∃ a ∈ X', ev a = σ :=
    ⟨_, fun _ => Iff.rfl⟩
  have hS_conj : ∀ σ, inS σ → ∀ g ∈ B0L, inS (g * σ * g⁻¹) := by
    intro σ hσ g hg
    obtain ⟨a, ha, rfl⟩ := (hinS σ).1 hσ
    obtain ⟨gH, rfl, hgc⟩ := exists_of_mem_B0L hg
    exact (hinS _).2 ⟨gH * a * gH⁻¹, hX3 a ha gH hgc, by rw [map_mul, map_mul, map_inv]⟩
  have hS_conj' : ∀ σ, inS σ → ∀ g ∈ B0L, inS (g⁻¹ * σ * g) := by
    intro σ hσ g hg
    obtain ⟨a, ha, rfl⟩ := (hinS σ).1 hσ
    obtain ⟨gH, rfl, hgc⟩ := exists_of_mem_B0L hg
    have hgc' : gH⁻¹ * tau1 = tau1 * gH⁻¹ :=
      (Commute.inv_left (show Commute gH tau1 from hgc)).eq
    refine (hinS _).2 ⟨gH⁻¹ * a * gH⁻¹⁻¹, hX3 a ha gH⁻¹ hgc', ?_⟩
    rw [inv_inv, map_mul, map_mul, map_inv]
  let R : List (P11 × List P11) := classes.filter fun c => decide (inS c.1)
  have hZ : ∀ b ∈ IL, inS b ↔ ZR R b = true := by
    intro b hb
    constructor
    · intro hbS
      obtain ⟨c, hc, hbc⟩ := classes_cover b hb
      obtain ⟨g, hg, hgb⟩ := classes_conj c hc b hbc
      have hr : inS c.1 := by
        have := hS_conj' b hbS g hg
        have e : g⁻¹ * b * g = c.1 := by rw [← hgb]; group
        rwa [e] at this
      refine List.any_eq_true.2 ⟨c, ?_, decide_eq_true hbc⟩
      exact List.mem_filter.2 ⟨hc, decide_eq_true hr⟩
    · intro hz
      obtain ⟨c, hcR, hbc⟩ := List.any_eq_true.1 hz
      have hbc' := of_decide_eq_true hbc
      obtain ⟨hc, hr⟩ := List.mem_filter.1 hcR
      have hr' := of_decide_eq_true hr
      obtain ⟨g, hg, hgb⟩ := classes_conj c hc b hbc'
      have := hS_conj c.1 hr' g hg
      rwa [hgb] at this
  have hXev : ∀ a ∈ X', ev a ∈ IL := fun a ha => ev_mem_IL a (hX1 a ha).1 (hX1 a ha).2
  have hXZ : ∀ a ∈ X', ZR R (ev a) = true := fun a ha =>
    (hZ _ (hXev a ha)).1 ((hinS _).2 ⟨a, ha, rfl⟩)
  have hnotZ : ∀ b : H11, ev b ∈ IL → b ∉ X' → ZR R (ev b) = false := by
    intro b hb hbX
    by_contra hne
    have hT : ZR R (ev b) = true := by simpa using hne
    obtain ⟨a, ha, hae⟩ := (hinS _).1 ((hZ _ hb).2 hT)
    exact hbX (by rwa [← ev_injective hae])
  have G1 : Nat.card {b : H11 // b ∈ X' ∧ ccard H11 tau1 b = 96} = (cl96.filter (ZR R)).length := by
    rw [← List.countP_eq_length_filter]
    refine card_subtype_eq_countP ev ev_injective cl96 cl96_nodup _ (ZR R) ?_ ?_ ?_
    · rintro b ⟨hb, hc⟩
      refine mem_cl96.2 ⟨hXev b hb, ?_⟩
      rw [← ev_tau1, ← ccard_eq]; exact hc
    · rintro b ⟨hb, -⟩
      exact hXZ b hb
    · intro n hn hZn
      have hnIL := (mem_cl96.1 hn).1
      obtain ⟨a, hae, -⟩ := exists_of_mem_IL hnIL
      obtain ⟨a', ha', hae'⟩ := (hinS _).1 ((hZ n hnIL).2 hZn)
      have : a' = a := ev_injective (hae'.trans hae.symm)
      subst this
      refine ⟨a', hae', ha', ?_⟩
      rw [ccard_eq, ev_tau1, hae']; exact (mem_cl96.1 hn).2
  have G2 : Nat.card {b : H11 // b ∈ X' ∧ ccard H11 tau1 b = 48} = (cl48.filter (ZR R)).length := by
    rw [← List.countP_eq_length_filter]
    refine card_subtype_eq_countP ev ev_injective cl48 cl48_nodup _ (ZR R) ?_ ?_ ?_
    · rintro b ⟨hb, hc⟩
      refine mem_cl48.2 ⟨hXev b hb, ?_⟩
      rw [← ev_tau1, ← ccard_eq]; exact hc
    · rintro b ⟨hb, -⟩
      exact hXZ b hb
    · intro n hn hZn
      have hnIL := (mem_cl48.1 hn).1
      obtain ⟨a, hae, -⟩ := exists_of_mem_IL hnIL
      obtain ⟨a', ha', hae'⟩ := (hinS _).1 ((hZ n hnIL).2 hZn)
      have : a' = a := ev_injective (hae'.trans hae.symm)
      subst this
      refine ⟨a', hae', ha', ?_⟩
      rw [ccard_eq, ev_tau1, hae']; exact (mem_cl48.1 hn).2
  have G3 : Nat.card {p : H11 × H11 // p.1 ∈ X' ∧
      (p.2 * tau1 = tau1 * p.2 ∧ IsInv p.2 ∧ p.2 ∉ X') ∧ ystar ∈ zpowers (p.1 * p.2)} =
      pairCount R := by
    unfold pairCount
    refine card_subtype_eq_countP (fun p : H11 × H11 => (ev p.1, ev p.2))
      (fun p q h => Prod.ext (ev_injective (congrArg Prod.fst h)) (ev_injective (congrArg Prod.snd h)))
      _ ((IL_nodup.filter _).product (IL_nodup.filter _)) _ (fun p => yPow (p.1 * p.2)) ?_ ?_ ?_
    · rintro ⟨a, b⟩ ⟨ha, ⟨hb1, hb2, hb3⟩, hz⟩
      refine List.mem_product.2 ⟨?_, ?_⟩
      · exact List.mem_filter.2 ⟨hXev a ha, hXZ a ha⟩
      · have hbIL := ev_mem_IL b hb1 hb2
        refine List.mem_filter.2 ⟨hbIL, ?_⟩
        rw [hnotZ b hbIL hb3]; rfl
    · rintro ⟨a, b⟩ ⟨ha, ⟨hb1, hb2, hb3⟩, hz⟩
      exact (zpowers_iff a b (hXev a ha) (ev_mem_IL b hb1 hb2)).1 hz
    · rintro ⟨σ, ρ⟩ hn hQ
      obtain ⟨hσ, hρ⟩ := List.mem_product.1 hn
      obtain ⟨hσIL, hσZ⟩ := List.mem_filter.1 hσ
      obtain ⟨hρIL, hρZ⟩ := List.mem_filter.1 hρ
      obtain ⟨a, rfl, ha1, ha2⟩ := exists_of_mem_IL hσIL
      obtain ⟨b, rfl, hb1, hb2⟩ := exists_of_mem_IL hρIL
      have haX : a ∈ X' := by
        obtain ⟨a', ha', hae'⟩ := (hinS _).1 ((hZ _ hσIL).2 hσZ)
        rwa [← ev_injective hae']
      have hbX : b ∉ X' := by
        intro hbX
        have := hXZ b hbX
        rw [Bool.not_eq_true'] at hρZ
        rw [hρZ] at this
        exact Bool.noConfusion this
      exact ⟨(a, b), rfl, haX, ⟨hb1, hb2, hbX⟩, (zpowers_iff a b hσIL hρIL).2 hQ⟩
  have hR96 : (cl96.filter (ZR R)).length = 6 := by rw [← G1]; exact h96
  have hR48 : (cl48.filter (ZR R)).length = 12 := by rw [← G2]; exact h48
  have hRY : ZR R Y11 = false := by
    by_contra hne
    have hT : ZR R Y11 = true := by simpa using hne
    obtain ⟨a, ha, hae⟩ := (hinS _).1 ((hZ Y11 Y11_mem_IL).2 hT)
    have : a = ystar := ev_injective (by rw [hae, ev_ystar])
    exact hX2 (this ▸ ha)
  have hsub : R ∈ classes.sublists := List.mem_sublists.2 List.filter_sublist
  have hcheck := of_decide_eq_true (List.all_eq_true.1 ryCheck_true R hsub)
  rw [G3]
  exact hcheck hR96 hR48 hRY

end CFSG.GH74.GLS.C3.Prop121.Card7.HC
