module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzR10ASet

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Certificates.FzR10A

variable {G : Type} [Group G] {t tau lam rho : G} {Z E W Q R T P : Subgroup G} {a b : G}

private lemma fzrAux_ap_lt (m : Mat) (n : ℕ) : m.ap n < 64 := by
  have h1 : (m.a * (n % 8) + m.b * (n / 8 % 8)) % 8 < 8 := Nat.mod_lt _ (by norm_num)
  have h2 : (m.c * (n % 8) + m.d * (n / 8 % 8)) % 8 < 8 := Nat.mod_lt _ (by norm_num)
  unfold Mat.ap
  omega

private lemma fzrAux_elt_mem (S : FzR10ASet t tau lam rho Z E W Q R T P a b) (n : ℕ) :
    fzrAElt a b n ∈ P := by
  unfold fzrAElt
  exact P.mul_mem (P.pow_mem S.basis.a_mem _) (P.pow_mem S.basis.b_mem _)

private lemma fzrAux_act_fix_iff (S : FzR10ASet t tau lam rho Z E W Q R T P a b) {M : Mat}
    (hc : FzR10AAct a b t M) {n : ℕ} (hn : n < 64) :
    M.ap n = n ↔ t * fzrAElt a b n = fzrAElt a b n * t := by
  constructor
  · intro h
    have h' : t * fzrAElt a b n * t⁻¹ = fzrAElt a b n := by rw [hc n hn, h]
    exact mul_inv_eq_iff_eq_mul.mp h'
  · intro h
    have h2 : t * fzrAElt a b n * t⁻¹ = fzrAElt a b n := by rw [h]; group
    have h3 : t * fzrAElt a b n * t⁻¹ = fzrAElt a b (M.ap n) := hc n hn
    exact S.basis.inj (M.ap n) n (fzrAux_ap_lt M n) hn (by rw [← h3, h2])

private lemma fzrAux_mem_fixP {M : Mat} {n : ℕ} :
    n ∈ fixP M ↔ n < 64 ∧ M.ap n = n := by
  rw [fixP, List.mem_filter, List.mem_range, beq_iff_eq]

theorem fzr_a_fix_iff_E (S : FzR10ASet t tau lam rho Z E W Q R T P a b) {M : Mat}
    (hc : FzR10AAct a b t M) {n : ℕ} (hn : n < 64) : M.ap n = n ↔ fzrAElt a b n ∈ E := by
  rw [fzrAux_act_fix_iff S hc hn]
  constructor
  · intro hcomm
    by_cases hpW : fzrAElt a b n ∈ W
    · exact S.pf.PW _ (fzrAux_elt_mem S n) hpW
    · exfalso
      exact S.str.Q_t _ (S.pf.PQ (fzrAux_elt_mem S n)) hpW (by rw [← hcomm]; group)
  · intro hpE
    exact S.str.W_comm t S.str.t_mem _ (S.str.EW hpE)

theorem fzr_a_fix_len (S : FzR10ASet t tau lam rho Z E W Q R T P a b) {M : Mat}
    (hc : FzR10AAct a b t M) : (fixP M).length = 16 := by
  classical
  have hfin : Finite E := Nat.finite_of_card_ne_zero (by rw [S.str.card_E]; norm_num)
  haveI : Fintype E := Fintype.ofFinite E
  have hnodup : (fixP M).Nodup := by rw [fixP]; exact List.nodup_range.filter _
  have hcard : (fixP M).toFinset.card = ((E : Set G)).toFinset.card := by
    refine Finset.card_bij (fun n _ => fzrAElt a b n) ?_ ?_ ?_
    · intro n hn
      rw [Set.mem_toFinset]
      have hn' : n < 64 ∧ M.ap n = n :=
        fzrAux_mem_fixP.mp (List.mem_toFinset.mp hn)
      exact (fzr_a_fix_iff_E S hc hn'.1).mp hn'.2
    · intro n1 hn1 n2 hn2 heq
      have h1 : n1 < 64 ∧ M.ap n1 = n1 :=
        fzrAux_mem_fixP.mp (List.mem_toFinset.mp hn1)
      have h2 : n2 < 64 ∧ M.ap n2 = n2 :=
        fzrAux_mem_fixP.mp (List.mem_toFinset.mp hn2)
      exact S.basis.inj n1 n2 h1.1 h2.1 heq
    · intro e he
      rw [Set.mem_toFinset] at he
      obtain ⟨n, hnlt, hne⟩ := S.basis.span e (S.pf.EP he)
      refine ⟨n, ?_, hne⟩
      exact List.mem_toFinset.mpr (fzrAux_mem_fixP.mpr
        ⟨hnlt, (fzr_a_fix_iff_E S hc hnlt).mpr (by rw [hne]; exact he)⟩)
  calc (fixP M).length = (fixP M).toFinset.card := (List.toFinset_card_of_nodup hnodup).symm
    _ = ((E : Set G)).toFinset.card := hcard
    _ = 16 := by
      rw [← Nat.card_eq_card_toFinset (E : Set G)]
      exact S.str.card_E

end CFSG.OddStandard.SmallF3.FritzII
