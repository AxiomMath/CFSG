module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzBK2B
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzBZ

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Certificates.FzBU FzbCoding

private theorem iterA_one (f : Array ℕ) (x : ℕ) : iterA f 1 x = f[x]! := rfl

private theorem iterA_two (f : Array ℕ) (x : ℕ) : iterA f 2 x = f[f[x]!]! := rfl

private theorem iterA_three (f : Array ℕ) (x : ℕ) : iterA f 3 x = f[f[f[x]!]!]! := rfl

private theorem iterA_four (f : Array ℕ) (x : ℕ) : iterA f 4 x = f[f[f[f[x]!]!]!]! := rfl

private theorem countBelow_congr {p p' : ℕ → Bool} (n : ℕ)
    (h : ∀ i < n, p i = p' i) : countBelow p n = countBelow p' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [countBelow, countBelow, h n (Nat.lt_succ_self n),
        ih (fun i hi => h i (Nat.lt_succ_of_lt hi))]

theorem fzb_tables_cond {G : Type} [Group G] {T₂ P : Subgroup G} (C : FzbCoding P)
    {t q s lam rho : G} (hR : FzbRel T₂ P t q s lam rho) (hN : ∀ g ∈ T₂, FzbNorm P g)
    (hρ : FzbNorm P rho) (hfpf : ∀ p ∈ P, rho * p * rho⁻¹ = p → p = 1)
    (hsZ : ∀ p ∈ P, C.enc (s * p * s⁻¹ * p⁻¹) < 4) :
    isRho (C.tab rho) = true ∧ condQ (C.tab rho) (C.tab q) = true ∧
      condS (C.tab rho) (C.tab q) (C.tab s) = true ∧ isInvR (C.tab rho) (C.tab lam) = true ∧
      commA (C.tab lam) (C.tab q) = true ∧ commA (C.tab lam) (C.tab s) = true := by
  have hqN : FzbNorm P q := hN q hR.q_mem
  have hsN : FzbNorm P s := hN s hR.s_mem
  have hlamN : FzbNorm P lam := hN lam hR.lam_mem
  have hqinv : q⁻¹ = q ^ 3 := by
    apply inv_eq_of_mul_eq_one_left
    rw [← pow_succ]
    exact hR.q_pow
  have hrhoinv : rho⁻¹ = rho ^ 2 := by
    apply inv_eq_of_mul_eq_one_left
    rw [← pow_succ]
    exact hR.rho_pow
  have hlrho : lam * rho = rho ^ 2 * lam := by
    have h1 : lam * rho = rho⁻¹ * lam := by
      have := congrArg (· * lam) hR.lam_rho
      simpa [mul_assoc] using this
    rw [h1, hrhoinv]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    rw [isRho, Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · rw [fzb_allBelow_iff]
      intro x hx
      rw [Bool.or_eq_true, beq_iff_eq, bne_iff_ne]
      by_cases hx0 : x = 0
      · exact Or.inl hx0
      · refine Or.inr ?_
        intro hfix
        apply hx0
        have hp : rho * C.dec x * rho⁻¹ = C.dec x := by
          rw [tab_dec C hρ hx, hfix]
        have h1 : C.dec x = 1 := hfpf (C.dec x) (C.dec_mem x hx) hp
        calc x = C.enc (C.dec x) := (C.enc_dec x hx).symm
          _ = C.enc 1 := by rw [h1]
          _ = 0 := C.enc_one
    · rw [fzb_allBelow_iff]
      intro x hx
      have h := tab_pow C hρ 3 hx
      rw [hR.rho_pow, tab_one C hx] at h
      rw [beq_iff_eq, ← iterA_three (C.tab rho) x]
      exact h.symm
  ·
    have htN : FzbNorm P t := by rw [← hR.q_sq]; exact FzbNorm.pow hqN 2
    rw [condQ, Bool.and_eq_true, Bool.and_eq_true]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact tab_comm C hqN hρ hR.rho_q.symm
    · rw [fzb_allBelow_iff]
      intro x hx
      have h := tab_pow C hqN 4 hx
      rw [hR.q_pow, tab_one C hx] at h
      rw [beq_iff_eq, ← iterA_four (C.tab q) x]
      exact h.symm
    · rw [beq_iff_eq]
      have hcongr : countBelow (fun x => (C.tab q)[(C.tab q)[x]!]! == x) 64
          = countBelow (fun x => (C.tab t)[x]! == x) 64 :=
        countBelow_congr 64 (fun x hx => by
          rw [← iterA_two (C.tab q) x, ← tab_pow C hqN 2 hx, hR.q_sq])
      rw [hcongr, tab_fix_count C htN, hR.card_cent]
  ·
    have htN : FzbNorm P t := by rw [← hR.q_sq]; exact FzbNorm.pow hqN 2
    rw [condS, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
    refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    ·
      exact tab_comm C hsN hρ hR.rho_s.symm
    ·
      obtain ⟨j, hj⟩ := hR.s_sq
      have hqj : q ^ j = q ^ (j % 4) := by
        have hdj : 4 * (j / 4) + j % 4 = j := Nat.div_add_mod j 4
        calc q ^ j = q ^ (4 * (j / 4) + j % 4) := by rw [hdj]
          _ = (q ^ 4) ^ (j / 4) * q ^ (j % 4) := by rw [pow_add, pow_mul]
          _ = q ^ (j % 4) := by rw [hR.q_pow, one_pow, one_mul]
      have hxj : ∀ x < 64,
          (C.tab s)[(C.tab s)[x]!]! = iterA (C.tab q) (j % 4) x := by
        intro x hx
        rw [← iterA_two (C.tab s) x, ← tab_pow C hsN 2 hx, hj, hqj,
          tab_pow C hqN (j % 4) hx]
      have hmod : j % 4 = 0 ∨ j % 4 = 1 ∨ j % 4 = 2 ∨ j % 4 = 3 := by
        have := Nat.mod_lt j (by norm_num : 0 < 4)
        omega
      rw [Bool.or_eq_true, Bool.or_eq_true, Bool.or_eq_true]
      rcases hmod with h0 | h1 | h2 | h3
      · left; left; left; rw [fzb_allBelow_iff]; intro x hx
        rw [beq_iff_eq, hxj x hx, h0]
        rfl
      · left; left; right; rw [fzb_allBelow_iff]; intro x hx
        rw [beq_iff_eq, hxj x hx, h1]
        exact iterA_one (C.tab q) x
      · left; right; rw [fzb_allBelow_iff]; intro x hx
        rw [beq_iff_eq, hxj x hx, h2]
        exact iterA_two (C.tab q) x
      · right; rw [fzb_allBelow_iff]; intro x hx
        rw [beq_iff_eq, hxj x hx, h3]
        exact iterA_three (C.tab q) x
    ·
      rw [Bool.or_eq_true]
      rcases hR.s_q with hq | hq
      · left
        apply tab_comm C hsN hqN
        have := congrArg (· * s) hq
        simpa [mul_assoc] using this
      · right
        rw [fzb_allBelow_iff]; intro x hx
        have hsq : s * q = q ^ 3 * s := by
          have h1 : s * q = q⁻¹ * s := by
            have := congrArg (· * s) hq
            simpa [mul_assoc] using this
          rw [h1, hqinv]
        rw [beq_iff_eq]
        calc (C.tab s)[(C.tab q)[x]!]!
            = (C.tab (s * q))[x]! := (tab_mul C hsN hqN hx).symm
          _ = (C.tab (q ^ 3 * s))[x]! := by rw [hsq]
          _ = (C.tab (q ^ 3))[(C.tab s)[x]!]! := tab_mul C (FzbNorm.pow hqN 3) hsN hx
          _ = (C.tab q)[(C.tab q)[(C.tab q)[(C.tab s)[x]!]!]!]! := by
                rw [tab_pow C hqN 3 (tab_lt C hsN hx), ← iterA_three]
    ·
      rw [fzb_allBelow_iff]; intro x hx
      rw [Bool.or_eq_true, bne_iff_ne, beq_iff_eq]
      by_cases hfix : (C.tab q)[(C.tab q)[x]!]! = x
      · right
        have hqsq : (C.tab q)[(C.tab q)[x]!]! = (C.tab t)[x]! := by
          rw [← iterA_two (C.tab q) x, ← tab_pow C hqN 2 hx, hR.q_sq]
        have htfix : (C.tab t)[x]! = x := by rw [← hqsq]; exact hfix
        have hpP : C.dec x ∈ P := C.dec_mem x hx
        have hpcent : C.dec x ∈ Subgroup.centralizer ({t} : Set G) := by
          rw [Subgroup.mem_centralizer_singleton_iff]
          have hconj : t * C.dec x * t⁻¹ = C.dec x := by
            rw [tab_dec C htN hx, htfix]
          have := congrArg (· * t) hconj
          simpa [mul_assoc] using this.symm
        have hpE : C.dec x ∈ P ⊓ Subgroup.centralizer ({t} : Set G) :=
          Subgroup.mem_inf.mpr ⟨hpP, hpcent⟩
        have hsdec : s * C.dec x * s⁻¹ = (C.dec x)⁻¹ := hR.s_inv _ hpE
        have hinvP : (C.dec x)⁻¹ ∈ P := P.inv_mem hpP
        have hasx : (C.tab s)[x]! = C.enc ((C.dec x)⁻¹) := by
          rw [tab_getElem C s hx, hsdec]
        rw [hasx]
        calc uMul (C.enc ((C.dec x)⁻¹)) x
            = uMul (C.enc ((C.dec x)⁻¹)) (C.enc (C.dec x)) := by rw [C.enc_dec x hx]
          _ = C.enc ((C.dec x)⁻¹ * C.dec x) :=
                (C.enc_mul (C.dec x)⁻¹ hinvP (C.dec x) hpP).symm
          _ = 0 := by rw [inv_mul_cancel, C.enc_one]
      · left; exact hfix
    ·
      rw [fzb_allBelow_iff]; intro p hp
      rw [fzb_anyBelow_iff]
      have hyP : C.dec p ∈ P := C.dec_mem p hp
      have hsyP : s * C.dec p * s⁻¹ ∈ P := hsN _ hyP
      have hcP : s * C.dec p * s⁻¹ * (C.dec p)⁻¹ ∈ P :=
        P.mul_mem hsyP (P.inv_mem hyP)
      set zc : ℕ := C.enc (s * C.dec p * s⁻¹ * (C.dec p)⁻¹) with hzdef
      refine ⟨zc, ?_, ?_⟩
      · rw [hzdef]; exact hsZ _ hyP
      · rw [beq_iff_eq]
        calc (C.tab s)[p]!
            = C.enc (s * C.dec p * s⁻¹) := tab_getElem C s hp
          _ = C.enc ((s * C.dec p * s⁻¹ * (C.dec p)⁻¹) * C.dec p) := by
                congr 1; group
          _ = uMul (C.enc (s * C.dec p * s⁻¹ * (C.dec p)⁻¹)) (C.enc (C.dec p)) :=
                C.enc_mul _ hcP (C.dec p) hyP
          _ = uMul zc p := by rw [hzdef, C.enc_dec p hp]
  ·
    rw [isInvR, Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · rw [fzb_allBelow_iff]; intro x hx
      have h := tab_pow C hlamN 2 hx
      rw [hR.lam_sq, tab_one C hx] at h
      rw [beq_iff_eq, ← iterA_two (C.tab lam) x]
      exact h.symm
    · rw [fzb_allBelow_iff]; intro x hx
      rw [beq_iff_eq]
      calc (C.tab lam)[(C.tab rho)[x]!]!
          = (C.tab (lam * rho))[x]! := (tab_mul C hlamN hρ hx).symm
        _ = (C.tab (rho ^ 2 * lam))[x]! := by rw [hlrho]
        _ = (C.tab (rho ^ 2))[(C.tab lam)[x]!]! := tab_mul C (FzbNorm.pow hρ 2) hlamN hx
        _ = (C.tab rho)[(C.tab rho)[(C.tab lam)[x]!]!]! := by
              rw [tab_pow C hρ 2 (tab_lt C hlamN hx), ← iterA_two]
  · exact tab_comm C hlamN hqN hR.lam_q
  · exact tab_comm C hlamN hsN hR.lam_s

end CFSG.OddStandard.SmallF3.FritzII
