module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzR10AFix
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzR10AAct
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzR10AElt
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzR10AMat

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Certificates.FzR10A
open scoped commutatorElement

variable {G : Type} [Group G] {t tau lam rho : G} {Z E W Q R T P : Subgroup G} {a b : G}

private lemma fzrAux_comm_of_conj {x y : G} (h : x * y * x⁻¹ = y) : x * y = y * x := by
  have h1 : (x * y * x⁻¹) * x = y * x := congrArg (· * x) h
  simpa [mul_assoc] using h1

private lemma fzrAux_inv_of_sq_one {x : G} (h : x * x = 1) : x⁻¹ = x :=
  inv_eq_of_mul_eq_one_right h

private lemma fzrAux_inv_of_cube_one {x : G} (h : x ^ 3 = 1) : x⁻¹ = x * x := by
  have hpow : x ^ 3 = x * (x * x) := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, pow_two, mul_assoc]
  exact inv_eq_of_mul_eq_one_right (by rw [← hpow]; exact h)

private lemma fzrAux_comm_conj_mul {x y z : G} (h : x * y = y * x) :
    ⁅x, y * z⁆ = y * ⁅x, z⁆ * y⁻¹ := by
  have h1 : ⁅x, y⁆ = 1 := by rw [commutatorElement_def, h]; group
  rw [commutatorElement_mul_right_eq_mul_conj, h1, one_mul]

private lemma fzrAux_not_beq {α : Type} [BEq α] [LawfulBEq α] {x y : α} (h : x ≠ y) :
    (!(x == y)) = true := by
  have hb : (x == y) = false := Bool.eq_false_of_not_eq_true (fun hxy => h (beq_iff_eq.mp hxy))
  rw [hb]
  rfl

private lemma fzrAux_mem_T_of_mem_P (S : FzR10ASet t tau lam rho Z E W Q R T P a b) {g : G}
    (hg : g ∈ P) : g ∈ T :=
  S.str.RT (S.str.QR (S.pf.PQ hg))

private lemma fzrAux_act_subP_eq_z (S : FzR10ASet t tau lam rho Z E W Q R T P a b)
    {M : Mat} (hc : FzR10AAct a b t M) {p : ℕ} (hp : p < 64) :
    ∃ z ∈ Z, fzrAElt a b (subP (M.ap p) p) = z := by
  have hgT : fzrAElt a b p ∈ T := fzrAux_mem_T_of_mem_P S (fzr_a_elt_mem S.basis p)
  obtain ⟨z, hzZ, hz⟩ := S.str.T_t (fzrAElt a b p) hgT
  refine ⟨z, hzZ, ?_⟩
  have htsq : t * t = 1 := by simpa [pow_two] using S.str.t_sq
  have htinv : t⁻¹ = t := fzrAux_inv_of_sq_one htsq
  have hzt : t * fzrAElt a b p * t⁻¹ * (fzrAElt a b p)⁻¹ = z := by
    calc t * fzrAElt a b p * t⁻¹ * (fzrAElt a b p)⁻¹
        = t * (fzrAElt a b p * t * (fzrAElt a b p)⁻¹) := by rw [htinv]; group
      _ = t * (t * z) := by rw [hz]
      _ = z := by rw [← mul_assoc, htsq, one_mul]
  rw [hc p hp, fzr_a_elt_div S.basis (fzr_a_ap_lt M p) hp] at hzt
  exact hzt

private lemma fzrAux_subsP_mem_E (S : FzR10ASet t tau lam rho Z E W Q R T P a b)
    {M : Mat} (hc : FzR10AAct a b tau M) {p : ℕ} (hp : p < 64) :
    fzrAElt a b (subP (M.ap p) p) ∈ E := by
  have hgQ : fzrAElt a b p ∈ Q := S.pf.PQ (fzr_a_elt_mem S.basis p)
  have hcomm : fzrAElt a b (subP (M.ap p) p) = ⁅tau, fzrAElt a b p⁆ := by
    rw [commutatorElement_def, hc p hp, fzr_a_elt_div S.basis (fzr_a_ap_lt M p) hp]
  have hW : fzrAElt a b (subP (M.ap p) p) ∈ W := by
    rw [hcomm]
    exact S.str.tau_Q _ hgQ
  exact S.pf.PW _ (fzr_a_elt_mem S.basis _) hW

private lemma fzrAux_lam_Q_P (S : FzR10ASet t tau lam rho Z E W Q R T P a b) :
    ∃ p, p < 64 ∧ fzrAElt a b p ∈ P ∧ ⁅lam, fzrAElt a b p⁆ ∉ W := by
  obtain ⟨n, hnQ, hnW⟩ := S.str.lam_Q
  have hlamt : lam * t = t * lam := fzrAux_comm_of_conj S.str.lam_t
  rcases S.pf.Q_eq n hnQ with hnP | hnP
  · obtain ⟨p, hp, hpe⟩ := S.basis.span n hnP
    subst n
    exact ⟨p, hp, hnP, hnW⟩
  · obtain ⟨p, hp, hpe⟩ := S.basis.span (t * n) hnP
    refine ⟨p, hp, ?_, ?_⟩
    · rw [hpe]; exact hnP
    · rw [hpe]
      have hn_eq : n = t * (t * n) := by rw [← mul_assoc, ← pow_two, S.str.t_sq, one_mul]
      have hconj : ⁅lam, n⁆ = t * ⁅lam, t * n⁆ * t⁻¹ := by
        conv_lhs => rw [hn_eq]
        rw [fzrAux_comm_conj_mul hlamt]
      intro hW
      apply hnW
      rw [hconj]
      exact W.mul_mem (W.mul_mem S.str.t_mem hW) (W.inv_mem S.str.t_mem)

theorem fzr_a_candT (S : FzR10ASet t tau lam rho Z E W Q R T P a b) {M : Mat}
    (hM : FzR10AMatLt M) (hc : FzR10AAct a b t M) : candT M = true := by
  have hrho0 : FzR10AMatLt rho0 := by simp [FzR10AMatLt, rho0]
  have ht2 : t * t = 1 := by simpa [pow_two] using S.str.t_sq
  have hmm : M.mul M = Mat.one := fzr_a_act_sq_one S.basis hM hc ht2
  have hcomm : M.mul rho0 = rho0.mul M :=
    fzr_a_act_comm S.basis hM hrho0 hc S.rho_act (fzrAux_comm_of_conj S.str.rho_t).symm
  have hfixlen : (fixP M).length = 16 := fzr_a_fix_len S hc
  have hD : (fixP M).all (fun p => p % 2 == 0 && p / 8 % 2 == 0) = true := by
    rw [List.all_eq_true]
    intro p hp
    obtain ⟨hp_range, hp_fix⟩ := List.mem_filter.mp hp
    have hp_lt : p < 64 := List.mem_range.mp hp_range
    have hp_eq : M.ap p = p := beq_iff_eq.mp hp_fix
    have hE : fzrAElt a b p ∈ E := (fzr_a_fix_iff_E S hc hp_lt).mp hp_eq
    have h4 : (fzrAElt a b p) ^ 4 = 1 := S.str.E_exp _ hE
    have hpar : p % 2 = 0 ∧ p / 8 % 2 = 0 :=
      (fzr_a_elt_pow4_eq_one_iff S.basis hp_lt).mp h4
    rw [Bool.and_eq_true_iff, beq_iff_eq, beq_iff_eq]
    exact hpar
  have hE : (List.range 64).all (fun p => inZ (subP (M.ap p) p)) = true := by
    rw [List.all_eq_true]
    intro p hp
    have hp_lt : p < 64 := List.mem_range.mp hp
    obtain ⟨z, hzZ, hz⟩ := fzrAux_act_subP_eq_z S hc hp_lt
    have hsq : (fzrAElt a b (subP (M.ap p) p)) ^ 2 = 1 := by
      rw [hz]; exact S.str.Z_sq z hzZ
    exact (fzr_a_elt_sq_eq_one_iff S.basis (fzr_a_subP_lt _ _)).mp hsq
  rw [candT]
  simp only [Bool.and_eq_true_iff]
  exact ⟨⟨⟨⟨beq_iff_eq.mpr hmm, beq_iff_eq.mpr hcomm⟩, beq_iff_eq.mpr hfixlen⟩, hD⟩, hE⟩

theorem fzr_a_candS (S : FzR10ASet t tau lam rho Z E W Q R T P a b) {Mt Ms : Mat}
    (hMt : FzR10AMatLt Mt) (hMs : FzR10AMatLt Ms) (hct : FzR10AAct a b t Mt)
    (hcs : FzR10AAct a b tau Ms) : candS Mt Ms = true := by
  have hrho0 : FzR10AMatLt rho0 := by simp [FzR10AMatLt, rho0]
  have hmm : Ms.mul Ms = Mat.one :=
    fzr_a_act_sq_one S.basis hMs hcs (by simpa [pow_two] using S.pf.tau_sq1)
  have hcommrho : Ms.mul rho0 = rho0.mul Ms :=
    fzr_a_act_comm S.basis hMs hrho0 hcs S.rho_act S.str.tau_rho
  have hcommt : Ms.mul Mt = Mt.mul Ms :=
    fzr_a_act_comm S.basis hMs hMt hcs hct (fzrAux_comm_of_conj S.str.tau_t)
  have hne : Ms ≠ Mat.one := by
    intro h1
    have hEZ : E ≤ Z := by
      intro e he
      obtain ⟨n, hn, rfl⟩ := S.basis.span e (S.pf.EP he)
      have hone : Ms.ap n = n := by rw [h1]; exact fzr_a_ap_one hn
      have hact : tau * fzrAElt a b n * tau⁻¹ = fzrAElt a b n := by
        rw [hcs n hn, hone]
      have htau : tau * fzrAElt a b n * tau⁻¹ = (fzrAElt a b n)⁻¹ :=
        S.str.tau_W _ (S.str.EW he)
      have heq : fzrAElt a b n = (fzrAElt a b n)⁻¹ := hact.symm.trans htau
      have he2 : fzrAElt a b n * fzrAElt a b n = 1 := by
        nth_rewrite 1 [heq]
        exact inv_mul_cancel _
      exact S.str.E_invol _ he (by simpa [pow_two] using he2)
    haveI : Finite Z := Nat.finite_of_card_ne_zero (by rw [S.str.card_Z]; norm_num)
    have hcard : Nat.card E ≤ Nat.card Z := Subgroup.card_le_of_le hEZ
    rw [S.str.card_E, S.str.card_Z] at hcard
    omega
  have hne_bool : (!(Ms == Mat.one)) = true := fzrAux_not_beq hne
  have hfix : (fixP Mt).all (fun p => Ms.ap p == subP 0 p) = true := by
    rw [List.all_eq_true]
    intro p hp
    obtain ⟨hp_range, hp_fix⟩ := List.mem_filter.mp hp
    have hp_lt : p < 64 := List.mem_range.mp hp_range
    have hp_eq : Mt.ap p = p := beq_iff_eq.mp hp_fix
    have hE : fzrAElt a b p ∈ E := (fzr_a_fix_iff_E S hct hp_lt).mp hp_eq
    have hW : fzrAElt a b p ∈ W := S.str.EW hE
    have heq : fzrAElt a b (Ms.ap p) = fzrAElt a b (subP 0 p) := by
      rw [← hcs p hp_lt, S.str.tau_W _ hW, fzr_a_elt_inv S.basis hp_lt]
    have hnum : Ms.ap p = subP 0 p :=
      (fzr_a_elt_eq_iff S.basis (fzr_a_ap_lt Ms p) (fzr_a_subP_lt 0 p)).mp heq
    exact beq_iff_eq.mpr hnum
  have hcontains : (List.range 64).all (fun p => (fixP Mt).contains (subP (Ms.ap p) p)) = true := by
    rw [List.all_eq_true]
    intro p hp
    have hp_lt : p < 64 := List.mem_range.mp hp
    apply List.contains_iff.mpr
    rw [fixP, List.mem_filter]
    refine ⟨List.mem_range.mpr (fzr_a_subP_lt _ _), ?_⟩
    exact beq_iff_eq.mpr ((fzr_a_fix_iff_E S hct (fzr_a_subP_lt _ _)).mpr
      (fzrAux_subsP_mem_E S hcs hp_lt))
  rw [candS]
  simp only [Bool.and_eq_true_iff]
  exact ⟨⟨⟨⟨⟨beq_iff_eq.mpr hmm, beq_iff_eq.mpr hcommrho⟩, beq_iff_eq.mpr hcommt⟩,
    hne_bool⟩, hfix⟩, hcontains⟩

theorem fzr_a_candL (S : FzR10ASet t tau lam rho Z E W Q R T P a b) {Mt Ml : Mat}
    (hMt : FzR10AMatLt Mt) (hMl : FzR10AMatLt Ml) (hct : FzR10AAct a b t Mt)
    (hcl : FzR10AAct a b lam Ml) : candL Mt Ml = true := by
  have hrho0 : FzR10AMatLt rho0 := by simp [FzR10AMatLt, rho0]
  have hrho2lt : FzR10AMatLt (rho0.mul rho0) := fzr_a_mul_lt rho0 rho0
  have hrho2 : FzR10AAct a b (rho * rho) (rho0.mul rho0) := fzr_a_act_mul S.rho_act S.rho_act
  have hmm : Ml.mul Ml = Mat.one :=
    fzr_a_act_sq_one S.basis hMl hcl (by simpa [pow_two] using S.str.lam_sq)
  have hinvrho : rho⁻¹ = rho * rho := fzrAux_inv_of_cube_one S.str.rho_ord
  have hlamrho : lam * rho = (rho * rho) * lam := by
    calc lam * rho = (lam * rho * lam⁻¹) * lam := by group
      _ = rho⁻¹ * lam := by rw [S.str.lam_rho]
      _ = (rho * rho) * lam := by rw [hinvrho]
  have hcommrho : Ml.mul rho0 = (rho0.mul rho0).mul Ml :=
    fzr_a_act_mul_eq S.basis hMl hrho0 hrho2lt hMl hcl S.rho_act hrho2 hcl hlamrho
  have hcommt : Ml.mul Mt = Mt.mul Ml :=
    fzr_a_act_comm S.basis hMl hMt hcl hct (fzrAux_comm_of_conj S.str.lam_t)
  have hanyZ : (List.range 64).any (fun p => inZ p && Ml.ap p != p) = true := by
    obtain ⟨z, hzZ, hzfix⟩ := S.str.lam_Z
    obtain ⟨p, hp_lt, hpz⟩ := S.basis.span z (S.pf.EP (S.str.ZE hzZ))
    have hinZ : inZ p = true := by
      have hz2 : z ^ 2 = 1 := S.str.Z_sq z hzZ
      rw [← hpz] at hz2
      exact (fzr_a_elt_sq_eq_one_iff S.basis hp_lt).mp hz2
    have hne : Ml.ap p ≠ p := by
      intro hfix
      apply hzfix
      rw [← hpz, hcl p hp_lt, hfix]
    exact List.any_eq_true.mpr ⟨p, List.mem_range.mpr hp_lt, by
      rw [Bool.and_eq_true_iff, bne_iff_ne]
      exact ⟨hinZ, hne⟩⟩
  have hanyQ : (List.range 64).any
      (fun p => Mt.ap (subP (Ml.ap p) p) != subP (Ml.ap p) p) = true := by
    obtain ⟨p, hp_lt, _hpP, hpW⟩ := fzrAux_lam_Q_P S
    refine List.any_eq_true.mpr ⟨p, List.mem_range.mpr hp_lt, ?_⟩
    rw [bne_iff_ne]
    intro hfix
    apply hpW
    have hcomm : ⁅lam, fzrAElt a b p⁆ = fzrAElt a b (subP (Ml.ap p) p) := by
      rw [commutatorElement_def, hcl p hp_lt,
        fzr_a_elt_div S.basis (fzr_a_ap_lt Ml p) hp_lt]
    rw [hcomm]
    exact S.str.EW ((fzr_a_fix_iff_E S hct (fzr_a_subP_lt _ _)).mp hfix)
  rw [candL]
  simp only [Bool.and_eq_true_iff]
  exact ⟨⟨⟨⟨beq_iff_eq.mpr hmm, beq_iff_eq.mpr hcommrho⟩, beq_iff_eq.mpr hcommt⟩, hanyZ⟩, hanyQ⟩

theorem fzr_a_comm_SL (S : FzR10ASet t tau lam rho Z E W Q R T P a b) {Ms Ml : Mat}
    (hMs : FzR10AMatLt Ms) (hMl : FzR10AMatLt Ml) (hcs : FzR10AAct a b tau Ms)
    (hcl : FzR10AAct a b lam Ml) : Ms.mul Ml = Ml.mul Ms :=
  fzr_a_act_comm S.basis hMs hMl hcs hcl S.str.tau_lam

end CFSG.OddStandard.SmallF3.FritzII
