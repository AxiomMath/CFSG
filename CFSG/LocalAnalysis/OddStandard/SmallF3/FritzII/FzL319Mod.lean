module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL319Conj

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.GH74.GLS.Bg.TwoGroups CFSG.GH74.GLS.Bg.TwoGroups.L23
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {t tau lam rho : G} {Z E W Q R T P : Subgroup G}
  (D : Fz319Data t tau lam rho Z E W Q R T P)

namespace Fz319Data

@[expose] noncomputable def mu (x : FzElt) : G :=
  (D.φ.symm x.1 : G) * t ^ x.2.1.val * tau ^ x.2.2.1.val * lam ^ x.2.2.2.val

private noncomputable def fzlM (t tau lam : G) (v : FzV) : G :=
  t ^ v.1.val * tau ^ v.2.1.val * lam ^ v.2.2.val

private lemma fzlV_add_self (v : FzV) : v + v = 0 := by
  have hall : ∀ a : ZMod 2, a + a = 0 := by decide
  exact Prod.ext (hall v.1) (Prod.ext (hall v.2.1) (hall v.2.2))

private lemma fzlM_zero (t tau lam : G) : fzlM t tau lam 0 = 1 := by
  simp [fzlM, ZMod.val_zero]

private lemma fzl_pow_add (s : G) (hs : s ^ 2 = 1) (a b : ZMod 2) :
    s ^ (a + b).val = s ^ a.val * s ^ b.val := by
  have h01 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases h01 a with ha | ha <;> rcases h01 b with hb | hb
  all_goals
    subst ha; subst hb
    simp [ZMod.val_add, ZMod.val_zero, ZMod.val_one, ← pow_two, hs]

private lemma fzl_three {a b c : G} (hab : a * b = b * a) (hac : a * c = c * a)
    (hbc : b * c = c * b) (p q r p' q' r' : ℕ) :
    a ^ p * b ^ q * c ^ r * (a ^ p' * b ^ q' * c ^ r') =
      a ^ (p + p') * b ^ (q + q') * c ^ (r + r') := by
  have hab' : Commute a b := hab
  have hac' : Commute a c := hac
  have hbc' : Commute b c := hbc
  have hca : c ^ r * a ^ p' = a ^ p' * c ^ r := ((hac'.symm.pow_left r).pow_right p').eq
  have hcb : c ^ r * b ^ q' = b ^ q' * c ^ r := ((hbc'.symm.pow_left r).pow_right q').eq
  have hba : b ^ q * a ^ p' = a ^ p' * b ^ q := ((hab'.symm.pow_left q).pow_right p').eq
  calc
    a ^ p * b ^ q * c ^ r * (a ^ p' * b ^ q' * c ^ r')
        = a ^ p * b ^ q * (c ^ r * a ^ p') * b ^ q' * c ^ r' := by group
    _ = a ^ p * b ^ q * (a ^ p' * c ^ r) * b ^ q' * c ^ r' := by rw [hca]
    _ = a ^ p * b ^ q * a ^ p' * c ^ r * b ^ q' * c ^ r' := by group
    _ = a ^ p * b ^ q * a ^ p' * (c ^ r * b ^ q') * c ^ r' := by group
    _ = a ^ p * b ^ q * a ^ p' * (b ^ q' * c ^ r) * c ^ r' := by rw [hcb]
    _ = a ^ p * (b ^ q * a ^ p') * b ^ q' * c ^ r * c ^ r' := by group
    _ = a ^ p * (a ^ p' * b ^ q) * b ^ q' * c ^ r * c ^ r' := by rw [hba]
    _ = a ^ p * a ^ p' * (b ^ q * b ^ q') * (c ^ r * c ^ r') := by group
    _ = a ^ (p + p') * b ^ (q + q') * c ^ (r + r') := by
      rw [← pow_add a p p', ← pow_add b q q', ← pow_add c r r']

private lemma fzlM_add_aux (t tau lam : G) (ht : t ^ 2 = 1) (htau : tau ^ 2 = 1)
    (hlam : lam ^ 2 = 1) (httau : tau * t = t * tau) (htlam : lam * t = t * lam)
    (htaulam : lam * tau = tau * lam) (v w : FzV) :
    fzlM t tau lam (v + w) = fzlM t tau lam v * fzlM t tau lam w := by
  unfold fzlM
  simp only [Prod.fst_add, Prod.snd_add]
  rw [fzl_three (a := t) (b := tau) (c := lam) httau.symm htlam.symm htaulam.symm
      v.1.val v.2.1.val v.2.2.val w.1.val w.2.1.val w.2.2.val]
  rw [fzl_pow_add t ht v.1 w.1, fzl_pow_add tau htau v.2.1 w.2.1,
      fzl_pow_add lam hlam v.2.2 w.2.2]
  rw [← pow_add t v.1.val w.1.val, ← pow_add tau v.2.1.val w.2.1.val,
      ← pow_add lam v.2.2.val w.2.2.val]

include D

private lemma fzl_tau_comm : tau * t = t * tau := by
  calc tau * t = tau * t * tau⁻¹ * tau := by group
    _ = t * tau := by rw [D.str.tau_t]

private lemma fzl_lam_comm_t : lam * t = t * lam := by
  calc lam * t = lam * t * lam⁻¹ * lam := by group
    _ = t * lam := by rw [D.str.lam_t]

private lemma fzlM_add (v w : FzV) :
    fzlM t tau lam (v + w) = fzlM t tau lam v * fzlM t tau lam w :=
  fzlM_add_aux t tau lam D.str.t_sq D.pf.tau_sq1 D.str.lam_sq (fzl_tau_comm D)
    (fzl_lam_comm_t D) D.str.tau_lam.symm v w

private lemma fzlM_sq (v : FzV) : fzlM t tau lam v * fzlM t tau lam v = 1 := by
  rw [← fzlM_add D v v, fzlV_add_self v, fzlM_zero]

private lemma fzlM_inv (v : FzV) : (fzlM t tau lam v)⁻¹ = fzlM t tau lam v :=
  inv_eq_of_mul_eq_one_right (fzlM_sq D v)

private lemma fzl_symm_mul (a b : FzUT) :
    ((D.φ.symm (a * b) : ↥P) : G)
      = ((D.φ.symm a : ↥P) : G) * ((D.φ.symm b : ↥P) : G) := by
  rw [map_mul]
  rfl

private lemma fzl_ap_conj (b : ZMod 2) (σ : MulAut FzUT) (s : G)
    (hσ : ∀ q, ((D.φ.symm (σ q) : ↥P) : G) = s * ((D.φ.symm q : ↥P) : G) * s⁻¹)
    (q : FzUT) :
    ((D.φ.symm (fzAp b σ q) : ↥P) : G)
      = s ^ b.val * ((D.φ.symm q : ↥P) : G) * (s ^ b.val)⁻¹ := by
  have h01 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  have h10 : (1 : ZMod 2) ≠ 0 := by decide
  rcases h01 b with hb | hb
  · subst hb; simp [fzAp, ZMod.val_zero]
  · subst hb
    rw [fzAp, if_neg h10, ZMod.val_one 2, pow_one]
    exact hσ q

private lemma fzl_act_conj (v : FzV) (q : FzUT) :
    ((D.φ.symm (fzAct D.cT D.cS D.cL v q) : ↥P) : G)
      = fzlM t tau lam v * ((D.φ.symm q : ↥P) : G) * (fzlM t tau lam v)⁻¹ := by
  have h3 := fzl_ap_conj D v.1 D.cT t D.cT_coe (fzAp v.2.1 D.cS (fzAp v.2.2 D.cL q))
  have h2 := fzl_ap_conj D v.2.1 D.cS tau D.cS_coe (fzAp v.2.2 D.cL q)
  have h1 := fzl_ap_conj D v.2.2 D.cL lam D.cL_coe q
  simp only [fzAct]
  rw [h3, h2, h1]
  unfold fzlM
  group

private lemma fzl_mu_eq (x : FzElt) :
    D.mu x = ((D.φ.symm x.1 : ↥P) : G) * fzlM t tau lam x.2 := by
  unfold mu fzlM
  group

private lemma fzlM_mem_P_zero (u : FzV) (hu : fzlM t tau lam u ∈ P) : u = 0 := by
  have h01 : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  have hPR : P ≤ R := D.pf.PQ.trans D.str.QR
  have htR : t ∈ R := D.str.QR (D.str.WQ D.str.t_mem)
  have htauR : tau ∈ R := D.str.tau_R
  have htQ : t ∈ Q := D.str.WQ D.str.t_mem
  by_cases h2 : u.2.2 = 1
  · have haR : t ^ u.1.val * tau ^ u.2.1.val ∈ R :=
      R.mul_mem (R.pow_mem htR _) (R.pow_mem htauR _)
    have hEq : fzlM t tau lam u = (t ^ u.1.val * tau ^ u.2.1.val) * lam := by
      simp only [fzlM, h2, ZMod.val_one 2, pow_one]
    have hmem : (t ^ u.1.val * tau ^ u.2.1.val)⁻¹ * fzlM t tau lam u ∈ R :=
      R.mul_mem (R.inv_mem haR) (hPR hu)
    rw [hEq] at hmem
    have hlamR : lam ∈ R := by
      have hc : (t ^ u.1.val * tau ^ u.2.1.val)⁻¹
          * ((t ^ u.1.val * tau ^ u.2.1.val) * lam) = lam := by group
      rwa [hc] at hmem
    obtain ⟨z, hzZ, hz⟩ := D.str.lam_Z
    exact (hz (D.str.R_Z lam hlamR z hzZ)).elim
  · have h2' : u.2.2 = 0 := by
      rcases h01 u.2.2 with h | h
      · exact h
      · exact (h2 h).elim
    by_cases h1 : u.2.1 = 1
    · have hEq : fzlM t tau lam u = t ^ u.1.val * tau := by
        simp only [fzlM, h1, h2', ZMod.val_one 2, ZMod.val_zero, pow_one, pow_zero, mul_one]
      have hmem : (t ^ u.1.val)⁻¹ * fzlM t tau lam u ∈ Q :=
        Q.mul_mem (Q.inv_mem (Q.pow_mem htQ _)) (D.pf.PQ hu)
      rw [hEq] at hmem
      have htauQ : tau ∈ Q := by
        have hc : (t ^ u.1.val)⁻¹ * (t ^ u.1.val * tau) = tau := by group
        rwa [hc] at hmem
      exact (D.str.tau_notin_Q htauQ).elim
    · have h1' : u.2.1 = 0 := by
        rcases h01 u.2.1 with h | h
        · exact h
        · exact (h1 h).elim
      by_cases h0 : u.1 = 1
      · have hEq : fzlM t tau lam u = t := by
          simp only [fzlM, h0, h1', h2', ZMod.val_one 2, ZMod.val_zero, pow_one, pow_zero,
            mul_one]
        have htP : t ∈ P := by rwa [hEq] at hu
        exact (D.str.t_notin_E (D.pf.PW t htP D.str.t_mem)).elim
      · have h0' : u.1 = 0 := by
          rcases h01 u.1 with h | h
          · exact h
          · exact (h0 h).elim
        exact Prod.ext h0' (Prod.ext h1' h2')

theorem mu_mul (x y : FzElt) : D.mu (fzMulC D.cT D.cS D.cL x y) = D.mu x * D.mu y := by
  rw [fzl_mu_eq D (x := fzMulC D.cT D.cS D.cL x y), fzl_mu_eq D (x := x),
    fzl_mu_eq D (x := y)]
  simp only [fzMulC]
  rw [fzl_symm_mul D, fzl_act_conj D, fzlM_add D]
  group

theorem mu_one : D.mu fzOneC = 1 := by
  rw [fzl_mu_eq D]
  simp [fzOneC, fzlM_zero]

theorem mu_mem (x : FzElt) : D.mu x ∈ T := by
  rw [fzl_mu_eq D]
  unfold fzlM
  refine T.mul_mem ?_ (T.mul_mem (T.mul_mem (T.pow_mem D.t_mem _) (T.pow_mem D.tau_mem _))
    (T.pow_mem D.lam_mem _))
  exact (D.pf.PQ.trans (D.str.QR.trans D.str.RT)) (D.φ.symm x.1).2

theorem mu_injective : Function.Injective D.mu := by
  intro x y h
  rw [fzl_mu_eq D (x := x), fzl_mu_eq D (x := y)] at h
  have hkey : ((D.φ.symm y.1 : ↥P) : G)⁻¹ * ((D.φ.symm x.1 : ↥P) : G)
      = fzlM t tau lam (y.2 + x.2) := by
    calc ((D.φ.symm y.1 : ↥P) : G)⁻¹ * ((D.φ.symm x.1 : ↥P) : G)
        = ((D.φ.symm y.1 : ↥P) : G)⁻¹
            * (((D.φ.symm x.1 : ↥P) : G) * fzlM t tau lam x.2)
            * (fzlM t tau lam x.2)⁻¹ := by group
      _ = ((D.φ.symm y.1 : ↥P) : G)⁻¹
            * (((D.φ.symm y.1 : ↥P) : G) * fzlM t tau lam y.2)
            * (fzlM t tau lam x.2)⁻¹ := by rw [h]
      _ = fzlM t tau lam y.2 * (fzlM t tau lam x.2)⁻¹ := by group
      _ = fzlM t tau lam y.2 * fzlM t tau lam x.2 := by rw [fzlM_inv D]
      _ = fzlM t tau lam (y.2 + x.2) := by rw [fzlM_add D]
  have hm : fzlM t tau lam (y.2 + x.2) ∈ P := by
    rw [← hkey]
    exact P.mul_mem (P.inv_mem (D.φ.symm y.1).2) (D.φ.symm x.1).2
  have huv : y.2 + x.2 = 0 := fzlM_mem_P_zero D (y.2 + x.2) hm
  have hx2 : x.2 = y.2 := by
    have hyy : y.2 + y.2 = 0 := fzlV_add_self y.2
    calc x.2 = x.2 + 0 := (add_zero _).symm
      _ = x.2 + (y.2 + y.2) := by rw [← hyy]
      _ = (x.2 + y.2) + y.2 := by abel
      _ = (y.2 + x.2) + y.2 := by rw [add_comm x.2 y.2]
      _ = 0 + y.2 := by rw [huv]
      _ = y.2 := zero_add _
  have hx1 : x.1 = y.1 := by
    have h2 := h
    rw [hx2] at h2
    have hA : ((D.φ.symm x.1 : ↥P) : G) = ((D.φ.symm y.1 : ↥P) : G) :=
      mul_right_cancel h2
    have hsub : (D.φ.symm x.1 : ↥P) = (D.φ.symm y.1 : ↥P) := Subtype.ext hA
    exact D.φ.symm.injective hsub
  exact Prod.ext hx1 hx2

theorem mu_surj {g : G} (hg : g ∈ T) : ∃ x : FzElt, D.mu x = g := by
  let f : FzElt → ↥T := fun x => ⟨D.mu x, D.mu_mem x⟩
  have hf : Function.Injective f := by
    intro x y hxy
    exact D.mu_injective (Subtype.ext_iff.mp hxy)
  have hcardV : Nat.card FzV = 8 := by
    show Nat.card (ZMod 2 × (ZMod 2 × ZMod 2)) = 8
    simp only [Nat.card_prod, Nat.card_zmod]
  have hcardUT : Nat.card FzUT = 64 := card_UT3c
  have hcardE : Nat.card FzElt = 512 := by
    show Nat.card (FzUT × FzV) = 512
    rw [Nat.card_prod, hcardUT, hcardV]
  have hcard : Nat.card ↥T ≤ Nat.card FzElt := by
    rw [D.str.card_T, hcardE]
  have hbij := hf.bijective_of_nat_card_le hcard
  obtain ⟨x, hx⟩ := hbij.2 ⟨g, hg⟩
  exact ⟨x, Subtype.ext_iff.mp hx⟩

end Fz319Data

end CFSG.OddStandard.SmallF3.FritzII
