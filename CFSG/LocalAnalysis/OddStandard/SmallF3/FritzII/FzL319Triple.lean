module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL319Facts

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.GH74.GLS.Bg.TwoGroups
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {t tau lam rho : G} {Z E W Q R T P : Subgroup G}
  (D : Fz319Data t tau lam rho Z E W Q R T P)

namespace Fz319Data

private lemma fzl_conj_comm {a b : G} (hab : a * b = b * a) (x : G) :
    a * (b * x * b⁻¹) * a⁻¹ = b * (a * x * a⁻¹) * b⁻¹ := by
  have hab' : b⁻¹ * a⁻¹ = a⁻¹ * b⁻¹ := by
    have := congrArg Inv.inv hab
    simpa [mul_inv_rev] using this
  calc a * (b * x * b⁻¹) * a⁻¹
      = (a * b) * x * (b⁻¹ * a⁻¹) := by group
    _ = (b * a) * x * (a⁻¹ * b⁻¹) := by rw [hab, hab']
    _ = b * (a * x * a⁻¹) * b⁻¹ := by group

private lemma fzl_conj_sq {a : G} (ha : a * a = 1) (x : G) :
    a * (a * x * a⁻¹) * a⁻¹ = x := by
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  rw [hainv]
  calc a * (a * x * a) * a = (a * a) * x * (a * a) := by group
    _ = x := by rw [ha]; group

private lemma fzl_conj_inv_sq {a b : G} (hab : a * b * a⁻¹ = b⁻¹) (hb : b ^ 3 = 1) (x : G) :
    a * (b * x * b⁻¹) * a⁻¹ = b * (b * (a * x * a⁻¹) * b⁻¹) * b⁻¹ := by
  have hba' : a * b⁻¹ * a⁻¹ = b := by
    have h := congrArg Inv.inv hab
    rw [mul_inv_rev, mul_inv_rev, inv_inv, inv_inv] at h
    calc a * b⁻¹ * a⁻¹ = a * (b⁻¹ * a⁻¹) := by group
      _ = b := h
  have hb3 : b * b * b = 1 := by simpa [pow_succ, pow_two, mul_assoc] using hb
  have hb2 : b⁻¹ = b * b := by
    apply inv_eq_of_mul_eq_one_right
    simpa [mul_assoc] using hb3
  have hb2' : b⁻¹ * b⁻¹ = b := by
    rw [hb2]
    calc (b * b) * (b * b) = b * (b * b * b) := by group
      _ = b * 1 := by rw [hb3]
      _ = b := by rw [mul_one]
  calc a * (b * x * b⁻¹) * a⁻¹
      = (a * b * a⁻¹) * (a * x * a⁻¹) * (a * b⁻¹ * a⁻¹) := by group
    _ = b⁻¹ * (a * x * a⁻¹) * b := by rw [hab, hba']
    _ = b * (b * (a * x * a⁻¹) * b⁻¹) * b⁻¹ := by
        rw [show b * (b * (a * x * a⁻¹) * b⁻¹) * b⁻¹
              = (b * b) * (a * x * a⁻¹) * (b⁻¹ * b⁻¹) by group, hb2', hb2]

private lemma fzl_conj_t_mul {n t lam : G} (h : lam * t = t * lam) :
    lam * (t * n) * lam⁻¹ * (t * n)⁻¹ = t * (lam * n * lam⁻¹ * n⁻¹) * t⁻¹ := by
  calc lam * (t * n) * lam⁻¹ * (t * n)⁻¹
      = (lam * t) * n * lam⁻¹ * n⁻¹ * t⁻¹ := by group
    _ = (t * lam) * n * lam⁻¹ * n⁻¹ * t⁻¹ := by rw [h]
    _ = t * (lam * n * lam⁻¹ * n⁻¹) * t⁻¹ := by group

private lemma fzl_eq_of_coe {a b : FzUT}
    (h : ((D.φ.symm a : ↥P) : G) = ((D.φ.symm b : ↥P) : G)) : a = b :=
  D.φ.symm.injective (Subtype.ext h)

theorem validTriple : FzValidTriple D.cT D.cS D.cL := by
  have ht2 : t * t = 1 := by simpa [pow_two] using D.str.t_sq
  have htau2 : tau * tau = 1 := by simpa [pow_two] using D.pf.tau_sq1
  have hlam2 : lam * lam = 1 := by simpa [pow_two] using D.str.lam_sq
  have htin : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have htrho : t * rho = rho * t := by
    calc t * rho = (rho * t * rho⁻¹) * rho := by rw [D.str.rho_t]
      _ = rho * t := by group
  have httau : t * tau = tau * t := by
    calc t * tau = (tau * t * tau⁻¹) * tau := by rw [D.str.tau_t]
      _ = tau * t := by group
  have htlam : t * lam = lam * t := by
    calc t * lam = (lam * t * lam⁻¹) * lam := by rw [D.str.lam_t]
      _ = lam * t := by group
  have htlam' : lam * t = t * lam := htlam.symm
  exact
    { t_sq := by
        intro x
        apply fzl_eq_of_coe (D := D)
        rw [D.cT_coe, D.cT_coe]
        exact fzl_conj_sq ht2 (D.φ.symm x : G)
      t_rho := by
        intro x
        rw [← D.cR_apply x, ← D.cR_apply (D.cT x)]
        apply fzl_eq_of_coe (D := D)
        simp only [D.cT_coe, D.cR_coe]
        exact fzl_conj_comm htrho (D.φ.symm x : G)
      t_Z := by
        intro x
        have hpT : ((D.φ.symm x : ↥P) : G) ∈ T :=
          D.str.RT (D.str.QR (D.pf.PQ (D.φ.symm x).2))
        obtain ⟨z, hzZ, hz⟩ := D.str.T_t ((D.φ.symm x : ↥P) : G) hpT
        have hmem : ((D.φ.symm (D.cT x * x⁻¹) : ↥P) : G) ∈ Z := by
          have hcoe : ((D.φ.symm (D.cT x * x⁻¹) : ↥P) : G)
              = t * ((D.φ.symm x : ↥P) : G) * t⁻¹ * ((D.φ.symm x : ↥P) : G)⁻¹ := by
            simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, D.cT_coe]
          rw [hcoe, htin]
          have hz' : t * ((D.φ.symm x : ↥P) : G) * t * ((D.φ.symm x : ↥P) : G)⁻¹ = z := by
            calc t * ((D.φ.symm x : ↥P) : G) * t * ((D.φ.symm x : ↥P) : G)⁻¹
                = t * (((D.φ.symm x : ↥P) : G) * t * ((D.φ.symm x : ↥P) : G)⁻¹) := by
                  group
              _ = t * (t * z) := by rw [hz]
              _ = z := by rw [← mul_assoc, ht2, one_mul]
          rw [hz']; exact hzZ
        have hZ := (D.Z_iff (D.φ.symm (D.cT x * x⁻¹))).mp hmem
        simpa only [MulEquiv.apply_symm_apply] using hZ
      t_fix := by
        let e : {x : FzUT // D.cT x = x} ≃ ↥E :=
          { toFun := fun x =>
              ⟨((D.φ.symm x.1 : ↥P) : G),
                (D.E_iff (D.φ.symm x.1)).mpr (by simpa using x.2)⟩
            invFun := fun e =>
              ⟨D.φ ⟨(e : G), D.pf.EP e.2⟩,
                (D.E_iff ⟨(e : G), D.pf.EP e.2⟩).mp e.2⟩
            left_inv := by
              intro x
              apply Subtype.ext
              simp
            right_inv := by
              intro e
              apply Subtype.ext
              simp }
        calc (Finset.univ.filter fun x : FzUT => D.cT x = x).card
            = Fintype.card {x : FzUT // D.cT x = x} := (Fintype.card_subtype _).symm
          _ = Nat.card {x : FzUT // D.cT x = x} := (Nat.card_eq_fintype_card).symm
          _ = Nat.card ↥E := Nat.card_congr e
          _ = 16 := D.str.card_E
      s_sq := by
        intro x
        apply fzl_eq_of_coe (D := D)
        rw [D.cS_coe, D.cS_coe]
        exact fzl_conj_sq htau2 (D.φ.symm x : G)
      s_rho := by
        intro x
        rw [← D.cR_apply x, ← D.cR_apply (D.cS x)]
        apply fzl_eq_of_coe (D := D)
        simp only [D.cS_coe, D.cR_coe]
        exact fzl_conj_comm D.str.tau_rho (D.φ.symm x : G)
      s_ne := by
        have hex : ∃ e : G, e ∈ E ∧ e ≠ e⁻¹ := by
          by_contra h
          push Not at h
          have hEZ : E ≤ Z := by
            intro e he
            have he2 : e ^ 2 = 1 := by
              rw [pow_two]
              nth_rewrite 2 [h e he]
              exact mul_inv_cancel e
            exact D.str.E_invol e he he2
          have hle : Nat.card ↥E ≤ Nat.card ↥Z := Subgroup.card_le_of_le hEZ
          rw [D.str.card_E, D.str.card_Z] at hle
          omega
        obtain ⟨e, heE, hne⟩ := hex
        refine ⟨D.φ ⟨e, D.pf.EP heE⟩, ?_⟩
        intro hfix
        have h := D.cS_coe (D.φ ⟨e, D.pf.EP heE⟩)
        rw [hfix] at h
        have h1 : e = tau * e * tau⁻¹ := by simpa using h
        exact hne (h1.trans (D.str.tau_W e (D.str.EW heE)))
      ts := by
        intro x
        apply fzl_eq_of_coe (D := D)
        simp only [D.cT_coe, D.cS_coe]
        exact fzl_conj_comm httau (D.φ.symm x : G)
      s_inv := by
        intro x hx
        apply fzl_eq_of_coe (D := D)
        have hpE : ((D.φ.symm x : ↥P) : G) ∈ E :=
          (D.E_iff (D.φ.symm x)).mpr (by simpa using hx)
        have htau := D.str.tau_W ((D.φ.symm x : ↥P) : G) (D.str.EW hpE)
        simp only [map_inv, Subgroup.coe_inv, D.cS_coe]
        rw [htau]
      s_fix := by
        intro x
        set c : G := tau * ((D.φ.symm x : ↥P) : G) * tau⁻¹ * ((D.φ.symm x : ↥P) : G)⁻¹
          with hc
        have hcP : c ∈ P := by
          rw [hc]
          exact P.mul_mem (D.pf.nrm_P tau D.tau_mem (D.φ.symm x) (D.φ.symm x).2)
            (P.inv_mem (D.φ.symm x).2)
        have hcW : c ∈ W := by
          rw [hc]
          simpa [commutatorElement_def] using
            D.str.tau_Q ((D.φ.symm x : ↥P) : G) (D.pf.PQ (D.φ.symm x).2)
        have hcE : c ∈ E := D.pf.PW c hcP hcW
        have hphi : D.φ ⟨c, hcP⟩ = D.cS x * x⁻¹ := by
          apply D.φ.symm.injective
          apply Subtype.ext
          rw [MulEquiv.symm_apply_apply]
          simp only [Subgroup.coe_mk, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
          rw [D.cS_coe]
        have h := (D.E_iff ⟨c, hcP⟩).mp hcE
        rw [hphi] at h
        exact h
      l_sq := by
        intro x
        apply fzl_eq_of_coe (D := D)
        rw [D.cL_coe, D.cL_coe]
        exact fzl_conj_sq hlam2 (D.φ.symm x : G)
      l_rho := by
        intro x
        rw [← D.cR_apply x, ← D.cR_apply (fzRho0 (D.cL x)), ← D.cR_apply (D.cL x)]
        apply fzl_eq_of_coe (D := D)
        simp only [D.cL_coe, D.cR_coe]
        exact fzl_conj_inv_sq D.str.lam_rho D.str.rho_ord (D.φ.symm x : G)
      tl := by
        intro x
        apply fzl_eq_of_coe (D := D)
        simp only [D.cT_coe, D.cL_coe]
        exact fzl_conj_comm htlam (D.φ.symm x : G)
      sl := by
        intro x
        apply fzl_eq_of_coe (D := D)
        simp only [D.cS_coe, D.cL_coe]
        exact fzl_conj_comm D.str.tau_lam (D.φ.symm x : G)
      l_Z := by
        obtain ⟨z, hzZ, hz_ne⟩ := D.str.lam_Z
        have hzP : z ∈ P := D.pf.EP (D.str.ZE hzZ)
        refine ⟨D.φ ⟨z, hzP⟩, (D.Z_iff ⟨z, hzP⟩).mp hzZ, ?_⟩
        intro hfix
        have h := D.cL_coe (D.φ ⟨z, hzP⟩)
        rw [hfix] at h
        exact hz_ne (by simpa using h.symm)
      l_Q := by
        obtain ⟨n, hnQ, hnW⟩ := D.str.lam_Q
        rcases D.pf.Q_eq n hnQ with hnP | htnP
        · refine ⟨D.φ ⟨n, hnP⟩, ?_⟩
          intro hfix
          have hmem : ((D.φ.symm (D.cL (D.φ ⟨n, hnP⟩) * (D.φ ⟨n, hnP⟩)⁻¹) : ↥P) : G) ∈ E :=
            (D.E_iff (D.φ.symm (D.cL (D.φ ⟨n, hnP⟩) * (D.φ ⟨n, hnP⟩)⁻¹))).mpr
              (by simpa only [MulEquiv.apply_symm_apply] using hfix)
          have heq : ((D.φ.symm (D.cL (D.φ ⟨n, hnP⟩) * (D.φ ⟨n, hnP⟩)⁻¹) : ↥P) : G)
              = lam * n * lam⁻¹ * n⁻¹ := by
            simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, D.cL_coe,
              MulEquiv.symm_apply_apply, Subgroup.coe_mk]
          rw [heq] at hmem
          exact hnW (by simpa [commutatorElement_def] using D.str.EW hmem)
        · refine ⟨D.φ ⟨t * n, htnP⟩, ?_⟩
          intro hfix
          have hmem :
              ((D.φ.symm (D.cL (D.φ ⟨t * n, htnP⟩) * (D.φ ⟨t * n, htnP⟩)⁻¹) : ↥P) : G) ∈ E :=
            (D.E_iff (D.φ.symm (D.cL (D.φ ⟨t * n, htnP⟩) * (D.φ ⟨t * n, htnP⟩)⁻¹))).mpr
              (by simpa only [MulEquiv.apply_symm_apply] using hfix)
          have heq : ((D.φ.symm (D.cL (D.φ ⟨t * n, htnP⟩) * (D.φ ⟨t * n, htnP⟩)⁻¹) : ↥P) : G)
              = t * (lam * n * lam⁻¹ * n⁻¹) * t⁻¹ := by
            simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, D.cL_coe,
              MulEquiv.symm_apply_apply, Subgroup.coe_mk]
            exact fzl_conj_t_mul htlam'
          rw [heq] at hmem
          have hcW : t * (lam * n * lam⁻¹ * n⁻¹) * t⁻¹ ∈ W := D.str.EW hmem
          have hc : lam * n * lam⁻¹ * n⁻¹ ∈ W := by
            have h := W.mul_mem (W.mul_mem (W.inv_mem D.str.t_mem) hcW) D.str.t_mem
            rwa [show t⁻¹ * (t * (lam * n * lam⁻¹ * n⁻¹) * t⁻¹) * t
                  = lam * n * lam⁻¹ * n⁻¹ by group] at h
          exact hnW (by simpa [commutatorElement_def] using hc) }

end Fz319Data

end CFSG.OddStandard.SmallF3.FritzII
