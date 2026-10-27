module

public import CFSG.LocalAnalysis.ComponentClassification.J2CoverModelsRigid

public section

namespace CFSG.ComponentClassification.J2Cover

open Models

theorem qte_j2_sylow_coset_action_validity :
    S ≤ P ∧ Nat.card S = 128 ∧ (∃ Q : Sylow 2 P, (Q : Subgroup P) = S.subgroupOf P) ∧
    Function.Bijective (fun k : Fin 128 => elt k) ∧ elt 0 = 1 ∧ rep 0 = 1 ∧
    (∀ i, rep i ∈ P) ∧ Function.Bijective tv ∧ Function.Bijective cosetMk ∧
    (∀ (i : Fin 4725) (j : ℕ), j < 2 → actT j i < 4725 ∧ witT j i < 128 ∧
      rep i * letter j = (elt (witT j i) : Perm315) * rep (actT j i) ∧
      (cosetAct i (letterP j) : ℕ) = actT j i) ∧
    ∀ j : ℕ, j < 2 → Function.Bijective fun i : Fin 4725 => cosetAct i (letterP j) := by
  refine ⟨S_le_P, card_S, exists_sylow_eq_S, eltEquiv.bijective, elt_zero, rep_zero, rep_mem,
    tv_bijective, cosetMk_bijective, fun i j hj => ?_,
    fun j _ => (cosetPerm (letterP j)).bijective⟩
  obtain ⟨h1, h2, h3⟩ := rep_mul_letter i.isLt hj
  exact ⟨h1, h2, h3, (cosetAct_letter i hj).1⟩

theorem ctss_j2_sylow_tables :
    Function.Bijective (fun k : Fin 128 => elt k) ∧ elt 0 = 1 ∧ Nat.card S = 128 ∧
    (∀ a d : ℕ, d < 128 → mulIdx a d < 128 ∧ elt a * elt d = elt (mulIdx a d)) ∧
    Function.Bijective tv ∧
    (∀ (i : Fin 4725) (g : P),
      rep i * (g : Perm315) = (factor i g : Perm315) * rep (cosetAct i g)) ∧
    (∀ (i : Fin 4725) (g h : P), cosetAct i (g * h) = cosetAct (cosetAct i g) h ∧
      factor i (g * h) = factor i g * factor (cosetAct i g) h) :=
  ⟨eltEquiv.bijective, elt_zero, card_S,
    fun _ _ hd => ⟨(mulIdx_spec hd).1, (mulIdx_spec hd).2.symm⟩,
    tv_bijective, rep_mul_eq, fun i g h => ⟨cosetAct_mul i g h, factor_mul i g h⟩⟩

theorem ctss_j2_cohomology_basis :
    (∀ j < 6, IsNormCocycle (hCoc j)) ∧
    (∀ g : S → S → ZMod 2, IsNormCocycle g →
      ∃ (b : S → ZMod 2) (ε : Fin 6 → ZMod 2), ∀ s t, g s t = cob b s t + ∑ j, ε j * hCoc j s t) ∧
    ∀ (ε : Fin 6 → ZMod 2) (b : S → ZMod 2), (∀ s t, ∑ j, ε j * hCoc j s t = cob b s t) → ε = 0 :=
  ⟨fun _ hj => isNormCocycle_hCoc hj, exists_eq_cob_add_sum, eq_zero_of_sum_eq_cob⟩

theorem ctss_j2_transfer_image :
    (∀ h : S → S → ZMod 2, IsNormCocycle h → IsNormCocycle (transfer h)) ∧
    (∀ j < 6, ∀ s t : S,
      transfer (hCoc j) (incl s) (incl t) = eFlag j * fCoc s t + cob (bCoch j) s t) ∧
    (eFlag 0 = 1 ∧ eFlag 1 = 0 ∧ eFlag 2 = 0 ∧ eFlag 3 = 0 ∧ eFlag 4 = 0 ∧ eFlag 5 = 0) ∧
    (∀ s t : S, transfer (hCoc 0) (incl s) (incl t) = fCoc s t) ∧ IsNormCocycle fCoc ∧
    (¬ ∃ b : S → ZMod 2, ∀ s t, fCoc s t = cob b s t) ∧
    ∀ s t : S, transfer fCoc (incl s) (incl t) + cob muCoch s t = fCoc s t :=
  ⟨fun _ hh => isNormCocycle_transfer hh, fun _ hj => transfer_hCoc hj,
    ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩, transfer_hCoc_zero,
    isNormCocycle_fCoc, fCoc_not_cob, transfer_fCoc⟩

theorem ctss_j2_involutions :
    (∀ x : P, orderOf x = 2 → fixCount (x : Perm315) = 11 ∨ fixCount (x : Perm315) = 15) ∧
    (∀ x y : P, orderOf x = 2 → orderOf y = 2 →
      fixCount (x : Perm315) = fixCount (y : Perm315) → ∃ g : P, g * x * g⁻¹ = y) ∧
    (∀ s : S, orderOf s = 2 → (fixCount (s : Perm315) = 11 ∧ fCoc s s = 0) ∨
      (fixCount (s : Perm315) = 15 ∧ fCoc s s = 1)) ∧
    orderOf (elt 4) = 2 ∧ fixCount (elt 4 : Perm315) = 11 ∧ orderOf (elt 2) = 2 ∧
      fixCount (elt 2 : Perm315) = 15 :=
  ⟨involution_fixCount, fun _ _ hx hy h => involution_conj hx hy h, fCoc_diag, orderOf_elt_four,
    fixCount_elt_four, orderOf_elt_two, fixCount_elt_two⟩

theorem ctss_j2_outer_involution :
    bOut = gB * uOut * gB⁻¹ ∧ bOut * bOut = 1 ∧ bOut ∉ P ∧
    (∀ g ∈ P, bOut * g * bOut⁻¹ ∈ P) ∧ (∀ s ∈ S, bOut * s * bOut⁻¹ ∈ S) ∧
    (∀ a : ℕ, a < 128 → betaIdx a < 128 ∧ bOut * (elt a : Perm315) * bOut⁻¹ = elt (betaIdx a)) ∧
    ∀ i : Fin 4725, bOut * rep i * bOut⁻¹ = (aElt i : Perm315) * rep (sigmaIdx i) :=
  ⟨bOut_eq, bOut_mul_self, bOut_not_mem, fun _ hg => bOut_conj_mem hg,
    fun _ hs => bOut_conj_mem_S hs, fun _ ha => ⟨betaIdx_lt ha, bOut_conj_elt ha⟩,
    fun i => bOut_conj_rep i.isLt⟩

theorem ctss_j2_tau :
    (∀ s t : S, fCoc s t + fCoc (betaS s) (betaS t) = cob lamCoch s t) ∧
    (∀ x : Rf, (tauR x).e = x.e + lamCoch x.g ∧ (tauR x).g = betaS x.g) ∧
    tauR CocExt.central = CocExt.central ∧ (∀ x : Rf, tauR (tauR x) = x) ∧
    (∀ x : Rf, CocExt.central * x = x * CocExt.central) ∧
    (∀ (i : Fin 4725) (g : P), (cMul i g).g = factor (sigmaIdx i) (betaP g) ∧
      cosetAct (sigmaIdx i) (betaP g) = sigmaIdx (cosetAct i g)) ∧
    ∀ s : S, lamCoch s = bigLam (incl s) + muCoch s + muCoch (betaS s) :=
  ⟨cob_lamCoch, fun _ => ⟨tauR_e _, tauR_g _⟩, tauR_central, tauR_tauR, CocExt.central_mul,
    cMul_snd, lamCoch_eq⟩

theorem ctss_j2_rigid_models :
    Nat.card Rf = 256 ∧ Nat.card T0 = 512 ∧ Nat.card T1 = 512 ∧
    (∀ x : Rf, x ∈ Subgroup.center Rf ↔
      x = 1 ∨ x = zR ∨ x = CocExt.central ∨ x = zR * CocExt.central) ∧
    (∀ p : T0, p ∈ Subgroup.center T0 ↔ p = 1 ∨ p = zT 0 ∨ p = tT 0 ∨ p = zT 0 * tT 0) ∧
    (∀ p : T1, p ∈ Subgroup.center T1 ↔ p = 1 ∨ p = zT 1 ∨ p = tT 1 ∨ p = zT 1 * tT 1) ∧
    (Nat.card (Subgroup.center Rf) = 4 ∧ ∀ x ∈ Subgroup.center Rf, x ^ 2 = 1) ∧
    (Nat.card (Subgroup.center T0) = 4 ∧ ∀ p ∈ Subgroup.center T0, p ^ 2 = 1) ∧
    (Nat.card (Subgroup.center T1) = 4 ∧ ∀ p ∈ Subgroup.center T1, p ^ 2 = 1) ∧
    (rootPair zR = (0, 0) ∧ rootPair (CocExt.central : Rf) = (48, 0) ∧
      rootPair (zR * CocExt.central) = (40, 96)) ∧
    (rootPair (zT 0) = (0, 0) ∧ rootPair (tT 0) = (48, 64) ∧ rootPair (zT 0 * tT 0) = (56, 160)) ∧
    (rootPair (zT 1) = (16, 0) ∧ rootPair (tT 1) = (96, 64) ∧ rootPair (zT 1 * tT 1) = (40, 160)) ∧
    (∀ φ : Rf ≃* Rf, ∀ x ∈ Subgroup.center Rf, φ x = x) ∧
    (∀ φ : T0 ≃* T0, ∀ x ∈ Subgroup.center T0, φ x = x) ∧
    ∀ φ : T1 ≃* T1, ∀ x ∈ Subgroup.center T1, φ x = x :=
  ⟨card_Rf, card_Teps 0, card_Teps 1, mem_center_Rf, mem_center_T0, mem_center_T1,
    ⟨card_center_Rf, center_Rf_sq⟩, ⟨card_center_T0, center_T0_sq⟩, ⟨card_center_T1, center_T1_sq⟩,
    rootPair_Rf, rootPair_T0, rootPair_T1, aut_fix_center_Rf, aut_fix_center_T0,
    aut_fix_center_T1⟩

theorem ctss_j2_native_sylow_transfer_image_and_rigid_models :
    (Function.Bijective (fun k : Fin 128 => elt k) ∧ elt 0 = 1 ∧ Nat.card S = 128 ∧
      (∀ a d : ℕ, d < 128 → mulIdx a d < 128 ∧ elt a * elt d = elt (mulIdx a d)) ∧
      Function.Bijective tv ∧
      (∀ (i : Fin 4725) (g : P),
        rep i * (g : Perm315) = (factor i g : Perm315) * rep (cosetAct i g)) ∧
      (∀ (i : Fin 4725) (g h : P), cosetAct i (g * h) = cosetAct (cosetAct i g) h ∧
        factor i (g * h) = factor i g * factor (cosetAct i g) h)) ∧
    ((∀ j < 6, IsNormCocycle (hCoc j)) ∧
      (∀ g : S → S → ZMod 2, IsNormCocycle g → ∃ (b : S → ZMod 2) (ε : Fin 6 → ZMod 2),
        ∀ s t, g s t = cob b s t + ∑ j, ε j * hCoc j s t) ∧
      ∀ (ε : Fin 6 → ZMod 2) (b : S → ZMod 2),
        (∀ s t, ∑ j, ε j * hCoc j s t = cob b s t) → ε = 0) ∧
    ((∀ h : S → S → ZMod 2, IsNormCocycle h → IsNormCocycle (transfer h)) ∧
      (∀ j < 6, ∀ s t : S,
        transfer (hCoc j) (incl s) (incl t) = eFlag j * fCoc s t + cob (bCoch j) s t) ∧
      (eFlag 0 = 1 ∧ eFlag 1 = 0 ∧ eFlag 2 = 0 ∧ eFlag 3 = 0 ∧ eFlag 4 = 0 ∧ eFlag 5 = 0) ∧
      (∀ s t : S, transfer (hCoc 0) (incl s) (incl t) = fCoc s t) ∧ IsNormCocycle fCoc ∧
      (¬ ∃ b : S → ZMod 2, ∀ s t, fCoc s t = cob b s t) ∧
      ∀ s t : S, transfer fCoc (incl s) (incl t) + cob muCoch s t = fCoc s t) ∧
    ((∀ x : P, orderOf x = 2 → fixCount (x : Perm315) = 11 ∨ fixCount (x : Perm315) = 15) ∧
      (∀ x y : P, orderOf x = 2 → orderOf y = 2 →
        fixCount (x : Perm315) = fixCount (y : Perm315) → ∃ g : P, g * x * g⁻¹ = y) ∧
      (∀ s : S, orderOf s = 2 → (fixCount (s : Perm315) = 11 ∧ fCoc s s = 0) ∨
        (fixCount (s : Perm315) = 15 ∧ fCoc s s = 1)) ∧
      orderOf (elt 4) = 2 ∧ fixCount (elt 4 : Perm315) = 11 ∧ orderOf (elt 2) = 2 ∧
        fixCount (elt 2 : Perm315) = 15) ∧
    (bOut = gB * uOut * gB⁻¹ ∧ bOut * bOut = 1 ∧ bOut ∉ P ∧
      (∀ g ∈ P, bOut * g * bOut⁻¹ ∈ P) ∧ (∀ s ∈ S, bOut * s * bOut⁻¹ ∈ S) ∧
      (∀ a : ℕ, a < 128 → betaIdx a < 128 ∧
        bOut * (elt a : Perm315) * bOut⁻¹ = elt (betaIdx a)) ∧
      ∀ i : Fin 4725, bOut * rep i * bOut⁻¹ = (aElt i : Perm315) * rep (sigmaIdx i)) ∧
    ((∀ s t : S, fCoc s t + fCoc (betaS s) (betaS t) = cob lamCoch s t) ∧
      (∀ x : Rf, (tauR x).e = x.e + lamCoch x.g ∧ (tauR x).g = betaS x.g) ∧
      tauR CocExt.central = CocExt.central ∧ (∀ x : Rf, tauR (tauR x) = x) ∧
      (∀ x : Rf, CocExt.central * x = x * CocExt.central) ∧
      (∀ (i : Fin 4725) (g : P), (cMul i g).g = factor (sigmaIdx i) (betaP g) ∧
        cosetAct (sigmaIdx i) (betaP g) = sigmaIdx (cosetAct i g)) ∧
      ∀ s : S, lamCoch s = bigLam (incl s) + muCoch s + muCoch (betaS s)) ∧
    (Nat.card Rf = 256 ∧ Nat.card T0 = 512 ∧ Nat.card T1 = 512 ∧
      (∀ x : Rf, x ∈ Subgroup.center Rf ↔
        x = 1 ∨ x = zR ∨ x = CocExt.central ∨ x = zR * CocExt.central) ∧
      (∀ p : T0, p ∈ Subgroup.center T0 ↔ p = 1 ∨ p = zT 0 ∨ p = tT 0 ∨ p = zT 0 * tT 0) ∧
      (∀ p : T1, p ∈ Subgroup.center T1 ↔ p = 1 ∨ p = zT 1 ∨ p = tT 1 ∨ p = zT 1 * tT 1) ∧
      (Nat.card (Subgroup.center Rf) = 4 ∧ ∀ x ∈ Subgroup.center Rf, x ^ 2 = 1) ∧
      (Nat.card (Subgroup.center T0) = 4 ∧ ∀ p ∈ Subgroup.center T0, p ^ 2 = 1) ∧
      (Nat.card (Subgroup.center T1) = 4 ∧ ∀ p ∈ Subgroup.center T1, p ^ 2 = 1) ∧
      (rootPair zR = (0, 0) ∧ rootPair (CocExt.central : Rf) = (48, 0) ∧
        rootPair (zR * CocExt.central) = (40, 96)) ∧
      (rootPair (zT 0) = (0, 0) ∧ rootPair (tT 0) = (48, 64) ∧
        rootPair (zT 0 * tT 0) = (56, 160)) ∧
      (rootPair (zT 1) = (16, 0) ∧ rootPair (tT 1) = (96, 64) ∧
        rootPair (zT 1 * tT 1) = (40, 160)) ∧
      (∀ φ : Rf ≃* Rf, ∀ x ∈ Subgroup.center Rf, φ x = x) ∧
      (∀ φ : T0 ≃* T0, ∀ x ∈ Subgroup.center T0, φ x = x) ∧
      ∀ φ : T1 ≃* T1, ∀ x ∈ Subgroup.center T1, φ x = x) :=
  ⟨ctss_j2_sylow_tables, ctss_j2_cohomology_basis, ctss_j2_transfer_image, ctss_j2_involutions,
    ctss_j2_outer_involution, ctss_j2_tau, ctss_j2_rigid_models⟩

end CFSG.ComponentClassification.J2Cover
