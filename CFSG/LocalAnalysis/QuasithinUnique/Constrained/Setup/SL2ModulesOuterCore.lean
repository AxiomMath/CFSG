module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesOuterAut
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesOuterTransport
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesFourModules

public section

namespace CFSG.QuasithinUnique.Setup.SL2Modules

open scoped MatrixGroups LinearAlgebra.Projectivization
open CFSG.GorensteinWalter Projectivization

section Numerics

theorem numerics_trivial {d m' : ℕ} (hd : 1 ≤ d) (hm : 1 ≤ m')
    (h : d * 2 ^ (2 * m') ≤ 1 + d * (2 ^ m' * (2 ^ m' + 1) / 2)) : d = 1 ∧ m' = 1 := by
  obtain ⟨h', hh'⟩ : ∃ h', h' = 2 ^ m' := ⟨_, rfl⟩
  have h2 : 2 ≤ h' := by
    rw [hh']
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ m' := Nat.pow_le_pow_right (by norm_num) hm
  have hpow : 2 ^ (2 * m') = h' * h' := by rw [hh', two_mul, pow_add]
  have hq : 2 * (h' * (h' + 1) / 2) = h' * (h' + 1) :=
    Nat.mul_div_cancel' (Nat.even_mul_succ_self h').two_dvd
  rw [hpow, ← hh'] at h
  generalize h' * (h' + 1) / 2 = q at h hq
  have h3 : h' = 2 := by
    by_contra hne
    have h3 : 3 ≤ h' := by omega
    nlinarith [Nat.mul_le_mul hd h3, Nat.mul_le_mul (Nat.mul_le_mul hd h3) h3]
  subst h3
  have hm1 : m' = 1 := by
    have : 2 ^ m' = 2 ^ 1 := hh'.symm
    exact Nat.pow_right_injective (le_refl 2) this
  refine ⟨?_, hm1⟩
  nlinarith

theorem numerics_nontrivial {s d m' n : ℕ} (hs : 1 ≤ s) (hd : 1 ≤ d) (hm : 1 ≤ m') (hn : n = 2 * s)
    (hrn : 2 * m' ≤ n) (horb : n ≤ 2 * m' * d)
    (h : d * 2 ^ (2 * m') ≤ (s + 1) + d * 2 ^ (2 * m' - 1)) : n = 2 ∧ d = 1 ∧ m' = 1 := by
  obtain ⟨r, hr⟩ : ∃ r, r = 2 * m' := ⟨_, rfl⟩
  have hr2 : 2 ≤ r := by omega
  have hpow : 2 ^ r = 2 * 2 ^ (r - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [← hr] at h horb hrn
  rw [hpow] at h
  have h1 : d * 2 ^ (r - 1) ≤ s + 1 := by nlinarith
  have h2 : r ≤ 2 ^ (r - 1) := by
    have := Nat.lt_two_pow_self (n := r - 1)
    omega
  have h3 : n ≤ 2 ^ (r - 1) * d := le_trans horb (by nlinarith)
  have hs1 : s = 1 := by nlinarith
  have hn2 : n = 2 := by omega
  have hr_eq : r = 2 := by omega
  have hm1 : m' = 1 := by omega
  refine ⟨hn2, ?_, hm1⟩
  rw [hr_eq] at h1
  simp at h1
  omega

theorem le_of_two_pow_le_mul {a b c : ℕ} (h : 2 ^ a ≤ 2 ^ b * 2 ^ c) : a ≤ b + c := by
  rw [← pow_add] at h
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h

end Numerics

section Fixed

variable {k₀ : Type*} [Field k₀] {W : Type*} [AddCommGroup W] [Module k₀ W] [Finite W]

omit [Finite W] in
theorem natCard_fixed_conj_units (a c : (Module.End k₀ W)ˣ) :
    Nat.card {w : W // (c⁻¹ * a * c).val w = w} = Nat.card {w : W // a.val w = w} := by
  have hc : ∀ w, (c⁻¹).val (c.val w) = w := fun w => by
    rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Module.End.one_apply]
  have hc' : ∀ w, c.val ((c⁻¹).val w) = w := fun w => by
    rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Module.End.one_apply]
  refine Nat.card_congr
    { toFun := fun w => ⟨c.val w.1, ?_⟩
      invFun := fun w => ⟨(c⁻¹).val w.1, ?_⟩
      left_inv := fun w => Subtype.ext (hc w.1)
      right_inv := fun w => Subtype.ext (hc' w.1) }
  · have h := w.2
    simp only [Units.val_mul, Module.End.mul_apply] at h
    have h2 := congrArg c.val h
    rwa [hc'] at h2
  · have h := w.2
    simp only [Units.val_mul, Module.End.mul_apply]
    rw [hc', h]

theorem natCard_fixed_le (S : Subgroup (Module.End k₀ W)ˣ) {a : (Module.End k₀ W)ˣ} (ha : a ∈ S) :
    Nat.card {w : W // ∀ c ∈ S, c.val w = w} ≤ Nat.card {w : W // a.val w = w} :=
  Nat.card_le_card_of_injective (fun w => ⟨w.1, w.2 a ha⟩)
    (fun _ _ h => Subtype.ext (congrArg (fun v : {w : W // a.val w = w} => v.1) h))

end Fixed

section Core

theorem outer_core {n : ℕ} (hn : 2 ≤ n) {F : Type*} [Field F] [Fintype F]
    (hF : Fintype.card F = 2 ^ n) [Fintype (ℙ F (Fin 2 → F))] [DecidableEq (ℙ F (Fin 2 → F))]
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) SL(2, F) W) (hρ : Function.Injective ρ) (hirr : ρ.IsIrreducible)
    (A : Subgroup (Module.End (ZMod 2) W)ˣ) [CFSG.IsElementaryAbelian 2 A] (hA1 : A ≠ ⊥)
    (hAN : A ≤ Subgroup.normalizer (ρ.toHomUnits.range : Set (Module.End (ZMod 2) W)ˣ))
    (hquad : ∀ a ∈ A, ∀ b ∈ A, ∀ w, b.val (a.val w - w) = a.val w - w)
    (hoff : Nat.card W ≤ Nat.card A * Nat.card {w : W // ∀ a ∈ A, a.val w = w})
    (hAL : ¬ A ≤ ρ.toHomUnits.range) :
    n = 2 ∧ Nat.card (EndRing ρ) = 2 ∧ Nat.card W = 16 ∧
      ∃ φ : W ≃+ ↥(evenWeight (ℙ F (Fin 2 → F))), ∀ (g : SL(2, F)) (w : W),
        (φ (ρ g w) : ℙ F (Fin 2 → F) → ZMod 2) =
          permAct (MulAction.toPerm g) (φ w : ℙ F (Fin 2 → F) → ZMod 2) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcharF : CharP F 2 := charP_two_of_card_eq hF
  have : Fact ρ.IsIrreducible := ⟨hirr⟩
  obtain ⟨hWnt, hWirr⟩ := (isIrreducible_iff ρ).mp hirr
  have hne : (uElt (1 : F) : SL(2, F)) ≠ 1 := fun h =>
    one_ne_zero (uElt_injective (h.trans uElt_zero.symm))
  have hnt : ∃ g, ρ g ≠ 1 := ⟨uElt 1, fun h => hne (hρ (h.trans (map_one ρ).symm))⟩
  set ρU := ρ.toHomUnits with hρU_def
  have hρU : Function.Injective ρU := fun g h e => hρ (by simpa [hρU_def] using congrArg Units.val e)
  set L := ρU.range with hL_def
  have hF4 : ∃ t : Finset F, t.card = 4 := by
    have h4 : 4 ≤ (Finset.univ : Finset F).card := by
      rw [Finset.card_univ, hF]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq h4
    exact ⟨t, ht⟩
  have hSperf : Group.IsPerfect SL(2, F) := CFSG.LinearGroups.special_linear_dimension_two_perfect hF4
  have hLperf : Group.IsPerfect L := by
    have := hSperf
    exact Group.IsPerfect.range ρU
  have hLnt : L ≠ ⊥ := by
    intro h
    have h1 : ρU (uElt 1) ∈ L := ⟨uElt 1, rfl⟩
    rw [h, Subgroup.mem_bot] at h1
    exact hne (hρU (h1.trans (map_one ρU).symm))
  have hirrL : (repOfSubgroup L).IsIrreducible := by
    rw [isIrreducible_iff]
    refine ⟨hWnt, fun U hU => hWirr U (fun g u hu => ?_)⟩
    have := hU ⟨ρU g, ⟨g, rfl⟩⟩ u hu
    simpa [repOfSubgroup_apply, hρU_def] using this
  have hAnorm : ∀ a ∈ A, ∀ g ∈ L, a * g * a⁻¹ ∈ L := fun a ha g hg =>
    (Subgroup.mem_normalizer_iff.mp (hAN ha) g).mp hg
  have hA2 : ∀ a ∈ A, a * a = 1 := fun a ha => by
    rw [← pow_two]
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian a ha
  have : Fact (repOfSubgroup L).IsIrreducible := ⟨hirrL⟩
  have hN17 := quadratic_offender_endomorphism_field_linearization (k := ZMod 2)
    L A hLperf hLnt hAnorm hA2 hA1 hquad hoff
  have hρU_val : ∀ g, (ρU g).val = ρ g := fun g => by rw [hρU_def]; rfl
  have hcommD : ∀ a ∈ A, ∀ δ : EndRing ρ, a.val * epsHom ρ δ = epsHom ρ δ * a.val := by
    intro a ha δ
    obtain ⟨δ', hδ'⟩ : ∃ δ' : EndRing (repOfSubgroup L), epsHom _ δ' = epsHom ρ δ := by
      obtain ⟨ψ, hψ⟩ := (mem_endRing_iff (repOfSubgroup L) (epsHom ρ δ)).mpr (fun g' v => by
        obtain ⟨g, hg⟩ := g'.2
        have h1 := epsHom_commutes ρ δ g v
        show epsHom ρ δ (g'.1.val v) = g'.1.val (epsHom ρ δ v)
        rw [← hg, hρU_val]
        exact h1)
      exact ⟨ψ, LinearMap.ext fun w => congrFun hψ w⟩
    rw [← hδ']
    exact hN17.1 a ha δ'
  obtain ⟨s, hs1, hns, hAcard, hAtriv, a, haA, haL, x, hxconj⟩ :=
    outer_data (n := n) (by omega) ((Nat.card_eq_fintype_card (α := F)).trans hF) ρ hirr hρU A hAN hAL
  rw [← hρU_def] at hxconj haL
  have hDfin : Finite (EndRing ρ) := finite_endRing ρ
  obtain ⟨d, hd1, hDcard, hdesc⟩ :=
    binary_SL2_irreducible_Frobenius_descent (n := n) (by omega) hF ρ hnt
  have : Module.Finite (EndRing ρ) W := Module.Finite.of_finite
  obtain ⟨E, hEF, hEfin, hEchar, ιF, ιD, J, hJne, hJn, ⟨Φ⟩, hshift, hdim⟩ :=
    hdesc (Module.finBasis (EndRing ρ) W)
  let _ : Algebra F E := ιF.toAlgebra
  have hF2 : Fintype.card F = 2 ^ (2 * s) := by rw [← hns]; exact hF
  have hJ2 : ∀ i ∈ J, i < 2 * s := fun i hi => hns ▸ hJn i hi
  set a' := (ρU x)⁻¹ * a * ρU x with ha'
  have ha'2 : a' * a' = 1 := by
    calc a' * a' = (ρU x)⁻¹ * (a * a) * ρU x := by simp only [ha']; group
      _ = 1 := by rw [hA2 a haA]; group
  have hcomm' : ∀ δ : EndRing ρ, a'.val * epsHom ρ δ = epsHom ρ δ * a'.val := by
    intro δ
    have h1 : ∀ g : SL(2, F), Commute (ρU g).val (epsHom ρ δ) := by
      intro g
      apply LinearMap.ext
      intro v
      rw [hρU_val]
      exact (epsHom_commutes ρ δ g v).symm
    have h3 : Commute (ρU x)⁻¹.val (epsHom ρ δ) := by
      rw [← map_inv ρU x]
      exact h1 x⁻¹
    have h2 : Commute a.val (epsHom ρ δ) := hcommD a haA δ
    have h4 := (h3.mul_left h2).mul_left (h1 x)
    show ((ρU x)⁻¹ * a * ρU x).val * _ = _ * ((ρU x)⁻¹ * a * ρU x).val
    rw [Units.val_mul, Units.val_mul]
    exact h4
  let aD : Module.End (EndRing ρ) W := linD ρ a'.val hcomm'
  have haD2 : aD * aD = 1 := by
    apply LinearMap.ext
    intro w
    have h := congrArg (fun u : (Module.End (ZMod 2) W)ˣ => u.val w) ha'2
    simp only [Units.val_mul, Module.End.mul_apply, Units.val_one, Module.End.one_apply] at h
    exact h
  have hconjD : ∀ g, aD * repD ρ g = repD ρ (fieldAut F s g) * aD := by
    intro g
    apply LinearMap.ext
    intro w
    have h := hxconj g
    have h' : a' * ρU g = ρU (fieldAut F s g) * a' := by
      calc a' * ρU g = (a' * ρU g * a'⁻¹) * a' := by group
        _ = ρU (fieldAut F s g) * a' := by rw [h]
    have h2 := congrArg (fun u : (Module.End (ZMod 2) W)ˣ => u.val w) h'
    simp only [Units.val_mul, Module.End.mul_apply, hρU_val] at h2
    exact h2
  obtain ⟨hJs, m', hm', hCa'⟩ := outer_involution_count ρ (Module.finBasis (EndRing ρ) W) ιD J Φ
    hs1 hF2 hJ2 aD haD2 hconjD
  have hCa : Nat.card {w : W // a.val w = w} =
      Nat.card (EndRing ρ) ^ (2 ^ m' * (2 ^ m' + 1) / 2) := by
    rw [← hCa']
    have h := natCard_fixed_conj_units a (ρU x)
    exact h.symm.trans (Nat.card_congr (Equiv.refl _))
  have hm1 : 1 ≤ m' := by
    have := Finset.card_pos.mpr hJne
    omega
  have hW : Nat.card W = 2 ^ (d * 2 ^ (2 * m')) := by
    rw [natCard_eq_pow_finrank (ρ := ρ), hdim, hm', hDcard, ← pow_mul]
  have hCa2 : Nat.card {w : W // a.val w = w} = 2 ^ (d * (2 ^ m' * (2 ^ m' + 1) / 2)) := by
    rw [hCa, hDcard, ← pow_mul]
  have horb : n ≤ J.card * d := n_le_card_mul (by omega) (by omega) hJn hJne hshift
  have hrn : J.card ≤ n := by
    calc J.card ≤ (Finset.range n).card :=
          Finset.card_le_card (fun i hi => Finset.mem_range.mpr (hJn i hi))
      _ = n := Finset.card_range n
  rw [hm'] at horb hrn
  have hnum : n = 2 ∧ d = 1 ∧ m' = 1 := by
    by_cases hB : ∀ b ∈ A, b ∈ L → b = 1
    · have hA2c : Nat.card A = 2 := hAtriv hB
      have h1 : Nat.card W ≤ 2 * Nat.card {w : W // a.val w = w} := by
        calc Nat.card W ≤ Nat.card A * Nat.card {w : W // ∀ c ∈ A, c.val w = w} := hoff
          _ ≤ 2 * Nat.card {w : W // a.val w = w} := by
            rw [hA2c]
            exact Nat.mul_le_mul_left 2 (natCard_fixed_le A haA)
      rw [hW, hCa2] at h1
      have h2 : 2 ^ (d * 2 ^ (2 * m')) ≤ 2 ^ 1 * 2 ^ (d * (2 ^ m' * (2 ^ m' + 1) / 2)) := by
        simpa using h1
      have h3 := le_of_two_pow_le_mul h2
      obtain ⟨hd, hm⟩ := numerics_trivial hd1 hm1 h3
      subst hd hm
      refine ⟨?_, rfl, rfl⟩
      omega
    · push Not at hB
      obtain ⟨b, hbA, hbL, hb1⟩ := hB
      obtain ⟨g, hg⟩ := hbL
      subst hg
      have hg1 : g ≠ 1 := fun h => hb1 (by rw [h, map_one])
      have hg2 : g * g = 1 := hρU (by rw [map_mul, hA2 _ hbA, map_one])
      have hCb := natCard_fixW_involution ρ (Module.finBasis (EndRing ρ) W) ιF ιD J hJne Φ g hg1
        hg2
      have h1 : Nat.card W ≤ 2 ^ (s + 1) * Nat.card {w : W // ρ g w = w} := by
        calc Nat.card W ≤ Nat.card A * Nat.card {w : W // ∀ c ∈ A, c.val w = w} := hoff
          _ ≤ 2 ^ (s + 1) * Nat.card {w : W // ρ g w = w} := by
            apply Nat.mul_le_mul hAcard
            have h5 := natCard_fixed_le A hbA
            rwa [hρU_val] at h5
      rw [hW, hCb, hDcard, ← pow_mul, hm'] at h1
      have h2 : 2 ^ (d * 2 ^ (2 * m')) ≤ 2 ^ (s + 1) * 2 ^ (d * 2 ^ (2 * m' - 1)) := h1
      exact numerics_nontrivial hs1 hd1 hm1 hns hrn horb (le_of_two_pow_le_mul h2)
  obtain ⟨hn2, hd, hm⟩ := hnum
  subst hd hm
  have hDcard2 : Nat.card (EndRing ρ) = 2 := by rw [hDcard]; norm_num
  have hWcard : Nat.card W = 16 := by rw [hW]; norm_num
  refine ⟨hn2, hDcard2, hWcard, ?_⟩
  have hk : Fintype.card F = 4 := by rw [hF, hn2]; norm_num
  have hJeq : J = {0, 1} := by
    have hsub : J ⊆ ({0, 1} : Finset ℕ) := fun i hi => by
      have := hJn i hi
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    exact Finset.eq_of_subset_of_card_le hsub (by rw [hm']; decide)
  subst hJeq
  obtain ⟨w₀, hw₀ne, hw₀⟩ := borel_fixed_vector hk ρ (Module.finBasis (EndRing ρ) W) ιF ιD Φ
  exact deleted_iso_of_borel_fixed hk ρ hnt w₀ hw₀ne hw₀

end Core

end CFSG.QuasithinUnique.Setup.SL2Modules
