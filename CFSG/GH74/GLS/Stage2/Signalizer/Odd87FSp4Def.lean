module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FSp4Cls

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open scoped Matrix
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag


theorem exists_isotropic_parabolic {F : Type} [Field F] [Finite F] {ℓ : ℕ} [Fact ℓ.Prime] [CharP F ℓ]
    {X : Subgroup (StatedProj (StatedSp 2 F))} (hX : IsPGroup ℓ ↥X) (hX1 : X ≠ ⊥) :
    ∃ W : Submodule F (Fin 2 ⊕ Fin 2 → F), W ≠ ⊥ ∧ IsTotallyIsotropic (pairedSympForm F 2) W ∧
      normalizer (X : Set (StatedProj (StatedSp 2 F))) ≤ projStabilizer 2 F W := by
  obtain ⟨S, P', hP'top, hN, -, -, hS⟩ := CFSG.LieType.BorelTits.holds_statedProj_statedSp 2 F ℓ X hX1 hX
  obtain ⟨M, hM, hP'M⟩ := (eq_top_or_exists_le_coatom P').resolve_left hP'top
  have hMmem : M ∈ spMaximalParabolics 2 F ℓ := ⟨hM, _, ⟨S, rfl⟩, hS.trans hP'M⟩
  obtain ⟨W, hW0, hWiso, hMW⟩ := (((maximal_parabolics (K := F) (r := 2) ℓ (by norm_num)).1 ▸ hMmem : M ∈ {M | ∃ W : Submodule F (Fin 2 ⊕ Fin 2 → F), W ≠ ⊥ ∧ IsTotallyIsotropic (pairedSympForm F 2) W ∧ M = projStabilizer 2 F W}))
  exact ⟨W, hW0, hWiso, hN.trans (hP'M.trans (le_of_eq hMW))⟩


theorem mulVec_mem_of_proj_mem {F : Type} [Field F] {W : Submodule F (Fin 2 ⊕ Fin 2 → F)}
    {g : StatedSp 2 F} (hg : proj 2 F g ∈ projStabilizer 2 F W) :
    ∀ w ∈ W, ((g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ w ∈ W := by
  intro w hw
  have hgs : g ∈ stabilizer 2 F W := by
    rw [← comap_projStabilizer]
    exact hg
  have hmap := mem_stabilizer.mp hgs
  have hw' : Matrix.mulVecLin ((g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) w ∈
      W.map (Matrix.mulVecLin ((g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) :=
    Submodule.mem_map_of_mem hw
  rw [hmap] at hw'
  exact hw'


open Module in
theorem finrank_le_two_of_isotropic {F : Type} [Field F] {W : Submodule F (Fin 2 ⊕ Fin 2 → F)}
    (hW : IsTotallyIsotropic (pairedSympForm F 2) W) : finrank F W ≤ 2 := by
  have hle : W ≤ (pairedSympForm F 2).orthogonal W := by
    intro x hx
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    exact hW y hy x hx
  have h1 : finrank F W ≤ finrank F ((pairedSympForm F 2).orthogonal W) := Submodule.finrank_mono hle
  have h2 := LinearMap.BilinForm.finrank_orthogonal (B := pairedSympForm F 2)
    (pairedSympForm_nondegenerate (K := F) (r := 2)) W
  have h3 : finrank F (Fin 2 ⊕ Fin 2 → F) = 4 := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
  omega

theorem index_projStabilizer_isotropic {F : Type} [Field F] [Finite F] {W : Submodule F (Fin 2 ⊕ Fin 2 → F)}
    (hW0 : W ≠ ⊥) (hW : IsTotallyIsotropic (pairedSympForm F 2) W) :
    (projStabilizer 2 F W).index = (Nat.card F + 1) * (Nat.card F ^ 2 + 1) := by
  have hk1 : 1 ≤ Module.finrank F W := Submodule.one_le_finrank_iff.mpr hW0
  have hk2 := finrank_le_two_of_isotropic hW
  have hq : (2 : ℕ) ≤ Nat.card F := by
    have := Finite.one_lt_card (α := F)
    omega
  have hqq : (1 : ℚ) < (Nat.card F : ℚ) := by exact_mod_cast hq
  obtain ⟨-, hind, h1, h2⟩ := isotropic_subspace_index (r := 2) (K := F) (q := Nat.card F) rfl
    (k := Module.finrank F W) hk2
  have hind' := hind W hW rfl
  have hq1 : ((Nat.card F : ℚ) - 1) ≠ 0 := by linarith
  have key : ((projStabilizer 2 F W).index : ℚ) = (((Nat.card F + 1) * (Nat.card F ^ 2 + 1) : ℕ) : ℚ) := by
    rw [hind']
    rcases (by omega : Module.finrank F W = 1 ∨ Module.finrank F W = 2) with hk | hk
    · rw [hk, h1]
      push_cast
      field_simp
      ring
    · rw [hk, h2]
      simp [Finset.prod_range_succ]
  exact_mod_cast key


theorem not_dvd_class_II {q : ℕ} (hq : 3 ≤ q) :
    ¬ q ^ 2 * (q ^ 4 - 1) ∣ q ^ 4 * (q ^ 2 - 1) * (q - 1) := by
  intro h
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  have hr : 2 ≤ r := by omega
  have e1 : (r + 1) ^ 2 - 1 = r * (r + 2) := by
    apply Nat.sub_eq_of_eq_add; ring
  have e2 : (r + 1) ^ 4 - 1 = r * (r + 2) * ((r + 1) ^ 2 + 1) := by
    apply Nat.sub_eq_of_eq_add; ring
  have e3 : r + 1 - 1 = r := by omega
  rw [e1, e2, e3] at h
  have hM : 0 < (r + 1) ^ 2 * (r * (r + 2)) := by positivity
  have h1 : (r + 1) ^ 2 * (r * (r + 2)) * ((r + 1) ^ 2 + 1) ∣
      (r + 1) ^ 2 * (r * (r + 2)) * ((r + 1) ^ 2 * r) := by
    have e : (r + 1) ^ 2 * (r * (r + 2) * ((r + 1) ^ 2 + 1)) =
        (r + 1) ^ 2 * (r * (r + 2)) * ((r + 1) ^ 2 + 1) := by ring
    have e' : (r + 1) ^ 4 * (r * (r + 2)) * r =
        (r + 1) ^ 2 * (r * (r + 2)) * ((r + 1) ^ 2 * r) := by ring
    rw [e, e'] at h
    exact h
  have h2 : (r + 1) ^ 2 + 1 ∣ (r + 1) ^ 2 * r := Nat.dvd_of_mul_dvd_mul_left hM h1
  have hcop : Nat.Coprime ((r + 1) ^ 2 + 1) ((r + 1) ^ 2) := by
    refine Nat.Coprime.pow_right 2 ?_
    have : (r + 1) ^ 2 + 1 = (r + 1) * (r + 1) + 1 := by ring
    rw [this]
    exact (Nat.coprime_mul_left_add_left 1 (r + 1) (r + 1)).mpr (Nat.coprime_one_left _)
  have h3 : (r + 1) ^ 2 + 1 ∣ r := hcop.dvd_of_dvd_mul_left h2
  have h4 := Nat.le_of_dvd (by omega) h3
  nlinarith

open CFSG.ComponentClassification CFSG.ComponentClassification.CatFactsSp4 in
theorem coreII_defining {F : Type} [Field F] [Finite F] (A : gsp 2 F) (d : Fˣ)
    (hAA : ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
      ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = (d : F) • 1)
    (hdm : (d : F) = (multiplierUnit A : F)) (hsq : ∀ l : F, l ^ 2 ≠ (multiplierUnit A : F))
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hpc : ringChar F = p)
    {X : Subgroup (StatedProj (StatedSp 2 F))} (h : PConfig (conjAut 2 F A) p X) : False := by
  classical
  have : CharP F p := hpc ▸ ringChar.charP F
  obtain ⟨hXp, hX1, -, hN⟩ := h
  obtain ⟨W, hW0, hWiso, hNW⟩ := exists_isotropic_parabolic hXp hX1
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨n, hpp, hqn⟩ := FiniteField.card F p
  have hK : Nat.card F = p ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hqn
  have hn1 : 1 ≤ (n : ℕ) := n.pos
  set q := Nat.card F with hq
  have h2 : (2 : F) ≠ 0 := by
    intro h0
    have : ((2 : ℕ) : F) = 0 := by exact_mod_cast h0
    rw [CharP.cast_eq_zero_iff F p] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).mp this)
  have hq3 : 3 ≤ q := by
    have h1 : 3 ≤ p := by
      have := (Fact.out : p.Prime).two_le
      omega
    calc 3 ≤ p := h1
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ (n : ℕ) := Nat.pow_le_pow_right (Fact.out : p.Prime).pos hn1
      _ = q := hK.symm
  have hd0 : (d : F) ≠ 0 := d.ne_zero
  have hdsq : ∀ l : F, l ^ 2 ≠ (d : F) := by rw [hdm]; exact hsq
  have hμ : ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)ᵀ * formJ 2 F *
      ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = (d : F) • formJ 2 F := by
    rw [hdm]; exact multiplierUnit_spec A
  obtain ⟨-, hcardS⟩ := fixOf_conjSp_nonsquare (Fact.out : p.Prime) hp2 hn1 hK A hd0 hdsq hAA hμ
  set θ := conjSp 2 F A with hθ
  have hθα : ∀ g, conjAut 2 F A (proj 2 F g) = proj 2 F (θ g) := fun g => conjAut_proj A g
  have hZ : ∀ z ∈ spScalars 2 F, θ z = z := fun z hz => conjSp_scalar A hz
  have hEle : (fixOf θ).map (proj 2 F) ≤ projStabilizer 2 F W :=
    (map_fixOf_le θ hθα).trans (fun x hx => hNW (hN hx))
  have hdvd : Nat.card ((fixOf θ).map (proj 2 F)) ∣ Nat.card (projStabilizer 2 F W) :=
    Subgroup.card_dvd_of_le hEle
  have hEcard := card_map_fixOf_mul_two h2 θ hZ
  have hind := index_projStabilizer_isotropic hW0 hWiso
  have hPW := Subgroup.card_mul_index (projStabilizer 2 F W)
  have hP := CFSG.ClassicalInvolution.card_statedProj_statedSp_of_two_ne_zero (K := F) (n := 2) h2 (by norm_num)
  have hprod : ∏ j ∈ Finset.Icc 1 2, (q ^ (2 * j) - 1) = (q ^ 2 - 1) * (q ^ 4 - 1) := by
    have e : Finset.Icc 1 2 = {1, 2} := by decide
    rw [e]; simp
  rw [hprod] at hP
  have hq4 : q ^ 4 - 1 = (q - 1) * ((q + 1) * (q ^ 2 + 1)) := by
    obtain ⟨r, hr⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
    rw [hr]
    have e1 : r + 1 - 1 = r := by omega
    rw [e1]
    apply Nat.sub_eq_of_eq_add; ring
  have hind' : (projStabilizer 2 F W).index = (q + 1) * (q ^ 2 + 1) := hind
  have h2PW : 2 * Nat.card (projStabilizer 2 F W) = q ^ 4 * (q ^ 2 - 1) * (q - 1) := by
    have hpos : 0 < (q + 1) * (q ^ 2 + 1) := by positivity
    apply Nat.eq_of_mul_eq_mul_right hpos
    calc 2 * Nat.card (projStabilizer 2 F W) * ((q + 1) * (q ^ 2 + 1))
        = (Nat.card (projStabilizer 2 F W) * (projStabilizer 2 F W).index) * 2 := by rw [hind']; ring
      _ = Nat.card (StatedProj (StatedSp 2 F)) * 2 := by rw [hPW]
      _ = q ^ (2 ^ 2) * ((q ^ 2 - 1) * (q ^ 4 - 1)) := hP
      _ = q ^ 4 * (q ^ 2 - 1) * (q - 1) * ((q + 1) * (q ^ 2 + 1)) := by
          rw [hq4]; ring
  have hEq : 2 * Nat.card ((fixOf θ).map (proj 2 F)) = q ^ 2 * (q ^ 4 - 1) := by
    rw [mul_comm, hEcard, hcardS, ← hK]
    have : (q ^ 2) ^ 2 = q ^ 4 := by ring
    rw [this]
  have hdvd2 : 2 * Nat.card ((fixOf θ).map (proj 2 F)) ∣ 2 * Nat.card (projStabilizer 2 F W) :=
    mul_dvd_mul_left 2 hdvd
  rw [hEq, h2PW] at hdvd2
  exact not_dvd_class_II hq3 hdvd2

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
