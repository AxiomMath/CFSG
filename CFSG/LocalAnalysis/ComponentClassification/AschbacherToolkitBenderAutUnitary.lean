module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderAutUnitaryModel
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderAutUnitaryCoordAut
import CFSG.Models.BenderSuzuki
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderAutOmega
public import CFSG.StronglyEmbedded.BenderUnitaryBorel

public section

namespace CFSG.ComponentClassification.AschbacherToolkit

namespace Bender

namespace UnitaryAut

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.ShultStronglyClosedTI

variable {K : Type*} [Field K] [Finite K] [CharP K 2]

theorem mulAut_apply_inv {G : Type*} [Group G] (φ : MulAut G) (x : G) : φ x⁻¹ = (φ x)⁻¹ :=
  map_inv φ x

omit [Finite K] [CharP K 2] in
theorem conj_root_fst (J : HermitianForm 3 K) (c v : hermitianUnipotentCoord J) :
    (c * v * c⁻¹).1.1 = v.1.1 := by
  change c.1.1 + v.1.1 + -c.1.1 = v.1.1
  ring

theorem autControlAt_root (J : HermitianForm 3 K) (f : ℕ) (hf : 2 ≤ f)
    (hKcard : Nat.card K = (2 ^ f) ^ 2) (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    AutControlAt (unitaryCoverRoot J hJ) := by
  intro α hn hz hpow hout
  classical
  have hq4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have : Finite (Matrix.ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_injective Subtype.val Subtype.coe_injective
  have : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
    huppert_II_10_13 J (2 ^ f) (by omega) hKcard hfixed
  have hcenter := center_eq_bot J (2 ^ f) (by omega) hKcard hfixed hJ
  set U := hermitianUnipotentPSU J hJ with hUdef
  have hU : Function.Injective U := CFSG.BenderSuzuki.Background.hermitianUnipotentPSU_injective J hJ
  have hconjU : ∀ (k : Kˣ) (z : hermitianUnipotentCoord J),
      hermitianTorusPSU J hJ k * U z * (hermitianTorusPSU J hJ k)⁻¹ =
        U (hermitianTorusAction J k z) := unitaryCoverTorus_conj_root J hJ
  obtain ⟨S, hS⟩ := exists_sylow_eq_root J f hf hKcard hfixed hJ
  obtain ⟨hNR, hcard⟩ := normalizer_and_card_sylow J f hf hKcard hfixed hJ
  obtain ⟨hSE, -, -, -⟩ :=
    benderBorel_sylowCenter (bender_projectiveSpecialUnitary_borel J f hf hKcard hfixed hJ) S
  have hHN : unitaryCoverTorus J hJ ≤
      Subgroup.normalizer (((S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))) : Set _) := by
    rw [hS]
    exact unitaryCoverTorus_le_normalizer J hJ
  have hmemZ : ∀ z, U z ∈ sylowCenter (unitaryCoverRoot J hJ) ↔ z.1.1 = 0 :=
    mem_sylowCenter_root J (2 ^ f) hKcard hfixed (by omega) hJ
  rw [← hS] at hn hz hNR hcard
  have hS₁ : hermitianWeylPSU J hJ • S ≠ S := by
    intro h
    apply weyl_not_mem_normalizer J (2 ^ f) hKcard hfixed hJ
    rw [← hS]
    exact (Sylow.smul_eq_iff_mem_normalizer).mp h
  have hHN₁ : unitaryCoverTorus J hJ ≤ Subgroup.normalizer
      ((((hermitianWeylPSU J hJ • S : Sylow 2 _)) :
        Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) : Set _) := by
    rintro _ ⟨k, rfl⟩
    rw [Omega.mem_normalizer_conj_smul_iff]
    have h := weyl_conj_torus J hJ (Units.map J.conj.toMonoidHom k)⁻¹
    have hk : (Units.map J.conj.toMonoidHom (Units.map J.conj.toMonoidHom k)⁻¹)⁻¹ = k := by
      ext
      simp [J.conj_involutive (k : K)]
    rw [hk] at h
    have h2 : (hermitianWeylPSU J hJ)⁻¹ * hermitianTorusPSU J hJ k * hermitianWeylPSU J hJ =
        hermitianTorusPSU J hJ (Units.map J.conj.toMonoidHom k)⁻¹ := by
      rw [← h]
      group
    rw [h2]
    exact hHN ⟨_, rfl⟩
  have hαS : α • S = S := Omega.smul_eq_of_mapsTo hn
  obtain ⟨r, hr, hrS₁⟩ := Omega.exists_conj_adjust hSE hcard hS₁ α hαS
  set α' := (MulAut.conj r)⁻¹ * α with hα'
  have hαα' : α = MulAut.conj r * α' := by rw [hα', mul_inv_cancel_left]
  have happ : ∀ g, α g = r * α' g * r⁻¹ := fun g => by
    rw [hαα', MulAut.mul_apply, MulAut.conj_apply]
  have hα'S : α' • S = S := by
    rw [hα', mul_smul, hαS, inv_smul_eq_iff, Omega.conj_smul_self hr]
  have hα'R : ∀ s ∈ (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)),
      α' s ∈ (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) := by
    intro s hs
    rw [hα', MulAut.mul_apply, MulAut.inv_apply, MulAut.conj_symm_apply]
    have h1 := (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).inv_mem hr
    exact (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).mul_mem
      ((S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).mul_mem h1 (hn s hs)) hr
  have hα'Z : ∀ z : hermitianUnipotentCoord J, z.1.1 = 0 → α' (U z) = U z := by
    intro z hz0
    have hZ : U z ∈ sylowCenter (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) := by
      rw [hS]
      exact (hmemZ z).mpr hz0
    rw [hα', MulAut.mul_apply, MulAut.inv_apply, MulAut.conj_symm_apply, hz _ hZ, mul_assoc,
      ← (mem_sylowCenter.mp hZ).2 r hr, inv_mul_cancel_left]
  have hα'H : ∀ k : Kˣ, ∃ k' : Kˣ, α' (hermitianTorusPSU J hJ k) = hermitianTorusPSU J hJ k' := by
    intro k
    have h1 := Omega.mem_normalizer_smul (α := α') (hHN ⟨k, rfl⟩)
    have h2 := Omega.mem_normalizer_smul (α := α') (hHN₁ ⟨k, rfl⟩)
    rw [hα'S] at h1
    rw [hrS₁] at h2
    obtain ⟨k', hk'⟩ := Omega.mem_of_mem_normalizer_of_mem_normalizer hSE hS₁ hNR hHN₁ h1 h2
    exact ⟨k', hk'.symm⟩
  have hRS : ∀ z, U z ∈ (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) := fun z => by
    rw [hS]
    exact ⟨z, rfl⟩
  have hex : ∀ z : hermitianUnipotentCoord J, ∃ z', α' (U z) = U z' := by
    intro z
    have h := hα'R _ (hRS z)
    rw [hS] at h
    obtain ⟨z', hz'⟩ := h
    exact ⟨z', hz'.symm⟩
  choose ψf hψf using hex
  let ψ : hermitianUnipotentCoord J →* hermitianUnipotentCoord J :=
    { toFun := ψf
      map_one' := by
        apply hU
        rw [← hψf, map_one, map_one]
      map_mul' := fun z z' => by
        apply hU
        rw [← hψf, map_mul, map_mul, map_mul, hψf, hψf] }
  have hψU : ∀ z, U (ψ z) = α' (U z) := fun z => (hψf z).symm
  have hψinj : Function.Injective ψ := by
    intro z z' h
    apply hU
    apply α'.injective
    rw [← hψU, ← hψU, h]
  have hψcen : ∀ z : hermitianUnipotentCoord J, z.1.1 = 0 → ψ z = z := fun z hz0 =>
    hU (by rw [hψU, hα'Z z hz0])
  have hψtor : ∀ k : Kˣ, ∃ k' : Kˣ,
      ∀ z, ψ (hermitianTorusAction J k z) = hermitianTorusAction J k' (ψ z) := by
    intro k
    obtain ⟨k', hk'⟩ := hα'H k
    refine ⟨k', fun z => hU ?_⟩
    calc U (ψ (hermitianTorusAction J k z)) = α' (U (hermitianTorusAction J k z)) := hψU _
      _ = α' (hermitianTorusPSU J hJ k * U z * (hermitianTorusPSU J hJ k)⁻¹) := by
          rw [hconjU]
      _ = α' (hermitianTorusPSU J hJ k) * α' (U z) * (α' (hermitianTorusPSU J hJ k))⁻¹ := by
          rw [map_mul, map_mul, mulAut_apply_inv]
      _ = hermitianTorusPSU J hJ k' * U (ψ z) * (hermitianTorusPSU J hJ k')⁻¹ := by
          rw [hk', hψU]
      _ = U (hermitianTorusAction J k' (ψ z)) := hconjU k' (ψ z)
  obtain ⟨lam, hNlam, hform⟩ := UnitaryCoordAut.coordAut_form J (2 ^ f) hKcard hfixed hq4 hJ ψ
    hψinj hψcen hψtor
  obtain ⟨c, rfl⟩ : ∃ c, U c = r := by
    have h := hr
    rw [hS] at h
    exact h
  have hαU : ∀ z, α (U z) = U (c * ψ z * c⁻¹) := by
    intro z
    rw [happ, ← hψU, ← map_inv, ← map_mul, ← map_mul]
  have hα'centralizes : (∀ z, ψ z = z) → False := by
    intro hid
    have hone := Omega.eq_one_of_centralizes hSE hcard hS₁ α' hα'S hrS₁ (fun s hs => by
      rw [hS] at hs
      obtain ⟨z, rfl⟩ := hs
      rw [← hψU, hid])
    apply hout (U c) (hS ▸ hr)
    rw [hαα', hone, mul_one]
  rcases hform with hid | hconj
  ·
    exfalso
    obtain ⟨n, hn2⟩ := hpow
    have hiter : ∀ (m : ℕ) (z : hermitianUnipotentCoord J), ∃ z',
        (α ^ m) (U z) = U z' ∧ z'.1.1 = lam ^ m * z.1.1 := by
      intro m
      induction m with
      | zero => exact fun z => ⟨z, by simp⟩
      | succ m ih =>
        intro z
        obtain ⟨z', hz', hz'1⟩ := ih z
        refine ⟨c * ψ z' * c⁻¹, ?_, ?_⟩
        · rw [pow_succ', MulAut.mul_apply, hz', hαU]
        · rw [conj_root_fst, (hid z').1, hz'1, pow_succ]
          ring
    have hsurj := unitaryCoverFirstCoord_surjective J (2 ^ f) hKcard hfixed hJ
    obtain ⟨z₁, hz₁⟩ := hsurj (Multiplicative.ofAdd 1)
    have hz₁1 : z₁.1.1 = 1 := congrArg Multiplicative.toAdd hz₁
    obtain ⟨z', hz', hz'1⟩ := hiter (2 ^ n) z₁
    rw [hn2, MulAut.one_apply] at hz'
    have hzz : z₁ = z' := hU hz'
    rw [← hzz, hz₁1, mul_one] at hz'1
    have hlam_pow : lam ^ (2 ^ n) = 1 := hz'1.symm
    have hlam0 : lam ≠ 0 := by
      rintro rfl
      rw [zero_pow (by positivity)] at hlam_pow
      exact zero_ne_one hlam_pow
    have hlam_card : lam ^ (Nat.card K - 1) = 1 := by
      have : Fintype K := Fintype.ofFinite K
      have := FiniteField.pow_card_sub_one_eq_one lam hlam0
      rwa [← Nat.card_eq_fintype_card] at this
    have hcop : Nat.Coprime (2 ^ n) (Nat.card K - 1) := by
      apply Nat.Coprime.pow_left
      rw [Nat.coprime_two_left, hKcard]
      have hev : Even (2 ^ f) := (by decide : Even (2 : ℕ)).pow_of_ne_zero (by omega)
      have hpos : 0 < (2 ^ f) ^ 2 := by positivity
      exact Nat.Even.sub_odd hpos (hev.pow_of_ne_zero (by decide)) odd_one
    have hlam1 : lam = 1 := by
      have := pow_gcd_eq_one.mpr ⟨hlam_pow, hlam_card⟩
      rwa [hcop.gcd_eq_one, pow_one] at this
    apply hα'centralizes
    intro z
    apply Subtype.ext
    apply Prod.ext
    · rw [(hid z).1, hlam1, one_mul]
    · exact (hid z).2
  ·
    have hψψ : ∀ z, ψ (ψ z) = z := by
      intro z
      apply Subtype.ext
      apply Prod.ext
      · change (ψ (ψ z)).1.1 = z.1.1
        rw [(hconj (ψ z)).1, (hconj z).1, map_mul, J.conj_involutive, ← mul_assoc, hNlam,
          one_mul]
      · change (ψ (ψ z)).1.2 = z.1.2
        rw [(hconj (ψ z)).2, (hconj z).2, (hconj z).1, map_mul, J.conj_involutive z.1.1]
        have h2 := CharTwo.add_self_eq_zero (z.1.1 * J.conj z.1.1)
        linear_combination h2 + z.1.1 * J.conj z.1.1 * hNlam
    have hα'2 : α' ^ 2 = 1 := by
      apply Omega.eq_one_of_centralizes hSE hcard hS₁ (α' ^ 2)
        (by rw [pow_two, mul_smul, hα'S, hα'S]) (by rw [pow_two, mul_smul, hrS₁, hrS₁])
      intro s hs
      rw [hS] at hs
      obtain ⟨z, rfl⟩ := hs
      rw [pow_two, MulAut.mul_apply, ← hψU, ← hψU, hψψ]
    have hα'α' : ∀ g, α' (α' g) = g := fun g => by
      have h := congrArg (fun φ : MulAut (ProjectiveSpecialUnitaryMatrixGroup J) => φ g) hα'2
      simpa only [pow_two, MulAut.mul_apply, MulAut.one_apply] using h
    have hα2 : α ^ 2 = MulAut.conj (U c * α' (U c)) := by
      ext g
      rw [pow_two, MulAut.mul_apply, happ, happ, MulAut.conj_apply, map_mul, map_mul,
        mulAut_apply_inv, hα'α']
      group
    have hα'c : α' (U c) = U (ψ c) := (hψU c).symm
    refine ⟨⟨U c * α' (U c), ?_, hα2⟩, ?_, ?_⟩
    · rw [hα'c, ← map_mul]
      exact ⟨c * ψ c, rfl⟩
    · rintro ⟨z₀, hz₀Z, hz₀⟩ t ht hfix
      have heq : MulAut.conj z₀ = MulAut.conj (U c * α' (U c)) := hz₀.symm.trans hα2
      have hz₀eq : z₀ = U c * α' (U c) := by
        set y := U c * α' (U c) with hy
        have hmem : y⁻¹ * z₀ ∈ Subgroup.center (ProjectiveSpecialUnitaryMatrixGroup J) := by
          rw [Subgroup.mem_center_iff]
          intro g
          have h1 := congrArg (fun φ : MulAut (ProjectiveSpecialUnitaryMatrixGroup J) => φ g) heq
          simp only [MulAut.conj_apply] at h1
          calc g * (y⁻¹ * z₀) = y⁻¹ * (y * g * y⁻¹) * z₀ := by group
            _ = y⁻¹ * (z₀ * g * z₀⁻¹) * z₀ := by rw [h1]
            _ = y⁻¹ * z₀ * g := by group
        rw [hcenter, Subgroup.mem_bot, inv_mul_eq_one] at hmem
        exact hmem.symm
      have hc0 : c.1.1 + lam * J.conj c.1.1 = 0 := by
        have hZc : U (c * ψ c) ∈ sylowCenter (unitaryCoverRoot J hJ) := by
          rw [map_mul, hψU, ← hz₀eq]
          exact hz₀Z
        have h := (hmemZ (c * ψ c)).mp hZc
        change c.1.1 + (ψ c).1.1 = 0 at h
        rwa [(hconj c).1] at h
      obtain ⟨z, rfl⟩ := ht
      have hfix' : c * ψ z * c⁻¹ = z := hU (by rw [← hαU]; exact hfix)
      have hψz : ψ z = c⁻¹ * z * c := by
        calc ψ z = c⁻¹ * (c * ψ z * c⁻¹) * c := by group
          _ = c⁻¹ * z * c := by rw [hfix']
      have h1 := (hconj z).1
      have h2 := (hconj z).2
      rw [hψz, UnitaryCoord.inv_mul_mul_fst] at h1
      rw [hψz, UnitaryCoord.inv_mul_mul_snd] at h2
      have hc2 := CharTwo.add_self_eq_zero (lam * J.conj c.1.1 * J.conj z.1.1)
      have h3 : z.1.1 * J.conj z.1.1 = 0 := by
        linear_combination -h2 + J.conj z.1.1 * hc0 - J.conj c.1.1 * h1 - hc2
      apply (hmemZ z).mpr
      rcases mul_eq_zero.mp h3 with h4 | h4
      · exact h4
      · exact (map_eq_zero J.conj).mp h4
    ·
      obtain ⟨a, ha⟩ : ∃ a : K, lam * J.conj a ≠ a := by
        by_contra hcon
        push Not at hcon
        have hl : lam = 1 := by
          have := hcon 1
          rwa [map_one, mul_one] at this
        have hall : ∀ a : K, J.conj a = a := fun a => by
          have := hcon a
          rwa [hl, one_mul] at this
        have h1 : Nat.card {x : K // J.conj x = x} = Nat.card K :=
          Nat.card_congr (Equiv.subtypeUnivEquiv hall)
        rw [hfixed, hKcard] at h1
        have h2 : 2 ^ f * 1 < 2 ^ f * 2 ^ f := Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
        rw [sq] at h1
        omega
      obtain ⟨z, hz⟩ :=
        unitaryCoverFirstCoord_surjective J (2 ^ f) hKcard hfixed hJ (Multiplicative.ofAdd a)
      have hz1 : z.1.1 = a := congrArg Multiplicative.toAdd hz
      refine ⟨U z, ⟨z, rfl⟩, ?_⟩
      rw [hαU, ← map_inv, ← map_mul, hmemZ]
      change -z.1.1 + (c * ψ z * c⁻¹).1.1 ≠ 0
      rw [conj_root_fst, (hconj z).1, hz1]
      intro h
      apply ha
      linear_combination h

theorem centPairAt_root (J : HermitianForm 3 K) (f : ℕ) (hf : 2 ≤ f)
    (hKcard : Nat.card K = (2 ^ f) ^ 2) (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    CentPairAt (unitaryCoverRoot J hJ) := by
  have hq4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hmemZ := mem_sylowCenter_root J (2 ^ f) hKcard hfixed (by omega) hJ
  intro s hs hsZ
  obtain ⟨z, rfl⟩ := hs
  have hz : z.1.1 ≠ 0 := fun h => hsZ ((hmemZ z).mpr h)
  obtain ⟨k, hk⟩ := UnitaryCoordAut.exists_scalar_not_fix J (2 ^ f) hKcard hfixed hq4 hJ
  refine ⟨(hermitianTorusPSU J hJ k)⁻¹,
    Subgroup.inv_mem _ (unitaryCoverTorus_le_normalizer J hJ ⟨k, rfl⟩), ?_⟩
  intro t ht hc₁ hc₂
  obtain ⟨w, rfl⟩ := ht
  rw [inv_inv, unitaryCoverTorus_conj_root] at hc₂
  rw [← map_mul, ← map_mul] at hc₁ hc₂
  have e1 := (UnitaryCoord.mul_comm_iff J z w).mp (CFSG.BenderSuzuki.Background.hermitianUnipotentPSU_injective J hJ hc₁)
  have e2 := (UnitaryCoord.mul_comm_iff J (hermitianTorusAction J k z) w).mp
    (CFSG.BenderSuzuki.Background.hermitianUnipotentPSU_injective J hJ hc₂)
  rw [UnitaryCoordAut.torusAction_fst, map_mul] at e2
  apply (hmemZ w).mpr
  by_contra hw
  apply hk
  have hne : w.1.1 * J.conj z.1.1 ≠ 0 := mul_ne_zero hw ((map_ne_zero J.conj).mpr hz)
  have h3 : (w.1.1 * J.conj z.1.1) * (J.conj ((k : K) * (J.conj (k : K))⁻¹ ^ 2) -
      (k : K) * (J.conj (k : K))⁻¹ ^ 2) = 0 := by
    linear_combination e2 - (k : K) * (J.conj (k : K))⁻¹ ^ 2 * e1
  rcases mul_eq_zero.mp h3 with h4 | h4
  · exact absurd h4 hne
  · exact sub_eq_zero.mp h4

theorem autControlAt_projectiveSpecialUnitary (J : HermitianForm 3 K) (f : ℕ) (hf : 2 ≤ f)
    (hKcard : Nat.card K = (2 ^ f) ^ 2) (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (T : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) :
    AutControlAt (T : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) := by
  have : Finite (Matrix.ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_injective Subtype.val Subtype.coe_injective
  obtain ⟨S, hS⟩ := exists_sylow_eq_root J f hf hKcard hfixed hJ
  exact autControlAt_of_one_sylow S (hS ▸ autControlAt_root J f hf hKcard hfixed hJ) T

theorem centPairAt_projectiveSpecialUnitary (J : HermitianForm 3 K) (f : ℕ) (hf : 2 ≤ f)
    (hKcard : Nat.card K = (2 ^ f) ^ 2) (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (T : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) :
    CentPairAt (T : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) := by
  have : Finite (Matrix.ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_injective Subtype.val Subtype.coe_injective
  obtain ⟨S, hS⟩ := exists_sylow_eq_root J f hf hKcard hfixed hJ
  exact centPairAt_of_one_sylow S (hS ▸ centPairAt_root J f hf hKcard hfixed hJ) T

end UnitaryAut

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups UnitaryAut in
theorem autControlAt_of_mulEquiv_psu3 {X : Type*} [Group X] [Finite X] {f : ℕ} (hf : 2 ≤ f)
    (e : X ≃* PSU3 2 f) (T : Sylow 2 X) : AutControlAt (T : Subgroup X) := by
  let k := GaloisField 2 f
  let K := FiniteField.Extension k 2 2
  let J := binaryQuadraticHermitian f (by omega)
  let : CharP K 2 := CharP.of_ringHom_of_ne_zero (algebraMap k K) 2 (by norm_num)
  have hKcard : Nat.card K = (2 ^ f) ^ 2 := by
    rw [FiniteField.natCard_extension, GaloisField.card 2 f (by omega)]
  have hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f :=
    quadraticBinaryFrobenius_fixed_card f (by omega)
  have hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] := rfl
  let e₁ := (projectiveSpecialUnitary_equiv_PSU3Model J f hf hJ hKcard hfixed).some
  have hmodel : PSU3Model f = PSU3 2 f := CFSG.Models.benderPSU3Model_eq_psu3 f
  let e₂ : ProjectiveSpecialUnitaryMatrixGroup J ≃* PSU3 2 f :=
    e₁.trans (MulEquiv.subgroupCongr hmodel)
  let e₃ : X ≃* ProjectiveSpecialUnitaryMatrixGroup J := e.trans e₂.symm
  exact autControlAt_of_mulEquiv e₃
    (autControlAt_projectiveSpecialUnitary J f hf hKcard hfixed hJ) T

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups UnitaryAut in
theorem centPairAt_of_mulEquiv_psu3 {X : Type*} [Group X] [Finite X] {f : ℕ} (hf : 2 ≤ f)
    (e : X ≃* PSU3 2 f) (T : Sylow 2 X) : CentPairAt (T : Subgroup X) := by
  let k := GaloisField 2 f
  let K := FiniteField.Extension k 2 2
  let J := binaryQuadraticHermitian f (by omega)
  let : CharP K 2 := CharP.of_ringHom_of_ne_zero (algebraMap k K) 2 (by norm_num)
  have hKcard : Nat.card K = (2 ^ f) ^ 2 := by
    rw [FiniteField.natCard_extension, GaloisField.card 2 f (by omega)]
  have hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f :=
    quadraticBinaryFrobenius_fixed_card f (by omega)
  have hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] := rfl
  let e₁ := (projectiveSpecialUnitary_equiv_PSU3Model J f hf hJ hKcard hfixed).some
  have hmodel : PSU3Model f = PSU3 2 f := CFSG.Models.benderPSU3Model_eq_psu3 f
  let e₂ : ProjectiveSpecialUnitaryMatrixGroup J ≃* PSU3 2 f :=
    e₁.trans (MulEquiv.subgroupCongr hmodel)
  let e₃ : X ≃* ProjectiveSpecialUnitaryMatrixGroup J := e.trans e₂.symm
  exact centPairAt_of_mulEquiv e₃
    (centPairAt_projectiveSpecialUnitary J f hf hKcard hfixed hJ) T

end Bender

end CFSG.ComponentClassification.AschbacherToolkit
