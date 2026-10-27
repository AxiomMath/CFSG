module

public import CFSG.GH74.Uniqueness.Bender.UnitaryDiag
public import CFSG.GH74.Uniqueness.Bender.UnitaryAut

public section

namespace CFSG.GH74.Uniqueness.Bender

open Subgroup

section Main

open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups CFSG.ShultStronglyClosedTI
open CFSG.ShultStronglyClosedTI.UnitaryAutomorphism CFSG.ProperTwoGeneratedCore.RootCenter

theorem BenderType.lemma_3_6_d_unitary
    {K : Type*} [Group K] [Finite K] {n e : ℕ}
    (h : BenderType K n 3 e) (Q : Sylow 2 K) :
    ∃ (t : K) (I : Subgroup K) (D₃ : Subgroup (MulAut K)),
      t * t = 1 ∧ t ∉ borel (Q : Subgroup K) ∧
      Nonempty (I ≃* PSL2Model n) ∧ rootCenter (Q : Subgroup K) ≤ I ∧
      fixCartan (Q : Subgroup K) t ⊓ I = ⊥ ∧
      (∀ x ∈ fixCartan (Q : Subgroup K) t, ∀ y ∈ I, x * y = y * x) ∧
      (∀ x ∈ fixCartan (Q : Subgroup K) t, x ≠ 1 →
        centralizer ({x} : Set K) = fixCartan (Q : Subgroup K) t ⊔ I) ∧
      IsCyclic D₃ ∧ Nat.card D₃ = 2 ^ n + 1 ∧
      D₃ ≤ autCentralizer (rootCenter (Q : Subgroup K)) ∧
      (∀ x ∈ fixCartan (Q : Subgroup K) t, MulAut.conj x ∈ D₃) ∧
      (∀ δ ∈ D₃, ∀ k ∈ fixCartan (Q : Subgroup K) t ⊔ I, δ k = k) ∧
      (∀ δ ∈ D₃, δ ≠ 1 → ∀ k : K, δ k = k → k ∈ fixCartan (Q : Subgroup K) t ⊔ I) ∧
      (∀ A : Subgroup (MulAut K), A ≤ autCentralizer (rootCenter (Q : Subgroup K)) →
        Odd (Nat.card A) →
        ∃ ρ ∈ (Q : Subgroup K), ∀ σ ∈ A, MulAut.conj ρ * σ * (MulAut.conj ρ)⁻¹ ∈ D₃) ∧
      (∀ A : Subgroup (MulAut K), A ≤ autCentralizer (rootCenter (Q : Subgroup K)) →
        Odd (Nat.card A) → A ≠ ⊥ →
        ∃ ρ ∈ (Q : Subgroup K), ∀ k : K,
          (∀ σ ∈ A, σ k = k) ↔ ρ * k * ρ⁻¹ ∈ fixCartan (Q : Subgroup K) t ⊔ I) := by
  classical
  obtain ⟨hn, he⟩ : 2 ≤ n ∧ e = (2 ^ n + 1) / Nat.gcd 3 (2 ^ n + 1) := by
    rcases h.cases' with ⟨hi1, -, -⟩ | ⟨hi2, -, -⟩ | ⟨-, he, hn⟩
    · omega
    · omega
    · exact ⟨hn, he⟩
  obtain ⟨t, hct⟩ := h.exists_benderCore Q
  obtain ⟨E, hE, hF, J, hJ, hcard, hfixed, φ, hφQ, hφD⟩ :=
    h.exists_standard_iso_unitary Q hct.sq_eq_one hct.not_mem
  have : Fintype E := Fintype.ofFinite E
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := n * 2) (by
    simpa only [Nat.card_eq_fintype_card, ← pow_mul] using hcard)
  have : Finite (Matrix.ProjGenLinGroup (Fin 3) E) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_injective _ Subtype.coe_injective
  have hZR : rootCenter (unitaryCoverRoot J hJ) = (rootCenter (Q : Subgroup K)).map φ.toMonoidHom := by
    rw [← hφQ, rootCenter_map]
  have hUR : unitaryRootCenter J hJ = (rootCenter (Q : Subgroup K)).map φ.toMonoidHom := by
    rw [unitaryRootCenter_eq_rootCenter J hJ n hn hcard hfixed, hZR]
  have hAut : rootCenterAut (unitaryCoverRoot J hJ) (unitaryRootCenter J hJ) =
      (autCentralizer (rootCenter (Q : Subgroup K))).map (MulAut.congr φ).toMonoidHom := by
    rw [hUR, ← hφQ, rootCenterAut_map φ, h.rootCenterAut_eq_autCentralizer Q]
  have hΦsymm : ∀ (σ : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) (k : K),
      (MulAut.congr φ).symm σ k = φ.symm (σ (φ k)) := fun σ k => by
    simp [MulAut.congr_symm_apply]
  have hΦapp : ∀ (σ : MulAut K) (k : K), (MulAut.congr φ) σ (φ k) = φ (σ k) := fun σ k => by
    simp [MulAut.congr_apply]
  have hΦconj : ∀ x : K, (MulAut.congr φ) (MulAut.conj x) = MulAut.conj (φ x) := fun x => by
    ext y
    simp [MulAut.congr_apply, MulAut.conj_apply]
  set F : Subgroup K := (torusP J hJ).map φ.symm.toMonoidHom with hFdef
  set I : Subgroup K := (sublineP J hJ).map φ.symm.toMonoidHom with hIdef
  have hmemF : ∀ y : K, y ∈ F ↔ φ y ∈ torusP J hJ := fun y => by
    rw [hFdef, Subgroup.mem_map_equiv]
    simp
  have hmemI : ∀ y : K, y ∈ I ↔ φ y ∈ sublineP J hJ := fun y => by
    rw [hIdef, Subgroup.mem_map_equiv]
    simp
  have hFle : F ≤ cartan (Q : Subgroup K) t := by
    intro y hy
    have h1 : φ y ∈ unitaryCoverTorus J hJ := torusP_le_unitaryCoverTorus J hJ ((hmemF y).mp hy)
    rw [← hφD] at h1
    obtain ⟨d, hd, hdy⟩ := h1
    have : d = y := φ.injective hdy
    rwa [← this]
  have hFcard : Nat.card F = e := by
    rw [hFdef, Subgroup.card_map_of_injective φ.symm.injective,
      card_torusP J hJ n hn hcard hfixed, he]
  have hD₂ : fixCartan (Q : Subgroup K) t = F :=
    eq_of_card_eq_of_cyclic hct.isCyclic (fixCartan_le_cartan _ t) hFle
      (by rw [hct.card_fixCartan, hFcard])
  have hmemFI : ∀ y : K, y ∈ F ⊔ I ↔ φ y ∈ sublineP J hJ ⊔ torusP J hJ := fun y => by
    rw [hFdef, hIdef, ← Subgroup.map_sup, Subgroup.mem_map_equiv, sup_comm]
    simp
  obtain ⟨eI⟩ := nonempty_sublineP_equiv J hJ n hn hcard hfixed
  have hIiso : Nonempty (I ≃* PSL2Model n) :=
    ⟨((Subgroup.equivMapOfInjective _ φ.symm.toMonoidHom φ.symm.injective).symm).trans eI⟩
  have hZI : rootCenter (Q : Subgroup K) ≤ I := by
    intro z hz
    have h1 : φ z ∈ rootCenter (unitaryCoverRoot J hJ) := by
      rw [hZR]
      exact ⟨z, hz, rfl⟩
    exact (hmemI z).mpr (rootCenter_le_sublineP J hJ n hn hcard hfixed h1)
  have hcentral : ∀ x ∈ F, x ≠ 1 → ∀ z : K, x * z = z * x ↔ z ∈ F ⊔ I := by
    intro x hx hx1 z
    have hφx : φ x ∈ torusP J hJ := (hmemF x).mp hx
    have hφx1 : φ x ≠ 1 := fun h1 => hx1 (φ.injective (by rw [h1, map_one]))
    rw [hmemFI z, ← mul_comm_iff_mem_sup_of_mem_torusP J hJ n hn hcard hfixed hφx hφx1 (φ z),
      ← map_mul, ← map_mul]
    exact ⟨fun h1 => by rw [h1], fun h1 => φ.injective h1⟩
  set D₃ : Subgroup (MulAut K) := (diagHom J hJ).range.map (MulAut.congr φ).symm.toMonoidHom with hD₃def
  have hmemD₃ : ∀ σ : MulAut K, σ ∈ D₃ ↔ (MulAut.congr φ) σ ∈ (diagHom J hJ).range := fun σ => by
    rw [hD₃def, Subgroup.mem_map_equiv]
    simp
  have hq : 2 < 2 ^ n := lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right two_pos hn)
  have hM : Nat.card (normOne J) = 2 ^ n + 1 := card_normOne Nat.prime_two hq hcard hfixed
  have hconjapp : ∀ (ρ : K) (σ : MulAut K) (k : K),
      (MulAut.conj ρ * σ * (MulAut.conj ρ)⁻¹) (ρ * k * ρ⁻¹) = ρ * σ k * ρ⁻¹ := by
    intro ρ σ k
    simp [MulAut.mul_apply, MulAut.conj_apply]
    group
  have hH : ∀ δ ∈ D₃, ∀ k ∈ F ⊔ I, δ k = k := by
    intro δ hδ k hk
    obtain ⟨c, hc⟩ := (hmemD₃ δ).mp hδ
    apply φ.injective
    rw [← hΦapp δ k, ← hc]
    exact diagAut_fixed_of_mem J hJ c ((hmemFI k).mp hk)
  have hI : ∀ δ ∈ D₃, δ ≠ 1 → ∀ k : K, δ k = k → k ∈ F ⊔ I := by
    intro δ hδ hδ1 k hk
    obtain ⟨c, hc⟩ := (hmemD₃ δ).mp hδ
    have hc1 : c ≠ 1 := by
      rintro rfl
      apply hδ1
      have : (MulAut.congr φ) δ = 1 := by rw [← hc, map_one]
      exact (MulAut.congr φ).injective (by rw [this, map_one])
    rw [hmemFI]
    refine (diagAut_fixed_iff J hJ n hn hcard hfixed hc1 (φ k)).mp ?_
    calc diagAut J hJ c (φ k) = (MulAut.congr φ) δ (φ k) := by rw [← hc]; rfl
      _ = φ (δ k) := hΦapp δ k
      _ = φ k := by rw [hk]
  have hSZ : ∀ A : Subgroup (MulAut K), A ≤ autCentralizer (rootCenter (Q : Subgroup K)) →
      Odd (Nat.card A) →
      ∃ ρ ∈ (Q : Subgroup K), ∀ σ ∈ A, MulAut.conj ρ * σ * (MulAut.conj ρ)⁻¹ ∈ D₃ := by
    intro A hA hodd
    have hA_P : A.map (MulAut.congr φ).toMonoidHom ≤
        rootCenterAut (unitaryCoverRoot J hJ) (unitaryRootCenter J hJ) := by
      rw [hAut]
      exact Subgroup.map_mono hA
    have hodd_P : Odd (Nat.card (A.map (MulAut.congr φ).toMonoidHom)) := by
      rwa [Subgroup.card_map_of_injective (MulAut.congr φ).injective]
    obtain ⟨r, hr, hconj⟩ := exists_conj_diag_of_odd J hJ n hn hcard hfixed _ hA_P hodd_P
    have hρ : φ.symm r ∈ (Q : Subgroup K) := by
      have : r ∈ (Q : Subgroup K).map φ.toMonoidHom := by rw [hφQ]; exact hr
      obtain ⟨q, hq', rfl⟩ := this
      show φ.symm (φ q) ∈ (Q : Subgroup K)
      rw [MulEquiv.symm_apply_apply]
      exact hq'
    refine ⟨φ.symm r, hρ, fun σ hσ => ?_⟩
    rw [hmemD₃, map_mul, map_mul, map_inv, hΦconj]
    simpa using hconj ((MulAut.congr φ) σ) ⟨σ, hσ, rfl⟩
  refine ⟨t, I, D₃, hct.sq_eq_one, hct.not_mem, hIiso, hZI, ?_⟩
  rw [hD₂]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hH, hI, hSZ, ?_⟩
  ·
    rw [hFdef, hIdef, ← Subgroup.map_inf_eq _ _ _ φ.symm.injective, inf_comm,
      sublineP_inf_torusP J hJ, Subgroup.map_bot]
  ·
    intro x hx y hy
    apply φ.injective
    rw [map_mul, map_mul]
    exact (sublineP_commute_torusP J hJ (φ y) ((hmemI y).mp hy) (φ x) ((hmemF x).mp hx)).symm
  ·
    intro x hx hx1
    ext z
    rw [Subgroup.mem_centralizer_singleton_iff, eq_comm, hcentral x hx hx1 z]
  ·
    have h1 : IsCyclic (diagHom J hJ).range :=
      isCyclic_of_surjective (diagHom J hJ).rangeRestrict (MonoidHom.rangeRestrict_surjective _)
    exact isCyclic_of_surjective
      (Subgroup.equivMapOfInjective _ (MulAut.congr φ).symm.toMonoidHom (MulAut.congr φ).symm.injective).toMonoidHom
      (Equiv.surjective _)
  ·
    rw [hD₃def, Subgroup.card_map_of_injective (MulAut.congr φ).symm.injective, ← hM]
    exact (Nat.card_congr
      (MonoidHom.ofInjective (diagHom_injective J hJ n hn hcard hfixed)).toEquiv).symm
  ·
    intro σ hσ z hz
    obtain ⟨c, hc⟩ := (hmemD₃ σ).mp hσ
    have hz' : φ z ∈ unitaryRootCenter J hJ := by
      rw [hUR]
      exact ⟨z, hz, rfl⟩
    apply φ.injective
    rw [← hΦapp σ z, ← hc]
    exact (diagAut_mem_rootCenterAut J hJ c).2 (φ z) hz'
  ·
    intro x hx
    rw [hmemD₃]
    obtain ⟨c, hc⟩ := (mem_torusP_iff J hJ).mp ((hmemF x).mp hx)
    refine ⟨(c ^ 3)⁻¹, ?_⟩
    rw [diagHom_apply, ← conj_psuMk_torusHom J hJ c, hc, hΦconj]
  ·
    intro A hA hodd hA1
    obtain ⟨ρ, hρ, hρD⟩ := hSZ A hA hodd
    obtain ⟨σ₀, hσ₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA1
    refine ⟨ρ, hρ, fun k => ⟨fun hk => ?_, fun hk σ hσ => ?_⟩⟩
    · have hne : MulAut.conj ρ * (σ₀ : MulAut K) * (MulAut.conj ρ)⁻¹ ≠ 1 := by
        intro h1
        apply hσ₀1
        apply Subtype.ext
        calc (σ₀ : MulAut K) = (MulAut.conj ρ)⁻¹ *
            (MulAut.conj ρ * (σ₀ : MulAut K) * (MulAut.conj ρ)⁻¹) * MulAut.conj ρ := by group
          _ = 1 := by rw [h1]; group
      exact hI _ (hρD σ₀ σ₀.2) hne (ρ * k * ρ⁻¹) (by rw [hconjapp, hk σ₀ σ₀.2])
    · have h1 := hH _ (hρD σ hσ) (ρ * k * ρ⁻¹) hk
      rw [hconjapp] at h1
      have h2 : σ k = k := by
        have := mul_left_cancel (mul_right_cancel h1)
        exact this
      exact h2

end Main

end CFSG.GH74.Uniqueness.Bender
