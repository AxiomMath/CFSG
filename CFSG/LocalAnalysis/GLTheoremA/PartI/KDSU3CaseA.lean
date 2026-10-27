module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.KDSU3Base
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KDSU3Fix
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KDSU3Stab

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag Matrix

variable {n : ℕ} {K : Type} [Field K]

theorem exists_stabilizer_data (h : UnitaryFieldData 2 n K) (g : GL (Fin 3) K)
    (hg : g ∈ primeFormUnitary h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
    (hg2 : g * g = 1) (hg1 : g ≠ 1) :
    ∃ (St : Subgroup (GL (Fin 3) K)) (ψ : St →* Kˣ),
      St ≤ primeFormUnitary h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ∧
      g ∈ St ∧
      (∀ c : Kˣ, h.norm (c : K) = 1 →
        ∃ hs : GeneralLinearGroup.scalar (Fin 3) c ∈ St,
          ψ ⟨GeneralLinearGroup.scalar (Fin 3) c, hs⟩ = 1) ∧
      (∀ A ∈ primeFormUnitary h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K),
        A * g * A⁻¹ ∈ St → A ∈ St) ∧
      (∀ A : St, ψ A = 1 → ∃ ν : Kˣ, h.norm (ν : K) = 1 ∧
        (A : GL (Fin 3) K) ^ 4 = GeneralLinearGroup.scalar (Fin 3) (ν ^ 4)) := by
  obtain ⟨w, hw0, hwiso, hgw, huniq⟩ := exists_fixed_isotropic h g hg hg2 hg1
  obtain ⟨St, ψ, hSt, hscal, hker⟩ := exists_stabilizer_hom h w hw0 hwiso
  refine ⟨St, ψ, fun A hA => ((hSt A).1 hA).1, (hSt g).2 ⟨hg, 1, by rw [hgw, one_smul]⟩, hscal,
    ?_, hker⟩
  intro A hA hAg
  obtain ⟨-, μ, hμ⟩ := (hSt _).1 hAg
  have hAinv : (A⁻¹ : GL (Fin 3) K) ∈ primeFormUnitary h
      ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := inv_mem hA
  set v : Fin 3 → K := ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w with hv
  have hAA : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hAA' : ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hv0 : v ≠ 0 := by
    intro h0
    apply hw0
    have := congrArg (fun x => ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ x) h0
    simpa [hv, Matrix.mulVec_mulVec, hAA] using this
  have hviso : gramForm h (1 : Matrix (Fin 3) (Fin 3) K) v v = 0 := by
    have := (gramForm_isometry_iff h (1 : Matrix (Fin 3) (Fin 3) K) _).2
      (mem_primeFormUnitary.1 hAinv) w w
    rw [hv, this]
    exact hwiso
  have hgv : (g : Matrix (Fin 3) (Fin 3) K) *ᵥ v = μ • v := by
    have h1 : ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
        ((((A * g * A⁻¹ : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) *ᵥ w) =
        ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ (μ • w) := by rw [hμ]
    have h2 : ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        (((A * g * A⁻¹ : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) =
        (g : Matrix (Fin 3) (Fin 3) K) * ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      rw [Units.val_mul, Units.val_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hAA',
        Matrix.one_mul]
    rw [Matrix.mulVec_mulVec, h2, Matrix.mulVec_smul, ← Matrix.mulVec_mulVec] at h1
    exact h1
  obtain ⟨c, hc⟩ := huniq v hv0 hviso μ hgv
  have h3 : w = c • (((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w) := by
    have := congrArg (fun x => ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ x) hc
    simp only [hv, Matrix.mulVec_mulVec, hAA, Matrix.one_mulVec, Matrix.mulVec_smul] at this
    exact this
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hw0
    simpa using h3
  refine (hSt A).2 ⟨hA, c⁻¹, ?_⟩
  calc ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w
      = c⁻¹ • (c • (((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w)) := by
        rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
    _ = c⁻¹ • w := by rw [← h3]




theorem card_dvd_of_hom {G M L : Type*} [Group G] [Group M] [Group L] [Finite M]
    (c : G →* M) (E : Subgroup M) (hE : IsPGroup 3 E) (hrange : E ≤ c.range)
    (ψ : E.comap c →* L)
    (hker : ∀ a : E.comap c, c a = 1 → ψ a = 1)
    (hψ : ∀ a : E.comap c, ψ a = 1 → (c a) ^ 4 = 1) :
    ∃ θ : E →* L, Function.Injective θ := by
  classical
  let s : E.comap c →* E :=
    (c.comp (E.comap c).subtype).codRestrict E (fun a => a.2)
  have hs : Function.Surjective s := by
    intro e
    obtain ⟨a, ha⟩ := hrange e.2
    exact ⟨⟨a, by rw [Subgroup.mem_comap, ha]; exact e.2⟩, Subtype.ext ha⟩
  have hker' : s.ker ≤ ψ.ker := by
    intro a ha
    rw [MonoidHom.mem_ker] at ha ⊢
    apply hker
    exact congrArg Subtype.val ha
  let θ : E →* L := MonoidHom.liftOfRightInverse s (Function.surjInv hs)
    (Function.rightInverse_surjInv hs) ⟨ψ, hker'⟩
  have hθ : ∀ a, θ (s a) = ψ a := fun a => by
    simp only [θ]
    exact DFunLike.congr_fun (MonoidHom.liftOfRightInverse_comp s (Function.surjInv hs)
      (Function.rightInverse_surjInv hs) ⟨ψ, hker'⟩) a
  refine ⟨θ, (injective_iff_map_eq_one θ).2 fun e he => ?_⟩
  obtain ⟨a, rfl⟩ := hs e
  rw [hθ] at he
  have h4 := hψ a he
  have h4' : (s a) ^ 4 = 1 := Subtype.ext (by
    change (c a) ^ 4 = 1
    exact h4)
  obtain ⟨k, hk⟩ := hE (s a)
  have hd1 : orderOf (s a) ∣ 4 := orderOf_dvd_of_pow_eq_one h4'
  have hd2 : orderOf (s a) ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk
  have hcop : Nat.Coprime (3 ^ k) 4 := by
    apply Nat.Coprime.pow_left
    norm_num
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hd2 hd1)

theorem caseA_core (h : UnitaryFieldData 2 n K) (hodd : n % 2 = 1) (h1 : 1 < n)
    (h3 : n % 3 ≠ 0) (E T : Subgroup (MulAut (pI h))) (hE : IsPGroup 3 E) (hT : IsPGroup 2 T)
    (hTD : T ⊓ primeFormD h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ≠ ⊥)
    (hnorm : E ≤ Subgroup.normalizer (T : Set (MulAut (pI h)))) :
    Nat.card E ≤ 3 := by
  classical
  have : Finite K := h.finite
  have hq := hq_aux h1
  have hED := le_primeFormD_of_isPGroup_three h h1 h3 E hE
  set T₀ := T ⊓ primeFormD h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hT₀
  have hT₀2 : IsPGroup 2 T₀ := hT.to_le inf_le_left
  haveI : Nontrivial T₀ := (Subgroup.nontrivial_iff_ne_bot T₀).2 hTD
  haveI : Nontrivial (Subgroup.center T₀) := hT₀2.center_nontrivial
  have hZ2 : IsPGroup 2 (Subgroup.center T₀) := hT₀2.to_subgroup _
  have hdvd : 2 ∣ Nat.card (Subgroup.center T₀) := by
    obtain ⟨m, hm⟩ := hZ2.exists_card_eq
    have h1lt : 1 < Nat.card (Subgroup.center T₀) := Finite.one_lt_card
    rw [hm] at h1lt ⊢
    have : m ≠ 0 := by
      rintro rfl
      simp at h1lt
    exact dvd_pow_self 2 this
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center T₀) 2 hdvd
  set t : MulAut (pI h) := ((y : T₀) : MulAut (pI h)) with ht
  have htT₀ : t ∈ T₀ := (y : T₀).2
  have htord : orderOf t = 2 := by
    rw [ht, Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact hy
  have htcomm : ∀ s ∈ T₀, s * t = t * s := by
    intro s hs
    have := Subgroup.mem_center_iff.1 y.2 ⟨s, hs⟩
    exact congrArg Subtype.val this
  have htD : t ∈ primeFormD h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := htT₀.2
  have htT : t ∈ T := htT₀.1
  have hφ : primeFormFieldFactor h isPrimeFormGram_one (by norm_num) hq t = RingEquiv.refl K := by
    have := htD
    rw [← ker_primeFormFieldFactor h isPrimeFormGram_one (by norm_num) hq, MonoidHom.mem_ker]
      at this
    exact this
  obtain ⟨s, hs1, hss, hts⟩ := exists_sq_eq_one_of_fieldFactor_eq_one h isPrimeFormGram_one
    (by norm_num) hq t htord hφ
  set g : GL (Fin 3) K := (s : GL (Fin 3) K) with hg
  have hgU : g ∈ primeFormUnitary h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := s.2.1
  obtain ⟨St, ψ, hStU, hgSt, hscal, hcrit, hker⟩ := exists_stabilizer_data h g hgU hss hs1
  set Ψ := primeFormConjHom h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hΨ
  have htΨ : Ψ ⟨g, hgU⟩ = t := hts.symm
  have hcl : ∀ A : primeFormUnitary h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K),
      Ψ A ∈ E → (A : GL (Fin 3) K) ∈ St := by
    intro A hAE
    set g' : GL (Fin 3) K := (A : GL (Fin 3) K) * g * (A : GL (Fin 3) K)⁻¹ with hg'
    have hg'U : g' ∈ primeFormUnitary h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
      mul_mem (mul_mem A.2 hgU) (inv_mem A.2)
    have hΨg' : Ψ ⟨g', hg'U⟩ = Ψ A * t * (Ψ A)⁻¹ := by
      rw [← htΨ, ← map_inv, ← map_mul, ← map_mul]
      rfl
    have hmemT : Ψ ⟨g', hg'U⟩ ∈ T := by
      rw [hΨg']
      exact (Subgroup.mem_normalizer_iff.1 (hnorm hAE) t).1 htT
    have hmemT₀ : Ψ ⟨g', hg'U⟩ ∈ T₀ := ⟨hmemT, ⟨_, rfl⟩⟩
    have hcomm := htcomm _ hmemT₀
    have hΨX : Ψ (⟨g', hg'U⟩ * ⟨g, hgU⟩ * ⟨g', hg'U⟩⁻¹ * ⟨g, hgU⟩⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, htΨ, hcomm]
      group
    have hΨX' : primeFormPsi h isPrimeFormGram_one
        ⟨(⟨g', hg'U⟩ * ⟨g, hgU⟩ * ⟨g', hg'U⟩⁻¹ * ⟨g, hgU⟩⁻¹ :
          primeFormUnitary h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)), 1⟩ = 1 := by
      rw [primeFormPsi_apply, map_one, mul_one]
      exact hΨX
    obtain ⟨-, c, hc, hXc⟩ := (primeFormPsi_eq_one_iff h isPrimeFormGram_one (by norm_num) _).1 hΨX'
    have hXc' : g' * g * g'⁻¹ * g⁻¹ = GeneralLinearGroup.scalar (Fin 3) c := hXc
    have hmem : g' * g * g'⁻¹ ∈ St := by
      have : g' * g * g'⁻¹ = GeneralLinearGroup.scalar (Fin 3) c * g := by
        calc g' * g * g'⁻¹ = (g' * g * g'⁻¹ * g⁻¹) * g := by group
          _ = GeneralLinearGroup.scalar (Fin 3) c * g := by rw [hXc']
      rw [this]
      obtain ⟨hs, -⟩ := hscal c hc
      exact mul_mem hs hgSt
    have hg'St : g' ∈ St := hcrit g' hg'U hmem
    exact hcrit (A : GL (Fin 3) K) A.2 hg'St
  let ι : (E.comap Ψ) →* St := MonoidHom.codRestrict
    ((primeFormUnitary h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)).subtype.comp
      (E.comap Ψ).subtype) St (fun a => hcl a.1 a.2)
  let ψ' : (E.comap Ψ) →* Kˣ := ψ.comp ι
  have hker' : ∀ a : E.comap Ψ, Ψ a = 1 → ψ' a = 1 := by
    intro a ha
    have hΨa : primeFormPsi h isPrimeFormGram_one
        ⟨(a : primeFormUnitary h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)), 1⟩ = 1 := by
      rw [primeFormPsi_apply, map_one, mul_one]
      exact ha
    obtain ⟨-, c, hc, hac⟩ := (primeFormPsi_eq_one_iff h isPrimeFormGram_one (by norm_num) _).1 hΨa
    obtain ⟨hs, hψ1⟩ := hscal c hc
    have : ι a = ⟨GeneralLinearGroup.scalar (Fin 3) c, hs⟩ := Subtype.ext hac
    simp only [ψ', MonoidHom.comp_apply, this, hψ1]
  have hψ' : ∀ a : E.comap Ψ, ψ' a = 1 → (Ψ a) ^ 4 = 1 := by
    intro a ha
    obtain ⟨ν, hν, h4⟩ := hker (ι a) ha
    rw [← map_pow]
    have hν4 : h.norm (((ν ^ 4 : Kˣ)) : K) = 1 := by
      rw [Units.val_pow_eq_pow_val]
      simp only [UnitaryFieldData.norm, map_pow] at hν ⊢
      rw [← mul_pow, hν, one_pow]
    have hΨ4 : primeFormPsi h isPrimeFormGram_one
        ⟨(a : primeFormUnitary h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) ^ 4, 1⟩ = 1 := by
      rw [primeFormPsi_eq_one_iff h isPrimeFormGram_one (by norm_num)]
      exact ⟨rfl, ν ^ 4, hν4, h4⟩
    rw [primeFormPsi_apply, map_one, mul_one] at hΨ4
    exact hΨ4
  obtain ⟨θ, hθ⟩ := card_dvd_of_hom Ψ E hE hED ψ' hker' hψ'
  have hcard : Nat.card E ∣ Nat.card Kˣ := Subgroup.card_dvd_of_injective θ hθ
  have hKcard : Nat.card Kˣ = 4 ^ n - 1 := by
    rw [Nat.card_units, h.card, pow_mul]
    norm_num
  rw [hKcard] at hcard
  exact card_le_three_of_isPGroup_dvd hE (not_nine_dvd_four_pow_sub_one h3) hcard




end CFSG.LocalAnalysis.GLTheoremA
