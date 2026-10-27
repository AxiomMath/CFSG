module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs256g
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2311e2
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUOddAll

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311h

open CFSG.Open CFSG.LieType.SeitzGeneration
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311c (UniPlaneGen uniPlaneClosure
  mem_uniPlaneClosure UniSeitzPlanes)
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256g

theorem ne_two_of_dvd_pow_add_one_of_ne_eight {ℓ f f₀ p : ℕ} (hp : p.Prime) (hf : f = p * f₀)
    (hpq : p ∣ ℓ ^ f + 1) (h8 : ℓ ^ f ≠ 8) : ℓ ^ f₀ ≠ 2 := by
  intro h2
  haveI : Fact p.Prime := ⟨hp⟩
  have hpow : ℓ ^ f = 2 ^ p := by rw [hf, mul_comm, pow_mul, h2]
  rw [hpow] at hpq h8
  have h0 : ((2 ^ p + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hpq
  push_cast at h0
  rw [ZMod.pow_card] at h0
  have h3 : ((3 : ℕ) : ZMod p) = 0 := by
    push_cast
    linear_combination h0
  rw [ZMod.natCast_eq_zero_iff] at h3
  have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h3
  exact h8 (by rw [hp3]; norm_num)

theorem pow_ne_eight_of_dvd_pow_add_one {ℓ f p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3)
    (hpq : p ∣ ℓ ^ f + 1) : ℓ ^ f ≠ 8 := by
  intro h8
  rw [h8] at hpq
  have h9 : p ∣ 3 ^ 2 := by
    show p ∣ 9
    simpa using hpq
  exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h9))

section URad

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.RankThree.PartOne.CTP

variable {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ}

theorem pow_sq_char_eq_one_of_mem_uRad {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    {W : Submodule K (Fin n → K)} {hW : ∀ x ∈ W, ∀ y ∈ W, herm σ x y = 0} {g : SUid σ n}
    (hg : g ∈ uRad σ W hW) : g ^ (ℓ ^ 2) = 1 := by
  obtain ⟨hg1, hg2, hg3⟩ := hg
  have hℓ : ℓ.Prime := Fact.out
  set N : Module.End K (Fin n → K) := actU σ n g - 1 with hNdef
  have hNx : ∀ x, N x = g • x - x := fun x => by
    simp [hNdef, CFSG.LieType.SeitzGeneration.actU_apply]
  have hN3 : N * N * N = 0 := by
    refine LinearMap.ext fun x => ?_
    have h1 : N x ∈ hermOrth σ W := by rw [hNx]; exact hg1 x
    have h2 : N (N x) ∈ W := by rw [hNx]; exact hg2 _ h1
    have h3 : N (N (N x)) = 0 := by rw [hNx, hg3 _ h2, sub_self]
    simpa using h3
  have hg1' : actU σ n g = 1 + N := by rw [hNdef]; abel
  have hℓcast : ((ℓ ^ 2 : ℕ) : K) = 0 := by
    rw [CharP.cast_eq_zero_iff K ℓ]
    exact dvd_pow_self ℓ two_ne_zero
  have hchoose : (((ℓ ^ 2).choose 2 : ℕ) : K) = 0 := by
    rw [CharP.cast_eq_zero_iff K ℓ]
    refine hℓ.dvd_choose_pow two_ne_zero fun h => ?_
    have h4 : 2 ^ 2 ≤ ℓ ^ 2 := Nat.pow_le_pow_left hℓ.two_le 2
    omega
  have hpow : actU σ n (g ^ (ℓ ^ 2)) = 1 := by
    rw [map_pow, hg1', unip_pow_of_cube_eq_zero (K := K) hN3 (ℓ ^ 2), hℓcast, hchoose, zero_smul,
      zero_smul, add_zero, add_zero]
  refine ext_smul σ fun v => ?_
  rw [one_smul]
  exact LinearMap.congr_fun hpow v

end URad

section ParabolicGen

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel CFSG.ClassicalGroups.Unitary
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.RankThree.PartOne.CTP

variable {ℓ f n p : ℕ} {K : Type} [Field K] [Finite K] [Fact ℓ.Prime] [CharP K ℓ]

theorem uniPlaneGen_of_isotropic_anyChar (h : UnitaryFieldData ℓ f K) (hq : ℓ ^ f ≠ 2) (hn : 3 ≤ n)
    (hp : p.Prime) (hpℓ : p ≠ ℓ) {E : Subgroup (MulAut (primeFormP h (idGram K n)))}
    (hE : IsElemAbelian p E) (hc : Nat.card E = p ^ 2) (hD : E ≤ primeFormD h (idGram K n))
    {W : Submodule K (Fin n → K)} (hW0 : W ≠ ⊥)
    (hWiso : ∀ x ∈ W, ∀ y ∈ W, herm (unitaryInvolution K ℓ f) x y = 0)
    (hWs : ∀ A : primeFormUnitary h (idGram K n), primeFormConjHom h (idGram K n) A ∈ E →
      ∀ w ∈ W, ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W) :
    UniPlaneGen ℓ E := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  set σ := unitaryInvolution K ℓ f with hσdef
  have hσ : IsUnitaryInvolution σ := Nonsplit.isUnitaryInvolution h
  have hiso : ∀ A : primeFormUnitary h (idGram K n), ∀ x y,
      herm σ (((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x)
        (((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ y) = herm σ x y := by
    intro A x y
    have := mem_sesqUnitaryGroup.mp ((toLin_mem_sesqUnitaryGroup_iff (A : GL (Fin n) K)).mpr A.2) x y
    rw [Nonsplit.idForm_eq_herm h, Nonsplit.idForm_eq_herm h] at this
    simpa [Matrix.toLin'_apply] using this
  set Ag : Subgroup (GL (Fin n) K) := (E.comap (primeFormConjHom h (idGram K n))).map
    (primeFormUnitary h (idGram K n)).subtype with hAg
  have hAiso : ∀ g ∈ Ag, ∀ x y, herm σ (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x)
      (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ y) = herm σ x y := by
    rintro _ ⟨A, -, rfl⟩ x y
    exact hiso A x y
  have hAs : ∀ g ∈ Ag, ∀ w ∈ W, ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W := by
    rintro _ ⟨A, hA, rfl⟩ w hw
    exact hWs A hA w hw
  obtain ⟨W', hW'iso, hcompl, hW's⟩ := exists_opposite_gl hσ
    (natCast_card_lifts_ne_zero h hn hp hpℓ hE.2) hAiso hWiso hAs
  have hW's' : ∀ A : primeFormUnitary h (idGram K n), primeFormConjHom h (idGram K n) A ∈ E →
      ∀ w ∈ W', ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W' :=
    fun A hA w hw => hW's _ ⟨A, hA, rfl⟩ w hw
  have hconj : ∀ {X : Submodule K (Fin n → K)} (hX : ∀ x ∈ X, ∀ y ∈ X, herm σ x y = 0),
      (∀ A : primeFormUnitary h (idGram K n), primeFormConjHom h (idGram K n) A ∈ E →
        ∀ w ∈ X, ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ X) →
      ∀ e ∈ E, ∀ s ∈ (uRad σ X hX).map (suP h), e s ∈ (uRad σ X hX).map (suP h) := by
    intro X hX hXs e he s hs
    obtain ⟨A, rfl⟩ := hD he
    obtain ⟨g, hg, rfl⟩ := hs
    have hmem : (A : GL (Fin n) K) * (g : GL (Fin n) K) * (A : GL (Fin n) K)⁻¹ ∈
        SUid (unitaryInvolution K ℓ f) n :=
      (sUid_eq_gramSU h).ge (conj_mem_gramSU h (idGram K n) A.2 ((sUid_eq_gramSU h).le g.2))
    have hAinv : primeFormConjHom h (idGram K n) A⁻¹ ∈ E := by
      rw [map_inv]; exact E.inv_mem he
    have he' : ∀ w ∈ X, ((((A : GL (Fin n) K))⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ X := by
      intro w hw
      rw [← Subgroup.coe_inv]
      exact hXs A⁻¹ hAinv w hw
    refine ⟨⟨_, hmem⟩, uRad_conj_mem_gl (hiso A) (hXs A he) he' hg rfl, ?_⟩
    exact (primeFormConjHom_suP h A g ⟨_, hmem⟩ rfl).symm
  have hr : ∀ {X : Submodule K (Fin n → K)} (hX : ∀ x ∈ X, ∀ y ∈ X, herm σ x y = 0),
      ∀ s ∈ (uRad σ X hX).map (suP h), ∃ m : ℕ, s ^ (ℓ ^ m) = 1 := by
    rintro X hX _ ⟨g, hg, rfl⟩
    refine ⟨2, ?_⟩
    rw [← map_pow, pow_sq_char_eq_one_of_mem_uRad (ℓ := ℓ) hg, map_one]
  have hgen : (uRad σ W hWiso).map (suP h) ⊔ (uRad σ W' hW'iso).map (suP h) = ⊤ := by
    set L := (uRad σ W hWiso).map (suP h) ⊔ (uRad σ W' hW'iso).map (suP h) with hL
    obtain ⟨s₀, hs₀0, hs₀⟩ := Nonsplit.exists_norm_ne_one h hq
    have htop : L.comap (suP h) = ⊤ :=
      eq_top_of_uRad_of_opposite hσ (by omega)
        (fun _ => ⟨s₀, hs₀0, by rw [Nonsplit.unitaryInvolution_eq_bar h]; exact hs₀⟩) hW0 hWiso
        hW'iso hcompl
        (fun q hq => Subgroup.mem_comap.2 (Subgroup.mem_sup_left ⟨q, hq, rfl⟩))
        (fun q hq => Subgroup.mem_comap.2 (Subgroup.mem_sup_right ⟨q, hq, rfl⟩))
    rw [← Subgroup.map_comap_eq_self_of_surjective (suP_surjective h) L, htop,
      Subgroup.map_top_of_surjective _ (suP_surjective h)]
  refine uniPlaneGen_of_rSubgroups hp hℓ hpℓ hE hc
    {(uRad σ W hWiso).map (suP h), (uRad σ W' hW'iso).map (suP h)} ?_ ?_ ?_
  · rintro H (rfl | rfl)
    · exact hr hWiso
    · exact hr hW'iso
  · rintro H (rfl | rfl)
    · exact hconj hWiso hWs
    · exact hconj hW'iso hW's'
  · rw [iSup_insert, iSup_singleton]
    exact hgen

end ParabolicGen

section InnDiag

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel CFSG.ClassicalGroups.Unitary
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

variable {ℓ f n p : ℕ} {K : Type} [Field K] [Finite K] [Fact ℓ.Prime] [CharP K ℓ]

theorem uniPlaneGen_of_pair_anyChar (h : UnitaryFieldData ℓ f K) (hq : ℓ ^ f ≠ 2) (hn : 3 ≤ n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ) (hpq : p ∣ ℓ ^ f + 1)
    {E : Subgroup (MulAut (primeFormP h (idGram K n)))} (hE : IsElemAbelian p E)
    (hc : Nat.card E = p ^ 2) (hD : E ≤ primeFormD h (idGram K n))
    (X Y : primeFormUnitary h (idGram K n))
    (hXE : primeFormConjHom h (idGram K n) X ∈ E) (hYE : primeFormConjHom h (idGram K n) Y ∈ E)
    (hind : ∀ i j : ℕ, (primeFormConjHom h (idGram K n) X) ^ i *
      (primeFormConjHom h (idGram K n) Y) ^ j = 1 → p ∣ i ∧ p ∣ j)
    {α c : K} (hα : α ≠ 0)
    (hXp : ((((X : GL (Fin n) K)) ^ p : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = α • 1)
    (hYp : (Y : GL (Fin n) K) ^ p = 1)
    (hYX : ((Y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      c • (((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((Y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) :
    UniPlaneGen ℓ E ∨ (n = p ∧ X * Y ≠ Y * X) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hn0 : 0 < n := by omega
  have hp1 : ¬ p ∣ 1 := fun hd => hp.one_lt.ne' (Nat.dvd_one.mp hd)
  set H := (uniPlaneClosure ℓ E).comap (suP h) with hHdef
  by_cases hc1 : c = 1
  · subst hc1
    have hcomm : (X : GL (Fin n) K) * Y = Y * X :=
      Units.ext (by rw [Units.val_mul, Units.val_mul, hYX, one_smul])
    by_cases hμ : ∃ μ : K, μ ^ p = α
    ·
      obtain ⟨μ, hμp⟩ := hμ
      have hμ0 : μ ≠ 0 := by
        rintro rfl
        rw [zero_pow hp.ne_zero] at hμp
        exact hα hμp.symm
      have hαN : h.bar α * α = 1 := bar_mul_eq_one_of_scalar_pow h (by omega) X.2 hXp
      have hμN : h.bar μ * μ = 1 :=
        bar_mul_eq_one_of_pow_eq h hp hp2 hpq hμ0 hμp (planeW_pow_card_succ h hαN)
      set u : Kˣ := Units.mk0 μ⁻¹ (inv_ne_zero hμ0) with hu
      have huN : h.norm (u : K) = 1 := by
        rw [UnitaryFieldData.norm, hu, Units.val_mk0, map_inv₀, ← mul_inv, mul_comm, hμN, inv_one]
      set X' : primeFormUnitary h (idGram K n) :=
        ⟨Matrix.GeneralLinearGroup.scalar (Fin n) u * X,
          mul_mem (scalar_mem_primeFormUnitary h huN) X.2⟩ with hX'
      have hX'M : ((X' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
          μ⁻¹ • ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
        simp only [hX', Units.val_mul, coe_scalar_gl, Matrix.smul_mul, Matrix.one_mul, hu,
          Units.val_mk0]
      have hcX' : primeFormConjHom h (idGram K n) X' = primeFormConjHom h (idGram K n) X := by
        have h1 : X' = ⟨_, scalar_mem_primeFormUnitary h huN⟩ * X := rfl
        rw [h1, map_mul, conj_scalar_eq_one h _ rfl, one_mul]
      have hXM : ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = α • 1 := by
        rw [← Units.val_pow_eq_pow_val]; exact hXp
      have hX'p : (X' : GL (Fin n) K) ^ p = 1 := by
        apply Units.ext
        rw [Units.val_pow_eq_pow_val, hX'M, smul_pow, hXM, smul_smul, inv_pow, hμp,
          inv_mul_cancel₀ hα, one_smul, Units.val_one]
      have hX'Y : (X' : GL (Fin n) K) * Y = Y * X' := by
        show Matrix.GeneralLinearGroup.scalar (Fin n) u * (X : GL (Fin n) K) * Y =
          Y * (Matrix.GeneralLinearGroup.scalar (Fin n) u * X)
        calc Matrix.GeneralLinearGroup.scalar (Fin n) u * (X : GL (Fin n) K) * Y
            = Matrix.GeneralLinearGroup.scalar (Fin n) u * ((X : GL (Fin n) K) * Y) := mul_assoc _ _ _
          _ = Matrix.GeneralLinearGroup.scalar (Fin n) u * ((Y : GL (Fin n) K) * X) := by rw [hcomm]
          _ = (Matrix.GeneralLinearGroup.scalar (Fin n) u * (Y : GL (Fin n) K)) * X :=
              (mul_assoc _ _ _).symm
          _ = ((Y : GL (Fin n) K) * Matrix.GeneralLinearGroup.scalar (Fin n) u) * X := by
              rw [(commute_scalar u (Y : GL (Fin n) K)).eq]
          _ = (Y : GL (Fin n) K) * (Matrix.GeneralLinearGroup.scalar (Fin n) u * X) := mul_assoc _ _ _
      have hind' : ∀ i j : ℕ, (primeFormConjHom h (idGram K n) X') ^ i *
          (primeFormConjHom h (idGram K n) Y) ^ j = 1 → p ∣ i ∧ p ∣ j := by
        rw [hcX']; exact hind
      have hindGL : ∀ a b : ℕ, (X' : GL (Fin n) K) ^ a * (Y : GL (Fin n) K) ^ b = 1 →
          p ∣ a ∧ p ∣ b := by
        intro a b hab
        apply hind' a b
        have h1 : X' ^ a * Y ^ b = 1 := Subtype.ext (by
          simpa only [Subgroup.coe_mul, SubgroupClass.coe_pow, OneMemClass.coe_one] using hab)
        rw [← map_pow, ← map_pow, ← map_mul, h1, map_one]
      left
      exact uniPlaneGen_of_comap_eq_top h (eq_top_of_abelian_pth_r h hp hpq hq (by omega) X'.2 Y.2
        hX'Y hX'p hYp hindGL (fun a b hab => rcent_word h (hcX' ▸ hXE) hYE hind' a b hab))
    ·
      have hY1 : ∀ c' : K, ((Y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ≠ c' • 1 := by
        intro c' hc'
        have hc'0 : c' ≠ 0 := by
          rintro rfl
          have h1 : (((Y : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
              ((Y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
            rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
          rw [hc', zero_smul, Matrix.mul_zero] at h1
          exact zero_ne_one (congrFun (congrFun h1 ⟨0, hn0⟩) ⟨0, hn0⟩)
        have hYs : (Y : GL (Fin n) K) = Matrix.GeneralLinearGroup.scalar (Fin n) (Units.mk0 c' hc'0) :=
          Units.ext (by rw [coe_scalar_gl, Units.val_mk0, hc'])
        exact hp1 (hind 0 1 (by rw [conj_scalar_eq_one h Y hYs]; simp)).2
      have hYp' : ((((Y : GL (Fin n) K)) ^ p : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
        rw [hYp, Units.val_one]
      have hcX : RCent H ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
        have := rcent_word h hXE hYE hind 1 0 (fun hd => hp1 hd.1)
        simpa using this
      have hcY : RCent H ((Y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
        have := rcent_word h hXE hYE hind 0 1 (fun hd => hp1 hd.2)
        simpa using this
      left
      exact uniPlaneGen_of_comap_eq_top h (eq_top_of_nonpth_pair_r h hp hp2 hpq hq X.2 Y.2 hcomm hXp
        hμ hYp' hY1 hcX hcY)
  · by_cases hnp : n = p
    · right
      refine ⟨hnp, fun hXY => hc1 ?_⟩
      have h1 : ((Y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
          ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            ((Y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
        rw [← Units.val_mul, ← Units.val_mul]
        exact congrArg (fun g : primeFormUnitary h (idGram K n) => ((g : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K)) hXY.symm
      rw [hYX] at h1
      have hM : ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((Y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ≠ 0 := by
        intro h0
        have h2 : (((X * Y : GL (Fin n) K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            ((((X * Y : GL (Fin n) K))⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
          rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
        rw [Units.val_mul, h0, Matrix.zero_mul] at h2
        exact zero_ne_one (congrFun (congrFun h2 ⟨0, hn0⟩) ⟨0, hn0⟩)
      have h3 : (c - 1) • (((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((Y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) = 0 := by
        rw [sub_smul, one_smul, h1, sub_self]
      exact sub_eq_zero.1 ((smul_eq_zero.1 h3).resolve_right hM)
    · left
      obtain ⟨W, hW0, hWiso, hWX, hWY⟩ :=
        exists_isotropic_of_heis h hp hpq hn hnp X.2 Y.2 hα hXp hYp hYX hc1
      refine uniPlaneGen_of_isotropic_anyChar h hq hn hp hpℓ hE hc hD hW0 hWiso ?_
      intro A hA
      let S : Subgroup (primeFormUnitary h (idGram K n)) :=
        (CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256e.stabSubGL' W).comap
          (primeFormUnitary h (idGram K n)).subtype
      have hcXp : (primeFormConjHom h (idGram K n) X) ^ p = 1 := hE.2 _ hXE
      have hgen : Subgroup.zpowers (primeFormConjHom h (idGram K n) X) ⊔
          Subgroup.zpowers (primeFormConjHom h (idGram K n) Y) = E :=
        zpowers_sup_zpowers_eq_of_card_sq hp hE.2 hc hXE (ne_one_of_indep hp hind) hYE
          (notMem_zpowers_of_indep hp hcXp hind)
      have hS : ∀ B, primeFormConjHom h (idGram K n) B = 1 → B ∈ S := by
        intro B hB
        obtain ⟨u, -, hu⟩ := eq_scalar_of_conj_eq_one h hn B hB
        refine ⟨fun w hw => ?_, fun w hw => ?_⟩
        · show ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W
          rw [hu, coe_scalar_gl, Matrix.smul_mulVec, Matrix.one_mulVec]
          exact W.smul_mem _ hw
        · show ((((B : GL (Fin n) K))⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W
          rw [hu, ← map_inv, coe_scalar_gl, Matrix.smul_mulVec, Matrix.one_mulVec]
          exact W.smul_mem _ hw
      have hXs : X ∈ S := by
        have hXp' : (X : GL (Fin n) K) ^ p =
            Matrix.GeneralLinearGroup.scalar (Fin n) (Units.mk0 α hα) :=
          Units.ext (by rw [hXp, coe_scalar_gl, Units.val_mk0])
        exact ⟨hWX, inv_mulVec_mem_of_pow_scalar hp.pos hXp' hWX⟩
      have hYs : Y ∈ S := by
        have hYp' : (Y : GL (Fin n) K) ^ p = Matrix.GeneralLinearGroup.scalar (Fin n) 1 := by
          rw [hYp, map_one]
        exact ⟨hWY, inv_mulVec_mem_of_pow_scalar hp.pos hYp' hWY⟩
      exact (mem_of_conj_mem_of_sup_eq h hgen hS hXs hYs hA).1

theorem uniPlaneGen_inndiag_anyChar (h : UnitaryFieldData ℓ f K) (hq : ℓ ^ f ≠ 2) (hn : 3 ≤ n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ) (hpq : p ∣ ℓ ^ f + 1)
    {E : Subgroup (MulAut (primeFormP h (idGram K n)))} (hE : IsElemAbelian p E)
    (hc : Nat.card E = p ^ 2) (hD : E ≤ primeFormD h (idGram K n)) :
    UniPlaneGen ℓ E ∨ (n = p ∧ ∃ A B : primeFormUnitary h (idGram K n),
      primeFormConjHom h (idGram K n) A ∈ E ∧ primeFormConjHom h (idGram K n) B ∈ E ∧
        A * B ≠ B * A) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hn0 : 0 < n := by omega
  obtain ⟨x, hxE, y, hyE, hy1, hxy⟩ := exists_independent_pair hp E hE.2 hc
  obtain ⟨A, rfl⟩ := hD hxE
  obtain ⟨B, rfl⟩ := hD hyE
  set cA := primeFormConjHom h (idGram K n) A with hcA
  set cB := primeFormConjHom h (idGram K n) B with hcB
  obtain ⟨α, hα, hAp⟩ := exists_pow_eq_smul_of_conj h hn A (hE.2 _ hxE)
  obtain ⟨β, hβ, hBp⟩ := exists_pow_eq_smul_of_conj h hn B (hE.2 _ hyE)
  have hcomm : cA * cB = cB * cA :=
    congrArg Subtype.val (hE.1.is_comm.comm ⟨_, hxE⟩ ⟨_, hyE⟩)
  obtain ⟨c, hBA⟩ := exists_smul_comm_of_conj h hn A B hcomm
  have hcp : c ^ p = 1 := pow_eq_one_of_smul_comm_p hn0 hα hAp hBA
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hcp
    exact zero_ne_one hcp
  have hindAB : ∀ i j : ℕ, cA ^ i * cB ^ j = 1 → p ∣ i ∧ p ∣ j := fun i j hij =>
    dvd_of_pow_mul_pow_eq_one_p hp (hE.2 _ hxE) (hE.2 _ hyE) hy1 hxy hij
  have hcAB : Commute cA cB := hcomm
  have hpK : p ∣ Nat.card K - 1 := by
    have hl : 0 < ℓ := (Fact.out : ℓ.Prime).pos
    have hq1 : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ hl
    have key : (ℓ ^ f) ^ 2 - 1 = (ℓ ^ f + 1) * (ℓ ^ f - 1) := by
      have h2 : 1 ≤ (ℓ ^ f) ^ 2 := Nat.one_le_pow _ _ (pow_pos hl _)
      zify [hq1, h2]
      ring
    rw [h.card_eq_sq, key]
    exact Dvd.dvd.mul_right hpq _
  obtain ⟨a, b, hab, ν, hν⟩ := exists_pth_power_word hp hpK hα hβ
  have hν0 : ν ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hν
    exact mul_ne_zero (pow_ne_zero _ hα) (pow_ne_zero _ hβ) hν.symm
  have hαN : h.bar α * α = 1 := bar_mul_eq_one_of_scalar_pow h (by omega) A.2 hAp
  have hβN : h.bar β * β = 1 := bar_mul_eq_one_of_scalar_pow h (by omega) B.2 hBp
  have hαβN : (α ^ a * β ^ b) ^ (ℓ ^ f + 1) = 1 := by
    rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm a, mul_comm b, pow_mul, pow_mul,
      planeW_pow_card_succ h hαN, planeW_pow_card_succ h hβN, one_pow, one_pow, one_mul]
  have hνN : h.bar ν * ν = 1 := bar_mul_eq_one_of_pow_eq h hp hp2 hpq hν0 hν hαβN
  set u : Kˣ := Units.mk0 ν⁻¹ (inv_ne_zero hν0) with hu
  have huN : h.norm (u : K) = 1 := by
    rw [UnitaryFieldData.norm, hu, Units.val_mk0, map_inv₀, ← mul_inv, mul_comm, hνN, inv_one]
  set S : primeFormUnitary h (idGram K n) :=
    ⟨Matrix.GeneralLinearGroup.scalar (Fin n) u, scalar_mem_primeFormUnitary h huN⟩ with hS
  have hcS : primeFormConjHom h (idGram K n) S = 1 := conj_scalar_eq_one h S rfl
  set Y₀ : primeFormUnitary h (idGram K n) := S * (A ^ a * B ^ b) with hY₀
  have hY₀E : primeFormConjHom h (idGram K n) Y₀ ∈ E := by
    rw [hY₀, map_mul, hcS, one_mul, map_mul, map_pow, map_pow]
    exact E.mul_mem (E.pow_mem hxE a) (E.pow_mem hyE b)
  have hcY₀ : primeFormConjHom h (idGram K n) Y₀ = cA ^ a * cB ^ b := by
    rw [hY₀, map_mul, hcS, one_mul, map_mul, map_pow, map_pow]
  have hAM : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = α • 1 := by
    rw [← Units.val_pow_eq_pow_val]; exact hAp
  have hBM : ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = β • 1 := by
    rw [← Units.val_pow_eq_pow_val]; exact hBp
  have hY₀M : ((Y₀ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ν⁻¹ • (((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ a *
        ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ b) := by
    simp only [hY₀, hS, Subgroup.coe_mul, SubgroupClass.coe_pow, Units.val_mul,
      Units.val_pow_eq_pow_val, coe_scalar_gl, hu, Units.val_mk0, Matrix.smul_mul, Matrix.one_mul]
  have hY₀p : (Y₀ : GL (Fin n) K) ^ p = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hY₀M, smul_pow, pow_word_p hp hp2 hAM hBM hBA hcp a b, ← hν,
      smul_smul, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hν0), one_smul, Units.val_one]
  by_cases hpb : p ∣ b
  ·
    have hpa : ¬ p ∣ a := fun hpa => hab ⟨hpa, hpb⟩
    have hind : ∀ i j : ℕ, cB ^ i * (primeFormConjHom h (idGram K n) Y₀) ^ j = 1 →
        p ∣ i ∧ p ∣ j := by
      intro i j hij
      rw [hcY₀, pow_mul_pow_pow_of_comm hcAB a b j] at hij
      have h1 : cA ^ (a * j) * cB ^ (i + b * j) = 1 := by
        rw [← hij, pow_add]
        calc cA ^ (a * j) * (cB ^ i * cB ^ (b * j)) = cB ^ i * (cA ^ (a * j) * cB ^ (b * j)) := by
              rw [← mul_assoc, ← mul_assoc, ((hcAB.pow_pow (a * j) i).eq)]
          _ = _ := rfl
      obtain ⟨h2, h3⟩ := hindAB _ _ h1
      have hj : p ∣ j := ((Nat.Prime.dvd_mul hp).1 h2).resolve_left hpa
      exact ⟨(Nat.dvd_add_right (dvd_mul_of_dvd_right hj b)).1 (by rw [add_comm]; exact h3), hj⟩
    have hYB : ((Y₀ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        (c ^ a)⁻¹ • (((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((Y₀ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
      rw [hY₀M, Matrix.smul_mul, planeW_comm_caseII hBA hc0 a b, Matrix.mul_smul, smul_comm]
    rcases uniPlaneGen_of_pair_anyChar h hq hn hp hp2 hpℓ hpq hE hc (by exact hD) B Y₀ hyE hY₀E hind hβ hBp hY₀p
        hYB with hU | ⟨hnp, hne⟩
    · exact Or.inl hU
    · exact Or.inr ⟨hnp, B, Y₀, hyE, hY₀E, hne⟩
  ·
    have hind : ∀ i j : ℕ, cA ^ i * (primeFormConjHom h (idGram K n) Y₀) ^ j = 1 →
        p ∣ i ∧ p ∣ j := by
      intro i j hij
      rw [hcY₀, pow_mul_pow_pow_of_comm hcAB a b j, ← mul_assoc, ← pow_add] at hij
      obtain ⟨h2, h3⟩ := hindAB _ _ hij
      have hj : p ∣ j := ((Nat.Prime.dvd_mul hp).1 h3).resolve_left hpb
      exact ⟨(Nat.dvd_add_left (dvd_mul_of_dvd_right hj a)).1 h2, hj⟩
    have hYA : ((Y₀ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        c ^ b • (((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((Y₀ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
      rw [hY₀M, Matrix.smul_mul, planeW_comm_caseI hBA a b, Matrix.mul_smul, smul_comm]
    rcases uniPlaneGen_of_pair_anyChar h hq hn hp hp2 hpℓ hpq hE hc (by exact hD) A Y₀ hxE hY₀E hind hα hAp hY₀p
        hYA with hU | ⟨hnp, hne⟩
    · exact Or.inl hU
    · exact Or.inr ⟨hnp, A, Y₀, hxE, hY₀E, hne⟩

end InnDiag

section FieldOuter

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.Classical CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.LieType.Chevalley CFSG.RankThree.PartOne.CTP

variable {ℓ f n p : ℕ} {K : Type} [Field K] [Finite K] [Fact ℓ.Prime] [CharP K ℓ]

theorem uniPlaneGen_field_outer_anyChar_of_ne_eight_or_four_le (h : UnitaryFieldData ℓ f K)
    (hq : ℓ ^ f ≠ 2) (h8 : ℓ ^ f ≠ 8 ∨ 4 ≤ n) (hpq : p ∣ ℓ ^ f + 1) (hn : 3 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpℓ : p ≠ ℓ)
    {E : Subgroup (MulAut (primeFormP h (idGram K n)))} (hE : IsElemAbelian p E)
    (hc : Nat.card E = p ^ 2) (hD : ¬ E ≤ primeFormD h (idGram K n)) : UniPlaneGen ℓ E := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hℓ : ℓ.Prime := Fact.out
  have hne : ¬(n = 3 ∧ ℓ ^ f = 2) := fun h3 => hq h3.2
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  set φF := primeFormFieldFactor h hC hn hne with hφF
  have hker : φF.ker = primeFormD h (idGram K n) := ker_primeFormFieldFactor h hC hn hne
  have hφD : ∀ x, φF x = 1 ↔ x ∈ primeFormD h (idGram K n) := fun x => by
    rw [← hker, MonoidHom.mem_ker]
  have hφf : ∀ τ : K ≃+* K, φF (primeFormFieldHom h hC τ) = τ := fun τ => by
    have := primeFormFieldFactor_apply h hC hn hne 1 τ
    rwa [map_one, one_mul] at this
  have hcyc : IsCyclic (K ≃+* K) := (card_ringAut_and_isCyclic hℓ K h.card).2
  have hfinAut : Finite (K ≃+* K) := Finite.of_injective (fun φ : K ≃+* K => (φ : K → K))
    DFunLike.coe_injective
  obtain ⟨a, haE, haD⟩ : ∃ a ∈ E, a ∉ primeFormD h (idGram K n) := by
    by_contra hcon
    push Not at hcon
    exact hD hcon
  have hap : a ^ p = 1 := hE.2 a haE
  have ha1 : a ≠ 1 := fun h1 => haD (h1 ▸ (primeFormD h (idGram K n)).one_mem)
  have hσ1 : φF a ≠ 1 := fun h1 => haD ((hφD a).1 h1)
  have hσord : orderOf (φF a) = p := orderOf_eq_prime (by rw [← map_pow, hap, map_one]) hσ1
  obtain ⟨-, -, -, -, -, M, hM⟩ :=
    CFSG.RankThree.UnitaryDescent.unitary_prime_semilinear_field_descent h hn hne hp hp2 hpℓ a
      (orderOf_eq_prime hap ha1) _ rfl hσord
  set σ := φF a with hσdef
  set c₀ : MulAut (primeFormP h (idGram K n)) := primeFormConjHom h (idGram K n) M with hc₀
  set E' := E.map (MulAut.congr c₀⁻¹).toMonoidHom with hE'def
  suffices hE' : UniPlaneGen ℓ E' from (Inputs2311c.uniPlaneGen_map_congr c₀⁻¹ ℓ E).1 hE'
  have hE'el : IsElemAbelian p E' := isElemAbelian_map_congr c₀⁻¹ hE
  have hE'c : Nat.card E' = p ^ 2 := (card_map_congr c₀⁻¹ E).trans hc
  have hcongr : ∀ φ : MulAut (primeFormP h (idGram K n)), MulAut.congr c₀⁻¹ φ = c₀⁻¹ * φ * c₀ :=
    fun φ => rfl
  set fσ := primeFormFieldHom h hC σ with hfσ
  have hfσE : fσ ∈ E' := ⟨a, haE, by rw [MulEquiv.coe_toMonoidHom, hcongr]; exact hM⟩
  have hfσ1 : fσ ≠ 1 := fun h1 => hσ1 (by rw [← hφf σ, ← hfσ, h1, map_one])
  obtain ⟨b, hbE, hbz⟩ := exists_notMem_zpowers_of_card_sq hp hE'el.2 hE'c hfσE hfσ1
  have hbp : b ^ p = 1 := hE'el.2 b hbE
  have hτp : (φF b) ^ p = 1 := by rw [← map_pow, hbp, map_one]
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1
    (mem_zpowers_of_pow_eq_one_of_isCyclic hp hσord hτp)
  set cA := b * fσ ^ (-j) with hcAdef
  have hcAE : cA ∈ E' := E'.mul_mem hbE (E'.zpow_mem hfσE _)
  have hcAD : cA ∈ primeFormD h (idGram K n) := by
    rw [← hφD, hcAdef, map_mul, map_zpow, hφf, ← hj, ← _root_.zpow_add, add_neg_cancel,
      zpow_zero]
  have hcA1 : cA ≠ 1 := by
    intro h1
    apply hbz
    have : b = fσ ^ j := by
      rw [hcAdef, mul_eq_one_iff_eq_inv, ← _root_.zpow_neg, neg_neg] at h1
      exact h1
    rw [this]
    exact Subgroup.zpow_mem_zpowers _ _
  obtain ⟨A, hA⟩ := hcAD
  set e₂ := cA * fσ with he₂def
  have he₂E : e₂ ∈ E' := E'.mul_mem hcAE hfσE
  have he₂φ : φF e₂ = σ := by
    rw [he₂def, map_mul, (hφD cA).2 (by rw [← hA]; exact ⟨A, rfl⟩), one_mul, hφf]
  have he₂1 : e₂ ≠ 1 := fun h1 => hσ1 (by rw [← he₂φ, h1, map_one])
  have he₂ord : orderOf e₂ = p := orderOf_eq_prime (hE'el.2 e₂ he₂E) he₂1
  obtain ⟨hpf, -, -, -, -, N, hN⟩ :=
    CFSG.RankThree.UnitaryDescent.unitary_prime_semilinear_field_descent h hn hne hp hp2 hpℓ e₂
      he₂ord σ he₂φ hσord
  have hN' : (primeFormConjHom h (idGram K n) N)⁻¹ * e₂ * primeFormConjHom h (idGram K n) N = fσ := hN
  have hNe : e₂ * primeFormConjHom h (idGram K n) N = primeFormConjHom h (idGram K n) N * fσ := by
    rw [← hN']; group
  have h1N : fσ * primeFormConjHom h (idGram K n) 1 = primeFormConjHom h (idGram K n) 1 * fσ := by
    rw [map_one, mul_one, one_mul]
  set h₀ := fixSubfield_unitaryFieldData h hp hp2 hσord with hh₀
  have hbar := fixSubfield_unitaryFieldData_bar h hp hp2 hσord
  set T := suSub h h₀ hbar n with hTdef
  have hfeq : f = p * (f / p) := (Nat.mul_div_cancel' hpf).symm
  have hnq₀ : ¬(n = 3 ∧ ℓ ^ (f / p) = 2) := by
    rintro ⟨hn3, hq0⟩
    have h8' : ℓ ^ f ≠ 8 := by
      rcases h8 with h8 | h4
      · exact h8
      · omega
    exact ne_two_of_dvd_pow_add_one_of_ne_eight hp hfeq hpq h8' hq0
  have hnq_pair : (n, ℓ ^ (f / p)) ≠ (3, 2) := fun h =>
    hnq₀ ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  set mk := QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n) with hmk
  by_cases hTN : T.map (primeFormConjSU h _ N).toMonoidHom ≠ T
  ·
    have hpair := subfieldPairSUOdd_of_not_three_two ℓ f (f / p) K h (fixSubfield σ) h₀ hbar p hp hp2
      hfeq n hn hnq₀ N hTN
    have hle1 : (T.map (primeFormConjSU h _ (1 : primeFormUnitary h (idGram K n))).toMonoidHom).map mk ≤
        uniPlaneClosure ℓ E' :=
      map_suSub_le_uniPlaneClosure_of_ne h (by omega) hp hp2 hσord hnq_pair 1 hfσE hfσ1 h1N
    have hle2 : (T.map (primeFormConjSU h _ N).toMonoidHom).map mk ≤ uniPlaneClosure ℓ E' :=
      map_suSub_le_uniPlaneClosure_of_ne h (by omega) hp hp2 hσord hnq_pair N he₂E he₂1 hNe
    have hT1 : T.map (primeFormConjSU h _ (1 : primeFormUnitary h (idGram K n))).toMonoidHom = T := by
      have : (primeFormConjSU h _ (1 : primeFormUnitary h (idGram K n))).toMonoidHom =
          MonoidHom.id _ := by
        refine MonoidHom.ext fun g => Subtype.ext ?_
        change ((1 : primeFormUnitary h (idGram K n)) : GL (Fin n) K) * (g : GL (Fin n) K) *
          ((1 : primeFormUnitary h (idGram K n)) : GL (Fin n) K)⁻¹ = g
        simp
      rw [this, Subgroup.map_id]
    rw [hT1] at hle1
    rw [UniPlaneGen, eq_top_iff]
    intro x _
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ x
    have hg : g ∈ Subgroup.closure ((T : Set (gramSU h (idGram K n))) ∪
        (T.map (primeFormConjSU h _ N).toMonoidHom : Set (gramSU h (idGram K n)))) := by
      rw [hpair]; exact Subgroup.mem_top g
    rw [← Subgroup.sup_eq_closure] at hg
    have h2 := Subgroup.mem_map_of_mem mk hg
    rw [Subgroup.map_sup] at h2
    exact (sup_le hle1 hle2) h2
  ·
    push Not at hTN
    exfalso
    apply hcA1
    have hrange := range_subfieldPSU_eq_map h h₀ hbar n
    rw [← hTdef] at hrange
    have hfixR : ∀ x ∈ (subfieldPSU h h₀ hbar n).range, fσ x = x := fun x hx =>
      primeFormFieldHom_apply_of_mem_range h n h₀ hbar (fun c hc => hc) hx
    have hTN' : T.map (primeFormConjSU h _ N⁻¹).toMonoidHom = T := by
      conv_lhs => rw [← hTN]
      rw [Subgroup.map_map]
      have : (primeFormConjSU h _ N⁻¹).toMonoidHom.comp (primeFormConjSU h _ N).toMonoidHom =
          MonoidHom.id _ := by
        refine MonoidHom.ext fun g => Subtype.ext ?_
        change ((N⁻¹ : primeFormUnitary h (idGram K n)) : GL (Fin n) K) *
          (((N : GL (Fin n) K)) * (g : GL (Fin n) K) * (N : GL (Fin n) K)⁻¹) *
            ((N⁻¹ : primeFormUnitary h (idGram K n)) : GL (Fin n) K)⁻¹ = g
        simp only [Subgroup.coe_inv, inv_inv]
        group
      rw [this, Subgroup.map_id]
    have hNinv : ∀ x ∈ (subfieldPSU h h₀ hbar n).range,
        (primeFormConjHom h (idGram K n) N)⁻¹ x ∈ (subfieldPSU h h₀ hbar n).range := by
      intro x hx
      rw [hrange] at hx ⊢
      obtain ⟨s, hs, rfl⟩ := hx
      refine ⟨(primeFormConjSU h _ N⁻¹) s, ?_, ?_⟩
      · rw [← hTN']; exact ⟨s, hs, rfl⟩
      · rw [← map_inv]
        change mk (primeFormConjSU h _ N⁻¹ s) = primeFormConjHom h (idGram K n) N⁻¹ (mk s)
        rw [hmk, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, primeFormConjHom_mk]
        rfl
    have hfixA : ∀ x ∈ (subfieldPSU h h₀ hbar n).range, cA x = x := by
      intro x hx
      have hx' := hNinv x hx
      have he₂x : e₂ x = x := by
        have h1 : e₂ = primeFormConjHom h (idGram K n) N * fσ * (primeFormConjHom h (idGram K n) N)⁻¹ := by
          rw [← hN']; group
        rw [h1, MulAut.mul_apply, MulAut.mul_apply, hfixR _ hx', ← MulAut.mul_apply, mul_inv_cancel,
          MulAut.one_apply]
      have hfx : fσ⁻¹ x = x := by
        conv_lhs => rw [← hfixR x hx]
        rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
      have h2 : cA = e₂ * fσ⁻¹ := by rw [he₂def]; group
      rw [h2, MulAut.mul_apply, hfx, he₂x]
    obtain ⟨τ', -, hτ'⟩ := eq_primeFormFieldHom_of_fix h n h₀ hbar hn hne hnq₀ cA hfixA
    have hτ'1 : τ' = 1 := by
      have h1 : φF cA = 1 := (hφD cA).2 (by rw [← hA]; exact ⟨A, rfl⟩)
      rw [hτ', hφf] at h1
      exact h1
    rw [hτ', hτ'1, map_one]

end FieldOuter

section Main

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel CFSG.ClassicalGroups.Unitary
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

variable {ℓ f n p : ℕ} {K : Type} [Field K] [Finite K] [Fact ℓ.Prime] [CharP K ℓ]

theorem uniPlaneGen_psu_anyChar_of_ne_eight_or_four_le
    (h : UnitaryFieldData ℓ f K) (hq : ℓ ^ f ≠ 2) (h8 : ℓ ^ f ≠ 8 ∨ 4 ≤ n)
    (hn : 3 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ) (hpq : p ∣ ℓ ^ f + 1)
    {E : Subgroup (MulAut (primeFormP h (idGram K n)))} (hE : IsElemAbelian p E)
    (hc : Nat.card E = p ^ 2) :
    UniPlaneGen ℓ E ∨ (E ≤ primeFormD h (idGram K n) ∧ n = p ∧ ∃ A B : primeFormUnitary h (idGram K n),
      primeFormConjHom h (idGram K n) A ∈ E ∧ primeFormConjHom h (idGram K n) B ∈ E ∧
        A * B ≠ B * A) := by
  by_cases hD : E ≤ primeFormD h (idGram K n)
  · rcases uniPlaneGen_inndiag_anyChar h hq hn hp hp2 hpℓ hpq hE hc hD with hU | hH
    · exact Or.inl hU
    · exact Or.inr ⟨hD, hH⟩
  · exact Or.inl (uniPlaneGen_field_outer_anyChar_of_ne_eight_or_four_le h hq h8 hpq hn hp hp2 hpℓ hE hc hD)

theorem uniPlaneGen_psu_anyChar_of_ne_eight (h : UnitaryFieldData ℓ f K)
    (hq : ℓ ^ f ≠ 2) (h8 : ℓ ^ f ≠ 8)
    (hn : 3 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ) (hpq : p ∣ ℓ ^ f + 1)
    {E : Subgroup (MulAut (primeFormP h (idGram K n)))} (hE : IsElemAbelian p E)
    (hc : Nat.card E = p ^ 2) :
    UniPlaneGen ℓ E ∨ (E ≤ primeFormD h (idGram K n) ∧ n = p ∧ ∃ A B : primeFormUnitary h (idGram K n),
      primeFormConjHom h (idGram K n) A ∈ E ∧ primeFormConjHom h (idGram K n) B ∈ E ∧
        A * B ≠ B * A) :=
  uniPlaneGen_psu_anyChar_of_ne_eight_or_four_le h hq (Or.inl h8) hn hp hp2 hpℓ hpq hE hc

theorem uniPlaneGen_psu_anyChar (h : UnitaryFieldData ℓ f K)
    (hq : ℓ ^ f ≠ 2) (hp3 : p ≠ 3)
    (hn : 3 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ) (hpq : p ∣ ℓ ^ f + 1)
    {E : Subgroup (MulAut (primeFormP h (idGram K n)))} (hE : IsElemAbelian p E)
    (hc : Nat.card E = p ^ 2) :
    UniPlaneGen ℓ E ∨ (E ≤ primeFormD h (idGram K n) ∧ n = p ∧ ∃ A B : primeFormUnitary h (idGram K n),
      primeFormConjHom h (idGram K n) A ∈ E ∧ primeFormConjHom h (idGram K n) B ∈ E ∧
        A * B ≠ B * A) :=
  uniPlaneGen_psu_anyChar_of_ne_eight h hq (pow_ne_eight_of_dvd_pow_add_one hp hp3 hpq) hn hp hp2 hpℓ hpq hE hc

end Main

section Heis

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
open scoped commutatorElement

variable {ℓ f n : ℕ} {K : Type} [Field K]

theorem lifts_commute_gu (h : UnitaryFieldData ℓ f K) (hn : 3 ≤ n)
    {E : Subgroup (MulAut (primeFormP h (idGram K n)))} {X Y : primeFormUnitary h (idGram K n)}
    (hgen : Subgroup.zpowers (primeFormConjHom h (idGram K n) X) ⊔
      Subgroup.zpowers (primeFormConjHom h (idGram K n) Y) = E)
    (hXY : X * Y = Y * X) {A B : primeFormUnitary h (idGram K n)}
    (hA : primeFormConjHom h (idGram K n) A ∈ E) (hB : primeFormConjHom h (idGram K n) B ∈ E) :
    A * B = B * A := by
  have hscal : ∀ (S : Set (primeFormUnitary h (idGram K n))) (C : primeFormUnitary h (idGram K n)),
      primeFormConjHom h (idGram K n) C = 1 → C ∈ Subgroup.centralizer S := by
    intro S C hC
    obtain ⟨c, -, hc⟩ := eq_scalar_of_conj_eq_one h hn C hC
    rw [Subgroup.mem_centralizer_iff]
    intro z _
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [hc]
    exact (commute_scalar c (z : GL (Fin n) K)).eq
  have hXc : X ∈ Subgroup.centralizer ({X, Y} : Set (primeFormUnitary h (idGram K n))) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro z (rfl | rfl)
    · rfl
    · exact hXY.symm
  have hYc : Y ∈ Subgroup.centralizer ({X, Y} : Set (primeFormUnitary h (idGram K n))) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro z (rfl | rfl)
    · exact hXY
    · rfl
  have hAc := mem_of_conj_mem_of_sup_eq h hgen (hscal _) hXc hYc hA
  rw [Subgroup.mem_centralizer_iff] at hAc
  have hXA : X ∈ Subgroup.centralizer ({A} : Set (primeFormUnitary h (idGram K n))) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro z rfl
    exact (hAc X (Set.mem_insert X _)).symm
  have hYA : Y ∈ Subgroup.centralizer ({A} : Set (primeFormUnitary h (idGram K n))) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro z rfl
    exact (hAc Y (Set.mem_insert_of_mem X rfl)).symm
  have hBA := mem_of_conj_mem_of_sup_eq h hgen (hscal _) hXA hYA hB
  exact Subgroup.mem_centralizer_iff.1 hBA A rfl

variable [Finite K] [CharP K 2]

theorem exists_su_involution_of_fixed (h : UnitaryFieldData ℓ f K) (b : primeFormUnitary h (idGram K n))
    {s : primeFormP h (idGram K n)} (hs1 : s ≠ 1) (hs2 : s ^ 2 = 1)
    (hfix : primeFormConjHom h (idGram K n) b s = s) :
    ∃ t : GL (Fin n) K, t ≠ 1 ∧ t ^ 2 = 1 ∧ t * (b : GL (Fin n) K) = (b : GL (Fin n) K) * t := by
  classical
  obtain ⟨g₀, rfl⟩ := QuotientGroup.mk_surjective s
  obtain ⟨m, hm⟩ : ∃ m, m = Nat.card K - 1 := ⟨_, rfl⟩
  obtain ⟨k, hk⟩ := Inputs2311e.odd_natCard_sub_one_of_charTwo (F := K)
  have hmk : m = 2 * k + 1 := hm.trans hk
  have hZ : ∀ z ∈ normOneScalars h (gramSU h (idGram K n)) n, z ^ m = 1 := by
    rintro z ⟨c, -, -, hz⟩
    apply Subtype.ext
    rw [SubgroupClass.coe_pow, hz, OneMemClass.coe_one, ← map_pow]
    have hc : c ^ m = 1 := by
      rw [hm, ← Nat.card_units]
      exact pow_card_eq_one'
    rw [hc, map_one]
  have hsq : g₀ ^ 2 ∈ normOneScalars h (gramSU h (idGram K n)) n := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hs2
  obtain ⟨g₁, hg₁⟩ : ∃ g₁, g₁ = g₀ ^ m := ⟨_, rfl⟩
  have hg₁2 : g₁ ^ 2 = 1 := by
    rw [hg₁, ← pow_mul, mul_comm, pow_mul, hZ _ hsq]
  have hpg₁ : (g₁ : primeFormP h (idGram K n)) = (g₀ : primeFormP h (idGram K n)) := by
    rw [hg₁, QuotientGroup.mk_pow, hmk, pow_succ, pow_mul, hs2, one_pow, one_mul]
  have hg₁1 : g₁ ≠ 1 := fun h1 => hs1 (by rw [← hpg₁, h1, QuotientGroup.mk_one])
  set w : gramSU h (idGram K n) := ⟨(b : GL (Fin n) K) * g₁ * (b : GL (Fin n) K)⁻¹,
    conj_mem_gramSU h (idGram K n) b.2 g₁.2⟩ with hw
  have hpw : (w : primeFormP h (idGram K n)) = (g₁ : primeFormP h (idGram K n)) := by
    rw [hw, ← primeFormConjHom_mk, hpg₁, hfix]
  have hz : w⁻¹ * g₁ ∈ normOneScalars h (gramSU h (idGram K n)) n := QuotientGroup.eq.1 hpw
  have hw2 : w ^ 2 = 1 := by
    apply Subtype.ext
    have h1 : ((g₁ : GL (Fin n) K)) ^ 2 = 1 := by
      rw [← SubgroupClass.coe_pow, hg₁2, OneMemClass.coe_one]
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one, hw]
    simp only
    rw [conj_pow, h1, mul_one, mul_inv_cancel]
  have hzc : ∀ g, Commute (w⁻¹ * g₁) g := fun g =>
    ((Subgroup.mem_center_iff.1 (normOneScalars_le_center h _ n hz)) g).symm
  have hz2 : (w⁻¹ * g₁) ^ 2 = 1 := by
    have h1 : (w⁻¹ * g₁) ^ 2 = w⁻¹ ^ 2 * g₁ ^ 2 := by
      rw [pow_two, pow_two, pow_two]
      calc w⁻¹ * g₁ * (w⁻¹ * g₁) = w⁻¹ * (g₁ * (w⁻¹ * g₁)) := by simp only [mul_assoc]
        _ = w⁻¹ * ((w⁻¹ * g₁) * g₁) := by rw [← (hzc g₁).eq]
        _ = w⁻¹ * w⁻¹ * (g₁ * g₁) := by simp only [mul_assoc]
    rw [h1, hg₁2, inv_pow, hw2, inv_one, one_mul]
  have hz1 : w⁻¹ * g₁ = 1 := by
    have h1 : (w⁻¹ * g₁) ^ m = w⁻¹ * g₁ := by
      rw [hmk, pow_succ, pow_mul, hz2, one_pow, one_mul]
    rw [← h1, hZ _ hz]
  have hwg : w = g₁ := by
    have := congrArg (fun x => w * x) hz1
    simpa using this.symm
  refine ⟨(g₁ : GL (Fin n) K), fun h1 => hg₁1 (Subtype.ext h1), ?_, ?_⟩
  · rw [← SubgroupClass.coe_pow, hg₁2, OneMemClass.coe_one]
  · have h1 : (b : GL (Fin n) K) * g₁ * (b : GL (Fin n) K)⁻¹ = g₁ := congrArg Subtype.val hwg
    calc (g₁ : GL (Fin n) K) * b = ((b : GL (Fin n) K) * g₁ * (b : GL (Fin n) K)⁻¹) * b := by rw [h1]
      _ = b * g₁ := by group

theorem not_two_dvd_card_fixedSubgroup_of_heis (h : UnitaryFieldData ℓ f K) (hn : 3 ≤ n) {p : ℕ}
    (hp : p.Prime) (hnp : n = p) (hζ : ∃ ζ : K, IsPrimitiveRoot ζ p)
    {A B : primeFormUnitary h (idGram K n)} (hBp : (primeFormConjHom h (idGram K n) B) ^ p = 1)
    (hAB : Commute (primeFormConjHom h (idGram K n) A) (primeFormConjHom h (idGram K n) B))
    (hnc : A * B ≠ B * A) :
    ¬ 2 ∣ Nat.card ↥(CFSG.RankThree.PartOne.CTP.fixedSubgroup (primeFormConjHom h (idGram K n) B)) := by
  classical
  intro h2
  haveI : Finite (primeFormP h (idGram K n)) :=
    Finite.of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hs1 : (s : primeFormP h (idGram K n)) ≠ 1 := by
    intro h1
    have : s = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hs
    exact absurd hs (by norm_num)
  have hs2 : (s : primeFormP h (idGram K n)) ^ 2 = 1 := by
    rw [← Subgroup.coe_pow, ← hs, pow_orderOf_eq_one, Subgroup.coe_one]
  have hfix : primeFormConjHom h (idGram K n) B (s : primeFormP h (idGram K n)) = s :=
    CFSG.RankThree.PartOne.CTP.mem_fixedSubgroup.1 s.2
  obtain ⟨t, ht1, ht2, htb⟩ := exists_su_involution_of_fixed h B hs1 hs2 hfix
  have hbp : Inputs2311e.IsScal ((B : GL (Fin n) K) ^ p) := by
    obtain ⟨c, -, hc⟩ := eq_scalar_of_conj_eq_one h hn (B ^ p) (by rw [map_pow, hBp])
    refine ⟨(c : K), ?_⟩
    rw [← coe_scalar_gl, ← hc]
    rfl
  have hab : Inputs2311e.IsScal ⁅(A : GL (Fin n) K), (B : GL (Fin n) K)⁆ := by
    obtain ⟨c, -, hc⟩ := eq_scalar_of_conj_eq_one h hn ⁅A, B⁆
      (by rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]; exact hAB.eq)
    refine ⟨(c : K), ?_⟩
    rw [← coe_scalar_gl, ← hc]
    simp [commutatorElement_def]
  have hnc' : (A : GL (Fin n) K) * B ≠ B * A := fun h1 => hnc (Subtype.ext h1)
  exact ht1 (Inputs2311e.eq_one_of_commute_heis hp hnp hζ hbp hab hnc' htb ht2)

end Heis

section Even

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel

theorem uniPlaneGen_psu_even_of_nonsolvable {ℓ f n p : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData ℓ f K) (hℓ2 : ℓ = 2) (hn : 3 ≤ n) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ ℓ ^ f + 1) {E : Subgroup (MulAut (primeFormP h (idGram K n)))}
    (hE : IsElemAbelian p E) (hc : Nat.card E = p ^ 2)
    (hns : ∃ e ∈ E, e ≠ 1 ∧ ¬ IsSolvable ↥(CFSG.RankThree.PartOne.CTP.fixedSubgroup e)) :
    UniPlaneGen ℓ E := by
  classical
  subst hℓ2
  have := h.finite
  haveI : CharP K 2 := h.charP
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  have hq : 2 ^ f ≠ 2 := by
    intro h2
    rw [h2] at hpq
    have := Nat.le_of_dvd (by norm_num) hpq
    omega
  rcases uniPlaneGen_psu_anyChar h hq hp3 hn hp hp2 hp2 hpq hE hc with hU | ⟨hD, hnp, A, B, hA, hB, hAB⟩
  · exact hU
  exfalso
  have hpK : p ∣ Nat.card K - 1 := by
    have hq1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    have key : (2 ^ f) ^ 2 - 1 = (2 ^ f + 1) * (2 ^ f - 1) := by
      have h2 : 1 ≤ (2 ^ f) ^ 2 := Nat.one_le_pow _ _ (pow_pos (by norm_num) _)
      zify [hq1, h2]
      ring
    rw [h.card_eq_sq, key]
    exact Dvd.dvd.mul_right hpq _
  have hζ := exists_primitiveRoot_of_dvd_card_sub_one hp hpK
  obtain ⟨e₁, he₁E, he₁1, hns⟩ := hns
  have hfin : Finite E := Nat.finite_of_card_ne_zero (by rw [hc]; exact pow_ne_zero 2 hp.ne_zero)
  obtain ⟨e₂, he₂E, he₂⟩ := exists_notMem_zpowers_of_card_sq hp hE.2 hc he₁E he₁1
  have hcomm₁₂ : Commute e₁ e₂ :=
    congrArg Subtype.val (hE.1.is_comm.comm ⟨e₁, he₁E⟩ ⟨e₂, he₂E⟩)
  have hgen : Subgroup.zpowers e₁ ⊔ Subgroup.zpowers e₂ = E :=
    zpowers_sup_zpowers_eq_of_card_sq hp hE.2 hc he₁E he₁1 he₂E he₂
  obtain ⟨b, rfl⟩ := hD he₁E
  obtain ⟨a, rfl⟩ := hD he₂E
  have hnc : a * b ≠ b * a := fun hab => hAB (lifts_commute_gu h hn hgen hab.symm hA hB)
  apply hns
  by_contra hsolv
  have h2 : 2 ∣ Nat.card ↥(CFSG.RankThree.PartOne.CTP.fixedSubgroup (primeFormConjHom h (idGram K n) b)) := by
    by_contra hodd
    haveI : Finite (primeFormP h (idGram K n)) :=
      Finite.of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
    exact hsolv (CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 hodd)))
  exact not_two_dvd_card_fixedSubgroup_of_heis h hn hp hnp hζ (hE.2 _ he₁E) hcomm₁₂.symm hnc h2

end Even

section Cat

theorem uniSeitzPlanes_unitary_nonCpf_even :
    UniSeitzPlanes fun d p E => IsUnitaryIndex' d.1 ∧ d.1.characteristic = 2 ∧ 5 ≤ p ∧
      ¬ CentralPrimeFree p d.1 ∧
        ∃ e ∈ E, e ≠ 1 ∧ ¬ IsSolvable ↥(CFSG.RankThree.PartOne.CTP.fixedSubgroup e) := by
  rintro ⟨d, hv⟩ p hp hp2 hpd _ E hE hc ⟨⟨m, q, hd⟩, hch, hp5, hncpf, hns⟩
  subst hd
  have hq2 : q.p = 2 := by simpa using hch
  have hlift : p ∣ q.card + 1 ∧ p ∣ m + 1 := by simpa [CentralPrimeFree] using hncpf
  obtain ⟨-, -, hn3, -, F, _, hU, ⟨θ⟩⟩ :=
    CFSG.RankThree.PartOne.exists_primeFormP_of_statedClassicalModel_PSU
      (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA m q hv
        (MulEquiv.refl (Cat ⟨.twistedA m q, hv⟩)))
  have hE'el : IsElemAbelian p (E.map (MulAut.congr θ).toMonoidHom) := isElemAbelian_map_congr θ hE
  have hE'c : Nat.card (E.map (MulAut.congr θ).toMonoidHom) = p ^ 2 := (card_map_congr θ E).trans hc
  have hns' : ∃ ε ∈ E.map (MulAut.congr θ).toMonoidHom, ε ≠ 1 ∧
      ¬ IsSolvable ↥(CFSG.RankThree.PartOne.CTP.fixedSubgroup ε) := by
    obtain ⟨ε, hεE, hε1, hεs⟩ := hns
    refine ⟨MulAut.congr θ ε, ⟨ε, hεE, rfl⟩, fun h => hε1 ?_, fun hs => hεs ?_⟩
    · exact (MulAut.congr θ).injective (h.trans (map_one _).symm)
    · exact Inputs2311e.isSolvable_fixedSubgroup_of_congr θ ε hs
  have hpq : p ∣ q.p ^ q.exponent + 1 := by
    rw [← TauCeti.PrimePower.card_def]
    exact hlift.1
  have h := uniPlaneGen_psu_even_of_nonsolvable hU hq2 hn3 hp hp5 hpq hE'el hE'c hns'
  have h' := (Inputs2311c.uniPlaneGen_map_congr θ _ E).1 h
  simpa using h'

theorem input23_11TwoOn_unitary_nonCpf_even :
    Inputs2323b.Input23_11TwoOn fun p d => d.characteristic = 2 ∧ ¬ CentralPrimeFree p d ∧
      IsUnitaryIndex' d :=
  Inputs2311e.input23_11TwoOn_of_uniSeitzPlanes_ns uniSeitzPlanes_unitary_nonCpf_even
    fun _ _ _ hp5 hR hch _ _ _ hns => ⟨hR.2.2, hch, hp5, hR.2.1, hns⟩

end Cat

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311h
