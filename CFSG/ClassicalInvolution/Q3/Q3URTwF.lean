module

public import CFSG.ClassicalInvolution.Q3.Q3URPat

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3W

open Matrix CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.Generic CFSG.LieType.Steinberg CFSG.LieType.BorelTits
  CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalInvolution.ModelFacts.UnitaryAut CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps
open CFSG.ClassicalInvolution.Generic.CoreAssembly

section Aut

theorem ringEquiv_gf9_apply_apply (φ : GaloisField 3 2 ≃+* GaloisField 3 2)
    (c : GaloisField 3 2) : φ (φ c) = c := by
  let toAlg : GaloisField 3 2 ≃ₐ[ZMod 3] GaloisField 3 2 :=
    AlgEquiv.ofRingEquiv (f := φ) fun x => by
      simp only [Algebra.algebraMap_eq_smul_one]
      rw [← ZMod.natCast_zmod_val x, Nat.cast_smul_eq_nsmul, map_nsmul, map_one]
  have hcard : Nat.card (GaloisField 3 2 ≃ₐ[ZMod 3] GaloisField 3 2) = 2 := by
    rw [IsGalois.card_aut_eq_finrank, GaloisField.finrank 3 two_ne_zero]
  have h2 : toAlg ^ 2 = 1 := by
    have := pow_card_eq_one' (G := GaloisField 3 2 ≃ₐ[ZMod 3] GaloisField 3 2) (x := toAlg)
    rwa [hcard] at this
  have h3 := congrArg (fun χ : GaloisField 3 2 ≃ₐ[ZMod 3] GaloisField 3 2 => χ c) h2
  have h4 : toAlg (toAlg c) = c := by simpa [pow_two] using h3
  exact h4

end Aut

section Pow

theorem fixed_of_iterate_su3 {Y : Type} [Group Y] [Finite Y]
    (θ : Su (GaloisField 3 2) 3 1 (2 + 1) →* Y)
    (hker : θ.ker ≤ Subgroup.center (Su (GaloisField 3 2) 3 1 (2 + 1))) (σ : Y ≃* Y) {n : ℕ}
    (hn : Nat.Coprime n 16) (hσn : ∀ x, σ^[n] (θ x) = θ x)
    (hstab : ∀ x, σ (θ x) ∈ θ.range)
    (hfix : ∀ A : Su (GaloisField 3 2) 3 1 2,
      σ (θ (blockEmb2 (GaloisField 3 2) 3 1 2 0 A)) = θ (blockEmb2 (GaloisField 3 2) 3 1 2 0 A)) :
    ∀ x, σ (θ x) = θ x := by
  classical
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hP3 := su2_pow_three_mem_commutator
  have hcen : ∀ x ∈ Subgroup.center (Su (GaloisField 3 2) 3 1 (2 + 1)), ¬ 3 ∣ orderOf x :=
    fun x hx => center_orderOf_not_dvd_three_su3 (by omega) hx
  have hQ : ∀ y ∈ θ.range, σ y ∈ θ.range := by
    rintro _ ⟨x, rfl⟩
    exact hstab x
  let σR₀ : θ.range →* θ.range :=
    (σ.toMonoidHom.comp θ.range.subtype).codRestrict θ.range fun y => hQ y y.2
  have hinj : Function.Injective σR₀ := fun a b h =>
    Subtype.ext (σ.injective (congrArg Subtype.val h))
  let σR : θ.range ≃* θ.range := MulEquiv.ofBijective σR₀ (Finite.injective_iff_bijective.mp hinj)
  obtain ⟨α, g, φ, hlift₀, hmat, -, -⟩ := Q3NT.unitaryAutClassification_isometry_of_odd card_gf9
    hp2 le_rfl (by omega : 3 ≤ 2 + 1) θ.range θ.rangeRestrict θ.rangeRestrict_surjective
    (by rw [MonoidHom.ker_rangeRestrict]; exact hker) σR
  have hlift : ∀ x, θ (α x) = σ (θ x) := fun x => congrArg Subtype.val (hlift₀ x)
  have hαfix : ∀ A : Su (GaloisField 3 2) 3 1 2,
      α (blockEmb2 (GaloisField 3 2) 3 1 2 0 A) = blockEmb2 (GaloisField 3 2) 3 1 2 0 A := fun A =>
    DFunLike.congr_fun (lift_comp_eq_of_fixed3 hP3 hker (fun x hx => hcen x (hker hx)) hlift
      (blockEmb2 (GaloisField 3 2) 3 1 2 0) hfix) A
  set G : Matrix (Fin (2 + 1)) (Fin (2 + 1)) (GaloisField 3 2) :=
    (g : Matrix (Fin (2 + 1)) (Fin (2 + 1)) (GaloisField 3 2)) with hG
  set Gi : Matrix (Fin (2 + 1)) (Fin (2 + 1)) (GaloisField 3 2) :=
    ((g⁻¹ : GL (Fin (2 + 1)) (GaloisField 3 2)) :
      Matrix (Fin (2 + 1)) (Fin (2 + 1)) (GaloisField 3 2)) with hGi
  have hGGi : G * Gi = 1 := by rw [hG, hGi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hGiG : Gi * G = 1 := by rw [hG, hGi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hφφ : ∀ M : Matrix (Fin (2 + 1)) (Fin (2 + 1)) (GaloisField 3 2),
      φ.mapMatrix (φ.mapMatrix M) = M := fun M => by
    ext i j
    simp [RingEquiv.mapMatrix_apply, ringEquiv_gf9_apply_apply φ]
  set H : Matrix (Fin (2 + 1)) (Fin (2 + 1)) (GaloisField 3 2) := G * φ.mapMatrix G with hH
  set Hi : Matrix (Fin (2 + 1)) (Fin (2 + 1)) (GaloisField 3 2) := φ.mapMatrix Gi * Gi with hHi
  have hHHi : H * Hi = 1 := by
    have h1 : φ.mapMatrix G * φ.mapMatrix Gi = 1 := by rw [← map_mul, hGGi, map_one]
    calc H * Hi = G * (φ.mapMatrix G * φ.mapMatrix Gi) * Gi := by
          simp only [hH, hHi, Matrix.mul_assoc]
      _ = 1 := by rw [h1, Matrix.mul_one, hGGi]
  have hHiH : Hi * H = 1 := by
    have h1 : φ.mapMatrix Gi * φ.mapMatrix G = 1 := by rw [← map_mul, hGiG, map_one]
    calc Hi * H = φ.mapMatrix Gi * (Gi * G) * φ.mapMatrix G := by
          simp only [hH, hHi, Matrix.mul_assoc]
      _ = 1 := by rw [hGiG, Matrix.mul_one, h1]
  have hmat2 : ∀ x : Su (GaloisField 3 2) 3 1 (2 + 1),
      (((α (α x) : Su (GaloisField 3 2) 3 1 (2 + 1)) : GL (Fin (2 + 1)) (GaloisField 3 2)) :
        Matrix (Fin (2 + 1)) (Fin (2 + 1)) (GaloisField 3 2)) =
        H * ((x : GL (Fin (2 + 1)) (GaloisField 3 2)) :
          Matrix (Fin (2 + 1)) (Fin (2 + 1)) (GaloisField 3 2)) * Hi := by
    intro x
    rw [hmat (α x), hmat x]
    simp only [map_mul, hφφ, hH, hHi, Matrix.mul_assoc]
  have hα2fix : ∀ A : Su (GaloisField 3 2) 3 1 2,
      α (α (blockEmb2 (GaloisField 3 2) 3 1 2 0 A)) =
        blockEmb2 (GaloisField 3 2) 3 1 2 0 A := fun A => by rw [hαfix A, hαfix A]
  have hF : UnitaryFieldData 3 1 (GaloisField 3 2) :=
    ⟨Fact.out, le_rfl, by rw [card_gf9, ← pow_mul, mul_comm]⟩
  obtain ⟨u, hu1, hu2⟩ := exists_normOne_ne hF hp2
  set c : GaloisField 3 2 := ((u : (GaloisField 3 2)ˣ) : GaloisField 3 2) with hc
  have hcinv : (((u : (GaloisField 3 2)ˣ)⁻¹ : (GaloisField 3 2)ˣ) : GaloisField 3 2) = c⁻¹ :=
    Units.val_inv_eq_inv_val _
  have hu2' : c⁻¹ ≠ c := by rw [← hcinv]; exact hu2
  have hrefl : ∀ M : Matrix (Fin (2 + 1)) (Fin (2 + 1)) (GaloisField 3 2),
      (RingEquiv.refl (GaloisField 3 2)).mapMatrix M = M := fun M => by ext a b; rfl
  have hrel : ∀ i j : Fin (2 + 1),
      (if i.val = (0 : Fin 2).val then c else if i.val = (0 : Fin 2).val + 1 then c⁻¹ else 1) *
        H i j = H i j * (if j.val = (0 : Fin 2).val then c else
          if j.val = (0 : Fin 2).val + 1 then c⁻¹ else 1) := by
    intro i j
    have h1 := hmat2 (blockEmb2 (GaloisField 3 2) 3 1 2 0
      (torusTwo (unitaryInvolution (GaloisField 3 2) 3 1) u))
    rw [hα2fix _, coe_coe_blockEmb2_torusTwo] at h1
    have h3 := diagonal_relation (RingEquiv.refl (GaloisField 3 2)) H Hi hHiH _
      (by rw [hrefl]; exact h1.symm) i j
    simpa [hcinv] using h3
  have hdiag : ∀ i j : Fin (2 + 1), i ≠ j → H i j = 0 := by
    intro i j hij
    by_contra hne
    rcases torus_entry_cases_id (0 : Fin 2) c hu1 hu2' i j (H i j) hne (hrel i j) with
      heq | ⟨h4, h5, h6, h7⟩
    · exact hij heq
    · apply hij
      apply Fin.ext
      have := i.isLt
      have := j.isLt
      simp only [Fin.val_zero] at h4 h5 h6 h7
      omega
  have hHd : H = diagonal fun i => H i i := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · rw [hdiag i j hij, Matrix.diagonal_apply_ne _ hij]
  let _ : Fintype (GaloisField 3 2) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField 3 2) = 9 := by
    rw [← Nat.card_eq_fintype_card, card_gf9]
    norm_num
  have hH8 : H ^ 8 = 1 := by
    have hent : ∀ i, H i i ≠ 0 := by
      intro i h0
      have h1 : (H * Hi) i i = 1 := by rw [hHHi]; exact Matrix.one_apply_eq i
      rw [Matrix.mul_apply, Finset.sum_eq_single i] at h1
      · rw [h0, zero_mul] at h1
        exact zero_ne_one h1
      · intro k _ hk
        rw [hdiag i k (Ne.symm hk), zero_mul]
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    have h8 : ∀ i, H i i ^ 8 = 1 := fun i => by
      have := FiniteField.pow_card_sub_one_eq_one (H i i) (hent i)
      rwa [hcard] at this
    rw [hHd, Matrix.diagonal_pow, ← Matrix.diagonal_one]
    congr 1
    funext i
    simpa [Pi.pow_apply] using h8 i
  have hHi8 : Hi ^ 8 = 1 := by
    have hcomm : Commute H Hi := by
      unfold Commute SemiconjBy
      rw [hHHi, hHiH]
    have h1 := hcomm.mul_pow 8
    rw [hHHi, one_pow, hH8, one_mul] at h1
    exact h1.symm
  have hiter : ∀ (m : ℕ) (x : Su (GaloisField 3 2) 3 1 (2 + 1)),
      ((((α ∘ α)^[m] x : Su (GaloisField 3 2) 3 1 (2 + 1)) : GL (Fin (2 + 1)) (GaloisField 3 2)) :
        Matrix (Fin (2 + 1)) (Fin (2 + 1)) (GaloisField 3 2)) =
        H ^ m * ((x : GL (Fin (2 + 1)) (GaloisField 3 2)) :
          Matrix (Fin (2 + 1)) (Fin (2 + 1)) (GaloisField 3 2)) * Hi ^ m := by
    intro m
    induction m with
    | zero => intro x; simp
    | succ m ih =>
      intro x
      rw [Function.iterate_succ_apply', Function.comp_apply, hmat2, ih, pow_succ' H m,
        pow_succ Hi m]
      simp only [Matrix.mul_assoc]
  have hα16 : ∀ x : Su (GaloisField 3 2) 3 1 (2 + 1), (α ∘ α)^[8] x = x := by
    intro x
    refine Subtype.ext (Units.ext ?_)
    rw [hiter 8 x, hH8, hHi8, Matrix.one_mul, Matrix.mul_one]
  have hσiter : ∀ (m : ℕ) (x : Su (GaloisField 3 2) 3 1 (2 + 1)),
      (σ ∘ σ)^[m] (θ x) = θ ((α ∘ α)^[m] x) := by
    intro m
    induction m with
    | zero => intro x; rfl
    | succ m ih =>
      intro x
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih x, Function.comp_apply,
        Function.comp_apply, ← hlift, ← hlift]
  have hdouble : ∀ (k : ℕ) (y : Y), (σ ∘ σ)^[k] y = σ^[2 * k] y := by
    intro k
    induction k with
    | zero => intro y; rfl
    | succ k ih =>
      intro y
      rw [Function.iterate_succ_apply, ih, show 2 * (k + 1) = 2 * k + 2 by ring,
        Function.iterate_add_apply]
      try rfl
  intro x
  have h16 : Function.IsPeriodicPt (⇑σ) 16 (θ x) := by
    have := hσiter 8 x
    rw [hα16 x, hdouble] at this
    exact this
  have hnper : Function.IsPeriodicPt (⇑σ) n (θ x) := hσn x
  have hg := h16.gcd hnper
  have hgcd : Nat.gcd 16 n = 1 := by rw [Nat.gcd_comm]; exact hn
  rw [hgcd] at hg
  simpa [Function.IsPeriodicPt, Function.IsFixedPt] using hg

end Pow

end CFSG.ClassicalInvolution.Q3.Q3W
