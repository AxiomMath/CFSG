module

public import CFSG.ClassicalInvolution.AschTight.Hall196Idx2

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1911

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.AscL62 CFSG.GorensteinWalter
open scoped MatrixGroups

theorem two_dvd_of_ringEquiv {p f : ℕ} [Fact p.Prime] (hf : f ≠ 0)
    {σ : GaloisField p f ≃+* GaloisField p f} (hσ : σ ≠ 1) (hσ2 : σ * σ = 1) : 2 ∣ f := by
  let σ' : GaloisField p f ≃ₐ[ZMod p] GaloisField p f :=
    AlgEquiv.ofRingEquiv (f := σ) fun x => by
      simp only [Algebra.algebraMap_eq_smul_one]
      rw [← ZMod.natCast_zmod_val x, Nat.cast_smul_eq_nsmul, map_nsmul, map_one]
  have h1 : σ' ≠ 1 := fun h => hσ (by ext x; exact congrArg (fun τ => τ x) h)
  have h2 : σ' * σ' = 1 := by
    ext x
    exact congrArg (fun τ : GaloisField p f ≃+* GaloisField p f => τ x) hσ2
  have hord : orderOf σ' = 2 := orderOf_eq_prime (by rw [sq]; exact h2) h1
  have hcard : Nat.card (GaloisField p f ≃ₐ[ZMod p] GaloisField p f) = f := by
    rw [IsGalois.card_aut_eq_finrank, GaloisField.finrank p hf]
  rw [← hcard, ← hord]
  exact orderOf_dvd_natCard σ'

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {K : Subgroup G} {z : G} {S : Sylow 2 G} {W : Subgroup G}

theorem mem_sup_of_mem_pGammaL2PGLRange (hd : Sec19Data p f K z S W)
    (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f))
    (hFcard : Nat.card (GaloisField p f) = p ^ f)
    (hF : IsOddPrimePower (Nat.card (GaloisField p f))) (h3 : 3 < Nat.card (GaloisField p f))
    (a : Subgroup.normalizer (K : Set G))
    (ha : normalizerToPGammaL2Mod e hFcard hF h3 a ∈
      (SemidirectProduct.inl : PGL2 (GaloisField p f) →* PGammaL2 (GaloisField p f)).range) :
    (a : G) ∈ sec19X K z ⊔ centralizerModOdd ⊤ K := by
  have hX := Hall196.map_sec19X_eq_pGammaL2PGLRange hd e hFcard hF h3
  have ha' : normalizerToPGammaL2Mod e hFcard hF h3 a ∈
      ((sec19X K z).subgroupOf (Subgroup.normalizer (K : Set G))).map
        (normalizerToPGammaL2Mod e hFcard hF h3) := by
    rw [hX]
    exact ha
  obtain ⟨x, hxX, hx⟩ := ha'
  have hy1 : normalizerToPGammaL2Mod e hFcard hF h3 (x⁻¹ * a) = 1 := by
    rw [map_mul, map_inv, hx, inv_mul_cancel]
  have hyC : ((x⁻¹ * a : Subgroup.normalizer (K : Set G)) : G) ∈ centralizerModOdd ⊤ K :=
    ⟨Subgroup.mem_top _, (x⁻¹ * a).2, mem_normalizer_oddCoreOf_of_mem_normalizer (x⁻¹ * a).2,
      (Hall196.normalizerToPGammaL2Mod_eq_one_iff e hFcard hF h3 _).mp hy1⟩
  have e' : (a : G) = (x : G) * ((x⁻¹ * a : Subgroup.normalizer (K : Set G)) : G) := by simp
  rw [e']
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hxX))
    (Subgroup.mem_sup_right hyC)

theorem fieldPart_of_not_mem (hd : Sec19Data p f K z S W)
    (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f))
    (hFcard : Nat.card (GaloisField p f) = p ^ f)
    (hF : IsOddPrimePower (Nat.card (GaloisField p f))) (h3 : 3 < Nat.card (GaloisField p f))
    (a : Subgroup.normalizer (K : Set G)) (ha2 : (a : G) * a = 1)
    (haX : (a : G) ∉ sec19X K z ⊔ centralizerModOdd ⊤ K) :
    (normalizerToPGammaL2Mod e hFcard hF h3 a).right ≠ 1 ∧
      (normalizerToPGammaL2Mod e hFcard hF h3 a).right *
        (normalizerToPGammaL2Mod e hFcard hF h3 a).right = 1 := by
  refine ⟨fun h => haX (mem_sup_of_mem_pGammaL2PGLRange hd e hFcard hF h3 a
    (mem_range_inl_of_right_eq_one h)), ?_⟩
  have haa : a * a = 1 := Subtype.ext ha2
  have h1 : normalizerToPGammaL2Mod e hFcard hF h3 a * normalizerToPGammaL2Mod e hFcard hF h3 a =
      1 := by
    rw [← map_mul, haa, map_one]
  have h2 := congrArg SemidirectProduct.right h1
  simpa using h2

theorem two_dvd_of_not_mem (hd : Sec19Data p f K z S W)
    (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f))
    (hFcard : Nat.card (GaloisField p f) = p ^ f)
    (hF : IsOddPrimePower (Nat.card (GaloisField p f))) (h3 : 3 < Nat.card (GaloisField p f))
    (a : Subgroup.normalizer (K : Set G)) (ha2 : (a : G) * a = 1)
    (haX : (a : G) ∉ sec19X K z ⊔ centralizerModOdd ⊤ K) : 2 ∣ f := by
  have hf : f ≠ 0 := by
    rintro rfl
    rw [hFcard, pow_zero] at h3
    omega
  obtain ⟨h1, h2⟩ := fieldPart_of_not_mem hd e hFcard hF h3 a ha2 haX
  exact two_dvd_of_ringEquiv hf h1 h2

variable (K) in
noncomputable abbrev slAut {F : Type} [Field F] (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, F))
    (n : Subgroup.normalizer (K : Set G)) : MulAut SL(2, F) :=
  MulAut.congr e (oddCoreQuotientAut K (normalizerConj K n))

omit [Finite G] [IsSimpleGroup G] in
theorem exists_semilinHom_of_mem (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f))
    (hFcard : Nat.card (GaloisField p f) = p ^ f)
    (hF : IsOddPrimePower (Nat.card (GaloisField p f))) (h3 : 3 < Nat.card (GaloisField p f))
    (n : Subgroup.normalizer (K : Set G)) :
    ∃ g : GL (Fin 2) (GaloisField p f), ∀ b, slAut K e n b =
      semilinHom g (normalizerToPGammaL2Mod e hFcard hF h3 n).right b :=
  exists_eq_semilinHom hF h3 (pGammaL2ToMulAutPSL2_normalizerToPGammaL2Mod e hFcard hF h3 n)

omit [Finite G] [IsSimpleGroup G] in
theorem slAut_slAut_of_mul_self {F : Type} [Field F]
    (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, F)) (a : Subgroup.normalizer (K : Set G))
    (ha2 : (a : G) * a = 1) (b : SL(2, F)) : slAut K e a (slAut K e a b) = b := by
  have haa : a * a = 1 := Subtype.ext ha2
  have h : slAut K e a * slAut K e a = 1 := by
    rw [slAut, ← map_mul, ← map_mul, ← map_mul, haa, map_one, map_one, map_one]
  exact congrArg (fun α : MulAut SL(2, F) => α b) h

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
