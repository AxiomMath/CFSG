module

public import CFSG.GH74.GLS.Stage4.SDWLayerComp
public import CFSG.GH74.GLS.Stage4.SDWCompK
public import CFSG.GH74.GLS.Stage4.SDWCompK3
public import CFSG.GH74.GLS.Stage4.SDWCompQ
public import CFSG.GH74.GLS.Stage4.SDWCompD
public import CFSG.GH74.GLS.Stage4.SDWCompSyl
public import CFSG.GH74.GLS.Stage4.SDWComp3

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open CFSG.GH74.GLS

theorem sdw_oddCore_eq_pPrimeCore_two (X : Type*) [Group X] :
    CFSG.oddCore X = CFSG.pPrimeCore 2 X := by
  unfold CFSG.oddCore CFSG.pPrimeCore
  congr 1
  ext L
  simp only [Set.mem_ofPred_eq, Nat.coprime_two_left]

theorem sdw_K_not_pGroup {X : Type} [Group X] [Finite X] {K : Subgroup X} {q : ℕ} (hq : 3 ≤ q)
    (hodd : Odd q) (hK : HasSL2Model ↥K (fun q' => q' = q)) : ¬ IsPGroup 2 ↥K := by
  intro hP
  obtain ⟨m, hm⟩ := hP.exists_card_eq
  have hcard := card_of_hasSL2Model hK
  have hdvd : q ∣ 2 ^ m := by
    rw [← hm, hcard]
    exact Dvd.intro _ rfl
  have hcop : Nat.Coprime q (2 ^ m) :=
    Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hodd)
  have := Nat.Coprime.eq_one_of_dvd hcop hdvd
  omega

theorem sdw_not_normalPComplement {X : Type} [Group X] [Finite X] (hbot : CFSG.oddCore X = ⊥)
    {K : Subgroup X} (hK : ¬ IsPGroup 2 ↥K) : ¬ CFSG.HasNormalPComplement 2 X := by
  rintro ⟨N, hN, hcop, hquot⟩
  have hNodd : Odd (Nat.card N) := Nat.coprime_two_left.1 hcop
  have hNle : N ≤ CFSG.oddCore X := le_sSup ⟨hN, hNodd⟩
  have hN1 : N = ⊥ := le_bot_iff.1 (hbot ▸ hNle)
  have hinj : Function.Injective (QuotientGroup.mk' N) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hN1]
  exact hK (IsPGroup.of_injective hquot (QuotientGroup.mk' N) hinj |>.to_subgroup K)

theorem sdw_shape_of_hasSDOrWreathed {X : Type} [Group X] [Finite X] (hSyl : HasSDOrWreathedSylow X)
    (S : Sylow 2 X) :
    (∃ m : ℕ, 4 ≤ m ∧ Nonempty (↥(S : Subgroup X) ≃* CFSG.Open.SemidihedralGroup m)) ∨
      (∃ m : ℕ, 2 ≤ m ∧ Nonempty (↥(S : Subgroup X) ≃* CFSG.Open.WreathedTwoGroup m)) := by
  obtain ⟨S₀, ⟨m, hm, ⟨f⟩⟩ | ⟨m, hm, ⟨e⟩⟩⟩ := hSyl
  · obtain ⟨g⟩ := (CFSG.QuasiDihedralFusion.hasSemidihedralSylow_of hm S₀ f.symm).2 S
    exact Or.inl ⟨m, hm, ⟨g.symm⟩⟩
  · obtain ⟨g⟩ := (CFSG.QuasiDihedralFusion.hasWreathedSylow_of hm S₀ e).2 S
    exact Or.inr ⟨m, hm, ⟨g⟩⟩

theorem sdwreathedComponent_proved : SDWreathedComponent := by
  intro X _ _ _hKX hbot hSyl p n hp hp2 hq z hz K hzK hK hCK hfus
  have hcore : CFSG.oddCore X = ⊥ := by
    rw [sdw_oddCore_eq_pPrimeCore_two X]; exact hbot
  have hqodd : Odd (p ^ n) := (hp.odd_of_ne_two hp2).pow
  have hzz : z * z = 1 := by
    have h := pow_orderOf_eq_one z
    rw [hz, sq] at h
    exact h
  have hQDsyl : CFSG.QuasiDihedralFusion.HasQDOrWreathedSylow X := by
    obtain ⟨S, ⟨m, hm, ⟨f⟩⟩ | ⟨m, hm, ⟨e⟩⟩⟩ := hSyl
    · exact ⟨1, Or.inl ⟨rfl, m, CFSG.QuasiDihedralFusion.hasSemidihedralSylow_of hm S f.symm⟩⟩
    · exact ⟨m, Or.inr (CFSG.QuasiDihedralFusion.hasWreathedSylow_of hm S e)⟩
  have hK2 : ∀ (P : Type) [Group P], IsPGroup 2 P → ∀ φ : ↥K →* P, φ = 1 :=
    fun P _ hP φ => sdwK_hom_two_group hp hp2 hq hK hP φ
  obtain ⟨a, ha1, ha2⟩ := hfus
  rcases CFSG.QuasiDihedralFusion.fusion_class_cases (Or.inl hQDsyl) with
    hQD | ⟨R, K₀, hR⟩ | hD | hC
  ·
    obtain ⟨hsimple, hodd, hle⟩ := hQD.involutionClosure_isSimple hcore
    refine ⟨CFSG.Wreathed.SimpleOddIndexQuotient.involutionClosure X, inferInstance, ?_, hodd,
      hsimple⟩
    by_cases h3 : p ^ n = 3
    ·
      have hK3 : HasSL2Model ↥K (fun q => q = 3) := by
        obtain ⟨F, iF, iFin, hF, he⟩ := hK
        exact ⟨F, iF, iFin, by rw [← h3]; exact hF, he⟩
      obtain ⟨Q, w, hQK, hwK, hQ2, hw3, hwQ, hact, hcos⟩ := sdwK_three_structure hK3
      have hKz : ∀ k ∈ K, k * z = z * k := hasSL2Model_involution_central hqodd hK hzK hzz
      obtain ⟨S, hQS, hSz⟩ := sdw_exists_sylow_cent hQD hz hQ2 (fun q hq => hKz q (hQK hq))
      have hSK : ∀ s ∈ (S : Subgroup X), ∀ k ∈ K, s * k * s⁻¹ ∈ K :=
        fun s hs k hk => hCK s (hSz s hs) k hk
      exact sdw_three_le hle hwK hQ2 hw3 hwQ hact hcos S hQS (sdw_shape_of_hasSDOrWreathed hSyl S) hSK
    ·
      have h5 : 5 ≤ p ^ n := by
        rcases hqodd with ⟨t, ht⟩
        omega
      have hsolv : Group.IsSolvable (X ⧸ CFSG.Wreathed.SimpleOddIndexQuotient.involutionClosure X) :=
        CFSG.Milestones.odd_order_solvable hodd
      have h1 := sdwK_solvable_trivial hp hp2 h5 hK
        ((QuotientGroup.mk' (CFSG.Wreathed.SimpleOddIndexQuotient.involutionClosure X)).comp K.subtype)
      intro k hk
      have h2 := DFunLike.congr_fun h1 ⟨k, hk⟩
      simpa [QuotientGroup.eq_one_iff] using h2
  ·
    exfalso
    have hK₀ : K₀.Normal := hR.normal
    obtain ⟨k, hk⟩ := hR.index_eq_two_pow
    have hP : IsPGroup 2 (X ⧸ K₀) := IsPGroup.of_card (n := k) hk
    have hzK₀ : z ∈ K₀ := by
      have h1 := hK2 _ hP ((QuotientGroup.mk' K₀).comp K.subtype)
      have h2 := DFunLike.congr_fun h1 ⟨z, hzK⟩
      simpa [QuotientGroup.eq_one_iff] using h2
    have hz'K₀ : a * z * a⁻¹ ∈ K₀ := hK₀.conj_mem z hzK₀ a
    have hz'2 : orderOf (a * z * a⁻¹) = 2 := by
      rw [← hz]
      exact (MulAut.conj a).orderOf_eq z
    exact sdw_not_klein_four_in_Q hR hzK₀ hz'K₀ hz hz'2 ha2.symm ha1.symm
  ·
    exfalso
    obtain ⟨i, j, hi, hj, hi4, hji, hjj⟩ := sdwK_quaternion_pair hp hp2 hq hK
    exact sdw_not_isDGroup hQDsyl hK2 hi hj hi4 hji hjj hD
  ·
    exfalso
    exact sdw_not_normalPComplement hcore (K := K) (sdw_K_not_pGroup hq hqodd hK) hC

end CFSG.GH74.GLS.Stage4.Rest
