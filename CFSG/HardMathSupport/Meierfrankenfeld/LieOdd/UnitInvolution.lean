module

public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.UnitInvPair
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSemilinearInvolution

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit

variable {K : Type} [Field K]

theorem refl_case_data (h : UnitaryFieldData 3 1 K) (A : GL (HypIndex 2 0) K)
    (hA : A ∈ hypUnitary h 2 0)
    (hord : orderOf (QuotientGroup.mk ⟨A, hA⟩ : hypUnitaryMod h 2 0) = 2) :
    ∃ l : K, l ≠ 0 ∧
      (∀ x, (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ
        ((A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ x) = (l ^ 2) • x) ∧
      (h.bar l * l = 1 ∨ h.bar l * l = -1) ∧
      ∀ c : K, ∃ x, (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ x ≠ c • x := by
  classical
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hsq : (QuotientGroup.mk (⟨A, hA⟩ * ⟨A, hA⟩ : hypUnitary h 2 0) : hypUnitaryMod h 2 0) = 1 := by
    rw [QuotientGroup.mk_mul, ← pow_two]
    exact orderOf_dvd_iff_pow_eq_one.mp (by rw [hord])
  obtain ⟨d, hdN, -, hAAd⟩ := (QuotientGroup.eq_one_iff _).1 hsq
  have hAAmat : (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) * (A : Matrix _ _ K) =
      (d : K) • (1 : Matrix (HypIndex 2 0) (HypIndex 2 0) K) := by
    have := congrArg (fun g : GL (HypIndex 2 0) K => (g : Matrix (HypIndex 2 0) (HypIndex 2 0) K))
      hAAd
    rw [scalar_val] at this
    simpa using this
  obtain ⟨l, hl0, hl2⟩ := exists_sq_eq_of_norm_eq_one h hp2 hdN
  refine ⟨l, hl0, ?_, ?_, ?_⟩
  · intro x
    rw [Matrix.mulVec_mulVec, hAAmat, hl2, Matrix.smul_mulVec, Matrix.one_mulVec]
  · have h1 : h.norm l * h.norm l = 1 := by
      rw [← norm_mul_eq' h l l, ← pow_two, hl2, hdN]
    have h2 := mul_self_eq_one_iff.1 h1
    rcases h2 with h3 | h3
    · left; rw [mul_comm]; exact h3
    · right; rw [mul_comm]; exact h3
  · intro c
    by_contra hcon
    push Not at hcon
    have hAc : (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) = c • 1 :=
      Matrix.ext_iff_mulVec.2 fun x => by rw [hcon x, Matrix.smul_mulVec, Matrix.one_mulVec]
    have hc0 : c ≠ 0 := by
      rintro rfl
      have h1 := A.val_inv
      rw [hAc, zero_smul, zero_mul] at h1
      have := congrFun (congrFun h1 (.inl 0)) (.inl 0)
      simp at this
    have hA' : ((A : Matrix (HypIndex 2 0) (HypIndex 2 0) K).map h.bar)ᵀ * hypGram 2 0 K *
        (A : Matrix _ _ K) = hypGram 2 0 K := hA
    have hiso := (gramForm_isometry_iff h (hypGram 2 0 K) _).2 hA'
    have h1 := hiso (Pi.single (.inl 0) 1) (Pi.single (.inr (.inr 0)) 1)
    rw [hcon, hcon] at h1
    simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, gramForm_single] at h1
    simp only [hypGram_inl_inr_inr, if_true] at h1
    have hcN : h.norm c = 1 := by
      have : c * h.bar c = 1 := by simpa using h1
      rw [UnitaryFieldData.norm]
      exact this
    have hmk : (QuotientGroup.mk ⟨A, hA⟩ : hypUnitaryMod h 2 0) = 1 := by
      refine (QuotientGroup.eq_one_iff _).2 ⟨Units.mk0 c hc0, hcN, pow_zero _, ?_⟩
      refine Units.ext ?_
      change (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) = _
      rw [scalar_val, hAc]
      rfl
    rw [hmk, orderOf_one] at hord
    exact absurd hord (by norm_num)

theorem Tcan_congr_vec {p f : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (h : UnitaryFieldData p f K) (G : Matrix ι ι K) (hG : (G.map h.bar)ᵀ = G) (h2 : (2 : K) ≠ 0)
    {v : ι → K} (hv : hf h G v v = 0) {a a' : ι → K} (e : a = a') (ha : hf h G v a = 0)
    (ha' : hf h G v a' = 0) : Tcan h G hG h2 hv ha = Tcan h G hG h2 hv ha' := by
  subst e; rfl

theorem exists_heis_of_involution_hyp (h : UnitaryFieldData 3 1 K)
    (α : MulAut (hypPSU h 2 0)) (hα2 : α * α = 1) (hα1 : α ≠ 1) :
    ∃ (x y : Fin 2 → hypPSU h 2 0) (z : hypPSU h 2 0),
      HeisCfg 3 2 x y z ∧ (∀ i, y i ^ 3 = 1) ∧ α (x 0) = (x 0)⁻¹ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨h.prime⟩
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd h hp2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf α = 2 := orderOf_eq_prime (by rw [pow_two]; exact hα2) hα1
  obtain ⟨hAct, -, -, hinv⟩ := odd_unitary_automorphism_semilinear_representation h hp2
    (r := 2) (ε := 0) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨A, σ, hx, hAu, hΦ, hσ, hσid, hσbar⟩ := hinv α hord
  set G : Matrix (HypIndex 2 0) (HypIndex 2 0) K := hypGram 2 0 K with hGdef
  have hGb : G.map h.bar = G := hypGram_map h.bar
  have hG : (G.map h.bar)ᵀ = G := by rw [hGb]; exact hypGram_transpose
  have hdet : G.det ≠ 0 := det_hypGram_ne_zero
  have hcard : Fintype.card (HypIndex 2 0) = 4 := by simpa using card_hypIndex (r := 2) (ε := 0)
  have hAu' : ((A : Matrix (HypIndex 2 0) (HypIndex 2 0) K).map h.bar)ᵀ * G *
      (A : Matrix _ _ K) = G := hAu
  have hiso : ∀ x y, hf h G ((A : Matrix _ _ K) *ᵥ x) ((A : Matrix _ _ K) *ᵥ y) = hf h G x y :=
    (gramForm_isometry_iff h G _).2 hAu'
  have hψ : ∀ g g' : ↥(gramSU h G), smat h G g' =
      (A : Matrix _ _ K) * (smat h G g).map σ * ((A⁻¹ : GL (HypIndex 2 0) K) : Matrix _ _ K) →
      α (QuotientGroup.mk g) = QuotientGroup.mk g' := by
    intro g g' hgg'
    have h1 := hAct ⟨⟨A, σ⟩, hx⟩ g
    rw [hΦ] at h1
    have hg' : g' = (⟨A * glAut σ (g : GL (HypIndex 2 0) K) * A⁻¹, conj_mem_hypSU hx g⟩ :
        ↥(gramSU h G)) := by
      refine smat_injective h G ?_
      rw [hgg']
      have e : smat h G (⟨A * glAut σ (g : GL (HypIndex 2 0) K) * A⁻¹, conj_mem_hypSU hx g⟩ :
          ↥(gramSU h G)) = (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
            (smat h G g).map σ * ((A⁻¹ : GL (HypIndex 2 0) K) : Matrix _ _ K) := by
        change ((A * glAut σ (g : GL (HypIndex 2 0) K) * A⁻¹ : GL (HypIndex 2 0) K) :
          Matrix (HypIndex 2 0) (HypIndex 2 0) K) = _
        rw [Units.val_mul, Units.val_mul, coe_glAut]
        rfl
      rw [e]
    rw [hg']
    exact h1
  have hσb : ∀ c, σ (h.bar c) = h.bar (σ c) := by
    rcases hσ with rfl | hb
    · intro c; rfl
    · intro c; rw [hb, hb]
  have hσ2 : ∀ c, σ (σ c) = c := by
    rcases hσ with rfl | hb
    · intro c; rfl
    · intro c; rw [hb, hb, h.bar_bar]
  have hσfix : ∀ c, h.bar c = c → σ c = c := by
    rcases hσ with rfl | hb
    · intro c _; rfl
    · intro c hc; rw [hb]; exact hc
  have hGσ : G.map σ = G := by
    rcases hσ with rfl | hb
    · exact Matrix.map_id G
    · have : G.map σ = G.map h.bar := by ext i j; simp [hb]
      rw [this, hGb]
  have hpair : ∃ v u, UnitPairData h G (tau σ (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K)) v u := by
    rcases hσ with hσr | hσbar'
    · obtain ⟨l, hl0, hAA, hN, hns⟩ := refl_case_data h A hAu (hσid hσr)
      have htau : tau σ (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) =
          fun x => (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ x := by
        funext x; rw [hσr]; rfl
      rw [htau]
      rcases hN with hN | hN
      · exact pair_refl_one h G _ l hl0 hAA h2 hG hcard hiso hN hns
      · exact pair_refl_neg h G _ l hl0 hAA h2 hG hdet hcard hiso hN hns
    · obtain ⟨c, hc0, hc⟩ := hσbar hσbar'
      have hAB : (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
          ((A⁻¹ : GL (HypIndex 2 0) K) : Matrix _ _ K) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      have hc1 := bar_scalar_pm_one h G σ hσbar' hG hGb hdet hcard _ _ hAB hAu' c hc
      exact pair_bar h G σ hσbar' h2 hG hGb hdet hcard _ hAu' c hc hc1
  obtain ⟨v, u, hv0, hvv, hvu, huk, lam, mu, hτv, hτu, hl, hc⟩ := hpair
  obtain ⟨a, b, ι₀, ha0, hS⟩ := exists_symp_system h G h2 hdet hG hcard hv0 hvv hvu huk
  have hinvx := psi_inv_of_eigen h G σ hσb hσ2 hGσ A hAu' hG α hψ hσfix h2 hvv hvu lam mu hτv
    hτu hl hc
  have hHeis := heisCfg_Tcan_proj h G hG hp2 h2 hdet (2 * 2 + 0) hvv hv0 a b hS.ha hS.hb hS.hι
    hS.hι0 hS.haa hS.hbb hS.hab hS.hii
  refine ⟨fun i => QuotientGroup.mk (Tcan h G hG h2 hvv (hS.ha i)),
    fun i => QuotientGroup.mk (Tcan h G hG h2 hvv (hS.hb i)),
    QuotientGroup.mk (Zel h G hG hvv hS.hι), hHeis, ?_, ?_⟩
  · intro i
    rw [← QuotientGroup.mk_pow, Tcan_pow_char h G hG hp2 h2 hvv (hS.hb i), QuotientGroup.mk_one]
  · show α (QuotientGroup.mk (Tcan h G hG h2 hvv (hS.ha 0))) =
      (QuotientGroup.mk (Tcan h G hG h2 hvv (hS.ha 0)))⁻¹
    rw [Tcan_congr_vec h G hG h2 hvv ha0 (hS.ha 0) hvu]
    exact hinvx

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
