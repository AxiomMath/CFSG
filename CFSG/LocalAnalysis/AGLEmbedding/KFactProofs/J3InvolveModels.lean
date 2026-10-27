module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical

public section

namespace CFSG.AGLEmbedding

open CFSG.Assembly.LowTwoRank
open CFSG.Open (pRank)

theorem exists_orderOf_nine_statedProj {F : Type} [Field F] (M : Matrix (Fin 2) (Fin 2) F)
    (hdet : M.det = 1) (h9 : M ^ 9 = -1) (h3 : (M ^ 3) 0 1 ≠ 0) :
    ∃ g : StatedProj (StatedSL 2 F), orderOf g = 9 := by
  have hdet' : M.det ≠ 0 := by rw [hdet]; exact one_ne_zero
  let A : GL (Fin 2) F := Matrix.GeneralLinearGroup.mkOfDetNeZero M hdet'
  have hAval : (A : Matrix (Fin 2) (Fin 2) F) = M := rfl
  have hA : A ∈ StatedSL 2 F := Subgroup.subset_closure (by simpa [hAval] using hdet)
  refine ⟨QuotientGroup.mk (s := (StatedScalars (Fin 2) F).subgroupOf (StatedSL 2 F))
    ⟨A, hA⟩, ?_⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have key : ∀ n : ℕ, (QuotientGroup.mk (s := (StatedScalars (Fin 2) F).subgroupOf
      (StatedSL 2 F)) ⟨A, hA⟩) ^ n = 1 ↔ A ^ n ∈ StatedScalars (Fin 2) F := by
    intro n
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    rfl
  have h1 : ¬ (QuotientGroup.mk (s := (StatedScalars (Fin 2) F).subgroupOf (StatedSL 2 F))
      ⟨A, hA⟩) ^ 3 ^ 1 = 1 := by
    rw [key]
    rintro ⟨c, hc⟩
    have := congrArg (fun X : GL (Fin 2) F => (X : Matrix (Fin 2) (Fin 2) F) 0 1) hc
    simp at this
    rw [hAval] at this
    exact h3 this.symm
  have h2 : (QuotientGroup.mk (s := (StatedScalars (Fin 2) F).subgroupOf (StatedSL 2 F))
      ⟨A, hA⟩) ^ 3 ^ (1 + 1) = 1 := by
    rw [key]
    refine ⟨-1, ?_⟩
    ext1
    have h9' : (A : Matrix (Fin 2) (Fin 2) F) ^ 9 = -1 := by rw [hAval]; exact h9
    rw [Units.val_pow_eq_pow_val, show 3 ^ (1 + 1) = 9 by norm_num, h9']
    ext i j
    simp [Matrix.GeneralLinearGroup.scalar, Matrix.one_apply]
  have := orderOf_eq_prime_pow h1 h2
  simpa using this

theorem exists_orderOf_nine_psl_of_card {K : Type} [Field K] [Finite K] {p : ℕ} [Fact p.Prime]
    (hK : Nat.card K = p) (M : Matrix (Fin 2) (Fin 2) (ZMod p)) (hdet : M.det = 1)
    (h9 : M ^ 9 = -1) (h3 : (M ^ 3) 0 1 ≠ 0) :
    ∃ g : StatedProj (StatedSL 2 K), orderOf g = 9 := by
  have : Finite (ZMod p) := inferInstance
  let φ : K ≃+* ZMod p :=
    CFSG.ClassicalInvolution.Upgrade.fieldIsoOfCard (by rw [hK, Nat.card_zmod])
  let e := CFSG.Adapters.RankTwoModelTransports.statedProjCongr
    (CFSG.Adapters.RankTwoModelTransports.glCongr φ)
    (CFSG.ClassicalInvolution.Upgrade.glCongr_statedSL φ 2)
    (CFSG.Adapters.RankTwoModelTransports.glCongr_statedScalars φ)
  obtain ⟨g, hg⟩ := exists_orderOf_nine_statedProj M hdet h9 h3
  exact ⟨e.symm g, by rw [MulEquiv.orderOf_eq]; exact hg⟩

theorem companion17_det : (!![0, 1; -1, 3] : Matrix (Fin 2) (Fin 2) (ZMod 17)).det = 1 := by
  decide

theorem companion17_pow_nine :
    (!![0, 1; -1, 3] : Matrix (Fin 2) (Fin 2) (ZMod 17)) ^ 9 = -1 := by
  decide

theorem companion17_pow_three :
    ((!![0, 1; -1, 3] : Matrix (Fin 2) (Fin 2) (ZMod 17)) ^ 3) 0 1 ≠ 0 := by
  decide

theorem companion19_det : (!![0, 1; -1, 10] : Matrix (Fin 2) (Fin 2) (ZMod 19)).det = 1 := by
  decide

theorem companion19_pow_nine :
    (!![0, 1; -1, 10] : Matrix (Fin 2) (Fin 2) (ZMod 19)) ^ 9 = -1 := by
  decide

theorem companion19_pow_three :
    ((!![0, 1; -1, 10] : Matrix (Fin 2) (Fin 2) (ZMod 19)) ^ 3) 0 1 ≠ 0 := by
  decide

theorem exists_orderOf_nine_psl_seventeen {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 17) : ∃ g : StatedProj (StatedSL 2 K), orderOf g = 9 := by
  have : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  exact exists_orderOf_nine_psl_of_card hK _ companion17_det companion17_pow_nine
    companion17_pow_three

theorem exists_orderOf_nine_psl_nineteen {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 19) : ∃ g : StatedProj (StatedSL 2 K), orderOf g = 9 := by
  have : Fact (Nat.Prime 19) := ⟨by norm_num⟩
  exact exists_orderOf_nine_psl_of_card hK _ companion19_det companion19_pow_nine
    companion19_pow_three

section DiagUnitary

variable (K : Type) [Field K]

noncomputable def psu42DiagUnits : (Fin 4 → Kˣ) →* GL (Fin 4) K :=
  (Units.map (Matrix.diagonalRingHom (Fin 4) K).toMonoidHom).comp
    (MulEquiv.piUnits.symm : (∀ _ : Fin 4, Kˣ) ≃* (Fin 4 → K)ˣ).toMonoidHom

def psu42ExtFour : (Fin 3 → Kˣ) →* (Fin 4 → Kˣ) :=
  MonoidHom.mk' (fun v => ![v 0, v 1, v 2, (v 0 * v 1 * v 2)⁻¹]) (by
    intro v w
    funext i
    fin_cases i <;> simp [mul_comm, mul_left_comm, mul_assoc])

noncomputable def psu42Diag : (Fin 3 → Kˣ) →* GL (Fin 4) K :=
  (psu42DiagUnits K).comp (psu42ExtFour K)

theorem psu42Diag_val (v : Fin 3 → Kˣ) :
    ((psu42Diag K v : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      Matrix.diagonal (fun i => ((psu42ExtFour K v i : Kˣ) : K)) := by
  rfl

variable {K}

theorem units_pow_three_of_card_four [Finite K] (hK : Nat.card K = 4) (u : Kˣ) : u ^ 3 = 1 := by
  have h : Nat.card Kˣ = 3 := by rw [Nat.card_units, hK]
  rw [← h]
  exact pow_card_eq_one'

theorem psu42Diag_mem_statedSU [Finite K] (hK : Nat.card K = 4) (v : Fin 3 → Kˣ) :
    psu42Diag K v ∈ StatedSU 4 2 K := by
  refine Subgroup.subset_closure ⟨?_, ?_⟩
  · rw [psu42Diag_val, Matrix.det_diagonal, Fin.prod_univ_four]
    simp [psu42ExtFour]
    field_simp
  · rw [psu42Diag_val, Matrix.diagonal_map (by simp), Matrix.diagonal_transpose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    have h3 := congrArg Units.val (units_pow_three_of_card_four hK (psu42ExtFour K v i))
    rw [← pow_succ]
    simpa using h3

noncomputable def psu42DiagProj [Finite K] (hK : Nat.card K = 4) :
    (Fin 3 → Kˣ) →* StatedProj (StatedSU 4 2 K) :=
  (QuotientGroup.mk' ((StatedScalars (Fin 4) K).subgroupOf (StatedSU 4 2 K))).comp
    ((psu42Diag K).codRestrict (StatedSU 4 2 K) (psu42Diag_mem_statedSU hK))

theorem psu42DiagProj_injective [Finite K] (hK : Nat.card K = 4) :
    Function.Injective (psu42DiagProj hK) := by
  rw [injective_iff_map_eq_one]
  intro v hv
  have hmem : psu42Diag K v ∈ StatedScalars (Fin 4) K := by
    have := (QuotientGroup.eq_one_iff _).1 hv
    exact this
  obtain ⟨c, hc⟩ := hmem
  have hdiag : ∀ i : Fin 4, psu42ExtFour K v i = c := by
    intro i
    have := congrArg (fun X : GL (Fin 4) K => (X : Matrix (Fin 4) (Fin 4) K) i i) hc
    simp [psu42Diag_val, Matrix.GeneralLinearGroup.scalar] at this
    exact Units.ext this.symm
  have h0 := hdiag 0
  have h1 := hdiag 1
  have h2 := hdiag 2
  have h3 := hdiag 3
  simp only [psu42ExtFour, MonoidHom.mk'_apply] at h0 h1 h2 h3
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at h0 h1 h2 h3
  have hc3 := units_pow_three_of_card_four hK c
  have e : c * c * c = 1 := by rw [← hc3, pow_three, mul_assoc]
  rw [h0, h1, h2, e, inv_one] at h3
  funext i
  fin_cases i
  · simpa [← h3] using h0
  · simpa [← h3] using h1
  · simpa [← h3] using h2

end DiagUnitary

theorem three_le_pRank_of_psu_four_two {L : Type} [Group L] [Finite L] {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = 4) (θ : L ≃* StatedProj (StatedSU 4 2 K)) :
    3 ≤ pRank 3 (⊤ : Subgroup L) := by
  have hcard : Nat.card (Fin 3 → Kˣ) = 3 ^ 3 := by
    rw [Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Nat.card_units, hK]
  refine CFSG.SectionRank.le_pRank_of_injective (A := Fin 3 → Kˣ) (by norm_num)
    (fun a b => mul_comm a b) (fun a => ?_) hcard
    (θ.symm.toMonoidHom.comp (psu42DiagProj hK))
    (θ.symm.injective.comp (psu42DiagProj_injective hK)) le_top
  funext i
  simpa using units_pow_three_of_card_four hK (a i)

end CFSG.AGLEmbedding
