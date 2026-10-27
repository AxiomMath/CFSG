module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD309ModelPkg
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseBUni
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD309ModelDft
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD309ModelOrd

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309M

open CFSG.LocalAnalysis.RankThreeUC.S15.ACore Subgroup Matrix Equiv
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309L
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseA
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseB
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.Open CFSG.SectionRank.OddCover

section Unitary

variable {r f : ℕ} {K : Type} [Field K] (hU : UnitaryFieldData r f K)

theorem monPermGL_mem_primeFormUnitary (σ : Perm (Fin 5)) :
    monPermGL 5 σ ∈ primeFormUnitary hU ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) := by
  rw [mem_primeFormUnitary, coe_monPermGL, Units.val_one, Matrix.mul_one]
  have h1 : ((σ⁻¹).permMatrix K).map hU.bar = (σ⁻¹).permMatrix K := by
    ext i j
    simp only [Matrix.map_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
      Equiv.toPEquiv_apply]
    split_ifs <;> simp
  rw [h1, Matrix.transpose_permMatrix, inv_inv, ← Matrix.permMatrix_mul, inv_mul_cancel,
    Matrix.permMatrix_one]

theorem diagHom_mem_primeFormUnitary {d : Fin 5 → Kˣ} (hd : ∀ i, hU.norm (d i : K) = 1) :
    diagHom 5 d ∈ primeFormUnitary hU ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) :=
  diagGL_mem_primeFormUnitary hU d hd

theorem norm_pow' (a : K) (n : ℕ) : hU.norm (a ^ n) = (hU.norm a) ^ n := by
  unfold UnitaryFieldData.norm
  rw [map_pow, mul_pow]

theorem scalar_mem_iff (z : Kˣ) :
    GeneralLinearGroup.scalar (Fin 5) z ∈
        primeFormUnitary hU ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) ↔
      hU.norm (z : K) = 1 := by
  constructor
  · intro h
    exact norm_eq_one_of_scalar_mem_primeFormUnitary hU (by norm_num) 1 h
  · intro hN
    have : (GeneralLinearGroup.scalar (Fin 5) z : GL (Fin 5) K) = diagGL 5 K (fun _ => z) := by
      apply Units.ext
      rw [GeneralLinearGroup.coe_scalar, diagGL_val, Matrix.scalar_apply]
    rw [this]
    exact diagGL_mem_primeFormUnitary hU _ (fun _ => hN)

theorem scalarsIn_uni (hn : 3 ≤ 5) (hq : ¬(5 = 3 ∧ r ^ f = 2)) :
    scalarsIn (uniModel hU hn hq) = (Units.map hU.normHom).ker := by
  ext z
  change GeneralLinearGroup.scalar (Fin 5) z ∈
      primeFormUnitary hU ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) ↔ _
  rw [scalar_mem_iff hU, hU.mem_ker_normUnits]

theorem card_ker_c_uni (hn : 3 ≤ 5) (hq : ¬(5 = 3 ∧ r ^ f = 2)) :
    Nat.card (uniModel hU hn hq).c.ker = r ^ f + 1 := by
  rw [card_ker_c _ (by norm_num), scalarsIn_uni hU hn hq]
  exact (unitary_field_norm hU).2.2.1

theorem exists_norm_five : ∃ c : K, hU.norm c = 5 := by
  have h5 : (5 : K) ∈ hU.fixedField := by
    rw [UnitaryFieldData.mem_fixedField]
    exact map_ofNat hU.bar 5
  obtain ⟨c, hc⟩ := hU.normHom_surjective ⟨5, h5⟩
  refine ⟨c, ?_⟩
  have := congrArg Subtype.val hc
  simpa using this

theorem dftGL_mem_unitary {ζ : Kˣ} (h : orderOf ζ = 5) (hN : hU.norm (ζ : K) = 1)
    (h5 : (5 : K) ≠ 0) {c : K} (hc : c ≠ 0) (hcN : hU.bar c * c * 5 = 1) :
    dftGL (isPrimitiveRoot_coe h) h5 c hc ∈
      primeFormUnitary hU ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) := by
  have hWv : ((dftGL (isPrimitiveRoot_coe h) h5 c hc : GL (Fin 5) K) :
      Matrix (Fin 5) (Fin 5) K) = c • dftMat (ζ : K) := rfl
  rw [mem_primeFormUnitary, hWv, Units.val_one, Matrix.mul_one]
  have hbar : hU.bar (ζ : K) = (ζ : K) ^ 4 := by
    have h1 : (ζ : K) * hU.bar (ζ : K) = 1 := hN
    have h2 : ((ζ ^ 5 : Kˣ) : K) = 1 := by rw [pow_five_of_orderOf h]; rfl
    have h3 : (ζ : K) * (ζ : K) ^ 4 = 1 := by
      rw [← pow_succ']
      exact_mod_cast h2
    exact mul_left_cancel₀ ζ.ne_zero (h1.trans h3.symm)
  ext k l
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply,
    smul_eq_mul, dftMat, Matrix.of_apply, map_mul, map_pow, hbar, Matrix.one_apply]
  have hterm : ∀ j : Fin 5, hU.bar c * ((ζ : K) ^ 4) ^ ((j : ℕ) * (k : ℕ)) *
      (c * (ζ : K) ^ ((j : ℕ) * (l : ℕ))) =
      (hU.bar c * c) * ((ζ : K) ^ ((l : ℕ) * (j : ℕ)) * (ζ : K) ^ (4 * ((j : ℕ) * (k : ℕ)))) := by
    intro j
    rw [← pow_mul]
    ring
  rw [Finset.sum_congr rfl (fun j _ => hterm j), ← Finset.mul_sum,
    dft_sum (isPrimitiveRoot_coe h) l k]
  by_cases hkl : k = l
  · subst hkl
    simp only [if_true]
    linear_combination hcN
  · have hlk : ¬ l = k := fun h' => hkl h'.symm
    simp [hkl, hlk]

theorem pkg_uni {Y : Type} [Group Y] [Finite Y] {P : Subgroup Y} {x z : Y} {L : Subgroup Y}
    [L.Normal] [Group.IsPerfect ↥L] (hcfg : LinUniCfg 5 P x z L)
    (hCp : IsPGroup 5 (centralizer (L : Set Y))) (hmodel : LinUniModelUni 5 x L) :
    Nonempty (Pkg Y L x) := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨q, K, instF, instFin, e, ŷ, ω, hK, hpq, hŷu, hŷp, hω, hact⟩ := hmodel
  have hq2 : 2 ≤ q := by
    have := Nat.le_of_dvd (by omega) hpq
    omega
  obtain ⟨r, f, rfl, ⟨hU⟩⟩ := exists_unitaryFieldData hK hq2
  have hn3 : 3 ≤ 5 := by norm_num
  have hn1 : 1 ≤ 5 := by norm_num
  have hq : ¬(5 = 3 ∧ r ^ f = 2) := fun ⟨h3, _⟩ => by omega
  obtain ⟨hM, hAut, hx⟩ := uniHyps_of_cfg hcfg hU Nat.prime_five (by norm_num) hn3 hq hK hpq e ŷ
    ω hŷu hŷp hω hact
  have hŷ : ŷ ∈ primeFormUnitary hU ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) := by
    rw [mem_primeFormUnitary, Units.val_one, Matrix.mul_one]
    exact hŷu
  have hŷp' : ((ŷ : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) ^ 5 =
      Matrix.scalar (Fin 5) (ω : K) := by
    rw [← Units.val_pow_eq_pow_val, hŷp, GeneralLinearGroup.coe_scalar]
  have hdet := not_pow_det Nat.prime_five (by norm_num) hŷp'
    (not_pow_omega Nat.prime_five (by norm_num) hpq hK hω)
  have ha : 1 ≤ (r ^ f + 1).factorization 5 :=
    Nat.Prime.factorization_pos_of_dvd Nat.prime_five (by omega) hpq
  have hK1card : Nat.card (Units.map hU.normHom).ker = r ^ f + 1 := (unitary_field_norm hU).2.2.1
  have hpK1 : 5 ∣ Nat.card (Units.map hU.normHom).ker := by
    rw [hK1card]
    exact hpq
  obtain ⟨ζ0, hζ0⟩ := exists_prime_orderOf_dvd_card' 5 hpK1
  have hζ : orderOf (ζ0 : Kˣ) = 5 := by
    rw [Subgroup.orderOf_coe]
    exact hζ0
  have hN : hU.norm ((ζ0 : Kˣ) : K) = 1 := (hU.mem_ker_normUnits).1 ζ0.2
  have hdvd : 5 ∣ Nat.card K - 1 := by
    have hq1 : 1 ≤ r ^ f := hq2.trans' (by norm_num)
    have : Nat.card K - 1 = (r ^ f - 1) * (r ^ f + 1) := by
      rw [hK]
      zify [Nat.one_le_pow 2 (r ^ f) (by omega), hq1]
      ring
    rw [this]
    exact Dvd.dvd.mul_left hpq _
  have h5 : (5 : K) ≠ 0 := five_ne_zero_of_dvd hdvd
  obtain ⟨lam, hlam⟩ := exists_norm_five hU
  have hlam0 : lam ≠ 0 := by
    rintro rfl
    have : hU.norm (0 : K) = 0 := by simp [UnitaryFieldData.norm]
    rw [this] at hlam
    exact h5 hlam.symm
  have hblam0 : hU.bar lam ≠ 0 := by
    intro h0
    have : lam = 0 := by
      have := congrArg hU.bar h0
      rwa [hU.bar_bar, map_zero] at this
    exact hlam0 this
  have hc0 : lam⁻¹ ≠ 0 := inv_ne_zero hlam0
  have hcN : hU.bar lam⁻¹ * lam⁻¹ * 5 = 1 := by
    have h1 : lam * hU.bar lam = 5 := hlam
    rw [map_inv₀]
    field_simp
    linear_combination (-1 : K) * h1
  have hW := dftGL_mem_unitary hU hζ hN h5 hc0 hcN
  refine ⟨{
    K := K
    P' := _
    eP := e.trans (statedEquiv hU hn1)
    M := uniModel hU hn3 hq
    hAut := hAut
    hout := ?_
    a := (r ^ f + 1).factorization 5
    ha := ha
    hGL := ?_
    hker := ?_
    e := e5' (ζ0 : Kˣ) hζ
    he := e5'_injective _ hζ
    hmon := ?_
    F := (dftGL (isPrimitiveRoot_coe hζ) h5 lam⁻¹ hc0)⁻¹
    hF := ?_
    hFconj := ?_ }⟩
  · change thetaP L (e.trans (statedEquiv hU hn1)) x ∉ _
    rw [hx]
    exact conjHom_not_mem_inner hU hn3 hq ⟨ŷ, hŷ⟩ hdet
  · exact factorization_card_primeFormUnitary Nat.prime_five (by norm_num) hU hpq
  · rw [card_ker_c_uni hU hn3 hq]
  · intro m
    change monEmb (e5' (ζ0 : Kˣ) hζ) 5 m ∈
      primeFormUnitary hU ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)
    rw [monEmb_apply]
    refine mul_mem (diagHom_mem_primeFormUnitary hU fun i => ?_)
      (monPermGL_mem_primeFormUnitary hU _)
    change hU.norm (((ζ0 : Kˣ) ^ (Multiplicative.toAdd (m.left i)).val : Kˣ) : K) = 1
    rw [Units.val_pow_eq_pow_val, norm_pow' hU, hN, one_pow]
  · exact inv_mem hW
  · rw [inv_inv]
    exact dftGL_conj (ζ0 : Kˣ) hζ h5 lam⁻¹ hc0

end Unitary

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309M
