module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD309ModelPkg
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseBLin
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD309ModelDft
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD309ModelOrd

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309M

open CFSG.LocalAnalysis.RankThreeUC.S15.ACore Subgroup Matrix
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309L
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseA
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseB
open CFSG.LocalAnalysis.ComponentInitial CFSG.Open

theorem card_ker_c_lin {K : Type} [Field K] [Finite K] (hn : 3 ≤ 5) :
    Nat.card (linModel 5 K hn).c.ker = Nat.card K - 1 := by
  rw [card_ker_c _ (by norm_num)]
  have : scalarsIn (linModel 5 K hn) = ⊤ := by
    unfold scalarsIn
    exact Subgroup.comap_top _
  rw [this, Subgroup.card_top, Nat.card_units]

theorem pkg_lin {Y : Type} [Group Y] [Finite Y] {P : Subgroup Y} {x z : Y} {L : Subgroup Y}
    [L.Normal] [Group.IsPerfect ↥L] (hcfg : LinUniCfg 5 P x z L)
    (hCp : IsPGroup 5 (centralizer (L : Set Y))) (hmodel : LinUniModelLin 5 x L) :
    Nonempty (Pkg Y L x) := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨K, instF, instFin, e, ŷ, ω, hpK, hŷp, hω, hact⟩ := hmodel
  obtain ⟨hn3, hM, hAut, hx⟩ := linHyps_of_cfg hcfg hCp e ŷ ω hpK hŷp hω hact
  have hKcard : 1 < Nat.card K := Finite.one_lt_card
  have ha : 1 ≤ (Nat.card K - 1).factorization 5 :=
    Nat.Prime.factorization_pos_of_dvd Nat.prime_five (by omega) hpK
  have hωnp : ∀ b : K, b ^ 5 ≠ (ω : K) :=
    not_pow_of_orderOf Nat.prime_five ha hω
      (Nat.pow_succ_factorization_not_dvd (by omega) Nat.prime_five)
  have hŷp' : ((ŷ : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) ^ 5 =
      Matrix.scalar (Fin 5) (ω : K) := by
    rw [← Units.val_pow_eq_pow_val, hŷp, GeneralLinearGroup.coe_scalar]
  have hdet := not_pow_det Nat.prime_five (by norm_num) hŷp' hωnp
  have hpN : 5 ∣ Nat.card Kˣ := by rwa [Nat.card_units]
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' 5 hpN
  have h5 : (5 : K) ≠ 0 := five_ne_zero_of_dvd hpK
  refine ⟨{
    K := K
    P' := _
    eP := e.trans (statedEquivL 5 K)
    M := linModel 5 K hn3
    hAut := hAut
    hout := ?_
    a := (Nat.card K - 1).factorization 5
    ha := ha
    hGL := ?_
    hker := ?_
    e := e5' ζ hζ
    he := e5'_injective ζ hζ
    hmon := fun _ => Subgroup.mem_top _
    F := (dftGL (isPrimitiveRoot_coe hζ) h5 1 one_ne_zero)⁻¹
    hF := Subgroup.mem_top _
    hFconj := ?_ }⟩
  · change thetaP L (e.trans (statedEquivL 5 K)) x ∉ _
    rw [hx]
    exact conjAut_not_mem_inner hn3 ŷ hdet
  · change (Nat.card (⊤ : Subgroup (GL (Fin 5) K))).factorization 5 = _
    rw [Subgroup.card_top]
    exact factorization_card_GL Nat.prime_five (by norm_num) hpK
  · change (Nat.card (linModel 5 K hn3).c.ker).factorization 5 = _
    rw [card_ker_c_lin]
  · rw [inv_inv]
    exact dftGL_conj ζ hζ h5 1 one_ne_zero

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309M
