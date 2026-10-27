module

public import CFSG.LieType.Steinberg.CurtisDatum
public import CFSG.LieType.Universal.Unitary.Extras
public import CFSG.LieType.Universal.Unitary.Comparison
public import CFSG.LieType.Steinberg.CentralExt.SUBruhatExtras
public import CFSG.LieType.Steinberg.CentralExt.UnitaryRootGroups
public import CFSG.LieType.Steinberg.CentralExt.BorelIndex
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw.CoverType
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw.CoverLift
public import TauCeti.LinearAlgebra.Matrix.Triangular
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperUnitriangular.Basic
public import Mathlib.LinearAlgebra.Matrix.CharP

public section

namespace CFSG.LieType.Universal.Unitary

open Matrix CFSG.LieType.Steinberg CFSG.LieType.RootSystem CFSG.LieType.BorelTits
  CFSG.LieType.Universal.Unitary.SUExtras CFSG.Quasithin.SmithCurtis
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw
open scoped MatrixGroups Pointwise

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

@[expose] noncomputable def curtisDatum (hF : Nat.card F = (p ^ f) ^ 2) (n : ℕ) (hn : 2 ≤ n)
    (ζ : traceZero (unitaryInvolution F p f)) (hζ : (ζ : F) ≠ 0) :
    CFSG.Quasithin.SmithCurtis.CurtisDatum (SU (unitaryInvolution F p f) n)
      (coxeterMatrix (isFiniteType_cartan n)).toCoxeterSystem p := by
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hσ := unitaryInvolution_involutive hF
  exact CFSG.LieType.Steinberg.curtisDatumOf (D := rootDatum hF n)
    (n := levelWeyl hσ ζ) (H := levelTorus (unitaryInvolution F p f))
    (isCTGroupDatum hF n hn ζ hζ) (steinbergExtras hF n hn ζ hζ)
    (CFSG.LieType.Steinberg.CentralExt.SUBruhat.bruhatExtras hF hn ζ hζ) p
    (fun γ hγ => CFSG.LieType.Steinberg.isPGroup_rootGroup hσ
      (toStd_ne_zero_of_mem_roots hγ))

theorem levelTorus_pow_card_sub_one {n : ℕ} {k : Fin (n / 2)}
    {x : SU (unitaryInvolution F p f) n}
    (hx : x ∈ levelTorus (unitaryInvolution F p f) k) :
    x ^ (Nat.card F - 1) = 1 := by
  obtain ⟨c, hc⟩ := exists_tFun_of_mem_levelTorus hx
  apply mat_injective
  rw [map_pow, hc, Matrix.diagonal_pow, map_one, ← Matrix.diagonal_one]
  congr 1
  funext s
  have : Fintype F := Fintype.ofFinite F
  have hpow := FiniteField.pow_card_sub_one_eq_one (tFun (unitaryInvolution F p f) k (c : F) s)
    (tFun_ne_zero k c.ne_zero s)
  simpa only [Pi.pow_apply, Pi.one_apply, Nat.card_eq_fintype_card] using hpow

theorem curtisDatum_H_pow_card_sub_one (hF : Nat.card F = (p ^ f) ^ 2) (n : ℕ) (hn : 2 ≤ n)
    (ζ : traceZero (unitaryInvolution F p f)) (hζ : (ζ : F) ≠ 0)
    {h : SU (unitaryInvolution F p f) n} (hh : h ∈ (curtisDatum hF n hn ζ hζ).H) :
    h ^ (Nat.card F - 1) = 1 := by
  have hct := isCTGroupDatum hF n hn ζ hζ
  have hext := steinbergExtras hF n hn ζ hζ
  unfold curtisDatum at hh
  change h ∈ (⨆ k, levelTorus (unitaryInvolution F p f) k) at hh
  have hmain : h ∈ (⨆ k, levelTorus (unitaryInvolution F p f) k) ∧
      h ^ (Nat.card F - 1) = 1 := by
    refine Subgroup.iSup_induction (levelTorus (unitaryInvolution F p f))
      (C := fun x => x ∈ (⨆ k, levelTorus (unitaryInvolution F p f) k) ∧
        x ^ (Nat.card F - 1) = 1) hh ?_ ?_ ?_
    · intro k x hx
      exact ⟨Subgroup.mem_iSup_of_mem k hx, levelTorus_pow_card_sub_one hx⟩
    · exact ⟨one_mem _, one_pow _⟩
    · intro x y hx hy
      obtain ⟨hxH, hxpow⟩ := hx
      obtain ⟨hyH, hypow⟩ := hy
      refine ⟨mul_mem hxH hyH, ?_⟩
      have hcomm : Commute x y :=
        (commute_iff_eq x y).mpr (CFSG.LieType.Steinberg.iSup_H_comm hext hxH hyH)
      rw [hcomm.mul_pow, hxpow, hypow, one_mul]
  exact hmain.2

omit [CharP F p] in
theorem not_dvd_card_sub_one (hF : Nat.card F = (p ^ f) ^ 2) :
    ¬ p ∣ Nat.card F - 1 := by
  rw [hF]
  have hp := (Fact.out : p.Prime)
  have hfpos : 0 < f := by
    by_contra h
    have hf0 : f = 0 := by omega
    rw [hf0, pow_zero] at hF
    have h1 : 1 < Nat.card F := Finite.one_lt_card
    rw [hF] at h1
    norm_num at h1
  intro hd
  have hp2 : p ∣ (p ^ f) ^ 2 := by
    rw [← pow_mul]
    exact dvd_pow_self p (by omega)
  have hsub := Nat.dvd_sub hp2 hd
  have heq : (p ^ f) ^ 2 - ((p ^ f) ^ 2 - 1) = 1 := by
    have hle : 1 ≤ (p ^ f) ^ 2 := Nat.one_le_pow 2 _ (pow_pos hp.pos f)
    omega
  rw [heq] at hsub
  exact hp.not_dvd_one hsub

theorem curtisDatum_splitOver (hF : Nat.card F = (p ^ f) ^ 2) (n : ℕ) (hn : 2 ≤ n)
    (ζ : traceZero (unitaryInvolution F p f)) (hζ : (ζ : F) ≠ 0)
    (k : Type*) [Field k] [Algebra F k] :
    SplitOver k (curtisDatum hF n hn ζ hζ).H :=
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw.splitOver_of_pow_card_sub_one
    (K := F) k (fun _ hh => curtisDatum_H_pow_card_sub_one hF n hn ζ hζ hh)

theorem antidiag_transpose {F : Type*} [Field F] (n : ℕ) :
    (antidiag n : Matrix (Fin n) (Fin n) F)ᵀ = antidiag n := by
  ext i j
  unfold antidiag
  simp only [Matrix.transpose_apply, of_apply]
  by_cases h : j = Fin.rev i
  · have h' : i = Fin.rev j := by rw [h, Fin.rev_rev]
    rw [if_pos h, if_pos h']
  · have h' : i ≠ Fin.rev j := fun hh => h (by rw [hh, Fin.rev_rev])
    rw [if_neg h, if_neg h']

theorem transpose_mem_SU {K : Type*} [Field K] {σ : K ≃+* K} {n : ℕ}
    {A : GL (Fin n) K} (hA : A ∈ SU σ n) :
    ∃ B : GL (Fin n) K, B ∈ SU σ n ∧ (B : Matrix (Fin n) (Fin n) K) = (A : Matrix (Fin n) (Fin n) K)ᵀ := by
  classical
  let M : Matrix (Fin n) (Fin n) K := (A : Matrix (Fin n) (Fin n) K)ᵀ
  have hdet : M.det ≠ 0 := by
    rw [show M.det = (A : Matrix (Fin n) (Fin n) K).det from by
      simp only [M, Matrix.det_transpose]]
    rw [(mem_SU.mp hA).1]
    exact one_ne_zero
  let B : GL (Fin n) K := Matrix.GeneralLinearGroup.mkOfDetNeZero M hdet
  have hBcoe : (B : Matrix (Fin n) (Fin n) K) = M := rfl
  refine ⟨B, ?_, hBcoe⟩
  rw [mem_SU]
  constructor
  · rw [hBcoe, show M.det = (A : Matrix (Fin n) (Fin n) K).det from by
      simp only [M, Matrix.det_transpose], (mem_SU.mp hA).1]
  · have hJ := antidiag_transpose (F := K) n
    have hJsq := antidiag_mul_self (F := K) n
    have hAcond : conjTr σ (A : Matrix (Fin n) (Fin n) K) * antidiag n *
        (A : Matrix (Fin n) (Fin n) K) = antidiag n := (mem_SU.mp hA).2
    let N : Matrix (Fin n) (Fin n) K := ((A : Matrix (Fin n) (Fin n) K).map σ)
    have hAinv : (A : Matrix (Fin n) (Fin n) K) * ((A : Matrix (Fin n) (Fin n) K))⁻¹ = 1 :=
      Matrix.mul_nonsing_inv _ (by rw [(mem_SU.mp hA).1]; exact isUnit_one)
    have h2 : Nᵀ * (antidiag n : Matrix (Fin n) (Fin n) K) =
        (antidiag n : Matrix (Fin n) (Fin n) K) * ((A : Matrix (Fin n) (Fin n) K))⁻¹ := by
      have hN : conjTr σ (A : Matrix (Fin n) (Fin n) K) = Nᵀ := rfl
      have h' := congrArg (· * ((A : Matrix (Fin n) (Fin n) K))⁻¹) hAcond
      rw [hN] at h'
      simpa only [Matrix.mul_assoc, hAinv, Matrix.mul_one] using h'
    have h1 : Nᵀ = (antidiag n : Matrix (Fin n) (Fin n) K) *
        ((A : Matrix (Fin n) (Fin n) K))⁻¹ * (antidiag n : Matrix (Fin n) (Fin n) K) := by
      calc Nᵀ = Nᵀ * (antidiag n : Matrix (Fin n) (Fin n) K) *
              (antidiag n : Matrix (Fin n) (Fin n) K) := by
            rw [Matrix.mul_assoc, hJsq, Matrix.mul_one]
        _ = ((antidiag n : Matrix (Fin n) (Fin n) K) *
              ((A : Matrix (Fin n) (Fin n) K))⁻¹) *
              (antidiag n : Matrix (Fin n) (Fin n) K) := by rw [h2]
    have h3 : N = (antidiag n : Matrix (Fin n) (Fin n) K) *
        ((A : Matrix (Fin n) (Fin n) K)⁻¹)ᵀ * (antidiag n : Matrix (Fin n) (Fin n) K) := by
      have := congrArg Matrix.transpose h1
      simpa only [Matrix.transpose_transpose, Matrix.transpose_mul, hJ, Matrix.mul_assoc] using this
    have hconj : conjTr σ (M : Matrix (Fin n) (Fin n) K) = N := by
      ext i j
      rfl
    have hAinvT : ((A : Matrix (Fin n) (Fin n) K)⁻¹)ᵀ *
        ((A : Matrix (Fin n) (Fin n) K))ᵀ = 1 := by
      rw [← Matrix.transpose_mul, hAinv, Matrix.transpose_one]
    rw [hBcoe]
    change conjTr σ (M : Matrix (Fin n) (Fin n) K) *
      (antidiag n : Matrix (Fin n) (Fin n) K) * M = antidiag n
    rw [hconj]
    calc N * (antidiag n : Matrix (Fin n) (Fin n) K) * M
        = ((antidiag n : Matrix (Fin n) (Fin n) K) *
            ((A : Matrix (Fin n) (Fin n) K)⁻¹)ᵀ *
            (antidiag n : Matrix (Fin n) (Fin n) K)) *
            (antidiag n : Matrix (Fin n) (Fin n) K) * M := by rw [h3]
      _ = (antidiag n : Matrix (Fin n) (Fin n) K) *
            ((A : Matrix (Fin n) (Fin n) K)⁻¹)ᵀ * M := by
            simp only [Matrix.mul_assoc]
            rw [← Matrix.mul_assoc (antidiag n) (antidiag n) M, hJsq, Matrix.one_mul]
      _ = (antidiag n : Matrix (Fin n) (Fin n) K) *
            (((A : Matrix (Fin n) (Fin n) K)⁻¹)ᵀ *
              ((A : Matrix (Fin n) (Fin n) K))ᵀ) := by
            rw [Matrix.mul_assoc]
      _ = (antidiag n : Matrix (Fin n) (Fin n) K) := by
            rw [hAinvT, Matrix.mul_one]

@[expose] noncomputable def upperUniSU (σ : F ≃+* F) (n : ℕ) : Subgroup (SU σ n) :=
  (TauCeti.upperUnitriangularGroup (Fin n) F).subgroupOf (SU σ n)

omit [Finite F] in
theorem mem_upperUniSU_iff {σ : F ≃+* F} {n : ℕ} {g : SU σ n} :
    g ∈ upperUniSU σ n ↔ (mat σ n g).IsUpperUnitriangular := by
  rw [upperUniSU, Subgroup.mem_subgroupOf,
    TauCeti.UpperUnitriangularGroup.mem_iff, mat_apply]

omit [Finite F] in
theorem exists_pow_eq_one_of_isUpperUnitriangular {σ : F ≃+* F} {n : ℕ} [NeZero n]
    {g : SU σ n} (hg : (mat σ n g).IsUpperUnitriangular) : ∃ k, g ^ (p ^ k) = 1 := by
  set N : Matrix (Fin n) (Fin n) F := mat σ n g - 1 with hNdef
  obtain ⟨m, hm⟩ := hg.isNilpotent_sub_one
  have hmle : m ≤ p ^ m :=
    le_of_lt (Nat.lt_pow_self (n := m) (a := p) (Fact.out : p.Prime).one_lt)
  have hNk : N ^ (p ^ m) = 0 := pow_eq_zero_of_le (m := m) (n := p ^ m) hmle hm
  refine ⟨m, ?_⟩
  apply mat_injective
  rw [map_pow, map_one]
  have hg1 : mat σ n g = 1 + N := by rw [hNdef]; abel
  rw [hg1, add_pow_char_pow_of_commute p m (Commute.one_left N), one_pow, hNk, add_zero]

theorem isPGroup_upperUniSU (n : ℕ) :
    IsPGroup p (upperUniSU (unitaryInvolution F p f) n) := by
  rcases n with _ | n
  · have : Subsingleton (SU (unitaryInvolution F p f) 0) :=
      ⟨fun a b => mat_injective (Subsingleton.elim _ _)⟩
    intro g
    exact ⟨0, by simpa using Subsingleton.elim g 1⟩
  · have : NeZero (n + 1) := ⟨Nat.succ_ne_zero n⟩
    intro g
    obtain ⟨k, hk⟩ := exists_pow_eq_one_of_isUpperUnitriangular
      (σ := unitaryInvolution F p f) (n := n + 1) (p := p) (mem_upperUniSU_iff.mp g.2)
    exact ⟨k, Subtype.ext hk⟩

theorem posUnipotent_le_upperUniSU (hF : Nat.card F = (p ^ f) ^ 2) (n : ℕ) :
    posUnipotent (rootDatum hF n) ≤ upperUniSU (unitaryInvolution F p f) n := by
  have hσ := unitaryInvolution_involutive hF
  intro g hg
  have hg' : g ∈ (⨆ γ ∈ {γ | γ ∈ roots (isFiniteType_cartan n) (divisible n) ∧ 0 < ht γ},
      rootGroup (unitaryInvolution F p f) hσ n γ) := hg
  have h := idBelow_of_mem_iSup hσ 1
    {γ | γ ∈ roots (isFiniteType_cartan n) (divisible n) ∧ 0 < ht γ}
    (fun γ hγ => by have := hγ.2; omega) hg'
  rw [mem_upperUniSU_iff, Matrix.isUpperUnitriangular_def]
  refine ⟨?_, ?_⟩
  · refine fun i j hij => ?_
    have hji : (j : ℤ) < (i : ℤ) := by exact_mod_cast hij
    have hlev : lvl 1 j - lvl 1 i < 1 := by
      unfold lvl
      omega
    rw [h i j hlev]
    exact Matrix.one_apply_ne (ne_of_gt hij)
  · intro i
    have hlev : lvl 1 i - lvl 1 i < 1 := by
      simp [lvl]
    rw [h i i hlev]
    exact Matrix.one_apply_eq i

theorem coprime_card_iSup_levelTorus (hF : Nat.card F = (p ^ f) ^ 2) (n : ℕ) (hn : 2 ≤ n)
    (ζ : traceZero (unitaryInvolution F p f)) (hζ : (ζ : F) ≠ 0) :
    p.Coprime (Nat.card ↥(⨆ k, levelTorus (unitaryInvolution F p f) (n := n) k)) := by
  rw [Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)]
  intro hdvd
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(⨆ k, levelTorus (unitaryInvolution F p f) (n := n) k)) p hdvd
  have hgH : (g : SU (unitaryInvolution F p f) n) ∈ (curtisDatum hF n hn ζ hζ).H := by
    unfold curtisDatum
    exact g.2
  have hgpow : (g : SU (unitaryInvolution F p f) n) ^ (Nat.card F - 1) = 1 :=
    curtisDatum_H_pow_card_sub_one hF n hn ζ hζ hgH
  have hgpow' : (g : ↥(⨆ k, levelTorus (unitaryInvolution F p f) (n := n) k)) ^
      (Nat.card F - 1) = 1 := Subtype.ext (by simpa using hgpow)
  have hdvd' : orderOf g ∣ Nat.card F - 1 := orderOf_dvd_iff_pow_eq_one.mpr hgpow'
  rw [hg] at hdvd'
  exact not_dvd_card_sub_one hF hdvd'

theorem coprime_index_posUnipotent (hF : Nat.card F = (p ^ f) ^ 2) (n : ℕ) (hn : 2 ≤ n)
    (ζ : traceZero (unitaryInvolution F p f)) (hζ : (ζ : F) ≠ 0) :
    p.Coprime (posUnipotent (rootDatum hF n)).index := by
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hσ := unitaryInvolution_involutive hF
  have hpG : ∀ γ ∈ (rootDatum hF n).roots,
      IsPGroup p ((rootDatum hF n).rootGroup γ) :=
    fun γ hγ => CFSG.LieType.Steinberg.isPGroup_rootGroup hσ
      (toStd_ne_zero_of_mem_roots hγ)
  refine CFSG.LieType.Steinberg.CentralExt.BorelIndex.coprime_index_posUnipotent
    (isCTGroupDatum hF n hn ζ hζ) (steinbergExtras hF n hn ζ hζ)
    (CFSG.LieType.Steinberg.CentralExt.SUBruhat.bruhatExtras hF hn ζ hζ) hpG ?_
  exact coprime_card_iSup_levelTorus hF n hn ζ hζ

theorem upperUniSU_le_posUnipotent (hF : Nat.card F = (p ^ f) ^ 2) (n : ℕ) (hn : 2 ≤ n)
    (ζ : traceZero (unitaryInvolution F p f)) (hζ : (ζ : F) ≠ 0) :
    upperUniSU (unitaryInvolution F p f) n ≤ posUnipotent (rootDatum hF n) := by
  have hU := posUnipotent_le_upperUniSU hF n
  have hVp : IsPGroup p (upperUniSU (unitaryInvolution F p f) n) :=
    isPGroup_upperUniSU n
  obtain ⟨k, hk⟩ := hVp.exists_card_eq
  have hcop : p.Coprime (posUnipotent (rootDatum hF n)).index :=
    coprime_index_posUnipotent hF n hn ζ hζ
  have hK : Nat.card (SU (unitaryInvolution F p f) n) =
      Nat.card (posUnipotent (rootDatum hF n)) *
        (posUnipotent (rootDatum hF n)).index :=
    (Subgroup.card_mul_index _).symm
  have hdvdK : p ^ k ∣ Nat.card (SU (unitaryInvolution F p f) n) := by
    rw [← hk]
    exact Subgroup.card_subgroup_dvd_card (upperUniSU (unitaryInvolution F p f) n)
  have hdvdK' : p ^ k ∣ Nat.card (posUnipotent (rootDatum hF n)) *
      (posUnipotent (rootDatum hF n)).index := by
    rwa [hK] at hdvdK
  have hcopk : Nat.Coprime (p ^ k) (posUnipotent (rootDatum hF n)).index :=
    hcop.pow_left k
  have hdvd : p ^ k ∣ Nat.card (posUnipotent (rootDatum hF n)) :=
    hcopk.dvd_of_dvd_mul_right hdvdK'
  have hcard : Nat.card (upperUniSU (unitaryInvolution F p f) n) ≤
      Nat.card (posUnipotent (rootDatum hF n)) := by
    rw [hk]
    exact Nat.le_of_dvd Nat.card_pos hdvd
  have heq := Subgroup.eq_of_le_of_card_ge hU hcard
  rw [← heq]

theorem mem_curtisDatum_U_iff (hF : Nat.card F = (p ^ f) ^ 2) (n : ℕ) (hn : 2 ≤ n)
    (ζ : traceZero (unitaryInvolution F p f)) (hζ : (ζ : F) ≠ 0)
    (g : SU (unitaryInvolution F p f) n) :
    g ∈ (curtisDatum hF n hn ζ hζ).U ↔
      (∀ a b : Fin n, b < a → mat (unitaryInvolution F p f) n g a b = 0) ∧
        ∀ a : Fin n, mat (unitaryInvolution F p f) n g a a = 1 := by
  have hU : (curtisDatum hF n hn ζ hζ).U = posUnipotent (rootDatum hF n) := by
    unfold curtisDatum curtisDatumOf
    rfl
  have hVU := upperUniSU_le_posUnipotent hF n hn ζ hζ
  have hUV := posUnipotent_le_upperUniSU hF n
  rw [hU]
  constructor
  · intro hg
    have h := mem_upperUniSU_iff.mp (hUV hg)
    rw [Matrix.isUpperUnitriangular_def] at h
    exact ⟨fun a b hab => h.1 (i := a) (j := b) hab, h.2⟩
  · intro hg
    refine hVU ?_
    rw [mem_upperUniSU_iff, Matrix.isUpperUnitriangular_def]
    exact ⟨fun i j hij => hg.1 i j hij, hg.2⟩

end CFSG.LieType.Universal.Unitary
