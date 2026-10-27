module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabIrrPow
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommLinTransferAut
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusBase
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabIrrLinModel
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabIrrLinAut
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommLinTransferNormFix
import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusLinThreeSetup
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherOuterQuotients

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabIrr

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.LeviBlock CFSG.LocalAnalysis.ComponentInitial
  LinearFlag
open CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm
open CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Lin
open CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabIrr.Lin
open scoped commutatorElement

theorem isCoprime_two_pow_of_odd_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (k : ℕ) :
    IsCoprime (((2 ^ k : ℕ)) : ℤ) (p : ℤ) :=
  Nat.isCoprime_iff_coprime.2
    (Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)))

section Pow

variable {A : Type} [Group A] [Finite A] {Y P : Subgroup A} {n : ℕ} {K : Type} [Field K]
  [Finite K] [CharP K 2] {I : Set ℕ}

theorem actsAsPow_of_conj_field (C : LinCover Y P n K I) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hI : ∀ i ∈ I, 1 ≤ i ∧ i < n) (hn3 : 3 ≤ n) (hblk : ∃ a : Fin n, 2 ≤ linBlockLen n I a)
    (hPY : P ≤ Y) {B : Subgroup A} (hBM : B ≤ Subgroup.normalizer (Y : Set A))
    (hBp : IsPGroup p ↥B) (hBP : B ≤ Subgroup.normalizer (P : Set A))
    (hW : ∀ b ∈ B, WCent P b) {m : ↥(Subgroup.normalizer (Y : Set A))}
    (hmB : ∀ b ∈ B, (m : A) * b * (m : A)⁻¹ ∈ B)
    (hflag : (projFlag K n I).map (C.autHom m).toMonoidHom = projFlag K n I)
    {C' : GL (Fin n) K} {σ : K ≃+* K} {k : ℕ} (hσ : ∀ a, σ a = a ^ 2 ^ k)
    (hm : C.autHom m = conjAut n K C' * fieldAut n K σ) :
    ActsAsPow C.autHom B hBM m (((2 ^ k : ℕ)) : ℤ) := by
  refine actsAsPow_of_two_pow hp hp2 hBM hBp hmB _ fun b hb => ?_
  have hp_odd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨j, hj⟩ := hBp ⟨b, hb⟩
  have hbj : b ^ p ^ j = 1 := by simpa using congrArg Subtype.val hj
  have hNF := C.normFix_autHom hPY (by omega) ⟨b, hBM hb⟩ (hBP hb) (hW b hb)
  obtain ⟨A', hA', h1, h2, h3⟩ :=
    exists_conj_of_normFix hn3 hI hblk (C.odd_orderOf_autHom ⟨b, hBM hb⟩ hp_odd hbj) hNF
  rw [hm] at hflag
  obtain ⟨i, hi⟩ := exists_pow_two_eq_one_conj_field (by omega) hI hσ hflag h1 h2 h3
  refine ⟨i, ?_⟩
  rw [hm, hA', zpow_natCast]
  exact hi

end Pow

theorem parabIrr_of_projectiveSL
    (hGA : CFSG.Open.GriessAllModelsStatement) {A : Type} [Group A] [Finite A]
    {Y P B N : Subgroup A} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hY : CFSG.Open.IsQuasisimple ↥Y) (h2 : pCoreOf 2 Y = ⊥) {n f : ℕ} (hn : 2 ≤ n) (hf : 1 ≤ f)
    (e : ↥Y ⧸ Subgroup.center ↥Y ≃* projectiveSL n (GaloisField 2 f))
    (hpar : IsParabolicTwo Y P) (hne : P ≠ Y)
    (hna : ∃ x ∈ P, ∃ y ∈ P, x * y * x⁻¹ * y⁻¹ ∉ pCoreOf 2 P)
    (hB : IsPGroup p ↥B) (hcyc : ¬ IsCyclic ↥B) (hBY : B ≤ Subgroup.normalizer (Y : Set A))
    (hBP : B ≤ Subgroup.normalizer (P : Set A)) (hW : ∀ b ∈ B, WCent P b)
    (hNY : N ≤ Subgroup.normalizer (Y : Set A)) (hNP : N ≤ Subgroup.normalizer (P : Set A))
    (hNB : N ≤ Subgroup.normalizer (B : Set A)) (hirr : IrredOn N B) :
    ∀ b ∈ B, ∀ y ∈ Y, b * y = y * b := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : Odd (Nat.card (Subgroup.center ↥Y)) :=
    odd_card_center_of_pCore_eq_bot (pCore_eq_bot_of_pCoreOf h2)
  obtain ⟨I, C, hI, hne'⟩ := exists_linCover hGA hY hodd hn e hpar
  have hPY : P ≤ Y := hpar.1
  have hn1 : 1 ≤ n := by omega
  have hblock := C.exists_block hPY hn1 hna
  have hn3 : 3 ≤ n := by
    obtain ⟨a, ha⟩ := hblock
    exact three_le_of_two_le_linBlockLen hI (hne' hne) ha
  have hp_odd : Odd p := hp.odd_of_ne_two hp2
  have hperf : Group.IsPerfect ↥Y := ⟨hY.1⟩
  have hmB : ∀ x ∈ N, ∀ b ∈ B, x * b * x⁻¹ ∈ B := fun x hx b hb =>
    (Subgroup.mem_normalizer_iff.1 (hNB hx) b).1 hb
  let E : Subgroup (MulAut (projectiveSL n (GaloisField 2 f))) :=
    semilinearAutGroup n (GaloisField 2 f)
  let N₀ : Subgroup A :=
    N ⊓ (E.comap C.autHom).map (Subgroup.normalizer (Y : Set A)).subtype
  have hmemN₀ : ∀ x (hx : x ∈ N), x ∈ N₀ ↔ C.autHom ⟨x, hNY hx⟩ ∈ E := by
    intro x hx
    refine ⟨?_, fun h => ⟨hx, ⟨⟨x, hNY hx⟩, h, rfl⟩⟩⟩
    rintro ⟨-, ⟨y, hy, rfl⟩⟩
    exact hy
  have hN₀ : N₀ ≤ N := inf_le_left
  have hab : ∀ b₁ (h₁ : b₁ ∈ B) b₂ (h₂ : b₂ ∈ B),
      C.autHom ⟨b₁, hBY h₁⟩ * C.autHom ⟨b₂, hBY h₂⟩ =
        C.autHom ⟨b₂, hBY h₂⟩ * C.autHom ⟨b₁, hBY h₁⟩ := by
    intro b₁ h₁ b₂ h₂
    obtain ⟨k₁, hk₁⟩ := hB ⟨b₁, h₁⟩
    obtain ⟨k₂, hk₂⟩ := hB ⟨b₂, h₂⟩
    have hcB : ⁅b₁, b₂⁆ ∈ B := by
      rw [commutatorElement_def]
      exact B.mul_mem (B.mul_mem (B.mul_mem h₁ h₂) (B.inv_mem h₁)) (B.inv_mem h₂)
    obtain ⟨k₃, hk₃⟩ := hB ⟨_, hcB⟩
    have hk₁' : b₁ ^ p ^ k₁ = 1 := by simpa using congrArg Subtype.val hk₁
    have hk₂' : b₂ ^ p ^ k₂ = 1 := by simpa using congrArg Subtype.val hk₂
    have hk₃' : ⁅b₁, b₂⁆ ^ p ^ k₃ = 1 := by simpa using congrArg Subtype.val hk₃
    let β₁ : ↥(Subgroup.normalizer (Y : Set A)) := ⟨b₁, hBY h₁⟩
    let β₂ : ↥(Subgroup.normalizer (Y : Set A)) := ⟨b₂, hBY h₂⟩
    have hodd₃ : Odd (orderOf ⁅C.autHom β₁, C.autHom β₂⁆) := by
      rw [← map_commutatorElement]
      exact C.odd_orderOf_autHom ⁅β₁, β₂⁆ hp_odd hk₃'
    exact commutatorElement_eq_one_iff_mul_comm.mp (linModelComm_holds (GaloisField 2 f) n I hn3 hI
      hblock (C.autHom β₁) (C.autHom β₂) (C.odd_orderOf_autHom β₁ hp_odd hk₁')
      (C.odd_orderOf_autHom β₂ hp_odd hk₂') hodd₃ (C.normFix_autHom hPY hn1 β₁ (hBP h₁) (hW b₁ h₁))
      (C.normFix_autHom hPY hn1 β₂ (hBP h₂) (hW b₂ h₂)))
  have hidx : ∀ m ∈ N, ∀ x ∈ N, m ∉ N₀ → x ∉ N₀ → m⁻¹ * x ∈ N₀ := by
    intro m hm x hx hm0 hx0
    have hmx : m⁻¹ * x ∈ N := N.mul_mem (N.inv_mem hm) hx
    refine (hmemN₀ _ hmx).2 ?_
    have h1 : C.autHom ⟨m, hNY hm⟩ ∉ E := fun h => hm0 ((hmemN₀ m hm).2 h)
    have h2 : C.autHom ⟨x, hNY hx⟩ ∉ E := fun h => hx0 ((hmemN₀ x hx).2 h)
    have e : (⟨m⁻¹ * x, hNY hmx⟩ : ↥(Subgroup.normalizer (Y : Set A))) =
        ⟨m, hNY hm⟩⁻¹ * ⟨x, hNY hx⟩ := rfl
    rw [e, map_mul, map_inv]
    exact inv_mul_mem_semilinear hn3 h1 h2
  have hpow : ∀ m (hm : m ∈ N₀), ∃ s : ℤ,
      ActsAsPow C.autHom B hBY ⟨m, hNY (hN₀ hm)⟩ s := by
    intro m hm
    have hmN : m ∈ N := hN₀ hm
    obtain ⟨C', σ, hCσ⟩ := mem_semilinearAutGroup_iff.1 ((hmemN₀ m hmN).1 hm)
    obtain ⟨k, hk⟩ := exists_frobenius_galoisField hf σ
    exact ⟨_, actsAsPow_of_conj_field C hp hp2 hI hn3 hblock hPY hBY hB hBP hW (hmB m hmN)
      (C.map_projFlag ⟨m, hNY hmN⟩ (hNP hmN)) hk hCσ⟩
  have hsq : ∀ x (hx : x ∈ N), x ∉ N₀ → ∃ s : ℤ, IsCoprime s (p : ℤ) ∧
      ActsAsPow C.autHom B hBY ⟨x * x, hNY (N.mul_mem hx hx)⟩ (s * s) := by
    intro x hx hx0
    have hxx : x * x ∈ N := N.mul_mem hx hx
    have h1 : C.autHom ⟨x, hNY hx⟩ ∉ E := fun h => hx0 ((hmemN₀ x hx).2 h)
    obtain ⟨C', σ, hCσ⟩ := mem_semilinearAutGroup_iff.1 (mul_dualAut_mem_of_not_mem hn3 h1)
    obtain ⟨k, hk⟩ := exists_frobenius_galoisField hf σ
    have hσσ : ∀ a, (σ * σ) a = a ^ 2 ^ (k + k) := fun a => by
      rw [RingAut.mul_apply, hk, hk, ← pow_mul, ← pow_add]
    have hm : C.autHom ⟨x * x, hNY hxx⟩ = conjAut n (GaloisField 2 f) (C' *
        Matrix.GeneralLinearGroup.map (σ : GaloisField 2 f →+* GaloisField 2 f)
          (Matrix.GeneralLinearGroup.inverseTranspose C')) *
            fieldAut n (GaloisField 2 f) (σ * σ) := by
      rw [← mul_self_eq_conj_field hCσ, ← map_mul]
      rfl
    have key := actsAsPow_of_conj_field C hp hp2 hI hn3 hblock hPY hBY hB hBP hW (hmB _ hxx)
      (C.map_projFlag ⟨x * x, hNY hxx⟩ (hNP hxx)) hσσ hm
    refine ⟨((2 ^ k : ℕ) : ℤ), isCoprime_two_pow_of_odd_prime hp hp2 k, ?_⟩
    have hexp : (((2 ^ (k + k) : ℕ)) : ℤ) = ((2 ^ k : ℕ) : ℤ) * ((2 ^ k : ℕ) : ℤ) := by
      push_cast
      ring
    rwa [hexp] at key
  have hall := forall_eq_one_of_index_two (ρ := C.autHom) hp hp2 hBY hNY hB hcyc hirr hNB hab hN₀
    hidx hpow hsq
  intro b hb y hy
  exact C.centralizes_of_autHom_eq_one ⟨b, hBY hb⟩ (hall b hb) y hy

theorem parabIrrOn_idxA_of
    (hGA : CFSG.Open.GriessAllModelsStatement) :
    ParabIrrOn (CFSG.AGLEmbedding.IsLieOf CFSG.AGLEmbedding.IdxA) := by
  intro A _ _ Y P B N p hp hp2 hY h2 hF hpar hne hna hB hcyc hBY hBP hW hNY hNP hNB hirr
  obtain ⟨n, f, hn, hf, ⟨e⟩⟩ := ToralCensus.exists_mulEquiv_projectiveSL_of_isLieOf hF
  exact Or.inl (parabIrr_of_projectiveSL hGA hp hp2 hY h2 hn hf e hpar hne hna hB hcyc hBY hBP hW
    hNY hNP hNB hirr)

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabIrr
