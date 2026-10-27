module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeBoundFieldIndex
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeGLMark
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges
public import CFSG.Blueprint.LieModelAPI
public import CFSG.GH74.GLS.IVK.Proofs2.OddTools
public import CFSG.GH74.GLS.Stage2.Local.P34Main
public import CFSG.GH74.GLS.Stage2.Local.P34S5A
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CoatomAbs
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GenCell
public import CFSG.LargeExtraspecial.OfFStar
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevInnerCover
public import CFSG.Models.Transport

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

@[expose] def LinTypeOneNonComm : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p N n : ℕ) (L J A : Subgroup G) (d b : G)
    (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ n → 3 ≤ N →
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* LargeEvenProj (LargeEvenSLGroup (Fin N) K)) →
    (hact : ∀ a ∈ A, ∃ φ ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K)) Set.univ,
      LargeEvenInduces θ (conjRel a) φ) →
    (hS : (Set.univ : Set (GL (Fin N) K)) ⊆ Subgroup.normalizer
      (LargeEvenSLGroup (Fin N) K : Set (GL (Fin N) K))) →
    (hsetup : Setup p L J A d b) →
    ∀ M : LiftMap (L := L) (A := A) (S := Set.univ) θ hact hS,
      (∃ c : Kˣ, (M.mat ⟨d, hsetup.d_mem⟩) ^ p =
        Matrix.GeneralLinearGroup.scalar (Fin N) (c ^ p)) →
      M.mat ⟨b, hsetup.b_mem⟩ * M.mat ⟨d, hsetup.d_mem⟩ ≠
        M.mat ⟨d, hsetup.d_mem⟩ * M.mat ⟨b, hsetup.b_mem⟩ → False

@[expose] def UniTypeOneNonComm : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p N n : ℕ) (L J A : Subgroup G) (d b : G)
    (K : Type) [Field K] [Finite K] (h : UnitaryFieldData 2 n K),
    p.Prime → p ∣ 2 ^ n + 1 → 3 ≤ N → (N, 2 ^ n) ≠ (3, 2) →
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* LargeEvenProj (unitarySU 2 n K N)) →
    (hact : ∀ a ∈ A, ∃ φ ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (unitarySU 2 n K N)) (LargeEvenGUSet (Fin N) K (2 ^ n)),
      LargeEvenInduces θ (conjRel a) φ) →
    (hS : LargeEvenGUSet (Fin N) K (2 ^ n) ⊆ Subgroup.normalizer
      (unitarySU 2 n K N : Set (GL (Fin N) K))) →
    (hsetup : Setup p L J A d b) →
    ∀ M : LiftMap (L := L) (A := A) (S := LargeEvenGUSet (Fin N) K (2 ^ n)) θ hact hS,
      (∃ c : Kˣ, (M.mat ⟨d, hsetup.d_mem⟩) ^ p =
        Matrix.GeneralLinearGroup.scalar (Fin N) (c ^ p)) →
      M.mat ⟨b, hsetup.b_mem⟩ * M.mat ⟨d, hsetup.d_mem⟩ ≠
        M.mat ⟨d, hsetup.d_mem⟩ * M.mat ⟨b, hsetup.b_mem⟩ → False

section Assembly


theorem linUniBoundOther_of_block (hLB : LinBlockInnDiag) (hUB : UniBlockInnDiag)
    (hLNC : LinTypeOneNonComm) (hUNC : UniTypeOneNonComm)
    (hAL : LinFieldTypeA0Bound) (hAU : UniFieldTypeA0Bound) : LinUniBoundOther := by
  intro G _ _ p L J A d b N hsetup hcat _
  obtain ⟨i, hv, hi, he⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.exists_lieIndex hcat
  obtain ⟨q0, hA | hU', hshape⟩ := hi
  ·
    subst hA
    have hcardq : q0.card = 2 ^ q0.exponent := by
      rw [TauCeti.PrimePower.card_def, hshape.1]
    have hcatLin : catalogIs (PSimple p L) (onLie fun i =>
        ∃ q : TauCeti.PrimePower, i = .A (N - 1) q ∧ q.card = 2 ^ q0.exponent) :=
      ⟨.lie ⟨.A (N - 1) q0, hv⟩, ⟨q0, rfl, hcardq⟩, he⟩
    have hN2 : 2 ≤ N := by
      have h := ((TauCeti.LieTypeIndex.inStandardRange_iff _).mp
        ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1).1
      omega
    have hpN : p ∣ N := by
      have h : p ∣ N.gcd (q0.card - 1) := by
        have h' := hshape.2
        rwa [show N - 1 + 1 = N by omega] at h'
      exact (Nat.dvd_gcd_iff.mp h).1
    have hp3 : 3 ≤ p :=
      Nat.succ_le_of_lt (Nat.lt_of_le_of_ne hsetup.prime.two_le (Ne.symm hsetup.odd))
    have hNpos : 0 < N := by omega
    haveI : Nonempty (Fin N) := ⟨⟨0, hNpos⟩⟩
    have hN : 3 ≤ N := le_trans hp3 (Nat.le_of_dvd hNpos hpN)
    obtain ⟨K, hK, hKfin, hKcard, θ, hact⟩ :=
      linMarking_holds G p L J A d b N q0.exponent hsetup.toWSetup hcatLin
    letI := hK
    letI := hKfin
    have hS : (Set.univ : Set (GL (Fin N) K)) ⊆ Subgroup.normalizer
        (LargeEvenSLGroup (Fin N) K : Set (GL (Fin N) K)) := by
      intro x _
      rw [Subgroup.normalizer_eq_top_iff.mpr
        (inferInstance : (LargeEvenSLGroup (Fin N) K).Normal)]
      exact Subgroup.mem_top x
    obtain ⟨M⟩ := LiftMap.exists (L := L) (A := A) (S := Set.univ) θ hact hS
    have hDp := M.dpow_mem_scalars (L := L) (A := A) hsetup
      (linKernelScalar_of_three_le (K := K) (N := N) hN)
    obtain ⟨lam, hlam⟩ := hDp
    have hlam' : M.mat ⟨d, hsetup.d_mem⟩ ^ p =
        Matrix.GeneralLinearGroup.scalar (Fin N) lam := hlam.symm
    by_cases hcube : ∃ c : Kˣ, c ^ p = lam
    · obtain ⟨c, hc⟩ := hcube
      have hc' : ∃ c : Kˣ, M.mat ⟨d, hsetup.d_mem⟩ ^ p =
          Matrix.GeneralLinearGroup.scalar (Fin N) (c ^ p) := ⟨c, by rw [hlam', hc]⟩
      by_cases hcomm : M.mat ⟨b, hsetup.b_mem⟩ * M.mat ⟨d, hsetup.d_mem⟩ =
          M.mat ⟨d, hsetup.d_mem⟩ * M.mat ⟨b, hsetup.b_mem⟩
      · exact (linTypeOne_commuting hLB hKcard θ hact hS hsetup M hc' hcomm).elim
      · exact (hLNC G p N q0.exponent L J A d b K hKcard hN θ hact hS hsetup M hc' hcomm).elim
    · obtain ⟨A₀, hA₀A, hcardA, hcomm⟩ :=
        linFieldTypeIndex_of_three_le (K := K) (N := N) (p := p) hN M hsetup hlam'
      have hA0 := hAL G p N q0.exponent L J A d b K hKcard hN θ hact hS hsetup M lam hlam'
        (fun c hc => hcube ⟨c, hc⟩) A₀ hA₀A hcomm
      calc Nat.card A ≤ p * Nat.card A₀ := hcardA
        _ ≤ p * p ^ (N / p) := Nat.mul_le_mul_left _ hA0
        _ = p ^ (1 + N / p) := by rw [pow_add, pow_one]
  ·
    subst hU'
    have hcardq : q0.card = 2 ^ q0.exponent := by
      rw [TauCeti.PrimePower.card_def, hshape.1]
    have hcatUni : catalogIs (PSimple p L) (onLie fun i =>
        ∃ q : TauCeti.PrimePower, i = .twistedA (N - 1) q ∧ q.card = 2 ^ q0.exponent) :=
      ⟨.lie ⟨.twistedA (N - 1) q0, hv⟩, ⟨q0, rfl, hcardq⟩, he⟩
    have hN2 : 2 ≤ N := by
      have h := ((TauCeti.LieTypeIndex.inStandardRange_iff _).mp
        ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1).1
      omega
    have hpN : p ∣ N := by
      have h : p ∣ N.gcd (q0.card + 1) := by
        have h' := hshape.2
        rwa [show N - 1 + 1 = N by omega] at h'
      exact (Nat.dvd_gcd_iff.mp h).1
    have hp3 : 3 ≤ p :=
      Nat.succ_le_of_lt (Nat.lt_of_le_of_ne hsetup.prime.two_le (Ne.symm hsetup.odd))
    have hNpos : 0 < N := by omega
    haveI : Nonempty (Fin N) := ⟨⟨0, hNpos⟩⟩
    have hN : 3 ≤ N := le_trans hp3 (Nat.le_of_dvd hNpos hpN)
    have hpq : p ∣ 2 ^ q0.exponent + 1 := by
      have h : p ∣ N.gcd (q0.card + 1) := by
        have h' := hshape.2
        rwa [show N - 1 + 1 = N by omega] at h'
      have hq : p ∣ q0.card + 1 := (Nat.dvd_gcd_iff.mp h).2
      rwa [hcardq] at hq
    have hNq : (N, 2 ^ q0.exponent) ≠ (3, 2) := by
      intro heq
      have hN3 : N = 3 := congrArg Prod.fst heq
      have hq2 : 2 ^ q0.exponent = 2 := congrArg Prod.snd heq
      have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
        ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
      have h3 : 3 ≤ q0.card := hrange.2 (by omega)
      have h3' : q0.card = 2 := hcardq.trans hq2
      omega
    obtain ⟨K, hK, hKfin, hUF, θ, hact⟩ :=
      uniMarking_holds G p L J A d b N q0.exponent hsetup.toWSetup hcatUni
    letI := hK
    letI := hKfin
    have hS : LargeEvenGUSet (Fin N) K (2 ^ q0.exponent) ⊆ Subgroup.normalizer
        (unitarySU 2 q0.exponent K N : Set (GL (Fin N) K)) :=
      TableBUE.gu_subset_normalizer hUF
    obtain ⟨M⟩ := LiftMap.exists (L := L) (A := A)
      (S := LargeEvenGUSet (Fin N) K (2 ^ q0.exponent)) θ hact hS
    have hDp := M.dpow_mem_scalars (L := L) (A := A) hsetup
      (uniKernelScalar (K := K) hUF hN hNq hsetup.prime hpq)
    obtain ⟨lam, hlam⟩ := hDp
    have hlam' : M.mat ⟨d, hsetup.d_mem⟩ ^ p =
        Matrix.GeneralLinearGroup.scalar (Fin N) lam := hlam.symm
    by_cases hcube : ∃ c : Kˣ, c ^ p = lam
    · obtain ⟨c, hc⟩ := hcube
      have hc' : ∃ c : Kˣ, M.mat ⟨d, hsetup.d_mem⟩ ^ p =
          Matrix.GeneralLinearGroup.scalar (Fin N) (c ^ p) := ⟨c, by rw [hlam', hc]⟩
      by_cases hcomm : M.mat ⟨b, hsetup.b_mem⟩ * M.mat ⟨d, hsetup.d_mem⟩ =
          M.mat ⟨d, hsetup.d_mem⟩ * M.mat ⟨b, hsetup.b_mem⟩
      · exact (uniTypeOne_commuting hUB hUF hsetup.prime hpq hN hNq hsetup M hc' hcomm).elim
      · exact (hUNC G p N q0.exponent L J A d b K hUF hsetup.prime hpq hN hNq θ hact hS hsetup M
          hc' hcomm).elim
    · obtain ⟨A₀, hA₀A, hcardA, hcomm⟩ :=
        uniFieldTypeIndex_of_side (K := K) (N := N) (p := p) hUF hN hNq hpq M hsetup hlam'
      have hA0 := hAU G p N q0.exponent L J A d b K hUF hN hNq hpq θ hact hS hsetup M lam
        hlam' (fun c hc => hcube ⟨c, hc⟩) A₀ hA₀A hcomm
      calc Nat.card A ≤ p * Nat.card A₀ := hcardA
        _ ≤ p * p ^ (N / p) := Nat.mul_le_mul_left _ hA0
        _ = p ^ (1 + N / p) := by rw [pow_add, pow_one]

end Assembly

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
