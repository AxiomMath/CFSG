module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ThirdLineAuxCore
public import CFSG.RankThree.PartOne.KF4.F4ThreeData

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.ThirdLineAux

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne
open CFSG.RankThree.E6 (chainRoot weylMatrix weylMatrix_mulVec weylMatrix_pow)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KF4
open CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
open scoped Matrix Pointwise

set_option linter.unusedSectionVars false


theorem ncard_offdiag_le_nine {α : Type*} (g : Fin 3 → Fin 3 → α) :
    {r | ∃ i j : Fin 3, i ≠ j ∧ r = g i j}.ncard ≤ 9 := by
  have hsub : {r | ∃ i j : Fin 3, i ≠ j ∧ r = g i j} ⊆
      Set.range (fun ij : Fin 3 × Fin 3 => g ij.1 ij.2) := by
    rintro r ⟨i, j, -, rfl⟩
    exact ⟨(i, j), rfl⟩
  calc _ ≤ (Set.range (fun ij : Fin 3 × Fin 3 => g ij.1 ij.2)).ncard :=
        Set.ncard_le_ncard hsub (Set.finite_range _)
    _ ≤ (Set.univ : Set (Fin 3 × Fin 3)).ncard := by
        rw [← Set.image_univ]
        exact Set.ncard_image_le Set.finite_univ
    _ = 9 := by rw [Set.ncard_univ]; simp

theorem twThirdLine_f4_aux (K : Type) [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) (δ : ℤ) (hδ : δ = 1 ∨ δ = -1)
    (hq3 : δ = -1 → 2 < ℓ ^ f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hΦ : (((δ : ℤ) : ZMod p) * ((Nat.card K : ℕ) : ZMod p)) ^ 2 +
      ((δ : ℤ) : ZMod p) * ((Nat.card K : ℕ) : ZMod p) + 1 = 0)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    (n : ModGL .F4 L) (hnm : n ∈ monomialSubgroup .F4 L)
    (hnW : ∀ u, weylQuotientHom .F4 L ⟨n, hnm⟩ • u = (δ • weylMatrix f4W3) *ᵥ u) :
    TwThirdLine .F4 K p := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have : Fintype K := Fintype.ofFinite K
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  set Φ : ModGL .F4 L →* ModGL .F4 L := Units.map (entrywiseHom Fr) with hΦdef
  have hFr' : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact hFr' c
  have hℓq : ℓ ∣ Nat.card K := by
    rw [hK]
    exact dvd_pow_self _ (by omega)
  have hℓ : ℓ.Prime := Fact.out
  have hnC : n ∈ adjointGroup .F4 L := monomialSubgroup_le_adjointGroup' hnm
  have hinj0 : Function.Injective (rootDiagUnitHom .F4 L) := rootDiagUnit_injective
  have hT : twistedTorusOf n Φ = (fixedCharTuples (f4ThreeM δ) Fr).map (rootDiagUnitHom .F4 L) := by
    have h := twistedFixedTuples_eq_fixedCharTuples hnW Fr
    rw [show f4ThreeM δ = δ • weylMatrix f4W3 from rfl, ← h]
    exact twistedTorus_eq_map_twistedFixedTuples_of_weylImage hnm _ rfl Fr
  set N : ℕ := (((Nat.card K : ℤ) ^ 2 + δ * (Nat.card K : ℤ) + 1).natAbs) ^ 2 with hNdef
  set Z0 : Subgroup (ModGL .F4 L) := (f4ThreeZ δ Fr).map (rootDiagUnitHom .F4 L) with hZ0def
  have hZ0le : Z0 ≤ twistedTorusOf n Φ := by
    rw [hT]
    exact Subgroup.map_mono (sup_le inf_le_left inf_le_left)
  have hZ0card : Nat.card Z0 = N := by
    rw [hZ0def, Subgroup.card_map_of_injective hinj0]
    exact f4Three_card_Z δ hδ Fr hFr hℓ hℓq hq2
  have hN : N ≠ 0 := by
    refine pow_ne_zero 2 (Int.natAbs_ne_zero.2 ?_)
    have := f4ThreeP_eval_ne_zero δ hδ hq2
    rwa [f4ThreeP_eval] at this
  have hord : p ^ (Nat.card (adjointGroup .F4 K)).factorization p = p ^ N.factorization p :=
    f4Three_ordProj K δ hδ hp hp3 hΦ
  obtain ⟨g0, hg0C, hg0, hperf, hconj⟩ := sigma_untwisted_sylow_F4 K hf hK L hp hp3 n hnC Z0 hZ0le
    hN hZ0card hord
  have hconj' : ∀ Q : Subgroup (adjointGroup .F4 K), IsPGroup p Q →
      ∃ c : adjointGroup .F4 K, ∀ y ∈ Q,
        g0⁻¹ * adjEmb .F4 K L (c * y * c⁻¹) * g0 ∈ twistedTorusOf n Φ := by
    intro Q hQ
    obtain ⟨c, hc⟩ := hconj Q hQ
    exact ⟨c, fun y hy => hZ0le ((mem_subtorusImage_iff _ _ _ _).1 (hc y hy))⟩
  have hbound : ∀ b : Fin Tag.F4.rank → Lˣ, rootDiagUnit .F4 b ∈ twistedTorusOf n Φ →
      (∀ i, b i ^ p = 1) → b ≠ 1 → (rootCharKernel b).ncard ≤ 9 := by
    intro b hbT hbp hb1
    have hbfix : b ∈ fixedCharTuples (f4ThreeM δ) Fr := by
      rw [hT] at hbT
      obtain ⟨b', hb', hb'e⟩ := hbT
      have : b' = b := hinj0 hb'e
      rw [← this]
      exact hb'
    rcases f4Three_kernel_of_fixed δ hδ Fr hFr hp hp3 hbfix hbp hb1 with
      h0 | ⟨v, ⟨hS, -⟩ | ⟨hS, -⟩⟩
    · rw [h0, Set.ncard_empty]
      omega
    · rw [hS]
      exact ncard_offdiag_le_nine _
    · rw [hS]
      exact ncard_offdiag_le_nine _
  have hperx : ∀ (x c : adjointGroup .F4 K) (b : Fin Tag.F4.rank → Lˣ), orderOf x = p →
      g0⁻¹ * adjEmb .F4 K L (c * x * c⁻¹) * g0 ∈ twistedTorusOf n Φ →
      rootDiagUnit .F4 b = g0⁻¹ * adjEmb .F4 K L (c * x * c⁻¹) * g0 →
      (rootCharKernel b).Nonempty →
      ¬ Group.IsSolvable ↥(Subgroup.centralizer ({x} : Set (adjointGroup .F4 K))) := by
    intro x c b hx hh hb hne
    obtain ⟨ψ, hψinj, -, -, hψK⟩ := f4_three_perx K hf hK δ hδ hq3 hp hp3 L n hnm hnW g0 hg0C
      hg0 hperf hT hx c hh
    obtain ⟨Pt, hPq, hcomm, -⟩ := hψK b hb hne
    exact not_isSolvable_of_embedding ψ hψinj hPq (hcomm ▸ commutator_le_self' _)
  refine twThirdLine_of_kernel Φ n g0 hp hconj' 9 (by rw [card_rootFinset_F4]; norm_num) hbound
    hperx

theorem twThirdLine_f4Six (K : Type) [Field K] [Finite K] (hK3 : 3 ≤ Nat.card K) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p)
    (hord : orderOf ((Nat.card K : ℕ) : ZMod p) = 6) : TwThirdLine .F4 K p := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨ℓ, f, hℓ, hchar, hf, hK⟩ := exists_char_pow K
  let L := AlgebraicClosure K
  haveI : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  have hcm := canonicalRep_mem_monomialSubgroup L (f4Cox ^ 10)
  have hπ : weylQuotientHom .F4 L ⟨canonicalRep (coxeterSystem .F4) L (f4Cox ^ 10), hcm⟩ =
      f4Cox ^ 10 := weylQuotientHom_eq (mapsRootLines_canonicalRep (f4Cox ^ 10))
  have hnW : ∀ u, weylQuotientHom .F4 L ⟨canonicalRep (coxeterSystem .F4) L (f4Cox ^ 10), hcm⟩ •
      u = ((-1 : ℤ) • weylMatrix f4W3) *ᵥ u := fun u => by
    rw [hπ, ← weylMatrix_mulVec, weylMatrix_f4Cox_ten, neg_one_smul]
  have hΦ' : ((Nat.card K : ℕ) : ZMod p) ^ 2 - ((Nat.card K : ℕ) : ZMod p) + 1 = 0 :=
    phi6_of_orderOf hord
  exact twThirdLine_f4_aux K hf hK (-1) (Or.inr rfl) (fun _ => by omega) hp (by omega)
    (f4Three_hΦ_neg _ hΦ') L _ hcm hnW

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.ThirdLineAux
