module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ThirdLineAuxCore
public import CFSG.RankThree.PartOne.KE.E8FiveData

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.ThirdLineAux

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne
open CFSG.RankThree.E6 (chainRoot weylMatrix weylMatrix_mulVec weylMatrix_pow)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.KE
open CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
open scoped Matrix Pointwise

set_option linter.unusedSectionVars false



theorem twThirdLine_e8Five_aux (K : Type) [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime]
    [CharP K ℓ] (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) (δ : ℤ) (hδ : δ = 1 ∨ δ = -1) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 < p) (hp7 : 7 < p) {m : ℕ} (hm : m = 5 ∨ m = 10)
    (hordq : orderOf ((Nat.card K : ℕ) : ZMod p) = m) (hpq : ¬ p ∣ Nat.card K)
    (hΦ : (((δ : ℤ) : ZMod p) * ((Nat.card K : ℕ) : ZMod p)) ^ 4 +
      (((δ : ℤ) : ZMod p) * ((Nat.card K : ℕ) : ZMod p)) ^ 3 +
      (((δ : ℤ) : ZMod p) * ((Nat.card K : ℕ) : ZMod p)) ^ 2 +
      (((δ : ℤ) : ZMod p) * ((Nat.card K : ℕ) : ZMod p)) + 1 = 0)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    (n : ModGL .E8 L) (hnm : n ∈ monomialSubgroup .E8 L)
    (hnW : ∀ u, weylQuotientHom .E8 L ⟨n, hnm⟩ • u = (δ • weylMatrix e8F5U) *ᵥ u) :
    TwThirdLine .E8 K p := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have : Fintype K := Fintype.ofFinite K
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  set Φ : ModGL .E8 L →* ModGL .E8 L := Units.map (entrywiseHom Fr) with hΦdef
  have hFr' : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact hFr' c
  have hℓq : ℓ ∣ Nat.card K := by
    rw [hK]
    exact dvd_pow_self _ (by omega)
  have hℓ : ℓ.Prime := Fact.out
  have hnC : n ∈ adjointGroup .E8 L := monomialSubgroup_le_adjointGroup' hnm
  have hinj0 : Function.Injective (rootDiagUnitHom .E8 L) := rootDiagUnit_injective
  have hT : twistedTorusOf n Φ = (fixedCharTuples (e8FiveM δ) Fr).map (rootDiagUnitHom .E8 L) := by
    have h := twistedFixedTuples_eq_fixedCharTuples hnW Fr
    rw [show e8FiveM δ = δ • weylMatrix e8F5U from rfl, ← h]
    exact twistedTorus_eq_map_twistedFixedTuples_of_weylImage hnm _ rfl Fr
  set G4 := fixedBlockTuples (e8FiveM δ) Fr
    (e8FiveCols 4 δ '' {i : Fin Tag.E8.rank | (i : ℕ) < 4}) with hG4
  set G0 := fixedBlockTuples (e8FiveM δ) Fr
    (e8FiveCols 0 δ '' {i : Fin Tag.E8.rank | (i : ℕ) < 4}) with hG0
  set N : ℕ := (((Nat.card K : ℤ) ^ 4 + δ * (Nat.card K : ℤ) ^ 3 + (Nat.card K : ℤ) ^ 2 +
    δ * (Nat.card K : ℤ) + 1).natAbs) ^ 2 with hNdef
  set Z0 : Subgroup (ModGL .E8 L) := (G4 ⊔ G0).map (rootDiagUnitHom .E8 L) with hZ0def
  have hZ0le : Z0 ≤ twistedTorusOf n Φ := by
    rw [hT]
    exact Subgroup.map_mono (sup_le inf_le_left inf_le_left)
  have hZ0card : Nat.card Z0 = N := by
    rw [hZ0def, Subgroup.card_map_of_injective hinj0]
    exact e8Five_card_sup δ hδ Fr hFr hℓ hℓq hq2
  have hN : N ≠ 0 := by
    refine pow_ne_zero 2 (Int.natAbs_ne_zero.2 ?_)
    have := e8FiveP_eval_ne_zero δ hδ hq2
    rwa [e8FiveP_eval] at this
  have hord : p ^ (Nat.card (adjointGroup .E8 K)).factorization p = p ^ N.factorization p :=
    e8Five_ordProj K δ hδ hp hp5 hm hordq hpq hΦ
  obtain ⟨g0, hg0C, hg0, hperf, hconj⟩ := sigma_untwisted_sylow .E8 1
    (Or.inr (Or.inr ⟨rfl, rfl⟩)) K hf hK L hp (by omega) n hnC Z0 hZ0le hN hZ0card hord
  have hconj' : ∀ Q : Subgroup (adjointGroup .E8 K), IsPGroup p Q →
      ∃ c : adjointGroup .E8 K, ∀ y ∈ Q,
        g0⁻¹ * adjEmb .E8 K L (c * y * c⁻¹) * g0 ∈ twistedTorusOf n Φ := by
    intro Q hQ
    obtain ⟨c, hc⟩ := hconj Q hQ
    exact ⟨c, fun y hy => hZ0le ((mem_subtorusImage_iff _ _ _ _).1 (hc y hy))⟩
  have hbound : ∀ b : Fin Tag.E8.rank → Lˣ, rootDiagUnit .E8 b ∈ twistedTorusOf n Φ →
      (∀ i, b i ^ p = 1) → b ≠ 1 → (rootCharKernel b).ncard ≤ 25 := by
    intro b hbT hbp hb1
    have hbfix : b ∈ fixedCharTuples (e8FiveM δ) Fr := by
      rw [hT] at hbT
      obtain ⟨b', hb', hb'e⟩ := hbT
      have : b' = b := hinj0 hb'e
      rw [← this]
      exact hb'
    rcases e8Five_kernel_of_fixed δ hδ Fr hFr hp hp5 hΦ hbfix hbp hb1 with h0 | ⟨v, hS, -⟩
    · rw [h0, Set.ncard_empty]
      omega
    · rw [hS]
      have hsub : sigmaSetE8A4 v ⊆
          Set.range (fun ij : Fin 5 × Fin 5 => sigmaRootE8A4 v ij.1 ij.2) := by
        intro r hr
        obtain ⟨i, j, -, rfl⟩ := mem_sigmaSetE8A4_iff.1 hr
        exact ⟨(i, j), rfl⟩
      calc _ ≤ (Set.range (fun ij : Fin 5 × Fin 5 => sigmaRootE8A4 v ij.1 ij.2)).ncard :=
            Set.ncard_le_ncard hsub (Set.finite_range _)
        _ ≤ (Set.univ : Set (Fin 5 × Fin 5)).ncard := by
            rw [← Set.image_univ]
            exact Set.ncard_image_le Set.finite_univ
        _ = 25 := by rw [Set.ncard_univ]; simp
  have hperx : ∀ (x c : adjointGroup .E8 K) (b : Fin Tag.E8.rank → Lˣ), orderOf x = p →
      g0⁻¹ * adjEmb .E8 K L (c * x * c⁻¹) * g0 ∈ twistedTorusOf n Φ →
      rootDiagUnit .E8 b = g0⁻¹ * adjEmb .E8 K L (c * x * c⁻¹) * g0 →
      (rootCharKernel b).Nonempty →
      ¬ Group.IsSolvable ↥(Subgroup.centralizer ({x} : Set (adjointGroup .E8 K))) := by
    intro x c b hx hh hb hne
    obtain ⟨ψ, hψinj, -, -, hψK⟩ := e8_five_perx K hf hK δ hδ hp hp5 hp7 hΦ L n hnm hnW g0 hg0C
      hg0 hperf hT hx c hh
    obtain ⟨Pt, hPq, hcomm, -⟩ := hψK b hb hne
    exact not_isSolvable_of_embedding ψ hψinj hPq (hcomm ▸ commutator_le_self' _)
  exact twThirdLine_of_kernel Φ n g0 hp hconj' 25 (by rw [card_rootFinset_E8]; norm_num) hbound
    hperx

theorem twThirdLine_e8Ten (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hord : orderOf ((Nat.card K : ℕ) : ZMod p) = 10) : TwThirdLine .E8 K p := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨ℓ, f, hℓ, hchar, hf, hK⟩ := exists_char_pow K
  let L := AlgebraicClosure K
  haveI : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  have hq0 : ((Nat.card K : ℕ) : ZMod p) ≠ 0 := fun h => by
    rw [h, orderOf_zero] at hord
    omega
  have hdvd : 10 ∣ p - 1 := hord ▸ ZMod.orderOf_dvd_card_sub_one hq0
  have hp7 : 7 < p := by omega
  have hpq : ¬ p ∣ Nat.card K := fun h => hq0 ((ZMod.natCast_eq_zero_iff _ _).2 h)
  have hΦ' := phi10_of_orderOf hord
  have hcm := canonicalRep_mem_monomialSubgroup L (e8F5C ^ 21)
  have hπ : weylQuotientHom .E8 L ⟨canonicalRep (coxeterSystem .E8) L (e8F5C ^ 21), hcm⟩ =
      e8F5C ^ 21 := weylQuotientHom_eq (mapsRootLines_canonicalRep (e8F5C ^ 21))
  have hnW : ∀ u, weylQuotientHom .E8 L
      ⟨canonicalRep (coxeterSystem .E8) L (e8F5C ^ 21), hcm⟩ • u =
        ((-1 : ℤ) • weylMatrix e8F5U) *ᵥ u := fun u => by
    rw [hπ, ← weylMatrix_mulVec, weylMatrix_e8F5C_21, neg_one_smul]
  exact twThirdLine_e8Five_aux K hf hK (-1) (Or.inr rfl) hp (by omega) hp7 (m := 10) (Or.inr rfl)
    hord hpq (e8Five_hΦ_neg _ hΦ') L _ hcm hnW

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.ThirdLineAux
