module

public import CFSG.HardMathSupport.Solomon.Coordinator.I271Defs202
public import CFSG.HardMathSupport.Solomon.Coordinator.I22_4Glue
public import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsAltGen
public import CFSG.LocalAnalysis.GLTheoremB.InputPiGenProof
public import CFSG.HardMathSupport.Solomon.Coordinator.I27_1Fam
public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Induction

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open Equiv Equiv.Perm MulAction CFSG.Open CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54Ns
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  GL83 GL83.CompFam
open scoped commutatorElement

section NN

variable {X : Type} [Group X] [Finite X]

theorem isInGOne_of_isInGMinusOne_of_four_le {B L : Subgroup X}
    (hB : 4 ≤ CFSG.Open.pRank 3 B) (h : IsInGMinusOne 3 B L) : IsInGOne 3 B L := by
  unfold IsInGOne coreIn
  apply le_antisymm
  · rw [IsInGMinusOne] at h
    refine h.le.trans ?_
    unfold gammaPrimeIn
    refine iSup_le fun E => iSup_le fun hE => ?_
    exact le_iSup₂_of_le E ⟨hE.1, by omega⟩
      (inf_le_inf_left _ (Subgroup.centralizer_le_normalizer _))
  · exact iSup₂_le fun Q _ => inf_le_left

theorem nn_caseA_of_hyperplane {K B : Subgroup X} (hK : GLAPComponent 3 ⊤ K)
    (hBel : IsElemAbelian 3 B) (h4 : 4 ≤ CFSG.Open.pRank 3 B)
    (hN1 : 1 ≤ CFSG.Open.pRank 3 (B ⊓ Subgroup.normalizer (K : Set X)))
    (hgen : K ≤ gammaPrimeIn 3 (CFSG.Open.pRank 3 (B ⊓ Subgroup.normalizer (K : Set X)) - 1)
      (B ⊓ Subgroup.normalizer (K : Set X)) K) : I271CaseA 3 K B :=
  ⟨h4, isInGOne_of_isInGMinusOne_of_four_le h4
    (input22_4_general Nat.prime_three le_top hBel hK hN1 hgen)⟩

theorem cent_le_centralizer_bClosure {p : ℕ} {B K E : Subgroup X} (hBel : IsElemAbelian p B)
    (hEB : E ≤ B) (hEK : E ≤ Subgroup.centralizer (K : Set X)) :
    bClosure B K ≤ Subgroup.centralizer (E : Set X) := by
  unfold bClosure
  refine iSup₂_le fun b hb x hx => ?_
  rw [mem_gLBConj] at hx
  rw [Subgroup.mem_centralizer_iff]
  intro e he
  have hbe : b * e = e * b := by
    have := hBel.1.is_comm.comm ⟨b, hb⟩ ⟨e, hEB he⟩
    exact congrArg Subtype.val this
  have hke : ∀ y ∈ K, e * y = y * e := fun y hy =>
    (Subgroup.mem_centralizer_iff.1 (hEK he) y hy).symm
  have hx' : x = b⁻¹ * (b * x * b⁻¹) * b := by group
  set k := b * x * b⁻¹ with hk
  have hkK : k ∈ K := hx
  have h1 : e * x = x * e := by
    rw [hx']
    calc e * (b⁻¹ * k * b) = b⁻¹ * (e * k) * b := by
          have : e * b⁻¹ = b⁻¹ * e := by
            calc e * b⁻¹ = b⁻¹ * (b * e) * b⁻¹ := by group
              _ = b⁻¹ * (e * b) * b⁻¹ := by rw [hbe]
              _ = b⁻¹ * e := by group
          calc e * (b⁻¹ * k * b) = (e * b⁻¹) * k * b := by group
            _ = b⁻¹ * e * k * b := by rw [this]
            _ = b⁻¹ * (e * k) * b := by group
      _ = b⁻¹ * (k * e) * b := by rw [hke k hkK]
      _ = (b⁻¹ * k * b) * e := by
          have : e * b = b * e := hbe.symm
          calc b⁻¹ * (k * e) * b = b⁻¹ * k * (e * b) := by group
            _ = b⁻¹ * k * (b * e) := by rw [this]
            _ = (b⁻¹ * k * b) * e := by group
  exact h1

theorem isInGOne_of_cent_rank {p : ℕ} {B K E : Subgroup X} (hBel : IsElemAbelian p B)
    (hEB : E ≤ B) (hEK : E ≤ Subgroup.centralizer (K : Set X)) (h3 : 3 ≤ CFSG.Open.pRank p E) :
    IsInGOne p B K := by
  unfold IsInGOne
  apply le_antisymm
  · have hcen := cent_le_centralizer_bClosure hBel hEB hEK
    have hK : bClosure B K ≤ Subgroup.normalizer ((E : Subgroup X) : Set X) := by
      intro x hx
      have : x ∈ Subgroup.centralizer (E : Set X) := hcen hx
      exact Subgroup.centralizer_le_normalizer _ this
    unfold coreIn
    exact le_iSup₂_of_le (f := fun (Q : Subgroup X) (_ : Q ≤ B ∧ 3 ≤ CFSG.Open.pRank p Q) =>
      bClosure B K ⊓ Subgroup.normalizer (Q : Set X)) E ⟨hEB, h3⟩ (le_inf le_rfl hK)
  · unfold coreIn
    exact iSup₂_le fun Q _ => inf_le_left

theorem nn_hatSeven_caseA {K B : Subgroup X} (hH : I271Hyp 3 K B) (hK7 : IsHatSeven ↥K) :
    I271CaseA 3 K B := by
  have hq : CFSG.Open.IsQuasisimple ↥K := i116e_isQuasisimple hH.core hH.comp
  haveI : Group.IsPerfect ↥K := ⟨hq.1⟩
  have hOK : GLAPPrimeCore 3 ↥K = ⊥ := i271h_primeCore_eq_bot hH.core hH.comp
  have hodd : Odd (Nat.card (Subgroup.center ↥K)) := odd_card_center hH.prime hH.odd hOK
  obtain ⟨-, -, ⟨e0⟩⟩ := hK7
  have e : ↥K ⧸ Subgroup.center ↥K ≃* alternatingGroup (Fin 7) := e0
  have hBel : IsElemAbelian 3 B := hH.scp.2.1
  set A : Subgroup X := B ⊓ Subgroup.normalizer (K : Set X) with hA
  have hAN : A ≤ Subgroup.normalizer (K : Set X) := inf_le_right
  have hAel : IsElemAbelian 3 A := elem_mono hBel inf_le_left
  have hgen : K ≤ centGenI 3 A K := le_centGenI_of_seven hAN hAel hodd e
  have hK' : K ≤ gammaPrimeIn 3 (CFSG.Open.pRank 3 A - 1) A K := by
    refine hgen.trans (iSup_le fun E => ?_)
    exact i224_le_gammaPrimeIn E.2.1 (i271h_pRank_sub_one_le hAel E.2.1 E.2.2)
  have hN1 : 1 ≤ CFSG.Open.pRank 3 A := by
    have hC : B ⊓ Subgroup.centralizer (K : Set X) ≠ ⊥ := hH.centralized
    have hCA : B ⊓ Subgroup.centralizer (K : Set X) ≤ A :=
      inf_le_inf_left _ (Subgroup.centralizer_le_normalizer _)
    have hCel : IsElemAbelian 3 (B ⊓ Subgroup.centralizer (K : Set X)) := elem_mono hBel inf_le_left
    obtain ⟨j, hj⟩ := exists_card_eq_pow hCel
    have hj1 : 1 ≤ j := by
      by_contra h0
      have : j = 0 := by omega
      rw [this, pow_zero] at hj
      exact hC (Subgroup.eq_bot_of_card_eq _ hj)
    exact hj1.trans (CFSG.SectionRank.le_pRank Nat.prime_three.one_lt hCA hCel hj)
  exact nn_caseA_of_hyperplane hH.comp hBel hH.rank_four hN1 hK'

end NN

section NNProof

variable {X : Type} [Group X] [Finite X]

theorem layer_conjSet_eq_bClosure (B K : Subgroup X) :
    GL83.CompFam.layer (conjSet B K) = bClosure B K := by
  apply le_antisymm
  · refine iSup₂_le fun K' hK' => ?_
    obtain ⟨b, hb, rfl⟩ := hK'
    intro x hx
    unfold bClosure
    refine (le_iSup₂_of_le (f := fun (c : X) (_ : c ∈ B) => GLBConj c K) b⁻¹ (B.inv_mem hb) ?_) hx
    intro y hy
    rw [mem_gLBConj]
    simpa using mem_cj.1 hy
  · unfold bClosure
    refine iSup₂_le fun b hb => ?_
    intro x hx
    refine le_layer (𝒦 := conjSet B K) (K := cj b⁻¹ K) ⟨b⁻¹, B.inv_mem hb, rfl⟩ ?_
    rw [mem_cj]
    simpa using mem_gLBConj.1 hx

theorem isInGOne_of_card_stab {p r : ℕ} (hp : p.Prime) {B K : Subgroup X}
    (hBel : IsElemAbelian p B) (hK : IsComponentOf K ⊤) (hr : 1 ≤ r)
    (hB : p ^ (3 + r) ≤ Nat.card B)
    (hA : Nat.card (stab B K) ≤ p ^ r * Nat.card (cen B K)) : IsInGOne p B K := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hF := isFam_conjSet hBel hK
  have h := hF.layer_le_centGen 3 (mem_conjSet_self B K) hr hB hA
  rw [layer_conjSet_eq_bClosure] at h
  unfold IsInGOne coreIn
  apply le_antisymm
  · refine h.trans (iSup₂_le fun E hEB => iSup_le fun hE => ?_)
    have hEel : IsElemAbelian p E := elem_mono hBel hEB
    obtain ⟨j, hj⟩ := exists_card_eq_pow hEel
    have hjk : 3 ≤ j := (Nat.pow_le_pow_iff_right hp.one_lt).1 (hj ▸ hE)
    have hrk : 3 ≤ CFSG.Open.pRank p E :=
      hjk.trans (CFSG.SectionRank.le_pRank hp.one_lt le_rfl hEel hj)
    exact le_iSup₂_of_le E ⟨hEB, hrk⟩
      (inf_le_inf_left _ (Subgroup.centralizer_le_normalizer _))
  · exact iSup₂_le fun Q _ => inf_le_left

end NNProof

section NNReduction

variable {X : Type} [Group X] [Finite X]

theorem nn_card_data {K B : Subgroup X} (hBel : IsElemAbelian 3 B)
    (hidx : (Subgroup.normalizer (K : Set X)).relIndex B = 3) :
    ∃ s c m : ℕ, autOrderIn B K = 3 ^ s ∧
      Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set X)) = 3 ^ c ∧ Nat.card B = 3 ^ m ∧
      Nat.card ↥(B ⊓ Subgroup.normalizer (K : Set X)) = 3 ^ s * 3 ^ c ∧ m = 1 + s + c ∧
      CFSG.Open.pRank 3 B = m ∧
      CFSG.Open.pRank 3 (B ⊓ Subgroup.centralizer (K : Set X)) = c := by
  set N : Subgroup X := Subgroup.normalizer (K : Set X) with hN
  set C0 : Subgroup X := B ⊓ Subgroup.centralizer (K : Set X) with hC0
  set A : Subgroup X := B ⊓ N with hA
  have hCN : Subgroup.centralizer (K : Set X) ≤ N := Subgroup.centralizer_le_normalizer _
  have hC0el : IsElemAbelian 3 C0 := elem_mono hBel inf_le_left
  have hAel : IsElemAbelian 3 A := elem_mono hBel inf_le_left
  have hBA : Nat.card B = 3 * Nat.card A := by
    have h := Subgroup.relIndex_mul_card (H := N) (K := B)
    rw [hidx, inf_comm] at h
    exact h.symm
  have hAC : Nat.card A = autOrderIn B K * Nat.card C0 := by
    have h := Subgroup.relIndex_mul_card (H := Subgroup.centralizer (K : Set X)) (K := A)
    have hinf : Subgroup.centralizer (K : Set X) ⊓ A = C0 := by
      ext x
      constructor
      · rintro ⟨hx1, hx2, hx3⟩
        exact ⟨hx2, hx1⟩
      · rintro ⟨hx1, hx2⟩
        exact ⟨hx2, hx1, hCN hx2⟩
    rw [hinf] at h
    exact h.symm
  obtain ⟨a, ha⟩ := exists_card_eq_pow hAel
  obtain ⟨c, hc⟩ := exists_card_eq_pow hC0el
  obtain ⟨m, hm⟩ := exists_card_eq_pow hBel
  have hdvd : autOrderIn B K ∣ 3 ^ a := ha ▸ Dvd.intro _ hAC.symm
  obtain ⟨s, -, hs⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  have hmsc : m = 1 + s + c := by
    have h1 : 3 ^ m = 3 ^ (1 + s + c) := by
      rw [← hm, hBA, hAC, hs, hc]; ring
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) h1
  refine ⟨s, c, m, hs, hc, hm, ?_, hmsc, i271_pRank_eq Nat.prime_three hBel hm,
    i271_pRank_eq Nat.prime_three hC0el hc⟩
  rw [hAC, hs, hc]

theorem nnUniform_holds (K B : Subgroup X) (hK : IsComponentOf K ⊤)
    (hBel : IsElemAbelian 3 B) (hNN : ¬ B ≤ Subgroup.normalizer (K : Set X))
    (hidx : (Subgroup.normalizer (K : Set X)).relIndex B = 3)
    (hnle : ¬ B ⊓ Subgroup.normalizer (K : Set X) ≤ B ⊓ Subgroup.centralizer (K : Set X))
    (hc2 : 2 ≤ CFSG.Open.pRank 3 (B ⊓ Subgroup.centralizer (K : Set X))) : IsInGOne 3 B K := by
  obtain ⟨s, c, m, hs, hc, hm, hA, hmsc, hpm, hpc⟩ := nn_card_data (K := K) hBel hidx
  rw [hpc] at hc2
  have hs1 : 1 ≤ s := by
    by_contra h0
    have : s = 0 := by omega
    apply hnle
    have hAcard : Nat.card ↥(B ⊓ Subgroup.normalizer (K : Set X)) =
        Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set X)) := by rw [hA, hc, this]; simp
    have hle : B ⊓ Subgroup.centralizer (K : Set X) ≤ B ⊓ Subgroup.normalizer (K : Set X) :=
      inf_le_inf_left _ (Subgroup.centralizer_le_normalizer _)
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hAcard])).symm ▸ le_rfl
  refine isInGOne_of_card_stab Nat.prime_three hBel hK hs1 ?_ ?_
  · rw [hm]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  · show Nat.card ↥(B ⊓ Subgroup.normalizer (K : Set X)) ≤
      3 ^ s * Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set X))
    rw [hA, hc]

theorem nn_caseA_or_exceptional {K B : Subgroup X} (hH : I271Hyp 3 K B)
    (hNN : ¬ B ≤ Subgroup.normalizer (K : Set X))
    (hidx : (Subgroup.normalizer (K : Set X)).relIndex B = 3)
    (hAut : autOrderIn B K ≤ 3 ^ 2) :
    I271CaseA 3 K B ∨ (CFSG.Open.pRank 3 B = 4 ∧ autOrderIn B K = 3 ^ 2) := by
  have hBel : IsElemAbelian 3 B := hH.scp.2.1
  have h4 : 4 ≤ CFSG.Open.pRank 3 B := hH.rank_four
  have hK : IsComponentOf K ⊤ := i116pI_isComponentOf hH.core hH.comp
  obtain ⟨r, c, m, hr, hc, hm, hA, hmrc, hpm, hpc⟩ := nn_card_data (K := K) hBel hidx
  have hr2 : r ≤ 2 := (Nat.pow_le_pow_iff_right (by norm_num)).1 (hr ▸ hAut)
  have hm4 : 4 ≤ m := hpm ▸ h4
  have hnotle : 1 ≤ r → ¬ B ⊓ Subgroup.normalizer (K : Set X) ≤ B ⊓ Subgroup.centralizer (K : Set X) := by
    intro hr1 hle
    have h1 := Subgroup.card_le_of_le hle
    rw [hA, hc] at h1
    have h3 : 3 ≤ 3 ^ r := by
      calc 3 = 3 ^ 1 := by norm_num
        _ ≤ 3 ^ r := Nat.pow_le_pow_right (by norm_num) hr1
    have h4 : 0 < 3 ^ c := by positivity
    nlinarith
  have hcase : IsInGOne 3 B K ∨ (m = 4 ∧ r = 2) := by
    by_cases hc3 : 3 ≤ c
    · exact Or.inl (isInGOne_of_cent_rank hBel inf_le_left inf_le_right (by rw [hpc]; exact hc3))
    · have hc2 : c ≤ 2 := by omega
      by_cases hr0 : r = 0
      · omega
      · by_cases hexc : m = 4 ∧ r = 2
        · exact Or.inr hexc
        · refine Or.inl (nnUniform_holds K B hK hBel hNN hidx ?_ ?_)
          · exact hnotle (by omega)
          · rw [hpc]; omega
  rcases hcase with h | ⟨hm4', hr2'⟩
  · exact Or.inl ⟨h4, h⟩
  · exact Or.inr ⟨hpm.trans hm4', by rw [hr, hr2']⟩

end NNReduction

section NNFamilies

@[expose] def NNFor (P : ∀ (X : Type) [Group X], Subgroup X → Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ K B : Subgroup X,
    I271Hyp 3 K B → ¬ B ≤ Subgroup.normalizer (K : Set X) → P X K →
      I271CaseA 3 K B ∨ IsStronglyBalancedIn 3 B K ∨ I271CaseC K B

@[expose] def NNFacts (P : ∀ (X : Type) [Group X], Subgroup X → Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ K B : Subgroup X,
    I271Hyp 3 K B → ¬ B ≤ Subgroup.normalizer (K : Set X) → P X K →
      (Subgroup.normalizer (K : Set X)).relIndex B = 3 ∧ autOrderIn B K ≤ 3 ^ 2

@[expose] def NNExc (P : ∀ (X : Type) [Group X], Subgroup X → Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ K B : Subgroup X,
    I271Hyp 3 K B → ¬ B ≤ Subgroup.normalizer (K : Set X) →
      (Subgroup.normalizer (K : Set X)).relIndex B = 3 → CFSG.Open.pRank 3 B = 4 →
      autOrderIn B K = 3 ^ 2 → P X K →
        I271CaseA 3 K B ∨ IsStronglyBalancedIn 3 B K ∨ I271CaseC K B

theorem nnFor_of_exc (P : ∀ (X : Type) [Group X], Subgroup X → Prop) (hF : NNFacts P)
    (hE : NNExc P) : NNFor P := by
  intro X _ _ hXK K B hH hNN hP
  obtain ⟨hidx, hAut⟩ := hF X hXK K B hH hNN hP
  rcases nn_caseA_or_exceptional hH hNN hidx hAut with h | ⟨h4, h9⟩
  · exact Or.inl h
  · exact hE X hXK K B hH hNN hidx h4 h9 hP

end NNFamilies

theorem nnHatSeven_holds :
    ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ K B : Subgroup X,
      I271Hyp 3 K B → ¬ B ≤ Subgroup.normalizer (K : Set X) → IsHatSeven ↥K →
        I271CaseA 3 K B ∨ IsStronglyBalancedIn 3 B K ∨ I271CaseC K B :=
  fun _ _ _ _ _ _ hH _ h7 => Or.inl (nn_hatSeven_caseA hH h7)

theorem i271NNOther_of_types (h1 : NNL2OddPow) (h3 : NNHatMTwentyTwo)
    (h4 : NNSLThreeExc) (h5 : NNSUThreeExc) : I271NNOther := by
  have h2 := nnHatSeven_holds
  intro X _ _ hXK K B hH hN hT
  rcases hT with h | h | h | h | h
  · exact h1 X hXK K B hH hN h
  · exact h2 X hXK K B hH hN h
  · exact h3 X hXK K B hH hN h
  · exact h4 X hXK K B hH hN h
  · exact h5 X hXK K B hH hN h

end CFSG.HardMathSupport.Solomon.Coordinator
