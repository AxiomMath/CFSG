module

public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.AutoRows
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.Descent
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.Burnside2
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.Rank

public section

namespace CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree

open CFSG.Open CFSG.RankThree.PartOne.Census3 TauCeti Subgroup

theorem gammaCore_le_inf {X : Type} [Group X] [Finite X] {M P : Subgroup X}
    (hM : GLBStronglyEmbedded 3 M) (hPM : P ≤ M) (A Q : Subgroup X) (hQP : Q ≤ P) :
    gammaCore 3 1 A Q ≤ M ⊓ A := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro x ⟨hxA, R, hRQ, hR, hxR⟩
  exact ⟨normalizer_le_of_stronglyEmbedded hM ((hRQ.trans hQP).trans hPM)
    (three_dvd_card_of_one_le_pRank hR) hxR, hxA⟩

theorem even_relIndex_of_cyclic {X : Type} [Group X] [Finite X] {K Γ Q J : Subgroup X}
    (hKs : IsSimpleGroup ↥K) (hKnc : ∃ a b : ↥K, a * b ≠ b * a) (hΓK : Γ ≤ K)
    (hΓ : Γ = Q ⊔ J) (hN : Γ ≤ Subgroup.normalizer (Q : Set X)) (hQ3 : IsPGroup 3 Q)
    (hJ : IsCyclic ↥J) : 2 ∣ Γ.relIndex K := by
  obtain ⟨T, hTΓ, hT2, hTi, hTc⟩ := exists_cyclic_sylow_two_of_normal_sup hΓ hN hQ3 hJ
  exact two_dvd_relIndex_of_cyclic_two_subgroup hKs hKnc hΓK hTΓ hT2 hTi hTc

theorem gt_nine_of_valid_A1 {q : PrimePower} (hq : q.p = 3) (hv : (LieTypeIndex.A 1 q).Valid) :
    9 < q.card := by
  rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff] at hv
  obtain ⟨⟨-, h4⟩, hdup⟩ := hv
  have h4 := h4 rfl
  have hne : q.card ≠ 9 := fun h => hdup ((LieTypeIndex.isDuplicateRepresentative_iff _).mpr
    (Or.inl ⟨rfl, Or.inr (Or.inr h)⟩))
  have hc : q.card = 3 ^ q.exponent := by rw [PrimePower.card_def, hq]
  have hpos := q.exponent_pos
  rcases Nat.lt_or_ge q.exponent 3 with h | h
  · interval_cases hexp : q.exponent
    · rw [hc] at h4; omega
    · rw [hc] at hne; omega
  · rw [hc]
    calc 9 < 27 := by norm_num
      _ = 3 ^ 3 := by norm_num
      _ ≤ 3 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) h

theorem one_le_of_valid_reeG2 {m : ℕ} (hv : (LieTypeIndex.reeG2 m).Valid) : 1 ≤ m := by
  rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff] at hv
  exact hv.1

theorem autoGoal_of_plus {X : Type} [Group X] [Finite X] {K M : Subgroup X} [hKn : K.Normal]
    (hKs : IsSimpleGroup ↥K) (hKnc : ∃ a b : ↥K, a * b ≠ b * a)
    (hM : GLBStronglyEmbedded 3 M) (P : Sylow 3 X) (hPM : (P : Subgroup X) ≤ M)
    (hK3 : 3 ∣ Nat.card K)
    (hrk : ∀ E : Subgroup X, E ≤ (P : Subgroup X) → IsElemAbelian 3 E → Nat.card E ≤ 9)
    (hconc : Gls3ConclusionPlus X K (P : Subgroup X)) :
    ((∀ a ∈ (P : Subgroup X), ∀ b ∈ (P : Subgroup X), a * b = b * a) →
        IsElemAbelian 3 (P : Subgroup X) ∧ Nat.card (P : Subgroup X) = 9 ∧ ActsIrr (Subgroup.normalizer ((P : Subgroup X) : Set X)) (P : Subgroup X)) ∧
    (¬ 2 ∣ M.index → IsElemAbelian 3 (P : Subgroup X) ∧ Nat.card (P : Subgroup X) = 9 ∧
        ∀ x ∈ (P : Subgroup X), ∀ y ∈ (P : Subgroup X), x ≠ 1 → y ≠ 1 →
          ∃ n ∈ Subgroup.normalizer ((P : Subgroup X) : Set X), n * x * n⁻¹ = y) := by
  have hP3 : IsPGroup 3 (P : Subgroup X) := P.isPGroup'
  have hsup : K ⊔ M = ⊤ := sup_eq_top_of_stronglyEmbedded hM P hPM hK3
  have hΓle := gammaCore_le_inf hM hPM K ((P : Subgroup X) ⊓ K) inf_le_left
  obtain ⟨hΓlt, hΓmax, hrows⟩ := hconc
  have hΓK : gammaCore 3 1 K ((P : Subgroup X) ⊓ K) ≤ K := hΓlt.le
  have hKM : M ⊓ K = gammaCore 3 1 K ((P : Subgroup X) ⊓ K) := by
    by_contra hne
    have hlt : gammaCore 3 1 K ((P : Subgroup X) ⊓ K) < M ⊓ K :=
      lt_of_le_of_ne hΓle (Ne.symm hne)
    have hMK : M ⊓ K = K := hΓmax (M ⊓ K) hlt inf_le_right
    have hKleM : K ≤ M := hMK ▸ inf_le_left
    apply hM.1
    rw [← hsup]
    exact (sup_eq_right.mpr hKleM).symm
  have hidx : M.index = (gammaCore 3 1 K ((P : Subgroup X) ⊓ K)).relIndex K := by
    rw [index_eq_relIndex_of_sup hsup, ← hKM, inf_relIndex_right]
  have heven : 2 ∣ (gammaCore 3 1 K ((P : Subgroup X) ⊓ K)).relIndex K → 2 ∣ M.index :=
    fun h => hidx ▸ h
  have hQ3 : IsPGroup 3 ((P : Subgroup X) ⊓ K : Subgroup X) := hP3.to_inf_left
  have hNQ : ∀ (hN : gammaCore 3 1 K ((P : Subgroup X) ⊓ K) =
        K ⊓ Subgroup.normalizer (((P : Subgroup X) ⊓ K : Subgroup X) : Set X)),
      gammaCore 3 1 K ((P : Subgroup X) ⊓ K) ≤
        Subgroup.normalizer (((P : Subgroup X) ⊓ K : Subgroup X) : Set X) :=
    fun hN => hN.le.trans inf_le_right
  have hPK : (3 ∣ K.index → False) → (P : Subgroup X) ⊓ K = P := fun h =>
    inf_eq_left.mpr (le_of_not_dvd_index hP3 h)
  rcases hrows with
    ⟨q, hq3, ⟨hv, -⟩, -, -, -, hE, hcard⟩ |
    ⟨q, hq3, ⟨hv, -⟩, hi3, hN, ⟨J, hJc, hJΓ⟩, hnab, -, E, hEQ, hEe, hEc⟩ |
    ⟨m, ⟨hv, -⟩, -, -, -, E, hEQ, hEe, hEc⟩ |
    ⟨-, hi3, -, -, hN, hD, -, hPnab⟩ |
    ⟨⟨φ, A, hA, hmem⟩, hi3, hE, h9, hN, J, hJc, hJΓ, hirr⟩ |
    ⟨-, ⟨k, hk⟩, hKc, hE, h9, hN, S, hS, hQS, hsupS, hQ8, hirr⟩ |
    ⟨-, hKtop, hE, h9, hN, S, hS, hsupS, h16, ⟨a, ha, b, hb, ho8, ho2, hbab, hSgen⟩, hC, hirr⟩
  ·
    exfalso
    have h1 := hrk _ inf_le_left hE
    rw [hcard] at h1
    have := gt_nine_of_valid_A1 hq3 hv
    omega
  ·
    have hQP := hPK (fun h => hi3 h)
    refine ⟨fun hcomm => absurd ?_ hnab, fun hodd => absurd (heven ?_) hodd⟩
    · rw [hQP]; exact hcomm
    · exact even_relIndex_of_cyclic hKs hKnc hΓK hJΓ (hNQ hN) hQ3 hJc
  ·
    exfalso
    have h1 := hrk E (hEQ.trans inf_le_left) hEe
    rw [hEc] at h1
    have hm := one_le_of_valid_reeG2 hv
    have : 3 ^ 3 ≤ 3 ^ (2 * m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  ·
    refine ⟨fun hcomm => absurd hcomm hPnab, fun hodd => absurd (heven ?_) hodd⟩
    have hcard18 : Nat.card ↥(gammaCore 3 1 K ((P : Subgroup X) ⊓ K)) = 18 := by
      obtain ⟨e⟩ := hD
      rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    obtain ⟨T, hTΓ, hT2, hTi, hTc⟩ := exists_cyclic_sylow_two_of_card_eq hcard18
    exact two_dvd_relIndex_of_cyclic_two_subgroup hKs hKnc hΓK hTΓ hT2 hTi hTc
  ·
    have hQP := hPK (fun h => hi3 h)
    have hJN : J ≤ Subgroup.normalizer ((P : Subgroup X) : Set X) := by
      have h1 : J ≤ gammaCore 3 1 K ((P : Subgroup X) ⊓ K) := hJΓ ▸ le_sup_right
      have h2 := h1.trans (hNQ hN)
      rwa [hQP] at h2
    refine ⟨fun _ => ⟨?_, ?_, ?_⟩, fun hodd => absurd (heven ?_) hodd⟩
    · rwa [hQP] at hE
    · rwa [hQP] at h9
    · rw [hQP] at hirr; exact hirr.mono hJN
    · exact even_relIndex_of_cyclic hKs hKnc hΓK hJΓ (hNQ hN) hQ3 hJc
  ·
    have hi3 : ¬ 3 ∣ K.index := by
      rw [hk]; intro h
      have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h)
      omega
    have hQP := hPK hi3
    have hSΓ : S ≤ Subgroup.normalizer (((P : Subgroup X) ⊓ K : Subgroup X) : Set X) :=
      hS.trans (hNQ hN)
    have hSN : S ≤ Subgroup.normalizer ((P : Subgroup X) : Set X) := by
      have := hSΓ; rwa [hQP] at this
    refine ⟨fun _ => ⟨?_, ?_, ?_⟩, fun hodd => absurd (heven ?_) hodd⟩
    · rwa [hQP] at hE
    · rwa [hQP] at h9
    · rw [hQP] at hirr; exact hirr.mono hSN
    · have hΓS : gammaCore 3 1 K ((P : Subgroup X) ⊓ K) = ((P : Subgroup X) ⊓ K) ⊔ S := hsupS.symm
      have hc72 := card_sup_of_normal_disjoint hΓS (hNQ hN) hQS
      have hS8 : Nat.card S = 8 := by
        obtain ⟨e⟩ := hQ8
        rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
      rw [h9, hS8] at hc72
      have h1 := Subgroup.relIndex_mul_card (gammaCore 3 1 K ((P : Subgroup X) ⊓ K)) K
      rw [inf_of_le_left hΓK, hc72, hKc] at h1
      omega
  ·
    have hPleK : (P : Subgroup X) ≤ K := hKtop ▸ le_top
    have hQP : (P : Subgroup X) ⊓ K = P := inf_eq_left.mpr hPleK
    have hSΓ : S ≤ Subgroup.normalizer (((P : Subgroup X) ⊓ K : Subgroup X) : Set X) :=
      hS.trans (hNQ hN)
    have hSN : S ≤ Subgroup.normalizer ((P : Subgroup X) : Set X) := by
      have := hSΓ; rwa [hQP] at this
    refine ⟨fun _ => ⟨?_, ?_, ?_⟩, fun _ => ⟨?_, ?_, ?_⟩⟩
    · rwa [hQP] at hE
    · rwa [hQP] at h9
    · rw [hQP] at hirr; exact hirr.mono hSN
    · rwa [hQP] at hE
    · rwa [hQP] at h9
    · intro x hx y hy hx1 hy1
      rw [hQP] at hC h9 hirr
      obtain ⟨s, hs, hsxy⟩ := transitive_of_quasidihedral h9 hSN hirr hC ha hb ho8 hbab hSgen x hx y hy hx1 hy1
      exact ⟨s, hSN hs, hsxy⟩

end CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree
