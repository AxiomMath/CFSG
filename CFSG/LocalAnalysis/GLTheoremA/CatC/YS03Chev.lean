module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS03Core
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.L3Char
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.Final
public import CFSG.LocalAnalysis.GLTheoremA.S4S.KData

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Solomon.Coordinator

section Amb

open CFSG.Yardstones.Md0ec50421ce4 CFSG.HardMathSupport.Dickson.I271
open CFSG.HardMathSupport.Solomon.Coordinator.YS08.L3Char (amb_lie_order card_alt)
open CFSG.HardMathSupport.Solomon.Coordinator.I1420 (lieOrderFormula)

theorem ys03_card_isLTwoTwentySeven {X : Type} [Group X]
    (h : CFSG.HardMathSupport.Solomon.Coordinator.IsLTwoTwentySeven X) : Nat.card X = 9828 := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv,
    CFSG.Open.StatedAPI.card_statedProj_statedSL_two_of_odd (by rw [hF]; decide), hF]
  norm_num


theorem ys03_not_amb_of_card {r : ℕ} {X : Type} [Group X] [Finite X] (hcard : Nat.card X = 9828)
    (h : catalogIs X (ambiguousChev r)) : False := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic _ _ => simp [ambiguousChev] at hi
  | sporadic _ => simp [ambiguousChev] at hi
  | alternating n hn5 =>
    simp only [ambiguousChev] at hi
    have hc : Nat.card X = n.factorial / 2 :=
      (Nat.card_congr e.toEquiv).trans (card_alt n (by omega))
    rcases hi with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> rw [hcard] at hc <;>
      norm_num [Nat.factorial] at hc
  | lie d =>
    obtain ⟨ld, hvld⟩ := d
    have hn : Nat.card X = lieOrderFormula ld :=
      CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds ⟨ld, hvld⟩ X ⟨e⟩
    have hval := amb_lie_order r ld hvld hi
    rw [hcard] at hn
    rcases hval with h | h | h | h <;> omega

theorem ys03_dvd_card_amb {p : ℕ} (hp2 : p ≠ 2) {X : Type} [Group X] [Finite X]
    (h : catalogIs X (ambiguousChev p)) : p ∣ Nat.card X := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic _ _ => simp [ambiguousChev] at hi
  | sporadic _ => simp [ambiguousChev] at hi
  | alternating n hn5 =>
    simp only [ambiguousChev] at hi
    have hc : Nat.card X = n.factorial / 2 :=
      (Nat.card_congr e.toEquiv).trans (card_alt n (by omega))
    rw [hc]
    rcases hi with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hp2
    · decide
    · exact absurd rfl hp2
    · decide
    · exact absurd rfl hp2
  | lie d =>
    obtain ⟨ld, hvld⟩ := d
    have hn : Nat.card X = lieOrderFormula ld :=
      CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds ⟨ld, hvld⟩ X ⟨e⟩
    rw [hn]
    cases ld with
    | A r q =>
      rcases r with _ | _ | r
      · simp [ambiguousChev] at hi
      · simp only [ambiguousChev] at hi
        rcases hi with ⟨-, rfl⟩ | ⟨h8, rfl⟩
        · exact absurd rfl hp2
        · simp only [lieOrderFormula]; rw [h8]; norm_num [orderA]
      · simp [ambiguousChev] at hi
    | twistedA r q =>
      rcases r with _ | _ | _ | _ | r
      · simp [ambiguousChev] at hi
      · simp [ambiguousChev] at hi
      · simp only [ambiguousChev] at hi
        exact absurd hi.2 hp2
      · simp only [ambiguousChev] at hi
        obtain ⟨h2, rfl⟩ := hi
        simp only [lieOrderFormula]; rw [h2]; decide
      · simp [ambiguousChev] at hi
    | _ => simp [ambiguousChev] at hi

section AmbBal


theorem ys03_strongBal_amb {S : Type} [Group S] [Finite S] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hS : IsSimpleGroup S) (hnc : ∃ a b : S, a * b ≠ b * a)
    (hamb : catalogIs S (ambiguousChev p)) : StrongBalAt p S := by
  intro X _ _ K B hcore hcomp ⟨eK⟩ hB hBN
  haveI := hS
  haveI : IsSimpleGroup ↥K := eK.isSimpleGroup
  have hncK : ∃ a b : ↥K, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnc
    exact ⟨eK.symm a, eK.symm b, fun h => hab (eK.symm.injective (by rw [map_mul, map_mul, h]))⟩
  have hZK : Subgroup.center ↥K = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥K) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hncK
      exact hab ((Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top a) b).symm)
  let eKZ : (↥K ⧸ Subgroup.center ↥K) ≃* S :=
    (QuotientGroup.quotientMulEquivOfEq hZK).trans (QuotientGroup.quotientBot.trans eK)
  have hambK : catalogIs (↥K ⧸ Subgroup.center ↥K) (ambiguousChev p) := by
    obtain ⟨i, hi, ⟨f⟩⟩ := hamb
    exact ⟨i, hi, ⟨eKZ.trans f⟩⟩
  have hH : Chev204Hyp p K B := ⟨hp, hp2, hcore, hcomp, hB, hBN, Or.inr hambK⟩
  have hne : ¬ ChevExc p K B := by
    rintro ⟨hp3, h | h⟩
    · exact ys03_not_amb_of_card (ys03_card_isLTwoTwentySeven h.1) hambK
    · have h3 := h.1.2.1
      rw [hZK, Subgroup.card_bot] at h3
      omega
  exact chevAmbCase_holds X p K B hH hambK hne

end AmbBal

end Amb

section L227

open CFSG.Yardstones.Md0ec50421ce4

theorem ys03_catalogIs_of_isL227 {S : Type} [Group S]
    (h : CFSG.HardMathSupport.Solomon.Coordinator.IsLTwoTwentySeven S) :
    catalogIs S (onLie (isL2 27)) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let q : TauCeti.PrimePower := ⟨3, 3, Nat.prime_three, by norm_num⟩
  have hq : q.card = 27 := by simp [q, TauCeti.PrimePower.card_def]
  have hv : (TauCeti.LieTypeIndex.A 1 q).Valid := by
    simp only [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff, hq]
    norm_num
  refine ⟨TauCeti.CFSGIndex.lie ⟨.A 1 q, hv⟩, hq, ⟨?_⟩⟩
  exact e.trans ((CFSG.ClassicalModels.statedLinearModelEquivGaloisPSL F 2 3 3 (by norm_num)
    (by rw [hF]; norm_num)).trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 q hv).symm)

end L227

section Main

open CFSG.Yardstones.Md0ec50421ce4 CFSG.HardMathSupport.Dickson.I271
open CFSG.HardMathSupport.Dickson.DefCharOuter.Export


theorem kd1912Chev_holds {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : KD1912Chev p := by
  intro S _ _ hS hnc hChev A hA
  by_cases hexc : p = 3 ∧ catalogIs S (onLie (isL2 27)) ∧ ¬ A ≤ innerAut S
  · exact Or.inr hexc
  refine Or.inl ?_
  intro D hD H hH hAH
  haveI : Fact p.Prime := ⟨hp⟩
  have hDne : D ≠ ⊥ := fun h => hp.ne_one (by
    have := hD.2.2
    rw [h, Subgroup.card_bot, pow_one] at this
    exact this.symm)
  obtain ⟨⟨x, hxD⟩, hx1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hDne
  have hx1 : x ≠ 1 := fun h => hx1' (Subtype.ext h)
  have hxA : x ∈ A := hD.1 hxD
  have hxp : x ^ p = 1 := hA.2 x hxA
  have hxord : orderOf x = p := orderOf_eq_prime hxp hx1
  have hcore : GLAPPrimeCoreOf p (H ⊓ Subgroup.centralizer ({x} : Set (MulAut S))) = ⊥ := by
    rcases hChev with hL | hAmb
    · obtain ⟨idx, ⟨e⟩, hch⟩ := lieType_of_catalogIs hL
      by_cases hxI : x ∈ innerAut S
      · exact defCharInnerCoreFree_holds S hS hnc idx ⟨e⟩ p hp hp2 hch x hxI hxord H hH
      · have hnotA : ¬ A ≤ innerAut S := fun h => hxI (h hxA)
        have hn27 : ¬ (p = 3 ∧ IsLTwoTwentySeven S) := fun h =>
          hexc ⟨h.1, ys03_catalogIs_of_isL227 h.2, hnotA⟩
        exact defCharOuterCoreFree_of_kdata kdOutCoreFree_holds kdOutCentInner_holds S hS hnc idx
          ⟨e⟩ p hp hp2 hch hn27 x hxord hxI H hH
    · exact ys03_coreFree_of_strongBal hS hnc hp (ys03_dvd_card_amb hp2 hAmb)
        (ys03_strongBal_amb hp hp2 hS hnc hAmb) hxp hH (hAH hxA)
  have hle : localDeltaIn p H D ≤
      GLAPPrimeCoreOf p (H ⊓ Subgroup.centralizer ({x} : Set (MulAut S))) := by
    unfold localDeltaIn
    exact iInf₂_le_of_le x hxD (iInf_le_of_le hx1 le_rfl)
  rw [hcore, le_bot_iff] at hle
  rw [hle, Subgroup.commutator_bot_left]
  simp

end Main


end CFSG.LocalAnalysis.GLTheoremA
