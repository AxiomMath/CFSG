module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesRankPMain
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesRankPLiftH
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesRankPD
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesRankPZhat
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesRankPBurn

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG CFSG.LocalCores Subgroup

namespace RankP

theorem case1_core (hI : GL83I66Two) {X : Type} [Group X] [Finite X] {p f : ℕ} (hf : f.Prime)
    (hf5 : 5 ≤ f) (hfp : f < p) (hK : CFSG.Open.IsKGroup X) (R L : Subgroup X) [R.Normal]
    [L.Normal]
    (hC : ∀ C : CFSG.LocalCores.ComponentIndex (X ⧸ R), IsSimpleGroup ↥C.1 ∧ f ∣ Nat.card C.1)
    (hcard : p ≤ Nat.card (CFSG.LocalCores.ComponentIndex (X ⧸ R)))
    (E : Subgroup X) (hEp : IsPGroup f E) (hEO : E ≤ L ⊓ R)
    (hEmax : ∀ Q : Subgroup X, Q ≤ L ⊓ R → IsPGroup f Q → E ≤ Q → Q = E)
    (hcover : CFSG.layer (X ⧸ R) ≤
      (L ⊓ centralizer (E : Set X)).map (QuotientGroup.mk' R))
    (y : X) (hy : orderOf y = f) (hEy : y ∈ normalizer (E : Set X)) :
    3 ≤ CFSG.Open.pRank f (centralizer ({y} : Set X)) := by
  haveI := Fact.mk hf
  have hf2 : f ≠ 2 := by omega
  have hf3 : 3 ≤ f := by omega
  have hyf : y ^ f = 1 := by
    have := pow_orderOf_eq_one y
    rwa [hy] at this
  obtain ⟨H, hH⟩ : ∃ H : Subgroup X, H = L ⊓ centralizer (E : Set X) := ⟨_, rfl⟩
  rw [← hH] at hcover
  have hHmem : ∀ x : X, x ∈ H ↔ x ∈ L ∧ ∀ e ∈ E, e * x = x * e := by
    intro x
    rw [hH, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    exact Iff.rfl
  have hHL : ∀ x ∈ H, x ∈ L := fun x hx => ((hHmem x).mp hx).1
  have hHC : ∀ x ∈ H, ∀ e ∈ E, e * x = x * e := fun x hx => ((hHmem x).mp hx).2
  have hZEp : IsPGroup f (E ⊓ centralizer (E : Set X) : Subgroup X) := hEp.to_inf_left
  have hZEN : (E ⊓ centralizer (E : Set X) : Subgroup X) ≤ H ⊓ R := by
    intro z hz
    have hzLR := hEO hz.1
    exact ⟨(hHmem z).mpr ⟨hzLR.1, fun e he => (Subgroup.mem_centralizer_iff.mp hz.2 e he)⟩,
      hzLR.2⟩
  have hZEc : ∀ z ∈ (E ⊓ centralizer (E : Set X) : Subgroup X), ∀ n ∈ H ⊓ R, n * z = z * n :=
    fun z hz n hn => (hHC n hn.1 z hz.1).symm
  have hmax : ∀ S : Subgroup X, S ≤ H ⊓ R → IsPGroup f S →
      S ≤ (E ⊓ centralizer (E : Set X) : Subgroup X) := by
    intro S hSN hSp
    have hSc : S ≤ centralizer (E : Set X) := fun s hs =>
      Subgroup.mem_centralizer_iff.mpr fun e he => (hHC s (hSN hs).1 e he)
    have hSnorm : S ≤ normalizer (E : Set X) :=
      hSc.trans (Subgroup.centralizer_le_normalizer (E : Set X))
    have hsup : IsPGroup f (S ⊔ E : Subgroup X) := hSp.to_sup_of_normal_right' hEp hSnorm
    have hSE : S ⊔ E ≤ L ⊓ R :=
      sup_le (fun s hs => ⟨hHL s (hSN hs).1, (hSN hs).2⟩) hEO
    have hEq : S ⊔ E = E := hEmax _ hSE hsup le_sup_right
    exact fun s hs => ⟨by rw [← hEq]; exact Subgroup.mem_sup_left hs, hSc hs⟩
  obtain ⟨T, hTN, hTf, hdec, hTnorm⟩ := exists_burnside_complement hZEp hZEN hZEc hmax
  have hTH : T ≤ H := fun t ht => (hTN ht).1
  have hTR : T ≤ R := fun t ht => (hTN ht).2
  have hTn : ∀ h ∈ H, ∀ t ∈ T, h * t * h⁻¹ ∈ T := fun h hh t ht =>
    hTnorm h (fun n hn => ⟨H.mul_mem (H.mul_mem hh hn.1) (H.inv_mem hh),
      (inferInstance : R.Normal).conj_mem n hn.2 h⟩) t ht
  have hyH : ∀ n ∈ normalizer (E : Set X), ∀ h ∈ H, n * h * n⁻¹ ∈ H := by
    intro n hn h hh
    refine (hHmem _).mpr ⟨(inferInstance : L.Normal).conj_mem h (hHL h hh) n, fun e he => ?_⟩
    have hen : n⁻¹ * e * n ∈ E := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hn) e).mp he
      simpa using this
    have hc := hHC h hh _ hen
    calc e * (n * h * n⁻¹) = n * ((n⁻¹ * e * n) * h) * n⁻¹ := by group
      _ = n * (h * (n⁻¹ * e * n)) * n⁻¹ := by rw [hc]
      _ = (n * h * n⁻¹) * e := by group
  have hyHn : y ∈ normalizer (H : Set X) := by
    refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx => hyH y hEy x hx, fun hx => ?_⟩
    have := hyH y⁻¹ (inv_mem hEy) _ hx
    simpa [mul_assoc] using this
  have hZ : ∀ C : CFSG.LocalCores.ComponentIndex (X ⧸ R), center C.1 = ⊥ := fun C =>
    center_eq_bot_of_simple C.2 (hC C).1
  have hvf : (QuotientGroup.mk' R y) ^ f = 1 := by rw [← map_pow, hyf, map_one]
  obtain ⟨Zh, -, hZab, hZexp, hZy, hZcard, hZcen⟩ :=
    exists_zhat_layer hZ (fun C => (hC C).2) (v := QuotientGroup.mk' R y) hvf
  have hlift : ∀ z ∈ Zh, ∃ h ∈ H, h ^ f = 1 ∧ QuotientGroup.mk' R h = z := by
    intro z hz
    obtain ⟨hzΛ, hzc⟩ := hZcen z hz
    exact exists_lift_in_H hI hf hf5 hK R H T (E ⊓ centralizer (E : Set X)) hTR hTH
      (fun z hz => (hZEN hz).1) hTn hTf hdec (fun z hz h hh => (hHC h hh z hz.1).symm)
      (fun C => (hC C).1) hZ hcover hzΛ (hZexp z hz) hzc
  obtain ⟨D, hDexp, hDcl, hDy, hDmap, hDZ⟩ :=
    exists_D hf2 R H (E ⊓ centralizer (E : Set X)) Zh (y := y)
      (fun z hz h hh => (hHC h hh z hz.1).symm) hmax hZab hZexp hyf hyHn hZy hlift
  have hdim : f ^ (f + 1) * Nat.card (_root_.commutator D) ≤ Nat.card D := by
    have h1 := card_mul_commutator_le (QuotientGroup.mk' R) D Zh hDmap
      (fun a ha b hb => hZab _ (hDZ a ha) _ (hDZ b hb))
    have h2 : f ^ (f + 1) ≤ Nat.card Zh :=
      (Nat.pow_le_pow_right hf.pos (by omega)).trans hZcard
    exact (Nat.mul_le_mul_right _ h2).trans h1
  exact step0 hf hf3 hDexp hDcl hdim hy hDy

end RankP

theorem rankPCase1_of_inputs (hI : RankP.GL83I66Two) : RankPCase1 := by
  intro X _ _ p f hp hf hf5 hfp hK hC hcard E hEp hEO hEmax hcover y hy hEy
  haveI := Fact.mk hp
  haveI hLc : (CFSG.pLayer X p).Characteristic :=
    CFSG.ComponentClassification.CatalogueBPrimeJoin.pLayer_characteristic (G := X) (p := p)
  haveI : (CFSG.pLayer X p).Normal := inferInstance
  exact RankP.case1_core hI hf hf5 hfp hK (CFSG.pPrimeCore p X) (CFSG.pLayer X p) hC hcard E hEp
    hEO hEmax hcover y hy hEy

theorem kFact613rankP_of_inputs (hI : RankP.GL83I66Two) : KFact613rankP :=
  kFact613rankP_of_case1 (rankPCase1_of_inputs hI)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
