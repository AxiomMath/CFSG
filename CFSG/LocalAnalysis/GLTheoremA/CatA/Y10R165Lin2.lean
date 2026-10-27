module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open

namespace LinEngine

theorem eq_one_of_pow_eq_one_of_not_dvd {F : Type*} [Field F] [Fintype F] {p : ℕ}
    (hp : p.Prime) (hpd : ¬ p ∣ Fintype.card F - 1) {x : F} (hx : x ^ p = 1) : x = 1 := by
  classical
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hx
    exact zero_ne_one hx
  let u : Fˣ := Units.mk0 x hx0
  have hu : u ^ p = 1 := by
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, Units.val_one, Units.val_mk0]
    exact hx
  have hdvd : orderOf u ∣ p := orderOf_dvd_of_pow_eq_one hu
  have hcard : orderOf u ∣ Fintype.card Fˣ := by
    have h := Subgroup.card_subgroup_dvd_card (Subgroup.zpowers u)
    rw [Nat.card_zpowers] at h
    rwa [Nat.card_eq_fintype_card] at h
  rcases (Nat.dvd_prime hp).1 hdvd with h1 | hp'
  · have h2 : u = 1 := orderOf_eq_one_iff.1 h1
    exact Units.ext_iff.1 h2
  · exfalso
    rw [hp', Fintype.card_units] at hcard
    exact hpd hcard

section Diagonal

variable {F : Type*} [Field F]

private noncomputable def diagEntry {n q : ℕ} (e : Fin n → rootsOfUnity q F)
    (i : Fin (n + 1)) : Fˣ :=
  if h : (i : ℕ) < n then (e ⟨(i : ℕ), h⟩ : Fˣ) else (∏ j, (e j : Fˣ))⁻¹

private theorem prod_diagEntry {n q : ℕ} (e : Fin n → rootsOfUnity q F) :
    (∏ i, diagEntry e i) = 1 := by
  rw [Fin.prod_univ_castSucc]
  have hlast : diagEntry e (Fin.last n) = (∏ j, (e j : Fˣ))⁻¹ := by
    simp [diagEntry]
  have hcast : ∀ k : Fin n, diagEntry e (Fin.castSucc k) = (e k : Fˣ) := by
    intro k
    simp [diagEntry]
  rw [hlast, Finset.prod_congr rfl (fun k _ => hcast k), mul_inv_cancel]

private theorem diagEntry_mul {n q : ℕ} (e e' : Fin n → rootsOfUnity q F) :
    diagEntry (e * e') = diagEntry e * diagEntry e' := by
  funext i
  by_cases h : (i : ℕ) < n
  · simp [diagEntry, h]
  · rw [Pi.mul_apply]
    simp only [diagEntry, dif_neg h]
    have hprod : (∏ j, ((e * e') j : Fˣ)) = (∏ j, (e j : Fˣ)) * (∏ j, (e' j : Fˣ)) := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun j _ => rfl
    rw [hprod, mul_inv_rev, mul_comm]

private theorem diagEntry_one {n q : ℕ} :
    diagEntry (F := F) (1 : Fin n → rootsOfUnity q F) = 1 := by
  funext i
  by_cases h : (i : ℕ) < n
  · simp [diagEntry, h]
  · simp only [diagEntry, dif_neg h, Pi.one_apply]
    simp

noncomputable def diagSLMat {n q : ℕ} (e : Fin n → rootsOfUnity q F) :
    Matrix.SpecialLinearGroup (Fin (n + 1)) F :=
  ⟨Matrix.diagonal fun i => (diagEntry e i : F), by
    rw [Matrix.det_diagonal]
    have h := map_prod (Units.coeHom F) (diagEntry e) (Finset.univ : Finset (Fin (n + 1)))
    rw [prod_diagEntry, map_one] at h
    exact h.symm⟩

private theorem coe_diagSLMat {n q : ℕ} (e : Fin n → rootsOfUnity q F) :
    ((diagSLMat e : Matrix.SpecialLinearGroup (Fin (n + 1)) F) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) F) = Matrix.diagonal fun i => (diagEntry e i : F) :=
  rfl

theorem diagSLMat_mul {n q : ℕ} (e e' : Fin n → rootsOfUnity q F) :
    diagSLMat (e * e') = diagSLMat e * diagSLMat e' := by
  apply Subtype.ext
  show Matrix.diagonal (fun i => (diagEntry (e * e') i : F)) =
    Matrix.diagonal (fun i => (diagEntry e i : F)) *
      Matrix.diagonal (fun i => (diagEntry e' i : F))
  rw [Matrix.diagonal_mul_diagonal, diagEntry_mul]
  rfl

theorem diagSLMat_one {n q : ℕ} : diagSLMat (F := F) (n := n) (q := q) 1 = 1 := by
  apply Subtype.ext
  show Matrix.diagonal (fun i => (diagEntry (1 : Fin n → rootsOfUnity q F) i : F)) = 1
  rw [diagEntry_one]
  simp

theorem diagSLMat_inv {n q : ℕ} (e : Fin n → rootsOfUnity q F) :
    diagSLMat (F := F) e⁻¹ = (diagSLMat e)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← diagSLMat_mul, inv_mul_cancel, diagSLMat_one]

theorem diagSLMat_pow {n q : ℕ} (e : Fin n → rootsOfUnity q F) (k : ℕ) :
    diagSLMat (F := F) (e ^ k) = diagSLMat e ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, diagSLMat_one]
  | succ k ih => rw [pow_succ, pow_succ, diagSLMat_mul, ih]

theorem diagSLMat_injective {n q : ℕ} :
    Function.Injective (diagSLMat (F := F) (n := n) (q := q)) := by
  intro e e' h
  have h1 := congrArg (fun g : Matrix.SpecialLinearGroup (Fin (n + 1)) F =>
    (g : Matrix (Fin (n + 1)) (Fin (n + 1)) F)) h
  rw [coe_diagSLMat, coe_diagSLMat] at h1
  funext j
  have h2 : Matrix.diagonal (fun i => (diagEntry e i : F)) (Fin.castSucc j) (Fin.castSucc j) =
      Matrix.diagonal (fun i => (diagEntry e' i : F)) (Fin.castSucc j) (Fin.castSucc j) :=
    congrFun (congrFun h1 (Fin.castSucc j)) (Fin.castSucc j)
  rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq] at h2
  have h3 : diagEntry e (Fin.castSucc j) = diagEntry e' (Fin.castSucc j) := Units.ext h2
  simp only [diagEntry, Fin.val_castSucc, dif_pos j.isLt] at h3
  exact Subtype.ext (by simpa using h3)

noncomputable def diagSLSub (n q : ℕ) : Subgroup (Matrix.SpecialLinearGroup (Fin (n + 1)) F) where
  carrier := Set.range (diagSLMat (F := F) (n := n) (q := q))
  mul_mem' := by
    rintro _ _ ⟨e, rfl⟩ ⟨e', rfl⟩
    exact ⟨e * e', diagSLMat_mul e e'⟩
  one_mem' := ⟨1, diagSLMat_one⟩
  inv_mem' := by
    rintro _ ⟨e, rfl⟩
    exact ⟨e⁻¹, diagSLMat_inv e⟩

theorem card_diagSLSub {n q : ℕ} [NeZero q] [Finite F] (hdvd : q ∣ Nat.card F - 1) :
    Nat.card (diagSLSub (F := F) n q) = q ^ n := by
  have h : Nat.card ↥(diagSLSub (F := F) n q) = Nat.card (Fin n → rootsOfUnity q F) :=
    Nat.card_congr (Equiv.ofInjective (diagSLMat (F := F) (n := n) (q := q))
      (diagSLMat_injective (F := F))).symm
  rw [h, Nat.card_pi]
  simp only [CFSG.LinearGroups.card_rootsOfUnity_of_dvd (K := F) (d := q) hdvd]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem isElemAbelian_diagSLSub {n q : ℕ} :
    IsElemAbelian q (diagSLSub (F := F) n q) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · apply Subtype.ext
    obtain ⟨e, he⟩ := a.2
    obtain ⟨e', he'⟩ := b.2
    show ((a : ↥(diagSLSub (F := F) n q)) : Matrix.SpecialLinearGroup (Fin (n + 1)) F) *
        ((b : ↥(diagSLSub (F := F) n q)) : Matrix.SpecialLinearGroup (Fin (n + 1)) F) =
      ((b : ↥(diagSLSub (F := F) n q)) : Matrix.SpecialLinearGroup (Fin (n + 1)) F) *
        ((a : ↥(diagSLSub (F := F) n q)) : Matrix.SpecialLinearGroup (Fin (n + 1)) F)
    rw [← he, ← he', ← diagSLMat_mul, ← diagSLMat_mul, mul_comm e e']
  · obtain ⟨e, he⟩ := hx
    rw [← he]
    rw [← diagSLMat_pow]
    rw [show e ^ q = 1 from by
      funext i
      exact Subtype.ext ((mem_rootsOfUnity q ((e i : rootsOfUnity q F) : Fˣ)).1 (e i).2)]
    exact diagSLMat_one

theorem le_pRank_diagSLSub {n q : ℕ} [Finite F] (hq : q.Prime) (hdvd : q ∣ Nat.card F - 1) :
    n ≤ CFSG.Open.pRank q (diagSLSub (F := F) n q) := by
  haveI : NeZero q := ⟨hq.ne_zero⟩
  exact CFSG.SectionRank.le_pRank hq.one_lt le_rfl isElemAbelian_diagSLSub
    (card_diagSLSub (F := F) hdvd)

theorem three_le_pRank_diagSLSub {n q : ℕ} [Finite F] (hq : q.Prime)
    (hdvd : q ∣ Nat.card F - 1) (hn : 3 ≤ n) :
    3 ≤ CFSG.Open.pRank q (diagSLSub (F := F) n q) :=
  le_trans hn (le_pRank_diagSLSub (F := F) hq hdvd)

end Diagonal

end LinEngine

end CFSG.LocalAnalysis.GLTheoremA.Y10F
