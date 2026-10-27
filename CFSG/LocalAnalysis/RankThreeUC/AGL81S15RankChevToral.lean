module

public import CFSG.Open.StatedDefs
public import CFSG.Open.Defs
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankChevDiag
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.LocalAnalysis.SectionRank.SubgroupRank
import CFSG.Open.StatedAPI

public section

open scoped Matrix

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace RankChevToralProof

open Matrix CFSG.Open CFSG.SectionRank CFSG.Open.StatedAPI

@[expose] noncomputable def torusHom (m : ℕ) (F : Type) [Field F] : (Fin m → Fˣ) →* GL (Fin m) F :=
  (Units.map (Matrix.diagonalRingHom (Fin m) F : (Fin m → F) →* Matrix (Fin m) (Fin m) F)).comp
    (MulEquiv.piUnits.symm : (Fin m → Fˣ) ≃* (Fin m → F)ˣ).toMonoidHom

theorem torusHom_coe {F : Type} [Field F] (m : ℕ) (x : Fin m → Fˣ) :
    ((torusHom m F x : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) =
      Matrix.diagonal (fun i => ((x i : Fˣ) : F)) := rfl

theorem torusHom_injective {F : Type} [Field F] (m : ℕ) :
    Function.Injective (torusHom m F) := by
  intro x y hxy
  funext i
  have h := congrArg (fun A : GL (Fin m) F => (A : Matrix (Fin m) (Fin m) F) i i) hxy
  simp only [torusHom_coe, diagonal_apply_eq] at h
  exact Units.ext h

@[expose] noncomputable def sncHom (k : ℕ) (F : Type) [Field F] : (Fin k → Fˣ) →* (Fin (k + 1) → Fˣ) where
  toFun x := Fin.snoc x (∏ i, x i)⁻¹
  map_one' := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  map_mul' x y := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.snoc_last, Pi.mul_apply, Finset.prod_mul_distrib, mul_inv]
    · simp

theorem prod_sncHom {F : Type} [Field F] (k : ℕ) (x : Fin k → Fˣ) :
    ∏ i, (sncHom k F x) i = 1 := by
  rw [Fin.prod_univ_castSucc]
  simp [sncHom]

@[expose] noncomputable def torusEmb (k : ℕ) (F : Type) [Field F] (Z : Subgroup Fˣ) :
    (Fin k → Z) →* GL (Fin (k + 1)) F :=
  (torusHom (k + 1) F).comp ((sncHom k F).comp (MonoidHom.compLeft Z.subtype (Fin k)))

theorem sncHom_injective {F : Type} [Field F] (k : ℕ) : Function.Injective (sncHom k F) := by
  intro x y hxy
  funext j
  have h := congrFun hxy (Fin.castSucc j)
  simpa [sncHom] using h

theorem torusEmb_injective {F : Type} [Field F] (k : ℕ) (Z : Subgroup Fˣ) :
    Function.Injective (torusEmb k F Z) := by
  refine (torusHom_injective (F := F) (k + 1)).comp ((sncHom_injective (F := F) k).comp ?_)
  intro x y hxy
  funext j
  exact Subtype.ext (congrFun hxy j)

theorem det_torusEmb {F : Type} [Field F] (k : ℕ) (Z : Subgroup Fˣ) (x : Fin k → Z) :
    ((torusEmb k F Z x : GL (Fin (k + 1)) F) : Matrix (Fin (k + 1)) (Fin (k + 1)) F).det = 1 := by
  have h := prod_sncHom (F := F) k (fun j => (x j : Fˣ))
  change ((torusHom (k + 1) F (sncHom k F (fun j => (x j : Fˣ))) : GL (Fin (k + 1)) F) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) F).det = 1
  rw [torusHom_coe, det_diagonal, ← Units.coe_prod, h, Units.val_one]

theorem exists_subgroup_order {F : Type} [Field F] [Finite F] {r : ℕ} [Fact r.Prime]
    (hdvd : r ∣ Nat.card F - 1) :
    ∃ Z : Subgroup Fˣ, Nat.card Z = r ∧ ∀ z : Z, z ^ r = 1 := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  have hcardU : Nat.card Fˣ = Nat.card F - 1 := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_units]
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) r (hcardU ▸ hdvd)
  refine ⟨Subgroup.zpowers ζ, by rw [Nat.card_zpowers, hζ], fun z => ?_⟩
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 z.2
  apply Subtype.ext
  change (z : Fˣ) ^ r = 1
  rw [← hn, ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, ← hζ,
    pow_orderOf_eq_one, _root_.one_zpow]

theorem sncHom_pow_eq_one {F : Type} [Field F] (k n : ℕ) (x : Fin k → Fˣ)
    (hx : ∀ j, x j ^ n = 1) (i : Fin (k + 1)) : (sncHom k F x i) ^ n = 1 := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [sncHom, MonoidHom.coe_mk, OneHom.coe_mk, Fin.snoc_last]
    rw [inv_pow, ← Finset.prod_pow]
    simp [hx]
  · simpa [sncHom] using hx j

end RankChevToralProof

open RankChevToralProof CFSG.Open CFSG.Open.StatedAPI in
theorem pRank_statedSL_ge {F : Type} [Field F] [Finite F] {r m : ℕ} [hr : Fact r.Prime]
    (hm : 1 ≤ m) (hdvd : r ∣ Nat.card F - 1) :
    m - 1 ≤ CFSG.Open.pRank r (StatedSL m F) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  obtain ⟨Z, hZc, hZr⟩ := exists_subgroup_order (F := F) (r := r) hdvd
  have hA : Nat.card (Fin k → Z) = r ^ k := by
    rw [Nat.card_pi, Finset.prod_const, hZc, Finset.card_univ, Fintype.card_fin]
  rw [Nat.add_sub_cancel]
  refine CFSG.SectionRank.le_pRank_of_injective hr.out.one_lt (fun a b => mul_comm a b)
    (fun a => funext fun j => by rw [Pi.pow_apply, hZr, Pi.one_apply]) hA (torusEmb k F Z)
    (torusEmb_injective k Z) ?_
  rintro _ ⟨x, rfl⟩
  exact mem_statedSL_of_det (det_torusEmb k Z x)

open CFSG.Open CFSG.Open.StatedAPI in
theorem pRank_statedSL_le {F : Type} [Field F] [Finite F] {r m : ℕ} [hr : Fact r.Prime]
    (hm : 1 ≤ m) (hrF : (r : F) ≠ 0) :
    CFSG.Open.pRank r (StatedSL m F) ≤ m - 1 := by
  refine CFSG.SectionRank.pRank_le hr.out.one_lt (fun E hEH hE => ?_)
  refine RankChevDiagProof.card_le_pow_pred_of_elementary hm hrF E (fun a ha b hb => ?_)
    (fun a ha => hE.2 a ha) (fun a ha => det_of_mem_statedSL (hEH ha))
  have := hE.1
  exact congrArg Subtype.val (this.is_comm.comm (⟨a, ha⟩ : E) ⟨b, hb⟩)

open CFSG.Open in
theorem pRank_top_statedSL_eq_pred {F : Type} [Field F] [Finite F] {r m : ℕ} [hr : Fact r.Prime]
    (hm : 1 ≤ m) (hrF : (r : F) ≠ 0) (hdvd : r ∣ Nat.card F - 1) :
    CFSG.Open.pRank r (⊤ : Subgroup ↥(StatedSL m F)) = m - 1 := by
  rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (StatedSL m F)]
  exact le_antisymm (pRank_statedSL_le hm hrF) (pRank_statedSL_ge hm hdvd)

open RankChevToralProof CFSG.Open CFSG.Open.StatedAPI in
theorem pRank_statedSU_ge {F : Type} [Field F] [Finite F] {q r m : ℕ} [hr : Fact r.Prime]
    (hm : 1 ≤ m) (hF : Nat.card F = q ^ 2) (hdvd : r ∣ q + 1) :
    m - 1 ≤ CFSG.Open.pRank r (StatedSU m q F) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hq1 : 1 ≤ q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · subst h
      have := Nat.card_pos (α := F)
      simp [hF] at this
    · exact h
  have hdvd' : r ∣ Nat.card F - 1 := by
    rw [hF]
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    have h1 : (q' + 1) ^ 2 - 1 = q' * (q' + 1 + 1) := by
      have : (q' + 1) ^ 2 = q' * (q' + 1 + 1) + 1 := by ring
      omega
    rw [h1]
    exact Dvd.dvd.mul_left hdvd q'
  obtain ⟨Z, hZc, hZr⟩ := exists_subgroup_order (F := F) (r := r) hdvd'
  have hA : Nat.card (Fin k → Z) = r ^ k := by
    rw [Nat.card_pi, Finset.prod_const, hZc, Finset.card_univ, Fintype.card_fin]
  rw [Nat.add_sub_cancel]
  refine CFSG.SectionRank.le_pRank_of_injective hr.out.one_lt (fun a b => mul_comm a b)
    (fun a => funext fun j => by rw [Pi.pow_apply, hZr, Pi.one_apply]) hA (torusEmb k F Z)
    (torusEmb_injective k Z) ?_
  rintro _ ⟨x, rfl⟩
  apply Subgroup.subset_closure
  refine ⟨det_torusEmb k Z x, ?_⟩
  obtain ⟨c, hc⟩ := hdvd
  have hxj : ∀ j, ((x j : Z) : Fˣ) ^ (q + 1) = 1 := fun j => by
    rw [hc, pow_mul]
    have := congrArg (fun z : Z => (z : Fˣ)) (hZr (x j))
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at this
    rw [this, one_pow]
  have hs := sncHom_pow_eq_one (F := F) k (q + 1) (fun j => ((x j : Z) : Fˣ)) hxj
  have hd : ∀ i, (((sncHom k F (fun j => ((x j : Z) : Fˣ))) i : Fˣ) : F) ^ q *
      (((sncHom k F (fun j => ((x j : Z) : Fˣ))) i : Fˣ) : F) = 1 := fun i => by
    rw [← pow_succ]
    have := congrArg (fun u : Fˣ => (u : F)) (hs i)
    simpa using this
  change (((torusHom (k + 1) F (sncHom k F (fun j => ((x j : Z) : Fˣ))) : GL (Fin (k + 1)) F) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) F).map (· ^ q))ᵀ *
      ((torusHom (k + 1) F (sncHom k F (fun j => ((x j : Z) : Fˣ))) : GL (Fin (k + 1)) F) :
        Matrix (Fin (k + 1)) (Fin (k + 1)) F) = 1
  rw [torusHom_coe, Matrix.diagonal_map (by simp [zero_pow (by omega : q ≠ 0)]),
    Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  exact hd i

open CFSG.Open CFSG.Open.StatedAPI in
theorem pRank_statedSU_le {F : Type} [Field F] [Finite F] {q r m : ℕ} [hr : Fact r.Prime]
    (hm : 1 ≤ m) (hrF : (r : F) ≠ 0) :
    CFSG.Open.pRank r (StatedSU m q F) ≤ m - 1 :=
  (CFSG.SectionRank.pRank_mono hr.out.one_lt (statedSU_le_statedSL m q F)).trans
    (pRank_statedSL_le hm hrF)

open CFSG.Open in
theorem pRank_top_statedSU_eq_pred {F : Type} [Field F] [Finite F] {q r m : ℕ} [hr : Fact r.Prime]
    (hm : 1 ≤ m) (hrF : (r : F) ≠ 0) (hF : Nat.card F = q ^ 2) (hdvd : r ∣ q + 1) :
    CFSG.Open.pRank r (⊤ : Subgroup ↥(StatedSU m q F)) = m - 1 := by
  rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (StatedSU m q F)]
  exact le_antisymm (pRank_statedSU_le hm hrF) (pRank_statedSU_ge hm hF hdvd)

end CFSG.LocalAnalysis.RankThreeUC.S15

