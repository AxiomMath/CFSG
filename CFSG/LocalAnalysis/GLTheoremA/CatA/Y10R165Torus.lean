module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Vac
public import CFSG.LocalAnalysis.ComponentClassification.GoldschmidtTDGriess
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.LowerExcOne
import all CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.LowerExcOne

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC.S15 CFSG.Blueprint.Chevalley
open Matrix
open scoped MatrixGroups

section Engine

variable {G : Type*} [Group G] {F : Type*} [Field F]

theorem sl2_sq_eq_one_of_commute_sl2Upper_one (h2 : ringChar F = 2)
    {A : SL(2, F)} (hA : A * CFSG.RankThree.CentralCover.sl2Upper (1 : F) =
      CFSG.RankThree.CentralCover.sl2Upper (1 : F) * A) : A ^ 2 = 1 := by
  haveI : CharP F 2 := ringChar.of_eq h2
  have h2' : (2 : F) = 0 := CharP.cast_eq_zero F 2
  set B : Matrix (Fin 2) (Fin 2) F := (A : Matrix (Fin 2) (Fin 2) F) with hB
  have hdet : B.det = 1 := A.2
  have hmul : B * (CFSG.RankThree.CentralCover.sl2Upper (1 : F) : Matrix (Fin 2) (Fin 2) F) =
      (CFSG.RankThree.CentralCover.sl2Upper (1 : F) : Matrix (Fin 2) (Fin 2) F) * B := by
    have := congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F)) hA
    simpa only [Matrix.SpecialLinearGroup.coe_mul] using this
  rw [CFSG.RankThree.CentralCover.coe_sl2Upper] at hmul
  have h10 : B 1 0 = 0 := by
    have h00 := congrFun (congrFun hmul 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h00
    linear_combination h00
  have h01 : B 0 0 = B 1 1 := by
    have h := congrFun (congrFun hmul 0) 1
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.head_fin_const, Matrix.cons_val_two] at h
    simp only [mul_one, one_mul] at h
    exact add_right_cancel (by rwa [add_comm (B 0 1) (B 1 1)] at h)
  have hBform : B = !![B 0 0, B 0 1; 0, B 0 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h10, h01]
  have ha2 : B 0 0 ^ 2 = 1 := by
    have h := hdet
    rw [hBform, Matrix.det_fin_two_of] at h
    simpa [pow_two, h10] using h
  have ha1 : B 0 0 = 1 := by
    have h : (B 0 0 - 1) * (B 0 0 - 1) = 0 := by
      have hsq : (B 0 0 - 1) * (B 0 0 - 1) = B 0 0 ^ 2 - 2 * B 0 0 + 1 := by ring
      rw [hsq, ha2]
      linear_combination h2' - B 0 0 * h2'
    have h0 : B 0 0 - 1 = 0 := by
      rcases mul_eq_zero.1 h with h' | h' <;> exact h'
    exact sub_eq_zero.1 h0
  have hBsl2 : B = (CFSG.RankThree.CentralCover.sl2Upper (B 0 1) : Matrix (Fin 2) (Fin 2) F) := by
    rw [CFSG.RankThree.CentralCover.coe_sl2Upper]
    conv_lhs => rw [hBform]
    rw [ha1]
  have hAsl2 : A = CFSG.RankThree.CentralCover.sl2Upper (B 0 1) := Subtype.ext hBsl2
  rw [hAsl2, pow_two, ← CFSG.RankThree.CentralCover.sl2Upper_add,
    CharTwo.add_self_eq_zero, CFSG.RankThree.CentralCover.sl2Upper_zero]

theorem exists_orderOf_sl2_of_card_add_one [Finite F] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpd : p ∣ Nat.card F + 1) :
    ∃ h : SL(2, F), orderOf h = p := by
  have hfac : Nat.card F ^ 2 - 1 = (Nat.card F + 1) * (Nat.card F - 1) := by
    have := Nat.sq_sub_sq (Nat.card F) 1
    simpa using this
  have hdvd' : p ∣ Nat.card F * (Nat.card F ^ 2 - 1) := by
    rw [hfac]
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_right hpd _) _
  have : Fact p.Prime := ⟨hp⟩
  refine exists_prime_orderOf_dvd_card' (G := SL(2, F)) p ?_
  rw [CFSG.LieType.SeitzGeneration.natCard_sl2_field]
  exact hdvd'

private theorem closure_range_le_centralizer {k : ℕ} {ψ : Fin k → (SL(2, F) →* G)}
    {h : SL(2, F)} {x : G} (hx : ∀ i, ψ i h * x = x * ψ i h) :
    Subgroup.closure (Set.range fun i => ψ i h) ≤ Subgroup.centralizer ({x} : Set G) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨i, rfl⟩
  exact Subgroup.mem_centralizer_singleton_iff.2 (hx i)

theorem exists_elemAbelian_of_commuting_sl2 [Finite F] [Finite G] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (h2 : ringChar F = 2) (hpd : p ∣ Nat.card F + 1) (h : SL(2, F))
    (hh : orderOf h = p) :
    ∀ {k : ℕ} (φ : Fin k → (SL(2, F) →* G)), (∀ i, Function.Injective (φ i)) →
    (∀ i j, i ≠ j → ∀ A B : SL(2, F), φ i A * φ j B = φ j B * φ i A) →
    ∃ E : Subgroup G, E = Subgroup.closure (Set.range fun i => φ i h) ∧
      IsElemAbelian p E ∧ Nat.card E = p ^ k := by
  intro k
  induction k with
  | zero =>
    intro φ _ _
    refine ⟨⊥, ?_, isElemAbelian_bot p, ?_⟩
    · rw [show (Set.range fun i : Fin 0 => φ i h) = ∅ by simp]
      simp
    · simp
  | succ k ih =>
    intro φ hφ hcomm
    have hφ' : ∀ i, Function.Injective (φ (Fin.succ i)) := fun i => hφ _
    have hcomm' : ∀ i j, i ≠ j → ∀ A B : SL(2, F),
        φ (Fin.succ i) A * φ (Fin.succ j) B = φ (Fin.succ j) B * φ (Fin.succ i) A :=
      fun i j hij A B => hcomm _ _ (fun hh' => hij (Fin.succ_injective _ hh')) A B
    obtain ⟨E, hE, hEel, hEcard⟩ := ih (fun i => φ (Fin.succ i)) hφ' hcomm'
    set x : G := φ 0 h with hx
    have hxord : orderOf x = p := by
      rw [hx, orderOf_injective (φ 0) (hφ 0), hh]
    have hUcard : Nat.card (Subgroup.zpowers x) = p := by rw [Nat.card_zpowers, hxord]
    have hUel : IsElemAbelian p (Subgroup.zpowers x) :=
      isElemAbelian_zpowers (by rw [← hxord]; exact pow_orderOf_eq_one x)
    have hgen_comm : ∀ y ∈ E, y * x = x * y := by
      have hle : E ≤ Subgroup.centralizer ({x} : Set G) := by
        rw [hE]
        exact closure_range_le_centralizer fun i => hcomm (Fin.succ i) 0
          (Fin.succ_ne_zero i) h h
      intro y hy
      exact Subgroup.mem_centralizer_singleton_iff.1 (hle hy)
    have hxE : x ∉ E := by
      intro hxE
      have hle : E ≤ Subgroup.centralizer
          ({φ 0 (CFSG.RankThree.CentralCover.sl2Upper (1 : F))} : Set G) := by
        rw [hE]
        exact closure_range_le_centralizer fun i => hcomm (Fin.succ i) 0
          (Fin.succ_ne_zero i) h (CFSG.RankThree.CentralCover.sl2Upper (1 : F))
      have hxc := Subgroup.mem_centralizer_singleton_iff.1 (hle hxE)
      have hhcomm : h * CFSG.RankThree.CentralCover.sl2Upper (1 : F) =
          CFSG.RankThree.CentralCover.sl2Upper (1 : F) * h := by
        apply hφ 0
        rw [map_mul, map_mul]
        rw [hx] at hxc
        exact hxc
      have hsq := sl2_sq_eq_one_of_commute_sl2Upper_one h2 hhcomm
      have h2dvd : orderOf h ∣ 2 := (orderOf_dvd_iff_pow_eq_one (x := h) (n := 2)).2 hsq
      rw [hh] at h2dvd
      have hle2 : p ≤ 2 := Nat.le_of_dvd (by norm_num) h2dvd
      have hpge := hp.two_le
      omega
    have hcommEU : ∀ a ∈ E, ∀ b ∈ Subgroup.zpowers x, a * b = b * a := by
      intro a ha b hb
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
      exact (show Commute a x from hgen_comm a ha).zpow_right m
    have hsupel : IsElemAbelian p (E ⊔ Subgroup.zpowers x) :=
      hEel.sup_of_commute hUel hcommEU
    have hinf : E ⊓ Subgroup.zpowers x = ⊥ := by
      have hdvd : Nat.card ↥(E ⊓ Subgroup.zpowers x) ∣ Nat.card ↥(Subgroup.zpowers x) :=
        Subgroup.card_dvd_of_le inf_le_right
      rw [hUcard] at hdvd
      have hone : Nat.card ↥(E ⊓ Subgroup.zpowers x) = 1 := by
        rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | hp'
        · exact h1
        · exfalso
          have hEq : E ⊓ Subgroup.zpowers x = Subgroup.zpowers x :=
            Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hp', hUcard])
          have hxinf : x ∈ E ⊓ Subgroup.zpowers x := hEq.symm ▸ Subgroup.mem_zpowers x
          exact hxE hxinf.1
      exact Subgroup.card_eq_one.mp hone
    have hcardmul := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute E
      (Subgroup.zpowers x) hcommEU).1
    rw [hinf, Subgroup.card_bot, mul_one] at hcardmul
    have hcard : Nat.card ↥(E ⊔ Subgroup.zpowers x) = p ^ (k + 1) := by
      rw [hcardmul, hEcard, hUcard, pow_succ]
    refine ⟨E ⊔ Subgroup.zpowers x, ?_, hsupel, hcard⟩
    have hclosure_singleton : Subgroup.closure ({φ 0 h} : Set G) = Subgroup.zpowers (φ 0 h) := by
      refine le_antisymm ?_ ?_
      · refine (Subgroup.closure_le _).2 ?_
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact Subgroup.mem_zpowers _
      · rw [Subgroup.zpowers_le]
        exact Subgroup.subset_closure (Set.mem_singleton _)
    rw [Fin.range_fin_succ, Set.insert_eq, Subgroup.closure_union, hclosure_singleton]
    rw [show Subgroup.closure (Set.range (Fin.tail fun i : Fin (k + 1) => φ i h)) =
        Subgroup.closure (Set.range (fun i : Fin k => φ (Fin.succ i) h)) from rfl]
    rw [← hE, hx, sup_comm]

theorem le_pRank_of_commuting_sl2 [Finite F] [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h2 : ringChar F = 2) (hpd : p ∣ Nat.card F + 1) {k : ℕ}
    (φ : Fin k → (SL(2, F) →* G)) (hφ : ∀ i, Function.Injective (φ i))
    (hcomm : ∀ i j, i ≠ j → ∀ A B : SL(2, F), φ i A * φ j B = φ j B * φ i A) :
    k ≤ CFSG.Open.pRank p (⊤ : Subgroup G) := by
  obtain ⟨h, hh⟩ := exists_orderOf_sl2_of_card_add_one hp hp2 hpd
  obtain ⟨E, -, hEel, hEcard⟩ := exists_elemAbelian_of_commuting_sl2 hp hp2 h2 hpd h hh φ hφ hcomm
  exact CFSG.SectionRank.le_pRank hp.one_lt le_top hEel hEcard

end Engine

theorem eS_two_pow_eq_one {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpd : p ∣ 2 ^ n + 1) :
    eS (2 ^ n) p = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have h0 : ((2 ^ n + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hpd
  have h1 : (2 : ZMod p) ^ n + 1 = 0 := by
    have h := h0
    push_cast at h
    exact h
  have hneg : (2 : ZMod p) ^ n = -1 := by
    rw [eq_neg_iff_add_eq_zero]
    exact h1
  rw [eS]
  have h2n : ((2 ^ n : ℕ) : ZMod p) = (2 : ZMod p) ^ n := by rw [Nat.cast_pow]; norm_num
  rw [h2n, hneg]
  norm_num

theorem eP_two_pow_eq_two {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpd : p ∣ 2 ^ n + 1) :
    eP (2 ^ n) p = 2 := by
  have hm0 : rk2Ord p n = 2 := (rk2Ord_eq_two_iff hp hp2).2 hpd
  have h2n : ((2 ^ n : ℕ) : ZMod p) = (2 : ZMod p) ^ n := by rw [Nat.cast_pow]; norm_num
  rw [eP, h2n]
  exact hm0

@[expose] def f4TorusRoots : Fin 4 → Fin 4 → ℤ :=
  ![![1, 1, 0, 0], ![1, 1, 2, 0], ![1, 1, 2, 2], ![1, 3, 4, 2]]

theorem f4TorusRoots_check :
    (∀ i, CFSG.LieType.Chevalley.RootOps.isRootB CFSG.Blueprint.Chevalley.Tag.F4
      (f4TorusRoots i) = true) ∧
    (∀ i j : Fin 4, i ≠ j → CFSG.LieType.Steinberg.Adjoint.iform
      (τ := CFSG.Blueprint.Chevalley.Tag.F4) (f4TorusRoots i) (f4TorusRoots j) = 0 ∧
      CFSG.LieType.Chevalley.RootOps.isRootB CFSG.Blueprint.Chevalley.Tag.F4
        (f4TorusRoots i + f4TorusRoots j) = false ∧
      CFSG.LieType.Chevalley.RootOps.isRootB CFSG.Blueprint.Chevalley.Tag.F4
        (f4TorusRoots i - f4TorusRoots j) = false) := by
  decide +kernel


section Classical


theorem i165TorusRankLower_classical (hG : CFSG.Open.GriessAllModelsStatement)
    (K : Type) [Group K] [Finite K] (lab : GLALabel) (p : ℕ) (hK : Rk2IsLabel K lab)
    (hp : p.Prime) (hp2 : p ≠ 2) (hZ : ¬ p ∣ Nat.card (Subgroup.center K))
    (hpd : p ∣ 2 ^ lab.n + 1) (hn2 : 2 ≤ lab.n)
    (htag : lab.tag = .B ∨ lab.tag = .C ∨ (lab.tag = .D ∧ Even lab.rank)) :
    i165TorusRank lab ≤ CFSG.Open.pRank p (⊤ : Subgroup K) := by
  have hC : LieOddRankChev := CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20x_lieOddRankChev hG
  have hm0 : rk2Ord p lab.n = 2 := (rk2Ord_eq_two_iff hp hp2).2 hpd
  have htag' : lab.tag = .A ∨ lab.tag = .twA ∨ lab.tag = .B ∨ lab.tag = .C ∨
      lab.tag = .D ∨ lab.tag = .twD := by
    rcases htag with h | h | ⟨h, -⟩
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  have hneA : lab.tag ≠ .A := by
    rcases htag with h | h | ⟨h, -⟩
    · rw [h]; decide
    · rw [h]; decide
    · rw [h]; decide
  have hEq := rk2_pRank_eq_of_isLabel_classical hC hK hp hp2 htag'
    (fun h _ => absurd h hneA) (fun h _ => absurd h hneA) (fun h _ => absurd h hneA)
    (fun _ _ => hn2) (fun _ _ => hn2)
  rw [hEq]
  have hES := eS_two_pow_eq_one hp hp2 hpd
  have hEP := eP_two_pow_eq_two hp hp2 hpd
  obtain ⟨t, l, n⟩ := lab
  rcases htag with h | h | ⟨h, hev⟩
  · cases h
    simp only [i165TorusRank]
    rw [show rk2Chev ⟨.B, l, n⟩ p (Nat.card (Subgroup.center K)) =
        rkSp l (2 ^ n) p by simp [rk2Chev]]
    simp only [rkSp]
    rw [hES, Nat.div_one]
  · cases h
    simp only [i165TorusRank]
    rw [show rk2Chev ⟨.C, l, n⟩ p (Nat.card (Subgroup.center K)) =
        rkSp l (2 ^ n) p by simp [rk2Chev]]
    simp only [rkSp]
    rw [hES, Nat.div_one]
  · cases h
    simp only [i165TorusRank]
    rw [show rk2Chev ⟨.D, l, n⟩ p (Nat.card (Subgroup.center K)) =
        rkOmPlus l (2 ^ n) p by simp [rk2Chev]]
    simp only [rkOmPlus]
    rw [hEP, hES]
    have hcond : ¬ (2 ∣ 2 * l ∧ ¬ 2 ∣ l) := by
      rintro ⟨-, h⟩
      exact h hev.two_dvd
    rw [if_neg hcond, Nat.div_one]

end Classical

section Exceptional


private theorem le_pRank_of_adjoint_model {K : Type} [Group K] [Finite K] {p : ℕ}
    (hp : p.Prime) {τ : CFSG.Blueprint.Chevalley.Tag} {F : Type} [Field F] [Finite F]
    (θ : K ⧸ Subgroup.center K ≃* CFSG.Blueprint.Chevalley.adjointGroup τ F)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center K)) {k : ℕ}
    (hk : k ≤ CFSG.Open.pRank p (⊤ : Subgroup (CFSG.Blueprint.Chevalley.adjointGroup τ F))) :
    k ≤ CFSG.Open.pRank p (⊤ : Subgroup K) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hquot : CFSG.Open.pRank p (⊤ : Subgroup (K ⧸ Subgroup.center K)) =
      CFSG.Open.pRank p (⊤ : Subgroup K) :=
    CFSG.SectionRank.pRank_quotient_eq (Subgroup.center K) hZ
  have hiso : CFSG.Open.pRank p (⊤ : Subgroup (K ⧸ Subgroup.center K)) =
      CFSG.Open.pRank p (⊤ : Subgroup (CFSG.Blueprint.Chevalley.adjointGroup τ F)) :=
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt θ
  rw [← hquot, hiso]
  exact hk

theorem i165TorusRankLower_exceptional
    (K : Type) [Group K] [Finite K] (lab : GLALabel) (p : ℕ) (hK : Rk2IsLabel K lab)
    (hp : p.Prime) (hp2 : p ≠ 2) (hZ : ¬ p ∣ Nat.card (Subgroup.center K))
    (hpd : p ∣ 2 ^ lab.n + 1) (hn2 : 2 ≤ lab.n)
    (htag : lab.tag = .F4 ∨ lab.tag = .E7 ∨ lab.tag = .E8) :
    i165TorusRank lab ≤ CFSG.Open.pRank p (⊤ : Subgroup K) := by
  obtain ⟨hQ, hl, hM⟩ := rk2_model_of_isLabel hK
  obtain ⟨t, l, n⟩ := lab
  have hn1 : 1 ≤ n := hl.1
  rcases htag with hF4 | hE7 | hE8
  ·
    have hM' : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .F4 0 2 n :=
      lieModel_of_markedModel_F4 hF4 hM
    obtain ⟨-, F, hFld, hFin, hFcard, ⟨φ⟩⟩ :=
      hM'.chevalleyExceptionalModel (by decide : StatedLieTag.F4 ∈ CFSG.Blueprint.chevalleyExceptionalTags)
    letI : Field F := hFld
    letI : Finite F := hFin
    haveI : CharP F 2 :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
        Nat.prime_two hn1 hFcard
    have h2 : ringChar F = 2 := ringChar.eq F 2
    have hpdF : p ∣ Nat.card F + 1 := by rw [hFcard]; exact hpd
    obtain ⟨ι, hι, hcomm⟩ :=
      CFSG.RankThree.PartTwo.Census.Exceptional.exists_commuting_rootSL2 (K := F)
        CFSG.Blueprint.Chevalley.Tag.F4 f4TorusRoots f4TorusRoots_check
    have hk : 4 ≤ CFSG.Open.pRank p (⊤ : Subgroup (adjointGroup .F4 F)) :=
      CFSG.LocalAnalysis.GLTheoremA.Y10F.le_pRank_of_commuting_sl2 hp hp2 h2 hpdF ι hι hcomm
    let θ : K ⧸ Subgroup.center K ≃* adjointGroup .F4 F :=
      φ.trans (CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.adjointQuotientEquiv .F4 F)
    have := le_pRank_of_adjoint_model hp θ hZ hk
    have htF4 : t = .F4 := hF4
    subst htF4
    simpa [i165TorusRank] using this
  ·
    have hM' : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .E7 0 2 n :=
      lieModel_of_markedModel_E7 hE7 hM
    obtain ⟨-, F, hFld, hFin, hFcard, ⟨φ⟩⟩ :=
      hM'.chevalleyExceptionalModel (by decide : StatedLieTag.E7 ∈ CFSG.Blueprint.chevalleyExceptionalTags)
    letI : Field F := hFld
    letI : Finite F := hFin
    haveI : CharP F 2 :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
        Nat.prime_two hn1 hFcard
    have h2 : ringChar F = 2 := ringChar.eq F 2
    have hpdF : p ∣ Nat.card F + 1 := by rw [hFcard]; exact hpd
    obtain ⟨ι, hι, hcomm⟩ :=
      CFSG.RankThree.PartTwo.Census.Exceptional.exists_commuting_rootSL2 (K := F)
        CFSG.Blueprint.Chevalley.Tag.E7 e7OrthogonalRoots (by decide +kernel)
    have hk : 7 ≤ CFSG.Open.pRank p (⊤ : Subgroup (adjointGroup .E7 F)) :=
      CFSG.LocalAnalysis.GLTheoremA.Y10F.le_pRank_of_commuting_sl2 hp hp2 h2 hpdF ι hι hcomm
    let θ : K ⧸ Subgroup.center K ≃* adjointGroup .E7 F :=
      φ.trans (CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.adjointQuotientEquiv .E7 F)
    have := le_pRank_of_adjoint_model hp θ hZ hk
    have htE7 : t = .E7 := hE7
    subst htE7
    simpa [i165TorusRank] using this
  ·
    have hM' : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .E8 0 2 n :=
      lieModel_of_markedModel_E8 hE8 hM
    obtain ⟨-, F, hFld, hFin, hFcard, ⟨φ⟩⟩ :=
      hM'.chevalleyExceptionalModel (by decide : StatedLieTag.E8 ∈ CFSG.Blueprint.chevalleyExceptionalTags)
    letI : Field F := hFld
    letI : Finite F := hFin
    haveI : CharP F 2 :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
        Nat.prime_two hn1 hFcard
    have h2 : ringChar F = 2 := ringChar.eq F 2
    have hpdF : p ∣ Nat.card F + 1 := by rw [hFcard]; exact hpd
    obtain ⟨ι, hι, hcomm⟩ :=
      CFSG.RankThree.PartTwo.Census.Exceptional.exists_commuting_rootSL2 (K := F)
        CFSG.Blueprint.Chevalley.Tag.E8 e8OrthogonalRoots (by decide +kernel)
    have hk : 8 ≤ CFSG.Open.pRank p (⊤ : Subgroup (adjointGroup .E8 F)) :=
      CFSG.LocalAnalysis.GLTheoremA.Y10F.le_pRank_of_commuting_sl2 hp hp2 h2 hpdF ι hι hcomm
    let θ : K ⧸ Subgroup.center K ≃* adjointGroup .E8 F :=
      φ.trans (CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.adjointQuotientEquiv .E8 F)
    have := le_pRank_of_adjoint_model hp θ hZ hk
    have htE8 : t = .E8 := hE8
    subst htE8
    simpa [i165TorusRank] using this

theorem i165TorusRankLower_holds : I165TorusRankLower := by
  intro K _ _ lab p hK hp hp2 hZ hpd hn2 htag
  rcases htag with hB | hC | ⟨hD, hev⟩ | hF4 | hE7 | hE8
  · exact i165TorusRankLower_classical
      (CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds)
      K lab p hK hp hp2 hZ hpd hn2 (Or.inl hB)
  · exact i165TorusRankLower_classical
      (CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds)
      K lab p hK hp hp2 hZ hpd hn2 (Or.inr (Or.inl hC))
  · exact i165TorusRankLower_classical
      (CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds)
      K lab p hK hp hp2 hZ hpd hn2 (Or.inr (Or.inr ⟨hD, hev⟩))
  · exact i165TorusRankLower_exceptional K lab p hK hp hp2 hZ hpd hn2 (Or.inl hF4)
  · exact i165TorusRankLower_exceptional K lab p hK hp hp2 hZ hpd hn2 (Or.inr (Or.inl hE7))
  · exact i165TorusRankLower_exceptional K lab p hK hp hp2 hZ hpd hn2 (Or.inr (Or.inr hE8))

end Exceptional

end CFSG.LocalAnalysis.GLTheoremA.Y10F
