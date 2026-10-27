module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.UpperE8
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.UpperE7
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.ExcE7
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.ClassicalArith
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.ExcResOthStd
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE8Levi
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.SubsystemRank

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.Assembly CFSG.ComponentClassification.CatLeafProof
open CFSG.StandardType.F4Rest
open scoped MatrixGroups

theorem pRank_specialLinear_le {K : Type} [Field K] [Finite K] [CharP K 2] {p d : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : ¬ p ∣ Nat.card K - 1) :
    CFSG.Open.pRank p (⊤ : Subgroup (SL(d, K))) ≤ d / 2 := by
  have hpK : (p : K) ≠ 0 := natCast_ne_zero_of_charTwo hp hp2
  refine CFSG.SectionRank.pRank_le hp.one_lt fun F _ hF => ?_
  have hb := card_le_pow_of_injective_GL (G := SL(d, K)) (ι := Fin d) (K := K) hp hpK
    (φ := Matrix.SpecialLinearGroup.toGL) Matrix.SpecialLinearGroup.toGL_injective hF
  have hd : 2 ≤ CFSG.StandardType.OrdPNS.ordQ K p := two_le_ordQ hp hpK hpq
  have hdd : Fintype.card (Fin d) / CFSG.StandardType.OrdPNS.ordQ K p ≤ d / 2 := by
    rw [Fintype.card_fin]
    exact div_le_div_two hd
  exact hb.trans (Nat.pow_le_pow_right hp.pos hdd)

theorem card_le_pow_of_le_map_subtype {τ : Tag} {K : Type} [Field K] [Finite K] {p k : ℕ}
    (hp : p.Prime) {S : Subgroup (adjointGroup τ K)} [Finite S]
    (hS : CFSG.Open.pRank p (⊤ : Subgroup S) ≤ k) {E : Subgroup (ModGL τ K)}
    (hE : E ≤ S.map (adjointGroup τ K).subtype) (hEel : IsElemAbelian p E) :
    Nat.card E ≤ p ^ k := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype K := Fintype.ofFinite K
  set E' : Subgroup (adjointGroup τ K) := E.comap (adjointGroup τ K).subtype with hE'def
  have hErange : E ≤ (adjointGroup τ K).subtype.range :=
    hE.trans (Subgroup.map_le_range _ _)
  have hE'le : E' ≤ S := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hE hx
    rwa [show y = x from Subtype.ext hyx] at hy
  have hcard : Nat.card E' = Nat.card E := by
    calc Nat.card E' = Nat.card (E'.map (adjointGroup τ K).subtype) :=
          (Subgroup.card_map_of_injective (adjointGroup τ K).subtype_injective).symm
      _ = Nat.card E := by rw [hE'def, Subgroup.map_comap_eq_self hErange]
  have hE'el : IsElemAbelian p E' :=
    isElemAbelian_comap (adjointGroup τ K).subtype_injective hEel
  obtain ⟨m, hm⟩ := (hE'el.isPGroup : IsPGroup p E').exists_card_eq
  have hmle : m ≤ k := by
    have h1 : m ≤ CFSG.Open.pRank p S :=
      CFSG.SectionRank.le_pRank hp.one_lt hE'le hE'el hm
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup S] at h1
    exact h1.trans hS
  calc Nat.card E = Nat.card E' := hcard.symm
    _ = p ^ m := hm
    _ ≤ p ^ k := Nat.pow_le_pow_right hp.pos hmle

theorem commute_subsystemGroup_of_cartan_zero {K : Type} [Field K]
    {A B : Set (Fin Tag.E8.rank)}
    (h : ∀ a ∈ A, ∀ b ∈ B, Tag.cartan .E8 a b = 0) :
    ∀ x ∈ subsystemGroup Tag.E8 K A, ∀ y ∈ subsystemGroup Tag.E8 K B, Commute x y := by
  have hgen : ∀ x ∈ {g | ∃ i ∈ A, ∃ c : K,
      g = xUnit Tag.E8 K i c ∨ g = yUnit Tag.E8 K i c},
      ∀ y ∈ {g | ∃ i ∈ B, ∃ c : K,
        g = xUnit Tag.E8 K i c ∨ g = yUnit Tag.E8 K i c}, Commute x y := by
    rintro _ ⟨a, ha, c, rfl | rfl⟩ _ ⟨b, hb, d, rfl | rfl⟩
    · exact (CFSG.HardMathSupport.Dickson.Sec6.I1431.excOth_commute_gen
        (Or.inr (Or.inr (Or.inr rfl))) (h a ha b hb) c d).1
    · exact (CFSG.HardMathSupport.Dickson.Sec6.I1431.excOth_commute_gen
        (Or.inr (Or.inr (Or.inr rfl))) (h a ha b hb) c d).2.1
    · exact (CFSG.HardMathSupport.Dickson.Sec6.I1431.excOth_commute_gen
        (Or.inr (Or.inr (Or.inr rfl))) (h a ha b hb) c d).2.2.1
    · exact (CFSG.HardMathSupport.Dickson.Sec6.I1431.excOth_commute_gen
        (Or.inr (Or.inr (Or.inr rfl))) (h a ha b hb) c d).2.2.2
  intro x hx y hy
  have hle : subsystemGroup Tag.E8 K B ≤
      Subgroup.centralizer (subsystemGroup Tag.E8 K A : Set (ModGL Tag.E8 K)) := by
    refine (Subgroup.closure_le _).2 fun y hy => ?_
    have hle' : subsystemGroup Tag.E8 K A ≤
        Subgroup.centralizer ({y} : Set (ModGL Tag.E8 K)) :=
      (Subgroup.closure_le _).2 fun x hx =>
        Subgroup.mem_centralizer_singleton_iff.2 (hgen x hx y hy).eq
    exact Subgroup.mem_centralizer_iff.2 fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.1 (hle' hx)
  exact Subgroup.mem_centralizer_iff.1 (hle hy) x hx

theorem not_dvd_card_inf_subsystemGroup_e8 {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hpq : ¬ p ∣ Nat.card K - 1) {J₁ J₂ : Set (Fin Tag.E8.rank)}
    (hcomm : ∀ x ∈ subsystemGroup Tag.E8 K J₁, ∀ y ∈ subsystemGroup Tag.E8 K J₂,
      Commute x y) :
    ¬ p ∣ Nat.card ↥(subsystemGroup Tag.E8 K J₁ ⊓ subsystemGroup Tag.E8 K J₂) := by
  haveI : Fintype K := Fintype.ofFinite K
  have hT : Nat.card (torusGroup Tag.E8 K) = (Nat.card K - 1) ^ 8 :=
    CFSG.Timmesfeld.ExceptionalOrders.card_torusGroup_E8 (K := K)
  have hle : subsystemGroup Tag.E8 K J₁ ⊓ subsystemGroup Tag.E8 K J₂ ≤
      torusGroup Tag.E8 K := by
    rintro z ⟨hz1, hz2⟩
    have hz : (⟨z, hz1⟩ : subsystemGroup Tag.E8 K J₁) ∈
        Subgroup.center (subsystemGroup Tag.E8 K J₁) := by
      rw [Subgroup.mem_center_iff]
      intro w
      exact Subtype.ext (hcomm w w.2 z hz2).eq
    exact supportedTorus_le_torusGroup J₁
      ((mem_center_subsystemGroup_iff (g := ⟨z, hz1⟩)).1 hz).1
  intro hd
  have hdvd0 : Nat.card ↥(subsystemGroup Tag.E8 K J₁ ⊓ subsystemGroup Tag.E8 K J₂) ∣
      Nat.card ↥(torusGroup Tag.E8 K) :=
    Subgroup.card_dvd_of_le (H := subsystemGroup Tag.E8 K J₁ ⊓ subsystemGroup Tag.E8 K J₂)
      (K := torusGroup Tag.E8 K) hle
  rw [hT] at hdvd0
  exact hpq (hp.dvd_of_dvd_pow (hd.trans hdvd0))

@[expose] def e8A7Node : Fin 7 → Fin Tag.E8.rank := ![0, 2, 3, 4, 5, 6, 7]

@[expose] def e8A6Node : Fin 6 → Fin Tag.E8.rank := ![1, 3, 4, 5, 6, 7]

@[expose] def e8A4Node : Fin 4 → Fin Tag.E8.rank := ![4, 5, 6, 7]

@[expose] def e8A4Node' : Fin 4 → Fin Tag.E8.rank := ![0, 2, 3, 1]

@[expose] def e8A3Node : Fin 3 → Fin Tag.E8.rank := ![5, 6, 7]

@[expose] def e8D7Node : Fin 7 → Fin Tag.E8.rank := ![7, 6, 5, 4, 3, 2, 1]

@[expose] def e8D5Node : Fin 5 → Fin Tag.E8.rank := ![0, 2, 3, 1, 4]

@[expose] def e8A2Node : Fin 2 → Fin Tag.E8.rank := ![6, 7]

@[expose] def e8E6Node : Fin 6 → Fin Tag.E8.rank := ![0, 1, 2, 3, 4, 5]

theorem mem_range_e8A7Node (j : Fin Tag.E8.rank) :
    j ∈ Set.range e8A7Node ↔ j ≠ 1 := by
  fin_cases j <;> decide

theorem mem_range_e8A6Node (j : Fin Tag.E8.rank) :
    j ∈ Set.range e8A6Node ↔ j ≠ 0 ∧ j ≠ 2 := by
  fin_cases j <;> decide

theorem mem_range_e8A4Node (j : Fin Tag.E8.rank) :
    j ∈ Set.range e8A4Node ↔ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by
  fin_cases j <;> decide

theorem mem_range_e8A4Node' (j : Fin Tag.E8.rank) :
    j ∈ Set.range e8A4Node' ↔ j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by
  fin_cases j <;> decide

theorem mem_range_e8A3Node (j : Fin Tag.E8.rank) :
    j ∈ Set.range e8A3Node ↔ j = 5 ∨ j = 6 ∨ j = 7 := by
  fin_cases j <;> decide

theorem mem_range_e8D7Node (j : Fin Tag.E8.rank) :
    j ∈ Set.range e8D7Node ↔ j ≠ 0 := by
  fin_cases j <;> decide

theorem mem_range_e8D5Node (j : Fin Tag.E8.rank) :
    j ∈ Set.range e8D5Node ↔ j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by
  fin_cases j <;> decide

theorem mem_range_e8A2Node (j : Fin Tag.E8.rank) :
    j ∈ Set.range e8A2Node ↔ j = 6 ∨ j = 7 := by
  fin_cases j <;> decide

theorem mem_range_e8E6Node (j : Fin Tag.E8.rank) :
    j ∈ Set.range e8E6Node ↔ j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by
  fin_cases j <;> decide

theorem mem_range_e8E7Node (j : Fin Tag.E8.rank) :
    j ∈ Set.range e8E7Node ↔ j ≠ 7 := by
  fin_cases j <;> decide

theorem e8A2Node_range : Set.range e8A2Node = ({6, 7} : Set (Fin Tag.E8.rank)) := by
  ext j
  rw [mem_range_e8A2Node]
  fin_cases j <;> simp

theorem card_le_pow_subsystemGroup_e8A {m : ℕ} (hm : 3 ≤ m) (ι : Fin m → Fin Tag.E8.rank)
    (hadj : ∀ i j : Fin m, j.val = i.val + 1 →
      ι i ≠ ι j ∧ Tag.cartan .E8 (ι i) (ι j) = -1 ∧ Tag.cartan .E8 (ι j) (ι i) = -1 ∧
        ∃ l, ¬ (3 : ℤ) ∣ Tag.cartan .E8 (ι i) l + 2 * Tag.cartan .E8 (ι j) l)
    (hnadj : ∀ i j : Fin m, i ≠ j → ¬ j.val = i.val + 1 → ¬ i.val = j.val + 1 →
      ι i ≠ ι j ∧ Tag.cartan .E8 (ι i) (ι j) = 0 ∧ Tag.cartan .E8 (ι j) (ι i) = 0)
    {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : ¬ p ∣ Nat.card K - 1) {E : Subgroup (ModGL Tag.E8 K)}
    (hE : E ≤ subsystemGroup Tag.E8 K (Set.range ι)) (hEel : IsElemAbelian p E) :
    Nat.card E ≤ p ^ ((m + 1) / 2) := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, -, hK⟩ := FiniteField.card K 2
  have hKn : Nat.card K = 2 ^ (n : ℕ) := by rw [← Fintype.card_eq_nat_card]; exact hK
  have hn : 1 ≤ (n : ℕ) := CFSG.Quasithin.R3c2.one_le_of_natCard_eq_two_pow hKn
  obtain ⟨O, C, hE'⟩ := exists_e8_chevalleyExtras K
  obtain ⟨ρ, hρ, hcomm, hψ⟩ := exists_levi_frame hE' rfl ι hadj hnadj
  have hadm : StatedLieAdmissible .PSL (m + 1) 2 (n : ℕ) := by
    refine ⟨Nat.prime_two, hn, by omega, ?_, ?_⟩
    · intro h
      exact absurd (congrArg Prod.fst h) (by omega)
    · intro h
      exact absurd (congrArg Prod.fst h) (by omega)
  obtain ⟨Ψ, hker, hrange, hqs, hmodel⟩ :=
    specialLinear_frame_subgroup (m := m) hadm hm hKn
      (U := fun k => CFSG.LieType.CurtisTits.rankOne (e8Datum K).rootGroup (ι k)) hcomm hρ hψ
  have hpK : (p : K) ≠ 0 := natCast_ne_zero_of_charTwo hp hp2
  have hpker : ¬ p ∣ Nat.card Ψ.ker := by
    intro hd
    have hcenter : Nat.card (Subgroup.center (SL(m + 1, K))) ∣ Nat.card K - 1 :=
      (CFSG.LieType.Steinberg.card_center_specialLinearGroup_dvd (n := m + 1) (by omega) K).trans
        (Nat.gcd_dvd_right _ _)
    exact hpq (hd.trans ((Subgroup.card_dvd_of_le hker).trans hcenter))
  have hS : CFSG.Open.pRank p (⊤ : Subgroup Ψ.range) ≤ (m + 1) / 2 := by
    have h1 : CFSG.Open.pRank p (⊤ : Subgroup Ψ.range) =
        CFSG.Open.pRank p (⊤ : Subgroup (SL(m + 1, K) ⧸ Ψ.ker)) :=
      CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt
        (QuotientGroup.quotientKerEquivRange Ψ).symm
    rw [h1, CFSG.SectionRank.pRank_quotient_eq Ψ.ker hpker]
    exact pRank_specialLinear_le (K := K) (p := p) (d := m + 1) hp hp2 hpq
  have hEmap : E ≤ Ψ.range.map (adjointGroup Tag.E8 K).subtype := by
    rw [hrange, map_subtype_iSup_rankOne ι]
    exact hE
  exact card_le_pow_of_le_map_subtype hp hS hEmap hEel

theorem e8A7_adj : ∀ i j : Fin 7, j.val = i.val + 1 →
    e8A7Node i ≠ e8A7Node j ∧ Tag.cartan .E8 (e8A7Node i) (e8A7Node j) = -1 ∧
      Tag.cartan .E8 (e8A7Node j) (e8A7Node i) = -1 ∧
      ∃ l, ¬ (3 : ℤ) ∣ Tag.cartan .E8 (e8A7Node i) l + 2 * Tag.cartan .E8 (e8A7Node j) l := by
  decide +kernel

theorem e8A7_nadj : ∀ i j : Fin 7, i ≠ j → ¬ j.val = i.val + 1 → ¬ i.val = j.val + 1 →
    e8A7Node i ≠ e8A7Node j ∧ Tag.cartan .E8 (e8A7Node i) (e8A7Node j) = 0 ∧
      Tag.cartan .E8 (e8A7Node j) (e8A7Node i) = 0 := by
  decide +kernel

theorem e8A6_adj : ∀ i j : Fin 6, j.val = i.val + 1 →
    e8A6Node i ≠ e8A6Node j ∧ Tag.cartan .E8 (e8A6Node i) (e8A6Node j) = -1 ∧
      Tag.cartan .E8 (e8A6Node j) (e8A6Node i) = -1 ∧
      ∃ l, ¬ (3 : ℤ) ∣ Tag.cartan .E8 (e8A6Node i) l + 2 * Tag.cartan .E8 (e8A6Node j) l := by
  decide +kernel

theorem e8A6_nadj : ∀ i j : Fin 6, i ≠ j → ¬ j.val = i.val + 1 → ¬ i.val = j.val + 1 →
    e8A6Node i ≠ e8A6Node j ∧ Tag.cartan .E8 (e8A6Node i) (e8A6Node j) = 0 ∧
      Tag.cartan .E8 (e8A6Node j) (e8A6Node i) = 0 := by
  decide +kernel

theorem e8A4_adj : ∀ i j : Fin 4, j.val = i.val + 1 →
    e8A4Node i ≠ e8A4Node j ∧ Tag.cartan .E8 (e8A4Node i) (e8A4Node j) = -1 ∧
      Tag.cartan .E8 (e8A4Node j) (e8A4Node i) = -1 ∧
      ∃ l, ¬ (3 : ℤ) ∣ Tag.cartan .E8 (e8A4Node i) l + 2 * Tag.cartan .E8 (e8A4Node j) l := by
  decide +kernel

theorem e8A4_nadj : ∀ i j : Fin 4, i ≠ j → ¬ j.val = i.val + 1 → ¬ i.val = j.val + 1 →
    e8A4Node i ≠ e8A4Node j ∧ Tag.cartan .E8 (e8A4Node i) (e8A4Node j) = 0 ∧
      Tag.cartan .E8 (e8A4Node j) (e8A4Node i) = 0 := by
  decide +kernel

theorem e8A4'_adj : ∀ i j : Fin 4, j.val = i.val + 1 →
    e8A4Node' i ≠ e8A4Node' j ∧ Tag.cartan .E8 (e8A4Node' i) (e8A4Node' j) = -1 ∧
      Tag.cartan .E8 (e8A4Node' j) (e8A4Node' i) = -1 ∧
      ∃ l, ¬ (3 : ℤ) ∣ Tag.cartan .E8 (e8A4Node' i) l + 2 * Tag.cartan .E8 (e8A4Node' j) l := by
  decide +kernel

theorem e8A4'_nadj : ∀ i j : Fin 4, i ≠ j → ¬ j.val = i.val + 1 → ¬ i.val = j.val + 1 →
    e8A4Node' i ≠ e8A4Node' j ∧ Tag.cartan .E8 (e8A4Node' i) (e8A4Node' j) = 0 ∧
      Tag.cartan .E8 (e8A4Node' j) (e8A4Node' i) = 0 := by
  decide +kernel

theorem e8A3_adj : ∀ i j : Fin 3, j.val = i.val + 1 →
    e8A3Node i ≠ e8A3Node j ∧ Tag.cartan .E8 (e8A3Node i) (e8A3Node j) = -1 ∧
      Tag.cartan .E8 (e8A3Node j) (e8A3Node i) = -1 ∧
      ∃ l, ¬ (3 : ℤ) ∣ Tag.cartan .E8 (e8A3Node i) l + 2 * Tag.cartan .E8 (e8A3Node j) l := by
  decide +kernel

theorem e8A3_nadj : ∀ i j : Fin 3, i ≠ j → ¬ j.val = i.val + 1 → ¬ i.val = j.val + 1 →
    e8A3Node i ≠ e8A3Node j ∧ Tag.cartan .E8 (e8A3Node i) (e8A3Node j) = 0 ∧
      Tag.cartan .E8 (e8A3Node j) (e8A3Node i) = 0 := by
  decide +kernel

theorem card_le_pow_four_subsystemGroup_e8A7 {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : ¬ p ∣ Nat.card K - 1)
    {E : Subgroup (ModGL Tag.E8 K)}
    (hE : E ≤ subsystemGroup Tag.E8 K (Set.range e8A7Node))
    (hEel : IsElemAbelian p E) : Nat.card E ≤ p ^ 4 := by
  have h := card_le_pow_subsystemGroup_e8A (m := 7) (by norm_num) e8A7Node
    e8A7_adj e8A7_nadj hp hp2 hpq hE hEel
  simpa using h

theorem card_le_pow_three_subsystemGroup_e8A6 {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : ¬ p ∣ Nat.card K - 1)
    {E : Subgroup (ModGL Tag.E8 K)}
    (hE : E ≤ subsystemGroup Tag.E8 K (Set.range e8A6Node))
    (hEel : IsElemAbelian p E) : Nat.card E ≤ p ^ 3 := by
  have h := card_le_pow_subsystemGroup_e8A (m := 6) (by norm_num) e8A6Node
    e8A6_adj e8A6_nadj hp hp2 hpq hE hEel
  simpa using h

theorem card_le_pow_two_subsystemGroup_e8A4 {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : ¬ p ∣ Nat.card K - 1)
    {E : Subgroup (ModGL Tag.E8 K)}
    (hE : E ≤ subsystemGroup Tag.E8 K (Set.range e8A4Node))
    (hEel : IsElemAbelian p E) : Nat.card E ≤ p ^ 2 := by
  have h := card_le_pow_subsystemGroup_e8A (m := 4) (by norm_num) e8A4Node
    e8A4_adj e8A4_nadj hp hp2 hpq hE hEel
  simpa using h

theorem card_le_pow_two_subsystemGroup_e8A4' {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : ¬ p ∣ Nat.card K - 1)
    {E : Subgroup (ModGL Tag.E8 K)}
    (hE : E ≤ subsystemGroup Tag.E8 K (Set.range e8A4Node'))
    (hEel : IsElemAbelian p E) : Nat.card E ≤ p ^ 2 := by
  have h := card_le_pow_subsystemGroup_e8A (m := 4) (by norm_num) e8A4Node'
    e8A4'_adj e8A4'_nadj hp hp2 hpq hE hEel
  simpa using h

theorem card_le_pow_two_subsystemGroup_e8A3 {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : ¬ p ∣ Nat.card K - 1)
    {E : Subgroup (ModGL Tag.E8 K)}
    (hE : E ≤ subsystemGroup Tag.E8 K (Set.range e8A3Node))
    (hEel : IsElemAbelian p E) : Nat.card E ≤ p ^ 2 := by
  have h := card_le_pow_subsystemGroup_e8A (m := 3) (by norm_num) e8A3Node
    e8A3_adj e8A3_nadj hp hp2 hpq hE hEel
  simpa using h

theorem card_le_pow_one_subsystemGroup_e8node {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : ¬ p ∣ Nat.card K - 1)
    (i : Fin Tag.E8.rank) {E : Subgroup (ModGL Tag.E8 K)}
    (hE : E ≤ subsystemGroup Tag.E8 K {i}) (hEel : IsElemAbelian p E) :
    Nat.card E ≤ p ^ 1 := by
  have hpK : (p : K) ≠ 0 := natCast_ne_zero_of_charTwo (K := K) hp hp2
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hinj : Function.Injective (simpleRootSL2 Tag.E8 K i) :=
    CFSG.LieType.Chevalley.E6GraphRadical.simpleRootSL2_injective_of_two h2 i
  have hrange : (simpleRootSL2 Tag.E8 K i).range = subsystemGroup Tag.E8 K {i} := by
    rw [range_simpleRootSL2, subsystemGroup]
    congr 1
    ext g
    constructor
    · rintro (⟨c, rfl⟩ | ⟨c, rfl⟩)
      · exact ⟨i, by simp, c, Or.inl rfl⟩
      · exact ⟨i, by simp, c, Or.inr rfl⟩
    · rintro ⟨j, hj, c, rfl | rfl⟩
      · rw [Set.mem_singleton_iff] at hj
        subst hj
        exact Or.inl ⟨c, rfl⟩
      · rw [Set.mem_singleton_iff] at hj
        subst hj
        exact Or.inr ⟨c, rfl⟩
  let Et : Subgroup (SL(2, K)) := E.comap (simpleRootSL2 Tag.E8 K i)
  have hEtrange : E ≤ (simpleRootSL2 Tag.E8 K i).range := hrange ▸ hE
  have hEtcard : Nat.card Et = Nat.card E := by
    calc Nat.card Et = Nat.card (Et.map (simpleRootSL2 Tag.E8 K i)) :=
          (Subgroup.card_map_of_injective hinj).symm
      _ = Nat.card E := by rw [Subgroup.map_comap_eq_self hEtrange]
  have hEtel : IsElemAbelian p Et := isElemAbelian_comap hinj hEel
  have hbound := card_le_pow_of_injective_GL (G := SL(2, K)) (ι := Fin 2) (K := K) hp hpK
    (φ := Matrix.SpecialLinearGroup.toGL) Matrix.SpecialLinearGroup.toGL_injective hEtel
  have hd : 2 ≤ CFSG.StandardType.OrdPNS.ordQ K p := two_le_ordQ hp hpK hpq
  have h2d : Fintype.card (Fin 2) / CFSG.StandardType.OrdPNS.ordQ K p ≤ 1 := by
    rw [Fintype.card_fin]
    have : 2 / CFSG.StandardType.OrdPNS.ordQ K p ≤ 2 / 2 :=
      Nat.div_le_div_left hd (by norm_num)
    omega
  calc Nat.card E = Nat.card Et := hEtcard.symm
    _ ≤ p ^ (Fintype.card (Fin 2) / CFSG.StandardType.OrdPNS.ordQ K p) := hbound
    _ ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos h2d

theorem map_subtype_pairSubgroup {K : Type} [Field K] (i j : Fin Tag.E8.rank) :
    (CFSG.LieType.CurtisTits.rankOne (e8Datum K).rootGroup i ⊔
      CFSG.LieType.CurtisTits.rankOne (e8Datum K).rootGroup j).map
      (adjointGroup Tag.E8 K).subtype =
      subsystemGroup Tag.E8 K ({i, j} : Set (Fin Tag.E8.rank)) := by
  have h1 : (⨆ k : Fin 2, CFSG.LieType.CurtisTits.rankOne (e8Datum K).rootGroup
      ((![i, j] : Fin 2 → Fin Tag.E8.rank) k)) =
      CFSG.LieType.CurtisTits.rankOne (e8Datum K).rootGroup i ⊔
        CFSG.LieType.CurtisTits.rankOne (e8Datum K).rootGroup j := by
    refine le_antisymm ?_ ?_
    · refine iSup_le fun k => ?_
      fin_cases k
      · exact le_sup_left
      · exact le_sup_right
    · exact sup_le (le_iSup (fun k : Fin 2 => CFSG.LieType.CurtisTits.rankOne
        (e8Datum K).rootGroup ((![i, j] : Fin 2 → Fin Tag.E8.rank) k)) 0)
        (le_iSup (fun k : Fin 2 => CFSG.LieType.CurtisTits.rankOne
        (e8Datum K).rootGroup ((![i, j] : Fin 2 → Fin Tag.E8.rank) k)) 1)
  have h2 := map_subtype_iSup_rankOne (τ := Tag.E8) (K := K) (r := 2)
    (![i, j] : Fin 2 → Fin Tag.E8.rank)
  rw [← h1, h2]
  congr 1
  ext x
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨k, rfl⟩
    fin_cases k
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

theorem card_le_pow_one_subsystemGroup_e8A2 {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : ¬ p ∣ Nat.card K - 1)
    {i j : Fin Tag.E8.rank} (hij : i ≠ j) (hcij : Tag.cartan .E8 i j = -1)
    (hcji : Tag.cartan .E8 j i = -1)
    (hk : ∃ l, ¬ (3 : ℤ) ∣ Tag.cartan .E8 i l + 2 * Tag.cartan .E8 j l)
    {E : Subgroup (ModGL Tag.E8 K)} (hE : E ≤ subsystemGroup Tag.E8 K ({i, j} : Set (Fin Tag.E8.rank)))
    (hEel : IsElemAbelian p E) : Nat.card E ≤ p ^ 1 := by
  have hpK : (p : K) ≠ 0 := natCast_ne_zero_of_charTwo hp hp2
  obtain ⟨l, hl⟩ := hk
  obtain ⟨O, C, hE'⟩ := exists_e8_chevalleyExtras K
  obtain ⟨emb, hinj, hpair, -⟩ :=
    CFSG.ClassicalInvolution.WeakCT.exists_sl3Levi (D := e8Datum K) (x := e8Par K) hE' rfl
      hij hcij hcji hl
  have hpairRoots : ∀ γ : Fin Tag.E8.rank → ℤ, γ ∈ CFSG.Timmesfeld.pairRoots (e8Datum K) i j →
      (e8Datum K).rootGroup γ ≤ emb.range := hpair
  have hs1 : Pi.single i 1 ∈ CFSG.Timmesfeld.pairRoots (e8Datum K) i j := by
    rw [CFSG.Timmesfeld.mem_pairRoots_iff]
    refine ⟨CFSG.Timmesfeld.LevisExtras.single_mem_roots (D := e8Datum K) i, ?_⟩
    intro k hk
    have hki : k ≠ i := fun h => hk (by simp [h])
    rw [Pi.single_eq_of_ne hki]
  have hs2 : -Pi.single i 1 ∈ CFSG.Timmesfeld.pairRoots (e8Datum K) i j := by
    rw [CFSG.Timmesfeld.mem_pairRoots_iff]
    refine ⟨CFSG.Timmesfeld.LevisExtras.neg_mem_roots (CFSG.Timmesfeld.LevisExtras.single_mem_roots (D := e8Datum K) i), ?_⟩
    intro k hk
    have hki : k ≠ i := fun h => hk (by simp [h])
    rw [Pi.neg_apply, Pi.single_eq_of_ne hki, neg_zero]
  have ht1 : Pi.single j 1 ∈ CFSG.Timmesfeld.pairRoots (e8Datum K) i j := by
    rw [CFSG.Timmesfeld.mem_pairRoots_iff]
    refine ⟨CFSG.Timmesfeld.LevisExtras.single_mem_roots (D := e8Datum K) j, ?_⟩
    intro k hk
    have hkj : k ≠ j := fun h => hk (by simp [h])
    rw [Pi.single_eq_of_ne hkj]
  have ht2 : -Pi.single j 1 ∈ CFSG.Timmesfeld.pairRoots (e8Datum K) i j := by
    rw [CFSG.Timmesfeld.mem_pairRoots_iff]
    refine ⟨CFSG.Timmesfeld.LevisExtras.neg_mem_roots (CFSG.Timmesfeld.LevisExtras.single_mem_roots (D := e8Datum K) j), ?_⟩
    intro k hk
    have hkj : k ≠ j := fun h => hk (by simp [h])
    rw [Pi.neg_apply, Pi.single_eq_of_ne hkj, neg_zero]
  have hSle : CFSG.LieType.CurtisTits.rankOne (e8Datum K).rootGroup i ⊔
      CFSG.LieType.CurtisTits.rankOne (e8Datum K).rootGroup j ≤ emb.range :=
    sup_le (sup_le (hpairRoots _ hs1) (hpairRoots _ hs2))
      (sup_le (hpairRoots _ ht1) (hpairRoots _ ht2))
  have hErange : E ≤ (CFSG.LieType.CurtisTits.rankOne (e8Datum K).rootGroup i ⊔
      CFSG.LieType.CurtisTits.rankOne (e8Datum K).rootGroup j).map (adjointGroup Tag.E8 K).subtype := by
    rw [map_subtype_pairSubgroup]
    exact hE
  set E' : Subgroup (adjointGroup Tag.E8 K) :=
    E.comap (adjointGroup Tag.E8 K).subtype with hE'def
  have hE'le : E' ≤ CFSG.LieType.CurtisTits.rankOne (e8Datum K).rootGroup i ⊔
      CFSG.LieType.CurtisTits.rankOne (e8Datum K).rootGroup j := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hErange hx
    rwa [show y = x from Subtype.ext hyx] at hy
  have hE'le_range : E' ≤ emb.range := hE'le.trans hSle
  have hcard' : Nat.card E' = Nat.card E := by
    calc Nat.card E' = Nat.card (E'.map (adjointGroup Tag.E8 K).subtype) :=
          (Subgroup.card_map_of_injective (adjointGroup Tag.E8 K).subtype_injective).symm
      _ = Nat.card E := by
        rw [hE'def, Subgroup.map_comap_eq_self]
        exact hErange.trans (Subgroup.map_le_range _ _)
  have hE'el : IsElemAbelian p E' :=
    isElemAbelian_comap (adjointGroup Tag.E8 K).subtype_injective hEel
  set E'' : Subgroup (SL(3, K)) := E'.comap emb with hE''def
  have hcard'' : Nat.card E'' = Nat.card E' := by
    have hker : emb.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).2 hinj
    calc Nat.card E'' = Nat.card emb.ker * Nat.card E' :=
          card_comap_of_le_range emb hE'le_range
      _ = Nat.card E' := by rw [hker, Subgroup.card_bot, one_mul]
  have hE''el : IsElemAbelian p E'' := isElemAbelian_comap hinj hE'el
  have hbound := card_le_pow_of_injective_GL (G := SL(3, K)) (ι := Fin 3) (K := K) hp hpK
    (φ := Matrix.SpecialLinearGroup.toGL) Matrix.SpecialLinearGroup.toGL_injective hE''el
  have hd : 2 ≤ CFSG.StandardType.OrdPNS.ordQ K p := two_le_ordQ hp hpK hpq
  have h31 : Fintype.card (Fin 3) / CFSG.StandardType.OrdPNS.ordQ K p ≤ 1 := by
    rw [Fintype.card_fin]
    have : 3 / CFSG.StandardType.OrdPNS.ordQ K p ≤ 3 / 2 :=
      Nat.div_le_div_left hd (by norm_num)
    omega
  calc Nat.card E = Nat.card E' := hcard'.symm
    _ = Nat.card E'' := hcard''.symm
    _ ≤ p ^ (Fintype.card (Fin 3) / CFSG.StandardType.OrdPNS.ordQ K p) := hbound
    _ ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos h31

theorem e8D7_adj : ∀ i j : Fin 7, Timmesfeld.edgeD 7 i j →
    e8D7Node i ≠ e8D7Node j ∧ Tag.cartan .E8 (e8D7Node i) (e8D7Node j) = -1 ∧
      Tag.cartan .E8 (e8D7Node j) (e8D7Node i) = -1 ∧
      ∃ l, ¬ (3 : ℤ) ∣ Tag.cartan .E8 (e8D7Node i) l + 2 * Tag.cartan .E8 (e8D7Node j) l := by
  decide +kernel

theorem e8D7_nadj : ∀ i j : Fin 7, i ≠ j → ¬ Timmesfeld.edgeD 7 i j →
    ¬ Timmesfeld.edgeD 7 j i →
    e8D7Node i ≠ e8D7Node j ∧ Tag.cartan .E8 (e8D7Node i) (e8D7Node j) = 0 ∧
      Tag.cartan .E8 (e8D7Node j) (e8D7Node i) = 0 := by
  decide +kernel

theorem card_le_pow_six_subsystemGroup_e8D7 {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hd : p ∣ Nat.card K + 1)
    {E : Subgroup (ModGL Tag.E8 K)}
    (hE : E ≤ subsystemGroup Tag.E8 K (Set.range e8D7Node))
    (hEel : IsElemAbelian p E) : Nat.card E ≤ p ^ 6 := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, -, hK⟩ := FiniteField.card K 2
  have hKn : Nat.card K = 2 ^ (n : ℕ) := by rw [← Fintype.card_eq_nat_card]; exact hK
  have hn : 1 ≤ (n : ℕ) := CFSG.Quasithin.R3c2.one_le_of_natCard_eq_two_pow hKn
  have hpq : ¬ p ∣ Nat.card K - 1 :=
    CFSG.RankThree.PartOne.S15K.not_dvd_sub_one_of_dvd_add_one Nat.card_pos
      (by have := hp.two_le; omega) hd
  obtain ⟨O, C, hE'⟩ := exists_e8_chevalleyExtras K
  obtain ⟨ρ, hρ, hcomm, hψ⟩ := exists_levi_frame hE' rfl e8D7Node e8D7_adj e8D7_nadj
  have hadm : StatedLieAdmissible .POmegaPlus 7 2 (n : ℕ) := ⟨Nat.prime_two, hn, by norm_num⟩
  obtain ⟨Ψ, hker, hrange, hqs, hmodel⟩ :=
    spinPlus_frame_subgroup (n := 7) hadm (by norm_num) hKn
      (U := fun k => CFSG.LieType.CurtisTits.rankOne (e8Datum K).rootGroup (e8D7Node k))
      hcomm hρ hψ
  have hqs' : CFSG.IsQuasisimple ↥Ψ.range := by
    rw [hrange]; exact hqs
  have hmodel' : LieModel (↥Ψ.range ⧸ Subgroup.center ↥Ψ.range) .POmegaPlus 7 2 (n : ℕ) := by
    rw [hrange]; exact hmodel
  have hd' : p ∣ 2 ^ (n : ℕ) + 1 := by rw [← hKn]; exact hd
  have hT : CFSG.LocalAnalysis.RankThreeUC.S15.LieOddRankChev :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20x_lieOddRankChev
      CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
  have hSCM : CFSG.Open.StatedClassicalModel
      (↥Ψ.range ⧸ Subgroup.center ↥Ψ.range) .POmegaPlus 7 2 (n : ℕ) :=
    hmodel'.statedClassicalModel (by decide)
  have hqsOpen : CFSG.Open.IsQuasisimple ↥Ψ.range :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff ↥Ψ.range).2.2.1.1 hqs'
  have hpr := CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20w_pRank_pomegaPlus
    (K := ↥Ψ.range) hT hqsOpen hSCM (r := p) hp hp2
  have heP : CFSG.LocalAnalysis.RankThreeUC.S15.eP (2 ^ (n : ℕ)) p = 2 := by
    rw [eP_two_pow]
    exact (rk2Ord_eq_two_iff hp hp2).mpr hd'
  have heS : CFSG.LocalAnalysis.RankThreeUC.S15.eS (2 ^ (n : ℕ)) p = 1 := by
    rw [CFSG.LocalAnalysis.RankThreeUC.S15.eS_eq_eP_div_gcd, heP]
    norm_num
  have h6 : CFSG.LocalAnalysis.RankThreeUC.S15.rkOmPlus 7 (2 ^ (n : ℕ)) p = 6 := by
    unfold CFSG.LocalAnalysis.RankThreeUC.S15.rkOmPlus
    rw [heP, heS]
    norm_num
  rw [h6] at hpr
  have hS : CFSG.Open.pRank p (⊤ : Subgroup Ψ.range) ≤ 6 := by rw [hpr]
  have hEmap : E ≤ Ψ.range.map (adjointGroup Tag.E8 K).subtype := by
    rw [hrange, map_subtype_iSup_rankOne e8D7Node]
    exact hE
  exact card_le_pow_of_le_map_subtype hp hS hEmap hEel

theorem e8E6_adj : ∀ i j : Fin 6, Timmesfeld.edgeE 6 i j →
    e8E6Node i ≠ e8E6Node j ∧ Tag.cartan .E8 (e8E6Node i) (e8E6Node j) = -1 ∧
      Tag.cartan .E8 (e8E6Node j) (e8E6Node i) = -1 ∧
      ∃ l, ¬ (3 : ℤ) ∣ Tag.cartan .E8 (e8E6Node i) l + 2 * Tag.cartan .E8 (e8E6Node j) l := by
  decide +kernel

theorem e8E6_nadj : ∀ i j : Fin 6, i ≠ j → ¬ Timmesfeld.edgeE 6 i j →
    ¬ Timmesfeld.edgeE 6 j i →
    e8E6Node i ≠ e8E6Node j ∧ Tag.cartan .E8 (e8E6Node i) (e8E6Node j) = 0 ∧
      Tag.cartan .E8 (e8E6Node j) (e8E6Node i) = 0 := by
  decide +kernel

theorem pRank_le_four_of_e6_model {S : Type} [Group S] [Finite S] {n p : ℕ}
    (hQs : CFSG.IsQuasisimple S)
    (hmodel : LieModel (S ⧸ Subgroup.center S) .E6 0 2 n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hd : p ∣ 2 ^ n + 1) :
    CFSG.Open.pRank p (⊤ : Subgroup S) ≤ 4 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hZ : ¬ p ∣ Nat.card (Subgroup.center S) := by
    obtain ⟨-, ⟨eM⟩⟩ := CFSG.Milestones.cl_lit_griess_schur_multipliers_all_native_models
      (S ⧸ Subgroup.center S) .E6 0 2 n hmodel
    have hg : CFSG.Blueprint.Multiplier.genericOrders .E6 0 2 n =
        (Nat.gcd 3 (2 ^ n - 1), 1) := rfl
    have he : CFSG.Blueprint.Multiplier.exceptionalOrders .E6 0 2 n = (1, 1) := rfl
    have hcard : Nat.card (CFSG.Open.griessHopfMultiplier (S ⧸ Subgroup.center S)) =
        Nat.gcd 3 (2 ^ n - 1) := by
      rw [Nat.card_congr eM.toEquiv,
        CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_generic_exceptional', hg, he]
      norm_num
    haveI : Finite (CFSG.Open.griessHopfMultiplier (S ⧸ Subgroup.center S)) :=
      Nat.finite_of_card_ne_zero
        (by rw [hcard]; exact (Nat.gcd_pos_of_pos_left _ (by norm_num)).ne')
    have hdvd := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_center_dvd_hopf hQs
      (MulEquiv.refl (S ⧸ Subgroup.center S))
    rw [hcard] at hdvd
    intro hpZ
    have h3 : p ∣ Nat.gcd 3 (2 ^ n - 1) := hpZ.trans hdvd
    have hp3 : p = 3 :=
      (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (h3.trans (Nat.gcd_dvd_left _ _))
    subst hp3
    have h1 : 3 ∣ 2 ^ n - 1 := h3.trans (Nat.gcd_dvd_right _ _)
    have h2 : 3 ∣ (2 ^ n + 1) - (2 ^ n - 1) := Nat.dvd_sub hd h1
    have h3' : (2 ^ n + 1) - (2 ^ n - 1) = 2 := by
      have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      omega
    rw [h3'] at h2
    exact (by norm_num : ¬ (3 : ℕ) ∣ 2) h2
  have hq : CFSG.Open.pRank p (⊤ : Subgroup (S ⧸ Subgroup.center S)) ≤ 4 := by
    obtain ⟨-, F', hF', hFin', hFcard', ⟨φ⟩⟩ :=
      hmodel.chevalleyExceptionalModel (by decide : StatedLieTag.E6 ∈ chevalleyExceptionalTags)
    letI : Field F' := hF'
    letI : Finite F' := hFin'
    let χ : AdjointQuotient .E6 F' ≃* adjointGroup .E6 F' :=
      (QuotientGroup.quotientMulEquivOfEq
        (center_adjointGroup_eq_bot (τ := Tag.E6) (K := F'))).trans QuotientGroup.quotientBot
    have he : CFSG.Open.pRank p (⊤ : Subgroup (S ⧸ Subgroup.center S)) =
        CFSG.Open.pRank p (⊤ : Subgroup (adjointGroup .E6 F')) :=
      CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt (φ.trans χ)
    rw [he]
    by_cases hp3 : p = 3
    · subst hp3
      have hord : rk2Ord 3 n = 2 := (rk2Ord_eq_two_iff Nat.prime_three (by norm_num)).mpr hd
      have hF2 : Nat.card F' = 2 ^ n := hFcard'
      exact rk2E6ThreeTwoFrontier F' n hF2 hord
    · have hp5 : 5 ≤ p := by
        have h2 := hp.two_le
        have h4 : p ≠ 4 := by
          rintro rfl
          exact absurd hp (by norm_num)
        omega
      have heord : orderOf ((Nat.card F' : ℕ) : ZMod p) = 2 := by
        rw [hFcard']
        have hcast : (((2 : ℕ) ^ n : ℕ) : ZMod p) = (2 : ZMod p) ^ n := by
          push_cast; ring
        rw [hcast]
        exact (rk2Ord_eq_two_iff hp hp2).mpr hd
      exact CFSG.SectionRank.pRank_le hp.one_lt fun E _ hE =>
        CFSG.LieType.SeitzGeneration.SylowTorus.rank_le
          (CFSG.StandardType.ExcFrames.sylowTorus_adjoint_E6_two F' hp (by omega) heord) hp hE
  calc CFSG.Open.pRank p (⊤ : Subgroup S)
      = CFSG.Open.pRank p (⊤ : Subgroup (S ⧸ Subgroup.center S)) :=
        (CFSG.SectionRank.pRank_quotient_eq (p := p) (G := S) (Subgroup.center S) hZ).symm
    _ ≤ 4 := hq

theorem card_le_pow_four_subsystemGroup_e8E6 {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hd : p ∣ Nat.card K + 1)
    {E : Subgroup (ModGL Tag.E8 K)}
    (hE : E ≤ subsystemGroup Tag.E8 K (Set.range e8E6Node))
    (hEel : IsElemAbelian p E) : Nat.card E ≤ p ^ 4 := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, -, hK⟩ := FiniteField.card K 2
  have hKn : Nat.card K = 2 ^ (n : ℕ) := by rw [← Fintype.card_eq_nat_card]; exact hK
  have hn : 1 ≤ (n : ℕ) := CFSG.Quasithin.R3c2.one_le_of_natCard_eq_two_pow hKn
  obtain ⟨O, C, hE'⟩ := exists_e8_chevalleyExtras K
  obtain ⟨ρ, hρ, hcomm, hψ⟩ := exists_levi_frame hE' rfl e8E6Node e8E6_adj e8E6_nadj
  have hadm : StatedLieAdmissible .E6 0 2 (n : ℕ) := ⟨Nat.prime_two, hn, rfl⟩
  obtain ⟨Ψ, hker, hrange, hqs, hmodel⟩ :=
    e6_frame_subgroup hadm hKn
      (U := fun k => CFSG.LieType.CurtisTits.rankOne (e8Datum K).rootGroup (e8E6Node k))
      hcomm hρ hψ
  have hqs' : CFSG.IsQuasisimple ↥Ψ.range := by
    rw [hrange]; exact hqs
  have hmodel' : LieModel (↥Ψ.range ⧸ Subgroup.center ↥Ψ.range) .E6 0 2 (n : ℕ) := by
    rw [hrange]; exact hmodel
  have hd' : p ∣ 2 ^ (n : ℕ) + 1 := by rw [← hKn]; exact hd
  have hS : CFSG.Open.pRank p (⊤ : Subgroup Ψ.range) ≤ 4 :=
    pRank_le_four_of_e6_model hqs' hmodel' hp hp2 hd'
  have hEmap : E ≤ Ψ.range.map (adjointGroup Tag.E8 K).subtype := by
    rw [hrange, map_subtype_iSup_rankOne e8E6Node]
    exact hE
  exact card_le_pow_of_le_map_subtype hp hS hEmap hEel

theorem card_le_pow_four_subsystemGroup_e8D5 {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hd : p ∣ Nat.card K + 1)
    {E : Subgroup (ModGL Tag.E8 K)}
    (hE : E ≤ subsystemGroup Tag.E8 K (Set.range e8D5Node))
    (hEel : IsElemAbelian p E) : Nat.card E ≤ p ^ 4 := by
  have hsub : Set.range e8D5Node ⊆ Set.range e8E6Node := by
    intro j hj
    have hj' := (mem_range_e8D5Node j).1 hj
    rw [mem_range_e8E6Node]
    rcases hj' with rfl | rfl | rfl | rfl | rfl <;> decide
  exact card_le_pow_four_subsystemGroup_e8E6 hp hp2 hd
    (hE.trans (subsystemGroup_mono hsub)) hEel

theorem pRank_le_seven_of_e7_model {S : Type} [Group S] [Finite S] {n p : ℕ}
    (hQs : CFSG.IsQuasisimple S)
    (hmodel : LieModel (S ⧸ Subgroup.center S) .E7 0 2 n)
    (hn : 1 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2) (hd : p ∣ 2 ^ n + 1) :
    CFSG.Open.pRank p (⊤ : Subgroup S) ≤ 7 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hZ : ¬ p ∣ Nat.card (Subgroup.center S) := by
    obtain ⟨-, ⟨eM⟩⟩ := CFSG.Milestones.cl_lit_griess_schur_multipliers_all_native_models
      (S ⧸ Subgroup.center S) .E7 0 2 n hmodel
    have hg : CFSG.Blueprint.Multiplier.genericOrders .E7 0 2 n =
        (Nat.gcd 2 (2 ^ n - 1), 1) := rfl
    have he : CFSG.Blueprint.Multiplier.exceptionalOrders .E7 0 2 n = (1, 1) := rfl
    have hodd : Odd (2 ^ n - 1) :=
      CFSG.Timmesfeld.Orders.odd_two_pow_sub_one (a := n) (by omega)
    have hgcd : Nat.gcd 2 (2 ^ n - 1) = 1 :=
      (Nat.coprime_two_left.mpr hodd).gcd_eq_one
    have hcard : Nat.card (CFSG.Open.griessHopfMultiplier (S ⧸ Subgroup.center S)) = 1 := by
      rw [Nat.card_congr eM.toEquiv,
        CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_generic_exceptional', hg, he, hgcd]
      norm_num
    haveI : Finite (CFSG.Open.griessHopfMultiplier (S ⧸ Subgroup.center S)) :=
      Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
    have hdvd := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_center_dvd_hopf hQs
      (MulEquiv.refl (S ⧸ Subgroup.center S))
    rw [hcard] at hdvd
    intro hpZ
    exact hp.ne_one (Nat.dvd_one.mp (hpZ.trans hdvd))
  have hq : CFSG.Open.pRank p (⊤ : Subgroup (S ⧸ Subgroup.center S)) ≤ 7 := by
    obtain ⟨-, F', hF', hFin', hFcard', ⟨φ⟩⟩ :=
      hmodel.chevalleyExceptionalModel (by decide : StatedLieTag.E7 ∈ chevalleyExceptionalTags)
    letI : Field F' := hF'
    letI : Finite F' := hFin'
    haveI : CharP F' 2 :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
        Nat.prime_two (by omega) hFcard'
    let χ : AdjointQuotient .E7 F' ≃* adjointGroup .E7 F' :=
      (QuotientGroup.quotientMulEquivOfEq
        (center_adjointGroup_eq_bot (τ := Tag.E7) (K := F'))).trans QuotientGroup.quotientBot
    have he : CFSG.Open.pRank p (⊤ : Subgroup (S ⧸ Subgroup.center S)) =
        CFSG.Open.pRank p (⊤ : Subgroup (adjointGroup .E7 F')) :=
      CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt (φ.trans χ)
    rw [he]
    have hpq' : p ∣ Nat.card F' + 1 := by rw [hFcard']; exact hd
    exact pRank_adjointGroup_E7_le_seven_of_dvd_add_one F' n hFcard' hn hp hp2 hpq'
  calc CFSG.Open.pRank p (⊤ : Subgroup S)
      = CFSG.Open.pRank p (⊤ : Subgroup (S ⧸ Subgroup.center S)) :=
        (CFSG.SectionRank.pRank_quotient_eq (p := p) (G := S) (Subgroup.center S) hZ).symm
    _ ≤ 7 := hq

theorem card_le_pow_seven_subsystemGroup_e8E7 {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hd : p ∣ Nat.card K + 1)
    {E : Subgroup (ModGL Tag.E8 K)}
    (hE : E ≤ subsystemGroup Tag.E8 K e8LeviE7)
    (hEel : IsElemAbelian p E) : Nat.card E ≤ p ^ 7 := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, -, hK⟩ := FiniteField.card K 2
  have hKn : Nat.card K = 2 ^ (n : ℕ) := by rw [← Fintype.card_eq_nat_card]; exact hK
  have hn : 1 ≤ (n : ℕ) := CFSG.Quasithin.R3c2.one_le_of_natCard_eq_two_pow hKn
  have hadm : StatedLieAdmissible .E7 0 2 (n : ℕ) := ⟨Nat.prime_two, hn, rfl⟩
  obtain ⟨Ψ, hker, hrange, hqs, hmodel⟩ :=
    exists_psi_E7_E8 (p := 2) (f := (n : ℕ)) hadm hKn
  have hqs' : CFSG.IsQuasisimple ↥Ψ.range := by
    rw [hrange]; exact hqs
  have hmodel' : LieModel (↥Ψ.range ⧸ Subgroup.center ↥Ψ.range) .E7 0 2 (n : ℕ) := by
    rw [hrange]; exact hmodel
  have hd' : p ∣ 2 ^ (n : ℕ) + 1 := by rw [← hKn]; exact hd
  have hS : CFSG.Open.pRank p (⊤ : Subgroup Ψ.range) ≤ 7 :=
    pRank_le_seven_of_e7_model hqs' hmodel' hn hp hp2 hd'
  have hEmap : E ≤ Ψ.range.map (adjointGroup Tag.E8 K).subtype := by
    rw [hrange, map_subtype_iSup_rankOne e8E7Node]
    exact hE
  exact card_le_pow_of_le_map_subtype hp hS hEmap hEel

theorem card_le_pow_seven_subsystemGroup_e8delete0 {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hd : p ∣ Nat.card K + 1)
    {E : Subgroup (ModGL Tag.E8 K)}
    (hE : E ≤ subsystemGroup Tag.E8 K {j : Fin Tag.E8.rank | j ≠ 0})
    (hEel : IsElemAbelian p E) : Nat.card E ≤ p ^ 7 := by
  have hsub : ({j : Fin Tag.E8.rank | j ≠ 0} : Set _) ⊆ Set.range e8D7Node := by
    intro j hj
    exact (mem_range_e8D7Node j).2 hj
  calc Nat.card E ≤ p ^ 6 :=
        card_le_pow_six_subsystemGroup_e8D7 hp hp2 hd (hE.trans (subsystemGroup_mono hsub)) hEel
    _ ≤ p ^ 7 := Nat.pow_le_pow_right hp.pos (by norm_num)

theorem card_le_pow_seven_subsystemGroup_e8delete1 {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hd : p ∣ Nat.card K + 1)
    {E : Subgroup (ModGL Tag.E8 K)}
    (hE : E ≤ subsystemGroup Tag.E8 K {j : Fin Tag.E8.rank | j ≠ 1})
    (hEel : IsElemAbelian p E) : Nat.card E ≤ p ^ 7 := by
  have hpq : ¬ p ∣ Nat.card K - 1 :=
    CFSG.RankThree.PartOne.S15K.not_dvd_sub_one_of_dvd_add_one Nat.card_pos
      (by have := hp.two_le; omega) hd
  have hsub : ({j : Fin Tag.E8.rank | j ≠ 1} : Set _) ⊆ Set.range e8A7Node := by
    intro j hj
    exact (mem_range_e8A7Node j).2 hj
  calc Nat.card E ≤ p ^ 4 :=
        card_le_pow_four_subsystemGroup_e8A7 hp hp2 hpq
          (hE.trans (subsystemGroup_mono hsub)) hEel
    _ ≤ p ^ 7 := Nat.pow_le_pow_right hp.pos (by norm_num)

theorem card_le_pow_seven_subsystemGroup_e8delete2 {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hd : p ∣ Nat.card K + 1)
    {E : Subgroup (ModGL Tag.E8 K)}
    (hE : E ≤ subsystemGroup Tag.E8 K {j : Fin Tag.E8.rank | j ≠ 2})
    (hEel : IsElemAbelian p E) : Nat.card E ≤ p ^ 7 := by
  have hpq : ¬ p ∣ Nat.card K - 1 :=
    CFSG.RankThree.PartOne.S15K.not_dvd_sub_one_of_dvd_add_one Nat.card_pos
      (by have := hp.two_le; omega) hd
  have hsub : ({j : Fin Tag.E8.rank | j ≠ 2} : Set _) ⊆
      ({0} : Set (Fin Tag.E8.rank)) ∪ Set.range e8A6Node := by
    intro j hj
    fin_cases j <;> first | exact absurd rfl hj | decide
  have hE' : E ≤ subsystemGroup Tag.E8 K (({0} : Set (Fin Tag.E8.rank)) ∪ Set.range e8A6Node) :=
    hE.trans (subsystemGroup_mono hsub)
  rw [subsystemGroup_union] at hE'
  have hcomm := commute_subsystemGroup_of_cartan_zero (K := K)
    (A := ({0} : Set (Fin Tag.E8.rank))) (B := Set.range e8A6Node) (by
      intro a ha b hb
      have ha0 : a = 0 := by simpa using ha
      subst ha0
      have hb' : b = 1 ∨ b = 3 ∨ b = 4 ∨ b = 5 ∨ b = 6 ∨ b = 7 := by
        have h1 := (mem_range_e8A6Node b).1 hb
        fin_cases b <;> first | exact absurd rfl h1.1 | exact absurd rfl h1.2 | decide
      rcases hb' with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  have hboundA : ∀ F : Subgroup (subsystemGroup Tag.E8 K ({0} : Set (Fin Tag.E8.rank))),
      IsElemAbelian p F → Nat.card F ≤ p ^ 1 :=
    bound_subgroup_of_ambient (fun F hF hFel =>
      card_le_pow_one_subsystemGroup_e8node hp hp2 hpq 0 hF hFel)
  have hboundB : ∀ F : Subgroup (subsystemGroup Tag.E8 K (Set.range e8A6Node)),
      IsElemAbelian p F → Nat.card F ≤ p ^ 3 :=
    bound_subgroup_of_ambient (fun F hF hFel =>
      card_le_pow_three_subsystemGroup_e8A6 hp hp2 hpq hF hFel)
  have h := card_le_pow_add_of_le_sup_of_not_dvd_inf (p := p) hp hcomm
    (not_dvd_card_inf_subsystemGroup_e8 hp hpq hcomm) hboundA hboundB hE' hEel
  exact h.trans (Nat.pow_le_pow_right hp.pos (by norm_num))

theorem card_le_pow_seven_subsystemGroup_e8delete3 {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hd : p ∣ Nat.card K + 1)
    {E : Subgroup (ModGL Tag.E8 K)}
    (hE : E ≤ subsystemGroup Tag.E8 K {j : Fin Tag.E8.rank | j ≠ 3})
    (hEel : IsElemAbelian p E) : Nat.card E ≤ p ^ 7 := by
  have hpq : ¬ p ∣ Nat.card K - 1 :=
    CFSG.RankThree.PartOne.S15K.not_dvd_sub_one_of_dvd_add_one Nat.card_pos
      (by have := hp.two_le; omega) hd
  have hsub : ({j : Fin Tag.E8.rank | j ≠ 3} : Set _) ⊆
      ({1} : Set (Fin Tag.E8.rank)) ∪ (({0, 2} : Set (Fin Tag.E8.rank)) ∪ Set.range e8A4Node) := by
    intro j hj
    fin_cases j <;> first | exact absurd rfl hj | decide
  have hE' : E ≤ subsystemGroup Tag.E8 K
      (({1} : Set (Fin Tag.E8.rank)) ∪ (({0, 2} : Set (Fin Tag.E8.rank)) ∪ Set.range e8A4Node)) :=
    hE.trans (subsystemGroup_mono hsub)
  rw [subsystemGroup_union] at hE'
  have hcomm₁ := commute_subsystemGroup_of_cartan_zero (K := K)
    (A := ({1} : Set (Fin Tag.E8.rank)))
    (B := (({0, 2} : Set (Fin Tag.E8.rank)) ∪ Set.range e8A4Node)) (by
      intro a ha b hb
      have ha1 : a = 1 := by simpa using ha
      subst ha1
      rcases hb with hb | hb
      · rcases (by simpa using hb : b = 0 ∨ b = 2) with rfl | rfl <;> decide
      · have hb' := (mem_range_e8A4Node b).1 hb
        rcases hb' with rfl | rfl | rfl | rfl <;> decide)
  have hcomm₂ := commute_subsystemGroup_of_cartan_zero (K := K)
    (A := ({0, 2} : Set (Fin Tag.E8.rank))) (B := Set.range e8A4Node) (by
      intro a ha b hb
      have ha' : a = 0 ∨ a = 2 := by simpa using ha
      have hb' := (mem_range_e8A4Node b).1 hb
      rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl | rfl | rfl <;> decide)
  have hboundA : ∀ F : Subgroup (subsystemGroup Tag.E8 K ({1} : Set (Fin Tag.E8.rank))),
      IsElemAbelian p F → Nat.card F ≤ p ^ 1 :=
    bound_subgroup_of_ambient (fun F hF hFel =>
      card_le_pow_one_subsystemGroup_e8node hp hp2 hpq 1 hF hFel)
  have hboundB : ∀ F : Subgroup (subsystemGroup Tag.E8 K
      (({0, 2} : Set (Fin Tag.E8.rank)) ∪ Set.range e8A4Node)),
      IsElemAbelian p F → Nat.card F ≤ p ^ (1 + 2) :=
    bound_subgroup_of_ambient (fun E hE hEel => by
      have hE' : E ≤ subsystemGroup Tag.E8 K ({0, 2} : Set (Fin Tag.E8.rank)) ⊔
          subsystemGroup Tag.E8 K (Set.range e8A4Node) := by
        rw [← subsystemGroup_union]
        exact hE
      exact card_le_pow_add_of_le_sup_of_not_dvd_inf (p := p) hp hcomm₂
        (not_dvd_card_inf_subsystemGroup_e8 hp hpq hcomm₂)
        (bound_subgroup_of_ambient (fun G hG hGel =>
          card_le_pow_one_subsystemGroup_e8A2 (i := 0) (j := 2) hp hp2 hpq
            (by decide) (by decide) (by decide) ⟨3, by decide⟩ hG hGel))
        (bound_subgroup_of_ambient (fun G hG hGel =>
          card_le_pow_two_subsystemGroup_e8A4 hp hp2 hpq hG hGel)) hE' hEel)
  have h := card_le_pow_add_of_le_sup_of_not_dvd_inf (p := p) hp hcomm₁
    (not_dvd_card_inf_subsystemGroup_e8 hp hpq hcomm₁) hboundA hboundB hE' hEel
  exact h.trans (Nat.pow_le_pow_right hp.pos (by norm_num))

theorem card_le_pow_seven_subsystemGroup_e8delete4 {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hd : p ∣ Nat.card K + 1)
    {E : Subgroup (ModGL Tag.E8 K)}
    (hE : E ≤ subsystemGroup Tag.E8 K {j : Fin Tag.E8.rank | j ≠ 4})
    (hEel : IsElemAbelian p E) : Nat.card E ≤ p ^ 7 := by
  have hpq : ¬ p ∣ Nat.card K - 1 :=
    CFSG.RankThree.PartOne.S15K.not_dvd_sub_one_of_dvd_add_one Nat.card_pos
      (by have := hp.two_le; omega) hd
  have hsub : ({j : Fin Tag.E8.rank | j ≠ 4} : Set _) ⊆
      Set.range e8A4Node' ∪ Set.range e8A3Node := by
    intro j hj
    fin_cases j <;> first | exact absurd rfl hj | decide
  have hE' : E ≤ subsystemGroup Tag.E8 K (Set.range e8A4Node' ∪ Set.range e8A3Node) :=
    hE.trans (subsystemGroup_mono hsub)
  rw [subsystemGroup_union] at hE'
  have hcomm := commute_subsystemGroup_of_cartan_zero (K := K)
    (A := Set.range e8A4Node') (B := Set.range e8A3Node) (by
      intro a ha b hb
      have ha' := (mem_range_e8A4Node' a).1 ha
      have hb' := (mem_range_e8A3Node b).1 hb
      rcases ha' with rfl | rfl | rfl | rfl <;>
        rcases hb' with rfl | rfl | rfl <;> decide)
  have hboundA : ∀ F : Subgroup (subsystemGroup Tag.E8 K (Set.range e8A4Node')),
      IsElemAbelian p F → Nat.card F ≤ p ^ 2 :=
    bound_subgroup_of_ambient (fun F hF hFel =>
      card_le_pow_two_subsystemGroup_e8A4' hp hp2 hpq hF hFel)
  have hboundB : ∀ F : Subgroup (subsystemGroup Tag.E8 K (Set.range e8A3Node)),
      IsElemAbelian p F → Nat.card F ≤ p ^ 2 :=
    bound_subgroup_of_ambient (fun F hF hFel =>
      card_le_pow_two_subsystemGroup_e8A3 hp hp2 hpq hF hFel)
  have h := card_le_pow_add_of_le_sup_of_not_dvd_inf (p := p) hp hcomm
    (not_dvd_card_inf_subsystemGroup_e8 hp hpq hcomm) hboundA hboundB hE' hEel
  exact h.trans (Nat.pow_le_pow_right hp.pos (by norm_num))

theorem card_le_pow_seven_subsystemGroup_e8delete5 {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hd : p ∣ Nat.card K + 1)
    {E : Subgroup (ModGL Tag.E8 K)}
    (hE : E ≤ subsystemGroup Tag.E8 K {j : Fin Tag.E8.rank | j ≠ 5})
    (hEel : IsElemAbelian p E) : Nat.card E ≤ p ^ 7 := by
  have hpq : ¬ p ∣ Nat.card K - 1 :=
    CFSG.RankThree.PartOne.S15K.not_dvd_sub_one_of_dvd_add_one Nat.card_pos
      (by have := hp.two_le; omega) hd
  have hsub : ({j : Fin Tag.E8.rank | j ≠ 5} : Set _) ⊆
      Set.range e8D5Node ∪ Set.range e8A2Node := by
    intro j hj
    fin_cases j <;> first | exact absurd rfl hj | decide
  have hE' : E ≤ subsystemGroup Tag.E8 K (Set.range e8D5Node ∪ Set.range e8A2Node) :=
    hE.trans (subsystemGroup_mono hsub)
  rw [subsystemGroup_union] at hE'
  have hcomm := commute_subsystemGroup_of_cartan_zero (K := K)
    (A := Set.range e8D5Node) (B := Set.range e8A2Node) (by
      intro a ha b hb
      have ha' := (mem_range_e8D5Node a).1 ha
      have hb' := (mem_range_e8A2Node b).1 hb
      rcases ha' with rfl | rfl | rfl | rfl | rfl <;>
        rcases hb' with rfl | rfl <;> decide)
  have hboundA : ∀ F : Subgroup (subsystemGroup Tag.E8 K (Set.range e8D5Node)),
      IsElemAbelian p F → Nat.card F ≤ p ^ 4 :=
    bound_subgroup_of_ambient (fun F hF hFel =>
      card_le_pow_four_subsystemGroup_e8D5 hp hp2 hd hF hFel)
  have hboundB : ∀ F : Subgroup (subsystemGroup Tag.E8 K (Set.range e8A2Node)),
      IsElemAbelian p F → Nat.card F ≤ p ^ 1 :=
    bound_subgroup_of_ambient (fun E hE hEel => by
      have hE' : E ≤ subsystemGroup Tag.E8 K ({6, 7} : Set (Fin Tag.E8.rank)) := by
        rw [← e8A2Node_range]
        exact hE
      exact card_le_pow_one_subsystemGroup_e8A2 (i := 6) (j := 7) hp hp2 hpq
        (by decide) (by decide) (by decide) ⟨5, by decide⟩ hE' hEel)
  have h := card_le_pow_add_of_le_sup_of_not_dvd_inf (p := p) hp hcomm
    (not_dvd_card_inf_subsystemGroup_e8 hp hpq hcomm) hboundA hboundB hE' hEel
  exact h.trans (Nat.pow_le_pow_right hp.pos (by norm_num))

theorem card_le_pow_seven_subsystemGroup_e8delete6 {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hd : p ∣ Nat.card K + 1)
    {E : Subgroup (ModGL Tag.E8 K)}
    (hE : E ≤ subsystemGroup Tag.E8 K {j : Fin Tag.E8.rank | j ≠ 6})
    (hEel : IsElemAbelian p E) : Nat.card E ≤ p ^ 7 := by
  have hpq : ¬ p ∣ Nat.card K - 1 :=
    CFSG.RankThree.PartOne.S15K.not_dvd_sub_one_of_dvd_add_one Nat.card_pos
      (by have := hp.two_le; omega) hd
  have hsub : ({j : Fin Tag.E8.rank | j ≠ 6} : Set _) ⊆
      Set.range e8E6Node ∪ ({7} : Set (Fin Tag.E8.rank)) := by
    intro j hj
    fin_cases j <;> first | exact absurd rfl hj | decide
  have hE' : E ≤ subsystemGroup Tag.E8 K (Set.range e8E6Node ∪ ({7} : Set (Fin Tag.E8.rank))) :=
    hE.trans (subsystemGroup_mono hsub)
  rw [subsystemGroup_union] at hE'
  have hcomm := commute_subsystemGroup_of_cartan_zero (K := K)
    (A := Set.range e8E6Node) (B := ({7} : Set (Fin Tag.E8.rank))) (by
      intro a ha b hb
      have ha' := (mem_range_e8E6Node a).1 ha
      have hb7 : b = 7 := by simpa using hb
      subst hb7
      rcases ha' with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  have hboundA : ∀ F : Subgroup (subsystemGroup Tag.E8 K (Set.range e8E6Node)),
      IsElemAbelian p F → Nat.card F ≤ p ^ 4 :=
    bound_subgroup_of_ambient (fun F hF hFel =>
      card_le_pow_four_subsystemGroup_e8E6 hp hp2 hd hF hFel)
  have hboundB : ∀ F : Subgroup (subsystemGroup Tag.E8 K ({7} : Set (Fin Tag.E8.rank))),
      IsElemAbelian p F → Nat.card F ≤ p ^ 1 :=
    bound_subgroup_of_ambient (fun F hF hFel =>
      card_le_pow_one_subsystemGroup_e8node hp hp2 hpq 7 hF hFel)
  have h := card_le_pow_add_of_le_sup_of_not_dvd_inf (p := p) hp hcomm
    (not_dvd_card_inf_subsystemGroup_e8 hp hpq hcomm) hboundA hboundB hE' hEel
  exact h.trans (Nat.pow_le_pow_right hp.pos (by norm_num))

theorem card_le_pow_seven_subsystemGroup_e8delete7 {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hd : p ∣ Nat.card K + 1)
    {E : Subgroup (ModGL Tag.E8 K)}
    (hE : E ≤ subsystemGroup Tag.E8 K {j : Fin Tag.E8.rank | j ≠ 7})
    (hEel : IsElemAbelian p E) : Nat.card E ≤ p ^ 7 := by
  have hsub : ({j : Fin Tag.E8.rank | j ≠ 7} : Set _) ⊆ e8LeviE7 := by
    intro j hj
    exact (mem_range_e8E7Node j).2 hj
  exact card_le_pow_seven_subsystemGroup_e8E7 hp hp2 hd
    (hE.trans (subsystemGroup_mono hsub)) hEel

theorem levi_card_le_seven_explicit {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hd : p ∣ Nat.card K + 1)
    {J : Set (Fin Tag.E8.rank)} (hJ : J ≠ Set.univ)
    {E : Subgroup (ModGL Tag.E8 K)} (hE : E ≤ subsystemGroup Tag.E8 K J)
    (hEel : IsElemAbelian p E) : Nat.card E ≤ p ^ 7 := by
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨i, hi⟩ : ∃ i, i ∉ J := by
    by_contra hall
    push Not at hall
    exact hJ (Set.eq_univ_of_forall hall)
  have hJle : J ⊆ {j : Fin Tag.E8.rank | j ≠ i} := by
    intro j hj hji
    exact hi (hji ▸ hj)
  have hE' : E ≤ subsystemGroup Tag.E8 K {j : Fin Tag.E8.rank | j ≠ i} :=
    hE.trans (subsystemGroup_mono hJle)
  fin_cases i
  · exact card_le_pow_seven_subsystemGroup_e8delete0 hp hp2 hd hE' hEel
  · exact card_le_pow_seven_subsystemGroup_e8delete1 hp hp2 hd hE' hEel
  · exact card_le_pow_seven_subsystemGroup_e8delete2 hp hp2 hd hE' hEel
  · exact card_le_pow_seven_subsystemGroup_e8delete3 hp hp2 hd hE' hEel
  · exact card_le_pow_seven_subsystemGroup_e8delete4 hp hp2 hd hE' hEel
  · exact card_le_pow_seven_subsystemGroup_e8delete5 hp hp2 hd hE' hEel
  · exact card_le_pow_seven_subsystemGroup_e8delete6 hp hp2 hd hE' hEel
  · exact card_le_pow_seven_subsystemGroup_e8delete7 hp hp2 hd hE' hEel

theorem rk2E8LeviRankInput_holds (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    Rk2E8LeviRankInput p := by
  change ∀ (F : Type) [Field F] [Finite F] [CharP F 2], p ∣ Nat.card F + 1 →
    ∀ (i : Fin Tag.E8.rank), ∀ E : Subgroup (ModGL Tag.E8 F),
      E ≤ subsystemGroup Tag.E8 F {j | j ≠ i} → IsElemAbelian p E → Nat.card E ≤ p ^ 7
  intro F hF hFin hCh hd i E hE hEel
  letI : Field F := hF
  letI : Finite F := hFin
  haveI : CharP F 2 := hCh
  refine levi_card_le_seven_explicit hp hp2 hd ?_ hE hEel
  intro h
  have hi : i ∈ ({j : Fin Tag.E8.rank | j ≠ i} : Set _) := by
    rw [h]
    exact Set.mem_univ i
  exact hi rfl

end CFSG.LocalAnalysis.GLTheoremA
