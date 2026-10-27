module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixToNineStmt
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.BarBlocks
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.BlockRankLower
import CFSG.LocalAnalysis.AGLEmbedding.LemmaBGlue
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveFourJComp
import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bOrbit
import CFSG.GroupTheory.ConjTransport
import CFSG.GroupTheory.PRankCommutingSup
import CFSG.GroupTheory.PGroup.PrimePartTransport
import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporAut168

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup CFSG.AGLEmbedding
open scoped commutatorElement
open CFSG.LocalAnalysis.RankThreeUC.AGL81C

variable {G : Type} [Group G] [Finite G]
variable {M H : Subgroup G} {d : ℕ} {L₁ L₂ L₃ : Subgroup G} {n₁ n₂ n₃ : ℕ}

namespace TwelveFiveData

private noncomputable def conjActionHom {B : Type} [Group B] {L X : Subgroup B}
    (hX : X ≤ Subgroup.normalizer (L : Set B)) : X →* MulAut ↥L :=
  (Subgroup.normalizerMonoidHom (H := L)).comp (Subgroup.inclusion hX)

private theorem conjActionHom_ker {B : Type} [Group B] {L X : Subgroup B}
    (hX : X ≤ Subgroup.normalizer (L : Set B)) :
    (conjActionHom hX).ker = (X ⊓ Subgroup.centralizer (L : Set B)).subgroupOf X := by
  rw [conjActionHom, ← MonoidHom.comap_ker, Subgroup.normalizerMonoidHom_ker]
  ext x
  simp [Subgroup.mem_subgroupOf]

private theorem card_range_conjAction_le_three {B : Type} [Group B] [Finite B]
    {L X : Subgroup B} (hX : IsPGroup 3 X) (hXN : X ≤ Subgroup.normalizer (L : Set B))
    (h9 : ¬ 3 ^ 2 ∣ Nat.card (MulAut ↥L)) :
    Nat.card (conjActionHom hXN).range ≤ 3 := by
  let φ := conjActionHom hXN
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : IsPGroup 3 ↥X := hX
  have hφ3 : IsPGroup 3 φ.range :=
    IsPGroup.of_equiv (IsPGroup.to_quotient hX φ.ker)
      (QuotientGroup.quotientKerEquivRange φ)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hφ3
  have hdvd : Nat.card φ.range ∣ Nat.card (MulAut ↥L) := by
    simpa using Subgroup.card_dvd_of_le (le_top : φ.range ≤ ⊤)
  have hk1 : k ≤ 1 := by
    by_contra h
    have hk2 : 2 ≤ k := by omega
    have h9dvd : 3 ^ 2 ∣ Nat.card φ.range := by
      rw [hk]
      exact pow_dvd_pow 3 hk2
    exact h9 (h9dvd.trans hdvd)
  calc Nat.card φ.range = 3 ^ k := hk
    _ ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
    _ = 3 := by norm_num

private theorem card_le_three_mul_card_inf_centralizer {B : Type} [Group B] [Finite B]
    {L X : Subgroup B} (hX : IsPGroup 3 X) (hXN : X ≤ Subgroup.normalizer (L : Set B))
    (h9 : ¬ 3 ^ 2 ∣ Nat.card (MulAut ↥L)) :
    Nat.card X ≤ 3 * Nat.card ↥(X ⊓ Subgroup.centralizer (L : Set B)) := by
  let φ := conjActionHom hXN
  have hφle := card_range_conjAction_le_three hX hXN h9
  have hker := conjActionHom_ker hXN
  have hcard := Subgroup.card_ker_mul_card_range φ
  have hkercard : Nat.card ↥φ.ker =
      Nat.card ↥(X ⊓ Subgroup.centralizer (L : Set B)) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [hkercard] at hcard
  calc Nat.card X = Nat.card ↥(X ⊓ Subgroup.centralizer (L : Set B)) *
        Nat.card φ.range := hcard.symm
    _ ≤ Nat.card ↥(X ⊓ Subgroup.centralizer (L : Set B)) * 3 :=
        Nat.mul_le_mul_left _ hφle
    _ = 3 * Nat.card ↥(X ⊓ Subgroup.centralizer (L : Set B)) := by ring

private theorem card_barM_eq_168 {M A : Subgroup G} (hA : IsTwoPrimeComponent M A)
    (hA3 : IsL3TwoPow 1 (↥A ⧸ pCore 2 ↥A)) :
    Nat.card ↥(barM M A) = 168 := by
  obtain ⟨e⟩ := CFSG.RankThree.PartTwo.Sec19.Item194Proof.nonempty_barM_mulEquiv
    hA.le hA.inf_twoCore
  have hQ : Nat.card (↥A ⧸ pCore 2 ↥A) = 168 := by
    have h := CFSG.LocalAnalysis.AGL81TheoremCD.Section12.card_of_isL3TwoPow_of_odd
      (by decide : Odd 1) hA3
    simpa using h
  rw [← Nat.card_congr e.toEquiv, hQ]

private theorem not_sq_three_dvd_card_mulAut_barM {M A : Subgroup G}
    (hA : IsTwoPrimeComponent M A) {n : ℕ} (hn : n = 1)
    (hL3 : IsL3TwoPow n (↥A ⧸ pCore 2 ↥A)) :
    ¬ 3 ^ 2 ∣ Nat.card (MulAut ↥(barM M A)) := by
  subst hn
  have hcard := card_barM_eq_168 hA hL3
  haveI hQsimple : IsSimpleGroup (↥A ⧸ pCore 2 ↥A) := hL3.isSimpleGroup
  haveI : IsSimpleGroup ↥(barM M A) := by
    obtain ⟨e⟩ := CFSG.RankThree.PartTwo.Sec19.Item194Proof.nonempty_barM_mulEquiv
      hA.le hA.inf_twoCore
    exact e.symm.isSimpleGroup
  haveI : Group.IsPerfect ↥(barM M A) := ⟨hA.component.2.2.1⟩
  have hnab : ∃ a b : ↥(barM M A), a * b ≠ b * a := by
    simpa only [isMulCommutative_iff, not_forall] using
      Group.IsPerfect.not_isMulCommutative (G := ↥(barM M A))
  exact CFSG.LocalAnalysis.GLTheoremA.I1416Rows.not_sq_three_dvd_card_mulAut_of_card_168
    hnab hcard

private theorem barM_ne_of_ne {M H A B : Subgroup G}
    (hA : A ∈ weakBlockSet M H) (hB : B ∈ weakBlockSet M H) (hAB : A ≠ B) :
    barM M A ≠ barM M B :=
  fun he => hAB (hA.toIsTwoPrimeComponent.eq_of_barM_eq hB.toIsTwoPrimeComponent he)


private theorem three_le_pRank_of_three_components {B : Type} [Group B] [Finite B]
    {A₁ A₂ A₃ : Subgroup B} (hcmp₁ : IsComponentOf A₁ ⊤) (hcmp₂ : IsComponentOf A₂ ⊤)
    (hcmp₃ : IsComponentOf A₃ ⊤) (h₁₂ : A₁ ≠ A₂) (h₁₃ : A₁ ≠ A₃) (h₂₃ : A₂ ≠ A₃)
    {y₁ y₂ y₃ : B} (hy₁ : y₁ ∈ A₁) (hy₂ : y₂ ∈ A₂) (hy₃ : y₃ ∈ A₃)
    (hq₁ : IsPGroup 3 (Subgroup.zpowers y₁)) (hq₂ : IsPGroup 3 (Subgroup.zpowers y₂))
    (hq₃ : IsPGroup 3 (Subgroup.zpowers y₃))
    (hz₁ : ∃ l ∈ A₁, y₁ * l ≠ l * y₁) (hz₂ : ∃ l ∈ A₂, y₂ * l ≠ l * y₂)
    (hz₃ : ∃ l ∈ A₃, y₃ * l ≠ l * y₃) :
    3 ≤ CFSG.Open.pRank 3 (A₁ ⊔ A₂ ⊔ A₃) := by
  classical
  let L : Fin 3 → Subgroup B := ![A₁, A₂, A₃]
  let y : Fin 3 → B := ![y₁, y₂, y₃]
  have hcomp : ∀ i, IsComponentOf (L i) ⊤ := by
    intro i
    fin_cases i <;> simp [L, hcmp₁, hcmp₂, hcmp₃]
  have hinj : Function.Injective L := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [L, h₁₂, h₁₃, h₂₃]
  have hyL : ∀ i, y i ∈ L i := by
    intro i
    fin_cases i <;> simp [L, y, hy₁, hy₂, hy₃]
  have hLA : ∀ i, L i ≤ A₁ ⊔ A₂ ⊔ A₃ := by
    intro i
    fin_cases i
    · simpa [L] using (le_sup_left.trans le_sup_left : A₁ ≤ A₁ ⊔ A₂ ⊔ A₃)
    · simpa [L] using (le_sup_right.trans le_sup_left : A₂ ≤ A₁ ⊔ A₂ ⊔ A₃)
    · simpa [L] using (le_sup_right : A₃ ≤ A₁ ⊔ A₂ ⊔ A₃)
  have hyA : ∀ i, y i ∈ A₁ ⊔ A₂ ⊔ A₃ := fun i => hLA i (hyL i)
  have hy0 : y 0 = y₁ := by simp [y]
  have hy1 : y 1 = y₂ := by simp [y]
  have hy2 : y 2 = y₃ := by simp [y]
  have hyq : ∀ i, IsPGroup 3 (Subgroup.zpowers (y i)) := by
    intro i
    fin_cases i
    · change IsPGroup 3 (Subgroup.zpowers (y 0))
      rw [hy0]; exact hq₁
    · change IsPGroup 3 (Subgroup.zpowers (y 1))
      rw [hy1]; exact hq₂
    · change IsPGroup 3 (Subgroup.zpowers (y 2))
      rw [hy2]; exact hq₃
  have hyZ : ∀ i, ∃ l ∈ L i, y i * l ≠ l * y i := by
    intro i
    fin_cases i
    · simpa [L, y] using hz₁
    · simpa [L, y] using hz₂
    · simpa [L, y] using hz₃
  have h := CFSG.AGLEmbedding.le_pRank_of_components (q := 3) Nat.prime_three L hcomp hinj
    (A₁ ⊔ A₂ ⊔ A₃) y hyA hyL hyq hyZ
  simpa using h

private theorem center_sup_sup_eq_bot_of_commute {B : Type} [Group B]
    {A₁ A₂ A₃ : Subgroup B} (hZ₁ : Subgroup.center ↥A₁ = ⊥)
    (hZ₂ : Subgroup.center ↥A₂ = ⊥) (hZ₃ : Subgroup.center ↥A₃ = ⊥)
    (hc₁₂ : ⁅A₁, A₂⁆ = ⊥) (hc₁₃ : ⁅A₁, A₃⁆ = ⊥) (hc₂₃ : ⁅A₂, A₃⁆ = ⊥) :
    Subgroup.center ↥(A₁ ⊔ A₂ ⊔ A₃) = ⊥ := by
  classical
  set F : Finset (Subgroup B) := {A₁, A₂, A₃}
  have hF : (⨆ A ∈ F, A) = A₁ ⊔ A₂ ⊔ A₃ := by
    rw [show F = insert A₁ (insert A₂ {A₃}) from rfl]
    rw [Finset.iSup_insert, Finset.iSup_insert, Finset.iSup_singleton, ← sup_assoc]
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  have hzB : (z : B) ∈ ⨆ A ∈ F, A := by rw [hF]; exact z.2
  have hzc : ∀ y ∈ (⨆ A ∈ F, A), (z : B) * y = y * (z : B) := by
    intro y hy
    have hyJ : y ∈ A₁ ⊔ A₂ ⊔ A₃ := by rwa [hF] at hy
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨y, hyJ⟩)).symm
  have hZ : ∀ A ∈ F, Subgroup.center ↥A = ⊥ := by
    intro A hA
    simp only [F, Finset.mem_insert, Finset.mem_singleton] at hA
    rcases hA with rfl | rfl | rfl <;> assumption
  have hc : ∀ A ∈ F, ∀ C ∈ F, A ≠ C → ⁅A, C⁆ = ⊥ := by
    intro A hA C hC hAC
    simp only [F, Finset.mem_insert, Finset.mem_singleton] at hA hC
    rcases hA with rfl | rfl | rfl <;> rcases hC with rfl | rfl | rfl
    all_goals first
      | exact absurd rfl hAC
      | assumption
      | (rw [Subgroup.commutator_comm]; assumption)
  have hz1 := CFSG.ComponentClassification.GSThmB.eq_one_of_mem_iSup_of_commute
    F hZ hc hzB hzc
  exact Subtype.ext hz1

private theorem card_le_twenty_seven_of_normalizer_chain {B : Type} [Group B] [Finite B]
    {A X₁ X₂ X₃ : Subgroup B} (hA : IsPGroup 3 A)
    (hN₁ : A ≤ Subgroup.normalizer (X₁ : Set B))
    (hN₂ : A ≤ Subgroup.normalizer (X₂ : Set B))
    (hN₃ : A ≤ Subgroup.normalizer (X₃ : Set B))
    (h9₁ : ¬ 3 ^ 2 ∣ Nat.card (MulAut ↥X₁))
    (h9₂ : ¬ 3 ^ 2 ∣ Nat.card (MulAut ↥X₂))
    (h9₃ : ¬ 3 ^ 2 ∣ Nat.card (MulAut ↥X₃))
    (hbot : A ⊓ Subgroup.centralizer (X₁ : Set B) ⊓ Subgroup.centralizer (X₂ : Set B) ⊓
      Subgroup.centralizer (X₃ : Set B) = ⊥) :
    Nat.card A ≤ 27 := by
  let C₁ : Subgroup B := Subgroup.centralizer (X₁ : Set B)
  let C₂ : Subgroup B := Subgroup.centralizer (X₂ : Set B)
  let C₃ : Subgroup B := Subgroup.centralizer (X₃ : Set B)
  let X1 : Subgroup B := A ⊓ C₁
  let X2 : Subgroup B := X1 ⊓ C₂
  let X3 : Subgroup B := X2 ⊓ C₃
  have hX1 : IsPGroup 3 X1 := hA.to_inf_left
  have hX2 : IsPGroup 3 X2 := hX1.to_inf_left
  have hX1N : X1 ≤ Subgroup.normalizer (X₂ : Set B) := inf_le_left.trans hN₂
  have hX2N : X2 ≤ Subgroup.normalizer (X₃ : Set B) :=
    (inf_le_left.trans inf_le_left).trans hN₃
  have h1 := card_le_three_mul_card_inf_centralizer hA hN₁ h9₁
  have h2 := card_le_three_mul_card_inf_centralizer hX1 hX1N h9₂
  have h3 := card_le_three_mul_card_inf_centralizer hX2 hX2N h9₃
  have hX3bot : X3 = ⊥ := by
    rw [show X3 = A ⊓ C₁ ⊓ C₂ ⊓ C₃ from rfl]
    exact hbot
  calc Nat.card A = Nat.card A := rfl
    _ ≤ 3 * Nat.card X1 := h1
    _ ≤ 3 * (3 * Nat.card X2) := Nat.mul_le_mul_left 3 h2
    _ ≤ 3 * (3 * (3 * Nat.card X3)) := Nat.mul_le_mul_left 3 (Nat.mul_le_mul_left 3 h3)
    _ = 27 * Nat.card X3 := by ring
    _ = 27 := by simp [hX3bot]

private theorem eq_one_of_mem_sup_sup_of_mem_centralizers {B : Type} [Group B]
    {X₁ X₂ X₃ : Subgroup B} (hZ : Subgroup.center ↥(X₁ ⊔ X₂ ⊔ X₃) = ⊥) {x : B}
    (hx : x ∈ X₁ ⊔ X₂ ⊔ X₃)
    (h₁ : x ∈ Subgroup.centralizer (X₁ : Set B))
    (h₂ : x ∈ Subgroup.centralizer (X₂ : Set B))
    (h₃ : x ∈ Subgroup.centralizer (X₃ : Set B)) : x = 1 := by
  have hcent : x ∈ Subgroup.centralizer ((X₁ ⊔ X₂ ⊔ X₃ : Subgroup B) : Set B) :=
    (CFSG.GorensteinWalter.le_centralizer_sup_of_le_centralizers
      (CFSG.GorensteinWalter.le_centralizer_sup_of_le_centralizers
        (Subgroup.zpowers_le.mpr h₁) (Subgroup.zpowers_le.mpr h₂))
      (Subgroup.zpowers_le.mpr h₃)) (Subgroup.mem_zpowers x)
  have hcenter : (X₁ ⊔ X₂ ⊔ X₃ : Subgroup B) ⊓
      Subgroup.centralizer (((X₁ ⊔ X₂ ⊔ X₃) : Subgroup B) : Set B) = ⊥ := by
    rw [← CFSG.center_map_subtype_eq_inf_centralizer (X₁ ⊔ X₂ ⊔ X₃ : Subgroup B), hZ,
      Subgroup.map_bot]
  have hxbot : x ∈ (⊥ : Subgroup B) := by
    rw [← hcenter]
    exact ⟨hx, hcent⟩
  exact Subgroup.mem_bot.mp hxbot

private theorem eq_three_of_mul_mul_eq_twenty_seven {a b c : ℕ} (ha : a ≤ 3) (hb : b ≤ 3)
    (hc : c ≤ 3) (h : a * (b * c) = 27) : a = 3 ∧ b = 3 ∧ c = 3 := by
  have ha0 : a ≠ 0 := by intro h0; rw [h0] at h; omega
  have hb0 : b ≠ 0 := by intro h0; rw [h0] at h; omega
  have hc0 : c ≠ 0 := by intro h0; rw [h0] at h; omega
  interval_cases a <;> interval_cases b <;> interval_cases c <;> simp_all

private theorem isMulCommutative_of_card_three {X : Type} [Group X] (h : Nat.card X = 3) :
    IsMulCommutative X := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : IsCyclic X := isCyclic_of_prime_card h
  exact IsMulCommutative.of_comm fun a b => (IsCyclic.commGroup (α := X)).mul_comm a b



private noncomputable def rangeActionHom {B : Type} [Group B] {L X : Subgroup B}
    (hX : X ≤ Subgroup.normalizer (L : Set B)) :
    X →* ↥(conjActionHom hX).range :=
  (conjActionHom hX).codRestrict _ fun x => MonoidHom.mem_range.mpr ⟨x, rfl⟩

private theorem ker_rangeAction_prod_eq_bot {B : Type} [Group B]
    {A X₁ X₂ X₃ : Subgroup B} (hA : A ≤ X₁ ⊔ X₂ ⊔ X₃)
    (hN₁ : A ≤ Subgroup.normalizer (X₁ : Set B))
    (hN₂ : A ≤ Subgroup.normalizer (X₂ : Set B))
    (hN₃ : A ≤ Subgroup.normalizer (X₃ : Set B))
    (hZ : Subgroup.center ↥(X₁ ⊔ X₂ ⊔ X₃) = ⊥) :
    ((rangeActionHom hN₁).prod ((rangeActionHom hN₂).prod (rangeActionHom hN₃))).ker = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  have hx₁ : conjActionHom hN₁ x = 1 := by
    have h := congrArg (fun y : ↥(conjActionHom hN₁).range ×
        (↥(conjActionHom hN₂).range × ↥(conjActionHom hN₃).range) =>
        ((y.1 : ↥(conjActionHom hN₁).range) : MulAut ↥X₁)) hx
    simpa [rangeActionHom, MonoidHom.prod_apply] using h
  have hx₂ : conjActionHom hN₂ x = 1 := by
    have h := congrArg (fun y : ↥(conjActionHom hN₁).range ×
        (↥(conjActionHom hN₂).range × ↥(conjActionHom hN₃).range) =>
        ((y.2.1 : ↥(conjActionHom hN₂).range) : MulAut ↥X₂)) hx
    simpa [rangeActionHom, MonoidHom.prod_apply] using h
  have hx₃ : conjActionHom hN₃ x = 1 := by
    have h := congrArg (fun y : ↥(conjActionHom hN₁).range ×
        (↥(conjActionHom hN₂).range × ↥(conjActionHom hN₃).range) =>
        ((y.2.2 : ↥(conjActionHom hN₃).range) : MulAut ↥X₃)) hx
    simpa [rangeActionHom, MonoidHom.prod_apply] using h
  have hc₁ : (x : B) ∈ Subgroup.centralizer (X₁ : Set B) := by
    have hxker : x ∈ (conjActionHom hN₁).ker := by rwa [MonoidHom.mem_ker]
    rw [conjActionHom_ker hN₁, Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hxker
    exact hxker.2
  have hc₂ : (x : B) ∈ Subgroup.centralizer (X₂ : Set B) := by
    have hxker : x ∈ (conjActionHom hN₂).ker := by rwa [MonoidHom.mem_ker]
    rw [conjActionHom_ker hN₂, Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hxker
    exact hxker.2
  have hc₃ : (x : B) ∈ Subgroup.centralizer (X₃ : Set B) := by
    have hxker : x ∈ (conjActionHom hN₃).ker := by rwa [MonoidHom.mem_ker]
    rw [conjActionHom_ker hN₃, Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hxker
    exact hxker.2
  exact Subtype.ext (eq_one_of_mem_sup_sup_of_mem_centralizers hZ (hA x.2) hc₁ hc₂ hc₃)

private theorem range_conjAction_card_eq_three {B : Type} [Group B] [Finite B]
    {A X₁ X₂ X₃ : Subgroup B} (hA : IsPGroup 3 A) (hAjoin : A ≤ X₁ ⊔ X₂ ⊔ X₃)
    (hN₁ : A ≤ Subgroup.normalizer (X₁ : Set B))
    (hN₂ : A ≤ Subgroup.normalizer (X₂ : Set B))
    (hN₃ : A ≤ Subgroup.normalizer (X₃ : Set B))
    (h9₁ : ¬ 3 ^ 2 ∣ Nat.card (MulAut ↥X₁))
    (h9₂ : ¬ 3 ^ 2 ∣ Nat.card (MulAut ↥X₂))
    (h9₃ : ¬ 3 ^ 2 ∣ Nat.card (MulAut ↥X₃))
    (hZ : Subgroup.center ↥(X₁ ⊔ X₂ ⊔ X₃) = ⊥) (hAcard : Nat.card A = 27) :
    Nat.card ↥(conjActionHom hN₁).range = 3 ∧
      Nat.card ↥(conjActionHom hN₂).range = 3 ∧
      Nat.card ↥(conjActionHom hN₃).range = 3 := by
  let Ψ := (rangeActionHom hN₁).prod ((rangeActionHom hN₂).prod (rangeActionHom hN₃))
  have hR₁ : Nat.card ↥(conjActionHom hN₁).range ≤ 3 :=
    card_range_conjAction_le_three hA hN₁ h9₁
  have hR₂ : Nat.card ↥(conjActionHom hN₂).range ≤ 3 :=
    card_range_conjAction_le_three hA hN₂ h9₂
  have hR₃ : Nat.card ↥(conjActionHom hN₃).range ≤ 3 :=
    card_range_conjAction_le_three hA hN₃ h9₃
  have hker : Ψ.ker = ⊥ := ker_rangeAction_prod_eq_bot hAjoin hN₁ hN₂ hN₃ hZ
  have hΨrange : Nat.card ↥Ψ.range = 27 := by
    have h := Subgroup.card_ker_mul_card_range Ψ
    rw [hker, Subgroup.card_bot, one_mul] at h
    rw [h, hAcard]
  have htarget_le : Nat.card ↥(conjActionHom hN₁).range *
      (Nat.card ↥(conjActionHom hN₂).range * Nat.card ↥(conjActionHom hN₃).range) ≤ 27 := by
    calc Nat.card ↥(conjActionHom hN₁).range *
          (Nat.card ↥(conjActionHom hN₂).range * Nat.card ↥(conjActionHom hN₃).range)
        ≤ 3 * (3 * 3) := Nat.mul_le_mul hR₁ (Nat.mul_le_mul hR₂ hR₃)
      _ = 27 := by norm_num
  have htarget_ge : 27 ≤ Nat.card ↥(conjActionHom hN₁).range *
      (Nat.card ↥(conjActionHom hN₂).range * Nat.card ↥(conjActionHom hN₃).range) := by
    rw [← hΨrange]
    simpa [Subgroup.card_top, Nat.card_prod] using
      (Subgroup.card_le_of_le (le_top : Ψ.range ≤ ⊤))
  have hprod : Nat.card ↥(conjActionHom hN₁).range *
      (Nat.card ↥(conjActionHom hN₂).range * Nat.card ↥(conjActionHom hN₃).range) = 27 :=
    le_antisymm htarget_le htarget_ge
  exact eq_three_of_mul_mul_eq_twenty_seven hR₁ hR₂ hR₃ hprod

private theorem ncard_pair_le_two {α : Type*} (a b : α) :
    ({a, b} : Set α).ncard ≤ 2 :=
  (Set.ncard_insert_le a {b}).trans (by rw [Set.ncard_singleton])

private theorem relIndex_inf_normalizer_le_three {U L₁ L₂ L₃ : Subgroup G}
    (hperm : ∀ u : ↥U, L₁.map (MulAut.conj (u : G)).toMonoidHom ∈
      ({L₁, L₂, L₃} : Set (Subgroup G))) :
    (U ⊓ Subgroup.normalizer (L₁ : Set G)).relIndex U ≤ 3 := by
  letI : MulAction (MulAut G) (Subgroup G) := Subgroup.pointwiseMulAction
  letI : MulAction ↥U (Subgroup G) :=
    MulAction.compHom (Subgroup G) ((MulAut.conj : G →* MulAut G).comp U.subtype)
  have hsmul : ∀ (u : ↥U) (P : Subgroup G),
      u • P = P.map (MulAut.conj (u : G)).toMonoidHom := by
    intro u P
    rw [MulAction.compHom_smul_def]
    change MulAut.conj (u : G) • P = P.map (MulAut.conj (u : G)).toMonoidHom
    ext x
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
      MulAut.conj_inv_apply, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  have horbit : MulAction.orbit ↥U L₁ ⊆ ({L₁, L₂, L₃} : Set (Subgroup G)) := by
    rintro P ⟨u, rfl⟩
    change u • L₁ ∈ ({L₁, L₂, L₃} : Set (Subgroup G))
    rw [hsmul u L₁]
    exact hperm u
  have hstab : MulAction.stabilizer ↥U L₁ =
      (U ⊓ Subgroup.normalizer (L₁ : Set G)).subgroupOf U := by
    ext u
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro hu
      refine ⟨u.2, ?_⟩
      rw [hsmul u L₁] at hu
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hu
    · rintro ⟨-, hu⟩
      rw [hsmul u L₁]
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hu
  have hcardOrbit : (MulAction.orbit ↥U L₁).ncard ≤ 3 := by
    refine (Set.ncard_le_ncard horbit).trans ?_
    calc ({L₁, L₂, L₃} : Set (Subgroup G)).ncard ≤
          ({L₂, L₃} : Set (Subgroup G)).ncard + 1 := Set.ncard_insert_le L₁ {L₂, L₃}
      _ ≤ ({L₃} : Set (Subgroup G)).ncard + 1 + 1 := by
          have := Set.ncard_insert_le L₂ {L₃}
          omega
      _ = 3 := by simp
  rw [Subgroup.relIndex, ← hstab, MulAction.index_stabilizer]
  exact hcardOrbit

private theorem map_conj_mem_pair_of_mem_three {U L A B : Subgroup G}
    (hperm : ∀ u : ↥U, L.map (MulAut.conj (u : G)).toMonoidHom = A ∨
      L.map (MulAut.conj (u : G)).toMonoidHom = L ∨
      L.map (MulAut.conj (u : G)).toMonoidHom = B)
    (hfixA : ∀ u : ↥U, A.map (MulAut.conj (u : G)).toMonoidHom = A) (hneA : L ≠ A) :
    ∀ u : ↥U, L.map (MulAut.conj (u : G)).toMonoidHom ∈ ({L, B} : Set (Subgroup G)) := by
  intro u
  rcases hperm u with h | h | h
  · exfalso
    have hfixinvA : A.map (MulAut.conj ((u : G)⁻¹)).toMonoidHom = A :=
      hfixA ⟨(u : G)⁻¹, U.inv_mem u.2⟩
    have hmapinv : (L.map (MulAut.conj (u : G)).toMonoidHom).map
        (MulAut.conj ((u : G)⁻¹)).toMonoidHom = L :=
      CFSG.GroupTheory.map_conj_map_conj_inv (u : G) L
    rw [h, hfixinvA] at hmapinv
    exact hneA hmapinv.symm
  · exact Or.inl h
  · exact Or.inr h

private theorem map_conj_eq_self_of_orbit_pair {U L B : Subgroup G}
    (hU : IsPGroup 3 U)
    (horbit : ∀ u : ↥U, L.map (MulAut.conj (u : G)).toMonoidHom ∈
      ({L, B} : Set (Subgroup G))) :
    ∀ u : ↥U, L.map (MulAut.conj (u : G)).toMonoidHom = L := by
  letI : MulAction (MulAut G) (Subgroup G) := Subgroup.pointwiseMulAction
  letI : MulAction ↥U (Subgroup G) :=
    MulAction.compHom (Subgroup G) ((MulAut.conj : G →* MulAut G).comp U.subtype)
  have hsmul : ∀ (u : ↥U) (P : Subgroup G),
      u • P = P.map (MulAut.conj (u : G)).toMonoidHom := by
    intro u P
    rw [MulAction.compHom_smul_def]
    change MulAut.conj (u : G) • P = P.map (MulAut.conj (u : G)).toMonoidHom
    ext x
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
      MulAut.conj_inv_apply, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  have hsub : MulAction.orbit ↥U L ⊆ ({L, B} : Set (Subgroup G)) := by
    rintro P ⟨u, rfl⟩
    change u • L ∈ ({L, B} : Set (Subgroup G))
    rw [hsmul u L]
    exact horbit u
  have hcard2 : (MulAction.orbit ↥U L).ncard ≤ 2 :=
    (Set.ncard_le_ncard hsub).trans (ncard_pair_le_two L B)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n, hn⟩ := IsPGroup.card_orbit hU L
  rw [Nat.card_coe_set_eq] at hn
  have hn0 : n = 0 := by
    by_contra h
    have h1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr h
    have h3n : 3 ≤ 3 ^ n := by simpa using Nat.pow_le_pow_right (by norm_num : 0 < 3) h1
    omega
  have hcard1 : (MulAction.orbit ↥U L).ncard = 1 := by rw [hn, hn0, pow_zero]
  obtain ⟨x, hx⟩ := Set.ncard_eq_one.mp hcard1
  have hxL : x = L := by
    have hLmem : L ∈ MulAction.orbit ↥U L := ⟨1, by simp⟩
    rw [hx] at hLmem
    exact (Set.mem_singleton_iff.mp hLmem).symm
  rw [hxL] at hx
  intro u
  have hmem : u • L ∈ ({L} : Set (Subgroup G)) := by
    rw [← hx]
    exact ⟨u, rfl⟩
  simpa [hsmul u L] using hmem

private theorem normalizes_of_fixed_of_perm {U L A B : Subgroup G}
    (hU : IsPGroup 3 U)
    (hperm : ∀ u : ↥U, L.map (MulAut.conj (u : G)).toMonoidHom = A ∨
      L.map (MulAut.conj (u : G)).toMonoidHom = L ∨
      L.map (MulAut.conj (u : G)).toMonoidHom = B)
    (hfixA : ∀ u : ↥U, A.map (MulAut.conj (u : G)).toMonoidHom = A) (hneA : L ≠ A) :
    U ≤ Subgroup.normalizer (L : Set G) := by
  have hfix := map_conj_eq_self_of_orbit_pair hU
    (map_conj_mem_pair_of_mem_three hperm hfixA hneA)
  intro u hu
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hfix ⟨u, hu⟩)

private theorem exists_threeElement_not_central_barM {M A : Subgroup G}
    (hA : IsTwoPrimeComponent M A)
    (hL3 : ∃ n : ℕ, Odd n ∧ IsL3TwoPow n (↥A ⧸ pCore 2 ↥A))
    (hcard : Nat.card ↥(barM M A) = 168) :
    ∃ y : ↥M ⧸ CFSG.pCore 2 ↥M, y ∈ barM M A ∧
      IsPGroup 3 (Subgroup.zpowers y) ∧
      ∃ l ∈ barM M A, y * l ≠ l * y := by
  have h3bar : 3 ∣ Nat.card ↥(barM M A) := by rw [hcard]; norm_num
  have hdvd : Nat.card ↥(barM M A) ∣ Nat.card A := by
    rw [barM]
    refine (Subgroup.card_map_dvd _ _).trans ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA.le).toEquiv]
  have h3A : 3 ∣ Nat.card A := h3bar.trans hdvd
  obtain ⟨y, hyord, l, hyl⟩ := exists_orderOf_eq_not_commute_barM
    Nat.prime_three (by norm_num) hA hL3 h3A
  refine ⟨(y : ↥M ⧸ CFSG.pCore 2 ↥M), y.2, ?_,
    (l : ↥M ⧸ CFSG.pCore 2 ↥M), l.2, ?_⟩
  · rw [isPGroup_iff_card_dvd_pow]
    refine ⟨1, ?_⟩
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hyord]
    norm_num
  · intro h
    exact hyl (Subtype.ext h)

private theorem barM_le_centralizer_of_isTwoPrimeComponent_of_ne {M A B : Subgroup G}
    (hA : IsTwoPrimeComponent M A) (hB : IsTwoPrimeComponent M B) (hne : A ≠ B) :
    barM M A ≤ Subgroup.centralizer (barM M B : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
  Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    (CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ hA.component hB.component
      fun he => hne (hA.eq_of_barM_eq hB he))

theorem le_normalizer_jSub (hd : TwelveFiveData M H d L₁ L₂ L₃ n₁ n₂ n₃) :
    M ≤ normalizer (jSub M H : Set G) := by
  have hdprime : d.Prime := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime d hd.mem_sigma.1
  haveI : Fact d.Prime := ⟨hdprime⟩
  rw [hd.j_eq]
  intro m hm
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  rw [CFSG.LocalAnalysis.RankThreeUC.AGL81C.S631.map_oPPrimeHull]
  have hMmap : M.map (MulAut.conj m).toMonoidHom = M :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hm)
  simpa using congrArg (fun X => oPPrimeHull d X) hMmap

theorem eq_of_isTwoPrimeComponent (hd : TwelveFiveData M H d L₁ L₂ L₃ n₁ n₂ n₃)
    {L : Subgroup G} (hL : CFSG.AGLEmbedding.IsTwoPrimeComponent M L) (hLJ : L ≤ jSub M H) :
    L = L₁ ∨ L = L₂ ∨ L = L₃ := by
  classical
  by_contra h
  simp only [not_or] at h
  obtain ⟨h1, h2, h3⟩ := h
  have hc1 := barM_le_centralizer_of_isTwoPrimeComponent_of_ne hL
    hd.mem₁.toIsTwoPrimeComponent h1
  have hc2 := barM_le_centralizer_of_isTwoPrimeComponent_of_ne hL
    hd.mem₂.toIsTwoPrimeComponent h2
  have hc3 := barM_le_centralizer_of_isTwoPrimeComponent_of_ne hL
    hd.mem₃.toIsTwoPrimeComponent h3
  have hcent : barM M L ≤ Subgroup.centralizer
      (((barM M L₁ ⊔ barM M L₂ ⊔ barM M L₃) :
        Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) : Set _) :=
    CFSG.GorensteinWalter.le_centralizer_sup_of_le_centralizers
      (CFSG.GorensteinWalter.le_centralizer_sup_of_le_centralizers hc1 hc2) hc3
  have hleJ : barM M L ≤ barM M (jSub M H) := CFSG.AGLEmbedding.barM_mono hLJ
  rw [barM_jSub_eq hd] at hleJ
  have hle_center : barM M L ≤ Subgroup.centralizer (barM M L : Set _) :=
    hcent.trans (Subgroup.centralizer_le hleJ)
  haveI : IsMulCommutative ↥(barM M L) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mp hle_center
  haveI : Group.IsSolvable ↥(barM M L) :=
    Group.isSolvable_of_comm fun a b => (IsMulCommutative.is_comm.comm a b)
  haveI : Group.IsPerfect ↥(barM M L) := ⟨hL.component.2.2.1⟩
  have hsub : Subsingleton ↥(barM M L) :=
    CFSG.ComponentClassification.SolvableKernelContainment.perfect_solvable_subsingleton
  haveI : IsSimpleGroup (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) :=
    hL.component.2.2.2
  haveI hnt : Nontrivial (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) :=
    hL.component.2.2.2.toNontrivial
  haveI hsubq : Subsingleton (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) :=
    inferInstance
  exact (not_subsingleton_iff_nontrivial.mpr hnt) hsubq

theorem weakBlockSet_eq (hd : TwelveFiveData M H d L₁ L₂ L₃ n₁ n₂ n₃) :
    weakBlockSet M H = {L₁, L₂, L₃} := by
  ext L
  constructor
  · intro hL
    have hLJ : L ≤ jSub M H := le_jSub hL
    rcases eq_of_isTwoPrimeComponent hd hL.toIsTwoPrimeComponent hLJ with rfl | rfl | rfl
    exacts [by simp, by simp, by simp]
  · intro hL
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hL
    rcases hL with rfl | rfl | rfl
    exacts [hd.mem₁, hd.mem₂, hd.mem₃]

private theorem pairwise_ne_aux (hd : TwelveFiveData M H d L₁ L₂ L₃ n₁ n₂ n₃)
    (hcard : (weakBlockSet M H).ncard = 3) : L₁ ≠ L₂ ∧ L₁ ≠ L₃ ∧ L₂ ≠ L₃ := by
  have hset := weakBlockSet_eq hd
  constructor
  · intro h
    have hsub : ({L₁, L₂, L₃} : Set (Subgroup G)) = ({L₂, L₃} : Set (Subgroup G)) := by
      ext x; simp [h]
    have h2 : (weakBlockSet M H).ncard ≤ 2 := by
      rw [hset, hsub]
      exact ncard_pair_le_two L₂ L₃
    omega
  constructor
  · intro h
    have hsub : ({L₁, L₂, L₃} : Set (Subgroup G)) = ({L₁, L₂} : Set (Subgroup G)) := by
      ext x; simp [h]; tauto
    have h2 : (weakBlockSet M H).ncard ≤ 2 := by
      rw [hset, hsub]
      exact ncard_pair_le_two L₁ L₂
    omega
  · intro h
    have hsub : ({L₁, L₂, L₃} : Set (Subgroup G)) = ({L₁, L₂} : Set (Subgroup G)) := by
      ext x; simp [h]
    have h2 : (weakBlockSet M H).ncard ≤ 2 := by
      rw [hset, hsub]
      exact ncard_pair_le_two L₁ L₂
    omega

private theorem three_le_pRank_barM_join (hd : TwelveFiveData M H d L₁ L₂ L₃ n₁ n₂ n₃)
    (hn : n₁ = 1 ∧ n₂ = 1 ∧ n₃ = 1) (hcard : (weakBlockSet M H).ncard = 3) :
    3 ≤ CFSG.Open.pRank 3 (barM M L₁ ⊔ barM M L₂ ⊔ barM M L₃) := by
  have hne := pairwise_ne_aux hd hcard
  have hb12 : barM M L₁ ≠ barM M L₂ := barM_ne_of_ne hd.mem₁ hd.mem₂ hne.1
  have hb13 : barM M L₁ ≠ barM M L₃ := barM_ne_of_ne hd.mem₁ hd.mem₃ hne.2.1
  have hb23 : barM M L₂ ≠ barM M L₃ := barM_ne_of_ne hd.mem₂ hd.mem₃ hne.2.2
  have hcard₁ : Nat.card ↥(barM M L₁) = 168 :=
    card_barM_eq_168 hd.mem₁.toIsTwoPrimeComponent (hn.1 ▸ hd.type₁)
  have hcard₂ : Nat.card ↥(barM M L₂) = 168 :=
    card_barM_eq_168 hd.mem₂.toIsTwoPrimeComponent (hn.2.1 ▸ hd.type₂)
  have hcard₃ : Nat.card ↥(barM M L₃) = 168 :=
    card_barM_eq_168 hd.mem₃.toIsTwoPrimeComponent (hn.2.2 ▸ hd.type₃)
  obtain ⟨y₁, hy₁, hq₁, hz₁⟩ := exists_threeElement_not_central_barM
    hd.mem₁.toIsTwoPrimeComponent ⟨n₁, hd.odd₁, hd.type₁⟩ hcard₁
  obtain ⟨y₂, hy₂, hq₂, hz₂⟩ := exists_threeElement_not_central_barM
    hd.mem₂.toIsTwoPrimeComponent ⟨n₂, hd.odd₂, hd.type₂⟩ hcard₂
  obtain ⟨y₃, hy₃, hq₃, hz₃⟩ := exists_threeElement_not_central_barM
    hd.mem₃.toIsTwoPrimeComponent ⟨n₃, hd.odd₃, hd.type₃⟩ hcard₃
  exact three_le_pRank_of_three_components hd.mem₁.toIsTwoPrimeComponent.component
    hd.mem₂.toIsTwoPrimeComponent.component hd.mem₃.toIsTwoPrimeComponent.component
    hb12 hb13 hb23 hy₁ hy₂ hy₃ hq₁ hq₂ hq₃ hz₁ hz₂ hz₃

private theorem center_barM_join_eq_bot (hd : TwelveFiveData M H d L₁ L₂ L₃ n₁ n₂ n₃)
    (hcard : (weakBlockSet M H).ncard = 3) :
    Subgroup.center ↥(barM M L₁ ⊔ barM M L₂ ⊔ barM M L₃) = ⊥ := by
  have hne := pairwise_ne_aux hd hcard
  have hZ₁ := center_barM_eq_bot_of_isTwoPrimeComponent hd.mem₁.toIsTwoPrimeComponent
    ⟨n₁, hd.odd₁, hd.type₁⟩
  have hZ₂ := center_barM_eq_bot_of_isTwoPrimeComponent hd.mem₂.toIsTwoPrimeComponent
    ⟨n₂, hd.odd₂, hd.type₂⟩
  have hZ₃ := center_barM_eq_bot_of_isTwoPrimeComponent hd.mem₃.toIsTwoPrimeComponent
    ⟨n₃, hd.odd₃, hd.type₃⟩
  have hc12 : ⁅barM M L₁, barM M L₂⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (barM_le_centralizer_barM_of_ne hd.mem₁ hd.mem₂ hne.1)
  have hc13 : ⁅barM M L₁, barM M L₃⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (barM_le_centralizer_barM_of_ne hd.mem₁ hd.mem₃ hne.2.1)
  have hc23 : ⁅barM M L₂, barM M L₃⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (barM_le_centralizer_barM_of_ne hd.mem₂ hd.mem₃ hne.2.2)
  exact center_sup_sup_eq_bot_of_commute hZ₁ hZ₂ hZ₃ hc12 hc13 hc23

private theorem eq_bot_of_isPGroup_three_le_centralizer_jSub
    (hd : TwelveFiveData M H d L₁ L₂ L₃ n₁ n₂ n₃)
    (hn : n₁ = 1 ∧ n₂ = 1 ∧ n₃ = 1) (h3 : CFSG.Open.pRank 3 M ≤ 3)
    (hcard : (weakBlockSet M H).ncard = 3)
    {Y : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hY : IsPGroup 3 Y)
    (hYc : Y ≤ Subgroup.centralizer
      (((barM M L₁ ⊔ barM M L₂ ⊔ barM M L₃) : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) : Set _)) :
    Y = ⊥ := by
  set Jbar : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M) :=
    barM M L₁ ⊔ barM M L₂ ⊔ barM M L₃ with hJbardef
  have hYc' : Y ≤ Subgroup.centralizer (Jbar : Set _) := hYc
  have hJcenter : Subgroup.center ↥Jbar = ⊥ := center_barM_join_eq_bot hd hcard
  have hJcenter' : Jbar ⊓ Subgroup.centralizer (Jbar : Set _) = ⊥ := by
    rw [← CFSG.center_map_subtype_eq_inf_centralizer Jbar, hJcenter, Subgroup.map_bot]
  have hYJ : Y ⊓ Jbar = ⊥ := by
    refine le_bot_iff.mp ?_
    calc Y ⊓ Jbar ≤ Subgroup.centralizer (Jbar : Set _) ⊓ Jbar :=
          le_inf (fun y hy => hYc' hy.1) inf_le_right
      _ = ⊥ := by rw [inf_comm, hJcenter']
  have hJrank : 3 ≤ CFSG.Open.pRank 3 Jbar := by
    rw [hJbardef]
    exact three_le_pRank_barM_join hd hn hcard
  have htop : CFSG.Open.pRank 3 (⊤ : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) ≤ 3 := by
    have h1 := CFSG.AGLEmbedding.pRank_barM_le (q := 3) Nat.prime_three (by norm_num) M M le_rfl
    have h2 : barM M M = ⊤ := by
      rw [barM, Subgroup.subgroupOf_self,
        Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥M))]
    rw [h2] at h1
    exact h1.trans h3
  have hAB : ¬ 3 ∣ Nat.card ↥(Y ⊓ Jbar) := by
    rw [hYJ, Subgroup.card_bot]
    norm_num
  have hadd := CFSG.GroupTheory.pRank_sup_eq_add_of_commute_of_not_dvd
    (p := 3) Nat.prime_three hYc' hAB
  have hsup_le : CFSG.Open.pRank 3 (Y ⊔ Jbar) ≤ 3 :=
    (CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) (le_top : Y ⊔ Jbar ≤ ⊤)).trans htop
  rw [hadd] at hsup_le
  have hYrank : CFSG.Open.pRank 3 Y = 0 := by omega
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hnot : ¬ 3 ∣ Nat.card Y :=
    CFSG.GroupTheory.not_dvd_card_of_pRank_eq_zero Nat.prime_three hYrank
  exact Subgroup.card_eq_one.mp (hY.card_eq_or_dvd.resolve_right hnot)

theorem map_conj_mem (hd : TwelveFiveData M H d L₁ L₂ L₃ n₁ n₂ n₃) {m : G} (hm : m ∈ M)
    {L : Subgroup G} (hL : L ∈ ({L₁, L₂, L₃} : Set (Subgroup G))) :
    L.map (MulAut.conj m).toMonoidHom ∈ ({L₁, L₂, L₃} : Set (Subgroup G)) := by
  have hLweak : L ∈ weakBlockSet M H := by rw [weakBlockSet_eq hd]; exact hL
  have hcomp : CFSG.AGLEmbedding.IsTwoPrimeComponent M
      (L.map (MulAut.conj m).toMonoidHom) :=
    hLweak.toIsTwoPrimeComponent.map_conj hm
  have hJmap : (jSub M H).map (MulAut.conj m).toMonoidHom = jSub M H :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (le_normalizer_jSub hd hm)
  have hLJ : L.map (MulAut.conj m).toMonoidHom ≤ jSub M H := by
    rw [← hJmap]
    exact Subgroup.map_mono (le_jSub hLweak)
  rcases eq_of_isTwoPrimeComponent hd hcomp hLJ with h | h | h
  · rw [h]; simp
  · rw [h]; simp
  · rw [h]; simp

theorem jSub_le_normalizer_left (hd : TwelveFiveData M H d L₁ L₂ L₃ n₁ n₂ n₃) :
    jSub M H ≤ normalizer (L₁ : Set G) := by
  rw [hd.join_eq]
  exact sup_le (sup_le Subgroup.le_normalizer (le_normalizer_of_mem_weakBlockSet hd.mem₂ hd.mem₁))
    (le_normalizer_of_mem_weakBlockSet hd.mem₃ hd.mem₁)

theorem jSub_le_normalizer_middle (hd : TwelveFiveData M H d L₁ L₂ L₃ n₁ n₂ n₃) :
    jSub M H ≤ normalizer (L₂ : Set G) := by
  rw [hd.join_eq]
  exact sup_le (sup_le (le_normalizer_of_mem_weakBlockSet hd.mem₁ hd.mem₂) Subgroup.le_normalizer)
    (le_normalizer_of_mem_weakBlockSet hd.mem₃ hd.mem₂)

theorem jSub_le_normalizer_right (hd : TwelveFiveData M H d L₁ L₂ L₃ n₁ n₂ n₃) :
    jSub M H ≤ normalizer (L₃ : Set G) := by
  rw [hd.join_eq]
  exact sup_le (sup_le (le_normalizer_of_mem_weakBlockSet hd.mem₁ hd.mem₃)
    (le_normalizer_of_mem_weakBlockSet hd.mem₂ hd.mem₃)) Subgroup.le_normalizer

theorem pairwise_ne (hd : TwelveFiveData M H d L₁ L₂ L₃ n₁ n₂ n₃)
    (hcard : (weakBlockSet M H).ncard = 3) : L₁ ≠ L₂ ∧ L₁ ≠ L₃ ∧ L₂ ≠ L₃ :=
  pairwise_ne_aux hd hcard

theorem three_le_pRank_jSub (hd : TwelveFiveData M H d L₁ L₂ L₃ n₁ n₂ n₃)
    (hcard : (weakBlockSet M H).ncard = 3) : 3 ≤ CFSG.Open.pRank 3 (jSub M H) := by
  have hL3 : ∀ L : Subgroup G, L ∈ weakBlockSet M H →
      ∃ n : ℕ, Odd n ∧ IsL3TwoPow n (↥L ⧸ pCore 2 ↥L) := by
    intro L hL
    rw [weakBlockSet_eq hd] at hL
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hL
    rcases hL with rfl | rfl | rfl
    exacts [⟨n₁, hd.odd₁, hd.type₁⟩, ⟨n₂, hd.odd₂, hd.type₂⟩, ⟨n₃, hd.odd₃, hd.type₃⟩]
  have h := CFSG.LocalAnalysis.AGL81TheoremCD.Section12.hr3_of_hL3 hL3
  rw [hcard] at h
  exact h

theorem card_le_of_le_normalizers (hd : TwelveFiveData M H d L₁ L₂ L₃ n₁ n₂ n₃)
    (hn : n₁ = 1 ∧ n₂ = 1 ∧ n₃ = 1) (h3 : CFSG.Open.pRank 3 M ≤ 3)
    (hcard : (weakBlockSet M H).ncard = 3) {U : Subgroup G} (hUM : U ≤ M) (hU : IsPGroup 3 U)
    (hUN : U ≤ normalizer (L₁ : Set G) ⊓ normalizer (L₂ : Set G) ⊓
      normalizer (L₃ : Set G)) :
    Nat.card U ≤ 27 := by
  classical
  obtain ⟨hn1, hn2, hn3⟩ := hn
  set B := ↥M ⧸ CFSG.pCore 2 ↥M
  let Ubar : Subgroup B := barM M U
  have hUN₁ : U ≤ normalizer (L₁ : Set G) := hUN.trans (le_trans inf_le_left inf_le_left)
  have hUN₂ : U ≤ normalizer (L₂ : Set G) := hUN.trans (le_trans inf_le_left inf_le_right)
  have hUN₃ : U ≤ normalizer (L₃ : Set G) := hUN.trans inf_le_right
  have hUbar3 : IsPGroup 3 Ubar := isPGroup_barM hU
  have hUb₁ : Ubar ≤ Subgroup.normalizer (barM M L₁ : Set B) :=
    CFSG.AGLEmbedding.barM_le_normalizer_barM hUN₁
  have hUb₂ : Ubar ≤ Subgroup.normalizer (barM M L₂ : Set B) :=
    CFSG.AGLEmbedding.barM_le_normalizer_barM hUN₂
  have hUb₃ : Ubar ≤ Subgroup.normalizer (barM M L₃ : Set B) :=
    CFSG.AGLEmbedding.barM_le_normalizer_barM hUN₃
  have h9₁ : ¬ 3 ^ 2 ∣ Nat.card (MulAut ↥(barM M L₁)) :=
    not_sq_three_dvd_card_mulAut_barM hd.mem₁.toIsTwoPrimeComponent hn1 hd.type₁
  have h9₂ : ¬ 3 ^ 2 ∣ Nat.card (MulAut ↥(barM M L₂)) :=
    not_sq_three_dvd_card_mulAut_barM hd.mem₂.toIsTwoPrimeComponent hn2 hd.type₂
  have h9₃ : ¬ 3 ^ 2 ∣ Nat.card (MulAut ↥(barM M L₃)) :=
    not_sq_three_dvd_card_mulAut_barM hd.mem₃.toIsTwoPrimeComponent hn3 hd.type₃
  set C₁ : Subgroup B := Subgroup.centralizer (barM M L₁ : Set B)
  set C₂ : Subgroup B := Subgroup.centralizer (barM M L₂ : Set B)
  set C₃ : Subgroup B := Subgroup.centralizer (barM M L₃ : Set B)
  set X3 : Subgroup B := (Ubar ⊓ C₁) ⊓ C₂ ⊓ C₃
  have hX3 : IsPGroup 3 X3 := hUbar3.to_inf_left.to_inf_left.to_inf_left
  have hX3c : X3 ≤ Subgroup.centralizer
      (((barM M L₁ ⊔ barM M L₂ ⊔ barM M L₃) : Subgroup B) : Set B) :=
    CFSG.GorensteinWalter.le_centralizer_sup_of_le_centralizers
      (CFSG.GorensteinWalter.le_centralizer_sup_of_le_centralizers
        ((inf_le_left.trans inf_le_left).trans inf_le_right)
        (inf_le_left.trans inf_le_right)) inf_le_right
  have hX3bot : X3 = ⊥ :=
    eq_bot_of_isPGroup_three_le_centralizer_jSub hd ⟨hn1, hn2, hn3⟩ h3 hcard hX3 hX3c
  have hbot : Ubar ⊓ C₁ ⊓ C₂ ⊓ C₃ = ⊥ := by
    simpa [X3, C₁, C₂, C₃] using hX3bot
  have hchain := card_le_twenty_seven_of_normalizer_chain hUbar3 hUb₁ hUb₂ hUb₃
    h9₁ h9₂ h9₃ hbot
  rw [← card_barM_of_isPGroup Nat.prime_three (by norm_num) hUM hU]
  exact hchain

private theorem le_normalizer_pair_of_le_normalizer_left
    (hd : TwelveFiveData M H d L₁ L₂ L₃ n₁ n₂ n₃)
    (hcard : (weakBlockSet M H).ncard = 3) {U : Subgroup G} (hUM : U ≤ M)
    (hU : IsPGroup 3 U) (hUN₁ : U ≤ Subgroup.normalizer (L₁ : Set G)) :
    U ≤ Subgroup.normalizer (L₂ : Set G) ∧ U ≤ Subgroup.normalizer (L₃ : Set G) := by
  classical
  let S : Set (Subgroup G) := {L₁, L₂, L₃}
  have hfix₁ : ∀ u : ↥U, L₁.map (MulAut.conj (u : G)).toMonoidHom = L₁ :=
    fun u => Subgroup.mem_normalizer_iff_map_conj_eq.mp (hUN₁ u.2)
  have hne := pairwise_ne_aux hd hcard
  have hperm₂ : ∀ u : ↥U, L₂.map (MulAut.conj (u : G)).toMonoidHom = L₁ ∨
      L₂.map (MulAut.conj (u : G)).toMonoidHom = L₂ ∨
      L₂.map (MulAut.conj (u : G)).toMonoidHom = L₃ := by
    intro u
    have h := map_conj_mem (L := L₂) hd (hUM u.2) (by simp)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have hUN₂ : U ≤ Subgroup.normalizer (L₂ : Set G) :=
    normalizes_of_fixed_of_perm hU hperm₂ hfix₁ hne.1.symm
  have hperm₃ : ∀ u : ↥U, L₃.map (MulAut.conj (u : G)).toMonoidHom = L₁ ∨
      L₃.map (MulAut.conj (u : G)).toMonoidHom = L₃ ∨
      L₃.map (MulAut.conj (u : G)).toMonoidHom = L₂ := by
    intro u
    have h := map_conj_mem (L := L₃) hd (hUM u.2) (by simp)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
  have hUN₃ : U ≤ Subgroup.normalizer (L₃ : Set G) :=
    normalizes_of_fixed_of_perm hU hperm₃ hfix₁ hne.2.1.symm
  exact ⟨hUN₂, hUN₃⟩

theorem card_le_eighty_one (hd : TwelveFiveData M H d L₁ L₂ L₃ n₁ n₂ n₃)
    (hn : n₁ = 1 ∧ n₂ = 1 ∧ n₃ = 1) (h3 : CFSG.Open.pRank 3 M ≤ 3)
    (hcard : (weakBlockSet M H).ncard = 3) {U : Subgroup G} (hUM : U ≤ M) (hU : IsPGroup 3 U) :
    Nat.card U ≤ 81 := by
  classical
  let S : Set (Subgroup G) := {L₁, L₂, L₃}
  let U₁ : Subgroup G := U ⊓ Subgroup.normalizer (L₁ : Set G)
  have hU₁M : U₁ ≤ M := inf_le_left.trans hUM
  have hU₁ : IsPGroup 3 U₁ := hU.to_inf_left
  have hU₁N₁ : U₁ ≤ Subgroup.normalizer (L₁ : Set G) := inf_le_right
  have hidx₁ : U₁.relIndex U ≤ 3 :=
    relIndex_inf_normalizer_le_three (by
      intro u
      exact map_conj_mem hd (hUM u.2) (by simp))
  obtain ⟨hU₁N₂, hU₁N₃⟩ :=
    le_normalizer_pair_of_le_normalizer_left hd hcard hU₁M hU₁ hU₁N₁
  have hU₁N : U₁ ≤ Subgroup.normalizer (L₁ : Set G) ⊓
      Subgroup.normalizer (L₂ : Set G) ⊓ Subgroup.normalizer (L₃ : Set G) :=
    le_inf (le_inf hU₁N₁ hU₁N₂) hU₁N₃
  have hcardU₁ : Nat.card U₁ ≤ 27 :=
    card_le_of_le_normalizers hd hn h3 hcard hU₁M hU₁ hU₁N
  have hcardU : Nat.card U = U₁.relIndex U * Nat.card U₁ := by
    have h := Subgroup.relIndex_mul_card (Subgroup.normalizer (L₁ : Set G)) U
    rw [inf_comm] at h
    rw [← Subgroup.inf_relIndex_left (H := U)
      (K := Subgroup.normalizer (L₁ : Set G))] at h
    simpa [U₁] using h.symm
  calc Nat.card U = U₁.relIndex U * Nat.card U₁ := hcardU
    _ ≤ 3 * 27 := Nat.mul_le_mul hidx₁ hcardU₁
    _ = 81 := by norm_num


private theorem card_le_twenty_seven_of_isSylowOf_jSub
    (hd : TwelveFiveData M H d L₁ L₂ L₃ n₁ n₂ n₃)
    (hn : n₁ = 1 ∧ n₂ = 1 ∧ n₃ = 1) (h3 : CFSG.Open.pRank 3 M ≤ 3)
    (hcard : (weakBlockSet M H).ncard = 3) {A : Subgroup G}
    (hA : CFSG.ABGLocalTools.IsSylowOf 3 A (jSub M H)) : Nat.card A ≤ 27 := by
  have hAM : A ≤ M := hA.le.trans (jSub_le M H)
  have hA3 : IsPGroup 3 A := hA.isPGroup
  have hAN₁ : A ≤ Subgroup.normalizer (L₁ : Set G) :=
    hA.le.trans (jSub_le_normalizer_left hd)
  have hAN₂ : A ≤ Subgroup.normalizer (L₂ : Set G) :=
    hA.le.trans (jSub_le_normalizer_middle hd)
  have hAN₃ : A ≤ Subgroup.normalizer (L₃ : Set G) :=
    hA.le.trans (jSub_le_normalizer_right hd)
  exact card_le_of_le_normalizers hd hn h3 hcard hAM hA3
    (le_inf (le_inf hAN₁ hAN₂) hAN₃)

private theorem le_card_of_isSylowOf_jSub
    (hd : TwelveFiveData M H d L₁ L₂ L₃ n₁ n₂ n₃)
    (_hn : n₁ = 1 ∧ n₂ = 1 ∧ n₃ = 1) (hcard : (weakBlockSet M H).ncard = 3)
    {A : Subgroup G} (hA : CFSG.ABGLocalTools.IsSylowOf 3 A (jSub M H)) :
    27 ≤ Nat.card A := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E, hEJ, hE, hEcard⟩ :=
    CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) (jSub M H)
  have h3J : 3 ≤ CFSG.Open.pRank 3 (jSub M H) := three_le_pRank_jSub hd hcard
  have h3dvdE : 3 ^ 3 ∣ Nat.card E := by
    rw [hEcard]
    exact pow_dvd_pow 3 h3J
  have h3dvdJ : 3 ^ 3 ∣ Nat.card (jSub M H) :=
    h3dvdE.trans (Subgroup.card_dvd_of_le hEJ)
  have hJne : Nat.card (jSub M H) ≠ 0 :=
    Nat.card_ne_zero.mpr ⟨⟨1, (jSub M H).one_mem⟩, inferInstance⟩
  have hfact : 3 ≤ (Nat.card (jSub M H)).factorization 3 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hJne).mp h3dvdJ
  rw [hA.card_eq]
  exact pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 3) hfact

private theorem isMulCommutative_of_action_data {B : Type} [Group B] [Finite B]
    {A X₁ X₂ X₃ : Subgroup B} (hA : IsPGroup 3 A) (hAjoin : A ≤ X₁ ⊔ X₂ ⊔ X₃)
    (hN₁ : A ≤ Subgroup.normalizer (X₁ : Set B))
    (hN₂ : A ≤ Subgroup.normalizer (X₂ : Set B))
    (hN₃ : A ≤ Subgroup.normalizer (X₃ : Set B))
    (h9₁ : ¬ 3 ^ 2 ∣ Nat.card (MulAut ↥X₁))
    (h9₂ : ¬ 3 ^ 2 ∣ Nat.card (MulAut ↥X₂))
    (h9₃ : ¬ 3 ^ 2 ∣ Nat.card (MulAut ↥X₃))
    (hZ : Subgroup.center ↥(X₁ ⊔ X₂ ⊔ X₃) = ⊥) (hAcard : Nat.card A = 27) :
    IsMulCommutative ↥A := by
  obtain ⟨hR₁, hR₂, hR₃⟩ := range_conjAction_card_eq_three hA hAjoin
    hN₁ hN₂ hN₃ h9₁ h9₂ h9₃ hZ hAcard
  haveI : IsMulCommutative ↥(conjActionHom hN₁).range :=
    isMulCommutative_of_card_three hR₁
  haveI : IsMulCommutative ↥(conjActionHom hN₂).range :=
    isMulCommutative_of_card_three hR₂
  haveI : IsMulCommutative ↥(conjActionHom hN₃).range :=
    isMulCommutative_of_card_three hR₃
  let Ψ := (rangeActionHom hN₁).prod ((rangeActionHom hN₂).prod (rangeActionHom hN₃))
  haveI hprodcomm : IsMulCommutative (↥(conjActionHom hN₁).range ×
      (↥(conjActionHom hN₂).range × ↥(conjActionHom hN₃).range)) := inferInstance
  have hΨinj : Function.Injective Ψ :=
    (MonoidHom.ker_eq_bot_iff Ψ).mp (ker_rangeAction_prod_eq_bot hAjoin hN₁ hN₂ hN₃ hZ)
  exact IsMulCommutative.of_comm fun a b => hΨinj (by
    rw [map_mul, map_mul]
    exact hprodcomm.is_comm.comm (Ψ a) (Ψ b))

private theorem isMulCommutative_barM_of_isSylowOf_jSub
    (hd : TwelveFiveData M H d L₁ L₂ L₃ n₁ n₂ n₃)
    (hn : n₁ = 1 ∧ n₂ = 1 ∧ n₃ = 1) (_h3 : CFSG.Open.pRank 3 M ≤ 3)
    (hcard : (weakBlockSet M H).ncard = 3) {A : Subgroup G}
    (hA : CFSG.ABGLocalTools.IsSylowOf 3 A (jSub M H)) (hAcard : Nat.card A = 27) :
    IsMulCommutative ↥(barM M A) := by
  classical
  obtain ⟨hn1, hn2, hn3⟩ := hn
  set B := ↥M ⧸ CFSG.pCore 2 ↥M
  have hAM : A ≤ M := hA.le.trans (jSub_le M H)
  have hA3 : IsPGroup 3 A := hA.isPGroup
  have hAbar3 : IsPGroup 3 (barM M A) := isPGroup_barM hA3
  have hAbarcard : Nat.card ↥(barM M A) = 27 := by
    rw [card_barM_of_isPGroup Nat.prime_three (by norm_num) hAM hA3, hAcard]
  have hAbarJ : barM M A ≤ barM M L₁ ⊔ barM M L₂ ⊔ barM M L₃ := by
    have h := CFSG.AGLEmbedding.barM_mono (M := M) hA.le
    rwa [barM_jSub_eq hd] at h
  have hAN₁ : A ≤ Subgroup.normalizer (L₁ : Set G) :=
    hA.le.trans (jSub_le_normalizer_left hd)
  have hAN₂ : A ≤ Subgroup.normalizer (L₂ : Set G) :=
    hA.le.trans (jSub_le_normalizer_middle hd)
  have hAN₃ : A ≤ Subgroup.normalizer (L₃ : Set G) :=
    hA.le.trans (jSub_le_normalizer_right hd)
  have hAbarN₁ : barM M A ≤ Subgroup.normalizer (barM M L₁ : Set B) :=
    CFSG.AGLEmbedding.barM_le_normalizer_barM hAN₁
  have hAbarN₂ : barM M A ≤ Subgroup.normalizer (barM M L₂ : Set B) :=
    CFSG.AGLEmbedding.barM_le_normalizer_barM hAN₂
  have hAbarN₃ : barM M A ≤ Subgroup.normalizer (barM M L₃ : Set B) :=
    CFSG.AGLEmbedding.barM_le_normalizer_barM hAN₃
  have h9₁ : ¬ 3 ^ 2 ∣ Nat.card (MulAut ↥(barM M L₁)) :=
    not_sq_three_dvd_card_mulAut_barM hd.mem₁.toIsTwoPrimeComponent hn1 hd.type₁
  have h9₂ : ¬ 3 ^ 2 ∣ Nat.card (MulAut ↥(barM M L₂)) :=
    not_sq_three_dvd_card_mulAut_barM hd.mem₂.toIsTwoPrimeComponent hn2 hd.type₂
  have h9₃ : ¬ 3 ^ 2 ∣ Nat.card (MulAut ↥(barM M L₃)) :=
    not_sq_three_dvd_card_mulAut_barM hd.mem₃.toIsTwoPrimeComponent hn3 hd.type₃
  exact isMulCommutative_of_action_data hAbar3 hAbarJ hAbarN₁ hAbarN₂ hAbarN₃
    h9₁ h9₂ h9₃ (center_barM_join_eq_bot hd hcard) hAbarcard

private theorem isMulCommutative_of_isSylowOf_jSub
    (hd : TwelveFiveData M H d L₁ L₂ L₃ n₁ n₂ n₃)
    (hn : n₁ = 1 ∧ n₂ = 1 ∧ n₃ = 1) (h3 : CFSG.Open.pRank 3 M ≤ 3)
    (hcard : (weakBlockSet M H).ncard = 3) {A : Subgroup G}
    (hA : CFSG.ABGLocalTools.IsSylowOf 3 A (jSub M H)) (hAcard : Nat.card A = 27) :
    IsMulCommutative A := by
  classical
  set B := ↥M ⧸ CFSG.pCore 2 ↥M
  have hAM : A ≤ M := hA.le.trans (jSub_le M H)
  have hA3 : IsPGroup 3 A := hA.isPGroup
  have hAbarcomm := isMulCommutative_barM_of_isSylowOf_jSub hd hn h3 hcard hA hAcard
  refine IsMulCommutative.of_comm fun a b => ?_
  have hmemA : (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨(a : G), hAM a.2⟩ : B) ∈ barM M A :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr a.2)
  have hmemB : (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨(b : G), hAM b.2⟩ : B) ∈ barM M A :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr b.2)
  have habA : ⁅(a : G), (b : G)⁆ ∈ A :=
    Subgroup.commutator_le_self A (Subgroup.commutator_mem_commutator a.2 b.2)
  have hmk : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨⁅(a : G), (b : G)⁆, hAM habA⟩ = 1 := by
    rw [show (⟨⁅(a : G), (b : G)⁆, hAM habA⟩ : ↥M) =
        ⁅(⟨(a : G), hAM a.2⟩ : ↥M), (⟨(b : G), hAM b.2⟩ : ↥M)⁆ from
        Subtype.ext rfl]
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact congrArg Subtype.val (hAbarcomm.is_comm.comm ⟨_, hmemA⟩ ⟨_, hmemB⟩)
  have hO : ((⁅(a : G), (b : G)⁆) : G) ∈ pCoreOf 2 M :=
    coe_mem_pCoreOf_two_of_mk_eq_one ⟨_, hAM habA⟩ hmk
  have h1 : ⁅(a : G), (b : G)⁆ = 1 :=
    eq_one_of_mem_pCoreOf_two Nat.prime_three (by norm_num) hA3 habA hO
  exact Subtype.ext (commutatorElement_eq_one_iff_mul_comm.mp h1)

theorem card_eq_and_comm_of_isSylowOf_jSub (hd : TwelveFiveData M H d L₁ L₂ L₃ n₁ n₂ n₃)
    (hn : n₁ = 1 ∧ n₂ = 1 ∧ n₃ = 1) (h3 : CFSG.Open.pRank 3 M ≤ 3)
    (hcard : (weakBlockSet M H).ncard = 3) {A : Subgroup G}
    (hA : CFSG.ABGLocalTools.IsSylowOf 3 A (jSub M H)) :
    Nat.card A = 27 ∧ IsMulCommutative A := by
  have hle : Nat.card A ≤ 27 := card_le_twenty_seven_of_isSylowOf_jSub hd hn h3 hcard hA
  have hge : 27 ≤ Nat.card A := le_card_of_isSylowOf_jSub hd hn hcard hA
  exact ⟨le_antisymm hle hge, isMulCommutative_of_isSylowOf_jSub hd hn h3 hcard hA
    (le_antisymm hle hge)⟩

end TwelveFiveData

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
