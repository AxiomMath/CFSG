module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveIIbExclE
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveIIbOdd

public section

open Subgroup CFSG.Open CFSG.Blueprint CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open scoped commutatorElement

namespace CFSG.ComponentClassification.RankTwoAltFive

namespace Setting310

variable {G : Type} [Group G] [Finite G] {A R T V₀ : Subgroup G} {g : G}
  (h : Setting310 A R g T V₀)
include h

section PStructure

variable {P : Subgroup G} (hP : IsSylowOf 2 P (transvGroup (R ⊔ T) V₀))
  (hPC : P ⊓ centralizer ((R ⊔ T : Subgroup G) : Set G) = R ⊔ T)
include hP hPC

variable (hIIb : centralizer (A : Set G) ⊓ normalizer (R : Set G) ≤ centralizer (R : Set G))
include hIIb

theorem false_of_eps_one_isVprime_of_conj
    (hGold : Asc76X.GoldschmidtTheoremA) (hP64 : Nat.card P = 64) (hε : EpsOne (R ⊔ T) P)
    {V' : Subgroup G} (hV' : IsVprime (R ⊔ T) V₀ P V') {c w : G} (hcV' : c ∈ V')
    (hcV₀ : c ∉ V₀) (hw : w ∈ V₀) (hw1 : w ≠ 1) (hwc : IsConj w c) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXn : (rankTwoX A).Normal := normalClosure_normal
  have hVP : R ⊔ T ≤ P := hPC ▸ inf_le_left
  have hV₀V' : V₀ ≤ V' := hV'.inf ▸ inf_le_right
  have hV₀X : V₀ ≤ rankTwoX A := h.V₀_le_A.trans le_normalClosure
  have hS := h.isSylowOf_top_of_eps_one_isVprime hP hPC hIIb hP64 hε hV'
  have hV'2 : ∀ v ∈ V', v * v = 1 := fun v hv => by rw [← sq]; exact hV'.elem.2 v hv
  have hcV : c ∉ R ⊔ T := fun he => hcV₀ (hV'.inf ▸ mem_inf.mpr ⟨he, hcV'⟩)
  have hconj : ∀ a ∈ V', a ≠ 1 → IsConj w a := by
    intro a ha ha1
    by_cases haV₀ : a ∈ V₀
    · exact h.isConj_of_mem_V₀ hw hw1 haV₀ ha1
    · have haV : a ∉ R ⊔ T := fun he => haV₀ (hV'.inf ▸ mem_inf.mpr ⟨he, ha⟩)
      obtain ⟨x, hx⟩ := h.P_invol_conj hP hPC (hV'.le hcV') hcV (hV'2 c hcV') (hV'.le ha) haV
        (hV'2 a ha)
      exact hwc.trans (isConj_iff.mpr ⟨x⁻¹, by rw [inv_inv]; exact hx⟩)
  obtain ⟨S, hSS⟩ : ∃ S : Sylow 2 G, (S : Subgroup G) = P := by
    have hc := hS.card_eq
    rw [Subgroup.card_top] at hc
    exact ⟨Sylow.ofCard _ hc, Sylow.coe_ofCard _ _⟩
  have hcl : ∀ a ∈ V', ∀ y : G, y⁻¹ * a * y ∈ (S : Subgroup G) → y⁻¹ * a * y ∈ V' := by
    intro a ha y hy
    rw [hSS] at hy
    by_cases ha1 : a = 1
    · rw [ha1, mul_one, inv_mul_cancel]
      exact one_mem _
    have hwa : IsConj w (y⁻¹ * a * y) :=
      (hconj a ha ha1).trans (isConj_iff.mpr ⟨y⁻¹, by rw [inv_inv]⟩)
    have hb2 : y⁻¹ * a * y * (y⁻¹ * a * y) = 1 := by
      calc y⁻¹ * a * y * (y⁻¹ * a * y) = y⁻¹ * (a * a) * y := by group
        _ = 1 := by rw [hV'2 a ha]; group
    by_cases hbV : y⁻¹ * a * y ∈ R ⊔ T
    · by_contra hb
      exact h.not_isRootInv_of_isConj hw hw1 hwa
        (h.isRootInv_of_mem_V hbV fun h0 => hb (hV₀V' h0))
    · exact hV'.inv _ hy hb2 hbV
  have hV'1 : V' ≠ ⊥ := fun he => hcV₀ (by rw [he, mem_bot] at hcV'; rw [hcV']; exact one_mem _)
  obtain ⟨hV'X, hinv⟩ := h.goldschmidt_X hGold S (hSS ▸ hV'.le) hV'.elem.1 hcl hV'1
  have hRX : ∀ r ∈ R, r ∈ rankTwoX A → r = 1 := by
    intro r hr hrX
    have hr2 : r ^ 2 = 1 := by rw [sq]; exact h.mul_self (mem_sup_left hr)
    have hrV' := hinv r (hSS ▸ hVP (mem_sup_left hr)) hrX hr2
    have hr0 : r ∈ V₀ := hV'.inf ▸ mem_inf.mpr ⟨mem_sup_left hr, hrV'⟩
    have h2 : r ∈ R ⊓ V₀ := mem_inf.mpr ⟨hr, hr0⟩
    rwa [h.inf_R_V₀, mem_bot] at h2
  have hPN : P ≤ normalizer (V' : Set G) := fun p hp =>
    h.mem_normalizer_Vprime hV' (le_normalizer hp) (hP.le hp).1
  have hV'syl : IsSylowOf 2 V' (rankTwoX A) := by
    have h1 : IsSylowOf 2 (P ⊓ rankTwoX A) (rankTwoX A) :=
      hS.inf_of_le_normalizer le_top (by rw [normalizer_eq_top_iff.mpr hXn])
    have heq : P ⊓ rankTwoX A = V' := by
      apply le_antisymm _ (le_inf hV'.le hV'X)
      intro p hp
      obtain ⟨hpP, hpX⟩ := mem_inf.mp hp
      have hpVV' : p ∈ V' ⊔ (R ⊔ T) := by rw [sup_comm, hV'.sup]; exact hpP
      obtain ⟨v', hv', v, hv, rfl⟩ :=
        exists_mul_of_mem_sup_of_le_normalizer (hVP.trans hPN) hpVV'
      have hvX : v ∈ rankTwoX A := by
        have := mul_mem (inv_mem (hV'X hv')) hpX
        rwa [inv_mul_cancel_left] at this
      obtain ⟨r, hr, w', hw', rfl⟩ := h.exists_mul hv
      have hrX : r ∈ rankTwoX A := by
        have := mul_mem hvX (inv_mem (hV₀X hw'))
        rwa [mul_inv_cancel_right] at this
      rw [hRX r hr hrX, one_mul]
      exact mul_mem hv' (hV₀V' hw')
    rwa [heq] at h1
  have hdec : ∀ y : G, ∃ x ∈ rankTwoX A, ∃ s ∈ R, y = x * s := fun y => by
    have hy : y ∈ rankTwoX A ⊔ R := by rw [h.sup_top]; exact mem_top y
    exact AS76b.exists_mul_of_mem_sup_of_le_normalizer
      (by rw [normalizer_eq_top_iff.mpr hXn]; exact le_top) hy
  have hconjX : ∀ a ∈ V', a ≠ 1 → ∃ x ∈ rankTwoX A, x * w * x⁻¹ = a := by
    intro a ha ha1
    obtain ⟨y, hy⟩ := isConj_iff.mp (hconj a ha ha1)
    obtain ⟨x, hx, s, hs, rfl⟩ := hdec y
    refine ⟨x, hx, ?_⟩
    have hsw : s * w = w * s := le_centralizer_iff.mp h.sylowR.le (h.V₀_le_A hw) s hs
    rw [← hy]
    calc x * w * x⁻¹ = x * (w * s) * s⁻¹ * x⁻¹ := by group
      _ = x * (s * w) * s⁻¹ * x⁻¹ := by rw [hsw]
      _ = x * s * w * (x * s)⁻¹ := by group
  have htrans : ∀ a ∈ V', ∀ b ∈ V', a ≠ 1 → b ≠ 1 →
      ∃ n ∈ rankTwoX A ⊓ normalizer (V' : Set G), n * a * n⁻¹ = b := by
    intro a ha b hb ha1 hb1
    obtain ⟨xa, hxa, hxaw⟩ := hconjX a ha ha1
    obtain ⟨xb, hxb, hxbw⟩ := hconjX b hb hb1
    set u := xb * xa⁻¹ with hudef
    have huX : u ∈ rankTwoX A := mul_mem hxb (inv_mem hxa)
    have hub : u * a * u⁻¹ = b := by rw [← hxaw, ← hxbw, hudef]; group
    set C := rankTwoX A ⊓ centralizer ({b} : Set G) with hCdef
    have hV'C : V' ≤ C := fun v hv => mem_inf.mpr ⟨hV'X hv, mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hV'.elem.1.is_comm.comm ⟨v, hv⟩ ⟨b, hb⟩))⟩
    have hmemU : ∀ x : G, x ∈ rightConjugate V' u⁻¹ ↔ u⁻¹ * x * u ∈ V' := fun x => by
      rw [mem_rightConjugate_iff, inv_inv]
    have hUC : rightConjugate V' u⁻¹ ≤ C := by
      intro x hx
      rw [hmemU] at hx
      refine mem_inf.mpr ⟨?_, mem_centralizer_singleton_iff.mpr ?_⟩
      · have := hXn.conj_mem _ (hV'X hx) u
        rwa [show u * (u⁻¹ * x * u) * u⁻¹ = x by group] at this
      · have h1 := congrArg Subtype.val (hV'.elem.1.is_comm.comm ⟨_, hx⟩ ⟨a, ha⟩)
        simp only [coe_mul] at h1
        rw [← hub]
        calc x * (u * a * u⁻¹) = u * (u⁻¹ * x * u * a) * u⁻¹ := by group
          _ = u * (a * (u⁻¹ * x * u)) * u⁻¹ := by rw [h1]
          _ = u * a * u⁻¹ * x := by group
    have hCX : C ≤ rankTwoX A := inf_le_left
    have hV'Cs : IsSylowOf 2 V' C := hV'syl.of_le hV'C hCX
    have hUs : IsSylowOf 2 (rightConjugate V' u⁻¹) C := by
      have h1 := AschbacherTheorem3.isSylowOf_rightConjugate hV'syl u⁻¹
      rw [(rightConjugate_eq_self_iff (rankTwoX A) u⁻¹).mpr
        (by rw [normalizer_eq_top_iff.mpr hXn]; exact mem_top _)] at h1
      exact h1.of_le hUC hCX
    obtain ⟨c', hc', hUc⟩ := Lemma22.exists_conj_eq_of_isSylowOf hV'Cs hUs
    obtain ⟨hc'X, hc'b⟩ := mem_inf.mp hc'
    refine ⟨c'⁻¹ * u, mem_inf.mpr ⟨mul_mem (inv_mem hc'X) huX, ?_⟩, ?_⟩
    · rw [mem_normalizer_iff]
      intro v
      have key : ∀ x : G, u⁻¹ * x * u ∈ V' ↔ c'⁻¹ * x * c' ∈ V' := fun x => by
        rw [← hmemU, hUc, Lemma34.mem_conj_iff]
      rw [show c'⁻¹ * u * v * (c'⁻¹ * u)⁻¹ = c'⁻¹ * (u * v * u⁻¹) * c' by group, ← key,
        show u⁻¹ * (u * v * u⁻¹) * u = v by group]
    · have hcb : c' * b = b * c' := mem_centralizer_singleton_iff.mp hc'b
      rw [show c'⁻¹ * u * a * (c'⁻¹ * u)⁻¹ = c'⁻¹ * (u * a * u⁻¹) * c' by group, hub]
      calc c'⁻¹ * b * c' = c'⁻¹ * (b * c') := by group
        _ = c'⁻¹ * (c' * b) := by rw [hcb]
        _ = b := by group
  refine false_of_transitive_odd (Y := rankTwoX A ⊓ normalizer (V' : Set G)) (B := R)
    hV'.elem hV'.card hV₀V' h.card_V₀ inf_le_right ?_ htrans
    (fun r hr => hPN (hVP (mem_sup_left hr))) ?_ h.cardR
    (fun r hr => h.mul_self (mem_sup_left hr)) ?_ ?_ ?_
  · intro n hn hn2
    obtain ⟨hnX, hnN⟩ := mem_inf.mp hn
    have hp : IsPGroup 2 (V' ⊔ zpowers n : Subgroup G) :=
      hV'syl.isPGroup.to_sup_of_normal_left' hn2 (zpowers_le.mpr hnN)
    have heq := hV'syl.eq_of_le le_sup_left (sup_le hV'X (zpowers_le.mpr hnX)) hp
    exact heq ▸ mem_sup_right (mem_zpowers n)
  · intro r hr n hn
    obtain ⟨hnX, hnN⟩ := mem_inf.mp hn
    have hrN := hPN (hVP (mem_sup_left hr))
    exact mem_inf.mpr ⟨hXn.conj_mem n hnX r, mul_mem (mul_mem hrN hnN) (inv_mem hrN)⟩
  · intro r hr hr1 v hv hrv
    by_contra hv0
    have hvV : v ∉ R ⊔ T := fun he => hv0 (hV'.inf ▸ mem_inf.mpr ⟨he, hv⟩)
    have hr0 := h.P_fixed hP hPC (hV'.le hv) hvV (mem_sup_left hr) (by
      calc v * r * v⁻¹ = (r * v * r⁻¹) * r * v⁻¹ := by rw [hrv]
        _ = r := by group)
    have h2 : r ∈ R ⊓ V₀ := mem_inf.mpr ⟨hr, hr0⟩
    rw [h.inf_R_V₀, mem_bot] at h2
    exact hr1 h2
  · intro r hr v hv
    have hrP : r ∈ P := hVP (mem_sup_left hr)
    have hvP : v ∈ P := hV'.le hv
    have h1 := h.commP_mem hP hPC hrP hvP
    have h2 : v⁻¹ * (r * v * r⁻¹) = ⁅r, v⁆ := by
      rw [commutatorElement_def]
      calc v⁻¹ * (r * v * r⁻¹) = v⁻¹ * (r * v * r⁻¹ * v⁻¹) * v := by group
        _ = r * v * r⁻¹ * v⁻¹ := by rw [P_comm_V₀ hP (by
              rw [← commutatorElement_def]; exact h1) (inv_mem hvP)]; group
    rw [h2]
    exact h1
  · intro r hr v hv
    rw [h.comm (mem_sup_left hr) (h.V₀_le hv)]
    group

end PStructure

end Setting310

end CFSG.ComponentClassification.RankTwoAltFive
