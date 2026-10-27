module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.SolomonK.Step1
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.EvenSporadicStandard.M12Std.SolomonK

open Subgroup

variable {K : Type} [Group K] [Finite K]

lemma exists_mul_eq_of_mem_sup {L C : Subgroup K} (hL : L.Normal) (hsup : L ⊔ C = ⊤)
    (x : K) : ∃ l ∈ L, ∃ c ∈ C, l * c = x := by
  haveI : L.Normal := hL
  have hx : x ∈ L ⊔ C := by rw [hsup]; exact Subgroup.mem_top x
  exact Subgroup.mem_sup_of_normal_left.mp hx

lemma eq_of_mul_eq_mul {L C : Subgroup K} (hLC : Disjoint L C) {l l' c c' : K}
    (hl : l ∈ L) (hl' : l' ∈ L) (hc : c ∈ C) (hc' : c' ∈ C) (h : l * c = l' * c') :
    l = l' ∧ c = c' := by
  have hleft : l'⁻¹ * l ∈ L := L.mul_mem (L.inv_mem hl') hl
  have hh : l'⁻¹ * (l * c) = c' := by rw [h, inv_mul_cancel_left]
  have hkey : l'⁻¹ * l = c' * c⁻¹ := by
    rw [← hh]
    group
  have hright : c' * c⁻¹ ∈ C := C.mul_mem hc' (C.inv_mem hc)
  have hmemC : l'⁻¹ * l ∈ C := by rw [hkey]; exact hright
  have hone : l'⁻¹ * l = 1 := Subgroup.disjoint_def.mp hLC hleft hmemC
  have hl_eq : l = l' := by
    calc l = l' * (l'⁻¹ * l) := by group
      _ = l' * 1 := by rw [hone]
      _ = l' := by simp
  have hc_eq : c = c' := by
    rw [hl_eq] at h
    exact mul_left_cancel h
  exact ⟨hl_eq, hc_eq⟩

lemma sq_eq_one_and_commute_of_mul_mem {E L C : Subgroup K} (hE : GoodE E) (hL : L.Normal)
    (hsup : L ⊔ C = ⊤) (hLC : Disjoint L C)
    (hcomm : ∀ l ∈ L, ∀ c ∈ C, l * c = c * l) {l c : K} (hl : l ∈ L) (hc : c ∈ C)
    (hlc : l * c ∈ E) :
    l * l = 1 ∧ c * c = 1 ∧ (∀ e ∈ E, l * e = e * l) ∧ (∀ e ∈ E, c * e = e * c) := by
  have hlc_comm : l * c = c * l := hcomm l hl c hc
  have hsq : (l * c) * (l * c) = 1 := hE.sq (l * c) hlc
  have hmul : (l * l) * (c * c) = 1 := by
    have h1 : (l * c) * (l * c) = (l * l) * (c * c) := by
      calc (l * c) * (l * c) = l * (c * l) * c := by group
        _ = l * (l * c) * c := by rw [← hlc_comm]
        _ = (l * l) * (c * c) := by group
    rw [← h1, hsq]
  have hll_eq : l * l = (c * c)⁻¹ := mul_eq_one_iff_eq_inv.mp hmul
  have hll : l * l = 1 := by
    have hmemL : l * l ∈ L := L.mul_mem hl hl
    have hmemC : l * l ∈ C := by rw [hll_eq]; exact C.inv_mem (C.mul_mem hc hc)
    exact Subgroup.disjoint_def.mp hLC hmemL hmemC
  have hcc : c * c = 1 := by
    have h := hmul
    rw [hll, one_mul] at h
    exact h
  have hcommE : ∀ e ∈ E, l * e = e * l ∧ c * e = e * c := by
    intro e he
    obtain ⟨l', hl', c', hc', hdec⟩ := exists_mul_eq_of_mem_sup hL hsup e
    have hl'c'E : l' * c' ∈ E := by rw [hdec]; exact he
    have hLHS : (l * c) * (l' * c') = (l * l') * (c * c') := by
      calc (l * c) * (l' * c') = l * (c * l') * c' := by group
        _ = l * (l' * c) * c' := by rw [← hcomm l' hl' c hc]
        _ = (l * l') * (c * c') := by group
    have hRHS : (l' * c') * (l * c) = (l' * l) * (c' * c) := by
      calc (l' * c') * (l * c) = l' * (c' * l) * c := by group
        _ = l' * (l * c') * c := by rw [← hcomm l hl c' hc']
        _ = (l' * l) * (c' * c) := by group
    have hcanon : (l * l') * (c * c') = (l' * l) * (c' * c) := by
      rw [← hLHS, ← hRHS]
      exact hE.comm (l * c) hlc (l' * c') hl'c'E
    have hpair : l * l' = l' * l ∧ c * c' = c' * c :=
      eq_of_mul_eq_mul hLC (L.mul_mem hl hl') (L.mul_mem hl' hl) (C.mul_mem hc hc')
        (C.mul_mem hc' hc) hcanon
    constructor
    · rw [← hdec]
      calc l * (l' * c') = (l * l') * c' := by group
        _ = (l' * l) * c' := by rw [hpair.1]
        _ = l' * (l * c') := by group
        _ = l' * (c' * l) := by rw [hcomm l hl c' hc']
        _ = (l' * c') * l := by group
    · rw [← hdec]
      calc c * (l' * c') = (c * l') * c' := by group
        _ = (l' * c) * c' := by rw [← hcomm l' hl' c hc]
        _ = l' * (c * c') := by group
        _ = l' * (c' * c) := by rw [hpair.2]
        _ = (l' * c') * c := by group
  exact ⟨hll, hcc, fun e he => (hcommE e he).1, fun e he => (hcommE e he).2⟩

lemma mem_of_mul_mem_of_goodE (hP : P12Facts) (hK : SolomonA12HypK K) {E L C : Subgroup K}
    (hE : GoodE E) (hL : L.Normal) (hsup : L ⊔ C = ⊤) (hLC : Disjoint L C)
    (hcomm : ∀ l ∈ L, ∀ c ∈ C, l * c = c * l) {l c : K} (hl : l ∈ L) (hc : c ∈ C)
    (hlc : l * c ∈ E) : l ∈ E ∧ c ∈ E := by
  obtain ⟨hll, hcc, hcommEl, hcommEc⟩ :=
    sq_eq_one_and_commute_of_mul_mem hE hL hsup hLC hcomm hl hc hlc
  have hlc_comm : l * c = c * l := hcomm l hl c hc
  let s : Set K := (E : Set K) ∪ {l, c}
  have hcomm_s : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a := by
    intro a ha b hb
    rcases ha with haE | ha2
    · rcases hb with hbE | hb2
      · exact hE.comm a haE b hbE
      · rcases hb2 with rfl | rfl
        · exact (hcommEl a haE).symm
        · exact (hcommEc a haE).symm
    · rcases ha2 with rfl | rfl
      · rcases hb with hbE | hb2
        · exact hcommEl b hbE
        · rcases hb2 with rfl | rfl
          · rfl
          · exact hlc_comm
      · rcases hb with hbE | hb2
        · exact hcommEc b hbE
        · rcases hb2 with rfl | rfl
          · exact hlc_comm.symm
          · rfl
  have hp_s : ∀ a ∈ s, a ^ 2 = 1 := by
    intro a ha
    rcases ha with haE | ha2
    · rw [pow_two]; exact hE.sq a haE
    · rcases ha2 with rfl | rfl
      · rw [pow_two]; exact hll
      · rw [pow_two]; exact hcc
  let B : Subgroup K := Subgroup.closure s
  have hBelem : CFSG.Open.IsElemAbelian 2 B :=
    CFSG.Open.IsElemAbelian.closure_of_commute hcomm_s hp_s
  have hB2 : IsPGroup 2 B := hBelem.isPGroup
  obtain ⟨S, hBS⟩ := hB2.exists_le_sylow
  have hQ : ElemFactsIn (S : Subgroup K) := elemFactsIn_sylow hP hK S
  have hEB : E ≤ B := fun x hx => Subgroup.subset_closure (show x ∈ s from Or.inl hx)
  have hEcard : 2 ^ 6 ≤ Nat.card B := by
    rw [← hE.card]
    exact Subgroup.card_le_of_le hEB
  have hBsq : ∀ x ∈ B, x * x = 1 := fun x hx => hBelem.mul_self_eq_one hx
  have hle : B ≤ E :=
    ElemFactsIn.le_of_elem hQ (hEB.trans hBS) hE.sq hE.card hBS hBsq hEcard
  exact ⟨hle (Subgroup.subset_closure (show l ∈ s from Or.inr (by simp))),
    hle (Subgroup.subset_closure (show c ∈ s from Or.inr (by simp)))⟩

lemma conj_mem_E_of_mem_normalizer_inf_left (hP : P12Facts) (hK : SolomonA12HypK K)
    {E L C : Subgroup K} (hE : GoodE E) (hL : L.Normal) (hsup : L ⊔ C = ⊤)
    (hLC : Disjoint L C) (hcomm : ∀ l ∈ L, ∀ c ∈ C, l * c = c * l) {g h : K}
    (hg : g ∈ normalizer ((E ⊓ L : Subgroup K) : Set K)) (hgL : g ∈ L) (hh : h ∈ E) :
    g * h * g⁻¹ ∈ E := by
  obtain ⟨l', hl', c', hc', hdec⟩ := exists_mul_eq_of_mem_sup hL hsup h
  have hl'c'E : l' * c' ∈ E := by rw [hdec]; exact hh
  obtain ⟨hl'E, hc'E⟩ := mem_of_mul_mem_of_goodE hP hK hE hL hsup hLC hcomm hl' hc' hl'c'E
  have hgl' : g * l' * g⁻¹ ∈ E ⊓ L :=
    (Subgroup.mem_normalizer_iff.mp hg l').mp ⟨hl'E, hl'⟩
  have hgc' : g * c' * g⁻¹ = c' := by
    rw [hcomm g hgL c' hc']
    simp
  rw [← hdec]
  have heq : g * (l' * c') * g⁻¹ = (g * l' * g⁻¹) * c' := by
    calc g * (l' * c') * g⁻¹ = (g * l' * g⁻¹) * (g * c' * g⁻¹) := by group
      _ = (g * l' * g⁻¹) * c' := by rw [hgc']
  rw [heq]
  exact E.mul_mem hgl'.1 hc'E

lemma conj_mem_E_of_mem_normalizer_inf_right (hP : P12Facts) (hK : SolomonA12HypK K)
    {E L C : Subgroup K} (hE : GoodE E) (hL : L.Normal) (hsup : L ⊔ C = ⊤)
    (hLC : Disjoint L C) (hcomm : ∀ l ∈ L, ∀ c ∈ C, l * c = c * l) {g h : K}
    (hg : g ∈ normalizer ((E ⊓ C : Subgroup K) : Set K)) (hgC : g ∈ C) (hh : h ∈ E) :
    g * h * g⁻¹ ∈ E := by
  obtain ⟨l', hl', c', hc', hdec⟩ := exists_mul_eq_of_mem_sup hL hsup h
  have hl'c'E : l' * c' ∈ E := by rw [hdec]; exact hh
  obtain ⟨hl'E, hc'E⟩ := mem_of_mul_mem_of_goodE hP hK hE hL hsup hLC hcomm hl' hc' hl'c'E
  have hgc' : g * c' * g⁻¹ ∈ E ⊓ C :=
    (Subgroup.mem_normalizer_iff.mp hg c').mp ⟨hc'E, hc'⟩
  have hgl' : g * l' * g⁻¹ = l' := by
    rw [← hcomm l' hl' g hgC]
    simp
  rw [← hdec]
  have heq : g * (l' * c') * g⁻¹ = l' * (g * c' * g⁻¹) := by
    calc g * (l' * c') * g⁻¹ = (g * l' * g⁻¹) * (g * c' * g⁻¹) := by group
      _ = l' * (g * c' * g⁻¹) := by rw [hgl']
  rw [heq]
  exact E.mul_mem hl'E hgc'.1

lemma normalizer_inf_left_le (hP : P12Facts) (hK : SolomonA12HypK K) {E L C : Subgroup K}
    (hE : GoodE E) (hL : L.Normal) (hsup : L ⊔ C = ⊤) (hLC : Disjoint L C)
    (hcomm : ∀ l ∈ L, ∀ c ∈ C, l * c = c * l) :
    normalizer ((E ⊓ L : Subgroup K) : Set K) ⊓ L ≤ normalizer (E : Set K) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact conj_mem_E_of_mem_normalizer_inf_left hP hK hE hL hsup hLC hcomm hg.1 hg.2 hh
  · intro hh
    have hg' : g⁻¹ ∈ normalizer ((E ⊓ L : Subgroup K) : Set K) ∧ g⁻¹ ∈ L :=
      ⟨inv_mem hg.1, inv_mem hg.2⟩
    have hconj :=
      conj_mem_E_of_mem_normalizer_inf_left hP hK hE hL hsup hLC hcomm hg'.1 hg'.2 hh
    have heq : g⁻¹ * (g * h * g⁻¹) * (g⁻¹)⁻¹ = h := by group
    rw [heq] at hconj
    exact hconj

lemma normalizer_inf_right_le (hP : P12Facts) (hK : SolomonA12HypK K) {E L C : Subgroup K}
    (hE : GoodE E) (hL : L.Normal) (hsup : L ⊔ C = ⊤) (hLC : Disjoint L C)
    (hcomm : ∀ l ∈ L, ∀ c ∈ C, l * c = c * l) :
    normalizer ((E ⊓ C : Subgroup K) : Set K) ⊓ C ≤ normalizer (E : Set K) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact conj_mem_E_of_mem_normalizer_inf_right hP hK hE hL hsup hLC hcomm hg.1 hg.2 hh
  · intro hh
    have hg' : g⁻¹ ∈ normalizer ((E ⊓ C : Subgroup K) : Set K) ∧ g⁻¹ ∈ C :=
      ⟨inv_mem hg.1, inv_mem hg.2⟩
    have hconj :=
      conj_mem_E_of_mem_normalizer_inf_right hP hK hE hL hsup hLC hcomm hg'.1 hg'.2 hh
    have heq : g⁻¹ * (g * h * g⁻¹) * (g⁻¹)⁻¹ = h := by group
    rw [heq] at hconj
    exact hconj

def splitM1 (E L C : Subgroup K)
    (hcomm : ∀ l ∈ L, ∀ c ∈ C, l * c = c * l) : Subgroup K where
  carrier := {x | ∃ l ∈ normalizer ((E ⊓ L : Subgroup K) : Set K) ⊓ L,
    ∃ c ∈ (E ⊓ C : Subgroup K), l * c = x}
  one_mem' := ⟨1, by simp, 1, by simp, by simp⟩
  mul_mem' := by
    rintro x y ⟨l₁, hl₁, c₁, hc₁, rfl⟩ ⟨l₂, hl₂, c₂, hc₂, rfl⟩
    refine ⟨l₁ * l₂, ⟨mul_mem hl₁.1 hl₂.1, mul_mem hl₁.2 hl₂.2⟩, c₁ * c₂,
      mul_mem hc₁ hc₂, ?_⟩
    calc (l₁ * l₂) * (c₁ * c₂) = l₁ * (l₂ * c₁) * c₂ := by group
      _ = l₁ * (c₁ * l₂) * c₂ := by rw [hcomm l₂ hl₂.2 c₁ hc₁.2]
      _ = (l₁ * c₁) * (l₂ * c₂) := by group
  inv_mem' := by
    rintro x ⟨l, hl, c, hc, rfl⟩
    have hlinv : l⁻¹ ∈ L := L.inv_mem hl.2
    have hcinv : c⁻¹ ∈ C := ((E ⊓ C : Subgroup K).inv_mem hc).2
    refine ⟨l⁻¹, ⟨(normalizer _).inv_mem hl.1, hlinv⟩, c⁻¹,
      (E ⊓ C : Subgroup K).inv_mem hc, ?_⟩
    calc l⁻¹ * c⁻¹ = c⁻¹ * l⁻¹ := hcomm l⁻¹ hlinv c⁻¹ hcinv
      _ = (l * c)⁻¹ := by group

lemma le_splitM1 (hP : P12Facts) (hK : SolomonA12HypK K) {E L C : Subgroup K}
    (hE : GoodE E) (hL : L.Normal) (hsup : L ⊔ C = ⊤) (hLC : Disjoint L C)
    (hcomm : ∀ l ∈ L, ∀ c ∈ C, l * c = c * l) : E ≤ splitM1 E L C hcomm := by
  intro e he
  obtain ⟨l, hl, c, hc, hdec⟩ := exists_mul_eq_of_mem_sup hL hsup e
  have hlcE : l * c ∈ E := by rw [hdec]; exact he
  obtain ⟨hlE, hcE⟩ := mem_of_mul_mem_of_goodE hP hK hE hL hsup hLC hcomm hl hc hlcE
  refine ⟨l, ⟨?_, hl⟩, c, ⟨hcE, hc⟩, hdec⟩
  exact Subgroup.centralizer_le_normalizer _ (by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact hE.comm y hy.1 l hlE)

lemma splitM1_le_normalizer (hP : P12Facts) (hK : SolomonA12HypK K) {E L C : Subgroup K}
    (hE : GoodE E) (hL : L.Normal) (hsup : L ⊔ C = ⊤) (hLC : Disjoint L C)
    (hcomm : ∀ l ∈ L, ∀ c ∈ C, l * c = c * l) :
    splitM1 E L C hcomm ≤ normalizer (E : Set K) := by
  rintro x ⟨l, hl, c, hc, rfl⟩
  exact (normalizer (E : Set K)).mul_mem
    (normalizer_inf_left_le hP hK hE hL hsup hLC hcomm hl)
    (Subgroup.le_normalizer (H := E) hc.1)

lemma splitM1_normalized {E L C : Subgroup K} (hL : L.Normal) (hsup : L ⊔ C = ⊤)
    (hLC : Disjoint L C) (hcomm : ∀ l ∈ L, ∀ c ∈ C, l * c = c * l) {g : K}
    (hg : g ∈ normalizer (E : Set K)) {m : K} (hm : m ∈ splitM1 E L C hcomm) :
    g * m * g⁻¹ ∈ splitM1 E L C hcomm := by
  obtain ⟨l, hl, c, hc, rfl⟩ := hm
  obtain ⟨l₀, hl₀, c₀, hc₀, hgdec⟩ := exists_mul_eq_of_mem_sup hL hsup g
  have hconjL : ∀ x ∈ L, (l₀ * c₀) * x * (l₀ * c₀)⁻¹ = l₀ * x * l₀⁻¹ := by
    intro x hx
    have hx' : c₀ * x * c₀⁻¹ = x := by rw [← hcomm x hx c₀ hc₀]; simp
    calc (l₀ * c₀) * x * (l₀ * c₀)⁻¹ = l₀ * (c₀ * x * c₀⁻¹) * l₀⁻¹ := by group
      _ = l₀ * x * l₀⁻¹ := by rw [hx']
  have hconjC : ∀ x ∈ C, (l₀ * c₀) * x * (l₀ * c₀)⁻¹ = c₀ * x * c₀⁻¹ := by
    intro x hx
    calc (l₀ * c₀) * x * (l₀ * c₀)⁻¹ = l₀ * (c₀ * x * c₀⁻¹) * l₀⁻¹ := by group
      _ = c₀ * x * c₀⁻¹ := by
        rw [hcomm l₀ hl₀ (c₀ * x * c₀⁻¹)
          (C.mul_mem (C.mul_mem hc₀ hx) (C.inv_mem hc₀))]
        simp
  have hl₀N : l₀ ∈ normalizer ((E ⊓ L : Subgroup K) : Set K) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hgx : g * x * g⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp hg x).mp hx.1
      rw [← hgdec, hconjL x hx.2] at hgx
      exact ⟨hgx, L.mul_mem (L.mul_mem hl₀ hx.2) (L.inv_mem hl₀)⟩
    · intro hx
      have hxL : x ∈ L := by
        have heq : x = l₀⁻¹ * (l₀ * x * l₀⁻¹) * l₀ := by group
        rw [heq]
        exact L.mul_mem (L.mul_mem (L.inv_mem hl₀) hx.2) hl₀
      have hgx : g * x * g⁻¹ ∈ E := by
        rw [← hgdec, hconjL x hxL]
        exact hx.1
      have hxE : x ∈ E := by
        have hconj :=
          (Subgroup.mem_normalizer_iff.mp ((normalizer (E : Set K)).inv_mem hg)
            (g * x * g⁻¹)).mp hgx
        have heq : g⁻¹ * (g * x * g⁻¹) * (g⁻¹)⁻¹ = x := by group
        rw [heq] at hconj
        exact hconj
      exact ⟨hxE, hxL⟩
  have hc₀N : c₀ ∈ normalizer ((E ⊓ C : Subgroup K) : Set K) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hgx : g * x * g⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp hg x).mp hx.1
      rw [← hgdec, hconjC x hx.2] at hgx
      exact ⟨hgx, C.mul_mem (C.mul_mem hc₀ hx.2) (C.inv_mem hc₀)⟩
    · intro hx
      have hxC : x ∈ C := by
        have heq : x = c₀⁻¹ * (c₀ * x * c₀⁻¹) * c₀ := by group
        rw [heq]
        exact C.mul_mem (C.mul_mem (C.inv_mem hc₀) hx.2) hc₀
      have hgx : g * x * g⁻¹ ∈ E := by
        rw [← hgdec, hconjC x hxC]
        exact hx.1
      have hxE : x ∈ E := by
        have hconj :=
          (Subgroup.mem_normalizer_iff.mp ((normalizer (E : Set K)).inv_mem hg)
            (g * x * g⁻¹)).mp hgx
        have heq : g⁻¹ * (g * x * g⁻¹) * (g⁻¹)⁻¹ = x := by group
        rw [heq] at hconj
        exact hconj
      exact ⟨hxE, hxC⟩
  have hll₀N : l₀ * l * l₀⁻¹ ∈ normalizer ((E ⊓ L : Subgroup K) : Set K) :=
    (normalizer _).mul_mem ((normalizer _).mul_mem hl₀N hl.1) ((normalizer _).inv_mem hl₀N)
  have hll₀L : l₀ * l * l₀⁻¹ ∈ L := L.mul_mem (L.mul_mem hl₀ hl.2) (L.inv_mem hl₀)
  have hcc₀C : c₀ * c * c₀⁻¹ ∈ E ⊓ C := (Subgroup.mem_normalizer_iff.mp hc₀N c).mp hc
  have hconjm : g * (l * c) * g⁻¹ = (l₀ * l * l₀⁻¹) * (c₀ * c * c₀⁻¹) := by
    calc g * (l * c) * g⁻¹ = (g * l * g⁻¹) * (g * c * g⁻¹) := by group
      _ = (l₀ * l * l₀⁻¹) * (c₀ * c * c₀⁻¹) := by
        rw [← hgdec, hconjL l hl.2, hconjC c hc.2]
  rw [hconjm]
  exact ⟨l₀ * l * l₀⁻¹, ⟨hll₀N, hll₀L⟩, c₀ * c * c₀⁻¹, hcc₀C, rfl⟩

theorem eq_bot_of_split (hP : P12Facts) (hK : SolomonA12HypK K) {L C : Subgroup K}
    (hL : L.Normal) (hC : C.Normal) (hLC : Disjoint L C) (hsup : L ⊔ C = ⊤)
    (hcomm : ∀ l ∈ L, ∀ c ∈ C, l * c = c * l) (hLnc : ∃ a ∈ L, ∃ b ∈ L, a * b ≠ b * a) :
    C = ⊥ := by
  obtain ⟨E, hE⟩ := hK.exists_goodE
  have hEM1 : E ≤ splitM1 E L C hcomm := le_splitM1 hP hK hE hL hsup hLC hcomm
  have hM1N : splitM1 E L C hcomm ≤ normalizer (E : Set K) :=
    splitM1_le_normalizer hP hK hE hL hsup hLC hcomm
  have hM1norm : ∀ g ∈ normalizer (E : Set K), ∀ m ∈ splitM1 E L C hcomm,
      g * m * g⁻¹ ∈ splitM1 E L C hcomm :=
    fun _ hg _ hm => splitM1_normalized hL hsup hLC hcomm hg hm
  rcases hE.eq_or_eq hEM1 hM1N hM1norm with hM1E | hM1N
  · exfalso
    have hNl_le : normalizer ((E ⊓ L : Subgroup K) : Set K) ⊓ L ≤ E ⊓ L := by
      intro g hg
      have hgE : g ∈ E := by
        have hgM1 : g ∈ splitM1 E L C hcomm := ⟨g, hg, 1, by simp, by simp⟩
        rwa [hM1E] at hgM1
      exact ⟨hgE, hg.2⟩
    have hL_eq : L = E ⊓ L :=
      eq_of_normalizer_le hK.fusionSimple.1 hL inf_le_right (hE.isPGroup.to_le inf_le_left)
        (fun x hx y hy => hE.comm x hx.1 y hy.1)
        (fun g hgL hgnorm => hNl_le ⟨hgnorm, hgL⟩)
    obtain ⟨a, ha, b, hb, hab⟩ := hLnc
    apply hab
    rw [hL_eq] at ha hb
    exact hE.comm a ha.1 b hb.1
  · have hN : ∀ g ∈ C, g ∈ normalizer ((E ⊓ C : Subgroup K) : Set K) → g ∈ E ⊓ C := by
      intro g hgC hgnorm
      have hgN : g ∈ normalizer (E : Set K) :=
        normalizer_inf_right_le hP hK hE hL hsup hLC hcomm ⟨hgnorm, hgC⟩
      have hgM1 : g ∈ splitM1 E L C hcomm := by
        rw [hM1N]
        exact hgN
      obtain ⟨l, hl, c, hc, hdec⟩ := hgM1
      have hlC : l ∈ C := by
        have hl_eq : l = g * c⁻¹ := by rw [← hdec]; group
        rw [hl_eq]
        exact C.mul_mem hgC (C.inv_mem hc.2)
      have hlbot : l = 1 := Subgroup.disjoint_def.mp hLC hl.2 hlC
      have hgc : g = c := by rw [← hdec, hlbot, one_mul]
      rw [hgc]
      exact hc
    have hC_eq : C = E ⊓ C :=
      eq_of_normalizer_le hK.fusionSimple.1 hC inf_le_right (hE.isPGroup.to_le inf_le_left)
        (fun x hx y hy => hE.comm x hx.1 y hy.1) hN
    have hCle : C ≤ E := by rw [hC_eq]; exact inf_le_left
    exact eq_bot_of_normal_isPGroup hP hK hC (hE.isPGroup.to_le hCle)

end CFSG.EvenSporadicStandard.M12Std.SolomonK
