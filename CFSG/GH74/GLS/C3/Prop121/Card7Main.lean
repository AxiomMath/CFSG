module

public import CFSG.GH74.GLS.C3.Prop121.Rec7
public import CFSG.GH74.GLS.C3.Prop121.Card7Abs12
public import CFSG.GH74.GLS.C3.Prop121.Card7Main1
public import CFSG.GH74.GLS.C3.Prop121.Card7Lab

public section

namespace CFSG.GH74.GLS.C3.Prop121.Card7

open Subgroup Equiv Perm CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model
  CFSG.GH74.GLS.Layer3

variable {G : Type} [Group G] [Finite G]

theorem card_centralizer_t
    (hF : FFacts) (hH : HFacts) (hSyl : SylFacts) (hC : pRank 2 G ≤ 4) {x : G}
    {K T Q S : Subgroup G} {a : G} (h : IsAConfig 7 x K T Q S a)
    (hap : IsApproxTo G (alternatingGroup (Fin (7 + 4)))) {t u g : G}
    (hS : Stage3Loc 7 x K Q t u g) :
    Nat.card ↥(centralizer ({t} : Set G)) = 60480 := by
  classical
  have hn : (7 : ℕ) = 5 ∨ (7 : ℕ) = 6 ∨ (7 : ℕ) = 7 := Or.inr (Or.inr rfl)
  have hG4 : pRank 2 G ≤ 4 := hC
  obtain ⟨ι, hι1, hι2⟩ := exists_coord hn hG4 h
  have hCQ := centralizer_Q_eq hn hG4 h (fnFacts 7 hn)
  have hKC : K ≤ centralizer ({x} : Set G) := h.K_le_C
  have hmem : g * t * g⁻¹ ∈ centralizer ({x} : Set G) := hKC hS.gt_K
  have h3 := lemma122_seven h hS ι hι2 hCQ hmem
  have hx2 : orderOf x = 2 := orderOf_eq_prime h.x_sq h.x_ne_one
  have ht3 : t ^ 3 = 1 := by
    have := pow_orderOf_eq_one t
    rwa [hS.t_order] at this
  have hsK : g * t * g⁻¹ ∈ K := hS.gt_K
  have hs3 : (g * t * g⁻¹) ^ 3 = 1 := by
    have : (g * t * g⁻¹) ^ 3 = g * t ^ 3 * g⁻¹ := conj_pow
    rw [this, ht3]; group
  set f' : F7 := ι ⟨g * t * g⁻¹, hmem⟩ with hf'
  have hf'2 : ((f' : F7) : Amb 7).2 = 1 := ((K_iff hn h hι2 ⟨g * t * g⁻¹, hmem⟩).1 hsK).2
  have hf'3 : f' ^ 3 = 1 := by
    have : (⟨g * t * g⁻¹, hmem⟩ : ↥(centralizer ({x} : Set G))) ^ 3 = 1 :=
      Subtype.ext (by simpa using hs3)
    rw [hf', ← map_pow, this, map_one]
  have hf'ty3 : Ty3 f' :=
    ⟨hf'2, hf'3, by rw [numMoved_eq_card_support]; exact h3.card_support⟩
  obtain ⟨k, hk⟩ := hF.conj3 f' hf'ty3
  have hcx : Nat.card ↥(centralizer ({x} : Set G)) = 4 * Nat.factorial 7 := by
    rw [Nat.card_congr ι.toEquiv, card_Fgrp]
  have pf : PatternFacts G 7 := patternFacts_of_approx hn hap
  obtain ⟨SS, hSS⟩ := h.sylowS.isPGroup.exists_le_sylow
  have hSeq : S = (SS : Subgroup G) := (h.sylowS.eq_of_le hSS le_top SS.isPGroup').symm
  have hcount := count_xtype hSyl hap x hx2 hcx SS
  rw [← hSeq] at hcount
  obtain ⟨QT, hQT⟩ := h.sylowT
  have hzK : g * x * g⁻¹ ∈ K := hS.g_Q x hS.x_mem
  set z : ↥(centralizer ({x} : Set G)) := ⟨g * x * g⁻¹, hKC hzK⟩ with hz
  have hz2 : orderOf (z : G) = 2 := by
    show orderOf (g * x * g⁻¹) = 2
    rw [show g * x * g⁻¹ = MulAut.conj g x from rfl, MulEquiv.orderOf_eq]; exact hx2
  have hzx : IsConj x (z : G) := isConj_iff.2 ⟨g, rfl⟩
  have hz1 : ((ι z : F7) : Amb 7).2 = 1 := ((K_iff hn h hι2 z).1 hzK).2
  have hlab := lab_abstract hF x hx2 ι pf z hz2 hzx hz1 S T h.T_lt_S.le QT hQT hcount
  have hap' : IsApproxTo G A11 := hap
  have h8 : (8 : ℕ) ≤ 11 := by norm_num
  obtain ⟨hab, hcl⟩ := PatternAux.altX_altY_classes (N := 11) h8 le_rfl
  obtain ⟨x', y0, hx', hy0, hxy', hclG, ⟨e1⟩, ⟨e2⟩⟩ :=
    pattern_two_classes hap'.1 (orderOf_altX h8) (orderOf_altY h8) hab hcl
  have hcy0 : Nat.card ↥(centralizer ({y0} : Set G)) = 1152 := by
    rw [Nat.card_congr e2.toEquiv]; exact card_cent_altY11
  have hxx' : IsConj x' x := by
    rcases hclG x hx2 with h' | h'
    · exact h'
    · exfalso
      have := card_centralizer_eq_of_isConj h'
      rw [hcy0, hcx] at this
      norm_num [Nat.factorial] at this
  let ι' : ↥(centralizer ({x} : Set G)) ≃* F7 := ι.trans (MulAut.conj k)
  have hι'app : ∀ c, ι' c = k * ι c * k⁻¹ := fun c => rfl
  have hx0c : k * x0F = x0F * k := Subtype.ext (x0_central 7 k.2)
  have hι'x : ι' ⟨x, mem_centralizer_singleton_iff.2 rfl⟩ = x0F := by
    rw [hι'app]
    have h1 : ι ⟨x, mem_centralizer_singleton_iff.2 rfl⟩ = x0F := Subtype.ext hι1
    rw [h1, hx0c]; group
  have hι's : ι' ⟨g * t * g⁻¹, hmem⟩ = f0 := by rw [hι'app, ← hf']; exact hk
  have hlab' : ∀ c : ↥(centralizer ({x} : Set G)), orderOf c = 2 →
      (IsConj (c : G) x ↔ nm7 ((ι' c : F7) : Amb 7) = 4) := by
    intro c hc
    rw [hι'app, nm7_conj]
    exact hlab c hc
  let C : Ctx G :=
    { x := x, hx := hx2, ι := ι', hιx := hι'x, y0 := y0, hy0 := hy0
      hxy0 := fun hc => hxy' (hxx'.trans hc)
      hcl := fun w hw => (hclG w hw).elim (fun h' => Or.inl (hxx'.symm.trans h')) Or.inr
      Ψ0 := e2, lab := hlab', s := g * t * g⁻¹, hs := hmem, hsF := hι's }
  have hcard := C.card_centralizer_s hF hH
  have hconj : IsConj t (g * t * g⁻¹) := isConj_iff.2 ⟨g, rfl⟩
  rw [card_centralizer_eq_of_isConj hconj]
  exact hcard

theorem s_card7_of_facts
    (hF : FFacts) (hH : HFacts) (hSyl : SylFacts) : S_card7 := by
  intro G _ _ hC x K T Q S a h hap t u g hS
  exact card_centralizer_t hF hH hSyl hC h hap hS

end CFSG.GH74.GLS.C3.Prop121.Card7
