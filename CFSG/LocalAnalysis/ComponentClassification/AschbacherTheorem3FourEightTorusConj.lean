module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3FourEightTorus
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3SmallIndexElementary

public section

namespace CFSG.ComponentClassification.AschbacherTheorem3.FourEight

open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools
open CFSG.Open
open scoped Pointwise

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem mem_normalizer_sup {E P : Subgroup X} {d : X}
    (hdE : d ∈ Subgroup.normalizer (E : Set X)) (hdP : d ∈ Subgroup.normalizer (P : Set X)) :
    d ∈ Subgroup.normalizer ((E ⊔ P : Subgroup X) : Set X) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hdE,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hdP]

omit [Finite X] in
theorem rightConjugate_le_sup {E P T : Subgroup X} {d : X} (hTM : T ≤ E ⊔ P)
    (hdE : d ∈ Subgroup.normalizer (E : Set X)) (hdP : d ∈ Subgroup.normalizer (P : Set X)) :
    rightConjugate T d ≤ E ⊔ P := by
  have h1 := rightConjugate_le_rightConjugate hTM d
  rwa [(rightConjugate_eq_self_iff _ d).mpr (mem_normalizer_sup hdE hdP)] at h1

theorem inf_eq_bot_of_torus {G T S Q H E P L D : Subgroup X} (h : SylowFrame G T S)
    (h43 : Hyp43 G T Q H) (hab : IsMulCommutative T) (hEPS : E ⊔ P ≤ S) (hTM : T ≤ E ⊔ P)
    (hEC : E ≤ Subgroup.centralizer (P : Set X)) (hPL : P ≤ L) (hLG : L ≤ G) (hTL : T ⊓ L = ⊥)
    (hDL : D ≤ L) (hDE : D ≤ Subgroup.centralizer (E : Set X))
    (hDP : D ≤ Subgroup.normalizer (P : Set X)) (hD : D ≠ ⊥)
    (hfree : ∀ d ∈ D, ∀ p ∈ P, p ≠ 1 → d⁻¹ * p * d = p → d = 1) (hTE : ¬ T ≤ E) :
    T ⊓ E = ⊥ := by
  by_contra hne
  obtain ⟨⟨x, hxT, hxE⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hx1' : x ≠ 1 := fun h1 => hx1 (Subtype.ext h1)
  have hEN : E ≤ Subgroup.normalizer (P : Set X) :=
    hEC.trans (Subgroup.centralizer_le_normalizer _)
  have hdEN : ∀ d ∈ D, d ∈ Subgroup.normalizer (E : Set X) := fun d hd =>
    Subgroup.centralizer_le_normalizer _ (hDE hd)
  have hDT : ∀ d ∈ D, rightConjugate T d = T := by
    intro d hd
    have hdx : d⁻¹ * x * d = x := by
      have := Subgroup.mem_centralizer_iff.mp (hDE hd) x hxE
      calc d⁻¹ * x * d = d⁻¹ * (x * d) := by group
        _ = d⁻¹ * (d * x) := by rw [this]
        _ = x := by group
    have hne' : rightConjugate T 1 ⊓ rightConjugate T d ≠ ⊥ := by
      rw [rightConjugate_one]
      intro hbot
      have hmem : x ∈ T ⊓ rightConjugate T d := by
        refine ⟨hxT, ?_⟩
        rw [← hdx]
        exact conj_mem_rightConjugate hxT d
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hx1' hmem
    have hdS : rightConjugate T d ≤ S := (rightConjugate_le_sup hTM (hdEN d hd) (hDP hd)).trans hEPS
    have := rightConjugate_eq_of_inf_ne_bot h h43 hab G.one_mem (hLG (hDL hd))
      (by rw [rightConjugate_one]; exact h.le) hdS hne'
    rw [rightConjugate_one] at this
    exact this.symm
  obtain ⟨⟨d, hdD⟩, hd1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hD
  have hd1' : d ≠ 1 := fun h1 => hd1 (Subtype.ext h1)
  apply hTE
  intro t ht
  have ht' : t ∈ (E : Set X) * (P : Set X) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right E P hEN]
    exact hTM ht
  obtain ⟨e, he, p, hp, rfl⟩ := Set.mem_mul.mp ht'
  have hconj : d⁻¹ * (e * p) * d ∈ T := by
    have h1 : d⁻¹ * (e * p) * d ∈ rightConjugate T d := conj_mem_rightConjugate ht d
    rwa [hDT d hdD] at h1
  have hde : d⁻¹ * e * d = e := by
    have := Subgroup.mem_centralizer_iff.mp (hDE hdD) e he
    calc d⁻¹ * e * d = d⁻¹ * (e * d) := by group
      _ = d⁻¹ * (d * e) := by rw [this]
      _ = e := by group
  have heq : (e * p)⁻¹ * (d⁻¹ * (e * p) * d) = p⁻¹ * (d⁻¹ * p * d) := by
    calc (e * p)⁻¹ * (d⁻¹ * (e * p) * d)
        = p⁻¹ * e⁻¹ * ((d⁻¹ * e * d) * (d⁻¹ * p * d)) := by group
      _ = p⁻¹ * (d⁻¹ * p * d) := by rw [hde]; group
  have hmem : (e * p)⁻¹ * (d⁻¹ * (e * p) * d) ∈ T ⊓ L := by
    refine ⟨T.mul_mem (T.inv_mem ht) hconj, ?_⟩
    rw [heq]
    exact L.mul_mem (L.inv_mem (hPL hp)) (L.mul_mem (L.mul_mem (L.inv_mem (hDL hdD)) (hPL hp))
      (hDL hdD))
  rw [hTL, Subgroup.mem_bot, heq] at hmem
  have hfix : d⁻¹ * p * d = p := by
    calc d⁻¹ * p * d = p * (p⁻¹ * (d⁻¹ * p * d)) := by group
      _ = p := by rw [hmem, mul_one]
  have hp1 : p = 1 := by
    by_contra hp1
    exact hd1' (hfree d hdD p hp hp1 hfix)
  rw [hp1, mul_one]
  exact he

theorem exists_eq_torus {G T S Q H E P L D : Subgroup X} (h : SylowFrame G T S)
    (h43 : Hyp43 G T Q H) (hab : IsMulCommutative T) (hEPS : E ⊔ P ≤ S) (hTM : T ≤ E ⊔ P)
    (hEP : E ⊓ P = ⊥) (hEC : E ≤ Subgroup.centralizer (P : Set X)) (hPL : P ≤ L) (hLG : L ≤ G)
    (hTE : T ⊓ E = ⊥) (hcardTE : Nat.card E ≤ Nat.card T) (hDL : D ≤ L)
    (hDE : D ≤ Subgroup.centralizer (E : Set X)) (hDP : D ≤ Subgroup.normalizer (P : Set X))
    (hcardD : Nat.card P - 1 ≤ Nat.card D)
    (hfree : ∀ d ∈ D, ∀ p ∈ P, p ≠ 1 → d⁻¹ * p * d = p → d = 1) (hT : T ≠ ⊥) {x : X}
    (hx : x ∈ G) (hxM : rightConjugate T x ≤ E ⊔ P) (hxE : rightConjugate T x ⊓ E = ⊥) :
    ∃ d ∈ D, rightConjugate T x = rightConjugate T d := by
  have hF := h.toFrame
  have hTP : T ⊓ P = ⊥ := by
    rw [eq_bot_iff, ← hF.inf_eq_bot]
    exact inf_le_inf_left T (hPL.trans hLG)
  have hEN : E ≤ Subgroup.normalizer (P : Set X) :=
    hEC.trans (Subgroup.centralizer_le_normalizer _)
  obtain ⟨⟨z, hz⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (fun hbot => hT (rightConjugate_eq_bot_iff.mp hbot))
  have hz1' : z ≠ 1 := fun h1 => hz1 (Subtype.ext h1)
  have hzE : z ∉ E := by
    intro hzE
    have hmem : z ∈ rightConjugate T x ⊓ E := ⟨hz, hzE⟩
    rw [hxE, Subgroup.mem_bot] at hmem
    exact hz1' hmem
  have hzP : z ∉ P := by
    intro hzP
    have hmem : z ∈ rightConjugate T x ⊓ G := ⟨hz, hLG (hPL hzP)⟩
    rw [(hF.rightConjugate_frame hx).inf_eq_bot, Subgroup.mem_bot] at hmem
    exact hz1' hmem
  obtain ⟨d, hd, hzd⟩ := exists_mem_rightConjugate hEP hEC hTM hTP hTE hcardTE hDE hDP hcardD
    hfree (hxM hz) hzE hzP
  have hdS : rightConjugate T d ≤ S :=
    (rightConjugate_le_sup hTM (Subgroup.centralizer_le_normalizer _ (hDE hd)) (hDP hd)).trans
      hEPS
  refine ⟨d, hd, rightConjugate_eq_of_inf_ne_bot h h43 hab hx (hLG (hDL hd)) (hxM.trans hEPS)
    hdS ?_⟩
  intro hbot
  have hmem : z ∈ rightConjugate T x ⊓ rightConjugate T d := ⟨hz, hzd⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hz1' hmem

end CFSG.ComponentClassification.AschbacherTheorem3.FourEight
