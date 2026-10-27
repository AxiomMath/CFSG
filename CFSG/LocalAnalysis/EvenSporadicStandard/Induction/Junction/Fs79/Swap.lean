module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Diag.Link
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Links
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Stage3Defs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Fusion
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ComponentOrder
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.General

public section

namespace CFSG.EvenSporadicStandard.Induction.Junction

open Subgroup CFSG.EvenSporadicStandard.Induction CFSG.EvenSporadicStandard.Solomon78
  CFSG.EvenSporadicStandard.HSStd CFSG.EvenSporadicStandard.HSStd.Zassenhaus

variable {H : Type} [Group H]

theorem isCompIn_eq_of_le [Finite H] {X B Y : Subgroup H} (hX : IsCompIn X Y) (hB : IsCompIn B Y)
    (hXB : X ≤ B) : X = B := by
  by_contra hne
  exact not_forall_commute_of_isQuasisimple hX.isQuasisimple fun a ha b hb =>
    hX.commute_of_ne hB hne a ha b (hXB hb)

theorem mem_normalizer_zpowers_of_commute {s t : H} (hst : s * t = t * s) :
    s ∈ normalizer ((zpowers t : Subgroup H) : Set H) := by
  refine Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun g hg => ?_)
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
  exact (Commute.zpow_left (show Commute t s from hst.symm) k).eq

theorem ltF_links_swap [Finite H] {A B : Subgroup H} {s t : H} (hs : orderOf s = 2)
    (ht : orderOf t = 2) (hst : s * t = t * s)
    (hA : IsCompIn A (centralizer ({s} : Set H))) (hB : IsCompIn B (centralizer ({t} : Set H)))
    (hAB : A ≤ B ⊔ B.map (MulAut.conj s).toMonoidHom)
    (hne : B.map (MulAut.conj s).toMonoidHom ≠ B) :
    Sol78Links H 1 (fun i => if i = 0 then A else B)
      (fun i => if i = 0 then zpowers t ⊔ zpowers s else zpowers t) (fun _ => s) := by
  have hss : s * s = 1 := Solomon78.mul_self_eq_one_of_orderOf_eq_two hs
  have hs2 : IsPGroup 2 ↥(zpowers s) := isPGroup_zpowers_of_orderOf_two hs
  have ht2 : IsPGroup 2 ↥(zpowers t) := isPGroup_zpowers_of_orderOf_two ht
  have hsN : s ∈ normalizer ((zpowers t : Subgroup H) : Set H) :=
    mem_normalizer_zpowers_of_commute hst
  have hsT : s ^ 2 ∈ zpowers t := by
    rw [pow_two, hss]
    exact one_mem _
  have hT0 : IsPGroup 2 ↥(zpowers t ⊔ zpowers s) := isPGroup_sup_zpowers ht2 hsN hsT
  have hB' : IsCompIn B (centralizer ((zpowers t : Subgroup H) : Set H)) := by
    rw [centralizer_zpowers_eq]
    exact hB
  have hAt : A ≤ centralizer ({t} : Set H) := by
    refine hAB.trans (sup_le hB.1 ?_)
    exact (isCompIn_conj_of_commute hst hB).1
  have hAst : IsCompIn A (centralizer ((zpowers t ⊔ zpowers s : Subgroup H) : Set H)) := by
    rw [centralizer_sup_zpowers_eq]
    exact isCompIn_of_le hA (le_inf hAt hA.1) inf_le_right
  have hd : DiagData (zpowers t) (zpowers s) ⊥ B A s := by
    refine ⟨?_, bot_le, Subgroup.mem_zpowers s, ?_, ?_, ?_, ?_, hB', ?_, ?_, ?_⟩
    · exact (zpowers_le.2 hsN)
    · intro h
      have : s = 1 := Subgroup.mem_bot.1 h
      rw [this, orderOf_one] at hs
      omega
    · rw [pow_two, hss]
      exact one_mem _
    · intro g _ u hu
      rw [Subgroup.mem_bot.1 hu]
      simp
    · intro g hg
      rcases mem_zpowers_cases_of_orderOf_two hs hg with h | h
      · exact Or.inl (h ▸ one_mem _)
      · exact Or.inr (by rw [h]; simp)
    · intro g hg hgN
      rcases mem_zpowers_cases_of_orderOf_two hs hg with h | h
      · exact h ▸ one_mem _
      · exfalso
        rw [h] at hgN
        exact hne (Solomon78.mem_normalizer_iff_map_conj_eq.1 hgN)
    · rw [sup_comm]
      exact hAst
    · exact hAB.trans (sup_le (le_conjClosure B _)
        (map_conj_le_conjClosure (Subgroup.mem_zpowers s)))
  obtain ⟨X, hX, hXne, hKX, hlayer, ⟨e⟩, hXle⟩ := diag_step hd
  rw [bot_sup_eq] at hX hlayer
  rw [conjClosure_of_le_normalizer (bot_le : (⊥ : Subgroup H) ≤ normalizer (B : Set H))] at hXle
  have hXB : X = B := isCompIn_eq_of_le hX hB' hXle
  subst hXB
  exact Sol78Links.single hT0 ht2 hAst hB' hs2 hsN hsT hAst hAB hlayer (Or.inl ⟨hXne, ⟨e⟩⟩)
