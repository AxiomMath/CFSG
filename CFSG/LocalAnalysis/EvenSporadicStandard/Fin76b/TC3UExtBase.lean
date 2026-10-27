
module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC3UData
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43ModelBase

@[expose] public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Certificates CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative CFSG.LieType.Multipliers.U43
  CFSG.EvenSporadicStandard.M24Std.CU43

theorem rep_rhoArr : Rep 820 rhoArr rhoPerm := fun i => by
  rw [rhoArr, getElem!_ofFn_nat _ i.2]
  exact (rhoPerm_apply i).symm

theorem rhoOK_spec (h : rhoOK = true) :
    rhoPerm ∈ normalizer (P : Set (Equiv.Perm (Fin 820))) ∧ rhoPerm * rhoPerm ∈ P := by
  simp only [rhoOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hinv, h1⟩, h2⟩, h3⟩ := h
  have hρi : Rep 820 (invCand 820 rhoArr) rhoPerm⁻¹ := rep_inv_of_isInvA rep_rhoArr hinv
  have e1 := (inP_iff (rep_compA rep_rhoArr (rep_compA rep_tabA hρi))).1 h1
  have e2 := (inP_iff (rep_compA rep_rhoArr (rep_compA rep_tabB hρi))).1 h2
  rw [← mul_assoc] at e1 e2
  exact ⟨mem_normalizer_P_of_gens e1 e2, (inP_iff (rep_compA rep_rhoArr rep_rhoArr)).1 h3⟩

@[expose] def extSub (hn : rhoPerm ∈ normalizer (P : Set (Equiv.Perm (Fin 820))))
    (h2 : rhoPerm * rhoPerm ∈ P) : Subgroup (Equiv.Perm (Fin 820)) where
  carrier := {x | x ∈ P ∨ ∃ g ∈ P, x = g * rhoPerm}
  one_mem' := Or.inl P.one_mem
  mul_mem' := by
    have hc : ∀ b ∈ P, rhoPerm * b * rhoPerm⁻¹ ∈ P := fun b hb =>
      (mem_normalizer_iff.1 hn b).1 hb
    rintro x y (hx | ⟨a, ha, rfl⟩) (hy | ⟨b, hb, rfl⟩)
    · exact Or.inl (P.mul_mem hx hy)
    · exact Or.inr ⟨x * b, P.mul_mem hx hb, by rw [mul_assoc]⟩
    · refine Or.inr ⟨a * (rhoPerm * y * rhoPerm⁻¹), P.mul_mem ha (hc y hy), by group⟩
    · refine Or.inl ?_
      have : a * rhoPerm * (b * rhoPerm) = a * (rhoPerm * b * rhoPerm⁻¹) * (rhoPerm * rhoPerm) := by
        group
      rw [this]
      exact P.mul_mem (P.mul_mem ha (hc b hb)) h2
  inv_mem' := by
    have hc' : ∀ b ∈ P, rhoPerm⁻¹ * b * rhoPerm ∈ P := fun b hb => by
      have := (mem_normalizer_iff.1 ((normalizer (P : Set (Equiv.Perm (Fin 820)))).inv_mem hn)
        b).1 hb
      simpa using this
    rintro x (hx | ⟨a, ha, rfl⟩)
    · exact Or.inl (P.inv_mem hx)
    · refine Or.inr ⟨(rhoPerm⁻¹ * a⁻¹ * rhoPerm) * (rhoPerm * rhoPerm)⁻¹,
        P.mul_mem (hc' _ (P.inv_mem ha)) (P.inv_mem h2), by group⟩

theorem baseFaithful_P : BaseFaithful P baseArr.toList := by
  have hQb : Q.base.toList.map Fin.val = baseArr.toList := rfl
  rw [← hQb]
  exact baseFaithful_of_valid (validSchreier_of_chainOK chainArrays (by norm_num) chain_check).1

theorem bad16_iff {v : List (Array ℕ)}
    {x : Equiv.Perm (Fin 820)} (hv : RepW 820 v x) (h16 : x ^ 16 ∈ P) (h8 : x ^ 8 ∈ P) :
    bad16 v = true ↔ x ^ 16 = 1 ∧ x ^ 8 ≠ 1 := by
  have hbs : ∀ b ∈ baseArr.toList, b < 820 := by
    have hQb : Q.base.toList.map Fin.val = baseArr.toList := rfl
    rw [← hQb]
    intro b hb
    obtain ⟨y, -, rfl⟩ := List.mem_map.1 hb
    exact y.2
  have key : ∀ e : ℕ, x ^ e ∈ P → (fixB baseArr.toList v e = true ↔ x ^ e = 1) := by
    intro e he
    rw [fixB_iff hbs hv e]
    constructor
    · exact baseFaithful_P _ he
    · intro h y _
      rw [h]
      rfl
  unfold bad16
  constructor
  · intro h
    rw [Bool.and_eq_true] at h
    obtain ⟨h16', h8'⟩ := h
    refine ⟨(key 16 h16).1 h16', fun h8'' => ?_⟩
    rw [(key 8 h8).2 h8''] at h8'
    exact absurd h8' (by decide)
  · rintro ⟨h16', h8'⟩
    rw [Bool.and_eq_true]
    refine ⟨(key 16 h16).2 h16', ?_⟩
    cases hb : fixB baseArr.toList v 8
    · rfl
    · exact absurd ((key 8 h8).1 hb) h8'

end CFSG.EvenSporadicStandard.Fin76b
