module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.Simple
public import CFSG.GH74.Uniqueness.SU.SU13Stmts
public import CFSG.GH74.Uniqueness.SU.SU12Basic

public section

namespace CFSG.GH74.Uniqueness.SU.SU12

open Subgroup CFSG.GH74 CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine

section Bridge

theorem isTwoAlt_of_isTwoANine {J : Type} [Group J] [Finite J] (h : IsTwoANine J) :
    K.IsTwoAlt J 9 := by
  obtain ⟨hperf, hc, ⟨e⟩⟩ := h
  have hs : IsSimpleGroup (alternatingGroup (Fin 9)) := alternatingGroup.isSimpleGroup (by simp)
  have hnab : ∃ a b : alternatingGroup (Fin 9), a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have hc' : IsMulCommutative (alternatingGroup (Fin 9)) := ⟨⟨fun a b => hcon a b⟩⟩
    have h3 := alternatingGroup.isMulCommutative_iff_card_le_three.1 hc'
    rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h3
    omega
  obtain ⟨a, b, hab⟩ := hnab
  exact ⟨⟨hperf, (MulEquiv.isSimpleGroup_congr e).mpr hs,
    e.symm a, e.symm b, fun h => hab (e.symm.injective (by rw [map_mul, map_mul]; exact h))⟩,
    ‹Finite J›, hc, ⟨e⟩⟩

theorem isTwoANine_of_isTwoAlt {J : Type} [Group J] (h : K.IsTwoAlt J 9) : IsTwoANine J := by
  obtain ⟨⟨hperf, -⟩, -, hc, he⟩ := h
  exact ⟨hperf, hc, he⟩

end Bridge

theorem isolatedFor_of_thm231 (h231 : SU13.Thm231Stmt) :
    ∀ (X : Type) [Group X] [Finite X], IsolatedFor X := by
  suffices h : ∀ n : ℕ, ∀ (X : Type) [Group X] [Finite X], Nat.card X = n → IsolatedFor X from
    fun X _ _ => h _ X rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro X _ _ hX S t ht hJ g hg
    by_contra hgt
    by_cases hO : CFSG.pPrimeCore 2 X = ⊥
    · have hMC : MinimalCounterexample X S t :=
        ⟨ht, hJ, ⟨g, hg, hgt⟩, hO, fun H hH => by
          have hlt : Nat.card H < n := by
            rw [← hX, ← Subgroup.card_top (G := X)]
            exact Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hH)
          exact ih _ hlt H rfl⟩
      have hsimple : IsSimpleGroup X := hMC.isSimpleGroup
      have hnab : ∃ a b : X, a * b ≠ b * a := ⟨t, g, fun h => hgt (by
        rw [mul_assoc, h, inv_mul_cancel_left])⟩
      exact h231 X hsimple hnab t ht.2.1 9 (Or.inl rfl)
        (isTwoAlt_of_isTwoANine hMC.isTwoANine_centralizer)
    · refine hgt (conj_eq_of_quotient odd_card_pPrimeCore_two S ht hJ ?_ g hg)
      have hlt : Nat.card (X ⧸ CFSG.pPrimeCore 2 X) < n := by
        rw [← hX]
        exact card_quotient_lt hO
      exact ih _ hlt (X ⧸ CFSG.pPrimeCore 2 X) rfl

theorem false_of_isolatedFor {G : Type} [Group G] [Finite G] (hT9 : IsolatedFor G)
    {S : Sylow 2 G} {M : Subgroup G} {z : G} (h : Hyp22 S M z) : False := by
  obtain ⟨g, hne, hgS⟩ := SU10.exists_conj_mem_sylow_ne h.simple h.nonab S h.z_invol h.z_center
  have hJ : IsTwoANine (CFSG.ProperTwoGeneratedCore.Assembly.EscapingQuotient z) :=
    isTwoANine_of_isTwoAlt h.shape.1
  have := hT9 S z ⟨h.z_mem, h.z_invol, h.z_center⟩ hJ g⁻¹ (by simpa using hgS)
  exact hne (by simpa using this)

theorem hyp22_false_of_thm231 (h231 : SU13.Thm231Stmt) {G : Type} [Group G] [Finite G]
    {S : Sylow 2 G} {M : Subgroup G} {z : G} (h : Hyp22 S M z) : False :=
  false_of_isolatedFor (isolatedFor_of_thm231 h231 G) h

theorem prop221_of_thm231 (h231 : SU13.Thm231Stmt) : Prop221Stmt :=
  fun _ _ _ _ _ _ h => (hyp22_false_of_thm231 h231 h).elim

end CFSG.GH74.Uniqueness.SU.SU12
