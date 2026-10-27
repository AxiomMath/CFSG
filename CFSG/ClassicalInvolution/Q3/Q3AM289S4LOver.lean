module

public import CFSG.ClassicalInvolution.Q3.Q3AM289S4LFam
public import CFSG.ClassicalInvolution.Asc77.AscSPN11

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM.S4L

open QuadraticMap CFSG.ClassicalGroups.Orthogonal
  CFSG.ClassicalInvolution.Balance.StrongBalance.Orth CFSG.ClassicalInvolution.Asc77.SPN

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

theorem polarNondegOn_comap {S U : Submodule F V} (hUS : U ≤ S) (hU : PolarNondegOn Q U) :
    PolarNondegOn (Q.restrict S) (U.comap S.subtype) := by
  intro x hx hxx
  apply Subtype.ext
  have hxU : (x : V) ∈ U := hx
  refine hU x hxU (fun y hy => ?_)
  have := hxx ⟨y, hUS hy⟩ hy
  rwa [polar_restrict] at this

theorem comap_sup_eq_top {S U N M : Submodule F V} (hUS : U ≤ S) (hNS : N ≤ S) (hMS : M ≤ S)
    (htop : U ⊔ N ⊔ M = S) :
    U.comap S.subtype ⊔ N.comap S.subtype ⊔ M.comap S.subtype = ⊤ := by
  apply Submodule.map_injective_of_injective S.injective_subtype
  rw [Submodule.map_sup, Submodule.map_sup, Submodule.map_comap_subtype,
    Submodule.map_comap_subtype, Submodule.map_comap_subtype, inf_of_le_right hUS,
    inf_of_le_right hNS, inf_of_le_right hMS, htop, Submodule.map_subtype_top]

theorem comap_sup_of_le {S U N : Submodule F V} (hUS : U ≤ S) (hNS : N ≤ S) :
    (U ⊔ N).comap S.subtype = U.comap S.subtype ⊔ N.comap S.subtype := by
  apply Submodule.map_injective_of_injective S.injective_subtype
  rw [Submodule.map_sup, Submodule.map_comap_subtype, Submodule.map_comap_subtype,
    Submodule.map_comap_subtype, inf_of_le_right hUS, inf_of_le_right hNS,
    inf_of_le_right (sup_le hUS hNS)]

theorem elemOn_mono_S4L {S S' : Submodule F V} (h : S ≤ S') : elemOn Q S ≤ elemOn Q S' := by
  rw [elemOn, Subgroup.closure_le]
  rintro _ ⟨u, w, hu, hw, -, -, rfl⟩
  exact eichler_mem_elemOn (h hu) (h hw)

theorem elemOn_le_of_overlap_sub [Finite F] [FiniteDimensional F V] (hodd : Odd (Nat.card F))
    {S U N M : Submodule F V} (hS : PolarNondegOn Q S) (hUS : U ≤ S) (hNS : N ≤ S) (hMS : M ≤ S)
    (hU : PolarNondegOn Q U) (h3 : 3 ≤ Module.finrank F U)
    (hUN : ∀ x ∈ U, ∀ y ∈ N, polar Q x y = 0) (hUM : ∀ x ∈ U, ∀ y ∈ M, polar Q x y = 0)
    (hNM : ∀ x ∈ N, ∀ y ∈ M, polar Q x y = 0) (hN : PolarNondegOn Q N) (hM : PolarNondegOn Q M)
    (hN0 : N ≠ ⊥) (hM0 : M ≠ ⊥)
    (hdim : 2 ≤ Module.finrank F N ∨ 2 ≤ Module.finrank F M) (htop : U ⊔ N ⊔ M = S)
    {H : Subgroup (V ≃ₗ[F] V)} (hH₁ : elemOn Q (U ⊔ N) ≤ H) (hH₂ : elemOn Q (N ⊔ M) ≤ H) :
    elemOn Q S ≤ H := by
  classical
  set H' : Subgroup (S ≃ₗ[F] S) := (H.comap (elemOn Q S).subtype).map (resHom Q S) with hH'
  have hQS := nondegenerate_polarBilin_restrict hS
  have key : ∀ T : Submodule F V, T ≤ S → elemOn Q T ≤ H →
      elemOn (Q.restrict S) (T.comap S.subtype) ≤ H' := by
    intro T hTS hT
    rw [elemOn, Subgroup.closure_le]
    rintro _ ⟨u, w, hu, hw, hQu, hpol, rfl⟩
    have huT : (u : V) ∈ T := hu
    have hwT : (w : V) ∈ T := hw
    have hmem : eichler Q (u : V) (w : V) ∈ elemOn Q S := eichler_mem_elemOn u.2 w.2
    refine ⟨⟨eichler Q (u : V) (w : V), hmem⟩, hT (eichler_mem_elemOn huT hwT), ?_⟩
    exact resAux_eichler (Q := Q) u.2 w.2
  have hmain : elementaryGroup (Q.restrict S) ≤ H' := by
    refine elementaryGroup_le_of_overlap (V := S) (Q := Q.restrict S) hodd hQS
      (U := U.comap S.subtype) (N := N.comap S.subtype) (M := M.comap S.subtype)
      (polarNondegOn_comap hUS hU) (by rwa [(Submodule.comapSubtypeEquivOfLe hUS).finrank_eq])
      ?_ ?_ ?_ (polarNondegOn_comap hNS hN) (polarNondegOn_comap hMS hM) ?_ ?_ ?_
      (comap_sup_eq_top hUS hNS hMS htop) ?_ ?_ ?_
    · intro x hx y hy
      rw [polar_restrict]; exact hUN x hx y hy
    · intro x hx y hy
      rw [polar_restrict]; exact hUM x hx y hy
    · intro x hx y hy
      rw [polar_restrict]; exact hNM x hx y hy
    · intro h0
      apply hN0
      rw [eq_bot_iff] at h0 ⊢
      intro x hx
      have := h0 (show (⟨x, hNS hx⟩ : S) ∈ N.comap S.subtype from hx)
      simpa using congrArg Subtype.val ((Submodule.mem_bot F).mp this)
    · intro h0
      apply hM0
      rw [eq_bot_iff] at h0 ⊢
      intro x hx
      have := h0 (show (⟨x, hMS hx⟩ : S) ∈ M.comap S.subtype from hx)
      simpa using congrArg Subtype.val ((Submodule.mem_bot F).mp this)
    · rwa [(Submodule.comapSubtypeEquivOfLe hNS).finrank_eq,
        (Submodule.comapSubtypeEquivOfLe hMS).finrank_eq]
    · rintro _ ⟨h, -, rfl⟩
      exact elementaryGroup_le_orthogonalGroup _ (resHom_mem_elementaryGroup h)
    · rw [← comap_sup_of_le hUS hNS]; exact key _ (sup_le hUS hNS) hH₁
    · rw [← comap_sup_of_le hNS hMS]; exact key _ (sup_le hNS hMS) hH₂
  intro g hg
  obtain ⟨h, hh, hhg⟩ := hmain (resHom_mem_elementaryGroup (⟨g, hg⟩ : elemOn Q S))
  have : h = ⟨g, hg⟩ := resHom_injective hQS hhg
  rw [this] at hh
  exact hh

variable [Finite F] [FiniteDimensional F V] {w : Fin 6 → V}

theorem elemOn_Sp_univ_le (hodd : Odd (Nat.card F)) (hw : IsON Q w) {H : Subgroup (V ≃ₗ[F] V)}
    (h₁ : elemOn Q (Sp w F {0, 1, 2, 3}) ≤ H) (h₂ : elemOn Q (Sp w F {2, 3, 4, 5}) ≤ H) :
    elemOn Q (Sp w F Finset.univ) ≤ H := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd hodd
  have hU := polarNondegOn_Sp hw h2 ({0, 1, 3} : Finset (Fin 6))
  have hN := polarNondegOn_Sp hw h2 ({2} : Finset (Fin 6))
  have hM := polarNondegOn_Sp hw h2 ({4, 5} : Finset (Fin 6))
  have hUN : Sp w F {0, 1, 3} ⊔ Sp w F {2} = Sp w F {0, 1, 2, 3} := by
    rw [Sp_sup, show ({0, 1, 3} ∪ {2} : Finset (Fin 6)) = {0, 1, 2, 3} from by decide]
  have hNM : Sp w F {2} ⊔ Sp w F {4, 5} ≤ Sp w F {2, 3, 4, 5} := by
    rw [Sp_sup]; exact Sp_mono (by decide)
  have htop : Sp w F {0, 1, 3} ⊔ Sp w F {2} ⊔ Sp w F {4, 5} = Sp w F Finset.univ := by
    rw [Sp_sup, Sp_sup,
      show ({0, 1, 3} ∪ {2} ∪ {4, 5} : Finset (Fin 6)) = Finset.univ from by decide]
  refine elemOn_le_of_overlap_sub hodd (polarNondegOn_Sp hw h2 Finset.univ) ?_ ?_ ?_ hU ?_
    ?_ ?_ ?_ hN hM ?_ ?_ ?_ htop ?_ ?_
  · exact Sp_mono (by decide)
  · exact Sp_mono (by decide)
  · exact Sp_mono (by decide)
  · rw [finrank_Sp hw h2]; decide
  · exact fun x hx y hy => polar_Sp_Sp hw (by decide) hx hy
  · exact fun x hx y hy => polar_Sp_Sp hw (by decide) hx hy
  · exact fun x hx y hy => polar_Sp_Sp hw (by decide) hx hy
  · intro h
    have := finrank_Sp hw h2 ({2} : Finset (Fin 6))
    rw [h, finrank_bot] at this
    simp at this
  · intro h
    have := finrank_Sp hw h2 ({4, 5} : Finset (Fin 6))
    rw [h, finrank_bot] at this
    simp at this
  · right
    rw [finrank_Sp hw h2]; decide
  · rw [hUN]; exact h₁
  · exact (elemOn_mono_S4L hNM).trans h₂

theorem elementaryGroup_le_of_pairs (hodd : Odd (Nat.card F)) (hQ : (polarBilin Q).Nondegenerate)
    (hdim : 7 ≤ Module.finrank F V) (hw : IsON Q w) {H : Subgroup (V ≃ₗ[F] V)}
    (hHO : H ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (h₁ : elemOn Q (Sp w F {0, 1, 2, 3}) ≤ H) (h₂ : elemOn Q (Sp w F {2, 3, 4, 5}) ≤ H)
    (h₃ : elemOn Q (Sp w F {4, 5} ⊔ Cmp w Q) ≤ H) : elementaryGroup Q ≤ H := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd hodd
  have hUN : Sp w F {0, 1, 2, 3} ⊔ Sp w F {4, 5} = Sp w F Finset.univ := by
    rw [Sp_sup, show ({0, 1, 2, 3} ∪ {4, 5} : Finset (Fin 6)) = Finset.univ from by decide]
  have horth : ∀ s : Finset (Fin 6), ∀ x ∈ Sp w F s, ∀ y ∈ Cmp w Q, polar Q x y = 0 :=
    fun s x hx y hy => by
      rw [polar_comm]
      exact (mem_Cmp_iff.mp hy) x (Sp_mono (Finset.subset_univ s) hx)
  refine elementaryGroup_le_of_overlap hodd hQ (U := Sp w F {0, 1, 2, 3})
    (N := Sp w F {4, 5}) (M := Cmp w Q) (polarNondegOn_Sp hw h2 _) ?_
    (fun x hx y hy => polar_Sp_Sp hw (by decide) hx hy) (horth _) (horth _)
    (polarNondegOn_Sp hw h2 _) (polarNondegOn_Cmp hw h2 hQ) ?_ (Cmp_ne_bot hw h2 (by omega))
    (Or.inl ?_) ?_ hHO ?_ h₃
  · rw [finrank_Sp hw h2]; decide
  · intro h
    have := finrank_Sp hw h2 ({4, 5} : Finset (Fin 6))
    rw [h, finrank_bot] at this
    simp at this
  · rw [finrank_Sp hw h2]; decide
  · rw [hUN]; exact (isCompl_Cmp hw h2).sup_eq_top
  · rw [hUN]; exact elemOn_Sp_univ_le hodd hw h₁ h₂

end CFSG.ClassicalInvolution.Q3.Q3AM.S4L
