module

public import CFSG.GH74.GLS.Stage2.Final.Thm4.L193B
public import CFSG.GH74.GLS.Stage2.Final.Thm4.L193Four
public import CFSG.GH74.GLS.Stage2.Final.Thm4.Stmt18
public import CFSG.GH74.GLS.Stage2.Final.Thm4.Basic
public import CFSG.GH74.GLS.Stage2.Final.Thm4.Closed
public import CFSG.GH74.GLS.Stage2.Final.Thm4.Stmt19

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm4

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Final.Thm4.L193
open scoped commutatorElement

theorem ab_of_ctx19 (h1813 : Prop18_13) {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S : Subgroup G}
    {p : ℕ} {U : Subgroup G} {t : G} (h : Ctx19 G z k S (Cen z) p U t) : ∃ g : G, Ab G z t g p := by
  have hctx17 : Ctx17 G z k S (Cen z) := h.base.base.ctx
  have hctx : Stage2Ctx G z k S := hctx17.ctx
  have hz2 : z * z = 1 := by
    have := hctx.orderOf_z
    calc z * z = z ^ 2 := (sq z).symm
      _ = 1 := by rw [← this]; exact pow_orderOf_eq_one z
  obtain ⟨c, hc⟩ := isConj_iff.mp h.t_conj
  have hcoat : IsCoatom (Cen z) := hctx17.mem.1
  have ht2 : t * t = 1 := by
    rw [← hc]
    calc c * z * c⁻¹ * (c * z * c⁻¹) = c * (z * z) * c⁻¹ := by group
      _ = 1 := by rw [hz2]; group
  have htM : t ∈ Cen z := hctx17.S_le h.t_mem
  have hsimple : ∀ N : Subgroup G, N.Normal → N = ⊥ ∨ N = ⊤ := fun N _ =>
    hctx.std.kps.1.eq_bot_or_eq_top_of_normal N
  have hFle : ∀ U' : Subgroup G, Fof p (Cen z) U' ≤ Cen z := fun U' =>
    sup_le ((inf_le_left : Qof p (Cen z) U' ≤ Op p (Cen z)).trans (Subgroup.map_subtype_le _))
      (iSup₂_le fun r _ => (Subgroup.map_subtype_le _).trans (Subgroup.map_subtype_le _))
  have hnG : ∀ U' : Subgroup G, U' ≤ Op p (Cen z) → (U'.subgroupOf (Op p (Cen z))).Normal →
      IsElementaryAbelian p ↥U' → Nat.card ↥U' = p ^ 2 → ∀ X : Subgroup G, X ≤ Fof p (Cen z) U' → X ≠ ⊥ →
        (∃ r : ℕ, r.Prime ∧ IsElementaryAbelian r ↥X) → normalizer (X : Set G) ≤ Cen z := by
    intro U' hle hn hel hc X hXF hXne hXel
    rcases IsCoatomic.eq_top_or_exists_le_coatom (normalizer (X : Set G)) with htop | ⟨H, hH, hXH⟩
    · exfalso
      have hXn : X.Normal := Subgroup.normalizer_eq_top_iff.mp htop
      rcases hsimple X hXn with hb | ht
      · exact hXne hb
      · have : (⊤ : Subgroup G) ≤ Cen z := by rw [← ht]; exact hXF.trans (hFle U')
        exact hcoat.1 (top_le_iff.mp this)
    · have := h1813 G z k S (Cen z) p h.base U' hle hn hel hc H hH (Or.inl ⟨X, hXF, hXne, hXel, hXH⟩)
      exact this ▸ hXH
  have hb : ∀ U' : Subgroup G, U' ≤ Op p (Cen z) → (U'.subgroupOf (Op p (Cen z))).Normal →
      IsElementaryAbelian p ↥U' → Nat.card ↥U' = p ^ 2 → ∀ g' : G, ∀ V : Subgroup G, V ≤ Qof p (Cen z) U' →
        IsElementaryAbelian p ↥V → p ^ 2 ≤ Nat.card ↥V → zpowers z ⊔ V ≤ conjugate (Cen z) g' →
          conjugate (Cen z) g' = Cen z := by
    intro U' hle hn hel hc g' V hVQ hVel hVc hZV
    exact h1813 G z k S (Cen z) p h.base U' hle hn hel hc (conjugate (Cen z) g')
      (isCoatom_conjugate' hcoat g') (Or.inr ⟨g', rfl, V, hVQ, hVel, hVc, hZV⟩)
  refine ⟨c⁻¹, ?_⟩
  refine ⟨h.base.prime, h.base.odd, h.base.rank, hcoat, hsimple, hz2, ht2, ?_, ?_, h.t_ne, ⟨hnG, hb⟩⟩
  · exact (Subgroup.mem_centralizer_singleton_iff.mp htM).symm
  · rw [inv_inv]; exact hc

theorem lemma19_3_thm (h1813 : Prop18_13) (h171 : Prop17_1) : Lemma19_3 := by
  intro G _ _ z k S M p U t h
  have hMC : M = Cen z := (h171 G z k S M h.base.base.ctx h.base.base.fail).1
  subst hMC
  obtain ⟨g, hAb⟩ := ab_of_ctx19 h1813 h
  have hU : IsU z p U := ⟨h.U_le, h.U_normal, h.U_elem, h.U_card⟩
  exact ⟨lemma19_3a hAb hU, fun r hr hr2 hrp hrank => lemma19_3b hAb hU hr hr2 hrp hrank⟩

theorem lemma19_4_thm (h1813 : Prop18_13) (h171 : Prop17_1) : Lemma19_4 := by
  intro G _ _ z k S M p U t h
  have hMC : M = Cen z := (h171 G z k S M h.base.base.ctx h.base.base.fail).1
  subst hMC
  obtain ⟨g, hAb⟩ := ab_of_ctx19 h1813 h
  exact lemma19_4 hAb ⟨h.U_le, h.U_normal, h.U_elem, h.U_card⟩

end CFSG.GH74.GLS.Stage2.Final.Thm4
