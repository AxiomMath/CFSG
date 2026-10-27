module

public import CFSG.ClassicalInvolution.Q3.TL3T52
public import CFSG.ClassicalInvolution.Q3.TL3T52A
public import CFSG.ClassicalInvolution.Q3.TL3T60
public import CFSG.ClassicalInvolution.Q3.TL4AECover

public section

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph
open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

section Trans

variable {G : Type} [Group G] {P : Set (Subgroup G)} {n : ℕ}

private theorem AEIdent.twin_z_of_trans_aux (I : AEIdent P n) (hn : 5 ≤ n)
    (hconj : ∀ L ∈ P, ∀ x ∈ pSpan P, conjSub x L ∈ P)
    (hinj : ∀ L ∈ P, ∀ L' ∈ P,
      (L.subgroupOf (pSpan P)).map I.φ = (L'.subgroupOf (pSpan P)).map I.φ → L = L')
    (htrans : ∀ L ∈ P, ∀ L' ∈ P, ∃ x ∈ pSpan P, conjSub x L = L')
    {J₀ J₀' : Subgroup G} (hJ₀ : J₀ ∈ P) (hJ₀' : J₀' ∈ P) {δ : Finset (Fin n)}
    {hδ : δ.card = 4} {c : Bool}
    (hlab₀ : (J₀.subgroupOf (pSpan P)).map I.φ = memBar δ hδ c)
    (hlab₀' : (J₀'.subgroupOf (pSpan P)).map I.φ = memBar δ hδ (!c))
    (hz₀ : ∀ u u' : G, IsUniqueInvolution J₀ u → IsUniqueInvolution J₀' u' → u = u') :
    ∀ (α : Finset (Fin n)) (h : α.card = 4), ∀ L ∈ P, ∀ L' ∈ P,
      (L.subgroupOf (pSpan P)).map I.φ = memBar α h true →
      (L'.subgroupOf (pSpan P)).map I.φ = memBar α h false →
      ∀ u u' : G, IsUniqueInvolution L u → IsUniqueInvolution L' u' → u = u' := by
  intro α h L hL L' hL' hlab hlab' u u' hu hu'
  obtain ⟨x, hx, hxL⟩ := htrans J₀ hJ₀ L hL
  obtain ⟨w, hw⟩ := QuotientGroup.mk'_surjective (piSub n) (I.φ ⟨x, hx⟩)
  have hc1 := TL4.AECov.map_conjSub_eq I J₀ ⟨x, hx⟩
  have hc2 := TL4.AECov.map_conjSub_eq I J₀' ⟨x, hx⟩
  rw [hxL, hlab₀, ← hw] at hc1
  rw [hlab₀', ← hw] at hc2
  obtain ⟨c₁, hc₁⟩ := exists_conj_memBar_map w δ hδ c
  obtain ⟨c₂, hc₂⟩ := exists_conj_memBar_map w δ hδ (!c)
  rw [hc₁] at hc1
  rw [hc₂] at hc2
  have hδα : δ.map w.perm.toEmbedding = α := AE.eq_of_memBar_eq' hn (hc1.symm.trans hlab)
  have hne : c₂ ≠ c₁ := by
    intro e
    rw [e] at hc₂
    have := conjSub_injective (mkQ n w) (hc₁.trans hc₂.symm)
    cases c
    · exact memBar_true_ne_false hn δ hδ this.symm
    · exact memBar_true_ne_false hn δ hδ this
  have hc₁t : c₁ = true := by
    by_contra hf
    have : c₁ = false := by cases c₁ <;> simp_all
    subst this
    subst hδα
    exact memBar_true_ne_false hn _ h (hlab.symm.trans hc1)
  have hc₂f : c₂ = false := by cases c₂ <;> simp_all
  subst hc₁t hc₂f
  have hxJ' : conjSub x J₀' = L' := by
    refine hinj _ (hconj J₀' hJ₀' x hx) L' hL' ?_
    rw [hc2, hlab']
    subst hδα
    rfl
  have hJ₀L : conjSub x⁻¹ L = J₀ := by rw [← hxL, conjSub_inv_conjSub]
  have hJ₀L' : conjSub x⁻¹ L' = J₀' := by rw [← hxJ', conjSub_inv_conjSub]
  have hv := hu.conj x⁻¹
  rw [hJ₀L] at hv
  have hv' := hu'.conj x⁻¹
  rw [hJ₀L'] at hv'
  have e := hz₀ _ _ hv hv'
  calc u = x * (x⁻¹ * u * x⁻¹⁻¹) * x⁻¹ := by group
    _ = x * (x⁻¹ * u' * x⁻¹⁻¹) * x⁻¹ := by rw [e]
    _ = u' := by group

end Trans

variable {G : Type} [Group G] [Finite G] {IH : ℕ → Prop} {Ω : Set (Subgroup G)}

namespace CSetting

variable {K J : Subgroup G} (hS : CSetting 3 IH Ω K J)
include hS

theorem aeCoverHyp_centMembers_of_twin {u : G} {m : ℕ} (hm5 : 5 ≤ m)
    (IY : AEIdent (centMembers Ω u) m)
    (hodd : classicalInvolutionOddCore ↥(pSpan (centMembers Ω u)) = ⊥)
    (htrans : ∀ L ∈ centMembers Ω u, ∀ L' ∈ centMembers Ω u,
      ∃ x ∈ pSpan (centMembers Ω u), conjSub x L = L')
    {J₀ J₀' : Subgroup G} (hJ₀ : J₀ ∈ centMembers Ω u) (hJ₀' : J₀' ∈ centMembers Ω u)
    {δ : Finset (Fin m)} {hδ : δ.card = 4} {c : Bool}
    (hlab : (J₀.subgroupOf (pSpan (centMembers Ω u))).map IY.φ = memBar δ hδ c)
    (hlab' : (J₀'.subgroupOf (pSpan (centMembers Ω u))).map IY.φ = memBar δ hδ (!c))
    (hz : ∀ v v' : G, IsUniqueInvolution J₀ v → IsUniqueInvolution J₀' v' → v = v') :
    TL4.AECoverHyp IY := by
  have hD := hS.cex.toThmDHyp
  have h8 : ∀ L ∈ Ω, Nat.card L = 8 := fun L hL => by rw [hD.card L hL]; norm_num
  have hPΩ : centMembers Ω u ⊆ Ω := fun _ h => h.1
  have hk : IsPGroup 2 IY.φ.ker := IY.toLabel.isPGroup_ker hodd
  have hconj : ∀ L ∈ centMembers Ω u, ∀ x ∈ pSpan (centMembers Ω u),
      conjSub x L ∈ centMembers Ω u := fun L hL x hx => hS.conjSub_mem_centMembers u hL hx
  have hinj : ∀ L ∈ centMembers Ω u, ∀ L' ∈ centMembers Ω u,
      (L.subgroupOf (pSpan (centMembers Ω u))).map IY.φ =
        (L'.subgroupOf (pSpan (centMembers Ω u))).map IY.φ → L = L' :=
    fun L hL L' hL' h => aeIdent_eq_of_map_eq hD.hyp hD.two hPΩ hm5 IY hk hL hL' h
  exact
    { ker_two := hk
      card := fun L hL => h8 L hL.1
      conj_mem := hconj
      label_inj := hinj
      twin_comm := by
        intro α h L hL L' hL' hl hl'
        refine aeIdent_comm_of_map_comm hD.hyp hD.two hPΩ IY hk hL hL' ?_ ?_
        · intro e
          subst e
          rw [hl] at hl'
          exact AE.memBar_true_ne_false hm5 α h hl'
        · rw [hl, hl']
          exact memBar_twin_comm α h true
      twin_z := IY.twin_z_of_trans_aux hm5 hconj hinj htrans hJ₀ hJ₀' hlab hlab' hz }

end CSetting

end CFSG.ClassicalInvolution.Q3.TC.Thin
