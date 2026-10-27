module

public import CFSG.ClassicalInvolution.Q3.TL3T67
public import CFSG.ClassicalInvolution.Q3.TL3T68
public import CFSG.ClassicalInvolution.Q3.TL3T64A

public section

namespace CFSG.ClassicalInvolution.Q3.AE

open Wr CFSG.ClassicalInvolution.Generic

theorem permAct_eq_of_fix {m : ℕ} {σ : Equiv.Perm (Fin m)} {α : Finset (Fin m)} (h : α.card = 4)
    (b : Bool) (hσ : ∀ x ∈ α, σ x = x) : permAct σ (memBar α h b) = memBar α h b :=
  TC.Thin.conjSub_eq_of_comm fun s hs => ofPerm_comm_memBar h b hσ s hs

end CFSG.ClassicalInvolution.Q3.AE

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph
open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
open CFSG.ComponentClassification.PresentationLocal Amalg

theorem strictMono_globEmb₁ (n : ℕ) : StrictMono (globEmb₁ n) := fun _ _ h => h

@[expose] def missing₁ (n : ℕ) : Finset (Fin (n + 4)) := {⟨n + 2, by omega⟩, ⟨n + 3, by omega⟩}

theorem card_missing₁ (n : ℕ) : (missing₁ n).card = 2 := by
  rw [missing₁, Finset.card_pair]
  intro h
  have := congrArg Fin.val h
  simp at this

theorem range_globEmb₁_eq (n : ℕ) :
    Set.range (globEmb₁ n) = ((missing₁ n : Finset (Fin (n + 4))) : Set (Fin (n + 4)))ᶜ := by
  ext x
  rw [GlueData.range_emb₁]
  simp [missing₁]

variable {G : Type} [Group G] [Finite G] {IH : ℕ → Prop} {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {n : ℕ}

structure LabCtx (I : AEIdent (orbOf (TC.nbrAdj Ω) K J) n) where
  D : PairChart Ω K J I
  E : GlueData D
  f : alternatingGroup (Fin (n + 4)) →* G
  hf₁ : ∀ σ : alternatingGroup (Fin (n + 2)),
    f (altExt (globEmb₁ n) σ) = E.g * ((E.s₁ σ : ↥(pSpan (centMembers Ω D.u))) : G) * E.g⁻¹
  hf₂ : ∀ σ : alternatingGroup (Fin (n + 2)),
    f (altExt E.emb₂ σ) = D.t * ((E.s₁ σ : ↥(pSpan (centMembers Ω D.u))) : G) * D.t⁻¹

theorem CSetting.nonempty_labCtx (hS : CSetting 3 IH Ω K J) (hn : 5 ≤ n) (hM : Model117At n)
    (I : AEIdent (orbOf (TC.nbrAdj Ω) K J) n) : Nonempty (LabCtx I) := by
  obtain ⟨D⟩ := hS.nonempty_pairChart hn hM I
  obtain ⟨E⟩ := D.nonempty_glueData hS hn hM
  obtain ⟨f, hf₁, hf₂⟩ := E.exists_hom hS hn
  exact ⟨⟨D, E, f, hf₁, hf₂⟩⟩

namespace LabCtx

variable {I : AEIdent (orbOf (TC.nbrAdj Ω) K J) n} (ctx : LabCtx I)

@[expose] noncomputable def lab₁ (M : Subgroup G) : Subgroup (AEQ (n + 4)) :=
  transLab (globEmb₁ n)
    (((conjSub ctx.E.g⁻¹ M).subgroupOf (pSpan (centMembers Ω ctx.D.u))).map ctx.D.IY.φ)

theorem lab₁_injOn (hn : 5 ≤ n) {M M' : Subgroup G} (hM : M ∈ centMembers Ω ctx.D.u)
    (hM' : M' ∈ centMembers Ω ctx.D.u) (h : ctx.lab₁ M = ctx.lab₁ M') : M = M' := by
  have hg : ctx.E.g⁻¹ ∈ pSpan (centMembers Ω ctx.D.u) := Subgroup.inv_mem _ ctx.E.hgY
  have h1 := ctx.D.hHY.conj_mem M hM _ hg
  have h2 := ctx.D.hHY.conj_mem M' hM' _ hg
  obtain ⟨α, hα, b, hlab⟩ := ctx.D.IY.label _ h1
  obtain ⟨α', hα', b', hlab'⟩ := ctx.D.IY.label _ h2
  have e : conjSub ctx.E.g⁻¹ M = conjSub ctx.E.g⁻¹ M' := by
    refine ctx.D.hHY.label_inj _ h1 _ h2 ?_
    unfold lab₁ at h
    rw [hlab, hlab'] at h ⊢
    exact transLab_injOn (by omega) (by omega) (globEmb₁ n)
      (memBar_mem_memLabels _ _ _) (memBar_mem_memLabels _ _ _) h
  exact conjSub_injective _ e

theorem lab₁_mem (hn : 5 ≤ n) {M : Subgroup G} (hM : M ∈ centMembers Ω ctx.D.u) :
    ctx.lab₁ M ∈ memLabelsOn (Set.range (globEmb₁ n)) := by
  have hg : ctx.E.g⁻¹ ∈ pSpan (centMembers Ω ctx.D.u) := Subgroup.inv_mem _ ctx.E.hgY
  obtain ⟨α, hα, b, hlab⟩ := ctx.D.IY.label _ (ctx.D.hHY.conj_mem M hM _ hg)
  unfold lab₁
  rw [hlab]
  exact transLab_mem_memLabelsOn (by omega) _ (memBar_mem_memLabels _ _ _)

theorem exists_lab₁_eq (hn : 5 ≤ n) {μ : Subgroup (AEQ (n + 4))}
    (hμ : μ ∈ memLabelsOn (Set.range (globEmb₁ n))) :
    ∃ M ∈ centMembers Ω ctx.D.u, ctx.lab₁ M = μ := by
  obtain ⟨μ', hμ', rfl⟩ := exists_transLab_eq (by omega) (globEmb₁ n) hμ
  obtain ⟨γ, hγ, b, rfl⟩ := hμ'
  obtain ⟨L, hL, hlab⟩ := ctx.D.IY.label_surj γ hγ b
  refine ⟨conjSub ctx.E.g L, ctx.D.hHY.conj_mem L hL _ ctx.E.hgY, ?_⟩
  unfold lab₁
  rw [conjSub_inv_conjSub, hlab]

theorem lab₁_conj (hn : 5 ≤ n) {σ : alternatingGroup (Fin (n + 4))}
    (hσ : ∀ x ∈ missing₁ n, (σ : Equiv.Perm (Fin (n + 4))) x = x) {M : Subgroup G}
    (hM : M ∈ centMembers Ω ctx.D.u) :
    conjSub (ctx.f σ) M ∈ centMembers Ω ctx.D.u ∧
      ctx.lab₁ (conjSub (ctx.f σ) M) = permAct (σ : Equiv.Perm (Fin (n + 4))) (ctx.lab₁ M) := by
  have hσ' : ∀ x, x ∉ Set.range (globEmb₁ n) → (σ : Equiv.Perm (Fin (n + 4))) x = x := by
    intro x hx
    rw [range_globEmb₁_eq, Set.mem_compl_iff, not_not] at hx
    exact hσ x (Finset.mem_coe.mp hx)
  obtain ⟨τ, rfl⟩ := exists_altExt_eq (globEmb₁ n) σ hσ'
  rw [ctx.hf₁ τ]
  set Y := pSpan (centMembers Ω ctx.D.u) with hY
  set s : G := ((ctx.E.s₁ τ : ↥Y) : G) with hs
  have hsY : s ∈ Y := (ctx.E.s₁ τ).2
  have hxY : ctx.E.g * s * ctx.E.g⁻¹ ∈ Y :=
    Y.mul_mem (Y.mul_mem ctx.E.hgY hsY) (Y.inv_mem ctx.E.hgY)
  refine ⟨ctx.D.hHY.conj_mem M hM _ hxY, ?_⟩
  have e1 : conjSub ctx.E.g⁻¹ (conjSub (ctx.E.g * s * ctx.E.g⁻¹) M) =
      conjSub s (conjSub ctx.E.g⁻¹ M) := by
    rw [← conjSub_mul, ← conjSub_mul]
    congr 1
    group
  have hM1 : conjSub ctx.E.g⁻¹ M ∈ centMembers Ω ctx.D.u :=
    ctx.D.hHY.conj_mem M hM _ (Y.inv_mem ctx.E.hgY)
  obtain ⟨α, hα, b, hlab⟩ := ctx.D.IY.label _ hM1
  have e2 := TL4.AECov.map_conjSub_eq ctx.D.IY (conjSub ctx.E.g⁻¹ M) (ctx.E.s₁ τ)
  rw [ctx.E.hs₁ τ, hlab] at e2
  unfold lab₁
  rw [e1, e2, hlab]
  exact transLab_permAct (by omega) (strictMono_globEmb₁ n) _
    (memBar_mem_memLabels _ _ _)

theorem lab₁_loc (hn : 5 ≤ n) {L : Subgroup G} (hL : L ∈ centMembers Ω ctx.D.u) {l : G}
    (hl : l ∈ L) :
    ∃ x ∈ ctx.lab₁ L, ∀ M' ∈ centMembers Ω ctx.D.u, conjSub l M' ∈ centMembers Ω ctx.D.u ∧
      ctx.lab₁ (conjSub l M') = conjSub x (ctx.lab₁ M') := by
  set Y := pSpan (centMembers Ω ctx.D.u) with hY
  have hlY : l ∈ Y := le_pSpan hL hl
  have hgi : ctx.E.g⁻¹ ∈ Y := Y.inv_mem ctx.E.hgY
  have hL1 : conjSub ctx.E.g⁻¹ L ∈ centMembers Ω ctx.D.u := ctx.D.hHY.conj_mem L hL _ hgi
  have hyY : ctx.E.g⁻¹ * l * ctx.E.g ∈ Y := Y.mul_mem (Y.mul_mem hgi hlY) ctx.E.hgY
  have hyL : ctx.E.g⁻¹ * l * ctx.E.g ∈ conjSub ctx.E.g⁻¹ L := by
    have := conj_mem_conjSub (n := ctx.E.g⁻¹) hl
    rwa [inv_inv] at this
  obtain ⟨δ, hδ, e, hδlab⟩ := ctx.D.IY.label _ hL1
  have hmem : ctx.D.IY.φ ⟨ctx.E.g⁻¹ * l * ctx.E.g, hyY⟩ ∈ memBar δ hδ e := by
    rw [← hδlab]
    exact ctx.D.IY.mem_map hL1 hyL
  obtain ⟨w₀, hw₀, hw₀e⟩ := hmem
  refine ⟨mkQ (n + 4) (embW (globEmb₁ n) w₀), ?_, fun M' hM' => ?_⟩
  · unfold lab₁
    rw [hδlab, transLab_memBar (by omega)]
    refine ⟨embW (globEmb₁ n) w₀, ?_, rfl⟩
    rw [← memAt_map_embW (strictMono_globEmb₁ n) δ hδ (by rw [Finset.card_map]; exact hδ) e]
    exact Subgroup.mem_map_of_mem _ hw₀
  · refine ⟨ctx.D.hHY.conj_mem M' hM' l hlY, ?_⟩
    have e1 : conjSub ctx.E.g⁻¹ (conjSub l M') =
        conjSub (ctx.E.g⁻¹ * l * ctx.E.g) (conjSub ctx.E.g⁻¹ M') := by
      rw [← conjSub_mul, ← conjSub_mul]
      congr 1
      group
    obtain ⟨α, hα, b, hlab⟩ := ctx.D.IY.label _ (ctx.D.hHY.conj_mem M' hM' _ hgi)
    have e2 := TL4.AECov.map_conjSub_eq ctx.D.IY (conjSub ctx.E.g⁻¹ M')
      ⟨ctx.E.g⁻¹ * l * ctx.E.g, hyY⟩
    rw [← hw₀e, hlab] at e2
    unfold lab₁
    rw [e1, e2, hlab]
    exact transport_conj (by omega) (strictMono_globEmb₁ n) w₀
      (memBar_mem_memLabels _ _ _)

end LabCtx

end CFSG.ClassicalInvolution.Q3.TC.Thin
