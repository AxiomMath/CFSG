module

public import CFSG.ClassicalInvolution.Q3.TL3T68B
public import CFSG.ClassicalInvolution.Q3.TL3T69

public section

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph
open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
open CFSG.ComponentClassification.PresentationLocal Amalg

variable {G : Type} [Group G] [Finite G] {IH : ℕ → Prop} {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {n : ℕ}

namespace LabCtx

variable {I : AEIdent (orbOf (TC.nbrAdj Ω) K J) n} (ctx : LabCtx I)

@[expose] def common : Set (Fin (n + 4)) := Set.range (globEmb₁ n) ∩ Set.range ctx.E.emb₂

theorem common_subset : ctx.common ⊆ Set.range (globEmb₁ n) := Set.inter_subset_left

theorem exists_four_common (hn : 5 ≤ n) :
    ∃ α : Finset (Fin (n + 4)), α.card = 4 ∧ (α : Set (Fin (n + 4))) ⊆ ctx.common := by
  have hcard : 4 ≤ (Finset.univ.map (ctx.E.c₁.trans (globEmb₁ n))).card := by
    rw [Finset.card_map, Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨α, hαU, hα⟩ := Finset.exists_subset_card_eq hcard
  refine ⟨α, hα, fun x hx => ?_⟩
  obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp (hαU (Finset.mem_coe.mp hx))
  exact ⟨⟨ctx.E.c₁ i, rfl⟩, ⟨ctx.E.c₂ i, by
    have := congrArg (fun e : Fin n ↪ Fin (n + 4) => e i) ctx.E.trans_eq
    exact this.symm⟩⟩

theorem s₁_comm (hn : 5 ≤ n) {L : Subgroup G} (hL : L ∈ centMembers Ω ctx.D.u)
    {γ : Finset (Fin (n + 2))} {hγ : γ.card = 4} {e : Bool}
    (hlab : (L.subgroupOf (pSpan (centMembers Ω ctx.D.u))).map ctx.D.IY.φ = memBar γ hγ e)
    {τ : alternatingGroup (Fin (n + 2))} (hτ : ∀ x ∈ γ, (τ : Equiv.Perm (Fin (n + 2))) x = x) :
    ∀ l ∈ L, ((ctx.E.s₁ τ : ↥(pSpan (centMembers Ω ctx.D.u))) : G) * l =
      l * ((ctx.E.s₁ τ : ↥(pSpan (centMembers Ω ctx.D.u))) : G) := by
  refine ctx.D.IY.comm_member (by omega) ctx.D.hHY.card ctx.D.hHY.conj_mem ctx.D.hHY.label_inj hL
    (ctx.E.s₁ τ) ?_
  intro y hy
  rw [hlab] at hy
  rw [ctx.E.hs₁]
  exact ofPerm_comm_memBar hγ e hτ y hy

theorem exists_label_of_lab₁ (hn : 5 ≤ n) {L : Subgroup G} (hL : L ∈ centMembers Ω ctx.D.u)
    {α : Finset (Fin (n + 4))} {hα : α.card = 4} {b : Bool}
    (hlab : ctx.lab₁ L = memBar α hα b) :
    ∃ (γ : Finset (Fin (n + 2))) (hγ : γ.card = 4) (b' : Bool),
      ((conjSub ctx.E.g⁻¹ L).subgroupOf (pSpan (centMembers Ω ctx.D.u))).map ctx.D.IY.φ =
        memBar γ hγ b' ∧ γ.map (globEmb₁ n) = α := by
  have hg : ctx.E.g⁻¹ ∈ pSpan (centMembers Ω ctx.D.u) := Subgroup.inv_mem _ ctx.E.hgY
  obtain ⟨γ, hγ, b', hl⟩ := ctx.D.IY.label _ (ctx.D.hHY.conj_mem L hL _ hg)
  refine ⟨γ, hγ, b', hl, ?_⟩
  unfold lab₁ at hlab
  rw [hl, transLab_memBar (by omega)] at hlab
  exact eq_of_memBar_eq' (by omega) hlab

theorem overlap (hn : 5 ≤ n) {L : Subgroup G} (hL : L ∈ centMembers Ω ctx.D.u)
    {α : Finset (Fin (n + 4))} {hα : α.card = 4} {b : Bool}
    (hαO : (α : Set (Fin (n + 4))) ⊆ ctx.common) (hlab : ctx.lab₁ L = memBar α hα b) :
    conjSub ctx.D.t⁻¹ L ∈ centMembers Ω ctx.D.u ∧
      ∃ (β : Finset (Fin (n + 2))) (hβ : β.card = 4) (e : Bool),
        ((conjSub ctx.D.t⁻¹ L).subgroupOf (pSpan (centMembers Ω ctx.D.u))).map ctx.D.IY.φ =
          memBar β hβ e ∧ β.map ctx.E.emb₂ = α := by
  classical
  set Y := pSpan (centMembers Ω ctx.D.u) with hY
  obtain ⟨γ, hγ, b', hlab', hγα⟩ := ctx.exists_label_of_lab₁ hn hL hlab
  obtain ⟨L', hL'1, hLg⟩ : ∃ L', conjSub ctx.E.g⁻¹ L = L' ∧ conjSub ctx.E.g L' = L :=
    ⟨_, rfl, conjSub_conjSub_inv ctx.E.g L⟩
  rw [hL'1] at hlab'
  have hγc : ∀ y ∈ γ, y ∈ Set.range ctx.E.c₁ := by
    intro y hy
    have hcy : globEmb₁ n y ∈ α := by rw [← hγα]; exact Finset.mem_map_of_mem _ hy
    have h := (ctx.E.range_emb₂ _).mp (hαO (Finset.mem_coe.mpr hcy)).2
    exact (ctx.E.hc₁ y).mpr ⟨fun h' => h.1 (by rw [h']), fun h' => h.2 (by rw [h'])⟩
  obtain ⟨γ₀, hγ₀⟩ := exists_map_eq_of_subset ctx.E.c₁ hγc
  subst hγ₀
  obtain ⟨v, hv⟩ := ctx.E.hgv
  have hLlab : ∃ b'' : Bool,
      (L.subgroupOf Y).map ctx.D.IY.φ = memBar (γ₀.map ctx.E.c₁) hγ b'' := by
    have e : ((conjSub ctx.E.g L').subgroupOf Y).map ctx.D.IY.φ =
        conjSub (ctx.D.IY.φ ⟨ctx.E.g, ctx.E.hgY⟩) ((L'.subgroupOf Y).map ctx.D.IY.φ) :=
      TL4.AECov.map_conjSub_eq ctx.D.IY L' ⟨ctx.E.g, ctx.E.hgY⟩
    rw [hLg, hv, hlab'] at e
    rw [e]
    rcases TL4.AECov.conjSub_memBar_of_perm_eq_one (w := ofVec v) rfl (γ₀.map ctx.E.c₁) hγ b'
      with h | h
    · exact ⟨true, h⟩
    · exact ⟨false, h⟩
  obtain ⟨b'', hb''⟩ := hLlab
  obtain ⟨L'', hL''Ω, hLt⟩ := ctx.E.hZ L hL γ₀ hγ b'' hb''
  have hL''eq : conjSub ctx.D.t⁻¹ L = L'' := by rw [← hLt, conjSub_inv_conjSub]
  rw [hL''eq]
  refine ⟨hL''Ω, ?_⟩
  obtain ⟨hα₂, e, hl₂⟩ := ctx.E.hcorr L hL γ₀ hγ b'' hb''
  have hlab'' : (L''.subgroupOf Y).map ctx.D.IY.φ = memBar (γ₀.map ctx.E.c₂) hα₂ e := by
    have h := ctx.D.IY.map_conj ctx.D.t (L := L'')
    rw [hLt] at h
    exact h.symm.trans hl₂
  refine ⟨γ₀.map ctx.E.c₂, hα₂, e, hlab'', ?_⟩
  rw [Finset.map_map, ← ctx.E.trans_eq, ← Finset.map_map]
  exact hγα

theorem centralizes (hn : 5 ≤ n) {L : Subgroup G} (hL : L ∈ centMembers Ω ctx.D.u)
    {α : Finset (Fin (n + 4))} {hα : α.card = 4} {b : Bool}
    (hαO : (α : Set (Fin (n + 4))) ⊆ ctx.common) (hlab : ctx.lab₁ L = memBar α hα b)
    {σ : alternatingGroup (Fin (n + 4))} (hσ : ∀ x ∈ α, (σ : Equiv.Perm (Fin (n + 4))) x = x) :
    ∀ l ∈ L, ctx.f σ * l = l * ctx.f σ := by
  classical
  set Y := pSpan (centMembers Ω ctx.D.u) with hY
  let C : Subgroup (alternatingGroup (Fin (n + 4))) :=
    (Subgroup.centralizer (L : Set G)).comap ctx.f
  have hmemC : ∀ ρ, ρ ∈ C ↔ ∀ l ∈ L, ctx.f ρ * l = l * ctx.f ρ := fun ρ => by
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    exact ⟨fun h l hl => (h l hl).symm, fun h l hl => (h l hl).symm⟩
  set P := missing₁ n with hP
  set Q : Finset (Fin (n + 4)) :=
    {globEmb₁ n (ctx.D.ι ctx.D.a), globEmb₁ n (ctx.D.ι ctx.D.c)} with hQ
  have hαc : ∀ x ∈ α, x ∈ Set.range (globEmb₁ n) := fun x hx =>
    ctx.common_subset (hαO (Finset.mem_coe.mpr hx))
  have hαe : ∀ x ∈ α, x ∈ Set.range ctx.E.emb₂ := fun x hx =>
    (hαO (Finset.mem_coe.mpr hx)).2
  have hαP : Disjoint α P := by
    rw [Finset.disjoint_left]
    intro x hx hxP
    have := (GlueData.range_emb₁ x).mp (hαc x hx)
    simp only [hP, missing₁, Finset.mem_insert, Finset.mem_singleton] at hxP
    rcases hxP with rfl | rfl
    · exact this.1 rfl
    · exact this.2 rfl
  have hαQ : Disjoint α Q := by
    rw [Finset.disjoint_left]
    intro x hx hxQ
    have := (ctx.E.range_emb₂ x).mp (hαe x hx)
    simp only [hQ, Finset.mem_insert, Finset.mem_singleton] at hxQ
    rcases hxQ with rfl | rfl
    · exact this.1 rfl
    · exact this.2 rfl
  have hPQ : Disjoint P Q := by
    rw [Finset.disjoint_left]
    intro x hxP hxQ
    simp only [hP, missing₁, Finset.mem_insert, Finset.mem_singleton] at hxP
    simp only [hQ, Finset.mem_insert, Finset.mem_singleton] at hxQ
    have hmem : x ∈ Set.range (globEmb₁ n) := by
      rcases hxQ with rfl | rfl <;> exact ⟨_, rfl⟩
    have := (GlueData.range_emb₁ x).mp hmem
    rcases hxP with rfl | rfl
    · exact this.1 rfl
    · exact this.2 rfl
  have hQc : Q.card ≤ 2 := Finset.card_le_two
  have hle := altFix_le_sup' α P Q hPQ (card_missing₁ n).le hQc hαP hαQ (by rw [hα]; omega)
  have hσα : σ ∈ altFix (α : Set (Fin (n + 4))) := fun x hx => hσ x (Finset.mem_coe.mp hx)
  have h1 : altFix ((α ∪ P : Finset (Fin (n + 4))) : Set (Fin (n + 4))) ≤ C := by
    intro ρ hρ
    rw [hmemC]
    have hρα : ∀ x ∈ α, (ρ : Equiv.Perm (Fin (n + 4))) x = x := fun x hx =>
      hρ x (by simp [hx])
    have hρ' : ∀ x, x ∉ Set.range (globEmb₁ n) → (ρ : Equiv.Perm (Fin (n + 4))) x = x := by
      intro x hx
      rw [range_globEmb₁_eq, Set.mem_compl_iff, not_not] at hx
      exact hρ x (by simp [hP, Finset.mem_coe.mp hx])
    obtain ⟨τ, rfl⟩ := exists_altExt_eq (globEmb₁ n) ρ hρ'
    obtain ⟨γ, hγ, b', hlab', hγα⟩ := ctx.exists_label_of_lab₁ hn hL hlab
    have hτ : ∀ y ∈ γ, (τ : Equiv.Perm (Fin (n + 2))) y = y := by
      intro y hy
      have h := hρα (globEmb₁ n y) (by rw [← hγα]; exact Finset.mem_map_of_mem _ hy)
      rw [altExt_coe, extPerm_apply_mem] at h
      exact (globEmb₁ n).injective h
    have hcomm := ctx.s₁_comm hn (ctx.D.hHY.conj_mem L hL _ (Y.inv_mem ctx.E.hgY)) hlab' hτ
    intro l hl
    rw [ctx.hf₁ τ]
    have hl' : ctx.E.g⁻¹ * l * ctx.E.g ∈ conjSub ctx.E.g⁻¹ L := by
      have := conj_mem_conjSub (n := ctx.E.g⁻¹) hl
      rwa [inv_inv] at this
    have e := hcomm _ hl'
    calc ctx.E.g * ((ctx.E.s₁ τ : ↥Y) : G) * ctx.E.g⁻¹ * l
        = ctx.E.g * (((ctx.E.s₁ τ : ↥Y) : G) * (ctx.E.g⁻¹ * l * ctx.E.g)) * ctx.E.g⁻¹ := by
          group
      _ = ctx.E.g * ((ctx.E.g⁻¹ * l * ctx.E.g) * ((ctx.E.s₁ τ : ↥Y) : G)) * ctx.E.g⁻¹ := by
          rw [e]
      _ = l * (ctx.E.g * ((ctx.E.s₁ τ : ↥Y) : G) * ctx.E.g⁻¹) := by group
  have h2 : altFix ((α ∪ Q : Finset (Fin (n + 4))) : Set (Fin (n + 4))) ≤ C := by
    intro ρ hρ
    rw [hmemC]
    have hρα : ∀ x ∈ α, (ρ : Equiv.Perm (Fin (n + 4))) x = x := fun x hx =>
      hρ x (by simp [hx])
    have hρ' : ∀ x, x ∉ Set.range ctx.E.emb₂ → (ρ : Equiv.Perm (Fin (n + 4))) x = x := by
      intro x hx
      rw [ctx.E.range_emb₂] at hx
      have hxQ : x ∈ Q := by
        by_contra h
        apply hx
        refine ⟨fun h' => h ?_, fun h' => h ?_⟩
        · simp [hQ, h']
        · simp [hQ, h']
      exact hρ x (by simp [hxQ])
    obtain ⟨τ, rfl⟩ := exists_altExt_eq ctx.E.emb₂ ρ hρ'
    obtain ⟨hL'', β, hβ, e', hlab'', hβα⟩ := ctx.overlap hn hL hαO hlab
    have hτ : ∀ y ∈ β, (τ : Equiv.Perm (Fin (n + 2))) y = y := by
      intro y hy
      have h := hρα (ctx.E.emb₂ y) (by rw [← hβα]; exact Finset.mem_map_of_mem _ hy)
      rw [altExt_coe, extPerm_apply_mem] at h
      exact ctx.E.emb₂.injective h
    have hcomm := ctx.s₁_comm hn hL'' hlab'' hτ
    intro l hl
    rw [ctx.hf₂ τ]
    have hl' : ctx.D.t⁻¹ * l * ctx.D.t ∈ conjSub ctx.D.t⁻¹ L := by
      have := conj_mem_conjSub (n := ctx.D.t⁻¹) hl
      rwa [inv_inv] at this
    have e := hcomm _ hl'
    calc ctx.D.t * ((ctx.E.s₁ τ : ↥Y) : G) * ctx.D.t⁻¹ * l
        = ctx.D.t * (((ctx.E.s₁ τ : ↥Y) : G) * (ctx.D.t⁻¹ * l * ctx.D.t)) * ctx.D.t⁻¹ := by
          group
      _ = ctx.D.t * ((ctx.D.t⁻¹ * l * ctx.D.t) * ((ctx.E.s₁ τ : ↥Y) : G)) * ctx.D.t⁻¹ := by
          rw [e]
      _ = l * (ctx.D.t * ((ctx.E.s₁ τ : ↥Y) : G) * ctx.D.t⁻¹) := by group
  exact (hmemC σ).mp ((sup_le h1 h2) (hle hσα))

theorem conjSub_t_mem (hS : CSetting 3 IH Ω K J) (hn : 5 ≤ n) {M : Subgroup G}
    (hM : M ∈ centMembers Ω ctx.D.u) {γ : Finset (Fin (n + 2))} {hγ : γ.card = 4} {e : Bool}
    (hγc : (γ : Set (Fin (n + 2))) ⊆ Set.range ctx.E.c₂)
    (hlab : (M.subgroupOf (pSpan (centMembers Ω ctx.D.u))).map ctx.D.IY.φ = memBar γ hγ e) :
    conjSub ctx.D.t M ∈ centMembers Ω ctx.D.u := by
  have hwY : ctx.D.t⁻¹ * ctx.D.u * ctx.D.t ∈ pSpan (centMembers Ω ctx.D.u) :=
    ctx.D.hsub.span_le ctx.D.hw'
  have hac : ctx.D.ι ctx.D.a' ≠ ctx.D.ι ctx.D.c' := ctx.D.ι.injective.ne ctx.D.hac'
  have hnot : ctx.D.ι ctx.D.a' ∉ γ ∧ ctx.D.ι ctx.D.c' ∉ γ := by
    refine ⟨fun h => ?_, fun h => ?_⟩
    · exact ((ctx.E.hc₂ _).mp (hγc (Finset.mem_coe.mpr h))).1 rfl
    · exact ((ctx.E.hc₂ _).mp (hγc (Finset.mem_coe.mpr h))).2 rfl
  have hcu := (ctx.D.IY.comm_pairVec_iff (by omega) ctx.D.hHY.card ctx.D.hHY.conj_mem
    ctx.D.hHY.label_inj (w := ⟨_, hwY⟩) hac ctx.D.hpair' hM hlab).mpr hnot
  refine ⟨hS.cex.hyp.conjInvariant _ M hM.1, fun m hm => ?_⟩
  have hm' : ctx.D.t⁻¹ * m * ctx.D.t ∈ M := mem_conjSub_iff.mp hm
  have e := hcu _ hm'
  calc m * ctx.D.u
      = ctx.D.t * ((ctx.D.t⁻¹ * m * ctx.D.t) * (ctx.D.t⁻¹ * ctx.D.u * ctx.D.t)) * ctx.D.t⁻¹ := by
        group
    _ = ctx.D.t * ((ctx.D.t⁻¹ * ctx.D.u * ctx.D.t) * (ctx.D.t⁻¹ * m * ctx.D.t)) * ctx.D.t⁻¹ := by
        rw [← e]
    _ = ctx.D.u * m := by group

theorem chart2 (hS : CSetting 3 IH Ω K J) (hn : 5 ≤ n) {M : Subgroup G}
    (hM : M ∈ centMembers Ω ctx.D.u) :
    ∃ σ : alternatingGroup (Fin (n + 4)), ∃ N ∈ centMembers Ω ctx.D.u,
      conjSub ctx.D.t M = conjSub (ctx.f σ) N := by
  set Y := pSpan (centMembers Ω ctx.D.u) with hY
  obtain ⟨γ, hγ, e, hlab⟩ := ctx.D.IY.label M hM
  have hcard : 4 ≤ (Finset.univ.map ctx.E.c₂).card := by
    rw [Finset.card_map, Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨γ₂, hγ₂U, hγ₂⟩ := Finset.exists_subset_card_eq hcard
  have hγ₂c : (γ₂ : Set (Fin (n + 2))) ⊆ Set.range ctx.E.c₂ := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp (hγ₂U (Finset.mem_coe.mp hx))
    exact ⟨i, rfl⟩
  obtain ⟨τ, hτ⟩ := exists_alt_permAct_eq (m := n + 2) (by omega) (memBar_mem_memLabels γ hγ e)
    (memBar_mem_memLabels γ₂ hγ₂ true)
  set s : G := ((ctx.E.s₁ τ : ↥Y) : G) with hs
  have hsY : s ∈ Y := (ctx.E.s₁ τ).2
  have hM' : conjSub s M ∈ centMembers Ω ctx.D.u := ctx.D.hHY.conj_mem M hM s hsY
  have hlab' : ((conjSub s M).subgroupOf Y).map ctx.D.IY.φ = memBar γ₂ hγ₂ true := by
    have e2 := TL4.AECov.map_conjSub_eq ctx.D.IY M (ctx.E.s₁ τ)
    rw [ctx.E.hs₁ τ, hlab] at e2
    rw [e2]
    exact hτ
  have hN := ctx.conjSub_t_mem hS hn hM' hγ₂c hlab'
  refine ⟨altExt ctx.E.emb₂ τ⁻¹, conjSub ctx.D.t (conjSub s M), hN, ?_⟩
  have hsi : ((ctx.E.s₁ τ⁻¹ : ↥Y) : G) = s⁻¹ := by rw [map_inv]; rfl
  rw [ctx.hf₂ τ⁻¹, hsi, ← conjSub_mul, ← conjSub_mul]
  congr 1
  group

end LabCtx

end CFSG.ClassicalInvolution.Q3.TC.Thin
