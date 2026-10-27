module

public import CFSG.ClassicalInvolution.Q3.TL3T82
public import CFSG.ClassicalInvolution.Q3.TL3T70

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

theorem labHyp' (hn : 5 ≤ n) :
    LabHyp' Ω ctx.f (centMembers Ω ctx.D.u) ctx.lab₁ (missing₁ n) ctx.common where
  card_T := card_missing₁ n
  hm := by omega
  sub := fun M hM => hM.1
  O_sub := by rw [← range_globEmb₁_eq]; exact ctx.common_subset
  O_four := ctx.exists_four_common (by omega)
  inj := fun M hM M' hM' h => ctx.lab₁_injOn (by omega) hM hM' h
  mem := fun M hM => by rw [← range_globEmb₁_eq]; exact ctx.lab₁_mem (by omega) hM
  surj := fun μ hμ => ctx.exists_lab₁_eq (by omega) (by rwa [range_globEmb₁_eq])
  conj := fun σ hσ M hM => ctx.lab₁_conj (by omega) hσ hM
  loc := fun L hL l hl => ctx.lab₁_loc (by omega) hL hl
  cent := fun L hL α hα b hαO hlab σ hσ l hl => ctx.centralizes (by omega) hL hαO hlab hσ l hl

private theorem exists_label_of_label_conj {L : Subgroup G} {γ : Finset (Fin (n + 2))}
    {hγ : γ.card = 4} {b : Bool}
    (hl : ((conjSub ctx.E.g⁻¹ L).subgroupOf (pSpan (centMembers Ω ctx.D.u))).map ctx.D.IY.φ =
      memBar γ hγ b) :
    ∃ b' : Bool,
      (L.subgroupOf (pSpan (centMembers Ω ctx.D.u))).map ctx.D.IY.φ = memBar γ hγ b' := by
  obtain ⟨v, hv⟩ := ctx.E.hgv
  have e : ((conjSub ctx.E.g (conjSub ctx.E.g⁻¹ L)).subgroupOf
        (pSpan (centMembers Ω ctx.D.u))).map ctx.D.IY.φ =
      conjSub (ctx.D.IY.φ ⟨ctx.E.g, ctx.E.hgY⟩) (((conjSub ctx.E.g⁻¹ L).subgroupOf
        (pSpan (centMembers Ω ctx.D.u))).map ctx.D.IY.φ) :=
    TL4.AECov.map_conjSub_eq ctx.D.IY (conjSub ctx.E.g⁻¹ L) ⟨ctx.E.g, ctx.E.hgY⟩
  rw [conjSub_conjSub_inv, hv, hl] at e
  rcases TL4.AECov.conjSub_memBar_of_perm_eq_one (w := ofVec v) rfl γ hγ b with h | h
  · exact ⟨true, e.trans h⟩
  · exact ⟨false, e.trans h⟩

theorem exists_label_self_of_lab₁ (hn : 5 ≤ n) {L : Subgroup G}
    (hL : L ∈ centMembers Ω ctx.D.u) {α : Finset (Fin (n + 4))} {hα : α.card = 4} {b : Bool}
    (hlab : ctx.lab₁ L = memBar α hα b) :
    ∃ (γ : Finset (Fin (n + 2))) (hγ : γ.card = 4) (b' : Bool),
      (L.subgroupOf (pSpan (centMembers Ω ctx.D.u))).map ctx.D.IY.φ = memBar γ hγ b' ∧
        γ.map (globEmb₁ n) = α := by
  obtain ⟨γ, hγ, b', hl, hγα⟩ := ctx.exists_label_of_lab₁ hn hL hlab
  obtain ⟨b'', hb''⟩ := ctx.exists_label_of_label_conj hl
  exact ⟨γ, hγ, b'', hb'', hγα⟩

theorem lab₁_of_label (hn : 5 ≤ n) {M : Subgroup G} (hM : M ∈ centMembers Ω ctx.D.u)
    {δ : Finset (Fin (n + 2))} {hδ : δ.card = 4} {e : Bool}
    (hlab : (M.subgroupOf (pSpan (centMembers Ω ctx.D.u))).map ctx.D.IY.φ = memBar δ hδ e) :
    ∃ b : Bool, ctx.lab₁ M = memBar (δ.map (globEmb₁ n)) (by rw [Finset.card_map]; exact hδ) b := by
  have hg : ctx.E.g⁻¹ ∈ pSpan (centMembers Ω ctx.D.u) := Subgroup.inv_mem _ ctx.E.hgY
  obtain ⟨γ, hγ, b', hl⟩ := ctx.D.IY.label _ (ctx.D.hHY.conj_mem M hM _ hg)
  obtain ⟨b'', hb''⟩ := ctx.exists_label_of_label_conj hl
  have hδγ : δ = γ := eq_of_memBar_eq' (by omega) (hlab.symm.trans hb'')
  subst hδγ
  refine ⟨b', ?_⟩
  unfold lab₁
  rw [hl, transLab_memBar (by omega)]

theorem lab₁_conjSub_t (hS : CSetting 3 IH Ω K J) (hn : 5 ≤ n) {M' : Subgroup G}
    (hM' : M' ∈ centMembers Ω ctx.D.u) {γ₂ : Finset (Fin (n + 2))} {hγ₂ : γ₂.card = 4}
    {e : Bool}
    (hlab : (M'.subgroupOf (pSpan (centMembers Ω ctx.D.u))).map ctx.D.IY.φ = memBar γ₂ hγ₂ e)
    (hγ₂c : (γ₂ : Set (Fin (n + 2))) ⊆ Set.range ctx.E.c₂) :
    conjSub ctx.D.t M' ∈ centMembers Ω ctx.D.u ∧
      ∃ b : Bool, ctx.lab₁ (conjSub ctx.D.t M') =
        memBar (γ₂.map ctx.E.emb₂) (by rw [Finset.card_map]; exact hγ₂) b := by
  classical
  have hN := ctx.conjSub_t_mem hS hn hM' hγ₂c hlab
  refine ⟨hN, ?_⟩
  obtain ⟨δ, hδ, e', hlabN⟩ := ctx.D.IY.label _ hN
  have hwY : ctx.D.t * ctx.D.u * ctx.D.t⁻¹ ∈ pSpan (centMembers Ω ctx.D.u) :=
    ctx.D.hsub.span_le ctx.D.hw
  have hac : ctx.D.ι ctx.D.a ≠ ctx.D.ι ctx.D.c := ctx.D.ι.injective.ne ctx.D.hac
  have hΩc : ConjInvariant Ω := fun x L hL => hS.cex.hyp.conjInvariant x L hL
  have hNi : conjSub ctx.D.t M' ∈ conjSub ctx.D.t '' centMembers Ω ctx.D.u := ⟨M', hM', rfl⟩
  have hcomm := ((mem_conjSub_image_centMembers hΩc).mp hNi).2
  have hnot := (ctx.D.IY.comm_pairVec_iff (by omega) ctx.D.hHY.card ctx.D.hHY.conj_mem
    ctx.D.hHY.label_inj (w := ⟨_, hwY⟩) hac ctx.D.hpair hN hlabN).mp
    fun l hl => (hcomm l hl).symm
  obtain ⟨b, hb⟩ := ctx.lab₁_of_label hn hN hlabN
  have hαO : ((δ.map (globEmb₁ n) : Finset (Fin (n + 4))) : Set (Fin (n + 4))) ⊆ ctx.common := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hx)
    refine ⟨⟨y, rfl⟩, (ctx.E.range_emb₂ _).mpr ⟨fun h => hnot.1 ?_, fun h => hnot.2 ?_⟩⟩
    · rw [← (globEmb₁ n).injective h]
      exact hy
    · rw [← (globEmb₁ n).injective h]
      exact hy
  obtain ⟨-, β, hβ, e'', hlabβ, hβα⟩ := ctx.overlap hn hN hαO hb
  rw [conjSub_inv_conjSub] at hlabβ
  have hβγ : β = γ₂ := eq_of_memBar_eq' (by omega) (hlabβ.symm.trans hlab)
  subst hβγ
  exact ⟨b, hb.trans (memBar_congr hβα.symm rfl)⟩

theorem chart2' (hS : CSetting 3 IH Ω K J) (hn : 5 ≤ n) (τ : alternatingGroup (Fin (n + 2)))
    {M : Subgroup G} (hM : M ∈ centMembers Ω ctx.D.u) {γ : Finset (Fin (n + 2))}
    {hγ : γ.card = 4} {e : Bool}
    (hlab : (M.subgroupOf (pSpan (centMembers Ω ctx.D.u))).map ctx.D.IY.φ = memBar γ hγ e)
    {γ₂ : Finset (Fin (n + 2))} {hγ₂ : γ₂.card = 4} {e₂ : Bool}
    (hτ : permAct (τ : Equiv.Perm (Fin (n + 2))) (memBar γ hγ e) = memBar γ₂ hγ₂ e₂)
    (hγ₂c : (γ₂ : Set (Fin (n + 2))) ⊆ Set.range ctx.E.c₂) :
    ∃ N ∈ centMembers Ω ctx.D.u,
      N = conjSub ctx.D.t
        (conjSub ((ctx.E.s₁ τ : ↥(pSpan (centMembers Ω ctx.D.u))) : G) M) ∧
      conjSub ctx.D.t M = conjSub (ctx.f (altExt ctx.E.emb₂ τ⁻¹)) N ∧
      ∃ b : Bool, ctx.lab₁ N =
        memBar (γ₂.map ctx.E.emb₂) (by rw [Finset.card_map]; exact hγ₂) b := by
  classical
  set Y := pSpan (centMembers Ω ctx.D.u) with hY
  set s : G := ((ctx.E.s₁ τ : ↥Y) : G) with hs
  have hsY : s ∈ Y := (ctx.E.s₁ τ).2
  have hM' : conjSub s M ∈ centMembers Ω ctx.D.u := ctx.D.hHY.conj_mem M hM s hsY
  have hlab' : ((conjSub s M).subgroupOf Y).map ctx.D.IY.φ = memBar γ₂ hγ₂ e₂ := by
    have e2 := TL4.AECov.map_conjSub_eq ctx.D.IY M (ctx.E.s₁ τ)
    rw [ctx.E.hs₁ τ, hlab] at e2
    rw [e2]
    exact hτ
  obtain ⟨hN, b, hb⟩ := ctx.lab₁_conjSub_t hS hn hM' hlab' hγ₂c
  refine ⟨conjSub ctx.D.t (conjSub s M), hN, rfl, ?_, b, hb⟩
  have hsi : ((ctx.E.s₁ τ⁻¹ : ↥Y) : G) = s⁻¹ := by rw [map_inv]; rfl
  rw [ctx.hf₂ τ⁻¹, hsi, ← conjSub_mul, ← conjSub_mul]
  congr 1
  group

theorem mem_orb_of_disjoint (hn : 5 ≤ n)
    (hmove : ∀ i : Fin n, ctx.E.c₁ i ∈ Finset.univ.map ctx.D.ι →
      ctx.E.c₂ i ∉ ctx.D.γ.map ctx.D.ι)
    {P : Subgroup G} (hP : P ∈ centMembers Ω ctx.D.u) {β : Finset (Fin (n + 4))}
    {hβ : β.card = 4} {e : Bool} (hlab : ctx.lab₁ P = memBar β hβ e)
    (hd : Disjoint β ((ctx.D.γ.map ctx.D.ι).map ctx.E.emb₂)) :
    P ∈ orbOf (TC.nbrAdj Ω) K J := by
  classical
  set T₂ : Finset (Fin (n + 4)) := (ctx.D.γ.map ctx.D.ι).map ctx.E.emb₂ with hT₂
  have hT₂c : T₂.card = 4 := by
    rw [hT₂, Finset.card_map, Finset.card_map]
    exact ctx.D.hγ
  set Sι : Finset (Fin (n + 2)) := Finset.univ.map ctx.D.ι with hSι
  have hSιc : Sι.card = n := by
    rw [hSι, Finset.card_map, Finset.card_univ, Fintype.card_fin]
  have hnot : ∀ y ∈ Sι, globEmb₁ n y ∉ T₂ := by
    intro y hy hyT
    obtain ⟨w, hw, hwy⟩ := Finset.mem_map.mp hyT
    rcases ctx.E.cases₁ y with ⟨i, rfl⟩ | rfl | rfl
    · rw [← ctx.E.emb₂_c₂ i] at hwy
      exact hmove i hy (ctx.E.emb₂.injective hwy ▸ hw)
    · exact ((ctx.E.range_emb₂ _).mp ⟨w, hwy⟩).1 rfl
    · exact ((ctx.E.range_emb₂ _).mp ⟨w, hwy⟩).2 rfl
  have hS : Sι.map (globEmb₁ n) = Finset.univ \ T₂ := by
    refine Finset.eq_of_subset_of_card_le (fun x hx => ?_) ?_
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hnot y hy⟩
    · rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
        hT₂c, Finset.card_map, hSιc]
      omega
  obtain ⟨γ', hγ', b', hlabP, hγ'β⟩ := ctx.exists_label_self_of_lab₁ hn hP hlab
  have hγ'S : ∀ x ∈ γ', x ∈ Sι := by
    intro x hx
    have hxβ : globEmb₁ n x ∈ β := by
      rw [← hγ'β]
      exact Finset.mem_map_of_mem _ hx
    have hxT : globEmb₁ n x ∉ T₂ := fun h => Finset.disjoint_left.mp hd hxβ h
    have hx' : globEmb₁ n x ∈ Sι.map (globEmb₁ n) := by
      rw [hS]
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hxT⟩
    obtain ⟨y, hy, hyx⟩ := Finset.mem_map.mp hx'
    exact (globEmb₁ n).injective hyx ▸ hy
  obtain ⟨α, hα⟩ := exists_map_eq_of_subset ctx.D.ι (α := γ') fun x hx => by
    obtain ⟨z, -, hz⟩ := Finset.mem_map.mp (hγ'S x hx)
    exact ⟨z, hz⟩
  subst hα
  obtain ⟨L, hLπ, hLlab⟩ := ctx.D.hsub.surj α hγ' b'
  have hPL : P = L := ctx.D.hHY.label_inj P hP L (ctx.D.hπY hLπ) (hlabP.trans hLlab.symm)
  exact hPL ▸ hLπ

theorem exists_alt_to_common (hn : 5 ≤ n) {γ : Finset (Fin (n + 2))} (hγ : γ.card = 4) (b : Bool) :
    ∃ (τ : alternatingGroup (Fin (n + 2))) (γ₂ : Finset (Fin (n + 2))) (hγ₂ : γ₂.card = 4),
      (γ₂ : Set (Fin (n + 2))) ⊆ Set.range ctx.E.c₂ ∧
        permAct (τ : Equiv.Perm (Fin (n + 2))) (memBar γ hγ b) = memBar γ₂ hγ₂ true := by
  have hcard : 4 ≤ (Finset.univ.map ctx.E.c₂).card := by
    rw [Finset.card_map, Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨γ₂, hγ₂U, hγ₂⟩ := Finset.exists_subset_card_eq hcard
  have hγ₂c : (γ₂ : Set (Fin (n + 2))) ⊆ Set.range ctx.E.c₂ := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp (hγ₂U (Finset.mem_coe.mp hx))
    exact ⟨i, rfl⟩
  obtain ⟨τ, hτ⟩ := exists_alt_permAct_eq (m := n + 2) (by omega)
    (memBar_mem_memLabels γ hγ b) (memBar_mem_memLabels γ₂ hγ₂ true)
  exact ⟨τ, γ₂, hγ₂, hγ₂c, hτ⟩

theorem subHyp_common :
    SubHyp ctx.D.IY
      (ctx.D.IY.over ({ctx.D.ι ctx.D.a, ctx.D.ι ctx.D.c} : Finset (Fin (n + 2)))ᶜ) ctx.E.c₁ := by
  have hc₁r : Set.range ctx.E.c₁ =
      ((({ctx.D.ι ctx.D.a, ctx.D.ι ctx.D.c} : Finset (Fin (n + 2)))ᶜ : Finset (Fin (n + 2))) :
        Set (Fin (n + 2))) := by
    ext x
    rw [ctx.E.hc₁, Finset.mem_coe, Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hpΓ : ctx.D.ι ctx.D.a ∉
      ({ctx.D.ι ctx.D.a, ctx.D.ι ctx.D.c} : Finset (Fin (n + 2)))ᶜ := by
    rw [Finset.mem_compl, not_not]
    exact Finset.mem_insert_self _ _
  exact ctx.D.IY.subHyp_over_emb ctx.E.c₁ hc₁r hpΓ ctx.D.hHY.card ctx.D.hHY.conj_mem
    ctx.D.hHY.label_inj

theorem over_common_subset :
    ctx.D.IY.over ({ctx.D.ι ctx.D.a, ctx.D.ι ctx.D.c} : Finset (Fin (n + 2)))ᶜ ⊆
      conjSub ctx.D.t '' centMembers Ω ctx.D.u := by
  rintro M ⟨hM, β, hβ, e, hβΓ, hlab⟩
  obtain ⟨α, rfl⟩ := exists_map_eq_of_subset ctx.E.c₁ (α := β) fun x hx => by
    have := Finset.mem_compl.mp (hβΓ hx)
    rw [Finset.mem_insert, Finset.mem_singleton, not_or] at this
    exact (ctx.E.hc₁ x).mpr this
  exact ctx.E.hZ M hM α hβ e hlab

theorem disj_five (hS : CSetting 3 IH Ω K J) (hn : 5 ≤ n)
    (hmove : ∀ i : Fin n, ctx.E.c₁ i ∈ Finset.univ.map ctx.D.ι →
      ctx.E.c₂ i ∉ ctx.D.γ.map ctx.D.ι) :
    (ctx.labHyp' hn).Disj := by
  classical
  have hC := hS.toCHyp
  have hD := hS.cex.toThmDHyp
  have hK : K ∈ Ω := hS.adj.1
  have hJπ : J ∈ orbOf (TC.nbrAdj Ω) K J := mem_orbOf_self K J
  have hJY : J ∈ centMembers Ω ctx.D.u := ctx.D.hπY hJπ
  have hJsY : ctx.D.Js ∈ centMembers Ω ctx.D.u := ctx.D.hπY ctx.D.hJs
  obtain ⟨hγ', b₁, hlabJ₁⟩ := ctx.D.hlabι J hJπ ctx.D.γ ctx.D.hγ ctx.D.b ctx.D.hlabJ
  obtain ⟨hγ'', b₂, hlabJs₁⟩ :=
    ctx.D.hlabι ctx.D.Js ctx.D.hJs ctx.D.γ ctx.D.hγ (!ctx.D.b) ctx.D.hlabJs
  obtain ⟨τ, γ₂, hγ₂, hγ₂c, hτ⟩ := ctx.exists_alt_to_common hn hγ' b₁
  have hγ₂eq : (ctx.D.γ.map ctx.D.ι).map (τ : Equiv.Perm (Fin (n + 2))).toEmbedding = γ₂ :=
    map_eq_of_permAct_memBar (by omega) hτ
  obtain ⟨e₂, hτ₂⟩ := permAct_memBar (τ : Equiv.Perm (Fin (n + 2))) _ hγ'' b₂
  have hτ₂' : permAct (τ : Equiv.Perm (Fin (n + 2))) (memBar (ctx.D.γ.map ctx.D.ι) hγ'' b₂) =
      memBar γ₂ hγ₂ e₂ := hτ₂.trans (memBar_congr hγ₂eq rfl)
  obtain ⟨N₁, hN₁, hN₁eq, hK₁, b, hb⟩ := ctx.chart2' hS hn τ hJY hlabJ₁ hτ hγ₂c
  obtain ⟨N₂, hN₂, hN₂eq, hK₂, b', hb'⟩ := ctx.chart2' hS hn τ hJsY hlabJs₁ hτ₂' hγ₂c
  have hKst : conjSub ctx.D.t ctx.D.Js = ctx.D.Ks := by rw [← ctx.D.htKs', conjSub_conjSub_inv]
  have hK₁' : conjSub (ctx.f (altExt ctx.E.emb₂ τ⁻¹)) N₁ = K := hK₁.symm.trans ctx.D.ht'
  have hK₂' : conjSub (ctx.f (altExt ctx.E.emb₂ τ⁻¹)) N₂ = ctx.D.Ks := hK₂.symm.trans hKst
  have hJJs : J ≠ ctx.D.Js := by
    intro h
    have e := congrArg (fun L : Subgroup G =>
      (L.subgroupOf (pSpan (orbOf (TC.nbrAdj Ω) K J))).map I.φ) h
    rw [ctx.D.hlabJ, ctx.D.hlabJs] at e
    cases hb : ctx.D.b
    · rw [hb] at e
      exact memBar_true_ne_false hn ctx.D.γ ctx.D.hγ e.symm
    · rw [hb] at e
      exact memBar_true_ne_false hn ctx.D.γ ctx.D.hγ e
  have hbb : b ≠ b' := by
    rintro rfl
    have hNN : N₁ = N₂ := ctx.lab₁_injOn hn hN₁ hN₂ (hb.trans hb'.symm)
    rw [hN₁eq, hN₂eq] at hNN
    exact hJJs (conjSub_injective _ (conjSub_injective _ hNN))
  have hδ : (γ₂.map ctx.E.emb₂).card = 4 := by
    rw [Finset.card_map]
    exact hγ₂
  have hT₂sub : (ctx.D.γ.map ctx.D.ι).map ctx.E.emb₂ ⊆
      (γ₂.map ctx.E.emb₂).map
        ((altExt ctx.E.emb₂ τ⁻¹ : alternatingGroup (Fin (n + 4))) :
          Equiv.Perm (Fin (n + 4))).toEmbedding := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    refine Finset.mem_map.mpr ⟨ctx.E.emb₂ ((τ : Equiv.Perm (Fin (n + 2))) y),
      Finset.mem_map_of_mem _ ?_, ?_⟩
    · rw [← hγ₂eq]
      exact Finset.mem_map_of_mem (τ : Equiv.Perm (Fin (n + 2))).toEmbedding hy
    · show (altExt ctx.E.emb₂ τ⁻¹ : Equiv.Perm (Fin (n + 4))) _ = _
      rw [altExt_coe, extPerm_apply_mem]
      show ctx.E.emb₂ ((τ : Equiv.Perm (Fin (n + 2)))⁻¹ ((τ : Equiv.Perm (Fin (n + 2))) y)) = _
      rw [perm_inv_apply]
  have hTT₂ : missing₁ n ⊆ (ctx.D.γ.map ctx.D.ι).map ctx.E.emb₂ := by
    intro x hx
    simp only [missing₁, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · refine Finset.mem_map.mpr ⟨ctx.D.ι ctx.D.a', Finset.mem_map_of_mem _ ctx.D.ha', ?_⟩
      exact (ctx.E.emb₂_apply _).trans ctx.E.emb₂Fun_a'
    · refine Finset.mem_map.mpr ⟨ctx.D.ι ctx.D.c', Finset.mem_map_of_mem _ ctx.D.hc', ?_⟩
      exact (ctx.E.emb₂_apply _).trans ctx.E.emb₂Fun_c'
  have hcomm : ∀ P ∈ centMembers Ω ctx.D.u, ∀ (β : Finset (Fin (n + 4))) (hβ : β.card = 4)
      (e : Bool), ctx.lab₁ P = memBar β hβ e →
      Disjoint β ((γ₂.map ctx.E.emb₂).map
        ((altExt ctx.E.emb₂ τ⁻¹ : alternatingGroup (Fin (n + 4))) :
          Equiv.Perm (Fin (n + 4))).toEmbedding) →
      (∀ a ∈ K, ∀ y ∈ P, a * y = y * a) ∧ (∀ a ∈ ctx.D.Ks, ∀ y ∈ P, a * y = y * a) := by
    intro P hP β hβ e hlab hd
    have hPπ : P ∈ orbOf (TC.nbrAdj Ω) K J :=
      ctx.mem_orb_of_disjoint hn hmove hP hlab (Finset.disjoint_of_subset_right hT₂sub hd)
    refine ⟨comm_of_mem_omegaNbr hD.hyp hD.two hK (hC.orb_subset hPπ), fun a ha y hy => ?_⟩
    exact (ctx.D.hKsX y (le_pSpan hPπ hy) a ha).symm
  have hT := hTT₂.trans hT₂sub
  refine ⟨?_⟩
  cases b <;> cases b'
  · exact absurd rfl hbb
  ·
    refine ⟨altExt ctx.E.emb₂ τ⁻¹, γ₂.map ctx.E.emb₂, hδ, N₂, N₁, hN₂, hN₁, hb', hb, hT,
      fun P hP β hβ e hlab hd => ?_⟩
    obtain ⟨h₁, h₂⟩ := hcomm P hP β hβ e hlab hd
    rw [hK₂', hK₁']
    exact ⟨h₂, h₁⟩
  · refine ⟨altExt ctx.E.emb₂ τ⁻¹, γ₂.map ctx.E.emb₂, hδ, N₁, N₂, hN₁, hN₂, hb, hb', hT,
      fun P hP β hβ e hlab hd => ?_⟩
    obtain ⟨h₁, h₂⟩ := hcomm P hP β hβ e hlab hd
    rw [hK₁', hK₂']
    exact ⟨h₁, h₂⟩
  · exact absurd rfl hbb

end LabCtx

end CFSG.ClassicalInvolution.Q3.TC.Thin
