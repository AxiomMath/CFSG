module

public import CFSG.ClassicalInvolution.Q3.TL3T66
public import CFSG.ClassicalInvolution.Q3.TL3T76
public import CFSG.ClassicalInvolution.Q3.TL3T72C

public section

namespace CFSG.ClassicalInvolution.Q3.AE

open Wr

variable {n : ℕ}

theorem ofPerm_comm_of_supportedOn {σ : Equiv.Perm (Fin n)} {w : Wr n} {s : Set (Fin n)}
    (hw : SupportedOn w s) (hσ : ∀ x ∈ s, σ x = x) : ofPerm σ * w = w * ofPerm σ := by
  have hσs : ∀ x, x ∉ s → σ x ∉ s := fun x hx h => hx (by
    have := σ.injective (hσ _ h)
    rw [this] at h
    exact h)
  have hσi : ∀ x ∈ s, σ.symm x = x := fun x hx => by
    conv_lhs => rw [← hσ x hx]
    exact σ.symm_apply_apply x
  have hσs' : ∀ x, x ∉ s → σ.symm x ∉ s := fun x hx h => hx (by
    have := hσ _ h
    rw [Equiv.apply_symm_apply] at this
    rw [this]
    exact h)
  have hws : ∀ x ∈ s, w.perm x ∈ s := fun x hx => by
    by_contra h
    have := (hw _ h).2
    rw [w.perm.injective this] at h
    exact h hx
  refine Wr.ext (funext fun i => ?_) ?_
  · rw [mul_vec, mul_vec]
    show (0 : ZMod 2) + w.vec (σ.symm i) = w.vec i + 0
    rw [zero_add, add_zero]
    by_cases hi : i ∈ s
    · rw [hσi i hi]
    · rw [(hw _ hi).1, (hw _ (hσs' i hi)).1]
  · show σ * w.perm = w.perm * σ
    refine Equiv.ext fun i => ?_
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
    by_cases hi : i ∈ s
    · rw [hσ i hi, hσ _ (hws i hi)]
    · rw [(hw i hi).2, (hw _ (hσs i hi)).2]

theorem ofPerm_comm_memBar {σ : Equiv.Perm (Fin n)} {α : Finset (Fin n)} (h : α.card = 4)
    (b : Bool) (hσ : ∀ x ∈ α, σ x = x) :
    ∀ y ∈ memBar α h b, mkQ n (ofPerm σ) * y = y * mkQ n (ofPerm σ) := by
  rintro _ ⟨w, hw, rfl⟩
  have hs := supportedOn_of_mem_memAt hw
  rw [range_emb] at hs
  rw [← map_mul, ← map_mul,
    ofPerm_comm_of_supportedOn hs fun x hx => hσ x (Finset.mem_coe.mp hx)]

end CFSG.ClassicalInvolution.Q3.AE

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph
open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
open CFSG.ComponentClassification.PresentationLocal Amalg

theorem bool_eq_not_of_ne {a b : Bool} (h : a ≠ b) : a = !b := by
  cases a <;> cases b <;> first | rfl | exact absurd rfl h

variable {G : Type} [Group G] [Finite G] {IH : ℕ → Prop} {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {n : ℕ} {I : AEIdent (orbOf (TC.nbrAdj Ω) K J) n} {D : PairChart Ω K J I}

namespace GlueData

variable (E : GlueData D)

theorem s₁_mem_orb (hn : 5 ≤ n) {σ : alternatingGroup (Fin (n + 2))}
    (hσ : ∀ x, x ∉ D.γ.map D.ι → (σ : Equiv.Perm (Fin (n + 2))) x = x) :
    ((E.s₁ σ : ↥(pSpan (centMembers Ω D.u))) : G) ∈ pSpan (orbOf (TC.nbrAdj Ω) K J) := by
  have hσ' : ∀ x, x ∉ Set.range D.ι → (σ : Equiv.Perm (Fin (n + 2))) x = x := by
    intro x hx
    refine hσ x fun h => hx ?_
    obtain ⟨y, -, rfl⟩ := Finset.mem_map.mp h
    exact ⟨y, rfl⟩
  obtain ⟨τ, rfl⟩ := exists_altExt_eq D.ι σ hσ'
  exact D.IY.section_mem_restrict hn D.hHY.ker_two D.hsub E.hs₁ τ

omit [Finite G] in
theorem conjSub_g_mem_orb {M : Subgroup G} (hM : M ∈ orbOf (TC.nbrAdj Ω) K J) :
    conjSub E.g M ∈ orbOf (TC.nbrAdj Ω) K J := by
  obtain ⟨α, hα, e, hlab⟩ := I.label M hM
  obtain ⟨hα', e₁, hlab₁⟩ := D.hlabι M hM α hα e hlab
  obtain ⟨v, hv⟩ := E.hgv
  have hmem := D.hHY.conj_mem M (D.hπY hM) E.g E.hgY
  have hl : ((conjSub E.g M).subgroupOf (pSpan (centMembers Ω D.u))).map D.IY.φ =
      conjSub (mkQ (n + 2) (ofVec v)) (memBar (α.map D.ι) hα' e₁) := by
    have := TL4.AECov.map_conjSub_eq D.IY M ⟨E.g, E.hgY⟩
    rw [hv, hlab₁] at this
    exact this
  rcases TL4.AECov.conjSub_memBar_of_perm_eq_one (w := ofVec v) rfl (α.map D.ι) hα' e₁ with
    h1 | h1
  · obtain ⟨M', hM', hlab'⟩ := D.hsub.surj α hα' true
    rw [D.hHY.label_inj _ hmem M' (D.hsub.sub hM') (by rw [hl, h1, hlab'])]
    exact hM'
  · obtain ⟨M', hM', hlab'⟩ := D.hsub.surj α hα' false
    rw [D.hHY.label_inj _ hmem M' (D.hsub.sub hM') (by rw [hl, h1, hlab'])]
    exact hM'

theorem conj_g_s₁_mem_orb (hn : 5 ≤ n) {σ : alternatingGroup (Fin (n + 2))}
    (hσ : ∀ x, x ∉ D.γ.map D.ι → (σ : Equiv.Perm (Fin (n + 2))) x = x) :
    E.g * ((E.s₁ σ : ↥(pSpan (centMembers Ω D.u))) : G) * E.g⁻¹ ∈
      pSpan (orbOf (TC.nbrAdj Ω) K J) :=
  conj_mem_pSpan_of_conj (fun _ hM => E.conjSub_g_mem_orb hM) (E.s₁_mem_orb hn hσ)

theorem comm_orb_of_three (hS : CSetting 3 IH Ω K J) (hn : 5 ≤ n)
    {σ : alternatingGroup (Fin (n + 2))}
    (hσ : ∀ x, x ∉ D.γ.map D.ι → (σ : Equiv.Perm (Fin (n + 2))) x = x) (h3 : σ ^ 3 = 1) :
    ∀ x ∈ pSpan (orbOf (TC.nbrAdj Ω) K J),
      (D.t * ((E.s₁ σ : ↥(pSpan (centMembers Ω D.u))) : G) * D.t⁻¹) * x =
        x * (D.t * ((E.s₁ σ : ↥(pSpan (centMembers Ω D.u))) : G) * D.t⁻¹) := by
  classical
  by_cases hn7 : n = 7
  · exact E.comm_orb_of_three_seven hS hn7 hσ h3
  have hC := hS.toCHyp
  have hD := hS.cex.toThmDHyp
  have hF := hC.graphFam'
  have hn5 : 5 ≤ n := hn
  have hK : K ∈ Ω := hS.adj.1
  have hJπ : J ∈ orbOf (TC.nbrAdj Ω) K J := mem_orbOf_self K J
  have hJΩ : J ∈ Ω := hC.orb_subset_omega hJπ
  have h8 : ∀ L ∈ Ω, Nat.card L = 8 := fun L hL => by rw [hD.card L hL]; norm_num
  have hH := hC.aeCoverHyp_orb' hn5 I
  have hH₁ := D.hHY
  obtain ⟨hti, hti'⟩ := CHyp.swap_inv D.ht D.ht'
  set x₀ : G := ((E.s₁ σ : ↥(pSpan (centMembers Ω D.u))) : G) with hx₀
  set y : G := D.t * x₀ * D.t⁻¹ with hy
  have hx₀X : x₀ ∈ pSpan (orbOf (TC.nbrAdj Ω) K J) := E.s₁_mem_orb hn5 hσ
  have hx₀3 : x₀ ^ 3 = 1 := by
    rw [hx₀, ← Subgroup.coe_pow, ← map_pow, h3, map_one, Subgroup.coe_one]
  have hy3 : y ^ 3 = 1 := by rw [hy, conj_pow, hx₀3, mul_one, mul_inv_cancel]
  set β₁ := D.γ.map D.ι with hβ₁
  obtain ⟨hβ', b₁, hlabJ₁⟩ := D.hlabι J hJπ D.γ D.hγ D.b D.hlabJ
  obtain ⟨hβ'', b₂, hlabJs₁⟩ := D.hlabι D.Js D.hJs D.γ D.hγ (!D.b) D.hlabJs
  have hJY : J ∈ centMembers Ω D.u := D.hπY hJπ
  have hJsY : D.Js ∈ centMembers Ω D.u := D.hπY D.hJs
  have hJJs : J ≠ D.Js := by
    intro h
    have e := congrArg (fun L : Subgroup G =>
      (L.subgroupOf (pSpan (orbOf (TC.nbrAdj Ω) K J))).map I.φ) h
    rw [D.hlabJ, D.hlabJs] at e
    cases hb : D.b
    · rw [hb] at e
      exact memBar_true_ne_false hn5 D.γ D.hγ e.symm
    · rw [hb] at e
      exact memBar_true_ne_false hn5 D.γ D.hγ e
  have hb12 : b₁ ≠ b₂ := by
    rintro rfl
    exact hJJs (hH₁.label_inj J hJY D.Js hJsY (hlabJ₁.trans hlabJs₁.symm))
  have hσβ : β₁.map (σ : Equiv.Perm (Fin (n + 2))).toEmbedding = β₁ := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hx
      by_contra hn'
      have e := hσ _ hn'
      simp only [Equiv.coe_toEmbedding] at e hn'
      rw [(σ : Equiv.Perm (Fin (n + 2))).injective e] at hn'
      exact hn' hz
    · exact (Finset.card_map _).ge
  have hmemS : ∀ {L : Subgroup G}, L ∈ centMembers Ω D.u → ∀ {e : Bool},
      (L.subgroupOf (pSpan (centMembers Ω D.u))).map D.IY.φ = memBar β₁ hβ' e →
      conjSub x₀ L = J ∨ conjSub x₀ L = D.Js := by
    intro L hL e hl
    obtain ⟨e', he'⟩ := exists_conj_ofPerm_memBar (σ : Equiv.Perm (Fin (n + 2))) β₁ hβ' e
    have hmem := hH₁.conj_mem L hL x₀ (E.s₁ σ).2
    have hl' : ((conjSub x₀ L).subgroupOf (pSpan (centMembers Ω D.u))).map D.IY.φ =
        memBar β₁ hβ' e' := by
      have := TL4.AECov.map_conjSub_eq D.IY L (E.s₁ σ)
      rw [E.hs₁, hl] at this
      refine this.trans (he'.trans ?_)
      congr 1
    by_cases hb : e' = b₁
    · subst hb
      exact Or.inl (hH₁.label_inj _ hmem J hJY (hl'.trans hlabJ₁.symm))
    · have : e' = b₂ := by
        cases e' <;> cases b₁ <;> cases b₂ <;>
          first | rfl | exact absurd rfl hb | exact absurd rfl hb12
      subst this
      exact Or.inr (hH₁.label_inj _ hmem D.Js hJsY (hl'.trans hlabJs₁.symm))
  have hx₀J : conjSub x₀ J = J := by
    rcases hmemS hJY hlabJ₁ with h | h
    · exact h
    · exfalso
      have h2 : conjSub x₀ D.Js = J := by
        rcases hmemS hJsY hlabJs₁ with h' | h'
        · exact h'
        · exact absurd (conjSub_injective x₀ (h.trans h'.symm)) hJJs
      have h3' : conjSub (x₀ ^ 3) J = D.Js := by
        rw [pow_succ, pow_two, conjSub_mul, conjSub_mul, h, h2, h]
      rw [hx₀3, conjSub_one] at h3'
      exact hJJs h3'
  have hyK : conjSub y K = K := by
    rw [hy, conjSub_mul, conjSub_mul, hti, hx₀J, D.ht']
  have hperm : ∀ M ∈ orbOf (TC.nbrAdj Ω) K J, conjSub y M ∈ orbOf (TC.nbrAdj Ω) K J :=
    fun M hM => by
      rw [← hC.conjSub_orb_of_mem_normalizer hyK]
      exact ⟨M, hM, rfl⟩
  have hnorm := hC.mem_normalizer_orb_of_conjSub hyK
  have hyX' : y ∈ pSpan (orbOf (TC.nbrAdj Ω) J K) := by
    have he : conjSub D.t '' orbOf (TC.nbrAdj Ω) K J = orbOf (TC.nbrAdj Ω) J K := by
      rw [← orbOf_conj hF.graph K J D.t, D.ht, D.ht']
    have := (pSpanConj D.t (orbOf (TC.nbrAdj Ω) K J) ⟨x₀, hx₀X⟩).2
    rw [pSpanConj_apply, he] at this
    exact this
  have hJK : TC.nbrAdj Ω J K := hF.graph.symm hS.adj
  have hXJ : pSpan (orbOf (TC.nbrAdj Ω) J K) ≤ Subgroup.centralizer (J : Set G) :=
    (pSpan_le fun L hL => le_pSpan (adj_of_mem_orbOf hF.graph hJK hL).2).trans
      (pSpan_omegaNbr_le_centralizer hD.hyp hD.two hJΩ)
  have hJsKs : conjSub D.t D.Js = D.Ks := by rw [← D.htKs', conjSub_conjSub_inv]
  have hcond : ∀ M ∈ orbOf (TC.nbrAdj Ω) K J, ∀ (β : Finset (Fin n)) (hβ : β.card = 4)
      (c : Bool), (M.subgroupOf (pSpan (orbOf (TC.nbrAdj Ω) K J))).map I.φ = memBar β hβ c →
      (β = D.γ ∨ Disjoint β D.γ) → M ≠ D.Ks → ∀ m ∈ M, y * m = m * y := by
    intro M hM β hβ c hlab hβγ _ m hm
    rcases hβγ with rfl | hd
    · have hMJ : M = J ∨ M = D.Js := by
        by_cases hc : c = D.b
        · subst hc
          exact Or.inl (hH.label_inj M hM J hJπ (hlab.trans D.hlabJ.symm))
        · have := bool_eq_not_of_ne hc
          subst this
          exact Or.inr (hH.label_inj M hM D.Js D.hJs (hlab.trans D.hlabJs.symm))
      rcases hMJ with rfl | rfl
      · exact ((Subgroup.mem_centralizer_iff.mp (hXJ hyX')) m hm).symm
      · have hm' : D.t⁻¹ * m * D.t ∈ D.Ks := by
          have := conj_mem_conjSub (n := D.t⁻¹) hm
          rwa [← D.htKs, conjSub_inv_conjSub, inv_inv] at this
        have e := D.hKsX x₀ hx₀X _ hm'
        calc y * m = D.t * (x₀ * (D.t⁻¹ * m * D.t)) * D.t⁻¹ := by rw [hy]; group
          _ = D.t * ((D.t⁻¹ * m * D.t) * x₀) * D.t⁻¹ := by rw [e]
          _ = m * y := by rw [hy]; group
    · have hβγ : β ≠ D.γ := by
        rintro rfl
        obtain ⟨x, hx⟩ := Finset.card_pos.mp (by rw [D.hγ]; norm_num : 0 < D.γ.card)
        exact Finset.disjoint_left.mp hd hx hx
      have hMJ : M ≠ J := by
        rintro rfl
        exact hβγ (eq_of_memBar_eq' hn5 (hlab.symm.trans D.hlabJ))
      have hMJs : M ≠ D.Js := by
        rintro rfl
        exact hβγ (eq_of_memBar_eq' hn5 (hlab.symm.trans D.hlabJs))
      have hMJc : ∀ a ∈ M, ∀ b ∈ J, a * b = b * a :=
        aeIdent_comm_of_map_comm hD.hyp hD.two hC.orb_subset_omega I hH.ker_two hM hJπ hMJ
          (by rw [hlab, D.hlabJ]; exact comm_memBar_of_disjoint hd c D.b)
      have hMKc : ∀ a ∈ K, ∀ b ∈ M, a * b = b * a :=
        comm_of_mem_omegaNbr hD.hyp hD.two hK (hC.orb_subset hM)
      set M' := conjSub D.t⁻¹ M with hM'
      have hM'Ω : M' ∈ Ω := hS.cex.hyp.conjInvariant _ M (hC.orb_subset_omega hM)
      have hM't : conjSub D.t M' = M := conjSub_conjSub_inv D.t M
      have hM'J : ∀ a ∈ M', ∀ b ∈ J, a * b = b * a := by
        have := comm_conjSub (fun a ha b hb => (hMKc b hb a ha).symm) D.t⁻¹
        rwa [hti] at this
      have hM'K : ∀ a ∈ M', ∀ b ∈ K, a * b = b * a := by
        have := comm_conjSub hMJc D.t⁻¹
        rwa [hti'] at this
      have hM'K' : M' ≠ K := by
        intro h
        apply hMJ
        rw [← hM't, h, D.ht]
      have hM'N : M' ∈ omegaNbr Ω K :=
        (TC.mem_omegaNbr_iff hD.hyp hD.two).mpr ⟨hM'Ω, hM'K', le_normalizer_of_comm hM'K⟩
      obtain ⟨I'⟩ := hC.nonempty_aeIdent_swap I
      have hM'π : M' ∈ orbOf (TC.nbrAdj Ω) K J := by
        rcases hS.eq_of_mem_omegaNbr_of_five_le hn5 I I' D.hKs D.hKsK D.hKsπ D.hz D.hKsX hM'N
          with h | h
        · exact h
        · exfalso
          apply hMJs
          rw [← hM't, h, D.htKs]
      have hM'J' : M' ≠ J := by
        intro h
        have hMK : M = K := by rw [← hM't, h, D.ht']
        exact (hC.orb_subset (show K ∈ orbOf (TC.nbrAdj Ω) K J from hMK ▸ hM)).2.1 rfl
      have hM'Js : M' ≠ D.Js := by
        intro h
        have hMKs : M = D.Ks := by rw [← hM't, h, hJsKs]
        exact D.hKsπ (hMKs ▸ hM)
      obtain ⟨δ, hδ, e, hlabM'⟩ := I.label M' hM'π
      have hδγ : Disjoint δ D.γ := by
        have himg : ∀ a ∈ memBar δ hδ e, ∀ b ∈ memBar D.γ D.hγ D.b, a * b = b * a := by
          intro a ha b hb
          rw [← hlabM'] at ha
          rw [← D.hlabJ] at hb
          obtain ⟨l, hl, rfl⟩ := I.exists_of_mem_map hM'π ha
          obtain ⟨j, hj, rfl⟩ := I.exists_of_mem_map hJπ hb
          rw [← map_mul, ← map_mul]
          exact congrArg I.φ (Subtype.ext (hM'J l hl j hj))
        rcases eq_or_disjoint_of_comm himg with h | h
        · exfalso
          subst h
          by_cases he : e = D.b
          · subst he
            exact hM'J' (hH.label_inj M' hM'π J hJπ (hlabM'.trans D.hlabJ.symm))
          · have := bool_eq_not_of_ne he
            subst this
            exact hM'Js (hH.label_inj M' hM'π D.Js D.hJs (hlabM'.trans D.hlabJs.symm))
        · exact h
      obtain ⟨hδ', e', hlabM'₁⟩ := D.hlabι M' hM'π δ hδ e hlabM'
      have hdisj' : Disjoint (δ.map D.ι) (D.γ.map D.ι) := (Finset.disjoint_map D.ι).mpr hδγ
      have hcomm := D.IY.comm_member (by omega) hH₁.card hH₁.conj_mem hH₁.label_inj
        (D.hπY hM'π) (E.s₁ σ) (by
          rw [hlabM'₁, E.hs₁]
          exact ofPerm_comm_memBar hδ' e' fun x hx => hσ x (Finset.disjoint_left.mp hdisj' hx))
      have hm' : D.t⁻¹ * m * D.t ∈ M' := by
        have := conj_mem_conjSub (n := D.t⁻¹) hm
        rwa [inv_inv] at this
      have e2 := hcomm _ hm'
      calc y * m = D.t * (x₀ * (D.t⁻¹ * m * D.t)) * D.t⁻¹ := by rw [hy]; group
        _ = D.t * ((D.t⁻¹ * m * D.t) * x₀) * D.t⁻¹ := by rw [e2]
        _ = m * y := by rw [hy]; group
  exact ae3Rigid hn5 hn7 G Ω hD.hyp hD.two h8 _ hC.orb_subset_omega I hH.ker_two y
    ⟨1, by rw [pow_one]; exact hy3⟩ hperm hnorm D.γ D.hγ D.Ks hcond

theorem comm_orb (hS : CSetting 3 IH Ω K J) (hn : 5 ≤ n) {σ : alternatingGroup (Fin (n + 2))}
    (hσ : ∀ x, x ∉ D.γ.map D.ι → (σ : Equiv.Perm (Fin (n + 2))) x = x) :
    ∀ x ∈ pSpan (orbOf (TC.nbrAdj Ω) K J),
      (D.t * ((E.s₁ σ : ↥(pSpan (centMembers Ω D.u))) : G) * D.t⁻¹) * x =
        x * (D.t * ((E.s₁ σ : ↥(pSpan (centMembers Ω D.u))) : G) * D.t⁻¹) := by
  classical
  set β₁ := D.γ.map D.ι with hβ₁
  have hβ₁c : β₁.card = 4 := by rw [hβ₁, Finset.card_map]; exact D.hγ
  set ι₄ := emb β₁ hβ₁c with hι₄
  have hr : Set.range ι₄ = (β₁ : Set (Fin (n + 2))) := range_emb β₁ hβ₁c
  obtain ⟨τ, rfl⟩ := exists_altExt_eq ι₄ σ fun x hx =>
    hσ x fun h => hx (by rw [hr]; exact_mod_cast h)
  set φ : alternatingGroup (Fin 4) →* G := (MulAut.conj D.t).toMonoidHom.comp
    ((pSpan (centMembers Ω D.u)).subtype.comp (E.s₁.comp (altExt ι₄))) with hφ
  set H := (Subgroup.centralizer (pSpan (orbOf (TC.nbrAdj Ω) K J) : Set G)).comap φ with hH
  have hle : Subgroup.closure {c : Equiv.Perm (Fin 4) | c.IsThreeCycle} ≤
      H.map (alternatingGroup (Fin 4)).subtype := by
    rw [Subgroup.closure_le]
    intro c hc
    have hcA : c ∈ alternatingGroup (Fin 4) := Equiv.Perm.IsThreeCycle.mem_alternatingGroup hc
    refine ⟨⟨c, hcA⟩, ?_, rfl⟩
    show φ ⟨c, hcA⟩ ∈ Subgroup.centralizer _
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hc3 : (⟨c, hcA⟩ : alternatingGroup (Fin 4)) ^ 3 = 1 := Subtype.ext (by
      simp only [Subgroup.coe_pow, Subgroup.coe_one]
      show c ^ 3 = 1
      rw [← hc.orderOf]
      exact pow_orderOf_eq_one c)
    have h3 : (altExt ι₄ ⟨c, hcA⟩) ^ 3 = 1 := by rw [← map_pow, hc3, map_one]
    have hsupp : ∀ x, x ∉ D.γ.map D.ι →
        ((altExt ι₄ ⟨c, hcA⟩ : alternatingGroup (Fin (n + 2))) : Equiv.Perm (Fin (n + 2))) x = x := by
      intro x hx
      rw [altExt_coe]
      exact extPerm_apply_not_mem ι₄ _ (by rw [hr]; exact_mod_cast hx)
    exact (E.comm_orb_of_three hS hn hsupp h3 x hx).symm
  rw [Equiv.Perm.closure_three_cycles_eq_alternating] at hle
  have hτ : τ ∈ H := by
    obtain ⟨τ'', hτ'', he⟩ := hle τ.2
    have : τ'' = τ := Subtype.ext he
    rwa [this] at hτ''
  intro x hx
  exact ((Subgroup.mem_centralizer_iff.mp hτ) x hx).symm

theorem exists_hom (hS : CSetting 3 IH Ω K J) (hn : 5 ≤ n) :
    ∃ f : alternatingGroup (Fin (n + 4)) →* G,
      (∀ σ, f (altExt (globEmb₁ n) σ) =
        E.g * ((E.s₁ σ : ↥(pSpan (centMembers Ω D.u))) : G) * E.g⁻¹) ∧
      ∀ σ, f (altExt E.emb₂ σ) = D.t * ((E.s₁ σ : ↥(pSpan (centMembers Ω D.u))) : G) * D.t⁻¹ :=
  E.exists_glue hn fun _ _ h1 h2 =>
    (E.comm_orb hS hn h2 _ (E.conj_g_s₁_mem_orb hn h1)).symm

end GlueData

end CFSG.ClassicalInvolution.Q3.TC.Thin
