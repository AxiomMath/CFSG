module

public import CFSG.ClassicalInvolution.Q3.TL3T65

public section

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph
open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
open CFSG.ComponentClassification.PresentationLocal Amalg

variable {G : Type} [Group G] [Finite G] {IH : ℕ → Prop} {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {n : ℕ} {I : AEIdent (orbOf (TC.nbrAdj Ω) K J) n} {D : PairChart Ω K J I}

private theorem ofPerm_comm_supp {σ : Equiv.Perm (Fin n)} {w : Wr n} {s : Set (Fin n)}
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

private theorem ofPerm_comm_bar {σ : Equiv.Perm (Fin n)} {α : Finset (Fin n)} (h : α.card = 4)
    (b : Bool) (hσ : ∀ x ∈ α, σ x = x) :
    ∀ y ∈ memBar α h b, mkQ n (ofPerm σ) * y = y * mkQ n (ofPerm σ) := by
  rintro _ ⟨w, hw, rfl⟩
  have hs := supportedOn_of_mem_memAt hw
  rw [range_emb] at hs
  rw [← map_mul, ← map_mul,
    ofPerm_comm_supp hs fun x hx => hσ x (Finset.mem_coe.mp hx)]

private theorem twin_labels (D : PairChart Ω K J I) (hn5 : 5 ≤ n) :
    ∃ (hβ : (D.γ.map D.ι).card = 4) (b₁ b₂ : Bool), b₁ ≠ b₂ ∧ J ≠ D.Js ∧
      (J.subgroupOf (pSpan (centMembers Ω D.u))).map D.IY.φ = memBar (D.γ.map D.ι) hβ b₁ ∧
      (D.Js.subgroupOf (pSpan (centMembers Ω D.u))).map D.IY.φ = memBar (D.γ.map D.ι) hβ b₂ := by
  have hJπ : J ∈ orbOf (TC.nbrAdj Ω) K J := mem_orbOf_self K J
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
    exact hJJs (D.hHY.label_inj J hJY D.Js hJsY (hlabJ₁.trans hlabJs₁.symm))
  exact ⟨hβ', b₁, b₂, hb12, hJJs, hlabJ₁, hlabJs₁⟩

namespace GlueData

variable (E : GlueData D)

private theorem s₁_mem_orb' (hn : 5 ≤ n) {σ : alternatingGroup (Fin (n + 2))}
    (hσ : ∀ x, x ∉ D.γ.map D.ι → (σ : Equiv.Perm (Fin (n + 2))) x = x) :
    ((E.s₁ σ : ↥(pSpan (centMembers Ω D.u))) : G) ∈ pSpan (orbOf (TC.nbrAdj Ω) K J) := by
  have hσ' : ∀ x, x ∉ Set.range D.ι → (σ : Equiv.Perm (Fin (n + 2))) x = x := by
    intro x hx
    refine hσ x fun h => hx ?_
    obtain ⟨y, -, rfl⟩ := Finset.mem_map.mp h
    exact ⟨y, rfl⟩
  obtain ⟨τ, rfl⟩ := exists_altExt_eq D.ι σ hσ'
  exact D.IY.section_mem_restrict hn D.hHY.ker_two D.hsub E.hs₁ τ

theorem comm_of_chart2 (hS : CSetting 3 IH Ω K J) (hn : 5 ≤ n)
    {σ : alternatingGroup (Fin (n + 2))}
    (hσ : ∀ x, x ∉ D.γ.map D.ι → (σ : Equiv.Perm (Fin (n + 2))) x = x)
    {M : Subgroup G} (hM : M ∈ orbOf (TC.nbrAdj Ω) K J) {δ : Finset (Fin n)} (hδ : δ.card = 4)
    (hδac : ∀ x ∈ δ, x ≠ D.a ∧ x ≠ D.c) {e : Bool}
    (hlab : (M.subgroupOf (pSpan (orbOf (TC.nbrAdj Ω) K J))).map I.φ = memBar δ hδ e) :
    ∀ m ∈ M, (D.t * ((E.s₁ σ : ↥(pSpan (centMembers Ω D.u))) : G) * D.t⁻¹) * m =
      m * (D.t * ((E.s₁ σ : ↥(pSpan (centMembers Ω D.u))) : G) * D.t⁻¹) := by
  classical
  have hC := hS.toCHyp
  have hD := hS.cex.toThmDHyp
  have hK : K ∈ Ω := hS.adj.1
  have hJπ : J ∈ orbOf (TC.nbrAdj Ω) K J := mem_orbOf_self K J
  have hJY : J ∈ centMembers Ω D.u := D.hπY hJπ
  have hJsY : D.Js ∈ centMembers Ω D.u := D.hπY D.hJs
  have hH₁ := D.hHY
  obtain ⟨hti, -⟩ := CHyp.swap_inv D.ht D.ht'
  obtain ⟨hβ, b₁, b₂, hb12, -, hlabJ₁, hlabJs₁⟩ := twin_labels D hn
  have hJsKs : conjSub D.t D.Js = D.Ks := by rw [← D.htKs', conjSub_conjSub_inv]
  obtain ⟨hδ', e', hlabM₁⟩ := D.hlabι M hM δ hδ e hlab
  obtain ⟨δ₀, hδ₀⟩ := exists_map_eq_of_subset E.c₁ (α := δ.map D.ι) fun y hy => by
    obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hy
    exact (E.hc₁ _).mpr ⟨fun h => (hδac z hz).1 (D.ι.injective h),
      fun h => (hδac z hz).2 (D.ι.injective h)⟩
  have hδ₀' : (δ₀.map E.c₁).card = 4 := by rw [hδ₀]; exact hδ'
  obtain ⟨L, hL, hLM⟩ := E.hZ M (D.hπY hM) δ₀ hδ₀' e' (by
    rw [hlabM₁]
    congr 1
    exact hδ₀.symm)
  have hMK : ∀ a ∈ K, ∀ b ∈ M, a * b = b * a :=
    comm_of_mem_omegaNbr hD.hyp hD.two hK (hC.orb_subset hM)
  have hLJ : ∀ a ∈ L, ∀ b ∈ J, a * b = b * a := by
    have := comm_conjSub (fun a ha b hb => (hMK b hb a ha).symm) D.t⁻¹
    rwa [← hLM, conjSub_inv_conjSub, hti] at this
  obtain ⟨β, hβ₀, e₃, hlabL⟩ := D.IY.label L hL
  have himg : ∀ a ∈ memBar β hβ₀ e₃, ∀ b ∈ memBar (D.γ.map D.ι) hβ b₁, a * b = b * a := by
    intro a ha b hb
    rw [← hlabL] at ha
    rw [← hlabJ₁] at hb
    obtain ⟨l, hl, rfl⟩ := D.IY.exists_of_mem_map hL ha
    obtain ⟨j, hj, rfl⟩ := D.IY.exists_of_mem_map hJY hb
    rw [← map_mul, ← map_mul]
    exact congrArg D.IY.φ (Subtype.ext (hLJ l hl j hj))
  have hβJ : Disjoint β (D.γ.map D.ι) := by
    rcases eq_or_disjoint_of_comm himg with h | h
    · exfalso
      subst h
      by_cases he : e₃ = b₁
      · subst he
        have hLJ' : L = J := hH₁.label_inj L hL J hJY (hlabL.trans hlabJ₁.symm)
        rw [hLJ', D.ht'] at hLM
        exact (hC.orb_subset (hLM ▸ hM : K ∈ orbOf (TC.nbrAdj Ω) K J)).2.1 rfl
      · have : e₃ = b₂ := by
          cases e₃ <;> cases b₁ <;> cases b₂ <;>
            first | rfl | exact absurd rfl he | exact absurd rfl hb12
        subst this
        have hLJs : L = D.Js := hH₁.label_inj L hL D.Js hJsY (hlabL.trans hlabJs₁.symm)
        rw [hLJs, hJsKs] at hLM
        exact D.hKsπ (hLM ▸ hM)
    · exact h
  have hcomm := D.IY.comm_member (by omega) hH₁.card hH₁.conj_mem hH₁.label_inj hL (E.s₁ σ) (by
    rw [hlabL, E.hs₁]
    exact ofPerm_comm_bar hβ₀ e₃ fun x hx => hσ x (Finset.disjoint_left.mp hβJ hx))
  intro m hm
  have hm' : D.t⁻¹ * m * D.t ∈ L := by
    have := conj_mem_conjSub (n := D.t⁻¹) hm
    rwa [← hLM, conjSub_inv_conjSub, inv_inv] at this
  have e2 := hcomm _ hm'
  calc (D.t * ((E.s₁ σ : ↥(pSpan (centMembers Ω D.u))) : G) * D.t⁻¹) * m =
      D.t * (((E.s₁ σ : ↥(pSpan (centMembers Ω D.u))) : G) * (D.t⁻¹ * m * D.t)) * D.t⁻¹ := by
        group
    _ = D.t * ((D.t⁻¹ * m * D.t) * ((E.s₁ σ : ↥(pSpan (centMembers Ω D.u))) : G)) * D.t⁻¹ := by
        rw [e2]
    _ = m * (D.t * ((E.s₁ σ : ↥(pSpan (centMembers Ω D.u))) : G) * D.t⁻¹) := by group

theorem comm_orb_of_three_seven (hS : CSetting 3 IH Ω K J) (hn : n = 7)
    {σ : alternatingGroup (Fin (n + 2))}
    (hσ : ∀ x, x ∉ D.γ.map D.ι → (σ : Equiv.Perm (Fin (n + 2))) x = x) (h3 : σ ^ 3 = 1) :
    ∀ x ∈ pSpan (orbOf (TC.nbrAdj Ω) K J),
      (D.t * ((E.s₁ σ : ↥(pSpan (centMembers Ω D.u))) : G) * D.t⁻¹) * x =
        x * (D.t * ((E.s₁ σ : ↥(pSpan (centMembers Ω D.u))) : G) * D.t⁻¹) := by
  classical
  have hC := hS.toCHyp
  have hD := hS.cex.toThmDHyp
  have hF := hC.graphFam'
  have hn5 : 5 ≤ n := by omega
  have hJπ : J ∈ orbOf (TC.nbrAdj Ω) K J := mem_orbOf_self K J
  have hJΩ : J ∈ Ω := hC.orb_subset_omega hJπ
  have h8 : ∀ L ∈ Ω, Nat.card L = 8 := fun L hL => by rw [hD.card L hL]; norm_num
  have hH₁ := D.hHY
  obtain ⟨hti, -⟩ := CHyp.swap_inv D.ht D.ht'
  set x₀ : G := ((E.s₁ σ : ↥(pSpan (centMembers Ω D.u))) : G) with hx₀
  set y : G := D.t * x₀ * D.t⁻¹ with hy
  have hx₀X : x₀ ∈ pSpan (orbOf (TC.nbrAdj Ω) K J) := E.s₁_mem_orb' hn5 hσ
  have hx₀3 : x₀ ^ 3 = 1 := by
    rw [hx₀, ← Subgroup.coe_pow, ← map_pow, h3, map_one, Subgroup.coe_one]
  have hy3 : y ^ 3 = 1 := by rw [hy, conj_pow, hx₀3, mul_one, mul_inv_cancel]
  set β₁ := D.γ.map D.ι
  obtain ⟨hβ', b₁, b₂, hb12, hJJs, hlabJ₁, hlabJs₁⟩ := twin_labels D hn5
  have hJY : J ∈ centMembers Ω D.u := D.hπY hJπ
  have hJsY : D.Js ∈ centMembers Ω D.u := D.hπY D.hJs
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
  have hk : IsPGroup 2 I.φ.ker := I.toLabel.isPGroup_ker hC.oddCore_orb_eq_bot
  set θ := I.inducedAut hn5 hnorm
  have hθ3 : θ ^ 3 ^ 1 = 1 := by
    rw [pow_one]
    exact I.inducedAut_pow_eq_one hn5 hnorm hy3
  have hθJ : ∀ x (hx : x ∈ memBar D.γ D.hγ D.b),
      θ ⟨x, memBar_le_aeModel D.γ D.hγ D.b hx⟩ = ⟨x, memBar_le_aeModel D.γ D.hγ D.b hx⟩ :=
    fun x hx => I.inducedAut_fix_of_comm hn5 hnorm
      (fun m hm => ((Subgroup.mem_centralizer_iff.mp (hXJ hyX')) m hm).symm) x
      (by rw [D.hlabJ]; exact hx) _
  obtain ⟨p, hp, q, hq, hpq⟩ : ∃ p ∈ D.γᶜ, ∃ q ∈ D.γᶜ, p ≠ q := by
    refine Finset.one_lt_card.mp ?_
    rw [Finset.card_compl, D.hγ, Fintype.card_fin]
    omega
  rw [Finset.mem_compl] at hp hq
  have hap : D.a ≠ p := fun h => hp (h ▸ D.ha)
  have haq : D.a ≠ q := fun h => hq (h ▸ D.ha)
  have hcp : D.c ≠ p := fun h => hp (h ▸ D.hc)
  have hcq : D.c ≠ q := fun h => hq (h ▸ D.hc)
  set S : Finset (Fin n) := ({D.a, D.c, p, q} : Finset (Fin n))ᶜ with hSdef
  have hS3 : S.card = 3 := by
    have h4 : ({D.a, D.c, p, q} : Finset (Fin n)).card = 4 := by
      rw [Finset.card_insert_of_notMem (by simp [D.hac, hap, haq]),
        Finset.card_insert_of_notMem (by simp [hcp, hcq]), Finset.card_pair hpq]
    rw [hSdef, Finset.card_compl, h4, Fintype.card_fin]
    omega
  have hpS : p ∉ S := by simp [hSdef]
  have hqS : q ∉ S := by simp [hSdef]
  have hδ₁ : (insert p S).card = 4 := by rw [Finset.card_insert_of_notMem hpS, hS3]
  have hδ₂ : (insert q S).card = 4 := by rw [Finset.card_insert_of_notMem hqS, hS3]
  have hSac : ∀ x ∈ S, x ≠ D.a ∧ x ≠ D.c := by
    intro x hx
    simp only [hSdef, Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hx
    exact ⟨hx.1, hx.2.1⟩
  have hδ₁ac : ∀ x ∈ insert p S, x ≠ D.a ∧ x ≠ D.c := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hxS
    · exact ⟨hap.symm, hcp.symm⟩
    · exact hSac x hxS
  have hδ₂ac : ∀ x ∈ insert q S, x ≠ D.a ∧ x ≠ D.c := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hxS
    · exact ⟨haq.symm, hcq.symm⟩
    · exact hSac x hxS
  obtain ⟨M₁, hM₁, hlab₁⟩ := I.label_surj (insert p S) hδ₁ true
  obtain ⟨M₂, hM₂, hlab₂⟩ := I.label_surj (insert q S) hδ₂ true
  have hc₁ := E.comm_of_chart2 hS hn5 hσ hM₁ hδ₁ hδ₁ac hlab₁
  have hc₂ := E.comm_of_chart2 hS hn5 hσ hM₂ hδ₂ hδ₂ac hlab₂
  have hθ₁ : ∀ x (hx : x ∈ memBar (insert p S) hδ₁ true),
      θ ⟨x, memBar_le_aeModel _ hδ₁ true hx⟩ = ⟨x, memBar_le_aeModel _ hδ₁ true hx⟩ :=
    fun x hx => I.inducedAut_fix_of_comm hn5 hnorm hc₁ x (by rw [hlab₁]; exact hx) _
  have hθ₂ : ∀ x (hx : x ∈ memBar (insert q S) hδ₂ true),
      θ ⟨x, memBar_le_aeModel _ hδ₂ true hx⟩ = ⟨x, memBar_le_aeModel _ hδ₂ true hx⟩ :=
    fun x hx => I.inducedAut_fix_of_comm hn5 hnorm hc₂ x (by rw [hlab₂]; exact hx) _
  have hind : indv (insert p S) + indv (insert q S) = TL4.pairVec p q := by
    funext x
    by_cases hxp : x = p
    · subst hxp
      simp [indv, TL4.pairVec, hpS, hpq, Pi.single_apply]
    · by_cases hxq : x = q
      · subst hxq
        simp [indv, TL4.pairVec, hqS, Ne.symm hpq, Pi.single_apply]
      · by_cases hxS : x ∈ S
        · simp [indv, TL4.pairVec, hxS, hxp, hxq, Pi.single_apply]
          decide
        · simp [indv, TL4.pairVec, hxS, hxp, hxq, Pi.single_apply]
  have hθw : θ ⟨TL4.vbar n (TL4.pairVec p q), vbar_pairVec_mem_aeModel p q⟩ =
      ⟨TL4.vbar n (TL4.pairVec p q), vbar_pairVec_mem_aeModel p q⟩ := by
    have e : (⟨TL4.vbar n (TL4.pairVec p q), vbar_pairVec_mem_aeModel p q⟩ :
        ↥(TL4.aeModel n)) = ⟨zBar (insert p S) hδ₁, zBar_mem_aeModel _ hδ₁⟩ *
        ⟨zBar (insert q S) hδ₂, zBar_mem_aeModel _ hδ₂⟩ := by
      apply Subtype.ext
      show TL4.vbar n (TL4.pairVec p q) = zBar (insert p S) hδ₁ * zBar (insert q S) hδ₂
      rw [zBar_eq_vbar_indv, zBar_eq_vbar_indv, ← TL4.vbar_add, hind]
    rw [e, map_mul, hθ₁ _ (zBar_mem_memBar _ hδ₁ true), hθ₂ _ (zBar_mem_memBar _ hδ₂ true)]
  have hθ1 : θ = 1 := aut_eq_one_of_cent_pair hn θ ⟨1, hθ3⟩ D.hγ hθJ hpq hp hq hθw
  exact I.comm_of_inducedAut_eq_one hD.hyp hD.two h8 hC.orb_subset_omega hn5 hk hnorm hperm hθ1

end GlueData

end CFSG.ClassicalInvolution.Q3.TC.Thin
