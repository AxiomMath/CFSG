module

public import CFSG.ClassicalInvolution.Q3.TL3T72E
public import CFSG.ClassicalInvolution.Q3.TL3T73D

public section

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph
open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

section Fin5

private theorem exists_threeCycle : ∀ a c : Fin 5, a ≠ c → ∃ σ : Equiv.Perm (Fin 5),
    σ a = a ∧ σ c = c ∧ σ * σ * σ = 1 ∧ ∀ p, p ≠ a → p ≠ c → σ p ≠ p ∧ σ (σ p) ≠ p := by
  decide +kernel

private theorem sign_eq_one_of_mul_cube {σ : Equiv.Perm (Fin 5)} (h : σ * σ * σ = 1) :
    Equiv.Perm.sign σ = 1 := by
  have h3 : Equiv.Perm.sign σ ^ 3 = 1 := by rw [← map_pow, pow_three', h, map_one]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1
  · exact h1
  · rw [h1] at h3
    exact absurd h3 (by decide)

private theorem map_ne_of_moves {γ : Finset (Fin 5)} (hγ : γ.card = 4) {a c : Fin 5} (ha : a ∈ γ)
    (hc : c ∈ γ) {ρ : Equiv.Perm (Fin 5)} (hmv : ∀ p, p ≠ a → p ≠ c → ρ p ≠ p) :
    γ.map ρ.toEmbedding ≠ γ := by
  classical
  intro h
  obtain ⟨q, hq⟩ := Finset.card_eq_one.mp
    (show γᶜ.card = 1 by rw [Finset.card_compl, hγ, Fintype.card_fin])
  have hqγ : q ∉ γ := Finset.mem_compl.mp (by rw [hq]; exact Finset.mem_singleton_self q)
  have hρq : ρ q ∉ γ := by
    intro hmem
    rw [← h] at hmem
    obtain ⟨x, hx, hxq⟩ := Finset.mem_map.mp hmem
    exact hqγ (ρ.injective hxq ▸ hx)
  have hρq' : ρ q ∈ γᶜ := Finset.mem_compl.mpr hρq
  rw [hq, Finset.mem_singleton] at hρq'
  exact hmv q (fun e => hqγ (by rw [e]; exact ha)) (fun e => hqγ (by rw [e]; exact hc)) hρq'

private theorem mkQ_ofPerm_comm_pairVec {σ : Equiv.Perm (Fin 5)} {a c : Fin 5} (ha : σ a = a)
    (hc : σ c = c) :
    mkQ 5 (ofPerm σ) * mkQ 5 (ofVec (TL4.pairVec a c)) =
      mkQ 5 (ofVec (TL4.pairVec a c)) * mkQ 5 (ofPerm σ) := by
  rw [← map_mul, ← map_mul]
  congr 1
  refine Wr.ext (funext fun i => ?_) (by show σ * 1 = 1 * σ; rw [mul_one, one_mul])
  have e : TL4.pairVec a c (σ.symm i) = TL4.pairVec a c i := by
    simp only [TL4.pairVec_apply, Equiv.symm_apply_eq, ha, hc]
  show (0 : ZMod 2) + TL4.pairVec a c (σ.symm i) = TL4.pairVec a c i + 0
  rw [zero_add, add_zero, e]

end Fin5

section Fill

variable {G : Type} [Group G] [Finite G] {π Y : Set (Subgroup G)} {m : ℕ}

private theorem exists_over_eq_conj (I : AEIdent π 5) (hH : TL4.AECoverHyp I)
    (hzL : ∀ L ∈ π, ∃ v, IsUniqueInvolution L v) (IY : AEIdent Y m) (hm5 : 5 ≤ m)
    (hinjY : ∀ L ∈ Y, ∀ L' ∈ Y,
      (L.subgroupOf (pSpan Y)).map IY.φ = (L'.subgroupOf (pSpan Y)).map IY.φ → L = L')
    {h : G} (hπY : ∀ L ∈ π, conjSub h L ∈ Y) {J : Subgroup G} (hJ : J ∈ conjSub h '' π)
    {δ : Finset (Fin m)} {hδ : δ.card = 4} {b : Bool}
    (hlabJ : (J.subgroupOf (pSpan Y)).map IY.φ = memBar δ hδ b) :
    ∃ x : Fin m, x ∉ δ ∧ IY.over (insert x δ) = conjSub h '' π := by
  classical
  have hPP : π ⊆ conjSub h⁻¹ '' Y := fun L hL => ⟨conjSub h L, hπY L hL, conjSub_inv_conjSub h L⟩
  obtain ⟨ι, hι⟩ := exists_emb_of_aeIdent_small' hPP le_rfl hm5 I (IY.conjE h⁻¹) hH hzL
  have hι' : ∀ L ∈ π, ∀ (α : Finset (Fin 5)) (hα : α.card = 4) (e : Bool),
      (L.subgroupOf (pSpan π)).map I.φ = memBar α hα e →
      ∃ (hα' : (α.map ι).card = 4) (e' : Bool),
        ((conjSub h L).subgroupOf (pSpan Y)).map IY.φ = memBar (α.map ι) hα' e' := by
    intro L hL α hα e hlab
    obtain ⟨hα', e', hlab'⟩ := hι L hL α hα e hlab
    refine ⟨hα', e', ?_⟩
    have hmc := IY.map_conj h⁻¹ (L := conjSub h L)
    rw [conjSub_inv_conjSub] at hmc
    rw [← hmc]
    exact hlab'
  obtain ⟨S, hSdef⟩ : ∃ S : Finset (Fin m), S = Finset.univ.map ι := ⟨_, rfl⟩
  have hScard : S.card = 5 := by rw [hSdef, Finset.card_map, Finset.card_univ, Fintype.card_fin]
  have heq : IY.over S = conjSub h '' π := by
    ext L₀
    constructor
    · rintro ⟨hL₀, β, hβ, e, hβS, hlab⟩
      obtain ⟨α, rfl⟩ := exists_map_eq_of_subset ι (α := β) fun x hx => by
        have := hβS hx
        rw [hSdef] at this
        obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp this
        exact ⟨i, rfl⟩
      have hα : α.card = 4 := by rwa [Finset.card_map] at hβ
      obtain ⟨M₁, hM₁, hlab₁⟩ := I.label_surj α hα true
      obtain ⟨M₂, hM₂, hlab₂⟩ := I.label_surj α hα false
      obtain ⟨_, b₁, hl₁⟩ := hι' M₁ hM₁ α hα true hlab₁
      obtain ⟨_, b₂, hl₂⟩ := hι' M₂ hM₂ α hα false hlab₂
      have hb : b₁ ≠ b₂ := by
        rintro rfl
        have h12 := conjSub_injective h (hinjY _ (hπY M₁ hM₁) _ (hπY M₂ hM₂) (hl₁.trans hl₂.symm))
        rw [h12] at hlab₁
        exact memBar_true_ne_false (by omega) α hα (hlab₁.symm.trans hlab₂)
      have hbool : ∀ x y z : Bool, x ≠ y → z = x ∨ z = y := by decide
      rcases hbool b₁ b₂ e hb with rfl | rfl
      · exact ⟨M₁, hM₁, (hinjY _ hL₀ _ (hπY M₁ hM₁) (hlab.trans hl₁.symm)).symm⟩
      · exact ⟨M₂, hM₂, (hinjY _ hL₀ _ (hπY M₂ hM₂) (hlab.trans hl₂.symm)).symm⟩
    · rintro ⟨L, hL, rfl⟩
      obtain ⟨α, hα, e, hlab⟩ := I.label L hL
      obtain ⟨hα', e', hlab'⟩ := hι' L hL α hα e hlab
      refine ⟨hπY L hL, α.map ι, hα', e', ?_, hlab'⟩
      rw [hSdef]
      exact Finset.map_subset_map.mpr (Finset.subset_univ α)
  have hJS : J ∈ IY.over S := heq ▸ hJ
  obtain ⟨-, α', hα', b', hα'S, hlab'⟩ := hJS
  have hδα : α' = δ := eq_of_memBar_eq' hm5 (hlab'.symm.trans hlabJ)
  subst hδα
  obtain ⟨x, hx, hxS⟩ := Finset.exists_eq_insert_iff.mpr ⟨hα'S, by rw [hα', hScard]⟩
  exact ⟨x, hx, by rw [hxS]; exact heq⟩

end Fill

variable {G : Type} [Group G] [Finite G] {IH : ℕ → Prop} {Ω : Set (Subgroup G)}

namespace CSetting

variable {K J : Subgroup G} (hS : CSetting 3 IH Ω K J)
include hS

private theorem conjSub_orb_ne (I : AEIdent (orbOf (TC.nbrAdj Ω) K J) 5)
    {t : G} (ht : conjSub t K = J) (ht' : conjSub t J = K)
    {γ : Finset (Fin 5)} {hγ : γ.card = 4} {b : Bool}
    (hlabJ : (J.subgroupOf (pSpan (orbOf (TC.nbrAdj Ω) K J))).map I.φ = memBar γ hγ b)
    {g : G} (hg : g ∈ pSpan (conjSub t '' orbOf (TC.nbrAdj Ω) K J)) {ρ : Equiv.Perm (Fin 5)}
    (hgρ : (I.conjE t).φ ⟨g, hg⟩ = mkQ 5 (ofPerm ρ)) (hρ : γ.map ρ.toEmbedding ≠ γ) :
    conjSub g '' orbOf (TC.nbrAdj Ω) K J ≠ orbOf (TC.nbrAdj Ω) K J := by
  classical
  intro hP
  have hC := hS.toCHyp
  have hK : K ∈ Ω := hS.adj.1
  have hn : (5 ≤ 5 ∧ 5 ≤ 7) ∨ 9 ≤ 5 := Or.inl ⟨le_rfl, by norm_num⟩
  obtain ⟨_, Ks, _, hDg, -, -, hKsπ, hKsX, hz⟩ := hC.exists_twin le_rfl I
  have hKs : Ks ∈ orbOf (TC.nbrAdj Ω) J K := by
    have h1 := hDg.Ks_mem
    rwa [hC.orb_swap_eq hDg.hg] at h1
  have hKsK : Ks ≠ K := hDg.Ks_ne
  obtain ⟨I''⟩ := hC.nonempty_aeIdent_swap I
  have hKg : conjSub g K ∈ maxOrbSet Ω (orbOf (TC.nbrAdj Ω) K J) := by
    refine ⟨hC.hyp.conjInvariant g K hK, ?_⟩
    have h1 := isMaxOrb_conj hC.graphFam' hC.mem_maxOrbSet_self.2 g
    rwa [hP] at h1
  obtain ⟨hti, hti'⟩ := CHyp.swap_inv ht ht'
  have hlabK : (K.subgroupOf (pSpan (conjSub t '' orbOf (TC.nbrAdj Ω) K J))).map (I.conjE t).φ =
      memBar γ hγ b := by
    have h1 := I.map_conj t (L := J)
    rw [ht'] at h1
    exact h1.trans hlabJ
  have hlabKs : (Ks.subgroupOf (pSpan (conjSub t '' orbOf (TC.nbrAdj Ω) K J))).map (I.conjE t).φ =
      memBar γ hγ (!b) := by
    have h1 := hC.conjSub_twin_label le_rfl (by norm_num) I hlabJ hti hti' hKs hKsK hz
    have h2 := I.map_conj t (L := conjSub t⁻¹ Ks)
    rw [conjSub_conjSub_inv] at h2
    exact h2.trans h1
  have hlabKg : ((conjSub g K).subgroupOf (pSpan (conjSub t '' orbOf (TC.nbrAdj Ω) K J))).map
      (I.conjE t).φ = conjSub (mkQ 5 (ofPerm ρ)) (memBar γ hγ b) := by
    have h1 := TL4.AECov.map_conjSub_eq (I.conjE t) K ⟨g, hg⟩
    rw [hgρ, hlabK] at h1
    exact h1
  obtain ⟨c', hc'⟩ := exists_conj_memBar_map (ofPerm ρ) γ hγ b
  have hlabKg' := hlabKg.trans hc'
  rcases hC.maxOrbSet_eq' hn I'' hKs hKsK hKsπ hz hKsX _ hKg with h | h
  · rw [h] at hlabKg'
    exact hρ (eq_of_memBar_eq' le_rfl (hlabK.symm.trans hlabKg')).symm
  · rw [h] at hlabKg'
    exact hρ (eq_of_memBar_eq' le_rfl (hlabKs.symm.trans hlabKg')).symm

private theorem exists_threeElt (I : AEIdent (orbOf (TC.nbrAdj Ω) K J) 5)
    {t u : G} (ht : conjSub t K = J) (ht' : conjSub t J = K)
    (huX' : u ∈ pSpan (orbOf (TC.nbrAdj Ω) J K)) {a c : Fin 5} (hac : a ≠ c)
    (hwt : t⁻¹ * u * t ∈ pSpan (orbOf (TC.nbrAdj Ω) K J))
    (hut : I.φ ⟨t⁻¹ * u * t, hwt⟩ = mkQ 5 (ofVec (TL4.pairVec a c)))
    {γ : Finset (Fin 5)} (hγ : γ.card = 4) (ha : a ∈ γ) (hc : c ∈ γ) :
    ∃ (g : G) (hg : g ∈ pSpan (conjSub t '' orbOf (TC.nbrAdj Ω) K J)) (σ : Equiv.Perm (Fin 5)),
      (I.conjE t).φ ⟨g, hg⟩ = mkQ 5 (ofPerm σ) ∧ γ.map σ.toEmbedding ≠ γ ∧
        γ.map (σ * σ).toEmbedding ≠ γ ∧ g * u = u * g ∧ ∀ j ∈ J, g * j = j * g := by
  classical
  have hC := hS.toCHyp
  have hJπ : J ∈ orbOf (TC.nbrAdj Ω) K J := mem_orbOf_self K J
  have hJΩ : J ∈ Ω := hC.orb_subset_omega hJπ
  have he : conjSub t '' orbOf (TC.nbrAdj Ω) K J = orbOf (TC.nbrAdj Ω) J K := by
    rw [← orbOf_conj hC.graphFam'.graph K J t, ht, ht']
  have huX : u ∈ pSpan (conjSub t '' orbOf (TC.nbrAdj Ω) K J) := by rw [he]; exact huX'
  have hI'u : (I.conjE t).φ ⟨u, huX⟩ = mkQ 5 (ofVec (TL4.pairVec a c)) := by
    rw [← hut]
    exact AEIdent.conjE_apply I t huX hwt
  have hodd' : classicalInvolutionOddCore
      ↥(pSpan (conjSub t '' orbOf (TC.nbrAdj Ω) K J)) = ⊥ := by
    rw [he]
    exact hC.swap.oddCore_orb_eq_bot
  have hk' : IsPGroup 2 (I.conjE t).φ.ker := (I.conjE t).toLabel.isPGroup_ker hodd'
  obtain ⟨σ, hσa, hσc, hσ3, hσmv⟩ := exists_threeCycle a c hac
  have hσ3' : σ ^ 3 = 1 := by rw [pow_three']; exact hσ3
  have hσA : σ ∈ alternatingGroup (Fin 5) :=
    Equiv.Perm.mem_alternatingGroup.mpr (sign_eq_one_of_mul_cube hσ3)
  have hx : mkQ 5 (ofPerm σ) ∈ (I.conjE t).φ.range := by
    rw [(I.conjE t).range_eq]
    exact mem_aeModel_ofPerm hσA
  have hx3 : mkQ 5 (ofPerm σ) ^ 3 = 1 := by
    rw [← map_pow, ofPerm_pow, hσ3', ofPerm_one, map_one]
  obtain ⟨y, hy, k, hyk⟩ := (I.conjE t).exists_lift_pow_three hx hx3
  have hcomm : (y : G) * u = u * (y : G) := by
    have h := (I.conjE t).comm_of_pow_three hk' hyk (w := ⟨u, huX⟩)
      (by rw [hy, hI'u]; exact mkQ_ofPerm_comm_pairVec hσa hσc)
    exact congrArg Subtype.val h
  have hcent : ∀ j ∈ J, (y : G) * j = j * (y : G) := by
    have hle : pSpan (conjSub t '' orbOf (TC.nbrAdj Ω) K J) ≤
        Subgroup.centralizer (J : Set G) := by
      rw [he]
      exact hC.swap.pSpan_orb_le.trans (pSpan_omegaNbr_le_centralizer hC.hyp hC.two hJΩ)
    intro j hj
    exact (Subgroup.mem_centralizer_iff.mp (hle y.2) j hj).symm
  refine ⟨y, y.2, σ, hy, map_ne_of_moves hγ ha hc fun p hpa hpc => (hσmv p hpa hpc).1, ?_,
    hcomm, hcent⟩
  exact map_ne_of_moves hγ ha hc fun p hpa hpc => (hσmv p hpa hpc).2

theorem degree_centMembers_five (I : AEIdent (orbOf (TC.nbrAdj Ω) K J) 5)
    {t u : G} (ht : conjSub t K = J) (ht' : conjSub t J = K)
    (huX' : u ∈ pSpan (orbOf (TC.nbrAdj Ω) J K)) {a c : Fin 5} (hac : a ≠ c)
    (hwt : t⁻¹ * u * t ∈ pSpan (orbOf (TC.nbrAdj Ω) K J))
    (hut : I.φ ⟨t⁻¹ * u * t, hwt⟩ = mkQ 5 (ofVec (TL4.pairVec a c)))
    (hacγ : ∀ {γ hγ b}, (J.subgroupOf (pSpan (orbOf (TC.nbrAdj Ω) K J))).map I.φ =
      memBar γ hγ b → a ∈ γ ∧ c ∈ γ)
    {m : ℕ} (IY : AEIdent (centMembers Ω u) m) (hm5 : 5 ≤ m) (hk : IsPGroup 2 IY.φ.ker)
    (hπY : orbOf (TC.nbrAdj Ω) K J ⊆ centMembers Ω u) : m = 7 := by
  classical
  have hC := hS.toCHyp
  have hD := hS.cex.toThmDHyp
  have hle := hS.degree_le_centMembers' le_rfl I ht ht' huX' hac hwt hut IY hm5 hk hπY
  have hH := hC.aeCoverHyp_orb le_rfl (by norm_num) I
  have hJπ : J ∈ orbOf (TC.nbrAdj Ω) K J := mem_orbOf_self K J
  have hJY : J ∈ centMembers Ω u := hπY hJπ
  obtain ⟨γ, hγ, b, hlabJ⟩ := I.label J hJπ
  obtain ⟨hγa, hγc⟩ := hacγ hlabJ
  obtain ⟨δ, hδ, bY, hlabJY⟩ := IY.label J hJY
  have hinjY : ∀ L ∈ centMembers Ω u, ∀ L' ∈ centMembers Ω u,
      (L.subgroupOf (pSpan (centMembers Ω u))).map IY.φ =
        (L'.subgroupOf (pSpan (centMembers Ω u))).map IY.φ → L = L' :=
    fun L hL L' hL' h => aeIdent_eq_of_map_eq hD.hyp hD.two (fun _ h => h.1) hm5 IY hk hL hL' h
  have hzL : ∀ L ∈ orbOf (TC.nbrAdj Ω) K J, ∃ v, IsUniqueInvolution L v := fun L hL =>
    (hD.hyp.omega1 L (hC.orb_subset_omega hL)).1
  obtain ⟨g, hg, σ, hgσ, hσ1, hσ2, hgu, hgJ⟩ :=
    hS.exists_threeElt I ht ht' huX' hac hwt hut hγ hγa hγc
  have hfam : ∀ h : G, h * u = u * h → (∀ j ∈ J, h * j = j * h) →
      ∃ x : Fin m, x ∉ δ ∧ IY.over (insert x δ) = conjSub h '' orbOf (TC.nbrAdj Ω) K J := by
    intro h hhu hhJ
    exact exists_over_eq_conj I hH hzL IY hm5 hinjY
      (fun L hL => hS.conjSub_mem_centMembers_of_comm hhu (hπY hL))
      ⟨J, hJπ, conjSub_eq_of_comm hhJ⟩ hlabJY
  obtain ⟨x₀, hx₀, h₀⟩ := hfam 1 (by rw [one_mul, mul_one]) fun j _ => by rw [one_mul, mul_one]
  obtain ⟨x₁, hx₁, h₁⟩ := hfam g hgu hgJ
  obtain ⟨x₂, hx₂, h₂⟩ := hfam (g * g) (Commute.mul_left hgu hgu)
    fun j hj => Commute.mul_left (hgJ j hj) (hgJ j hj)
  have hP0 : conjSub (1 : G) '' orbOf (TC.nbrAdj Ω) K J = orbOf (TC.nbrAdj Ω) K J := by
    ext L
    simp only [Set.mem_image, conjSub_one, exists_eq_right]
  rw [hP0] at h₀
  have hgg : g * g ∈ pSpan (conjSub t '' orbOf (TC.nbrAdj Ω) K J) := mul_mem hg hg
  have hggσ : (I.conjE t).φ ⟨g * g, hgg⟩ = mkQ 5 (ofPerm (σ * σ)) := by
    have e : (⟨g * g, hgg⟩ : ↥(pSpan (conjSub t '' orbOf (TC.nbrAdj Ω) K J))) =
        ⟨g, hg⟩ * ⟨g, hg⟩ := rfl
    rw [e, map_mul, hgσ, ← map_mul, ofPerm_mul]
  have d01 := hS.conjSub_orb_ne I ht ht' hlabJ hg hgσ hσ1
  have d02 := hS.conjSub_orb_ne I ht ht' hlabJ hgg hggσ hσ2
  have d12 : conjSub g '' orbOf (TC.nbrAdj Ω) K J ≠ conjSub (g * g) '' orbOf (TC.nbrAdj Ω) K J := by
    intro h
    have hAA : conjSub (g * g) '' orbOf (TC.nbrAdj Ω) K J =
        conjSub g '' (conjSub g '' orbOf (TC.nbrAdj Ω) K J) := by
      ext L
      simp only [Set.mem_image]
      constructor
      · rintro ⟨M, hM, rfl⟩
        exact ⟨conjSub g M, ⟨M, hM, rfl⟩, (conjSub_mul g g M).symm⟩
      · rintro ⟨_, ⟨M, hM, rfl⟩, rfl⟩
        exact ⟨M, hM, conjSub_mul g g M⟩
    have hinj : Function.Injective (Set.image (conjSub g : Subgroup G → Subgroup G)) :=
      Set.image_injective.mpr (conjSub_injective g)
    exact d01 (hinj (h.trans hAA)).symm
  have hx01 : x₀ ≠ x₁ := fun e =>
    d01 (h₁.symm.trans ((congrArg (fun x => IY.over (insert x δ)) e).symm.trans h₀))
  have hx02 : x₀ ≠ x₂ := fun e =>
    d02 (h₂.symm.trans ((congrArg (fun x => IY.over (insert x δ)) e).symm.trans h₀))
  have hx12 : x₁ ≠ x₂ := fun e =>
    d12 (h₁.symm.trans ((congrArg (fun x => IY.over (insert x δ)) e).trans h₂))
  have hsub : ({x₀, x₁, x₂} : Finset (Fin m)) ⊆ δᶜ := by
    intro x hx
    rw [Finset.mem_compl]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact hx₀
    · exact hx₁
    · exact hx₂
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_eq_three.mpr ⟨x₀, x₁, x₂, hx01, hx02, hx12, rfl⟩, Finset.card_compl,
    Fintype.card_fin, hδ] at hcard
  omega

end CSetting

end CFSG.ClassicalInvolution.Q3.TC.Thin
