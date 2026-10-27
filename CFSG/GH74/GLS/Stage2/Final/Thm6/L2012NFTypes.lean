module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2012NFY
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der75Main

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L2012

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Bg CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage2.Final
  CFSG.GH74.GLS.Stage2.Final.Thm6.SL2Bound CFSG.GH74.GLS.Stage2.Bender.Thm1
  CFSG.GH74.GLS.Stage2.Final.Thm6.L20


section PGLOverLemmas

variable {Y : Type} [Group Y] [Finite Y]

omit [Finite Y] in
theorem pglOver_congr {L T T' : Subgroup Y} {r : ℕ} (h : L ⊔ T = L ⊔ T') (hp : PGLOver L T r) :
    PGLOver L T' r := by
  unfold PGLOver at hp ⊢
  rw [← h]
  exact hp

omit [Finite Y] in
theorem card_sup_of_pgl {L T : Subgroup Y} {r : ℕ} (hodd : Odd r)
    (hsl : HasSL2Model ↥L (fun q => q = r)) (hp : PGLOver L T r) :
    Nat.card ↥(L ⊔ T) = 2 * Nat.card ↥L := by
  obtain ⟨hn, F₀, hF₀, hFin₀, hF₀r, ⟨e₀⟩⟩ := hp
  obtain ⟨F, hF, hFin, hFr, ⟨e⟩⟩ := hsl
  set Zm : Subgroup Y := (center ↥L).map L.subtype with hZm
  have hZmL : Zm ≤ L := Subgroup.map_subtype_le _
  have hZmX : Zm ≤ L ⊔ T := hZmL.trans le_sup_left
  have hcardZm : Nat.card ↥Zm = 2 := by
    have := (sl2_model_center_inv hodd ⟨F, hF, hFin, hFr, ⟨e⟩⟩).1
    rw [hZm, Subgroup.card_map_of_injective L.subtype_injective]
    exact this
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Zm.subgroupOf (L ⊔ T))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZmX).toEquiv, hcardZm,
    Nat.card_congr e₀.toEquiv, CFSG.GorensteinWalter.pgl2_card_formula, hF₀r] at h1
  have h2 : Nat.card ↥L = Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) := by
    rw [Nat.card_congr e.toEquiv,
      ← Nat.card_congr (specialLinearGroupEquivStatedSL 2 F).toEquiv]
  rw [h2, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hFr]
  rw [h1]
  ring

end PGLOverLemmas

section Ctx

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} {ε : Bool} {q : ℕ}
  {L₁ L₂ : Subgroup (CentralizerBar z)} {K₁ K₂ : Subgroup G}

structure NFCtx (G : Type) [Group G] [Finite G] (z : G) (S : Subgroup G) (ε : Bool) (q : ℕ)
    (L₁ L₂ : Subgroup (CentralizerBar z)) (K₁ K₂ : Subgroup G) : Prop where
  ctx : Stage2Ctx G z (Kind.l4 ε) S
  comp : CompData z K₁ K₂ L₁ L₂
  l4 : Stage1L4 G z S ε q L₁ L₂
  two : ∃ x : G, TwoClassData G z S L₁ L₂ q x
  fuse : ∀ y : G, GoodInvolution z S L₁ L₂ q y → IsConj z y
  good : ∃ y : G, GoodInvolution z S L₁ L₂ q y

theorem NFCtx.pair (h : NFCtx G z S ε q L₁ L₂ K₁ K₂) : Stage1Pair G z S q L₁ L₂ := h.l4.pair

theorem NFCtx.SC (h : NFCtx G z S ε q L₁ L₂ K₁ K₂) : S ≤ Cen z := h.ctx.S_le_Cen

theorem NFCtx.z2 (h : NFCtx G z S ε q L₁ L₂ K₁ K₂) : z * z = 1 := by
  have h2 := h.ctx.orderOf_z
  have : z ^ 2 = 1 := by rw [← h2]; exact pow_orderOf_eq_one z
  simpa [pow_two] using this

theorem NFCtx.z1 (h : NFCtx G z S ε q L₁ L₂ K₁ K₂) : z ≠ 1 := by
  intro e
  have h2 := h.ctx.orderOf_z
  rw [e, orderOf_one] at h2
  omega

theorem NFCtx.swaps_or_nrm (h : NFCtx G z S ε q L₁ L₂ K₁ K₂) {s : G} (hs : s ∈ S) :
    Swaps z s L₁ L₂ ∨ (toBar z ⟨s, h.SC hs⟩ ∈ normalizer (L₁ : Set (CentralizerBar z)) ∧
      toBar z ⟨s, h.SC hs⟩ ∈ normalizer (L₂ : Set (CentralizerBar z))) := by
  rcases comps_dichotomy h.pair (toBar z ⟨s, h.SC hs⟩) with ⟨a1, a2⟩ | ⟨a1, -⟩
  · right
    exact ⟨bar_mem_normalizer_iff_conjugate_eq.2 a1, bar_mem_normalizer_iff_conjugate_eq.2 a2⟩
  · left
    exact (swaps_iff_conj h.pair (h.SC hs)).2 a1


omit [Finite G] in
theorem barOf_zpowers (z u : G) (hu : u ∈ Cen z) :
    barOf z (zpowers u) = zpowers (toBar z ⟨u, hu⟩) := by
  have h1 : (zpowers u).subgroupOf (Cen z) = zpowers (⟨u, hu⟩ : ↥(Cen z)) := by
    ext x
    rw [Subgroup.mem_subgroupOf, mem_zpowers_iff, mem_zpowers_iff]
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨n, Subtype.ext (by simpa using hn)⟩
    · rintro ⟨n, hn⟩
      exact ⟨n, by simpa using congrArg Subtype.val hn⟩
  unfold barOf
  rw [h1, MonoidHom.map_zpowers]


open CFSG.GH74.GLS.Stage2.Final.Thm6.L208g2 in
theorem NFCtx.zbar_mem (h : NFCtx G z S ε q L₁ L₂ K₁ K₂) :
    toBar z ⟨z, mem_Cen_self z⟩ ∈ L₁ ⊓ L₂ := by
  have hz : z ∈ LC z := z_mem_LC_of_pair h.pair h.ctx.orderOf_z
  have hb : toBar z ⟨z, mem_Cen_self z⟩ ∈ LBar z :=
    ⟨⟨z, mem_Cen_self z⟩, Subgroup.mem_subgroupOf.mpr hz, rfl⟩
  rw [← h.pair.prod.1] at hb
  have hcom : ∀ c : CentralizerBar z, c * toBar z ⟨z, mem_Cen_self z⟩ = toBar z ⟨z, mem_Cen_self z⟩ * c :=
    Subgroup.mem_center_iff.mp (toBar_z_mem_center z)
  have p₁ := pair₁_of_stage1 h.pair
  have p₂ := pair₂_of_stage1 h.pair
  have h2 : toBar z ⟨z, mem_Cen_self z⟩ ∈ L₂ := p₁.mem_of_cen hb (fun c _ => (hcom c).symm)
  have h1 : toBar z ⟨z, mem_Cen_self z⟩ ∈ L₁ :=
    p₂.mem_of_cen (by rwa [sup_comm] at hb) (fun c _ => (hcom c).symm)
  exact ⟨h1, h2⟩


theorem NFCtx.mem_S1 (h : NFCtx G z S ε q L₁ L₂ K₁ K₂) {u : G} (hu : u ∈ S)
    (hn₁ : toBar z ⟨u, h.SC hu⟩ ∈ normalizer (L₁ : Set (CentralizerBar z)))
    (hn₂ : toBar z ⟨u, h.SC hu⟩ ∈ normalizer (L₂ : Set (CentralizerBar z))) : u ∈ S1 S z :=
  bar_mem_S1_iff.2 ⟨hu, h.SC hu, fun _ hK _ => bar_mem_normalizer_comp h.pair.comps hn₁ hn₂ hK⟩

theorem NFCtx.good_of_nrm (h : NFCtx G z S ε q L₁ L₂ K₁ K₂) {u : G} (hu : u ∈ S) (hu2 : u * u = 1)
    (hu1 : u ≠ 1) (hn₁ : toBar z ⟨u, h.SC hu⟩ ∈ normalizer (L₁ : Set (CentralizerBar z)))
    (hn₂ : toBar z ⟨u, h.SC hu⟩ ∈ normalizer (L₂ : Set (CentralizerBar z))) (hLC : u ∉ LC z) :
    GoodInvolution z S L₁ L₂ q u := by
  have hP := h.pair
  have huC : u ∈ Cen z := h.SC hu
  have hS1 := h.mem_S1 hu hn₁ hn₂
  have hbarS1 : toBar z ⟨u, huC⟩ ∈ SBar (S1 S z) z := bar_mem_barOf_iff.2 ⟨u, huC, hS1, rfl⟩
  have hu2b : toBar z ⟨u, huC⟩ * toBar z ⟨u, huC⟩ = 1 := by
    rw [← map_mul, show (⟨u, huC⟩ : ↥(Cen z)) * ⟨u, huC⟩ = 1 from Subtype.ext hu2, map_one]
  have hord : orderOf u = 2 := orderOf_eq_prime (by rw [← sq] at hu2; exact hu2) hu1
  refine ⟨hu, hord, ?_, ?_⟩
  ·
    have hnin : toBar z ⟨u, huC⟩ ∉ L₁ ⊔ centralizer (L₁ : Set (CentralizerBar z)) := fun hin =>
      hLC (inner_mem_LC_bar h.SC hP.ne hP.prod hP.comps hP.sl₁ h.l4.pgl.1 hP.swap h.l4.index_le hu huC hn₁ hin)
    have := pgl_of_nrm hP.odd hP.sl₁ h.l4.pgl.1 hbarS1 hu2b hn₁ hnin
    rwa [barOf_zpowers z u huC]
  ·
    have hcomps₂ : {K : Subgroup (CentralizerBar z) | IsComponent K} = {L₂, L₁} := by
      rw [hP.comps]; exact Set.pair_comm _ _
    have hswap₂ : ∃ s ∈ S, Swaps z s L₂ L₁ := by
      obtain ⟨s, hs, hsC, h1, h2⟩ := hP.swap
      exact ⟨s, hs, hsC, h2, h1⟩
    have hnin : toBar z ⟨u, huC⟩ ∉ L₂ ⊔ centralizer (L₂ : Set (CentralizerBar z)) := fun hin =>
      hLC (inner_mem_LC_bar h.SC hP.ne.symm (bar_isCentralProd_symm hP.prod) hcomps₂ hP.sl₂ h.l4.pgl.2
        hswap₂ h.l4.index_le hu huC hn₂ hin)
    have := pgl_of_nrm hP.odd hP.sl₂ h.l4.pgl.2 hbarS1 hu2b hn₂ hnin
    rwa [barOf_zpowers z u huC]


theorem NFCtx.good_ne_z (h : NFCtx G z S ε q L₁ L₂ K₁ K₂) {u : G}
    (hg : GoodInvolution z S L₁ L₂ q u) : u ≠ z := by
  intro hu
  have huC : u ∈ Cen z := h.SC hg.1
  have hpg := hg.2.2.1
  have hcard := card_sup_of_pgl h.pair.odd h.pair.sl₁ hpg
  have hzL : barOf z (zpowers u) ≤ L₁ := by
    rw [barOf_zpowers z u huC, zpowers_le]
    subst hu
    exact (h.zbar_mem).1
  rw [sup_eq_left.2 hzL] at hcard
  have hpos : 0 < Nat.card ↥L₁ := Nat.card_pos
  omega

theorem NFCtx.good_mul_z (h : NFCtx G z S ε q L₁ L₂ K₁ K₂) {u : G}
    (hg : GoodInvolution z S L₁ L₂ q u) : GoodInvolution z S L₁ L₂ q (u * z) := by
  have hne := h.good_ne_z hg
  obtain ⟨huS, hord, hp₁, hp₂⟩ := hg
  have huC : u ∈ Cen z := h.SC huS
  have hzS : z ∈ S := h.ctx.z_mem
  have huzC : u * z ∈ Cen z := (Cen z).mul_mem huC (mem_Cen_self z)
  have hcomm : u * z = z * u := h.ctx.S_comm_z huS
  have hsq : (u * z) * (u * z) = 1 := by
    calc (u * z) * (u * z) = u * (z * u) * z := by group
      _ = u * (u * z) * z := by rw [hcomm]
      _ = (u * u) * (z * z) := by group
      _ = 1 := by
        have hu2 : u * u = 1 := by
          have : u ^ 2 = 1 := by rw [← hord]; exact pow_orderOf_eq_one u
          simpa [pow_two] using this
        rw [hu2, h.z2, one_mul]
  have hne1 : u * z ≠ 1 := by
    intro h1
    apply hne
    have : u = z⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [this]
    exact inv_eq_of_mul_eq_one_right h.z2
  have hord' : orderOf (u * z) = 2 := orderOf_eq_prime (by rw [← sq] at hsq; exact hsq) hne1
  have hmul : toBar z ⟨u * z, huzC⟩ = toBar z ⟨u, huC⟩ * toBar z ⟨z, mem_Cen_self z⟩ := by
    rw [← map_mul]; rfl
  have hjoin : ∀ L : Subgroup (CentralizerBar z), toBar z ⟨z, mem_Cen_self z⟩ ∈ L →
      L ⊔ barOf z (zpowers u) = L ⊔ barOf z (zpowers (u * z)) := by
    intro L hL
    rw [barOf_zpowers z u huC, barOf_zpowers z (u * z) huzC, hmul]
    apply le_antisymm
    · refine sup_le le_sup_left (zpowers_le.2 ?_)
      have hm : toBar z ⟨u, huC⟩ * toBar z ⟨z, mem_Cen_self z⟩ ∈
          L ⊔ zpowers (toBar z ⟨u, huC⟩ * toBar z ⟨z, mem_Cen_self z⟩) :=
        Subgroup.mem_sup_right (mem_zpowers _)
      have := Subgroup.mul_mem _ hm (Subgroup.mem_sup_left (L.inv_mem hL))
      simpa using this
    · refine sup_le le_sup_left (zpowers_le.2 ?_)
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (mem_zpowers _)) (Subgroup.mem_sup_left hL)
  exact ⟨(S.mul_mem huS hzS), hord', pglOver_congr (hjoin L₁ h.zbar_mem.1) hp₁,
    pglOver_congr (hjoin L₂ h.zbar_mem.2) hp₂⟩


theorem NFCtx.good_props (h : NFCtx G z S ε q L₁ L₂ K₁ K₂) {u : G}
    (hg : GoodInvolution z S L₁ L₂ q u) :
    u ≠ z ∧ ¬ Swaps z u L₁ L₂ ∧ u ∉ LC z ∧ IsConj z u ∧
      toBar z ⟨u, h.SC hg.1⟩ ∈ normalizer (L₁ : Set (CentralizerBar z)) ∧
      toBar z ⟨u, h.SC hg.1⟩ ∈ normalizer (L₂ : Set (CentralizerBar z)) := by
  have hne := h.good_ne_z hg
  have hconj := h.fuse u hg
  have huC := h.SC hg.1
  obtain ⟨x, hx⟩ := h.two
  have hnsw : ¬ Swaps z u L₁ L₂ := by
    intro hsw
    have hc := (hx.swap_conseq u hg.1 hconj hsw).1
    have hc2 := h.fuse (u * z) (h.good_mul_z hg)
    have hzx : IsConj z x := hc2.trans hc.symm
    exact hx.x_nonCentral (isCentralInvolution_of_conj' h.ctx.central hzx)
  have hn : toBar z ⟨u, huC⟩ ∈ normalizer (L₁ : Set (CentralizerBar z)) ∧
      toBar z ⟨u, huC⟩ ∈ normalizer (L₂ : Set (CentralizerBar z)) := by
    rcases h.swaps_or_nrm hg.1 with hsw | hn
    · exact absurd hsw hnsw
    · exact hn
  refine ⟨hne, hnsw, ?_, hconj, hn.1, hn.2⟩
  intro hLC
  have hu2 : u * u = 1 := by
    have : u ^ 2 = 1 := by rw [← hg.2.1]; exact pow_orderOf_eq_one u
    simpa [pow_two] using this
  have hbar : toBar z ⟨u, huC⟩ ∈ L₁ ⊔ L₂ := by
    rw [h.pair.prod.1]
    exact ⟨⟨u, huC⟩, Subgroup.mem_subgroupOf.mpr hLC, rfl⟩
  have hem := h.comp.mem_layer u huC hu2 hbar
  exact hne (layer_conj_eq_of_two h.ctx.central hx u hem hconj)


theorem NFCtx.toBar_sq (h : NFCtx G z S ε q L₁ L₂ K₁ K₂) {u : G} (hu : u ∈ S) (hu2 : u * u = 1) :
    toBar z ⟨u, h.SC hu⟩ * toBar z ⟨u, h.SC hu⟩ = 1 := by
  rw [← map_mul, show (⟨u, h.SC hu⟩ : ↥(Cen z)) * ⟨u, h.SC hu⟩ = 1 from Subtype.ext hu2, map_one]

omit [Finite G] in
theorem sq_of_good {u : G} (hg : GoodInvolution z S L₁ L₂ q u) :
    u * u = 1 := by
  have : u ^ 2 = 1 := by rw [← hg.2.1]; exact pow_orderOf_eq_one u
  simpa [pow_two] using this

theorem NFCtx.outer_of_good (h : NFCtx G z S ε q L₁ L₂ K₁ K₂) {u : G}
    (hg : GoodInvolution z S L₁ L₂ q u) :
    OuterOK L₁ (toBar z ⟨u, h.SC hg.1⟩) q ∧ OuterOK L₂ (toBar z ⟨u, h.SC hg.1⟩) q := by
  obtain ⟨-, -, -, -, hn₁, hn₂⟩ := h.good_props hg
  have hu2 := h.toBar_sq hg.1 (sq_of_good hg)
  have hp₁ := hg.2.2.1
  have hp₂ := hg.2.2.2
  rw [barOf_zpowers z u (h.SC hg.1)] at hp₁ hp₂
  exact ⟨outerOK_of_pgl h.pair.odd h.pair.gt3 h.pair.sl₁ hn₁ hu2 hp₁,
    outerOK_of_pgl h.pair.odd h.pair.gt3 h.pair.sl₂ hn₂ hu2 hp₂⟩

end Ctx




end CFSG.GH74.GLS.Stage2.Final.Thm6.L2012
