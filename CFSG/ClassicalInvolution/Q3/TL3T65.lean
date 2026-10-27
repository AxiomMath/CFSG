module

public import CFSG.ClassicalInvolution.Q3.TL3T81
public import CFSG.ClassicalInvolution.Q3.TL3T48
public import CFSG.ClassicalInvolution.Q3.TL3T61
public import CFSG.ClassicalInvolution.Q3.TL3T73D
public import CFSG.ClassicalInvolution.Q3.TL3T78

public section

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph
open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
open CFSG.ComponentClassification.PresentationLocal Amalg

variable {G : Type} [Group G] {P Q : Set (Subgroup G)} {n k : ℕ}

theorem _root_.CFSG.ClassicalInvolution.Q3.TL4.AECoverHyp.conjE {I : AEIdent P n} (hH : TL4.AECoverHyp I) (g : G) :
    TL4.AECoverHyp (I.conjE g) where
  ker_two := by
    rintro ⟨x, hx⟩
    have hx' : (pSpanConj g P).symm x ∈ I.φ.ker := by
      rw [MonoidHom.mem_ker, ← I.conjHom_apply]
      exact hx
    obtain ⟨k, hk⟩ := hH.ker_two ⟨_, hx'⟩
    refine ⟨k, Subtype.ext ?_⟩
    have e : ((pSpanConj g P).symm x) ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have e' : x ^ 2 ^ k = 1 := by
      have := congrArg (pSpanConj g P) e
      rwa [map_pow, MulEquiv.apply_symm_apply, map_one] at this
    simpa using e'
  card := by
    rintro _ ⟨L, hL, rfl⟩
    rw [conjSub, Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hH.card L hL
  conj_mem := by
    rintro _ ⟨L, hL, rfl⟩ x hx
    have hx₀ : g⁻¹ * x * g ∈ pSpan P := by
      have := ((pSpanConj g P).symm ⟨x, hx⟩).2
      rwa [pSpanConj_symm_apply] at this
    refine ⟨conjSub (g⁻¹ * x * g) L, hH.conj_mem L hL _ hx₀, ?_⟩
    rw [← conjSub_mul, ← conjSub_mul, show g * (g⁻¹ * x * g) = x * g by group]
  label_inj := by
    rintro _ ⟨L, hL, rfl⟩ _ ⟨L', hL', rfl⟩ h
    rw [hH.label_inj L hL L' hL' ((I.map_conj g).symm.trans (h.trans (I.map_conj g)))]
  twin_comm := by
    rintro α h _ ⟨L, hL, rfl⟩ _ ⟨L', hL', rfl⟩ hl hl'
    exact comm_conjSub (hH.twin_comm α h L hL L' hL' ((I.map_conj g).symm.trans hl)
      ((I.map_conj g).symm.trans hl')) g
  twin_z := by
    rintro α h _ ⟨L, hL, rfl⟩ _ ⟨L', hL', rfl⟩ hl hl' v v' hv hv'
    have hv₀ : IsUniqueInvolution L (g⁻¹ * v * g⁻¹⁻¹) := by
      have := hv.conj g⁻¹
      rwa [conjSub_inv_conjSub] at this
    have hv₀' : IsUniqueInvolution L' (g⁻¹ * v' * g⁻¹⁻¹) := by
      have := hv'.conj g⁻¹
      rwa [conjSub_inv_conjSub] at this
    have e := hH.twin_z α h L hL L' hL' ((I.map_conj g).symm.trans hl)
      ((I.map_conj g).symm.trans hl') _ _ hv₀ hv₀'
    calc v = g * (g⁻¹ * v * g⁻¹⁻¹) * g⁻¹ := by group
      _ = g * (g⁻¹ * v' * g⁻¹⁻¹) * g⁻¹ := by rw [e]
      _ = v' := by group

theorem _root_.CFSG.ClassicalInvolution.Q3.TL4.AECoverHyp.exists_section [Finite G] (hn : 5 ≤ n) {I : AEIdent P n}
    (hH : TL4.AECoverHyp I) (hzL : ∀ L ∈ P, ∃ u, IsUniqueInvolution L u) :
    ∃ s : alternatingGroup (Fin n) →* ↥(pSpan P),
      ∀ σ : alternatingGroup (Fin n), I.φ (s σ) = mkQ n (ofPerm (σ : Equiv.Perm (Fin n))) :=
  I.exists_section hn hH.ker_two hH.card hzL
    (fun L hL L' hL' α hα h1 h2 => ⟨hH.twin_comm α hα L hL L' hL' h1 h2,
      hH.twin_z α hα L hL L' hL' h1 h2⟩) hH.label_inj hH.conj_mem

theorem AEIdent.subHyp_over_emb (I : AEIdent P n) {Γ : Finset (Fin n)} (c : Fin k ↪ Fin n)
    (hc : Set.range c = (Γ : Set (Fin n))) {p : Fin n} (hp : p ∉ Γ)
    (hcard : ∀ L ∈ P, Nat.card ↥L = 8) (hconj : ∀ L ∈ P, ∀ x ∈ pSpan P, conjSub x L ∈ P)
    (hinj : ∀ L ∈ P, ∀ L' ∈ P,
      (L.subgroupOf (pSpan P)).map I.φ = (L'.subgroupOf (pSpan P)).map I.φ → L = L') :
    SubHyp I (I.over Γ) c where
  sub := I.over_subset Γ
  miss := ⟨p, by rw [hc]; exact_mod_cast hp⟩
  card := fun L hL => hcard L hL.1
  conj := fun L hL x hx => I.conjSub_mem_over hconj Γ hL hx
  inj := fun L hL L' hL' h => hinj L hL.1 L' hL'.1 h
  lab := by
    intro L hL
    obtain ⟨α, h, b, hαΓ, hlab⟩ := hL.2
    obtain ⟨α', rfl⟩ := exists_map_eq_of_subset c (α := α) fun x hx => by
      rw [hc]
      exact_mod_cast hαΓ hx
    exact ⟨α', h, b, hlab⟩
  surj := by
    intro α' hα' b
    obtain ⟨L, hL, hlab⟩ := I.label_surj (α'.map c) hα' b
    refine ⟨L, ⟨hL, α'.map c, hα', b, ?_, hlab⟩, hlab⟩
    intro x hx
    rw [Finset.mem_map] at hx
    obtain ⟨i, -, rfl⟩ := hx
    have : c i ∈ Set.range c := ⟨i, rfl⟩
    rw [hc] at this
    exact_mod_cast this

theorem mem_conjSub_image_centMembers {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) {g u : G}
    {M : Subgroup G} :
    M ∈ conjSub g '' centMembers Ω u ↔ M ∈ Ω ∧ ∀ m ∈ M, m * (g * u * g⁻¹) = (g * u * g⁻¹) * m := by
  constructor
  · rintro ⟨L, hL, rfl⟩
    refine ⟨hΩ g L hL.1, fun m hm => ?_⟩
    have e := hL.2 _ (mem_conjSub_iff.mp hm)
    calc m * (g * u * g⁻¹) = g * ((g⁻¹ * m * g) * u) * g⁻¹ := by group
      _ = g * (u * (g⁻¹ * m * g)) * g⁻¹ := by rw [e]
      _ = (g * u * g⁻¹) * m := by group
  · rintro ⟨hM, hc⟩
    refine ⟨conjSub g⁻¹ M, ⟨hΩ g⁻¹ M hM, fun l hl => ?_⟩, conjSub_conjSub_inv g M⟩
    have hl' : g * l * g⁻¹ ∈ M := by
      have := mem_conjSub_iff.mp hl
      rwa [inv_inv] at this
    have e := hc _ hl'
    calc l * u = g⁻¹ * ((g * l * g⁻¹) * (g * u * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * u * g⁻¹) * (g * l * g⁻¹)) * g := by rw [e]
      _ = u * l := by group

variable [Finite G] {IH : ℕ → Prop} {Ω : Set (Subgroup G)} {K J : Subgroup G}

structure GlueData {n : ℕ} {I : AEIdent (orbOf (TC.nbrAdj Ω) K J) n} (D : PairChart Ω K J I) where
  s₁ : alternatingGroup (Fin (n + 2)) →* ↥(pSpan (centMembers Ω D.u))
  hs₁ : ∀ σ : alternatingGroup (Fin (n + 2)),
    D.IY.φ (s₁ σ) = mkQ (n + 2) (ofPerm (σ : Equiv.Perm (Fin (n + 2))))
  c₁ : Fin n ↪ Fin (n + 2)
  c₂ : Fin n ↪ Fin (n + 2)
  hc₁ : ∀ x, x ∈ Set.range c₁ ↔ x ≠ D.ι D.a ∧ x ≠ D.ι D.c
  hc₂ : ∀ x, x ∈ Set.range c₂ ↔ x ≠ D.ι D.a' ∧ x ≠ D.ι D.c'
  hZ : ∀ M ∈ centMembers Ω D.u, ∀ (α : Finset (Fin n)) (hα : (α.map c₁).card = 4) (e : Bool),
    (M.subgroupOf (pSpan (centMembers Ω D.u))).map D.IY.φ = memBar (α.map c₁) hα e →
    M ∈ conjSub D.t '' centMembers Ω D.u
  hcorr : ∀ M ∈ centMembers Ω D.u, ∀ (α : Finset (Fin n)) (hα : (α.map c₁).card = 4) (e : Bool),
    (M.subgroupOf (pSpan (centMembers Ω D.u))).map D.IY.φ = memBar (α.map c₁) hα e →
    ∃ (hα' : (α.map c₂).card = 4) (e' : Bool),
      (M.subgroupOf (pSpan (conjSub D.t '' centMembers Ω D.u))).map (D.IY.conjE D.t).φ =
        memBar (α.map c₂) hα' e'
  g : G
  hgY : g ∈ pSpan (centMembers Ω D.u)
  hgv : ∃ v : Fin (n + 2) → ZMod 2, D.IY.φ ⟨g, hgY⟩ = mkQ (n + 2) (ofVec v)
  halign : ∀ τ : alternatingGroup (Fin n),
    D.t * ((s₁ (altExt c₂ τ) : ↥(pSpan (centMembers Ω D.u))) : G) * D.t⁻¹ =
      g * ((s₁ (altExt c₁ τ) : ↥(pSpan (centMembers Ω D.u))) : G) * g⁻¹
  hdisj : ∀ i : Fin n, c₁ i ∈ D.γ.map D.ι → c₂ i ∉ D.γ.map D.ι

namespace PairChart

variable {n : ℕ} {I : AEIdent (orbOf (TC.nbrAdj Ω) K J) n}

theorem nonempty_glueData (hS : CSetting 3 IH Ω K J) (hn : 5 ≤ n) (hM : Model117At n)
    (D : PairChart Ω K J I) : Nonempty (GlueData D) := by
  classical
  have hC := hS.toCHyp
  have hD := hS.cex.toThmDHyp
  have hK : K ∈ Ω := hS.adj.1
  have hn5 : 5 ≤ n := hn
  have hN5 : 5 ≤ n + 2 := by omega
  have hH := hC.aeCoverHyp_orb' hn5 I
  have hH₁ := D.hHY
  have hH₂ := D.hHY.conjE D.t
  have hΩc : ConjInvariant Ω := fun x L hL => hS.cex.hyp.conjInvariant x L hL
  have hJπ : J ∈ orbOf (TC.nbrAdj Ω) K J := mem_orbOf_self K J
  have hzL : ∀ L ∈ centMembers Ω D.u, ∃ v, IsUniqueInvolution L v := fun L hL =>
    (hD.hyp.omega1 L hL.1).1
  obtain ⟨s₁, hs₁⟩ := hH₁.exists_section hN5 hzL
  set s₂ : alternatingGroup (Fin (n + 2)) →* ↥(pSpan (conjSub D.t '' centMembers Ω D.u)) :=
    (pSpanConj D.t (centMembers Ω D.u)).toMonoidHom.comp s₁ with hs₂def
  have hs₂ : ∀ σ : alternatingGroup (Fin (n + 2)),
      (D.IY.conjE D.t).φ (s₂ σ) = mkQ (n + 2) (ofPerm (σ : Equiv.Perm (Fin (n + 2)))) := by
    intro σ
    show D.IY.conjHom D.t (pSpanConj D.t _ (s₁ σ)) = _
    rw [AEIdent.conjHom_apply_conj, hs₁]
  have hs₂v : ∀ σ, ((s₂ σ : ↥(pSpan (conjSub D.t '' centMembers Ω D.u))) : G) =
      D.t * ((s₁ σ : ↥(pSpan (centMembers Ω D.u))) : G) * D.t⁻¹ := fun σ =>
    pSpanConj_apply D.t _ (s₁ σ)
  set Γ₁ : Finset (Fin (n + 2)) := ({D.ι D.a, D.ι D.c} : Finset (Fin (n + 2)))ᶜ with hΓ₁
  have hac₁ : D.ι D.a ≠ D.ι D.c := D.ι.injective.ne D.hac
  have hΓ₁c : Γ₁.card = n := by
    rw [hΓ₁, Finset.card_compl, Finset.card_pair hac₁, Fintype.card_fin]
    omega
  set c₁ : Fin n ↪ Fin (n + 2) := (Γ₁.orderEmbOfFin hΓ₁c).toEmbedding with hc₁def
  have hc₁r : Set.range c₁ = (Γ₁ : Set (Fin (n + 2))) := Finset.range_orderEmbOfFin Γ₁ hΓ₁c
  have hc₁ : ∀ x, x ∈ Set.range c₁ ↔ x ≠ D.ι D.a ∧ x ≠ D.ι D.c := by
    intro x
    rw [hc₁r, Finset.mem_coe, hΓ₁, Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hpΓ : D.ι D.a ∉ Γ₁ := by
    rw [hΓ₁, Finset.mem_compl, not_not]
    exact Finset.mem_insert_self _ _
  have h₁ : SubHyp D.IY (D.IY.over Γ₁) c₁ :=
    D.IY.subHyp_over_emb c₁ hc₁r hpΓ hH₁.card hH₁.conj_mem hH₁.label_inj
  have hwY : D.t * D.u * D.t⁻¹ ∈ pSpan (centMembers Ω D.u) := D.hsub.span_le D.hw
  have hu₂ : D.u ∈ pSpan (conjSub D.t '' centMembers Ω D.u) := by
    have := (pSpanConj D.t (centMembers Ω D.u) ⟨_, D.hsub.span_le D.hw'⟩).2
    rwa [pSpanConj_apply, show D.t * (D.t⁻¹ * D.u * D.t) * D.t⁻¹ = D.u by group] at this
  have hu₂I : (D.IY.conjE D.t).φ ⟨D.u, hu₂⟩ =
      mkQ (n + 2) (ofVec (TL4.pairVec (D.ι D.a') (D.ι D.c'))) := by
    rw [AEIdent.conjE_apply D.IY D.t hu₂ (D.hsub.span_le D.hw')]
    exact D.hpair'
  have hac₂ : D.ι D.a' ≠ D.ι D.c' := D.ι.injective.ne D.hac'
  have hZ₂ : D.IY.over Γ₁ ⊆ conjSub D.t '' centMembers Ω D.u := by
    rintro M ⟨hM, β, hβ, e, hβΓ, hlab⟩
    refine (mem_conjSub_image_centMembers hΩc).mpr ⟨hM.1, fun m hm => ?_⟩
    have hcu := (D.IY.comm_pairVec_iff hN5 hH₁.card hH₁.conj_mem hH₁.label_inj (w := ⟨_, hwY⟩)
      hac₁ D.hpair hM hlab).mpr ⟨fun h' => (Finset.mem_compl.mp (hβΓ h'))
        (Finset.mem_insert_self _ _),
      fun h' => (Finset.mem_compl.mp (hβΓ h')) (Finset.mem_insert_of_mem
        (Finset.mem_singleton_self _))⟩
    exact (hcu m hm).symm
  set J₁ := D.IY.restrict hn5 h₁ with hJ₁
  have hJ₁H := h₁.aeCoverHyp_restrict' hH₁ hn5
  obtain ⟨c₂, hc₂lab⟩ : ∃ c₂ : Fin n ↪ Fin (n + 2), ∀ L ∈ D.IY.over Γ₁,
      ∀ (α : Finset (Fin n)) (hα : α.card = 4) (b : Bool),
      (L.subgroupOf (pSpan (D.IY.over Γ₁))).map J₁.φ = memBar α hα b →
      ∃ (hα' : (α.map c₂).card = 4) (b' : Bool),
        (L.subgroupOf (pSpan (conjSub D.t '' centMembers Ω D.u))).map (D.IY.conjE D.t).φ =
          memBar (α.map c₂) hα' b' :=
    exists_emb_of_aeIdent_small_eq hZ₂ hn5 J₁ (D.IY.conjE D.t) hJ₁H
      (fun L hL => (hD.hyp.omega1 L hL.1.1).1)
  have hmiss₂ : ∃ x, x ∉ Set.range c₂ := by
    by_contra hcon
    push Not at hcon
    have := Fintype.card_le_of_surjective c₂ fun x => hcon x
    simp only [Fintype.card_fin] at this
    omega
  have h₂ : SubHyp (D.IY.conjE D.t) (D.IY.over Γ₁) c₂ :=
    subHyp_of_labels J₁ (D.IY.conjE D.t) hZ₂ hn5 c₂ hmiss₂ h₁.card h₁.conj hH₂.label_inj hc₂lab
  have hc₂ : ∀ x, x ∈ Set.range c₂ ↔ x ≠ D.ι D.a' ∧ x ≠ D.ι D.c' := by
    have hsub : ∀ i, c₂ i ≠ D.ι D.a' ∧ c₂ i ≠ D.ι D.c' := by
      intro i
      obtain ⟨α, hiα, hα⟩ : ∃ α : Finset (Fin n), i ∈ α ∧ α.card = 4 := by
        obtain ⟨α, h1, h2, h3⟩ := Finset.exists_subsuperset_card_eq (s := {i})
          (t := Finset.univ) (n := 4) (Finset.subset_univ _) (by rw [Finset.card_singleton]; norm_num)
          (by rw [Finset.card_univ, Fintype.card_fin]; omega)
        exact ⟨α, Finset.singleton_subset_iff.mp h1, h3⟩
      have hα' : (α.map c₂).card = 4 := by rw [Finset.card_map]; exact hα
      obtain ⟨L, hL, hlab⟩ := h₂.surj α hα' true
      have hL₂ := hZ₂ hL
      have hcu := (( D.IY.conjE D.t).comm_pairVec_iff hN5 hH₂.card hH₂.conj_mem hH₂.label_inj
        (w := ⟨D.u, hu₂⟩) hac₂ hu₂I hL₂ hlab).mp fun l hl => (hL.1.2 l hl).symm
      have hi : c₂ i ∈ α.map c₂ := Finset.mem_map_of_mem _ hiα
      exact ⟨fun h' => hcu.1 (h' ▸ hi), fun h' => hcu.2 (h' ▸ hi)⟩
    have hcard : (Finset.univ.map c₂) = ({D.ι D.a', D.ι D.c'} : Finset (Fin (n + 2)))ᶜ := by
      refine Finset.eq_of_subset_of_card_le (fun x hx => ?_) ?_
      · obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp hx
        rw [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton]
        rintro (h' | h')
        · exact (hsub i).1 h'
        · exact (hsub i).2 h'
      · rw [Finset.card_compl, Finset.card_pair hac₂, Finset.card_map, Finset.card_univ,
          Fintype.card_fin, Fintype.card_fin]
        omega
    intro x
    constructor
    · rintro ⟨i, rfl⟩
      exact hsub i
    · rintro ⟨h1, h2⟩
      have hx : x ∈ Finset.univ.map c₂ := by
        rw [hcard, Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton]
        rintro (h' | h')
        · exact h1 h'
        · exact h2 h'
      obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp hx
      exact ⟨i, rfl⟩
  have hover : ∀ M ∈ centMembers Ω D.u, ∀ (α : Finset (Fin n)) (hα : (α.map c₁).card = 4)
      (e : Bool), (M.subgroupOf (pSpan (centMembers Ω D.u))).map D.IY.φ =
        memBar (α.map c₁) hα e → M ∈ D.IY.over Γ₁ := by
    intro M hM α hα e hlab
    refine ⟨hM, α.map c₁, hα, e, fun y hy => ?_, hlab⟩
    obtain ⟨z, -, rfl⟩ := Finset.mem_map.mp hy
    have : c₁ z ∈ Set.range c₁ := ⟨z, rfl⟩
    rw [hc₁r] at this
    exact_mod_cast this
  have hcorr : ∀ M ∈ centMembers Ω D.u, ∀ (α : Finset (Fin n)) (hα : (α.map c₁).card = 4)
      (e : Bool), (M.subgroupOf (pSpan (centMembers Ω D.u))).map D.IY.φ =
        memBar (α.map c₁) hα e →
      ∃ (hα' : (α.map c₂).card = 4) (e' : Bool),
        (M.subgroupOf (pSpan (conjSub D.t '' centMembers Ω D.u))).map (D.IY.conjE D.t).φ =
          memBar (α.map c₂) hα' e' := by
    intro M hM α hα e hlab
    have hMo := hover M hM α hα e hlab
    obtain ⟨hα₀, b₂, hr⟩ := h₁.restrict_label hn5 hMo hα hlab
    exact hc₂lab M hMo α hα₀ b₂ hr
  have hsame : ∀ L ∈ D.IY.over Γ₁, ∀ (α : Finset (Fin n)) (hα₂ : (α.map c₂).card = 4) (b : Bool),
      (L.subgroupOf (pSpan (conjSub D.t '' centMembers Ω D.u))).map (D.IY.conjE D.t).φ =
        memBar (α.map c₂) hα₂ b →
      ∃ (hα₁ : (α.map c₁).card = 4) (b' : Bool),
        (L.subgroupOf (pSpan (centMembers Ω D.u))).map D.IY.φ = memBar (α.map c₁) hα₁ b' := by
    intro L hL α hα₂ b hl₂
    obtain ⟨β, hβ', b₁, hl₁⟩ := h₁.lab L hL
    obtain ⟨hβ₂, b₃, hl₃⟩ := hcorr L hL.1 β hβ' b₁ hl₁
    have hαβ : α.map c₂ = β.map c₂ := eq_of_memBar_eq' hN5 (hl₂.symm.trans hl₃)
    have := Finset.map_injective c₂ hαβ
    subst this
    exact ⟨hβ', b₁, hl₁⟩
  obtain ⟨g, hgv, hg⟩ := AEIdent.exists_align' hn5 hM (D.IY.conjE D.t) D.IY hH₂.ker_two
    hH₁.ker_two h₂ h₁ hsame hH₁.conj_mem hH₁.label_inj hs₂ hs₁
  have hdisj : ∀ i : Fin n, c₁ i ∈ D.γ.map D.ι → c₂ i ∉ D.γ.map D.ι := by
    by_cases hn5e : n = 5
    · exact hdisj_five_of_eq hn5e hS D hc₁ h₁ hZ₂ hcorr
    have hn6 : 6 ≤ n := by omega
    intro i hi hi₂
    obtain ⟨x₀, hx₀γ, hx₀⟩ := Finset.mem_map.mp hi
    have hx₀a : x₀ ≠ D.a := fun h' => ((hc₁ (c₁ i)).mp ⟨i, rfl⟩).1 (by rw [← hx₀, h'])
    have hx₀c : x₀ ≠ D.c := fun h' => ((hc₁ (c₁ i)).mp ⟨i, rfl⟩).2 (by rw [← hx₀, h'])
    obtain ⟨δ, hδs, hx₀δ, hδ⟩ : ∃ δ : Finset (Fin n), δ ⊆ ({D.a, D.c} : Finset (Fin n))ᶜ ∧
        x₀ ∈ δ ∧ δ.card = 4 := by
      obtain ⟨δ, h1, h2, h3⟩ := Finset.exists_subsuperset_card_eq (s := {x₀})
        (t := ({D.a, D.c} : Finset (Fin n))ᶜ) (n := 4)
        (by
          rw [Finset.singleton_subset_iff, Finset.mem_compl, Finset.mem_insert,
            Finset.mem_singleton]
          rintro (h' | h')
          · exact hx₀a h'
          · exact hx₀c h')
        (by rw [Finset.card_singleton]; norm_num)
        (by rw [Finset.card_compl, Finset.card_pair D.hac, Fintype.card_fin]; omega)
      exact ⟨δ, h2, Finset.singleton_subset_iff.mp h1, h3⟩
    obtain ⟨M, hMπ, hlabM⟩ := I.label_surj δ hδ true
    obtain ⟨hδ', e₁, hlabM₁⟩ := D.hlabι M hMπ δ hδ true hlabM
    have hδΓ : δ.map D.ι ⊆ Γ₁ := by
      intro y hy
      obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hy
      have hz' := Finset.mem_compl.mp (hδs hz)
      rw [hΓ₁, Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton]
      rintro (h' | h')
      · exact hz' (by rw [D.ι.injective h']; exact Finset.mem_insert_self _ _)
      · have hc' : D.c ∈ ({D.a, D.c} : Finset (Fin n)) :=
          Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
        exact hz' (by rw [D.ι.injective h']; exact hc')
    have hMZ : M ∈ D.IY.over Γ₁ := ⟨D.hπY hMπ, δ.map D.ι, hδ', e₁, hδΓ, hlabM₁⟩
    obtain ⟨δ₀, hδ₀⟩ := exists_map_eq_of_subset c₁ (α := δ.map D.ι) fun y hy => by
      rw [hc₁r]
      exact_mod_cast hδΓ hy
    have hiδ₀ : i ∈ δ₀ := by
      have : c₁ i ∈ δ₀.map c₁ := by
        rw [hδ₀, ← hx₀]
        exact Finset.mem_map_of_mem _ hx₀δ
      obtain ⟨i', hi', he⟩ := Finset.mem_map.mp this
      rwa [c₁.injective he] at hi'
    have hδ₀' : (δ₀.map c₁).card = 4 := by rw [hδ₀]; exact hδ'
    have hlabM₁' : (M.subgroupOf (pSpan (centMembers Ω D.u))).map D.IY.φ =
        memBar (δ₀.map c₁) hδ₀' e₁ := by
      rw [hlabM₁]
      congr 1
      exact hδ₀.symm
    obtain ⟨hδ₀c, e₂, hr⟩ := h₁.restrict_label hn5 hMZ hδ₀' hlabM₁'
    obtain ⟨hδ₂, e₃, hlabM₂⟩ := hc₂lab M hMZ δ₀ hδ₀c e₂ hr
    have hJY : J ∈ centMembers Ω D.u := D.hπY hJπ
    have hJsY : D.Js ∈ centMembers Ω D.u := D.hπY D.hJs
    obtain ⟨hγ', b₁, hlabJ₁⟩ := D.hlabι J hJπ D.γ D.hγ D.b D.hlabJ
    obtain ⟨hγ'', b₂, hlabJs₁⟩ := D.hlabι D.Js D.hJs D.γ D.hγ (!D.b) D.hlabJs
    have hKt : conjSub D.t J = K := D.ht'
    have hKst : conjSub D.t D.Js = D.Ks := by rw [← D.htKs', conjSub_conjSub_inv]
    have hK₂ : K ∈ conjSub D.t '' centMembers Ω D.u := ⟨J, hJY, hKt⟩
    have hKs₂ : D.Ks ∈ conjSub D.t '' centMembers Ω D.u := ⟨D.Js, hJsY, hKst⟩
    have hlabK₂ : (K.subgroupOf (pSpan (conjSub D.t '' centMembers Ω D.u))).map
        (D.IY.conjE D.t).φ = memBar (D.γ.map D.ι) hγ' b₁ := by
      have := (D.IY.map_conj D.t (L := J)).trans hlabJ₁
      rw [hKt] at this
      exact this
    have hlabKs₂ : (D.Ks.subgroupOf (pSpan (conjSub D.t '' centMembers Ω D.u))).map
        (D.IY.conjE D.t).φ = memBar (D.γ.map D.ι) hγ' b₂ := by
      have := (D.IY.map_conj D.t (L := D.Js)).trans hlabJs₁
      rw [hKst] at this
      exact this
    have hMK : ∀ x ∈ K, ∀ y ∈ M, x * y = y * x :=
      comm_of_mem_omegaNbr hD.hyp hD.two hK (hC.orb_subset hMπ)
    have hM₂ := hZ₂ hMZ
    have himg : ∀ x ∈ memBar (δ₀.map c₂) hδ₂ e₃, ∀ y ∈ memBar (D.γ.map D.ι) hγ' b₁,
        x * y = y * x := by
      intro x hx y hy
      rw [← hlabM₂] at hx
      rw [← hlabK₂] at hy
      obtain ⟨l, hl, rfl⟩ := (D.IY.conjE D.t).exists_of_mem_map hM₂ hx
      obtain ⟨k, hk, rfl⟩ := (D.IY.conjE D.t).exists_of_mem_map hK₂ hy
      rw [← map_mul, ← map_mul]
      exact congrArg (D.IY.conjE D.t).φ (Subtype.ext (hMK k hk l hl).symm)
    rcases eq_or_disjoint_of_comm himg with he | he
    ·
      have hKnot : K ∉ orbOf (TC.nbrAdj Ω) K J := fun h' => (hC.orb_subset h').2.1 rfl
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
      have hlabM₂' : (M.subgroupOf (pSpan (conjSub D.t '' centMembers Ω D.u))).map
          (D.IY.conjE D.t).φ = memBar (D.γ.map D.ι) hγ' e₃ := by
        rw [hlabM₂]
        congr 1
      by_cases he₃ : e₃ = b₁
      · subst he₃
        have := hH₂.label_inj M hM₂ K hK₂ (hlabM₂'.trans hlabK₂.symm)
        exact hKnot (this ▸ hMπ)
      · have : e₃ = b₂ := by
          cases e₃ <;> cases b₁ <;> cases b₂ <;>
            first | rfl | exact absurd rfl he₃ | exact absurd rfl hb12
        subst this
        have := hH₂.label_inj M hM₂ D.Ks hKs₂ (hlabM₂'.trans hlabKs₂.symm)
        exact D.hKsπ (this ▸ hMπ)
    · exact Finset.disjoint_left.mp he (Finset.mem_map_of_mem _ hiδ₀) hi₂
  refine ⟨{
    s₁ := s₁, hs₁ := hs₁, c₁ := c₁, c₂ := c₂, hc₁ := hc₁, hc₂ := hc₂,
    hZ := fun M hM α hα e hlab => hZ₂ (hover M hM α hα e hlab), hcorr := hcorr,
    g := (g : G), hgY := g.2, hgv := hgv,
    halign := fun τ => by rw [← hs₂v]; exact hg τ,
    hdisj := hdisj }⟩

end PairChart

end CFSG.ClassicalInvolution.Q3.TC.Thin
