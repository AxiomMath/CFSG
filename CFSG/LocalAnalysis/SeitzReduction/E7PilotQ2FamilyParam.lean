module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotAlignFieldTriangle
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotQ2FieldSL2

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg

local instance e7PilotQ2FamilyParamNeZeroRank : NeZero Tag.E7.rank := ⟨by decide⟩

section Param

variable {K : Type} [Field K] (σ : K ≃+* K) {G : Type} [Group G] {L : Subgroup G}
  (e : L ≃* adjointGroup .E7 (fixSubfield σ))

structure TwoFieldParam (N : E7Neighbour) (E : Subgroup G) where
  Φ : N.levi K ≃* E
  fix : ∀ x : N.levi (fixSubfield σ), ((Φ (leviInclusion σ N x) : E) : G) =
    ((e.symm (x : adjointGroup .E7 (fixSubfield σ)) : L) : G)

variable {σ e}

theorem TwoFieldParam.map_conj_of_mem {N : E7Neighbour} {E : Subgroup G}
    (h : TwoFieldParam σ e N E) (y : N.levi (fixSubfield σ)) (x : N.levi K) :
    ((h.Φ (leviInclusion σ N y * x * (leviInclusion σ N y)⁻¹) : E) : G) =
      ((e.symm (y : adjointGroup .E7 (fixSubfield σ)) : L) : G) * (h.Φ x : G) *
        ((e.symm (y : adjointGroup .E7 (fixSubfield σ)) : L) : G)⁻¹ := by
  rw [map_mul, map_mul, map_inv, coe_mul, coe_mul, coe_inv, h.fix y]

@[expose] noncomputable def TwoFieldParam.congr {N : E7Neighbour} {E E' : Subgroup G}
    (h : TwoFieldParam σ e N E) (hE : E = E') : TwoFieldParam σ e N E' where
  Φ := h.Φ.trans (MulEquiv.subgroupCongr hE)
  fix x := h.fix x

variable [Finite K]

@[expose] noncomputable def TwoFieldParam.twist {N : E7Neighbour} {E : Subgroup G}
    (h : TwoFieldParam σ e N E) (ρ : K ≃+* K) (hρ : ∀ c : fixSubfield σ, ρ c = c) :
    TwoFieldParam σ e N E where
  Φ := (leviEntrywiseEquiv ρ N).trans h.Φ
  fix x := by
    have hx : leviEntrywiseEquiv ρ N (leviInclusion σ N x) = leviInclusion σ N x := by
      refine Subtype.ext (Subtype.ext ?_)
      have hcomp : (ρ : K →+* K).comp (fixSubfield σ).subtype = (fixSubfield σ).subtype :=
        RingHom.ext fun c => hρ c
      rw [coe_leviEntrywiseEquiv, coe_leviInclusion, F4Pilot.baseChangeGL_baseChangeGL, hcomp]
    rw [MulEquiv.trans_apply, hx]
    exact h.fix x

theorem TwoFieldParam.twist_apply {N : E7Neighbour} {E : Subgroup G}
    (h : TwoFieldParam σ e N E) (ρ : K ≃+* K) (hρ : ∀ c : fixSubfield σ, ρ c = c)
    (x : N.levi K) : (h.twist ρ hρ).Φ x = h.Φ (leviEntrywiseEquiv ρ N x) :=
  rfl

end Param

section Conj

variable {K : Type} [Field K] {σ : K ≃+* K} {G : Type} [Group G] {L : Subgroup G}
  {e : L ≃* adjointGroup .E7 (fixSubfield σ)}

@[expose] noncomputable def TwoFieldParam.toNeighbour {E : Subgroup G}
    (h : TwoFieldParam σ e .high E) (N : E7Neighbour) :
    TwoFieldParam σ e N
      (E.map (MulAut.conj ((e.symm (N.rep (fixSubfield σ)) : L) : G)).toMonoidHom) where
  Φ := ((highLeviConjEquiv K N).symm.trans h.Φ).trans
    ((MulAut.conj ((e.symm (N.rep (fixSubfield σ)) : L) : G)).subgroupMap E)
  fix x := by
    obtain ⟨x₀, rfl⟩ := (highLeviConjEquiv (fixSubfield σ) N).surjective x
    change ((e.symm (N.rep (fixSubfield σ)) : L) : G) *
        (h.Φ ((highLeviConjEquiv K N).symm (leviInclusion σ N
          (highLeviConjEquiv (fixSubfield σ) N x₀))) : G) *
          ((e.symm (N.rep (fixSubfield σ)) : L) : G)⁻¹ =
      ((e.symm (N.rep (fixSubfield σ) * (x₀ : adjointGroup .E7 (fixSubfield σ)) *
        (N.rep (fixSubfield σ))⁻¹) : L) : G)
    rw [leviInclusion, leviBaseChange_highLeviConjEquiv, MulEquiv.symm_apply_apply, ← leviInclusion,
      h.fix x₀, map_mul, map_mul, map_inv, L.coe_mul, L.coe_mul, L.coe_inv]

end Conj

section Twist

variable {K : Type} [Field K] {σ : K ≃+* K} {G : Type} [Group G] {L : Subgroup G}
  {e : L ≃* adjointGroup .E7 (fixSubfield σ)}

@[expose] def TwoFieldParam.TwistAt {N N' : E7Neighbour} {E E' : Subgroup G}
    (h : TwoFieldParam σ e N E) (h' : TwoFieldParam σ e N' E') (ρ : K ≃+* K)
    (γ : Fin (Tag.rank .E7) → ℤ) : Prop :=
  ∀ (hγ : γ ∈ orthRoots N.root) (hγ' : γ ∈ orthRoots N'.root) (a : K),
    ((h.Φ (leviRootElt N hγ a) : E) : G) = h'.Φ (leviRootElt N' hγ' (ρ a))

@[expose] def TwoFieldParam.TwistOn {N N' : E7Neighbour} {E E' : Subgroup G}
    (h : TwoFieldParam σ e N E) (h' : TwoFieldParam σ e N' E') (ρ : K ≃+* K)
    (S : Finset (Fin (Tag.rank .E7))) : Prop :=
  ∀ j ∈ S, h.TwistAt h' ρ (Pi.single j 1) ∧ h.TwistAt h' ρ (-Pi.single j 1)

theorem TwoFieldParam.TwistAt.twist [Finite K] {N N' : E7Neighbour} {E E' : Subgroup G}
    {h : TwoFieldParam σ e N E} {h' : TwoFieldParam σ e N' E'} {ρ : K ≃+* K}
    {γ : Fin (Tag.rank .E7) → ℤ} (hT : h.TwistAt h' ρ γ) (hρ : ∀ c : fixSubfield σ, ρ c = c) :
    h.TwistAt (h'.twist ρ hρ) 1 γ := by
  intro hγ hγ' a
  rw [TwoFieldParam.twist_apply, leviEntrywiseEquiv_leviRootElt]
  exact hT hγ hγ' a

theorem TwoFieldParam.eq_on_leviPiece {N N' : E7Neighbour} {E E' : Subgroup G}
    (h : TwoFieldParam σ e N E) (h' : TwoFieldParam σ e N' E') {J : Finset (Fin (Tag.rank .E7))}
    (hJ : J ⊆ N.nodes) (hJ' : J ⊆ N'.nodes) (hT : h.TwistOn h' 1 J) {x : N.levi K}
    {x' : N'.levi K} (hxx' : (x : adjointGroup .E7 K) = x') (hx : x ∈ leviPiece K N J) :
    ((h.Φ x : E) : G) = h'.Φ x' := by
  set I : Subgroup (adjointGroup .E7 K) := N.levi K ⊓ N'.levi K with hI
  set f : I →* G := E.subtype.comp (h.Φ.toMonoidHom.comp (Subgroup.inclusion inf_le_left))
    with hf
  set f' : I →* G := E'.subtype.comp (h'.Φ.toMonoidHom.comp (Subgroup.inclusion inf_le_right))
    with hf'
  set H : Subgroup (ModGL .E7 K) :=
    ((MonoidHom.eqLocus f f').map I.subtype).map (adjointGroup .E7 K).subtype with hH
  have hgen : rootSpan .E7 K (amalgamRoots J) ≤ H := by
    refine iSup₂_le fun γ hγ => (closure_le _).2 ?_
    rintro _ ⟨c, rfl⟩
    obtain ⟨j, hj, hγj⟩ := hγ
    have hγN : γ ∈ orthRoots N.root := by
      rcases hγj with rfl | rfl
      exacts [single_mem_orthRoots (hJ hj), neg_single_mem_orthRoots (hJ hj)]
    have hγN' : γ ∈ orthRoots N'.root := by
      rcases hγj with rfl | rfl
      exacts [single_mem_orthRoots (hJ' hj), neg_single_mem_orthRoots (hJ' hj)]
    have hTγ : h.TwistAt h' 1 γ := by
      rcases hγj with rfl | rfl
      exacts [(hT j hj).1, (hT j hj).2]
    refine ⟨⟨pinnedX .E7 K γ c, pinnedX_mem_adjointGroup γ c⟩,
      ⟨⟨_, ⟨(leviRootElt N hγN c).2, (leviRootElt N' hγN' c).2⟩⟩, ?_, rfl⟩, rfl⟩
    exact hTγ hγN hγN' c
  have hxH : ((x : adjointGroup .E7 K) : ModGL .E7 K) ∈ H := hgen (mem_leviPiece.1 hx)
  obtain ⟨_, ⟨y, hy, rfl⟩, hyx⟩ := hxH
  have hyx' : ((y : adjointGroup .E7 K)) = x := Subtype.ext hyx
  have h1 : x = Subgroup.inclusion inf_le_left y := Subtype.ext hyx'.symm
  have h2 : x' = Subgroup.inclusion inf_le_right y := Subtype.ext (hxx'.symm.trans hyx'.symm)
  rw [h1, h2]
  exact hy

end Twist

section Transfer

variable {K : Type} [Field K] [CharP K 2] {σ : K ≃+* K} {G : Type} [Group G] {L : Subgroup G}
  {e : L ≃* adjointGroup .E7 (fixSubfield σ)}

theorem TwoFieldParam.TwistAt.conj_word {N N' : E7Neighbour} {E E' : Subgroup G}
    {h : TwoFieldParam σ e N E} {h' : TwoFieldParam σ e N' E'} {ρ : K ≃+* K}
    {γ : Fin (Tag.rank .E7) → ℤ} (hT : h.TwistAt h' ρ γ) (hγN : γ ∈ orthRoots N.root)
    (hγN' : γ ∈ orthRoots N'.root) (ω : List (Fin (Tag.rank .E7)))
    (hωN : wordElt (fixSubfield σ) ω ∈ rootSpan .E7 (fixSubfield σ) (orthRoots N.root))
    (hωN' : wordElt (fixSubfield σ) ω ∈ rootSpan .E7 (fixSubfield σ) (orthRoots N'.root)) :
    h.TwistAt h' ρ ((coxeterSystem .E7).wordProd ω • γ) := by
  intro hδ hδ' a
  set n : adjointGroup .E7 (fixSubfield σ) :=
    ⟨wordElt (fixSubfield σ) ω, wordElt_mem_adjointGroup ω⟩ with hn
  set y : N.levi (fixSubfield σ) := ⟨n, mem_subgroupOf.2 hωN⟩ with hy
  set y' : N'.levi (fixSubfield σ) := ⟨n, mem_subgroupOf.2 hωN'⟩ with hy'
  have hconj : ∀ (M : E7Neighbour) (z : M.levi (fixSubfield σ)), (z : adjointGroup .E7 _) = n →
      ∀ (hγM : γ ∈ orthRoots M.root) (hδM : (coxeterSystem .E7).wordProd ω • γ ∈ orthRoots M.root)
        (b : K), leviRootElt M hδM b =
          leviInclusion σ M z * leviRootElt M hγM b * (leviInclusion σ M z)⁻¹ := by
    intro M z hz hγM hδM b
    refine Subtype.ext (Subtype.ext ?_)
    simp only [coe_leviRootElt, Subgroup.coe_mul, Subgroup.coe_inv, coe_leviInclusion, hz, hn]
    rw [baseChangeGL_wordElt, wordElt_conj_pinnedX ω hγM.1]
  rw [hconj N y rfl hγN hδ a, h.map_conj_of_mem y, hT hγN hγN' a,
    hconj N' y' rfl hγN' hδ' (ρ a), h'.map_conj_of_mem y']

theorem TwoFieldParam.TwistAt.transfer_single {N N' : E7Neighbour} {E E' : Subgroup G}
    {h : TwoFieldParam σ e N E} {h' : TwoFieldParam σ e N' E'} {ρ : K ≃+* K}
    {a b : Fin (Tag.rank .E7)} (ha : a ∈ N.nodes) (ha' : a ∈ N'.nodes)
    (hT : h.TwistAt h' ρ (Pi.single a 1) ∧ h.TwistAt h' ρ (-Pi.single a 1))
    (ω : List (Fin (Tag.rank .E7)))
    (hω : (coxeterSystem .E7).wordProd ω • (Pi.single a 1 : Fin (Tag.rank .E7) → ℤ) =
      Pi.single b 1)
    (hωN : wordElt (fixSubfield σ) ω ∈ rootSpan .E7 (fixSubfield σ) (orthRoots N.root))
    (hωN' : wordElt (fixSubfield σ) ω ∈ rootSpan .E7 (fixSubfield σ) (orthRoots N'.root)) :
    h.TwistAt h' ρ (Pi.single b 1) ∧ h.TwistAt h' ρ (-Pi.single b 1) := by
  refine ⟨?_, ?_⟩
  · have h1 := hT.1.conj_word (single_mem_orthRoots ha) (single_mem_orthRoots ha') ω hωN hωN'
    rwa [hω] at h1
  · have h1 := hT.2.conj_word (neg_single_mem_orthRoots ha) (neg_single_mem_orthRoots ha') ω hωN
      hωN'
    rwa [smul_neg, hω] at h1

theorem TwoFieldParam.TwistAt.transfer_pair {N N' : E7Neighbour} {E E' : Subgroup G}
    {h : TwoFieldParam σ e N E} {h' : TwoFieldParam σ e N' E'} {ρ : K ≃+* K}
    {a b : Fin (Tag.rank .E7)} (ha : a ∈ N.nodes) (ha' : a ∈ N'.nodes) (hb : b ∈ N.nodes)
    (hb' : b ∈ N'.nodes)
    (hab : (a, b) = (2, 3) ∨ (a, b) = (3, 1) ∨ (a, b) = (3, 4) ∨ (a, b) = (5, 6))
    (hT : h.TwistAt h' ρ (Pi.single a 1) ∧ h.TwistAt h' ρ (-Pi.single a 1)) :
    h.TwistAt h' ρ (Pi.single b 1) ∧ h.TwistAt h' ρ (-Pi.single b 1) := by
  have hmem : ∀ M : E7Neighbour, a ∈ M.nodes → b ∈ M.nodes →
      wordElt (fixSubfield σ) [a, b] ∈ rootSpan .E7 (fixSubfield σ) (orthRoots M.root) :=
    fun M haM hbM => wordElt_mem_rootSpan_of_nodes fun i hi => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      exacts [haM, hbM]
  exact TwoFieldParam.TwistAt.transfer_single ha ha' hT [a, b] (wordProd_pair_single hab)
    (hmem N ha hb) (hmem N' ha' hb')

end Transfer

section RankOne

variable {K : Type} [Field K] [Finite K] [CharP K 2] {σ : K ≃+* K} {G : Type} [Group G]
  {L : Subgroup G} {e : L ≃* adjointGroup .E7 (fixSubfield σ)}

theorem TwoFieldParam.exists_twistAt_single_of_map_eq {N N' : E7Neighbour} {E E' : Subgroup G}
    (h : TwoFieldParam σ e N E) (h' : TwoFieldParam σ e N' E') {j : Fin (Tag.rank .E7)}
    (hj : j ∈ N.nodes) (hj' : j ∈ N'.nodes)
    (hmap : ((leviPiece K N {j}).map h.Φ.toMonoidHom).map E.subtype =
      ((leviPiece K N' {j}).map h'.Φ.toMonoidHom).map E'.subtype) :
    ∃ ρ : K ≃+* K, (∀ c : fixSubfield σ, ρ c = c) ∧ h.TwistAt h' ρ (Pi.single j 1) ∧
      h.TwistAt h' ρ (-Pi.single j 1) := by
  have hα : IsRoot .E7 (Pi.single j 1 : Fin (Tag.rank .E7) → ℤ) := isRoot_single _ j
  obtain ⟨hRinj, hrange, -, hgen, -⟩ :=
    CFSG.RankThree.Chevalley.even_Chevalley_pinned_root_SL2_maps .E7 K hα
  set R := rootSL2 .E7 K (Pi.single j 1 : Fin (Tag.rank .E7) → ℤ) with hR
  have hRmem : ∀ M : E7Neighbour, j ∈ M.nodes → ∀ A,
      R A ∈ rootSpan .E7 K (orthRoots M.root) := by
    intro M hjM A
    have hA : R A ∈ R.range := ⟨A, rfl⟩
    rw [hrange] at hA
    have hle : rootSubgroup .E7 K (Pi.single j 1) ⊔ rootSubgroup .E7 K (-Pi.single j 1) ≤
        rootSpan .E7 K (orthRoots M.root) :=
      sup_le (le_iSup₂_of_le (f := fun α (_ : α ∈ orthRoots M.root) => rootSubgroup .E7 K α)
          _ (single_mem_orthRoots hjM) le_rfl)
        (le_iSup₂_of_le (f := fun α (_ : α ∈ orthRoots M.root) => rootSubgroup .E7 K α)
          _ (neg_single_mem_orthRoots hjM) le_rfl)
    exact hle hA
  let ψ : ∀ M : E7Neighbour, j ∈ M.nodes →
      Matrix.SpecialLinearGroup (Fin 2) K →* M.levi K := fun M hjM =>
    (R.codRestrict (adjointGroup .E7 K) fun A =>
      EPilot.rootSpan_le_adjointGroup' _ (hRmem M hjM A)).codRestrict (M.levi K) fun A =>
        mem_subgroupOf.2 (hRmem M hjM A)
  have hψ : ∀ M hjM A, (((ψ M hjM A : M.levi K) : adjointGroup .E7 K) : ModGL .E7 K) = R A :=
    fun _ _ _ => rfl
  have hψinj : ∀ M hjM, Function.Injective (ψ M hjM) := fun M hjM A B hAB =>
    hRinj (by rw [← hψ M hjM A, ← hψ M hjM B, hAB])
  have hψrange : ∀ M hjM, (ψ M hjM).range = leviPiece K M {j} := by
    intro M hjM
    ext x
    rw [mem_leviPiece, rootSpan_amalgamRoots_singleton, ← hrange]
    constructor
    · rintro ⟨A, rfl⟩
      exact ⟨A, rfl⟩
    · rintro ⟨A, hA⟩
      exact ⟨A, Subtype.ext (Subtype.ext hA)⟩
  set ε := E.subtype.comp (h.Φ.toMonoidHom.comp (ψ N hj)) with hε
  set ε' := E'.subtype.comp (h'.Φ.toMonoidHom.comp (ψ N' hj')) with hε'
  have hεinj : Function.Injective ε :=
    Subtype.val_injective.comp (h.Φ.injective.comp (hψinj N hj))
  have hε'inj : Function.Injective ε' :=
    Subtype.val_injective.comp (h'.Φ.injective.comp (hψinj N' hj'))
  have hεrange : ε.range = ε'.range := by
    rw [hε, hε', MonoidHom.range_comp, MonoidHom.range_comp, MonoidHom.range_comp,
      MonoidHom.range_comp, hψrange N hj, hψrange N' hj']
    exact hmap
  set θ : MulAut (Matrix.SpecialLinearGroup (Fin 2) K) := ((MonoidHom.ofInjective hεinj).trans
    (MulEquiv.subgroupCongr hεrange)).trans (MonoidHom.ofInjective hε'inj).symm with hθdef
  have hθ : ∀ A, ε' (θ A) = ε A := by
    intro A
    have h1 := (MonoidHom.ofInjective hε'inj).apply_symm_apply
      (MulEquiv.subgroupCongr hεrange (MonoidHom.ofInjective hεinj A))
    have h2 := congrArg Subtype.val h1
    rw [MonoidHom.ofInjective_apply] at h2
    exact h2
  have hk : ∀ (M : E7Neighbour) (hjM : j ∈ M.nodes) (EM : Subgroup G)
      (hM : TwoFieldParam σ e M EM) (γ : Fin (Tag.rank .E7) → ℤ) (hγ : γ ∈ orthRoots M.root)
      (c : fixSubfield σ) (A : Matrix.SpecialLinearGroup (Fin 2) K),
        R A = pinnedX .E7 K γ (c : K) →
        ((hM.Φ (ψ M hjM A) : EM) : G) =
          ((e.symm ⟨pinnedX .E7 (fixSubfield σ) γ c, pinnedX_mem_adjointGroup γ c⟩ : L) : G) := by
    intro M hjM EM hM γ hγ c A hA
    have h1 : ψ M hjM A = leviInclusion σ M (leviRootElt M hγ c) := by
      refine Subtype.ext (Subtype.ext ?_)
      rw [hψ M hjM A, hA, coe_leviInclusion, coe_leviRootElt, baseChangeGL_pinnedX]
      rfl
    rw [h1, hM.fix]
    rfl
  have hfixU : ∀ c : fixSubfield σ, θ (sl2Upper ((fixSubfield σ).subtype c)) =
      sl2Upper ((fixSubfield σ).subtype c) := by
    intro c
    apply hε'inj
    rw [hθ]
    change ((h.Φ (ψ N hj (sl2Upper (c : K))) : E) : G) =
      ((h'.Φ (ψ N' hj' (sl2Upper (c : K))) : E') : G)
    rw [hk N hj E h _ (single_mem_orthRoots hj) c (sl2Upper (c : K)) (hgen (c : K)).1,
      hk N' hj' E' h' _ (single_mem_orthRoots hj') c (sl2Upper (c : K)) (hgen (c : K)).1]
  have hfixL : ∀ c : fixSubfield σ, θ (sl2Lower ((fixSubfield σ).subtype c)) =
      sl2Lower ((fixSubfield σ).subtype c) := by
    intro c
    apply hε'inj
    rw [hθ]
    change ((h.Φ (ψ N hj (sl2Lower (c : K))) : E) : G) =
      ((h'.Φ (ψ N' hj' (sl2Lower (c : K))) : E') : G)
    rw [hk N hj E h _ (neg_single_mem_orthRoots hj) c (sl2Lower (c : K)) (hgen (c : K)).2,
      hk N' hj' E' h' _ (neg_single_mem_orthRoots hj') c (sl2Lower (c : K)) (hgen (c : K)).2]
  obtain ⟨ρ, hρ, hθρ⟩ :=
    E8Pilot.exists_ringEquiv_of_forall_sl2_of_charTwo (fixSubfield σ).subtype θ hfixU hfixL
  refine ⟨ρ, fun c => hρ c, ?_, ?_⟩
  · intro hγ hγ' a
    have h1 : leviRootElt N hγ a = ψ N hj (sl2Upper a) :=
      Subtype.ext (Subtype.ext ((coe_leviRootElt N hγ a).trans (hgen a).1.symm))
    have h2 : leviRootElt N' hγ' (ρ a) = ψ N' hj' (sl2Upper (ρ a)) :=
      Subtype.ext (Subtype.ext ((coe_leviRootElt N' hγ' (ρ a)).trans (hgen (ρ a)).1.symm))
    rw [h1, h2, ← (hθρ a).1]
    exact (hθ (sl2Upper a)).symm
  · intro hγ hγ' a
    have h1 : leviRootElt N hγ a = ψ N hj (sl2Lower a) :=
      Subtype.ext (Subtype.ext ((coe_leviRootElt N hγ a).trans (hgen a).2.symm))
    have h2 : leviRootElt N' hγ' (ρ a) = ψ N' hj' (sl2Lower (ρ a)) :=
      Subtype.ext (Subtype.ext ((coe_leviRootElt N' hγ' (ρ a)).trans (hgen (ρ a)).2.symm))
    rw [h1, h2, ← (hθρ a).2]
    exact (hθ (sl2Lower a)).symm

end RankOne

end CFSG.SeitzReduction.E7Pilot
