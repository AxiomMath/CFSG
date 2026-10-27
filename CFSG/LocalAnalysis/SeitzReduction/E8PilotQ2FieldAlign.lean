module

public import CFSG.LocalAnalysis.SeitzReduction.E8PilotQ2FieldSL2
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotAlignFieldTriangle
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersThData
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E8Pilot

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Steinberg
open CFSG.Quasithin (perfectCore perfectCore_le)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)

local instance e8PilotQ2FieldAlignNeZeroRank : NeZero Tag.E8.rank := ⟨by decide⟩

section Param

variable {K : Type} [Field K] {K₂ : Type} [Field K₂] (ι : K →+* K₂) {G : Type} [Group G]
  {L : Subgroup G} (e : L ≃* adjointGroup .E8 K)

structure TwoFieldParam (N : E8Neighbour) (E : Subgroup G) where
  Φ : N.levi K₂ ≃* E
  fix : ∀ x : N.levi K, ((Φ (leviBaseChange ι N x) : E) : G) = ((e.symm x : L) : G)

variable {ι e}

theorem TwoFieldParam.map_conj_of_mem {N : E8Neighbour} {E : Subgroup G}
    (h : TwoFieldParam ι e N E) (y : N.levi K) (x : N.levi K₂) :
    ((h.Φ (leviBaseChange ι N y * x * (leviBaseChange ι N y)⁻¹) : E) : G) =
      ((e.symm (y : adjointGroup .E8 K) : L) : G) * (h.Φ x : G) *
        ((e.symm (y : adjointGroup .E8 K) : L) : G)⁻¹ := by
  rw [map_mul, map_mul, map_inv, coe_mul, coe_mul, coe_inv, h.fix y]

@[expose] noncomputable def TwoFieldParam.toNeighbour {E : Subgroup G}
    (h : TwoFieldParam ι e .high E) (N : E8Neighbour) :
    TwoFieldParam ι e N (E.map (MulAut.conj ((e.symm (N.rep K) : L) : G)).toMonoidHom) where
  Φ := ((highLeviConjEquiv K₂ N).symm.trans h.Φ).trans
    ((MulAut.conj ((e.symm (N.rep K) : L) : G)).subgroupMap E)
  fix x := by
    obtain ⟨x₀, rfl⟩ := (highLeviConjEquiv K N).surjective x
    change ((e.symm (N.rep K) : L) : G) *
        (h.Φ ((highLeviConjEquiv K₂ N).symm (leviBaseChange ι N
          (highLeviConjEquiv K N x₀))) : G) * ((e.symm (N.rep K) : L) : G)⁻¹ =
      ((e.symm (N.rep K * (x₀ : adjointGroup .E8 K) * (N.rep K)⁻¹) : L) : G)
    rw [leviBaseChange_highLeviConjEquiv, MulEquiv.symm_apply_apply, h.fix x₀, map_mul, map_mul,
      map_inv, L.coe_mul, L.coe_mul, L.coe_inv]

variable [Finite K₂]

@[expose] noncomputable def TwoFieldParam.twist {N : E8Neighbour} {E : Subgroup G}
    (h : TwoFieldParam ι e N E) (ρ : K₂ ≃+* K₂) (hρ : ∀ c : K, ρ (ι c) = ι c) :
    TwoFieldParam ι e N E where
  Φ := (leviEntrywiseEquiv ρ N).trans h.Φ
  fix x := by
    have hx : leviEntrywiseEquiv ρ N (leviBaseChange ι N x) = leviBaseChange ι N x := by
      refine Subtype.ext (Subtype.ext ?_)
      have hcomp : (ρ : K₂ →+* K₂).comp ι = ι := RingHom.ext fun c => hρ c
      rw [coe_leviEntrywiseEquiv, coe_leviBaseChange, F4Pilot.baseChangeGL_baseChangeGL, hcomp]
    rw [MulEquiv.trans_apply, hx]
    exact h.fix x

theorem TwoFieldParam.twist_apply {N : E8Neighbour} {E : Subgroup G}
    (h : TwoFieldParam ι e N E) (ρ : K₂ ≃+* K₂) (hρ : ∀ c : K, ρ (ι c) = ι c) (x : N.levi K₂) :
    (h.twist ρ hρ).Φ x = h.Φ (leviEntrywiseEquiv ρ N x) :=
  rfl

end Param

section Twist

variable {K : Type} [Field K] {K₂ : Type} [Field K₂] {ι : K →+* K₂} {G : Type} [Group G]
  {L : Subgroup G} {e : L ≃* adjointGroup .E8 K}

@[expose] def TwoFieldParam.TwistAt {N N' : E8Neighbour} {E E' : Subgroup G}
    (h : TwoFieldParam ι e N E) (h' : TwoFieldParam ι e N' E') (ρ : K₂ ≃+* K₂)
    (γ : Fin (Tag.rank .E8) → ℤ) : Prop :=
  ∀ (hγ : γ ∈ orthRoots N.root) (hγ' : γ ∈ orthRoots N'.root) (a : K₂),
    ((h.Φ (leviRootElt N hγ a) : E) : G) = h'.Φ (leviRootElt N' hγ' (ρ a))

theorem TwoFieldParam.TwistAt.twist [Finite K₂] {N N' : E8Neighbour} {E E' : Subgroup G}
    {h : TwoFieldParam ι e N E} {h' : TwoFieldParam ι e N' E'} {ρ : K₂ ≃+* K₂}
    {γ : Fin (Tag.rank .E8) → ℤ} (hT : h.TwistAt h' ρ γ) (hρ : ∀ c : K, ρ (ι c) = ι c) :
    h.TwistAt (h'.twist ρ hρ) 1 γ := by
  intro hγ hγ' a
  rw [TwoFieldParam.twist_apply, leviEntrywiseEquiv_leviRootElt]
  exact hT hγ hγ' a

variable [CharP K₂ 2]

theorem TwoFieldParam.TwistAt.conj_word {N N' : E8Neighbour} {E E' : Subgroup G}
    {h : TwoFieldParam ι e N E} {h' : TwoFieldParam ι e N' E'} {ρ : K₂ ≃+* K₂}
    {γ : Fin (Tag.rank .E8) → ℤ} (hT : h.TwistAt h' ρ γ) (hγN : γ ∈ orthRoots N.root)
    (hγN' : γ ∈ orthRoots N'.root) (ω : List (Fin (Tag.rank .E8)))
    (hωN : wordElt K ω ∈ rootSpan .E8 K (orthRoots N.root))
    (hωN' : wordElt K ω ∈ rootSpan .E8 K (orthRoots N'.root)) :
    h.TwistAt h' ρ ((coxeterSystem .E8).wordProd ω • γ) := by
  intro hδ hδ' a
  set n : adjointGroup .E8 K := ⟨wordElt K ω, wordElt_mem_adjointGroup ω⟩ with hn
  set y : N.levi K := ⟨n, mem_subgroupOf.2 hωN⟩ with hy
  set y' : N'.levi K := ⟨n, mem_subgroupOf.2 hωN'⟩ with hy'
  have hconj : ∀ (M : E8Neighbour) (z : M.levi K), (z : adjointGroup .E8 _) = n →
      ∀ (hγM : γ ∈ orthRoots M.root) (hδM : (coxeterSystem .E8).wordProd ω • γ ∈ orthRoots M.root)
        (b : K₂), leviRootElt M hδM b =
          leviBaseChange ι M z * leviRootElt M hγM b * (leviBaseChange ι M z)⁻¹ := by
    intro M z hz hγM hδM b
    refine Subtype.ext (Subtype.ext ?_)
    simp only [coe_leviRootElt, Subgroup.coe_mul, Subgroup.coe_inv, coe_leviBaseChange, hz, hn]
    rw [baseChangeGL_wordElt, wordElt_conj_pinnedX ω hγM.1]
  rw [hconj N y rfl hγN hδ a, h.map_conj_of_mem y, hT hγN hγN' a,
    hconj N' y' rfl hγN' hδ' (ρ a), h'.map_conj_of_mem y']

@[expose] def TwoFieldParam.TwistOn {N N' : E8Neighbour} {E E' : Subgroup G}
    (h : TwoFieldParam ι e N E) (h' : TwoFieldParam ι e N' E') (ρ : K₂ ≃+* K₂)
    (S : Finset (Fin (Tag.rank .E8))) : Prop :=
  ∀ j ∈ S, h.TwistAt h' ρ (Pi.single j 1) ∧ h.TwistAt h' ρ (-Pi.single j 1)

theorem TwoFieldParam.TwistAt.transfer_single {N N' : E8Neighbour} {E E' : Subgroup G}
    {h : TwoFieldParam ι e N E} {h' : TwoFieldParam ι e N' E'} {ρ : K₂ ≃+* K₂}
    {a b : Fin (Tag.rank .E8)} (ha : a ∈ N.nodes) (ha' : a ∈ N'.nodes)
    (hT : h.TwistAt h' ρ (Pi.single a 1) ∧ h.TwistAt h' ρ (-Pi.single a 1))
    (ω : List (Fin (Tag.rank .E8)))
    (hω : (coxeterSystem .E8).wordProd ω • (Pi.single a 1 : Fin (Tag.rank .E8) → ℤ) =
      Pi.single b 1)
    (hωN : wordElt K ω ∈ rootSpan .E8 K (orthRoots N.root))
    (hωN' : wordElt K ω ∈ rootSpan .E8 K (orthRoots N'.root)) :
    h.TwistAt h' ρ (Pi.single b 1) ∧ h.TwistAt h' ρ (-Pi.single b 1) := by
  refine ⟨?_, ?_⟩
  · have h1 := hT.1.conj_word (single_mem_orthRoots ha) (single_mem_orthRoots ha') ω hωN hωN'
    rwa [hω] at h1
  · have h1 := hT.2.conj_word (neg_single_mem_orthRoots ha) (neg_single_mem_orthRoots ha') ω hωN
      hωN'
    rwa [smul_neg, hω] at h1

theorem TwoFieldParam.TwistAt.transfer_pair {N N' : E8Neighbour} {E E' : Subgroup G}
    {h : TwoFieldParam ι e N E} {h' : TwoFieldParam ι e N' E'} {ρ : K₂ ≃+* K₂}
    {a b : Fin (Tag.rank .E8)} (ha : a ∈ N.nodes) (ha' : a ∈ N'.nodes) (hb : b ∈ N.nodes)
    (hb' : b ∈ N'.nodes)
    (hab : (a, b) = (0, 2) ∨ (a, b) = (2, 3) ∨ (a, b) = (3, 1) ∨ (a, b) = (5, 4) ∨
      (a, b) = (5, 6))
    (hT : h.TwistAt h' ρ (Pi.single a 1) ∧ h.TwistAt h' ρ (-Pi.single a 1)) :
    h.TwistAt h' ρ (Pi.single b 1) ∧ h.TwistAt h' ρ (-Pi.single b 1) := by
  have hmem : ∀ M : E8Neighbour, a ∈ M.nodes → b ∈ M.nodes →
      wordElt K [a, b] ∈ rootSpan .E8 K (orthRoots M.root) :=
    fun M haM hbM => wordElt_mem_rootSpan_of_nodes fun i hi => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      exacts [haM, hbM]
  exact TwoFieldParam.TwistAt.transfer_single ha ha' hT [a, b] (wordProd_pair_single hab)
    (hmem N ha hb) (hmem N' ha' hb')

end Twist

section Triangle

variable {K : Type} [Field K] [CharP K 2] {K₂ : Type} [Field K₂] [CharP K₂ 2] {ι : K →+* K₂}
  {G : Type} [Group G] {L : Subgroup G} {e : L ≃* adjointGroup .E8 K}

theorem TwoFieldParam.twistOn_high_two {E E' : Subgroup G} {hX : TwoFieldParam ι e .high E}
    {hY : TwoFieldParam ι e .two E'} {ρ : K₂ ≃+* K₂}
    (h0 : hX.TwistAt hY ρ (Pi.single 0 1) ∧ hX.TwistAt hY ρ (-Pi.single 0 1)) :
    hX.TwistOn hY ρ {0, 2, 4, 5, 6} := by
  have h2 := TwoFieldParam.TwistAt.transfer_pair (by decide) (by decide) (by decide)
    (by decide) (Or.inl rfl) h0
  have h5 := TwoFieldParam.TwistAt.transfer_single (by decide) (by decide) h0 wordHT
    wordProd_wordHT_single (wordElt_wordHT_mem (Or.inl rfl)) (wordElt_wordHT_mem (Or.inr rfl))
  have h4 := TwoFieldParam.TwistAt.transfer_pair (by decide) (by decide) (by decide)
    (by decide) (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) h5
  have h6 := TwoFieldParam.TwistAt.transfer_pair (by decide) (by decide) (by decide)
    (by decide) (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) h5
  intro j hj
  simp only [Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl
  exacts [h0, h2, h4, h5, h6]

theorem TwoFieldParam.twistOn_high_six {E E' : Subgroup G} {hX : TwoFieldParam ι e .high E}
    {hZ : TwoFieldParam ι e .six E'} {ρ : K₂ ≃+* K₂}
    (h0 : hX.TwistAt hZ ρ (Pi.single 0 1) ∧ hX.TwistAt hZ ρ (-Pi.single 0 1)) :
    hX.TwistOn hZ ρ {0, 1, 2, 3} := by
  have h2 := TwoFieldParam.TwistAt.transfer_pair (by decide) (by decide) (by decide)
    (by decide) (Or.inl rfl) h0
  have h3 := TwoFieldParam.TwistAt.transfer_pair (by decide) (by decide) (by decide)
    (by decide) (Or.inr (Or.inl rfl)) h2
  have h1 := TwoFieldParam.TwistAt.transfer_pair (by decide) (by decide) (by decide)
    (by decide) (Or.inr (Or.inr (Or.inl rfl))) h3
  intro j hj
  simp only [Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl | rfl | rfl | rfl
  exacts [h0, h1, h2, h3]

theorem TwoFieldParam.twistOn_two_six {E E' : Subgroup G} {hY : TwoFieldParam ι e .two E}
    {hZ : TwoFieldParam ι e .six E'} {ρ : K₂ ≃+* K₂}
    (h0 : hY.TwistAt hZ ρ (Pi.single 0 1) ∧ hY.TwistAt hZ ρ (-Pi.single 0 1)) :
    hY.TwistOn hZ ρ {0, 2, 7} := by
  have h2 := TwoFieldParam.TwistAt.transfer_pair (by decide) (by decide) (by decide)
    (by decide) (Or.inl rfl) h0
  have h7 := TwoFieldParam.TwistAt.transfer_single (by decide) (by decide) h0 wordTS
    wordProd_wordTS_single (wordElt_wordTS_mem (Or.inl rfl)) (wordElt_wordTS_mem (Or.inr rfl))
  intro j hj
  simp only [Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl | rfl | rfl
  exacts [h0, h2, h7]

omit [CharP K 2] [CharP K₂ 2] in
theorem twoField_twist_cocycle {E₁ E₂ E₃ : Subgroup G} (hX : TwoFieldParam ι e .high E₁)
    (hY : TwoFieldParam ι e .two E₂) (hZ : TwoFieldParam ι e .six E₃) {ρht ρts ρhs : K₂ ≃+* K₂}
    (hht : hX.TwistAt hY ρht (Pi.single 0 1)) (hts : hY.TwistAt hZ ρts (Pi.single 0 1))
    (hhs : hX.TwistAt hZ ρhs (Pi.single 0 1)) : ρhs = ρht.trans ρts := by
  have hγX : (Pi.single 0 1 : Fin (Tag.rank .E8) → ℤ) ∈ orthRoots E8Neighbour.high.root :=
    single_mem_orthRoots (by decide)
  have hγY : (Pi.single 0 1 : Fin (Tag.rank .E8) → ℤ) ∈ orthRoots E8Neighbour.two.root :=
    single_mem_orthRoots (by decide)
  have hγZ : (Pi.single 0 1 : Fin (Tag.rank .E8) → ℤ) ∈ orthRoots E8Neighbour.six.root :=
    single_mem_orthRoots (by decide)
  ext a
  have h4 : ((hZ.Φ (leviRootElt _ hγZ (ρhs a)) : E₃) : G) =
      hZ.Φ (leviRootElt _ hγZ (ρts (ρht a))) := by
    rw [← hhs hγX hγZ a, hht hγX hγY a, hts hγY hγZ (ρht a)]
  have h5 := hZ.Φ.injective (Subtype.ext h4)
  have h6 := congrArg (fun x : E8Neighbour.six.levi K₂ =>
    ((x : adjointGroup .E8 K₂) : ModGL .E8 K₂)) h5
  simp only [coe_leviRootElt] at h6
  rw [RingEquiv.trans_apply]
  exact pinnedX_injective (τ := .E8) (R := K₂) _ h6

theorem exists_aligned_twoFieldParam [Finite K₂] {E₁ E₂ E₃ : Subgroup G}
    (hX : TwoFieldParam ι e .high E₁) (hY : TwoFieldParam ι e .two E₂)
    (hZ : TwoFieldParam ι e .six E₃) {ρht ρhs ρts : K₂ ≃+* K₂}
    (hρht : ∀ c : K, ρht (ι c) = ι c) (hρhs : ∀ c : K, ρhs (ι c) = ι c)
    (h1 : hX.TwistAt hY ρht (Pi.single 0 1) ∧ hX.TwistAt hY ρht (-Pi.single 0 1))
    (h2 : hX.TwistAt hZ ρhs (Pi.single 0 1) ∧ hX.TwistAt hZ ρhs (-Pi.single 0 1))
    (h3 : hY.TwistAt hZ ρts (Pi.single 0 1) ∧ hY.TwistAt hZ ρts (-Pi.single 0 1)) :
    hX.TwistOn (hY.twist ρht hρht) 1 {0, 2, 4, 5, 6} ∧
      hX.TwistOn (hZ.twist ρhs hρhs) 1 {0, 1, 2, 3} ∧
      (hY.twist ρht hρht).TwistOn (hZ.twist ρhs hρhs) 1 {0, 2, 7} := by
  have hTht := TwoFieldParam.twistOn_high_two h1
  have hThs := TwoFieldParam.twistOn_high_six h2
  have hTts := TwoFieldParam.twistOn_two_six h3
  have hcoc := twoField_twist_cocycle hX hY hZ h1.1 h3.1 h2.1
  refine ⟨fun j hj => ⟨(hTht j hj).1.twist hρht, (hTht j hj).2.twist hρht⟩,
    fun j hj => ⟨(hThs j hj).1.twist hρhs, (hThs j hj).2.twist hρhs⟩, fun j hj => ?_⟩
  have key : ∀ {γ : Fin (Tag.rank .E8) → ℤ}, hY.TwistAt hZ ρts γ →
      (hY.twist ρht hρht).TwistAt (hZ.twist ρhs hρhs) 1 γ := by
    intro γ hT hγ hγ' a
    rw [TwoFieldParam.twist_apply, TwoFieldParam.twist_apply,
      leviEntrywiseEquiv_leviRootElt, leviEntrywiseEquiv_leviRootElt, RingAut.one_apply, hcoc,
      RingEquiv.trans_apply]
    exact hT hγ hγ' (ρht a)
  exact ⟨key (hTts j hj).1, key (hTts j hj).2⟩

omit [CharP K 2] [CharP K₂ 2] in
theorem TwoFieldParam.eq_on_leviPiece {N N' : E8Neighbour} {E E' : Subgroup G}
    (h : TwoFieldParam ι e N E) (h' : TwoFieldParam ι e N' E') {J : Finset (Fin (Tag.rank .E8))}
    (hJ : J ⊆ N.nodes) (hJ' : J ⊆ N'.nodes) (hT : h.TwistOn h' 1 J) {x : N.levi K₂}
    {x' : N'.levi K₂} (hxx' : (x : adjointGroup .E8 K₂) = x') (hx : x ∈ leviPiece K₂ N J) :
    ((h.Φ x : E) : G) = h'.Φ x' := by
  set I : Subgroup (adjointGroup .E8 K₂) := N.levi K₂ ⊓ N'.levi K₂ with hI
  set f : I →* G := E.subtype.comp (h.Φ.toMonoidHom.comp (Subgroup.inclusion inf_le_left))
    with hf
  set f' : I →* G := E'.subtype.comp (h'.Φ.toMonoidHom.comp (Subgroup.inclusion inf_le_right))
    with hf'
  set H : Subgroup (ModGL .E8 K₂) :=
    ((MonoidHom.eqLocus f f').map I.subtype).map (adjointGroup .E8 K₂).subtype with hH
  have hgen : rootSpan .E8 K₂ (amalgamRoots J) ≤ H := by
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
    refine ⟨⟨pinnedX .E8 K₂ γ c, pinnedX_mem_adjointGroup γ c⟩,
      ⟨⟨_, ⟨(leviRootElt N hγN c).2, (leviRootElt N' hγN' c).2⟩⟩, ?_, rfl⟩, rfl⟩
    exact hTγ hγN hγN' c
  have hxH : ((x : adjointGroup .E8 K₂) : ModGL .E8 K₂) ∈ H := hgen (mem_leviPiece.1 hx)
  obtain ⟨_, ⟨y, hy, rfl⟩, hyx⟩ := hxH
  have hyx' : ((y : adjointGroup .E8 K₂)) = x := Subtype.ext hyx
  have h1 : x = Subgroup.inclusion inf_le_left y := Subtype.ext hyx'.symm
  have h2 : x' = Subgroup.inclusion inf_le_right y := Subtype.ext (hxx'.symm.trans hyx'.symm)
  rw [h1, h2]
  exact hy

end Triangle

section RankOne

variable {K : Type} [Field K] {K₂ : Type} [Field K₂] [Finite K₂] [CharP K₂ 2] {ι : K →+* K₂}
  {G : Type} [Group G] {L : Subgroup G} {e : L ≃* adjointGroup .E8 K}

theorem TwoFieldParam.exists_twistAt_single_of_map_eq {N N' : E8Neighbour} {E E' : Subgroup G}
    (h : TwoFieldParam ι e N E) (h' : TwoFieldParam ι e N' E') {j : Fin (Tag.rank .E8)}
    (hj : j ∈ N.nodes) (hj' : j ∈ N'.nodes)
    (hmap : ((leviPiece K₂ N {j}).map h.Φ.toMonoidHom).map E.subtype =
      ((leviPiece K₂ N' {j}).map h'.Φ.toMonoidHom).map E'.subtype) :
    ∃ ρ : K₂ ≃+* K₂, (∀ c : K, ρ (ι c) = ι c) ∧ h.TwistAt h' ρ (Pi.single j 1) ∧
      h.TwistAt h' ρ (-Pi.single j 1) := by
  have hα : IsRoot .E8 (Pi.single j 1 : Fin (Tag.rank .E8) → ℤ) := isRoot_single _ j
  obtain ⟨hRinj, hrange, -, hgen, -⟩ :=
    CFSG.RankThree.Chevalley.even_Chevalley_pinned_root_SL2_maps .E8 K₂ hα
  set R := rootSL2 .E8 K₂ (Pi.single j 1 : Fin (Tag.rank .E8) → ℤ) with hR
  have hRmem : ∀ M : E8Neighbour, j ∈ M.nodes → ∀ A,
      R A ∈ rootSpan .E8 K₂ (orthRoots M.root) := by
    intro M hjM A
    have hA : R A ∈ R.range := ⟨A, rfl⟩
    rw [hrange] at hA
    have hle : rootSubgroup .E8 K₂ (Pi.single j 1) ⊔ rootSubgroup .E8 K₂ (-Pi.single j 1) ≤
        rootSpan .E8 K₂ (orthRoots M.root) :=
      sup_le (le_iSup₂_of_le (f := fun α (_ : α ∈ orthRoots M.root) => rootSubgroup .E8 K₂ α)
          _ (single_mem_orthRoots hjM) le_rfl)
        (le_iSup₂_of_le (f := fun α (_ : α ∈ orthRoots M.root) => rootSubgroup .E8 K₂ α)
          _ (neg_single_mem_orthRoots hjM) le_rfl)
    exact hle hA
  let ψ : ∀ M : E8Neighbour, j ∈ M.nodes →
      Matrix.SpecialLinearGroup (Fin 2) K₂ →* M.levi K₂ := fun M hjM =>
    (R.codRestrict (adjointGroup .E8 K₂) fun A =>
      rootSpan_le_adjointGroup_E8 _ (hRmem M hjM A)).codRestrict (M.levi K₂) fun A =>
        mem_subgroupOf.2 (hRmem M hjM A)
  have hψ : ∀ M hjM A, (((ψ M hjM A : M.levi K₂) : adjointGroup .E8 K₂) : ModGL .E8 K₂) = R A :=
    fun _ _ _ => rfl
  have hψinj : ∀ M hjM, Function.Injective (ψ M hjM) := fun M hjM A B hAB =>
    hRinj (by rw [← hψ M hjM A, ← hψ M hjM B, hAB])
  have hψrange : ∀ M hjM, (ψ M hjM).range = leviPiece K₂ M {j} := by
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
  set θ : MulAut (Matrix.SpecialLinearGroup (Fin 2) K₂) := ((MonoidHom.ofInjective hεinj).trans
    (MulEquiv.subgroupCongr hεrange)).trans (MonoidHom.ofInjective hε'inj).symm with hθdef
  have hθ : ∀ A, ε' (θ A) = ε A := by
    intro A
    have h1 := (MonoidHom.ofInjective hε'inj).apply_symm_apply
      (MulEquiv.subgroupCongr hεrange (MonoidHom.ofInjective hεinj A))
    have h2 := congrArg Subtype.val h1
    rw [MonoidHom.ofInjective_apply] at h2
    exact h2
  have hk : ∀ (M : E8Neighbour) (hjM : j ∈ M.nodes) (EM : Subgroup G)
      (hM : TwoFieldParam ι e M EM) (γ : Fin (Tag.rank .E8) → ℤ) (hγ : γ ∈ orthRoots M.root)
      (c : K) (A : Matrix.SpecialLinearGroup (Fin 2) K₂), R A = pinnedX .E8 K₂ γ (ι c) →
        ((hM.Φ (ψ M hjM A) : EM) : G) =
          ((e.symm ⟨pinnedX .E8 K γ c, pinnedX_mem_adjointGroup γ c⟩ : L) : G) := by
    intro M hjM EM hM γ hγ c A hA
    have h1 : ψ M hjM A = leviBaseChange ι M (leviRootElt M hγ c) := by
      refine Subtype.ext (Subtype.ext ?_)
      rw [hψ M hjM A, hA, coe_leviBaseChange, coe_leviRootElt, baseChangeGL_pinnedX]
    rw [h1, hM.fix]
    rfl
  have hfixU : ∀ c : K, θ (sl2Upper (ι c)) = sl2Upper (ι c) := by
    intro c
    apply hε'inj
    rw [hθ]
    change ((h.Φ (ψ N hj (sl2Upper (ι c))) : E) : G) =
      ((h'.Φ (ψ N' hj' (sl2Upper (ι c))) : E') : G)
    rw [hk N hj E h _ (single_mem_orthRoots hj) c (sl2Upper (ι c)) (hgen (ι c)).1,
      hk N' hj' E' h' _ (single_mem_orthRoots hj') c (sl2Upper (ι c)) (hgen (ι c)).1]
  have hfixL : ∀ c : K, θ (sl2Lower (ι c)) = sl2Lower (ι c) := by
    intro c
    apply hε'inj
    rw [hθ]
    change ((h.Φ (ψ N hj (sl2Lower (ι c))) : E) : G) =
      ((h'.Φ (ψ N' hj' (sl2Lower (ι c))) : E') : G)
    rw [hk N hj E h _ (neg_single_mem_orthRoots hj) c (sl2Lower (ι c)) (hgen (ι c)).2,
      hk N' hj' E' h' _ (neg_single_mem_orthRoots hj') c (sl2Lower (ι c)) (hgen (ι c)).2]
  obtain ⟨ρ, hρ, hθρ⟩ := exists_ringEquiv_of_forall_sl2_of_charTwo ι θ hfixU hfixL
  refine ⟨ρ, hρ, ?_, ?_⟩
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

end CFSG.SeitzReduction.E8Pilot
