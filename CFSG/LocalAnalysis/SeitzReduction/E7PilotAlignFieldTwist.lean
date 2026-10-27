module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotFieldNormalizeConj
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotAlignFieldSL2
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotAlignField

public section

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
open CFSG.Quasithin (perfectCore)

local instance e7PilotAlignFieldTwistNeZeroRank : NeZero Tag.E7.rank := ⟨by decide⟩

section Words

variable (K : Type) [Field K]

noncomputable abbrev wordElt (ω : List (Fin (Tag.rank .E7))) : ModGL .E7 K :=
  (ω.map fun i => weylElt .E7 K i 1).prod

@[expose] noncomputable def wordRep (ω : List (Fin (Tag.rank .E7))) : adjointGroup .E7 K :=
  (ω.map (CFSG.LieType.Chevalley.weylElement .E7 K)).prod

variable {K}

theorem coe_wordRep (ω : List (Fin (Tag.rank .E7))) :
    (wordRep K ω : ModGL .E7 K) = wordElt K ω := by
  rw [wordRep, ← Subgroup.coe_subtype, map_list_prod, List.map_map]
  rfl

theorem wordElt_append (ω₁ ω₂ : List (Fin (Tag.rank .E7))) :
    wordElt K (ω₁ ++ ω₂) = wordElt K ω₁ * wordElt K ω₂ := by
  simp [wordElt, List.prod_append]

theorem wordElt_cons (i : Fin (Tag.rank .E7)) (ω : List (Fin (Tag.rank .E7))) :
    wordElt K (i :: ω) = weylElt .E7 K i 1 * wordElt K ω := by
  simp [wordElt]

theorem wordElt_singleton (i : Fin (Tag.rank .E7)) : wordElt K [i] = weylElt .E7 K i 1 := by
  simp [wordElt]

theorem baseChangeGL_wordElt {k : Type} [Field k] (ι : k →+* K)
    (ω : List (Fin (Tag.rank .E7))) : baseChangeGL ι (wordElt k ω) = wordElt K ω := by
  rw [wordElt, map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp_apply]
  rw [CFSG.Blueprint.Chevalley.weylElt_eq_xUnit_mul, map_mul, map_mul, baseChangeGL_xUnit,
    baseChangeGL_yUnit, CFSG.Blueprint.Chevalley.weylElt_eq_xUnit_mul]
  simp

theorem weylElt_one_mul_self_of_charTwo [CharP K 2] (i : Fin (Tag.rank .E7)) :
    weylElt .E7 K i 1 * weylElt .E7 K i 1 = 1 := by
  rw [CFSG.LieType.Chevalley.weylElt_one_mul_self,
    show (-1 : Kˣ) = 1 from Units.ext (CharTwo.neg_eq 1), torusElt_one]

theorem wordElt_reverse_mul [CharP K 2] (ω : List (Fin (Tag.rank .E7))) :
    wordElt K ω.reverse * wordElt K ω = 1 := by
  induction ω with
  | nil => simp [wordElt]
  | cons i ω ih =>
    rw [List.reverse_cons, wordElt_append, wordElt_singleton, wordElt_cons]
    calc wordElt K ω.reverse * weylElt .E7 K i 1 * (weylElt .E7 K i 1 * wordElt K ω) =
        wordElt K ω.reverse * (weylElt .E7 K i 1 * weylElt .E7 K i 1) * wordElt K ω := by group
      _ = 1 := by rw [weylElt_one_mul_self_of_charTwo, mul_one, ih]

theorem wordElt_reverse [CharP K 2] (ω : List (Fin (Tag.rank .E7))) :
    wordElt K ω.reverse = (wordElt K ω)⁻¹ :=
  eq_inv_of_mul_eq_one_left (wordElt_reverse_mul ω)

end Words

section Membership

variable {K : Type} [Field K]

theorem weylElt_mem_rootSpan {S : Set (Fin (Tag.rank .E7) → ℤ)} {i : Fin (Tag.rank .E7)}
    (h1 : (Pi.single i 1 : Fin (Tag.rank .E7) → ℤ) ∈ S) (h2 : -Pi.single i 1 ∈ S) :
    weylElt .E7 K i 1 ∈ rootSpan .E7 K S := by
  have hx : ∀ c : K, xUnit .E7 K i c ∈ rootSpan .E7 K S := fun c => by
    rw [← pinnedX_single]
    exact le_iSup₂_of_le (f := fun α (_ : α ∈ S) => rootSubgroup .E7 K α) _ h1 le_rfl
      (subset_closure ⟨c, rfl⟩)
  have hy : ∀ c : K, yUnit .E7 K i c ∈ rootSpan .E7 K S := fun c => by
    rw [← pinnedX_neg_single]
    exact le_iSup₂_of_le (f := fun α (_ : α ∈ S) => rootSubgroup .E7 K α) _ h2 le_rfl
      (subset_closure ⟨c, rfl⟩)
  rw [CFSG.Blueprint.Chevalley.weylElt_eq_xUnit_mul]
  exact mul_mem (mul_mem (hx _) (hy _)) (hx _)

theorem wordElt_mem_rootSpan {S : Set (Fin (Tag.rank .E7) → ℤ)} {ω : List (Fin (Tag.rank .E7))}
    (h : ∀ i ∈ ω, (Pi.single i 1 : Fin (Tag.rank .E7) → ℤ) ∈ S ∧ -Pi.single i 1 ∈ S) :
    wordElt K ω ∈ rootSpan .E7 K S :=
  list_prod_mem fun x hx => by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    exact weylElt_mem_rootSpan (h i hi).1 (h i hi).2

end Membership

section Conj

variable {K : Type} [Field K] [CharP K 2]

theorem weylElt_conj_pinnedX_E7 (i : Fin (Tag.rank .E7)) {δ : Fin (Tag.rank .E7) → ℤ}
    (hδ : IsRoot .E7 δ) (c : K) :
    weylElt .E7 K i 1 * pinnedX .E7 K δ c * (weylElt .E7 K i 1)⁻¹ =
      pinnedX .E7 K (reflect .E7 i δ) c := by
  obtain ⟨ε, hε, h⟩ := weylElt_mul_pinnedX_mul_inv K i hδ
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hε1 : ε = 1 := by
    have hsq : (ε - 1) ^ 2 = 0 := by linear_combination hε - (ε - 1) * h2
    exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hsq)
  rw [h, hε1, one_mul]

theorem wordElt_conj_pinnedX (ω : List (Fin (Tag.rank .E7))) {δ : Fin (Tag.rank .E7) → ℤ}
    (hδ : IsRoot .E7 δ) (c : K) :
    wordElt K ω * pinnedX .E7 K δ c * (wordElt K ω)⁻¹ =
      pinnedX .E7 K ((coxeterSystem .E7).wordProd ω • δ) c := by
  induction ω with
  | nil => simp [wordElt]
  | cons i ω ih =>
    rw [wordElt_cons, (coxeterSystem .E7).wordProd_cons, mul_smul, simple_smul]
    calc weylElt .E7 K i 1 * wordElt K ω * pinnedX .E7 K δ c *
          (weylElt .E7 K i 1 * wordElt K ω)⁻¹ =
        weylElt .E7 K i 1 * (wordElt K ω * pinnedX .E7 K δ c * (wordElt K ω)⁻¹) *
          (weylElt .E7 K i 1)⁻¹ := by group
      _ = _ := by rw [ih, weylElt_conj_pinnedX_E7 i (IsRoot.smul hδ _)]

theorem wordElt_reflWord_mem_rootSpan {S : Set (Fin (Tag.rank .E7) → ℤ)}
    (v : List (Fin (Tag.rank .E7))) (i : Fin (Tag.rank .E7))
    (h1 : (coxeterSystem .E7).wordProd v • (Pi.single i 1 : Fin (Tag.rank .E7) → ℤ) ∈ S)
    (h2 : -((coxeterSystem .E7).wordProd v • (Pi.single i 1 : Fin (Tag.rank .E7) → ℤ)) ∈ S) :
    wordElt K (v ++ [i] ++ v.reverse) ∈ rootSpan .E7 K S := by
  rw [wordElt_append, wordElt_append, wordElt_singleton, wordElt_reverse]
  have hmem : weylElt .E7 K i 1 ∈
      rootSpan .E7 K {Pi.single i 1, -Pi.single i 1} :=
    weylElt_mem_rootSpan (by simp) (by simp)
  have hconj : (rootSpan .E7 K {Pi.single i 1, -Pi.single i 1}).map
      (MulAut.conj (wordElt K v)).toMonoidHom ≤ rootSpan .E7 K S := by
    simp only [rootSpan, Subgroup.map_iSup]
    refine iSup₂_le fun α hα => ?_
    rcases hα with rfl | hα
    · rw [map_conj_prod_weylElt_rootSubgroup K v (isRoot_single _ i)]
      exact le_iSup₂_of_le (f := fun α (_ : α ∈ S) => rootSubgroup .E7 K α) _ h1 le_rfl
    · rw [Set.mem_singleton_iff] at hα
      rw [hα, map_conj_prod_weylElt_rootSubgroup K v (isRoot_neg_single _ i), smul_neg]
      exact le_iSup₂_of_le (f := fun α (_ : α ∈ S) => rootSubgroup .E7 K α) _ h2 le_rfl
  exact hconj ⟨_, hmem, rfl⟩

end Conj

section Twist

variable {K : Type} [Field K]

theorem pinnedX_mem_rootSpan_orthRoots {N : E7Neighbour} {γ : Fin (Tag.rank .E7) → ℤ}
    (hγ : γ ∈ orthRoots N.root) (a : K) :
    pinnedX .E7 K γ a ∈ rootSpan .E7 K (orthRoots N.root) :=
  le_iSup₂_of_le (f := fun α (_ : α ∈ orthRoots N.root) => rootSubgroup .E7 K α) γ hγ le_rfl
    (subset_closure ⟨a, rfl⟩)

@[expose] noncomputable def leviRootElt (N : E7Neighbour) {γ : Fin (Tag.rank .E7) → ℤ}
    (hγ : γ ∈ orthRoots N.root) (a : K) : N.levi K :=
  ⟨⟨pinnedX .E7 K γ a, pinnedX_mem_adjointGroup γ a⟩,
    mem_subgroupOf.2 (pinnedX_mem_rootSpan_orthRoots hγ a)⟩

theorem coe_leviRootElt (N : E7Neighbour) {γ : Fin (Tag.rank .E7) → ℤ}
    (hγ : γ ∈ orthRoots N.root) (a : K) :
    (((leviRootElt N hγ a : N.levi K) : adjointGroup .E7 K) : ModGL .E7 K) = pinnedX .E7 K γ a :=
  rfl

theorem single_mem_orthRoots {N : E7Neighbour} {j : Fin (Tag.rank .E7)} (hj : j ∈ N.nodes) :
    (Pi.single j 1 : Fin (Tag.rank .E7) → ℤ) ∈ orthRoots N.root :=
  ⟨isRoot_single _ j, (N.iform_root_single_eq_zero_iff j).2 hj⟩

theorem neg_single_mem_orthRoots {N : E7Neighbour} {j : Fin (Tag.rank .E7)} (hj : j ∈ N.nodes) :
    (-Pi.single j 1 : Fin (Tag.rank .E7) → ℤ) ∈ orthRoots N.root :=
  ⟨isRoot_neg_single _ j, by
    rw [iform_neg_right_E7, (N.iform_root_single_eq_zero_iff j).2 hj, neg_zero]⟩

variable {σ : K ≃+* K} {G : Type} [Group G] {L : Subgroup G}
  {e : L ≃* adjointGroup .E7 (fixSubfield σ)}

@[expose] def FieldNeighbourIso.TwistAt {N N' : E7Neighbour} (h : FieldNeighbourIso σ e N)
    (h' : FieldNeighbourIso σ e N') (ρ : K ≃+* K) (γ : Fin (Tag.rank .E7) → ℤ) : Prop :=
  ∀ (hγ : γ ∈ orthRoots N.root) (hγ' : γ ∈ orthRoots N'.root) (a : K),
    ((h.Φ (leviRootElt N hγ a) : neighbourCore e N) : G) = h'.Φ (leviRootElt N' hγ' (ρ a))

theorem leviEntrywiseEquiv_leviRootElt [Finite K] (ρ : K ≃+* K) {N : E7Neighbour}
    {γ : Fin (Tag.rank .E7) → ℤ} (hγ : γ ∈ orthRoots N.root) (a : K) :
    leviEntrywiseEquiv ρ N (leviRootElt N hγ a) = leviRootElt N hγ (ρ a) :=
  Subtype.ext (Subtype.ext (baseChangeGL_pinnedX _ γ a))

theorem FieldNeighbourIso.TwistAt.twist [Finite K] {N N' : E7Neighbour}
    {h : FieldNeighbourIso σ e N} {h' : FieldNeighbourIso σ e N'} {ρ : K ≃+* K}
    {γ : Fin (Tag.rank .E7) → ℤ} (hT : h.TwistAt h' ρ γ) (hρ : ∀ c : fixSubfield σ, ρ c = c) :
    h.TwistAt (h'.twist ρ hρ) 1 γ := by
  intro hγ hγ' a
  rw [FieldNeighbourIso.twist_apply, leviEntrywiseEquiv_leviRootElt]
  exact hT hγ hγ' a

theorem wordElt_mem_adjointGroup (ω : List (Fin (Tag.rank .E7))) :
    wordElt K ω ∈ adjointGroup .E7 K :=
  list_prod_mem fun x hx => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    exact weylElt_mem_adjointGroup i 1

end Twist

section Transfer

variable {K : Type} [Field K] [CharP K 2] {σ : K ≃+* K} {G : Type} [Group G] {L : Subgroup G}
  {e : L ≃* adjointGroup .E7 (fixSubfield σ)}

theorem FieldNeighbourIso.TwistAt.conj_word {N N' : E7Neighbour}
    {h : FieldNeighbourIso σ e N} {h' : FieldNeighbourIso σ e N'} {ρ : K ≃+* K}
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

end Transfer

section RankOne

theorem exists_ne_zero_ne_one_of_four_le {k : Type} [Field k] [Finite k] (hq : 4 ≤ Nat.card k) :
    ∃ c : k, c ≠ 0 ∧ c ≠ 1 := by
  classical
  by_contra hall
  push Not at hall
  have : Fintype k := Fintype.ofFinite k
  have hsub : (Finset.univ : Finset k) ⊆ {0, 1} := fun c _ => by
    by_cases hc : c = 0
    · simp [hc]
    · simp [hall c hc]
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at h1
  have h2 := Finset.card_insert_le (0 : k) {1}
  rw [Finset.card_singleton] at h2
  omega

theorem rootSpan_amalgamRoots_singleton
    {K : Type} [Field K] (j : Fin (Tag.rank .E7)) :
    rootSpan .E7 K (amalgamRoots {j}) =
      rootSubgroup .E7 K (Pi.single j 1) ⊔ rootSubgroup .E7 K (-Pi.single j 1) := by
  refine le_antisymm (iSup₂_le fun γ hγ => ?_) (sup_le ?_ ?_)
  · obtain ⟨j', hj', rfl | rfl⟩ := hγ
    · rw [Finset.mem_singleton.1 hj']
      exact le_sup_left
    · rw [Finset.mem_singleton.1 hj']
      exact le_sup_right
  · exact le_iSup₂_of_le (f := fun α (_ : α ∈ amalgamRoots {j}) => rootSubgroup .E7 K α)
      (Pi.single j 1) ⟨j, Finset.mem_singleton_self j, Or.inl rfl⟩ le_rfl
  · exact le_iSup₂_of_le (f := fun α (_ : α ∈ amalgamRoots {j}) => rootSubgroup .E7 K α)
      (-Pi.single j 1) ⟨j, Finset.mem_singleton_self j, Or.inr rfl⟩ le_rfl

variable {K : Type} [Field K] [Finite K] [CharP K 2] {σ : K ≃+* K} {G : Type} [Group G]
  [Finite G] {L : Subgroup G} {e : L ≃* adjointGroup .E7 (fixSubfield σ)}

theorem FieldNeighbourIso.exists_twistAt_single {N N' : E7Neighbour}
    (h : FieldNeighbourIso σ e N) (h' : FieldNeighbourIso σ e N')
    (hq : 4 ≤ Nat.card (fixSubfield σ)) {j : Fin (Tag.rank .E7)} (hj : j ∈ N.nodes)
    (hj' : j ∈ N'.nodes) :
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
  set ε := (neighbourCore e N).subtype.comp (h.Φ.toMonoidHom.comp (ψ N hj)) with hε
  set ε' := (neighbourCore e N').subtype.comp (h'.Φ.toMonoidHom.comp (ψ N' hj')) with hε'
  have hεinj : Function.Injective ε :=
    Subtype.val_injective.comp (h.Φ.injective.comp (hψinj N hj))
  have hε'inj : Function.Injective ε' :=
    Subtype.val_injective.comp (h'.Φ.injective.comp (hψinj N' hj'))
  have hJ : ({j} : Finset (Fin (Tag.rank .E7))).card ≤ 2 := by simp
  have hεrange : ε.range = ε'.range := by
    rw [hε, hε', MonoidHom.range_comp, MonoidHom.range_comp, MonoidHom.range_comp,
      MonoidHom.range_comp, hψrange N hj, hψrange N' hj',
      h.map_leviPiece hq (Finset.singleton_subset_iff.2 hj) hJ,
      h'.map_leviPiece hq (Finset.singleton_subset_iff.2 hj') hJ]
  set θ : MulAut (Matrix.SpecialLinearGroup (Fin 2) K) := ((MonoidHom.ofInjective hεinj).trans
    (MulEquiv.subgroupCongr hεrange)).trans (MonoidHom.ofInjective hε'inj).symm with hθdef
  have hθ : ∀ A, ε' (θ A) = ε A := by
    intro A
    have h1 := (MonoidHom.ofInjective hε'inj).apply_symm_apply
      (MulEquiv.subgroupCongr hεrange (MonoidHom.ofInjective hεinj A))
    have h2 := congrArg Subtype.val h1
    rw [MonoidHom.ofInjective_apply] at h2
    exact h2
  have hk : ∀ (M : E7Neighbour) (hjM : j ∈ M.nodes) (hM : FieldNeighbourIso σ e M)
      (γ : Fin (Tag.rank .E7) → ℤ) (hγ : γ ∈ orthRoots M.root) (c : fixSubfield σ)
      (A : Matrix.SpecialLinearGroup (Fin 2) K), R A = pinnedX .E7 K γ (c : K) →
        ((hM.Φ (ψ M hjM A) : neighbourCore e M) : G) =
          ((e.symm ⟨pinnedX .E7 (fixSubfield σ) γ c, pinnedX_mem_adjointGroup γ c⟩ : L) : G) := by
    intro M hjM hM γ hγ c A hA
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
    change ((h.Φ (ψ N hj (sl2Upper (c : K))) : neighbourCore e N) : G) =
      ((h'.Φ (ψ N' hj' (sl2Upper (c : K))) : neighbourCore e N') : G)
    rw [hk N hj h _ (single_mem_orthRoots hj) c (sl2Upper (c : K)) (hgen (c : K)).1,
      hk N' hj' h' _ (single_mem_orthRoots hj') c (sl2Upper (c : K)) (hgen (c : K)).1]
  have hfixL : ∀ c : fixSubfield σ, θ (sl2Lower ((fixSubfield σ).subtype c)) =
      sl2Lower ((fixSubfield σ).subtype c) := by
    intro c
    apply hε'inj
    rw [hθ]
    change ((h.Φ (ψ N hj (sl2Lower (c : K))) : neighbourCore e N) : G) =
      ((h'.Φ (ψ N' hj' (sl2Lower (c : K))) : neighbourCore e N') : G)
    rw [hk N hj h _ (neg_single_mem_orthRoots hj) c (sl2Lower (c : K)) (hgen (c : K)).2,
      hk N' hj' h' _ (neg_single_mem_orthRoots hj') c (sl2Lower (c : K)) (hgen (c : K)).2]
  obtain ⟨ρ, hρ, hθρ⟩ := E8Pilot.exists_ringEquiv_of_forall_sl2 (fixSubfield σ).subtype
    (exists_ne_zero_ne_one_of_four_le hq) θ hfixU hfixL
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
