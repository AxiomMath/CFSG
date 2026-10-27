module

public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.ExcDim

public section

open scoped commutatorElement

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.RootOps CFSG.SignalizerFunctorTheorem.NonLocalExc
  CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit CFSG.LieType.Steinberg.Adjoint

set_option linter.unusedSectionVars false

variable {τ : Tag} {K : Type} [Field K]

section Facts

structure HeisGenFacts (τ : Tag) (α0 : Fin τ.rank → ℤ) (S : Finset (Fin τ.rank → ℤ)) : Prop where
  isRoot_α0 : IsRoot τ α0
  isRoot_of_mem : ∀ β ∈ S, IsRoot τ β
  isRoot_sub : ∀ β ∈ S, IsRoot τ (α0 - β)
  pos : ∀ β ∈ S, 0 < height β
  two_height_lt : ∀ β ∈ S, 2 * height β < height α0
  nil_SS : ∀ β ∈ S, ∀ β' ∈ S, β ≠ β' → ∀ p ∈ commCandidates,
    ¬ IsRoot τ (p.1 • β + p.2 • β')
  nil_TT : ∀ β ∈ S, ∀ β' ∈ S, β ≠ β' → ∀ p ∈ commCandidates,
    ¬ IsRoot τ (p.1 • (α0 - β) + p.2 • (α0 - β'))
  nil_α0S : ∀ β ∈ S, ∀ p ∈ commCandidates, ¬ IsRoot τ (p.1 • α0 + p.2 • β)
  nil_α0T : ∀ β ∈ S, ∀ p ∈ commCandidates, ¬ IsRoot τ (p.1 • α0 + p.2 • (α0 - β))
  nil_TS : ∀ β ∈ S, ∀ β' ∈ S, β ≠ β' → ∀ p ∈ commCandidates,
    ¬ IsRoot τ (p.1 • (α0 - β) + p.2 • β')
  main : ∀ β ∈ S, ∀ p ∈ commCandidates, IsRoot τ (p.1 • (α0 - β) + p.2 • β) ↔ p = (1, 1)
  iform_ne : iform α0 α0 ≠ 0
  iform_pair : ∀ β ∈ S, 2 * iform α0 β / iform α0 α0 = 1

@[expose] def GenCodeFacts (τ : Tag) (a0 : ℕ) (Sc : List ℕ) : Prop :=
  isRootB τ (decodeVec a0) = true ∧
  (∀ c ∈ Sc, isRootB τ (decodeVec c) = true ∧ isRootB τ (decodeVec a0 - decodeVec c) = true ∧
     0 < ∑ j, decodeVec (τ := τ) c j ∧
     2 * ∑ j, decodeVec (τ := τ) c j < ∑ j, decodeVec (τ := τ) a0 j) ∧
  (∀ c ∈ Sc, ∀ d ∈ Sc, c ≠ d → ∀ p ∈ commCandidates,
    isRootB τ (p.1 • decodeVec (τ := τ) c + p.2 • decodeVec d) = false) ∧
  (∀ c ∈ Sc, ∀ d ∈ Sc, c ≠ d → ∀ p ∈ commCandidates,
    isRootB τ (p.1 • (decodeVec (τ := τ) a0 - decodeVec c) +
      p.2 • (decodeVec a0 - decodeVec d)) = false) ∧
  (∀ c ∈ Sc, ∀ p ∈ commCandidates,
    isRootB τ (p.1 • decodeVec (τ := τ) a0 + p.2 • decodeVec c) = false ∧
    isRootB τ (p.1 • decodeVec (τ := τ) a0 + p.2 • (decodeVec a0 - decodeVec c)) = false) ∧
  (∀ c ∈ Sc, ∀ d ∈ Sc, c ≠ d → ∀ p ∈ commCandidates,
    isRootB τ (p.1 • (decodeVec (τ := τ) a0 - decodeVec c) + p.2 • decodeVec d) = false) ∧
  (∀ c ∈ Sc, ∀ p ∈ commCandidates,
    isRootB τ (p.1 • (decodeVec (τ := τ) a0 - decodeVec c) + p.2 • decodeVec c) = true ↔
      p = (1, 1)) ∧
  iform (decodeVec (τ := τ) a0) (decodeVec a0) ≠ 0 ∧
  (∀ c ∈ Sc, 2 * iform (decodeVec (τ := τ) a0) (decodeVec c) /
    iform (decodeVec (τ := τ) a0) (decodeVec a0) = 1)

instance (τ : Tag) (a0 : ℕ) (Sc : List ℕ) : Decidable (GenCodeFacts τ a0 Sc) := by
  unfold GenCodeFacts
  infer_instance

theorem genCodeFacts_G2 : GenCodeFacts .G2 186 [137, 153] := by decide +kernel

theorem genCodeFacts_F4 :
    GenCodeFacts .F4 44218 [34953, 34969, 35481, 35225, 35497, 39321, 39577] := by
  decide +kernel

@[expose] def genS (τ : Tag) (Sc : List ℕ) : Finset (Fin τ.rank → ℤ) :=
  (Sc.map (decodeVec (τ := τ))).toFinset

theorem mem_genS {Sc : List ℕ} {β : Fin τ.rank → ℤ} :
    β ∈ genS τ Sc ↔ ∃ c ∈ Sc, decodeVec c = β := by
  simp [genS]

theorem HeisGenFacts.of_codeFacts {a0 : ℕ} {Sc : List ℕ} (h : GenCodeFacts τ a0 Sc) :
    HeisGenFacts τ (decodeVec a0) (genS τ Sc) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  have hne : ∀ {c d : ℕ}, decodeVec (τ := τ) c ≠ decodeVec d → c ≠ d := fun h hc => h (by rw [hc])
  refine ⟨(isRootB_iff).1 h1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h8, ?_⟩
  · intro β hβ
    obtain ⟨c, hc, rfl⟩ := mem_genS.1 hβ
    exact (isRootB_iff).1 (h2 c hc).1
  · intro β hβ
    obtain ⟨c, hc, rfl⟩ := mem_genS.1 hβ
    exact (isRootB_iff).1 (h2 c hc).2.1
  · intro β hβ
    obtain ⟨c, hc, rfl⟩ := mem_genS.1 hβ
    exact (h2 c hc).2.2.1
  · intro β hβ
    obtain ⟨c, hc, rfl⟩ := mem_genS.1 hβ
    exact (h2 c hc).2.2.2
  · intro β hβ β' hβ' hne' p hp
    obtain ⟨c, hc, rfl⟩ := mem_genS.1 hβ
    obtain ⟨d, hd, rfl⟩ := mem_genS.1 hβ'
    intro hr
    have := h3 c hc d hd (hne hne') p hp
    rw [(isRootB_iff).2 hr] at this
    exact absurd this (by simp)
  · intro β hβ β' hβ' hne' p hp
    obtain ⟨c, hc, rfl⟩ := mem_genS.1 hβ
    obtain ⟨d, hd, rfl⟩ := mem_genS.1 hβ'
    intro hr
    have := h4 c hc d hd (hne hne') p hp
    rw [(isRootB_iff).2 hr] at this
    exact absurd this (by simp)
  · intro β hβ p hp hr
    obtain ⟨c, hc, rfl⟩ := mem_genS.1 hβ
    have := (h5 c hc p hp).1
    rw [(isRootB_iff).2 hr] at this
    exact absurd this (by simp)
  · intro β hβ p hp hr
    obtain ⟨c, hc, rfl⟩ := mem_genS.1 hβ
    have := (h5 c hc p hp).2
    rw [(isRootB_iff).2 hr] at this
    exact absurd this (by simp)
  · intro β hβ β' hβ' hne' p hp hr
    obtain ⟨c, hc, rfl⟩ := mem_genS.1 hβ
    obtain ⟨d, hd, rfl⟩ := mem_genS.1 hβ'
    have := h6 c hc d hd (hne hne') p hp
    rw [(isRootB_iff).2 hr] at this
    exact absurd this (by simp)
  · intro β hβ p hp
    obtain ⟨c, hc, rfl⟩ := mem_genS.1 hβ
    rw [← isRootB_iff]
    exact h7 c hc p hp
  · intro β hβ
    obtain ⟨c, hc, rfl⟩ := mem_genS.1 hβ
    exact h9 c hc

end Facts

section Pinned

variable {S : Finset (Fin τ.rank → ℤ)} {α0 : Fin τ.rank → ℤ}

theorem commPairs_eq_nil {α β : Fin τ.rank → ℤ}
    (h : ∀ p ∈ commCandidates, ¬ IsRoot τ (p.1 • α + p.2 • β)) : commPairs τ α β = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro p hp
  rw [mem_commPairs] at hp
  exact h p hp.1 hp.2

theorem commPairs_eq_single {α β : Fin τ.rank → ℤ}
    (h : ∀ p ∈ commCandidates, IsRoot τ (p.1 • α + p.2 • β) ↔ p = (1, 1)) :
    commPairs τ α β = [(1, 1)] := by
  refine list_eq_singleton_of_forall_eq (fun p hp => ?_) (commPairs_nodup α β) ?_
  · rw [mem_commPairs] at hp
    exact (h p hp.1).1 hp.2
  · rw [mem_commPairs]
    refine ⟨by decide, (h (1, 1) (by decide)).2 rfl⟩

theorem pinnedA_comm_self (α : Fin τ.rank → ℤ) (c d : K) :
    pinnedA τ K α c * pinnedA τ K α d = pinnedA τ K α d * pinnedA τ K α c := by
  rw [← pinnedA_add, ← pinnedA_add, add_comm]

theorem pinnedA_comm_of_nil {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hβ : IsRoot τ β)
    (hne : α ≠ β) (hne' : α ≠ -β) (hnil : commPairs τ α β = []) (c d : K) :
    pinnedA τ K α c * pinnedA τ K β d = pinnedA τ K β d * pinnedA τ K α c := by
  obtain ⟨-, -, -, -, hF⟩ := root_commutator_formula.{0} τ hα hβ hne hne'
  have h := hF K c d
  rw [hnil] at h
  simp only [List.map_nil, List.prod_nil] at h
  rw [← pinnedX_neg, ← pinnedX_neg] at h
  refine pinnedA_ext ?_
  exact commutatorElement_eq_one_iff_mul_comm.1 (by rw [commutatorElement_def]; exact h)

theorem pinnedA_comm_single {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hβ : IsRoot τ β)
    (hne : α ≠ β) (hne' : α ≠ -β) (hone : commPairs τ α β = [(1, 1)]) (c d : K) :
    pinnedX τ K α c * pinnedX τ K β d * pinnedX τ K α (-c) * pinnedX τ K β (-d) =
      pinnedX τ K (α + β) ((commConst τ α β (1, 1) : K) * c * d) := by
  obtain ⟨-, -, -, -, hF⟩ := root_commutator_formula.{0} τ hα hβ hne hne'
  have h := hF K c d
  rw [hone] at h
  simpa using h

theorem ne_neg_of_pos {α β : Fin τ.rank → ℤ} (ha : 0 < height α) (hb : 0 < height β) :
    α ≠ -β := fun h => by
  have := congrArg height h
  rw [height_neg'] at this
  omega

end Pinned

section System

variable {S : Finset (Fin τ.rank → ℤ)} {α0 : Fin τ.rank → ℤ}

theorem HeisGenFacts.height_sub_pos (hF : HeisGenFacts τ α0 S) {β : Fin τ.rank → ℤ} (hβ : β ∈ S) :
    0 < height (α0 - β) := by
  have h1 := hF.pos β hβ
  have h2 := hF.two_height_lt β hβ
  rw [height_sub']
  omega

theorem HeisGenFacts.pos_α0 (hF : HeisGenFacts τ α0 S) {β : Fin τ.rank → ℤ} (hβ : β ∈ S) :
    0 < height α0 := by
  have h1 := hF.pos β hβ
  have h2 := hF.two_height_lt β hβ
  omega

theorem HeisGenFacts.ne_α0 (hF : HeisGenFacts τ α0 S) {β : Fin τ.rank → ℤ} (hβ : β ∈ S) :
    α0 ≠ β := fun h => by
  have h1 := hF.pos β hβ
  have h2 := hF.two_height_lt β hβ
  rw [h] at h2
  omega

theorem HeisGenFacts.ne_sub (hF : HeisGenFacts τ α0 S) {β : Fin τ.rank → ℤ} (hβ : β ∈ S) :
    α0 ≠ α0 - β := fun h => by
  have h1 := hF.pos β hβ
  have h2 := congrArg height h
  rw [height_sub'] at h2
  omega

theorem HeisGenFacts.sub_ne (hF : HeisGenFacts τ α0 S) {β β' : Fin τ.rank → ℤ} (hβ : β ∈ S)
    (hβ' : β' ∈ S) : α0 - β ≠ β' := fun h => by
  have h1 := hF.pos β hβ
  have h2 := hF.two_height_lt β hβ
  have h3 := hF.two_height_lt β' hβ'
  have h4 := congrArg height h
  rw [height_sub'] at h4
  omega

theorem exists_comm_ss_gen (hF : HeisGenFacts τ α0 S) {β : Fin τ.rank → ℤ} (hβ : β ∈ S) :
    commPairs τ (α0 - β) β = [(1, 1)] := by
  refine commPairs_eq_single (hF.main β hβ)

variable (hF : HeisGenFacts τ α0 S)
include hF

@[expose] noncomputable def heisSystemGen
    (hC : ∀ β ∈ S, ((commConst τ (α0 - β) β (1, 1) : ℤ) : K) ≠ 0) :
    HeisSystem ↥(adjointGroup τ K) K ↥S where
  xa s c := pinnedA τ K s.1 c
  xb s c := pinnedA τ K (α0 - s.1) c
  z c := pinnedA τ K α0 c
  ε s := -((commConst τ (α0 - s.1) s.1 (1, 1) : ℤ) : K)
  xa_add s c d := pinnedA_add s.1 c d
  xb_add s c d := pinnedA_add _ c d
  z_add c d := pinnedA_add _ c d
  z_injective := fun c d h => pinnedX_injective τ K _ (congrArg (fun x : ↥(adjointGroup τ K) =>
    (x : ModGL τ K)) h)
  ε_ne s := neg_ne_zero.2 (hC s.1 s.2)
  xa_comm s t c d := by
    by_cases hst : s = t
    · subst hst; exact pinnedA_comm_self _ c d
    · exact pinnedA_comm_of_nil (hF.isRoot_of_mem _ s.2) (hF.isRoot_of_mem _ t.2)
        (fun h => hst (Subtype.ext h)) (ne_neg_of_pos (hF.pos _ s.2) (hF.pos _ t.2))
        (commPairs_eq_nil (hF.nil_SS _ s.2 _ t.2 (fun h => hst (Subtype.ext h)))) c d
  xb_comm s t c d := by
    by_cases hst : s = t
    · subst hst; exact pinnedA_comm_self _ c d
    · have hne : s.1 ≠ t.1 := fun h => hst (Subtype.ext h)
      exact pinnedA_comm_of_nil (hF.isRoot_sub _ s.2) (hF.isRoot_sub _ t.2)
        (fun h => hne (sub_right_injective h))
        (ne_neg_of_pos (hF.height_sub_pos s.2) (hF.height_sub_pos t.2))
        (commPairs_eq_nil (hF.nil_TT _ s.2 _ t.2 hne)) c d
  z_comm_a c s d :=
    pinnedA_comm_of_nil hF.isRoot_α0 (hF.isRoot_of_mem _ s.2) (hF.ne_α0 s.2)
      (ne_neg_of_pos (hF.pos_α0 s.2) (hF.pos _ s.2)) (commPairs_eq_nil (hF.nil_α0S _ s.2)) c d
  z_comm_b c s d :=
    pinnedA_comm_of_nil hF.isRoot_α0 (hF.isRoot_sub _ s.2) (hF.ne_sub s.2)
      (ne_neg_of_pos (hF.pos_α0 s.2) (hF.height_sub_pos s.2))
      (commPairs_eq_nil (hF.nil_α0T _ s.2)) c d
  xab_comm s t hst c d :=
    pinnedA_comm_of_nil (hF.isRoot_sub _ s.2) (hF.isRoot_of_mem _ t.2) (hF.sub_ne s.2 t.2)
      (ne_neg_of_pos (hF.height_sub_pos s.2) (hF.pos _ t.2))
      (commPairs_eq_nil (hF.nil_TS _ s.2 _ t.2 (fun h => hst (Subtype.ext h)))) c d
  comm_ss s c d := by
    have hf := pinnedA_comm_single (K := K) (hF.isRoot_sub _ s.2) (hF.isRoot_of_mem _ s.2)
      (hF.sub_ne s.2 s.2) (ne_neg_of_pos (hF.height_sub_pos s.2) (hF.pos _ s.2))
      (exists_comm_ss_gen hF s.2) (-c) d
    simp only [sub_add_cancel] at hf
    rw [pinnedA_neg]
    refine pinnedA_ext ?_
    show ⁅pinnedX τ K (α0 - s.1) (-c), pinnedX τ K s.1 d⁆ = _
    rw [commutatorElement_def, pinnedX_neg, pinnedX_neg, hf]
    congr 1
    ring

end System

section Torus

variable {S : Finset (Fin τ.rank → ℤ)} {α0 : Fin τ.rank → ℤ} (hF : HeisGenFacts τ α0 S)
include hF

theorem torusA_conj_z_gen (c : Kˣ) (e : K) :
    torusA τ K α0 c * pinnedA τ K α0 e * (torusA τ K α0 c)⁻¹ =
      pinnedA τ K α0 (((c ^ 2 : Kˣ) : K) * e) := by
  refine pinnedA_ext ?_
  have h := rootTorusSL2_conj_pinnedX_of_isRoot (K := K) hF.isRoot_α0 hF.isRoot_α0 c e
  have hexp : c ^ (2 * iform α0 α0 / iform α0 α0) = c ^ 2 := by
    rw [Int.mul_ediv_cancel _ hF.iform_ne]; norm_num
  rw [hexp] at h
  exact h

theorem torusA_conj_xa_gen (c : Kˣ) {β : Fin τ.rank → ℤ} (hβ : β ∈ S) (d : K) :
    torusA τ K α0 c * pinnedA τ K β d * (torusA τ K α0 c)⁻¹ = pinnedA τ K β ((c : K) * d) := by
  refine pinnedA_ext ?_
  have h := rootTorusSL2_conj_pinnedX_of_isRoot (K := K) hF.isRoot_α0 (hF.isRoot_of_mem β hβ) c d
  rw [hF.iform_pair β hβ, zpow_one] at h
  exact h

theorem eq_zero_of_pinnedA_mem_center_gen (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) (c : K)
    (hc : pinnedA τ K α0 c ∈ Subgroup.center ↥(adjointGroup τ K)) : c = 0 := by
  let u : Kˣ := Units.mk0 2 h2
  have e := torusA_conj_z_gen hF u c
  have hcomm := Subgroup.mem_center_iff.1 hc (torusA τ K α0 u)
  rw [hcomm, mul_inv_cancel_right] at e
  have hinj := pinnedX_injective τ K α0
    (congrArg (fun x : ↥(adjointGroup τ K) => (x : ModGL τ K)) e)
  have hu : (((u ^ 2 : Kˣ)) : K) = 4 := by
    simp [u]
    norm_num
  rw [hu] at hinj
  have h3c : (3 : K) * c = 0 := by linear_combination (-1 : K) * hinj
  exact (mul_eq_zero.1 h3c).resolve_left h3

theorem torusA_conj_xaProd_gen (hC : ∀ β ∈ S, ((commConst τ (α0 - β) β (1, 1) : ℤ) : K) ≠ 0)
    [Fintype ↥S] [DecidableEq ↥S] (c : Kˣ) (u : ↥S → K) :
    ∃ u' : ↥S → K,
      torusA τ K α0 c * heisXaProd (heisSystemGen hF hC) (Multiplicative.ofAdd u) *
        (torusA τ K α0 c)⁻¹ = heisXaProd (heisSystemGen hF hC) (Multiplicative.ofAdd u') := by
  have hw : u = ∑ s, Pi.single s (u s) := (Finset.univ_sum_single u).symm
  rw [hw]
  refine Finset.sum_induction _ (fun x : ↥S → K => ∃ u' : ↥S → K,
    torusA τ K α0 c * heisXaProd (heisSystemGen hF hC) (Multiplicative.ofAdd x) *
      (torusA τ K α0 c)⁻¹ = heisXaProd (heisSystemGen hF hC) (Multiplicative.ofAdd u')) ?_ ?_ ?_
  · rintro x y ⟨x', hx⟩ ⟨y', hy⟩
    refine ⟨x' + y', ?_⟩
    rw [ofAdd_add, map_mul, ofAdd_add, map_mul, ← hx, ← hy]
    group
  · exact ⟨0, by simp⟩
  · intro s _
    refine ⟨Pi.single s ((c : K) * u s), ?_⟩
    rw [heisXaProd_single, heisXaProd_single]
    exact torusA_conj_xa_gen hF c s.2 (u s)

end Torus

section Main

theorem natCast_ne_zero_of_ne {p q : ℕ} [Fact p.Prime] [CharP K p] (hq : q.Prime) (h : p ≠ q) :
    (q : K) ≠ 0 := fun h0 =>
  h ((Nat.prime_dvd_prime_iff_eq Fact.out hq).1 ((CharP.cast_eq_zero_iff K p q).1 h0))

theorem commConst_cast_ne_zero_gen {S : Finset (Fin τ.rank → ℤ)} {α0 : Fin τ.rank → ℤ}
    (hF : HeisGenFacts τ α0 S) (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) {β : Fin τ.rank → ℤ}
    (hβ : β ∈ S) : ((commConst τ (α0 - β) β (1, 1) : ℤ) : K) ≠ 0 := by
  obtain ⟨-, -, -, hC, -⟩ := root_commutator_formula.{0} τ (hF.isRoot_sub β hβ)
    (hF.isRoot_of_mem β hβ) (hF.sub_ne hβ hβ)
    (ne_neg_of_pos (hF.height_sub_pos hβ) (hF.pos β hβ))
  have hmem : ((1 : ℕ), (1 : ℕ)) ∈ commPairs τ (α0 - β) β := by
    rw [exists_comm_ss_gen hF hβ]; simp
  obtain ⟨hl, hu⟩ := hC (1, 1) hmem
  have hcases : commConst τ (α0 - β) β (1, 1) = 1 ∨ commConst τ (α0 - β) β (1, 1) = -1 ∨
      commConst τ (α0 - β) β (1, 1) = 2 ∨ commConst τ (α0 - β) β (1, 1) = -2 ∨
      commConst τ (α0 - β) β (1, 1) = 3 ∨ commConst τ (α0 - β) β (1, 1) = -3 := by
    rcases abs_cases (commConst τ (α0 - β) β (1, 1)) with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
  rcases hcases with h | h | h | h | h | h <;> rw [h] <;> simp [h2, h3]

theorem two_pow_le_card_of_heisGen {S : Finset (Fin τ.rank → ℤ)} {α0 : Fin τ.rank → ℤ}
    (hF : HeisGenFacts τ α0 S)
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w * w = 1) [Finite K] {p : ℕ}
    [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2) (hp3 : p ≠ 3) {L : Subgroup (MulAut W)}
    (π : ↥L →* AdjointQuotient τ K) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center ↥L) (hZ : ¬ p ∣ Nat.card π.ker) :
    2 ^ (orderOf (2 : ZMod p) * ((Nat.card K - 1) / 2 * Nat.card K ^ S.card / (p - 1))) ≤
      Nat.card W := by
  classical
  have h2 : (2 : K) ≠ 0 := by
    have := natCast_ne_zero_of_ne (K := K) (p := p) Nat.prime_two hp2
    simpa using this
  have h3 : (3 : K) ≠ 0 := by
    have := natCast_ne_zero_of_ne (K := K) (p := p) Nat.prime_three hp3
    simpa using this
  have hC : ∀ β ∈ S, ((commConst τ (α0 - β) β (1, 1) : ℤ) : K) ≠ 0 := fun β hβ =>
    commConst_cast_ne_zero_gen hF h2 h3 hβ
  have key := two_pow_le_card_of_heisSystem hW hp2 π hπ hker hZ
    (heisSystemGen (K := K) hF hC) (QuotientGroup.mk' (Subgroup.center ↥(adjointGroup τ K)))
    (by rw [QuotientGroup.ker_mk'])
    (fun c hc => eq_zero_of_pinnedA_mem_center_gen hF h2 h3 c hc)
    ((QuotientGroup.mk' (Subgroup.center ↥(adjointGroup τ K))).comp (torusA τ K α0))
    (powMonoidHom 2)
    (fun s c => by
      show QuotientGroup.mk' _ (torusA τ K α0 s) * QuotientGroup.mk' _
        (pinnedA τ K α0 c) * (QuotientGroup.mk' _ (torusA τ K α0 s))⁻¹ = _
      rw [← map_inv, ← map_mul, ← map_mul]
      exact congrArg _ (torusA_conj_z_gen hF s c))
    (fun s u => by
      obtain ⟨u', hu'⟩ := torusA_conj_xaProd_gen hF hC s u
      refine ⟨u', ?_⟩
      show QuotientGroup.mk' _ (torusA τ K α0 s) * QuotientGroup.mk' _ _ *
        (QuotientGroup.mk' _ (torusA τ K α0 s))⁻¹ = _
      rw [← map_inv, ← map_mul, ← map_mul, hu'])
  rwa [card_range_powMonoidHom_two h2, Nat.card_fun, Nat.card_eq_fintype_card (α := ↥S),
    Fintype.card_coe] at key

theorem two_pow_le_card_of_adjointG2
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w * w = 1) [Finite K] {p : ℕ}
    [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2) (hp3 : p ≠ 3) {L : Subgroup (MulAut W)}
    (π : ↥L →* AdjointQuotient .G2 K) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center ↥L) (hZ : ¬ p ∣ Nat.card π.ker) :
    2 ^ (orderOf (2 : ZMod p) * ((Nat.card K - 1) / 2 * Nat.card K ^ 2 / (p - 1))) ≤
      Nat.card W := by
  have key := two_pow_le_card_of_heisGen (HeisGenFacts.of_codeFacts genCodeFacts_G2) hW hp2 hp3 π
    hπ hker hZ
  have hc : (genS .G2 [137, 153]).card = 2 := by decide +kernel
  rwa [hc] at key

end Main

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
