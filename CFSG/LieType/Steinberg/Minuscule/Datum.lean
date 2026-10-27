module

public import CFSG.LieType.Steinberg.Minuscule.RankOne
public import CFSG.LieType.Steinberg.Minuscule.Unipotent
public import CFSG.LieType.Steinberg.Statement
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116

public noncomputable section

namespace CFSG.LieType.Steinberg.Minuscule

open CFSG.Blueprint.Chevalley CFSG.LieType.RootSystem CFSG.LieType.CurtisTits
  CFSG.LieType.Universal
open scoped commutatorElement

variable {τ : Tag}

theorem roots_eq (hA : TauCeti.IsFiniteType τ.cartan) :
    CFSG.LieType.RootSystem.roots hA ∅ = {γ | IsRoot τ γ} := by
  ext γ
  constructor
  · rintro (⟨w, i, rfl⟩ | ⟨w, i, hi, -⟩)
    · obtain ⟨ω, rfl⟩ := (coxeterMatrix hA).toCoxeterSystem.wordProd_surjective w
      induction ω with
      | nil => simpa using IsRoot.basis i
      | cons j ω ih =>
        rw [CoxeterSystem.wordProd_cons, weylAction_mul_apply, weylAction_simple,
          reflection_apply]
        exact IsRoot.reflect j ih
    · exact absurd hi (Set.notMem_empty i)
  · intro h
    induction h with
    | basis j => exact Or.inl ⟨1, j, by simp⟩
    | @reflect i v _ ih =>
      rcases ih with ⟨w, j, hw⟩ | ⟨w, j, hj, -⟩
      · refine Or.inl ⟨(coxeterMatrix hA).toCoxeterSystem.simple i * w, j, ?_⟩
        rw [weylAction_mul_apply, ← hw, weylAction_simple, reflection_apply]
        rfl
      · exact absurd hj (Set.notMem_empty j)

theorem weylAction_simple_apply (hA : TauCeti.IsFiniteType τ.cartan) (i : Fin τ.rank)
    (γ : Fin τ.rank → ℤ) :
    weylAction hA ((coxeterMatrix hA).toCoxeterSystem.simple i) γ = reflect τ i γ := by
  rw [weylAction_simple, reflection_apply]
  rfl

theorem eq_single_of_support {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) {i : Fin τ.rank}
    (h : ∀ k, k ≠ i → γ k = 0) : γ = Pi.single i 1 ∨ γ = -Pi.single i 1 := by
  have e : γ = γ i • Pi.single i 1 := by
    ext k
    by_cases hk : k = i
    · subst hk; simp
    · simp [h k hk, Pi.single_eq_of_ne hk]
  rcases hγ.eq_one_or_neg_one_of_eq_smul e with h1 | h1
  · left; rw [e, h1, one_smul]
  · right; rw [e, h1, neg_one_smul]

theorem not_isRoot_two_smul (γ : Fin τ.rank → ℤ) : ¬ IsRoot τ (2 • γ) := by
  intro h
  have e : (2 • γ : Fin τ.rank → ℤ) = (2 : ℤ) • γ := by rw [two_nsmul, two_zsmul]
  rcases h.eq_one_or_neg_one_of_eq_smul e with h1 | h1 <;> omega

namespace MinData

namespace Valid

variable {D : MinData τ} (hV : D.Valid) (hA : TauCeti.IsFiniteType τ.cartan) (k : Type*)
  [Field k]

abbrev minDatum : UniversalRootDatum ↥(hV.minGroup k) where
  rank := τ.rank
  cartan := τ.cartan
  isFiniteType := hA
  divisible := ∅
  rootGroup := hV.rootGroup k

theorem minDatum_roots : (hV.minDatum hA k).roots = {γ | IsRoot τ γ} := roots_eq hA

theorem mem_minDatum_roots {γ : Fin τ.rank → ℤ} :
    γ ∈ (hV.minDatum hA k).roots ↔ IsRoot τ γ := by
  rw [minDatum_roots]
  rfl

include hV in
theorem nm_mem_rankOne (i : Fin τ.rank) : hV.nm k i ∈ rankOne (hV.rootGroup k) i := by
  refine mul_mem (mul_mem ?_ ?_) ?_
  · exact Subgroup.mem_sup_left (hV.xm_mem_rootGroup k _ _)
  · exact Subgroup.mem_sup_right (hV.xm_mem_rootGroup k _ _)
  · exact Subgroup.mem_sup_left (hV.xm_mem_rootGroup k _ _)

include hV in
theorem nt_mem_rankOne (i : Fin τ.rank) (t : kˣ) : hV.nt k i t ∈ rankOne (hV.rootGroup k) i := by
  refine mul_mem (mul_mem ?_ ?_) ?_
  · exact Subgroup.mem_sup_left (hV.xm_mem_rootGroup k _ _)
  · exact Subgroup.mem_sup_right (hV.xm_mem_rootGroup k _ _)
  · exact Subgroup.mem_sup_left (hV.xm_mem_rootGroup k _ _)

include hV in
theorem torus_le_rankOne (i : Fin τ.rank) : hV.torus k i ≤ rankOne (hV.rootGroup k) i := by
  rintro _ ⟨t, rfl⟩
  exact mul_mem (hV.nt_mem_rankOne k i t) (inv_mem (hV.nt_mem_rankOne k i 1))

include hV in
theorem nm_braidWord (i j : Fin τ.rank) :
    ((CoxeterSystem.braidWord (coxeterMatrix hA) i j).map (hV.nm k)).prod =
      ((CoxeterSystem.braidWord (coxeterMatrix hA) j i).map (hV.nm k)).prod := by
  rcases eq_or_ne i j with rfl | hij
  · rfl
  simp only [CoxeterSystem.braidWord, coxeterMatrix, TauCeti.coxeterMatrixOfCartanMatrix_apply]
  by_cases h0 : τ.cartan i j = 0
  · have h0' : τ.cartan j i = 0 := (hA.apply_eq_zero_iff).1 h0
    rw [h0, h0', zero_mul, TauCeti.coxeterOrder_zero]
    simp [CoxeterSystem.alternatingWord, hV.nm_comm k hij h0]
  · have h1 := hV.cartan_mul_cartan hij h0
    have h1' : τ.cartan j i * τ.cartan i j = 1 := by rw [mul_comm]; exact h1
    rw [h1, h1', TauCeti.coxeterOrder_one]
    simp only [CoxeterSystem.alternatingWord, List.concat_eq_append, List.nil_append,
      List.cons_append, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [← mul_assoc, ← mul_assoc]
    exact (hV.nm_braid k hij h0).symm

theorem minDatum_isCTGroupDatum :
    IsCTGroupDatum (coxeterMatrix (hV.minDatum hA k).isFiniteType).toCoxeterSystem
      (weylAction (hV.minDatum hA k).isFiniteType) (hV.minDatum hA k).roots
      (hV.minDatum hA k).rootGroup (hV.nm k) (hV.torus k) where
  n_mem i := hV.nm_mem_rankOne k i
  conj_mem i γ hγ x hx := by
    obtain ⟨c, rfl⟩ := (hV.mem_rootGroup k).1 hx
    obtain ⟨σ, -, h⟩ := hV.nm_conj_xm k ((hV.mem_minDatum_roots hA k).1 hγ) i
    rw [h]
    change _ ∈ hV.rootGroup k _
    rw [weylAction_simple_apply hA]
    exact hV.xm_mem_rootGroup k _ _
  braid i j := hV.nm_braidWord hA k i j
  H_le i := hV.torus_le_rankOne k i
  sq_mem i := by
    rw [hV.nm_sq]
    exact hV.hm_mem_torus k i _
  H_conj_mem l γ hγ h hh x hx := by
    obtain ⟨t, rfl⟩ := (hV.mem_torus k).1 hh
    obtain ⟨c, rfl⟩ := (hV.mem_rootGroup k).1 hx
    rw [hV.hm_conj_xm k ((hV.mem_minDatum_roots hA k).1 hγ)]
    exact hV.xm_mem_rootGroup k _ _
  conj_H_mem j l h hh := by
    obtain ⟨t, rfl⟩ := (hV.mem_torus k).1 hh
    rw [hV.nm_conj_hm]
    exact mul_mem (Subgroup.mem_sup_right (hV.hm_mem_torus k l t))
      (Subgroup.mem_sup_left (hV.hm_mem_torus k j _))
  le_rankOne i γ hγ hsupp := by
    rcases eq_single_of_support ((hV.mem_minDatum_roots hA k).1 hγ) hsupp with rfl | rfl
    · exact le_sup_left
    · exact le_sup_right
  iSup_eq_top := by
    rw [minDatum_roots]
    exact hV.iSup_rootGroup k

theorem setOf_pos_eq :
    {γ | γ ∈ (hV.minDatum hA k).roots ∧ 0 < ht γ} = {γ | IsRoot τ γ ∧ 0 < ht γ} := by
  ext γ
  exact and_congr_left' (hV.mem_minDatum_roots hA k)

theorem setOf_neg_eq :
    {γ | γ ∈ (hV.minDatum hA k).roots ∧ ht γ < 0} = {γ | IsRoot τ γ ∧ ht γ < 0} := by
  ext γ
  exact and_congr_left' (hV.mem_minDatum_roots hA k)

theorem rootGroup_ne_bot {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) : hV.rootGroup k γ ≠ ⊥ := by
  intro h
  have h1 := hV.xm_mem_rootGroup k γ 1
  rw [h, Subgroup.mem_bot, ← hV.xm_zero k γ] at h1
  exact one_ne_zero (hV.xm_injective k hγ h1)

theorem commutator_mem_openCone {γ δ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (hδ : IsRoot τ δ)
    (hlin : LinIndepPair γ δ) {x y : hV.minGroup k} (hx : x ∈ hV.rootGroup k γ)
    (hy : y ∈ hV.rootGroup k δ) :
    ⁅x, y⁆ ∈ ⨆ ε ∈ openCone (hV.minDatum hA k).roots γ δ, (hV.minDatum hA k).rootGroup ε := by
  have hne : γ + δ ≠ 0 := fun h => by
    have := (hlin 1 1 (by rw [one_smul, one_smul, h])).1
    exact one_ne_zero this
  obtain ⟨c, rfl⟩ := (hV.mem_rootGroup k).1 hx
  obtain ⟨d, rfl⟩ := (hV.mem_rootGroup k).1 hy
  obtain ⟨hroot, hcomm⟩ := hV.commutator_xm k hγ hδ hne
  by_cases hr : IsRoot τ (γ + δ)
  · obtain ⟨σ, -, h⟩ := hroot hr
    rw [h]
    have hcone : γ + δ ∈ openCone (hV.minDatum hA k).roots γ δ :=
      ⟨(hV.mem_minDatum_roots hA k).2 hr, 1, 1, one_pos, one_pos, by rw [one_smul, one_smul]⟩
    exact Subgroup.mem_iSup_of_mem (γ + δ)
      (Subgroup.mem_iSup_of_mem hcone (hV.xm_mem_rootGroup k _ _))
  · rw [hcomm hr]
    exact one_mem _

theorem minDatum_steinbergExtras (hpd : (τ.cartan.map (Int.cast : ℤ → ℚ)).PosDef) :
    SteinbergExtras (hV.minDatum hA k) (hV.nm k) (hV.torus k) where
  ne_bot γ hγ := hV.rootGroup_ne_bot k ((hV.mem_minDatum_roots hA k).1 hγ)
  two_smul_le γ _ h2 := absurd ((hV.mem_minDatum_roots hA k).1 h2) (not_isRoot_two_smul γ)
  commutator_mem γ hγ δ hδ hlin x hx y hy :=
    hV.commutator_mem_openCone hA k ((hV.mem_minDatum_roots hA k).1 hγ)
      ((hV.mem_minDatum_roots hA k).1 hδ) hlin hx hy
  prodInjective_pos L hnd hmem hsort :=
    hV.prodInjective hpd 1 L hnd
      (fun γ hγ => ⟨(hV.mem_minDatum_roots hA k).1 ((hmem γ).1 hγ).1, by
        rw [one_mul]; exact ((hmem γ).1 hγ).2.1⟩)
      (hsort.imp fun h => by rwa [one_mul, one_mul])
  prodInjective_neg L hnd hmem hsort :=
    hV.prodInjective hpd (-1) L hnd
      (fun γ hγ => ⟨(hV.mem_minDatum_roots hA k).1 ((hmem γ).1 hγ).1, by
        have := ((hmem γ).1 hγ).2.1; linarith⟩)
      (hsort.imp fun h => by linarith)
  posPart_inf_negPart := by
    rw [setOf_pos_eq, setOf_neg_eq]
    exact hV.posPart_inf_negPart k
  rankOne_bruhat i g hg := hV.bruhat k i hg
  eq_one_of_mem_normalizer i u hu hn := hV.eq_one_of_mem_normalizer k i hu hn
  torus_commute i j h hh h' hh' := hV.torus_commute k i j hh hh'
  torus_iSupIndep := hV.torus_iSupIndep k
  torus_inf_posPart := by
    rw [setOf_pos_eq]
    exact hV.torus_inf_posPart k

theorem minDatum_isParametrization (Φ : Steinberg.RootSystem (Fin τ.rank))
    (hΦ : Φ.roots = {γ | IsRoot τ γ}) :
    IsParametrization (Φ := Φ) (hV.minDatum hA k).rootGroup (hV.xm k) := by
  intro γ hγ
  rw [hΦ] at hγ
  exact ⟨fun g => hV.mem_rootGroup k, fun c d => hV.xm_add k γ c d, hV.xm_injective k hγ⟩

open _root_.Classical in
@[expose] def commSign (α β : Fin τ.rank → ℤ) : ℤ :=
  if h : ∃ N : ℤ, (N = 1 ∨ N = -1) ∧
      ∀ c d : k, ⁅hV.xm k α c, hV.xm k β d⁆ = hV.xm k (α + β) (N * c * d) then h.choose
  else 1

theorem commSign_eq_one_or (α β : Fin τ.rank → ℤ) :
    hV.commSign k α β = 1 ∨ hV.commSign k α β = -1 := by
  classical
  rw [commSign]
  split_ifs with h
  · exact h.choose_spec.1
  · exact Or.inl rfl

theorem commutator_xm_commSign {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hβ : IsRoot τ β)
    (hne : α + β ≠ 0) (hr : IsRoot τ (α + β)) (c d : k) :
    ⁅hV.xm k α c, hV.xm k β d⁆ = hV.xm k (α + β) (hV.commSign k α β * c * d) := by
  classical
  have h : ∃ N : ℤ, (N = 1 ∨ N = -1) ∧
      ∀ c d : k, ⁅hV.xm k α c, hV.xm k β d⁆ = hV.xm k (α + β) (N * c * d) := by
    obtain ⟨σ, hσ, hc⟩ := (hV.commutator_xm k hα hβ hne).1 hr
    rcases hσ with rfl | rfl
    · exact ⟨1, Or.inl rfl, fun c d => by rw [hc, Int.cast_one]⟩
    · exact ⟨-1, Or.inr rfl, fun c d => by rw [hc, Int.cast_neg, Int.cast_one]⟩
  rw [commSign, dite_eq_left h]
  exact h.choose_spec.2 c d

theorem eq_singleton_of_nodup {α : Type*} {l : List α} {q : α} (hl : l.Nodup)
    (h : ∀ p, p ∈ l ↔ p = q) : l = [q] :=
  List.perm_singleton.1 ((List.perm_ext_iff_of_nodup hl (List.nodup_singleton q)).2
    fun p => by rw [h, List.mem_singleton])

theorem minDatum_commutatorFormula (hpd : (τ.cartan.map (Int.cast : ℤ → ℚ)).PosDef)
    (Φ : Steinberg.RootSystem (Fin τ.rank)) (hΦ : Φ.roots = {γ | IsRoot τ γ})
    (O : CommOrder Φ) :
    ∃ C : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ) → ℕ × ℕ → ℤ,
      (∀ α ∈ Φ.roots, ∀ β ∈ Φ.roots, ∀ p ∈ expPairs Φ α β,
        (C α β p).natAbs ∈ ({1, 2, 3} : Set ℕ)) ∧ CommutatorFormula (hV.xm k) O C := by
  refine ⟨fun α β _ => hV.commSign k α β, fun α _ β _ p _ => ?_, fun α hα β hβ hne c d => ?_⟩
  · rcases hV.commSign_eq_one_or k α β with h | h <;> simp [h]
  have hα₀ := hα
  have hβ₀ := hβ
  rw [hΦ] at hα hβ
  have hexp : ∀ p, p ∈ expPairs Φ α β ↔ IsRoot τ (α + β) ∧ p = (1, 1) := by
    intro p
    simp only [expPairs, Set.mem_ofPred_eq, hΦ]
    constructor
    · rintro ⟨h1, h2, h3⟩
      obtain ⟨e1, e2⟩ := eq_one_of_isRoot_nsmul_add_nsmul hpd hα hβ hne h1 h2 h3
      refine ⟨?_, Prod.ext e1 e2⟩
      rwa [e1, e2, one_smul, one_smul] at h3
    · rintro ⟨hr, rfl⟩
      exact ⟨one_pos, one_pos, by rwa [one_smul, one_smul]⟩
  by_cases hr : IsRoot τ (α + β)
  · have hl : O.list α β = [(1, 1)] := eq_singleton_of_nodup (O.nodup α β) fun p => by
      rw [O.mem_iff α hα₀ β hβ₀ hne, hexp]
      exact and_iff_right hr
    rw [hl, List.map_singleton, List.prod_singleton, one_smul, one_smul, pow_one, pow_one,
      hV.commutator_xm_commSign k hα hβ hne hr]
  · have hl : O.list α β = [] := List.eq_nil_iff_forall_not_mem.2 fun p hp => by
      rw [O.mem_iff α hα₀ β hβ₀ hne, hexp] at hp
      exact hr hp.1
    rw [hl, List.map_nil, List.prod_nil, ((hV.commutator_xm k hα hβ hne).2 hr) c d]

end Valid

end MinData

theorem isFiniteType_cartan_E6 : TauCeti.IsFiniteType (Tag.cartan .E6) := by
  rw [cartan_E6, ← TauCeti.DynkinType.cartanMatrix_E6]
  exact TauCeti.DynkinType.isFiniteType_cartanMatrix_E6

theorem isFiniteType_cartan_E7 : TauCeti.IsFiniteType (Tag.cartan .E7) := by
  rw [cartan_E7, ← TauCeti.DynkinType.cartanMatrix_E7]
  exact TauCeti.DynkinType.isFiniteType_cartanMatrix_E7

variable (k : Type*) [Field k]

abbrev e6Datum : UniversalRootDatum ↥(e6Data_valid.minGroup k) :=
  e6Data_valid.minDatum isFiniteType_cartan_E6 k

abbrev e7Datum : UniversalRootDatum ↥(e7Data_valid.minGroup k) :=
  e7Data_valid.minDatum isFiniteType_cartan_E7 k

theorem e6Datum_isCTGroupDatum :
    IsCTGroupDatum (coxeterMatrix (e6Datum k).isFiniteType).toCoxeterSystem
      (weylAction (e6Datum k).isFiniteType) (e6Datum k).roots (e6Datum k).rootGroup
      (e6Data_valid.nm k) (e6Data_valid.torus k) :=
  e6Data_valid.minDatum_isCTGroupDatum isFiniteType_cartan_E6 k

theorem e7Datum_isCTGroupDatum :
    IsCTGroupDatum (coxeterMatrix (e7Datum k).isFiniteType).toCoxeterSystem
      (weylAction (e7Datum k).isFiniteType) (e7Datum k).roots (e7Datum k).rootGroup
      (e7Data_valid.nm k) (e7Data_valid.torus k) :=
  e7Data_valid.minDatum_isCTGroupDatum isFiniteType_cartan_E7 k

theorem e6Datum_steinbergExtras :
    SteinbergExtras (e6Datum k) (e6Data_valid.nm k) (e6Data_valid.torus k) :=
  e6Data_valid.minDatum_steinbergExtras isFiniteType_cartan_E6 k posDef_cartan_E6

theorem e7Datum_steinbergExtras :
    SteinbergExtras (e7Datum k) (e7Data_valid.nm k) (e7Data_valid.torus k) :=
  e7Data_valid.minDatum_steinbergExtras isFiniteType_cartan_E7 k posDef_cartan_E7

theorem e6Datum_isParametrization (Φ : Steinberg.RootSystem (Fin (Tag.rank .E6)))
    (hΦ : Φ.roots = {γ | IsRoot .E6 γ}) :
    IsParametrization (Φ := Φ) (e6Datum k).rootGroup (e6Data_valid.xm k) :=
  e6Data_valid.minDatum_isParametrization isFiniteType_cartan_E6 k Φ hΦ

theorem e7Datum_isParametrization (Φ : Steinberg.RootSystem (Fin (Tag.rank .E7)))
    (hΦ : Φ.roots = {γ | IsRoot .E7 γ}) :
    IsParametrization (Φ := Φ) (e7Datum k).rootGroup (e7Data_valid.xm k) :=
  e7Data_valid.minDatum_isParametrization isFiniteType_cartan_E7 k Φ hΦ

theorem e6Datum_commutatorFormula (Φ : Steinberg.RootSystem (Fin (Tag.rank .E6)))
    (hΦ : Φ.roots = {γ | IsRoot .E6 γ}) (O : CommOrder Φ) :
    ∃ C : (Fin (Tag.rank .E6) → ℤ) → (Fin (Tag.rank .E6) → ℤ) → ℕ × ℕ → ℤ,
      (∀ α ∈ Φ.roots, ∀ β ∈ Φ.roots, ∀ p ∈ expPairs Φ α β,
        (C α β p).natAbs ∈ ({1, 2, 3} : Set ℕ)) ∧ CommutatorFormula (e6Data_valid.xm k) O C :=
  e6Data_valid.minDatum_commutatorFormula k posDef_cartan_E6 Φ hΦ O

theorem e7Datum_commutatorFormula (Φ : Steinberg.RootSystem (Fin (Tag.rank .E7)))
    (hΦ : Φ.roots = {γ | IsRoot .E7 γ}) (O : CommOrder Φ) :
    ∃ C : (Fin (Tag.rank .E7) → ℤ) → (Fin (Tag.rank .E7) → ℤ) → ℕ × ℕ → ℤ,
      (∀ α ∈ Φ.roots, ∀ β ∈ Φ.roots, ∀ p ∈ expPairs Φ α β,
        (C α β p).natAbs ∈ ({1, 2, 3} : Set ℕ)) ∧ CommutatorFormula (e7Data_valid.xm k) O C :=
  e7Data_valid.minDatum_commutatorFormula k posDef_cartan_E7 Φ hΦ O

end CFSG.LieType.Steinberg.Minuscule
