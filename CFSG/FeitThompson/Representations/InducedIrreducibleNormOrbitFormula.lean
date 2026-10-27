module

public import CFSG.FeitThompson.Representations.IrreducibleCharacterOrthogonality
public import CFSG.FeitThompson.Representations.FrobeniusReciprocityClassFunctions
public import CFSG.FeitThompson.Representations.NormalSubgroupInduction
public import CFSG.FeitThompson.Representations.DisjointAntirealBlocksOrthogonal

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open scoped ComplexConjugate

open NormalInduction (conjClassFun conjClassFun_apply)

variable {G : Type*} [Group G]

theorem mem_normalInduction_classFun_iff {f : G → ℂ} :
    f ∈ NormalInduction.classFun G ↔ f ∈ classFun G := by
  constructor
  · intro h
    refine mem_classFun.2 fun x y hxy => ?_
    obtain ⟨c, rfl⟩ := isConj_iff.1 hxy
    exact ((NormalInduction.mem_classFun.1 h) c x).symm
  · intro h
    exact NormalInduction.mem_classFun.2 fun x g => classFun.apply_conj h g x

theorem normalInduction_irrChars_eq_Irr : NormalInduction.irrChars G = Irr G := by
  ext χ
  constructor
  · intro h
    obtain ⟨V, _, _, ρ, hfd, hirr, rfl⟩ := NormalInduction.mem_irrChars_iff.1 h
    have : Module.Finite ℂ V := hfd
    refine mem_Irr.2 ⟨FDRep.of ρ, ?_, ?_⟩
    · rw [FDRep.of_ρ']; exact hirr
    · change Representation.character (FDRep.of ρ).ρ = _
      rw [FDRep.of_ρ']
  · intro h
    obtain ⟨V, hV, rfl⟩ := mem_Irr.1 h
    exact NormalInduction.mem_irrChars_iff.2 ⟨↑V.V, inferInstance, inferInstance, V.ρ,
      inferInstance, hV, rfl⟩

theorem indClassFun_mem_classFun [Fintype G] (H : Subgroup G) (f : H → ℂ) :
    indClassFun H f ∈ classFun G :=
  mem_classFun.2 fun x y hxy => by
    obtain ⟨c, rfl⟩ := isConj_iff.1 hxy
    exact (indClassFun_conj H f c x).symm

theorem normalInduction_indClassFun_eq [Fintype G] (H : Subgroup G) (f : H → ℂ) :
    NormalInduction.indClassFun H f = indClassFun H f := by
  funext g
  rw [NormalInduction.indClassFun_apply, indClassFun_eq_sum_extendByZero]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases h : x⁻¹ * g * x ∈ H
  · lift (x⁻¹ * g * x) to H using h with z hz
    rw [extendByZero_apply_coe, NormalInduction.extendByZero_apply_coe]
  · rw [extendByZero_of_notMem _ _ h, NormalInduction.extendByZero_of_notMem _ _ h]

theorem conjClassFun_mul (N : Subgroup G) [N.Normal] (g t : G) (f : N → ℂ) :
    conjClassFun N (g * t) f = conjClassFun N g (conjClassFun N t f) := by
  funext n
  simp only [conjClassFun_apply, mul_inv_rev, map_mul]
  rfl

@[simp] theorem conjClassFun_one (N : Subgroup G) [N.Normal] (f : N → ℂ) :
    conjClassFun N 1 f = f := by
  funext n
  simp [conjClassFun_apply]

theorem conjClassFun_mem_Irr (N : Subgroup G) [N.Normal] (t : G) {ψ : N → ℂ}
    (hψ : ψ ∈ Irr N) : conjClassFun N t ψ ∈ Irr N := by
  rw [← normalInduction_irrChars_eq_Irr] at hψ ⊢
  exact NormalInduction.conjClassFun_mem_irrChars N t hψ

theorem conjClassFun_eq_of_quotient_eq (N : Subgroup G) [N.Normal] {f : N → ℂ}
    (hf : f ∈ classFun N) {s t : G} (hst : (s : G ⧸ N) = (t : G ⧸ N)) :
    conjClassFun N s f = conjClassFun N t f := by
  obtain ⟨m, hm⟩ : ∃ m : N, t = s * (m : G) := ⟨⟨s⁻¹ * t, QuotientGroup.eq.1 hst⟩, by simp⟩
  subst hm
  funext n
  rw [conjClassFun_apply, conjClassFun_apply]
  have hcast : (MulAut.conjNormal (s * (m : G))⁻¹ n) = m⁻¹ * (MulAut.conjNormal s⁻¹ n) * m := by
    apply Subtype.ext
    push_cast [MulAut.conjNormal_apply]
    group
  rw [hcast]
  simpa using (classFun.apply_conj hf (MulAut.conjNormal s⁻¹ n) m⁻¹).symm

def inertiaGroup (N : Subgroup G) [N.Normal] (χ : N → ℂ) : Subgroup G where
  carrier := {g | conjClassFun N g χ = χ}
  one_mem' := conjClassFun_one N χ
  mul_mem' {a b} ha hb := by
    change conjClassFun N (a * b) χ = χ
    rw [conjClassFun_mul, show conjClassFun N b χ = χ from hb,
      show conjClassFun N a χ = χ from ha]
  inv_mem' {a} ha := by
    have h := congrArg (conjClassFun N a⁻¹) (show conjClassFun N a χ = χ from ha)
    rw [← conjClassFun_mul, inv_mul_cancel, conjClassFun_one] at h
    exact h.symm

theorem mem_inertiaGroup {N : Subgroup G} [N.Normal] {χ : N → ℂ} {g : G} :
    g ∈ inertiaGroup N χ ↔ conjClassFun N g χ = χ := Iff.rfl

theorem le_inertiaGroup (N : Subgroup G) [N.Normal] {χ : N → ℂ} (hχ : χ ∈ classFun N) :
    N ≤ inertiaGroup N χ := by
  intro n hn
  rw [mem_inertiaGroup]
  have h : ((n : G) : G ⧸ N) = ((1 : G) : G ⧸ N) := by
    rw [QuotientGroup.eq]; simpa using hn
  rw [conjClassFun_eq_of_quotient_eq N hχ h, conjClassFun_one]

def conjCosets (N : Subgroup G) [N.Normal] (ψ χ : N → ℂ) : Set (G ⧸ N) :=
  {q | ∃ t : G, (t : G ⧸ N) = q ∧ conjClassFun N t ψ = χ}

theorem mem_conjCosets_mk {N : Subgroup G} [N.Normal] {ψ χ : N → ℂ} (hψ : ψ ∈ classFun N)
    {t : G} : ((t : G ⧸ N)) ∈ conjCosets N ψ χ ↔ conjClassFun N t ψ = χ := by
  refine ⟨fun ⟨s, hs, hcs⟩ => ?_, fun h => ⟨t, rfl, h⟩⟩
  rwa [conjClassFun_eq_of_quotient_eq N hψ (hs : (s : G ⧸ N) = (t : G ⧸ N))] at hcs

theorem conjCosets_eq_empty {N : Subgroup G} [N.Normal] {ψ χ : N → ℂ}
    (h : ∀ t : G, conjClassFun N t ψ ≠ χ) : conjCosets N ψ χ = ∅ := by
  ext q
  simp only [conjCosets, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists]
  exact fun t ht => h t ht.2

theorem conjCosets_self_eq_coe_map (N : Subgroup G) [N.Normal] (ψ : N → ℂ) :
    conjCosets N ψ ψ = ((inertiaGroup N ψ).map (QuotientGroup.mk' N) : Set (G ⧸ N)) := by
  rw [Subgroup.coe_map]
  ext q
  exact ⟨fun ⟨t, ht, hct⟩ => ⟨t, hct, ht⟩, fun ⟨t, ht, hq⟩ => ⟨t, hq, ht⟩⟩

theorem card_conjCosets_self (N : Subgroup G) [N.Normal] (ψ : N → ℂ) :
    Nat.card (conjCosets N ψ ψ) = N.relIndex (inertiaGroup N ψ) := by
  rw [conjCosets_self_eq_coe_map, SetLike.coe_sort_coe,
    ← Subgroup.relIndex_ker (inertiaGroup N ψ) (QuotientGroup.mk' N), QuotientGroup.ker_mk']

theorem card_conjCosets_eq_card_filter [Finite G] (N : Subgroup G) [N.Normal] {ψ χ : N → ℂ}
    (hψ : ψ ∈ classFun N) {T : Finset G}
    (hT : Subgroup.IsComplement (T : Set G) (N : Set G))
    [DecidablePred fun t : G => conjClassFun N t ψ = χ] :
    Nat.card (conjCosets N ψ χ) = (T.filter fun t => conjClassFun N t ψ = χ).card := by
  set P : G → Prop := fun t => conjClassFun N t ψ = χ with hP
  set e := hT.leftQuotientEquiv with he
  have hmk : ∀ q : G ⧸ N, ((e q : G) : G ⧸ N) = q := fun q =>
    hT.quotientGroupMk_leftQuotientEquiv q
  have key : ∀ q : G ⧸ N, q ∈ conjCosets N ψ χ ↔ P (e q : G) := by
    intro q
    conv_lhs => rw [← hmk q]
    exact mem_conjCosets_mk hψ
  have E1 : ↥(conjCosets N ψ χ) ≃ {q : G ⧸ N // P (e q : G)} := Equiv.subtypeEquivRight key
  have E2 : {q : G ⧸ N // P (e q : G)} ≃ {t : ↑(T : Set G) // P (t : G)} :=
    Equiv.subtypeEquiv e fun q => Iff.rfl
  have E3 : {t : ↑(T : Set G) // P (t : G)} ≃ {x : G // x ∈ (T : Set G) ∧ P x} :=
    Equiv.subtypeSubtypeEquivSubtypeInter _ _
  classical
  have : Fintype G := Fintype.ofFinite G
  rw [Nat.card_eq_of_bijective _ (E1.trans (E2.trans E3)).bijective, Nat.card_eq_fintype_card,
    Fintype.card_subtype]
  congr 1
  ext x
  simp [hP]

theorem resClassFun_indClassFun_eq_sum [Fintype G] (N : Subgroup G) [N.Normal] {ψ : N → ℂ}
    (hψ : ψ ∈ classFun N) {T : Finset G}
    (hT : Subgroup.IsComplement (T : Set G) (N : Set G)) :
    resClassFun N (indClassFun N ψ) = ∑ t ∈ T, conjClassFun N t ψ := by
  funext n
  rw [resClassFun_apply, ← normalInduction_indClassFun_eq,
    NormalInduction.indClassFun_apply_of_mem N (mem_normalInduction_classFun_iff.2 hψ) hT n]
  simp [Finset.sum_apply]

theorem cfInner_indClassFun_indClassFun [Fintype G] (N : Subgroup G) [N.Normal]
    {χ ψ : N → ℂ} (hχ : χ ∈ Irr N) (hψ : ψ ∈ Irr N) :
    cfInner (indClassFun N χ) (indClassFun N ψ) = (Nat.card (conjCosets N ψ χ) : ℂ) := by
  classical
  obtain ⟨S, hS, -⟩ := N.exists_isComplement_left 1
  set T : Finset G := S.toFinset with hTdef
  have hT : Subgroup.IsComplement (T : Set G) (N : Set G) := by rwa [hTdef, Set.coe_toFinset]
  rw [cfInner_indClassFun _ _ (indClassFun_mem_classFun N ψ),
    resClassFun_indClassFun_eq_sum N (Irr_subset_classFun hψ) hT, cfInner_sum_right,
    card_conjCosets_eq_card_filter N (Irr_subset_classFun hψ) hT]
  rw [Finset.sum_congr rfl (g := fun t => if conjClassFun N t ψ = χ then (1 : ℂ) else 0)
    fun t _ => ?_]
  · rw [Finset.sum_boole]
  · rw [cfInner_eq_ite_of_mem_Irr hχ (conjClassFun_mem_Irr N t hψ)]
    simp [eq_comm]

theorem cfInner_indClassFun_indClassFun_eq_zero [Fintype G] (N : Subgroup G) [N.Normal]
    {χ ψ : N → ℂ} (hχ : χ ∈ Irr N) (hψ : ψ ∈ Irr N)
    (h : ∀ t : G, conjClassFun N t ψ ≠ χ) :
    cfInner (indClassFun N χ) (indClassFun N ψ) = 0 := by
  rw [cfInner_indClassFun_indClassFun N hχ hψ, conjCosets_eq_empty h]
  simp

theorem cfInner_self_indClassFun [Fintype G] (N : Subgroup G) [N.Normal] {χ : N → ℂ}
    (hχ : χ ∈ Irr N) :
    cfInner (indClassFun N χ) (indClassFun N χ) = (N.relIndex (inertiaGroup N χ) : ℂ) := by
  rw [cfInner_indClassFun_indClassFun N hχ hχ, card_conjCosets_self N χ]

end CFSG.FeitThompson
