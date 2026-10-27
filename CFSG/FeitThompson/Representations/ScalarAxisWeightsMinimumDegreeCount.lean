module

public import CFSG.FeitThompson.Representations.ScalarAxisWeightsMinimumDegreeSupport

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Module SemidirectProduct

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open scoped ComplexOrder

theorem Finset.card_eq_natCard {α : Type*} (s : Finset α) : s.card = Nat.card {x // x ∈ s} := by
  rw [Nat.card_eq_fintype_card, Fintype.card_coe]

instance instIsMulCommutativeQuotientCommutator (G : Type*) [Group G] :
    IsMulCommutative (G ⧸ commutator G) :=
  Subgroup.Normal.quotient_commutative_iff_commutator_le.2 le_rfl

variable {p q : ℕ} [Fact p.Prime] {V U : Type*} [AddCommGroup V] [Module (ZMod p) V] [Group U]

namespace ScalarCoordinateSystem

variable (S : ScalarCoordinateSystem p q V U) [Finite U]

open scoped Classical in
noncomputable def axisBaseFinset (i : Fin q) : Finset (S.base → ℂ) :=
  {lam ∈ irrFinset S.base | ∃ χ : Multiplicative V →* ℂˣ, S.IsAxisChar i χ ∧ S.baseChar χ = lam}

theorem mem_axisBaseFinset {i : Fin q} {lam : S.base → ℂ} :
    lam ∈ S.axisBaseFinset i ↔ ∃ χ : Multiplicative V →* ℂˣ,
      S.IsAxisChar i χ ∧ S.baseChar χ = lam := by
  classical
  rw [axisBaseFinset, Finset.mem_filter]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  obtain ⟨χ, -, rfl⟩ := h
  exact mem_irrFinset.2 (S.baseChar_mem_Irr χ)

theorem baseChar_mem_axisBaseFinset {i : Fin q} {χ : Multiplicative V →* ℂˣ}
    (h : S.IsAxisChar i χ) : S.baseChar χ ∈ S.axisBaseFinset i :=
  (S.mem_axisBaseFinset).2 ⟨χ, h, rfl⟩

theorem axisBaseFinset_subset_Irr (i : Fin q) : ↑(S.axisBaseFinset i) ⊆ Irr S.base := by
  intro lam hlam
  obtain ⟨χ, -, rfl⟩ := (S.mem_axisBaseFinset).1 hlam
  exact S.baseChar_mem_Irr χ

theorem card_axisBaseFinset (i : Fin q) : (S.axisBaseFinset i).card = p - 1 := by
  rw [Finset.card_eq_natCard, ← S.natCard_setOf_isAxisChar i]
  refine Nat.card_congr ?_
  refine ⟨fun y => ⟨((S.mem_axisBaseFinset).1 y.2).choose,
      ((S.mem_axisBaseFinset).1 y.2).choose_spec.1⟩,
    fun x => ⟨S.baseChar x.1, S.baseChar_mem_axisBaseFinset x.2⟩, ?_, ?_⟩
  · intro y
    exact Subtype.ext ((S.mem_axisBaseFinset).1 y.2).choose_spec.2
  · intro x
    refine Subtype.ext (S.baseChar_injective ?_)
    exact ((S.mem_axisBaseFinset).1 (S.baseChar_mem_axisBaseFinset x.2)).choose_spec.2

open scoped Classical in
noncomputable def axisWeightFinset (i : Fin q) : Finset (S.grp → ℂ) :=
  {θ ∈ irrFinset S.grp | ∃ lam ∈ S.axisBaseFinset i, lam ∈ resConstituents S.base θ}

theorem mem_axisWeightFinset {i : Fin q} {θ : S.grp → ℂ} :
    θ ∈ S.axisWeightFinset i ↔ θ ∈ Irr S.grp ∧
      ∃ lam ∈ S.axisBaseFinset i, lam ∈ resConstituents S.base θ := by
  classical
  rw [axisWeightFinset, Finset.mem_filter, mem_irrFinset]

theorem axisWeightFinset_subset_Irr (i : Fin q) : ↑(S.axisWeightFinset i) ⊆ Irr S.grp :=
  fun _ h => ((S.mem_axisWeightFinset).1 h).1

theorem mem_axisBaseFinset_of_mem_resConstituents {i : Fin q} {θ : S.grp → ℂ}
    (hθ : θ ∈ S.axisWeightFinset i) {mu : S.base → ℂ}
    (hmu : mu ∈ resConstituents S.base θ) : mu ∈ S.axisBaseFinset i := by
  obtain ⟨hIrr, lam, hlam, hlamres⟩ := (S.mem_axisWeightFinset).1 hθ
  obtain ⟨χ, hχ, rfl⟩ := (S.mem_axisBaseFinset).1 hlam
  obtain ⟨t, ht⟩ := (mem_resConstituents_iff_exists_conjClassFun hIrr hlamres).1 hmu
  rw [S.conjClassFun_baseChar t χ] at ht
  exact (S.mem_axisBaseFinset).2 ⟨S.charAct t.right⁻¹ χ, hχ.charAct _, ht⟩

theorem mem_axisWeightFinset_iff_baseChar {i : Fin q} {θ : S.grp → ℂ} :
    θ ∈ S.axisWeightFinset i ↔ θ ∈ Irr S.grp ∧ ∃ χ : Multiplicative V →* ℂˣ,
      S.IsAxisChar i χ ∧ S.baseChar χ ∈ resConstituents S.base θ := by
  rw [S.mem_axisWeightFinset]
  refine and_congr_right fun _ => ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨lam, hlam, hlamres⟩ := h
    obtain ⟨χ, hχ, rfl⟩ := (S.mem_axisBaseFinset).1 hlam
    exact ⟨χ, hχ, hlamres⟩
  · obtain ⟨χ, hχ, hres⟩ := h
    exact ⟨S.baseChar χ, S.baseChar_mem_axisBaseFinset hχ, hres⟩

theorem disjoint_axisWeightFinset {i j : Fin q} (hij : i ≠ j) :
    Disjoint (S.axisWeightFinset i) (S.axisWeightFinset j) := by
  rw [Finset.disjoint_left]
  intro θ hi hj
  obtain ⟨-, χ, hχ, hres⟩ := (S.mem_axisWeightFinset_iff_baseChar).1 hj
  obtain ⟨χ', hχ', hχ'eq⟩ :=
    (S.mem_axisBaseFinset).1 (S.mem_axisBaseFinset_of_mem_resConstituents hi hres)
  have hchi : χ' = χ := S.baseChar_injective hχ'eq
  subst hchi
  exact hij (hχ'.unique hχ)

theorem card_resConstituents_of_mem_axisWeightFinset {i : Fin q} {θ : S.grp → ℂ}
    (hθ : θ ∈ S.axisWeightFinset i) :
    (resConstituents S.base θ).card = (S.lineCentralizer i).index := by
  obtain ⟨hIrr, lam, hlam, hlamres⟩ := (S.mem_axisWeightFinset).1 hθ
  obtain ⟨χ, hχ, rfl⟩ := (S.mem_axisBaseFinset).1 hlam
  rw [← natCard_quotient_inertiaGroup_eq_card (K := S.grp) (N := S.base) hIrr hlamres,
    ← Subgroup.index_eq_card, S.index_inertiaGroup_baseChar hχ]

variable [IsMulCommutative U]

theorem exists_finset_axisBlock {i : Fin q} {χ : Multiplicative V →* ℂˣ}
    (h : S.IsAxisChar i χ) :
    ∃ T : Finset (S.grp → ℂ), ↑T ⊆ Irr S.grp ∧
      T.card = Nat.card (S.lineCentralizer i) ∧
      indClassFun S.base (S.baseChar χ) = ∑ ψ ∈ T, ψ ∧
      ∀ ψ ∈ T, ψ 1 = ((S.lineCentralizer i).index : ℂ) := by
  have hcomm : IsMulCommutative
      ((S.complSub ⊓ inertiaGroup S.base (S.baseChar χ) : Subgroup S.grp) : Type _) := by
    rw [S.inf_complSub_inertiaGroup_eq h]
    refine ⟨⟨?_⟩⟩
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    obtain ⟨x, -, rfl⟩ := Subgroup.mem_map.1 ha
    obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.1 hb
    refine Subtype.ext ?_
    change (inr x : S.grp) * inr y = inr y * inr x
    rw [← map_mul, ← map_mul, IsMulCommutative.is_comm.comm]
  obtain ⟨T, hTsub, hTcard, hTsum, hTdeg⟩ :=
    AbelianInertiaBlock.exists_finset_Irr_indClassFun (U := S.complSub)
      (S.baseChar_mem_Irr χ) S.sup_base_complSub S.inf_base_complSub
      (by rw [S.natCard_complSub]; exact S.coprime_natCard_base)
  refine ⟨T, hTsub, ?_, hTsum, fun ψ hψ => ?_⟩
  · rw [hTcard, S.inf_complSub_inertiaGroup_eq h]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective (S.lineCentralizer i)
      (inr : U →* S.grp) (inr_injective (φ := S.mulAutHom))).toEquiv).symm
  · rw [hTdeg ψ hψ, S.baseChar_one, mul_one, S.index_inertiaGroup_baseChar h]

theorem mem_block_iff_mem_resConstituents {i : Fin q} {χ : Multiplicative V →* ℂˣ}
    (h : S.IsAxisChar i χ) {T : Finset (S.grp → ℂ)} (hTsub : ↑T ⊆ Irr S.grp)
    (hTsum : indClassFun S.base (S.baseChar χ) = ∑ ψ ∈ T, ψ)
    {θ : S.grp → ℂ} (hθIrr : θ ∈ Irr S.grp) :
    S.baseChar χ ∈ resConstituents S.base θ ↔ θ ∈ T := by
  classical
  rw [mem_resConstituents]
  have hfrob : cfInner (indClassFun S.base (S.baseChar χ)) θ
      = cfInner (resClassFun S.base θ) (S.baseChar χ) :=
    cfInner_indClassFun_eq_cfInner_resClassFun hθIrr (S.baseChar_mem_Irr χ)
  have hsum : cfInner (indClassFun S.base (S.baseChar χ)) θ = if θ ∈ T then 1 else 0 := by
    rw [hTsum, cfInner_sum_left,
      Finset.sum_congr rfl fun ψ hψ => cfInner_eq_ite_of_mem_Irr (hTsub hψ) hθIrr]
    by_cases hmem : θ ∈ T
    · rw [if_pos hmem, Finset.sum_eq_single_of_mem θ hmem (fun ψ _ hne => if_neg hne), if_pos rfl]
    · rw [if_neg hmem]
      refine Finset.sum_eq_zero fun ψ hψ => if_neg ?_
      intro hcon
      exact hmem (by rw [← hcon]; exact hψ)
  rw [← hfrob, hsum]
  refine ⟨fun hc => ?_, fun hmem => ⟨S.baseChar_mem_Irr χ, ?_⟩⟩
  · by_contra hcon
    rw [if_neg hcon] at hc
    exact absurd hc.2 (by norm_num)
  · rw [if_pos hmem]; norm_num

theorem apply_one_of_mem_axisWeightFinset {i : Fin q} {θ : S.grp → ℂ}
    (hθ : θ ∈ S.axisWeightFinset i) : θ 1 = ((S.lineCentralizer i).index : ℂ) := by
  obtain ⟨hIrr, lam, hlam, hlamres⟩ := (S.mem_axisWeightFinset).1 hθ
  obtain ⟨χ, hχ, rfl⟩ := (S.mem_axisBaseFinset).1 hlam
  obtain ⟨T, hTsub, -, hTsum, hTdeg⟩ := S.exists_finset_axisBlock hχ
  exact hTdeg θ ((S.mem_block_iff_mem_resConstituents hχ hTsub hTsum hIrr).1 hlamres)

theorem card_over_axisBase {i : Fin q} {lam : S.base → ℂ} (hlam : lam ∈ S.axisBaseFinset i)
    [DecidablePred fun θ : S.grp → ℂ => lam ∈ resConstituents S.base θ] :
    {θ ∈ S.axisWeightFinset i | lam ∈ resConstituents S.base θ}.card
      = Nat.card (S.lineCentralizer i) := by
  obtain ⟨χ, hχ, rfl⟩ := (S.mem_axisBaseFinset).1 hlam
  obtain ⟨T, hTsub, hTcard, hTsum, -⟩ := S.exists_finset_axisBlock hχ
  have key : ∀ θ : S.grp → ℂ, θ ∈ Irr S.grp →
      (S.baseChar χ ∈ resConstituents S.base θ ↔ θ ∈ T) :=
    fun θ hθ => S.mem_block_iff_mem_resConstituents hχ hTsub hTsum hθ
  have heq : {θ ∈ S.axisWeightFinset i | S.baseChar χ ∈ resConstituents S.base θ} = T := by
    refine Finset.ext fun θ => ?_
    rw [Finset.mem_filter]
    refine ⟨fun hc => (key θ ((S.mem_axisWeightFinset).1 hc.1).1).1 hc.2, fun hmem => ?_⟩
    exact ⟨(S.mem_axisWeightFinset).2 ⟨hTsub hmem, S.baseChar χ, hlam,
      (key θ (hTsub hmem)).2 hmem⟩, (key θ (hTsub hmem)).2 hmem⟩
  rw [heq, hTcard]

theorem card_below_axisWeight {i : Fin q} {θ : S.grp → ℂ} (hθ : θ ∈ S.axisWeightFinset i)
    [DecidablePred fun lam : S.base → ℂ => lam ∈ resConstituents S.base θ] :
    {lam ∈ S.axisBaseFinset i | lam ∈ resConstituents S.base θ}.card
      = (S.lineCentralizer i).index := by
  have heq : {lam ∈ S.axisBaseFinset i | lam ∈ resConstituents S.base θ}
      = resConstituents S.base θ := by
    refine Finset.ext fun mu => ?_
    rw [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨S.mem_axisBaseFinset_of_mem_resConstituents hθ h, h⟩⟩
  rw [heq, S.card_resConstituents_of_mem_axisWeightFinset hθ]

theorem card_axisWeightFinset_mul_index (i : Fin q) :
    (S.axisWeightFinset i).card * (S.lineCentralizer i).index
      = (p - 1) * Nat.card (S.lineCentralizer i) := by
  classical
  have h : ∑ lam ∈ S.axisBaseFinset i,
      {θ ∈ S.axisWeightFinset i | lam ∈ resConstituents S.base θ}.card
      = ∑ θ ∈ S.axisWeightFinset i,
        {lam ∈ S.axisBaseFinset i | lam ∈ resConstituents S.base θ}.card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl fun lam hlam => S.card_over_axisBase hlam,
    Finset.sum_congr rfl fun θ hθ => S.card_below_axisWeight hθ,
    Finset.sum_const, Finset.sum_const, S.card_axisBaseFinset, smul_eq_mul, smul_eq_mul] at h
  exact h.symm

noncomputable def allAxisWeightFinset : Finset (S.grp → ℂ) :=
  Finset.univ.biUnion S.axisWeightFinset

omit [IsMulCommutative U] in
theorem mem_allAxisWeightFinset {θ : S.grp → ℂ} :
    θ ∈ S.allAxisWeightFinset ↔ ∃ i, θ ∈ S.axisWeightFinset i := by
  rw [allAxisWeightFinset, Finset.mem_biUnion]
  constructor
  · intro h; obtain ⟨i, -, h2⟩ := h; exact ⟨i, h2⟩
  · intro h; obtain ⟨i, h2⟩ := h; exact ⟨i, Finset.mem_univ i, h2⟩

theorem allAxisWeightFinset_subset_Irr : ↑S.allAxisWeightFinset ⊆ Irr S.grp := by
  intro θ hθ
  obtain ⟨i, hi⟩ := (S.mem_allAxisWeightFinset).1 hθ
  exact S.axisWeightFinset_subset_Irr i hi

theorem card_allAxisWeightFinset_mul_sq (a : ℕ) (ha : ∀ i, (S.lineCentralizer i).index = a) :
    S.allAxisWeightFinset.card * a ^ 2 = q * ((p - 1) * Nat.card U) := by
  classical
  rw [allAxisWeightFinset,
    Finset.card_biUnion fun i _ j _ hij => S.disjoint_axisWeightFinset hij]
  have key : ∀ i : Fin q, (S.axisWeightFinset i).card * a ^ 2 = (p - 1) * Nat.card U := by
    intro i
    have h1 := S.card_axisWeightFinset_mul_index i
    rw [ha i] at h1
    have hci : Nat.card (S.lineCentralizer i) * a = Nat.card U := by
      rw [← ha i]; exact Subgroup.card_mul_index _
    calc (S.axisWeightFinset i).card * a ^ 2
        = (S.axisWeightFinset i).card * a * a := by ring
      _ = (p - 1) * Nat.card (S.lineCentralizer i) * a := by rw [h1]
      _ = (p - 1) * (Nat.card (S.lineCentralizer i) * a) := by ring
      _ = (p - 1) * Nat.card U := by rw [hci]
  rw [Finset.sum_mul, Finset.sum_congr rfl fun i _ => key i, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]

omit [IsMulCommutative U] in
theorem mem_axisBaseFinset_iff {i : Fin q} {lam : S.base → ℂ} :
    lam ∈ S.axisBaseFinset i ↔ lam ∈ Irr S.base ∧
      (∃ v ∈ S.line i, lam (S.baseHom (Multiplicative.ofAdd v)) ≠ lam 1) ∧
      ∀ j, j ≠ i → ∀ v ∈ S.line j, lam (S.baseHom (Multiplicative.ofAdd v)) = lam 1 := by
  constructor
  · intro h
    obtain ⟨χ, hχ, rfl⟩ := (S.mem_axisBaseFinset).1 h
    refine ⟨S.baseChar_mem_Irr χ, ?_, fun j hj v hv => ?_⟩
    · obtain ⟨v, hv, hvne⟩ := hχ.exists_ne_one
      refine ⟨v, hv, ?_⟩
      rw [S.baseChar_apply, S.baseChar_one]
      exact fun hcon => hvne (Units.ext hcon)
    · rw [S.baseChar_apply, S.baseChar_one, hχ.eq_one_of_ne hj hv]
      simp
  · intro h
    obtain ⟨hIrr, ⟨v, hv, hvne⟩, hother⟩ := h
    obtain ⟨χ, rfl⟩ := S.exists_baseChar_eq hIrr
    refine (S.mem_axisBaseFinset).2 ⟨χ, isAxisChar_of ⟨v, hv, ?_⟩ fun j hj w hw => ?_, rfl⟩
    · intro hcon
      rw [S.baseChar_apply, S.baseChar_one, hcon] at hvne
      exact hvne (by simp)
    · have hw2 := hother j hj w hw
      rw [S.baseChar_apply, S.baseChar_one] at hw2
      exact Units.ext hw2

omit [IsMulCommutative U] in
theorem mem_axisWeightFinset_iff {i : Fin q} {θ : S.grp → ℂ} :
    θ ∈ S.axisWeightFinset i ↔ θ ∈ Irr S.grp ∧
      ∃ lam ∈ resConstituents S.base θ,
        (∃ v ∈ S.line i, lam (S.baseHom (Multiplicative.ofAdd v)) ≠ lam 1) ∧
        ∀ j, j ≠ i → ∀ v ∈ S.line j, lam (S.baseHom (Multiplicative.ofAdd v)) = lam 1 := by
  rw [S.mem_axisWeightFinset]
  refine and_congr_right fun hθ => ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨lam, hlam, hlamres⟩ := h
    obtain ⟨-, h1, h2⟩ := (S.mem_axisBaseFinset_iff).1 hlam
    exact ⟨lam, hlamres, h1, h2⟩
  · obtain ⟨lam, hlamres, h1, h2⟩ := h
    exact ⟨lam, (S.mem_axisBaseFinset_iff).2
      ⟨resConstituents_subset_Irr (Finset.mem_coe.2 hlamres), h1, h2⟩, hlamres⟩

omit [IsMulCommutative U] in
theorem cfInner_resClassFun_baseChar_eq (θ : S.grp → ℂ) (χ : Multiplicative V →* ℂˣ)
    [Fintype (Multiplicative V)] :
    cfInner (resClassFun S.base θ) (S.baseChar χ)
      = cfInner (fun v : Multiplicative V => θ (inl v)) (fun v => (χ v : ℂ)) := by
  rw [← cfInner_comp_equiv S.baseEquiv.toEquiv]
  congr 1
  · funext v
    rw [Function.comp_apply, resClassFun_apply]
    congr 1
    change ((S.baseEquiv v : S.base) : S.grp) = inl v
    rw [S.baseEquiv_apply, S.coe_baseHom_apply]
  · funext v
    rw [Function.comp_apply]
    change S.baseChar χ (S.baseEquiv v) = (χ v : ℂ)
    rw [S.baseEquiv_apply, S.baseChar_apply]

omit [IsMulCommutative U] in
theorem cfInner_resClassFun_baseChar_quot {θ' : (S.quot).grp → ℂ} (χ : Multiplicative V →* ℂˣ) :
    cfInner (resClassFun S.base (θ' ∘ S.quotHom)) (S.baseChar χ)
      = cfInner (resClassFun (S.quot).base θ') ((S.quot).baseChar χ) := by
  have hfin : Finite V := S.finite_of_finite_line
  have : Finite (Multiplicative V) := hfin
  let _ : Fintype (Multiplicative V) := Fintype.ofFinite _
  rw [S.cfInner_resClassFun_baseChar_eq, (S.quot).cfInner_resClassFun_baseChar_eq]
  congr 1
  funext v
  simp only [Function.comp_apply]
  rw [S.quotHom_inl]

omit [IsMulCommutative U] in
theorem exists_comp_quotHom_of_kernel {θ : S.grp → ℂ} (hθ : θ ∈ Irr S.grp)
    (hker : ∀ u ∈ commutator U, θ (inr u) = θ 1) :
    ∃ θ' ∈ Irr (S.quot).grp, θ' ∘ S.quotHom = θ := by
  have hmem : θ ∈ irrTrivialOn (S.quotHom).ker := by
    rw [mem_irrTrivialOn]
    refine ⟨hθ, fun x hx => ?_⟩
    rw [S.mem_ker_quotHom] at hx
    have hx2 : x = inr x.right :=
      SemidirectProduct.ext (by rw [left_inr, hx.1]) (by rw [right_inr])
    rw [hx2]
    exact hker _ hx.2
  exact (bijOn_comp_of_surjective S.quotHom_surjective).surjOn hmem

omit [IsMulCommutative U] in
theorem quot_lineScalar_mk (i : Fin q) (u : U) :
    (S.quot).lineScalar i (QuotientGroup.mk u) = S.lineScalar i u := by
  refine ((S.quot).eq_lineScalar i (QuotientGroup.mk u) ?_).symm
  intro v hv
  rw [quot_act, S.quotAct_mk]
  rw [S.quot_line] at hv
  exact S.act_apply_eq_lineScalar_smul i u hv

omit [IsMulCommutative U] in
theorem lineCentralizer_quot (i : Fin q) :
    S.lineCentralizer i
      = ((S.quot).lineCentralizer i).comap (QuotientGroup.mk' (commutator U)) := by
  ext u
  rw [Subgroup.mem_comap, S.lineCentralizer_eq_ker, (S.quot).lineCentralizer_eq_ker,
    MonoidHom.mem_ker, MonoidHom.mem_ker, S.lineScalarHom_apply, (S.quot).lineScalarHom_apply,
    show (QuotientGroup.mk' (commutator U)) u = QuotientGroup.mk u from rfl,
    S.quot_lineScalar_mk]

omit [IsMulCommutative U] in
theorem index_lineCentralizer_quot (i : Fin q) :
    ((S.quot).lineCentralizer i).index = (S.lineCentralizer i).index := by
  rw [S.lineCentralizer_quot i]
  exact (Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)).symm

omit [IsMulCommutative U] in
theorem quot_isAxisChar_iff {i : Fin q} {χ : Multiplicative V →* ℂˣ} :
    (S.quot).IsAxisChar i χ ↔ S.IsAxisChar i χ := by
  rw [(S.quot).isAxisChar_def, S.isAxisChar_def, S.quot_line]

omit [IsMulCommutative U] in
theorem mem_resConstituents_baseChar_comp_quotHom_iff {χ : Multiplicative V →* ℂˣ}
    {θ' : (S.quot).grp → ℂ} :
    S.baseChar χ ∈ resConstituents S.base (θ' ∘ S.quotHom)
      ↔ (S.quot).baseChar χ ∈ resConstituents (S.quot).base θ' := by
  rw [mem_resConstituents, mem_resConstituents, S.cfInner_resClassFun_baseChar_quot]
  exact and_congr_left fun _ => ⟨fun _ => (S.quot).baseChar_mem_Irr χ,
    fun _ => S.baseChar_mem_Irr χ⟩

omit [IsMulCommutative U] in
theorem mem_axisWeightFinset_comp_quotHom_iff {i : Fin q} {θ' : (S.quot).grp → ℂ}
    (hθ' : θ' ∈ Irr (S.quot).grp) :
    (θ' ∘ S.quotHom) ∈ S.axisWeightFinset i ↔ θ' ∈ (S.quot).axisWeightFinset i := by
  have hIrr : (θ' ∘ S.quotHom) ∈ Irr S.grp :=
    irrTrivialOn_subset_Irr ((bijOn_comp_of_surjective S.quotHom_surjective).mapsTo hθ')
  rw [S.mem_axisWeightFinset_iff_baseChar, (S.quot).mem_axisWeightFinset_iff_baseChar]
  simp only [and_iff_right hIrr, and_iff_right hθ']
  exact exists_congr fun χ =>
    and_congr (S.quot_isAxisChar_iff).symm S.mem_resConstituents_baseChar_comp_quotHom_iff

end ScalarCoordinateSystem

end CFSG.FeitThompson
