module

public import CFSG.FeitThompson.Representations.InvariantDetectingCharsQuotientDegree
public import CFSG.FeitThompson.Representations.CentralFrobeniusLayerDegreeSquareSum
import CFSG.FeitThompson.Representations.CentralLayerDegreeSquareDivisor
import CFSG.FeitThompson.Representations.FrobeniusAbelianKernelInducedCharacters
import CFSG.FeitThompson.Representations.CentralFrobeniusFamilyDescription

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace ScalarInvariantSystem

open SemidirectProduct Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p q : ℕ} [Fact p.Prime] [Fact q.Prime] {V U : Type*} [AddCommGroup V]
  [Module (ZMod p) V] [Group U] (S : ScalarInvariantSystem p q V U)

theorem natCard_base : Nat.card S.base = p ^ q := by
  have hfin : Finite V := S.finite_base
  have : Fintype V := Fintype.ofFinite V
  have hint : DirectSum.IsInternal S.line :=
    (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top S.line).2
      ⟨S.indep_line, S.iSup_line⟩
  have hfin2 : ∀ i, Module.Finite (ZMod p) (S.line i) := fun i =>
    Module.finite_of_finrank_eq_succ (n := 0) (S.finrank_line i)
  have e : (DirectSum (Fin q) fun i => (S.line i)) ≃ₗ[ZMod p] V :=
    LinearEquiv.ofBijective (DirectSum.coeLinearMap S.line) hint
  have hrk : Module.finrank (ZMod p) V = q := by
    rw [← e.finrank_eq, Module.finrank_directSum]
    simp [S.finrank_line]
  have hc := Module.card_eq_pow_finrank (K := ZMod p) (V := V)
  rw [ZMod.card, hrk] at hc
  rw [base_eq_range_inl,
    Nat.card_congr (MonoidHom.ofInjective (inl_injective (φ := S.mulAutHom))).toEquiv.symm,
    Nat.card_congr Multiplicative.toAdd, Nat.card_eq_fintype_card, hc]

theorem index_base : (S.base).index = Nat.card U := by
  rw [base_eq_range_inl, index_range_inl]

theorem sum_sq_degree_irrDetect_base :
    ∑ θ ∈ irrKerFinset S.base ⊥, θ 1 ^ 2 = (Nat.card U : ℂ) * ((p : ℂ) ^ q - 1) := by
  rw [sum_sq_degree_irrKerFinset_bot S.base, S.index_base, S.natCard_base]
  push_cast
  ring

theorem mem_irrKerFinset_base_bot {θ : S.grp → ℂ} :
    θ ∈ irrKerFinset S.base ⊥ ↔
      θ ∈ Irr S.grp ∧ ¬ ((S.base : Set S.grp) ⊆ charValueKernel θ) := by
  have h : θ ∈ (irrKerFinset S.base ⊥ : Set (S.grp → ℂ)) ↔ θ ∈ irrDetect ℂ S.base := by
    rw [coe_irrKerFinset_bot]
  rw [← Finset.mem_coe, h, mem_irrDetect, irrChar_eq_Irr]

theorem ne_one_of_mem_irrKerFinset_base_bot {θ : S.grp → ℂ} (hθ : θ ∈ irrKerFinset S.base ⊥) :
    θ ≠ 1 := by
  rintro rfl
  exact (S.mem_irrKerFinset_base_bot.1 hθ).2 (by rw [charValueKernel_one]; exact Set.subset_univ _)

noncomputable def indMap (θ : S.grp → ℂ) : S.bigGrp → ℂ :=
  indClassFun S.grpPart (kernelClassFun S.bAutHom θ)

theorem indMap_eq (θ : S.grp → ℂ) :
    S.indMap θ = indClassFun S.grpPart (kernelClassFun S.bAutHom θ) := (rfl)

theorem indMap_apply_one (θ : S.grp → ℂ) : S.indMap θ 1 = (q : ℂ) * θ 1 := by
  rw [indMap, indClassFun_apply_one, kernelClassFun_one, index_range_inl (φ := S.bAutHom),
    Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

theorem bAutHom_eq_semiAut_pow (β : Multiplicative (ZMod q)) :
    S.bAutHom β = S.semiAut ^ (Multiplicative.toAdd β).val := by
  have hne : NeZero q := ⟨(Nat.Prime.pos (Fact.out)).ne'⟩
  have hβ : β = Multiplicative.ofAdd (1 : ZMod q) ^ (Multiplicative.toAdd β).val := by
    rw [← ofAdd_nsmul, nsmul_eq_mul, mul_one]; simp
  conv_lhs => rw [hβ]
  rw [map_pow, S.bAutHom_gen]

theorem semiAut_pow_inl (n : ℕ) (v : V) :
    (S.semiAut ^ n) (inl (Multiplicative.ofAdd v)) =
      inl (Multiplicative.ofAdd ((S.lineAut ^ n) v)) := by
  refine SemidirectProduct.ext ?_ ?_
  · rw [S.semiAut_pow_left]; simp
  · rw [S.semiAut_pow_right]; simp

theorem bAutHom_apply_mem_base (β : Multiplicative (ZMod q)) {x : S.grp} (hx : x ∈ S.base) :
    S.bAutHom β x ∈ S.base := by
  rw [base_eq_range_inl] at hx ⊢
  obtain ⟨y, rfl⟩ := hx
  obtain ⟨v, rfl⟩ : ∃ v : V, Multiplicative.ofAdd v = y := ⟨Multiplicative.toAdd y, rfl⟩
  rw [S.bAutHom_eq_semiAut_pow, S.semiAut_pow_inl]
  exact ⟨_, rfl⟩

theorem base_subset_charValueKernel_comp_iff (β : Multiplicative (ZMod q)) (θ : S.grp → ℂ) :
    ((S.base : Set S.grp) ⊆ charValueKernel (θ ∘ S.bAutHom β))
      ↔ ((S.base : Set S.grp) ⊆ charValueKernel θ) := by
  constructor
  · intro h x hx
    obtain ⟨y, hy, hyx⟩ : ∃ y ∈ S.base, S.bAutHom β y = x := by
      refine ⟨(S.bAutHom β)⁻¹ x, ?_, by simp⟩
      have h2 := S.bAutHom_apply_mem_base β⁻¹ hx
      rwa [map_inv] at h2
    have h3 := mem_charValueKernel.1 (h hy)
    simp only [Function.comp_apply, map_one] at h3
    rw [hyx] at h3
    exact mem_charValueKernel.2 h3
  · intro h x hx
    refine mem_charValueKernel.2 ?_
    simp only [Function.comp_apply, map_one]
    exact mem_charValueKernel.1 (h (S.bAutHom_apply_mem_base β hx))

theorem comp_bAutHom_mem_irrKerFinset (β : Multiplicative (ZMod q)) {θ : S.grp → ℂ}
    (hθ : θ ∈ irrKerFinset S.base ⊥) : θ ∘ S.bAutHom β ∈ irrKerFinset S.base ⊥ := by
  rw [S.mem_irrKerFinset_base_bot] at hθ ⊢
  exact ⟨mem_Irr_comp_mulAut hθ.1 _, fun hc =>
    hθ.2 ((S.base_subset_charValueKernel_comp_iff β θ).1 hc)⟩

theorem charStabilizer_comp_bAutHom (θ : S.grp → ℂ) (β : Multiplicative (ZMod q)) :
    charStabilizer S.bAutHom (θ ∘ S.bAutHom β) = charStabilizer S.bAutHom θ := by
  have key : ∀ (ψ : S.grp → ℂ) (b g : Multiplicative (ZMod q)),
      (∀ k : S.grp, ψ (S.bAutHom g k) = ψ k) →
      ∀ k : S.grp, (ψ ∘ S.bAutHom b) (S.bAutHom g k) = (ψ ∘ S.bAutHom b) k := by
    intro ψ b g h k
    simp only [Function.comp_apply, ← MulAut.mul_apply, ← map_mul]
    rw [mul_comm b g, map_mul, MulAut.mul_apply, h]
  ext γ
  simp only [mem_charStabilizer]
  refine ⟨fun h => ?_, key θ β γ⟩
  have h2 := key (θ ∘ S.bAutHom β) β⁻¹ γ h
  intro k
  have h3 := h2 k
  simp only [Function.comp_apply, ← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one] at h3
  simpa using h3

theorem invariant_comp_bAutHom_iff (θ : S.grp → ℂ) (β : Multiplicative (ZMod q)) :
    (∀ x : S.grp, (θ ∘ S.bAutHom β) (S.semiAut x) = (θ ∘ S.bAutHom β) x)
      ↔ (∀ x : S.grp, θ (S.semiAut x) = θ x) := by
  rw [← S.charStabilizer_eq_top_iff, ← S.charStabilizer_eq_top_iff,
    S.charStabilizer_comp_bAutHom]

theorem comp_bAutHom_injective {θ : S.grp → ℂ}
    (hmove : ¬ (∀ x : S.grp, θ (S.semiAut x) = θ x)) :
    Function.Injective (fun β : Multiplicative (ZMod q) => θ ∘ S.bAutHom β) := by
  intro β γ h
  have hst := S.charStabilizer_eq_bot_of_not_invariant hmove
  have hmem : β * γ⁻¹ ∈ charStabilizer S.bAutHom θ := by
    refine mem_charStabilizer.2 fun k => ?_
    have h2 := congrFun h (S.bAutHom γ⁻¹ k)
    simp only [Function.comp_apply, ← MulAut.mul_apply, ← map_mul] at h2
    rw [mul_inv_cancel, map_one] at h2
    simpa using h2
  rw [hst, Subgroup.mem_bot] at hmem
  exact mul_inv_eq_one.1 hmem

theorem indMap_eq_iff {θ ψ : S.grp → ℂ} (hθ : θ ∈ Irr S.grp) (hψ : ψ ∈ Irr S.grp) :
    S.indMap θ = S.indMap ψ ↔ ∃ β : Multiplicative (ZMod q), ψ ∘ (S.bAutHom β) = θ := by
  have hf : Fintype S.grp := Fintype.ofFinite _
  have h := indClassFun_kernelClassFun_eq_iff (φ := S.bAutHom) hθ hψ
  rw [Subsingleton.elim (instFintypeSemidirectProduct (φ := S.bAutHom))
    (inferInstanceAs (Fintype S.bigGrp))] at h
  exact h

open Classical in
noncomputable def invIrrDetectBase : Finset (S.grp → ℂ) :=
  {θ ∈ irrKerFinset S.base ⊥ | ∀ x : S.grp, θ (S.semiAut x) = θ x}

open Classical in
theorem mem_invIrrDetectBase {θ : S.grp → ℂ} :
    θ ∈ S.invIrrDetectBase ↔
      θ ∈ irrKerFinset S.base ⊥ ∧ ∀ x : S.grp, θ (S.semiAut x) = θ x := by
  rw [invIrrDetectBase, Finset.mem_filter]

open Classical in
noncomputable def movedIrrDetectBase : Finset (S.grp → ℂ) :=
  {θ ∈ irrKerFinset S.base ⊥ | ¬ (∀ x : S.grp, θ (S.semiAut x) = θ x)}

open Classical in
theorem mem_movedIrrDetectBase {θ : S.grp → ℂ} :
    θ ∈ S.movedIrrDetectBase ↔
      θ ∈ irrKerFinset S.base ⊥ ∧ ¬ (∀ x : S.grp, θ (S.semiAut x) = θ x) := by
  rw [movedIrrDetectBase, Finset.mem_filter]

theorem mem_invIrrDetectBase_or_movedIrrDetectBase {θ : S.grp → ℂ}
    (hθ : θ ∈ irrKerFinset S.base ⊥) :
    θ ∈ S.invIrrDetectBase ∨ θ ∈ S.movedIrrDetectBase := by
  classical
  by_cases h : ∀ x : S.grp, θ (S.semiAut x) = θ x
  · exact Or.inl (S.mem_invIrrDetectBase.2 ⟨hθ, h⟩)
  · exact Or.inr (S.mem_movedIrrDetectBase.2 ⟨hθ, h⟩)

open Classical in
theorem sum_split_irrKerFinset_base_bot (f : (S.grp → ℂ) → ℂ) :
    ∑ θ ∈ irrKerFinset S.base ⊥, f θ
      = ∑ θ ∈ S.invIrrDetectBase, f θ + ∑ θ ∈ S.movedIrrDetectBase, f θ := by
  rw [invIrrDetectBase, movedIrrDetectBase,
    Finset.sum_filter_add_sum_filter_not (irrKerFinset S.base ⊥)
      (fun θ => ∀ x : S.grp, θ (S.semiAut x) = θ x) f]

theorem card_invIrrDetectBase : S.invIrrDetectBase.card = p - 1 := by
  classical
  rw [← S.natCard_invariantNonprincipalIrr, ← Nat.card_eq_finsetCard]
  refine Nat.card_congr ?_
  refine ⟨fun x => ⟨⟨x.1, ?_⟩, ?_, ?_⟩, fun y => ⟨y.1.1, ?_⟩, ?_, ?_⟩
  · exact (S.mem_irrKerFinset_base_bot.1 (S.mem_invIrrDetectBase.1 x.2).1).1
  · exact (irrAut_eq_self_iff _ _).2 (S.mem_invIrrDetectBase.1 x.2).2
  · exact S.ne_one_of_mem_irrKerFinset_base_bot (S.mem_invIrrDetectBase.1 x.2).1
  · refine S.mem_invIrrDetectBase.2 ⟨?_, (irrAut_eq_self_iff _ _).1 y.2.1⟩
    exact S.mem_irrKerFinset_base_bot.2 ⟨y.1.2, S.not_base_subset_charValueKernel y.1.2
      ((irrAut_eq_self_iff _ _).1 y.2.1) y.2.2⟩
  · intro x; rfl
  · intro y; rfl

theorem apply_one_of_mem_invIrrDetectBase (hfaith : S.totalCentralizer = ⊥) {θ : S.grp → ℂ}
    (hθ : θ ∈ S.invIrrDetectBase) : θ 1 = (Nat.card U : ℂ) := by
  obtain ⟨hθT, hinv⟩ := S.mem_invIrrDetectBase.1 hθ
  rw [S.apply_one_eq_index_totalCentralizer_of_invariant
    (S.mem_irrKerFinset_base_bot.1 hθT).1 hinv (S.ne_one_of_mem_irrKerFinset_base_bot hθT),
    hfaith, Subgroup.index_bot]

theorem sum_sq_degree_invIrrDetectBase (hfaith : S.totalCentralizer = ⊥) :
    ∑ θ ∈ S.invIrrDetectBase, θ 1 ^ 2 = ((p : ℂ) - 1) * (Nat.card U : ℂ) ^ 2 := by
  rw [Finset.sum_congr rfl (fun θ hθ => by
      rw [S.apply_one_of_mem_invIrrDetectBase hfaith hθ]), Finset.sum_const,
    S.card_invIrrDetectBase, nsmul_eq_mul]
  congr 1
  have h1 : 1 ≤ p := (Nat.Prime.one_lt (Fact.out)).le
  push_cast [Nat.cast_sub h1]
  ring

theorem indMap_mem_Irr_of_mem_movedIrrDetectBase {θ : S.grp → ℂ}
    (hθ : θ ∈ S.movedIrrDetectBase) : S.indMap θ ∈ Irr S.bigGrp := by
  obtain ⟨hθT, hmove⟩ := S.mem_movedIrrDetectBase.1 hθ
  exact S.indClassFun_mem_Irr_of_not_invariant (S.mem_irrKerFinset_base_bot.1 hθT).1 hmove

theorem indMap_notMem_Irr_of_mem_invIrrDetectBase {θ : S.grp → ℂ}
    (hθ : θ ∈ S.invIrrDetectBase) : S.indMap θ ∉ Irr S.bigGrp := by
  obtain ⟨hθT, hinv⟩ := S.mem_invIrrDetectBase.1 hθ
  intro hc
  have h1 := cfInner_self_of_mem_Irr hc
  rw [indMap, S.cfInner_self_indClassFun_of_invariant
    (S.mem_irrKerFinset_base_bot.1 hθT).1 hinv] at h1
  have hq1 : (q : ℕ) = 1 := by exact_mod_cast h1
  exact (Nat.Prime.one_lt (Fact.out : q.Prime)).ne' hq1

theorem apply_one_indMap_of_mem_invIrrDetectBase (hfaith : S.totalCentralizer = ⊥)
    {θ : S.grp → ℂ} (hθ : θ ∈ S.invIrrDetectBase) :
    S.indMap θ 1 = (q : ℂ) * (Nat.card U : ℂ) := by
  rw [S.indMap_apply_one, S.apply_one_of_mem_invIrrDetectBase hfaith hθ]

open Classical in
theorem card_fibre_movedIrrDetectBase {θ : S.grp → ℂ} (hθ : θ ∈ S.movedIrrDetectBase) :
    ({ψ ∈ S.movedIrrDetectBase | S.indMap ψ = S.indMap θ}).card = q := by
  obtain ⟨hθT, hmove⟩ := S.mem_movedIrrDetectBase.1 hθ
  have hθIrr := (S.mem_irrKerFinset_base_bot.1 hθT).1
  have hfib : {ψ ∈ S.movedIrrDetectBase | S.indMap ψ = S.indMap θ}
      = Finset.image (fun β : Multiplicative (ZMod q) => θ ∘ S.bAutHom β) Finset.univ := by
    ext ψ
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hψ, heq⟩
      have hψIrr := (S.mem_irrKerFinset_base_bot.1 (S.mem_movedIrrDetectBase.1 hψ).1).1
      exact (S.indMap_eq_iff hψIrr hθIrr).1 heq
    · rintro ⟨β, rfl⟩
      refine ⟨S.mem_movedIrrDetectBase.2 ⟨S.comp_bAutHom_mem_irrKerFinset β hθT, ?_⟩, ?_⟩
      · rw [S.invariant_comp_bAutHom_iff]; exact hmove
      · exact (S.indMap_eq_iff (mem_Irr_comp_mulAut hθIrr _) hθIrr).2 ⟨β, rfl⟩
  rw [hfib, Finset.card_image_of_injective _ (S.comp_bAutHom_injective hmove),
    Finset.card_univ, ← Nat.card_eq_fintype_card, Nat.card_congr Multiplicative.toAdd,
    Nat.card_zmod]

noncomputable def basePart : Subgroup S.grpPart :=
  S.base.map (mulEquivRangeInl S.bAutHom).toMonoidHom

theorem mem_basePart {x : S.grpPart} :
    x ∈ S.basePart ↔ (mulEquivRangeInl S.bAutHom).symm x ∈ S.base := by
  simp only [basePart, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [show (mulEquivRangeInl S.bAutHom).symm
      ((mulEquivRangeInl S.bAutHom).toMonoidHom y) = y from
        (mulEquivRangeInl S.bAutHom).symm_apply_apply y]
    exact hy
  · exact fun h => ⟨_, h, by simp⟩

theorem basePart_subset_charValueKernel_iff {θ : S.grp → ℂ} :
    ((S.basePart : Set S.grpPart) ⊆ charValueKernel (kernelClassFun S.bAutHom θ))
      ↔ ((S.base : Set S.grp) ⊆ charValueKernel θ) := by
  set e := mulEquivRangeInl S.bAutHom with he
  have hval : ∀ x : S.grpPart, kernelClassFun S.bAutHom θ x = θ (e.symm x) := by
    intro x; rw [kernelClassFun_eq_comp]; rfl
  constructor
  · intro h y hy
    have hx : (e y : S.grpPart) ∈ S.basePart := by
      rw [S.mem_basePart, e.symm_apply_apply]; exact hy
    have h2 := mem_charValueKernel.1 (h hx)
    rw [hval, hval, e.symm_apply_apply, map_one] at h2
    exact mem_charValueKernel.2 h2
  · intro h x hx
    have h2 := mem_charValueKernel.1 (h (S.mem_basePart.1 hx))
    refine mem_charValueKernel.2 ?_
    rw [hval, hval, map_one]
    exact h2

theorem kernelClassFun_comp_mulEquivRangeInl (ψ : S.grpPart → ℂ) :
    kernelClassFun S.bAutHom (ψ ∘ mulEquivRangeInl S.bAutHom) = ψ := by
  rw [kernelClassFun_eq_comp]; funext x; simp

theorem irrDetect_basePart_eq_image :
    irrDetect ℂ S.basePart = kernelClassFun S.bAutHom '' (irrDetect ℂ S.base) := by
  ext ψ
  constructor
  · intro hψ
    refine ⟨ψ ∘ mulEquivRangeInl S.bAutHom, ?_, S.kernelClassFun_comp_mulEquivRangeInl ψ⟩
    rw [mem_irrDetect, irrChar_eq_Irr] at hψ ⊢
    refine ⟨FrobeniusInduction.mem_Irr_comp_mulEquiv hψ.1 (mulEquivRangeInl S.bAutHom), ?_⟩
    rw [← S.basePart_subset_charValueKernel_iff, S.kernelClassFun_comp_mulEquivRangeInl]
    exact hψ.2
  · rintro ⟨θ, hθ, rfl⟩
    rw [mem_irrDetect, irrChar_eq_Irr] at hθ ⊢
    exact ⟨kernelClassFun_mem_Irr hθ.1, fun hc =>
      hθ.2 (S.basePart_subset_charValueKernel_iff.1 hc)⟩

noncomputable def indDetect : Finset (S.bigGrp → ℂ) := indFamDetectFinset S.grpPart S.basePart

theorem indDetect_eq : S.indDetect = indFamDetectFinset S.grpPart S.basePart := (rfl)

theorem mem_indDetect {f : S.bigGrp → ℂ} :
    f ∈ S.indDetect ↔ ∃ θ ∈ irrKerFinset S.base ⊥, S.indMap θ = f := by
  rw [indDetect, mem_indFamDetectFinset, mem_indFamDetect, S.irrDetect_basePart_eq_image]
  simp only [← Finset.mem_coe, coe_irrKerFinset_bot, indMap]
  constructor
  · rintro ⟨ψ, ⟨θ, hθ, rfl⟩, h⟩
    exact ⟨θ, hθ, h⟩
  · rintro ⟨θ, hθ, h⟩
    exact ⟨_, ⟨θ, hθ, rfl⟩, h⟩

open Classical in
noncomputable def indDetectIrr : Finset (S.bigGrp → ℂ) :=
  {χ ∈ S.indDetect | χ ∈ Irr S.bigGrp}

open Classical in
theorem mem_indDetectIrr {χ : S.bigGrp → ℂ} :
    χ ∈ S.indDetectIrr ↔ χ ∈ S.indDetect ∧ χ ∈ Irr S.bigGrp := by
  rw [indDetectIrr, Finset.mem_filter]

open Classical in
theorem indDetectIrr_eq_image : S.indDetectIrr = Finset.image S.indMap S.movedIrrDetectBase := by
  ext χ
  rw [S.mem_indDetectIrr, Finset.mem_image]
  constructor
  · rintro ⟨hS, hIrr⟩
    obtain ⟨θ, hθ, rfl⟩ := S.mem_indDetect.1 hS
    rcases S.mem_invIrrDetectBase_or_movedIrrDetectBase hθ with hinv | hmv
    · exact absurd hIrr (S.indMap_notMem_Irr_of_mem_invIrrDetectBase hinv)
    · exact ⟨θ, hmv, rfl⟩
  · rintro ⟨θ, hmv, rfl⟩
    exact ⟨S.mem_indDetect.2 ⟨θ, (S.mem_movedIrrDetectBase.1 hmv).1, rfl⟩,
      S.indMap_mem_Irr_of_mem_movedIrrDetectBase hmv⟩

open Classical in
noncomputable def indDetectSmall : Finset (S.bigGrp → ℂ) :=
  {χ ∈ S.indDetect | χ 1 = (q : ℂ) * (S.a : ℂ)}

open Classical in
theorem mem_indDetectSmall {χ : S.bigGrp → ℂ} :
    χ ∈ S.indDetectSmall ↔ χ ∈ S.indDetect ∧ χ 1 = (q : ℂ) * (S.a : ℂ) := by
  rw [indDetectSmall, Finset.mem_filter]

open Classical in
noncomputable def indDetectLarge : Finset (S.bigGrp → ℂ) :=
  {χ ∈ S.indDetectIrr | χ 1 = (q : ℂ) * (Nat.card U : ℂ)}

open Classical in
theorem mem_indDetectLarge {χ : S.bigGrp → ℂ} :
    χ ∈ S.indDetectLarge ↔
      χ ∈ S.indDetect ∧ χ ∈ Irr S.bigGrp ∧ χ 1 = (q : ℂ) * (Nat.card U : ℂ) := by
  rw [indDetectLarge, Finset.mem_filter, S.mem_indDetectIrr, and_assoc]

theorem mul_a_ne_mul_natCard (hau : S.a < Nat.card U) :
    (q : ℂ) * (S.a : ℂ) ≠ (q : ℂ) * (Nat.card U : ℂ) := by
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.Prime.pos (Fact.out : q.Prime)).ne'
  intro hc
  exact hau.ne (Nat.cast_injective (mul_left_cancel₀ hq0 hc))

open Classical in
theorem indDetectIrr_eq_union (hfaith : S.totalCentralizer = ⊥)
    (hdeg : ∀ χ ∈ S.indDetect, χ 1 = (q : ℂ) * (S.a : ℂ) ∨ χ 1 = (q : ℂ) * (Nat.card U : ℂ))
    (hau : S.a < Nat.card U) :
    S.indDetectIrr = S.indDetectSmall ∪ S.indDetectLarge := by
  ext χ
  rw [Finset.mem_union, S.mem_indDetectSmall, S.mem_indDetectLarge, S.mem_indDetectIrr]
  constructor
  · rintro ⟨hS, hIrr⟩
    rcases hdeg χ hS with h | h
    · exact Or.inl ⟨hS, h⟩
    · exact Or.inr ⟨hS, hIrr, h⟩
  · rintro (⟨hS, hsmall⟩ | ⟨hS, hIrr, -⟩)
    · refine ⟨hS, ?_⟩
      obtain ⟨θ, hθ, rfl⟩ := S.mem_indDetect.1 hS
      rcases S.mem_invIrrDetectBase_or_movedIrrDetectBase hθ with hinv | hmv
      · exact absurd (hsmall.symm.trans (S.apply_one_indMap_of_mem_invIrrDetectBase hfaith hinv))
          (S.mul_a_ne_mul_natCard hau)
      · exact S.indMap_mem_Irr_of_mem_movedIrrDetectBase hmv
    · exact ⟨hS, hIrr⟩

open Classical in
theorem disjoint_indDetectSmall_indDetectLarge (hau : S.a < Nat.card U) :
    Disjoint S.indDetectSmall S.indDetectLarge :=
  Finset.disjoint_left.2 fun _ h1 h2 =>
    S.mul_a_ne_mul_natCard hau ((S.mem_indDetectSmall.1 h1).2.symm.trans
      (S.mem_indDetectLarge.1 h2).2.2)

open Classical in
theorem sum_sq_degree_movedIrrDetectBase :
    ∑ θ ∈ S.movedIrrDetectBase, θ 1 ^ 2
      = ∑ χ ∈ S.indDetectIrr, (q : ℂ) * (χ 1 / (q : ℂ)) ^ 2 := by
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.Prime.pos (Fact.out : q.Prime)).ne'
  have hmaps : ∀ θ ∈ S.movedIrrDetectBase, S.indMap θ ∈ S.indDetectIrr := by
    intro θ hθ
    rw [S.indDetectIrr_eq_image]
    exact Finset.mem_image_of_mem _ hθ
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun θ => θ 1 ^ 2)]
  refine Finset.sum_congr rfl fun χ hχ => ?_
  obtain ⟨θ₀, hθ₀, rfl⟩ := Finset.mem_image.1 (S.indDetectIrr_eq_image ▸ hχ)
  have hcongr : ∀ ψ ∈ {ψ ∈ S.movedIrrDetectBase | S.indMap ψ = S.indMap θ₀},
      ψ 1 ^ 2 = (S.indMap θ₀ 1 / (q : ℂ)) ^ 2 := by
    intro ψ hψ
    rw [Finset.mem_filter] at hψ
    rw [← hψ.2, S.indMap_apply_one, mul_div_cancel_left₀ _ hq0]
  rw [Finset.sum_congr rfl hcongr, Finset.sum_const, S.card_fibre_movedIrrDetectBase hθ₀,
    nsmul_eq_mul]

open Classical in
theorem sum_sq_degree_eq_of_two_degrees (hfaith : S.totalCentralizer = ⊥)
    (hdeg : ∀ χ ∈ S.indDetect, χ 1 = (q : ℂ) * (S.a : ℂ) ∨ χ 1 = (q : ℂ) * (Nat.card U : ℂ))
    (hau : S.a < Nat.card U) :
    ∑ θ ∈ irrKerFinset S.base ⊥, θ 1 ^ 2
      = (q : ℂ) * ((S.indDetectSmall.card : ℂ) * (S.a : ℂ) ^ 2)
        + (q : ℂ) * ((S.indDetectLarge.card : ℂ) * (Nat.card U : ℂ) ^ 2)
        + ((p : ℂ) - 1) * (Nat.card U : ℂ) ^ 2 := by
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.Prime.pos (Fact.out : q.Prime)).ne'
  have hsm : ∑ χ ∈ S.indDetectSmall, (q : ℂ) * (χ 1 / (q : ℂ)) ^ 2
      = (q : ℂ) * ((S.indDetectSmall.card : ℂ) * (S.a : ℂ) ^ 2) := by
    rw [Finset.sum_congr rfl (g := fun _ => (q : ℂ) * (S.a : ℂ) ^ 2) (fun χ hχ => by
      rw [(S.mem_indDetectSmall.1 hχ).2, mul_div_cancel_left₀ _ hq0]), Finset.sum_const,
      nsmul_eq_mul]
    ring
  have hlg : ∑ χ ∈ S.indDetectLarge, (q : ℂ) * (χ 1 / (q : ℂ)) ^ 2
      = (q : ℂ) * ((S.indDetectLarge.card : ℂ) * (Nat.card U : ℂ) ^ 2) := by
    rw [Finset.sum_congr rfl (g := fun _ => (q : ℂ) * (Nat.card U : ℂ) ^ 2) (fun χ hχ => by
      rw [(S.mem_indDetectLarge.1 hχ).2.2, mul_div_cancel_left₀ _ hq0]), Finset.sum_const,
      nsmul_eq_mul]
    ring
  rw [S.sum_split_irrKerFinset_base_bot (fun θ => θ 1 ^ 2),
    S.sum_sq_degree_invIrrDetectBase hfaith, S.sum_sq_degree_movedIrrDetectBase,
    S.indDetectIrr_eq_union hfaith hdeg hau,
    Finset.sum_union (S.disjoint_indDetectSmall_indDetectLarge hau), hsm, hlg]
  ring

end ScalarInvariantSystem

theorem count_of_two_degrees_aux {p q a u s₁ n : ℕ} (hu : 0 < u)
    (hp : (p : ℂ) - 1 = 2 * a) (hs₁ : (s₁ : ℂ) * a = 2 * u)
    (hsum : (q : ℂ) * (s₁ * a ^ 2) + (q : ℂ) * (n * u ^ 2) + ((p : ℂ) - 1) * u ^ 2
      = (u : ℂ) * ((p : ℂ) ^ q - 1)) :
    (q : ℂ) * u * n + ((p : ℂ) - 1) * ((q : ℂ) + u) = (p : ℂ) ^ q - 1 := by
  have hu0 : (u : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hu.ne'
  refine mul_left_cancel₀ hu0 ?_
  linear_combination hsum + ((q : ℂ) * u) * hp - ((q : ℂ) * a) * hs₁

theorem count_of_two_degrees {p q : ℕ} [Fact p.Prime] [Fact q.Prime] {V U : Type*}
    [AddCommGroup V] [Module (ZMod p) V] [Group U] (S : ScalarInvariantSystem p q V U)
    (hfaith : S.totalCentralizer = ⊥) (hp : (p : ℂ) - 1 = 2 * (S.a : ℂ))
    (hdeg : ∀ χ ∈ S.indDetect, χ 1 = (q : ℂ) * (S.a : ℂ) ∨ χ 1 = (q : ℂ) * (Nat.card U : ℂ))
    (hau : S.a < Nat.card U)
    (hsmall : (S.indDetectSmall.card : ℂ) * (S.a : ℂ) = 2 * (Nat.card U : ℂ)) :
    (q : ℂ) * (Nat.card U : ℂ) * (S.indDetectLarge.card : ℂ)
        + ((p : ℂ) - 1) * ((q : ℂ) + (Nat.card U : ℂ))
      = (p : ℂ) ^ q - 1 := by
  have hUfin : Finite U := S.finite_units
  exact count_of_two_degrees_aux (a := S.a) (s₁ := S.indDetectSmall.card)
    (n := S.indDetectLarge.card) (u := Nat.card U) Nat.card_pos hp hsmall
    ((S.sum_sq_degree_eq_of_two_degrees hfaith hdeg hau).symm.trans
      S.sum_sq_degree_irrDetect_base)

end CFSG.FeitThompson
