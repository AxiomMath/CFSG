module

public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.FixedSpaceNum
public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.OrthJ
public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.Simple

public section

namespace CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  CFSG.LocalAnalysis.GLTheoremB CFSG.Assembly.LowTwoRank

@[expose] def PiData {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (p : ℕ)
    (Q : QuadraticForm (ZMod 2) V) (W : Submodule (ZMod 2) V) : Prop :=
  IsSimpleGroup ↥(orthJ Q W) ∧ (∃ a b : ↥(orthJ Q W), a * b ≠ b * a) ∧
    p ∣ Nat.card ↥(orthJ Q W) ∧
    ∃ (n' : ℕ) (ε' : Bool), 1 ≤ n' ∧
      CFSG.LocalAnalysis.GLTheoremB.IsOmegaTwo ε' (n' + 1) ↥(orthJ Q W) ∧
      CFSG.LocalAnalysis.GLTheoremB.HasFixedPointFreeOrder ε' n' p

section Perfect

variable {K : Type} [Field K] [IsF2 K] {V : Type*} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V}

theorem exists_noncomm_of_perfect {G : Type*} [Group G] [Nontrivial G] (h : commutator G = ⊤) :
    ∃ a b : G, a * b ≠ b * a := by
  by_contra hne
  push Not at hne
  obtain ⟨x, hx⟩ := exists_ne (1 : G)
  have hx' : x ∈ commutator G := h ▸ Subgroup.mem_top x
  have hle : commutator G ≤ ⊥ := by
    rw [commutator_def, Subgroup.commutator_le]
    intro g _ k _
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact hne g k
  exact hx (Subgroup.mem_bot.mp (hle hx'))

theorem commutator_elementaryGroup_eq_top_of_isometry_plus {m : ℕ} (hm : 3 ≤ m)
    (φ : V ≃ₗ[K] (Fin m ⊕ Fin m → K)) (hφ : ∀ v, quadPlus m K (φ v) = Q v) :
    commutator ↥(elementaryGroup Q) = ⊤ := by
  obtain ⟨hfd, hd, hnd⟩ := isometry_plus_facts φ hφ
  exact commutator_elementaryGroup_eq_top_f2 hnd (by omega)

theorem commutator_elementaryGroup_eq_top_of_isometry_minus {m : ℕ} (hm : 2 ≤ m)
    (φ : V ≃ₗ[K] (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K))
    (hφ : ∀ v, quadMinus m K 1 1 (φ v) = Q v) :
    commutator ↥(elementaryGroup Q) = ⊤ := by
  obtain ⟨hfd, hd, hnd⟩ := isometry_minus_facts (m := m) (by omega) φ hφ
  by_cases h3 : 3 ≤ m
  · exact commutator_elementaryGroup_eq_top_f2 hnd (by omega)
  · obtain rfl : m = 2 := by omega
    exact commutator_elementaryGroup_eq_top_of_four hnd (by omega)
      (not_exists_totallySingular_plane_of_isometry φ hφ
        not_exists_totallySingular_plane_quadMinus_two)

end Perfect

section Transport

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] {Q' : QuadraticForm (ZMod 2) W}

@[expose] noncomputable def statedOmegaEquivElementaryPlus {m : ℕ} (hm : 3 ≤ m)
    (φ : W ≃ₗ[ZMod 2] (Fin m ⊕ Fin m → ZMod 2)) (hφ : ∀ v, quadPlus m (ZMod 2) (φ v) = Q' v) :
    ↥(StatedOmega (StatedQuadPlus m (ZMod 2))) ≃* ↥(elementaryGroup Q') :=
  (Subgroup.equivMapOfInjective _ (glEquivStd (Fin m ⊕ Fin m)).toMonoidHom
    (glEquivStd (Fin m ⊕ Fin m)).injective).trans
    ((MulEquiv.subgroupCongr (statedOmega_map_glEquiv_plus hm φ hφ)).trans
      (Subgroup.equivMapOfInjective _ (conjAut φ).toMonoidHom (conjAut φ).injective).symm)

@[expose] noncomputable def statedOmegaEquivElementaryMinus {m : ℕ} (hm : 2 ≤ m)
    (φ : W ≃ₗ[ZMod 2] (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → ZMod 2))
    (hφ : ∀ v, quadMinus m (ZMod 2) 1 1 (φ v) = Q' v) :
    ↥(StatedOmega (StatedQuadMinus m (ZMod 2) 1 1)) ≃* ↥(elementaryGroup Q') :=
  (Subgroup.equivMapOfInjective _ (glEquivStd (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2)).toMonoidHom
    (glEquivStd (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2)).injective).trans
    ((MulEquiv.subgroupCongr (statedOmega_map_glEquiv_minus hm φ hφ)).trans
      (Subgroup.equivMapOfInjective _ (conjAut φ).toMonoidHom (conjAut φ).injective).symm)

theorem isOmegaTwo_elementaryGroup {ε : Bool} {n : ℕ} (hn : 1 ≤ n) (hε : ε = true → 2 ≤ n)
    (h : IsStdSpace ε Q' (n + 1)) :
    IsOmegaTwo ε (n + 1) ↥(elementaryGroup Q') := by
  cases ε
  · obtain ⟨φ, hφ⟩ := h
    exact ⟨(statedOmegaEquivElementaryMinus (by omega) φ hφ).symm⟩
  · obtain ⟨φ, hφ⟩ := h
    exact ⟨(statedOmegaEquivElementaryPlus (by have := hε rfl; omega) φ hφ).symm⟩

theorem isSimpleGroup_of_isStdSpace {ε : Bool} {n : ℕ} (hn : 1 ≤ n) (hε : ε = true → 2 ≤ n)
    (h : IsStdSpace ε Q' (n + 1)) : IsSimpleGroup ↥(elementaryGroup Q') := by
  cases ε
  · exact isSimpleGroup_elementaryGroup_of_isMinusSpace (by omega) h
  · exact isSimpleGroup_elementaryGroup_of_isPlusSpace (by have := hε rfl; omega) h

theorem exists_noncomm_of_isStdSpace {ε : Bool} {n : ℕ} (hn : 1 ≤ n) (hε : ε = true → 2 ≤ n)
    (h : IsStdSpace ε Q' (n + 1)) : ∃ a b : ↥(elementaryGroup Q'), a * b ≠ b * a := by
  have : Nontrivial ↥(elementaryGroup Q') := (isSimpleGroup_of_isStdSpace hn hε h).toNontrivial
  refine exists_noncomm_of_perfect ?_
  cases ε
  · obtain ⟨φ, hφ⟩ := h
    exact commutator_elementaryGroup_eq_top_of_isometry_minus (by omega) φ hφ
  · obtain ⟨φ, hφ⟩ := h
    exact commutator_elementaryGroup_eq_top_of_isometry_plus (by have := hε rfl; omega) φ hφ

@[expose] def prodRefl {U : Type*} [AddCommGroup U] [Module (ZMod 2) U] :
    (U ≃ₗ[ZMod 2] U) →* (((ZMod 2 × ZMod 2) × U) ≃ₗ[ZMod 2] ((ZMod 2 × ZMod 2) × U)) where
  toFun T₀ := LinearEquiv.prodCongr (LinearEquiv.refl (ZMod 2) (ZMod 2 × ZMod 2)) T₀
  map_one' := LinearEquiv.ext fun _ => rfl
  map_mul' _ _ := LinearEquiv.ext fun _ => rfl

theorem prodRefl_injective {U : Type*} [AddCommGroup U] [Module (ZMod 2) U] :
    Function.Injective (prodRefl (U := U)) := fun a b h =>
  LinearEquiv.ext fun u => by
    have := congrArg (fun S : ((ZMod 2 × ZMod 2) × U) ≃ₗ[ZMod 2] ((ZMod 2 × ZMod 2) × U) => (S (0, u)).2) h
    exact this

theorem exists_isometry_orderOf_of_isStdSpace {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    {Q'' : QuadraticForm (ZMod 2) U} {ε : Bool} {n p : ℕ} (h : IsStdSpace ε Q'' n)
    (hf : HasFixedPointFreeOrder ε n p) :
    ∃ T₀ : U ≃ₗ[ZMod 2] U, (∀ v, Q'' (T₀ v) = Q'' v) ∧ orderOf T₀ = p := by
  cases ε
  · obtain ⟨φ, hφ⟩ := h
    obtain ⟨A, hA, hord, -⟩ := hf
    have hφ' : ∀ v, StatedQuadMinus n (ZMod 2) 1 1 (φ v) = Q'' v := fun v => by
      rw [← hφ v, quadMinus_apply]; rfl
    have hiso := mem_statedOmega_isometry _ hA
    refine ⟨(conjAut φ).symm (glEquivStd _ A), fun v => ?_, ?_⟩
    · rw [← hφ' v, ← hφ' ((conjAut φ).symm (glEquivStd _ A) v), conjAut_symm_apply,
        LinearEquiv.apply_symm_apply, glEquivStd_apply]
      exact hiso _
    · rw [MulEquiv.orderOf_eq, MulEquiv.orderOf_eq, hord]
  · obtain ⟨φ, hφ⟩ := h
    obtain ⟨A, hA, hord, -⟩ := hf
    have hφ' : ∀ v, StatedQuadPlus n (ZMod 2) (φ v) = Q'' v := fun v => by
      rw [← hφ v, quadPlus_apply]; rfl
    have hiso := mem_statedOmega_isometry _ hA
    refine ⟨(conjAut φ).symm (glEquivStd _ A), fun v => ?_, ?_⟩
    · rw [← hφ' v, ← hφ' ((conjAut φ).symm (glEquivStd _ A) v), conjAut_symm_apply,
        LinearEquiv.apply_symm_apply, glEquivStd_apply]
      exact hiso _
    · rw [MulEquiv.orderOf_eq, MulEquiv.orderOf_eq, hord]

theorem dvd_natCard_elementaryGroup_of_isStdSpace [FiniteDimensional (ZMod 2) W] {ε : Bool}
    {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 1 ≤ n) (hε : ε = true → 2 ≤ n)
    (hnd : PolarNondeg Q') (hstd : IsStdSpace ε Q' (n + 1)) (hf : HasFixedPointFreeOrder ε n p) :
    p ∣ Nat.card ↥(elementaryGroup Q') := by
  have hfr := finrank_of_isStdSpace_arf hstd (fun _ => by omega)
  obtain ⟨x, hx0, hxQ⟩ := exists_ne_zero_map_eq_zero' (Q := Q') (by omega)
  obtain ⟨P, -⟩ := exists_hypPair hnd hxQ hx0
  have hstd2 := isStdSpace_restrict_perp hnd P hstd
  obtain ⟨T₀, hT₀, hord₀⟩ := exists_isometry_orderOf_of_isStdSpace hstd2 hf
  set T : W ≃ₗ[ZMod 2] W := (conjAut (hypSplit P)).symm (prodRefl T₀) with hT
  have hTv : ∀ v, hypSplit P (T v) = prodRefl T₀ (hypSplit P v) := fun v => by
    rw [hT, conjAut_symm_apply, LinearEquiv.apply_symm_apply]
  have hTiso : ∀ v, Q' (T v) = Q' v := fun v => by
    rw [map_eq_hypSplit P (T v), map_eq_hypSplit P v, hTv]
    exact congrArg _ (hT₀ (hypSplit P v).2)
  have hTO : T ∈ TauCeti.QuadraticMap.orthogonalGroup Q' :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr hTiso
  have hTord : orderOf T = p := by
    rw [hT, MulEquiv.orderOf_eq, orderOf_injective _ prodRefl_injective, hord₀]
  have hTp : T ^ p = 1 := hTord ▸ pow_orderOf_eq_one T
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hTE : T ∈ elementaryGroup Q' := by
    cases ε
    · exact mem_elementaryGroup_of_odd_pow_of_isMinusSpace (by omega) hstd hTO hodd hTp
    · exact mem_elementaryGroup_of_odd_pow_of_isPlusSpace (by have := hε rfl; omega) hstd hTO
        hodd hTp
  have := orderOf_dvd_natCard (⟨T, hTE⟩ : ↥(elementaryGroup Q'))
  rwa [Subgroup.orderOf_mk, hTord] at this

end Transport

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem piData_of_isStdSpace [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
    {W : Submodule (ZMod 2) V} (hW : PolarNondegOn Q W) {ε' : Bool} {n' p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn' : 1 ≤ n')
    (hε' : ε' = true → 2 ≤ n') (hstd : IsStdSpace ε' (Q.restrict W) (n' + 1))
    (hf : HasFixedPointFreeOrder ε' n' p) : PiData p Q W := by
  have e := orthJEquiv hW
  have hΩ : IsOmegaTwo ε' (n' + 1) ↥(orthJ Q W) := by
    have := isOmegaTwo_elementaryGroup hn' hε' hstd
    cases ε'
    · obtain ⟨e'⟩ := this
      exact ⟨e.trans e'⟩
    · obtain ⟨e'⟩ := this
      exact ⟨e.trans e'⟩
  have hdvd : p ∣ Nat.card ↥(orthJ Q W) := by
    rw [Nat.card_congr e.toEquiv]
    exact dvd_natCard_elementaryGroup_of_isStdSpace hp hp2 hn' hε' (nondegenerate_polarBilin_restrict hW) hstd hf
  refine ⟨?_, ?_, hdvd, n', ε', hn', hΩ, hf⟩
  · exact (MulEquiv.isSimpleGroup_congr e).mpr (isSimpleGroup_of_isStdSpace hn' hε' hstd)
  · obtain ⟨a, b, hab⟩ := exists_noncomm_of_isStdSpace hn' hε' hstd
    refine ⟨(orthJEquiv hW).symm a, (orthJEquiv hW).symm b, fun h => hab ?_⟩
    have := congrArg (orthJEquiv hW) h
    simpa using this

theorem piData_of_fixedSpace [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
    (hQ : PolarNondeg Q) {ε : Bool} {n : ℕ} (hstd : IsStdSpace ε Q (n + 1)) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hn : 1 ≤ n) (hfpf : HasFixedPointFreeOrder ε n p)
    {g : V ≃ₗ[ZMod 2] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hgp : g ^ p = 1)
    (hdim : 4 ≤ finrank (ZMod 2) (fixSub (Subgroup.zpowers g))) :
    PiData p Q (fixSub (Subgroup.zpowers g)) := by
  obtain ⟨ε', n', h1, h2, h3, h4⟩ := fixedSpace_numerics' hQ hstd hp hp2 hn hfpf hg hgp hdim
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hEO : Subgroup.zpowers g ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
    (Subgroup.zpowers_le).mpr hg
  have hoddc : Odd (Nat.card (Subgroup.zpowers g)) :=
    odd_natCard_subgroup_of_pow_eq_one hodd fun h hh => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hgp, one_zpow]
  exact piData_of_isStdSpace (polarNondegOn_fixSub hQ hEO hoddc) hp hp2 h1 h2 h3 h4

end CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration
