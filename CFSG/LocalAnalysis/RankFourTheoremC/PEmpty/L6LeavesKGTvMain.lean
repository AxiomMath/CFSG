module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKGSixDefs
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKGTvGroup
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKGTvStage

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KGTv

open CFSG.Open CFSG.HardMathSupport.Solomon.UniquenessMaximal
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.LocalAnalysis.GLTheoremB Subgroup

theorem mem_sup_zpowers_cases {A : Type} [Group A] {N : Subgroup A} {a : A}
    (ha : a ∈ normalizer (N : Set A)) (ha2 : a ^ 2 = 1) :
    ∀ x ∈ N ⊔ zpowers a, x ∈ N ∨ x * a ∈ N := by
  have haa : a * a = 1 := by rw [← pow_two]; exact ha2
  have hinv : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have hconj : ∀ n ∈ N, a * n * a ∈ N := fun n hn => by
    have := (Subgroup.mem_set_normalizer_iff.1 ha n).1 hn
    rwa [hinv] at this
  let T : Subgroup A :=
    { carrier := {x | x ∈ N ∨ x * a ∈ N}
      one_mem' := Or.inl N.one_mem
      mul_mem' := fun {x y} hx hy => by
        rcases hx with hx | hx <;> rcases hy with hy | hy
        · exact Or.inl (N.mul_mem hx hy)
        · refine Or.inr ?_
          rw [mul_assoc]
          exact N.mul_mem hx hy
        · refine Or.inr ?_
          have e : x * y * a = x * a * (a * y * a) := by
            calc x * y * a = x * (a * a) * y * a := by rw [haa, mul_one]
              _ = x * a * (a * y * a) := by group
          rw [e]
          exact N.mul_mem hx (hconj y hy)
        · refine Or.inl ?_
          have e : x * y = x * a * (a * (y * a) * a) := by
            calc x * y = x * (a * a) * y * (a * a) := by rw [haa, mul_one, mul_one]
              _ = x * a * (a * (y * a) * a) := by group
          rw [e]
          exact N.mul_mem hx (hconj _ hy)
      inv_mem' := fun {x} hx => by
        rcases hx with hx | hx
        · exact Or.inl (N.inv_mem hx)
        · refine Or.inr ?_
          have e : x⁻¹ * a = a * (x * a)⁻¹ * a := by group
          rw [e]
          exact hconj _ (N.inv_mem hx) }
  have hle : N ⊔ zpowers a ≤ T :=
    sup_le (fun n hn => Or.inl hn) (zpowers_le.2 (Or.inr (by rw [haa]; exact N.one_mem)))
  exact fun x hx => hle hx

theorem isOmegaTwo_of_mulEquiv {ε : Bool} {n : ℕ} {X Y : Type*} [Group X] [Group Y]
    (e : X ≃* Y) (h : IsOmegaTwo ε n X) : IsOmegaTwo ε n Y := by
  cases ε
  · obtain ⟨f⟩ := h
    exact ⟨e.symm.trans f⟩
  · obtain ⟨f⟩ := h
    exact ⟨e.symm.trans f⟩

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KGTv

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open CFSG.HardMathSupport.Solomon.UniquenessMaximal
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.LocalAnalysis.GLTheoremB Subgroup KGTv
  CFSG.ComponentClassification.OutcomeLocal

theorem kgTransvCent_holds : KGTransvCent := by
  unfold KGTransvCent
  intro A _ _ V _ _ hV ρ N a z q hNs hNn hnotAlt haNor ha1 ha2 haN hC hρ hTv hzN hzq hq hq5 hcomm
  classical
  set X0 : Subgroup A := N ⊔ zpowers a with hX0def
  have hNX : N ≤ X0 := le_sup_left
  have haX : a ∈ X0 := Subgroup.mem_sup_right (Subgroup.mem_zpowers a)
  have hcases := mem_sup_zpowers_cases haNor ha2
  let N' : Subgroup X0 := N.subgroupOf X0
  let a' : X0 := ⟨a, haX⟩
  let z' : X0 := ⟨z, hNX hzN⟩
  have eN : ↥N' ≃* ↥N := Subgroup.subgroupOfEquivOfLe hNX
  have hX' : ∀ x : X0, x ∈ N' ∨ x * a' ∈ N' := fun x => by
    rcases hcases x.1 x.2 with h | h
    · exact Or.inl h
    · exact Or.inr h
  have haN' : a' ∉ N' := haN
  have hidx : N'.index = 2 :=
    Subgroup.index_eq_two_iff_exists_notMem_and.2 ⟨a', haN', fun b => (hX' b).symm⟩
  haveI : N'.Normal := Subgroup.normal_of_index_eq_two hidx
  haveI hNs' : IsSimpleGroup ↥N' := eN.isSimpleGroup
  have hNn' : ∃ x y : ↥N', x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hNn
    exact ⟨eN.symm x, eN.symm y, fun h => hxy (eN.symm.injective (by
      rw [map_mul, map_mul]
      exact h))⟩
  have hnotAlt' : ∀ n : ℕ, 7 ≤ n → ¬ Nonempty (↥N' ≃* alternatingGroup (Fin n)) :=
    fun n hn ⟨f⟩ => hnotAlt n hn ⟨eN.symm.trans f⟩
  have hC' : ∀ x : X0, (∀ n ∈ N', x * n = n * x) → x = 1 := by
    intro x hx
    have := hC x.1 x.2 (fun n hn => congrArg Subtype.val (hx ⟨n, hNX hn⟩ hn))
    exact Subtype.ext this
  letI : Module (ZMod 2) (Additive V) := AddCommGroup.zmodModule fun x => by
    rw [two_nsmul]
    apply Additive.toMul.injective
    rw [toMul_add, toMul_zero]
    exact hV _
  let ρ₀ : X0 →* LinearMap.GeneralLinearGroup (ZMod 2) (Additive V) :=
    (i285_Φ.toMonoidHom.comp ρ).comp X0.subtype
  have hρ₀ : Function.Injective ρ₀ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : ρ x.1 = 1 := i285_Φ.injective (hx.trans (map_one _).symm)
    exact Subtype.ext (hρ x.1 x.2 h1)
  have hτ₀ : IsF2Transvection (ρ₀ a') := i285_isF2Transvection_Φ hV hTv
  have ha1' : a' ≠ 1 := fun h => ha1 (congrArg Subtype.val h)
  obtain ⟨U, _, _, _, ψ, hψinj, hψirr, hψgen, hψτ⟩ :=
    exists_irreducible_module hNs' hNn' hC' ha1' hX' ρ₀ hρ₀ hτ₀
  have hz'q : orderOf z' = q := by
    show orderOf (⟨z, hNX hzN⟩ : X0) = q
    rw [Subgroup.orderOf_mk]
    exact hzq
  have hcomm' : a' * z' = z' * a' := Subtype.ext hcomm
  have hz'N : z' ∈ N' := hzN
  obtain ⟨ε, n, hn3, hΩ, Y', hY'le, hz'Y, hY's, hY'n, hY'3⟩ :=
    stageL hNs' hNn' hnotAlt' haN' hX' hz'N hz'q hq hq5 hcomm' ψ hψinj hψirr hψgen hψτ
  let e : ↥Y' ≃* ↥(Y'.map X0.subtype) := Y'.equivMapOfInjective X0.subtype X0.subtype_injective
  refine ⟨ε, n, hn3, isOmegaTwo_of_mulEquiv eN hΩ, Y'.map X0.subtype, ?_, ⟨z', hz'Y, rfl⟩, ?_, ?_,
    ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    have hy' := hY'le hy
    rw [Subgroup.mem_inf] at hy'
    obtain ⟨hyN, hya⟩ := hy'
    rw [Subgroup.mem_inf]
    refine ⟨hyN, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hya ⊢
    exact congrArg Subtype.val hya
  · haveI := hY's
    exact e.symm.isSimpleGroup
  · obtain ⟨x, y, hxy⟩ := hY'n
    exact ⟨e x, e y, fun h => hxy (e.injective (by rw [map_mul, map_mul]; exact h))⟩
  · rw [← Nat.card_congr e.toEquiv]
    exact hY'3

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
