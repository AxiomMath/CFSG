module

public import CFSG.LocalAnalysis.ComponentClassification.GS82ResidueVert
public import CFSG.LocalAnalysis.ComponentClassification.GS82DPrimeEscData

public section

namespace CFSG.ComponentClassification.GS82PumpInputs.Residue

open CFSG Subgroup
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem false_of_typQ_of_typL16
    {A B : Type} [Group A] [Group B]
    (e : A ⧸ pPrimeCore 2 A ≃* B ⧸ pPrimeCore 2 B) {q₀ : ℕ} (hA : TypQ q₀ A) (hB : TypL16 B) :
    False := by
  rcases hA.1 with hodd | ⟨n, -, h2A⟩
  · have hY : Blueprint.OddLieType ((B ⧸ pPrimeCore 2 B) ⧸ center (B ⧸ pPrimeCore 2 B)) :=
      oddLieType_of_mulEquiv ((Sol78.coreQuotientCenterEquiv A).symm.trans
        (Sol78.centerQuotCongr e)) hodd
    exact not_oddLieType_of_l34 hB.1 hY
  · obtain ⟨-, h2, -⟩ := isDoubleCoverOfAlt_of_mulEquiv e h2A
    rw [hB.2] at h2
    exact absurd h2 (by norm_num)

variable {H : Type} [Group H] [Finite H]

theorem exists_conj_mulAut' {M : Subgroup H} {x : H} (hx : orderOf x = 2)
    (hxN : x ∈ normalizer (M : Set H)) {T : Subgroup H} (hTM : T ≤ M)
    (hTC : T ≤ centralizer ({x} : Set H))
    (hTpc : IsPComponent 2 (T.subgroupOf (centralizer ({x} : Set H)))) :
    ∃ c : MulAut ↥M, (∀ y : ↥M, ((c y : ↥M) : H) = x * y * x⁻¹) ∧ (∀ y, c (c y) = y) ∧
      T.subgroupOf M ≤ fixedSubgroup c ∧
      IsPComponent 2 ((T.subgroupOf M).subgroupOf (fixedSubgroup c)) := by
  have hxx : x * x = 1 := by rw [← pow_two, ← hx, pow_orderOf_eq_one]
  set c : MulAut M := M.normalizerMonoidHom ⟨x, hxN⟩ with hcdef
  have hcapp : ∀ y : M, ((c y : M) : H) = x * y * x⁻¹ := fun y => rfl
  have hc : ∀ y, c (c y) = y := by
    intro y
    apply Subtype.ext
    rw [hcapp, hcapp]
    calc x * (x * (y : H) * x⁻¹) * x⁻¹ = (x * x) * y * (x * x)⁻¹ := by group
      _ = y := by rw [hxx]; group
  have hfixC : fixedSubgroup c = (M ⊓ centralizer ({x} : Set H)).subgroupOf M := by
    ext y
    rw [LocalAnalysis.ComponentInitial.mem_fixedSubgroup_iff, mem_subgroupOf, mem_inf,
      mem_centralizer_singleton_iff]
    constructor
    · intro hy
      have h1 := congrArg Subtype.val hy
      rw [hcapp] at h1
      refine ⟨y.2, ?_⟩
      calc (y : H) * x = x * y * x⁻¹ * x := by rw [h1]
        _ = x * y := by group
    · rintro ⟨-, hy⟩
      apply Subtype.ext
      rw [hcapp]
      calc x * (y : H) * x⁻¹ = y * x * x⁻¹ := by rw [hy]
        _ = y := by group
  have hTM' : T ≤ M ⊓ centralizer ({x} : Set H) := le_inf hTM hTC
  refine ⟨c, hcapp, hc, ?_, ?_⟩
  · rw [hfixC]
    intro y hy
    rw [mem_subgroupOf] at hy ⊢
    exact hTM' hy
  · rw [hfixC]
    exact (UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' (L := T) inf_le_left 2
      Nat.prime_two).mpr (CatalogueBPrimeJoin.pComponent_subgroupOf_of_le hTM' inf_le_right hTpc)

theorem verticalCentralEsc'_typQ
    (hP : TypPumpInput) (hP11 : L34CentralSLTwoFact) {q₀ : ℕ}
    (hq₀ : q₀ ∈ ({5, 7, 9} : Finset ℕ)) : VerticalCentralEsc' (TypQ q₀) TypL16 := by
  intro H _ _ hH M hM x hx hxN T hTM hTC hTpc hTQ w hw hwT hwZ
  rcases verticalCentralEsc_typQ hP hP11 hq₀ H hH M hM x hx hxN T hTM hTC hTpc hTQ w hw hwT
      hwZ with hT | hE
  · exact Or.inl hT
  refine Or.inr ⟨hE, ?_⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨c, hcapp, hc, hT'C, hT'p⟩ := exists_conj_mulAut' hx hxN hTM hTC hTpc
  have hxinv : x⁻¹ = x := by
    rw [inv_eq_iff_mul_eq_one, ← pow_two, ← hx, pow_orderOf_eq_one]
  have htriv : ∀ y : ↥M, y⁻¹ * c y ∈ pPrimeCore 2 ↥M := by
    intro y
    obtain ⟨z, hz, hzeq⟩ := hcon (y : H) y.2
    have e : z = y⁻¹ * c y := by
      apply Subtype.ext
      change (z : H) = _ at hzeq
      rw [hzeq, Subgroup.coe_mul, Subgroup.coe_inv, hcapp, hxinv]
    rwa [← e]
  have hMq2 : HarrisLit.IsTwoQuasisimple ↥M :=
    ((HarrisLit.isTwoComponent_iff_isPComponent M).mpr hM).2
  obtain ⟨e⟩ := nonempty_quot_equiv_of_map_eq_top
    (map_eq_top_of_forall_inv_mul_mem hMq2.2 c hc htriv hT'C hT'p)
  have hTQ' : TypQ q₀ ↥(T.subgroupOf M) :=
    coreInvariant_typQ q₀ _ _ ⟨Sol78.coreQuotCongr (subgroupOfEquivOfLe hTM).symm⟩ hTQ
  exact false_of_typQ_of_typL16 e hTQ' hE

end CFSG.ComponentClassification.GS82PumpInputs.Residue
