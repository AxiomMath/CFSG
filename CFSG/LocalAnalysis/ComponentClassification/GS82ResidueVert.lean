module

public import CFSG.LocalAnalysis.ComponentClassification.GS82ResidueL34

public section

namespace CFSG.ComponentClassification.GS82PumpInputs.Residue

open CFSG Subgroup
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

variable {H : Type} [Group H] [Finite H]

theorem exists_conj_mulAut {M : Subgroup H} {x : H} (hx : orderOf x = 2)
    (hxN : x ∈ normalizer (M : Set H)) {T : Subgroup H} (hTM : T ≤ M)
    (hTC : T ≤ centralizer ({x} : Set H))
    (hTpc : IsPComponent 2 (T.subgroupOf (centralizer ({x} : Set H)))) :
    ∃ c : MulAut ↥M, (∀ y, c (c y) = y) ∧ T.subgroupOf M ≤ fixedSubgroup c ∧
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
  refine ⟨c, hc, ?_, ?_⟩
  · rw [hfixC]
    intro y hy
    rw [mem_subgroupOf] at hy ⊢
    exact hTM' hy
  · rw [hfixC]
    exact (UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' (L := T) inf_le_left 2
      Nat.prime_two).mpr (CatalogueBPrimeJoin.pComponent_subgroupOf_of_le hTM' inf_le_right hTpc)

theorem mem_fusionZStar_of_mem_map {M : Subgroup H} {w : H} (hwM : w ∈ M)
    (hwZ : w ∈ (Open.fusionZStar ↥M).map M.subtype) : (⟨w, hwM⟩ : ↥M) ∈ Open.fusionZStar ↥M := by
  obtain ⟨m, hm, hmw⟩ := hwZ
  have : m = ⟨w, hwM⟩ := Subtype.ext hmw
  rwa [← this]

theorem center_ne_bot_of_mem {M T : Subgroup H} (hTM : T ≤ M) {w : H} (hw : orderOf w = 2)
    (hwT : w ∈ T) (hwZ : w ∈ (Open.fusionZStar ↥M).map M.subtype) :
    center (↥M ⧸ pPrimeCore 2 ↥M) ≠ ⊥ ∧
      center (↥(T.subgroupOf M) ⧸ pPrimeCore 2 ↥(T.subgroupOf M)) ≠ ⊥ := by
  have hw'Z := mem_fusionZStar_of_mem_map (hTM hwT) hwZ
  have hw'T : (⟨w, hTM hwT⟩ : ↥M) ∈ T.subgroupOf M := mem_subgroupOf.mpr hwT
  have hw'2 : orderOf (⟨w, hTM hwT⟩ : ↥M) = 2 := by rw [Subgroup.orderOf_mk]; exact hw
  constructor
  · obtain ⟨hc', hc1⟩ := mk_mem_center_ne_one hw'Z hw'2
    intro h
    rw [h, mem_bot] at hc'
    exact hc1 hc'
  · have h2 : orderOf (⟨_, hw'T⟩ : ↥(T.subgroupOf M)) = 2 := by
      rw [Subgroup.orderOf_mk]; exact hw'2
    obtain ⟨hc', hc1⟩ := mk_mem_center_ne_one (mem_fusionZStar_of_mem hw'T hw'Z) h2
    intro h
    rw [h, mem_bot] at hc'
    exact hc1 hc'

theorem verticalCentralEsc_typQ
    (hP : TypPumpInput) (hP11 : L34CentralSLTwoFact) {q₀ : ℕ}
    (hq₀ : q₀ ∈ ({5, 7, 9} : Finset ℕ)) : VerticalCentralEsc (TypQ q₀) TypL16 := by
  intro H _ _ hH M hM x hx hxN T hTM hTC hTpc hTQ w hw hwT hwZ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hc, hT'C, hT'p⟩ := exists_conj_mulAut hx hxN hTM hTC hTpc
  obtain ⟨hZM, hZT⟩ := center_ne_bot_of_mem hTM hw hwT hwZ
  have hTQ' : TypQ q₀ ↥(T.subgroupOf M) :=
    coreInvariant_typQ q₀ _ _ ⟨Sol78.coreQuotCongr (subgroupOfEquivOfLe hTM).symm⟩ hTQ
  have hTC' : TypC ↥(T.subgroupOf M) := hTQ'.1.elim Or.inl fun h => Or.inr (Or.inl h)
  have hMq2 : HarrisLit.IsTwoQuasisimple ↥M :=
    ((HarrisLit.isTwoComponent_iff_isPComponent M).mpr hM).2
  have hdvd : q₀ * (q₀ ^ 2 - 1) ∣ Nat.card (↥M ⧸ pPrimeCore 2 ↥M) :=
    hTQ.2.trans (card_quot_dvd_of_le hTM)
  rcases hP ↥M (hH.subgroup M) hMq2 hZM c hc _ hT'C hT'p hZT hTC' with hodd | h2A | ⟨hL, hZ⟩
  · exact Or.inl ⟨Or.inl hodd, hdvd⟩
  · exact Or.inl ⟨Or.inr h2A, hdvd⟩
  · have hw'2 : orderOf (⟨w, hTM hwT⟩ : ↥M) = 2 := by rw [Subgroup.orderOf_mk]; exact hw
    exact Or.inr (typL16_of_fixed hP11 hMq2.2 hL hZ c hc hT'C hT'p hq₀ hTQ' hw'2
      (mem_subgroupOf.mpr hwT) (mem_fusionZStar_of_mem_map (hTM hwT) hwZ))

end CFSG.ComponentClassification.GS82PumpInputs.Residue
