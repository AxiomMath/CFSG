module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLBalanceTools
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitGW36
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma22
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCoreInner
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitQuotientChain
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitThm46Four
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinConvention
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinInteraction
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreQuotient
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bOrbit
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.SignalizerFunctor

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup
open scoped commutatorElement

theorem range_eq_bot_of_le_odd {H Y : Type} [Group H] [Finite H] [Group Y] [Finite Y]
    {L : Subgroup H} (hL : IsPComponent 2 L) (g : ↥L →* Y) {U : Subgroup Y}
    (hU : Odd (Nat.card U)) (hgU : g.range ≤ U) : g.range = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hres := CatalogueBPrimeJoin.primeResidual_eq_top_of_pComponent 2 L hL
  have hker : g.ker = ⊤ := by
    rw [eq_top_iff, ← hres]
    apply sSup_le
    intro P hP x hx
    rw [MonoidHom.mem_ker]
    exact eq_one_of_mem_of_odd (hP.map g) hU (mem_map_of_mem g hx) (hgU ⟨x, rfl⟩)
  rw [eq_bot_iff]
  rintro _ ⟨x, rfl⟩
  have hx : x ∈ g.ker := hker ▸ mem_top x
  exact (mem_bot).mpr (MonoidHom.mem_ker.mp hx)

variable {H : Type} [Group H] [Finite H]

local notation "π" => QuotientGroup.mk' (pPrimeCore 2 H)

omit [Finite H] in
theorem isComponent_map_mk_of_isPComponent {L : Subgroup H} (hL : IsPComponent 2 L) :
    CFSG.IsComponent (L.map π) ∧ ∃ k₁ ∈ L.map π, ∃ k₂ ∈ L.map π, k₁ * k₂ ≠ k₂ * k₁ := by
  obtain ⟨K₀, hK₀, -, hLK₀, -⟩ := hL
  have hK : CFSG.IsComponent (L.map π) := by rw [hLK₀]; exact hK₀
  refine ⟨hK, ?_⟩
  obtain ⟨u, v, huv⟩ := hK.1.2.2
  obtain ⟨k₁, rfl⟩ := QuotientGroup.mk_surjective u
  obtain ⟨k₂, rfl⟩ := QuotientGroup.mk_surjective v
  refine ⟨k₁, k₁.2, k₂, k₂.2, fun h => huv ?_⟩
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, show k₁ * k₂ = k₂ * k₁ from Subtype.ext h]

theorem oddCore_map_mk_facts {a : H} (ha : orderOf a = 2) {L : Subgroup H}
    (hXL : oddCoreOfCentralizer a ≤ normalizer (L : Set H)) :
    Odd (Nat.card ((oddCoreOfCentralizer a).map π)) ∧
      (oddCoreOfCentralizer a).map π ≤ normalizer ((L.map π : Subgroup _) : Set _) ∧
      centralizer ({π a} : Set (H ⧸ pPrimeCore 2 H)) ≤
        normalizer (((oddCoreOfCentralizer a).map π : Subgroup _) : Set _) ∧
      (oddCoreOfCentralizer a).map π ≤ centralizer ({π a} : Set (H ⧸ pPrimeCore 2 H)) := by
  refine ⟨Odd.of_dvd_nat (odd_card_oddCoreOfCentralizer a)
    (Subgroup.card_map_dvd (H := oddCoreOfCentralizer a) π), ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact le_normalizer_map π (mem_map_of_mem π (hXL hx))
  · intro c hc
    rw [← map_centralizer_mk ha] at hc
    obtain ⟨c₀, hc₀, rfl⟩ := hc
    exact le_normalizer_map π (mem_map_of_mem π (mem_normalizer_oddCoreOfCentralizer hc₀))
  · rintro _ ⟨x, hx, rfl⟩
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      mem_centralizer_singleton_iff.mp (oddCoreOfCentralizer_le_centralizer a hx)]

theorem le_centralizer_map_of_commutator_mem {a : H} (ha : orderOf a = 2) {L : Subgroup H}
    (hL : IsPComponent 2 L) (hXL : oddCoreOfCentralizer a ≤ normalizer (L : Set H))
    (hLa : ∀ x ∈ L, x⁻¹ * a⁻¹ * x * a ∈ (pPrimeCore 2 L).map L.subtype) :
    L.map π ≤ centralizer (((oddCoreOfCentralizer a).map π : Subgroup _) : Set _) := by
  obtain ⟨hXodd, hXK, hCa, -⟩ := oddCore_map_mk_facts ha hXL
  obtain ⟨hK, hKnc⟩ := isComponent_map_mk_of_isPComponent hL
  have hLsub : L.IsSubnormal := by
    obtain ⟨-, -, h, -, -⟩ := id hL
    exact h
  have hKp : ⁅L.map π, L.map π⁆ = L.map π := Subgroup.isPerfect_iff.mp hK.1.1
  have hKa : L.map π ≤ centralizer ({π a} : Set (H ⧸ pPrimeCore 2 H)) := by
    rintro _ ⟨l, hl, rfl⟩
    have h1 : l⁻¹ * a⁻¹ * l * a ∈ pPrimeCore 2 H :=
      Walter.map_pPrimeCore_le_of_isSubnormal hLsub (hLa l hl)
    have h2 : π (l⁻¹ * a⁻¹ * l * a) = 1 := (QuotientGroup.eq_one_iff _).mpr h1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h2
    rw [mem_centralizer_singleton_iff]
    calc π l * π a = π a * π l * ((π l)⁻¹ * (π a)⁻¹ * π l * π a) := by group
      _ = π a * π l := by rw [h2, mul_one]
  refine le_centralizer_of_odd_of_normalizes hXodd hXK (hKa.trans hCa) hKp ?_
  intro U hUK hKU hUodd u hu d hd
  have hn : (U.subgroupOf (L.map π)).Normal :=
    (normal_subgroupOf_iff_le_normalizer hUK).mpr hKU
  rcases le_center_or_eq_top_of_normal hK.1 hn with h | h
  · have h1 := mem_center_iff.mp
      (h (show (⟨u, hUK hu⟩ : ↥(L.map π)) ∈ U.subgroupOf (L.map π) from hu)) ⟨d, hd⟩
    exact (congrArg Subtype.val h1).symm
  · exfalso
    have hKU' : L.map π ≤ U := subgroupOf_eq_top.mp h
    have h1 := range_eq_bot_of_le_odd hL ((π).comp L.subtype) hUodd
      (by rw [MonoidHom.range_comp, range_subtype]; exact hKU')
    rw [MonoidHom.range_comp, range_subtype] at h1
    obtain ⟨k₁, hk₁, k₂, hk₂, hne⟩ := hKnc
    rw [h1, mem_bot] at hk₁ hk₂
    exact hne (by rw [hk₁, hk₂])

theorem range_eq_bot_of_map_mk {L : Subgroup H} (hL : IsPComponent 2 L) {Y : Type}
    [Group Y] [Finite Y] (g : ↥(L.map π) →* Y) {U : Subgroup Y} (hU : Odd (Nat.card U))
    (hgU : g.range ≤ U) : g.range = ⊥ := by
  have hs : ((π).subgroupMap L).range = ⊤ :=
    MonoidHom.range_eq_top.mpr ((π).subgroupMap_surjective L)
  have h1 := range_eq_bot_of_le_odd hL (g.comp ((π).subgroupMap L)) hU
    (by rw [MonoidHom.range_comp, hs, ← MonoidHom.range_eq_map]; exact hgU)
  rwa [MonoidHom.range_comp, hs, ← MonoidHom.range_eq_map] at h1

theorem le_centralizer_map_of_conjugate_ne {a : H} (ha : orderOf a = 2) {L : Subgroup H}
    (hL : IsPComponent 2 L) (hXL : oddCoreOfCentralizer a ≤ normalizer (L : Set H))
    (hLa : conjugate L a ≠ L) :
    L.map π ≤ centralizer (((oddCoreOfCentralizer a).map π : Subgroup _) : Set _) := by
  obtain ⟨hXodd, hXK, hCa, hXa⟩ := oddCore_map_mk_facts ha hXL
  obtain ⟨hK, hKnc⟩ := isComponent_map_mk_of_isPComponent hL
  have hLsub : L.IsSubnormal := by
    obtain ⟨-, -, h, -, -⟩ := id hL
    exact h
  have hL' := UnbalancedLayer.isPComponent_conjugate hL a
  obtain ⟨-, -, hcomm, -⟩ := (CatalogueBPrimeJoin.distinct_p_components_core_commutation 2
    Nat.prime_two L (conjugate L a) hL hL').2 (Ne.symm hLa)
  have hKK' : ∀ k ∈ L.map π, ∀ k' ∈ (conjugate L a).map π, k * k' = k' * k := by
    rintro _ ⟨l, hl, rfl⟩ _ ⟨l', hl', rfl⟩
    have h1 : ⁅l, l'⁆ ∈ pPrimeCore 2 H := Walter.map_pPrimeCore_le_of_isSubnormal hLsub
      (mem_inf.mp (hcomm (commutator_mem_commutator hl hl'))).1
    have h2 : π ⁅l, l'⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr h1
    rwa [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h2
  have hbK : ∀ k ∈ L.map π, (π a)⁻¹ * k * π a ∈ (conjugate L a).map π := by
    rintro _ ⟨l, hl, rfl⟩
    refine ⟨a⁻¹ * l * a, ⟨l, hl, ?_⟩, by rw [map_mul, map_mul, map_inv]⟩
    show a⁻¹ * l * a⁻¹⁻¹ = a⁻¹ * l * a
    rw [inv_inv]
  have hb : π a * π a = 1 := by
    rw [← map_mul, ← sq, ← ha, pow_orderOf_eq_one, map_one]
  exact le_centralizer_of_diagonal hK.1 hKnc (fun g U hU hgU => range_eq_bot_of_map_mk hL g hU hgU)
    hb hKK' hbK hXodd hXK hCa hXa

theorem commutator_le_of_le_centralizer_map {X L : Subgroup H}
    (hXL : X ≤ normalizer (L : Set H))
    (hcen : L.map π ≤ centralizer ((X.map π : Subgroup _) : Set _)) :
    ⁅X, L⁆ ≤ (pPrimeCore 2 L).map L.subtype := by
  have hXLT : ⁅X, L⁆ ≤ L ⊓ pPrimeCore 2 H := by
    rw [commutator_le]
    intro x hx l hl
    refine mem_inf.mpr ⟨?_, ?_⟩
    · rw [commutatorElement_def]
      exact mul_mem ((mem_normalizer_iff.mp (hXL hx) l).mp hl) (inv_mem hl)
    · have h1 := mem_centralizer_iff.mp (hcen (mem_map_of_mem π hl)) (π x)
        (mem_map_of_mem π hx)
      have h2 : π ⁅x, l⁆ = 1 := by
        rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        exact h1
      exact (QuotientGroup.eq_one_iff _).mp h2
  refine hXLT.trans ?_
  have hTL : L ⊓ pPrimeCore 2 H ≤ L := inf_le_left
  have hTn : ((L ⊓ pPrimeCore 2 H).subgroupOf L).Normal := ⟨fun t ht l => by
    rw [mem_subgroupOf] at ht ⊢
    have ht' := mem_inf.mp ht
    rw [coe_mul, coe_mul, coe_inv]
    exact mem_inf.mpr ⟨mul_mem (mul_mem l.2 ht'.1) (inv_mem l.2),
      (inferInstance : (pPrimeCore 2 H).Normal).conj_mem _ ht'.2 _⟩⟩
  have hTodd : Nat.Coprime 2 (Nat.card ((L ⊓ pPrimeCore 2 H).subgroupOf L)) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hTL).toEquiv]
    exact Nat.Coprime.coprime_dvd_right (card_dvd_of_le inf_le_right) pPrimeCore_coprime_card
  have hle : (L ⊓ pPrimeCore 2 H).subgroupOf L ≤ pPrimeCore 2 L := le_sSup ⟨hTn, hTodd⟩
  intro t ht
  exact ⟨⟨t, hTL ht⟩, hle ht, rfl⟩

theorem footeLBalanceInput_holds : FooteLBalanceInput := by
  intro H _ _ a ha L hL
  have hB : IsPGroup 2 (zpowers a) := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha,
    pow_one])
  have hc : centralizer ((zpowers a : Subgroup H) : Set H) = centralizer ({a} : Set H) := by
    rw [zpowers_eq_closure, centralizer_closure]
  have hXL : oddCoreOfCentralizer a ≤ normalizer (L : Set H) := by
    have h := GrSLit.oddCore_centralizer_le_normalizer hB hL
    rw [hc] at h
    exact h
  refine ⟨hXL, fun hcase => commutator_le_of_le_centralizer_map hXL ?_⟩
  rcases hcase with h | h
  · exact le_centralizer_map_of_conjugate_ne ha hL hXL h
  · exact le_centralizer_map_of_commutator_mem ha hL hXL h

end CFSG.ComponentClassification.FooteLit
