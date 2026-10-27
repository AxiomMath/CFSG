module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB516PumpQuot
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog516Pump
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aOddQuotIso
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bOrbit
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog516
public import CFSG.Open.QuasithinDefs

public section

namespace CFSG.ComponentClassification.GSThmB.Pump516

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

theorem centralizer_subgroupOf_eq {G : Type*} [Group G] {X : Subgroup G} {g : G} (hg : g ∈ X) :
    (centralizer ({g} : Set G)).subgroupOf X = centralizer ({(⟨g, hg⟩ : X)} : Set X) := by
  ext x
  rw [mem_subgroupOf, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  exact ⟨fun h1 => Subtype.ext h1, fun h1 => congrArg Subtype.val h1⟩

variable {X : Type} [Group X] [Finite X]

local notation "π" => QuotientGroup.mk' (pPrimeCore 2 X)

theorem map_ne_one_of_orderOf_eq_two {u : X} (hu : orderOf u = 2) : π u ≠ 1 := by
  intro h1
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  have h2 := orderOf_dvd_natCard (⟨u, h1⟩ : ↥(pPrimeCore 2 X))
  rw [Subgroup.orderOf_mk, hu] at h2
  exact Nat.not_even_iff_odd.mpr OddQuot.odd_card_pPrimeCore (even_iff_two_dvd.mpr h2)

theorem exists_pComponent_of_pumpUp (hX : LBalance.SchreierSections X) {β a b : X}
    (hPump : ∀ L₀ : Subgroup (X ⧸ pPrimeCore 2 X), IsComponent L₀ →
      π β ∈ normalizer (L₀ : Set (X ⧸ pPrimeCore 2 X)) →
        CF516PumpUpAt (X ⧸ pPrimeCore 2 X) L₀ (π β)) (hβ : ∃ n : ℕ, β ^ 2 ^ n = 1)
    (ha2 : a * a = 1) (hbZ : b ∈ center X) {K J JB : Subgroup X}
    (hKC : K ≤ centralizer ({β} : Set X))
    (hK : IsPComponent 2 (K.subgroupOf (centralizer ({β} : Set X))))
    (hJC : J ≤ centralizer ({a} : Set X))
    (hJ : IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set X))))
    (habK : a * b ∈ K) (hab2 : orderOf (a * b) = 2) (hJBK : JB ≤ K) (hJBJ : JB ≤ J)
    (hJBp : ⁅JB, JB⁆ = JB) (hJB1 : JB ≠ ⊥) (hJsup : J ≤ JB ⊔ oddCoreIn J)
    (hβJ : β ∈ coreActionKernel J)
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hKt : (p ^ f % 4 = 3 ∧ ∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = p ^ f ∧
          Nonempty (K ⧸ pPrimeCore 2 K ≃* StatedProj (StatedSL 4 F))) ∨
        (p ^ f % 4 = 1 ∧ ∃ (F : Type) (_ : Field F), UnitaryFieldData p f F ∧
          Nonempty (K ⧸ pPrimeCore 2 K ≃* StatedProj (StatedSU 4 (p ^ f) F))))
    (hJt : Blueprint.LieModel (J ⧸ pPrimeCore 2 J) .PSL 2 p (2 * f)) :
    ∃ L : Subgroup X, IsPComponent 2 L ∧ K ≤ L ∧ L ≤ K ⊔ pPrimeCore 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Xb := X ⧸ pPrimeCore 2 X
  have hker := OddQuot.not_two_dvd_card_ker (H := X)
  have ha : ∃ n : ℕ, a ^ 2 ^ n = 1 := ⟨1, by rw [pow_one, pow_two, ha2]⟩
  obtain ⟨hKbC, hKb⟩ := isPComponent_map_centralizer hβ hKC hK
  obtain ⟨hJbC, hJb⟩ := isPComponent_map_centralizer ha hJC hJ
  have hKE : K.map π ≤ layer Xb :=
    (map_mono (le_pLayer_of_isPComponent_centralizer hX hβ hKC hK)).trans map_pLayer_le_layer
  have hJE : J.map π ≤ layer Xb :=
    (map_mono (le_pLayer_of_isPComponent_centralizer hX ha hJC hJ)).trans map_pLayer_le_layer
  have hbZ' : ∀ y : Xb, y * π b = π b * y := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 X) y
    rw [← map_mul, ← map_mul, (mem_center_iff.mp hbZ x)]
  have hbN : ∀ L : Subgroup Xb, π b ∈ normalizer (L : Set Xb) := fun L =>
    centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun y _ => hbZ' y)
  have haN : ∀ L : Subgroup Xb, IsComponent L → π a ∈ normalizer (L : Set Xb) := by
    intro L hL
    have h1 : π (a * b) ∈ normalizer (L : Set Xb) :=
      layer_le_normalizer hL (hKE (mem_map_of_mem π habK))
    have h2 : π a = π (a * b) * (π b)⁻¹ := by rw [map_mul, mul_inv_cancel_right]
    rw [h2]
    exact mul_mem h1 (inv_mem (hbN L))
  obtain ⟨L₀, hL₀, hJL₀⟩ := exists_isComponent_le haN hJbC hJb hJE
  have hKp : ⁅K, K⁆ = K :=
    Subgroup.isPerfect_iff.mp (B5a.isPerfect_of_isPComponent_subgroupOf hKC hK)
  have hJBb : ¬ JB.map π ≤ (pPrimeCore 2 ↥(K.map π)).map (K.map π).subtype := by
    intro hle
    have hodd : Odd (Nat.card ↥((pPrimeCore 2 ↥(K.map π)).map (K.map π).subtype)) := by
      rw [card_map_of_injective (K.map π).subtype_injective]
      exact OddQuot.odd_card_pPrimeCore
    have h1 := eq_bot_of_perfect_of_le_odd (by rw [← map_commutator, hJBp]) hle hodd
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h1
    exact hJB1 (eq_bot_of_perfect_of_le_odd hJBp h1 OddQuot.odd_card_pPrimeCore)
  have hKL₀ : K.map π ≤ L₀ :=
    le_of_isPComponent_of_perfect hKbC hKb hL₀.2 (map_mono hJBK)
      ((map_mono hJBJ).trans hJL₀) (by rw [← map_commutator, hJBp]) hJBb
  have hKbp : ⁅K.map π, K.map π⁆ = K.map π := by rw [← map_commutator, hKp]
  have hKb1 : K.map π ≠ ⊥ := by
    intro hbot
    have := B5a.nontrivial_of_isPComponent_subgroupOf hKbC hKb
    rw [hbot] at this
    exact not_nontrivial _ this
  have hβN : π β ∈ normalizer (L₀ : Set Xb) :=
    mem_normalizer_of_le_centralizer hL₀ hKL₀ hKbp hKb1 hKbC
  have hKt' : (p ^ f % 4 = 3 ∧ ∃ (F : Type) (_ : Field F) (_ : Fintype F),
        Fintype.card F = p ^ f ∧
          Nonempty (↥(K.map π) ⧸ pPrimeCore 2 ↥(K.map π) ≃* StatedProj (StatedSL 4 F))) ∨
      (p ^ f % 4 = 1 ∧ ∃ (F : Type) (_ : Field F), UnitaryFieldData p f F ∧
        Nonempty (↥(K.map π) ⧸ pPrimeCore 2 ↥(K.map π) ≃*
          StatedProj (StatedSU 4 (p ^ f) F))) := by
    obtain ⟨e⟩ := OddQuot.nonempty_quotient_pPrimeCore_equiv π hker K
    rcases hKt with ⟨h4, F, i1, i2, hF, ⟨eF⟩⟩ | ⟨h4, F, i1, hF, ⟨eF⟩⟩
    · exact Or.inl ⟨h4, F, i1, i2, hF, ⟨e.symm.trans eF⟩⟩
    · exact Or.inr ⟨h4, F, i1, hF, ⟨e.symm.trans eF⟩⟩
  have hJt' : Blueprint.LieModel (↥(J.map π) ⧸ pPrimeCore 2 ↥(J.map π)) .PSL 2 p (2 * f) := by
    obtain ⟨e⟩ := OddQuot.nonempty_quotient_pPrimeCore_equiv π hker J
    exact OddQuot.lieModel_of_equiv e hJt
  have htK : π (a * b) ∈ K.map π := mem_map_of_mem π habK
  have ht2 : orderOf (π (a * b)) = 2 := by
    refine orderOf_eq_prime ?_ (map_ne_one_of_orderOf_eq_two hab2)
    rw [← map_pow, ← hab2, pow_orderOf_eq_one, map_one]
  have hCt : centralizer ({π (a * b)} : Set Xb) ≤ centralizer ({π a} : Set Xb) := by
    intro y hy
    rw [mem_centralizer_singleton_iff] at hy ⊢
    rw [map_mul] at hy
    have h1 : y * π a * π b = π a * y * π b := by
      calc y * π a * π b = y * (π a * π b) := by group
        _ = π a * π b * y := hy
        _ = π a * (π b * y) := by group
        _ = π a * (y * π b) := by rw [hbZ' y]
        _ = π a * y * π b := by group
    exact mul_right_cancel h1
  have hJt2 : J.map π ≤ centralizer ({π (a * b)} : Set Xb) := by
    intro y hy
    have h1 := mem_centralizer_singleton_iff.mp (hJbC hy)
    rw [mem_centralizer_singleton_iff, map_mul]
    calc y * (π a * π b) = (y * π a) * π b := by group
      _ = (π a * y) * π b := by rw [h1]
      _ = π a * (y * π b) := by group
      _ = π a * (π b * y) := by rw [hbZ' y]
      _ = π a * π b * y := by group
  have hJsup' : J.map π ≤ JB.map π ⊔ oddCoreIn (J.map π) := by
    rw [← OddQuot.map_oddCoreIn π hker J, ← Subgroup.map_sup]
    exact map_mono hJsup
  have hβJ' : π β ∈ coreActionKernel (J.map π) := by
    have hzN : zpowers β ≤ normalizer (J : Set X) :=
      zpowers_le.mpr (mem_coreActionKernel.mp hβJ).1
    have h1 := OddQuot.map_inf_coreActionKernel hzN
    have h2 : π β ∈ (zpowers β ⊓ coreActionKernel J).map π :=
      mem_map_of_mem π (mem_inf.mpr ⟨mem_zpowers β, hβJ⟩)
    rw [h1] at h2
    exact (mem_inf.mp h2).2
  have hKL : K.map π = L₀ := hPump L₀ hL₀ hβN p f hp hp2 hf (K.map π) (le_inf hKL₀ hKbC)
    (CatalogueBPrimeJoin.pComponent_subgroupOf_of_le (le_inf hKL₀ hKbC) inf_le_right hKb) hKt'
    (π (a * b)) htK ht2 (J.map π) (le_inf hJL₀ hJt2)
    (CatalogueBPrimeJoin.pComponent_subgroupOf_of_le (le_inf hJL₀ hJt2)
      (inf_le_right.trans hCt) hJb) hJt' hβJ' (JB.map π) (le_inf (map_mono hJBJ)
      (map_mono hJBK)) (by rw [← map_commutator, hJBp]) hJsup'
  exact exists_pComponent_of_map_eq hL₀ hKp hKL

end CFSG.ComponentClassification.GSThmB.Pump516
