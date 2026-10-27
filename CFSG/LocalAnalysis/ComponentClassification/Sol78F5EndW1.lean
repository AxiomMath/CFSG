module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.Goldschmidt.Steps.G37Basic
public import CFSG.Goldschmidt75.Comp26
public import CFSG.Goldschmidt75.Sig3Defs
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma22
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public noncomputable section

namespace CFSG.ComponentClassification.Sol78.F514

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools CFSG.Goldschmidt CFSG.Goldschmidt75 CFSG.Open

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_of_pow_odd_mem {X : Subgroup G} {g : G} {a m : ℕ} (hg : orderOf g = 2 ^ a)
    (hm : Odd m) (hgm : g ^ m ∈ X) : g ∈ X := by
  have hcop : m.Coprime (orderOf g) := by
    rw [hg]
    exact Nat.Coprime.pow_right a (Nat.coprime_two_right.mpr hm)
  obtain ⟨u, hu⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hu]
  exact pow_mem hgm u

omit [Finite G] in
theorem le_of_le_sup_commute {L X N : Subgroup G} (hLres : L ≤ oddResidualIn L)
    (hLXN : L ≤ X ⊔ N) (hNodd : Odd (Nat.card N)) (hNc : ∀ n ∈ N, ∀ x ∈ X, n * x = x * n) :
    L ≤ X := by
  refine hLres.trans ((closure_le _).mpr ?_)
  rintro g ⟨hgL, a, ha⟩
  have hNX : N ≤ normalizer (X : Set G) := by
    intro n hn
    refine mem_normalizer_iff.mpr fun y => ⟨fun hy => ?_, fun hy => ?_⟩
    · rw [hNc n hn y hy, mul_inv_cancel_right]
      exact hy
    · have h1 := hNc n hn _ hy
      have h2 : n * y * n⁻¹ = y := by
        calc n * y * n⁻¹ = n⁻¹ * (n * (n * y * n⁻¹)) := by group
          _ = n⁻¹ * ((n * y * n⁻¹) * n) := by rw [h1]
          _ = y := by group
      rw [← h2]
      exact hy
  obtain ⟨n, hn, x, hx, rfl⟩ := G37.mem_sup_of_le_normalizer hNX (by rw [sup_comm]; exact hLXN hgL)
  have hnx : Commute n x := hNc n hn x hx
  have hnm : n ^ Nat.card N = 1 := by
    have h1 := congrArg Subtype.val (pow_card_eq_one' (G := N) (x := ⟨n, hn⟩))
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at h1
  refine mem_of_pow_odd_mem ha hNodd ?_
  rw [hnx.mul_pow, hnm, one_mul]
  exact pow_mem hx _

omit [Finite G] in
theorem le_sup_oddCoreIn_of_normal {L X : Subgroup G} [IsSimpleGroup (L ⧸ pPrimeCore 2 L)]
    (hXL : X ≤ L) (hXn : ∀ l ∈ L, ∀ y ∈ X, l * y * l⁻¹ ∈ X) {x : G} (hxX : x ∈ X)
    (hxO : x ∉ oddCoreIn L) : L ≤ X ⊔ oddCoreIn L := by
  set π := QuotientGroup.mk' (pPrimeCore 2 L) with hπ
  set X' := (X.subgroupOf L).map π with hX'
  have hX'n : X'.Normal := by
    refine Subgroup.Normal.map ⟨fun y hy l => ?_⟩ π (QuotientGroup.mk'_surjective _)
    exact hXn l l.2 y hy
  have hX'top : X' = ⊤ := by
    rcases hX'n.eq_bot_or_eq_top with h | h
    · exfalso
      apply hxO
      have h1 : π ⟨x, hXL hxX⟩ ∈ X' := ⟨⟨x, hXL hxX⟩, hxX, rfl⟩
      rw [h, mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact ⟨_, h1, rfl⟩
    · exact h
  intro l hl
  have h1 : π ⟨l, hl⟩ ∈ X' := hX'top ▸ mem_top _
  obtain ⟨y, hy, hyl⟩ := h1
  rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hyl
  rw [show l = (y : G) * ((y : G)⁻¹ * l) by group]
  exact mul_mem (mem_sup_left hy) (mem_sup_right ⟨_, hyl, by simp⟩)

theorem le_centralizer_of_commute {L N : Subgroup G} [IsSimpleGroup (L ⧸ pPrimeCore 2 L)]
    (hLres : L ≤ oddResidualIn L) (hLN : L ≤ normalizer (N : Set G)) {t : G} (htL : t ∈ L)
    (htO : t ∉ oddCoreIn L) (htN : ∀ n ∈ N, n * t = t * n)
    (hO : ∀ o ∈ oddCoreIn L, ∀ x ∈ L ⊓ centralizer (N : Set G), o * x = x * o) :
    L ≤ centralizer (N : Set G) := by
  set X := L ⊓ centralizer (N : Set G) with hX
  have hXn : ∀ l ∈ L, ∀ y ∈ X, l * y * l⁻¹ ∈ X := by
    intro l hl y hy
    obtain ⟨hyL, hyC⟩ := mem_inf.mp hy
    refine mem_inf.mpr ⟨mul_mem (mul_mem hl hyL) (inv_mem hl), mem_centralizer_iff.mpr ?_⟩
    intro n hn
    have hn' : l⁻¹ * n * l ∈ N := by
      have h1 := (mem_normalizer_iff.mp (inv_mem (hLN hl)) n).mp hn
      rwa [inv_inv] at h1
    have h2 := mem_centralizer_iff.mp hyC _ hn'
    calc n * (l * y * l⁻¹) = l * ((l⁻¹ * n * l) * y) * l⁻¹ := by group
      _ = l * (y * (l⁻¹ * n * l)) * l⁻¹ := by rw [h2]
      _ = l * y * l⁻¹ * n := by group
  have htX : t ∈ X := mem_inf.mpr ⟨htL, mem_centralizer_iff.mpr fun n hn => htN n hn⟩
  have h1 := le_sup_oddCoreIn_of_normal inf_le_left hXn htX htO
  exact (le_of_le_sup_commute hLres h1 (odd_card_oddCoreIn L) hO).trans inf_le_right

theorem oddCoreIn_le_oddCent {a : G} {M : Subgroup G} (hMC : M ≤ centralizer ({a} : Set G))
    (hMn : centralizer ({a} : Set G) ≤ normalizer (M : Set G)) : oddCoreIn M ≤ oddCent a := by
  have hOC : oddCoreIn M ≤ centralizer ({a} : Set G) := (map_subtype_le _).trans hMC
  have hle : (oddCoreIn M).subgroupOf (centralizer ({a} : Set G)) ≤
      goldschmidtOddCore (centralizer ({a} : Set G)) := by
    refine le_sSup ⟨(normal_subgroupOf_iff_le_normalizer hOC).mpr
      fun c hc => mem_normalizer_oddCoreIn (hMn hc), ?_⟩
    rw [Nat.card_congr (subgroupOfEquivOfLe hOC).toEquiv]
    exact odd_card_oddCoreIn M
  intro x hx
  exact ⟨⟨x, hOC hx⟩, hle hx, rfl⟩

end CFSG.ComponentClassification.Sol78.F514
