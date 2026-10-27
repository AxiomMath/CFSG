module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.S622Defs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KG2024

open Subgroup CFSG.Open
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
  (relPPrimeCore_normal coprime_card_relPPrimeCore)

theorem rankThreePrimeCore_eq_of_section {A : Type} [Group A] [Finite A] {p : ℕ} (hp : p.Prime)
    {Y D : Subgroup A} (hs : S622IsSimpleSection Y D) (hD : Nat.Coprime p (Nat.card D))
    {z : A} (hzY : z ∈ Y) (hz : orderOf z = p) : rankThreePrimeCore p Y = D := by
  obtain ⟨hDY, hDn, -, hmin, -⟩ := hs
  have hDle : D ≤ rankThreePrimeCore p Y := le_sSup ⟨hDY, hDn, hD⟩
  have hRY : rankThreePrimeCore p Y ≤ Y := sSup_le fun _ hN => hN.1
  have hRn : ((rankThreePrimeCore p Y).subgroupOf Y).Normal := relPPrimeCore_normal hp Y
  rcases hmin _ hDle hRY hRn with h | h
  · exact h
  · exfalso
    have hcop : Nat.Coprime p (Nat.card (rankThreePrimeCore p Y)) :=
      coprime_card_relPPrimeCore hp Y
    rw [h] at hcop
    have hdvd : p ∣ Nat.card Y := hz ▸ Subgroup.orderOf_dvd_natCard Y hzY
    exact hp.one_lt.ne' (hcop.eq_one_of_dvd hdvd)

theorem exists_minimal_invariant {G : Type*} [Group G] [Finite G] (z : G) (U : Subgroup G)
    (hU : U ≠ ⊥) (hinv : ∀ u, u ∈ U ↔ z * u * z⁻¹ ∈ U) :
    ∃ T : Subgroup G, T ≤ U ∧ T ≠ ⊥ ∧ (∀ t, t ∈ T ↔ z * t * z⁻¹ ∈ T) ∧
      ∀ T₁ : Subgroup G, T₁ ≤ T → (∀ t, t ∈ T₁ ↔ z * t * z⁻¹ ∈ T₁) → T₁ = ⊥ ∨ T₁ = T := by
  classical
  obtain ⟨T, hT, hmin⟩ := WellFounded.has_min (wellFounded_lt (α := Subgroup G))
    {T : Subgroup G | T ≤ U ∧ T ≠ ⊥ ∧ ∀ t, t ∈ T ↔ z * t * z⁻¹ ∈ T} ⟨U, le_rfl, hU, hinv⟩
  refine ⟨T, hT.1, hT.2.1, hT.2.2, fun T₁ hle hinv₁ => ?_⟩
  by_cases h : T₁ = ⊥
  · exact Or.inl h
  · right
    by_contra hne
    exact hmin T₁ ⟨hle.trans hT.1, h, hinv₁⟩ (lt_of_le_of_ne hle hne)

theorem mem_normalizer_of_commute {G : Type*} [Group G] {T : Subgroup G} {y : G}
    (h : ∀ t ∈ T, y * t = t * y) : y ∈ normalizer (T : Set G) := by
  rw [Subgroup.mem_set_normalizer_iff]
  intro g
  constructor
  · intro hg
    have hg' : g ∈ T := hg
    show y * g * y⁻¹ ∈ T
    rw [h g hg']
    simpa using hg'
  · intro hg
    have hg' : y * g * y⁻¹ ∈ T := hg
    have h1 : y * (y * g * y⁻¹) = y * g := by rw [h _ hg']; group
    have h2 : y * g * y⁻¹ = g := mul_left_cancel h1
    show g ∈ T
    rw [← h2]
    exact hg'

theorem mem_normalizer_of_forward {G : Type*} [Group G] {T : Subgroup G} {y : G}
    (h1 : ∀ t ∈ T, y * t * y⁻¹ ∈ T) (h2 : ∀ t ∈ T, y⁻¹ * t * y ∈ T) :
    y ∈ normalizer (T : Set G) := by
  rw [Subgroup.mem_set_normalizer_iff]
  intro g
  constructor
  · intro hg
    exact h1 g hg
  · intro hg
    have := h2 _ hg
    have e : y⁻¹ * (y * g * y⁻¹) * y = g := by group
    rw [e] at this
    exact this

theorem isSimpleSection_bot {A : Type} [Group A] [Finite A] {Y : Subgroup A}
    (hY : IsSimpleGroup ↥Y) {p : ℕ} (hp5 : 5 ≤ p) (hpY : p ∣ Nat.card ↥Y)
    (h3 : 3 ∣ Nat.card ↥Y) : S622IsSimpleSection Y ⊥ := by
  have hab : ∃ x y : ↥Y, x * y ≠ y * x := by
    by_contra hcon
    push Not at hcon
    letI : CommGroup ↥Y := { (inferInstance : Group ↥Y) with mul_comm := hcon }
    have hprime := IsSimpleGroup.prime_card (α := ↥Y)
    have e1 := hprime.eq_one_or_self_of_dvd p hpY
    have e2 := hprime.eq_one_or_self_of_dvd 3 h3
    omega
  obtain ⟨x, y, hxy⟩ := hab
  refine ⟨bot_le, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.bot_subgroupOf]
    infer_instance
  · intro h
    apply hxy
    have hx : (x : A) ∈ (⊥ : Subgroup A) := by rw [h]; exact x.2
    have hy : (y : A) ∈ (⊥ : Subgroup A) := by rw [h]; exact y.2
    rw [Subgroup.mem_bot] at hx hy
    exact Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, hx, hy])
  · intro N _ hNY hN
    rcases hY.eq_bot_or_eq_top_of_normal (N.subgroupOf Y) with h | h
    · left
      refine le_antisymm (fun n hn => ?_) bot_le
      have : (⟨n, hNY hn⟩ : ↥Y) ∈ N.subgroupOf Y := hn
      rw [h, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
    · right
      refine le_antisymm hNY fun n hn => ?_
      have : (⟨n, hn⟩ : ↥Y) ∈ N.subgroupOf Y := by rw [h]; exact Subgroup.mem_top _
      exact this
  · intro hall
    apply hxy
    have := hall x x.2 y y.2
    rw [Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at this
    exact Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, this])

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KG2024
