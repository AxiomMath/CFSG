module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GeneratorRank
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Frattini.Core
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.HarrisEnd

open CFSG Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem exists_closure_eq_of_sup {P A : Subgroup G} (hP : IsPGroup 2 P)
    (hA2 : ∀ a ∈ A, a ^ 2 = 1) (hAA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hPA : ∀ x ∈ P, ∀ a ∈ A, x * a = a * x) (hdisj : P ⊓ A = ⊥) {k n : ℕ}
    (hAk : Nat.card A = 2 ^ k) {s : Finset G} (hs : s.card ≤ n)
    (hsc : closure (s : Set G) = P ⊔ A) :
    ∃ s' : Finset G, s'.card ≤ n - k ∧ closure (s' : Set G) = P := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (IsPGroup 2 ↥P) := ⟨hP⟩
  set Φ : Subgroup G := (frattini ↥P).map P.subtype with hΦdef
  have hΦP : Φ ≤ P := map_subtype_le _
  have hAnorm : A ≤ normalizer (P : Set G) := by
    intro a ha
    refine mem_normalizer_iff.mpr fun x => ?_
    constructor
    · intro hx
      rw [← hPA x hx a ha, mul_assoc, mul_inv_cancel, mul_one]
      exact hx
    · intro hx
      have hy := hPA _ hx a ha
      have : x = a * x * a⁻¹ :=
        calc x = a⁻¹ * ((a * x * a⁻¹) * a) := by group
          _ = a⁻¹ * (a * (a * x * a⁻¹)) := by rw [hy]
          _ = a * x * a⁻¹ := by group
      rw [this]
      exact hx
  have hdec : ∀ h ∈ P ⊔ A, ∃ x ∈ P, ∃ a ∈ A, h = x * a := by
    intro h hh
    have hh' : h ∈ ((P : Set G) * (A : Set G)) := by
      rw [← coe_mul_of_right_le_normalizer_left P A hAnorm]
      exact hh
    obtain ⟨x, hx, a, ha, rfl⟩ := hh'
    exact ⟨x, hx, a, ha, rfl⟩
  have hcommP : ∀ x ∈ P, ∀ y ∈ P, x * y * x⁻¹ * y⁻¹ ∈ Φ := by
    intro x hx y hy
    have hmem : (⟨x, hx⟩ : ↥P) * ⟨y, hy⟩ * (⟨x, hx⟩ : ↥P)⁻¹ * (⟨y, hy⟩ : ↥P)⁻¹ ∈ frattini ↥P :=
      commutator_le_frattini_of_isPGroup (R := ↥P) (p := 2)
        (Subgroup.commutator_mem_commutator (mem_top _) (mem_top _))
    exact ⟨_, hmem, rfl⟩
  have hsqP : ∀ x ∈ P, x ^ 2 ∈ Φ := by
    intro x hx
    exact ⟨_, pth_power_mem_frattini_of_isPGroup (R := ↥P) (p := 2) ⟨x, hx⟩, rfl⟩
  have hcomm : ∀ h₁ ∈ P ⊔ A, ∀ h₂ ∈ P ⊔ A, h₁ * h₂ * h₁⁻¹ * h₂⁻¹ ∈ Φ := by
    intro h₁ hh₁ h₂ hh₂
    obtain ⟨x, hx, a, ha, rfl⟩ := hdec h₁ hh₁
    obtain ⟨y, hy, b, hb, rfl⟩ := hdec h₂ hh₂
    have e1 : a * y = y * a := (hPA y hy a ha).symm
    have e2 : a * b = b * a := hAA a ha b hb
    have e3 : b * x = x * b := (hPA x hx b hb).symm
    have : x * a * (y * b) * (x * a)⁻¹ * (y * b)⁻¹ = x * y * x⁻¹ * y⁻¹ := by
      calc x * a * (y * b) * (x * a)⁻¹ * (y * b)⁻¹
          = x * (a * y) * b * a⁻¹ * x⁻¹ * b⁻¹ * y⁻¹ := by group
        _ = x * y * (a * b) * a⁻¹ * x⁻¹ * b⁻¹ * y⁻¹ := by rw [e1]; group
        _ = x * y * b * x⁻¹ * b⁻¹ * y⁻¹ := by rw [e2]; group
        _ = x * y * x⁻¹ * y⁻¹ := by
          rw [show x * y * b * x⁻¹ * b⁻¹ * y⁻¹ = x * y * (b * x⁻¹) * b⁻¹ * y⁻¹ by group]
          have e4 : b * x⁻¹ = x⁻¹ * b :=
            calc b * x⁻¹ = x⁻¹ * (x * b) * x⁻¹ := by group
              _ = x⁻¹ * (b * x) * x⁻¹ := by rw [e3]
              _ = x⁻¹ * b := by group
          rw [e4]; group
    rw [this]
    exact hcommP x hx y hy
  have hsq : ∀ h ∈ P ⊔ A, h ^ 2 ∈ Φ := by
    intro h hh
    obtain ⟨x, hx, a, ha, rfl⟩ := hdec h hh
    have e : (x * a) ^ 2 = x ^ 2 := by
      rw [sq, sq, show x * a * (x * a) = x * (a * x) * a by group, ← hPA x hx a ha,
        show x * (x * a) * a = x * x * (a * a) by group, ← sq a, hA2 a ha, mul_one]
    rw [e]
    exact hsqP x hx
  have hΦH : Φ ≤ P ⊔ A := hΦP.trans le_sup_left
  set H : Subgroup G := P ⊔ A with hHdef
  set N : Subgroup ↥H := Φ.subgroupOf H with hNdef
  have hN : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [hNdef, mem_subgroupOf] at hn ⊢
    have e : ((g * n * g⁻¹ : ↥H) : G) = ((g : G) * n * (g : G)⁻¹ * (n : G)⁻¹) * n := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
    exact Φ.mul_mem (hcomm _ g.2 _ n.2) hn
  have hQcomm : ∀ q₁ q₂ : ↥H ⧸ N, q₁ * q₂ = q₂ * q₁ := by
    intro q₁ q₂
    induction q₁ using QuotientGroup.induction_on with | H h₁ => ?_
    induction q₂ using QuotientGroup.induction_on with | H h₂ => ?_
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, hNdef, mem_subgroupOf]
    have e : (((h₁ * h₂)⁻¹ * (h₂ * h₁) : ↥H) : G) =
        (h₂ : G)⁻¹ * (h₁ : G)⁻¹ * ((h₂ : G)⁻¹)⁻¹ * ((h₁ : G)⁻¹)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
    exact hcomm _ (H.inv_mem h₂.2) _ (H.inv_mem h₁.2)
  have hQsq : ∀ q : ↥H ⧸ N, q ^ 2 = 1 := by
    intro q
    induction q using QuotientGroup.induction_on with | H h => ?_
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, hNdef, mem_subgroupOf]
    simpa using hsq _ h.2
  have hQel : IsElementaryAbelian 2 (↥H ⧸ N) :=
    { toIsMulCommutative := ⟨⟨hQcomm⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hQsq }
  have hrankH : Group.rank ↥H ≤ n := by
    have h1 : Group.rank ↥(closure (s : Set G)) ≤ s.card := Subgroup.rank_closure_finset_le_card s
    rw [Subgroup.rank_congr hsc] at h1
    exact h1.trans hs
  have hrankQ : Group.rank (↥H ⧸ N) ≤ n :=
    (Group.rank_le_of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)).trans
      hrankH
  have hQcard : Nat.card (↥H ⧸ N) ≤ 2 ^ n := by
    rw [elementaryAbelian_card_eq_pow_generatorRank (p := 2), generatorRank_eq_group_rank]
    exact Nat.pow_le_pow_right (by norm_num) hrankQ
  have hcardH : Nat.card ↥H = Nat.card P * Nat.card A := by
    refine GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer P A hAnorm ?_
    rw [disjoint_iff]
    exact hdisj
  have hcardN : Nat.card N = Nat.card (frattini ↥P) := by
    rw [hNdef, Nat.card_congr (subgroupOfEquivOfLe hΦH).toEquiv, hΦdef,
      card_map_of_injective P.subtype_injective]
  have hcardHN := Subgroup.card_eq_card_quotient_mul_card_subgroup N
  have hcardPF := Subgroup.card_eq_card_quotient_mul_card_subgroup (frattini ↥P)
  have hFpos : 0 < Nat.card (frattini ↥P) := Nat.card_pos
  have hQeq : Nat.card (↥H ⧸ N) = Nat.card (↥P ⧸ frattini ↥P) * 2 ^ k := by
    have h1 : Nat.card (↥H ⧸ N) * Nat.card (frattini ↥P) =
        Nat.card (↥P ⧸ frattini ↥P) * 2 ^ k * Nat.card (frattini ↥P) :=
      calc Nat.card (↥H ⧸ N) * Nat.card (frattini ↥P) = Nat.card (↥H ⧸ N) * Nat.card N := by
            rw [hcardN]
        _ = Nat.card ↥H := hcardHN.symm
        _ = Nat.card P * Nat.card A := hcardH
        _ = Nat.card (↥P ⧸ frattini ↥P) * Nat.card (frattini ↥P) * 2 ^ k := by
            rw [hcardPF, hAk]
        _ = Nat.card (↥P ⧸ frattini ↥P) * 2 ^ k * Nat.card (frattini ↥P) := by ring
    exact Nat.eq_of_mul_eq_mul_right hFpos h1
  have hPel := isElementaryAbelian_quotient_frattini (R := ↥P) (p := 2)
  have hPcard : Nat.card (↥P ⧸ frattini ↥P) = 2 ^ generatorRank (↥P ⧸ frattini ↥P) :=
    elementaryAbelian_card_eq_pow_generatorRank (p := 2) _
  have hburn : generatorRank ↥P ≤ generatorRank (↥P ⧸ frattini ↥P) :=
    generatorRank_le_generatorRank_quotient_frattini (p := 2) ↥P
  have hle : generatorRank ↥P + k ≤ n := by
    have h2 : 2 ^ (generatorRank (↥P ⧸ frattini ↥P) + k) ≤ 2 ^ n := by
      rw [pow_add, ← hPcard, ← hQeq]
      exact hQcard
    have h3 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h2
    omega
  obtain ⟨S, hScard, hStop⟩ := Group.rank_spec ↥P
  refine ⟨S.map ⟨P.subtype, P.subtype_injective⟩, ?_, ?_⟩
  · rw [Finset.card_map, hScard, ← generatorRank_eq_group_rank]
    omega
  · rw [Finset.coe_map, Function.Embedding.coeFn_mk, ← MonoidHom.map_closure, hStop,
      ← MonoidHom.range_eq_map, range_subtype]

end CFSG.ComponentClassification.HarrisLit.HarrisEnd
