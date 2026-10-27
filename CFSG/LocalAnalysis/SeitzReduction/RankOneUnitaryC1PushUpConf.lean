module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1PushUpTorus
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1Basic

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.GH74.Uniqueness.Bender

structure U3C1Cartan {G : Type} [Group G] (L T D : Subgroup G) (d : G) : Prop where
  mem : d ∈ D
  le : D ≤ L
  le_normalizer : D ≤ normalizer (szT₁ L T : Set G)
  inf_eq : szT₁ L T ⊓ D = ⊥
  odd : Odd (Nat.card D)
  trans : ∀ b ∈ szA₁ (szT₁ L T), ∀ b' ∈ szA₁ (szT₁ L T), b ≠ 1 → b' ≠ 1 →
    ∃ n : ℕ, (d ^ n)⁻¹ * b * d ^ n = b'
  conj : ∀ s ∈ T, ∃ n ∈ szT₁ L T, ∀ x ∈ D, (n⁻¹ * s) * x * (n⁻¹ * s)⁻¹ ∈ D

structure U3C1OuterConf (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G)
    (T R₂ D V : Subgroup G) (k : ℕ) : Prop where
  one_le : 1 ≤ k
  R₂_le : R₂ ≤ V
  le_centralizer : V ≤ centralizer (szT₁ L T : Set G)
  comm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x
  card : Nat.card V = (2 ^ f) ^ (k + 1)
  omega : ∀ x ∈ V, x ^ 2 = 1 → x ∈ szA₁ (szT₁ L T)
  pow : ∀ x ∈ V, x ^ 2 ^ (k + 1) = 1
  le : szA₁ (szT₁ L T) ≤ V
  inv : ∀ x ∈ V, t * x * t⁻¹ = x⁻¹
  T_le : T ≤ normalizer (V : Set G)
  D_le : D ≤ normalizer (V : Set G)

namespace U3C1OuterConf

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}
  {T R₂ D V : Subgroup G} {k : ℕ}

theorem mem_szA₁_of_conj_eq (hc : U3C1OuterConf G L f t T R₂ D V k) {u : G} (hu : u ∈ V)
    (htu : t * u * t⁻¹ = u) : u ∈ szA₁ (szT₁ L T) := by
  refine hc.omega u hu ?_
  have h1 : u⁻¹ = u := by rw [← hc.inv u hu, htu]
  rw [sq]
  calc u * u = u * u⁻¹ := by rw [h1]
    _ = 1 := mul_inv_cancel u

theorem sign (hc : U3C1OuterConf G L f t T R₂ D V k)
    (h : U3Start G L f t T) (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    {d : G} (hC : U3C1Cartan L T D d) :
    ∀ w ∈ T, w ^ 2 = 1 → w ∉ szT₁ L T ⊔ zpowers t →
      (∀ u ∈ V, w * u * w⁻¹ = u → u ∈ szA₁ (szT₁ L T)) ∨
        ∀ u ∈ V, u⁻¹ * (w * u * w⁻¹) ∈ szA₁ (szT₁ L T) := fun w hwT hw2 hwS =>
  h.sign_of_cartan hS2 hC.mem hC.le_normalizer hC.odd hC.trans hC.conj hc.comm hc.le_centralizer
    (by have := hc.one_le; omega) hc.card hc.pow hc.omega hc.D_le hc.T_le hwT hw2 hwS

theorem exists_pow_four_ne (hc : U3C1OuterConf G L f t T R₂ D V k)
    (h : U3Start G L f t T) (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hk : 2 ≤ k) : ∃ a ∈ V, ∃ b ∈ V, ∀ n : ℤ, (a ^ n * b) ^ 4 ≠ 1 ∧ (b ^ n * a) ^ 4 ≠ 1 := by
  obtain ⟨-, hA₁card, -⟩ := h.facts_of_card_sylow hS2
  have hq : 3 ≤ 2 ^ f :=
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h.two_le
  exact pushUp_exists_pow_four_ne hc.comm hq (by omega) hc.card hc.pow hc.omega
    (le_of_eq hA₁card)

end U3C1OuterConf

section Certificates

theorem U3Start.u3C1OuterConf_one {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ}
    {t : G} {T R₂ : Subgroup G} (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hinv : ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹) {D : Subgroup G}
    {d : G} (hC : U3C1Cartan L T D d) : U3C1OuterConf G L f t T R₂ D R₂ 1 := by
  obtain ⟨-, -, -, -, hNR₂, -⟩ := h.u3R2_canonical_of_card_sylow hS2 hR
  have hTA : normalizer (T : Set G) ≤ normalizer (szA L T t : Set G) :=
    h.normalizer_le_normalizer_szA_of_card_sylow hS2
  have ht : t ∈ centralizer (szA₁ (szT₁ L T) : Set G) :=
    centralizer_le (szA₁_le _) h.mem_centralizer_szT₁
  exact
    { one_le := le_rfl
      R₂_le := le_rfl
      le_centralizer := fun r hr => mem_centralizer_iff.mpr fun y hy => hR.commT₁ y hy r hr
      comm := hR.comm
      card := hR.card
      omega := fun r hr h2 => hR.mem_szA₁_of_sq_eq_one_of_inv hinv hr h2
      pow := fun r hr => hR.pow_four_eq_one_of_inv hr
      le := hR.le
      inv := hinv
      T_le := fun x hx => hNR₂ (hTA (Subgroup.le_normalizer hx))
      D_le := fun x hx => hNR₂ (SzPartition.mem_normalizer_sup_zpowers ht
        (normalizer_le_normalizer_inf_centralizer _ (hC.le_normalizer hx))
        (mem_centralizer_iff.mp h.mem x (hC.le hx))) }

end Certificates

end CFSG.SeitzReduction.RankOne
