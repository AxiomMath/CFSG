module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryU1Card
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryFreeU3

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.ABGLocalTools

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem card_le_of_sq_eq_one_of_le_of_card_sylow
    (h : U3Start G L f t T) (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    {B : Subgroup G} (hBT : B ≤ T) (hB2 : ∀ x ∈ B, x ^ 2 = 1) : Nat.card B ≤ 4 * 2 ^ f := by
  obtain ⟨-, -, -, -, -, hNn, -⟩ := h.start_of_card_sylow hS2
  have := hNn
  have hcyc := h.isCyclic_quotient_of_card_sylow hS2
  obtain ⟨-, -, -, -, -, -, hinvA⟩ := h.facts_of_card_sylow hS2
  obtain ⟨hAcard, -⟩ := h.szA_facts_of_card_sylow hS2
  set N := szT₁ L T ⊔ zpowers t with hN
  set ψ : B →* T ⧸ N.subgroupOf T :=
    (QuotientGroup.mk' (N.subgroupOf T)).comp (Subgroup.inclusion hBT) with hψ
  have hrange : Nat.card ψ.range ≤ 2 := by
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ψ.range)
    have hg2 : g ^ 2 = 1 := by
      obtain ⟨b, hb⟩ := g.2
      apply Subtype.ext
      have hb2 : b ^ 2 = 1 := Subtype.ext (by simpa using hB2 b b.2)
      rw [SubgroupClass.coe_pow, ← hb, ← map_pow, hb2, map_one]
      rfl
    rw [← orderOf_eq_card_of_forall_mem_zpowers hg]
    exact orderOf_le_of_pow_eq_one (by norm_num) hg2
  have hker : Nat.card ψ.ker ≤ 2 * 2 ^ f := by
    have hle : ψ.ker.map B.subtype ≤ szA L T t := by
      rintro _ ⟨b, hb, rfl⟩
      have hb' : ψ b = 1 := hb
      change (QuotientGroup.mk (Subgroup.inclusion hBT b) : T ⧸ N.subgroupOf T) = 1 at hb'
      have hbN : ((Subgroup.inclusion hBT b : T) : G) ∈ N :=
        mem_subgroupOf.mp ((QuotientGroup.eq_one_iff (Subgroup.inclusion hBT b)).mp hb')
      exact hinvA b hbN (hB2 b b.2)
    calc Nat.card ψ.ker = Nat.card (ψ.ker.map B.subtype) :=
          (Subgroup.card_map_of_injective B.subtype_injective).symm
      _ ≤ Nat.card (szA L T t) := Subgroup.card_le_of_le hle
      _ = 2 * 2 ^ f := hAcard
  have hcard := Subgroup.card_mul_index ψ.ker
  rw [Subgroup.index_ker] at hcard
  rw [← hcard]
  calc Nat.card ψ.ker * Nat.card ψ.range ≤ (2 * 2 ^ f) * 2 := Nat.mul_le_mul hker hrange
    _ = 4 * 2 ^ f := by ring

theorem isSylowOf_centralizer (h : U3Start G L f t T) :
    IsSylowOf 2 T (centralizer ({t} : Set G)) := by
  obtain ⟨P, hP⟩ := h.sylow
  exact ⟨P, by rw [hP, subgroupOf_map_subtype, inf_eq_left.mpr h.le]⟩

theorem card_lt_of_sq_eq_one_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {B : Subgroup G}
    (hBt : B ≤ centralizer ({t} : Set G)) (hB2 : ∀ x ∈ B, x ^ 2 = 1) :
    Nat.card B < 2 * (2 ^ f) ^ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hBp : IsPGroup 2 B := fun g => ⟨1, Subtype.ext (by simpa using hB2 g g.2)⟩
  obtain ⟨a, -, ha⟩ := exists_conj_mem_of_isSylowOf h.isSylowOf_centralizer hBt hBp
  have hB'T : B.map (MulAut.conj a⁻¹).toMonoidHom ≤ T := by
    rintro _ ⟨x, hx, rfl⟩
    simpa [MulAut.conj_apply] using ha x hx
  have hB'2 : ∀ x ∈ B.map (MulAut.conj a⁻¹).toMonoidHom, x ^ 2 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hB2 x hx, map_one]
  have h1 := h.card_le_of_sq_eq_one_of_le_of_card_sylow hS2 hB'T hB'2
  rw [Subgroup.card_map_of_injective (MulAut.conj a⁻¹).injective] at h1
  have hq : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h.two_le
  nlinarith

theorem card_lt_of_isPGroup_of_card_sylow (h : U3Start G L f t T)
    (hT6 : Nat.card T < (2 ^ f) ^ 6) {P : Subgroup G} (hP : IsPGroup 2 P)
    (hPt : P ≤ centralizer ({t} : Set G)) : Nat.card P < (2 ^ f) ^ 6 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, -, ha⟩ := exists_conj_mem_of_isSylowOf h.isSylowOf_centralizer hPt hP
  have hP'T : P.map (MulAut.conj a⁻¹).toMonoidHom ≤ T := by
    rintro _ ⟨x, hx, rfl⟩
    simpa [MulAut.conj_apply] using ha x hx
  have h1 := Subgroup.card_le_of_le hP'T
  rw [Subgroup.card_map_of_injective (MulAut.conj a⁻¹).injective] at h1
  omega

section Certificates


theorem conj_t_not_mem_u3U₁_of_card_T_lt_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hc : ¬ ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹)
    (hΩ : (u3Omega L T R₂ t).ncard = (2 ^ f) ^ 2)
    {E : Subgroup (Equiv.Perm (u3Omega L T R₂ t))} (hE : E ≤ (u3OmegaAction L T R₂ t).range)
    (hEn : (E.subgroupOf (u3OmegaAction L T R₂ t).range).Normal)
    (hEreg : ∀ a b : u3Omega L T R₂ t, ∃! x : E, (x : Equiv.Perm (u3Omega L T R₂ t)) a = b)
    (hR₂2 : ∀ r ∈ R₂, r ^ 2 = 1) (hT6 : Nat.card T < (2 ^ f) ^ 6) (g : G) :
    g * t * g⁻¹ ∉ u3U L T R₂ t E ⊓ centralizer (R₂ : Set G) := by
  refine h.conj_t_not_mem_u3U₁_of_card_sylow hS2 hR hc hΩ hEreg hR₂2 (fun P hP hPt => ?_)
    (fun B hBt hB2 _ => h.card_lt_of_sq_eq_one_of_card_sylow hS2 hBt hB2) g
  rw [h.card_u3U₁_of_card_sylow hS2 hR hc hΩ hE hEn hEreg]
  exact h.card_lt_of_isPGroup_of_card_sylow hT6 hP hPt

theorem conj_t_of_mem_u3U₁_sup_of_card_T_lt_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hc : ¬ ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹)
    (hΩ : (u3Omega L T R₂ t).ncard = (2 ^ f) ^ 2)
    {E : Subgroup (Equiv.Perm (u3Omega L T R₂ t))} (hE : E ≤ (u3OmegaAction L T R₂ t).range)
    (hEn : (E.subgroupOf (u3OmegaAction L T R₂ t).range).Normal)
    (hEreg : ∀ a b : u3Omega L T R₂ t, ∃! x : E, (x : Equiv.Perm (u3Omega L T R₂ t)) a = b)
    (hR₂2 : ∀ r ∈ R₂, r ^ 2 = 1)
    (hU₁c : ∀ x ∈ u3U L T R₂ t E ⊓ centralizer (R₂ : Set G),
      ∀ y ∈ u3U L T R₂ t E ⊓ centralizer (R₂ : Set G), x * y * x⁻¹ * y⁻¹ ∈ R₂)
    (hU₁2 : ∀ x ∈ u3U L T R₂ t E ⊓ centralizer (R₂ : Set G), x ^ 2 ∈ R₂)
    (hT6 : Nat.card T < (2 ^ f) ^ 6) (g : G)
    (hg : g * t * g⁻¹ ∈ (u3U L T R₂ t E ⊓ centralizer (R₂ : Set G)) ⊔ zpowers t) :
    ∃ u ∈ u3U L T R₂ t E ⊓ centralizer (R₂ : Set G), g * t * g⁻¹ = u * t * u⁻¹ :=
  h.conj_t_of_mem_u3U₁_sup_of_card_sylow hS2 hR hc hΩ hE hEn hEreg hR₂2 hU₁c hU₁2
    (h.conj_t_not_mem_u3U₁_of_card_T_lt_of_card_sylow hS2 hR hc hΩ hE hEn hEreg hR₂2 hT6) g hg

end Certificates

end U3Start

end CFSG.SeitzReduction.RankOne
