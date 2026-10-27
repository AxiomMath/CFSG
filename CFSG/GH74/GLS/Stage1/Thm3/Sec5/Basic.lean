module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Glue
public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Struct2
public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Struct4
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Defs

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec5

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4
open scoped commutatorElement

section Basic

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G}

theorem pPrimeCoreOf_le_Oz {K : Subgroup G} (hK : IsPCompIn 2 (Cz z) K) :
    pPrimeCoreOf 2 K ≤ Oz z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hKC, K', -, hsub, -⟩ := hK
  have h1 := pPrimeCoreOf_le_of_subnormal (X := ↥(Cz z)) 2 hsub
  rw [TwoThin.pPrimeCoreOf_eq_map_subgroupOf hKC]
  exact Subgroup.map_mono h1

omit [Finite G] in
theorem Oz_conj {x n : G} (hx : x ∈ Cz z) (hn : n ∈ Oz z) : x * n * x⁻¹ ∈ Oz z :=
  TwoThin.pPrimeCoreOf_normalized (Cz z) hx hn

theorem card_Oz_odd : Odd (Nat.card ↥(Oz z)) := TwoThin.card_pPrimeCoreOf_odd (Cz z)

omit [Finite G] in
theorem le_normalizer_Oz {X : Subgroup G} (hX : X ≤ Cz z) : X ≤ normalizer (Oz z : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro n
  constructor
  · exact fun hn => Oz_conj (hX hx) hn
  · intro hn
    have := Oz_conj (hX (X.inv_mem hx)) hn
    simpa [mul_assoc] using this

omit [Finite G] in
theorem inducesFAut_of_mul_cSec {K : Subgroup G} {s t : G} (ht : InducesFAut t K)
    (h : s * t⁻¹ ∈ cSec K) : InducesFAut s K := by
  obtain ⟨htn, hF⟩ := ht
  have hsn : s ∈ normalizer (K : Set G) := by
    have := mul_mem h.1 htn
    simpa using this
  refine ⟨hsn, ?_⟩
  have h1 : phi K (s * t⁻¹) h.1 = 1 := (phi_eq_one_iff K h.1).2 h
  have h2 : phi K (s * t⁻¹ * t) (mul_mem h.1 htn) = phi K (s * t⁻¹) h.1 * phi K t htn :=
    phi_mul K h.1 htn
  have h3 : phi K s hsn = phi K (s * t⁻¹ * t) (mul_mem h.1 htn) :=
    phi_congr K (by group) hsn _
  have h4 : phi K s hsn = phi K t htn := by rw [h3, h2, h1, one_mul]
  show IsFAutomorphism (Hat K) (phi K s hsn)
  rw [h4]
  exact hF

theorem isSylowOf_of_syl2In {P H : Subgroup G} (h : M.Syl2In P H) :
    CFSG.ABGLocalTools.IsSylowOf 2 P H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.ABGLocalTools.isSylowOf_iff.2 h

variable (hM : M.M4 (pPrimeCoreOf 2) InducesFAut SDp z S K₁ K₂)

include hM

omit [Finite G] in
theorem S_le_Cz : S ≤ Cz z := hM.S_syl.1

omit [Finite G] in
theorem normalizer_other (hne : K₁ ≠ K₂) {c : G} (hc : c ∈ Cz z)
    (h1 : c ∈ normalizer (K₁ : Set G)) : c ∈ normalizer (K₂ : Set G) := by
  rcases hM.perm c hc with ⟨_, h2⟩ | ⟨h1', _⟩
  · exact M.cj_eq_iff_normalizer.1 h2
  · exact absurd (h1'.symm.trans (M.cj_eq_iff_normalizer.2 h1)) (Ne.symm hne)

omit [Finite G] in
theorem Pof_le_Qof {A B : Subgroup G} (hAB : A = K₁ ∧ B = K₂ ∨ A = K₂ ∧ B = K₁) :
    Pof S A ≤ Qof S B := by
  rcases hAB with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact fun x hx => ⟨hx.1, hM.cs₂ hx.2⟩
  · exact fun x hx => ⟨hx.1, hM.cs₁ hx.2⟩

theorem z_mem_Qof {B : Subgroup G} (hB : B = K₁ ∨ B = K₂) : z ∈ Qof S B :=
  ⟨hM.z_mem_S, hM.z_mem_secCent_comp hB⟩

theorem eq_z_of_mem_Qof {B : Subgroup G} (hB : B = K₁ ∨ B = K₂) (hr : pRank 2 ↥(Qof S B) = 1)
    (hz2 : orderOf z = 2) {a : G} (ha : a ∈ Qof S B) (ha2 : orderOf a = 2) : a = z := by
  have haC : a ∈ Cz z := hM.S_syl.1 ha.1
  have hcomm : a * z = z * a := Subgroup.mem_centralizer_singleton_iff.1 haC
  exact eq_of_pRank_one hr ha (z_mem_Qof hM hB) ha2 hz2 hcomm

theorem Pof_card {K : Subgroup G} (hK : K = K₁ ∨ K = K₂) :
    Nat.card ↥(S ⊓ K) = 2 ^ (Nat.card ↥K).factorization 2 := by
  have hle : K ≤ K₁ ⊔ K₂ := by
    rcases hK with rfl | rfl
    · exact le_sup_left
    · exact le_sup_right
  have hsyl := hM.Pi_syl hK
  have hinf : M.Pm S K₁ K₂ ⊓ K = S ⊓ K := by
    unfold M.Pm
    rw [inf_assoc, inf_eq_right.2 hle]
  rw [hinf] at hsyl
  obtain ⟨a, m, hP, hm, hKm⟩ := hsyl.card_eq_pow_mul
  have hm0 : m ≠ 0 := hm.pos.ne'
  have h2 : (Nat.card ↥K).factorization 2 = a := by
    rw [hKm, Nat.factorization_mul (by positivity) hm0]
    simp only [Finsupp.add_apply]
    have : m.factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (by
        intro h; exact (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr h))
    rw [this, Nat.Prime.factorization_pow Nat.prime_two]
    simp
  rw [hP, h2]

end Basic

end CFSG.GH74.GLS.Stage1.Thm3.Sec5
