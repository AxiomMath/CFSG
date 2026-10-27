module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx63

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G}


abbrev piC (z : G) : ↥(Cz z) →* CentralizerBar z := QuotientGroup.mk' (pPrimeCore 2 ↥(Cz z))

@[expose] def imgBar (z : G) (K : Subgroup G) : Subgroup (CentralizerBar z) :=
  (K.subgroupOf (Cz z)).map (piC z)

omit [Finite G] in
theorem mem_imgBar {K : Subgroup G} (hKC : K ≤ Cz z) {x : CentralizerBar z} :
    x ∈ imgBar z K ↔ ∃ (k : G) (hk : k ∈ K), piC z ⟨k, hKC hk⟩ = x := by
  unfold imgBar
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨k, hKC hk⟩, hk, rfl⟩

omit [Finite G] in
theorem piC_mem_imgBar {K : Subgroup G} (hKC : K ≤ Cz z) {k : G} (hk : k ∈ K) :
    piC z ⟨k, hKC hk⟩ ∈ imgBar z K := (mem_imgBar hKC).2 ⟨k, hk, rfl⟩

theorem imgBar_equiv {K : Subgroup G} (hK : IsPCompIn 2 (Cz z) K) :
    Nonempty (HatT K ≃* ↥(imgBar z K)) := by
  obtain ⟨hKC, K', -, hsub, -⟩ := hK
  obtain ⟨e1⟩ := TwoThin.hat_equiv_map (M := K.subgroupOf (Cz z)) hsub
  obtain ⟨e2⟩ := TwoThin.hat_equiv_subgroupOf hKC
  exact ⟨e2.trans e1⟩


theorem imgBar_comm (hII : II4_4_4_center) (hf : Fused8 G z S K₁ K₂) :
    ∀ a ∈ imgBar z K₁, ∀ b ∈ imgBar z K₂, a * b = b * a := by
  have hM := hf.m4 hII
  have hK₁C : K₁ ≤ Cz z := hM.K₁_le
  have hK₂C : K₂ ≤ Cz z := hM.K₂_le
  intro a ha b hb
  obtain ⟨k₁, hk₁, rfl⟩ := (mem_imgBar hK₁C).1 ha
  obtain ⟨k₂, hk₂, rfl⟩ := (mem_imgBar hK₂C).1 hb
  have h1 : ⁅k₁, k₂⁆ ∈ pPrimeCoreOf 2 K₁ := (hM.cs₁ hk₂).2.2 k₁ hk₁
  have hOz : ⁅k₁, k₂⁆ ∈ Oz z := pPrimeCoreOf_le_Oz (hf.std.comp_isPCompIn (Or.inl rfl)) h1
  have hcx : ⁅k₁, k₂⁆ ∈ Cz z := by
    simp only [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem (hK₁C hk₁) (hK₂C hk₂)) (inv_mem (hK₁C hk₁)))
      (inv_mem (hK₂C hk₂))
  have hcomm1 : piC z ⟨⁅k₁, k₂⁆, hcx⟩ = 1 :=
    (hatMk_eq_one_iff (Cz z) ⟨⁅k₁, k₂⁆, hcx⟩).2 hOz
  have e : (⟨⁅k₁, k₂⁆, hcx⟩ : ↥(Cz z)) =
      ⁅(⟨k₁, hK₁C hk₁⟩ : ↥(Cz z)), (⟨k₂, hK₂C hk₂⟩ : ↥(Cz z))⁆ := rfl
  rw [e, map_commutatorElement] at hcomm1
  exact commutatorElement_eq_one_iff_mul_comm.1 hcomm1

theorem zbar_facts (hII : II4_4_4_center) (hf : Fused8 G z S K₁ K₂) :
    piC z ⟨z, mem_centralizer_singleton_iff.2 rfl⟩ ∈ imgBar z K₁ ⊓ imgBar z K₂ ∧
      piC z ⟨z, mem_centralizer_singleton_iff.2 rfl⟩ ≠ 1 := by
  have hM := hf.m4 hII
  have hK₁C : K₁ ≤ Cz z := hM.K₁_le
  have hK₂C : K₂ ≤ Cz z := hM.K₂_le
  refine ⟨⟨piC_mem_imgBar hK₁C (hM.z_mem_comp (Or.inl rfl)),
    piC_mem_imgBar hK₂C (hM.z_mem_comp (Or.inr rfl))⟩, fun h => ?_⟩
  have hz : z ∈ Oz z := (hatMk_eq_one_iff (Cz z) ⟨z, mem_centralizer_singleton_iff.2 rfl⟩).1 h
  have hdvd := Subgroup.orderOf_dvd_natCard (Oz z) hz
  rw [hf.std.orderOf_z] at hdvd
  exact (Nat.not_even_iff_odd.2 card_Oz_odd) (even_iff_two_dvd.2 hdvd)

theorem imgBar_inf_card (hII : II4_4_4_center) (h44 : II4_44) (hf : Fused8 G z S K₁ K₂) :
    Nat.card ↥(imgBar z K₁ ⊓ imgBar z K₂) = 2 := by
  have hc1 := hf.std.comp_isPCompIn (Or.inl rfl : K₁ = K₁ ∨ K₁ = K₂)
  have hsl := h44 G hf.std.simple z hf.std.orderOf_z K₁ hc1 (hf.std.comp_pRank (Or.inl rfl))
  obtain ⟨e⟩ := imgBar_equiv hc1
  have hcen : Nat.card ↥(Subgroup.center ↥(imgBar z K₁)) = 2 := by
    have := Nat.card_congr (Subgroup.centerCongr e).toEquiv
    rw [hsl.2] at this
    exact this.symm
  have hD : (imgBar z K₁ ⊓ imgBar z K₂).subgroupOf (imgBar z K₁) ≤
      Subgroup.center ↥(imgBar z K₁) := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    rw [Subgroup.mem_center_iff]
    intro a
    exact Subtype.ext (imgBar_comm hII hf a a.2 x hx.2)
  have hle : Nat.card ↥(imgBar z K₁ ⊓ imgBar z K₂) ≤ 2 := by
    have h1 := Subgroup.card_le_of_le hD
    rw [hcen, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_left : imgBar z K₁ ⊓ imgBar z K₂ ≤ imgBar z K₁)).toEquiv] at h1
    exact h1
  have hge : 2 ≤ Nat.card ↥(imgBar z K₁ ⊓ imgBar z K₂) := by
    obtain ⟨hz1, hz2⟩ := zbar_facts hII hf
    have hne : imgBar z K₁ ⊓ imgBar z K₂ ≠ ⊥ := by
      intro hbot
      rw [hbot, Subgroup.mem_bot] at hz1
      exact hz2 hz1
    have := (Subgroup.one_lt_card_iff_ne_bot _).2 hne
    omega
  omega

end CFSG.GH74.GLS.Stage1.Thm3.Sec8
