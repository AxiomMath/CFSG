module

public import CFSG.GH74.GLS.C3.Layer1.Thm1L32M12

public section

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin
  CFSG.GH74.GLS.C3.Layer1 CFSG.GH74.GLS.C3.Layer1.Thm1 CFSG.GH74.GLS.IVK

namespace CFSG.GH74.GLS.C3.Layer1.Thm1L32

section Glue

variable {G : Type} [Group G] [Finite G]

theorem kside_of_data {x f : G} {K Λ : Subgroup G}
    (hKC : K ≤ centralizer ({x} : Set G))
    (hKN : ∀ c ∈ centralizer ({x} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K)
    (hfC : f ∈ centralizer ({x} : Set G)) (hf2 : orderOf f = 2) (hΛK : Λ ≤ K)
    (himg : (Λ.subgroupOf K).map (QuotientGroup.mk' (pPrimeCore 2 ↥K)) =
      (_root_.commutator ↥(fixedSubgroup (kBar K) (Back.actHom hKN ⟨f, hfC⟩))).map
        (fixedSubgroup (kBar K) (Back.actHom hKN ⟨f, hfC⟩)).subtype)
    (hΛc : pPrimeCoreOf 2 Λ ≤ pPrimeCoreOf 2 K)
    (hA : ∀ β : MulAut (kBar K),
      (∀ i ∈ (_root_.commutator ↥(fixedSubgroup (kBar K) (Back.actHom hKN ⟨f, hfC⟩))).map
        (fixedSubgroup (kBar K) (Back.actHom hKN ⟨f, hfC⟩)).subtype, β i = i) →
        β = 1 ∨ β = Back.actHom hKN ⟨f, hfC⟩)
    (hB : Back.actHom hKN ⟨f, hfC⟩ ∉ innAut (kBar K))
    (hC : ∃ c ∈ fixedSubgroup (kBar K) (Back.actHom hKN ⟨f, hfC⟩),
      c ∉ (_root_.commutator ↥(fixedSubgroup (kBar K) (Back.actHom hKN ⟨f, hfC⟩))).map
        (fixedSubgroup (kBar K) (Back.actHom hKN ⟨f, hfC⟩)).subtype) :
    KSide K x f Λ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set α := Back.actHom hKN ⟨f, hfC⟩ with hα
  set I : Subgroup (kBar K) := (_root_.commutator ↥(fixedSubgroup (kBar K) α)).map
    (fixedSubgroup (kBar K) α).subtype with hI
  have hαα : α * α = 1 := by
    rw [hα, ← map_mul]
    have : (⟨f, hfC⟩ * ⟨f, hfC⟩ : ↥(centralizer ({x} : Set G))) = 1 := by
      apply Subtype.ext
      have := pow_orderOf_eq_one f
      rwa [hf2, pow_two] at this
    rw [this, map_one]
  refine ⟨?_, ?_, ?_⟩
  ·
    intro c hc hyp
    have hcN : c ∈ centralizer ({x} : Set G) := hc.1
    have hfix : ∀ i ∈ I, Back.actHom hKN ⟨c, hcN⟩ i = i := by
      intro ib hib
      rw [← himg] at hib
      obtain ⟨k, hk, rfl⟩ := hib
      have hkΛ : (k : G) ∈ Λ := hk
      show Back.actHom hKN ⟨c, hcN⟩ (QuotientGroup.mk k) = QuotientGroup.mk k
      rw [Back.actHom_mk]
      have hzK : c * (k : G) * c⁻¹ * (k : G)⁻¹ ∈ pPrimeCoreOf 2 K := hΛc (hyp k hkΛ)
      obtain ⟨hzmem, hz1⟩ := (IVK.Lifted.mem_pPrimeCoreOf_iff_hatMk K _).1 hzK
      have heq : (⟨c * (k : G) * c⁻¹, hKN c hcN k k.2⟩ : ↥K) =
          ⟨c * (k : G) * c⁻¹ * (k : G)⁻¹, hzmem⟩ * k := Subtype.ext (by simp)
      rw [heq, QuotientGroup.mk_mul]
      have hz1' : (QuotientGroup.mk (⟨c * (k : G) * c⁻¹ * (k : G)⁻¹, hzmem⟩ : ↥K) : kBar K) = 1 := hz1
      rw [hz1', one_mul]
    rcases hA _ hfix with h1 | h1
    · left
      have hker : (⟨c, hcN⟩ : ↥(centralizer ({x} : Set G))) ∈ (Back.actHom hKN).ker := h1
      rw [Back.actHom_ker] at hker
      exact Subgroup.mem_subgroupOf.1 hker
    · right
      have hker : (⟨c, hcN⟩ * ⟨f, hfC⟩ : ↥(centralizer ({x} : Set G))) ∈ (Back.actHom hKN).ker := by
        rw [MonoidHom.mem_ker, map_mul, h1, hαα]
      rw [Back.actHom_ker] at hker
      exact Subgroup.mem_subgroupOf.1 hker
  ·
    intro k hk hkf
    have hkC : k ∈ centralizer ({x} : Set G) := hKC hk
    have hker : (⟨k, hkC⟩ * ⟨f, hfC⟩ : ↥(centralizer ({x} : Set G))) ∈ (Back.actHom hKN).ker := by
      rw [Back.actHom_ker]
      exact Subgroup.mem_subgroupOf.2 hkf
    rw [MonoidHom.mem_ker, map_mul, Back.actHom_of_mem hKN hk hkC] at hker
    apply hB
    have : α = (MulAut.conj (QuotientGroup.mk (⟨k, hk⟩ : ↥K) : kBar K))⁻¹ :=
      eq_inv_of_mul_eq_one_right hker
    rw [this, ← map_inv]
    exact ⟨_, rfl⟩
  ·
    obtain ⟨c, hcC, hcI⟩ := hC
    obtain ⟨gH, hgH⟩ := centMap_surjective hKN hfC hf2 ⟨c, hcC⟩
    refine ⟨(gH : G), gH.2, fun δ hδ hmem => ?_⟩
    apply hcI
    have hδK : δ ∈ K := hΛK hδ
    obtain ⟨ho, h1⟩ := (IVK.Lifted.mem_pPrimeCoreOf_iff_hatMk K _).1 hmem
    have hgK : (gH : G) ∈ K := gH.2.1
    have h2 : (QuotientGroup.mk (⟨δ, hδK⟩ : ↥K) : kBar K) = QuotientGroup.mk ⟨(gH : G), hgK⟩ := by
      have h3 : (⟨δ⁻¹ * (gH : G), ho⟩ : ↥K) = (⟨δ, hδK⟩ : ↥K)⁻¹ * ⟨(gH : G), hgK⟩ := Subtype.ext (by simp)
      have h4 : (QuotientGroup.mk ((⟨δ, hδK⟩ : ↥K)⁻¹ * ⟨(gH : G), hgK⟩) : kBar K) = 1 := by
        rw [← h3]; exact h1
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, inv_mul_eq_one] at h4
      exact h4
    have h5 : c = (QuotientGroup.mk (⟨(gH : G), hgK⟩ : ↥K) : kBar K) := by
      have := congrArg Subtype.val hgH
      rw [centMap_apply] at this
      exact this.symm
    rw [h5, ← h2, ← himg]
    exact ⟨⟨δ, hδK⟩, Subgroup.mem_subgroupOf.2 hδ, rfl⟩

end Glue

end CFSG.GH74.GLS.C3.Layer1.Thm1L32
