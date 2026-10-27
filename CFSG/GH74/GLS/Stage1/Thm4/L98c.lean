module

public import CFSG.GH74.GLS.Stage1.Thm4.L98b
public import CFSG.GH74.GLS.Stage1.Thm4.Closed

public section

namespace CFSG.GH74.GLS.Stage1.Thm4

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5
open scoped commutatorElement

theorem isDoubleCoverOfAlt_congr {K L : Type} [Group K] [Group L] (e : K ≃* L) {n : ℕ}
    (h : IsDoubleCoverOfAlt K n) : IsDoubleCoverOfAlt L n := by
  obtain ⟨hq, hc, ⟨φ⟩⟩ := h
  refine ⟨(CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr e).1 hq, ?_, ?_⟩
  · rw [← Nat.card_congr (Subgroup.centerCongr e).toEquiv]; exact hc
  · have hmap : (center K).map e.toMonoidHom = center L := by
      ext y
      simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom]
      constructor
      · rintro ⟨x, hx, rfl⟩
        rw [Subgroup.mem_center_iff] at hx ⊢
        intro g
        have := hx (e.symm g)
        have h2 := congrArg e this
        simpa using h2
      · intro hy
        refine ⟨e.symm y, ?_, by simp⟩
        rw [Subgroup.mem_center_iff] at hy ⊢
        intro g
        have := hy (e g)
        have h2 := congrArg e.symm this
        simpa using h2
    exact ⟨(QuotientGroup.congr (center K) (center L) e hmap).symm.trans φ⟩

section Sup

variable {G : Type} [Group G] [Finite G] {z : G} {K : Subgroup G}

omit [Finite G] in
theorem mem_sup_subgroupOf_of_mem (hK : K ≤ Cz z) {c : ↥(Cz z)} (hc : (c : G) ∈ K ⊔ Oz z) :
    c ∈ K.subgroupOf (Cz z) ⊔ pPrimeCore 2 ↥(Cz z) := by
  have e : (K.subgroupOf (Cz z) ⊔ pPrimeCore 2 ↥(Cz z)).map (Cz z).subtype = K ⊔ Oz z := by
    rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hK]
    rfl
  rw [← e] at hc
  obtain ⟨y, hy, hyc⟩ := hc
  have : y = c := Subtype.ext hyc
  rwa [this] at hy

theorem toBar_mem_barOf_of_mem (hK : K ≤ Cz z) {c : ↥(Cz z)} (hc : (c : G) ∈ K ⊔ Oz z) :
    toBar z c ∈ barOf z K := by
  have h1 := mem_sup_subgroupOf_of_mem hK hc
  have h2 : toBar z c ∈ (K.subgroupOf (Cz z) ⊔ pPrimeCore 2 ↥(Cz z)).map (toBar z) :=
    Subgroup.mem_map_of_mem _ h1
  have hN : (pPrimeCore 2 ↥(Cz z)).map (toBar z) = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨n, hn, rfl⟩
    exact (QuotientGroup.eq_one_iff n).2 hn
  rwa [Subgroup.map_sup, hN, sup_bot_eq] at h2

end Sup

namespace Ctx98

variable {G : Type} [Group G] [Finite G] {Lh : Type} [Group Lh] {z t : G} {S K : Subgroup G}
  (h : Ctx98 G Lh z t S K)

include h

theorem barOf_normal : (barOf z K).Normal := by
  have hn : (K.subgroupOf (Cz z)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hn' : (n : G) ∈ K := hn
    have := (Subgroup.mem_normalizer_iff.1 (h.mem_normalizer g.2) n).1 hn'
    rw [Subgroup.mem_subgroupOf]
    simpa using this
  exact hn.map (toBar z) (QuotientGroup.mk'_surjective _)

theorem cover_bar {n : ℕ} (hcov : IsDoubleCoverOfAlt Lh n) : IsDoubleCoverOfAlt ↥(barOf z K) n := by
  obtain ⟨e⟩ := h.std.K_rigid.2
  exact isDoubleCoverOfAlt_congr (e.symm.trans h.hatEquivBar) hcov

theorem hyp5B (hF : Step9_8_Fstar) {n : ℕ} (hn8 : 8 ≤ n) (hn11 : n ≤ 11)
    (hcov : IsDoubleCoverOfAlt Lh n) : Hyp5B (CentralizerBar z) (barOf z K) n where
  normal := h.barOf_normal
  n_ge := hn8
  n_le := hn11
  cover := h.cover_bar hcov
  cent := by
    intro y hy
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥(Cz z)) y
    have hc : ∀ k ∈ K, ⁅k, ((c : ↥(Cz z)) : G)⁆ ∈ Oz z := by
      intro k hk
      have hkC : k ∈ Cz z := h.K_le hk
      have hmem : toBar z ⟨k, hkC⟩ ∈ barOf z K := ⟨⟨k, hkC⟩, hk, rfl⟩
      have hcomm := hy (toBar z ⟨k, hkC⟩) hmem
      have hcomm' : toBar z (c * ⟨k, hkC⟩) = toBar z (⟨k, hkC⟩ * c) := by
        rw [map_mul, map_mul]; exact hcomm
      have hmN : (c * ⟨k, hkC⟩)⁻¹ * (⟨k, hkC⟩ * c) ∈ pPrimeCore 2 ↥(Cz z) :=
        QuotientGroup.eq.1 hcomm'
      have hconj := (pPrimeCore_normal (p := 2) (G := ↥(Cz z))).conj_mem _ hmN (c * ⟨k, hkC⟩)
      have e : (c * ⟨k, hkC⟩) * ((c * ⟨k, hkC⟩)⁻¹ * (⟨k, hkC⟩ * c)) * (c * ⟨k, hkC⟩)⁻¹ =
          ⁅(⟨k, hkC⟩ : ↥(Cz z)), c⁆ := by
        simp only [commutatorElement_def]; group
      rw [e] at hconj
      exact (mem_Oz_iff (z := z)).2 hconj
    have hsup := hF G Lh z t S K h.std h.r1 h.q1 (c : G) c.2 hc
    have hsup' : (c : G) ∈ K ⊔ Oz z :=
      (sup_le_sup_right ((Subgroup.zpowers_le).2 h.z_mem) _) hsup
    exact toBar_mem_barOf_of_mem h.K_le hsup'

end Ctx98

end CFSG.GH74.GLS.Stage1.Thm4
