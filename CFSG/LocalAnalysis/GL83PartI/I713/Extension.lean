module

public import CFSG.LocalAnalysis.GL83PartI.I_7_13
public import CFSG.LocalAnalysis.SectionRank.SubgroupRank
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace GL83.I713

open CFSG.Open CFSG.ComponentClassification.OuterAutomorphisms

variable {p : ℕ}

theorem isElemAbelian_of_le {G : Type*} [Group G] {E F : Subgroup G} (hF : IsElemAbelian p F)
    (hEF : E ≤ F) : IsElemAbelian p E := by
  exact CFSG.Open.IsElemAbelian.mono hF hEF

theorem pRank_top_le_add_pRank_quotient {G : Type*} [Group G] [Finite G] (hp : p.Prime)
    (N : Subgroup G) [N.Normal] :
    pRank p (⊤ : Subgroup G) ≤ pRank p N + pRank p (⊤ : Subgroup (G ⧸ N)) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨E, -, hE, hcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (⊤ : Subgroup G)
  have hEp : IsPGroup p E := IsPGroup.of_card hcard
  obtain ⟨a, ha⟩ := (hEp.to_le (inf_le_left : E ⊓ N ≤ E)).exists_card_eq
  have haN : a ≤ pRank p N :=
    CFSG.SectionRank.le_pRank hp.one_lt inf_le_right (isElemAbelian_of_le hE inf_le_left) ha
  obtain ⟨b, hb⟩ := (hEp.map (QuotientGroup.mk' N)).exists_card_eq
  have hbQ : b ≤ pRank p (⊤ : Subgroup (G ⧸ N)) :=
    CFSG.SectionRank.le_pRank hp.one_lt le_top (CFSG.SectionRank.isElemAbelian_map hE _) hb
  have hsplit := Subgroup.relIndex_mul_card (QuotientGroup.mk' N).ker E
  rw [Subgroup.relIndex_ker, inf_comm, QuotientGroup.ker_mk'] at hsplit
  rw [hcard, ha, hb, ← pow_add] at hsplit
  have := Nat.pow_right_injective hp.two_le hsplit
  omega

noncomputable def innerEquiv (K : Type*) [Group K] (hZ : Subgroup.center K = ⊥) :
    K ≃* inner K :=
  MonoidHom.ofInjective (f := (MulAut.conj : K →* MulAut K)) <| by
    intro a b hab
    have hc : a⁻¹ * b ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h : a * g * a⁻¹ = b * g * b⁻¹ := by
        simpa only [MulAut.conj_apply] using congrArg (fun φ : MulAut K => φ g) hab
      calc g * (a⁻¹ * b) = a⁻¹ * (a * g * a⁻¹) * b := by group
        _ = a⁻¹ * (b * g * b⁻¹) * b := by rw [h]
        _ = a⁻¹ * b * g := by group
    rw [hZ, Subgroup.mem_bot] at hc
    exact inv_mul_eq_one.mp hc

theorem pRank_mulAut_le {K : Type*} [Group K] [Finite K] (hp : p.Prime)
    (hZ : Subgroup.center K = ⊥) :
    pRank p (⊤ : Subgroup (MulAut K)) ≤
      pRank p (⊤ : Subgroup K) + pRank p (⊤ : Subgroup (Outer K)) := by
  have h := pRank_top_le_add_pRank_quotient hp (inner K)
  have hinn : pRank p (inner K) = pRank p (⊤ : Subgroup K) := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup,
      CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt (innerEquiv K hZ)]
  rw [hinn] at h
  exact h

@[expose] def I713OuterClause : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K →
    (∃ a b : K, a * b ≠ b * a) → IsCatalogGroup K → pRank p (⊤ : Subgroup K) ≤ 1 →
      pRank p (⊤ : Subgroup (Outer K)) ≤ 1

theorem center_eq_bot_of_simple {K : Type*} [Group K] [IsSimpleGroup K]
    (hnonab : ∃ a b : K, a * b ≠ b * a) : Subgroup.center K = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center K) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnonab
    have hb : b ∈ Subgroup.center K := h ▸ Subgroup.mem_top b
    exact hab (Subgroup.mem_center_iff.mp hb a)

theorem i_7_13_1_of_outerClause (h : I713OuterClause) : GL83.I_7_13_1 := by
  intro p hp hp2 K _ _ hs hnonab hcat hK
  have hout := h p hp hp2 K hs hnonab hcat hK
  refine ⟨hout, ?_⟩
  have := hs
  have := pRank_mulAut_le hp (center_eq_bot_of_simple (K := K) hnonab)
  omega

end GL83.I713
