module

public import CFSG.GroupTheory.ElemAbelianRank
public import CFSG.HardMathSupport.Malle.OvergroupTransport.Transport
public import CFSG.HardMathSupport.Timmesfeld.Proving.PRankQuotient
public import CFSG.LocalAnalysis.RankThreeUC.OddRankOneQuotient.OddRankOneQuotient

public section

namespace CFSG.GroupTheory

open CFSG.Open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem exists_card_prime_le_inf_of_le_sup_of_normal {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {L₁ L₂ E : Subgroup G} (hL₂ : L₂ ≤ normalizer (L₁ : Set G))
    [hN : (L₁.subgroupOf (L₂ ⊔ L₁)).Normal]
    (hrk : CFSG.Open.pRank q L₂ ≤ 1) (hE : E ≤ L₁ ⊔ L₂) (hEel : IsElemAbelian q E)
    (hEcard : Nat.card E = q ^ 2) :
    ∃ F : Subgroup G, F ≤ E ⊓ L₁ ∧ Nat.card F = q := by
  classical
  have hEH : E ≤ L₂ ⊔ L₁ := by
    rw [sup_comm]
    exact hE
  have hErank : CFSG.Open.pRank q E = 2 := by
    have h := card_eq_pow_pRank_of_isElemAbelian hq hEel
    rw [hEcard] at h
    exact (Nat.pow_right_injective hq.two_le h).symm
  have hL2rank : CFSG.pRank q ↥L₂ ≤ 1 := by
    rwa [CFSG.SectionRank.pRank_coe_eq_openPRank q L₂]
  let φ : ↥L₂ →* ↥(L₂ ⊔ L₁) ⧸ (L₁.subgroupOf (L₂ ⊔ L₁)) :=
    (QuotientGroup.mk' (L₁.subgroupOf (L₂ ⊔ L₁))).comp
      (Subgroup.inclusion (show L₂ ≤ L₂ ⊔ L₁ from le_sup_left))
  have hφ : Function.Surjective φ := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨a, ha, b, hb, hab⟩ : ∃ a ∈ L₂, ∃ b ∈ L₁, a * b = x := by
      have hxmul : (x : G) ∈ (L₂ : Set G) * (L₁ : Set G) := by
        rw [← Subgroup.coe_mul_of_left_le_normalizer_right L₂ L₁ hL₂]
        exact x.2
      exact Set.mem_mul.mp hxmul
    refine ⟨⟨a, ha⟩, ?_⟩
    apply QuotientGroup.eq.2
    rw [Subgroup.mem_subgroupOf]
    have hx : ((Subgroup.inclusion (show L₂ ≤ L₂ ⊔ L₁ from le_sup_left) ⟨a, ha⟩)⁻¹ * x :
        ↥(L₂ ⊔ L₁)) = Subgroup.inclusion (show L₁ ≤ L₂ ⊔ L₁ from le_sup_right) ⟨b, hb⟩ := by
      ext
      simp [Subgroup.inclusion, ← hab]
    rw [hx]
    exact hb
  have hHrank : CFSG.pRank q (↥(L₂ ⊔ L₁) ⧸ (L₁.subgroupOf (L₂ ⊔ L₁))) ≤ 1 :=
    CFSG.LocalAnalysis.RankThreeUC.OddRankOneQuotient.pRank_le_one_of_surjective hq hq2
      hL2rank φ hφ
  have hHopen : CFSG.Open.pRank q
      (⊤ : Subgroup (↥(L₂ ⊔ L₁) ⧸ (L₁.subgroupOf (L₂ ⊔ L₁)))) ≤ 1 := by
    rw [← CFSG.SectionRank.pRank_eq_open_pRank_top q
      (↥(L₂ ⊔ L₁) ⧸ (L₁.subgroupOf (L₂ ⊔ L₁)))]
    exact hHrank
  have hmain := CFSG.HardMathSupport.Timmesfeld.Proving.pRank_le_pRank_inf_add_pRank_map
    (G := ↥(L₂ ⊔ L₁)) hq (E.subgroupOf (L₂ ⊔ L₁)) (L₁.subgroupOf (L₂ ⊔ L₁))
  have hinf : (E.subgroupOf (L₂ ⊔ L₁)) ⊓ (L₁.subgroupOf (L₂ ⊔ L₁)) =
      (E ⊓ L₁).subgroupOf (L₂ ⊔ L₁) := by
    ext x
    simp [Subgroup.mem_subgroupOf]
  rw [hinf] at hmain
  rw [CFSG.HardMathSupport.Malle.OvergroupTransport.pRank_subgroupOf q hEH] at hmain
  rw [CFSG.HardMathSupport.Malle.OvergroupTransport.pRank_subgroupOf q
    (inf_le_left.trans hEH)] at hmain
  have himg : CFSG.Open.pRank q
      ((E.subgroupOf (L₂ ⊔ L₁)).map (QuotientGroup.mk' (L₁.subgroupOf (L₂ ⊔ L₁)))) ≤ 1 :=
    (CFSG.SectionRank.pRank_mono hq.one_lt (le_top)).trans hHopen
  have hpos : 1 ≤ CFSG.Open.pRank q (E ⊓ L₁) := by
    have h2 : 2 ≤ CFSG.Open.pRank q (E ⊓ L₁) + 1 := by
      calc 2 = CFSG.Open.pRank q E := hErank.symm
        _ ≤ CFSG.Open.pRank q (E ⊓ L₁) +
              CFSG.Open.pRank q
                ((E.subgroupOf (L₂ ⊔ L₁)).map
                  (QuotientGroup.mk' (L₁.subgroupOf (L₂ ⊔ L₁)))) := hmain
        _ ≤ CFSG.Open.pRank q (E ⊓ L₁) + 1 := Nat.add_le_add_left himg _
    omega
  obtain ⟨A, hAle, hAel, hAcard⟩ := CFSG.SectionRank.exists_pRank hq.one_lt (E ⊓ L₁)
  have hAcard' : Nat.card A = q ^ CFSG.Open.pRank q (E ⊓ L₁) := hAcard
  have hAlt : 1 < Nat.card A := by
    rw [hAcard']
    exact Nat.one_lt_pow (by omega) hq.one_lt
  have hAne : A ≠ ⊥ := (Subgroup.one_lt_card_iff_ne_bot A).mp hAlt
  obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hAne
  have hord : orderOf (a : G) = q := by
    have hdvd : orderOf (a : G) ∣ q :=
      orderOf_dvd_of_pow_eq_one (by simpa using hAel.2 (a : G) a.2)
    rcases hq.eq_one_or_self_of_dvd (orderOf (a : G)) hdvd with h1 | hqeq
    · exfalso
      exact ha1 (Subtype.ext (orderOf_eq_one_iff.mp h1))
    · exact hqeq
  refine ⟨Subgroup.zpowers (a : G), ?_, ?_⟩
  · exact (Subgroup.zpowers_le.mpr a.2).trans hAle
  · rw [Nat.card_zpowers, hord]

theorem exists_card_prime_le_inf_of_le_sup {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {L₁ L₂ E : Subgroup G} (hL₂ : L₂ ≤ normalizer (L₁ : Set G))
    (hrk : CFSG.Open.pRank q L₂ ≤ 1) (hE : E ≤ L₁ ⊔ L₂) (hEel : IsElemAbelian q E)
    (hEcard : Nat.card E = q ^ 2) :
    ∃ F : Subgroup G, F ≤ E ⊓ L₁ ∧ Nat.card F = q :=
  exists_card_prime_le_inf_of_le_sup_of_normal (hN :=
    Subgroup.normal_subgroupOf_sup_of_le_normalizer hL₂) hq hq2 hL₂ hrk hE hEel hEcard

end CFSG.GroupTheory
