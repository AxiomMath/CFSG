module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldSetupCenter
public import CFSG.LocalAnalysis.OddStandard.Seitz77L34Certified

public section

namespace CFSG.OddStandard.ChengHeld

open Subgroup CFSG.Open CFSG.Blueprint
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

theorem relIndex_sup_centralizer_dvd (h : Hyp G A) :
    (A ⊔ centralizer (A : Set G)).relIndex (normalizer (A : Set G)) ∣ 12 := by
  obtain ⟨e⟩ := ComponentClassification.CatFactsSmall.nonempty_equiv_psl34_of_lieModel h.model
  obtain ⟨ψ, hψ⟩ := ComponentClassification.RankTwoSporadic.exists_isActionHom
    ComponentClassification.RankTwoL3Four.HypII.l34AutModel h.commutator_eq_top e
  let Sbar : Subgroup ↥ComponentClassification.PSL3Four.R :=
    ComponentClassification.PSL3Four.S.subgroupOf ComponentClassification.PSL3Four.R
  have : Sbar.Normal := ComponentClassification.PSL3Four.S_normal
  have hN : Nat.card Sbar = 20160 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe ComponentClassification.PSL3Four.S_le_R).toEquiv,
      ComponentClassification.PSL3Four.card_S]
  have hQ : Nat.card (ComponentClassification.PSL3Four.R ⧸ Sbar) = 12 := by
    have h := card_eq_card_quotient_mul_card_subgroup Sbar
    rw [ComponentClassification.PSL3Four.card_R, hN] at h
    omega
  let f : ↥(normalizer (A : Set G)) →* ↥ComponentClassification.PSL3Four.R ⧸ Sbar :=
    (QuotientGroup.mk' Sbar).comp ψ
  have hker : (A ⊔ centralizer (A : Set G)).subgroupOf (normalizer (A : Set G)) = f.ker := by
    ext x
    rw [mem_subgroupOf, MonoidHom.mem_ker,
      Seitz77.L34.mem_sup_centralizer_iff hψ x.2]
    exact (QuotientGroup.eq_one_iff _).symm
  rw [Subgroup.relIndex, hker, Subgroup.index_ker]
  exact (Subgroup.card_subgroup_dvd_card f.range).trans (hQ ▸ dvd_rfl)

theorem normalizer_le_normalizer_sup_centralizer (h : Hyp G A) :
    normalizer (A : Set G) ≤ normalizer ((A ⊔ centralizer (A : Set G) : Subgroup G) : Set G) := by
  intro n hn
  have hnC : n ∈ normalizer ((centralizer (A : Set G) : Subgroup G) : Set G) := by
    rw [h.setting.standard.2.2.2.1]
    exact hn
  rw [mem_normalizer_iff_map_conj_eq] at hn hnC ⊢
  rw [Subgroup.map_sup, hn, hnC]

theorem not_three_dvd_relIndex_of_forall_pow_three (h : Hyp G A)
    (hpow : ∀ n ∈ normalizer (A : Set G), n ^ 3 ∈ A ⊔ centralizer (A : Set G) →
      n ∈ A ⊔ centralizer (A : Set G)) :
    ¬ 3 ∣ (A ⊔ centralizer (A : Set G)).relIndex (normalizer (A : Set G)) := by
  intro h3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set M := A ⊔ centralizer (A : Set G) with hM
  set N := normalizer (A : Set G) with hN
  have hMN : M ≤ N := sup_le le_normalizer (centralizer_le_normalizer _)
  have : (M.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMN).mpr
      (normalizer_le_normalizer_sup_centralizer h)
  have hcard : 3 ∣ Nat.card (↥N ⧸ M.subgroupOf N) := h3
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥N ⧸ M.subgroupOf N) 3 hcard
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective x
  have hn3 : ((n : ↥N ⧸ M.subgroupOf N)) ^ 3 = 1 := by
    rw [← hx]
    exact pow_orderOf_eq_one _
  have hn1 : ((n : ↥N ⧸ M.subgroupOf N)) ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hx
    exact absurd hx (by norm_num)
  have h3M : (n : G) ^ 3 ∈ M := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hn3
    exact mem_subgroupOf.mp hn3
  have h1M : (n : G) ∉ M := fun hM' =>
    hn1 ((QuotientGroup.eq_one_iff _).mpr (mem_subgroupOf.mpr hM'))
  exact h1M (hpow n n.2 h3M)

namespace Datum

variable (d : Datum A)

theorem normalizer_eq (h : Hyp G A)
    (h3 : ¬ 3 ∣ (A ⊔ centralizer (A : Set G)).relIndex (normalizer (A : Set G))) :
    normalizer (A : Set G) = (A ⊔ centralizer (A : Set G)) ⊔ d.X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd := relIndex_sup_centralizer_dvd h
  set M := A ⊔ centralizer (A : Set G) with hM
  set N := normalizer (A : Set G) with hN
  have hMN : M ≤ N := sup_le le_normalizer (centralizer_le_normalizer _)
  have hXN : d.X ≤ N := d.X_sylow.le
  have hMXN : M ⊔ d.X ≤ N := sup_le hMN hXN
  refine le_antisymm ?_ hMXN
  have hX2 : ¬ 2 ∣ d.X.relIndex N := (CFSG.ABGLocalTools.isSylowOf_iff.mp d.X_sylow).2.2
  have hk4 : M.relIndex N ∣ 4 := by
    have hcop : Nat.Coprime (M.relIndex N) 3 :=
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3).symm
    exact hcop.dvd_of_dvd_mul_right (by simpa using hdvd)
  have h1 : (M ⊔ d.X).relIndex N ∣ M.relIndex N := Subgroup.relIndex_dvd_of_le_left N le_sup_left
  have h2 : (M ⊔ d.X).relIndex N ∣ d.X.relIndex N := Subgroup.relIndex_dvd_of_le_left N le_sup_right
  have h24 : (M ⊔ d.X).relIndex N ∣ 4 := h1.trans hk4
  have hodd : ¬ 2 ∣ (M ⊔ d.X).relIndex N := fun h2' => hX2 (h2'.trans h2)
  have hle : (M ⊔ d.X).relIndex N ≤ 4 := Nat.le_of_dvd (by norm_num) h24
  have h1' : (M ⊔ d.X).relIndex N = 1 := by
    generalize (M ⊔ d.X).relIndex N = a at h24 hodd hle
    interval_cases a <;> simp_all
  exact (Subgroup.relIndex_eq_one.mp h1')

theorem inf_centralizer_S_le
    (h : Hyp G A) :
    d.X ⊓ centralizer (d.S : Set G) ≤ (d.S ⊓ centralizer (d.S : Set G)) ⊔ d.Q := by
  obtain ⟨e⟩ := ComponentClassification.CatFactsSmall.nonempty_equiv_psl34_of_lieModel h.model
  rintro x ⟨hxX, hxS⟩
  have hxN : x ∈ normalizer (A : Set G) := d.X_sylow.le hxX
  have h1 := Seitz77.centralizer_V_le_of_certificate h.commutator_eq_top e d.S_sylow ⟨hxN, hxS⟩
  have hcomm : d.S ⊓ centralizer (d.S : Set G) ≤ centralizer (centralizer (A : Set G) : Set G) :=
    fun z hz => mem_centralizer_iff.mpr fun c hc =>
      (mem_centralizer_iff.mp hc z (d.S_le_A hz.1)).symm
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer hcomm h1
  have hbX : b ∈ d.X := by
    have := d.X.mul_mem (d.X.inv_mem (d.S_le_X ha.1)) hxX
    simpa using this
  exact mul_mem (mem_sup_left ha) (mem_sup_right ⟨hbX, hb⟩)

theorem fixes_q_of_center_S_le
    (h : Hyp G A) (hZS : d.S ⊓ centralizer (d.S : Set G) ≤ centralizer (A : Set G)) :
    ∀ n ∈ normalizer (d.X : Set G), n⁻¹ * d.q * n = d.q := by
  refine d.fixes_q_of_unique_central_involution h fun z hzX hzc hz2 => ?_
  have hzS : z ∈ centralizer (d.S : Set G) :=
    mem_centralizer_iff.mpr fun s hs => hzc s (d.S_le_X hs)
  have h1 := d.inf_centralizer_S_le h ⟨hzX, hzS⟩
  have hzC : z ∈ centralizer (A : Set G) :=
    (sup_le hZS d.Q_le_centralizer) h1
  exact d.eq_q_of_mem_centralizer h hzC hz2

theorem X_sylow_G_of_center_S
    (h : Hyp G A) (hZS : d.S ⊓ centralizer (d.S : Set G) ≤ centralizer (A : Set G)) :
    IsSylowOf 2 d.X (⊤ : Subgroup G) :=
  d.X_sylow_G h (d.fixes_q_of_center_S_le h hZS)

end Datum

theorem Chart4.X_sylow_G {α : ℕ}
    {d : Datum A} (c : Chart4 d α) (h : Hyp G A)
    (hZ : d.S ⊓ centralizer (d.S : Set G) ≤ zpowers c.t) :
    IsSylowOf 2 d.X (⊤ : Subgroup G) :=
  d.X_sylow_G_of_center_S h
    (hZ.trans (zpowers_le.mpr (d.Q_le_centralizer c.t_mem.1)))

end CFSG.OddStandard.ChengHeld
