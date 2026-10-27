module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutSpecial
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutAmbient

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open CFSG.OddStandard.SmallF3.HarrisU33.Outside

variable {G : Type} [Group G] [Finite G]

private lemma mem_normalizer_of_conj_mem {Ξ : Subgroup G} {ρ : G}
    (hρΞ : ∀ x ∈ Ξ, ρ * x * ρ⁻¹ ∈ Ξ) : ρ ∈ normalizer (Ξ : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact map_eq_of_forall_mem (MulAut.conj ρ) Ξ (fun x hx => by
    simpa [MulAut.conj_apply] using hρΞ x hx)

theorem sq_comm_mem_of_fpf_quot {Ξ Y V' : Subgroup G} {ρ : G} (hρ3 : ρ ^ 3 = 1)
    (hρΞ : ∀ x ∈ Ξ, ρ * x * ρ⁻¹ ∈ Ξ) (hρV : ∀ v ∈ V', ρ * v * ρ⁻¹ ∈ V')
    (hV'Y : V' ≤ Y) (hYΞ : Y ≤ Ξ) (hYc : ∀ y ∈ Y, ∀ x ∈ Ξ, x * y = y * x)
    (hΞ : Nat.card Ξ = 256) (hY : Nat.card Y = 16) (hV' : Nat.card V' = 4)
    (hfpf : ∀ x ∈ Ξ, x * ρ = ρ * x → x = 1)
    (hnab : ∃ a ∈ Ξ, ∃ b ∈ Ξ, a * b * a⁻¹ * b⁻¹ ∉ V') :
    (∀ x ∈ Ξ, x * x ∈ Y) ∧ ∀ x ∈ Ξ, ∀ x' ∈ Ξ, x * x' * x⁻¹ * x'⁻¹ ∈ Y := by
  classical
  have hV'Ξ : V' ≤ Ξ := hV'Y.trans hYΞ
  let N : Subgroup Ξ := V'.subgroupOf Ξ
  have hNY : N ≤ Y.subgroupOf Ξ := Subgroup.subgroupOf_mono Ξ hV'Y
  have hNle_center : N ≤ Subgroup.center Ξ := by
    intro n hn
    rw [Subgroup.mem_center_iff]
    intro x
    apply Subtype.ext
    show x.1 * n.1 = n.1 * x.1
    have hnV : n.1 ∈ V' := by
      have h := hn
      change n.1 ∈ V' at h
      exact h
    exact hYc n.1 (hV'Y hnV) x.1 x.2
  haveI hNn : N.Normal := Subgroup.normal_of_le_center hNle_center
  have hYle_center : Y.subgroupOf Ξ ≤ Subgroup.center Ξ := by
    intro y hy
    rw [Subgroup.mem_center_iff]
    intro x
    apply Subtype.ext
    show x.1 * y.1 = y.1 * x.1
    have hyY : y.1 ∈ Y := by
      have h := hy
      change y.1 ∈ Y at h
      exact h
    exact hYc y.1 hyY x.1 x.2
  haveI hYn : (Y.subgroupOf Ξ).Normal := Subgroup.normal_of_le_center hYle_center
  have hρmem : ρ ∈ normalizer (Ξ : Set G) := mem_normalizer_of_conj_mem hρΞ
  let ρ₀ : MulAut Ξ := conjAut Ξ ρ hρmem
  have hρ0cube : ρ₀ ^ 3 = 1 := by
    change (conjAut Ξ ρ hρmem) ^ 3 = 1
    have hp := conjAut_pow Ξ hρmem 3 (pow_mem hρmem 3)
    have hconj : conjAut Ξ (ρ ^ 3) (pow_mem hρmem 3) = 1 := by
      rw [conjAut_eq_one_iff]
      intro h _
      rw [hρ3, one_mul, mul_one]
    rw [← hp]
    exact hconj
  have hρ0fpf : ∀ g : Ξ, ρ₀ g = g → g = 1 := by
    intro g hg
    have hg' : ρ * g.1 * ρ⁻¹ = g.1 := by
      have h := congrArg Subtype.val hg
      simpa [ρ₀, conjAut_coe] using h
    have hcomm : g.1 * ρ = ρ * g.1 := by
      have h := congrArg (fun z : G => z * ρ) hg'
      simpa using h.symm
    exact Subtype.ext (hfpf g.1 g.2 hcomm)
  have hNinv : N.map ρ₀.toMonoidHom = N :=
    map_eq_of_forall_mem ρ₀ N (fun n hn => by
      have hnV : n.1 ∈ V' := by
        have h := hn
        change n.1 ∈ V' at h
        exact h
      change (ρ₀ n : G) ∈ V'
      change (conjAut Ξ ρ hρmem n : G) ∈ V'
      rw [conjAut_coe]
      simpa using hρV n.1 hnV)
  let T := Ξ ⧸ N
  haveI hFinT : Finite T :=
    Finite.of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
  let ρbar : MulAut T := quotAut ρ₀ N hNinv
  have hNcard : Nat.card N = 4 := by
    have h := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV'Ξ).toEquiv
    rw [hV'] at h
    exact h
  have hcardT : Nat.card T = 64 := by
    change Nat.card (Ξ ⧸ N) = 64
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    rw [hΞ, hNcard] at h
    omega
  have hnonab : ∃ a b : T, a * b ≠ b * a := by
    obtain ⟨a, ha, b, hb, hcomm⟩ := hnab
    refine ⟨QuotientGroup.mk' N ⟨a, ha⟩, QuotientGroup.mk' N ⟨b, hb⟩, ?_⟩
    intro heq
    apply hcomm
    have heq' : ((⟨a, ha⟩ * ⟨b, hb⟩ : Ξ) : T) = ((⟨b, hb⟩ * ⟨a, ha⟩ : Ξ) : T) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]
      exact heq
    have hdiv : (⟨a, ha⟩ * ⟨b, hb⟩) / (⟨b, hb⟩ * ⟨a, ha⟩) ∈ N :=
      (QuotientGroup.eq_iff_div_mem).mp heq'
    have hmemV : ((⟨a, ha⟩ * ⟨b, hb⟩) / (⟨b, hb⟩ * ⟨a, ha⟩) : Ξ).1 ∈ V' := by
      have h := hdiv
      change ((⟨a, ha⟩ * ⟨b, hb⟩) / (⟨b, hb⟩ * ⟨a, ha⟩) : Ξ).1 ∈ V' at h
      exact h
    have hval : ((⟨a, ha⟩ * ⟨b, hb⟩) / (⟨b, hb⟩ * ⟨a, ha⟩) : Ξ).1 =
        a * b * a⁻¹ * b⁻¹ := by
      rw [Subgroup.coe_div, Subgroup.coe_mul, Subgroup.coe_mul, div_eq_mul_inv]
      group
    rw [hval] at hmemV
    exact hmemV
  have hFpf : FpfNonab T ρbar :=
    ⟨hcardT, hnonab, quotAut_pow_three ρ₀ hρ0cube N hNinv,
      fun x hx => quotAut_fpf ρ₀ hρ0cube hρ0fpf N hNinv x hx⟩
  have hSpec : FpfSpecial T := hFpf.special
  let Ybar : Subgroup T := (Y.subgroupOf Ξ).map (QuotientGroup.mk' N)
  have hYbar_le_center : Ybar ≤ Subgroup.center T := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro t
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hz
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N t
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    show g.1 * y.1 = y.1 * g.1
    have hyY : y.1 ∈ Y := by
      have h := hy
      change y.1 ∈ Y at h
      exact h
    exact hYc y.1 hyY g.1 g.2
  have hcard_quot_Ybar : Nat.card (T ⧸ Ybar) = 16 := by
    have heq := QuotientGroup.quotientQuotientEquivQuotient N (Y.subgroupOf Ξ) hNY
    have h1 : Nat.card (T ⧸ Ybar) = Nat.card (Ξ ⧸ (Y.subgroupOf Ξ)) :=
      Nat.card_congr heq.toEquiv
    rw [h1]
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Y.subgroupOf Ξ)
    have hYsub : Nat.card (Y.subgroupOf Ξ) = 16 := by
      have h := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYΞ).toEquiv
      rw [hY] at h
      exact h
    rw [hΞ, hYsub] at h2
    omega
  have hcardYbar : Nat.card Ybar = 4 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup Ybar
    rw [hcardT, hcard_quot_Ybar] at h
    omega
  have hcenter : Subgroup.center T = Ybar :=
    (Subgroup.eq_of_le_of_card_ge hYbar_le_center
      (by simp [hSpec.card_center, hcardYbar])).symm
  have key : ∀ c : Ξ, QuotientGroup.mk' N c ∈ Subgroup.center T → c.1 ∈ Y := by
    intro c hc
    have hcY : QuotientGroup.mk' N c ∈ Ybar := by
      rwa [hcenter] at hc
    obtain ⟨y, hy, hyc⟩ := Subgroup.mem_map.mp hcY
    have hyc' : (y : Ξ ⧸ N) = (c : Ξ ⧸ N) := by
      simpa only [QuotientGroup.mk'_apply] using hyc
    have hdiff : y⁻¹ * c ∈ N := QuotientGroup.eq.mp hyc'
    have hmemV : (y⁻¹ * c).1 ∈ V' := by
      have h := hdiff
      change (y⁻¹ * c).1 ∈ V' at h
      exact h
    have hyY : y.1 ∈ Y := by
      have h := hy
      change y.1 ∈ Y at h
      exact h
    have hceq : c.1 = y.1 * (y⁻¹ * c).1 := by
      show c.1 = y.1 * (y.1⁻¹ * c.1)
      group
    rw [hceq]
    exact mul_mem hyY (hV'Y hmemV)
  refine ⟨?_, ?_⟩
  · intro x hx
    have h := key (⟨x, hx⟩ * ⟨x, hx⟩) (by
      rw [map_mul]
      exact hSpec.sq_mem (QuotientGroup.mk' N ⟨x, hx⟩))
    simpa using h
  · intro x hx x' hx'
    have h := key (⟨x, hx⟩ * ⟨x', hx'⟩ * ⟨x, hx⟩⁻¹ * ⟨x', hx'⟩⁻¹) (by
      simp only [map_mul, map_inv]
      exact hSpec.comm_mem (QuotientGroup.mk' N ⟨x, hx⟩)
        (QuotientGroup.mk' N ⟨x', hx'⟩))
    simpa using h

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
