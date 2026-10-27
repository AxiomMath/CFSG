module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AQ14C
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AQ15A
public import CFSG.GH74.GLS.Bg.TwoGroups.L27C

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup
open scoped commutatorElement
open CFSG.GH74.GLS.Bg.TwoGroups (commAut)
open CFSG.GH74.GLS.Bg.TwoGroups.L26 (commAut_invariant)
open CFSG.GH74.GLS.Bg.TwoGroups.L27 (commAut_normal)

section Q15B

variable {G : Type} [Group G] [Finite G] {Q Y : Subgroup G} {ρ : G}
variable [(Y.subgroupOf Q).Normal]
private lemma q15_mem_zpowers_sq : ρ * ρ ∈ zpowers ρ := by
  refine Subgroup.mem_zpowers_iff.mpr ⟨((2 : ℕ) : ℤ), ?_⟩
  rw [zpow_natCast, pow_two]
private lemma q15_pi_commutator_rho_gen (hρQ : ρ ∈ normalizer (Q : Set G))
    (hρY : ρ ∈ normalizer (Y : Set G)) (q : ↥Q) :
    (QuotientGroup.mk' (Y.subgroupOf Q) q)⁻¹ *
        quotConj Q Y ρ hρQ hρY (QuotientGroup.mk' (Y.subgroupOf Q) q) =
      QuotientGroup.mk' (Y.subgroupOf Q)
        ⟨⁅(q : G)⁻¹, ρ⁆, q15_commutator_le hρQ
          (Subgroup.commutator_mem_commutator (inv_mem q.2) (Subgroup.mem_zpowers ρ))⟩ := by
  have hqmem : ρ * (q : G) * ρ⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp hρQ (q : G)).mp q.2
  rw [← map_inv]
  rw [show quotConj Q Y ρ hρQ hρY (QuotientGroup.mk' (Y.subgroupOf Q) q) =
      QuotientGroup.mk' (Y.subgroupOf Q) ⟨ρ * (q : G) * ρ⁻¹, hqmem⟩ from
    (quotConj_mk hρQ hρY q hqmem)]
  rw [← map_mul]
  congr 1
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
  group
private lemma q15_pi_commutator_rho (hρQ : ρ ∈ normalizer (Q : Set G))
    (hρY : ρ ∈ normalizer (Y : Set G)) {g₁ : G} (hg₁ : g₁ ∈ Q) :
    (QuotientGroup.mk' (Y.subgroupOf Q))
        ⟨⁅g₁, ρ⁆, q15_commutator_le hρQ
          (Subgroup.commutator_mem_commutator hg₁ (Subgroup.mem_zpowers ρ))⟩ =
      (QuotientGroup.mk' (Y.subgroupOf Q) ⟨g₁, hg₁⟩) *
        ((QuotientGroup.mk' (Y.subgroupOf Q) ⟨g₁, hg₁⟩)⁻¹ *
          quotConj Q Y ρ hρQ hρY
            (QuotientGroup.mk' (Y.subgroupOf Q) ⟨g₁, hg₁⟩))⁻¹ *
        (QuotientGroup.mk' (Y.subgroupOf Q) ⟨g₁, hg₁⟩)⁻¹ := by
  have hqmem : ρ * g₁ * ρ⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hρQ g₁).mp hg₁
  have hq : (⟨⁅g₁, ρ⁆, q15_commutator_le hρQ
        (Subgroup.commutator_mem_commutator hg₁ (Subgroup.mem_zpowers ρ))⟩ : ↥Q) =
      (⟨g₁, hg₁⟩ : ↥Q) * (⟨ρ * g₁ * ρ⁻¹, hqmem⟩ : ↥Q)⁻¹ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
    group
  rw [hq, map_mul, map_inv]
  rw [show (QuotientGroup.mk' (Y.subgroupOf Q)) ⟨ρ * g₁ * ρ⁻¹, hqmem⟩ =
      quotConj Q Y ρ hρQ hρY (QuotientGroup.mk' (Y.subgroupOf Q) ⟨g₁, hg₁⟩) from
    (quotConj_mk hρQ hρY ⟨g₁, hg₁⟩ hqmem).symm]
  group
private lemma q15_pi_comm_rho_mem (hρQ : ρ ∈ normalizer (Q : Set G))
    (hρY : ρ ∈ normalizer (Y : Set G)) {g₁ : G} (hg₁ : g₁ ∈ Q) :
    (QuotientGroup.mk' (Y.subgroupOf Q))
        ⟨⁅g₁, ρ⁆, q15_commutator_le hρQ
          (Subgroup.commutator_mem_commutator hg₁ (Subgroup.mem_zpowers ρ))⟩ ∈
      commAut (quotConj Q Y ρ hρQ hρY) := by
  rw [q15_pi_commutator_rho hρQ hρY hg₁]
  exact (commAut_normal (quotConj Q Y ρ hρQ hρY)).conj_mem _
    (inv_mem (Subgroup.subset_closure ⟨_, rfl⟩)) _
private lemma q15_pi_commutator_rho2 (hρQ : ρ ∈ normalizer (Q : Set G))
    (hρY : ρ ∈ normalizer (Y : Set G)) {g₁ : G} (hg₁ : g₁ ∈ Q) :
    (QuotientGroup.mk' (Y.subgroupOf Q))
        ⟨⁅g₁, ρ * ρ⁆, q15_commutator_le hρQ
          (Subgroup.commutator_mem_commutator hg₁ q15_mem_zpowers_sq)⟩ =
      (QuotientGroup.mk' (Y.subgroupOf Q))
          ⟨⁅g₁, ρ⁆, q15_commutator_le hρQ
            (Subgroup.commutator_mem_commutator hg₁ (Subgroup.mem_zpowers ρ))⟩ *
        quotConj Q Y ρ hρQ hρY
          ((QuotientGroup.mk' (Y.subgroupOf Q))
            ⟨⁅g₁, ρ⁆, q15_commutator_le hρQ
              (Subgroup.commutator_mem_commutator hg₁ (Subgroup.mem_zpowers ρ))⟩) := by
  have h₁ : (⁅g₁, ρ⁆ : G) ∈ Q :=
    q15_commutator_le hρQ
      (Subgroup.commutator_mem_commutator hg₁ (Subgroup.mem_zpowers ρ))
  have hmem : ρ * ⁅g₁, ρ⁆ * ρ⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp hρQ ⁅g₁, ρ⁆).mp h₁
  have hq : (⟨⁅g₁, ρ * ρ⁆, q15_commutator_le hρQ
        (Subgroup.commutator_mem_commutator hg₁ q15_mem_zpowers_sq)⟩ : ↥Q) =
      (⟨⁅g₁, ρ⁆, h₁⟩ : ↥Q) * ⟨ρ * ⁅g₁, ρ⁆ * ρ⁻¹, hmem⟩ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, commutatorElement_def]
    group
  rw [hq, map_mul]
  rw [show (QuotientGroup.mk' (Y.subgroupOf Q)) ⟨ρ * ⁅g₁, ρ⁆ * ρ⁻¹, hmem⟩ =
      quotConj Q Y ρ hρQ hρY
        ((QuotientGroup.mk' (Y.subgroupOf Q)) ⟨⁅g₁, ρ⁆, h₁⟩) from
    (quotConj_mk hρQ hρY ⟨⁅g₁, ρ⁆, h₁⟩ hmem).symm]
private lemma q15_pi_commutator_mem (hρ3 : ρ ^ 3 = 1)
    (hρQ : ρ ∈ normalizer (Q : Set G)) (hρY : ρ ∈ normalizer (Y : Set G))
    {g₁ : G} (hg₁ : g₁ ∈ Q) {g₂ : G} (hg₂ : g₂ ∈ zpowers ρ) :
    (QuotientGroup.mk' (Y.subgroupOf Q))
        ⟨⁅g₁, g₂⁆, q15_commutator_le hρQ
          (Subgroup.commutator_mem_commutator hg₁ hg₂)⟩ ∈
      commAut (quotConj Q Y ρ hρQ hρY) := by
  rw [Subgroup.mem_zpowers_iff] at hg₂
  obtain ⟨k, hk⟩ := hg₂
  have h3 : ρ ^ (3 : ℤ) = 1 := by simpa using hρ3
  have hmod : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by
    have h1 := Int.emod_nonneg k (by norm_num : (3 : ℤ) ≠ 0)
    have h2 := Int.emod_lt_of_pos k (by norm_num : (0 : ℤ) < 3)
    omega
  have hz : g₂ = 1 ∨ g₂ = ρ ∨ g₂ = ρ * ρ := by
    have hk' : ρ ^ k = ρ ^ (k % 3) := zpow_eq_zpow_emod k h3
    rw [← hk]
    rcases hmod with h0 | h1 | h2
    · left; rw [hk', h0, zpow_zero]
    · right; left; rw [hk', h1, zpow_one]
    · right; right
      rw [hk', h2, show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, pow_two]
  clear hk
  rcases hz with h1 | h1 | h1 <;> subst g₂
  · have hz1 : (⟨⁅g₁, (1 : G)⁆, q15_commutator_le hρQ
          (Subgroup.commutator_mem_commutator hg₁ hg₂)⟩ : ↥Q) = 1 := by
      apply Subtype.ext
      change (⁅g₁, (1 : G)⁆ : G) = (1 : G)
      group
    rw [hz1, map_one]
    exact Subgroup.one_mem _
  · exact q15_pi_comm_rho_mem hρQ hρY hg₁
  · rw [q15_pi_commutator_rho2 hρQ hρY hg₁]
    exact mul_mem (q15_pi_comm_rho_mem hρQ hρY hg₁)
      (commAut_invariant _ _ (q15_pi_comm_rho_mem hρQ hρY hg₁))
theorem q15_map_commutator_eq (hρ3 : ρ ^ 3 = 1) (hρQ : ρ ∈ normalizer (Q : Set G))
    (hρY : ρ ∈ normalizer (Y : Set G)) :
    ((⁅Q, zpowers ρ⁆ : Subgroup G).subgroupOf Q).map (QuotientGroup.mk' (Y.subgroupOf Q)) =
      commAut (quotConj Q Y ρ hρQ hρY) := by
  have hK : (⁅Q, zpowers ρ⁆ : Subgroup G) ≤
      ((commAut (quotConj Q Y ρ hρQ hρY)).comap
        (QuotientGroup.mk' (Y.subgroupOf Q))).map Q.subtype := by
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    exact ⟨⟨⁅g₁, g₂⁆, q15_commutator_le hρQ
          (Subgroup.commutator_mem_commutator hg₁ hg₂)⟩,
        q15_pi_commutator_mem hρ3 hρQ hρY hg₁ hg₂, rfl⟩
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    intro x hx
    rw [← Subgroup.mem_map_iff_mem Q.subtype_injective]
    exact hK (Subgroup.mem_subgroupOf.mp hx)
  · rw [commAut, Subgroup.closure_le]
    rintro _ ⟨g, rfl⟩
    obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective (Y.subgroupOf Q) g
    refine ⟨⟨⁅(q : G)⁻¹, ρ⁆, q15_commutator_le hρQ
        (Subgroup.commutator_mem_commutator (inv_mem q.2) (Subgroup.mem_zpowers ρ))⟩,
      Subgroup.mem_subgroupOf.mpr
        (Subgroup.commutator_mem_commutator (inv_mem q.2) (Subgroup.mem_zpowers ρ)),
      (q15_pi_commutator_rho_gen hρQ hρY q).symm⟩
theorem q15_subgroupOf_eq_comap (hρ3 : ρ ^ 3 = 1) (hρQ : ρ ∈ normalizer (Q : Set G))
    (hρY : ρ ∈ normalizer (Y : Set G)) (hY : Y ≤ ⁅Q, zpowers ρ⁆) :
    (⁅Q, zpowers ρ⁆ : Subgroup G).subgroupOf Q =
      (commAut (quotConj Q Y ρ hρQ hρY)).comap (QuotientGroup.mk' (Y.subgroupOf Q)) := by
  have h1 := Subgroup.comap_map_eq (f := QuotientGroup.mk' (Y.subgroupOf Q))
    ((⁅Q, zpowers ρ⁆ : Subgroup G).subgroupOf Q)
  rw [q15_map_commutator_eq hρ3 hρQ hρY,
    QuotientGroup.ker_mk' (Y.subgroupOf Q)] at h1
  have hle : Y.subgroupOf Q ≤ (⁅Q, zpowers ρ⁆ : Subgroup G).subgroupOf Q := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hY hx
  rw [sup_eq_left.mpr hle] at h1
  exact h1.symm
theorem q15_mem_commutator_iff (hρ3 : ρ ^ 3 = 1) (hρQ : ρ ∈ normalizer (Q : Set G))
    (hρY : ρ ∈ normalizer (Y : Set G)) (hY : Y ≤ ⁅Q, zpowers ρ⁆) {x : G} (hx : x ∈ Q) :
    x ∈ ⁅Q, zpowers ρ⁆ ↔
      (QuotientGroup.mk (⟨x, hx⟩ : ↥Q) : ↥Q ⧸ Y.subgroupOf Q) ∈
        commAut (quotConj Q Y ρ hρQ hρY) := by
  change (⟨x, hx⟩ : ↥Q) ∈ (⁅Q, zpowers ρ⁆ : Subgroup G).subgroupOf Q ↔
    (QuotientGroup.mk (⟨x, hx⟩ : ↥Q) : ↥Q ⧸ Y.subgroupOf Q) ∈
      commAut (quotConj Q Y ρ hρQ hρY)
  rw [q15_subgroupOf_eq_comap hρ3 hρQ hρY hY, Subgroup.mem_comap]
  rfl
theorem q15_sectionIso_commutator (hρ3 : ρ ^ 3 = 1) (hρQ : ρ ∈ normalizer (Q : Set G))
    (hρY : ρ ∈ normalizer (Y : Set G)) (hY : Y ≤ ⁅Q, zpowers ρ⁆) {K : Type} [Group K]
    (e : ↥(commAut (quotConj Q Y ρ hρQ hρY)) ≃* K) :
    Sec4SectionIso (⁅Q, zpowers ρ⁆ : Subgroup G) Y K := by
  have hle : (⁅Q, zpowers ρ⁆ : Subgroup G) ≤ Q := q15_commutator_le hρQ
  let ψ : ↥(⁅Q, zpowers ρ⁆ : Subgroup G) →* ↥(commAut (quotConj Q Y ρ hρQ hρY)) :=
    ((QuotientGroup.mk' (Y.subgroupOf Q)).comp (Subgroup.inclusion hle)).codRestrict
      (commAut (quotConj Q Y ρ hρQ hρY))
      (fun x => (q15_mem_commutator_iff hρ3 hρQ hρY hY (hle x.2)).mp x.2)
  refine ⟨e.toMonoidHom.comp ψ, e.surjective.comp ?_, ?_⟩
  · intro a
    have ha : (a : ↥Q ⧸ Y.subgroupOf Q) ∈
        ((⁅Q, zpowers ρ⁆ : Subgroup G).subgroupOf Q).map
          (QuotientGroup.mk' (Y.subgroupOf Q)) := by
      rw [q15_map_commutator_eq hρ3 hρQ hρY]
      exact a.2
    rw [Subgroup.mem_map] at ha
    obtain ⟨y, hy, hyπ⟩ := ha
    refine ⟨⟨y, Subgroup.mem_subgroupOf.mp hy⟩, ?_⟩
    apply Subtype.ext
    show (QuotientGroup.mk' (Y.subgroupOf Q))
        (Subgroup.inclusion hle ⟨y, Subgroup.mem_subgroupOf.mp hy⟩) = ↑a
    rw [show Subgroup.inclusion hle ⟨y, Subgroup.mem_subgroupOf.mp hy⟩ = y from rfl, hyπ]
  · rw [MonoidHom.ker_comp_of_injective ψ e.toMonoidHom e.injective]
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      have hxq : (QuotientGroup.mk' (Y.subgroupOf Q))
          (Subgroup.inclusion hle x) = 1 := by
        have h1 : ((ψ x : ↥(commAut (quotConj Q Y ρ hρQ hρY))) :
            ↥Q ⧸ Y.subgroupOf Q) = 1 := by
          rw [hx]
          rfl
        exact h1
      have hmem := (QuotientGroup.eq_one_iff (Subgroup.inclusion hle x)).mp hxq
      rwa [Subgroup.mem_subgroupOf] at hmem
    · intro hx
      have hxq : (QuotientGroup.mk' (Y.subgroupOf Q))
          (Subgroup.inclusion hle x) = 1 :=
        (QuotientGroup.eq_one_iff (Subgroup.inclusion hle x)).mpr (by
          rwa [Subgroup.mem_subgroupOf])
      apply Subtype.ext
      change ((ψ x : ↥(commAut (quotConj Q Y ρ hρQ hρY))) : ↥Q ⧸ Y.subgroupOf Q) =
        ((1 : ↥(commAut (quotConj Q Y ρ hρQ hρY))) : ↥Q ⧸ Y.subgroupOf Q)
      exact hxq
theorem q15_card_commutator (hρ3 : ρ ^ 3 = 1) (hρQ : ρ ∈ normalizer (Q : Set G))
    (hρY : ρ ∈ normalizer (Y : Set G)) (hY : Y ≤ ⁅Q, zpowers ρ⁆) :
    Nat.card (⁅Q, zpowers ρ⁆ : Subgroup G) =
      Nat.card Y * Nat.card (commAut (quotConj Q Y ρ hρQ hρY)) := by
  obtain ⟨φ, hφs, hφk⟩ :=
    q15_sectionIso_commutator hρ3 hρQ hρY hY (MulEquiv.refl _)
  have h1 := Subgroup.card_ker_mul_card_of_surjective hφs
  rw [hφk, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hY).toEquiv] at h1
  exact h1.symm
theorem q15_t_not_mem (hρ3 : ρ ^ 3 = 1) (hρQ : ρ ∈ normalizer (Q : Set G))
    (hρY : ρ ∈ normalizer (Y : Set G)) (hY : Y ≤ ⁅Q, zpowers ρ⁆) {t : G} (htQ : t ∈ Q)
    (htY : t ∉ Y)
    (hinf : commAut (quotConj Q Y ρ hρQ hρY) ⊓
      zpowers (QuotientGroup.mk (⟨t, htQ⟩ : ↥Q) : ↥Q ⧸ Y.subgroupOf Q) = ⊥) :
    t ∉ ⁅Q, zpowers ρ⁆ := by
  intro ht
  have hmem : (QuotientGroup.mk (⟨t, htQ⟩ : ↥Q) : ↥Q ⧸ Y.subgroupOf Q) ∈
      commAut (quotConj Q Y ρ hρQ hρY) :=
    (q15_mem_commutator_iff hρ3 hρQ hρY hY htQ).mp ht
  have hzp : (QuotientGroup.mk (⟨t, htQ⟩ : ↥Q) : ↥Q ⧸ Y.subgroupOf Q) ∈
      zpowers (QuotientGroup.mk (⟨t, htQ⟩ : ↥Q) : ↥Q ⧸ Y.subgroupOf Q) :=
    Subgroup.mem_zpowers _
  have hbot : (QuotientGroup.mk (⟨t, htQ⟩ : ↥Q) : ↥Q ⧸ Y.subgroupOf Q) ∈
      (⊥ : Subgroup (↥Q ⧸ Y.subgroupOf Q)) := by
    rw [← hinf]
    exact Subgroup.mem_inf.mpr ⟨hmem, hzp⟩
  rw [Subgroup.mem_bot] at hbot
  apply htY
  have hYmem : (⟨t, htQ⟩ : ↥Q) ∈ Y.subgroupOf Q :=
    (QuotientGroup.eq_one_iff (⟨t, htQ⟩ : ↥Q)).mp hbot
  rwa [Subgroup.mem_subgroupOf] at hYmem
theorem q15_Q_eq_sup (hρ3 : ρ ^ 3 = 1) (hρQ : ρ ∈ normalizer (Q : Set G))
    (hρY : ρ ∈ normalizer (Y : Set G)) (hY : Y ≤ ⁅Q, zpowers ρ⁆) {t : G} (htQ : t ∈ Q)
    (hsup : commAut (quotConj Q Y ρ hρQ hρY) ⊔
      zpowers (QuotientGroup.mk (⟨t, htQ⟩ : ↥Q) : ↥Q ⧸ Y.subgroupOf Q) = ⊤) :
    Q = ⁅Q, zpowers ρ⁆ ⊔ zpowers t := by
  apply le_antisymm
  · intro x hx
    have hH : ((⁅Q, zpowers ρ⁆ : Subgroup G) ⊔ zpowers t).subgroupOf Q = ⊤ := by
      have hleY : Y.subgroupOf Q ≤
          ((⁅Q, zpowers ρ⁆ : Subgroup G) ⊔ zpowers t).subgroupOf Q := by
        intro y hy
        rw [Subgroup.mem_subgroupOf] at hy ⊢
        exact (le_sup_left : (⁅Q, zpowers ρ⁆ : Subgroup G) ≤
          (⁅Q, zpowers ρ⁆ : Subgroup G) ⊔ zpowers t) (hY hy)
      have hmap : (((⁅Q, zpowers ρ⁆ : Subgroup G) ⊔ zpowers t).subgroupOf Q).map
          (QuotientGroup.mk' (Y.subgroupOf Q)) = ⊤ := by
        rw [eq_top_iff, ← hsup]
        apply sup_le
        · rw [← q15_map_commutator_eq hρ3 hρQ hρY]
          apply Subgroup.map_mono
          intro z hz
          rw [Subgroup.mem_subgroupOf] at hz ⊢
          exact (le_sup_left : (⁅Q, zpowers ρ⁆ : Subgroup G) ≤
            (⁅Q, zpowers ρ⁆ : Subgroup G) ⊔ zpowers t) hz
        · rw [Subgroup.zpowers_le]
          exact Subgroup.mem_map_of_mem (QuotientGroup.mk' (Y.subgroupOf Q))
            (Subgroup.mem_subgroupOf.mpr
              ((le_sup_right : zpowers t ≤ (⁅Q, zpowers ρ⁆ : Subgroup G) ⊔ zpowers t)
                (Subgroup.mem_zpowers t)))
      have h1 : (⊤ : Subgroup ↥Q) =
          (((⁅Q, zpowers ρ⁆ : Subgroup G) ⊔ zpowers t).subgroupOf Q) ⊔
            (QuotientGroup.mk' (Y.subgroupOf Q)).ker := by
        rw [← Subgroup.comap_top (QuotientGroup.mk' (Y.subgroupOf Q)),
          ← Subgroup.comap_map_eq (QuotientGroup.mk' (Y.subgroupOf Q)) _, hmap]
      rw [show (QuotientGroup.mk' (Y.subgroupOf Q)).ker = Y.subgroupOf Q from
          QuotientGroup.ker_mk' (Y.subgroupOf Q), sup_eq_left.mpr hleY] at h1
      exact h1.symm
    have hxH : (⟨x, hx⟩ : ↥Q) ∈
        ((⁅Q, zpowers ρ⁆ : Subgroup G) ⊔ zpowers t).subgroupOf Q := by
      rw [hH]
      exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp hxH
  · exact sup_le (q15_commutator_le hρQ) (Subgroup.zpowers_le.mpr htQ)

end Q15B
end CFSG.OddStandard.SmallF3.HarrisU33.S4A
