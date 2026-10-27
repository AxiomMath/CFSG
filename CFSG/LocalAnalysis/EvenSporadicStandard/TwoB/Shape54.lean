module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.Shape54Good
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.Shape54Quot
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.Lemma210Two
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.Lemma57

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoB

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.TwoFi22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {t z : G}

theorem mk_mul_comm_iff_mem_zpowers {Q : Subgroup G} {z : G} [((zpowers z).subgroupOf Q).Normal]
    (a b : ↥Q) : (a : ↥Q ⧸ (zpowers z).subgroupOf Q) * b = b * a ↔
      (a : G) * b * (a : G)⁻¹ * (b : G)⁻¹ ∈ zpowers z := by
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq_iff_div_mem,
    mem_subgroupOf]
  have e : ((a * b / (b * a) : ↥Q) : G) = (a : G) * b * (a : G)⁻¹ * (b : G)⁻¹ := by
    simp [div_eq_mul_inv, mul_assoc]
  rw [e]

section Certified


theorem Level55.exists_involution_shape (d : Level55 G t z)
    {Q : Subgroup G} (hQC : Q ≤ centZ z) (hKQ : centPair z t ≤ Q)
    [((zpowers z).subgroupOf Q).Normal] :
    ∃ τ : ↥Q ⧸ (zpowers z).subgroupOf Q, orderOf τ = 2 ∧
      CFSG.IsCharacteristicP 2 ↥(centralizer ({τ} : Set (↥Q ⧸ (zpowers z).subgroupOf Q))) ∧
      IsMulCommutative (CFSG.pCore 2
        ↥(centralizer ({τ} : Set (↥Q ⧸ (zpowers z).subgroupOf Q)))) ∧
      Nonempty (↥(centralizer ({τ} : Set (↥Q ⧸ (zpowers z).subgroupOf Q))) ⧸
        CFSG.pCore 2 ↥(centralizer ({τ} : Set (↥Q ⧸ (zpowers z).subgroupOf Q))) ≃*
          Carrier .Co2) := by
  have htK : t ∈ centPair z t := mem_centPair_iff.2 ⟨d.zt_comm, rfl⟩
  set N : Subgroup G := Q ⊓ normPair z t with hN
  have hKN : centPair z t ≤ N := le_inf hKQ (centPair_le_normPair z t)
  have hNC : N ≤ centZ z := inf_le_left.trans hQC
  have hNn : N ≤ normPair z t := inf_le_right
  obtain ⟨Y₀, hg⟩ := d.exists_good hKN hNC hNn
  have hnorm : (Y₀.subgroupOf N).Normal :=
    ⟨fun u hu g => mem_subgroupOf.2 (hg.normal g g.2 u (mem_subgroupOf.1 hu))⟩
  obtain ⟨e⟩ := hg.nonempty_quotient hKN
  set τ : ↥Q ⧸ (zpowers z).subgroupOf Q := ((⟨t, hKQ htK⟩ : ↥Q) : ↥Q ⧸ (zpowers z).subgroupOf Q)
    with hτdef
  have hτ : orderOf τ = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [hτdef, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_subgroupOf]
      have : t ^ 2 = 1 := by rw [← d.t_ord]; exact pow_orderOf_eq_one t
      show t ^ 2 ∈ zpowers z
      rw [this]
      exact one_mem _
    · rw [hτdef, Ne, QuotientGroup.eq_one_iff, mem_subgroupOf]
      intro h
      rcases eq_one_or_eq_of_mem_zpowers_two d.z_ord h with h1 | h1
      · have := d.t_ord
        rw [show t = 1 from h1, orderOf_one] at this
        omega
      · exact d.z_ne_t h1.symm
  have hNQ : N ≤ Q := inf_le_left
  have hnt : ∀ n ∈ N, n * t * n⁻¹ * t⁻¹ ∈ zpowers z := by
    intro n hn
    have hnz : n * z = z * n := mem_centralizer_singleton_iff.1 (hNC hn)
    rcases d.conj_t_of_mem_normPair hnz (hNn hn) with h | h
    · rw [h]
      simp
    · rw [h]
      have : t * z * t⁻¹ = z := by rw [← d.zt_comm]; group
      rw [this]
      exact mem_zpowers z
  let ψ₀ : ↥N →* ↥Q ⧸ (zpowers z).subgroupOf Q :=
    (QuotientGroup.mk' ((zpowers z).subgroupOf Q)).comp (Subgroup.inclusion hNQ)
  have hψ₀ : ∀ n : ↥N, ψ₀ n ∈ centralizer ({τ} : Set (↥Q ⧸ (zpowers z).subgroupOf Q)) := by
    intro n
    rw [mem_centralizer_singleton_iff]
    exact (mk_mul_comm_iff_mem_zpowers (Subgroup.inclusion hNQ n) ⟨t, hKQ htK⟩).2 (hnt n n.2)
  let ψ : ↥N →* ↥(centralizer ({τ} : Set (↥Q ⧸ (zpowers z).subgroupOf Q))) :=
    ψ₀.codRestrict _ hψ₀
  have hψ : Function.Surjective ψ := by
    rintro ⟨j, hj⟩
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective j
    have hqc := mem_centralizer_singleton_iff.1 hj
    have hcomm := (mk_mul_comm_iff_mem_zpowers q ⟨t, hKQ htK⟩).1 hqc
    have hqz : (q : G) * z = z * q := mem_centralizer_singleton_iff.1 (hQC q.2)
    have hqn : (q : G) ∈ normPair z t := by
      refine mem_normPair_of_conj_t hqz ?_
      rcases eq_one_or_eq_of_mem_zpowers_two d.z_ord hcomm with h | h
      · left
        exact mul_inv_eq_one.1 h
      · right
        calc (q : G) * t * (q : G)⁻¹ = ((q : G) * t * (q : G)⁻¹ * t⁻¹) * t := by group
          _ = z * t := by rw [h]
          _ = t * z := d.zt_comm
    exact ⟨⟨q, mem_inf.2 ⟨q.2, hqn⟩⟩, Subtype.ext rfl⟩
  have hker : ψ.ker ≤ Y₀.subgroupOf N := by
    intro n hn
    rw [MonoidHom.mem_ker] at hn
    have h1 : ψ₀ n = 1 := congrArg Subtype.val hn
    have h2 : (n : G) ∈ zpowers z := by
      have : (QuotientGroup.mk (Subgroup.inclusion hNQ n) :
          ↥Q ⧸ (zpowers z).subgroupOf Q) = 1 := h1
      rw [QuotientGroup.eq_one_iff, mem_subgroupOf] at this
      exact this
    exact mem_subgroupOf.2 (hg.O2K_le (d.pair_le_O2K (mem_sup_left h2)))
  have hcomm : ∀ a ∈ Y₀.subgroupOf N, ∀ b ∈ Y₀.subgroupOf N, ψ a * ψ b = ψ b * ψ a := by
    intro a ha b hb
    apply Subtype.ext
    exact (mk_mul_comm_iff_mem_zpowers (Subgroup.inclusion hNQ a) (Subgroup.inclusion hNQ b)).2
      (hg.comm a (mem_subgroupOf.1 ha) b (mem_subgroupOf.1 hb))
  have hcent : ∀ h : ↥N, (∀ y ∈ Y₀.subgroupOf N, ψ h * ψ y = ψ y * ψ h) →
      h ∈ Y₀.subgroupOf N := by
    intro h hh
    refine mem_subgroupOf.2 (hg.cent h h.2 fun w hw => ?_)
    have hwN : w ∈ N := hg.le hw
    have := congrArg Subtype.val (hh ⟨w, hwN⟩ (mem_subgroupOf.2 hw))
    exact (mk_mul_comm_iff_mem_zpowers (Subgroup.inclusion hNQ h)
      (Subgroup.inclusion hNQ ⟨w, hwN⟩)).1 this
  have := hnorm
  have hp : IsPGroup 2 (Y₀.subgroupOf N) := hg.pgroup.of_equiv (subgroupOfEquivOfLe hg.le).symm
  obtain ⟨hchar, hcommut, ⟨e'⟩⟩ :=
    exists_shape_of_surjective ψ hψ (Y₀.subgroupOf N) hp e hker hcomm hcent
  exact ⟨τ, hτ, hchar, hcommut, ⟨e'⟩⟩

theorem Level55.false_of_quotient_simple (d : Level55 G t z) (h210 : DS81Lemma210Two)
    {Q : Subgroup G} (hQC : Q ≤ centZ z) (hKQ : centPair z t ≤ Q)
    [((zpowers z).subgroupOf Q).Normal]
    [IsSimpleGroup (↥Q ⧸ (zpowers z).subgroupOf Q)]
    (hnonab : ∃ a b : ↥Q ⧸ (zpowers z).subgroupOf Q, a * b ≠ b * a)
    (hcat : CFSG.Blueprint.Catalog (↥Q ⧸ (zpowers z).subgroupOf Q)) : False := by
  obtain ⟨τ, hτ, hchar, hcommut, hquot⟩ := d.exists_involution_shape hQC hKQ
  exact h210 _ hnonab hcat τ hτ hchar hcommut hquot

end Certified

end CFSG.EvenSporadicStandard.TwoB
