module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.Branch55
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.Act55
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.XStruct
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.Normal55

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoB

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.TwoFi22
open scoped commutatorElement
open Act55

variable {G : Type} [Group G] [Finite G] {t z : G}

theorem Level55.card_O2K (d : Level55 G t z) : Nat.card (O2In (centPair z t)) = 2 ^ 24 := by
  rw [d.O2K, card_sup_zpowers_of_orderOf_eq_two d.t_ord d.t_not_mem
    (fun r hr => d.R0_comm_t hr), d.R0_card]
  norm_num

theorem Level55.exists_mem_O2K_not_mem_pair (d : Level55 G t z) :
    ∃ y ∈ O2In (centPair z t), y ∉ pair z t := by
  by_contra h
  push Not at h
  have hle : O2In (centPair z t) ≤ pair z t := h
  have h1 := Subgroup.card_le_of_le hle
  rw [d.card_O2K] at h1
  have h2 := card_pair_le d.z_ord d.t_ord d.zt_comm
  have h3 : (2 : ℕ) ^ 24 = 16777216 := by norm_num
  omega

theorem Level55.exists_noncomm_O2K (d : Level55 G t z) :
    ∃ a ∈ O2In (centPair z t), ∃ b ∈ O2In (centPair z t), a * b ≠ b * a := by
  by_contra h
  push Not at h
  have hcen : center ↥d.R0 = ⊤ := by
    rw [eq_top_iff]
    intro a _
    rw [mem_center_iff]
    intro b
    exact Subtype.ext (h b (d.R0_le_O2K b.2) a (d.R0_le_O2K a.2))
  have h1 := d.R0_ext.2.2.2
  rw [hcen, Subgroup.card_top, d.R0_card] at h1
  norm_num at h1

theorem Level55.z_mem_of_commutators (d : Level55 G t z) {M : Subgroup G}
    (hM : ∀ a ∈ d.R0, ∀ b ∈ d.R0, ⁅a, b⁆ ∈ M) : z ∈ M := by
  have hz : z ∈ (center ↥d.R0).map d.R0.subtype := d.R0_center ▸ mem_zpowers z
  obtain ⟨c, hc, hcz⟩ := hz
  have hc' : c ∈ commutator ↥d.R0 := by rw [d.R0_ext.2.1]; exact hc
  have hle : commutator ↥d.R0 ≤ M.subgroupOf d.R0 := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    exact mem_subgroupOf.2 (hM a a.2 b b.2)
  have h1 := mem_subgroupOf.1 (hle hc')
  have hcz' : (c : G) = z := hcz
  rwa [hcz'] at h1

theorem Level55.t_mem_of_cosets (d : Level55 G t z) {A₁ : Subgroup G}
    (hA₁K : ∀ k ∈ centPair z t, ∀ w ∈ A₁, k * w * k⁻¹ ∈ A₁)
    (hcos : ∀ y ∈ O2In (centPair z t), y ∈ A₁ ∨ y * t ∈ A₁) : t ∈ A₁ := by
  have hle : ⁅d.R0, centPair z t⁆ ≤ A₁ := by
    rw [Subgroup.commutator_le]
    intro r hr k hk
    have hrY : r ∈ O2In (centPair z t) := d.R0_le_O2K hr
    have hkt : k * t * k⁻¹ = t := by
      have := (mem_centPair_iff.1 hk).2
      calc k * t * k⁻¹ = (t * k) * k⁻¹ := by rw [this]
        _ = t := by group
    rcases hcos r hrY with hrA | hrtA
    · have h1 := hA₁K k hk r⁻¹ (inv_mem hrA)
      have e : ⁅r, k⁆ = r * (k * r⁻¹ * k⁻¹) := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact mul_mem hrA h1
    · have h1 := hA₁K k hk _ hrtA
      have e1 : k * (r * t) * k⁻¹ = (k * r * k⁻¹) * t := by
        calc k * (r * t) * k⁻¹ = (k * r * k⁻¹) * (k * t * k⁻¹) := by group
          _ = (k * r * k⁻¹) * t := by rw [hkt]
      have e : ⁅r, k⁆ = (r * t) * (k * (r * t) * k⁻¹)⁻¹ := by
        rw [e1]
        simp only [commutatorElement_def]; group
      rw [e]
      exact mul_mem hrtA (inv_mem h1)
  exact hle d.t_mem_comm

theorem Level55.eq_O2K_of_sup_pair (d : Level55 G t z) {M : Subgroup G}
    (hMY : M ≤ O2In (centPair z t)) (hMK : ∀ k ∈ centPair z t, ∀ w ∈ M, k * w * k⁻¹ ∈ M)
    (hsup : M ⊔ pair z t = O2In (centPair z t)) : M = O2In (centPair z t) := by
  have hdec : ∀ y ∈ O2In (centPair z t), ∃ m ∈ M, ∃ p ∈ pair z t, y = m * p := by
    intro y hy
    rw [← hsup] at hy
    refine exists_mul_of_mem_sup_of_le_centralizer ?_ hy
    intro p hp
    rw [mem_centralizer_iff]
    intro m hm
    exact (O2In_centPair_comm hp (hMY hm)).symm
  have hzM : z ∈ M := by
    refine d.z_mem_of_commutators fun a ha b hb => ?_
    obtain ⟨m, hm, p, hp, rfl⟩ := hdec a (d.R0_le_O2K ha)
    obtain ⟨m', hm', p', hp', rfl⟩ := hdec b (d.R0_le_O2K hb)
    rw [commutatorElement_mul_left_eq (O2In_centPair_comm hp
        (mul_mem (hMY hm') (d.pair_le_O2K hp'))),
      commutatorElement_mul_right_eq (O2In_centPair_comm hp' (hMY hm))]
    simp only [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hm hm') (inv_mem hm)) (inv_mem hm')
  have hzz := d.z_mul_self
  have htt : t * t = 1 := by rw [← pow_two, ← d.t_ord]; exact pow_orderOf_eq_one t
  have htM : t ∈ M := by
    refine d.t_mem_of_cosets hMK fun y hy => ?_
    obtain ⟨m, hm, p, hp, rfl⟩ := hdec y hy
    rcases mem_pair_cases d.z_ord d.t_ord d.zt_comm hp with rfl | rfl | rfl | rfl
    · left; simpa using hm
    · left; exact mul_mem hm hzM
    · right; rw [mul_assoc, htt, mul_one]; exact hm
    · right
      have : m * (z * t) * t = m * z := by
        rw [mul_assoc, mul_assoc, htt, mul_one]
      rw [this]
      exact mul_mem hm hzM
  have hpair : pair z t ≤ M := sup_le (zpowers_le.2 hzM) (zpowers_le.2 htM)
  rw [← hsup]
  exact (sup_eq_left.2 hpair).symm

theorem Level55.invariant_le_pair_or_eq (d : Level55 G t z) {M : Subgroup G}
    (hMY : M ≤ O2In (centPair z t)) (hMK : ∀ k ∈ centPair z t, ∀ w ∈ M, k * w * k⁻¹ ∈ M) :
    M ≤ pair z t ∨ M = O2In (centPair z t) := by
  have hpairK : ∀ k ∈ centPair z t, ∀ w ∈ pair z t, k * w * k⁻¹ ∈ pair z t := by
    intro k hk a ha
    have : a * k = k * a := mem_centralizer_iff.1 hk a ha
    rw [← this, mul_inv_cancel_right]
    exact ha
  have hWK : ∀ k ∈ centPair z t, ∀ w ∈ M ⊔ pair z t, k * w * k⁻¹ ∈ M ⊔ pair z t := fun k hk =>
    conj_mem_sup_of_invariant (hMK k hk) (hpairK k hk)
  rcases d.irred (M ⊔ pair z t) le_sup_right (sup_le hMY d.pair_le_O2K) hWK with h | h
  · left
    exact le_sup_left.trans h.le
  · right
    exact d.eq_O2K_of_sup_pair hMY hMK h

theorem Level55.pair_comm (d : Level55 G t z) {p q : G} (hp : p ∈ pair z t) (hq : q ∈ pair z t) :
    p * q = q * p := by
  have hc : Commute z t := d.zt_comm
  have hzq : Commute z q := by
    rcases mem_pair_cases d.z_ord d.t_ord d.zt_comm hq with h | h | h | h <;> rw [h] <;>
      first
      | exact Commute.one_right z
      | exact Commute.refl z
      | exact hc
      | exact (Commute.refl z).mul_right hc
  have htq : Commute t q := by
    rcases mem_pair_cases d.z_ord d.t_ord d.zt_comm hq with h | h | h | h <;> rw [h] <;>
      first
      | exact Commute.one_right t
      | exact hc.symm
      | exact Commute.refl t
      | exact hc.symm.mul_right (Commute.refl t)
  rcases mem_pair_cases d.z_ord d.t_ord d.zt_comm hp with h | h | h | h <;> rw [h]
  · exact (Commute.one_left q).eq
  · exact hzq.eq
  · exact htq.eq
  · exact (hzq.mul_left htq).eq

theorem Level55.conj_zpowers_z (_d : Level55 G t z) {k : G} (hk : k ∈ centPair z t) :
    ∀ w ∈ zpowers z, k * w * k⁻¹ ∈ zpowers z := by
  refine conj_mem_zpowers_of_conj_mem ?_
  rw [mul_inv_eq_iff_eq_mul.2 (mem_centPair_iff.1 hk).1.symm]
  exact mem_zpowers z

theorem Level55.conj_pair (_d : Level55 G t z) {k : G} (hk : k ∈ centPair z t) :
    ∀ w ∈ pair z t, k * w * k⁻¹ ∈ pair z t := by
  intro a ha
  have : a * k = k * a := mem_centralizer_iff.1 hk a ha
  rw [← this, mul_inv_cancel_right]
  exact ha

theorem Level55.conj_O2K (_d : Level55 G t z) {k : G} (hk : k ∈ centPair z t) :
    ∀ w ∈ O2In (centPair z t), k * w * k⁻¹ ∈ O2In (centPair z t) := fun w hw =>
  (normal_subgroupOf_O2In (centPair z t)).conj_mem ⟨w, O2In_le _ hw⟩ (mem_subgroupOf.2 hw)
    ⟨k, hk⟩

theorem Level55.eq_K_of_sup_O2K (d : Level55 G t z) {N : Subgroup G} (hNK : N ≤ centPair z t)
    (hN : ∀ k ∈ centPair z t, ∀ n ∈ N, k * n * k⁻¹ ∈ N)
    (hsup : ∀ k ∈ centPair z t, ∃ n ∈ N, ∃ y ∈ O2In (centPair z t), k = n * y) :
    N = centPair z t := by
  refine le_antisymm hNK (fun k hk => ?_)
  have hMK : ∀ k ∈ centPair z t, ∀ w ∈ N ⊓ O2In (centPair z t),
      k * w * k⁻¹ ∈ N ⊓ O2In (centPair z t) := fun k hk w hw =>
    mem_inf.2 ⟨hN k hk w (mem_inf.1 hw).1, d.conj_O2K hk w (mem_inf.1 hw).2⟩
  rcases d.invariant_le_pair_or_eq (inf_le_right : N ⊓ O2In (centPair z t) ≤ _) hMK with
    hle | heq
  · exfalso
    obtain ⟨y, hyY, hyp⟩ := d.exists_mem_O2K_not_mem_pair
    have hWK : ∀ k' ∈ centPair z t, k' * y * k'⁻¹ ∈ pair z t ⊔ zpowers y := by
      intro k' hk'
      obtain ⟨n, hn, y₁, hy₁, rfl⟩ := hsup k' hk'
      have hn' : n ∈ centPair z t := hNK hn
      have hyK : y ∈ centPair z t := O2In_le _ hyY
      have hc : y₁ * y * y₁⁻¹ * y⁻¹ ∈ zpowers z := d.O2K_commutator_mem_zpowers hy₁ hyY
      have hcn : n * (y₁ * y * y₁⁻¹ * y⁻¹) * n⁻¹ ∈ pair z t :=
        (le_sup_left : zpowers z ≤ pair z t) (d.conj_zpowers_z hn' _ hc)
      have he : n * y * n⁻¹ * y⁻¹ ∈ pair z t := by
        refine hle (mem_inf.2 ⟨?_, ?_⟩)
        · have h1 := hN y hyK n⁻¹ (inv_mem hn)
          have e : n * y * n⁻¹ * y⁻¹ = n * (y * n⁻¹ * y⁻¹) := by group
          rw [e]
          exact mul_mem hn h1
        · exact mul_mem (d.conj_O2K hn' y hyY) (inv_mem hyY)
      have e : (n * y₁) * y * (n * y₁)⁻¹ =
          (n * (y₁ * y * y₁⁻¹ * y⁻¹) * n⁻¹) * (n * y * n⁻¹ * y⁻¹) * y := by group
      rw [e]
      exact Subgroup.mul_mem_sup (mul_mem hcn he) (mem_zpowers y)
    have hWinv : ∀ k' ∈ centPair z t, ∀ w ∈ pair z t ⊔ zpowers y,
        k' * w * k'⁻¹ ∈ pair z t ⊔ zpowers y := fun k' hk' =>
      conj_mem_sup_of_conj_mem (fun a ha => mem_sup_left (d.conj_pair hk' a ha))
        (conj_mem_zpowers_of_conj_mem (hWK k' hk'))
    have hWY : pair z t ⊔ zpowers y ≤ O2In (centPair z t) :=
      sup_le d.pair_le_O2K (zpowers_le.2 hyY)
    rcases d.irred _ le_sup_left hWY hWinv with h | h
    · exact hyp (h ▸ mem_sup_right (mem_zpowers y))
    · obtain ⟨a, ha, b, hb, hab⟩ := d.exists_noncomm_O2K
      have hcen : pair z t ≤ centralizer ((zpowers y : Subgroup G) : Set G) := by
        intro p hp
        rw [mem_centralizer_iff]
        intro u hu
        obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hu
        exact (Commute.zpow_left (show Commute y p from (O2In_centPair_comm hp hyY).symm) j).eq
      have hdec : ∀ x ∈ O2In (centPair z t), ∃ u ∈ zpowers y, ∃ p ∈ pair z t, x = u * p := by
        intro x hx
        rw [← h, sup_comm] at hx
        exact exists_mul_of_mem_sup_of_le_centralizer hcen hx
      obtain ⟨u, hu, p, hp, rfl⟩ := hdec a ha
      obtain ⟨u', hu', p', hp', rfl⟩ := hdec b hb
      apply hab
      have hup : u * u' = u' * u := by
        obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hu
        obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hu'
        exact (Commute.zpow_zpow_self y i j).eq
      have hpu : p * u' = u' * p := (mem_centralizer_iff.1 (hcen hp) u' hu').symm
      have hp'u : p' * u = u * p' := (mem_centralizer_iff.1 (hcen hp') u hu).symm
      calc u * p * (u' * p') = u * (p * u') * p' := by group
        _ = u * (u' * p) * p' := by rw [hpu]
        _ = (u * u') * (p * p') := by group
        _ = (u' * u) * (p' * p) := by rw [hup, d.pair_comm hp hp']
        _ = u' * (u * p') * p := by group
        _ = u' * (p' * u) * p := by rw [hp'u]
        _ = u' * p' * (u * p) := by group
  · have hYN : O2In (centPair z t) ≤ N := fun y hy => by
      have hy' : y ∈ N ⊓ O2In (centPair z t) := by rw [heq]; exact hy
      exact (mem_inf.1 hy').1
    obtain ⟨n, hn, y, hy, rfl⟩ := hsup k hk
    exact mul_mem hn (hYN hy)

section Certified


theorem Level55.eq_K_of_not_le_O2K (d : Level55 G t z) {N : Subgroup G} (hNK : N ≤ centPair z t)
    (hN : ∀ k ∈ centPair z t, ∀ n ∈ N, k * n * k⁻¹ ∈ N)
    (hnle : ¬ N ≤ O2In (centPair z t)) : N = centPair z t := by
  refine d.eq_K_of_sup_O2K hNK hN ?_
  obtain ⟨e⟩ := d.quot
  have hSs : IsSimpleGroup (↥(centPair z t) ⧸ CFSG.pCore 2 ↥(centPair z t)) :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Co2.isSimpleGroup_Co2 e
  have hN'n : (N.subgroupOf (centPair z t)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [mem_subgroupOf] at hn ⊢
    exact hN g g.2 n hn
  have hmap : ((N.subgroupOf (centPair z t)).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥(centPair z t)))).Normal :=
    Subgroup.Normal.map hN'n _ (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N.subgroupOf (centPair z t)).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥(centPair z t)))) with hb | ht
  · exfalso
    apply hnle
    intro n hn
    have hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥(centPair z t)) (⟨n, hNK hn⟩ : ↥(centPair z t)) ∈
        (N.subgroupOf (centPair z t)).map (QuotientGroup.mk' (CFSG.pCore 2 ↥(centPair z t))) :=
      Subgroup.mem_map_of_mem _ (mem_subgroupOf.2 hn)
    rw [hb, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
    exact (mem_pCore_iff_mem_O2In (H := centPair z t) ⟨n, hNK hn⟩).1 hmem
  · intro k hk
    have hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥(centPair z t)) (⟨k, hk⟩ : ↥(centPair z t)) ∈
        (N.subgroupOf (centPair z t)).map (QuotientGroup.mk' (CFSG.pCore 2 ↥(centPair z t))) := by
      rw [ht]; exact mem_top _
    obtain ⟨n, hn, hnk⟩ := hmem
    refine ⟨(n : G), mem_subgroupOf.1 hn, (n : G)⁻¹ * k, ?_, by group⟩
    have h1 : n⁻¹ * (⟨k, hk⟩ : ↥(centPair z t)) ∈ CFSG.pCore 2 ↥(centPair z t) := by
      rw [← QuotientGroup.eq]
      exact hnk
    exact (mem_pCore_iff_mem_O2In (H := centPair z t) _).1 h1

theorem Level55.central_K_le_pair (d : Level55 G t z) {c : G} (hc : c ∈ centPair z t)
    (hcc : ∀ k ∈ centPair z t, c * k = k * c) : c ∈ pair z t := by
  let N : Subgroup G := centPair z t ⊓ centralizer ((centPair z t : Subgroup G) : Set G)
  have hN : ∀ k ∈ centPair z t, ∀ n ∈ N, k * n * k⁻¹ ∈ N := by
    intro k hk n hn
    have hcomm : n * k = k * n := mem_centralizer_iff.1 (mem_inf.1 hn).2 k hk |>.symm
    rw [← hcomm, mul_inv_cancel_right]
    exact hn
  by_cases hle : N ≤ O2In (centPair z t)
  · have hcN : c ∈ N := mem_inf.2 ⟨hc, mem_centralizer_iff.2 fun k hk => (hcc k hk).symm⟩
    exact d.mem_pair_of_central (hle hcN) fun r hr => hcc r (O2In_le _ hr)
  · exfalso
    have heq := d.eq_K_of_not_le_O2K inf_le_left hN hle
    obtain ⟨a, ha, b, hb, hab⟩ := d.exists_noncomm_O2K
    apply hab
    have hbK : b ∈ centPair z t ⊓ centralizer ((centPair z t : Subgroup G) : Set G) := by
      rw [heq]; exact O2In_le _ hb
    exact mem_centralizer_iff.1 (mem_inf.1 hbK).2 a (O2In_le _ ha)

end Certified

end CFSG.EvenSporadicStandard.TwoB
