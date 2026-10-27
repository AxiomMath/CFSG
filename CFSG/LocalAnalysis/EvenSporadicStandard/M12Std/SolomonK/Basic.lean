module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.SolomonK.Defs
public import CFSG.GH74.M12.T1NonSimple

public section

namespace CFSG.EvenSporadicStandard.M12Std.SolomonK

open Subgroup

variable {K : Type} [Group K]

theorem comm_of_sq_eq_one {A : Subgroup K} (hsq : ∀ x ∈ A, x * x = 1) {x y : K} (hx : x ∈ A)
    (hy : y ∈ A) : x * y = y * x := by
  have h1 := hsq (x * y) (A.mul_mem hx hy)
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hsq x hx)
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right (hsq y hy)
  have h2 : x * y = (x * y)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
  rw [h2, mul_inv_rev, hxi, hyi]

structure GoodE (E : Subgroup K) : Prop where
  sq : ∀ x ∈ E, x * x = 1
  card : Nat.card E = 2 ^ 6
  not_normal : ¬ E.Normal
  iso : Nonempty (↥(normalizer (E : Set K)) ⧸ E.subgroupOf (normalizer (E : Set K)) ≃*
    GL (Fin 3) (ZMod 2))

theorem SolomonA12HypK.exists_goodE (h : SolomonA12HypK K) : ∃ E : Subgroup K, GoodE E := by
  obtain ⟨E, h1, h2, h3, h4⟩ := h.exists_E
  exact ⟨E, ⟨h1, h2, h3, h4⟩⟩

namespace GoodE

variable {E : Subgroup K}

theorem comm (hE : GoodE E) : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun _ hx _ hy =>
  comm_of_sq_eq_one hE.sq hx hy

theorem isPGroup [Finite K] (hE : GoodE E) : IsPGroup 2 E :=
  IsPGroup.of_card (n := 6) hE.card

theorem card_normalizer [Finite K] (hE : GoodE E) :
    Nat.card (normalizer (E : Set K)) = 2 ^ 6 * 168 := by
  obtain ⟨e⟩ := hE.iso
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (E.subgroupOf (normalizer (E : Set K)))
  have h2 : Nat.card (E.subgroupOf (normalizer (E : Set K))) = Nat.card E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.le_normalizer (H := E))).toEquiv
  have h3 : Nat.card
      (↥(normalizer (E : Set K)) ⧸ E.subgroupOf (normalizer (E : Set K))) = 168 := by
    rw [Nat.card_congr e.toEquiv, card_gl_three_two]
  rw [h1, h2, h3, hE.card]
  ring

theorem eq_or_eq [Finite K] (hE : GoodE E) {M : Subgroup K} (hEM : E ≤ M)
    (hMN : M ≤ normalizer (E : Set K))
    (hM : ∀ g ∈ normalizer (E : Set K), ∀ m ∈ M, g * m * g⁻¹ ∈ M) :
    M = E ∨ M = normalizer (E : Set K) := by
  let N : Subgroup K := normalizer (E : Set K)
  let E' : Subgroup N := E.subgroupOf N
  let M' : Subgroup N := M.subgroupOf N
  haveI : E'.Normal := Subgroup.normal_in_normalizer
  have hE'le : E' ≤ M' := fun x hx => (Subgroup.mem_subgroupOf).mpr (hEM hx)
  have hM'normal : M'.Normal :=
    (Subgroup.normal_subgroupOf_iff hMN).mpr fun m g hm hg => hM g hg m hm
  haveI : (M'.map (QuotientGroup.mk' E')).Normal :=
    hM'normal.map _ (QuotientGroup.mk'_surjective E')
  obtain ⟨e⟩ := hE.iso
  haveI : IsSimpleGroup (GL (Fin 3) (ZMod 2)) := CFSG.GH74.M12.Thm1.isSimpleGroup_GL3_two
  haveI : IsSimpleGroup (N ⧸ E') := e.isSimpleGroup
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (M'.map (QuotientGroup.mk' E')) with
    hbot | htop
  · left
    refine le_antisymm ?_ hEM
    intro m hm
    have hmN : m ∈ N := hMN hm
    have hmM' : (⟨m, hmN⟩ : N) ∈ M' := (Subgroup.mem_subgroupOf).mpr hm
    have hmap : QuotientGroup.mk' E' ⟨m, hmN⟩ ∈ M'.map (QuotientGroup.mk' E') :=
      Subgroup.mem_map_of_mem _ hmM'
    rw [hbot] at hmap
    have hmem : (⟨m, hmN⟩ : N) ∈ E' := by
      rw [← QuotientGroup.eq_one_iff]
      exact Subgroup.mem_bot.mp hmap
    exact (Subgroup.mem_subgroupOf).mp hmem
  · right
    refine le_antisymm hMN ?_
    intro n hn
    have hmap : QuotientGroup.mk' E' ⟨n, hn⟩ ∈ M'.map (QuotientGroup.mk' E') := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨m', hm', heq⟩ := (Subgroup.mem_map).mp hmap
    have hmemE' : m'⁻¹ * ⟨n, hn⟩ ∈ E' := QuotientGroup.eq.mp heq
    have hmemM' : m'⁻¹ * ⟨n, hn⟩ ∈ M' := hE'le hmemE'
    have hmem : (⟨n, hn⟩ : N) ∈ M' := by
      have hmul : m' * (m'⁻¹ * ⟨n, hn⟩) ∈ M' := M'.mul_mem hm' hmemM'
      have heq2 : m' * (m'⁻¹ * ⟨n, hn⟩) = ⟨n, hn⟩ := by group
      rwa [heq2] at hmul
    exact (Subgroup.mem_subgroupOf).mp hmem

theorem eq_of_isPGroup [Finite K] (hE : GoodE E) {M : Subgroup K} (hEM : E ≤ M)
    (hMN : M ≤ normalizer (E : Set K))
    (hM : ∀ g ∈ normalizer (E : Set K), ∀ m ∈ M, g * m * g⁻¹ ∈ M) (hM2 : IsPGroup 2 M) :
    M = E := by
  rcases hE.eq_or_eq hEM hMN hM with h | h
  · exact h
  · exfalso
    have hN2 : IsPGroup 2 (normalizer (E : Set K)) := h ▸ hM2
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp hN2
    have h3 : 3 ∣ Nat.card (normalizer (E : Set K)) := by
      rw [hE.card_normalizer]
      norm_num
    rw [hn] at h3
    have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 3) h3
    exact absurd h32 (by norm_num)

theorem exists_commutator_not_mem [Finite K] (hE : GoodE E) :
    ∃ x ∈ normalizer (E : Set K), ∃ y ∈ normalizer (E : Set K), x * y * x⁻¹ * y⁻¹ ∉ E := by
  by_contra h
  push Not at h
  let N : Subgroup K := normalizer (E : Set K)
  let E' : Subgroup N := E.subgroupOf N
  haveI : E'.Normal := Subgroup.normal_in_normalizer
  obtain ⟨e⟩ := hE.iso
  haveI : IsSimpleGroup (GL (Fin 3) (ZMod 2)) := CFSG.GH74.M12.Thm1.isSimpleGroup_GL3_two
  haveI : IsSimpleGroup (N ⧸ E') := e.isSimpleGroup
  have hcomm' : ∀ a b : N, a * b * a⁻¹ * b⁻¹ ∈ E' := fun a b =>
    (Subgroup.mem_subgroupOf).mpr (h a a.2 b b.2)
  have hcomm : ∀ q1 q2 : N ⧸ E', q1 * q2 = q2 * q1 := by
    intro q1 q2
    obtain ⟨n1, rfl⟩ := QuotientGroup.mk'_surjective E' q1
    obtain ⟨n2, rfl⟩ := QuotientGroup.mk'_surjective E' q2
    have h1 : QuotientGroup.mk' E' (n1 * n2 * n1⁻¹ * n2⁻¹) = 1 :=
      (QuotientGroup.eq_one_iff (n1 * n2 * n1⁻¹ * n2⁻¹)).mpr (hcomm' n1 n2)
    have h2 : QuotientGroup.mk' E' n1 * QuotientGroup.mk' E' n2 *
        (QuotientGroup.mk' E' n1)⁻¹ * (QuotientGroup.mk' E' n2)⁻¹ = 1 := by
      simpa only [map_mul, map_inv] using h1
    have h3 : (QuotientGroup.mk' E' n1 * QuotientGroup.mk' E' n2) *
        (QuotientGroup.mk' E' n2 * QuotientGroup.mk' E' n1)⁻¹ = 1 := by
      simpa only [mul_inv_rev, mul_assoc] using h2
    exact mul_inv_eq_one.mp h3
  haveI : IsMulCommutative (N ⧸ E') := IsMulCommutative.of_comm hcomm
  have hprime : (Nat.card (N ⧸ E')).Prime :=
    (Group.is_simple_iff_prime_card (α := N ⧸ E')).mp inferInstance
  have h168 : Nat.card (N ⧸ E') = 168 := by
    rw [Nat.card_congr e.toEquiv, card_gl_three_two]
  rw [h168] at hprime
  exact (by norm_num : ¬ (Nat.Prime 168)) hprime

end GoodE

end CFSG.EvenSporadicStandard.M12Std.SolomonK
