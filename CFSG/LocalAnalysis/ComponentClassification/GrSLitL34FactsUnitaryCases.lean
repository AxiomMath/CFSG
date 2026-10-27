
module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsUnitaryCasesBase

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsUnitaryFix

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34

variable {E : Type*} [Group E]

theorem qc_ne_one : qc ≠ 1 := quat_relations.2.2.2.1

theorem qc_mul_self : qc * qc = 1 := quat_relations.2.2.1

theorem orderOf_qc : orderOf qc = 2 :=
  orderOf_eq_two' qc_mul_self qc_ne_one

namespace IsUSetting

variable {q : E →* Equiv.Perm (Fin 42)} {l : Cover →* E} {β : E ≃* E}

theorem card_K_le_two_of_cyclic
    [Finite E]
    (h : IsUSetting q l β) (hcyc : IsCyclic q.ker) : Nat.card ↥(fixT0 q β ⊓ q.ker) ≤ 2 := by
  classical
  have : Fintype q.ker := Fintype.ofFinite _
  have h2 := IsCyclic.card_pow_eq_one_le (α := q.ker) (n := 2) (by norm_num)
  have e : Nat.card ↥(fixT0 q β ⊓ q.ker) = Nat.card {a : q.ker // a ^ 2 = 1} := by
    apply Nat.card_congr
    exact
      { toFun := fun z => ⟨⟨z.1, ((h.mem_K _).1 z.2).1⟩, Subtype.ext (by
          rw [Subgroup.coe_pow, pow_two]
          exact ((h.mem_K _).1 z.2).2)⟩
        invFun := fun a => ⟨a.1.1, (h.mem_K _).2 ⟨a.1.2, by
          have := congrArg Subtype.val a.2
          rwa [Subgroup.coe_pow, pow_two] at this⟩⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [e, Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact h2

theorem K_ne_bot
    (h : IsUSetting q l β)
    (hne : q.ker ≠ ⊥) : fixT0 q β ⊓ q.ker ≠ ⊥ := by
  obtain ⟨⟨z, hz⟩, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one.mp hne)
  have hz1' : z ≠ 1 := fun e => hz1 (Subtype.ext e)
  intro hK
  by_cases h2 : z * z = 1
  · have hmem : z ∈ fixT0 q β ⊓ q.ker := (h.mem_K z).2 ⟨hz, h2⟩
    rw [hK, mem_bot] at hmem
    exact hz1' hmem
  · have hmem : z * z ∈ fixT0 q β ⊓ q.ker := (h.mem_K _).2 ⟨q.ker.mul_mem hz hz, by
      rw [← pow_four_eq]
      exact h.pow_four_of_ker hz⟩
    rw [hK, mem_bot] at hmem
    exact h2 hmem

theorem exists_order_four
    [Finite E] (h : IsUSetting q l β)
    (hK : Nat.card ↥(fixT0 q β ⊓ q.ker) = 2) : ∃ m ∈ fixT0 q β, q m * q m = qc := by
  by_contra hno
  push Not at hno
  set f : fixT0 q β →* Equiv.Perm (Fin 42) := q.comp (fixT0 q β).subtype with hf
  have hrange : f.range ≤ zpowers qc := by
    rintro _ ⟨m, rfl⟩
    have hq := h.q_mem_Q8_of_fix m.2
    rcases mul_self_mem_Q8 hq with h1 | h1
    · rcases eq_of_mem_Q8_of_mul_self hq h1 with h2 | h2
      · show q m ∈ zpowers qc
        rw [h2]
        exact one_mem _
      · show q m ∈ zpowers qc
        rw [h2]
        exact mem_zpowers _
    · exact absurd h1 (hno m m.2)
  have h1 := Subgroup.card_ker_mul_card_range f
  rw [hf, card_ker_restrict, hK, h.card_fixT0, ← hf] at h1
  have h2 := Subgroup.card_le_of_le hrange
  rw [Nat.card_zpowers, orderOf_qc] at h2
  omega

theorem cyclic_case
    [Finite E] (h : IsUSetting q l β) (hne : q.ker ≠ ⊥)
    (hcyc : IsCyclic q.ker) :
    Nat.card ↥(fixT0 q β ⊓ q.ker) = 2 ∧ (∀ a ∈ fixT0 q β, ∀ b ∈ fixT0 q β, a * b = b * a) ∧
      Monoid.exponent (fixT0 q β) = 4 ∧
      ∃ m ∈ fixT0 q β, orderOf m = 4 ∧ orderOf (q m) = 4 := by
  have hK2 : Nat.card ↥(fixT0 q β ⊓ q.ker) = 2 :=
    le_antisymm (h.card_K_le_two_of_cyclic hcyc) ((one_lt_card_iff_ne_bot _).2 (h.K_ne_bot hne))
  obtain ⟨m, hm, hmq⟩ := h.exists_order_four hK2
  have hqm4 : orderOf (q m) = 4 :=
    orderOf_eq_four (by rw [pow_four_eq, hmq, qc_mul_self]) (by rw [hmq]; exact qc_ne_one)
  have hm4 : orderOf m = 4 := orderOf_eq_four (h.pow_four_of_fix hm) fun h' =>
    qc_ne_one (by rw [← hmq, ← map_mul, h', map_one])
  have hzp : zpowers m ≤ fixT0 q β := (zpowers_le).2 hm
  have hsup : (fixT0 q β ⊓ q.ker) ⊔ zpowers m = fixT0 q β :=
    sup_eq_of_card inf_le_left hzp (inf_ker_eq_bot q _ (hqm4.trans hm4.symm)) h.card_fixT0
      (Or.inl ⟨hK2, by rw [Nat.card_zpowers, hm4]⟩)
  refine ⟨hK2, ?_, ?_, m, hm, hm4, hqm4⟩
  · have hKn : (fixT0 q β ⊓ q.ker).Normal := normal_of_le_center (inf_le_right.trans h.ker_le)
    intro a ha b hb
    rw [← hsup, sup_comm] at ha hb
    obtain ⟨y, hy, k, hk, rfl⟩ := mem_sup_of_normal_right.1 ha
    obtain ⟨y', hy', k', hk', rfl⟩ := mem_sup_of_normal_right.1 hb
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hy
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hy'
    have hkc := mem_center_iff.mp (h.ker_le hk.2)
    have hk'c := mem_center_iff.mp (h.ker_le hk'.2)
    have e1 : m ^ i * k * (m ^ j * k') = m ^ i * m ^ j * (k * k') := by
      rw [show m ^ i * k * (m ^ j * k') = m ^ i * (k * m ^ j) * k' by group, ← hkc (m ^ j)]
      group
    have e2 : m ^ j * k' * (m ^ i * k) = m ^ j * m ^ i * (k' * k) := by
      rw [show m ^ j * k' * (m ^ i * k) = m ^ j * (k' * m ^ i) * k by group, ← hk'c (m ^ i)]
      group
    rw [e1, e2, (Commute.zpow_zpow_self m i j).eq, hkc k']
  · apply Nat.dvd_antisymm
    · exact Monoid.exponent_dvd_of_forall_pow_eq_one fun g => Subtype.ext (by
        rw [Subgroup.coe_pow, h.pow_four_of_fix g.2]
        rfl)
    · have := Monoid.order_dvd_exponent (⟨m, hm⟩ : fixT0 q β)
      rwa [orderOf_mk, hm4] at this

theorem noncyclic_case
    [Finite E] (h : IsUSetting q l β) (hcyc : ¬ IsCyclic q.ker) :
    Nat.card ↥(fixT0 q β ⊓ q.ker) = 4 ∧ (∀ e ∈ fixT0 q β, e * e = 1) ∧
      ∃ m ∈ fixT0 q β, orderOf m = 2 ∧ orderOf (q m) = 2 := by
  have hK3 : 2 < Nat.card ↥(fixT0 q β ⊓ q.ker) := by
    by_contra hle
    push Not at hle
    exact hcyc (isCyclic_of_card_le_two h.ker_le (fun z hz => h.pow_four_of_ker hz) h.mem_K hle)
  have hKd : Nat.card ↥(fixT0 q β ⊓ q.ker) ∣ 8 := h.card_fixT0 ▸ card_dvd_of_le inf_le_left
  obtain ⟨e₀, he₀, hq₀⟩ := h.exists_fix_qc
  have hK8 : Nat.card ↥(fixT0 q β ⊓ q.ker) ≠ 8 := by
    intro h8
    have hKeq : fixT0 q β ⊓ q.ker = fixT0 q β :=
      eq_of_le_of_card_ge inf_le_left (by rw [h8, h.card_fixT0])
    have hmem : e₀ ∈ fixT0 q β ⊓ q.ker := by rw [hKeq]; exact he₀
    have := (mem_inf.mp hmem).2
    rw [MonoidHom.mem_ker, hq₀] at this
    exact qc_ne_one this
  have hK4 : Nat.card ↥(fixT0 q β ⊓ q.ker) = 4 := by
    have hle : Nat.card ↥(fixT0 q β ⊓ q.ker) ≤ 8 := Nat.le_of_dvd (by norm_num) hKd
    interval_cases hc : Nat.card ↥(fixT0 q β ⊓ q.ker) <;>
      first | rfl | omega
  have hsq : ∀ e ∈ fixT0 q β, e * e = 1 := by
    set f : fixT0 q β →* Equiv.Perm (Fin 42) := q.comp (fixT0 q β).subtype with hf
    have h1 := Subgroup.card_ker_mul_card_range f
    rw [hf, card_ker_restrict, hK4, h.card_fixT0, ← hf] at h1
    have hr2 : Nat.card f.range = 2 := by omega
    intro e he
    have hpow := pow_card_eq_one' (G := f.range) (x := ⟨q e, ⟨e, he⟩, rfl⟩)
    rw [hr2] at hpow
    have hqe : q e * q e = 1 := by
      have := congrArg Subtype.val hpow
      rwa [Subgroup.coe_pow, pow_two] at this
    rcases eq_of_mem_Q8_of_mul_self (h.q_mem_Q8_of_fix he) hqe with h2 | h2
    · exact (h.mem_fixT0_of_ker h2).1 he
    · exact h.mul_self_of_q_eq_qc he h2
  refine ⟨hK4, hsq, e₀, he₀, orderOf_eq_two' (hsq e₀ he₀) fun h1 => qc_ne_one ?_, ?_⟩
  · rw [← hq₀, h1, map_one]
  · rw [hq₀, orderOf_qc]

theorem card_comap_T0 [Finite E]
    (h : IsUSetting q l β) : Nat.card (T0.comap q) = 64 * Nat.card q.ker := by
  rw [card_comap_eq q T0 (fun t ht => h.qsurj t (T0_le_S ht)), card_T0]

theorem card_inv_le
    [Finite E] (h : IsUSetting q l β) :
    Nat.card {e : E // q e ∈ T0 ∧ β e = e⁻¹} ≤ 8 * Nat.card q.ker := by
  classical
  have : Fintype E := Fintype.ofFinite E
  set A := Finset.univ.filter (fun e : E => q e ∈ T0 ∧ β e = e⁻¹) with hA
  set Kset := (Finset.range 64).filter (fun k => (comp 42 (wordTab (tg k))
    (conjTab 42 r₄T r₄T (wordTab (tg k))) == idTab 42) = true) with hKset
  have hK8 : Kset.card = 8 := by
    have := countBelow_eq 64 (fun k => comp 42 (wordTab (tg k))
      (conjTab 42 r₄T r₄T (wordTab (tg k))) == idTab 42)
    rw [coverParts.count8] at this
    exact this.symm
  have hr4i : TabRep r₄T r₄⁻¹ := by
    rw [inv_eq_of_mul_eq_one_right r₄_mul_self]
    exact tabRep_r₄
  have himg : A.image q ⊆ Kset.image (fun k => wordPerm (tg k)) := by
    intro t ht
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp ht
    rw [hA, Finset.mem_filter] at he
    obtain ⟨-, hT, hβ⟩ := he
    obtain ⟨k, hk, hkt⟩ := exists_tg hT
    refine Finset.mem_image.mpr ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, ?_⟩, hkt⟩
    have hrep := (tabRep_wordTab (tg k)).comp (tabRep_r₄.conjTab (tabRep_wordTab (tg k)) hr4i)
    rw [hrep.beq_iff TabRep.idTab, hkt]
    have h1 := h.qβ e
    rw [hβ, map_inv] at h1
    rw [← h1, mul_inv_cancel]
  have hfib : ∀ b ∈ A.image q, (A.filter fun a => q a = b).card ≤ Nat.card q.ker := by
    intro b hb
    obtain ⟨a₀, -, rfl⟩ := Finset.mem_image.mp hb
    have hcard : Nat.card q.ker = (q.ker : Set E).toFinset.card := Nat.card_eq_card_toFinset _
    rw [hcard]
    refine Finset.card_le_card_of_injOn (fun a => a₀⁻¹ * a) ?_ ?_
    · intro a ha
      rw [Finset.mem_coe, Finset.mem_filter] at ha
      rw [Finset.mem_coe, Set.mem_toFinset, SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv,
        ha.2, inv_mul_cancel]
    · intro a _ b _ hab
      exact mul_left_cancel hab
  have h1 := Finset.card_le_mul_card_image A (Nat.card q.ker) hfib
  have h2 : (A.image q).card ≤ 8 :=
    (Finset.card_le_card himg).trans (Finset.card_image_le.trans hK8.le)
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  calc A.card ≤ Nat.card q.ker * (A.image q).card := h1
    _ ≤ Nat.card q.ker * 8 := Nat.mul_le_mul_left _ h2
    _ = 8 * Nat.card q.ker := mul_comm _ _

end IsUSetting

end CFSG.ComponentClassification.GrSLit.L34Facts
