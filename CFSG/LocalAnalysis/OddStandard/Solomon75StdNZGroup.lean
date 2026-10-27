module

public import CFSG.GroupTheory.CyclicSylowNormalOddComplement

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup
open scoped Pointwise

private lemma not_four_dvd_card_map_of_orderOf_eq_two {G H : Type*} [Group G] [Group H]
    (Y : Subgroup G) (f : G →* H) {z : G} (hzY : z ∈ Y) (hz : orderOf z = 2) (hfz : f z = 1)
    (h8 : ¬ 8 ∣ Nat.card Y) : ¬ 4 ∣ Nat.card (Y.map f) := by
  intro h4
  have hmul := Subgroup.card_ker_mul_card_range (f.domRestrict Y)
  rw [MonoidHom.domRestrict_range] at hmul
  have hker : (⟨z, hzY⟩ : Y) ∈ (f.domRestrict Y).ker := by
    rw [MonoidHom.mem_ker]
    exact hfz
  have h2 : 2 ∣ Nat.card (f.domRestrict Y).ker := by
    have := Subgroup.orderOf_dvd_natCard _ hker
    rwa [Subgroup.orderOf_mk, hz] at this
  apply h8
  rw [← hmul]
  have h8' := mul_dvd_mul h2 h4
  norm_num at h8'
  exact h8'

private lemma exists_subgroup_pow_four_mem {G : Type*} [Group G] [Finite G] (O : Subgroup G)
    [O.Normal] [IsCyclic (G ⧸ O)] (hodd : Odd (Nat.card O)) :
    ∃ Y : Subgroup G, (∀ x, x ∈ Y ↔ x ^ 4 ∈ O) ∧ ¬ 8 ∣ Nat.card Y := by
  classical
  let Y : Subgroup G :=
    { carrier := {x | x ^ 4 ∈ O}
      one_mem' := by simp
      mul_mem' := fun {a b} ha hb => by
        have h1 : ((a ^ 4 : G) : G ⧸ O) = 1 := (QuotientGroup.eq_one_iff _).mpr ha
        have h2 : ((b ^ 4 : G) : G ⧸ O) = 1 := (QuotientGroup.eq_one_iff _).mpr hb
        show (a * b) ^ 4 ∈ O
        rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, QuotientGroup.mk_mul,
          Commute.mul_pow (mul_comm' _ _)]
        rw [QuotientGroup.mk_pow] at h1 h2
        rw [h1, h2, one_mul]
      inv_mem' := fun {a} ha => by
        show a⁻¹ ^ 4 ∈ O
        rw [inv_pow]
        exact O.inv_mem ha }
  refine ⟨Y, fun x => Iff.rfl, ?_⟩
  have hOY : O ≤ Y := fun o ho => by
    show o ^ 4 ∈ O
    exact O.pow_mem ho 4
  let π : Y →* G ⧸ O := (QuotientGroup.mk' O).domRestrict Y
  have hker : π.ker = O.subgroupOf Y := by
    ext x
    simp [π, Subgroup.mem_subgroupOf]
  have hkercard : Nat.card π.ker = Nat.card O := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOY).toEquiv
  have hrange : Nat.card π.range ≤ 4 := by
    have : Fintype (G ⧸ O) := Fintype.ofFinite _
    have hsub : (π.range : Set (G ⧸ O)) ⊆
        ((Finset.univ.filter fun c : G ⧸ O => c ^ 4 = 1 : Finset (G ⧸ O)) : Set (G ⧸ O)) := by
      rintro _ ⟨⟨x, hx⟩, rfl⟩
      simp only [Finset.coe_filter, Finset.mem_univ, true_and]
      show ((x : G ⧸ O)) ^ 4 = 1
      rw [← QuotientGroup.mk_pow]
      exact (QuotientGroup.eq_one_iff _).mpr hx
    calc Nat.card π.range
        ≤ Nat.card ((Finset.univ.filter fun c : G ⧸ O => c ^ 4 = 1 : Finset (G ⧸ O)) :
            Set (G ⧸ O)) := Nat.card_mono (Set.toFinite _) hsub
      _ = (Finset.univ.filter fun c : G ⧸ O => c ^ 4 = 1).card := by simp
      _ ≤ 4 := by
        convert IsCyclic.card_pow_eq_one_le (α := G ⧸ O) (n := 4) (by norm_num)
  have hpos : 0 < Nat.card π.range := Nat.card_pos
  intro h8
  have hmul := Subgroup.card_ker_mul_card_range π
  rw [hkercard] at hmul
  rw [← hmul] at h8
  have hcop : Nat.Coprime 8 (Nat.card O) := by
    have := (Nat.coprime_two_left.mpr hodd).pow_left 3
    simpa using this
  have h8' := hcop.dvd_of_dvd_mul_left h8
  have := Nat.le_of_dvd hpos h8'
  omega

theorem exists_normal_two_part_le {B : Type*} [Group B] [Finite B] (N : Subgroup B) [N.Normal]
    (hcyc : ∀ V : Subgroup B, V ≤ N → IsPGroup 2 ↥V → IsCyclic ↥V) {y : B} (hyN : y ∈ N)
    (hy4 : orderOf y = 4) :
    ∃ Y : Subgroup B, Y.Normal ∧ y ∈ Y ∧ Y ≤ N ∧
      ∀ {H : Type*} [Group H] (Θ : B →* H), Θ (y ^ 2) = 1 → ¬ 4 ∣ Nat.card (Y.map Θ) := by
  obtain ⟨T⟩ : Nonempty (Sylow 2 N) := inferInstance
  have hT : IsCyclic T := by
    have h1 : IsCyclic ↥((T : Subgroup N).map N.subtype) :=
      hcyc _ (Subgroup.map_subtype_le _) (T.isPGroup'.map N.subtype)
    exact (MulEquiv.isCyclic
      (Subgroup.equivMapOfInjective _ N.subtype N.subtype_injective)).mpr h1
  obtain ⟨-, hTO, -, ⟨-, hOodd, -, -⟩, hOchar⟩ := CFSG.cyclic_sylow_normal_odd_complement T hT
  set O := CFSG.pPrimeCore 2 N
  have : O.Normal := CFSG.pPrimeCore_normal
  have hcycQ : IsCyclic (N ⧸ O) := by
    refine isCyclic_of_surjective ((QuotientGroup.mk' O).comp (T : Subgroup N).subtype) ?_
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    have hg : g ∈ (O : Set N) * (T : Set N) := by rw [hTO]; trivial
    obtain ⟨o, ho, t, ht, rfl⟩ := hg
    refine ⟨⟨t, ht⟩, ?_⟩
    simp [(QuotientGroup.eq_one_iff o).mpr ho]
  obtain ⟨Y', hY'mem, hY'8⟩ := exists_subgroup_pow_four_mem O hOodd
  have hy41 : y ^ 4 = 1 := by rw [← hy4]; exact pow_orderOf_eq_one y
  have hy'4 : (⟨y, hyN⟩ : N) ^ 4 = 1 := Subtype.ext (by simpa using hy41)
  have hy'mem : (⟨y, hyN⟩ : N) ∈ Y' := by
    rw [hY'mem, hy'4]
    exact O.one_mem
  refine ⟨Y'.map N.subtype, ?_, ⟨⟨y, hyN⟩, hy'mem, rfl⟩, Subgroup.map_subtype_le _, ?_⟩
  · refine ⟨fun n hn g => ?_⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hn
    refine Subgroup.mem_map.mpr ⟨MulAut.conjNormal g x, ?_, ?_⟩
    · have hφ := SetLike.ext_iff.mp ((Subgroup.characteristic_iff_comap_eq.mp hOchar)
        (MulAut.conjNormal g)) (x ^ 4)
      rw [hY'mem] at hx ⊢
      rw [← map_pow]
      exact hφ.mpr hx
    · simp [MulAut.conjNormal_apply]
  · intro H _ Θ hΘ
    rw [Subgroup.map_map]
    refine not_four_dvd_card_map_of_orderOf_eq_two Y' (Θ.comp N.subtype)
      (z := (⟨y, hyN⟩ : N) ^ 2) (Y'.pow_mem hy'mem 2) ?_ ?_ hY'8
    · rw [orderOf_pow_of_dvd (by norm_num) (by rw [Subgroup.orderOf_mk, hy4]; norm_num)]
      simp [Subgroup.orderOf_mk, hy4]
    · simpa using hΘ

end CFSG.OddStandard.Solomon75
