module

public import CFSG.RankThree.PartTwo.Sec4.Vocabulary

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Census219

open Subgroup Equiv

@[expose] noncomputable def cosetPerm {Q : Type*} [Group Q] (K : Subgroup Q) {n : ℕ}
    (e : Q ⧸ K ≃ Fin n) : Q →* Perm (Fin n) :=
  (e.permCongrHom : Perm (Q ⧸ K) ≃* Perm (Fin n)).toMonoidHom.comp (MulAction.toPermHom Q (Q ⧸ K))

theorem cosetPerm_apply {Q : Type*} [Group Q] (K : Subgroup Q) {n : ℕ} (e : Q ⧸ K ≃ Fin n)
    (q : Q) (j : Fin n) : cosetPerm K e q j = e (q • e.symm j) := by
  simp [cosetPerm, Equiv.permCongr_apply]

theorem cosetPerm_eq_one_of_central {Q : Type*} [Group Q] (K : Subgroup Q) {n : ℕ}
    (e : Q ⧸ K ≃ Fin n) {x : Q} (hxc : x ∈ center Q) (hxK : x ∈ K) : cosetPerm K e x = 1 := by
  ext j
  rw [cosetPerm_apply]
  obtain ⟨q, hq⟩ := QuotientGroup.mk_surjective (e.symm j)
  have h : x • e.symm j = e.symm j := by
    rw [← hq]
    show ((x * q : Q) : Q ⧸ K) = (q : Q ⧸ K)
    rw [QuotientGroup.eq]
    have hc : x * q = q * x := (Subgroup.mem_center_iff.1 hxc q).symm
    rw [hc, mul_inv_rev, inv_mul_cancel_right]
    exact K.inv_mem hxK
  rw [h]
  simp

theorem tripleCover_of_range {Q : Type*} [Group Q] [Finite Q] {n : ℕ} (hn : 5 ≤ n)
    (π : Q →* Perm (Fin n)) {x : Q} (hx : orderOf x = 3) (hxc : x ∈ center Q) (hxk : π x = 1)
    (hA : alternatingGroup (Fin n) ≤ π.range)
    (hcard : Nat.card Q = 3 * Nat.card (alternatingGroup (Fin n)))
    (hperf : Group.IsPerfect Q) :
    π.ker = zpowers x ∧ π.range = alternatingGroup (Fin n) ∧ center Q = zpowers x ∧
      CFSG.IsQuasisimple Q ∧ CFSG.RankThree.PartTwo.Sec4.IsTripleCover Q (alternatingGroup (Fin n)) := by
  have hz : Nat.card (zpowers x) = 3 := by rw [Nat.card_zpowers, hx]
  have hzk : zpowers x ≤ π.ker := by rw [zpowers_le]; exact hxk
  have hprod : Nat.card Q = Nat.card π.range * Nat.card π.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker]
    congr 1
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange π).toEquiv
  have h1 : Nat.card (alternatingGroup (Fin n)) ≤ Nat.card π.range := Subgroup.card_le_of_le hA
  have h2 : 3 ≤ Nat.card π.ker := hz ▸ Subgroup.card_le_of_le hzk
  have hapos : 0 < Nat.card (alternatingGroup (Fin n)) := Nat.card_pos
  have hr : Nat.card π.range = Nat.card (alternatingGroup (Fin n)) := by
    by_contra hne
    have : Nat.card (alternatingGroup (Fin n)) < Nat.card π.range := lt_of_le_of_ne h1 (Ne.symm hne)
    nlinarith
  have hk : Nat.card π.ker = 3 := by
    rw [hr] at hprod
    have : Nat.card (alternatingGroup (Fin n)) * 3 = Nat.card (alternatingGroup (Fin n)) * Nat.card π.ker := by
      rw [← hprod, hcard]; ring
    exact (Nat.eq_of_mul_eq_mul_left hapos this).symm
  have hker : π.ker = zpowers x :=
    (Subgroup.eq_of_le_of_card_ge hzk (by rw [hk, hz])).symm
  have hrange : π.range = alternatingGroup (Fin n) :=
    (Subgroup.eq_of_le_of_card_ge hA (by rw [hr])).symm
  have hcen : center Q = π.ker := by
    apply le_antisymm
    · intro z hz'
      rw [MonoidHom.mem_ker]
      have hzr : π z ∈ alternatingGroup (Fin n) := hrange ▸ ⟨z, rfl⟩
      have hc : (⟨π z, hzr⟩ : alternatingGroup (Fin n)) ∈ center (alternatingGroup (Fin n)) := by
        rw [Subgroup.mem_center_iff]
        intro a
        have ha : (a : Perm (Fin n)) ∈ π.range := hA a.2
        obtain ⟨q, hq⟩ := ha
        apply Subtype.ext
        show (a : Perm (Fin n)) * π z = π z * a
        rw [← hq, ← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz' q]
      have hbot : center (alternatingGroup (Fin n)) = ⊥ :=
        alternatingGroup.center_eq_bot (by simpa using hn.trans' (by norm_num : 4 ≤ 5))
      rw [hbot, Subgroup.mem_bot] at hc
      exact congrArg Subtype.val hc
    · rw [hker, zpowers_le]; exact hxc
  have hcen' : center Q = zpowers x := hcen.trans hker
  have hequiv : Q ⧸ center Q ≃* alternatingGroup (Fin n) :=
    ((QuotientGroup.quotientMulEquivOfEq hcen).trans (QuotientGroup.quotientKerEquivRange π)).trans
      (MulEquiv.subgroupCongr hrange)
  have hsimple : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by simpa using hn)
  refine ⟨hker, hrange, hcen', ⟨hperf, ?_, ?_⟩, ?_, ⟨hequiv⟩⟩
  · exact hequiv.isSimpleGroup
  · by_contra hcon
    push Not at hcon
    have hall : ∀ a b : alternatingGroup (Fin n), a * b = b * a := fun a b => by
      obtain ⟨a', rfl⟩ := hequiv.surjective a
      obtain ⟨b', rfl⟩ := hequiv.surjective b
      rw [← map_mul, ← map_mul, hcon a' b']
    have hbot : center (alternatingGroup (Fin n)) = ⊥ :=
      alternatingGroup.center_eq_bot (by simpa using hn.trans' (by norm_num : 4 ≤ 5))
    have : Nontrivial (alternatingGroup (Fin n)) :=
      alternatingGroup.nontrivial_of_three_le_card (by simpa using hn.trans' (by norm_num : 3 ≤ 5))
    obtain ⟨a, ha⟩ := exists_ne (1 : alternatingGroup (Fin n))
    have h1 : a ∈ center (alternatingGroup (Fin n)) :=
      Subgroup.mem_center_iff.2 fun b => hall b a
    rw [hbot, Subgroup.mem_bot] at h1
    exact ha h1
  · rw [hcen']; exact hz

theorem eq_alternatingGroup_of_card {m : ℕ} (hm : 3 ≤ m) (H : Subgroup (Perm (Fin m)))
    (hH : Nat.card H = Nat.card (alternatingGroup (Fin m))) : H = alternatingGroup (Fin m) := by
  have : Nontrivial (Fin m) := ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp⟩
  have hidx : H.index = 2 := by
    have h1 := H.index_mul_card
    have h2 := two_mul_nat_card_alternatingGroup (α := Fin m)
    rw [hH] at h1
    have hpos : 0 < Nat.card (alternatingGroup (Fin m)) := Nat.card_pos
    nlinarith
  have hnorm : H.Normal := Subgroup.normal_of_index_eq_two hidx
  have hsq : ∀ g : Perm (Fin m), g * g ∈ H := by
    intro g
    have hc : Nat.card (Perm (Fin m) ⧸ H) = 2 := by rw [← Subgroup.index, hidx]
    have : ((g : Perm (Fin m) ⧸ H)) ^ 2 = 1 := by
      have := pow_card_eq_one' (G := Perm (Fin m) ⧸ H) (x := (g : Perm (Fin m) ⧸ H))
      rwa [hc] at this
    rw [pow_two, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff] at this
    exact this
  have h3 : alternatingGroup (Fin m) ≤ H := by
    rw [← Equiv.Perm.closure_three_cycles_eq_alternating, Subgroup.closure_le]
    intro c hc
    have hc3 : orderOf c = 3 := hc.orderOf
    have : c = (c * c) * (c * c) := by
      have : c ^ 3 = 1 := by rw [← hc3]; exact pow_orderOf_eq_one c
      calc c = c * c ^ 3 := by rw [this, mul_one]
        _ = (c * c) * (c * c) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [this]
    exact H.mul_mem (hsq _) (hsq _)
  exact (Subgroup.eq_of_le_of_card_ge h3 hH.le).symm

theorem isTripleCover_of_mulEquiv {A B S : Type*} [Group A] [Group B] [Group S] (e : A ≃* B)
    (h : CFSG.RankThree.PartTwo.Sec4.IsTripleCover A S) :
    CFSG.RankThree.PartTwo.Sec4.IsTripleCover B S := by
  obtain ⟨hc, ⟨q⟩⟩ := h
  refine ⟨?_, ⟨?_⟩⟩
  · rw [← hc]
    exact Nat.card_congr (Subgroup.centerCongr e).symm.toEquiv
  · exact (QuotientGroup.congr (center A) (center B) e (Subgroup.map_center_eq e)).symm.trans q

end CFSG.AGLEmbeddingD2.Wilson.Census219
