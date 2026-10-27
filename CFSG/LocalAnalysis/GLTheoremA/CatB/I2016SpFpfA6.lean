module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.GLTheoremA.S8.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2016Sp

open CFSG.Yardstones.Md0ec50421ce4

private theorem nonempty_equiv_alt6_of_isA6' {Q : Type} [Group Q] (h : catalogIs Q S8.isA6) :
    Nonempty (Q ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  rcases hi with hi | hi
  · cases i with
    | alternating n hn =>
      have hn6 : n = 6 := hi
      subst hn6
      exact ⟨e⟩
    | _ => exact hi.elim
  · cases i with
    | lie j =>
      obtain ⟨d, hv⟩ := j
      cases d with
      | A n q =>
        rcases n with _ | _ | n
        · exact hi.elim
        · have hq : q.card = 9 := hi
          have hdup := ((TauCeti.LieTypeIndex.valid_iff _).1 hv).2
          rw [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff] at hdup
          exact (hdup (Or.inl ⟨rfl, Or.inr (Or.inr hq)⟩)).elim
        · exact hi.elim
      | _ => exact hi.elim
    | _ => exact hi.elim

private def fpfSigma6 : alternatingGroup (Fin 6) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 4 5, by
    rw [Equiv.Perm.mem_alternatingGroup]
    simp [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap]⟩

private theorem orderOf_fpfSigma6 : orderOf fpfSigma6 = 4 := by
  rw [orderOf_eq_iff (by norm_num : 0 < 4)]
  refine ⟨by decide +kernel, fun m hm hm0 => ?_⟩
  interval_cases m <;> decide +kernel

theorem a6_data {S : Type} [Group S] (h : catalogIs S S8.isA6) :
    IsSimpleGroup S ∧ 5 ∣ Nat.card S ∧ ∃ y : S, orderOf y = 4 := by
  obtain ⟨e⟩ := nonempty_equiv_alt6_of_isA6' h
  haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  refine ⟨e.isSimpleGroup, ?_, e.symm fpfSigma6, ?_⟩
  · rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.card_eq_fintype_card, Nat.factorial]
  · rw [MulEquiv.orderOf_eq]
    exact orderOf_fpfSigma6

theorem sq_eq_one_of_normal_exp_two {A S : Type} [Group A] [Group S] [IsSimpleGroup S]
    (f : A →* S) (hf : Function.Surjective f) (K : Subgroup A) [K.Normal]
    (hK : ∀ k ∈ K, k ^ 2 = 1) {m : A} (hm : m ^ 2 ∈ K) : (f m) ^ 2 = 1 := by
  haveI : (K.map f).Normal := Subgroup.Normal.map ‹K.Normal› f hf
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (K.map f) with h | h
  · have hmem : f (m ^ 2) ∈ K.map f := Subgroup.mem_map.2 ⟨m ^ 2, hm, rfl⟩
    rw [h, Subgroup.mem_bot, map_pow] at hmem
    exact hmem
  · have hmem : f m ∈ K.map f := by
      rw [h]
      exact Subgroup.mem_top _
    obtain ⟨k, hk, hkm⟩ := Subgroup.mem_map.1 hmem
    rw [← hkm, ← map_pow, hK k hk, map_one]

theorem exists_two_element_lift {A S : Type} [Group A] [Finite A] [Group S] (f : A →* S)
    (hf : Function.Surjective f) {y : S} (hy : orderOf y = 4) :
    ∃ (m : A) (a : ℕ), m ^ (2 ^ a) = 1 ∧ (f m) ^ 2 ≠ 1 := by
  obtain ⟨m₀, hm₀⟩ := hf y
  obtain ⟨a, b, hb, hdec⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos m₀).ne'
  obtain ⟨c, hc⟩ := hb
  have hbpos : 0 < b := by omega
  have hdvd : b ∣ orderOf m₀ := by
    rw [hdec]
    exact dvd_mul_left b (2 ^ a)
  have hord : orderOf (m₀ ^ b) = 2 ^ a := by
    rw [orderOf_pow_of_dvd hbpos.ne' hdvd, hdec, Nat.mul_div_cancel _ hbpos]
  have hfm : f (m₀ ^ b) = y ^ b := by
    rw [map_pow, hm₀]
  refine ⟨m₀ ^ b, a, ?_, ?_⟩
  · have h1 := pow_orderOf_eq_one (m₀ ^ b)
    rw [hord] at h1
    exact h1
  · intro h2
    rw [hfm, ← pow_mul] at h2
    have hd := orderOf_dvd_of_pow_eq_one h2
    rw [hy] at hd
    omega

end CFSG.LocalAnalysis.GLTheoremA.I2016Sp

end
