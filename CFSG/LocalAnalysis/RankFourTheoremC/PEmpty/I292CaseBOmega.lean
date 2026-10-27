module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292LinUniDefs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseB

open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {Y : Type} [Group Y] {T L : Subgroup Y}

theorem omegaOneTwo_le : omegaOneTwo T L ≤ T ⊓ L :=
  (Subgroup.closure_le _).2 fun _ ht => ht.1

theorem omegaOneTwo_le_left : omegaOneTwo T L ≤ L := omegaOneTwo_le.trans inf_le_right

theorem isPGroup_omegaOneTwo (hT : IsPGroup 2 T) : IsPGroup 2 (omegaOneTwo T L) :=
  IsPGroup.to_le hT (omegaOneTwo_le.trans inf_le_left)

theorem omegaOneTwo_ne_bot [Finite Y] (hT : IsPGroup 2 T) (hTL : T ⊓ L ≠ ⊥) :
    omegaOneTwo T L ≠ ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Nontrivial ↥(T ⊓ L) := (Subgroup.nontrivial_iff_ne_bot _).2 hTL
  have hP : IsPGroup 2 ↥(T ⊓ L) := IsPGroup.to_le hT inf_le_left
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hn1 : n ≠ 0 := by
    rintro rfl
    have h1 : 1 < Nat.card ↥(T ⊓ L) := Finite.one_lt_card
    rw [hn] at h1
    simp at h1
  have hdvd : 2 ∣ Nat.card ↥(T ⊓ L) := by
    rw [hn]
    exact dvd_pow_self 2 hn1
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  have ht2 : (t : Y) ^ 2 = 1 := by
    have h1 : t ^ 2 = 1 := by
      have := pow_orderOf_eq_one t
      rwa [ht] at this
    simpa using congrArg Subtype.val h1
  have ht1 : (t : Y) ≠ 1 := by
    intro h
    have h1 : t = 1 := Subtype.ext h
    rw [h1, orderOf_one] at ht
    omega
  intro hbot
  have hmem : (t : Y) ∈ omegaOneTwo T L := Subgroup.subset_closure ⟨t.2, ht2⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  exact ht1 hmem

theorem conj_mem_omegaOneTwo' [L.Normal] {g : Y} (hg : g ∈ normalizer (T : Set Y)) {h : Y}
    (hh : h ∈ omegaOneTwo T L) : g * h * g⁻¹ ∈ omegaOneTwo T L := by
  have hsub : (omegaOneTwo T L).map (MulAut.conj g).toMonoidHom ≤ omegaOneTwo T L := by
    unfold omegaOneTwo
    rw [MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨s, ⟨hsTL, hs2⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.1 hg s).1 (Subgroup.mem_inf.1 hsTL).1
      · exact ‹L.Normal›.conj_mem s (Subgroup.mem_inf.1 hsTL).2 g
    · show ((MulAut.conj g).toMonoidHom s) ^ 2 = 1
      rw [← map_pow, hs2, map_one]
  exact hsub ⟨h, hh, rfl⟩

theorem mem_normalizer_omegaOneTwo' [L.Normal] {g : Y} (hg : g ∈ normalizer (T : Set Y)) :
    g ∈ normalizer (omegaOneTwo T L : Set Y) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => conj_mem_omegaOneTwo' hg hh, fun hh => ?_⟩
  have := conj_mem_omegaOneTwo' (Subgroup.inv_mem _ hg) hh
  simpa [mul_assoc] using this

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseB
