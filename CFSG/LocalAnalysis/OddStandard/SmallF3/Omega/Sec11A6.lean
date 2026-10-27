module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Notation

public section

namespace CFSG.OddStandard.SmallF3.Omega

variable {G : Type} [Group G]

private theorem sec11A6_fin6_exists_ne (i m : Fin 6) (h : i ≠ m) :
    ∃ k : Fin 6, (k = 0 ∨ k = 1 ∨ k = 2) ∧ k ≠ i ∧ k ≠ m := by
  revert i m
  decide

theorem sec11_normal_two_alt6 {N : Subgroup ↥(alternatingGroup (Fin 6))} (hN : N.Normal)
    (h2 : IsPGroup 2 N) : N = ⊥ := by
  haveI : IsSimpleGroup ↥(alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by norm_num [Nat.card_fin])
  haveI : N.Normal := hN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · exact h
  · exfalso
    rw [h] at h2
    let w : Equiv.Perm (Fin 6) := Equiv.swap 0 1 * Equiv.swap 0 2
    have hw : w.IsThreeCycle :=
      Equiv.Perm.isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)
    let g : ↥(alternatingGroup (Fin 6)) := ⟨w, hw.mem_alternatingGroup⟩
    have hgval : (g : Equiv.Perm (Fin 6)) = w := rfl
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp h2) ⟨g, Subgroup.mem_top g⟩
    have hkg : orderOf g = 2 ^ k := by
      simpa only [Subgroup.orderOf_mk] using hk
    have hg3 : orderOf g = 3 := by
      rw [← Subgroup.orderOf_coe g, hgval]
      exact hw.orderOf
    have h3 : 3 = 2 ^ k := by
      rw [← hg3]
      exact hkg
    have hdvd : 3 ∣ 2 ^ k := by rw [← h3]
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd) (by norm_num)

theorem sec11_normal_two_perm6 {N : Subgroup (Equiv.Perm (Fin 6))} (hN : N.Normal)
    (h2 : IsPGroup 2 N) : N = ⊥ := by
  haveI : N.Normal := hN
  have h2' : IsPGroup 2 (N.subgroupOf (alternatingGroup (Fin 6))) := by
    have hinf : IsPGroup 2 ↥(N ⊓ alternatingGroup (Fin 6)) := h2.to_inf_left
    rw [← Subgroup.inf_subgroupOf_right N (alternatingGroup (Fin 6))]
    exact hinf.of_equiv (Subgroup.subgroupOfEquivOfLe
      (inf_le_right : N ⊓ alternatingGroup (Fin 6) ≤ alternatingGroup (Fin 6))).symm
  have hsub : N.subgroupOf (alternatingGroup (Fin 6)) = ⊥ :=
    sec11_normal_two_alt6 (hN.subgroupOf _) h2'
  rw [eq_bot_iff]
  intro n hn
  rw [Subgroup.mem_bot]
  by_contra hn1
  have hcomm : ∀ g : Equiv.Perm (Fin 6), g * n = n * g := by
    intro g
    have hcN : g * n * g⁻¹ * n⁻¹ ∈ N :=
      N.mul_mem (hN.conj_mem n hn g) (N.inv_mem hn)
    have hcA : g * n * g⁻¹ * n⁻¹ ∈ alternatingGroup (Fin 6) := by
      rw [Equiv.Perm.mem_alternatingGroup]
      simp only [map_mul, map_inv, map_one]
      rw [mul_inv_cancel_comm, mul_inv_cancel]
    have hmemb : (⟨g * n * g⁻¹ * n⁻¹, hcA⟩ : ↥(alternatingGroup (Fin 6))) ∈
        N.subgroupOf (alternatingGroup (Fin 6)) := hcN
    rw [hsub, Subgroup.mem_bot] at hmemb
    have hc : g * n * g⁻¹ * n⁻¹ = 1 := by
      have := congrArg (fun x : ↥(alternatingGroup (Fin 6)) => (x : Equiv.Perm (Fin 6)))
        hmemb
      simpa using this
    have h1 : g * n * g⁻¹ = n := mul_inv_eq_one.mp hc
    rw [show g * n = g * n * g⁻¹ * g by group, h1]
  have hni : ∃ i : Fin 6, n i ≠ i := by
    by_contra h
    push Not at h
    exact hn1 (Equiv.ext fun i => by simpa using h i)
  obtain ⟨i, hi⟩ := hni
  obtain ⟨k, _, hki, hkm⟩ := sec11A6_fin6_exists_ne i (n i) (Ne.symm hi)
  let j : Fin 6 := k
  let g : Equiv.Perm (Fin 6) := Equiv.swap (n i) j
  have hgi : g i = i := Equiv.swap_apply_of_ne_of_ne (Ne.symm hi) (Ne.symm hki)
  have hgn : (g * n) i = j := by simp [g]
  have hng : (n * g) i = n i := by simp [hgi]
  rw [hcomm g] at hgn
  rw [hng] at hgn
  exact hkm hgn.symm

theorem sec11_pCore_hyp111 {t : G} {S L : Subgroup G} (h : Hyp111 t S L) :
    CFSG.pCore 2 ↥(secMstar t S L) = ⊥ := by
  apply le_antisymm ?_ bot_le
  rw [CFSG.pCore]
  apply sSup_le
  rintro K ⟨hKn, hK2⟩
  rw [le_bot_iff]
  rcases h with he | he
  · obtain ⟨e⟩ := he
    have hmap : K.map e.toMonoidHom = ⊥ :=
      sec11_normal_two_alt6 (hKn.map e.toMonoidHom e.surjective) (hK2.map e.toMonoidHom)
    exact (Subgroup.map_eq_bot_iff_of_injective K e.injective).mp hmap
  · obtain ⟨e⟩ := he
    have hmap : K.map e.toMonoidHom = ⊥ :=
      sec11_normal_two_perm6 (hKn.map e.toMonoidHom e.surjective) (hK2.map e.toMonoidHom)
    exact (Subgroup.map_eq_bot_iff_of_injective K e.injective).mp hmap

end CFSG.OddStandard.SmallF3.Omega
