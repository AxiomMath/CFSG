module

public import CFSG.CGT.Timmesfeld75.Sec4CaseIFinal
public import CFSG.CGT.Timmesfeld75.Sec4CaseINormal
public import CFSG.CGT.Timmesfeld75.Sec4CaseIPGroup
public import CFSG.CGT.Timmesfeld75.Sec4CaseITheoremX

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

section Setup

variable {G : Type} [Group G] [Finite G] {T T₁ T₂ : Subgroup G} {a : G}

theorem Sec4Hyp.closure_sec4R_inter_eq (h : Sec4Hyp T T₁ a T₂) :
    Subgroup.closure ((sec4R T T₁ T₂ : Set G) ∩ classD T) = sec4R T T₁ T₂ := by
  apply le_antisymm
  · exact (Subgroup.closure_le _).2 Set.inter_subset_left
  · refine sup_le ?_ ?_
    · intro t ht
      by_cases ht1 : t = 1
      · rw [ht1]
        exact Subgroup.one_mem _
      · exact Subgroup.subset_closure ⟨left_le_sec4R ht, ⟨1, t, ht, ht1, by group⟩⟩
    · rw [← h.closure_sec4D₀_eq]
      exact Subgroup.closure_mono fun d hd => ⟨hd.2.1, hd.1⟩

end Setup

section SetE

variable {G : Type} [Group G] {T T₁ T₂ : Subgroup G}

@[expose] def sec4E (T T₁ T₂ : Subgroup G) : Set G :=
  {z | ∃ n ∈ Subgroup.normalizer (T : Set G), ∃ d ∈ classD T, d ∈ sec4R T T₁ T₂ ∧
    z = n * d * n⁻¹}

theorem sec4E_conj {z n : G} (hz : z ∈ sec4E T T₁ T₂) (hn : n ∈ Subgroup.normalizer (T : Set G)) :
    n * z * n⁻¹ ∈ sec4E T T₁ T₂ := by
  obtain ⟨m, hm, d, hdD, hdR, rfl⟩ := hz
  exact ⟨n * m, (Subgroup.normalizer (T : Set G)).mul_mem hn hm, d, hdD, hdR, by group⟩

theorem subset_sec4E {d : G} (hdD : d ∈ classD T) (hdR : d ∈ sec4R T T₁ T₂) :
    d ∈ sec4E T T₁ T₂ :=
  ⟨1, Subgroup.one_mem _, d, hdD, hdR, by group⟩

end SetE

section Normal

variable {G : Type} [Group G] [Finite G] {T T₁ T₂ : Subgroup G} {a : G}

theorem Sec4Hyp.closure_inter_sec4E_eq
    [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) (hind : SimpleCaseUpTo (Nat.card G))
    (hAsc : AschbacherNoPolarInput)
    (hA : Sec4I4TrivialAction)
    (hC : Sec4I4OuterAction) (h : Sec4Hyp T T₁ a T₂)
    (hq : 2 * Nat.card (normIn T T₁) < Nat.card T) (h16 : Nat.card T ≠ 16) {U : Subgroup G}
    (hU : IsPGroup 2 U) (hRU : sec4R T T₁ T₂ ≤ U) (hUN : U ≤ Subgroup.normalizer (T : Set G)) :
    Subgroup.closure ((U : Set G) ∩ sec4E T T₁ T₂) = sec4R T T₁ T₂ := by
  have hgen := h.closure_sec4R_inter_eq
  have hsub : (sec4R T T₁ T₂ : Set G) ∩ classD T ⊆
      ((U : Set G) ∩ sec4E T T₁ T₂) ∩ (sec4R T T₁ T₂ : Set G) :=
    fun d hd => ⟨⟨hRU hd.1, subset_sec4E hd.2 hd.1⟩, hd.1⟩
  have hR : Subgroup.closure (((U : Set G) ∩ sec4E T T₁ T₂) ∩ (sec4R T T₁ T₂ : Set G)) =
      sec4R T T₁ T₂ :=
    le_antisymm ((Subgroup.closure_le _).2 Set.inter_subset_right)
      (calc sec4R T T₁ T₂ = Subgroup.closure ((sec4R T T₁ T₂ : Set G) ∩ classD T) := hgen.symm
        _ ≤ _ := Subgroup.closure_mono hsub)
  by_contra hne
  obtain ⟨x, ⟨hxU, hxE⟩, hxN, hxR⟩ := exists_mem_normalizer_of_closure_ne hU
    Set.inter_subset_left
    (fun s hs d hd => ⟨U.mul_mem (U.mul_mem hs hd.1) (U.inv_mem hs),
      sec4E_conj hd.2 (hUN hs)⟩) hRU hR hne
  obtain ⟨n, hn, d, hdD, hdR, rfl⟩ := hxE
  have hxD : n * d * n⁻¹ ∈ classD T := conj_mem_classD hdD n
  have hxT : n * d * n⁻¹ ∈ Subgroup.normalizer (T : Set G) := hUN hxU
  have hxN' := h.mem_normalizer_sec4N hxN hxT
  obtain ⟨t, htT, htL, hact, hlt⟩ :=
    h.exists_acts_like_t hnab hind hAsc hA hC hq h16 hxD hxT hxN' hxR
  rw [card_inf_centralizer_conj_of_mem_normalizer hn] at hlt
  rcases h.mem_or_mem_sec4N_of_mem_sec4R ⟨hdD, sec4R_le_normalizer_left hdR⟩ hdR with hdT | hdN
  · exact hxR (left_le_sec4R (conj_mem_of_mem_normalizer hn hdT))
  · have hLC : normIn T T₁ ≤ T ⊓ Subgroup.centralizer ({d} : Set G) := fun l hl =>
      ⟨normIn_le _ _ hl, Subgroup.mem_centralizer_singleton_iff.2
        (elemAbelian_mul_comm h.isElemAbelian_sec4N (normIn_le_sec4N_left hl) hdN)⟩
    exact absurd (Subgroup.card_le_of_le hLC) (not_le.2 hlt)

theorem Sec4Hyp.mem_normalizer_sec4R
    [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) (hind : SimpleCaseUpTo (Nat.card G))
    (hAsc : AschbacherNoPolarInput)
    (hA : Sec4I4TrivialAction)
    (hC : Sec4I4OuterAction) (h : Sec4Hyp T T₁ a T₂)
    (hq : 2 * Nat.card (normIn T T₁) < Nat.card T) (h16 : Nat.card T ≠ 16) {U : Subgroup G}
    (hU : IsPGroup 2 U) (hRU : sec4R T T₁ T₂ ≤ U) (hUN : U ≤ Subgroup.normalizer (T : Set G))
    {u : G} (hu : u ∈ U) : u ∈ Subgroup.normalizer (sec4R T T₁ T₂ : Set G) := by
  rw [← h.closure_inter_sec4E_eq hnab hind hAsc hA hC hq h16 hU hRU hUN]
  exact mem_normalizer_closure fun d hd => ⟨U.mul_mem (U.mul_mem hu hd.1) (U.inv_mem hu),
    sec4E_conj hd.2 (hUN hu)⟩

end Normal

end CFSG.CGT.Timmesfeld75
