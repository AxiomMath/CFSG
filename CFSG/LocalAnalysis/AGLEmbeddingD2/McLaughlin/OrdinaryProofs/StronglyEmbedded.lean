module

public import CFSG.RankThree.PartTwo.Sec21.StronglyEmbedded

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs

open CFSG.Open CFSG.RankThree.PartTwo.Sec21

variable {N : Type*} [Group N] [Finite N] {p : ℕ} [Fact p.Prime]

theorem card_le_pow_factorization {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {K : Subgroup G} {m : ℕ} (hK : Nat.card K = p ^ m) {M : ℕ} (hM : Nat.card K ∣ M)
    (hM0 : M ≠ 0) : Nat.card K ≤ p ^ M.factorization p := by
  rw [hK] at hM ⊢
  exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos
    ((Nat.Prime.pow_dvd_iff_le_factorization (Fact.out : p.Prime) hM0).mp hM)

theorem exists_mem_normalizer_not_mem {Q H : Subgroup N} (hQ : IsPGroup p Q) (hHQ : H ≤ Q)
    (hne : H ≠ Q) :
    ∃ x ∈ Q, x ∈ Subgroup.normalizer (H : Set N) ∧ x ∉ H := by
  have : Group.IsNilpotent Q := hQ.isNilpotent
  have hnc : NormalizerCondition Q := Group.normalizerCondition_of_isNilpotent
  have htop : H.subgroupOf Q ≠ ⊤ := by
    intro h
    exact hne (le_antisymm hHQ (Subgroup.subgroupOf_eq_top.mp h))
  obtain ⟨x, hxN, hxnot⟩ := IsConcreteLE.exists_of_lt (hnc _ (lt_of_le_of_ne le_top htop))
  refine ⟨x, x.2, ?_, fun hxH => hxnot (Subgroup.mem_subgroupOf.mpr hxH)⟩
  have : x ∈ (Subgroup.normalizer (H : Set N)).subgroupOf Q := by
    rw [Subgroup.subgroupOf_normalizer_eq hHQ]
    exact hxN
  exact Subgroup.mem_subgroupOf.mp this

theorem exists_sylow_le_of_glbStronglyEmbedded {N₀ : Subgroup N} (h : GLBStronglyEmbedded p N₀) :
    ∃ Q : Sylow p N, (Q : Subgroup N) ≤ N₀ := by
  classical
  have hp : p.Prime := Fact.out
  have hN₀ : Nat.card N₀ ≠ 0 := Nat.card_pos.ne'
  have hdvd : p ∣ Nat.card N₀ := h.2.1
  have hv : 0 < (Nat.card N₀).factorization p := hp.factorization_pos_of_dvd hN₀ hdvd
  let P0 : Sylow p N₀ := default
  let P : Subgroup N := (P0 : Subgroup N₀).map N₀.subtype
  have hPN₀ : P ≤ N₀ := Subgroup.map_subtype_le _
  have hPcard : Nat.card P = p ^ (Nat.card N₀).factorization p := by
    rw [Subgroup.card_map_of_injective N₀.subtype_injective, Sylow.card_eq_multiplicity]
  have hPpg : IsPGroup p P := IsPGroup.iff_card.mpr ⟨_, hPcard⟩
  have hPne : P ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card P = 1 := by rw [hbot, Subgroup.card_bot]
    have h2 := Nat.pow_le_pow_right hp.pos hv
    rw [hPcard] at h1
    rw [pow_one] at h2
    have := hp.one_lt
    omega
  obtain ⟨Q, hPQ⟩ := hPpg.exists_le_sylow
  refine ⟨Q, ?_⟩
  have hQP : (Q : Subgroup N) = P := by
    by_contra hne
    obtain ⟨x, hxQ, hxN, hxP⟩ :=
      exists_mem_normalizer_not_mem Q.isPGroup' hPQ (Ne.symm hne)
    have hxN₀ : x ∈ N₀ :=
      normalizer_le_of_glbStronglyEmbedded h hPN₀ hPpg hPne hxN
    have hQcard : Nat.card (Q : Subgroup N) = p ^ (Nat.card N).factorization p :=
      Sylow.card_eq_multiplicity Q
    have hKdvd : Nat.card (N₀ ⊓ (Q : Subgroup N) : Subgroup N) ∣ Nat.card (Q : Subgroup N) :=
      Subgroup.card_dvd_of_le inf_le_right
    rw [hQcard] at hKdvd
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hp).mp hKdvd
    have hKle : Nat.card (N₀ ⊓ (Q : Subgroup N) : Subgroup N) ≤ p ^ (Nat.card N₀).factorization p :=
      card_le_pow_factorization hm (Subgroup.card_dvd_of_le inf_le_left) hN₀
    have hPK : P ≤ N₀ ⊓ (Q : Subgroup N) := le_inf hPN₀ hPQ
    have hPK_eq : P = N₀ ⊓ (Q : Subgroup N) :=
      Subgroup.eq_of_le_of_card_ge hPK (by rw [hPcard]; exact hKle)
    apply hxP
    rw [hPK_eq]
    exact ⟨hxN₀, hxQ⟩
  rw [hQP]
  exact hPN₀

theorem not_dvd_index_of_glbStronglyEmbedded {N₀ : Subgroup N} (h : GLBStronglyEmbedded p N₀) :
    ¬ p ∣ N₀.index := by
  obtain ⟨Q, hQ⟩ := exists_sylow_le_of_glbStronglyEmbedded h
  intro hd
  exact (Sylow.not_dvd_index Q) (hd.trans (Subgroup.index_dvd_of_le hQ))

theorem exists_sylow_le_of_not_dvd_index {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {H : Subgroup G} (h : ¬ p ∣ H.index) : ∃ Q : Sylow p G, (Q : Subgroup G) ≤ H := by
  classical
  have hp : p.Prime := Fact.out
  let P0 : Sylow p H := default
  let P : Subgroup G := (P0 : Subgroup H).map H.subtype
  have hPH : P ≤ H := Subgroup.map_subtype_le _
  have hidx : H.index.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd h
  have hfact : (Nat.card H).factorization p = (Nat.card G).factorization p := by
    rw [← H.card_mul_index, Nat.factorization_mul (Nat.card_pos (α := H)).ne'
      H.index_ne_zero_of_finite, Finsupp.add_apply, hidx, add_zero]
  have hPcard : Nat.card P = p ^ (Nat.card G).factorization p := by
    rw [Subgroup.card_map_of_injective H.subtype_injective, Sylow.card_eq_multiplicity, hfact]
  have hPpg : IsPGroup p P := IsPGroup.iff_card.mpr ⟨_, hPcard⟩
  obtain ⟨Q, hPQ⟩ := hPpg.exists_le_sylow
  refine ⟨Q, ?_⟩
  have hQcard : Nat.card (Q : Subgroup G) = p ^ (Nat.card G).factorization p :=
    Sylow.card_eq_multiplicity Q
  have hQP : (Q : Subgroup G) = P :=
    (Subgroup.eq_of_le_of_card_ge hPQ (le_of_eq (by rw [hQcard, hPcard]))).symm
  rw [hQP]
  exact hPH

theorem relIndex_sup_eq_of_normal {X : Subgroup N} (hX : X.Normal) (H : Subgroup N) :
    H.relIndex (X ⊔ H) = H.relIndex X := by
  have := hX
  have hd : X.relIndex H ≠ 0 := by
    rw [Subgroup.relIndex]
    exact Subgroup.index_ne_zero_of_finite
  have e1 : (H ⊓ X).relIndex H * H.relIndex (X ⊔ H) = (H ⊓ X).relIndex (X ⊔ H) :=
    Subgroup.relIndex_mul_relIndex (H ⊓ X) H (X ⊔ H) inf_le_left le_sup_right
  have e2 : (H ⊓ X).relIndex X * X.relIndex (X ⊔ H) = (H ⊓ X).relIndex (X ⊔ H) :=
    Subgroup.relIndex_mul_relIndex (H ⊓ X) X (X ⊔ H) inf_le_right le_sup_left
  rw [Subgroup.inf_relIndex_left] at e1
  rw [Subgroup.inf_relIndex_right, Subgroup.relIndex_sup_left] at e2
  refine Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hd) ?_
  rw [e1, ← e2, mul_comm]

theorem sup_eq_top_of_normal {N₀ X : Subgroup N} (h : GLBStronglyEmbedded p N₀) (hX : X.Normal)
    (hp : p ∣ Nat.card X) : X ⊔ N₀ = ⊤ := by
  classical
  have hp' : p.Prime := Fact.out
  have := hX
  have hX0 : Nat.card X ≠ 0 := Nat.card_pos.ne'
  have hc : ¬ p ∣ N₀.relIndex X := by
    rw [← relIndex_sup_eq_of_normal hX N₀]
    intro hd
    apply not_dvd_index_of_glbStronglyEmbedded h
    exact hd.trans ⟨_, (Subgroup.relIndex_mul_index le_sup_right).symm⟩
  obtain ⟨Q, hQ⟩ := exists_sylow_le_of_not_dvd_index (G := X) (H := N₀.subgroupOf X) hc
  have hQcard : Nat.card (Q : Subgroup X) = p ^ (Nat.card X).factorization p :=
    Sylow.card_eq_multiplicity Q
  have hQ1 : Nat.card (Q : Subgroup X) ≠ 1 := by
    intro h1
    have h2 := Nat.pow_le_pow_right hp'.pos (hp'.factorization_pos_of_dvd hX0 hp)
    rw [hQcard] at h1
    rw [pow_one] at h2
    have := hp'.one_lt
    omega
  have hSN₀ : (Q : Subgroup X).map X.subtype ≤ N₀ := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    exact Subgroup.mem_subgroupOf.mp (hQ hy)
  have hSpg : IsPGroup p ((Q : Subgroup X).map X.subtype) := Q.isPGroup'.map X.subtype
  have hScard : Nat.card ((Q : Subgroup X).map X.subtype) = Nat.card (Q : Subgroup X) :=
    Subgroup.card_map_of_injective X.subtype_injective
  have hSne : (Q : Subgroup X).map X.subtype ≠ ⊥ := by
    intro hbot
    apply hQ1
    rw [← hScard, hbot, Subgroup.card_bot]
  have hNle : Subgroup.normalizer (((Q : Subgroup X).map X.subtype : Subgroup N) : Set N) ≤ N₀ :=
    normalizer_le_of_glbStronglyEmbedded h hSN₀ hSpg hSne
  have hfrat := Sylow.normalizer_sup_eq_top (N := X) Q
  rw [eq_top_iff, ← hfrat]
  exact sup_le (hNle.trans le_sup_right) le_sup_left

end CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs
