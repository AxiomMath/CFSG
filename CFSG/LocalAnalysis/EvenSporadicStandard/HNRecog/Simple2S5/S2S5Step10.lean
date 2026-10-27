module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.Data.Finite.Perm

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Simple2S5

private theorem eq_top_of_card_eq_aux {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (W : Subgroup S) (hW : Nat.card W = 126000)
    (h2 : ∀ R : Subgroup S, IsPGroup 2 R → Nat.card R ≤ 16)
    (hdvd : Nat.card S ∣ 44352000) : W = ⊤ := by
  have hmul : Nat.card W * W.index = Nat.card S := W.card_mul_index
  rw [hW] at hmul
  have hk : W.index ∣ 352 := by
    rw [← hmul, show (44352000 : ℕ) = 126000 * 352 by norm_num] at hdvd
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) hdvd
  have hodd : ¬ 2 ∣ W.index := by
    rintro ⟨m, hm⟩
    obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := S) 2 (n := 5)
      ⟨7875 * m, by rw [← hmul, hm]; ring⟩
    have hp : IsPGroup 2 K := IsPGroup.of_card hK
    have := h2 K hp
    rw [hK] at this
    norm_num at this
  have key : ∀ k : ℕ, k ∣ 352 → ¬ 2 ∣ k → k = 1 ∨ k = 11 := by
    intro k h1 h2
    have := Nat.le_of_dvd (by norm_num) h1
    interval_cases k <;> omega
  have hk' := key _ hk hodd
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (MulAction.toPermHom S (S ⧸ W)).ker
    with hker | hker
  · exfalso
    have hinj : Function.Injective (MulAction.toPermHom S (S ⧸ W)) :=
      (MonoidHom.ker_eq_bot_iff _).1 hker
    have hd : Nat.card S ∣ (W.index).factorial := by
      have := Subgroup.card_dvd_of_injective _ hinj
      rwa [Nat.card_perm] at this
    rw [← hmul] at hd
    rcases hk' with h | h <;> rw [h] at hd <;> revert hd <;> decide
  · apply eq_top_iff.2
    intro g _
    have hg : g ∈ (MulAction.toPermHom S (S ⧸ W)).ker := hker ▸ Subgroup.mem_top g
    have h1 : g • ((1 : S) : S ⧸ W) = ((1 : S) : S ⧸ W) := by
      simpa using congrArg (fun σ : Equiv.Perm (S ⧸ W) => σ ((1 : S) : S ⧸ W))
        (MonoidHom.mem_ker.1 hg)
    rw [MulAction.Quotient.smul_mk, QuotientGroup.eq] at h1
    simpa using h1

theorem eq_of_card_eq {G : Type*} [Group G] [Finite G] {S W : Subgroup G} [IsSimpleGroup ↥S]
    (hWS : W ≤ S) (hW : Nat.card ↥W = 126000)
    (h2 : ∀ R : Subgroup G, R ≤ S → IsPGroup 2 ↥R → Nat.card ↥R ≤ 16)
    (hdvd : Nat.card ↥S ∣ 44352000) : W = S := by
  have hW' : Nat.card ↥(W.subgroupOf S) = 126000 := by
    rw [← hW]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWS).toEquiv
  have h2' : ∀ R : Subgroup ↥S, IsPGroup 2 ↥R → Nat.card ↥R ≤ 16 := by
    intro R hR
    have hcard : Nat.card ↥(R.map S.subtype) = Nat.card ↥R :=
      Subgroup.card_map_of_injective S.subtype_injective
    have := h2 (R.map S.subtype) (Subgroup.map_subtype_le R) (hR.map S.subtype)
    rwa [hcard] at this
  have htop : W.subgroupOf S = ⊤ :=
    eq_top_of_card_eq_aux (W.subgroupOf S) hW' h2' hdvd
  exact le_antisymm hWS (Subgroup.subgroupOf_eq_top.1 htop)

end CFSG.EvenSporadicStandard.HNRecog.Simple2S5
