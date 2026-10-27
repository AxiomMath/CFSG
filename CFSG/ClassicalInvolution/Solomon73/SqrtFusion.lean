module

public import CFSG.Quasithin.Background.A1cTransfer

public section

namespace CFSG.ClassicalInvolution.Solomon73

open CFSG.Quasithin

variable {G : Type*} [Group G]

theorem isWeaklyClosedIn_self [Finite G] {p : ℕ} [Fact p.Prime] (T : Sylow p G) :
    IsWeaklyClosedIn (T : Subgroup G) T := by
  intro g hg
  apply Subgroup.eq_of_le_of_card_ge hg
  rw [conjSubgroup, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]

theorem nat_card_sq_eq_of_isConj [Finite G] {p : ℕ} [Fact p.Prime] (T : Sylow p G) {x y : G}
    (hx : x ∈ Subgroup.centralizer (T : Set G)) (hy : y ∈ Subgroup.centralizer (T : Set G))
    (hxy : IsConj x y) :
    Nat.card {s : (T : Subgroup G) // (s : G) ^ 2 = x} =
      Nat.card {s : (T : Subgroup G) // (s : G) ^ 2 = y} := by
  obtain ⟨c, hc⟩ := isConj_iff.mp hxy
  obtain ⟨n, hn, hny⟩ := burnside_fusion_lemma_centralizer T le_rfl (isWeaklyClosedIn_self T)
    hx hy (g := c⁻¹) (by rw [inv_inv]; exact hc)
  have hn' : n⁻¹ ∈ Subgroup.normalizer ((T : Subgroup G) : Set G) := inv_mem hn
  have hmem : ∀ s ∈ (T : Subgroup G), n⁻¹ * s * n ∈ (T : Subgroup G) := fun s hs => by
    have h := (Subgroup.mem_normalizer_iff.mp hn' s).mp hs
    rwa [inv_inv] at h
  have hmem' : ∀ s ∈ (T : Subgroup G), n * s * n⁻¹ ∈ (T : Subgroup G) := fun s hs =>
    (Subgroup.mem_normalizer_iff.mp hn s).mp hs
  have hxn : x = n * y * n⁻¹ := by rw [← hny]; group
  refine Nat.card_congr
    { toFun := fun s => ⟨⟨n⁻¹ * s * n, hmem _ s.1.2⟩, ?_⟩
      invFun := fun s => ⟨⟨n * s * n⁻¹, hmem' _ s.1.2⟩, ?_⟩
      left_inv := fun s => ?_
      right_inv := fun s => ?_ }
  · have h := conj_pow (a := n⁻¹) (b := (s.1 : G)) (i := 2)
    rw [inv_inv] at h
    simp only [h, s.2, hny]
  · have h := conj_pow (a := n) (b := (s.1 : G)) (i := 2)
    simp only [h, s.2, hxn]
  · apply Subtype.ext
    apply Subtype.ext
    show n * (n⁻¹ * (s.1 : G) * n) * n⁻¹ = s.1
    group
  · apply Subtype.ext
    apply Subtype.ext
    show n⁻¹ * (n * (s.1 : G) * n⁻¹) * n = s.1
    group

theorem nat_card_sq_congr {H K : Type*} [Group H] [Group K] (φ : H ≃* K) (x : H) :
    Nat.card {s : H // s ^ 2 = x} = Nat.card {s : K // s ^ 2 = φ x} :=
  Nat.card_congr
    { toFun := fun s => ⟨φ s, by rw [← map_pow, s.2]⟩
      invFun := fun s => ⟨φ.symm s, by rw [← map_pow, s.2, MulEquiv.symm_apply_apply]⟩
      left_inv := fun s => Subtype.ext (φ.symm_apply_apply s.1)
      right_inv := fun s => Subtype.ext (φ.apply_symm_apply s.1) }

theorem nat_card_sq_subtype (H : Subgroup G) (x : H) :
    Nat.card {s : H // (s : G) ^ 2 = x} = Nat.card {s : H // s ^ 2 = x} :=
  Nat.card_congr
    { toFun := fun s => ⟨s.1, Subtype.ext (by rw [Subgroup.coe_pow]; exact s.2)⟩
      invFun := fun s => ⟨s.1, by rw [← Subgroup.coe_pow, s.2]⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

end CFSG.ClassicalInvolution.Solomon73
