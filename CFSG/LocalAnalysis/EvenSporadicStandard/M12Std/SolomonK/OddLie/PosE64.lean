module

public import CFSG.GH74.Filter.ElemAbelian

public section

namespace CFSG.EvenSporadicStandard.M12Std.SolomonK.OddLie

open Subgroup

@[expose] def PosE64 (G : Type) [Group G] : Prop :=
  ∃ E : Subgroup G, (∀ x ∈ E, x * x = 1) ∧ 2 ^ 6 ≤ Nat.card E ∧
    ∃ H : Subgroup G, H ≤ normalizer (E : Set G) ∧ 5 ∣ Nat.card H

theorem PosE64.of_mulEquiv {G G' : Type} [Group G] [Group G'] (e : G ≃* G') (h : PosE64 G) :
    PosE64 G' := by
  obtain ⟨E, hsq, hcard, H, hH, h5⟩ := h
  refine ⟨E.map e.toMonoidHom, ?_, ?_, H.map e.toMonoidHom, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    rw [← map_mul, hsq y hy, map_one]
  · rwa [Subgroup.card_map_of_injective e.injective]
  · exact (Subgroup.map_mono hH).trans (Subgroup.le_normalizer_map _)
  · rwa [Subgroup.card_map_of_injective e.injective]

theorem frame_conj_pow {G : Type} [Group G] {n : ℕ} (x : Fin n → G) (y : G)
    (σ : Equiv.Perm (Fin n)) (hconj : ∀ k, y * x k * y⁻¹ = x (σ k)) (m : ℕ) (k : Fin n) :
    y ^ m * x k * (y ^ m)⁻¹ = x ((σ ^ m) k) := by
  induction m generalizing k with
  | zero => simp
  | succ m ih =>
    calc y ^ (m + 1) * x k * (y ^ (m + 1))⁻¹
        = y * (y ^ m * x k * (y ^ m)⁻¹) * y⁻¹ := by group
      _ = x ((σ ^ (m + 1)) k) := by
        rw [ih, hconj, pow_succ' σ m, Equiv.Perm.mul_apply]

theorem posE64_of_frame {G : Type} [Group G] [Finite G] (x : Fin 6 → G) (y : G)
    (σ : Equiv.Perm (Fin 6)) (hsq : ∀ k, x k * x k = 1) (hcomm : ∀ i j, x i * x j = x j * x i)
    (hker : ∀ a : Fin 6 → Fin 2, a ≠ 0 → (List.ofFn fun k => x k ^ (a k : ℕ)).prod ≠ 1)
    (hinj : Function.Injective x) (hconj : ∀ k, y * x k * y⁻¹ = x (σ k))
    (hσ : ∀ m : ℕ, (σ ^ m) 0 = 0 → 5 ∣ m) : PosE64 G := by
  set E : Subgroup G := Subgroup.closure (Set.range x) with hE
  have hEc : IsMulCommutative E :=
    Subgroup.isMulCommutative_closure (by
      rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
      exact hcomm i j)
  have hEsq : ∀ e ∈ E, e * e = 1 := by
    intro e he
    induction he using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨k, rfl⟩ := hg
      exact hsq k
    | one => simp
    | mul a b ha hb iha ihb =>
      have hab : a * b = b * a :=
        congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : E) ⟨b, hb⟩)
      calc a * b * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [← hab]
        _ = (a * a) * (b * b) := by group
        _ = 1 := by rw [iha, ihb, one_mul]
    | inv a ha iha => rw [← mul_inv_rev, iha, inv_one]
  have hcard : 2 ^ 6 ≤ Nat.card E := by
    let u : Fin 6 → E := fun k => ⟨x k, Subgroup.subset_closure ⟨k, rfl⟩⟩
    have hu2 : ∀ k, u k ^ 2 = 1 := fun k => Subtype.ext (by simpa [u, sq] using hsq k)
    have huc : ∀ i j, Commute (u i) (u j) := fun i j => Subtype.ext (hcomm i j)
    have huk : ∀ a : Fin 6 → Fin 2, a ≠ 0 →
        (List.ofFn fun k => u k ^ (a k : ℕ)).prod ≠ 1 := by
      intro a ha h1
      apply hker a ha
      have h2 := congrArg Subtype.val h1
      simpa [Function.comp_def, u] using h2
    obtain ⟨f, hf⟩ := CFSG.GH74.Filter.exists_injective_of_commuting_involutions u hu2 huc huk
    have := Nat.card_le_card_of_injective f hf
    rwa [CFSG.GH74.Filter.card_pi_zmod_two] at this
  have hyN : y ∈ normalizer (Set.range x) := by
    rw [mem_normalizer_iff_conj_image_eq]
    ext z
    simp only [Set.mem_image, Set.mem_range, MulAut.conj_apply]
    constructor
    · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
      exact ⟨σ k, (hconj k).symm⟩
    · rintro ⟨k, rfl⟩
      exact ⟨x (σ.symm k), ⟨σ.symm k, rfl⟩, by rw [hconj, σ.apply_symm_apply]⟩
  refine ⟨E, hEsq, hcard, Subgroup.zpowers y,
    Subgroup.zpowers_le.2 (Subgroup.normalizer_le_normalizer_closure _ hyN), ?_⟩
  rw [Nat.card_zpowers]
  apply hσ
  have h1 := frame_conj_pow x y σ hconj (orderOf y) 0
  rw [pow_orderOf_eq_one, inv_one, one_mul, mul_one] at h1
  exact (hinj h1).symm

end CFSG.EvenSporadicStandard.M12Std.SolomonK.OddLie
