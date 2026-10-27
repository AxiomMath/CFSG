module

public import CFSG.GH74.Uniqueness.Section14Defs
public import CFSG.GroupTheory.ABGLocalTools.FrobeniusFixedPoints

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

theorem frobRank_aux {H M : Type} [Group H] [Finite H] [AddCommGroup M] [Module (ZMod 2) M]
    [Finite M] (ρ : Representation (ZMod 2) H M) (K B : Subgroup H) [K.Normal]
    (hK : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a) (hodd : Odd (Nat.card K))
    (hfpf : ∀ b ∈ B, b ≠ 1 → ∀ k ∈ K, b * k = k * b → k = 1)
    (hmove : ∃ k ∈ K, ∃ v : M, ρ k v ≠ v) : 2 ^ Nat.card B ≤ Nat.card M := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : Module.Finite (ZMod 2) M := Module.Finite.of_finite
  let ρK : Representation (ZMod 2) K M := ρ.comp K.subtype
  let N : Module.End (ZMod 2) M := Representation.norm ρK
  have hNapply : ∀ x : M, N x = ∑ k : K, ρ k x := by
    intro x
    simp [N, Representation.norm, ρK, LinearMap.sum_apply]
  have hNcomm : ∀ (h : H) (x : M), N (ρ h x) = ρ h (N x) := by
    intro h x
    rw [hNapply, hNapply, map_sum]
    let e : K ≃ K := (MulAut.conjNormal (H := K) h⁻¹).toEquiv
    rw [← Equiv.sum_comp e (fun k => ρ h (ρ k x))]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hek : ((e k : K) : H) = h⁻¹ * k * h := by
      simp [e]
    rw [hek, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
    congr 2
    group
  let W : Submodule (ZMod 2) M := LinearMap.ker N
  have hW : ∀ h : H, W ≤ W.comap (ρ h) := by
    intro h w hw
    simp only [W, Submodule.mem_comap, LinearMap.mem_ker] at hw ⊢
    rw [hNcomm, hw, map_zero]
  let ρW : Representation (ZMod 2) H W := ρ.subrepresentation W hW
  have hNfix : ∀ x : M, (∀ k : K, ρ k x = x) → N x = x := by
    intro x hx
    rw [hNapply]
    simp only [hx, Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul (ZMod 2)]
    have : ((Fintype.card K : ℕ) : ZMod 2) = 1 := by
      apply Odd.natCast_zmod_two
      rwa [← Nat.card_eq_fintype_card]
    rw [this, one_smul]
  have hfix : Representation.invariants (ρW.comp K.subtype) = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    rw [Representation.mem_invariants] at hw
    have h1 : ∀ k : K, ρ k (w : M) = w := fun k => congrArg Subtype.val (hw k)
    have h2 : N (w : M) = w := hNfix _ h1
    have h3 : N (w : M) = 0 := w.2
    rw [Submodule.mem_bot]
    exact Subtype.ext (h2.symm.trans h3)
  obtain ⟨k₀, hk₀, v, hv⟩ := hmove
  have hWpos : 0 < Module.finrank (ZMod 2) W := by
    rw [Module.finrank_pos_iff_exists_ne_zero]
    refine ⟨⟨v - ρ k₀ v, ?_⟩, ?_⟩
    · show N (v - ρ k₀ v) = 0
      rw [map_sub]
      have := Representation.norm_self_apply ρK ⟨k₀, hk₀⟩ v
      exact sub_eq_zero.mpr this.symm
    · intro h
      apply hv
      have h' : v - ρ k₀ v = 0 := congrArg Subtype.val h
      exact (sub_eq_zero.mp h').symm
  have hmain := CFSG.ABGLocalTools.finrank_invariants_mul_card_of_fixedPointFree ρW
    (K := K) (B := B) ⟨⟨fun a b => Subtype.ext (hK a a.2 b b.2)⟩⟩
    (by rw [Subgroup.normalizer_eq_top]; exact le_top) hfpf
    (by rw [ZMod.ringChar_zmod_n]; exact hodd.not_two_dvd_nat) hfix
  have hle : Nat.card B ≤ Module.finrank (ZMod 2) W :=
    Nat.le_of_dvd hWpos (hmain ▸ Dvd.intro_left _ rfl)
  calc 2 ^ Nat.card B ≤ 2 ^ Module.finrank (ZMod 2) W := Nat.pow_le_pow_right (by norm_num) hle
    _ = Nat.card W := by rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    _ ≤ Nat.card M := Nat.card_le_card_of_injective _ Subtype.val_injective

theorem frobRank_module {G M : Type} [Group G] [Finite G] [AddCommGroup M] [Module (ZMod 2) M]
    [Finite M] (ρ : Representation (ZMod 2) G M) (A B : Subgroup G)
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hodd : Odd (Nat.card A))
    (hB : B ≤ normalizer (A : Set G))
    (hfpf : ∀ b ∈ B, b ≠ 1 → ∀ a ∈ A, b * a = a * b → a = 1)
    (hmove : ∃ a ∈ A, ∃ v : M, ρ a v ≠ v) : 2 ^ Nat.card B ≤ Nat.card M := by
  have hAH : A ≤ normalizer (A : Set G) := Subgroup.le_normalizer
  have : (A.subgroupOf (normalizer (A : Set G))).Normal := Subgroup.normal_in_normalizer
  have hKcard : Nat.card (A.subgroupOf (normalizer (A : Set G))) = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv
  have hBcard : Nat.card (B.subgroupOf (normalizer (A : Set G))) = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB).toEquiv
  rw [← hBcard]
  refine frobRank_aux (ρ.comp (normalizer (A : Set G)).subtype)
    (A.subgroupOf (normalizer (A : Set G))) (B.subgroupOf (normalizer (A : Set G))) ?_ ?_ ?_ ?_
  · intro a ha b hb
    exact Subtype.ext (hA a (mem_subgroupOf.mp ha) b (mem_subgroupOf.mp hb))
  · rwa [hKcard]
  · intro b hb hb1 k hk hbk
    refine Subtype.ext ?_
    have hb1' : (b : G) ≠ 1 := fun h => hb1 (Subtype.ext h)
    simpa using hfpf b (mem_subgroupOf.mp hb) hb1' k (mem_subgroupOf.mp hk)
      (congrArg Subtype.val hbk)
  · obtain ⟨a, ha, v, hv⟩ := hmove
    exact ⟨⟨a, hAH ha⟩, mem_subgroupOf.mpr ha, v, hv⟩

theorem frobRank : FrobRankStmt := by
  intro G V _ _ _ _ hV ρ A B hA hodd hB hfpf hmove
  have hcomm : ∀ a b : V, a * b = b * a := by
    intro a b
    have h1 : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hV a)
    have h2 : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hV b)
    have h3 : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right (hV (a * b))
    calc a * b = (a * b)⁻¹ := h3.symm
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = b * a := by rw [h1, h2]
  let _ : CommGroup V := { ‹Group V› with mul_comm := hcomm }
  let _ : Module (ZMod 2) (Additive V) := AddCommGroup.zmodModule (n := 2) (fun x => by
    rw [two_nsmul]
    show Additive.ofMul (Additive.toMul x * Additive.toMul x) = Additive.ofMul 1
    rw [hV])
  let ρ' : Representation (ZMod 2) G (Additive V) :=
    { toFun := fun g =>
        (MonoidHom.toAdditive (ρ g).toMonoidHom : Additive V →+ Additive V).toZModLinearMap 2
      map_one' := by
        refine LinearMap.ext fun x => ?_
        rw [map_one ρ]
        rfl
      map_mul' := fun g h => by
        refine LinearMap.ext fun x => ?_
        rw [map_mul ρ]
        rfl }
  exact frobRank_module ρ' A B hA hodd hB hfpf (by
    obtain ⟨a, ha, v, hv⟩ := hmove
    exact ⟨a, ha, Additive.ofMul v, fun h => hv (Additive.ofMul.injective h)⟩)

end CFSG.GH74.Uniqueness
