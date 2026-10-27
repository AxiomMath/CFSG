module

public import CFSG.LocalAnalysis.PreuniquenessRankFour.Helpers
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.AGLEmbedding.ChevOuter

open MonoidHom

abbrev M3 : Type := Multiplicative (ZMod 3)

variable {G : Type*} [Group G]

@[expose] def pow3Hom (x : G) (hx : x ^ 3 = 1) : M3 →* G where
  toFun t := x ^ (Multiplicative.toAdd t).val
  map_one' := by simp
  map_mul' a b := by
    simp only [toAdd_mul, ZMod.val_add]
    rw [← pow_add]
    exact (pow_eq_pow_mod _ hx).symm

theorem pow3Hom_apply (x : G) (hx : x ^ 3 = 1) (t : M3) :
    pow3Hom x hx t = x ^ (Multiplicative.toAdd t).val := rfl

theorem m3_pow_three (t : M3) : t ^ 3 = 1 := by
  revert t
  decide

theorem m3_val_eq_zero (t : M3) (h : (Multiplicative.toAdd t).val = 0) : t = 1 :=
  (ZMod.val_eq_zero _).1 h

theorem val_one3 : (1 : ZMod 3).val = 1 := rfl

theorem card_m3 : Nat.card M3 = 3 := by
  rw [Nat.card_eq_fintype_card]
  decide

@[expose] def pair3Hom (x y : G) (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (hxy : Commute x y) :
    M3 × M3 →* G :=
  (pow3Hom x hx).noncommCoprod (pow3Hom y hy) fun a b => by
    rw [pow3Hom_apply, pow3Hom_apply]
    exact hxy.pow_pow _ _

theorem pair3Hom_apply (x y : G) (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (hxy : Commute x y)
    (t : M3 × M3) : pair3Hom x y hx hy hxy t =
      x ^ (Multiplicative.toAdd t.1).val * y ^ (Multiplicative.toAdd t.2).val := by
  simp [pair3Hom, MonoidHom.noncommCoprod_apply, pow3Hom_apply]

theorem pair3Hom_injective (x y : G) (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (hxy : Commute x y)
    (hind : ∀ a b : ℕ, a < 3 → b < 3 → x ^ a * y ^ b = 1 → a = 0 ∧ b = 0) :
    Function.Injective (pair3Hom x y hx hy hxy) := by
  rw [injective_iff_map_eq_one]
  intro t ht
  rw [pair3Hom_apply] at ht
  obtain ⟨h1, h2⟩ := hind _ _ (ZMod.val_lt _) (ZMod.val_lt _) ht
  exact Prod.ext (m3_val_eq_zero _ h1) (m3_val_eq_zero _ h2)

@[expose] def triple3Hom (x y z : G) (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (hz : z ^ 3 = 1)
    (hxy : Commute x y) (hxz : Commute x z) (hyz : Commute y z) : (M3 × M3) × M3 →* G :=
  (pair3Hom x y hx hy hxy).noncommCoprod (pow3Hom z hz) fun a b => by
    rw [pair3Hom_apply, pow3Hom_apply]
    exact (hxz.pow_pow _ _).mul_left (hyz.pow_pow _ _)

theorem triple3Hom_apply (x y z : G) (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (hz : z ^ 3 = 1)
    (hxy : Commute x y) (hxz : Commute x z) (hyz : Commute y z) (t : (M3 × M3) × M3) :
    triple3Hom x y z hx hy hz hxy hxz hyz t = x ^ (Multiplicative.toAdd t.1.1).val *
      y ^ (Multiplicative.toAdd t.1.2).val * z ^ (Multiplicative.toAdd t.2).val := by
  simp [triple3Hom, MonoidHom.noncommCoprod_apply, pow3Hom_apply, pair3Hom_apply]

theorem triple3Hom_injective (x y z : G) (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (hz : z ^ 3 = 1)
    (hxy : Commute x y) (hxz : Commute x z) (hyz : Commute y z)
    (hind : ∀ a b c : ℕ, a < 3 → b < 3 → c < 3 → x ^ a * y ^ b * z ^ c = 1 →
      a = 0 ∧ b = 0 ∧ c = 0) :
    Function.Injective (triple3Hom x y z hx hy hz hxy hxz hyz) := by
  rw [injective_iff_map_eq_one]
  intro t ht
  rw [triple3Hom_apply] at ht
  obtain ⟨h1, h2, h3⟩ := hind _ _ _ (ZMod.val_lt _) (ZMod.val_lt _) (ZMod.val_lt _) ht
  exact Prod.ext (Prod.ext (m3_val_eq_zero _ h1) (m3_val_eq_zero _ h2)) (m3_val_eq_zero _ h3)

theorem closure_pair [Finite G] (x y : G) (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (hxy : Commute x y)
    (hind : ∀ a b : ℕ, a < 3 → b < 3 → x ^ a * y ^ b = 1 → a = 0 ∧ b = 0) :
    IsMulCommutative (Subgroup.closure {x, y}) ∧ (∀ g ∈ Subgroup.closure {x, y}, g ^ 3 = 1) ∧
      Nat.card (Subgroup.closure {x, y}) = 3 ^ 2 := by
  set ψ := pair3Hom x y hx hy hxy with hψ
  have hrange : ψ.range = Subgroup.closure {x, y} := by
    apply le_antisymm
    · rintro _ ⟨t, rfl⟩
      rw [hψ, pair3Hom_apply]
      exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
        (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
    · rw [Subgroup.closure_le]
      intro g hg
      rcases hg with rfl | rfl
      · exact ⟨(Multiplicative.ofAdd 1, 1), by simp [hψ, pair3Hom_apply, val_one3]⟩
      · exact ⟨(1, Multiplicative.ofAdd 1), by simp [hψ, pair3Hom_apply, val_one3]⟩
  rw [← hrange]
  refine ⟨?_, ?_, ?_⟩
  · rw [MonoidHom.range_eq_map]
    infer_instance
  · rintro _ ⟨t, rfl⟩
    rw [← map_pow]
    have : t ^ 3 = 1 := Prod.ext (m3_pow_three _) (m3_pow_three _)
    rw [this, map_one]
  · rw [← Nat.card_congr (MonoidHom.ofInjective (pair3Hom_injective x y hx hy hxy hind)).toEquiv,
      Nat.card_prod, card_m3]
    norm_num

theorem closure_triple [Finite G] (x y z : G) (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (hz : z ^ 3 = 1)
    (hxy : Commute x y) (hxz : Commute x z) (hyz : Commute y z)
    (hind : ∀ a b c : ℕ, a < 3 → b < 3 → c < 3 → x ^ a * y ^ b * z ^ c = 1 →
      a = 0 ∧ b = 0 ∧ c = 0) :
    IsMulCommutative (Subgroup.closure {x, y, z}) ∧
      (∀ g ∈ Subgroup.closure {x, y, z}, g ^ 3 = 1) ∧
      Nat.card (Subgroup.closure {x, y, z}) = 3 ^ 3 := by
  set ψ := triple3Hom x y z hx hy hz hxy hxz hyz with hψ
  have hrange : ψ.range = Subgroup.closure {x, y, z} := by
    apply le_antisymm
    · rintro _ ⟨t, rfl⟩
      rw [hψ, triple3Hom_apply]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _
        (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
        (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _))
        (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
    · rw [Subgroup.closure_le]
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl
      · exact ⟨((Multiplicative.ofAdd 1, 1), 1), by simp [hψ, triple3Hom_apply, val_one3]⟩
      · exact ⟨((1, Multiplicative.ofAdd 1), 1), by simp [hψ, triple3Hom_apply, val_one3]⟩
      · exact ⟨((1, 1), Multiplicative.ofAdd 1), by simp [hψ, triple3Hom_apply, val_one3]⟩
  rw [← hrange]
  refine ⟨?_, ?_, ?_⟩
  · rw [MonoidHom.range_eq_map]
    infer_instance
  · rintro _ ⟨t, rfl⟩
    rw [← map_pow]
    have : t ^ 3 = 1 :=
      Prod.ext (Prod.ext (m3_pow_three _) (m3_pow_three _)) (m3_pow_three _)
    rw [this, map_one]
  · rw [← Nat.card_congr
      (MonoidHom.ofInjective (triple3Hom_injective x y z hx hy hz hxy hxz hyz hind)).toEquiv,
      Nat.card_prod, Nat.card_prod, card_m3]
    norm_num

theorem conj_mem_of_gens {S : Set G} {n : G} (h : ∀ s ∈ S, n * s * n⁻¹ ∈ Subgroup.closure S) :
    ∀ f ∈ Subgroup.closure S, n * f * n⁻¹ ∈ Subgroup.closure S := by
  intro f hf
  induction hf using Subgroup.closure_induction with
  | mem s hs => exact h s hs
  | one => simp
  | mul a b _ _ ha hb =>
    have : n * (a * b) * n⁻¹ = (n * a * n⁻¹) * (n * b * n⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ ha hb
  | inv a _ ha =>
    have : n * a⁻¹ * n⁻¹ = (n * a * n⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ ha

theorem mem_normalizer_of_conj_mem [Finite G] {F : Subgroup G} {n : G}
    (h : ∀ f ∈ F, n * f * n⁻¹ ∈ F) : n ∈ Subgroup.normalizer (F : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro f
  refine ⟨h f, fun hf => ?_⟩
  let c : F → F := fun a => ⟨n * a * n⁻¹, h a a.2⟩
  have hinj : Function.Injective c := by
    intro a b hab
    have := congrArg Subtype.val hab
    simp only [c] at this
    apply Subtype.ext
    simpa using this
  obtain ⟨a, ha⟩ := (Finite.injective_iff_surjective.1 hinj) ⟨n * f * n⁻¹, hf⟩
  have := congrArg Subtype.val ha
  simp only [c] at this
  have h2 : (a : G) = f := by simpa using this
  rw [← h2]
  exact a.2

theorem normalizer_le_weakCore_of_E27 [Finite G] {R E F : Subgroup G} (hER : E ≤ R)
    (hEc : IsMulCommutative E) (hE3 : ∀ g ∈ E, g ^ 3 = 1) (hEcard : Nat.card E = 3 ^ 3)
    (hFE : F ≤ E) (hFcard : Nat.card F = 3 ^ 2) :
    Subgroup.normalizer (F : Set G) ≤ CFSG.Open.GLBWeakCore 3 R := by
  have hp : 1 < 3 := by norm_num
  have hErank : 3 ≤ CFSG.Open.pRank 3 E := CFSG.SectionRank.le_pRank hp le_rfl ⟨hEc, hE3⟩ hEcard
  have hFc : IsMulCommutative F := ⟨⟨fun a b => by
    have key : (a : G) * b = b * a := by
      have := hEc.is_comm.comm ⟨a, hFE a.2⟩ ⟨b, hFE b.2⟩
      exact congrArg Subtype.val this
    exact Subtype.ext key⟩⟩
  have hFrank : 2 ≤ CFSG.Open.pRank 3 F :=
    CFSG.SectionRank.le_pRank hp le_rfl ⟨hFc, fun g hg => hE3 g (hFE hg)⟩ hFcard
  exact CFSG.PreuniquenessRankFour.Helpers.normalizer_le_weakCore_of_commutative_overgroup 3
    Nat.prime_three hER hFE hEc hFrank hErank

end CFSG.AGLEmbedding.ChevOuter
