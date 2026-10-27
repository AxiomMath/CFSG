module

public import CFSG.CGT.T75P.SylowSplit
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LieType.SeitzGeneration.Defs

public section

namespace CFSG.AGLEmbedding.SeitzEqTwo

open CFSG.Open CFSG.LieType.SeitzGeneration
open scoped Pointwise

variable {C : Type*} [Group C]

theorem isElemAbelian_sup_of_commute {p : ℕ} {A B : Subgroup C} (hA : IsElemAbelian p A)
    (hB : IsElemAbelian p B) (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    IsElemAbelian p (A ⊔ B) := CFSG.Open.IsElemAbelian.sup_of_commute hA hB hcomm

variable {p : ℕ} {τ : MulAut C} {A : Subgroup C}

theorem commute_conj_of_fixed {a : C} (ha : τ a = a) :
    τ * MulAut.conj a = MulAut.conj a * τ := by
  ext x
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, ha]

theorem isElemAbelian_cube (hτp : τ ^ p = 1) (hA : IsElemAbelian p A)
    (hfix : ∀ a ∈ A, τ a = a) :
    IsElemAbelian p (Subgroup.zpowers τ ⊔ A.map (MulAut.conj : C →* MulAut C)) := by
  have hZ : IsElemAbelian p (Subgroup.zpowers τ) := by
    refine ⟨IsMulCommutative.of_comm fun x y => ?_, fun x hx => ?_⟩
    · obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 x.2
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 y.2
      apply Subtype.ext
      change (x : MulAut C) * y = y * x
      rw [← hm, ← hn, ← zpow_add, ← zpow_add, add_comm]
    · obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hτp, one_zpow]
  refine isElemAbelian_sup_of_commute hZ
    (CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hA _) ?_
  rintro x hx _ ⟨a, ha, rfl⟩
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  exact (Commute.zpow_left (commute_conj_of_fixed (hfix a ha) : Commute τ _) m).eq

theorem card_cube (hp : p.Prime) (hinj : Function.Injective (MulAut.conj : C →* MulAut C))
    (hτp : τ ^ p = 1) (hτ : τ ∉ (MulAut.conj : C →* MulAut C).range) (hAc : Nat.card A = p ^ 2)
    (hfix : ∀ a ∈ A, τ a = a) :
    Nat.card ↥(Subgroup.zpowers τ ⊔ A.map (MulAut.conj : C →* MulAut C)) = p ^ 3 := by
  have : Fact p.Prime := ⟨hp⟩
  have hτ1 : τ ≠ 1 := fun h => hτ ⟨1, by rw [h, map_one]⟩
  have hord : orderOf τ = p := orderOf_eq_prime hτp hτ1
  have hinf : Subgroup.zpowers τ ⊓ A.map (MulAut.conj : C →* MulAut C) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxz, hxA⟩
    rw [Subgroup.mem_bot]
    by_contra hx1
    have hxp : x ^ p = 1 := by
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hxz
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hτp, one_zpow]
    have hxo : orderOf x = p := orderOf_eq_prime hxp hx1
    have hfin : Finite (Subgroup.zpowers τ) :=
      Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers, hord]; exact hp.ne_zero)
    have heq : Subgroup.zpowers x = Subgroup.zpowers τ :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hxz)
        (by rw [Nat.card_zpowers, Nat.card_zpowers, hxo, hord])
    obtain ⟨a, -, ha⟩ := hxA
    have hxr : x ∈ (MulAut.conj : C →* MulAut C).range := ⟨a, ha⟩
    have hτx : τ ∈ Subgroup.zpowers x := by
      rw [heq]
      exact Subgroup.mem_zpowers τ
    exact hτ (Subgroup.zpowers_le.2 hxr hτx)
  rw [CFSG.CGT.T75P.card_sup_of_commute ?_ hinf, Nat.card_zpowers, hord,
    Subgroup.card_map_of_injective hinj, hAc]
  · ring
  · rintro x hx _ ⟨a, ha, rfl⟩
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    exact (Commute.zpow_left (commute_conj_of_fixed (hfix a ha) : Commute τ _) m).eq

theorem card_le_of_rankLE2 {G : Type*} [Group G] {H F : Subgroup G} (h : RankLE2 p H)
    (hF : IsElemAbelian p F) (hle : F ≤ H) : Nat.card F ≤ p ^ 2 := by
  have := hF.1
  have hF' : IsElemAbelian p (F.subgroupOf H) := by
    refine ⟨IsMulCommutative.of_comm fun x y => ?_, fun x hx => ?_⟩
    · apply Subtype.ext
      apply Subtype.ext
      change ((x : H) : G) * ((y : H) : G) = ((y : H) : G) * ((x : H) : G)
      exact setLike_mul_comm (Subgroup.mem_subgroupOf.1 x.2) (Subgroup.mem_subgroupOf.1 y.2)
    · apply Subtype.ext
      simpa using hF.2 _ (Subgroup.mem_subgroupOf.1 hx)
  have h1 := h _ hF'
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] at h1

theorem not_rankLE2_sup_of_conj (hp : p.Prime)
    (hinj : Function.Injective (MulAut.conj : C →* MulAut C)) (hτp : τ ^ p = 1)
    (hτ : τ ∉ (MulAut.conj : C →* MulAut C).range) (hA : IsElemAbelian p A)
    (hAc : Nat.card A = p ^ 2) (hfix : ∀ a ∈ A, τ a = a) {E : Subgroup (MulAut C)}
    {α : MulAut C} (hαE : α ∈ E) (ψ : MulAut C) (r : ℕ) (hψ : ψ * α ^ r * ψ⁻¹ = τ) :
    ¬ RankLE2 p ↥((MulAut.conj : C →* MulAut C).range ⊔ E) := by
  intro h
  set F := Subgroup.zpowers τ ⊔ A.map (MulAut.conj : C →* MulAut C) with hFdef
  set F' := F.map (MulAut.conj ψ⁻¹).toMonoidHom with hF'def
  have hF'e : IsElemAbelian p F' :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p (isElemAbelian_cube hτp hA hfix) _
  have hF'c : Nat.card F' = p ^ 3 := by
    rw [hF'def, Subgroup.card_map_of_injective (MulAut.conj ψ⁻¹).injective,
      card_cube hp hinj hτp hτ hAc hfix]
  have hle : F' ≤ (MulAut.conj : C →* MulAut C).range ⊔ E := by
    rw [hF'def, Subgroup.map_le_iff_le_comap]
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le, Subgroup.mem_comap]
      change ψ⁻¹ * τ * ψ⁻¹⁻¹ ∈ (MulAut.conj : C →* MulAut C).range ⊔ E
      have e : ψ⁻¹ * τ * ψ⁻¹⁻¹ = α ^ r := by
        rw [← hψ, inv_inv]
        group
      rw [e]
      exact Subgroup.mem_sup_right (E.pow_mem hαE r)
    · rintro _ ⟨a, -, rfl⟩
      rw [Subgroup.mem_comap]
      change ψ⁻¹ * MulAut.conj a * ψ⁻¹⁻¹ ∈ (MulAut.conj : C →* MulAut C).range ⊔ E
      refine Subgroup.mem_sup_left ⟨ψ⁻¹ a, ?_⟩
      rw [inv_inv]
      ext x
      simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.inv_apply_self]
  have h1 := card_le_of_rankLE2 h hF'e hle
  rw [hF'c] at h1
  have h3 : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  omega

end CFSG.AGLEmbedding.SeitzEqTwo
