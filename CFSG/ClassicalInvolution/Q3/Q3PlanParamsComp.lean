module

public import CFSG.ClassicalInvolution.Q3.Q3PlanParamsLift

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open
open scoped commutatorElement

theorem five_le_pow_of_odd_prime_of_ne_three {r e : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (he : 1 ≤ e)
    (hne : r ≠ 3 ∨ e ≠ 1) : 5 ≤ r ^ e := by
  rcases hne with h3 | h1
  · have h5 : 5 ≤ r := by
      by_contra hlt
      have : r < 5 := by omega
      interval_cases r <;> first | exact absurd hr (by decide) | exact h3 rfl | exact hr2 rfl
    exact h5.trans (Nat.le_self_pow (by omega) r)
  · have h3 : 3 ≤ r := by
      have := hr.two_le
      omega
    calc 5 ≤ 3 ^ 2 := by norm_num
      _ ≤ r ^ 2 := Nat.pow_le_pow_left h3 2
      _ ≤ r ^ e := Nat.pow_le_pow_right (by omega) (by omega)

variable {G : Type*} [Group G]

theorem le_normalizer_of_forall_conj_mem {C A : Subgroup G}
    (h : ∀ c ∈ C, ∀ x ∈ A, c * x * c⁻¹ ∈ A) : C ≤ Subgroup.normalizer (A : Set G) := by
  intro c hc
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => h c hc x hx, fun hx => ?_⟩
  have := h c⁻¹ (C.inv_mem hc) _ hx
  simpa [mul_assoc] using this

theorem le_or_commutator_eq_bot_of_normalizes {K L T : Subgroup G} (hK : CFSG.Open.IsQuasisimple K)
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) (hTL : T ≤ L)
    (hKL : K ≤ Subgroup.normalizer (L : Set G)) : K ≤ L ∨ ⁅K, T⁆ = ⊥ := by
  let D := ⁅K, T⁆
  have hDK : D ≤ K := Subgroup.le_normalizer_iff_commutator_le_left.mp hTK
  have hDL : D ≤ L := (Subgroup.commutator_mono le_rfl hTL).trans
    (Subgroup.le_normalizer_iff_commutator_le_right.mp hKL)
  let DK := D.subgroupOf K
  let : DK.Normal := Subgroup.normal_subgroupOf_of_le_normalizer
    (Subgroup.normalizer_commutator_ge_left K T)
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hK DK with
    hcentral | htop
  · right
    let : Group.IsPerfect K := ⟨hK.1⟩
    have hDC : D ≤ Subgroup.centralizer (K : Set G) := by
      intro d hd
      apply Subgroup.mem_centralizer_iff.mpr
      intro k hk
      exact congrArg Subtype.val
        (Subgroup.mem_center_iff.mp (hcentral (show (⟨d, hDK hd⟩ : K) ∈ DK from hd))
          (⟨k, hk⟩ : K))
    exact CFSG.ComponentClassification.Quasisimple.perfect_double_commutator K T
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hDC)
  · left
    have hD : D = K := by
      have hmap := congrArg (Subgroup.map K.subtype) htop
      change (D.subgroupOf K).map K.subtype = (⊤ : Subgroup K).map K.subtype at hmap
      simpa only [Subgroup.map_subgroupOf_eq_of_le hDK, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype] using hmap
    exact hD ▸ hDL

theorem le_or_commutator_eq_bot_of_isSubnormal {C A N : Subgroup G}
    (hA : CFSG.Open.IsQuasisimple A) (hAC : A ≤ C) (hAn : C ≤ Subgroup.normalizer (A : Set G))
    (hN : IsSubnormal N C) : A ≤ N ∨ ⁅A, N⁆ = ⊥ := by
  induction hN with
  | refl => exact Or.inl hAC
  | @step H M K' hHM hHn hM ih =>
    rcases ih hAC hAn with hAM | hAM
    · have hMn : M ≤ Subgroup.normalizer (H : Set G) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hHM).mp hHn
      have hMC : M ≤ K' := CFSG.ClassicalInvolution.isSubnormal_le hM
      exact le_or_commutator_eq_bot_of_normalizes hA ((hHM.trans hMC).trans hAn) le_rfl
        (hAM.trans hMn)
    · exact Or.inr (eq_bot_iff.mpr (hAM ▸ Subgroup.commutator_mono le_rfl hHM))

theorem commute_of_isSubnormal_of_isSolvable {C A N : Subgroup G}
    (hA : CFSG.Open.IsQuasisimple A) (hAC : A ≤ C) (hAn : C ≤ Subgroup.normalizer (A : Set G))
    (hN : IsSubnormal N C) (hs : Group.IsSolvable N) : ∀ n ∈ N, ∀ a ∈ A, n * a = a * n := by
  rcases le_or_commutator_eq_bot_of_isSubnormal hA hAC hAn hN with h | h
  · exfalso
    have hAs : Group.IsSolvable ↥A :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion h)
        (Subgroup.inclusion_injective h)
    exact false_of_isQuasisimple_of_isSolvable hA hAs
  · intro n hn a ha
    have hle : A ≤ Subgroup.centralizer (N : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
    exact Subgroup.mem_centralizer_iff.mp (hle ha) n hn

omit [Group G] in
theorem derivedSeries_two_eq_bot_of_commutator_mem {H : Type*} [Group H] {J B : Subgroup H}
    (hB : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (h : ∀ x ∈ J, ∀ y ∈ J, ⁅x, y⁆ ∈ B) :
    derivedSeries ↥J 2 = ⊥ := by
  have h1 : derivedSeries ↥J 1 ≤ B.subgroupOf J := by
    rw [derivedSeries_one, commutator_def, Subgroup.commutator_le]
    intro x _ y _
    exact h x x.2 y y.2
  rw [derivedSeries_succ, eq_bot_iff, Subgroup.commutator_le]
  intro u hu v hv
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
  exact Subtype.ext (hB u.1 (h1 hu) v.1 (h1 hv))

omit [Group G] in
theorem derivedSeries_two_eq_bot_of_commute {H : Type*} [Group H] {N : Subgroup H}
    (h : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a) : derivedSeries ↥N 2 = ⊥ := by
  have h1 : derivedSeries ↥N 1 = ⊥ := by
    rw [derivedSeries_one, eq_bot_iff, commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact Subtype.ext (h x x.2 y y.2)
  rw [derivedSeries_succ, h1]
  simp

section Transport

variable {H : Type*} [Group H]

theorem IsOddGenerated.map {N : Subgroup G} (f : G →* H) (hf : Function.Injective f)
    (h : IsOddGenerated N) : IsOddGenerated (N.map f) := by
  refine (Subgroup.map_mono h).trans ?_
  rw [MonoidHom.map_closure]
  refine Subgroup.closure_mono ?_
  rintro _ ⟨x, ⟨hxN, hxo⟩, rfl⟩
  exact ⟨Subgroup.mem_map_of_mem f hxN, by rwa [orderOf_injective f hf]⟩

theorem derivedSeries_eq_bot_of_map {N : Subgroup G} (f : G →* H) (hf : Function.Injective f)
    {n : ℕ} (h : derivedSeries ↥(N.map f) n = ⊥) : derivedSeries ↥N n = ⊥ := by
  have hsurj : Function.Surjective (Subgroup.equivMapOfInjective N f hf).toMonoidHom :=
    (Subgroup.equivMapOfInjective N f hf).surjective
  have hinj : Function.Injective (Subgroup.equivMapOfInjective N f hf).toMonoidHom :=
    (Subgroup.equivMapOfInjective N f hf).injective
  have h1 := map_derivedSeries_eq hsurj n
  rw [h] at h1
  apply Subgroup.map_injective hinj
  rw [h1, Subgroup.map_bot]

end Transport

section Equiv

variable {H : Type*} [Group H]

theorem commute_of_forall_map_mulEquiv (e : G ≃* H) {w : G} {N : Subgroup G}
    (hNs : IsSubnormal N (Subgroup.centralizer ({w} : Set G))) (hsolv : Group.IsSolvable N)
    (h : ∀ M : Subgroup H, IsSubnormal M (Subgroup.centralizer ({e w} : Set H)) →
      Group.IsSolvable M → ∀ x ∈ M, ∀ y ∈ M, x * y = y * x) :
    ∀ x ∈ N, ∀ y ∈ N, x * y = y * x := by
  have hC : (Subgroup.centralizer ({w} : Set G)).map e.toMonoidHom =
      Subgroup.centralizer ({e w} : Set H) := by
    ext x'
    obtain ⟨x, rfl⟩ := e.surjective x'
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply, Subgroup.mem_centralizer_iff,
      Subgroup.mem_centralizer_iff]
    simp only [Set.mem_singleton_iff, forall_eq]
    rw [← map_mul, ← map_mul, e.injective.eq_iff]
  have hMs : IsSubnormal (N.map e.toMonoidHom) (Subgroup.centralizer ({e w} : Set H)) := by
    rw [← hC]
    exact CFSG.ClassicalInvolution.isSubnormal_map_mulEquiv e hNs
  have hMsolv : Group.IsSolvable ↥(N.map e.toMonoidHom) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.equivMapOfInjective N e.toMonoidHom e.injective).symm.toMonoidHom)
      (Subgroup.equivMapOfInjective N e.toMonoidHom e.injective).symm.injective
  intro x hx y hy
  apply e.injective
  rw [map_mul, map_mul]
  exact h _ hMs hMsolv _ (Subgroup.mem_map_of_mem _ hx) _ (Subgroup.mem_map_of_mem _ hy)

end Equiv

end CFSG.ClassicalInvolution.Q3
