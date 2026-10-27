module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG.GroupTheory

open QuaternionGroup

theorem eq_eight_of_dvd_eight_of_two_le_of_modEq {r c : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r)
    (hc : c ∣ 8) (hc2 : 2 ≤ c) (hcong : 8 ≡ c [MOD r]) : c = 8 := by
  have hc8 : c ∣ 2 ^ 3 := by simpa using hc
  obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hc8
  rw [hk] at hc2 hcong ⊢
  interval_cases k
  · norm_num at hc2
  · have hdiv : r ∣ 8 - 2 ^ 1 :=
      (Nat.modEq_iff_dvd' (by norm_num : 2 ^ 1 ≤ 8)).mp hcong.symm
    norm_num at hdiv
    have hrle : r ≤ 6 := Nat.le_of_dvd (by norm_num) hdiv
    interval_cases r <;> norm_num at *
  · have hdiv : r ∣ 8 - 2 ^ 2 :=
      (Nat.modEq_iff_dvd' (by norm_num : 2 ^ 2 ≤ 8)).mp hcong.symm
    norm_num at hdiv
    have hrle : r ≤ 4 := Nat.le_of_dvd (by norm_num) hdiv
    omega
  · norm_num

theorem isPGroup_zpowers_of_pow_eq_one_of_prime {G : Type*} [Group G] {r : ℕ}
    (hr : r.Prime) {σ : G} (hσ : σ ^ r = 1) : IsPGroup r (Subgroup.zpowers σ) := by
  rcases (Nat.dvd_prime hr).mp (orderOf_dvd_of_pow_eq_one hσ) with h | h
  · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])

theorem mem_fixedPoints_zpowers_of_smul_eq_self {G α : Type*} [Group G] [Group α]
    [MulDistribMulAction G α] {σ : G} {a : α} (h : σ • a = a) :
    a ∈ FixedPoints.subgroup (Subgroup.zpowers σ) α := by
  rw [FixedPoints.mem_subgroup]
  intro m
  exact smul_eq_self_of_mem_zpowers m.2 h

theorem exists_mulAut_comp_eq_of_ker_le {H K : Type*} [Group H] [Group K] [Finite K]
    (φ : H →* K) (hφ : Function.Surjective φ) (c : MulAut H)
    (hc : φ.ker ≤ (φ.comp c.toMonoidHom).ker) :
    ∃ β : MulAut K, ∀ h : H, β (φ h) = φ (c h) := by
  let g : H →* K := φ.comp c.toMonoidHom
  have hgker : φ.ker ≤ g.ker := hc
  let ψ : K → H := Function.surjInv hφ
  have hψ : Function.RightInverse ψ φ := Function.rightInverse_surjInv hφ
  let β : K →* K := MonoidHom.liftOfRightInverse φ ψ hψ ⟨g, hgker⟩
  have hβcomp : β.comp φ = g := by
    simpa [β] using
      MonoidHom.liftOfRightInverse_comp (f := φ) (f_inv := ψ) hψ ⟨g, hgker⟩
  have hgsurj : Function.Surjective g := by
    simpa [g] using hφ.comp c.surjective
  have hβsurj : Function.Surjective β := by
    intro q
    obtain ⟨u, hu⟩ := hgsurj q
    refine ⟨φ u, ?_⟩
    have h := congrArg (fun f : H →* K => f u) hβcomp
    exact h.trans hu
  have hβinj : Function.Injective β := Finite.injective_iff_surjective.mpr hβsurj
  refine ⟨MulEquiv.ofBijective β ⟨hβinj, hβsurj⟩, ?_⟩
  intro u
  exact (congrArg (fun f : H →* K => f u) hβcomp).trans rfl

theorem mulAut_pow_comp_apply {H K : Type*} [Group H] [Group K]
    (φ : H →* K) (β : MulAut K) (c : MulAut H)
    (h : ∀ x : H, β (φ x) = φ (c x)) (n : ℕ) (x : H) :
    (β ^ n) (φ x) = φ ((c ^ n) x) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, MulAut.mul_apply, h, ih (c x), pow_succ, MulAut.mul_apply]

theorem quaternion_eq_a_two_or_sq_eq_a_two {g : QuaternionGroup 2} (hg : g ≠ 1) :
    g = a 2 ∨ g ^ 2 = a 2 := by
  revert hg
  decide +revert

theorem quaternion_a_two_mem_of_ne_bot {H : Subgroup (QuaternionGroup 2)} (hH : H ≠ ⊥) :
    a 2 ∈ H := by
  obtain ⟨g, hg1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hH
  have hg1' : (g : QuaternionGroup 2) ≠ 1 := by
    intro h
    exact hg1 (Subtype.ext h)
  rcases quaternion_eq_a_two_or_sq_eq_a_two hg1' with h | h
  · rw [← h]
    exact g.2
  · rw [← h]
    exact H.pow_mem g.2 2

theorem mulAut_quaternion_apply_a_two (σ : MulAut (QuaternionGroup 2)) : σ (a 2) = a 2 := by
  have ha2 : (a 2 : QuaternionGroup 2) ≠ 1 := by decide
  have hsq : (a 2 : QuaternionGroup 2) ^ 2 = 1 := by decide
  have hne : σ (a 2) ≠ 1 := by
    intro h
    exact ha2 (σ.injective (by rw [h, map_one]))
  have hsq' : (σ (a 2)) ^ 2 = 1 := by
    rw [← map_pow, hsq, map_one]
  rcases quaternion_eq_a_two_or_sq_eq_a_two hne with h | h
  · exact h
  · rw [h] at hsq'
    exact absurd hsq' ha2

theorem mulAut_quaternion_eq_one_of_pow_eq_one {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r)
    {σ : MulAut (QuaternionGroup 2)} (hσ : σ ^ r = 1) : σ = 1 := by
  let H : Subgroup (MulAut (QuaternionGroup 2)) := Subgroup.zpowers σ
  let F : Subgroup (QuaternionGroup 2) := FixedPoints.subgroup H (QuaternionGroup 2)
  have hHpg : IsPGroup r H := isPGroup_zpowers_of_pow_eq_one_of_prime hr hσ
  have hQcard : Nat.card (QuaternionGroup 2) = 8 := by
    rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
  have ha2ne : (a 2 : QuaternionGroup 2) ≠ 1 := by decide
  have ha2F : (a 2 : QuaternionGroup 2) ∈ F :=
    mem_fixedPoints_zpowers_of_smul_eq_self
      (G := MulAut (QuaternionGroup 2)) (α := QuaternionGroup 2)
      (by simpa [MulAut.smul_def] using mulAut_quaternion_apply_a_two σ)
  have hFcard : Nat.card F = Nat.card (MulAction.fixedPoints H (QuaternionGroup 2)) := rfl
  haveI : Fact r.Prime := ⟨hr⟩
  have hcong : 8 ≡ Nat.card F [MOD r] := by
    have h := hHpg.card_modEq_card_fixedPoints (QuaternionGroup 2)
    rw [hQcard, ← hFcard] at h
    exact h
  have hdvd : Nat.card F ∣ 8 := by
    rw [← hQcard]
    exact Subgroup.card_subgroup_dvd_card F
  haveI : Nontrivial F := by
    refine ⟨⟨⟨a 2, ha2F⟩, ⟨1, F.one_mem⟩, ?_⟩⟩
    intro h
    exact ha2ne (congrArg Subtype.val h)
  have hc2 : 2 ≤ Nat.card F := by
    have := Finite.one_lt_card_iff_nontrivial (α := F).mpr inferInstance
    omega
  have hc8 : Nat.card F = 8 :=
    eq_eight_of_dvd_eight_of_two_le_of_modEq hr hr5 hdvd hc2 hcong
  have htop : F = ⊤ := Subgroup.eq_top_of_card_eq F (by rw [hc8, hQcard])
  apply MulEquiv.ext
  intro g
  have hg : g ∈ F := by rw [htop]; exact Subgroup.mem_top g
  have h := (FixedPoints.mem_subgroup (M := H) (α := QuaternionGroup 2) g).mp hg
    ⟨σ, Subgroup.mem_zpowers σ⟩
  simpa [MulAut.smul_def] using h

theorem quaternion_map_normalizerMonoidHom_eq {Γ : Type*} [Group Γ] {T : Subgroup Γ}
    (φ : ↥T →* QuaternionGroup 2) (hφ : Function.Surjective φ)
    (x : Subgroup.normalizer (T : Set Γ))
    (hker : ∀ t : ↥T, φ t = 1 → φ (Subgroup.normalizerMonoidHom T x t) = 1)
    {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r) (hxr : x ^ r = 1) (t : ↥T) :
    φ (Subgroup.normalizerMonoidHom T x t) = φ t := by
  let c : MulAut ↥T := Subgroup.normalizerMonoidHom T x
  have hc : φ.ker ≤ (φ.comp c.toMonoidHom).ker := fun u hu => hker u hu
  obtain ⟨β, hβ⟩ := exists_mulAut_comp_eq_of_ker_le φ hφ c hc
  have hcr : c ^ r = 1 := by
    change (Subgroup.normalizerMonoidHom T x) ^ r = 1
    rw [← map_pow (Subgroup.normalizerMonoidHom T) x r, hxr, map_one]
  have hβr : β ^ r = 1 := by
    apply MulEquiv.ext
    intro q
    obtain ⟨u, rfl⟩ := hφ q
    rw [mulAut_pow_comp_apply φ β c hβ r u, hcr]
    simp
  have hβ1 : β = 1 := mulAut_quaternion_eq_one_of_pow_eq_one hr hr5 hβr
  have h := hβ t
  rw [hβ1] at h
  simpa [c] using h.symm

end CFSG.GroupTheory
