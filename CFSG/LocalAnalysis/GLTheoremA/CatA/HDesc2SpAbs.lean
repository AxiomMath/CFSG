module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDesc2Lin
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LieType.BorelTits.FormFlag

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HDesc

open CFSG.LieType.BorelTits

section AbsSp

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]

theorem two_eq_zero_K : (2 : K) = 0 := by
  have := CharP.cast_eq_zero K 2
  simpa using this

include K in
theorem add_self_eq_zero_V (v : V) : v + v = 0 := by
  rw [← two_smul K v, two_eq_zero_K, zero_smul]

variable {E : Type} [Group E]

theorem sq_eq_one_of_trivial_on_lagrangian (F : ReflForm K V) (ρ : E →* Module.End K V)
    (hρ : IsIsometric F ρ) (hinj : Function.Injective ρ) {W : Submodule K V}
    (hW : F.perp W = W) (y : E) (hy : ∀ w ∈ W, ρ y w = w) : y * y = 1 := by
  have hmem : ∀ v, ρ y v - v ∈ W := by
    intro v
    rw [← hW, ReflForm.mem_perp]
    intro w hw
    rw [ReflForm.β_sub_right]
    have h1 := hρ y w v
    rw [hy w hw] at h1
    rw [h1, sub_self]
  have hsq : ρ (y * y) = 1 := by
    refine LinearMap.ext fun v => ?_
    have h := hy _ (hmem v)
    rw [map_sub] at h
    rw [map_mul, Module.End.mul_apply, Module.End.one_apply]
    have h2 := add_self_eq_zero_V (K := K) (ρ y v)
    have h3 := add_self_eq_zero_V (K := K) v
    calc ρ y (ρ y v) = (ρ y v - v) + ρ y v := by rw [← h]; abel
      _ = (ρ y v + ρ y v) - v := by abel
      _ = -v := by rw [h2]; simp
      _ = v := by rw [neg_eq_iff_add_eq_zero]; exact h3
  exact hinj (hsq.trans (map_one ρ).symm)

@[expose] def restrictHom (ρ : E →* Module.End K V) (X : Submodule K V) (hX : ∀ y : E, ∀ x ∈ X, ρ y x ∈ X) :
    E →* Module.End K X where
  toFun y := (ρ y).restrict (hX y)
  map_one' := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    simp
  map_mul' a b := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    simp

theorem restrictHom_apply (ρ : E →* Module.End K V) (X : Submodule K V)
    (hX : ∀ y : E, ∀ x ∈ X, ρ y x ∈ X) (y : E) (x : X) :
    ((restrictHom ρ X hX y x : X) : V) = ρ y x := rfl

theorem caseLagrangian (hP3 : ∀ d : K, d ^ 3 = 1 → d = 1) [FiniteDimensional K V]
    (hV : Module.finrank K V = 4) (F : ReflForm K V) (hE3 : ∀ y : E, y ^ 3 = 1)
    (hcomm : ∀ a b : E, a * b = b * a) (ρ : E →* Module.End K V) (hρ : IsIsometric F ρ)
    (hinj : Function.Injective ρ) {W : Submodule K V} (hW2 : Module.finrank K W = 2)
    (hWiso : F.IsTotallyIsotropic W) (hWst : ∀ y : E, ∀ w ∈ W, ρ y w ∈ W) :
    Nat.card E ≤ 3 := by
  have hperp := F.finrank_perp W
  have hWeq : F.perp W = W :=
    (Submodule.eq_of_le_of_finrank_eq hWiso (by omega)).symm
  refine card_le_three_of_faithful_plane hP3 hW2 hE3 hcomm (restrictHom ρ W hWst) ?_
  rw [injective_iff_map_eq_one]
  intro y hy
  have hy' : ∀ w ∈ W, ρ y w = w := by
    intro w hw
    have := congrArg (fun f : Module.End K W => (f ⟨w, hw⟩ : V)) hy
    simpa [restrictHom_apply] using this
  have hsq := sq_eq_one_of_trivial_on_lagrangian F ρ hρ hinj hWeq y hy'
  calc y = y ^ 3 * (y * y)⁻¹ := by group
    _ = 1 := by rw [hE3 y, hsq]; simp


theorem casePoint (hP3 : ∀ d : K, d ^ 3 = 1 → d = 1) [FiniteDimensional K V]
    (hV : Module.finrank K V = 4) (F : ReflForm K V) (halt : ∀ v, F.β v v = 0)
    [Finite E] (hE3 : ∀ y : E, y ^ 3 = 1) (hcomm : ∀ a b : E, a * b = b * a)
    (hcard : ∃ k : ℕ, Nat.card E = 3 ^ k) (ρ : E →* Module.End K V) (hρ : IsIsometric F ρ)
    (hinj : Function.Injective ρ) {w₀ : V} (hw₀ : w₀ ≠ 0) (hfix : ∀ y : E, ρ y w₀ = w₀) :
    Nat.card E ≤ 3 := by
  classical
  haveI := Fintype.ofFinite E
  obtain ⟨k, hk⟩ := hcard
  have h3K : (3 : K) = 1 := by
    have := two_eq_zero_K (K := K)
    linear_combination this
  have hn : ((Fintype.card E : ℕ) : K) = 1 := by
    rw [← Nat.card_eq_fintype_card, hk]
    push_cast
    rw [h3K, one_pow]
  set π : Module.End K V := ∑ y : E, ρ y with hπ
  have hπρ : ∀ z : E, π * ρ z = π := by
    intro z
    calc π * ρ z = (∑ y : E, ρ y) * ρ z := by rw [← hπ]
      _ = ∑ y : E, ρ (y * z) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun y _ => (map_mul ρ y z).symm
      _ = π := Fintype.sum_equiv (Equiv.mulRight z) _ _ (fun y => rfl)
  have hρπ : ∀ z : E, ρ z * π = π := by
    intro z
    calc ρ z * π = ρ z * ∑ y : E, ρ y := by rw [← hπ]
      _ = ∑ y : E, ρ (z * y) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun y _ => (map_mul ρ z y).symm
      _ = π := Fintype.sum_equiv (Equiv.mulLeft z) _ _ (fun y => rfl)
  have hsumconst : ∀ c : Module.End K V, (∑ _z : E, c) = c := by
    intro c
    rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul K, hn, one_smul]
  have hππ : π * π = π := by
    calc π * π = (∑ z : E, ρ z) * π := by rw [← hπ]
      _ = ∑ z : E, ρ z * π := Finset.sum_mul _ _ _
      _ = ∑ _z : E, π := by simp_rw [hρπ]
      _ = π := hsumconst π
  have hππ' : ∀ v, π (π v) = π v := fun v => by
    have := congrArg (fun f : Module.End K V => f v) hππ
    simpa [Module.End.mul_apply] using this
  have hfixπ : ∀ (u : V) (y : E), ρ y (π u) = π u := fun u y => by
    have := congrArg (fun f : Module.End K V => f u) (hρπ y)
    simpa [Module.End.mul_apply] using this
  have hπv : ∀ v : V, (∀ y : E, ρ y v = v) → π v = v := by
    intro v hv
    rw [hπ, LinearMap.sum_apply]
    simp_rw [hv]
    rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul K, hn, one_smul]
  have hdecomp : ∀ v : V, v - π v ∈ LinearMap.ker π := fun v => by
    rw [LinearMap.mem_ker, map_sub, hππ', sub_self]
  have hXst : ∀ y : E, ∀ x ∈ LinearMap.ker π, ρ y x ∈ LinearMap.ker π := by
    intro y x hx
    rw [LinearMap.mem_ker] at hx ⊢
    have := congrArg (fun f : Module.End K V => f x) (hπρ y)
    simpa [Module.End.mul_apply, hx] using this
  have horth : ∀ v ∈ LinearMap.range π, ∀ x ∈ LinearMap.ker π, F.β v x = 0 := by
    intro v hv x hx
    obtain ⟨u, rfl⟩ := hv
    have h1 : ∀ y : E, F.β (π u) (ρ y x) = F.β (π u) x := fun y => by
      have := hρ y (π u) x
      rwa [hfixπ u y] at this
    have h2 : F.β (π u) (π x) = F.β (π u) x := by
      have hsum : π x = ∑ y : E, ρ y x := by rw [hπ, LinearMap.sum_apply]
      calc F.β (π u) (π x) = F.toDual (π u) (π x) := rfl
        _ = F.toDual (π u) (∑ y : E, ρ y x) := by rw [hsum]
        _ = ∑ y : E, F.toDual (π u) (ρ y x) := map_sum _ _ _
        _ = ∑ _y : E, F.β (π u) x := Finset.sum_congr rfl fun y _ => h1 y
        _ = F.β (π u) x := by
          rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul K, hn, one_smul]
    rw [LinearMap.mem_ker] at hx
    rw [← h2, hx, F.β_zero_right]
  have hfaith : ∀ y : E, (∀ x ∈ LinearMap.ker π, ρ y x = x) → y = 1 := by
    intro y hX
    have : ρ y = 1 := by
      refine LinearMap.ext fun v => ?_
      have hv : v = π v + (v - π v) := by abel
      rw [Module.End.one_apply]
      conv_lhs => rw [hv]
      rw [map_add, hfixπ v y, hX _ (hdecomp v)]
      abel
    exact hinj (this.trans (map_one ρ).symm)
  have hw₀R : w₀ ∈ LinearMap.range π := ⟨w₀, hπv w₀ hfix⟩
  have hrk := LinearMap.finrank_range_add_finrank_ker π
  have hR1 : Module.finrank K (LinearMap.range π) ≠ 1 := by
    intro h1
    obtain ⟨v₀, hv₀, hspan⟩ := finrank_eq_one_iff'.mp h1
    have hv₀' : (v₀ : V) ≠ 0 := fun h => hv₀ (Subtype.ext h)
    obtain ⟨u, hu⟩ : ∃ u, F.β v₀ u ≠ 0 := by
      by_contra! hh
      exact hv₀' (F.nondeg _ hh)
    have hsplit : F.β v₀ u = F.β v₀ (π u) + F.β v₀ (u - π u) := by
      rw [← F.add_right]
      congr 1
      abel
    have h2 : F.β v₀ (u - π u) = 0 := horth v₀ v₀.2 _ (hdecomp u)
    obtain ⟨c, hc⟩ := hspan ⟨π u, u, rfl⟩
    have hc' : π u = c • (v₀ : V) := (congrArg Subtype.val hc).symm
    have h3 : F.β v₀ (π u) = 0 := by rw [hc', F.smul_right, halt, mul_zero]
    exact hu (by rw [hsplit, h2, h3, add_zero])
  have hX1 : Module.finrank K (LinearMap.ker π) ≠ 1 := by
    intro h1
    obtain ⟨x₀, hx₀, hspan⟩ := finrank_eq_one_iff'.mp h1
    have hx₀' : (x₀ : V) ≠ 0 := fun h => hx₀ (Subtype.ext h)
    obtain ⟨u, hu⟩ : ∃ u, F.β x₀ u ≠ 0 := by
      by_contra! hh
      exact hx₀' (F.nondeg _ hh)
    have hsplit : F.β x₀ u = F.β x₀ (π u) + F.β x₀ (u - π u) := by
      rw [← F.add_right]
      congr 1
      abel
    have h2 : F.β x₀ (π u) = 0 := F.refl _ _ (horth (π u) ⟨u, rfl⟩ x₀ x₀.2)
    obtain ⟨c, hc⟩ := hspan ⟨u - π u, hdecomp u⟩
    have hc' : u - π u = c • (x₀ : V) := (congrArg Subtype.val hc).symm
    have h3 : F.β x₀ (u - π u) = 0 := by rw [hc', F.smul_right, halt, mul_zero]
    exact hu (by rw [hsplit, h2, h3, add_zero])
  have hRpos : 1 ≤ Module.finrank K (LinearMap.range π) :=
    Submodule.one_le_finrank_iff.mpr (by
      intro hbot
      rw [hbot] at hw₀R
      exact hw₀ ((Submodule.mem_bot K).mp hw₀R))
  rcases (by omega : Module.finrank K (LinearMap.ker π) = 0 ∨
      Module.finrank K (LinearMap.ker π) = 2) with h0 | h2
  · have hbot : LinearMap.ker π = ⊥ := Submodule.finrank_eq_zero.mp h0
    have hone : ∀ y : E, y = 1 := fun y => hfaith y (fun x hx => by
      rw [hbot, Submodule.mem_bot] at hx
      rw [hx, map_zero])
    have : Subsingleton E := ⟨fun a b => by rw [hone a, hone b]⟩
    have := Nat.card_of_subsingleton (1 : E)
    omega
  · refine card_le_three_of_faithful_plane hP3 h2 hE3 hcomm (restrictHom ρ (LinearMap.ker π) hXst) ?_
    rw [injective_iff_map_eq_one]
    intro y hy
    refine hfaith y (fun x hx => ?_)
    have := congrArg (fun f : Module.End K (LinearMap.ker π) => (f ⟨x, hx⟩ : V)) hy
    simpa [restrictHom_apply] using this


theorem card_le_three_of_stable_isotropic (hP3 : ∀ d : K, d ^ 3 = 1 → d = 1)
    [FiniteDimensional K V] (hV : Module.finrank K V = 4) (F : ReflForm K V)
    (halt : ∀ v, F.β v v = 0) [Finite E] (hE3 : ∀ y : E, y ^ 3 = 1)
    (hcomm : ∀ a b : E, a * b = b * a) (hcard : ∃ k : ℕ, Nat.card E = 3 ^ k)
    (ρ : E →* Module.End K V) (hρ : IsIsometric F ρ) (hinj : Function.Injective ρ)
    {W : Submodule K V} (hW0 : W ≠ ⊥) (hWiso : F.IsTotallyIsotropic W)
    (hWst : ∀ y : E, ∀ w ∈ W, ρ y w ∈ W) : Nat.card E ≤ 3 := by
  have hperp := F.finrank_perp W
  have hle : Module.finrank K W ≤ Module.finrank K (F.perp W) := Submodule.finrank_mono hWiso
  have hge : 1 ≤ Module.finrank K W := Submodule.one_le_finrank_iff.mpr hW0
  rcases (by omega : Module.finrank K W = 1 ∨ Module.finrank K W = 2) with h1 | h2
  · obtain ⟨w₀, hw₀, hspan⟩ := finrank_eq_one_iff'.mp h1
    have hw₀' : (w₀ : V) ≠ 0 := fun h => hw₀ (Subtype.ext h)
    have hfix : ∀ y : E, ρ y w₀ = w₀ := by
      intro y
      obtain ⟨c, hc⟩ := hspan ⟨ρ y w₀, hWst y w₀ w₀.2⟩
      have hc' : ρ y (w₀ : V) = c • (w₀ : V) := (congrArg Subtype.val hc).symm
      have hpow : ∀ n : ℕ, (ρ y ^ n) (w₀ : V) = c ^ n • (w₀ : V) := by
        intro n
        induction n with
        | zero => simp
        | succ n ih =>
          rw [pow_succ', Module.End.mul_apply, ih, map_smul, hc', smul_smul, pow_succ]
      have h3 : (ρ y ^ 3) (w₀ : V) = (w₀ : V) := by
        rw [← map_pow, hE3 y, map_one, Module.End.one_apply]
      rw [hpow] at h3
      have : (c ^ 3 - 1) • (w₀ : V) = 0 := by rw [sub_smul, h3, one_smul, sub_self]
      rcases smul_eq_zero.mp this with h | h
      · have hc3 : c = 1 := hP3 c (by linear_combination h)
        rw [hc', hc3, one_smul]
      · exact absurd h hw₀'
    exact casePoint hP3 hV F halt hE3 hcomm hcard ρ hρ hinj hw₀' hfix
  · exact caseLagrangian hP3 hV F hE3 hcomm ρ hρ hinj h2 hWiso hWst

end AbsSp

end CFSG.LocalAnalysis.GLTheoremA.HDesc
