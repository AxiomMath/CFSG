module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.LieOver.Orthogonal

public section

namespace CFSG.Quasithin.LieOver

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open scoped Pointwise
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel

  (statedProjectiveSubspaceStabilizer statedProjectiveFlagStabilizer)

section Generic

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def lh_perp (Q : QuadraticForm K V) (W : Submodule K V) : Submodule K V where
  carrier := {x | ∀ w ∈ W, polar Q x w = 0}
  add_mem' := by
    intro x y hx hy
    show ∀ w ∈ W, polar Q (x + y) w = 0
    intro w hw
    rw [polar_add_left, hx w hw, hy w hw, add_zero]
  zero_mem' := by
    show ∀ w ∈ W, polar Q 0 w = 0
    intro w _
    simp
  smul_mem' := by
    intro c x hx
    show ∀ w ∈ W, polar Q (c • x) w = 0
    intro w hw
    rw [polar_smul_left, hx w hw, smul_zero]

theorem lh_mem_perp {Q : QuadraticForm K V} {W : Submodule K V} {x : V} :
    x ∈ lh_perp Q W ↔ ∀ w ∈ W, polar Q x w = 0 := Iff.rfl

def lh_rad (Q : QuadraticForm K V) (W : Submodule K V) : Subgroup (V ≃ₗ[K] V) where
  carrier := {g | g ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧ (∀ w ∈ W, g w = w) ∧
    (∀ x, g x - x ∈ lh_perp Q W) ∧ (∀ x ∈ lh_perp Q W, g x - x ∈ W)}
  one_mem' := by
    refine ⟨Subgroup.one_mem _, fun w _ => rfl, fun x => ?_, fun x _ => ?_⟩
    · show x - x ∈ lh_perp Q W
      rw [sub_self]
      exact zero_mem _
    · show x - x ∈ W
      rw [sub_self]
      exact zero_mem _
  mul_mem' := by
    rintro g h ⟨hg0, hg1, hg2, hg3⟩ ⟨hh0, hh1, hh2, hh3⟩
    refine ⟨mul_mem hg0 hh0, fun w hw => ?_, fun x => ?_, fun x hx => ?_⟩
    · show g (h w) = w
      rw [hh1 w hw, hg1 w hw]
    · show g (h x) - x ∈ lh_perp Q W
      have e : g (h x) - x = (g (h x) - h x) + (h x - x) := by abel
      rw [e]
      exact add_mem (hg2 _) (hh2 x)
    · show g (h x) - x ∈ W
      have h1 : g (h x - x) = h x - x := hg1 _ (hh3 x hx)
      rw [map_sub] at h1
      have e : g (h x) - x = (h x - x) + (g x - x) := by
        calc g (h x) - x = (g (h x) - g x) + (g x - x) := by abel
          _ = (h x - x) + (g x - x) := by rw [h1]
      rw [e]
      exact add_mem (hh3 x hx) (hg3 x hx)
  inv_mem' := by
    rintro g ⟨hg0, hg1, hg2, hg3⟩
    have hfix : ∀ w ∈ W, g.symm w = w := fun w hw => by
      conv_lhs => rw [← hg1 w hw]
      exact g.symm_apply_apply w
    refine ⟨inv_mem hg0, hfix, fun x => ?_, fun x hx => ?_⟩
    · show g.symm x - x ∈ lh_perp Q W
      have h := hg2 (g.symm x)
      rw [g.apply_symm_apply] at h
      rw [← neg_sub]
      exact neg_mem h
    · show g.symm x - x ∈ W
      have hxs : g.symm x ∈ lh_perp Q W := by
        refine lh_mem_perp.2 (fun w hw => ?_)
        have h := polar_map_of_mem hg0 (g.symm x) w
        rw [g.apply_symm_apply, hg1 w hw] at h
        rw [← h]
        exact lh_mem_perp.1 hx w hw
      have h := hg3 _ hxs
      rw [g.apply_symm_apply] at h
      rw [← neg_sub]
      exact neg_mem h

theorem lh_mem_rad_iff {Q : QuadraticForm K V} {W : Submodule K V} {g : V ≃ₗ[K] V} :
    g ∈ lh_rad Q W ↔ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧ (∀ w ∈ W, g w = w) ∧
      (∀ x, g x - x ∈ lh_perp Q W) ∧ (∀ x ∈ lh_perp Q W, g x - x ∈ W) := Iff.rfl

theorem lh_app_inv (X : V ≃ₗ[K] V) (w : V) : X (X⁻¹ w) = w := X.apply_symm_apply w

theorem lh_inv_app (X : V ≃ₗ[K] V) (w : V) : X⁻¹ (X w) = w := X.symm_apply_apply w

theorem lh_mul_apply (f g : V ≃ₗ[K] V) (x : V) : (f * g) x = f (g x) := rfl

theorem lh_polar_eq_zero_of_mem {Q : QuadraticForm K V} {W : Submodule K V}
    (hW : ∀ w ∈ W, Q w = 0) {w w' : V} (hw : w ∈ W) (hw' : w' ∈ W) :
    polar Q w w' = 0 := by
  have h := hW (w + w') (W.add_mem hw hw')
  have h1 := hW w hw
  have h2 := hW w' hw'
  simp only [polar, h, h1, h2, sub_zero]

theorem lh_mem_perp_self {Q : QuadraticForm K V} {W : Submodule K V} (hW : ∀ w ∈ W, Q w = 0)
    {w : V} (hw : w ∈ W) : w ∈ lh_perp Q W :=
  lh_mem_perp.2 (fun w' hw' => lh_polar_eq_zero_of_mem hW hw hw')

theorem lh_eichler_mem_rad {Q : QuadraticForm K V} {W : Submodule K V} (hW : ∀ w ∈ W, Q w = 0)
    {u y : V} (hu : u ∈ W) (hy : y ∈ lh_perp Q W) : eichler Q u y ∈ lh_rad Q W := by
  have hQu : Q u = 0 := hW u hu
  have hpol : polar Q u y = 0 := by rw [polar_comm]; exact lh_mem_perp.1 hy u hu
  have huP : u ∈ lh_perp Q W := lh_mem_perp_self hW hu
  refine lh_mem_rad_iff.2 ⟨eichler_mem_orthogonalGroup Q u y, fun w hw => ?_, fun x => ?_,
    fun x hx => ?_⟩
  · have h1 : polar Q w u = 0 := lh_polar_eq_zero_of_mem hW hw hu
    have h2 : polar Q w y = 0 := by rw [polar_comm]; exact lh_mem_perp.1 hy w hw
    rw [eichler_apply hQu hpol w, h1, h2]
    simp
  · have e : eichler Q u y x - x = polar Q x u • y - (polar Q x y + Q y * polar Q x u) • u := by
      rw [eichler_apply hQu hpol x]
      abel
    rw [e]
    exact sub_mem (Submodule.smul_mem _ _ hy) (Submodule.smul_mem _ _ huP)
  · have hxu : polar Q x u = 0 := lh_mem_perp.1 hx u hu
    have e : eichler Q u y x - x = -(polar Q x y • u) := by
      rw [eichler_apply hQu hpol x, hxu]
      simp
    rw [e]
    exact neg_mem (Submodule.smul_mem _ _ hu)

theorem lh_rad_conj {Q : QuadraticForm K V} {W : Submodule K V} {X M : V ≃ₗ[K] V}
    (hX : X ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hXW : ∀ w ∈ W, X w ∈ W)
    (hXW' : ∀ w ∈ W, X⁻¹ w ∈ W) (hM : M ∈ lh_rad Q W) : X * M * X⁻¹ ∈ lh_rad Q W := by
  obtain ⟨hM0, hM1, hM2, hM3⟩ := lh_mem_rad_iff.1 hM
  have hXperp : ∀ p ∈ lh_perp Q W, X p ∈ lh_perp Q W := by
    intro p hp
    refine lh_mem_perp.2 (fun w hw => ?_)
    have h := polar_map_of_mem hX p (X⁻¹ w)
    rw [lh_app_inv] at h
    rw [h]
    exact lh_mem_perp.1 hp _ (hXW' w hw)
  have hXperp' : ∀ z ∈ lh_perp Q W, X⁻¹ z ∈ lh_perp Q W := by
    intro z hz
    refine lh_mem_perp.2 (fun w hw => ?_)
    have h := polar_map_of_mem hX (X⁻¹ z) w
    rw [lh_app_inv] at h
    rw [← h]
    exact lh_mem_perp.1 hz _ (hXW w hw)
  refine lh_mem_rad_iff.2 ⟨mul_mem (mul_mem hX hM0) (inv_mem hX), fun w hw => ?_,
    fun z => ?_, fun z hz => ?_⟩
  · show X (M (X⁻¹ w)) = w
    rw [hM1 _ (hXW' w hw), lh_app_inv]
  · show X (M (X⁻¹ z)) - z ∈ lh_perp Q W
    have e : X (M (X⁻¹ z)) - z = X (M (X⁻¹ z) - X⁻¹ z) := by
      rw [map_sub, lh_app_inv]
    rw [e]
    exact hXperp _ (hM2 _)
  · show X (M (X⁻¹ z)) - z ∈ W
    have e : X (M (X⁻¹ z)) - z = X (M (X⁻¹ z) - X⁻¹ z) := by
      rw [map_sub, lh_app_inv]
    rw [e]
    exact hXW _ (hM3 _ (hXperp' z hz))

theorem lh_pow_four {Q : QuadraticForm K V} {W : Submodule K V} [CharP K 2] {g : V ≃ₗ[K] V}
    (hg : g ∈ lh_rad Q W) : g ^ 4 = 1 := by
  obtain ⟨-, hg1, hg2, hg3⟩ := lh_mem_rad_iff.1 hg
  have h2 : ∀ y : V, y + y = 0 := fun y => by
    rw [← two_smul K y, CharTwo.two_eq_zero, zero_smul]
  have key : ∀ x : V, g (g (g (g x))) = x := by
    intro x
    have hy : g x - x ∈ lh_perp Q W := hg2 x
    have hz : g (g x - x) - (g x - x) ∈ W := hg3 _ hy
    have hgz : g (g (g x - x) - (g x - x)) = g (g x - x) - (g x - x) := hg1 _ hz
    set y := g x - x with hy_def
    set z := g y - y with hz_def
    have hgx : g x = x + y := by rw [hy_def]; abel
    have hgy : g y = y + z := by rw [hz_def]; abel
    have h1 : g (g x) = x + z := by
      rw [hgx, map_add, hgx, hgy]
      rw [show x + y + (y + z) = x + (y + y) + z by abel, h2 y, add_zero]
    rw [h1, map_add, map_add, h1, hgz, hgz, add_assoc, h2 z, add_zero]
  ext x
  simp only [pow_succ, pow_zero, one_mul, lh_mul_apply]
  exact key x

theorem lh_charTwo_of_normal {G : Type*} [Group G] [Finite G] {H N : Subgroup G} (hNH : N ≤ H)
    (hN2 : IsPGroup 2 N) (hNn : ∀ x ∈ H, ∀ n ∈ N, x * n * x⁻¹ ∈ N)
    (hcent : ∀ x ∈ H, (∀ n ∈ N, x * n = n * x) → x ∈ N) : CharTwo H := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnorm : (N.subgroupOf H).Normal := by
    refine ⟨fun a ha g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    simpa using hNn (g : G) g.2 (a : G) ha
  have hNO : N ≤ pCoreOf 2 H := CFSG.LieType.BorelTits.le_pCoreOf 2 hNH hnorm hN2
  rintro x ⟨hxH, hxC⟩
  apply hNO
  apply hcent x hxH
  intro n hn
  exact (Subgroup.mem_centralizer_iff.mp hxC n (hNO hn)).symm

def lh_stab (Q : QuadraticForm K V) (W : Submodule K V) : Subgroup (orthElementaryGroup Q) :=
  (MulAction.stabilizer (V ≃ₗ[K] V) W).subgroupOf (orthElementaryGroup Q)

def lh_N (Q : QuadraticForm K V) (W : Submodule K V) : Subgroup (orthElementaryGroup Q) :=
  (lh_rad Q W).subgroupOf (orthElementaryGroup Q)

theorem lh_mem_stab_iff {W : Submodule K V} {g : V ≃ₗ[K] V} :
    g ∈ MulAction.stabilizer (V ≃ₗ[K] V) W ↔ W.map (g : V ≃ₗ[K] V).toLinearMap = W :=
  Iff.rfl

theorem lh_central {Q : QuadraticForm K V} {W : Submodule K V} [CharP K 2]
    (hnd : ∀ w : V, (∀ x : V, polar Q x w = 0) → w = 0)
    (hW : ∀ w ∈ W, Q w = 0) (hne : ∃ u ∈ W, u ≠ 0)
    (hframe : ∀ u ∈ W, u ≠ 0 → ∃ y ∈ lh_perp Q W, ∃ y' ∈ lh_perp Q W, ∀ a b c : K,
      a • u + b • y + c • y' = 0 → a = 0 ∧ b = 0 ∧ c = 0)
    (hlam : (∃ v ∈ lh_perp Q W, ∃ v' ∈ lh_perp Q W, polar Q v v' ≠ 0) ∨
      (∀ u ∈ W, u ≠ 0 → ∃ y ∈ W, ∃ y' ∈ W, ∀ a b c : K,
        a • u + b • y + c • y' = 0 → a = 0 ∧ b = 0 ∧ c = 0))
    {g : V ≃ₗ[K] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hcomm : ∀ u ∈ W, ∀ y ∈ lh_perp Q W, ∀ x : V,
      g (eichler Q u y x) = eichler Q u y (g x)) :
    g ∈ lh_rad Q W := by
  have hiso : ∀ a b : V, polar Q (g a) (g b) = polar Q a b :=
    fun a b => polar_map_of_mem hg a b
  have ND1 : ∀ u : V, u ≠ 0 → ∃ x : V, polar Q x u = 1 := by
    intro u hu
    obtain ⟨x, hx⟩ : ∃ x : V, polar Q x u ≠ 0 := by
      by_contra h
      push Not at h
      exact hu (hnd u h)
    exact ⟨(polar Q x u)⁻¹ • x, by rw [polar_smul_left, smul_eq_mul, inv_mul_cancel₀ hx]⟩
  have ND2 : ∀ u y : V, u ≠ 0 → (∀ c : K, y ≠ c • u) →
      ∃ x : V, polar Q x u = 0 ∧ polar Q x y = 1 := by
    intro u y hu hy
    obtain ⟨x1, hx1⟩ := ND1 u hu
    have hex : ∃ x : V, polar Q x u = 0 ∧ polar Q x y ≠ 0 := by
      by_contra h
      push Not at h
      have key : ∀ x : V, polar Q x y = polar Q x u * polar Q x1 y := by
        intro x
        have h0 : polar Q (x - polar Q x u • x1) u = 0 := by
          rw [polar_sub_left, polar_smul_left, hx1, smul_eq_mul, mul_one, sub_self]
        have h1 := h _ h0
        rw [polar_sub_left, polar_smul_left, smul_eq_mul, sub_eq_zero] at h1
        exact h1
      apply hy (polar Q x1 y)
      apply sub_eq_zero.1
      apply hnd
      intro x
      rw [polar_sub_right, polar_smul_right, key x, smul_eq_mul]
      ring
    obtain ⟨x, hx0, hx⟩ := hex
    refine ⟨(polar Q x y)⁻¹ • x, ?_, ?_⟩
    · rw [polar_smul_left, hx0, smul_zero]
    · rw [polar_smul_left, smul_eq_mul, inv_mul_cancel₀ hx]
  have stepA : ∀ u ∈ W, u ≠ 0 → ∃ a : K, g u = a • u := by
    intro u hu hu0
    obtain ⟨y, hy, y', hy', hind⟩ := hframe u hu hu0
    have hyu : ∀ c : K, y ≠ c • u := by
      intro c hc
      have h := hind (-c) 1 0 (by rw [hc]; simp)
      exact one_ne_zero h.2.1
    have hy'u : ∀ c : K, y' ≠ c • u := by
      intro c hc
      have h := hind (-c) 0 1 (by rw [hc]; simp)
      exact one_ne_zero h.2.2
    have rep : ∀ z ∈ lh_perp Q W, ∀ x0 : V, polar Q x0 u = 0 → polar Q x0 z = 1 →
        g u = (polar Q (g x0) z + Q z * polar Q (g x0) u) • u + (-polar Q (g x0) u) • z := by
      intro z hz x0 h0 h1
      have hc := hcomm u hu z hz x0
      have hpu : polar Q u z = 0 := by rw [polar_comm]; exact lh_mem_perp.1 hz u hu
      rw [eichler_apply (hW u hu) hpu x0, h0, h1] at hc
      rw [eichler_apply (hW u hu) hpu (g x0)] at hc
      simp only [zero_smul, add_zero, mul_zero, one_smul, map_sub] at hc
      linear_combination (norm := module) -hc
    obtain ⟨x0, h0, h1⟩ := ND2 u y hu0 hyu
    obtain ⟨x0', h0', h1'⟩ := ND2 u y' hu0 hy'u
    have e1 := rep y hy x0 h0 h1
    have e2 := rep y' hy' x0' h0' h1'
    have hz := hind (polar Q (g x0) y + Q y * polar Q (g x0) u
        - (polar Q (g x0') y' + Q y' * polar Q (g x0') u))
      (-polar Q (g x0) u) (polar Q (g x0') u) (by linear_combination (norm := module) e2 - e1)
    have hp : polar Q (g x0) u = 0 := neg_eq_zero.1 hz.2.1
    refine ⟨polar Q (g x0) y + Q y * polar Q (g x0) u, ?_⟩
    rw [e1, hp, neg_zero, zero_smul, add_zero]
  choose! a ha using stepA
  have claimL : ∀ u ∈ W, ∀ b : K, u ≠ 0 → g u = b • u →
      ∀ y ∈ lh_perp Q W, ∃ c : K, b • g y - y = c • u := by
    intro u hu b hu0 hgu y hy
    obtain ⟨x0, hx0⟩ := ND1 u hu0
    have hpu : polar Q u y = 0 := by rw [polar_comm]; exact lh_mem_perp.1 hy u hu
    have hc := hcomm u hu y hy x0
    rw [eichler_apply (hW u hu) hpu x0, hx0] at hc
    rw [eichler_apply (hW u hu) hpu (g x0)] at hc
    simp only [one_smul, mul_one, map_sub, map_add, map_smul, hgu] at hc
    have hβ : b * polar Q (g x0) u = 1 := by
      have h := hiso x0 u
      rw [hgu, hx0, polar_smul_right, smul_eq_mul] at h
      exact h
    refine ⟨b ^ 2 * (polar Q x0 y + Q y) - b * (polar Q (g x0) y + Q y * polar Q (g x0) u), ?_⟩
    linear_combination (norm := module) b • hc + hβ • y
  have hWperp : ∀ w ∈ W, w ∈ lh_perp Q W := fun w hw => lh_mem_perp_self hW hw
  have hpair : ∀ p ∈ W, ∀ q ∈ W, p ≠ 0 → (∀ s t : K, s • p + t • q = 0 → s = 0 ∧ t = 0) →
      a p * a q = 1 := by
    intro p hp q hq hp0 hind2
    have hq0 : q ≠ 0 := by
      intro h0
      have h := hind2 0 1 (by rw [h0]; simp)
      exact one_ne_zero h.2
    obtain ⟨c, hc⟩ := claimL p hp (a p) hp0 (ha p hp hp0) q (hWperp q hq)
    rw [ha q hq hq0] at hc
    have hvec : (-c) • p + (a p * a q - 1) • q = 0 := by
      linear_combination (norm := module) hc
    exact sub_eq_zero.1 (hind2 (-c) (a p * a q - 1) hvec).2
  have hsq : ∀ u ∈ W, u ≠ 0 → a u * a u = 1 := by
    rcases hlam with ⟨v, hv, v', hv', hvv⟩ | hL
    · intro u hu hu0
      obtain ⟨cv, hcv⟩ := claimL u hu (a u) hu0 (ha u hu hu0) v hv
      obtain ⟨cv', hcv'⟩ := claimL u hu (a u) hu0 (ha u hu hu0) v' hv'
      have P1 : a u • g v = cv • u + v := eq_add_of_sub_eq hcv
      have P2 : a u • g v' = cv' • u + v' := eq_add_of_sub_eq hcv'
      have huu : polar Q u u = 0 := lh_polar_eq_zero_of_mem hW hu hu
      have hvu : polar Q v u = 0 := lh_mem_perp.1 hv u hu
      have huv' : polar Q u v' = 0 := by rw [polar_comm]; exact lh_mem_perp.1 hv' u hu
      have key : polar Q (a u • g v) (a u • g v') = polar Q (cv • u + v) (cv' • u + v') := by
        rw [P1, P2]
      have lhs : polar Q (a u • g v) (a u • g v') = a u * (a u * polar Q v v') := by
        rw [polar_smul_left, polar_smul_right, smul_eq_mul, smul_eq_mul, hiso v v']
      have rhs : polar Q (cv • u + v) (cv' • u + v') = polar Q v v' := by
        simp only [polar_add_left, polar_add_right, polar_smul_left, polar_smul_right, huu,
          huv', hvu, smul_eq_mul, mul_zero, zero_mul, add_zero, zero_add]
      rw [lhs, rhs] at key
      have h2 : (a u * a u - 1) * polar Q v v' = 0 := by linear_combination key
      exact sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_right hvv)
    · intro u hu hu0
      obtain ⟨y, hy, y', hy', hind3⟩ := hL u hu hu0
      have hy0 : y ≠ 0 := fun h => one_ne_zero (hind3 0 1 0 (by simp [h])).2.1
      have hu_y : ∀ s t : K, s • u + t • y = 0 → s = 0 ∧ t = 0 := fun s t h => by
        have h' := hind3 s t 0 (by simpa using h)
        exact ⟨h'.1, h'.2.1⟩
      have hy_y' : ∀ s t : K, s • y + t • y' = 0 → s = 0 ∧ t = 0 := fun s t h => by
        have h' := hind3 0 s t (by simpa using h)
        exact ⟨h'.2.1, h'.2.2⟩
      have hu_y' : ∀ s t : K, s • u + t • y' = 0 → s = 0 ∧ t = 0 := fun s t h => by
        have h' := hind3 s 0 t (by simpa using h)
        exact ⟨h'.1, h'.2.2⟩
      have e1 := hpair u hu y hy hu0 hu_y
      have e2 := hpair y hy y' hy' hy0 hy_y'
      have e3 := hpair u hu y' hy' hu0 hu_y'
      have e4 : a y' = a u := by linear_combination (-(a y')) * e1 + (a u) * e2
      linear_combination e3 - (a u) * e4
  have ha1 : ∀ u ∈ W, u ≠ 0 → a u = 1 := by
    intro u hu hu0
    have h2 : (a u - 1) * (a u - 1) = 0 := by
      linear_combination hsq u hu hu0 + (1 - a u) * (CharTwo.two_eq_zero : (2 : K) = 0)
    exact sub_eq_zero.1 (mul_self_eq_zero.1 h2)
  have hfix : ∀ w ∈ W, g w = w := by
    intro w hw
    by_cases hw0 : w = 0
    · rw [hw0, map_zero]
    · rw [ha w hw hw0, ha1 w hw hw0, one_smul]
  obtain ⟨u0, hu0W, hu00⟩ := hne
  have hD : ∀ y ∈ lh_perp Q W, g y - y ∈ W := by
    intro y hy
    obtain ⟨c, hc⟩ := claimL u0 hu0W (a u0) hu00 (ha u0 hu0W hu00) y hy
    have h1 : a u0 • g y - y ∈ W := by
      rw [hc]
      exact Submodule.smul_mem _ _ hu0W
    rw [ha1 u0 hu0W hu00, one_smul] at h1
    exact h1
  have hE : ∀ x : V, g x - x ∈ lh_perp Q W := by
    intro x
    refine lh_mem_perp.2 (fun w hw => ?_)
    have h := hiso x w
    rw [hfix w hw] at h
    rw [polar_sub_left, h, sub_self]
  exact lh_mem_rad_iff.2 ⟨hg, hfix, hE, hD⟩

theorem lh_charTwo_of_rad {Q : QuadraticForm K V} {W : Submodule K V} [CharP K 2]
    [Finite (orthElementaryGroup Q)]
    (hnd : ∀ w : V, (∀ x : V, polar Q x w = 0) → w = 0)
    (hW : ∀ w ∈ W, Q w = 0) (hne : ∃ u ∈ W, u ≠ 0)
    (hframe : ∀ u ∈ W, u ≠ 0 → ∃ y ∈ lh_perp Q W, ∃ y' ∈ lh_perp Q W, ∀ a b c : K,
      a • u + b • y + c • y' = 0 → a = 0 ∧ b = 0 ∧ c = 0)
    (hlam : (∃ v ∈ lh_perp Q W, ∃ v' ∈ lh_perp Q W, polar Q v v' ≠ 0) ∨
      (∀ u ∈ W, u ≠ 0 → ∃ y ∈ W, ∃ y' ∈ W, ∀ a b c : K,
        a • u + b • y + c • y' = 0 → a = 0 ∧ b = 0 ∧ c = 0)) :
    CharTwo (lh_stab Q W) := by
  refine lh_charTwo_of_normal (N := lh_N Q W) ?_ ?_ ?_ ?_
  · intro x hx
    have hx' := lh_mem_rad_iff.1 (Subgroup.mem_subgroupOf.1 hx)
    exact Subgroup.mem_subgroupOf.2
      (lh_mem_stab_iff.2 (lf_map_eq_of_fixes (fun w hw => hx'.2.1 w hw)))
  · intro n
    refine ⟨2, Subtype.ext (Subtype.ext ?_)⟩
    have h4 := lh_pow_four (Subgroup.mem_subgroupOf.1 n.2)
    simpa using h4
  · intro x hx m hm
    have hx1 : W.map (x : V ≃ₗ[K] V).toLinearMap = W :=
      lh_mem_stab_iff.1 (Subgroup.mem_subgroupOf.1 hx)
    have hXO : (x : V ≃ₗ[K] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
      orthElementaryGroup_le Q x.2
    have hXW : ∀ w ∈ W, (x : V ≃ₗ[K] V) w ∈ W := fun w hw => by
      have h : (x : V ≃ₗ[K] V) w ∈ W.map (x : V ≃ₗ[K] V).toLinearMap :=
        Submodule.mem_map_of_mem hw
      rw [hx1] at h
      exact h
    have hXW' : ∀ w ∈ W, (x : V ≃ₗ[K] V)⁻¹ w ∈ W := fun w hw => by
      have hw' : w ∈ W.map (x : V ≃ₗ[K] V).toLinearMap := by rw [hx1]; exact hw
      obtain ⟨v, hv, hvw⟩ := Submodule.mem_map.1 hw'
      rw [← hvw]
      show (x : V ≃ₗ[K] V)⁻¹ ((x : V ≃ₗ[K] V) v) ∈ W
      rw [lh_inv_app]
      exact hv
    refine Subgroup.mem_subgroupOf.2 ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact lh_rad_conj hXO hXW hXW' (Subgroup.mem_subgroupOf.1 hm)
  · intro x hx hcx
    refine Subgroup.mem_subgroupOf.2
      (lh_central hnd hW hne hframe hlam (orthElementaryGroup_le Q x.2) ?_)
    intro u hu y hy z
    have hmem : eichler Q u y ∈ orthElementaryGroup Q := eichler_mem_elementaryGroup Q u y
    have hmN : (⟨eichler Q u y, hmem⟩ : orthElementaryGroup Q) ∈ lh_N Q W :=
      Subgroup.mem_subgroupOf.2 (lh_eichler_mem_rad hW hu hy)
    have h := congrArg (fun e : orthElementaryGroup Q => (e : V ≃ₗ[K] V) z) (hcx _ hmN)
    simpa [lh_mul_apply] using h

end Generic

theorem lh_plus_nd {n : ℕ} {K : Type} [Field K] (w : Fin n ⊕ Fin n → K)
    (h : ∀ x, polar (quadPlus n K) x w = 0) : w = 0 := by
  funext v
  rcases v with k | k
  · have h1 := h (Pi.single (Sum.inr k) 1)
    rw [polar_quadPlus] at h1
    simpa [Pi.single_apply] using h1
  · have h1 := h (Pi.single (Sum.inl k) 1)
    rw [polar_quadPlus] at h1
    simpa [Pi.single_apply] using h1

theorem lh_perp_single_inl {n : ℕ} {K : Type} [Field K] (W : Submodule K (Fin n ⊕ Fin n → K))
    (hW : ∀ w ∈ W, ∀ k, w (Sum.inr k) = 0) (j : Fin n) :
    Pi.single (Sum.inl j) (1 : K) ∈ lh_perp (quadPlus n K) W := by
  refine lh_mem_perp.2 (fun w hw => ?_)
  rw [polar_quadPlus]
  apply Finset.sum_eq_zero
  intro m _
  simp [Pi.single_apply, hW w hw m]

theorem lh_perp_single_inr {n : ℕ} {K : Type} [Field K] (W : Submodule K (Fin n ⊕ Fin n → K))
    (j : Fin n) (hW : ∀ w ∈ W, w (Sum.inl j) = 0) :
    Pi.single (Sum.inr j) (1 : K) ∈ lh_perp (quadPlus n K) W := by
  refine lh_mem_perp.2 (fun w hw => ?_)
  rw [polar_quadPlus]
  apply Finset.sum_eq_zero
  intro m _
  by_cases hm : m = j
  · subst hm
    simp [Pi.single_apply, hW w hw]
  · simp [Pi.single_apply, hm, Ne.symm hm]

theorem lh_polar_single {n : ℕ} {K : Type} [Field K] (j : Fin n) :
    polar (quadPlus n K) (Pi.single (Sum.inl j) (1 : K)) (Pi.single (Sum.inr j) 1) ≠ 0 := by
  rw [polar_quadPlus]
  simp [Pi.single_apply]

theorem lh_frameX {n : ℕ} {K : Type} [Field K] (hn : 3 ≤ n) {u : Fin n ⊕ Fin n → K}
    (hu : ∀ k, u (Sum.inr k) = 0) (hu0 : u ≠ 0) :
    ∃ j1 j2 : Fin n, j1 ≠ j2 ∧ ∀ a b c : K,
      a • u + b • Pi.single (Sum.inl j1) (1 : K) + c • Pi.single (Sum.inl j2) (1 : K) = 0 →
        a = 0 ∧ b = 0 ∧ c = 0 := by
  obtain ⟨k, hk⟩ : ∃ k : Fin n, u (Sum.inl k) ≠ 0 := by
    by_contra h
    push Not at h
    apply hu0
    funext v
    rcases v with k | k
    · exact h k
    · exact hu k
  have hcard : 1 < (Finset.univ.erase k).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨j1, hj1, j2, hj2, hj12⟩ := Finset.one_lt_card.1 hcard
  rw [Finset.mem_erase] at hj1 hj2
  refine ⟨j1, j2, hj12, fun a b c h => ?_⟩
  have ha : a = 0 := by
    have hk' := congrFun h (Sum.inl k)
    have h1 : a * u (Sum.inl k) = 0 := by
      simpa [Pi.single_apply, hj1.1, hj2.1] using hk'
    exact (mul_eq_zero.1 h1).resolve_right hk
  subst ha
  have hb := congrFun h (Sum.inl j1)
  have hc := congrFun h (Sum.inl j2)
  simp [Pi.single_apply, hj12, Ne.symm hj12] at hb hc
  exact ⟨rfl, hb, hc⟩

theorem lh_frame_perp {n : ℕ} {K : Type} [Field K] (hn : 3 ≤ n)
    (W : Submodule K (Fin n ⊕ Fin n → K)) (hWin : ∀ w ∈ W, ∀ k, w (Sum.inr k) = 0) :
    ∀ u ∈ W, u ≠ 0 → ∃ y ∈ lh_perp (quadPlus n K) W, ∃ y' ∈ lh_perp (quadPlus n K) W,
      ∀ a b c : K, a • u + b • y + c • y' = 0 → a = 0 ∧ b = 0 ∧ c = 0 := by
  intro u hu hu0
  obtain ⟨j1, j2, -, hind⟩ := lh_frameX hn (fun k => hWin u hu k) hu0
  exact ⟨_, lh_perp_single_inl W hWin j1, _, lh_perp_single_inl W hWin j2, hind⟩

theorem lh_lam_W {n : ℕ} {K : Type} [Field K] (hn : 3 ≤ n)
    (W : Submodule K (Fin n ⊕ Fin n → K)) (hWin : ∀ w ∈ W, ∀ k, w (Sum.inr k) = 0)
    (hWe : ∀ j : Fin n, Pi.single (Sum.inl j) (1 : K) ∈ W) :
    ∀ u ∈ W, u ≠ 0 → ∃ y ∈ W, ∃ y' ∈ W, ∀ a b c : K,
      a • u + b • y + c • y' = 0 → a = 0 ∧ b = 0 ∧ c = 0 := by
  intro u hu hu0
  obtain ⟨j1, j2, -, hind⟩ := lh_frameX hn (fun k => hWin u hu k) hu0
  exact ⟨_, hWe j1, _, hWe j2, hind⟩

theorem lh_single_mem_flag {n : ℕ} {K : Type} [Field K] (i : ℕ) (j : Fin n) (hj : (j : ℕ) < i) :
    Pi.single (Sum.inl j) (1 : K) ∈ OrthogonalSplit.flag n K i := by
  rw [OrthogonalSplit.mem_flag_iff_coord]
  refine ⟨fun k => by simp [Pi.single_apply], fun k hk => ?_⟩
  have hjk : j ≠ k := fun h => by subst h; omega
  simp [Pi.single_apply, hjk]

theorem lh_single_inl_mem_Xstar {n : ℕ} {K : Type} [Field K] (hr : 0 < n) (j : Fin n)
    (hj : (j : ℕ) ≠ n - 1) : Pi.single (Sum.inl j) (1 : K) ∈ OrthogonalSplit.Xstar n K hr := by
  rw [OrthogonalSplit.mem_Xstar hr]
  have hjm : j ≠ ⟨n - 1, by omega⟩ := fun h => hj (by rw [h])
  refine ⟨by simp [Pi.single_apply, hjm], fun k _ => by simp [Pi.single_apply]⟩

theorem lh_single_inr_mem_Xstar {n : ℕ} {K : Type} [Field K] (hr : 0 < n) :
    Pi.single (Sum.inr (⟨n - 1, by omega⟩ : Fin n)) (1 : K) ∈ OrthogonalSplit.Xstar n K hr := by
  rw [OrthogonalSplit.mem_Xstar hr]
  refine ⟨by simp [Pi.single_apply], fun k hk => ?_⟩
  simp [Pi.single_apply, hk, Ne.symm hk]

theorem lh_quadPlus_Xstar {n : ℕ} {K : Type} [Field K] (hr : 0 < n) :
    ∀ w ∈ OrthogonalSplit.Xstar n K hr, quadPlus n K w = 0 := by
  intro w hw
  obtain ⟨h1, h2⟩ := (OrthogonalSplit.mem_Xstar hr).1 hw
  rw [quadPlus_apply]
  apply Finset.sum_eq_zero
  intro m _
  by_cases hm : m = ⟨n - 1, by omega⟩
  · rw [hm, h1, zero_mul]
  · rw [h2 m hm, mul_zero]

theorem lh_frameS {n : ℕ} {K : Type} [Field K] (hn : 4 ≤ n) {u : Fin n ⊕ Fin n → K}
    (hu : u ∈ OrthogonalSplit.Xstar n K (by omega)) (hu0 : u ≠ 0) :
    ∃ y ∈ OrthogonalSplit.Xstar n K (by omega), ∃ y' ∈ OrthogonalSplit.Xstar n K (by omega),
      ∀ a b c : K, a • u + b • y + c • y' = 0 → a = 0 ∧ b = 0 ∧ c = 0 := by
  have hr : 0 < n := by omega
  obtain ⟨hmm1, hmm2⟩ := (OrthogonalSplit.mem_Xstar hr).1 hu
  by_cases hk : ∃ k : Fin n, u (Sum.inl k) ≠ 0
  · obtain ⟨k, hk⟩ := hk
    have hkmm : k ≠ ⟨n - 1, by omega⟩ := fun h => hk (by rw [h]; exact hmm1)
    have hcard : 1 < ((Finset.univ.erase k).erase (⟨n - 1, by omega⟩ : Fin n)).card := by
      rw [Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨Ne.symm hkmm, Finset.mem_univ _⟩),
        Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
      omega
    obtain ⟨j1, hj1, j2, -, -⟩ := Finset.one_lt_card.1 hcard
    rw [Finset.mem_erase, Finset.mem_erase] at hj1
    have hj1mm : (j1 : ℕ) ≠ n - 1 := fun h => hj1.1 (Fin.ext h)
    refine ⟨Pi.single (Sum.inl j1) 1, lh_single_inl_mem_Xstar hr j1 hj1mm,
      Pi.single (Sum.inr (⟨n - 1, by omega⟩ : Fin n)) 1, lh_single_inr_mem_Xstar hr, ?_⟩
    intro a b c h
    have ha : a = 0 := by
      have hk' := congrFun h (Sum.inl k)
      have h1 : a * u (Sum.inl k) = 0 := by
        simpa [Pi.single_apply, hj1.2.1, hkmm] using hk'
      exact (mul_eq_zero.1 h1).resolve_right hk
    subst ha
    have hb := congrFun h (Sum.inl j1)
    have hc := congrFun h (Sum.inr (⟨n - 1, by omega⟩ : Fin n))
    simp [Pi.single_apply, hj1.2.1, hkmm] at hb hc
    exact ⟨rfl, hb, hc⟩
  · push Not at hk
    have ht : u (Sum.inr (⟨n - 1, by omega⟩ : Fin n)) ≠ 0 := by
      intro h0
      apply hu0
      funext v
      rcases v with k | k
      · exact hk k
      · by_cases hkm : k = ⟨n - 1, by omega⟩
        · subst hkm
          exact h0
        · exact hmm2 k hkm
    have hcard : 1 < (Finset.univ.erase (⟨n - 1, by omega⟩ : Fin n)).card := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
      omega
    obtain ⟨j1, hj1, j2, hj2, hj12⟩ := Finset.one_lt_card.1 hcard
    rw [Finset.mem_erase] at hj1 hj2
    have hj1mm : (j1 : ℕ) ≠ n - 1 := fun h => hj1.1 (Fin.ext h)
    have hj2mm : (j2 : ℕ) ≠ n - 1 := fun h => hj2.1 (Fin.ext h)
    refine ⟨Pi.single (Sum.inl j1) 1, lh_single_inl_mem_Xstar hr j1 hj1mm,
      Pi.single (Sum.inl j2) 1, lh_single_inl_mem_Xstar hr j2 hj2mm, ?_⟩
    intro a b c h
    have ha : a = 0 := by
      have hk' := congrFun h (Sum.inr (⟨n - 1, by omega⟩ : Fin n))
      have h1 : a * u (Sum.inr (⟨n - 1, by omega⟩ : Fin n)) = 0 := by
        simpa [Pi.single_apply] using hk'
      exact (mul_eq_zero.1 h1).resolve_right ht
    subst ha
    have hb := congrFun h (Sum.inl j1)
    have hc := congrFun h (Sum.inl j2)
    simp [Pi.single_apply, hj12, Ne.symm hj12] at hb hc
    exact ⟨rfl, hb, hc⟩

theorem lh_charTwo_flag_lt {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} (hn : 4 ≤ n)
    (i : ℕ) (hi : 1 ≤ i) (hin : i < n) :
    CharTwo (lh_stab (quadPlus n K) (OrthogonalSplit.flag n K i)) := by
  haveI : Finite (orthElementaryGroup (quadPlus n K)) := finite_orthElementaryGroup
  have hWin : ∀ w ∈ OrthogonalSplit.flag n K i, ∀ k, w (Sum.inr k) = 0 :=
    fun w hw k => ((OrthogonalSplit.mem_flag_iff_coord).1 hw).1 k
  have hWl : ∀ w ∈ OrthogonalSplit.flag n K i, w (Sum.inl (⟨n - 1, by omega⟩ : Fin n)) = 0 :=
    fun w hw => ((OrthogonalSplit.mem_flag_iff_coord).1 hw).2 _ (by show i ≤ n - 1; omega)
  have hne : ∃ u ∈ OrthogonalSplit.flag n K i, u ≠ 0 := by
    refine ⟨Pi.single (Sum.inl (⟨0, by omega⟩ : Fin n)) (1 : K),
      lh_single_mem_flag i _ (by show 0 < i; omega), ?_⟩
    intro h
    have := congrFun h (Sum.inl (⟨0, by omega⟩ : Fin n))
    simp at this
  exact lh_charTwo_of_rad (fun w h => lh_plus_nd w h)
    (fun w hw => OrthogonalSplit.flag_singular i w hw) hne
    (lh_frame_perp (by omega) _ hWin)
    (Or.inl ⟨Pi.single (Sum.inl (⟨n - 1, by omega⟩ : Fin n)) (1 : K),
      lh_perp_single_inl _ hWin _, Pi.single (Sum.inr (⟨n - 1, by omega⟩ : Fin n)) (1 : K),
      lh_perp_single_inr _ _ hWl, lh_polar_single _⟩)

theorem lh_charTwo_flag_top {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} (hn : 4 ≤ n) :
    CharTwo (lh_stab (quadPlus n K) (OrthogonalSplit.flag n K n)) := by
  haveI : Finite (orthElementaryGroup (quadPlus n K)) := finite_orthElementaryGroup
  have hWin : ∀ w ∈ OrthogonalSplit.flag n K n, ∀ k, w (Sum.inr k) = 0 :=
    fun w hw k => ((OrthogonalSplit.mem_flag_iff_coord).1 hw).1 k
  have hWe : ∀ j : Fin n, Pi.single (Sum.inl j) (1 : K) ∈ OrthogonalSplit.flag n K n :=
    fun j => lh_single_mem_flag n j j.isLt
  have hne : ∃ u ∈ OrthogonalSplit.flag n K n, u ≠ 0 := by
    refine ⟨Pi.single (Sum.inl (⟨0, by omega⟩ : Fin n)) (1 : K), hWe _, ?_⟩
    intro h
    have := congrFun h (Sum.inl (⟨0, by omega⟩ : Fin n))
    simp at this
  exact lh_charTwo_of_rad (fun w h => lh_plus_nd w h)
    (fun w hw => OrthogonalSplit.flag_singular n w hw) hne
    (lh_frame_perp (by omega) _ hWin) (Or.inr (lh_lam_W (by omega) _ hWin hWe))

theorem lh_charTwo_Xstar {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} (hn : 4 ≤ n) :
    CharTwo (lh_stab (quadPlus n K) (OrthogonalSplit.Xstar n K (by omega))) := by
  haveI : Finite (orthElementaryGroup (quadPlus n K)) := finite_orthElementaryGroup
  have hr : 0 < n := by omega
  have hW : ∀ w ∈ OrthogonalSplit.Xstar n K hr, quadPlus n K w = 0 := lh_quadPlus_Xstar hr
  have hne : ∃ u ∈ OrthogonalSplit.Xstar n K hr, u ≠ 0 := by
    refine ⟨Pi.single (Sum.inl (⟨0, by omega⟩ : Fin n)) (1 : K),
      lh_single_inl_mem_Xstar hr (⟨0, by omega⟩ : Fin n) (by show (0 : ℕ) ≠ n - 1; omega), ?_⟩
    intro h
    have := congrFun h (Sum.inl (⟨0, by omega⟩ : Fin n))
    simp at this
  have hperp : ∀ w ∈ OrthogonalSplit.Xstar n K hr,
      w ∈ lh_perp (quadPlus n K) (OrthogonalSplit.Xstar n K hr) :=
    fun w hw => lh_mem_perp_self hW hw
  exact lh_charTwo_of_rad (fun w h => lh_plus_nd w h) hW hne
    (fun u hu hu0 => by
      obtain ⟨y, hy, y', hy', hind⟩ := lh_frameS hn hu hu0
      exact ⟨y, hperp y hy, y', hperp y' hy', hind⟩)
    (Or.inr (fun u hu hu0 => lh_frameS hn hu hu0))

theorem pOmegaPlusCharTwo_holds : POmegaPlusCharTwo := by
  unfold POmegaPlusCharTwo
  intro n K _ _ _ hn W hW
  rcases hW with ⟨i, hi1, hi2, rfl⟩ | rfl | rfl
  · exact lh_charTwo_flag_lt hn i hi1 (by omega)
  · exact lh_charTwo_flag_top hn
  · exact lh_charTwo_Xstar hn

section Faithful

variable {K : Type} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem lh_charTwo_of_faithful {Γ : Type*} [Group Γ] [Finite Γ] {Q : QuadraticForm K V}
    {W : Submodule K V} [CharP K 2] (ρ : Γ →* (V ≃ₗ[K] V)) (hρ : Function.Injective ρ)
    (hO : ∀ γ : Γ, ρ γ ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hEl : ∀ u ∈ W, ∀ y ∈ lh_perp Q W, ∃ γ : Γ, ρ γ = eichler Q u y)
    (hnd : ∀ w : V, (∀ x : V, polar Q x w = 0) → w = 0)
    (hW : ∀ w ∈ W, Q w = 0) (hne : ∃ u ∈ W, u ≠ 0)
    (hframe : ∀ u ∈ W, u ≠ 0 → ∃ y ∈ lh_perp Q W, ∃ y' ∈ lh_perp Q W, ∀ a b c : K,
      a • u + b • y + c • y' = 0 → a = 0 ∧ b = 0 ∧ c = 0)
    (hlam : (∃ v ∈ lh_perp Q W, ∃ v' ∈ lh_perp Q W, polar Q v v' ≠ 0) ∨
      (∀ u ∈ W, u ≠ 0 → ∃ y ∈ W, ∃ y' ∈ W, ∀ a b c : K,
        a • u + b • y + c • y' = 0 → a = 0 ∧ b = 0 ∧ c = 0)) :
    CharTwo ((MulAction.stabilizer (V ≃ₗ[K] V) W).comap ρ) := by
  refine lh_charTwo_of_normal (N := (lh_rad Q W).comap ρ) ?_ ?_ ?_ ?_
  · intro x hx
    have hx' := lh_mem_rad_iff.1 (Subgroup.mem_comap.1 hx)
    exact Subgroup.mem_comap.2
      (lh_mem_stab_iff.2 (lf_map_eq_of_fixes (fun w hw => hx'.2.1 w hw)))
  · intro n
    refine ⟨2, Subtype.ext ?_⟩
    apply hρ
    have h4 := lh_pow_four (Subgroup.mem_comap.1 n.2)
    simpa [map_pow] using h4
  · intro x hx m hm
    have hx1 : W.map (ρ x).toLinearMap = W := lh_mem_stab_iff.1 (Subgroup.mem_comap.1 hx)
    have hXW : ∀ w ∈ W, ρ x w ∈ W := fun w hw => by
      have h : ρ x w ∈ W.map (ρ x).toLinearMap := Submodule.mem_map_of_mem hw
      rw [hx1] at h
      exact h
    have hXW' : ∀ w ∈ W, (ρ x)⁻¹ w ∈ W := fun w hw => by
      have hw' : w ∈ W.map (ρ x).toLinearMap := by rw [hx1]; exact hw
      obtain ⟨v, hv, hvw⟩ := Submodule.mem_map.1 hw'
      rw [← hvw]
      show (ρ x)⁻¹ (ρ x v) ∈ W
      rw [lh_inv_app]
      exact hv
    refine Subgroup.mem_comap.2 ?_
    rw [map_mul, map_mul, map_inv]
    exact lh_rad_conj (hO x) hXW hXW' (Subgroup.mem_comap.1 hm)
  · intro x hx hcx
    refine Subgroup.mem_comap.2 (lh_central hnd hW hne hframe hlam (hO x) ?_)
    intro u hu y hy z
    obtain ⟨γ, hγ⟩ := hEl u hu y hy
    have hγN : γ ∈ (lh_rad Q W).comap ρ :=
      Subgroup.mem_comap.2 (by rw [hγ]; exact lh_eichler_mem_rad hW hu hy)
    have h := congrArg (fun e : (V ≃ₗ[K] V) => e z) (congrArg ρ (hcx γ hγN))
    simp only [map_mul, hγ, lh_mul_apply] at h
    exact h

theorem lh_commutator_le_orth {V : Type*} [AddCommGroup V] [Module K V] (Q : QuadraticForm K V) :
    ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ ≤
      TauCeti.QuadraticMap.orthogonalGroup Q := by
  rw [Subgroup.commutator_le]
  intro g₁ h₁ g₂ h₂
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem h₁ h₂) (inv_mem h₁)) (inv_mem h₂)

theorem lh_toLin_mem_orth {ι : Type} [Fintype ι] [DecidableEq ι] {Q : QuadraticForm K (ι → K)}
    {Q0 : (ι → K) → K} (hQ : ⇑Q = Q0) {g : Matrix.GeneralLinearGroup ι K}
    (hg : g ∈ StatedOmega Q0) :
    toLinEquiv ι K g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  rw [statedOmega_eq_comap hQ] at hg
  exact lh_commutator_le_orth Q (Subgroup.mem_comap.1 hg)

theorem lh_omega_scalar_one [CharP K 2] {ι : Type} [Fintype ι] [DecidableEq ι]
    {Q : QuadraticForm K (ι → K)} {Q0 : (ι → K) → K} (hQ : ⇑Q = Q0) {v0 : ι → K}
    (hv0 : Q v0 ≠ 0) {g : Matrix.GeneralLinearGroup ι K} (hg : g ∈ StatedOmega Q0)
    (hs : g ∈ StatedScalars ι K) : g = 1 := by
  have hO := lh_toLin_mem_orth hQ hg
  obtain ⟨c, hc⟩ := mem_scalars.1 ((mem_statedScalars_iff g).1 hs)
  have h1 := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1 hO v0
  rw [hc v0, map_smul_eq_sq] at h1
  have h2 : (c ^ 2 - 1) * Q v0 = 0 := by linear_combination h1
  have h3 : c ^ 2 - 1 = 0 := (mul_eq_zero.1 h2).resolve_right hv0
  have hc1 : c = 1 := by
    have h4 : (c - 1) * (c - 1) = 0 := by
      linear_combination h3 + (1 - c) * (CharTwo.two_eq_zero : (2 : K) = 0)
    exact sub_eq_zero.1 (mul_self_eq_zero.1 h4)
  have hgone : toLinEquiv ι K g = 1 := LinearEquiv.ext fun v => by
    simp [hc v, hc1]
  exact (toLinEquiv ι K).injective (by rw [hgone, map_one])

noncomputable def lh_rho {ι : Type} [Fintype ι] [DecidableEq ι] {Q : QuadraticForm K (ι → K)}
    {Q0 : (ι → K) → K} [CharP K 2] (hQ : ⇑Q = Q0) {v0 : ι → K} (hv0 : Q v0 ≠ 0) :
    StatedProj (StatedOmega Q0) →* ((ι → K) ≃ₗ[K] (ι → K)) :=
  QuotientGroup.lift _ ((toLinEquiv ι K).toMonoidHom.comp (StatedOmega Q0).subtype)
    (fun x hx => by
      have hs : (x : Matrix.GeneralLinearGroup ι K) ∈ StatedScalars ι K :=
        Subgroup.mem_subgroupOf.1 hx
      have h1 := lh_omega_scalar_one hQ hv0 x.2 hs
      rw [MonoidHom.mem_ker]
      simp [h1])

theorem lh_rho_injective {ι : Type} [Fintype ι] [DecidableEq ι] {Q : QuadraticForm K (ι → K)}
    {Q0 : (ι → K) → K} [CharP K 2] (hQ : ⇑Q = Q0) {v0 : ι → K} (hv0 : Q v0 ≠ 0) :
    Function.Injective (lh_rho hQ hv0) := by
  refine (injective_iff_map_eq_one _).2 (fun x hx => ?_)
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ x
  have hx' : toLinEquiv ι K (g : Matrix.GeneralLinearGroup ι K) = 1 := hx
  have hg : (g : Matrix.GeneralLinearGroup ι K) = 1 :=
    (toLinEquiv ι K).injective (hx'.trans (map_one _).symm)
  refine (QuotientGroup.eq_one_iff g).2 (Subgroup.mem_subgroupOf.2 ?_)
  rw [hg]
  exact Subgroup.one_mem _

end Faithful

section MinusFacts

variable {K : Type} [Field K]

theorem lh_tail_props {n : ℕ} (i : Fin (n - 1)) :
    ∀ w ∈ OrthogonalTail.tailModelFlag (n - 1) K (Fin 2) i,
      (∀ k, w (Sum.inr k) = 0) ∧ (∀ j : Fin (n - 1), i < j → w (Sum.inl j) = 0) := by
  intro w hw
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, hj, rfl⟩ := hx
    refine ⟨fun k => ?_, fun m hm => ?_⟩
    · simp [Pi.single_apply]
    · have hjm : j ≠ m := by
        intro h
        subst h
        rw [Fin.lt_def] at hm
        simp only [Set.mem_setOf_eq] at hj
        omega
      simp [Pi.single_apply, hjm]
  | zero => exact ⟨fun k => rfl, fun j _ => rfl⟩
  | add x y _ _ hx hy =>
    exact ⟨fun k => by simp [hx.1 k, hy.1 k], fun j hj => by simp [hx.2 j hj, hy.2 j hj]⟩
  | smul a x _ hx => exact ⟨fun k => by simp [hx.1 k], fun j hj => by simp [hx.2 j hj]⟩

theorem lh_tail_single_mem {n : ℕ} (i j : Fin (n - 1)) (hj : j ≤ i) :
    Pi.single (Sum.inl j) (1 : K) ∈ OrthogonalTail.tailModelFlag (n - 1) K (Fin 2) i :=
  Submodule.subset_span ⟨j, by
    show (j : ℕ) < (i : ℕ) + 1
    have := Fin.le_iff_val_le_val.1 hj
    omega, rfl⟩

theorem lh_tail_sing {n : ℕ} {b c : K} (i : Fin (n - 1)) :
    ∀ w ∈ OrthogonalTail.tailModelFlag (n - 1) K (Fin 2) i, quadMinus n K b c w = 0 := by
  intro w hw
  rw [quadMinus_apply]
  simp [(lh_tail_props i w hw).1]

theorem lh_minus_nd {n : ℕ} [CharP K 2] {b c : K} (hb : b ≠ 0)
    (w : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K)
    (h : ∀ x, polar (quadMinus n K b c) x w = 0) : w = 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hA : ∀ j : Fin (n - 1), w (Sum.inr (Sum.inl j)) = 0 := fun j => by
    have := h (Pi.single (Sum.inl j) 1)
    simpa [polar_quadMinus, Pi.single_apply] using this
  have hB : ∀ j : Fin (n - 1), w (Sum.inl j) = 0 := fun j => by
    have := h (Pi.single (Sum.inr (Sum.inl j)) 1)
    simpa [polar_quadMinus, Pi.single_apply] using this
  have hU : w (Sum.inr (Sum.inr 0)) = 0 := by
    have := h (Pi.single (Sum.inr (Sum.inr 1)) 1)
    have h' : b * w (Sum.inr (Sum.inr 0)) = 0 := by
      simpa [polar_quadMinus, Pi.single_apply, h2] using this
    exact (mul_eq_zero.1 h').resolve_left hb
  have hV : w (Sum.inr (Sum.inr 1)) = 0 := by
    have := h (Pi.single (Sum.inr (Sum.inr 0)) 1)
    have h' : b * w (Sum.inr (Sum.inr 1)) = 0 := by
      simpa [polar_quadMinus, Pi.single_apply, h2] using this
    exact (mul_eq_zero.1 h').resolve_left hb
  funext k
  rcases k with j | j | j
  · exact hB j
  · exact hA j
  · fin_cases j
    · exact hU
    · exact hV

theorem lh_minus_b_ne [Finite K] [CharP K 2] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    b ≠ 0 := by
  intro hb
  have hinj : Function.Injective (fun s : K => s ^ 2) := by
    intro s t hst
    have hst' : s ^ 2 = t ^ 2 := hst
    have h : (s - t) * (s - t) = 0 := by
      linear_combination hst' + (t * (t - s)) * (CharTwo.two_eq_zero : (2 : K) = 0)
    exact sub_eq_zero.1 (mul_self_eq_zero.1 h)
  obtain ⟨s, hs⟩ := (Finite.injective_iff_surjective.1 hinj) c
  have hs' : s ^ 2 = c := hs
  exact hirr s (by rw [hb, zero_mul, add_zero, hs', CharTwo.add_self_eq_zero])

theorem lh_minus_v0_ne {n : ℕ} (b c : K) (hn : 4 ≤ n) :
    quadMinus n K b c (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin (n - 1))) (1 : K) +
      Pi.single (Sum.inr (Sum.inl (⟨0, by omega⟩ : Fin (n - 1)))) 1) ≠ 0 := by
  rw [quadMinus_apply]
  simp [Pi.single_apply]

theorem lh_minus_perp_single {n : ℕ} {b c : K}
    (W : Submodule K (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K))
    (hW : ∀ w ∈ W, ∀ k, w (Sum.inr k) = 0) (j : Fin (n - 1)) :
    Pi.single (Sum.inl j) (1 : K) ∈ lh_perp (quadMinus n K b c) W := by
  refine lh_mem_perp.2 (fun w hw => ?_)
  rw [polar_quadMinus]
  simp [Pi.single_apply, hW w hw]

theorem lh_minus_perp_f {n : ℕ} {b c : K}
    (W : Submodule K (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K)) (m : Fin (n - 1))
    (hW : ∀ w ∈ W, w (Sum.inl m) = 0) :
    Pi.single (Sum.inr (Sum.inl m)) (1 : K) ∈ lh_perp (quadMinus n K b c) W := by
  refine lh_mem_perp.2 (fun w hw => ?_)
  rw [polar_quadMinus]
  simp [Pi.single_apply, hW w hw]

theorem lh_minus_polar_ef {n : ℕ} {b c : K} (m : Fin (n - 1)) :
    polar (quadMinus n K b c) (Pi.single (Sum.inl m) (1 : K))
      (Pi.single (Sum.inr (Sum.inl m)) 1) ≠ 0 := by
  rw [polar_quadMinus]
  simp [Pi.single_apply]

theorem lh_frameX_gen {m : ℕ} {κ : Type} [DecidableEq κ] (hm : 3 ≤ m) {u : Fin m ⊕ κ → K}
    (hu : ∀ k : κ, u (Sum.inr k) = 0) (hu0 : u ≠ 0) :
    ∃ j1 j2 : Fin m, j1 ≠ j2 ∧ ∀ a b c : K,
      a • u + b • Pi.single (Sum.inl j1) (1 : K) + c • Pi.single (Sum.inl j2) (1 : K) = 0 →
        a = 0 ∧ b = 0 ∧ c = 0 := by
  obtain ⟨k, hk⟩ : ∃ k : Fin m, u (Sum.inl k) ≠ 0 := by
    by_contra h
    push Not at h
    apply hu0
    funext v
    rcases v with k | k
    · exact h k
    · exact hu k
  have hcard : 1 < (Finset.univ.erase k).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨j1, hj1, j2, hj2, hj12⟩ := Finset.one_lt_card.1 hcard
  rw [Finset.mem_erase] at hj1 hj2
  refine ⟨j1, j2, hj12, fun a b c h => ?_⟩
  have ha : a = 0 := by
    have hk' := congrFun h (Sum.inl k)
    have h1 : a * u (Sum.inl k) = 0 := by
      simpa [Pi.single_apply, hj1.1, hj2.1] using hk'
    exact (mul_eq_zero.1 h1).resolve_right hk
  subst ha
  have hb := congrFun h (Sum.inl j1)
  have hc := congrFun h (Sum.inl j2)
  simp [Pi.single_apply, hj12, Ne.symm hj12] at hb hc
  exact ⟨rfl, hb, hc⟩

theorem lh_minus_frame {n : ℕ} {b c : K} (hn : 4 ≤ n) (i : Fin (n - 1)) :
    ∀ u ∈ OrthogonalTail.tailModelFlag (n - 1) K (Fin 2) i, u ≠ 0 →
      ∃ y ∈ lh_perp (quadMinus n K b c) (OrthogonalTail.tailModelFlag (n - 1) K (Fin 2) i),
      ∃ y' ∈ lh_perp (quadMinus n K b c) (OrthogonalTail.tailModelFlag (n - 1) K (Fin 2) i),
        ∀ a b c : K, a • u + b • y + c • y' = 0 → a = 0 ∧ b = 0 ∧ c = 0 := by
  intro u hu hu0
  obtain ⟨j1, j2, -, hind⟩ :=
    lh_frameX_gen (by omega : 3 ≤ n - 1) (fun k => (lh_tail_props i u hu).1 k) hu0
  exact ⟨_, lh_minus_perp_single _ (fun w hw => (lh_tail_props i w hw).1) j1, _,
    lh_minus_perp_single _ (fun w hw => (lh_tail_props i w hw).1) j2, hind⟩

theorem lh_minus_lam {n : ℕ} {b c : K} (hn : 4 ≤ n) (i : Fin (n - 1)) :
    (∃ v ∈ lh_perp (quadMinus n K b c) (OrthogonalTail.tailModelFlag (n - 1) K (Fin 2) i),
      ∃ v' ∈ lh_perp (quadMinus n K b c) (OrthogonalTail.tailModelFlag (n - 1) K (Fin 2) i),
        polar (quadMinus n K b c) v v' ≠ 0) ∨
    (∀ u ∈ OrthogonalTail.tailModelFlag (n - 1) K (Fin 2) i, u ≠ 0 →
      ∃ y ∈ OrthogonalTail.tailModelFlag (n - 1) K (Fin 2) i,
      ∃ y' ∈ OrthogonalTail.tailModelFlag (n - 1) K (Fin 2) i,
        ∀ a b c : K, a • u + b • y + c • y' = 0 → a = 0 ∧ b = 0 ∧ c = 0) := by
  have hiv : (i : ℕ) < n - 1 := i.isLt
  by_cases hi : (i : ℕ) < n - 2
  · left
    have hm : i < (⟨n - 2, by omega⟩ : Fin (n - 1)) := by
      rw [Fin.lt_def]
      exact hi
    exact ⟨_, lh_minus_perp_single _ (fun w hw => (lh_tail_props i w hw).1) _, _,
      lh_minus_perp_f _ _ (fun w hw => (lh_tail_props i w hw).2 _ hm), lh_minus_polar_ef _⟩
  · right
    intro u hu hu0
    obtain ⟨j1, j2, -, hind⟩ :=
      lh_frameX_gen (by omega : 3 ≤ n - 1) (fun k => (lh_tail_props i u hu).1 k) hu0
    have hj : ∀ j : Fin (n - 1), j ≤ i := fun j => by
      rw [Fin.le_iff_val_le_val]
      have := j.isLt
      omega
    exact ⟨_, lh_tail_single_mem i j1 (hj j1), _, lh_tail_single_mem i j2 (hj j2), hind⟩

end MinusFacts

theorem pOmegaMinusCharTwo_char2 {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} (b c : K)
    (hn : 4 ≤ n) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (i : Fin (n - 1)) :
    CharTwo (statedProjectiveSubspaceStabilizer (StatedQuadMinus n K b c)
      (OrthogonalTail.tailModelFlag (n - 1) K (Fin 2) i)) := by
  have hb : b ≠ 0 := lh_minus_b_ne hirr
  have hQ : ⇑(quadMinus n K b c) = StatedQuadMinus n K b c := coe_quadMinus n K b c
  have hv0 := lh_minus_v0_ne (K := K) b c hn
  haveI : Finite (StatedProj (StatedOmega (StatedQuadMinus n K b c))) := inferInstance
  have hE := commutator_orthogonalGroup_quadMinus hn hirr
  have hstab : (MulAction.stabilizer ((Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) ≃ₗ[K]
      (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K))
        (OrthogonalTail.tailModelFlag (n - 1) K (Fin 2) i)).comap (lh_rho hQ hv0) =
      statedProjectiveSubspaceStabilizer (StatedQuadMinus n K b c)
        (OrthogonalTail.tailModelFlag (n - 1) K (Fin 2) i) := by
    ext x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ x
    exact Iff.rfl
  rw [← hstab]
  refine lh_charTwo_of_faithful (Q := quadMinus n K b c)
    (W := OrthogonalTail.tailModelFlag (n - 1) K (Fin 2) i) (lh_rho hQ hv0)
    (lh_rho_injective hQ hv0) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro γ
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ γ
    exact lh_toLin_mem_orth hQ g.2
  · intro u hu y hy
    have hmem : (toLinEquiv (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K).symm
        (eichler (quadMinus n K b c) u y) ∈ StatedOmega (StatedQuadMinus n K b c) := by
      rw [statedOmega_eq_map_elementaryGroup hQ hE]
      exact Subgroup.mem_map_of_mem _ (eichler_mem_elementaryGroup _ u y)
    exact ⟨QuotientGroup.mk ⟨_, hmem⟩, (toLinEquiv _ K).apply_symm_apply _⟩
  · exact fun w h => lh_minus_nd hb w h
  · exact fun w hw => lh_tail_sing i w hw
  · refine ⟨Pi.single (Sum.inl (⟨0, by omega⟩ : Fin (n - 1))) (1 : K),
      lh_tail_single_mem i _ (Fin.le_iff_val_le_val.2 (Nat.zero_le _)), ?_⟩
    intro h
    have h0 := congrFun h (Sum.inl (⟨0, by omega⟩ : Fin (n - 1)))
    simp at h0
  · exact lh_minus_frame hn i
  · exact lh_minus_lam hn i

theorem pOmegaMinusCharTwo_holds_char2 :
    ∀ (n : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K), 4 ≤ n →
      (∀ s : K, s ^ 2 + b * s + c ≠ 0) → ∀ i : Fin (n - 1),
        CharTwo (statedProjectiveSubspaceStabilizer (StatedQuadMinus n K b c)
          (OrthogonalTail.tailModelFlag (n - 1) K (Fin 2) i)) := by
  intro n K _ _ _ b c hn hirr i
  exact pOmegaMinusCharTwo_char2 b c hn hirr i

theorem pOmegaMinusCharTwo_holds : POmegaMinusCharTwo :=
  pOmegaMinusCharTwo_holds_char2

end CFSG.Quasithin.LieOver
