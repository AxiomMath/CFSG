module

public import CFSG.HardMathSupport.Curtis.Coordinator.PerfThreeOrthPieces
public import CFSG.ClassicalGroups.Orthogonal.Basic
public import Mathlib.GroupTheory.Nilpotent

public section

open scoped commutatorElement

namespace CFSG.HardMathSupport.Curtis.Coordinator

open Module

theorem exists_central_commutator_order_three {G : Type*} [Group G] [Finite G] (hG : IsPGroup 3 G)
    (hnc : ¬ ∀ g h : G, g * h = h * g) :
    ∃ z : G, z ≠ 1 ∧ z ^ 3 = 1 ∧ z ∈ Subgroup.center G ∧
      z ∈ ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hnil : Group.IsNilpotent G := hG.isNilpotent
  set H : Subgroup G := ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ with hH
  have hHbot : H ≠ ⊥ := by
    intro hbot
    apply hnc
    intro g h
    have h1 : ⁅g, h⁆ ∈ H := Subgroup.commutator_mem_commutator (Subgroup.mem_top g)
      (Subgroup.mem_top h)
    rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_commute] at h1
    exact h1
  obtain ⟨z₀, hz₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hHbot))
  have hz₀H : (z₀ : G) ∈ H := (Subgroup.mem_inf.mp z₀.2).1
  have hz₀C : (z₀ : G) ∈ Subgroup.center G := (Subgroup.mem_inf.mp z₀.2).2
  have hne : (z₀ : G) ≠ 1 := fun h => hz₀1 (Subtype.ext h)
  obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp hG) (z₀ : G)
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hne (orderOf_eq_one_iff.mp (by simpa using hm))
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  refine ⟨(z₀ : G) ^ 3 ^ m', ?_, ?_, ?_, ?_⟩
  · intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hm] at this
    have h2 : 3 ^ (m' + 1) ∣ 3 ^ m' := this
    have := Nat.le_of_dvd (by positivity) h2
    have : 3 ^ m' < 3 ^ (m' + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  · rw [← pow_mul, ← pow_succ]
    rw [← hm]
    exact pow_orderOf_eq_one _
  · exact Subgroup.pow_mem _ hz₀C _
  · exact Subgroup.pow_mem _ hz₀H _

theorem card_modEq_fixed_three {α : Type*} [Finite α] (f : α → α) (hf : ∀ x, f (f (f x)) = x) :
    Nat.card α ≡ Nat.card {x // f x = x} [MOD 3] := by
  classical
  have : Fintype α := Fintype.ofFinite α
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let F : Function.End α := f
  have hf3 : F ^ 3 ^ 1 = 1 := by
    funext x
    simp only [pow_succ, pow_zero, one_mul]
    exact hf x
  have h := Equiv.Perm.card_fixedPoints_modEq (p := 3) (n := 1) hf3
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at h
  exact h

section Decomp

variable {K V : Type*} [Field K] [CharP K 2] [AddCommGroup V] [Module K V]

omit [CharP K 2] in
theorem add_self_eq_zero'' [CharP K 2] (v : V) : v + v = 0 := by
  rw [← two_smul K v, CharTwo.two_eq_zero (R := K), zero_smul]

@[expose] def fixSub (z : V ≃ₗ[K] V) : Submodule K V where
  carrier := {v | z v = v}
  add_mem' := fun {a b} ha hb => by
    simp only [Set.mem_ofPred_eq] at *
    rw [map_add, ha, hb]
  zero_mem' := by simp
  smul_mem' := fun c v hv => by
    simp only [Set.mem_ofPred_eq] at *
    rw [map_smul, hv]

@[expose] def comSub (z : V ≃ₗ[K] V) : Submodule K V where
  carrier := {v | z (z v) + z v + v = 0}
  add_mem' := fun {a b} ha hb => by
    simp only [Set.mem_ofPred_eq] at *
    have : z (z (a + b)) + z (a + b) + (a + b) = (z (z a) + z a + a) + (z (z b) + z b + b) := by
      simp only [map_add]
      abel
    rw [this, ha, hb, add_zero]
  zero_mem' := by simp
  smul_mem' := fun c v hv => by
    simp only [Set.mem_ofPred_eq] at *
    have : z (z (c • v)) + z (c • v) + c • v = c • (z (z v) + z v + v) := by
      simp only [map_smul, smul_add]
    rw [this, hv, smul_zero]

omit [CharP K 2] in
theorem mem_fixSub {z : V ≃ₗ[K] V} {v : V} : v ∈ fixSub z ↔ z v = v := Iff.rfl

omit [CharP K 2] in
theorem mem_comSub {z : V ≃ₗ[K] V} {v : V} : v ∈ comSub z ↔ z (z v) + z v + v = 0 := Iff.rfl

theorem isCompl_fixSub_comSub {z : V ≃ₗ[K] V} (hz : z ^ 3 = 1) : IsCompl (fixSub z) (comSub z) := by
  have hz3 : ∀ v, z (z (z v)) = v := fun v => by
    have : (z ^ 3) v = z (z (z v)) := by simp [pow_succ, LinearEquiv.mul_apply]
    rw [← this, hz]
    rfl
  have hadd : ∀ x : V, x + x = 0 := add_self_eq_zero'' (K := K)
  constructor
  · rw [Submodule.disjoint_def]
    intro v h1 h2
    rw [mem_fixSub] at h1
    rw [mem_comSub, h1, h1] at h2
    have : v + v + v = v := by rw [hadd v, zero_add]
    rw [this] at h2
    exact h2
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    have hc : z (z v) + z v + v ∈ fixSub z := by
      rw [mem_fixSub]
      simp only [map_add, hz3]
      abel
    have hd : z (z v) + z v ∈ comSub z := by
      rw [mem_comSub]
      have e1 : z (z (z v) + z v) = v + z (z v) := by rw [map_add, hz3]
      have e2 : z (z (z (z v) + z v)) = z v + v := by rw [e1, map_add, hz3]
      rw [e2, e1]
      linear_combination (norm := module) hadd v + hadd (z v) + hadd (z (z v))
    have hv : v = (z (z v) + z v + v) + (z (z v) + z v) := by
      have := hadd (z (z v) + z v)
      calc v = v + (z (z v) + z v + (z (z v) + z v)) := by rw [this, add_zero]
        _ = _ := by abel
    rw [hv]
    exact Submodule.add_mem_sup hc hd

end Decomp

section Quad

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {K V : Type*} [Field K] [CharP K 2] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem polar_fixSub_comSub {z : V ≃ₗ[K] V}
    (hzO : z ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {c v : V} (hc : c ∈ fixSub z)
    (hv : v ∈ comSub z) : polar Q c v = 0 := by
  rw [mem_fixSub] at hc
  rw [mem_comSub] at hv
  have hv' : z (z v) + z v = v :=
    add_right_cancel (hv.trans (add_self_eq_zero'' (K := K) v).symm)
  have h1 : ∀ x, polar Q c (z x) = polar Q c x := fun x => by
    have := polar_map_of_mem hzO c x
    rwa [hc] at this
  calc polar Q c v = polar Q c (z (z v) + z v) := by rw [hv']
    _ = polar Q c (z (z v)) + polar Q c (z v) := polar_add_right Q _ _ _
    _ = 0 := by
      rw [h1 (z v)]
      exact CharTwo.add_self_eq_zero _

theorem eq_zero_of_polar_fixSub {z : V ≃ₗ[K] V}
    (hzO : z ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hz : z ^ 3 = 1)
    (hQ : (polarBilin Q).Nondegenerate) {c : V} (hc : c ∈ fixSub z)
    (h : ∀ c' ∈ fixSub z, polar Q c c' = 0) : c = 0 := by
  apply eq_zero_of_polar_eq_zero hQ
  intro x
  have hx : x ∈ fixSub z ⊔ comSub z := by
    rw [(isCompl_fixSub_comSub hz).sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
  rw [polar_add_right, h a ha, polar_fixSub_comSub hzO hc hb, add_zero]

omit [CharP K 2] in
theorem map_fixSub_le {z g : V ≃ₗ[K] V} (hzg : g * z = z * g) {c : V} (hc : c ∈ fixSub z) :
    g c ∈ fixSub z := by
  rw [mem_fixSub] at *
  have : z (g c) = g (z c) := by
    have := congrArg (fun f : V ≃ₗ[K] V => f c) hzg
    exact this.symm
  rw [this, hc]

omit [CharP K 2] in
theorem map_comSub_le {z g : V ≃ₗ[K] V} (hzg : g * z = z * g) {c : V} (hc : c ∈ comSub z) :
    g c ∈ comSub z := by
  rw [mem_comSub] at *
  have h1 : ∀ x, z (g x) = g (z x) := fun x => (congrArg (fun f : V ≃ₗ[K] V => f x) hzg).symm
  rw [h1, h1, ← map_add, ← map_add, hc, map_zero]

end Quad

section Main

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {K V : Type} [Field K] [CharP K 2] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

omit [CharP K 2] [Finite K] [FiniteDimensional K V] in
theorem pow_three_apply {z : V ≃ₗ[K] V} (hz : z ^ 3 = 1) (v : V) : z (z (z v)) = v := by
  have : (z ^ 3) v = z (z (z v)) := by simp [pow_succ, LinearEquiv.mul_apply]
  rw [← this, hz]
  rfl

theorem no_singular_in_fixed (hK : Nat.card K = 2) {z : V ≃ₗ[K] V}
    (hzO : z ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hz : z ^ 3 = 1)
    (hQ : (polarBilin Q).Nondegenerate) (hcount : Nat.card {v : V // Q v = 0} % 3 = 1)
    (hCdim : finrank K (fixSub z) ≤ 2) : ∀ c ∈ fixSub z, Q c = 0 → c = 0 := by
  classical
  have hfinV : Finite V := Module.finite_of_finite K
  have hz3 := pow_three_apply hz
  let f : {v : V // Q v = 0} → {v : V // Q v = 0} :=
    fun s => ⟨z s.1, by rw [map_of_mem hzO]; exact s.2⟩
  have hf : ∀ x, f (f (f x)) = x := fun x => Subtype.ext (hz3 x.1)
  have hmod := card_modEq_fixed_three f hf
  have hF : Nat.card {x // f x = x} % 3 = 1 := by
    rw [Nat.ModEq] at hmod
    rw [← hmod]
    exact hcount
  let φ : {x // f x = x} → ↥(fixSub z) := fun s => ⟨s.1.1, congrArg Subtype.val s.2⟩
  have hφ : Function.Injective φ := by
    intro a b h
    have h' : a.1.1 = b.1.1 := congrArg (fun t : ↥(fixSub z) => (t : V)) h
    exact Subtype.ext (Subtype.ext h')
  have hCcard : Nat.card ↥(fixSub z) ≤ 4 := by
    rw [Module.natCard_eq_pow_finrank (K := K), hK]
    calc 2 ^ finrank K (fixSub z) ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hCdim
      _ = 4 := by norm_num
  have hFle : Nat.card {x // f x = x} ≤ 4 :=
    (Nat.card_le_card_of_injective φ hφ).trans hCcard
  intro c hc hQc
  by_contra hc0
  have hFc : f ⟨c, hQc⟩ = ⟨c, hQc⟩ := Subtype.ext (mem_fixSub.mp hc)
  have hF0 : f ⟨0, by simp⟩ = ⟨0, by simp⟩ := Subtype.ext (map_zero z)
  have h2 : 2 ≤ Nat.card {x // f x = x} := by
    have : 1 < Nat.card {x // f x = x} := by
      rw [Finite.one_lt_card_iff_nontrivial]
      refine ⟨⟨⟨⟨c, hQc⟩, hFc⟩, ⟨⟨0, by simp⟩, hF0⟩, ?_⟩⟩
      intro h
      exact hc0 (congrArg (fun x => x.1.1) h)
    omega
  have hF4 : Nat.card {x // f x = x} = 4 := by omega
  have hbij : Function.Bijective φ := hφ.bijective_of_nat_card_le (by rw [hF4]; exact hCcard)
  have hall : ∀ c' ∈ fixSub z, Q c' = 0 := by
    intro c' hc'
    obtain ⟨s, hs⟩ := hbij.2 ⟨c', hc'⟩
    have h' : s.1.1 = c' := congrArg (fun t : ↥(fixSub z) => (t : V)) hs
    rw [← h']
    exact s.1.2
  apply hc0
  refine eq_zero_of_polar_fixSub hzO hz hQ hc fun c' hc' => ?_
  have hcc' : c + c' ∈ fixSub z := (fixSub z).add_mem hc hc'
  rw [polar, hall _ hcc', hQc, hall _ hc', sub_zero, sub_zero]

omit [CharP K 2] [Finite K] [FiniteDimensional K V] in
theorem map_eq_of_invariant {E : Subgroup (V ≃ₗ[K] V)} {A : Submodule K V}
    (h : ∀ g ∈ E, ∀ a ∈ A, g a ∈ A) {g : V ≃ₗ[K] V} (hg : g ∈ E) :
    A.map (g : V ≃ₗ[K] V).toLinearMap = A := by
  apply le_antisymm
  · rintro _ ⟨a, ha, rfl⟩
    exact h g hg a ha
  · intro x hx
    refine ⟨g⁻¹ x, h g⁻¹ (E.inv_mem hg) x hx, ?_⟩
    change g (g⁻¹ x) = x
    exact LinearEquiv.apply_inv_apply' g x

theorem commutative_of_three_subgroup (hK : Nat.card K = 2) (hQ : (polarBilin Q).Nondegenerate)
    (hdim : finrank K V = 8) (hcount : Nat.card {v : V // Q v = 0} % 3 = 1)
    {E : Subgroup (V ≃ₗ[K] V)} (hEO : E ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hE3 : IsPGroup 3 E) {W : Submodule K V} (hW0 : W ≠ ⊥) (hWQ : ∀ w ∈ W, Q w = 0)
    (hWE : ∀ g ∈ E, ∀ w ∈ W, g w ∈ W) : ∀ g ∈ E, ∀ h ∈ E, g * h = h * g := by
  classical
  have hfinV : Finite V := Module.finite_of_finite K
  have hfinAut : Finite (V ≃ₗ[K] V) :=
    Finite.of_injective (fun g : V ≃ₗ[K] V => (g : V → V)) DFunLike.coe_injective
  have hfinE : Finite E := inferInstance
  by_contra hnc
  have hnc' : ¬ ∀ g h : E, g * h = h * g := by
    intro hall
    apply hnc
    intro g hg h hh
    exact congrArg Subtype.val (hall ⟨g, hg⟩ ⟨h, hh⟩)
  obtain ⟨z, hz1, hz3, hzC, hzK⟩ := exists_central_commutator_order_three hE3 hnc'
  have hζ3 : (z : V ≃ₗ[K] V) ^ 3 = 1 := by
    have := congrArg Subtype.val hz3
    simpa using this
  have hζ1 : (z : V ≃ₗ[K] V) ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hζE : (z : V ≃ₗ[K] V) ∈ E := z.2
  have hζO := hEO hζE
  have hcomm : ∀ g ∈ E, g * (z : V ≃ₗ[K] V) = (z : V ≃ₗ[K] V) * g := by
    intro g hg
    have := Subgroup.mem_center_iff.mp hzC ⟨g, hg⟩
    exact congrArg Subtype.val this
  have hCinv : ∀ g ∈ E, ∀ c ∈ fixSub (z : V ≃ₗ[K] V), g c ∈ fixSub (z : V ≃ₗ[K] V) :=
    fun g hg c hc => map_fixSub_le (hcomm g hg) hc
  have hV'inv : ∀ g ∈ E, ∀ c ∈ comSub (z : V ≃ₗ[K] V), g c ∈ comSub (z : V ≃ₗ[K] V) :=
    fun g hg c hc => map_comSub_le (hcomm g hg) hc
  have hcompl := isCompl_fixSub_comSub hζ3
  have hdimsum := Submodule.finrank_add_eq_of_isCompl hcompl
  by_cases hd' : finrank K (comSub (z : V ≃ₗ[K] V)) ≤ 5
  ·
    have h := commutator_apply_sub_mem hK hE3 (A := ⊥) (B := comSub (z : V ≃ₗ[K] V)) bot_le
      (fun g _ => Submodule.map_bot _) (fun g hg => map_eq_of_invariant hV'inv hg)
      (by rw [finrank_bot]; omega) hzK
    have hV'0 : comSub (z : V ≃ₗ[K] V) = ⊥ := by
      rw [eq_bot_iff]
      intro b hb
      have h1 : (z : V ≃ₗ[K] V) b - b ∈ (⊥ : Submodule K V) := h b hb
      rw [Submodule.mem_bot, sub_eq_zero] at h1
      exact (Submodule.disjoint_def.mp hcompl.1) b h1 hb
    apply hζ1
    apply LinearEquiv.ext
    intro v
    have hv : v ∈ fixSub (z : V ≃ₗ[K] V) ⊔ comSub (z : V ≃ₗ[K] V) := by
      rw [hcompl.sup_eq_top]
      exact Submodule.mem_top
    rw [hV'0, sup_bot_eq] at hv
    exact mem_fixSub.mp hv
  · push Not at hd'
    have hCdim : finrank K (fixSub (z : V ≃ₗ[K] V)) ≤ 2 := by omega
    have hnosing := no_singular_in_fixed hK hζO hζ3 hQ hcount hCdim
    have hW2 : 2 ≤ finrank K W := by
      by_contra hlt
      push Not at hlt
      have hpos : 1 ≤ finrank K W := Submodule.one_le_finrank_iff.mpr hW0
      have h1 : finrank K W = 1 := by omega
      obtain ⟨w₀, hw₀, hw⟩ := finrank_eq_one_iff'.mp h1
      obtain ⟨c, hc⟩ := hw ⟨(z : V ≃ₗ[K] V) w₀, hWE _ hζE w₀ w₀.2⟩
      have hc' : (z : V ≃ₗ[K] V) (w₀ : V) = c • (w₀ : V) := (congrArg Subtype.val hc).symm
      rcases eq_zero_or_one_of_card_two hK c with rfl | rfl
      · rw [zero_smul] at hc'
        apply hw₀
        apply Subtype.ext
        exact (z : V ≃ₗ[K] V).injective (by rw [hc']; simp)
      · rw [one_smul] at hc'
        apply hw₀
        exact Subtype.ext (hnosing _ (mem_fixSub.mpr hc') (hWQ _ w₀.2))
    set Wp : Submodule K V := LinearMap.BilinForm.orthogonal (polarBilin Q) W with hWp
    have hWWp : W ≤ Wp := by
      intro w hw
      rw [hWp, LinearMap.BilinForm.mem_orthogonal_iff]
      intro n hn
      rw [polarBilin_apply_apply, polar, hWQ _ (W.add_mem hn hw), hWQ _ hn, hWQ _ hw]
      simp
    have hWpdim : finrank K Wp = 8 - finrank K W := by
      rw [hWp, LinearMap.BilinForm.finrank_orthogonal hQ W, hdim]
    have hWpinv : ∀ g ∈ E, ∀ y ∈ Wp, g y ∈ Wp := by
      intro g hg y hy
      rw [hWp, LinearMap.BilinForm.mem_orthogonal_iff] at *
      intro n hn
      have hgO := hEO hg
      have hn' : g⁻¹ n ∈ W := hWE g⁻¹ (E.inv_mem hg) n hn
      have := hy _ hn'
      rw [polarBilin_apply_apply] at this ⊢
      have h2 := polar_map_of_mem hgO (g⁻¹ n) y
      rw [LinearEquiv.apply_inv_apply' g n] at h2
      rw [h2, this]
    have hd4 : finrank K W ≤ 4 := by
      have := Submodule.finrank_mono hWWp
      omega
    have hA1 := commutator_apply_sub_mem hK hE3 (A := Wp) (B := ⊤) le_top
      (fun g hg => map_eq_of_invariant hWpinv hg)
      (fun g hg => map_eq_of_invariant (fun g _ a _ => Submodule.mem_top) hg)
      (by rw [finrank_top, hdim, hWpdim]; omega) hzK
    have hA2 := commutator_apply_sub_mem hK hE3 (A := W) (B := Wp) hWWp
      (fun g hg => map_eq_of_invariant hWE hg) (fun g hg => map_eq_of_invariant hWpinv hg)
      (by rw [hWpdim]; omega) hzK
    have hA3 := commutator_apply_sub_mem hK hE3 (A := ⊥) (B := W) bot_le
      (fun g _ => Submodule.map_bot _) (fun g hg => map_eq_of_invariant hWE hg)
      (by rw [finrank_bot]; omega) hzK
    apply hζ1
    refine eq_one_of_chain hK (k := 1) (by simpa using hζ3) (U₁ := W) (U₂ := Wp)
      (fun v => hA1 v Submodule.mem_top) hA2 ?_
    intro u hu
    have := hA3 u hu
    rw [Submodule.mem_bot, sub_eq_zero] at this
    exact this

end Main

end CFSG.HardMathSupport.Curtis.Coordinator
