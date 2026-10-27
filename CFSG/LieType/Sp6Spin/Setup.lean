module

public import CFSG.LieType.TorusWeights.RootOp
public import CFSG.LieType.Sp6Spin.Sp6
public import CFSG.LieType.Sp6Spin.Orbits

public section

namespace CFSG.LieType.Sp6Spin

open CFSG.LieType.TorusWeights CFSG.LieType.Universal.Symplectic
  CFSG.LieType.Universal.Symplectic.SpExtras CFSG.Assembly.LowTwoRank TauCeti.GLSymplecticFin
  QuadraticMap

attribute [local instance] Fintype.ofFinite Classical.propDecidable

@[expose] noncomputable def rootWt (K : Type) [Field K] [Finite K] (r : RootSubgroupIndex 3) :
    Fin 3 → ZMod (Nat.card Kˣ) :=
  castW (Nat.card Kˣ) (stdVec r)

@[expose] def spinWt {N : ℕ} (x : ZMod N) (σ : Fin 3 → Bool) : Fin 3 → ZMod N :=
  fun i => if σ i then x else -x

structure SpinSetting (K : Type) [Field K] [Finite K] [CharP K 2] (V : Type) [AddCommGroup V]
    [Module K V] where
  card_le : 4 ≤ Nat.card K
  finrank_eq : Module.finrank K V = 8
  Q : QuadraticForm K V
  nondeg : (QuadraticMap.polarBilin Q).Nondegenerate
  ψ : StatedSp 3 K →* (V ≃ₗ[K] V)
  map_Q : ∀ g v, Q (ψ g v) = Q v
  irred : ∀ W : Submodule K V, (∀ g, ∀ w ∈ W, ψ g w ∈ W) → W = ⊥ ∨ W = ⊤

namespace SpinSetting

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  (S : SpinSetting K V)

include S in
theorem finiteDimensional : FiniteDimensional K V :=
  Module.finite_of_finrank_pos (by rw [S.finrank_eq]; norm_num)

@[expose] noncomputable def ρ : Representation K (StatedSp 3 K) V :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp S.ψ

theorem ρ_apply (g : StatedSp 3 K) (v : V) : S.ρ g v = S.ψ g v := by
  rw [ρ, MonoidHom.comp_apply]
  rfl

@[expose] noncomputable def X (a : Fin 3 → ZMod (Nat.card Kˣ)) : Submodule K V :=
  wtSpace (diagHom 3 K) S.ρ a

theorem mem_X {a : Fin 3 → ZMod (Nat.card Kˣ)} {v : V} :
    v ∈ S.X a ↔ ∀ t : Fin 3 → Kˣ, S.ψ (diagHom 3 K t) v = (wtChar a t : K) • v := by
  simp only [X, mem_wtSpace, ρ_apply]

@[expose] noncomputable def mult (a : Fin 3 → ZMod (Nat.card Kˣ)) : ℕ :=
  Module.finrank K (S.X a)

@[expose] noncomputable def A (r : RootSubgroupIndex 3) (k : ℕ) : Module.End K V :=
  rootOp S.ρ (elt (F := K) r) k

structure IsSpinPattern (S : SpinSetting K V) (x : ZMod (Nat.card Kˣ)) : Prop where
  ne_zero : x ≠ 0
  mult_eq : ∀ a, S.mult a = if ∀ i, a i = x ∨ a i = -x then 1 else 0

theorem hconj (r : RootSubgroupIndex 3) (t : Fin 3 → Kˣ) (c : K) :
    diagHom 3 K t * elt r c * (diagHom 3 K t)⁻¹ = elt r ((wtChar (rootWt K r) t : K) * c) := by
  rw [diagHom_conj_elt]
  congr 1
  simp only [rootWt, wtChar_castW]

theorem A_mem (r : RootSubgroupIndex 3) {a : Fin 3 → ZMod (Nat.card Kˣ)} {v : V}
    (hv : v ∈ S.X a) (k : ℕ) :
    S.A r k v ∈ S.X (a + (k : ZMod (Nat.card Kˣ)) • rootWt K r) := by
  simp only [X, A] at hv ⊢
  exact rootOp_mem_wtSpace (diagHom 3 K) S.ρ (elt (F := K) r) (hconj r) hv k

theorem A_mul_card_sub (r : RootSubgroupIndex 3) {i : ℕ} (hi : i ≤ Nat.card Kˣ) :
    S.A r i * S.A r (Nat.card Kˣ - i) = S.A r (Nat.card Kˣ) := by
  simpa only [A] using
    rootOp_mul_card_sub (ρ := S.ρ) (x := elt (F := K) r) (elt_add r) hi

theorem X_eq_bot_iff {a : Fin 3 → ZMod (Nat.card Kˣ)} : S.X a = ⊥ ↔ S.mult a = 0 := by
  haveI := S.finiteDimensional
  exact (Submodule.finrank_eq_zero (S := S.X a)).symm

private theorem polar_map_ψ (g : StatedSp 3 K) (u v : V) :
    polar S.Q (S.ψ g u) (S.ψ g v) = polar S.Q u v := by
  rw [polar, polar, ← (S.ψ g).map_add u v, S.map_Q, S.map_Q, S.map_Q]

private theorem polar_invariant (g : StatedSp 3 K) (u v : V) :
    polarBilin S.Q (S.ρ g u) (S.ρ g v) = polarBilin S.Q u v := by
  rw [polarBilin_apply_apply, polarBilin_apply_apply, ρ_apply, ρ_apply]
  exact S.polar_map_ψ g u v

theorem polar_A (r : RootSubgroupIndex 3) (u v : V) (k : ℕ) :
    polar S.Q (S.A r k u) v = polar S.Q u (S.A r k v) := by
  simpa only [A, polarBilin_apply_apply] using
    bilin_rootOp_left (ρ := S.ρ) (x := elt (F := K) r) (B := polarBilin S.Q)
      S.polar_invariant (elt_add r) u v k

theorem fix_of_A (r : RootSubgroupIndex 3) {v : V}
    (h : ∀ k : ℕ, 1 ≤ k → k ≤ Nat.card Kˣ → S.A r k v = 0) (c : K) :
    S.ψ (elt r c) v = v := by
  rw [← ρ_apply]
  refine (forall_rho_eq_iff (ρ := S.ρ) (x := elt (F := K) r) (elt_zero r) (v := v)).mpr ?_ c
  intro k hk
  by_cases hkN : k ≤ Nat.card Kˣ
  · exact h k hk hkN
  · rw [rootOp_of_lt (ρ := S.ρ) (x := elt (F := K) r) (k := k) (by omega)]
    rfl

theorem fix_of_forall (r : RootSubgroupIndex 3) {a : Fin 3 → ZMod (Nat.card Kˣ)} {v : V}
    (hv : v ∈ S.X a)
    (h : ∀ k : ℕ, 1 ≤ k → k < Nat.card Kˣ →
      S.mult (a + (k : ZMod (Nat.card Kˣ)) • rootWt K r) = 0) (c : K) :
    S.ψ (elt r c) v = v := by
  have hN3 : 3 ≤ Nat.card Kˣ := by
    rw [Nat.card_units]
    have := S.card_le
    omega
  refine S.fix_of_A r ?_ c
  intro k hk1 hkN
  rcases lt_or_eq_of_le hkN with hlt | heq
  · have hmem := S.A_mem r hv k
    rw [(S.X_eq_bot_iff).mpr (h k hk1 hlt)] at hmem
    exact hmem
  · rw [heq, ← S.A_mul_card_sub r (i := 1) (by omega), Module.End.mul_apply]
    have h0 : S.A r (Nat.card Kˣ - 1) v = 0 := by
      have hmem := S.A_mem r hv (Nat.card Kˣ - 1)
      rw [(S.X_eq_bot_iff).mpr (h (Nat.card Kˣ - 1) (by omega) (by omega))] at hmem
      exact hmem
    rw [h0, map_zero]

theorem ψ_lw_mem (k : Fin 3) {a : Fin 3 → ZMod (Nat.card Kˣ)} {v : V} (hv : v ∈ S.X a) :
    S.ψ (lw k) v ∈ S.X (Function.update a k (-a k)) := by
  simp only [X] at hv ⊢
  have h := map_mem_wtSpace (diagHom 3 K) S.ρ (m := lw k)
    (τ := fun t => Function.update t k (t k)⁻¹) (lw_inv_conj_diagHom k)
    (fun t => wtChar_update_inv k a t) hv
  simpa only [ρ_apply] using h

theorem mult_swap (i j : Fin 3) (a : Fin 3 → ZMod (Nat.card Kˣ)) :
    S.mult (a ∘ Equiv.swap i j) = S.mult a := by
  haveI := S.finiteDimensional
  by_cases hij : i = j
  · subst hij
    simp [Equiv.swap_self]
  · refine le_antisymm ?_ ?_
    · exact finrank_wtSpace_le_of_conj (diagHom 3 K) S.ρ (m := sw hij)
        (τ := fun t => t ∘ Equiv.swap i j) (sw_inv_conj_diagHom hij)
        (a := a ∘ Equiv.swap i j) (b := a) (fun t => by
          have hcomp : (a ∘ Equiv.swap i j) ∘ Equiv.swap i j = a := by
            funext x
            simp
          simpa only [Equiv.symm_swap, hcomp] using
            wtChar_comp_perm (Equiv.swap i j) (a ∘ Equiv.swap i j) t)
    · exact finrank_wtSpace_le_of_conj (diagHom 3 K) S.ρ (m := sw hij)
        (τ := fun t => t ∘ Equiv.swap i j) (sw_inv_conj_diagHom hij)
        (a := a) (b := a ∘ Equiv.swap i j) (fun t => by
          simpa only [Equiv.symm_swap] using wtChar_comp_perm (Equiv.swap i j) a t)

theorem mult_neg (i : Fin 3) (a : Fin 3 → ZMod (Nat.card Kˣ)) :
    S.mult (Function.update a i (-a i)) = S.mult a := by
  haveI := S.finiteDimensional
  refine le_antisymm ?_ ?_
  · exact finrank_wtSpace_le_of_conj (diagHom 3 K) S.ρ (m := lw i)
      (τ := fun t => Function.update t i (t i)⁻¹) (lw_inv_conj_diagHom i)
      (a := Function.update a i (-a i)) (b := a) (fun t => by
        rw [wtChar_update_inv]; simp)
  · exact finrank_wtSpace_le_of_conj (diagHom 3 K) S.ρ (m := lw i)
      (τ := fun t => Function.update t i (t i)⁻¹) (lw_inv_conj_diagHom i)
      (a := a) (b := Function.update a i (-a i)) (fun t => wtChar_update_inv i a t)

theorem sum_mult : ∑ a, S.mult a = 8 := by
  haveI := S.finiteDimensional
  have h := finrank_eq_sum_finrank_wtSpace (diagHom 3 K) S.ρ (X := V)
  rw [S.finrank_eq] at h
  convert h.symm using 2 <;> rfl

theorem weight_trichotomy :
    S.mult 0 = 8 ∨
    (∃ x : ZMod (Nat.card Kˣ), x ≠ 0 ∧ S.mult 0 = 2 ∧ ∀ a, a ≠ 0 →
      S.mult a = if ∃ i, a = Pi.single i x ∨ a = Pi.single i (-x) then 1 else 0) ∨
    (∃ x : ZMod (Nat.card Kˣ), x ≠ 0 ∧
      ∀ a, S.mult a = if ∀ i, a i = x ∨ a i = -x then 1 else 0) := by
  haveI : NeZero (Nat.card Kˣ) := ⟨Nat.card_pos.ne'⟩
  exact weight_cases (N := Nat.card Kˣ) (odd_natCard_units (K := K)) S.mult
    S.mult_swap S.mult_neg S.sum_mult

theorem nondeg' (v : V) (h : ∀ w, polar S.Q v w = 0) : v = 0 :=
  S.nondeg.1 v fun w => by
    rw [polarBilin_apply_apply]
    exact h w

theorem polar_eq_zero {a b : Fin 3 → ZMod (Nat.card Kˣ)} (hab : a + b ≠ 0) {u v : V}
    (hu : u ∈ S.X a) (hv : v ∈ S.X b) : polar S.Q u v = 0 := by
  simp only [X] at hu hv
  exact bilin_eq_zero_of_mem_wtSpace (diagHom 3 K) S.ρ (B := polarBilin S.Q)
    S.polar_invariant hab hu hv

theorem exists_polar_eq_one {a : Fin 3 → ZMod (Nat.card Kˣ)} {u : V} (hu : u ∈ S.X a)
    (hu0 : u ≠ 0) : ∃ w ∈ S.X (-a), polar S.Q u w = 1 := by
  have hne : ∃ w : V, polar S.Q u w ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hu0 (S.nondeg' u h)
  obtain ⟨w, hw⟩ := hne
  have hsum : polar S.Q u w =
      ∑ b, polar S.Q u (wtProj (diagHom 3 K) S.ρ b w) := by
    conv_lhs => rw [← sum_wtProj (diagHom 3 K) S.ρ w]
    rw [← polarBilin_apply_apply, map_sum]
    simp only [polarBilin_apply_apply]
  have hterm : polar S.Q u (wtProj (diagHom 3 K) S.ρ (-a) w) ≠ 0 := by
    intro hzero
    apply hw
    rw [hsum]
    refine Finset.sum_eq_zero fun b _ => ?_
    by_cases hb : b = -a
    · rw [hb]; exact hzero
    · refine S.polar_eq_zero ?_ hu (wtProj_mem (diagHom 3 K) S.ρ b w)
      intro h
      have hba : b = -a := by
        rw [eq_neg_iff_add_eq_zero, add_comm]
        exact h
      exact hb hba
  refine ⟨(polar S.Q u (wtProj (diagHom 3 K) S.ρ (-a) w))⁻¹ •
    wtProj (diagHom 3 K) S.ρ (-a) w, ?_, ?_⟩
  · exact (S.X (-a)).smul_mem _ (wtProj_mem (diagHom 3 K) S.ρ (-a) w)
  · rw [polar_smul_right, smul_eq_mul, inv_mul_cancel₀ hterm]

theorem eq_zero_of_fixed {v : V}
    (hshort : ∀ r : RootSubgroupIndex 3, IsShortIndex r → ∀ c : K, S.ψ (elt r c) v = v)
    (hlong : ∀ c : K, S.ψ (elt (.positiveLong 2) c) v = v) : v = 0 := by
  classical
  let T : Set (StatedSp 3 K) :=
    {g | ∃ r : RootSubgroupIndex 3, IsShortIndex r ∧ ∃ c : K, elt r c = g} ∪
      Set.range (elt (n := 3) (F := K) (.positiveLong 2))
  have hclosure : Subgroup.closure T = ⊤ := closure_short_long_eq_top
  let H : Subgroup (StatedSp 3 K) :=
    { carrier := {g | S.ψ g v = v}
      mul_mem' := by
        intro a b ha hb
        show S.ψ (a * b) v = v
        rw [map_mul]
        exact (congrArg (S.ψ a) hb).trans ha
      one_mem' := by simp
      inv_mem' := by
        intro a ha
        show S.ψ a⁻¹ v = v
        rw [map_inv]
        simpa using (congrArg (⇑(S.ψ a)⁻¹) ha).symm }
  have hmem : ∀ g ∈ T, g ∈ H := by
    rintro g (⟨r, hr, c, rfl⟩ | ⟨c, rfl⟩)
    · exact hshort r hr c
    · exact hlong c
  have hle : Subgroup.closure T ≤ H := by
    rw [Subgroup.closure_le]
    exact hmem
  have hHtop : H = ⊤ := by
    rw [eq_top_iff, ← hclosure]
    exact hle
  have hfix : ∀ g : StatedSp 3 K, S.ψ g v = v := by
    intro g
    have hg : g ∈ H := by rw [hHtop]; exact Subgroup.mem_top g
    exact hg
  have hfixW : ∀ g, ∀ w ∈ (Submodule.span K {v} : Submodule K V),
      S.ψ g w ∈ Submodule.span K {v} := by
    intro g w hw
    have hmap : Submodule.map (S.ψ g).toLinearMap (Submodule.span K {v}) =
        Submodule.span K {v} := by
      rw [Submodule.map_span]
      have himg : (S.ψ g).toLinearMap '' ({v} : Set V) = {v} := by
        rw [Set.image_singleton]
        exact congrArg (fun x => ({x} : Set V)) (hfix g)
      rw [himg]
    rw [← hmap]
    exact Submodule.mem_map_of_mem hw
  by_contra hv
  rcases S.irred (Submodule.span K {v}) hfixW with hbot | htop
  · have hvbot : v ∈ (⊥ : Submodule K V) := by
      rw [← hbot]
      exact Submodule.mem_span_singleton_self v
    exact hv (by simpa using hvbot)
  · have h1 : Module.finrank K (Submodule.span K {v}) = 1 := finrank_span_singleton hv
    have h8 : Module.finrank K (Submodule.span K {v}) = 8 := by
      rw [htop, finrank_top, S.finrank_eq]
    omega

end SpinSetting

end CFSG.LieType.Sp6Spin
