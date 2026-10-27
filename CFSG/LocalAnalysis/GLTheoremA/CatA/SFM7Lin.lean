module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public section

namespace CFSG.LocalAnalysis.GLTheoremA.SFM7Lin

open Matrix

variable {K : Type} [Field K] [Finite K]

@[expose] def actV (g : GL (Fin 4) K) (v : Fin 4 → K) : Fin 4 → K :=
  (g : Matrix (Fin 4) (Fin 4) K) *ᵥ v

theorem actV_mul (g h : GL (Fin 4) K) (v : Fin 4 → K) :
    actV (g * h) v = actV g (actV h v) := by
  simp [actV, Units.val_mul, Matrix.mulVec_mulVec]

theorem actV_one (v : Fin 4 → K) : actV (1 : GL (Fin 4) K) v = v := by
  simp [actV]

theorem actV_injective (g : GL (Fin 4) K) : Function.Injective (actV g) := by
  intro x y hxy
  have h := congrArg (actV g⁻¹) hxy
  simpa [← actV_mul, actV_one] using h

abbrev glMulAction : MulAction (GL (Fin 4) K) (Fin 4 → K) where
  smul g v := actV g v
  one_smul v := actV_one v
  mul_smul g h v := actV_mul g h v

@[expose] def fixV (X : Set (GL (Fin 4) K)) : Submodule K (Fin 4 → K) where
  carrier := {v | ∀ g ∈ X, actV g v = v}
  add_mem' := fun {a b} ha hb g hg => by
    simp only [Set.mem_setOf_eq, actV, Matrix.mulVec_add] at ha hb ⊢
    rw [ha g hg, hb g hg]
  zero_mem' := fun g _ => by
    simp [actV]
  smul_mem' := fun c v hv g hg => by
    simp only [Set.mem_setOf_eq, actV, Matrix.mulVec_smul] at hv ⊢
    rw [hv g hg]

theorem mem_fixV {X : Set (GL (Fin 4) K)} {v : Fin 4 → K} : v ∈ fixV X ↔ ∀ g ∈ X, actV g v = v :=
  Iff.rfl

theorem mem_fixV_singleton {g : GL (Fin 4) K} {v : Fin 4 → K} :
    v ∈ fixV ({g} : Set (GL (Fin 4) K)) ↔ actV g v = v := by
  simp [mem_fixV]

@[expose] def StableV (g : GL (Fin 4) K) (F : Submodule K (Fin 4 → K)) : Prop :=
  ∀ v ∈ F, actV g v ∈ F

noncomputable def permV (g : GL (Fin 4) K) (F : Submodule K (Fin 4 → K)) (hF : StableV g F) :
    Equiv.Perm F :=
  Equiv.ofBijective (fun x => ⟨actV g x.1, hF x.1 x.2⟩) (by
    refine Finite.injective_iff_bijective.1 ?_
    intro x y hxy
    apply Subtype.ext
    apply actV_injective g
    exact congrArg Subtype.val hxy)

theorem permV_pow_val (g : GL (Fin 4) K) (F : Submodule K (Fin 4 → K)) (hF : StableV g F) (n : ℕ)
    (x : F) : ((permV g F hF ^ n) x : Fin 4 → K) = actV (g ^ n) x.1 := by
  induction n with
  | zero => simp [actV]
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    change actV g ((permV g F hF ^ n) x : Fin 4 → K) = _
    rw [ih, pow_succ', actV_mul]

theorem permV_pow_eq_one (g : GL (Fin 4) K) (F : Submodule K (Fin 4 → K)) (hF : StableV g F) (n : ℕ)
    (hg : g ^ n = 1) : permV g F hF ^ n = 1 := by
  refine Equiv.ext fun x => ?_
  apply Subtype.ext
  rw [permV_pow_val, hg]
  simp [actV]

theorem card_perm_modEq {X : Type} [Finite X] (σ : Equiv.Perm X) {p : ℕ} [Fact p.Prime]
    (hσ : σ ^ p = 1) : Nat.card X ≡ Nat.card {x // σ x = x} [MOD p] := by
  classical
  haveI := Fintype.ofFinite X
  have h := Equiv.Perm.card_compl_support_modEq (p := p) (n := 1) (σ := σ) (by simpa using hσ)
  have h2 : Nat.card {x // σ x = x} = σ.supportᶜ.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext x
    simp [Equiv.Perm.mem_support]
  rw [h2, Nat.card_eq_fintype_card]
  exact h.symm

theorem perm_fixed_iff (g : GL (Fin 4) K) (F : Submodule K (Fin 4 → K)) (hF : StableV g F) (x : F) :
    permV g F hF x = x ↔ actV g x.1 = x.1 :=
  Subtype.ext_iff

noncomputable def fixEquivV (g : GL (Fin 4) K) (F : Submodule K (Fin 4 → K)) (hF : StableV g F) :
    {x : F // permV g F hF x = x} ≃ ↥(F ⊓ fixV ({g} : Set (GL (Fin 4) K))) where
  toFun x := ⟨x.1.1, Submodule.mem_inf.2 ⟨x.1.2, mem_fixV_singleton.2 ((perm_fixed_iff g F hF x.1).1 x.2)⟩⟩
  invFun y :=
    ⟨⟨y.1, (Submodule.mem_inf.1 y.2).1⟩, (perm_fixed_iff g F hF _).2 (mem_fixV_singleton.1 (Submodule.mem_inf.1 y.2).2)⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv y := by
    apply Subtype.ext
    rfl

theorem eq_one_of_actV (g : GL (Fin 4) K) (h : ∀ v, actV g v = v) : g = 1 := by
  apply Units.ext
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Units.val_one, Matrix.one_mulVec]
  exact h v

theorem arith_three : ∀ d < 4, ∀ e ≤ d, 8 ^ d % 5 = 8 ^ e % 5 → e = d := by decide

theorem arith_four : ∀ f < 5, 1 ≤ f → 8 ^ 4 % 5 = 8 ^ f % 5 → f = 4 := by decide

theorem natCard_submodule (hK : Nat.card K = 8) (W : Submodule K (Fin 4 → K)) :
    Nat.card W = 8 ^ Module.finrank K W := by
  rw [Module.natCard_eq_pow_finrank (K := K) (V := ↥W), hK]

theorem five_fix (hK : Nat.card K = 8) (g : GL (Fin 4) K) (hg : g ^ 5 = 1)
    (F : Submodule K (Fin 4 → K)) (hF : StableV g F) (hF0 : F ≠ ⊥) (hFt : F ≠ ⊤) : g = 1 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hmodF := card_perm_modEq (permV g F hF) (p := 5) (permV_pow_eq_one g F hF 5 hg)
  rw [Nat.card_congr (fixEquivV g F hF), natCard_submodule hK, natCard_submodule hK] at hmodF
  unfold Nat.ModEq at hmodF
  have hEF : F ⊓ fixV ({g} : Set (GL (Fin 4) K)) ≤ F := inf_le_left
  have hle1 : Module.finrank K ↥(F ⊓ fixV ({g} : Set (GL (Fin 4) K))) ≤ Module.finrank K ↥F :=
    Submodule.finrank_mono hEF
  have hF_lt : Module.finrank K ↥F < 4 := by
    have h := Submodule.finrank_lt hFt
    simpa using h
  have heq : Module.finrank K ↥(F ⊓ fixV ({g} : Set (GL (Fin 4) K))) = Module.finrank K ↥F :=
    arith_three _ hF_lt _ hle1 hmodF
  have hEq : F ⊓ fixV ({g} : Set (GL (Fin 4) K)) = F :=
    Submodule.eq_of_le_of_finrank_eq hEF heq
  have hFfix : F ≤ fixV ({g} : Set (GL (Fin 4) K)) := inf_eq_left.1 hEq
  have htop : StableV g ⊤ := fun v _ => Submodule.mem_top
  have hmodV := card_perm_modEq (permV g ⊤ htop) (p := 5) (permV_pow_eq_one g ⊤ htop 5 hg)
  rw [Nat.card_congr (fixEquivV g ⊤ htop), natCard_submodule hK, natCard_submodule hK,
    top_inf_eq] at hmodV
  unfold Nat.ModEq at hmodV
  have hVfin : Module.finrank K ↥(⊤ : Submodule K (Fin 4 → K)) = 4 := by
    simp
  rw [hVfin] at hmodV
  have hpos : 1 ≤ Module.finrank K ↥(fixV ({g} : Set (GL (Fin 4) K))) := by
    have hle := Submodule.finrank_mono hFfix
    have hFpos : 1 ≤ Module.finrank K ↥F := by
      by_contra hcon
      apply hF0
      have h0 : Module.finrank K ↥F = 0 := by omega
      exact (Submodule.finrank_eq_zero).1 h0
    omega
  have hf4 : Module.finrank K ↥(fixV ({g} : Set (GL (Fin 4) K))) = 4 := by
    have hlt := Submodule.finrank_le (fixV ({g} : Set (GL (Fin 4) K)))
    simp only [Module.finrank_fin_fun] at hlt
    exact arith_four _ (by omega) hpos hmodV
  have htopfix : fixV ({g} : Set (GL (Fin 4) K)) = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by simp [hf4])
  apply eq_one_of_actV
  intro v
  have hv : v ∈ fixV ({g} : Set (GL (Fin 4) K)) := by
    rw [htopfix]
    exact Submodule.mem_top
  exact mem_fixV_singleton.1 hv


theorem fixV_ne_bot_of_isPGroup {S : Type} [Group S] (φ : S →* GL (Fin 4) K) (hK : Nat.card K = 8)
    (T : Subgroup S) (hT : IsPGroup 2 T) : fixV ((φ : S → GL (Fin 4) K) '' (T : Set S)) ≠ ⊥ := by
  intro hbot
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : MulAction (GL (Fin 4) K) (Fin 4 → K) := glMulAction
  letI : MulAction S (Fin 4 → K) := MulAction.compHom _ φ
  have hmod := IsPGroup.card_modEq_card_fixedPoints hT (Fin 4 → K)
  have hfix : Nat.card (MulAction.fixedPoints (↥T) (Fin 4 → K)) =
      Nat.card ↥(fixV ((φ : S → GL (Fin 4) K) '' (T : Set S))) := by
    apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro x
    rw [MulAction.mem_fixedPoints, mem_fixV]
    constructor
    · intro h g hg
      obtain ⟨t, ht, rfl⟩ := hg
      exact h ⟨t, ht⟩
    · intro h g
      exact h (φ g) (Set.mem_image_of_mem φ g.2)
  have hV : Nat.card (Fin 4 → K) = 8 ^ 4 := by
    rw [Module.natCard_eq_pow_finrank (K := K) (V := Fin 4 → K), hK, Module.finrank_fin_fun]
  have hbotcard : Nat.card (⊥ : Submodule K (Fin 4 → K)) = 1 := by
    rw [natCard_submodule hK, finrank_bot, pow_zero]
  rw [hfix, hbot, hbotcard, hV] at hmod
  unfold Nat.ModEq at hmod
  norm_num at hmod

theorem exists_fiveCycle : ∃ c : alternatingGroup (Fin 7), c ^ 5 = 1 ∧ c ≠ 1 := by
  let σ : Equiv.Perm (Fin 7) := Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 3 4
  have hσ : σ ∈ alternatingGroup (Fin 7) := by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide
  refine ⟨⟨σ, hσ⟩, ?_, ?_⟩
  · apply Subtype.ext
    show σ ^ 5 = 1
    decide
  · intro h
    have h' : σ = 1 := congrArg Subtype.val h
    exact absurd h' (by decide)

theorem core {S : Type} [Group S] (hK : Nat.card K = 8) (φ : S →* GL (Fin 4) K)
    (hφ : Function.Injective φ) (ψ : alternatingGroup (Fin 7) →* S) (hψ : Function.Injective ψ)
    (T : Subgroup S) (hT : IsPGroup 2 T) (hT1 : T ≠ ⊥)
    (hn : ∀ a : alternatingGroup (Fin 7), ∀ t ∈ T, ψ a * t * (ψ a)⁻¹ ∈ T) : False := by
  have hne := fixV_ne_bot_of_isPGroup φ hK T hT
  by_cases hFt : fixV ((φ : S → GL (Fin 4) K) '' (T : Set S)) = ⊤
  · apply hT1
    rw [eq_bot_iff]
    intro t ht
    have hall : ∀ v : Fin 4 → K, actV (φ t) v = v := by
      intro v
      have hv : v ∈ fixV ((φ : S → GL (Fin 4) K) '' (T : Set S)) := by
        rw [hFt]
        exact Submodule.mem_top
      exact hv (φ t) (Set.mem_image_of_mem φ ht)
    have h1 : φ t = 1 := eq_one_of_actV _ hall
    rw [Subgroup.mem_bot]
    apply hφ
    rw [h1, map_one]
  · obtain ⟨c, hc5, hc1⟩ := exists_fiveCycle
    have hg5 : (φ (ψ c)) ^ 5 = 1 := by
      rw [← map_pow, ← map_pow, hc5, map_one, map_one]
    have hstab : StableV (φ (ψ c)) (fixV ((φ : S → GL (Fin 4) K) '' (T : Set S))) := by
      intro v hv
      rw [mem_fixV]
      intro g' hg'
      obtain ⟨t, ht, rfl⟩ := hg'
      have hu : (ψ c)⁻¹ * t * ψ c ∈ T := by
        have := hn c⁻¹ t ht
        rwa [map_inv, inv_inv] at this
      have hv' := hv (φ ((ψ c)⁻¹ * t * ψ c)) (Set.mem_image_of_mem φ hu)
      calc actV (φ t) (actV (φ (ψ c)) v)
          = actV (φ t * φ (ψ c)) v := (actV_mul _ _ _).symm
        _ = actV (φ (ψ c) * φ ((ψ c)⁻¹ * t * ψ c)) v := by
            congr 1
            rw [← map_mul, ← map_mul]
            congr 1
            group
        _ = actV (φ (ψ c)) (actV (φ ((ψ c)⁻¹ * t * ψ c)) v) := actV_mul _ _ _
        _ = actV (φ (ψ c)) v := by rw [hv']
    have hfive := five_fix hK _ hg5 _ hstab hne hFt
    apply hc1
    apply hψ
    apply hφ
    simpa [map_one] using hfive

end CFSG.LocalAnalysis.GLTheoremA.SFM7Lin
