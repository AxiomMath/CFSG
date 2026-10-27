module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.BinaryThreeSpaceIrreducibleModulesFlag
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

universe u

namespace CFSG.ProperTwoGeneratedCore.BinaryThreeSpace

open Module

section Factor

variable {k G M N E : Type*} [Field k] [Monoid G] [AddCommGroup M] [Module k M] [AddCommGroup N]
  [Module k N] [AddCommGroup E] [Module k E]

theorem exists_factor (actM : G → M → M) (actN : G → N → N) (ρ : Representation k G E)
    (Ψ : M →ₗ[k] N) (hΨ : Function.Surjective Ψ) (hΨe : ∀ g m, Ψ (actM g m) = actN g (Ψ m))
    (Φ : M →ₗ[k] E) (hΦe : ∀ g m, Φ (actM g m) = ρ g (Φ m)) (hker : ∀ m, Ψ m = 0 → Φ m = 0) :
    ∃ Φ' : N →ₗ[k] E, (∀ m, Φ' (Ψ m) = Φ m) ∧ ∀ g n, Φ' (actN g n) = ρ g (Φ' n) := by
  obtain ⟨σ, hσ⟩ := Ψ.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hΨ)
  have hfac : ∀ m, Φ (σ (Ψ m)) = Φ m := fun m => by
    have h := hker (σ (Ψ m) - m) (by
      rw [map_sub, ← LinearMap.comp_apply, hσ, LinearMap.id_apply, sub_self])
    rwa [map_sub, sub_eq_zero] at h
  refine ⟨Φ ∘ₗ σ, hfac, fun g n => ?_⟩
  obtain ⟨m, rfl⟩ := hΨ n
  simp only [LinearMap.comp_apply]
  rw [← hΨe, hfac, hfac, hΦe]

end Factor

section Classification

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem permActU_zero {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Fintype W]
    [DecidableEq W] (g : W ≃ₗ[ZMod 2] W) : permActU g (0 : augmentation W) = 0 :=
  rfl

theorem dualRep_eq_dualMap (g : V ≃ₗ[ZMod 2] V) (f : Module.Dual (ZMod 2) V) :
    dualRep V g f = g.symm.dualMap f :=
  rfl

variable [Fintype V] [DecidableEq V] [Fintype (Module.Dual (ZMod 2) V)]
  [DecidableEq (Module.Dual (ZMod 2) V)] {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
  [Finite E]

theorem exists_equiv_model (hV : finrank (ZMod 2) V = 3)
    (ρ : Representation (ZMod 2) (V ≃ₗ[ZMod 2] V) E) (hρ : ρ.IsIrreducible) :
    Nonempty (ρ.Equiv (trivRep V)) ∨ Nonempty (ρ.Equiv (natRep V)) ∨
      Nonempty (ρ.Equiv (dualRep V)) ∨ Nonempty (ρ.Equiv (adjRep V)) := by
  have : Module.Finite (ZMod 2) V := Module.finite_of_finrank_eq_succ hV
  have : Nontrivial E := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    have hbt : (⊥ : Subrepresentation ρ) = ⊤ := by
      rw [eq_top_iff]
      intro x _
      rw [Subsingleton.elim x 0]
      exact (⊥ : Subrepresentation ρ).toSubmodule.zero_mem
    exact (haveI := hρ; bot_ne_top) hbt
  obtain ⟨pf₀⟩ : Nonempty (Flags V) := Fintype.card_pos_iff.mp (by rw [card_flags hV]; norm_num)
  obtain ⟨e, he0, hfix⟩ := exists_fixed_ne_zero ρ hV pf₀
  obtain ⟨Φ, hΦe, hΦ0⟩ : ∃ Φ : (Flags V → ZMod 2) →ₗ[ZMod 2] E,
      (∀ g z, Φ (flagPermAct g z) = ρ g (Φ z)) ∧ Φ ≠ 0 :=
    ⟨flagMap ρ hV pf₀ e, flagMap_flagPermAct ρ hV hfix, fun h => he0 (by
      rw [← flagMap_single ρ hV hfix, h, LinearMap.zero_apply])⟩
  by_cases hK : ∀ t, Φ (flagIota V t) = 0
  · right; right; right
    obtain ⟨Φ', hΦ', hΦ'e⟩ := exists_factor flagPermAct (fun g X => adjRep V g X) ρ (flagPsi V)
      (flagPsi_surjective hV) (fun g z => Subtype.ext (flagPsi_equivariant g z)) Φ hΦe
      fun z hz => by
        have hz' : z ∈ LinearMap.ker (flagPsi V) := LinearMap.mem_ker.mpr hz
        rw [ker_flagPsi_eq hV] at hz'
        obtain ⟨t, rfl⟩ := hz'
        exact hK t
    refine nonempty_equiv_of_ne_zero hρ (adjRep_isIrreducible hV) Φ' hΦ'e fun h => hΦ0 ?_
    refine LinearMap.ext fun z => ?_
    rw [← hΦ' z, h, LinearMap.zero_apply, LinearMap.zero_apply]
  push Not at hK
  obtain ⟨t₀, ht₀⟩ := hK
  let Φ₁ := Φ ∘ₗ flagIota V
  have hΦ₁e : ∀ (g : V ≃ₗ[ZMod 2] V) c x y,
      Φ₁ (c, permActU g x, permActU g.symm.dualMap y) = ρ g (Φ₁ (c, x, y)) := fun g c x y =>
    (congrArg Φ (flagIota_equivariant g (c, x, y))).trans (hΦe g _)
  have hdecomp : ∀ c x y, Φ₁ (c, x, y) = Φ₁ (c, 0, 0) + Φ₁ (0, x, 0) + Φ₁ (0, 0, y) :=
    fun c x y => by
      rw [← map_add, ← map_add]
      congr 1
      simp
  by_cases h1 : ∃ c, Φ₁ (c, 0, 0) ≠ 0
  · left
    obtain ⟨c₀, hc₀⟩ := h1
    refine nonempty_equiv_of_ne_zero hρ trivRep_isIrreducible
      (Φ₁ ∘ₗ LinearMap.inl (ZMod 2) (ZMod 2) _) (fun g c => ?_)
      fun h => hc₀ (LinearMap.congr_fun h c₀)
    have h := hΦ₁e g c 0 0
    rw [permActU_zero, permActU_zero] at h
    exact h
  push Not at h1
  by_cases h2 : ∃ x, Φ₁ (0, x, 0) ≠ 0
  · obtain ⟨x₀, hx₀⟩ := h2
    let Φ₂ : augmentation V →ₗ[ZMod 2] E :=
      Φ₁ ∘ₗ (LinearMap.inr (ZMod 2) (ZMod 2) _ ∘ₗ LinearMap.inl (ZMod 2) _ _)
    have hΦ₂ : ∀ x, Φ₂ x = Φ₁ (0, x, 0) := fun x => rfl
    have hΦ₂e : ∀ g x, Φ₂ (permActU g x) = ρ g (Φ₂ x) := fun g x => by
      have h := hΦ₁e g 0 x 0
      rw [permActU_zero] at h
      exact h
    by_cases h2a : ∃ f, Φ₂ (kappa hV f) ≠ 0
    ·
      right; right; left
      obtain ⟨f₀, hf₀⟩ := h2a
      refine nonempty_equiv_of_ne_zero hρ (dualRep_isIrreducible hV) (Φ₂ ∘ₗ kappa hV)
        (fun g f => ?_) fun h => hf₀ (LinearMap.congr_fun h f₀)
      change Φ₂ (kappa hV (dualRep V g f)) = ρ g (Φ₂ (kappa hV f))
      rw [← hΦ₂e]
      exact congrArg Φ₂ (Subtype.ext (kappa_equivariant hV g f))
    ·
      right; left
      push Not at h2a
      obtain ⟨Φ₃, hΦ₃, hΦ₃e⟩ := exists_factor permActU (fun g v => natRep V g v) ρ (theta V)
        (theta_surjective hV) theta_equivariant Φ₂ hΦ₂e fun x hx => by
          have hx' : x ∈ LinearMap.ker (theta V) := LinearMap.mem_ker.mpr hx
          rw [ker_theta_eq hV] at hx'
          obtain ⟨f, rfl⟩ := hx'
          exact h2a f
      refine nonempty_equiv_of_ne_zero hρ (natRep_isIrreducible hV) Φ₃ hΦ₃e fun h => hx₀ ?_
      rw [← hΦ₂, ← hΦ₃, h, LinearMap.zero_apply]
  push Not at h2
  have h3 : ∃ y, Φ₁ (0, 0, y) ≠ 0 := by
    by_contra h3
    push Not at h3
    obtain ⟨c, x, y⟩ := t₀
    exact ht₀ (by
      change Φ₁ (c, x, y) = 0
      rw [hdecomp, h1, h2, h3, add_zero, add_zero])
  obtain ⟨y₀, hy₀⟩ := h3
  let Φ₄ : augmentation (Module.Dual (ZMod 2) V) →ₗ[ZMod 2] E :=
    Φ₁ ∘ₗ (LinearMap.inr (ZMod 2) (ZMod 2) _ ∘ₗ LinearMap.inr (ZMod 2) _ _)
  have hΦ₄ : ∀ y, Φ₄ y = Φ₁ (0, 0, y) := fun y => rfl
  have hΦ₄e : ∀ (g : V ≃ₗ[ZMod 2] V) y, Φ₄ (permActU g.symm.dualMap y) = ρ g (Φ₄ y) :=
    fun g y => by
      have h := hΦ₁e g 0 0 y
      rw [permActU_zero] at h
      exact h
  let ν : V →ₗ[ZMod 2] augmentation (Module.Dual (ZMod 2) V) :=
    kappa (finrank_dual hV) ∘ₗ Module.Dual.eval (ZMod 2) V
  have hν : ∀ (g : V ≃ₗ[ZMod 2] V) v, ν (natRep V g v) = permActU g.symm.dualMap (ν v) :=
    fun _ _ => rfl
  by_cases h3a : ∃ v, Φ₄ (ν v) ≠ 0
  ·
    right; left
    obtain ⟨v₀, hv₀⟩ := h3a
    refine nonempty_equiv_of_ne_zero hρ (natRep_isIrreducible hV) (Φ₄ ∘ₗ ν) (fun g v => ?_)
      fun h => hv₀ (LinearMap.congr_fun h v₀)
    change Φ₄ (ν (natRep V g v)) = ρ g (Φ₄ (ν v))
    rw [hν, hΦ₄e]
  ·
    right; right; left
    push Not at h3a
    obtain ⟨Φ₅, hΦ₅, hΦ₅e⟩ := exists_factor (fun g y => permActU g.symm.dualMap y)
      (fun g f => dualRep V g f) ρ (theta (Module.Dual (ZMod 2) V))
      (theta_surjective (finrank_dual hV))
      (fun g y => (theta_equivariant g.symm.dualMap y).trans (dualRep_eq_dualMap g _).symm)
      Φ₄ hΦ₄e fun y hy => by
        have hy' : y ∈ LinearMap.ker (theta (Module.Dual (ZMod 2) V)) := LinearMap.mem_ker.mpr hy
        rw [ker_theta_eq (finrank_dual hV)] at hy'
        obtain ⟨F, rfl⟩ := hy'
        obtain ⟨v, rfl⟩ := (Module.evalEquiv (ZMod 2) V).surjective F
        exact h3a v
    refine nonempty_equiv_of_ne_zero hρ (dualRep_isIrreducible hV) Φ₅ hΦ₅e fun h => hy₀ ?_
    rw [← hΦ₄, ← hΦ₅, h, LinearMap.zero_apply]

end Classification

section Series

variable {k G W : Type*} [Field k] [Monoid G] [AddCommGroup W] [Module k W]
  {ρ : Representation k G W}

@[expose] def inSubrep (A B : Subrepresentation ρ) : Subrepresentation B.toRepresentation where
  toSubmodule := A.toSubmodule.comap B.toSubmodule.subtype
  apply_mem_toSubmodule g _ hx := A.apply_mem_toSubmodule g hx

theorem quotient_isIrreducible {A B : Subrepresentation ρ} (hAB : A < B)
    (hcov : ∀ C : Subrepresentation ρ, A < C → ¬C < B) :
    (inSubrep A B).quotient.IsIrreducible := by
  obtain ⟨x, hxB, hxA⟩ := IsConcreteLE.exists_of_lt hAB
  refine { exists_pair_ne := ⟨⊥, ⊤, bot_ne_top_of_ne_zero _
    (m := Submodule.Quotient.mk (⟨x, hxB⟩ : B.toSubmodule)) ?_⟩, eq_bot_or_eq_top := fun R => ?_ }
  · rw [Ne, Submodule.Quotient.mk_eq_zero]
    exact hxA
  let C : Subrepresentation ρ :=
    ⟨(R.toSubmodule.comap (inSubrep A B).toSubmodule.mkQ).map B.toSubmodule.subtype, by
      rintro g _ ⟨y, hy, rfl⟩
      exact ⟨B.toRepresentation g y, R.apply_mem_toSubmodule g hy, rfl⟩⟩
  have hAC : A ≤ C := fun a ha => ⟨⟨a, hAB.le ha⟩, by
    change Submodule.Quotient.mk _ ∈ R.toSubmodule
    rw [(Submodule.Quotient.mk_eq_zero (inSubrep A B).toSubmodule
      (x := ⟨a, hAB.le ha⟩)).mpr ha]
    exact R.toSubmodule.zero_mem, rfl⟩
  have hCB : C ≤ B := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  rcases hAC.lt_or_eq with h | h
  · right
    have hCB' : C = B := by
      by_contra hne
      exact hcov C h (lt_of_le_of_ne hCB hne)
    rw [eq_top_iff]
    intro q _
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    have hy : (y : W) ∈ C := by
      rw [hCB']
      exact y.2
    obtain ⟨y', hy', hyy'⟩ := hy
    obtain rfl : y' = y := Subtype.ext hyy'
    exact hy'
  · left
    rw [eq_bot_iff]
    intro q hq
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    have hy : (y : W) ∈ C := ⟨y, hq, rfl⟩
    rw [← h] at hy
    exact (Submodule.mem_bot k).mpr ((Submodule.Quotient.mk_eq_zero _).mpr hy)

theorem exists_series [FiniteDimensional k W] (N : Subrepresentation ρ) :
    ∃ (n : ℕ) (c : Fin (n + 1) → Subrepresentation ρ), c 0 = ⊥ ∧ c (Fin.last n) = N ∧
      ∀ i : Fin n, c i.castSucc < c i.succ ∧ ∀ C, c i.castSucc < C → ¬C < c i.succ := by
  induction h : finrank k N.toSubmodule using Nat.strong_induction_on generalizing N with
  | _ d ih =>
  by_cases hN : N = ⊥
  · exact ⟨0, fun _ => ⊥, rfl, hN.symm, fun i => i.elim0⟩
  obtain ⟨L, hLN, hLmax⟩ := (measure fun L : Subrepresentation ρ =>
      finrank k N.toSubmodule - finrank k L.toSubmodule).wf.has_min {L | L < N}
    ⟨⊥, bot_lt_iff_ne_bot.mpr hN⟩
  have hlt : ∀ {A B : Subrepresentation ρ}, A < B →
      finrank k A.toSubmodule < finrank k B.toSubmodule := fun hAB =>
    Submodule.finrank_lt_finrank_of_lt hAB
  have hcov : ∀ C, L < C → ¬C < N := fun C hLC hCN => by
    have h1 : ¬finrank k N.toSubmodule - finrank k C.toSubmodule <
        finrank k N.toSubmodule - finrank k L.toSubmodule := hLmax C hCN
    have h2 := hlt hLC
    have h3 := hlt hCN
    omega
  obtain ⟨n, c, hc0, hcn, hc⟩ := ih _ (h ▸ hlt hLN) L rfl
  refine ⟨n + 1, Fin.snoc c N, ?_, Fin.snoc_last _ _, fun i => ?_⟩
  · rw [← Fin.castSucc_zero, Fin.snoc_castSucc, hc0]
  induction i using Fin.lastCases with
  | last =>
    rw [Fin.snoc_castSucc, hcn, Fin.succ_last, Fin.snoc_last]
    exact ⟨hLN, hcov⟩
  | cast j =>
    rw [Fin.snoc_castSucc, Fin.succ_castSucc, Fin.snoc_castSucc]
    exact hc j

end Series

theorem existsUnique_four {P₀ P₁ P₂ P₃ : Prop} (h : P₀ ∨ P₁ ∨ P₂ ∨ P₃) (h01 : ¬(P₀ ∧ P₁))
    (h02 : ¬(P₀ ∧ P₂)) (h03 : ¬(P₀ ∧ P₃)) (h12 : ¬(P₁ ∧ P₂)) (h13 : ¬(P₁ ∧ P₃))
    (h23 : ¬(P₂ ∧ P₃)) : ∃! i : Fin 4, ![P₀, P₁, P₂, P₃] i := by
  refine existsUnique_of_exists_of_unique ?_ fun i j hi hj => ?_
  · rcases h with h | h | h | h
    exacts [⟨0, h⟩, ⟨1, h⟩, ⟨2, h⟩, ⟨3, h⟩]
  · fin_cases i <;> fin_cases j <;> simp_all

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem irreducible_binary_GL3_module_production (hV : finrank (ZMod 2) V = 3) :
    (∀ (E : Type u) [AddCommGroup E] [Module (ZMod 2) E] [FiniteDimensional (ZMod 2) E]
        (ρ : Representation (ZMod 2) (V ≃ₗ[ZMod 2] V) E), ρ.IsIrreducible →
        ∃! i : Fin 4, ![Nonempty (ρ.Equiv (trivRep V)), Nonempty (ρ.Equiv (natRep V)),
          Nonempty (ρ.Equiv (dualRep V)), Nonempty (ρ.Equiv (adjRep V))] i) ∧
    ((trivRep V).IsIrreducible ∧ (natRep V).IsIrreducible ∧ (dualRep V).IsIrreducible ∧
      (adjRep V).IsIrreducible) ∧
    (finrank (ZMod 2) (ZMod 2) = 1 ∧ finrank (ZMod 2) V = 3 ∧
      finrank (ZMod 2) (Module.Dual (ZMod 2) V) = 3 ∧ finrank (ZMod 2) (traceZeroEnd V) = 8) ∧
    (IsEmpty ((trivRep V).Equiv (natRep V)) ∧ IsEmpty ((trivRep V).Equiv (dualRep V)) ∧
      IsEmpty ((trivRep V).Equiv (adjRep V)) ∧ IsEmpty ((natRep V).Equiv (dualRep V)) ∧
      IsEmpty ((natRep V).Equiv (adjRep V)) ∧ IsEmpty ((dualRep V).Equiv (adjRep V))) ∧
    ∀ (W : Type u) [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
      (ρ : Representation (ZMod 2) (V ≃ₗ[ZMod 2] V) W), finrank (ZMod 2) W ≤ 7 →
      ∃ (n : ℕ) (c : Fin (n + 1) → Subrepresentation ρ), c 0 = ⊥ ∧ c (Fin.last n) = ⊤ ∧
        ∀ i : Fin n, c i.castSucc < c i.succ ∧
          (inSubrep (c i.castSucc) (c i.succ)).quotient.IsIrreducible ∧
          (Nonempty ((inSubrep (c i.castSucc) (c i.succ)).quotient.Equiv (trivRep V)) ∨
            Nonempty ((inSubrep (c i.castSucc) (c i.succ)).quotient.Equiv (natRep V)) ∨
            Nonempty ((inSubrep (c i.castSucc) (c i.succ)).quotient.Equiv (dualRep V))) := by
  classical
  have : Module.Finite (ZMod 2) V := Module.finite_of_finrank_eq_succ hV
  have : Finite V := Module.finite_of_finite (ZMod 2)
  let _ : Fintype V := Fintype.ofFinite V
  have : Finite (Module.Dual (ZMod 2) V) := Module.finite_of_finite (ZMod 2)
  let _ : Fintype (Module.Dual (ZMod 2) V) := Fintype.ofFinite _
  have hdual : finrank (ZMod 2) (Module.Dual (ZMod 2) V) = 3 := finrank_dual hV
  have hA : finrank (ZMod 2) (traceZeroEnd V) = 8 := finrank_traceZeroEnd hV
  have h01 : IsEmpty ((trivRep V).Equiv (natRep V)) :=
    isEmpty_equiv_of_finrank_ne (by rw [finrank_self, hV]; norm_num)
  have h02 : IsEmpty ((trivRep V).Equiv (dualRep V)) :=
    isEmpty_equiv_of_finrank_ne (by rw [finrank_self, hdual]; norm_num)
  have h03 : IsEmpty ((trivRep V).Equiv (adjRep V)) :=
    isEmpty_equiv_of_finrank_ne (by rw [finrank_self, hA]; norm_num)
  have h12 : IsEmpty ((natRep V).Equiv (dualRep V)) := isEmpty_equiv_natRep_dualRep hV
  have h13 : IsEmpty ((natRep V).Equiv (adjRep V)) :=
    isEmpty_equiv_of_finrank_ne (by rw [hV, hA]; norm_num)
  have h23 : IsEmpty ((dualRep V).Equiv (adjRep V)) :=
    isEmpty_equiv_of_finrank_ne (by rw [hdual, hA]; norm_num)
  have hclass : ∀ (E : Type u) [AddCommGroup E] [Module (ZMod 2) E]
      [FiniteDimensional (ZMod 2) E] (ρ : Representation (ZMod 2) (V ≃ₗ[ZMod 2] V) E),
      ρ.IsIrreducible →
      Nonempty (ρ.Equiv (trivRep V)) ∨ Nonempty (ρ.Equiv (natRep V)) ∨
        Nonempty (ρ.Equiv (dualRep V)) ∨ Nonempty (ρ.Equiv (adjRep V)) :=
    fun E _ _ _ ρ hρ => by
      have : Finite E := Module.finite_of_finite (ZMod 2)
      exact exists_equiv_model hV ρ hρ
  refine ⟨fun E _ _ _ ρ hρ => ?_, ⟨trivRep_isIrreducible, natRep_isIrreducible hV,
    dualRep_isIrreducible hV, adjRep_isIrreducible hV⟩, ⟨finrank_self _, hV, hdual, hA⟩,
    ⟨h01, h02, h03, h12, h13, h23⟩, fun W _ _ _ ρ hW => ?_⟩
  · exact existsUnique_four (hclass E ρ hρ) (fun ⟨⟨φ⟩, ⟨ψ⟩⟩ => h01.elim (φ.symm.trans ψ))
      (fun ⟨⟨φ⟩, ⟨ψ⟩⟩ => h02.elim (φ.symm.trans ψ)) (fun ⟨⟨φ⟩, ⟨ψ⟩⟩ => h03.elim (φ.symm.trans ψ))
      (fun ⟨⟨φ⟩, ⟨ψ⟩⟩ => h12.elim (φ.symm.trans ψ)) (fun ⟨⟨φ⟩, ⟨ψ⟩⟩ => h13.elim (φ.symm.trans ψ))
      fun ⟨⟨φ⟩, ⟨ψ⟩⟩ => h23.elim (φ.symm.trans ψ)
  obtain ⟨n, c, hc0, hcn, hc⟩ := exists_series (⊤ : Subrepresentation ρ)
  refine ⟨n, c, hc0, hcn, fun i => ⟨(hc i).1, quotient_isIrreducible (hc i).1 (hc i).2, ?_⟩⟩
  rcases hclass _ _ (quotient_isIrreducible (hc i).1 (hc i).2) with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · exfalso
    obtain ⟨φ⟩ := h
    have h1 := finrank_eq_of_equiv φ
    have h2 := Submodule.finrank_quotient_le (inSubrep (c i.castSucc) (c i.succ)).toSubmodule
    have h3 := Submodule.finrank_le (c i.succ).toSubmodule
    omega

end CFSG.ProperTwoGeneratedCore.BinaryThreeSpace
