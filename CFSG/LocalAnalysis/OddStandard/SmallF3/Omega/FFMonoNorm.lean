module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFMonoDef

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private lemma exists_ne_pair (i m : Fin 6) : ∃ k : Fin 6, k ≠ i ∧ k ≠ m := by
  revert i m
  decide

theorem ffMono_eigen_frame (fr : NFrame Q (Fin 6) 1) {v : V} (hv : v ≠ 0)
    (h : ∀ K : Finset (Fin 6), Even K.card →
      ((fr.signChange K : OGroup Q) : V ≃ₗ[ZMod 3] V) v = v ∨
        ((fr.signChange K : OGroup Q) : V ≃ₗ[ZMod 3] V) v = -v) :
    ∃ (j : Fin 6) (a : ZMod 3), a ≠ 0 ∧ v = a • fr.b j := by
  obtain ⟨j, hj⟩ : ∃ j : Fin 6, fr.b.repr v j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hv (fr.b.ext_elem (fun i => by rw [hcon i]; simp))
  have hother : ∀ m : Fin 6, m ≠ j → fr.b.repr v m = 0 := by
    intro m hm
    by_contra hm0
    obtain ⟨k, hkj, hkm⟩ := exists_ne_pair j m
    have hjK : j ∈ ({j, k} : Finset (Fin 6)) := by simp
    have hmK : m ∉ ({j, k} : Finset (Fin 6)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hm, fun h => hkm h.symm⟩
    have hcard : Even ({j, k} : Finset (Fin 6)).card := by
      rw [Finset.card_pair_eq_two_iff.mpr hkj.symm]
      exact even_two
    rcases h {j, k} hcard with hvv | hvv
    · have hc := congrArg (fun w : V => fr.b.repr w j) hvv
      rw [fr.repr_signChange ({j, k}) v j, if_pos hjK] at hc
      have h2 : (2 : ZMod 3) * fr.b.repr v j = 0 := by
        rw [two_mul]
        exact eq_neg_iff_add_eq_zero.mp hc.symm
      exact hj ((mul_eq_zero.mp h2).resolve_left (by decide))
    · have hc := congrArg (fun w : V => fr.b.repr w m) hvv
      rw [fr.repr_signChange ({j, k}) v m, if_neg hmK, map_neg, Finsupp.neg_apply] at hc
      have h2 : (2 : ZMod 3) * fr.b.repr v m = 0 := by
        rw [two_mul]
        exact eq_neg_iff_add_eq_zero.mp hc
      exact hm0 ((mul_eq_zero.mp h2).resolve_left (by decide))
  refine ⟨j, fr.b.repr v j, hj, ?_⟩
  apply fr.b.ext_elem
  intro i
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, Module.Basis.repr_self]
  by_cases hij : i = j
  · subst hij; simp
  · rw [Finsupp.single_eq_of_ne hij, mul_zero]
    exact hother i hij

theorem ffMono_of_normalizes (fr : NFrame Q (Fin 6) 1) (γ : simGroup Q)
    (h : ∀ b ∈ ffB0 fr, simAct Q γ⁻¹ b ∈ ffB0 fr) :
    ∃ (σ : Equiv.Perm (Fin 6)) (K : Finset (Fin 6)),
      γ = orthToSim Q (fr.permOrth σ * fr.signChange K) := by
  let X : V ≃ₗ[ZMod 3] V := (γ : V ≃ₗ[ZMod 3] V)
  have key : ∀ i : Fin 6, ∀ K : Finset (Fin 6), Even K.card →
      ((fr.signChange K : OGroup Q) : V ≃ₗ[ZMod 3] V) (X (fr.b i)) = X (fr.b i) ∨
        ((fr.signChange K : OGroup Q) : V ≃ₗ[ZMod 3] V) (X (fr.b i)) = -X (fr.b i) := by
    intro i K hK
    obtain ⟨J, _hJeven, hJeq⟩ :=
      (mem_ffB0_iff fr).mp (h (fr.signChange K) (signChange_mem_ffB0 fr hK))
    have hcoe : ((γ⁻¹ : simGroup Q) : V ≃ₗ[ZMod 3] V) *
        (fr.signChange K : V ≃ₗ[ZMod 3] V) *
        ((γ⁻¹ : simGroup Q) : V ≃ₗ[ZMod 3] V)⁻¹ =
        (fr.signChange J : V ≃ₗ[ZMod 3] V) := by
      have hh := congrArg (fun g : OGroup Q => (g : V ≃ₗ[ZMod 3] V)) hJeq
      rwa [coe_simAct] at hh
    have hX : X⁻¹ * (fr.signChange K : V ≃ₗ[ZMod 3] V) * X =
        (fr.signChange J : V ≃ₗ[ZMod 3] V) := by
      have hh := hcoe
      rw [Subgroup.coe_inv] at hh
      rw [show ((γ : simGroup Q) : V ≃ₗ[ZMod 3] V) = X from rfl] at hh
      rwa [inv_inv] at hh
    have hbJ : (fr.signChange K : V ≃ₗ[ZMod 3] V) (X (fr.b i)) =
        X ((fr.signChange J : V ≃ₗ[ZMod 3] V) (fr.b i)) := by
      have hh := congrArg (fun e : V ≃ₗ[ZMod 3] V => X (e (fr.b i))) hX
      simpa only [LinearEquiv.mul_apply, LinearEquiv.coe_inv,
        LinearEquiv.apply_symm_apply] using hh
    rw [hbJ, fr.signChange_basis J i]
    by_cases hi : i ∈ J
    · right; rw [if_pos hi, map_neg]
    · left; rw [if_neg hi]
  have hb : ∀ i : Fin 6, X (fr.b i) ≠ 0 := by
    intro i h0
    exact fr.b.ne_zero i (X.injective (by simpa using h0))
  choose σ' a ha hXb using fun i => ffMono_eigen_frame fr (hb i) (key i)
  have hσ'inj : Function.Injective σ' := by
    intro i i' hii
    have hzero : X (a i' • fr.b i - a i • fr.b i') = 0 := by
      rw [map_sub, map_smul, map_smul, hXb i, hXb i', hii]
      simp [smul_smul, mul_comm]
    have hlin : a i' • fr.b i - a i • fr.b i' = 0 :=
      X.injective (by rw [hzero, map_zero])
    exact ffMono_index_eq fr (ha i') (sub_eq_zero.mp hlin)
  have hσ'bij : Function.Bijective σ' := hσ'inj.bijective_of_finite
  let σ : Equiv.Perm (Fin 6) := Equiv.ofBijective σ' hσ'bij
  let K : Finset (Fin 6) := Finset.univ.filter (fun i => a i = -1)
  have ha_eq : ∀ i : Fin 6, a i = (if i ∈ K then (-1 : ZMod 3) else 1) := by
    intro i
    by_cases hi : i ∈ K
    · rw [if_pos hi]
      exact (Finset.mem_filter.mp hi).2
    · rw [if_neg hi]
      rcases (by decide : ∀ e : ZMod 3, e ≠ 0 → e = 1 ∨ e = -1) (a i) (ha i) with h1 | h1
      · exact h1
      · exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h1⟩) hi
  have hXeq : X = ((fr.permOrth σ * fr.signChange K : OGroup Q) : V ≃ₗ[ZMod 3] V) := by
    apply fr.b.ext'
    intro i
    rw [hXb i, ffMono_basis, show σ i = σ' i from rfl, ha_eq i]
  exact ⟨σ, K, Subtype.ext (by rw [coe_orthToSim]; exact hXeq)⟩

end CFSG.OddStandard.SmallF3.Omega
