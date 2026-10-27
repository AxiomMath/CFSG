module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeA2ConjDim

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSEight

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint

set_option linter.unusedSectionVars false

section Conj

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem pow_apply_of_apply_eq_smul {s : Module.End K V} {c : K} {v : V} (h : s v = c • v)
    (n : ℕ) : (s ^ n) v = c ^ n • v := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, h, map_smul, ih, smul_smul, pow_succ, mul_comm]

theorem finrank_ker_sub_smul_le_of_conj_pow [FiniteDimensional K V] (s : Module.End K V)
    (m : V ≃ₗ[K] V) (k : ℕ) (hm : ∀ v, m (s v) = (s ^ k) (m v)) (c : K) :
    Module.finrank K (LinearMap.ker (s - c • 1)) ≤
      Module.finrank K (LinearMap.ker (s - c ^ k • 1)) := by
  have hker : ∀ (t : Module.End K V) (d : K) (v : V),
      v ∈ LinearMap.ker (t - d • 1) ↔ t v = d • v := by
    intro t d v
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
      sub_eq_zero]
  have h1 : LinearMap.ker (s - c • 1) ≤ LinearMap.ker (s ^ k - c ^ k • 1) := by
    intro v hv
    rw [hker] at hv ⊢
    exact pow_apply_of_apply_eq_smul hv k
  have h2 : (LinearMap.ker (s - c ^ k • 1)).map (m : V →ₗ[K] V) =
      LinearMap.ker (s ^ k - c ^ k • 1) := by
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      rw [SetLike.mem_coe, hker] at hv
      rw [hker, LinearEquiv.coe_coe, ← hm, hv, map_smul]
    · intro hw
      rw [hker] at hw
      refine ⟨m.symm w, ?_, by simp⟩
      rw [SetLike.mem_coe, hker]
      apply m.injective
      rw [hm, LinearEquiv.apply_symm_apply, hw, map_smul, LinearEquiv.apply_symm_apply]
  calc Module.finrank K (LinearMap.ker (s - c • 1))
      ≤ Module.finrank K (LinearMap.ker (s ^ k - c ^ k • 1)) := Submodule.finrank_mono h1
    _ = Module.finrank K ((LinearMap.ker (s - c ^ k • 1)).map (m : V →ₗ[K] V)) := by rw [h2]
    _ = Module.finrank K (LinearMap.ker (s - c ^ k • 1)) := LinearEquiv.finrank_map_eq m _

end Conj

section Eigen

variable {τ : Tag} {K : Type} [Field K]

theorem ker_rootDiag_sub_smul (a : Fin τ.rank → Kˣ) (c : K) :
    LinearMap.ker (rootDiag a - c • 1) =
      Finsupp.supported K K {b | ((rootChar a (labelWt τ b) : Kˣ) : K) = c} := by
  ext v
  rw [LinearMap.mem_ker, Finsupp.mem_supported]
  constructor
  · intro h b hb
    have h1 := congrArg (fun w : RootModule τ K => w b) h
    simp only [LinearMap.sub_apply, Finsupp.coe_sub, Pi.sub_apply, rootDiag_coord,
      LinearMap.smul_apply, Module.End.one_apply, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul,
      Finsupp.coe_zero, Pi.zero_apply] at h1
    have hv : v b ≠ 0 := Finsupp.mem_support_iff.1 hb
    have h2 : (((rootChar a (labelWt τ b) : Kˣ) : K) - c) * v b = 0 := by
      rw [sub_mul]
      exact h1
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact sub_eq_zero.1 h3
    · exact absurd h3 hv
  · intro h
    ext b
    simp only [LinearMap.sub_apply, Finsupp.coe_sub, Pi.sub_apply, rootDiag_coord,
      LinearMap.smul_apply, Module.End.one_apply, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul,
      Finsupp.coe_zero, Pi.zero_apply]
    by_cases hb : v b = 0
    · rw [hb, mul_zero, mul_zero, sub_zero]
    · have : ((rootChar a (labelWt τ b) : Kˣ) : K) = c := h (Finsupp.mem_support_iff.2 hb)
      rw [this, sub_self]

theorem finrank_ker_rootDiag_sub_smul (a : Fin τ.rank → Kˣ) (c : K) [Finite (Label τ)] :
    Module.finrank K (LinearMap.ker (rootDiag a - c • 1)) =
      Nat.card {b : Label τ // ((rootChar a (labelWt τ b) : Kˣ) : K) = c} := by
  classical
  rw [ker_rootDiag_sub_smul]
  haveI : Fintype ↥{b : Label τ | ((rootChar a (labelWt τ b) : Kˣ) : K) = c} :=
    Fintype.ofFinite _
  rw [(Finsupp.supportedEquivFinsupp (M := K) (R := K) _).finrank_eq,
    Module.finrank_finsupp_self]
  exact Nat.card_eq_fintype_card.symm


open scoped Classical in
theorem finrank_ker_rootDiag_sub_smul_card (a : Fin τ.rank → Kˣ) {c : K} (hc : c ≠ 1) :
    Module.finrank K (LinearMap.ker (rootDiag a - c • 1)) =
      ((rootFinset τ).filter fun α => ((rootChar a α : Kˣ) : K) = c).card := by
  rw [finrank_ker_rootDiag_sub_smul]
  have e : {b : Label τ // ((rootChar a (labelWt τ b) : Kˣ) : K) = c} ≃
      {α : {v : Fin τ.rank → ℤ // IsRoot τ v} // ((rootChar a α.1 : Kˣ) : K) = c} :=
    Equiv.subtypeSum.trans ((Equiv.sumCongr
      (@Equiv.equivEmpty _ ⟨fun i => by
        have h := i.2
        change ((rootChar a (0 : Fin τ.rank → ℤ) : Kˣ) : K) = c at h
        rw [rootChar_zero, Units.val_one] at h
        exact hc h.symm⟩)
      (Equiv.refl _)).trans (Equiv.emptySum _ _))
  have e2 : {α : {v : Fin τ.rank → ℤ // IsRoot τ v} // ((rootChar a α.1 : Kˣ) : K) = c} ≃
      {v : Fin τ.rank → ℤ // v ∈ (rootFinset τ).filter fun α => ((rootChar a α : Kˣ) : K) = c} :=
    { toFun := fun p => ⟨p.1.1, Finset.mem_filter.2 ⟨mem_rootFinset.2 p.1.2, p.2⟩⟩
      invFun := fun p =>
        ⟨⟨p.1, mem_rootFinset.1 (Finset.mem_filter.1 p.2).1⟩, (Finset.mem_filter.1 p.2).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_congr e2, Nat.card_eq_fintype_card, Fintype.card_coe]

end Eigen

set_option maxRecDepth 100000 in
theorem e6_iform_count : ∀ β ∈ rootFinset .E6,
    ((rootFinset .E6).filter (fun α => iform α β = 1)).card = 20 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem e6_iform_bound : ∀ β ∈ rootFinset .E6, ∀ α ∈ rootFinset .E6,
    -2 ≤ iform α β ∧ iform α β ≤ 2 ∧ (iform α β = -2 → α = -β) := by
  decide +kernel

section Coroot

variable {K : Type} [Field K]

open scoped Classical in
theorem finrank_ker_rootDiag_pow_lt {β : Fin Tag.E6.rank → ℤ} (hβ : β ∈ rootFinset .E6)
    {μ : Kˣ} (hμ : orderOf μ = 9) {a : Fin Tag.E6.rank → Kˣ}
    (ha : ∀ α ∈ rootFinset .E6, rootChar a α = μ ^ iform α β) {k : ℕ} (hk : k = 4 ∨ k = 7) :
    Module.finrank K (LinearMap.ker (rootDiag a - ((μ ^ k : Kˣ) : K) • 1)) <
      Module.finrank K (LinearMap.ker (rootDiag a - (μ : K) • 1)) := by
  have hμ1 : (μ : K) ≠ 1 := by
    intro h
    have : μ = 1 := Units.ext h
    rw [this, orderOf_one] at hμ
    omega
  have hμk1 : ((μ ^ k : Kˣ) : K) ≠ 1 := by
    intro h
    have h1 : μ ^ k = 1 := Units.ext h
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [hμ] at h2
    rcases hk with rfl | rfl <;> norm_num at h2
  rw [finrank_ker_rootDiag_sub_smul_card a hμk1, finrank_ker_rootDiag_sub_smul_card a hμ1]
  have hle : ((rootFinset .E6).filter fun α => ((rootChar a α : Kˣ) : K) = ((μ ^ k : Kˣ) : K)) ⊆
      {-β} := by
    intro α hα
    rw [Finset.mem_filter] at hα
    obtain ⟨hαΦ, hαk⟩ := hα
    have h1 : μ ^ iform α β = μ ^ (k : ℤ) := by
      rw [← ha α hαΦ, zpow_natCast]
      exact Units.ext hαk
    have h2 := (zpow_eq_zpow_iff_modEq.1 h1)
    rw [hμ] at h2
    obtain ⟨hlo, hhi, hm2⟩ := e6_iform_bound β hβ α hαΦ
    rw [Finset.mem_singleton]
    apply hm2
    unfold Int.ModEq at h2
    rcases hk with rfl | rfl <;> omega
  have hge : (rootFinset .E6).filter (fun α => iform α β = 1) ⊆
      (rootFinset .E6).filter fun α => ((rootChar a α : Kˣ) : K) = (μ : K) := by
    intro α hα
    rw [Finset.mem_filter] at hα ⊢
    refine ⟨hα.1, ?_⟩
    rw [ha α hα.1, hα.2, zpow_one]
  have h1 := Finset.card_le_card hle
  have h2 := Finset.card_le_card hge
  rw [Finset.card_singleton] at h1
  rw [e6_iform_count β hβ] at h2
  omega

end Coroot

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSEight
