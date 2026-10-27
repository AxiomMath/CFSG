module

public import CFSG.HardMathSupport.Solomon.Coordinator.I28_14IdentBGroup
public import CFSG.HardMathSupport.Solomon.Coordinator.I28_5

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Solomon.Coordinator

open Module CFSG.ComponentClassification.OutcomeLocal

section Blocks

variable {M : Type} [AddCommGroup M] [Module (ZMod 2) M]

local notation "𝔾" => LinearMap.GeneralLinearGroup (ZMod 2) M

theorem i28_14_identB_finite_gl [Finite M] : Finite 𝔾 :=
  Finite.of_injective (fun g : 𝔾 => ((g : M →ₗ[ZMod 2] M) : M → M))
    (fun _ _ hgh => Units.ext (LinearMap.ext (congrFun hgh)))

theorem i28_14_identB_finite_submodule [Finite M] : Finite (Submodule (ZMod 2) M) :=
  Finite.of_injective (fun T : Submodule (ZMod 2) M => (T : Set M)) SetLike.coe_injective

namespace i285_Setup

variable (S : i285_Setup M)

theorem identB_conj {R₁ R₂ : Submodule (ZMod 2) M} (h1 : S.IsMin R₁) (h2 : S.IsMin R₂) :
    ∃ g ∈ S.X, CFSG.Open.GLBConj g (S.H R₁) = S.H R₂ := by
  obtain ⟨d, hd⟩ := S.T_nonempty h2
  obtain ⟨x, hx, hdx⟩ := S.exists_mem_T h1 hd.1
  have hR : R₂ = R₁.map (x : M →ₗ[ZMod 2] M) := by
    by_contra hne
    obtain ⟨v, hv, hdv⟩ := hd.2
    exact hdv (S.fix_of_ne (S.isMin_map h1 hx) h2 (fun h => hne h.symm) hdx v hv)
  refine ⟨x⁻¹, S.X.inv_mem hx, ?_⟩
  rw [S.H_conj (S.X.inv_mem hx), inv_inv, hR]

theorem identB_equiv {R₁ R₂ : Submodule (ZMod 2) M} (h1 : S.IsMin R₁) (h2 : S.IsMin R₂) :
    Nonempty (↥(S.H R₁) ≃* ↥(S.H R₂)) := by
  obtain ⟨g, -, hg⟩ := S.identB_conj h1 h2
  rw [← hg]
  exact ⟨Subgroup.equivMapOfInjective _ _ (MulAut.conj g⁻¹).injective⟩

theorem identB_eq_one [Finite M] {w : 𝔾} (hw : w ∈ S.W) (h : ∀ R, S.IsMin R → w ∈ i285_fix R) :
    w = 1 := by
  obtain ⟨R₀, hR₀⟩ := S.exists_isMin
  have hP : S.P ≤ i285_fixSub w := by
    rw [← S.isMin_iSup_map hR₀]
    refine iSup_le fun x => ?_
    intro v hv
    exact i285_mem_fixSub.2 (h _ (S.isMin_map hR₀ x.2) v hv)
  refine S.faithful hw fun v hv => ?_
  rw [i285_mem_fixSub.1 (hP hv), sub_self]
  exact S.Q.zero_mem

@[expose] def identBI {r : ℕ} (W : Fin (r + 1) → Subgroup 𝔾) (j : Fin (r + 1)) :
    Set (Submodule (ZMod 2) M) :=
  {R | S.IsMin R ∧ S.T R ⊆ (W j : Set 𝔾)}

theorem identB_iSup [Finite M] {r : ℕ} {W : Fin (r + 1) → Subgroup 𝔾}
    (hW : i285_Decomp S.X S.τ r W)
    (hgen : ∀ j, W j = Subgroup.closure (S.D ∩ (W j : Set 𝔾)))
    (hfac : ∀ R : Submodule (ZMod 2) M, S.IsMin R → ∃ j, S.T R ⊆ (W j : Set 𝔾)) (j : Fin (r + 1)) :
    W j = ⨆ R : S.identBI W j, S.H R.1 := by
  obtain ⟨-, -, -, hind, -⟩ := hW
  refine le_antisymm ((hgen j).le.trans ?_) (iSup_le fun R => (Subgroup.closure_le _).2 R.2.2)
  rw [Subgroup.closure_le]
  rintro d ⟨hdD, hdW⟩
  obtain ⟨R₀, hR₀⟩ := S.exists_isMin
  obtain ⟨x, hx, hdT⟩ := S.exists_mem_T hR₀ hdD
  have hmin := S.isMin_map hR₀ hx
  obtain ⟨j', hj'⟩ := hfac _ hmin
  have hd1 : d ≠ 1 := by
    obtain ⟨g, hg, rfl⟩ := hdD
    intro h
    apply S.τ_ne_one
    calc S.τ = g * (g⁻¹ * S.τ * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; group
  have hjj : j' = j := by
    by_contra hne
    have : d ∈ W j ⊓ ⨆ k : {k // k ≠ j}, W k :=
      ⟨hdW, Subgroup.mem_iSup_of_mem ⟨j', hne⟩ (hj' hdT)⟩
    rw [hind j, Subgroup.mem_bot] at this
    exact hd1 this
  rw [hjj] at hj'
  exact Subgroup.mem_iSup_of_mem (⟨_, hmin, hj'⟩ : S.identBI W j) (Subgroup.subset_closure hdT)

theorem identB_normal [Finite M] {r : ℕ} {W : Fin (r + 1) → Subgroup 𝔾}
    (hW : i285_Decomp S.X S.τ r W)
    (hgen : ∀ j, W j = Subgroup.closure (S.D ∩ (W j : Set 𝔾)))
    (hfac : ∀ R : Submodule (ZMod 2) M, S.IsMin R → ∃ j, S.T R ⊆ (W j : Set 𝔾)) (j : Fin (r + 1))
    (R : S.identBI W j) : ∀ g ∈ W j, ∀ a ∈ S.H R.1, g * a * g⁻¹ ∈ S.H R.1 := by
  intro g hg a ha
  rw [S.identB_iSup hW hgen hfac j] at hg
  have : (⨆ R' : S.identBI W j, S.H R'.1) ≤ Subgroup.normalizer (S.H R.1) := by
    refine iSup_le fun R' => ?_
    by_cases hR : R' = R
    · subst hR
      exact Subgroup.le_normalizer
    · rw [Subgroup.le_normalizer_iff]
      intro g' hg' k hk
      have hc := Subgroup.mem_centralizer_iff.1
        (S.H_le_centralizer R'.2.1 R.2.1 (fun h => hR (Subtype.ext h)) hg') k hk
      have e : g' * k * g'⁻¹ = k := by rw [← hc]; group
      rw [e]
      exact hk
  exact (Subgroup.mem_normalizer_iff.1 (this hg) a).1 ha

theorem identB_commute {r : ℕ} {W : Fin (r + 1) → Subgroup 𝔾} {j : Fin (r + 1)}
    {R₁ R₂ : S.identBI W j} (hne : R₁ ≠ R₂) {x y : 𝔾} (hx : x ∈ S.H R₁.1) (hy : y ∈ S.H R₂.1) :
    Commute x y :=
  (Subgroup.mem_centralizer_iff.1
    (S.H_le_centralizer R₁.2.1 R₂.2.1 (fun h => hne (Subtype.ext h)) hx) y hy).symm

theorem identB_indep [Finite M] {r : ℕ} (W : Fin (r + 1) → Subgroup 𝔾) (j : Fin (r + 1)) :
    iSupIndep fun R : S.identBI W j => S.H R.1 := by
  intro R
  rw [disjoint_iff, eq_bot_iff]
  rintro w ⟨hw1, hw2⟩
  rw [Subgroup.mem_bot]
  refine S.identB_eq_one (S.H_le_W _ hw1) fun R''' hR''' => ?_
  by_cases hk : R''' = R.1
  · subst hk
    have : (⨆ (R' : S.identBI W j) (_ : R' ≠ R), S.H R'.1) ≤ i285_fix R.1 :=
      iSup_le fun R' => iSup_le fun hR' =>
        S.H_le_fix R'.2.1 R.2.1 (fun h => hR' (Subtype.ext h))
    exact this hw2
  · exact S.H_le_fix R.2.1 hR''' (Ne.symm hk) hw1

end i285_Setup

end Blocks

end CFSG.HardMathSupport.Solomon.Coordinator
