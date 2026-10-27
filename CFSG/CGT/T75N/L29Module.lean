module

public import CFSG.CGT.T75N.L29Plane
public import CFSG.CGT.T75N.BinTransvection
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherSubspaceIndex

public section

namespace CFSG.CGT.T75N

open Matrix MatrixGroups CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {F : Type} [Field F] {m : ℕ}

theorem exists_indep_pair (r : Fin (m + 2) → F) (hr : r ≠ 0) :
    ∃ z : Fin (m + 2) → F, LinearIndependent F ![r, z] := by
  obtain ⟨i, hi⟩ : ∃ i, r i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hr (funext hcon)
  obtain ⟨j, hj⟩ : ∃ j : Fin (m + 2), j ≠ i := by
    by_cases hi0 : i = 0
    · exact ⟨1, by rw [hi0]; exact Fin.zero_ne_one.symm⟩
    · exact ⟨0, fun h => hi0 h.symm⟩
  refine ⟨Pi.single j 1, LinearIndependent.pair_iff.2 fun s t hst => ?_⟩
  have h1 := congrFun hst i
  simp [hj.symm] at h1
  rcases h1 with h1 | h1
  · subst h1
    simp at hst
    exact ⟨rfl, hst⟩
  · exact absurd h1 hi

theorem exists_plane (x y : Fin (m + 2) → F) :
    ∃ W : Submodule F (Fin (m + 2) → F), Module.finrank F W = 2 ∧ x ∈ W ∧ y ∈ W := by
  have hspan : ∀ (r z : Fin (m + 2) → F), LinearIndependent F ![r, z] →
      Module.finrank F (Submodule.span F (Set.range ![r, z])) = 2 := fun r z h => by
    rw [finrank_span_eq_card h]
    simp
  have hmem1 : ∀ r z : Fin (m + 2) → F, r ∈ Submodule.span F (Set.range ![r, z]) :=
    fun r z => Submodule.subset_span ⟨0, rfl⟩
  have hmem2 : ∀ r z : Fin (m + 2) → F, z ∈ Submodule.span F (Set.range ![r, z]) :=
    fun r z => Submodule.subset_span ⟨1, rfl⟩
  by_cases hli : LinearIndependent F ![x, y]
  · exact ⟨_, hspan x y hli, hmem1 x y, hmem2 x y⟩
  · by_cases hx : x = 0
    · by_cases hy : y = 0
      · have h0 : (Pi.single 0 1 : Fin (m + 2) → F) ≠ 0 := by
          intro h
          have := congrFun h 0
          simp at this
        obtain ⟨z, hz⟩ := exists_indep_pair _ h0
        exact ⟨_, hspan _ z hz, by rw [hx]; exact Submodule.zero_mem _,
          by rw [hy]; exact Submodule.zero_mem _⟩
      · obtain ⟨z, hz⟩ := exists_indep_pair y hy
        exact ⟨_, hspan y z hz, by rw [hx]; exact Submodule.zero_mem _, hmem1 y z⟩
    · obtain ⟨z, hz⟩ := exists_indep_pair x hx
      refine ⟨_, hspan x z hz, hmem1 x z, ?_⟩
      rw [LinearIndependent.pair_iff] at hli
      push Not at hli
      obtain ⟨s, t, hst, hne⟩ := hli
      have ht : t ≠ 0 := by
        rintro rfl
        rw [zero_smul, add_zero, smul_eq_zero] at hst
        rcases hst with hs | hx'
        · exact hne hs rfl
        · exact hx hx'
      have hy : y = (-(s / t)) • x := by
        have h1 : t • y = (-s) • x := by
          rw [neg_smul]
          exact eq_neg_of_add_eq_zero_right hst
        calc y = t⁻¹ • (t • y) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
          _ = (-(s / t)) • x := by
            rw [h1, smul_smul]
            congr 1
            field_simp
      rw [hy]
      exact Submodule.smul_mem _ _ (hmem1 x z)

theorem two_le_of_ne (k : Fin (m + 2)) (h0 : k ≠ 0) (h1 : k ≠ 1) : 2 ≤ (k : ℕ) := by
  by_contra hlt
  push Not at hlt
  have : (k : ℕ) = 0 ∨ (k : ℕ) = 1 := by omega
  rcases this with h | h
  · exact h0 (Fin.ext h)
  · exact h1 (Fin.ext h)

section Add

variable {V : Type} [CommGroup V] {σ : SpecialLinearGroup (Fin (m + 2)) F →* MulAut V}
  {Φ : V → (Fin (m + 2) → F)} (h : EqBij σ Φ) (hV2 : ∀ v : V, v * v = 1) (hF2 : (2 : F) = 0)
include h hV2 hF2

theorem EqBij.add_of_mem_plane (W : Submodule F (Fin (m + 2) → F)) (hW : Module.finrank F W = 2)
    {v v' : V} (hv : Φ v ∈ W) (hv' : Φ v' ∈ W) : Φ (v * v') = Φ v + Φ v' := by
  obtain ⟨g, hg⟩ := exists_map_eq_of_finrank_eq (K := F) (n := m + 2)
    (W := flagSpace (m + 2) F 2) (W' := W) (by rw [finrank_flagSpace (by omega), hW])
  have hmem : ∀ w : V, Φ w ∈ W → ∀ k : Fin (m + 2), k ≠ 0 → k ≠ 1 → Φ (σ g⁻¹ w) k = 0 := by
    intro w hw k hk0 hk1
    rw [h.equivariant]
    rw [← hg] at hw
    obtain ⟨x, hx, hxw⟩ := Submodule.mem_map.1 hw
    rw [mulVecLin_apply] at hxw
    rw [← hxw, mulVec_mulVec]
    have h1 : ((g⁻¹ : SpecialLinearGroup (Fin (m + 2)) F) :
        Matrix (Fin (m + 2)) (Fin (m + 2)) F) * (g : Matrix (Fin (m + 2)) (Fin (m + 2)) F) = 1 :=
      coe_inv_mul_coe g
    rw [h1, one_mulVec]
    exact (mem_flagSpace.1 hx) k (two_le_of_ne k hk0 hk1)
  have hu := h.plane_add hV2 hF2 (hmem v hv) (hmem v' hv')
  have hgg : ∀ w : V, σ g (σ g⁻¹ w) = w := fun w => by
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, _root_.map_one, MulAut.one_apply]
  have e1 : v * v' = σ g (σ g⁻¹ v * σ g⁻¹ v') := by
    rw [map_mul, hgg, hgg]
  have e2 : ∀ w : V, Φ w = (g : Matrix (Fin (m + 2)) (Fin (m + 2)) F) *ᵥ Φ (σ g⁻¹ w) := by
    intro w
    rw [← h.equivariant, hgg]
  rw [e1, h.equivariant, hu, mulVec_add, ← e2, ← e2]

theorem EqBij.add (v v' : V) : Φ (v * v') = Φ v + Φ v' := by
  obtain ⟨W, hW, hv, hv'⟩ := exists_plane (Φ v) (Φ v')
  exact h.add_of_mem_plane hV2 hF2 W hW hv hv'

@[expose] noncomputable def EqBij.mulEquiv : V ≃* Multiplicative (Fin (m + 2) → F) :=
  { Equiv.ofBijective (fun v => Multiplicative.ofAdd (Φ v))
      ⟨fun a b hab => h.bijective.1 (by simpa using hab), fun y => by
        obtain ⟨v, hv⟩ := h.bijective.2 (Multiplicative.toAdd y)
        exact ⟨v, by simp [hv]⟩⟩ with
    map_mul' := fun a b => by
      show Multiplicative.ofAdd (Φ (a * b)) =
        Multiplicative.ofAdd (Φ a) * Multiplicative.ofAdd (Φ b)
      rw [h.add hV2 hF2, ofAdd_add] }

theorem EqBij.mulEquiv_apply (v : V) :
    h.mulEquiv hV2 hF2 v = Multiplicative.ofAdd (Φ v) := rfl

end Add

section Natural

variable {V : Type} [CommGroup V] [Finite F]

theorem natural_module [CharP F 2] (hV2 : ∀ v : V, v * v = 1)
    (hcard : Nat.card V = Nat.card F ^ (m + 2))
    (σ : SpecialLinearGroup (Fin (m + 2)) F →* MulAut V) (a : V) (ha : a ≠ 1)
    (hstab : ∀ g : SpecialLinearGroup (Fin (m + 2)) F, σ g a = a ↔
      (g : Matrix (Fin (m + 2)) (Fin (m + 2)) F) *ᵥ (Pi.single 0 1 : Fin (m + 2) → F) =
        Pi.single 0 1)
    (htrans : ∀ w : V, w ≠ 1 → ∃ g : SpecialLinearGroup (Fin (m + 2)) F, σ g a = w) :
    ∃ φ : V ≃* Multiplicative (Fin (m + 2) → F), ∀ (g : SpecialLinearGroup (Fin (m + 2)) F)
      (v : V), φ (σ g v) = Multiplicative.ofAdd
        ((g : Matrix (Fin (m + 2)) (Fin (m + 2)) F) *ᵥ Multiplicative.toAdd (φ v)) := by
  classical
  have hF2 : (2 : F) = 0 := by
    have := CharP.cast_eq_zero F 2
    simpa using this
  set e0 : Fin (m + 2) → F := Pi.single 0 1 with he0
  have he0ne : e0 ≠ 0 := fun h => by
    have := congrFun h 0
    simp [he0] at this
  let Φ : V → (Fin (m + 2) → F) := fun v =>
    if hv : ∃ g : SpecialLinearGroup (Fin (m + 2)) F, σ g a = v then
      ((Classical.choose hv : SpecialLinearGroup (Fin (m + 2)) F) :
        Matrix (Fin (m + 2)) (Fin (m + 2)) F) *ᵥ e0 else 0
  have hnz : ∀ v : V, v ≠ 1 → ∃ g : SpecialLinearGroup (Fin (m + 2)) F, σ g a = v :=
    htrans
  have hΦspec : ∀ g : SpecialLinearGroup (Fin (m + 2)) F, Φ (σ g a) =
      (g : Matrix (Fin (m + 2)) (Fin (m + 2)) F) *ᵥ e0 := by
    intro g
    have hv : ∃ g' : SpecialLinearGroup (Fin (m + 2)) F, σ g' a = σ g a := ⟨g, rfl⟩
    simp only [Φ, hv, ↓reduceDIte]
    set g₀ := Classical.choose hv with hg₀
    have hg₀a : σ g₀ a = σ g a := Classical.choose_spec hv
    have h1 : σ (g₀⁻¹ * g) a = a := by
      rw [map_mul, MulAut.mul_apply, ← hg₀a, map_inv, ← MulAut.mul_apply, inv_mul_cancel,
        MulAut.one_apply]
    have h2 := (hstab _).1 h1
    rw [SpecialLinearGroup.coe_mul, ← mulVec_mulVec] at h2
    have h3 := congrArg (fun x => (g₀ : Matrix (Fin (m + 2)) (Fin (m + 2)) F) *ᵥ x) h2
    simp only [mulVec_mulVec] at h3
    rw [← Matrix.mul_assoc, coe_mul_coe_inv, Matrix.one_mul] at h3
    exact h3.symm
  have hΦ1 : Φ 1 = 0 := by
    have hv : ¬ ∃ g : SpecialLinearGroup (Fin (m + 2)) F, σ g a = 1 := by
      rintro ⟨g, hg⟩
      apply ha
      have : σ g a = σ g 1 := by rw [hg, _root_.map_one]
      exact (σ g).injective this
    simp only [Φ, hv, ↓reduceDIte]
  have hΦeq : ∀ (g : SpecialLinearGroup (Fin (m + 2)) F) (v : V), Φ (σ g v) =
      (g : Matrix (Fin (m + 2)) (Fin (m + 2)) F) *ᵥ Φ v := by
    intro g v
    by_cases hv : v = 1
    · rw [hv, _root_.map_one, hΦ1, mulVec_zero]
    · obtain ⟨h, rfl⟩ := hnz v hv
      rw [← MulAut.mul_apply, ← map_mul, hΦspec, hΦspec, SpecialLinearGroup.coe_mul,
        ← mulVec_mulVec]
  have hΦnz : ∀ v : V, v ≠ 1 → Φ v ≠ 0 := by
    intro v hv
    obtain ⟨h, rfl⟩ := hnz v hv
    rw [hΦspec]
    intro h0
    apply he0ne
    have := congrArg (fun x => ((h⁻¹ : SpecialLinearGroup (Fin (m + 2)) F) :
      Matrix (Fin (m + 2)) (Fin (m + 2)) F) *ᵥ x) h0
    simp only [mulVec_mulVec, mulVec_zero] at this
    rw [coe_inv_mul_coe, one_mulVec] at this
    exact this
  have hΦinj : Function.Injective Φ := by
    intro v w hvw
    by_cases hv : v = 1
    · by_cases hw : w = 1
      · rw [hv, hw]
      · exact absurd (by rw [← hvw, hv, hΦ1]) (hΦnz w hw)
    · by_cases hw : w = 1
      · exact absurd (by rw [hvw, hw, hΦ1]) (hΦnz v hv)
      · obtain ⟨g, rfl⟩ := hnz v hv
        obtain ⟨h, rfl⟩ := hnz w hw
        rw [hΦspec, hΦspec] at hvw
        have h1 : σ (h⁻¹ * g) a = a := by
          rw [hstab]
          rw [SpecialLinearGroup.coe_mul, ← mulVec_mulVec, hvw, mulVec_mulVec, coe_inv_mul_coe,
            one_mulVec]
        have h2 := congrArg (fun x => σ h x) h1
        simp only [← MulAut.mul_apply, ← map_mul, mul_inv_cancel_left] at h2
        exact h2
  have hΦbij : Function.Bijective Φ :=
    hΦinj.bijective_of_nat_card_le (by
      rw [hcard, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin (m + 2)), Fintype.card_fin])
  have hE : EqBij σ Φ := ⟨hΦeq, hΦbij, hΦ1⟩
  refine ⟨hE.mulEquiv hV2 hF2, fun g v => ?_⟩
  rw [EqBij.mulEquiv_apply, EqBij.mulEquiv_apply, hΦeq]
  rfl

end Natural

end CFSG.CGT.T75N
