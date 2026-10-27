module

public import CFSG.LieType.Universal.Unitary.BinaryModel.FixedLine
public import CFSG.LieType.SpecialLinear.ExteriorModel.WeightRank
public import CFSG.LieType.SpecialLinear.ExteriorModel.Reversal
public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.CaseAnalysis
public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.EndFieldModel

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar

open Module CFSG.Open CFSG.HardMathSupport.GuralnickMalle CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.LieType.SpecialLinear CFSG.LieType.SpecialLinear.ExteriorModel Matrix

theorem finrank_range_rep_conj_sub_one {G k V : Type*} [Group G] [Field k] [AddCommGroup V]
    [Module k V] (ρ : Representation k G V) (g a : G) :
    finrank k (LinearMap.range (ρ (g * a * g⁻¹) - 1)) = finrank k (LinearMap.range (ρ a - 1)) := by
  have hinv : ∀ v, ρ g (ρ g⁻¹ v) = v := fun v => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hinv' : ∀ v, ρ g⁻¹ (ρ g v) = v := fun v => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have h : ρ (g * a * g⁻¹) - 1 = ρ g ∘ₗ ((ρ a - 1) ∘ₗ ρ g⁻¹) := by
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.sub_apply, Module.End.one_apply, LinearMap.comp_apply, map_sub, hinv,
      map_mul, Module.End.mul_apply]
  have hsurj : LinearMap.range (ρ g⁻¹) = ⊤ :=
    LinearMap.range_eq_top.mpr fun v => ⟨ρ g v, hinv' v⟩
  have hinj : Function.Injective (ρ g) := fun v w hvw => by
    rw [← hinv' v, ← hinv' w, hvw]
  rw [h, LinearMap.range_comp, LinearMap.range_comp, hsurj, Submodule.map_top]
  exact (Submodule.equivMapOfInjective _ hinj _).finrank_eq.symm

variable {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ} {k : Type} [Field k] [CharP k 2]

theorem exists_perm_finrank_range_suRep_sub_one (φ₀ : K →+* k) {m : ℕ} (hm : 2 ≤ m)
    (ε : Fin f → Finset (Fin m)) {x : SU (unitaryInvolution K 2 f) m} (hx : x * x = 1)
    (hx1 : x ≠ 1) :
    ∃ π : Equiv.Perm (Fin m), π * π = 1 ∧ π ⟨0, by omega⟩ = ⟨1, by omega⟩ ∧
      finrank k (LinearMap.range (bRep ε (fun _ => permSL (k := k) π) - 1)) =
        finrank k (LinearMap.range (suRep φ₀ m ε x - 1)) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  let y := suSL (unitaryInvolution K 2 f) (n + 2) x
  have hy : y * y = 1 := by rw [← map_mul, hx, map_one]
  have hy1 : y ≠ 1 := by
    intro h
    apply hx1
    apply SUExtras.mat_injective
    rw [map_one, ← coe_suSL, show suSL (unitaryInvolution K 2 f) (n + 2) x = 1 from h]
    rfl
  obtain ⟨π, g, hπ, hπ0, hconj⟩ := exists_conj_eq_permMatrix_of_ne_one hy hy1
  refine ⟨π, hπ, by simpa using hπ0, ?_⟩
  let G := twistHom (suFrob φ₀ f) g
  have hG : G * suTwist φ₀ f (n + 2) x * G⁻¹ = fun _ => permSL (k := k) π := by
    rw [suTwist, MonoidHom.comp_apply, ← map_inv, ← map_mul, ← map_mul]
    funext r
    refine Subtype.ext ?_
    change ((SpecialLinearGroup.map (suFrob φ₀ f r) (g * y * g⁻¹) :
      SpecialLinearGroup (Fin (n + 2)) k) : Matrix (Fin (n + 2)) (Fin (n + 2)) k) =
        π.permMatrix k
    rw [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, hconj, permMatrix_map]
  have h := finrank_range_rep_conj_sub_one (bRep (k := k) ε) G (suTwist φ₀ f (n + 2) x)
  rw [hG] at h
  exact h

theorem movedTop_le_two_mul_codim (φ₀ : K →+* k) {m : ℕ} (hm : 2 ≤ m) (ε : Fin f → Finset (Fin m))
    {P : Subgroup (SU (unitaryInvolution K 2 f) m)} (hP : P ≠ ⊥) (hPel : IsElemAbelian 2 P) :
    movedTop hm ε ≤ 2 * (finrank k (BModel k ε) - finrank k (fixSubGen (suRep φ₀ m ε) P)) := by
  obtain ⟨⟨x, hxP⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hP
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hx : x * x = 1 := by rw [← sq]; exact hPel.2 x hxP
  obtain ⟨π, hπ, hπ01, hrank⟩ := exists_perm_finrank_range_suRep_sub_one φ₀ hm ε hx hx1'
  calc movedTop hm ε ≤ 2 * finrank k (LinearMap.range (bRep ε (fun _ => permSL (k := k) π) - 1)) :=
        by unfold movedTop; convert card_moved_top_le (k := k) ε hm π hπ hπ01
    _ = 2 * finrank k (LinearMap.range (suRep φ₀ m ε x - 1)) := by rw [hrank]
    _ ≤ _ := Nat.mul_le_mul_left 2 (finrank_range_sub_one_le _ P hxP)

theorem mul_sub_one_le_two_mul_codim (φ₀ : K →+* k) {m : ℕ} (hm : 5 ≤ m)
    (ε : Fin f → Finset (Fin m)) {P : Subgroup (SU (unitaryInvolution K 2 f) m)} (hP : P ≠ ⊥)
    (hPel : IsElemAbelian 2 P) (i₀ : Fin f) (hε' : ∀ i, i ≠ i₀ → ε i = ∅)
    (hε : ε i₀ = {⟨1, by omega⟩, ⟨2, by omega⟩} ∨ ε i₀ = {⟨m - 2, by omega⟩, ⟨m - 1, by omega⟩}) :
    m * (m - 1) ≤ 2 * (finrank k (BModel k ε) - finrank k (fixSubGen (suRep φ₀ m ε) P)) := by
  obtain ⟨⟨x, hxP⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hP
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hx : x * x = 1 := by rw [← sq]; exact hPel.2 x hxP
  obtain ⟨π, hπ, hπ01, hrank⟩ := exists_perm_finrank_range_suRep_sub_one φ₀ (by omega) ε hx hx1'
  have hlow : m * (m - 1) ≤ 2 * finrank k (LinearMap.range (bRep ε (fun _ => permSL (k := k) π) - 1)) := by
    rcases hε with hε | hε
    · exact mul_le_two_mul_finrank_of_one_two (k := k) hm ε i₀ hε hε' π hπ hπ01
    · exact mul_le_two_mul_finrank_of_last_two (k := k) hm ε i₀ hε hε' π hπ hπ01
  calc m * (m - 1) ≤ 2 * finrank k (LinearMap.range (bRep ε (fun _ => permSL (k := k) π) - 1)) := hlow
    _ = 2 * finrank k (LinearMap.range (suRep φ₀ m ε x - 1)) := by rw [hrank]
    _ ≤ _ := Nat.mul_le_mul_left 2 (finrank_range_sub_one_le _ P hxP)

end CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar
