module

public import CFSG.ClassicalGroups.Orthogonal.SiegelRT1Basic
public import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis

public section

namespace CFSG.ClassicalGroups.Orthogonal.SiegelRT1

open CFSG.HardMathSupport.Kantor79 QuadraticMap Module

variable {K : Type*} [Field K] [CharP K 2] {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Qf : QuadraticForm K V}

omit [CharP K 2] [FiniteDimensional K V] in
theorem orthogonal_sup_polar (A B : Submodule K V) :
    LinearMap.BilinForm.orthogonal (polarBilin Qf) (A ⊔ B) =
      LinearMap.BilinForm.orthogonal (polarBilin Qf) A ⊓
        LinearMap.BilinForm.orthogonal (polarBilin Qf) B := by
  ext v
  simp only [Submodule.mem_inf, LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro h
    exact ⟨fun a ha => h a (Submodule.mem_sup_left ha),
      fun b hb => h b (Submodule.mem_sup_right hb)⟩
  · rintro ⟨h1, h2⟩ w hw
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hw
    rw [map_add, LinearMap.add_apply, h1 a ha, h2 b hb, add_zero]

theorem movedSpace_mul_eq_sup_of_commute (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0)
    {x y : V ≃ₗ[K] V} (hx : IsLongRootElement Qf x) (hy : IsLongRootElement Qf y)
    (hxy : x * y = y * x) (hdisj : Disjoint (movedSpace x) (movedSpace y)) :
    movedSpace (x * y) = movedSpace x ⊔ movedSpace y := by
  have hyx : movedSpace y ≤ LinearMap.BilinForm.orthogonal (polarBilin Qf) (movedSpace x) :=
    movedSpace_le_orthogonal_of_commute hx hy hxy hdisj
  have hkx := ker_sub_one_eq_orthogonal_movedSpace hnd hx.isometry
  have hky := ker_sub_one_eq_orthogonal_movedSpace hnd hy.isometry
  have happ : ∀ v, (x * y) v - v = (x v - v) + (y v - v) := by
    intro v
    have hmem : y v - v ∈ LinearMap.ker ((x : V →ₗ[K] V) - 1) := by
      rw [hkx]
      exact hyx (sub_mem_movedSpace y v)
    have hmem' : x (y v - v) = y v - v := by
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, LinearEquiv.coe_coe,
        sub_eq_zero] at hmem
      exact hmem
    rw [LinearEquiv.mul_apply]
    have : x (y v) = x (y v - v) + x v := by rw [← map_add, sub_add_cancel]
    rw [this, hmem']
    abel
  have hle : movedSpace (x * y) ≤ movedSpace x ⊔ movedSpace y := by
    rintro _ ⟨v, rfl⟩
    change (x * y) v - v ∈ _
    rw [happ]
    exact Submodule.add_mem_sup (sub_mem_movedSpace x v) (sub_mem_movedSpace y v)
  have hker : LinearMap.ker (((x * y : V ≃ₗ[K] V) : V →ₗ[K] V) - 1) =
      LinearMap.ker ((x : V →ₗ[K] V) - 1) ⊓ LinearMap.ker ((y : V →ₗ[K] V) - 1) := by
    ext v
    simp only [LinearMap.mem_ker, Submodule.mem_inf, LinearMap.sub_apply, Module.End.one_apply,
      LinearEquiv.coe_coe]
    rw [happ]
    constructor
    · intro h
      have hx0 : x v - v ∈ movedSpace x ⊓ movedSpace y := by
        refine ⟨sub_mem_movedSpace x v, ?_⟩
        have : x v - v = -(y v - v) := eq_neg_of_add_eq_zero_left h
        rw [this]
        exact neg_mem (sub_mem_movedSpace y v)
      rw [hdisj.eq_bot, Submodule.mem_bot] at hx0
      refine ⟨hx0, ?_⟩
      rw [hx0, zero_add] at h
      exact h
    · rintro ⟨h1, h2⟩
      rw [h1, h2, add_zero]
  have hdimsup : finrank K ↥(movedSpace x ⊔ movedSpace y) = 4 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (movedSpace x) (movedSpace y)
    rw [hdisj.eq_bot, finrank_bot, add_zero, hx.finrank_movedSpace hnd,
      hy.finrank_movedSpace hnd] at h
    exact h
  have hdim : finrank K ↥(movedSpace (x * y)) = 4 := by
    have hrn := LinearMap.finrank_range_add_finrank_ker
      (((x * y : V ≃ₗ[K] V) : V →ₗ[K] V) - 1)
    rw [hker, hkx, hky, ← orthogonal_sup_polar, finrank_orthogonal_polar hnd, hdimsup] at hrn
    have h4 : 4 ≤ finrank K V := hdimsup ▸ Submodule.finrank_le _
    change finrank K ↥(movedSpace (x * y)) + (finrank K V - 4) = finrank K V at hrn
    omega
  exact Submodule.eq_of_le_of_finrank_eq hle (hdim.trans hdimsup.symm)

theorem movedSpace_inf_ne_bot_of_commute (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0)
    {x y : V ≃ₗ[K] V} (hx : IsLongRootElement Qf x) (hy : IsLongRootElement Qf y)
    (hxy : x * y = y * x) (hxy' : IsLongRootElement Qf (x * y)) :
    movedSpace x ⊓ movedSpace y ≠ ⊥ := by
  intro h0
  have hdisj : Disjoint (movedSpace x) (movedSpace y) := disjoint_iff.mpr h0
  have h2 := hxy'.finrank_movedSpace hnd
  rw [movedSpace_mul_eq_sup_of_commute hnd hx hy hxy hdisj] at h2
  have h := Submodule.finrank_sup_add_finrank_inf_eq (movedSpace x) (movedSpace y)
  rw [h0, finrank_bot, add_zero, hx.finrank_movedSpace hnd, hy.finrank_movedSpace hnd, h2] at h
  omega

omit [CharP K 2] in
theorem finrank_sup_add_one_le_of_inf_ne_bot {A B : Submodule K V} (h : A ⊓ B ≠ ⊥) :
    finrank K ↥(A ⊔ B) + 1 ≤ finrank K A + finrank K B := by
  have h1 : 0 < finrank K ↥(A ⊓ B) :=
    Nat.pos_of_ne_zero fun h0 => h (Submodule.finrank_eq_zero.mp h0)
  have := Submodule.finrank_sup_add_finrank_inf_eq A B
  omega

theorem finrank_commutatorSpace_le_seven (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0)
    {x₁ x₂ x₃ x₄ y : V ≃ₗ[K] V} (h₁ : IsLongRootElement Qf x₁) (h₂ : IsLongRootElement Qf x₂)
    (h₃ : IsLongRootElement Qf x₃) (h₄ : IsLongRootElement Qf x₄) (hy : IsLongRootElement Qf y)
    (hyH : y ∈ Subgroup.closure ({x₁, x₂, x₃} : Set (V ≃ₗ[K] V)))
    (hcomm : x₄ * y = y * x₄) (h₄y : IsLongRootElement Qf (x₄ * y)) :
    finrank K ↥(commutatorSpace (Subgroup.closure ({x₁, x₂, x₃, x₄} : Set (V ≃ₗ[K] V)))) ≤ 7 := by
  have hrange3 : ({x₁, x₂, x₃} : Set (V ≃ₗ[K] V)) = Set.range ![x₁, x₂, x₃] := by
    ext g
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range, Fin.exists_fin_succ,
      Matrix.cons_val_zero, Matrix.cons_val_succ, IsEmpty.exists_iff, or_false]
    tauto
  have hrange4 : ({x₁, x₂, x₃, x₄} : Set (V ≃ₗ[K] V)) = Set.range ![x₁, x₂, x₃, x₄] := by
    ext g
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range, Fin.exists_fin_succ,
      Matrix.cons_val_zero, Matrix.cons_val_succ, IsEmpty.exists_iff, or_false]
    tauto
  set S := movedSpace x₁ ⊔ movedSpace x₂ ⊔ movedSpace x₃ with hS
  have hS3 : commutatorSpace (Subgroup.closure ({x₁, x₂, x₃} : Set (V ≃ₗ[K] V))) = S := by
    rw [hrange3, commutatorSpace_closure_eq_iSup_movedSpace]
    apply le_antisymm
    · refine iSup_le fun i => ?_
      fin_cases i
      · exact le_sup_left.trans le_sup_left
      · exact le_sup_right.trans le_sup_left
      · exact le_sup_right
    · exact sup_le (sup_le (le_iSup_of_le 0 le_rfl) (le_iSup_of_le 1 le_rfl))
        (le_iSup_of_le 2 le_rfl)
  have hS4 : commutatorSpace (Subgroup.closure ({x₁, x₂, x₃, x₄} : Set (V ≃ₗ[K] V))) =
      S ⊔ movedSpace x₄ := by
    rw [hrange4, commutatorSpace_closure_eq_iSup_movedSpace]
    apply le_antisymm
    · refine iSup_le fun i => ?_
      fin_cases i
      · exact (le_sup_left.trans le_sup_left).trans le_sup_left
      · exact (le_sup_right.trans le_sup_left).trans le_sup_left
      · exact le_sup_right.trans le_sup_left
      · exact le_sup_right
    · exact sup_le (sup_le (sup_le (le_iSup_of_le 0 le_rfl) (le_iSup_of_le 1 le_rfl))
        (le_iSup_of_le 2 le_rfl)) (le_iSup_of_le 3 le_rfl)
  have hyS : movedSpace y ≤ S := hS3 ▸ movedSpace_le_commutatorSpace hyH
  have hov : movedSpace x₄ ⊓ movedSpace y ≠ ⊥ := movedSpace_inf_ne_bot_of_commute hnd h₄ hy
    hcomm h₄y
  have hov' : S ⊓ movedSpace x₄ ≠ ⊥ := by
    intro h0
    apply hov
    rw [eq_bot_iff]
    intro v hv
    have : v ∈ S ⊓ movedSpace x₄ := ⟨hyS hv.2, hv.1⟩
    rwa [h0] at this
  have hS6 : finrank K ↥S ≤ 6 := by
    have e1 := Submodule.finrank_add_le_finrank_add_finrank (movedSpace x₁ ⊔ movedSpace x₂)
      (movedSpace x₃)
    have e2 := Submodule.finrank_add_le_finrank_add_finrank (movedSpace x₁) (movedSpace x₂)
    rw [h₁.finrank_movedSpace hnd, h₂.finrank_movedSpace hnd] at e2
    rw [h₃.finrank_movedSpace hnd, ← hS] at e1
    omega
  rw [hS4]
  have := finrank_sup_add_one_le_of_inf_ne_bot hov'
  rw [h₄.finrank_movedSpace hnd] at this
  omega

theorem finrank_commutatorSpace_cons_le (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0)
    {k : ℕ} (x : Fin k → V ≃ₗ[K] V) (hx : ∀ i, IsLongRootElement Qf (x i))
    {e y : V ≃ₗ[K] V} (he : IsLongRootElement Qf e) (hy : IsLongRootElement Qf y)
    (hyH : y ∈ Subgroup.closure (Set.range x)) (hcomm : e * y = y * e)
    (hey : IsLongRootElement Qf (e * y)) :
    finrank K ↥(commutatorSpace (Subgroup.closure (Set.range (Fin.cons e x)))) ≤ 2 * k + 1 := by
  set S := commutatorSpace (Subgroup.closure (Set.range x)) with hS
  have hSk : finrank K ↥S ≤ k * 2 := by
    have := finrank_commutatorSpace_le x (r := 2) fun i => (hx i).finrank_movedSpace hnd |>.le
    simpa [Fintype.card_fin] using this
  have hcons : commutatorSpace (Subgroup.closure (Set.range (Fin.cons e x))) =
      movedSpace e ⊔ S := by
    rw [commutatorSpace_closure_eq_iSup_movedSpace, hS, commutatorSpace_closure_eq_iSup_movedSpace]
    apply le_antisymm
    · refine iSup_le fun i => ?_
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [Fin.cons_zero]
        exact le_sup_left
      · simp only [Fin.cons_succ]
        exact le_sup_of_le_right (le_iSup (fun i => movedSpace (x i)) j)
    · refine sup_le ?_ (iSup_le fun j => ?_)
      · exact le_iSup_of_le 0 (by simp only [Fin.cons_zero]; exact le_rfl)
      · exact le_iSup_of_le j.succ (by simp only [Fin.cons_succ]; exact le_rfl)
  have hyS : movedSpace y ≤ S := movedSpace_le_commutatorSpace hyH
  have hov : movedSpace e ⊓ movedSpace y ≠ ⊥ := movedSpace_inf_ne_bot_of_commute hnd he hy
    hcomm hey
  have hov' : movedSpace e ⊓ S ≠ ⊥ := by
    intro h0
    apply hov
    rw [eq_bot_iff]
    intro v hv
    have : v ∈ movedSpace e ⊓ S := ⟨hv.1, hyS hv.2⟩
    rwa [h0] at this
  rw [hcons]
  have := finrank_sup_add_one_le_of_inf_ne_bot hov'
  rw [he.finrank_movedSpace hnd] at this
  omega

theorem finrank_eq_six_of_closure_four (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0)
    {X : Type*} [Group X] (ρ : X →* (V ≃ₗ[K] V)) (hV : commutatorSpace ρ.range = ⊤)
    {d₁ d₂ d₃ e y : X} (h₁ : IsLongRootElement Qf (ρ d₁)) (h₂ : IsLongRootElement Qf (ρ d₂))
    (h₃ : IsLongRootElement Qf (ρ d₃)) (he : IsLongRootElement Qf (ρ e))
    (hy : IsLongRootElement Qf (ρ y))
    (hgen : Subgroup.closure ({d₁, d₂, d₃, e} : Set X) = ⊤)
    (hyH : y ∈ Subgroup.closure ({d₁, d₂, d₃} : Set X)) (hcomm : e * y = y * e)
    (hey : IsLongRootElement Qf (ρ (e * y))) (h6 : 6 ≤ finrank K V) :
    finrank K V = 6 := by
  have hrange : ρ.range = Subgroup.closure ({ρ d₁, ρ d₂, ρ d₃, ρ e} : Set (V ≃ₗ[K] V)) := by
    rw [MonoidHom.range_eq_map, ← hgen, MonoidHom.map_closure]
    congr 1
    simp [Set.image_insert_eq]
  have hyH' : ρ y ∈ Subgroup.closure ({ρ d₁, ρ d₂, ρ d₃} : Set (V ≃ₗ[K] V)) := by
    have := Subgroup.mem_map_of_mem ρ hyH
    rw [MonoidHom.map_closure] at this
    simpa [Set.image_insert_eq] using this
  have h7 := finrank_commutatorSpace_le_seven hnd h₁ h₂ h₃ he hy hyH'
    (by rw [← map_mul, ← map_mul, hcomm]) (by rwa [← map_mul])
  rw [← hrange, hV, finrank_top] at h7
  have hev : Even (finrank K V) := LinearMap.BilinForm.IsAlt.even_finrank
    (B := polarBilin Qf) (fun x => polar_self_eq_zero x) (nondegenerate_polarBilin hnd)
  obtain ⟨r, hr⟩ := hev
  omega

end CFSG.ClassicalGroups.Orthogonal.SiegelRT1
