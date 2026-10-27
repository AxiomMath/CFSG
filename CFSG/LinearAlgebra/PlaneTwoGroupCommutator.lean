module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import TauCeti.Algebra.CharP.LinearMaps
import TauCeti.RepresentationTheory.Unipotent.PowerOrder

public section

namespace CFSG.LinearAlgebra

variable {K E Γ : Type*} [Field K] [AddCommGroup E] [Module K E] [Group Γ]

private def restrictRep (ρ : Γ →* (E ≃ₗ[K] E)) (U : Submodule K E) (H : Subgroup Γ)
    (hH : ∀ h ∈ H, ∀ u ∈ U, ρ h u ∈ U) : Representation K H U where
  toFun h := (ρ h : E →ₗ[K] E).restrict (hH h h.2)
  map_one' := LinearMap.ext fun u => Subtype.ext (by
    show ρ 1 u = u
    rw [map_one]
    rfl)
  map_mul' g h := LinearMap.ext fun u => Subtype.ext (by
    show ρ ((g : Γ) * h) u = ρ g (ρ h u)
    rw [map_mul]
    rfl)

private def fixSub (ρ : Γ →* (E ≃ₗ[K] E)) (U : Submodule K E) (R : Subgroup Γ) :
    Submodule K E where
  carrier := {e | e ∈ U ∧ ∀ r ∈ R, ρ r e = e}
  add_mem' ha hb := ⟨U.add_mem ha.1 hb.1, fun r hr => by rw [map_add, ha.2 r hr, hb.2 r hr]⟩
  zero_mem' := ⟨U.zero_mem, fun r _ => map_zero _⟩
  smul_mem' c e he := ⟨U.smul_mem c he.1, fun r hr => by rw [map_smul, he.2 r hr]⟩

private def fixGrp (ρ : Γ →* (E ≃ₗ[K] E)) (U : Submodule K E) : Subgroup Γ where
  carrier := {g | ∀ u ∈ U, ρ g u = u}
  mul_mem' {a b} ha hb u hu := by
    show ρ (a * b) u = u
    rw [map_mul, LinearEquiv.mul_apply, hb u hu, ha u hu]
  one_mem' u _ := by
    show ρ 1 u = u
    rw [map_one]
    rfl
  inv_mem' {g} hg u hu := by
    show ρ g⁻¹ u = u
    calc ρ g⁻¹ u = ρ g⁻¹ (ρ g u) := by rw [hg u hu]
      _ = ρ (g⁻¹ * g) u := by rw [map_mul]; rfl
      _ = u := by rw [inv_mul_cancel, map_one]; rfl

private theorem apply_inv_apply (ρ : Γ →* (E ≃ₗ[K] E)) (g : Γ) (e : E) : ρ g (ρ g⁻¹ e) = e := by
  calc ρ g (ρ g⁻¹ e) = ρ (g * g⁻¹) e := by rw [map_mul]; rfl
    _ = e := by rw [mul_inv_cancel, map_one]; rfl

private theorem inv_apply_apply (ρ : Γ →* (E ≃ₗ[K] E)) (g : Γ) (e : E) : ρ g⁻¹ (ρ g e) = e := by
  calc ρ g⁻¹ (ρ g e) = ρ (g⁻¹ * g) e := by rw [map_mul]; rfl
    _ = e := by rw [inv_mul_cancel, map_one]; rfl

private theorem finrank_fixSub_eq_one [CharP K 2] (ρ : Γ →* (E ≃ₗ[K] E)) {U : Submodule K E}
    (hU : Module.finrank K U = 2) {R : Subgroup Γ} (hRU : ∀ r ∈ R, ∀ u ∈ U, ρ r u ∈ U)
    (hR : IsPGroup 2 R) (hR1 : ¬ ∀ r ∈ R, ∀ u ∈ U, ρ r u = u) :
    Module.finrank K (fixSub ρ U R) = 1 := by
  have : FiniteDimensional K U := Module.finite_of_finrank_pos (by omega)
  have : Nontrivial U := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  have hFU : fixSub ρ U R ≤ U := fun e he => he.1
  have : FiniteDimensional K (fixSub ρ U R) := Submodule.finiteDimensional_of_le hFU
  obtain ⟨v, hv0, hv⟩ :=
    Representation.exists_common_fixed_vector_of_isPGroup 2 hR (restrictRep ρ U R hRU)
  have hvF : (v : E) ∈ fixSub ρ U R := ⟨v.2, fun r hr => congrArg Subtype.val (hv ⟨r, hr⟩)⟩
  have hbot : fixSub ρ U R ≠ ⊥ := by
    intro h
    rw [h, Submodule.mem_bot] at hvF
    exact hv0 (Submodule.coe_eq_zero.mp hvF)
  have hne : fixSub ρ U R ≠ U := by
    intro h
    refine hR1 fun r hr u hu => ?_
    rw [← h] at hu
    exact hu.2 r hr
  have h1 := Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hFU hne)
  have h2 : Module.finrank K (fixSub ρ U R) ≠ 0 := fun h => hbot (Submodule.finrank_eq_zero.mp h)
  omega

private theorem mem_fixSub_of_mem (ρ : Γ →* (E ≃ₗ[K] E)) {U : Submodule K E} {P R : Subgroup Γ}
    (hPU : ∀ p ∈ P, ∀ u ∈ U, ρ p u ∈ U) (hRn : ∀ p ∈ P, ∀ r ∈ R, p * r * p⁻¹ ∈ R) {p : Γ}
    (hp : p ∈ P) {f : E} (hf : f ∈ fixSub ρ U R) : ρ p f ∈ fixSub ρ U R := by
  refine ⟨hPU p hp f hf.1, fun r hr => ?_⟩
  have h1 : p⁻¹ * r * p ∈ R := by simpa using hRn p⁻¹ (P.inv_mem hp) r hr
  have e : r * p = p * (p⁻¹ * r * p) := by group
  calc ρ r (ρ p f) = ρ (r * p) f := by rw [map_mul]; rfl
    _ = ρ (p * (p⁻¹ * r * p)) f := by rw [e]
    _ = ρ p (ρ (p⁻¹ * r * p) f) := by rw [map_mul]; rfl
    _ = ρ p f := by rw [hf.2 _ h1]

private theorem sq_restrictRep_sub_one [CharP K 2] (ρ : Γ →* (E ≃ₗ[K] E)) {U : Submodule K E}
    (hU : Module.finrank K U = 2) {P : Subgroup Γ} (hPU : ∀ p ∈ P, ∀ u ∈ U, ρ p u ∈ U)
    {p : P} {k : ℕ} (hp : p ^ 2 ^ k = 1) : (restrictRep ρ U P hPU p - 1) ^ 2 = 0 := by
  have : FiniteDimensional K U := Module.finite_of_finrank_pos (by omega)
  have h1 : restrictRep ρ U P hPU p ^ 2 ^ k = 1 := by rw [← map_pow, hp, map_one]
  obtain ⟨j, hj⟩ := Module.End.isNilpotent_sub_one_of_pow_expChar_pow_eq_one 2 k h1
  have h2 := Module.End.ker_pow_le_ker_pow_finrank (restrictRep ρ U P hPU p - 1) j
  rw [hj, LinearMap.ker_zero, hU, top_le_iff, LinearMap.ker_eq_top] at h2
  exact h2

private theorem apply_sub_fixed [CharP K 2] (ρ : Γ →* (E ≃ₗ[K] E)) {U : Submodule K E}
    (hU : Module.finrank K U = 2) {P : Subgroup Γ} (hPU : ∀ p ∈ P, ∀ u ∈ U, ρ p u ∈ U)
    {s : Γ} (hsP : s ∈ P) {k : ℕ} (hs : s ^ 2 ^ k = 1) {u : E} (hu : u ∈ U) :
    ρ s (ρ s u - u) = ρ s u - u := by
  have hp : (⟨s, hsP⟩ : P) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hs)
  have h1 : (restrictRep ρ U P hPU ⟨s, hsP⟩ - 1)
      ((restrictRep ρ U P hPU ⟨s, hsP⟩ - 1) ⟨u, hu⟩) = 0 := by
    rw [← Module.End.mul_apply, ← sq, sq_restrictRep_sub_one ρ hU hPU hp, LinearMap.zero_apply]
  have h2 : ρ s (ρ s u - u) - (ρ s u - u) = 0 := congrArg Subtype.val h1
  exact sub_eq_zero.mp h2

private theorem apply_eq_of_mem_fixSub [CharP K 2] (ρ : Γ →* (E ≃ₗ[K] E)) {U : Submodule K E}
    (hU : Module.finrank K U = 2) {P R : Subgroup Γ} (hPU : ∀ p ∈ P, ∀ u ∈ U, ρ p u ∈ U)
    (hRn : ∀ p ∈ P, ∀ r ∈ R, p * r * p⁻¹ ∈ R) (hF1 : Module.finrank K (fixSub ρ U R) = 1)
    {s : Γ} (hsP : s ∈ P) {k : ℕ} (hs : s ^ 2 ^ k = 1) {f : E} (hf : f ∈ fixSub ρ U R) :
    ρ s f = f := by
  have : Nontrivial (fixSub ρ U R) := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  obtain ⟨v, hv0⟩ := exists_ne (0 : fixSub ρ U R)
  have hdim := (finrank_eq_one_iff_of_nonzero' v hv0).mp hF1
  have hNv : ρ s v - v ∈ fixSub ρ U R :=
    sub_mem (mem_fixSub_of_mem ρ hPU hRn hsP v.2) v.2
  obtain ⟨c, hc⟩ := hdim ⟨_, hNv⟩
  have hc' : c • (v : E) = ρ s v - v := congrArg Subtype.val hc
  have h1 := apply_sub_fixed ρ hU hPU hsP hs v.2.1
  rw [← hc', map_smul] at h1
  have h2 : c • (c • (v : E)) = 0 := by
    rw [hc', smul_sub, h1, sub_self]
  have hv0' : (v : E) ≠ 0 := fun h => hv0 (Subtype.ext h)
  have hcc : c = 0 := by
    rw [smul_smul, smul_eq_zero] at h2
    rcases h2 with h | h
    · exact mul_self_eq_zero.mp h
    · exact absurd h hv0'
  have hsv : ρ s v = v := by
    rw [hcc, zero_smul] at hc'
    exact (sub_eq_zero.mp hc'.symm)
  obtain ⟨d, hd⟩ := hdim ⟨f, hf⟩
  have hd' : d • (v : E) = f := congrArg Subtype.val hd
  rw [← hd', map_smul, hsv]

private theorem sub_mem_fixSub [CharP K 2] (ρ : Γ →* (E ≃ₗ[K] E)) {U : Submodule K E}
    (hU : Module.finrank K U = 2) {P R : Subgroup Γ} (hPU : ∀ p ∈ P, ∀ u ∈ U, ρ p u ∈ U)
    (hRn : ∀ p ∈ P, ∀ r ∈ R, p * r * p⁻¹ ∈ R) (hF1 : Module.finrank K (fixSub ρ U R) = 1)
    {s : Γ} (hsP : s ∈ P) {k : ℕ} (hs : s ^ 2 ^ k = 1) {u : E} (hu : u ∈ U) :
    ρ s u - u ∈ fixSub ρ U R := by
  have : FiniteDimensional K U := Module.finite_of_finrank_pos (by omega)
  let W : Submodule K E := U ⊓ LinearMap.ker ((ρ s : E →ₗ[K] E) - 1)
  have hker : ∀ e, e ∈ W ↔ e ∈ U ∧ ρ s e = e := fun e => by
    simp [W, sub_eq_zero]
  have hFW : fixSub ρ U R ≤ W := fun f hf =>
    (hker f).mpr ⟨hf.1, apply_eq_of_mem_fixSub ρ hU hPU hRn hF1 hsP hs hf⟩
  have hNu : ρ s u - u ∈ W :=
    (hker _).mpr ⟨sub_mem (hPU s hsP u hu) hu, apply_sub_fixed ρ hU hPU hsP hs hu⟩
  by_cases hWU : W = U
  · have h1 : ρ s u = u := ((hker u).mp (hWU ▸ hu)).2
    rw [h1, sub_self]
    exact Submodule.zero_mem _
  · have h1 : Module.finrank K W < Module.finrank K U :=
      Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne inf_le_left hWU)
    rw [Submodule.eq_of_le_of_finrank_le hFW (by omega)]
    exact hNu

private theorem forall_mem_fixSub [CharP K 2] (ρ : Γ →* (E ≃ₗ[K] E)) {U : Submodule K E}
    (hU : Module.finrank K U = 2) {S : Set Γ} (hS : ∀ s ∈ S, ∃ k : ℕ, s ^ 2 ^ k = 1)
    {P R : Subgroup Γ} (hPS : Subgroup.closure S = P) (hPU : ∀ p ∈ P, ∀ u ∈ U, ρ p u ∈ U)
    (hRn : ∀ p ∈ P, ∀ r ∈ R, p * r * p⁻¹ ∈ R) (hF1 : Module.finrank K (fixSub ρ U R) = 1)
    {p : Γ} (hp : p ∈ P) :
    (∀ u ∈ U, ρ p u - u ∈ fixSub ρ U R) ∧ ∀ f ∈ fixSub ρ U R, ρ p f = f := by
  rw [← hPS] at hp
  induction hp using Subgroup.closure_induction with
  | mem s hs =>
    obtain ⟨k, hk⟩ := hS s hs
    have hsP : s ∈ P := hPS ▸ Subgroup.subset_closure hs
    exact ⟨fun u hu => sub_mem_fixSub ρ hU hPU hRn hF1 hsP hk hu,
      fun f hf => apply_eq_of_mem_fixSub ρ hU hPU hRn hF1 hsP hk hf⟩
  | one =>
    have h1 : ∀ e : E, ρ 1 e = e := fun e => by rw [map_one]; rfl
    exact ⟨fun u _ => by rw [h1, sub_self]; exact Submodule.zero_mem _, fun f _ => h1 f⟩
  | mul g h _ _ hg hh =>
    refine ⟨fun u hu => ?_, fun f hf => ?_⟩
    · have hhu : ρ h u ∈ U := by
        have h2 := U.add_mem (hh.1 u hu).1 hu
        rwa [sub_add_cancel] at h2
      have e : ρ (g * h) u - u = (ρ g (ρ h u) - ρ h u) + (ρ h u - u) := by
        rw [map_mul, LinearEquiv.mul_apply]
        abel
      rw [e]
      exact add_mem (hg.1 _ hhu) (hh.1 u hu)
    · rw [map_mul, LinearEquiv.mul_apply, hh.2 f hf, hg.2 f hf]
  | inv g _ hg =>
    refine ⟨fun u hu => ?_, fun f hf => ?_⟩
    · have hNu := hg.1 u hu
      have e1 : ρ g (u - (ρ g u - u)) = u := by
        rw [map_sub, hg.2 _ hNu]
        abel
      have e2 : ρ g⁻¹ u = u - (ρ g u - u) := by
        calc ρ g⁻¹ u = ρ g⁻¹ (ρ g (u - (ρ g u - u))) := by rw [e1]
          _ = u - (ρ g u - u) := inv_apply_apply ρ g _
      have e3 : ρ g⁻¹ u - u = -(ρ g u - u) := by
        rw [e2]
        abel
      rw [e3]
      exact neg_mem hNu
    · calc ρ g⁻¹ f = ρ g⁻¹ (ρ g f) := by rw [hg.2 f hf]
        _ = f := inv_apply_apply ρ g f

theorem fix_or_commutator_fix_of_finrank_eq_two [CharP K 2] (ρ : Γ →* (E ≃ₗ[K] E))
    {U : Submodule K E} (hU : Module.finrank K U = 2) {S : Set Γ}
    (hS : ∀ s ∈ S, ∃ k : ℕ, s ^ 2 ^ k = 1) {P R : Subgroup Γ} (hPS : Subgroup.closure S = P)
    (hPU : ∀ p ∈ P, ∀ u ∈ U, ρ p u ∈ U) (hRP : R ≤ P)
    (hRn : ∀ p ∈ P, ∀ r ∈ R, p * r * p⁻¹ ∈ R) (hR : IsPGroup 2 R) :
    (∀ r ∈ R, ∀ u ∈ U, ρ r u = u) ∨ ∀ c ∈ ⁅P, P⁆, ∀ u ∈ U, ρ c u = u := by
  by_cases hR1 : ∀ r ∈ R, ∀ u ∈ U, ρ r u = u
  · exact Or.inl hR1
  refine Or.inr ?_
  have hF1 := finrank_fixSub_eq_one ρ hU (fun r hr => hPU r (hRP hr)) hR hR1
  have hΦ := fun p (hp : p ∈ P) => forall_mem_fixSub ρ hU hS hPS hPU hRn hF1 hp
  have hcomm : ∀ g ∈ P, ∀ h ∈ P, ∀ u ∈ U, ρ g (ρ h u) = ρ h (ρ g u) := by
    intro g hg h hh u hu
    have e1 : ρ g (ρ h u) = ρ g u + (ρ h u - u) := by
      calc ρ g (ρ h u) = ρ g (u + (ρ h u - u)) := by rw [add_sub_cancel]
        _ = ρ g u + (ρ h u - u) := by rw [map_add, (hΦ g hg).2 _ ((hΦ h hh).1 u hu)]
    have e2 : ρ h (ρ g u) = ρ h u + (ρ g u - u) := by
      calc ρ h (ρ g u) = ρ h (u + (ρ g u - u)) := by rw [add_sub_cancel]
        _ = ρ h u + (ρ g u - u) := by rw [map_add, (hΦ h hh).2 _ ((hΦ g hg).1 u hu)]
    rw [e1, e2]
    abel
  have hle : ⁅P, P⁆ ≤ fixGrp ρ U := by
    rw [Subgroup.commutator_le]
    intro g hg h hh
    rw [commutatorElement_def]
    intro u hu
    have hv : ρ g⁻¹ (ρ h⁻¹ u) ∈ U := hPU _ (P.inv_mem hg) _ (hPU _ (P.inv_mem hh) u hu)
    show ρ (g * h * g⁻¹ * h⁻¹) u = u
    rw [map_mul, map_mul, map_mul]
    simp only [LinearEquiv.mul_apply]
    rw [hcomm g hg h hh _ hv, apply_inv_apply, apply_inv_apply]
  exact fun c hc u hu => hle hc u hu

end CFSG.LinearAlgebra
