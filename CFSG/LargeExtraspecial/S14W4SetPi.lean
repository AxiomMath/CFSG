module

public import CFSG.LargeExtraspecial.S14W4SetS0

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup CFSG.Open CFSG.LargeExtraspecial.S4

variable {G : Type} [Group G] [Finite G]

namespace W4Hyp

variable {S : Setting G} {g : G} {t : S.O} {c : Config} (h : W4Hyp S g t c)
include h

theorem apply_mem_Vt_of_mem_Ct {y : S.O} (hy : y ∈ Ct S t) {v : S.Qt} (hv : v ∈ Vt S g t) :
    (y : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ Vt S g t := by
  have hk : ∃ k : S.M, S.ρ k = y := MonoidHom.mem_range.mp hy.1
  cases hk with
  | intro k hk =>
    subst hk
    exact apply_mem_Vt h.haQ (mem_centralizer_singleton_iff.mp hy.2) hv

omit h in
@[expose] noncomputable def π (h : W4Hyp S g t c) :
    ↥(h.S₀.M) →* (Vt S g t ≃ₗ[ZMod 2] Vt S g t) :=
  restrictHom (S.O.subtype.comp (h.ιK : ↥(h.S₀.M) →* S.O)) (Vt S g t)
    fun x _ hv => h.apply_mem_Vt_of_mem_Ct (h.ιK_mem_Ct x) hv

theorem π_eq_one_iff (x : ↥(h.S₀.M)) :
    h.π x = 1 ↔ ∀ v ∈ Vt S g t, ((ι S x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v :=
  restrictHom_eq_one_iff _ _ _ x

theorem π_eq_one_of_mem_Q {x : ↥(h.S₀.M)} (hx : x ∈ h.S₀.Q) : h.π x = 1 :=
  (h.π_eq_one_iff x).mpr fun v hv => (show ι S x ∈ Nbar S g t from hx).2 v hv

theorem Q_le_ker_π : h.S₀.Q ≤ h.π.ker := fun _ hx => h.π_eq_one_of_mem_Q hx

omit h in
@[expose] noncomputable def R₀ (_h : W4Hyp S g t c) : Subgroup ↥(Mbar0 S) :=
  (Rbar S g t).comap (ι S)

theorem R₀_le_M : h.R₀ ≤ h.S₀.M := fun _ hx =>
  h.mem_S₀_M.mpr (commute_of_mem_Rbar h.haQ hx)

theorem exists_R₀ {y : S.O} (hy : y ∈ Rbar S g t) : ∃ r : ↥(Mbar0 S), r ∈ h.R₀ ∧ ι S r = y := by
  have hx : ∃ x : ↥(Mbar0 S), ι S x = y := exists_ι_eq (h.le hy)
  cases hx with
  | intro x hx =>
    subst hx
    exact ⟨x, hy, rfl⟩

theorem conj_mem_R₀ {k : ↥(Mbar0 S)} (hk : k ∈ h.S₀.M) {r : ↥(Mbar0 S)} (hr : r ∈ h.R₀) :
    k * r * k⁻¹ ∈ h.R₀ := by
  have hkt : ι S k * t = t * ι S k := h.mem_S₀_M.mp hk
  have hk' : ∃ m : S.M, S.ρ m = ι S k := MonoidHom.mem_range.mp (ι_mem_Mbar S k)
  have e : ι S (k * r * k⁻¹) = ι S k * ι S r * (ι S k)⁻¹ := by simp only [map_mul, map_inv]
  show ι S (k * r * k⁻¹) ∈ Rbar S g t
  rw [e]
  cases hk' with
  | intro m hm =>
    rw [← hm] at hkt ⊢
    exact conj_mem_Rbar hkt hr

theorem π_R₀ : (h.R₀.subgroupOf h.S₀.M).map h.π = RmodN S g t := by
  ext e
  constructor
  · intro he
    have he' : ∃ r : ↥(h.S₀.M), r ∈ h.R₀.subgroupOf h.S₀.M ∧ h.π r = e := Subgroup.mem_map.mp he
    cases he' with
    | intro r hr =>
      cases hr with
      | intro hrR hre =>
        subst hre
        exact ⟨ι S r, hrR, fun v => rfl⟩
  · intro he
    have he' : ∃ x ∈ Rbar S g t, ∀ v : Vt S g t, ((e v : Vt S g t) : S.Qt) =
        (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v := he
    cases he' with
    | intro x hx =>
      have hr := h.exists_R₀ hx.1
      cases hr with
      | intro r hr' =>
        refine Subgroup.mem_map.mpr ⟨⟨r, h.R₀_le_M hr'.1⟩, hr'.1, ?_⟩
        refine LinearEquiv.ext fun v => Subtype.ext ?_
        calc ((h.π ⟨r, h.R₀_le_M hr'.1⟩ v : Vt S g t) : S.Qt)
            = ((ι S r : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v := rfl
          _ = (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v :=
            congrArg (fun y : S.O => (y : S.Qt ≃ₗ[ZMod 2] S.Qt) (v : S.Qt)) hr'.2
          _ = ((e v : Vt S g t) : S.Qt) := (hx.2 v).symm

end W4Hyp

end CFSG.LargeExtraspecial.S14
