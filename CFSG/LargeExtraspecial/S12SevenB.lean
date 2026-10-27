module

public import CFSG.RankThree.OrthogonalInvolutions.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

omit [FiniteDimensional (ZMod 2) V] in
theorem s12_apply_mem_commSpace_self (x : V ≃ₗ[ZMod 2] V) {v : V} (hv : v ∈ commSpace x) :
    x v ∈ commSpace x := by
  obtain ⟨w, rfl⟩ := mem_commSpace.mp hv
  exact mem_commSpace.mpr ⟨x w, by rw [map_sub]⟩

omit [FiniteDimensional (ZMod 2) V] in
theorem s12_mem_fixSpace_pow {y : V ≃ₗ[ZMod 2] V} {v : V} (hv : y v = v) (a : ℕ) :
    (y ^ a) v = v := by
  induction a with
  | zero => rfl
  | succ a ih => rw [pow_succ, LinearEquiv.mul_apply, hv, ih]

omit [FiniteDimensional (ZMod 2) V] in
theorem s12_fixSpace_mul_eq_bot {i j : V ≃ₗ[ZMod 2] V} (hi3 : i ^ 3 = 1) (hj3 : j ^ 3 = 1)
    (hsup : commSpace i ⊔ commSpace j = ⊤)
    (hinf : commSpace i ⊓ commSpace j = ⊥) (hfi : fixSpace i = commSpace j)
    (hfj : fixSpace j = commSpace i) {a b : ℕ} (ha : a = 1 ∨ a = 2) (hb : b = 1 ∨ b = 2) :
    fixSpace (i ^ a * j ^ b) = ⊥ := by
  have hfix_pow : ∀ {y : V ≃ₗ[ZMod 2] V}, y ^ 3 = 1 → ∀ {c : ℕ}, (c = 1 ∨ c = 2) →
      ∀ v, (y ^ c) v = v → y v = v := by
    intro y hy3 c hc v hv
    rcases hc with rfl | rfl
    · simpa using hv
    · have e3 : (y ^ 3) v = v := by rw [hy3]; rfl
      rw [pow_succ', LinearEquiv.mul_apply, hv] at e3
      exact e3
  rw [eq_bot_iff]
  intro v hv
  rw [mem_fixSpace] at hv
  obtain ⟨vA, hvA, vB, hvB, rfl⟩ := Submodule.mem_sup.mp (hsup ▸ Submodule.mem_top (x := v))
  have hjA : ∀ c : ℕ, (j ^ c) vA = vA := fun c =>
    s12_mem_fixSpace_pow (mem_fixSpace.mp (hfj ▸ hvA)) c
  have hiB : ∀ c : ℕ, (i ^ c) vB = vB := fun c =>
    s12_mem_fixSpace_pow (mem_fixSpace.mp (hfi ▸ hvB)) c
  have hpowmem : ∀ {y : V ≃ₗ[ZMod 2] V} {w : V}, w ∈ commSpace y → ∀ c : ℕ,
      (y ^ c) w ∈ commSpace y := by
    intro y w hw c
    induction c with
    | zero => simpa using hw
    | succ c ih => rw [pow_succ', LinearEquiv.mul_apply]; exact s12_apply_mem_commSpace_self y ih
  have hcomm : ∀ c d : ℕ, (i ^ c * j ^ d) vB = (j ^ d) vB := by
    intro c d
    rw [LinearEquiv.mul_apply]
    exact s12_mem_fixSpace_pow (mem_fixSpace.mp (hfi ▸ hpowmem hvB d)) c
  rw [map_add, LinearEquiv.mul_apply, hjA, hcomm] at hv
  have hiA := hpowmem hvA a
  have hjB := hpowmem hvB b
  have hd : (i ^ a) vA - vA = -((j ^ b) vB - vB) := by
    rw [neg_sub]
    exact sub_eq_sub_iff_add_eq_add.mpr (by rw [hv, add_comm])
  have hmemA : (i ^ a) vA - vA ∈ commSpace i ⊓ commSpace j := by
    refine ⟨Submodule.sub_mem _ hiA hvA, ?_⟩
    rw [hd]
    exact Submodule.neg_mem _ (Submodule.sub_mem _ hjB hvB)
  rw [hinf, Submodule.mem_bot, sub_eq_zero] at hmemA
  have hmemB : (j ^ b) vB - vB = 0 := by
    have : -((j ^ b) vB - vB) = 0 := by rw [← hd, hmemA, sub_self]
    exact neg_eq_zero.mp this
  rw [sub_eq_zero] at hmemB
  have hvA0 : vA = 0 := by
    have h1 : i vA = vA := hfix_pow hi3 ha vA hmemA
    have h2 : vA ∈ commSpace i ⊓ commSpace j := ⟨hvA, hfi ▸ mem_fixSpace.mpr h1⟩
    rwa [hinf, Submodule.mem_bot] at h2
  have hvB0 : vB = 0 := by
    have h1 : j vB = vB := hfix_pow hj3 hb vB hmemB
    have h2 : vB ∈ commSpace i ⊓ commSpace j := ⟨hfj ▸ mem_fixSpace.mpr h1, hvB⟩
    rwa [hinf, Submodule.mem_bot] at h2
  rw [hvA0, hvB0, add_zero]
  exact Submodule.zero_mem _

theorem s12_fixSpace_le_commSpace {x y : V ≃ₗ[ZMod 2] V} (hxy : x * y = y * x)
    (hxy0 : fixSpace x ⊓ fixSpace y = ⊥) : fixSpace x ≤ commSpace y := by
  have hinv : ∀ v ∈ fixSpace x, ((y : V →ₗ[ZMod 2] V) - 1) v ∈ fixSpace x := by
    intro v hv
    rw [mem_fixSpace] at hv ⊢
    simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, Module.End.one_apply, map_sub]
    rw [hv, ← LinearEquiv.mul_apply, hxy, LinearEquiv.mul_apply, hv]
  set ψ := ((y : V →ₗ[ZMod 2] V) - 1).restrict hinv
  have hψinj : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro v hv
    rw [LinearMap.mem_ker] at hv
    have h1 : y v = v := by
      have := congrArg Subtype.val hv
      simp only [ψ, LinearMap.coe_restrict_apply, LinearMap.sub_apply, LinearEquiv.coe_coe,
        Module.End.one_apply, ZeroMemClass.coe_zero] at this
      exact sub_eq_zero.mp this
    have h2 : (v : V) ∈ fixSpace x ⊓ fixSpace y := ⟨v.2, mem_fixSpace.mpr h1⟩
    rw [hxy0, Submodule.mem_bot] at h2
    exact (Submodule.mem_bot _).mpr (Subtype.ext h2)
  have hψsurj : Function.Surjective ψ := LinearMap.injective_iff_surjective.mp hψinj
  intro v hv
  obtain ⟨w, hw⟩ := hψsurj ⟨v, hv⟩
  refine mem_commSpace.mpr ⟨w, ?_⟩
  have := congrArg Subtype.val hw
  simpa [ψ] using this

theorem s12_fixSpace_sup_commSpace {x : V ≃ₗ[ZMod 2] V} (hx3 : x ^ 3 = 1) :
    fixSpace x ⊔ commSpace x = ⊤ := by
  have hinf : fixSpace x ⊓ commSpace x = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨hv, hvc⟩
    obtain ⟨w, rfl⟩ := mem_commSpace.mp hvc
    replace hv : x (x w - w) = x w - w := mem_fixSpace.mp hv
    have h1 : x w = w + (x w - w) := by abel
    have h2 : x (x w) = w := by
      conv_lhs => rw [h1]
      rw [map_add, hv]
      have : x w - w + (x w - w) = 0 := by
        rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]
      calc x w + (x w - w) = w + (x w - w + (x w - w)) := by abel
        _ = w := by rw [this, add_zero]
    have h3 : (x ^ 3) w = x w := by
      rw [pow_succ, LinearEquiv.mul_apply, pow_two, LinearEquiv.mul_apply, h2]
    rw [hx3] at h3
    have h4 : x w - w = 0 := by
      rw [show (1 : V ≃ₗ[ZMod 2] V) w = w from rfl] at h3
      rw [← h3, sub_self]
    rw [h4]
    exact Submodule.zero_mem _
  have h := Submodule.finrank_sup_add_finrank_inf_eq (fixSpace x) (commSpace x)
  rw [hinf, finrank_bot, add_zero, add_comm, finrank_commSpace_add_finrank_fixSpace] at h
  exact Submodule.eq_top_of_finrank_eq h

theorem s12_decomp_of_commute {i j : V ≃ₗ[ZMod 2] V} (hij : i * j = j * i)
    (hfix : fixSpace i ⊓ fixSpace j = ⊥) (hsup : commSpace i ⊔ commSpace j = ⊤)
    (hdim : finrank (ZMod 2) (commSpace i) + finrank (ZMod 2) (commSpace j) =
      finrank (ZMod 2) V) :
    commSpace i ⊓ commSpace j = ⊥ ∧ fixSpace i = commSpace j ∧ fixSpace j = commSpace i := by
  have hinf : commSpace i ⊓ commSpace j = ⊥ := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (commSpace i) (commSpace j)
    rw [hsup, finrank_top, ← hdim] at h
    exact Submodule.finrank_eq_zero.mp (by omega)
  have hfi : fixSpace i ≤ commSpace j := s12_fixSpace_le_commSpace hij hfix
  have hfj : fixSpace j ≤ commSpace i :=
    s12_fixSpace_le_commSpace hij.symm (by rw [inf_comm]; exact hfix)
  have hdi := finrank_commSpace_add_finrank_fixSpace i
  have hdj := finrank_commSpace_add_finrank_fixSpace j
  refine ⟨hinf, Submodule.eq_of_le_of_finrank_eq hfi (by omega),
    Submodule.eq_of_le_of_finrank_eq hfj (by omega)⟩

theorem s12_commSpace_sup_eq_top {i j : V ≃ₗ[ZMod 2] V} (hij : i * j = j * i)
    (hi3 : i ^ 3 = 1) (hfix : fixSpace i ⊓ fixSpace j = ⊥) :
    commSpace i ⊔ commSpace j = ⊤ := by
  have h1 := s12_fixSpace_sup_commSpace hi3
  have h2 := s12_fixSpace_le_commSpace hij hfix
  rw [eq_top_iff, ← h1]
  exact sup_le (h2.trans le_sup_right) le_sup_left

end CFSG.LargeExtraspecial
