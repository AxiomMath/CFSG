module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.LinearAlgebra.Center
public import Mathlib.Algebra.Field.ZMod

public noncomputable section

namespace CFSG.LinearAlgebra

open Module

theorem binary_rank_one_dihedral_action_is_the_natural_S3_module {H : Type*} [Group H]
    {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {z t : H} (hz : orderOf z = p) (ht : orderOf t = 2)
    (htz : t * z * t = z⁻¹) (hgen : Subgroup.closure ({z, t} : Set H) = ⊤) {I : Type*}
    [AddCommGroup I] [Module (ZMod 2) I] [Nontrivial I] (ρ : Representation (ZMod 2) H I)
    (hfaith : Function.Injective ρ)
    (hirr : ∀ U : Submodule (ZMod 2) I, (∀ h, ∀ u ∈ U, ρ h u ∈ U) → U = ⊥ ∨ U = ⊤)
    (hdim : finrank (ZMod 2) (I ⧸ LinearMap.ker (ρ t - 1)) = 1) :
    p = 3 ∧ finrank (ZMod 2) I = 2 ∧ Function.Surjective ρ.asGroupHom ∧
      ∀ f : Module.End (ZMod 2) I, (∀ h, f * ρ h = ρ h * f) → ∃ c : ZMod 2, f = c • 1 := by
  classical
  have ht2 : t * t = 1 := by rw [← pow_two, ← ht]; exact pow_orderOf_eq_one t
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hzp : z ^ p = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  have hρinv : ∀ h v, ρ h⁻¹ (ρ h v) = v := fun h v => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hρinv' : ∀ h v, ρ h (ρ h⁻¹ v) = v := fun h v => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hρinj : ∀ h, Function.Injective (ρ h) := fun h x y hxy => by
    rw [← hρinv h x, hxy, hρinv]
  set T : Module.End (ZMod 2) I := ρ t with hT
  set t' : H := z⁻¹ * t * z with ht'
  have hrange1 : finrank (ZMod 2) (LinearMap.range (T - 1)) = 1 := by
    rw [← hdim]
    exact (LinearMap.quotKerEquivRange (T - 1)).finrank_eq.symm
  have hconj : ρ t' - 1 = ρ z⁻¹ * (T - 1) * ρ z := by
    rw [hT, ht', map_mul, map_mul, mul_sub, sub_mul, mul_one, ← map_mul ρ z⁻¹ z, inv_mul_cancel,
      map_one]
  have hrange2 : finrank (ZMod 2) (LinearMap.range (ρ t' - 1)) = 1 := by
    have e : LinearMap.range (ρ t' - 1) = (LinearMap.range (T - 1)).map (ρ z⁻¹) := by
      rw [hconj]
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact ⟨(T - 1) (ρ z y), LinearMap.mem_range_self _ _, rfl⟩
      · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
        exact ⟨ρ z⁻¹ y, by rw [Module.End.mul_apply, Module.End.mul_apply, hρinv']⟩
    rw [e, ← (Submodule.equivMapOfInjective (ρ z⁻¹) (hρinj z⁻¹) _).finrank_eq, hrange1]
  set U := LinearMap.range (T - 1) ⊔ LinearMap.range (ρ t' - 1) with hU
  have hUt : ∀ u ∈ U, T u ∈ U := fun u hu => by
    have e : T u = u + (T - 1) u := by
      rw [LinearMap.sub_apply, Module.End.one_apply]
      abel
    rw [e]
    exact U.add_mem hu (Submodule.mem_sup_left (LinearMap.mem_range_self _ _))
  have hUt' : ∀ u ∈ U, ρ t' u ∈ U := fun u hu => by
    have e : ρ t' u = u + (ρ t' - 1) u := by
      rw [LinearMap.sub_apply, Module.End.one_apply]
      abel
    rw [e]
    exact U.add_mem hu (Submodule.mem_sup_right (LinearMap.mem_range_self _ _))
  have htt' : t * t' = z ^ 2 := by
    have h1 : t * z⁻¹ * t = z := by
      calc t * z⁻¹ * t = t⁻¹ * z⁻¹ * t⁻¹ := by rw [htinv]
        _ = (t * z * t)⁻¹ := by group
        _ = z := by rw [htz, inv_inv]
    calc t * t' = (t * z⁻¹ * t) * z := by rw [ht']; group
      _ = z ^ 2 := by rw [h1, pow_two]
  have hpow : ∀ (x : H), (∀ u ∈ U, ρ x u ∈ U) → ∀ n : ℕ, ∀ u ∈ U, ρ (x ^ n) u ∈ U := by
    intro x hx n
    induction n with
    | zero => intro u hu; rw [pow_zero, map_one, Module.End.one_apply]; exact hu
    | succ n ih => intro u hu; rw [pow_succ, map_mul, Module.End.mul_apply]; exact ih _ (hx u hu)
  have hUz2 : ∀ u ∈ U, ρ (z ^ 2) u ∈ U := fun u hu => by
    rw [← htt', map_mul, Module.End.mul_apply]
    exact hUt _ (hUt' u hu)
  obtain ⟨m, hm⟩ : ∃ m, p = 2 * m + 1 := (hp.out.eq_two_or_odd'.resolve_left hp2)
  have hUz : ∀ u ∈ U, ρ z u ∈ U := by
    have e : z = (z ^ 2) ^ (m + 1) := by
      rw [← pow_mul, show 2 * (m + 1) = p + 1 by omega, pow_succ, hzp, one_mul]
    rw [e]
    exact hpow _ hUz2 _
  have hUzinv : ∀ u ∈ U, ρ z⁻¹ u ∈ U := by
    have e : z⁻¹ = z ^ (2 * m) := by
      rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ, show 2 * m + 1 = p by omega, hzp]
    rw [e]
    exact hpow _ hUz _
  have hUinv : ∀ h, ∀ u ∈ U, ρ h u ∈ U := by
    intro h
    have hh : h ∈ (Subgroup.closure ({z, t} : Set H)).toSubmonoid := by
      rw [hgen]
      exact Subgroup.mem_top h
    rw [Subgroup.closure_toSubmonoid] at hh
    induction hh using Submonoid.closure_induction with
    | mem x hx =>
      simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_inv] at hx
      rcases hx with (rfl | rfl) | (hx | hx)
      · exact hUz
      · exact hUt
      · rw [← inv_inv x, hx]
        exact hUzinv
      · rw [← inv_inv x, hx, htinv]
        exact hUt
    | one => intro u hu; rw [map_one, Module.End.one_apply]; exact hu
    | mul x y _ _ hx hy => intro u hu; rw [map_mul, Module.End.mul_apply]; exact hx _ (hy u hu)
  have hU0 : U ≠ ⊥ := by
    intro h
    have hle : LinearMap.range (T - 1) ≤ U := le_sup_left
    rw [h, le_bot_iff] at hle
    rw [hle, finrank_bot] at hrange1
    exact zero_ne_one hrange1
  have hUtop : U = ⊤ := (hirr U hUinv).resolve_left hU0
  have : FiniteDimensional (ZMod 2) (LinearMap.range (T - 1)) :=
    Module.finite_of_finrank_pos (by omega)
  have : FiniteDimensional (ZMod 2) (LinearMap.range (ρ t' - 1)) :=
    Module.finite_of_finrank_pos (by omega)
  have : FiniteDimensional (ZMod 2) I := Module.Finite.equiv (LinearEquiv.ofTop U hUtop)
  have hle2 : finrank (ZMod 2) I ≤ 2 := by
    have h1 := Submodule.finrank_add_le_finrank_add_finrank (LinearMap.range (T - 1))
      (LinearMap.range (ρ t' - 1))
    rw [← hU, hUtop, finrank_top, hrange1, hrange2] at h1
    exact h1
  have hTT : ∀ y, (T - 1) ((T - 1) y) = 0 := fun y => by
    have hTy : T (T y) = y := by
      rw [hT, ← Module.End.mul_apply, ← map_mul, ht2, map_one, Module.End.one_apply]
    rw [LinearMap.sub_apply, LinearMap.sub_apply, map_sub, Module.End.one_apply,
      Module.End.one_apply, hTy]
    have e : y - T y - (T y - y) = (2 : ZMod 2) • (y - T y) := by module
    rw [e, show (2 : ZMod 2) = 0 from rfl, zero_smul]
  have hI2 : finrank (ZMod 2) I = 2 := by
    have hpos : 0 < finrank (ZMod 2) I := Module.finrank_pos
    rcases (by omega : finrank (ZMod 2) I = 1 ∨ finrank (ZMod 2) I = 2) with h1 | h2
    · exfalso
      have htop : LinearMap.range (T - 1) = ⊤ :=
        Submodule.eq_top_of_finrank_eq (by rw [hrange1, h1])
      have hzero : T - 1 = 0 := LinearMap.ext fun x => by
        obtain ⟨y, rfl⟩ : x ∈ LinearMap.range (T - 1) := htop ▸ Submodule.mem_top
        exact hTT y
      rw [hzero, LinearMap.range_zero, finrank_bot] at hrange1
      exact zero_ne_one hrange1
    · exact h2
  have hGL : Nat.card (LinearMap.GeneralLinearGroup (ZMod 2) I) = 6 := by
    let b := Module.finBasisOfFinrankEq (ZMod 2) I hI2
    rw [← Nat.card_congr (Matrix.GeneralLinearGroup.toLin' b).toEquiv, Matrix.card_GL_field,
      Fin.prod_univ_two, ZMod.card]
    norm_num
  have : Finite (LinearMap.GeneralLinearGroup (ZMod 2) I) :=
    Nat.finite_of_card_ne_zero (by rw [hGL]; norm_num)
  have hinj : Function.Injective ρ.asGroupHom := fun x y hxy => hfaith (by
    have := congrArg Units.val hxy
    rwa [Representation.asGroupHom_apply, Representation.asGroupHom_apply] at this)
  have hordz : orderOf (ρ.asGroupHom z) = p := by rw [orderOf_injective _ hinj, hz]
  have hordt : orderOf (ρ.asGroupHom t) = 2 := by rw [orderOf_injective _ hinj, ht]
  have hp3 : p = 3 := by
    have h1 := orderOf_dvd_natCard (ρ.asGroupHom z)
    rw [hordz, hGL, show (6 : ℕ) = 2 * 3 by norm_num] at h1
    rcases (Nat.Prime.dvd_mul hp.out).1 h1 with h | h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 h) hp2
    · exact (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_three).1 h
  have hsurj : Function.Surjective ρ.asGroupHom := by
    rw [← MonoidHom.range_eq_top]
    set R := ρ.asGroupHom.range
    have h3 : 3 ∣ Nat.card R := by
      have := orderOf_dvd_natCard (⟨ρ.asGroupHom z, MonoidHom.mem_range.2 ⟨z, rfl⟩⟩ : R)
      rwa [← orderOf_submonoid, hordz, hp3] at this
    have h2 : 2 ∣ Nat.card R := by
      have := orderOf_dvd_natCard (⟨ρ.asGroupHom t, MonoidHom.mem_range.2 ⟨t, rfl⟩⟩ : R)
      rwa [← orderOf_submonoid, hordt] at this
    have h6 : 6 ∣ Nat.card R := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h3
    have hle : Nat.card R ∣ 6 := hGL ▸ Subgroup.card_subgroup_dvd_card R
    exact (Subgroup.card_eq_iff_eq_top R).1 (by rw [hGL]; exact Nat.dvd_antisymm hle h6)
  refine ⟨hp3, hI2, hsurj, fun f hf => ?_⟩
  refine LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent fun v hli => ?_
  let b' := basisOfLinearIndependentOfCardEqFinrank hli (by rw [Fintype.card_fin, hI2])
  have hb'0 : b' 0 = v := by
    simp [b', coe_basisOfLinearIndependentOfCardEqFinrank]
  have hb'1 : b' 1 = f v := by
    simp [b', coe_basisOfLinearIndependentOfCardEqFinrank]
  set c := b'.coord 1 with hc
  have hcv : c v = 0 := by rw [← hb'0, hc, Basis.coord_apply, Basis.repr_self]; simp
  have hcfv : c (f v) = 1 := by rw [← hb'1, hc, Basis.coord_apply, Basis.repr_self]; simp
  set g : Module.End (ZMod 2) I := 1 + c.smulRight v with hgdef
  have hg : ∀ x, g x = x + c x • v := fun x => rfl
  have hgg : g * g = 1 := LinearMap.ext fun x => by
    rw [Module.End.mul_apply, hg, hg, map_add, map_smul, hcv, smul_eq_mul, mul_zero, add_zero,
      add_assoc, ← add_smul, CharTwo.add_self_eq_zero, zero_smul, add_zero, Module.End.one_apply]
  obtain ⟨h, hh⟩ := hsurj ⟨g, g, hgg, hgg⟩
  have hρh : ρ h = g := by
    have := congrArg Units.val hh
    rwa [Representation.asGroupHom_apply] at this
  have h1 := LinearMap.congr_fun (hf h) v
  rw [Module.End.mul_apply, Module.End.mul_apply, hρh, hg, hg, hcv, zero_smul, add_zero, hcfv,
    one_smul, left_eq_add] at h1
  exact hli.ne_zero 0 (by simpa using h1)

end CFSG.LinearAlgebra
