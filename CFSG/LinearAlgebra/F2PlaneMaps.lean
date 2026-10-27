module

public import CFSG.RankThree.OrthogonalInvolutions.Basic
public import CFSG.LinearAlgebra.RestrictEquiv
import CFSG.LargeExtraspecial.S12LinAlg

public section

namespace CFSG.LinearAlgebra

open Module CFSG.RankThree.OrthogonalInvolutions

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {W : Submodule (ZMod 2) V}

section Plane

variable [FiniteDimensional (ZMod 2) W]

theorem restrictEquiv_pow_six_of_finrank_eq_two {g : V ≃ₗ[ZMod 2] V}
    (hgW : ∀ w ∈ W, g w ∈ W) (hW : finrank (ZMod 2) W = 2) :
    restrictEquiv hgW ^ 6 = 1 := by
  ext w
  exact congrArg Subtype.val (CFSG.LargeExtraspecial.s12_pow_six_apply (V := W) (W := ⊤)
    (by simpa using hW) (x := restrictEquiv hgW) (fun _ _ => Submodule.mem_top)
    (fun _ _ => Submodule.mem_top) w Submodule.mem_top)

theorem exists_restrictEquiv_ne_of_exists_ne {g : V ≃ₗ[ZMod 2] V}
    (hgW : ∀ w ∈ W, g w ∈ W) (h : ∃ w ∈ W, g w ≠ w) :
    ∃ w : W, restrictEquiv hgW w ≠ w := by
  obtain ⟨w, hw, hgw⟩ := h
  refine ⟨⟨w, hw⟩, fun hcon => hgw ?_⟩
  have := congrArg Subtype.val hcon
  simpa [restrictEquiv_apply] using this

end Plane

theorem apply_eq_self_of_odd_of_apply_eq (hW : finrank (ZMod 2) W = 2) {g : V ≃ₗ[ZMod 2] V}
    (hgW : ∀ w ∈ W, g w ∈ W) (hodd : Odd (orderOf g)) {w₀ : V} (hw₀ : w₀ ∈ W) (hw₀0 : w₀ ≠ 0)
    (hfix : g w₀ = w₀) : ∀ w ∈ W, g w = w := by
  haveI : FiniteDimensional (ZMod 2) W :=
    FiniteDimensional.of_finrank_pos (by rw [hW]; norm_num)
  let e := restrictEquiv hgW
  have hfixe : e ⟨w₀, hw₀⟩ = ⟨w₀, hw₀⟩ := Subtype.ext (by simpa [e] using hfix)
  have hdvd : orderOf e ∣ orderOf g :=
    orderOf_dvd_of_pow_eq_one (restrictEquiv_pow_eq_one hgW (pow_orderOf_eq_one g))
  have hodd_e : Odd (orderOf e) := hodd.of_dvd_nat hdvd
  have h6 : e ^ 6 = 1 := restrictEquiv_pow_six_of_finrank_eq_two hgW hW
  have hdvd6 : orderOf e ∣ 6 := orderOf_dvd_of_pow_eq_one h6
  have he1 : e = 1 := by
    have hdvd3 : orderOf e ∣ 3 :=
      hodd_e.coprime_two_right.dvd_of_dvd_mul_left (by simpa using hdvd6)
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd3 with h1 | h3ord
    · exact orderOf_eq_one_iff.mp h1
    · exfalso
      have h3 : e ^ 3 = 1 := by rw [← h3ord]; exact pow_orderOf_eq_one e
      have hmoved : ∃ w : W, e w ≠ w := by
        by_contra hc
        have heq : e = 1 := LinearEquiv.ext (fun w => by
          by_contra hw
          exact hc ⟨w, by simpa using hw⟩)
        rw [heq, orderOf_one] at h3ord
        norm_num at h3ord
      have hmoved_top : ∃ w ∈ (⊤ : Submodule (ZMod 2) W), e w ≠ w := by
        obtain ⟨w, hw⟩ := hmoved
        exact ⟨w, Submodule.mem_top, hw⟩
      exact (CFSG.LargeExtraspecial.s12_no_fix_of_pow_three (V := W) (W := ⊤)
        (by simpa using hW) (c := e) h3 (fun _ _ => Submodule.mem_top) hmoved_top
        (p := ⟨w₀, hw₀⟩) Submodule.mem_top (by simpa using hw₀0)) hfixe
  intro w hw
  have := congrArg Subtype.val (LinearEquiv.congr_fun he1 ⟨w, hw⟩)
  simpa [e, restrictEquiv_apply] using this

theorem apply_apply_eq_of_pow_two_pow (hW : finrank (ZMod 2) W = 2) {g : V ≃ₗ[ZMod 2] V}
    (hgW : ∀ w ∈ W, g w ∈ W) {k : ℕ} (hk : g ^ 2 ^ k = 1) : ∀ w ∈ W, g (g w) = w := by
  haveI : FiniteDimensional (ZMod 2) W :=
    FiniteDimensional.of_finrank_pos (by rw [hW]; norm_num)
  let e := restrictEquiv hgW
  have hk_e : e ^ 2 ^ k = 1 := restrictEquiv_pow_eq_one hgW hk
  have h6 : e ^ 6 = 1 := restrictEquiv_pow_six_of_finrank_eq_two hgW hW
  have hdvd2k : orderOf e ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk_e
  have hdvd6 : orderOf e ∣ 6 := orderOf_dvd_of_pow_eq_one h6
  have hnot3 : ¬ 3 ∣ orderOf e := by
    intro h3
    have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three (h3.trans hdvd2k)
    norm_num at h32
  have hcop : Nat.Coprime (orderOf e) 3 :=
    ((Nat.prime_three.coprime_iff_not_dvd).mpr hnot3).symm
  have hdvd2 : orderOf e ∣ 2 :=
    hcop.dvd_of_dvd_mul_right (by simpa using hdvd6)
  have he2 : e ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp hdvd2
  intro w hw
  have h := congrArg Subtype.val (LinearEquiv.congr_fun he2 ⟨w, hw⟩)
  simpa [e, pow_two, LinearEquiv.mul_apply, restrictEquiv_apply] using h

theorem inf_fixSpace_eq_bot_of_pow_three (hW : finrank (ZMod 2) W = 2)
    {x : V ≃ₗ[ZMod 2] V} (hxW : ∀ w ∈ W, x w ∈ W) (hx3 : x ^ 3 = 1)
    (hx : ∃ w ∈ W, x w ≠ w) : W ⊓ fixSpace x = ⊥ := by
  haveI : FiniteDimensional (ZMod 2) W :=
    FiniteDimensional.of_finrank_pos (by rw [hW]; norm_num)
  let e := restrictEquiv hxW
  have he3 : e ^ 3 = 1 := restrictEquiv_pow_eq_one hxW hx3
  have hmoved : ∃ w : W, e w ≠ w := exists_restrictEquiv_ne_of_exists_ne hxW hx
  have hmoved_top : ∃ w ∈ (⊤ : Submodule (ZMod 2) W), e w ≠ w := by
    obtain ⟨w, hw⟩ := hmoved
    exact ⟨w, Submodule.mem_top, hw⟩
  rw [eq_bot_iff]
  intro v hv
  obtain ⟨hvW, hvf⟩ := Submodule.mem_inf.mp hv
  rw [Submodule.mem_bot]
  by_contra hv0
  have hfixe : e ⟨v, hvW⟩ = ⟨v, hvW⟩ :=
    Subtype.ext (by simpa [e, restrictEquiv_apply] using (mem_fixSpace.mp hvf))
  exact (CFSG.LargeExtraspecial.s12_no_fix_of_pow_three (V := W) (W := ⊤)
    (by simpa using hW) (c := e) he3 (fun _ _ => Submodule.mem_top) hmoved_top
    (p := ⟨v, hvW⟩) Submodule.mem_top (by simpa using hv0)) hfixe

theorem forall_apply_eq_or_forall_apply_eq_sq (hW : finrank (ZMod 2) W = 2)
    {x y : V ≃ₗ[ZMod 2] V} (hxW : ∀ w ∈ W, x w ∈ W) (hyW : ∀ w ∈ W, y w ∈ W)
    (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1) (hx : ∃ w ∈ W, x w ≠ w) (hy : ∃ w ∈ W, y w ≠ w) :
    (∀ w ∈ W, y w = x w) ∨ ∀ w ∈ W, y w = x (x w) := by
  haveI : FiniteDimensional (ZMod 2) W :=
    FiniteDimensional.of_finrank_pos (by rw [hW]; norm_num)
  let e := restrictEquiv hxW
  let e' := restrictEquiv hyW
  have he3 : e ^ 3 = 1 := restrictEquiv_pow_eq_one hxW hx3
  have he'3 : e' ^ 3 = 1 := restrictEquiv_pow_eq_one hyW hy3
  have hmoved_top : ∃ w ∈ (⊤ : Submodule (ZMod 2) W), e w ≠ w := by
    obtain ⟨w, hw⟩ := exists_restrictEquiv_ne_of_exists_ne hxW hx
    exact ⟨w, Submodule.mem_top, hw⟩
  have hmoved_top' : ∃ w ∈ (⊤ : Submodule (ZMod 2) W), e' w ≠ w := by
    obtain ⟨w, hw⟩ := exists_restrictEquiv_ne_of_exists_ne hyW hy
    exact ⟨w, Submodule.mem_top, hw⟩
  rcases CFSG.LargeExtraspecial.s12_eq_or_eq_sq_of_pow_three (V := W) (W := ⊤)
    (by simpa using hW) (c := e) (c' := e') he3 he'3 (fun _ _ => Submodule.mem_top)
    (fun _ _ => Submodule.mem_top) hmoved_top hmoved_top' with h | h
  · left
    intro w hw
    have := congrArg Subtype.val (h ⟨w, hw⟩ Submodule.mem_top)
    simpa [e, e', restrictEquiv_apply] using this
  · right
    intro w hw
    have := congrArg Subtype.val (h ⟨w, hw⟩ Submodule.mem_top)
    simpa [e, e', restrictEquiv_apply, pow_two, LinearEquiv.mul_apply] using this

theorem apply_eq_self_of_isPerfect (hW : finrank (ZMod 2) W = 2) {Γ : Type*} [Group Γ]
    [Group.IsPerfect Γ] (ρ : Γ →* (V ≃ₗ[ZMod 2] V))
    (hst : ∀ g : Γ, ∀ w ∈ W, ρ g w ∈ W) : ∀ g : Γ, ∀ w ∈ W, ρ g w = w := by
  haveI : FiniteDimensional (ZMod 2) W :=
    FiniteDimensional.of_finrank_pos (by rw [hW]; norm_num)
  haveI : Finite W := Module.finite_of_finite (ZMod 2)
  have hcard : Nat.card W = 4 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W)
    rw [hW, Nat.card_zmod] at h
    norm_num at h
    exact h
  haveI : Group.IsSolvable (Equiv.Perm W) := Equiv.Perm.isSolvable hcard.le
  let res : Γ →* (W ≃ₗ[ZMod 2] W) :=
    { toFun := fun g => restrictEquiv (hst g)
      map_one' := by
        ext w
        simp [restrictEquiv_apply]
      map_mul' := by
        intro g h
        ext w
        simp [restrictEquiv_apply, map_mul, LinearEquiv.mul_apply] }
  let φ : Γ →* Equiv.Perm W := (MulAction.toPermHom (W ≃ₗ[ZMod 2] W) W).comp res
  haveI : Group.IsPerfect φ.range := Group.IsPerfect.range φ
  have hsub : Subsingleton φ.range := by
    by_contra h
    haveI : Nontrivial φ.range := not_subsingleton_iff_nontrivial.mp h
    exact Group.IsPerfect.not_isSolvable φ.range inferInstance
  intro g w hw
  have hφ : (⟨φ g, MonoidHom.mem_range.mpr ⟨g, rfl⟩⟩ : φ.range) = 1 :=
    Subsingleton.elim _ _
  have h1 : φ g = 1 := congrArg Subtype.val hφ
  have h := congrArg (fun σ : Equiv.Perm W => ((σ ⟨w, hw⟩ : W) : V)) h1
  simpa [φ, res, restrictEquiv_apply] using h

theorem apply_eq_self_of_coprime_six (hW : finrank (ZMod 2) W = 2) {g : V ≃ₗ[ZMod 2] V}
    (hgW : ∀ w ∈ W, g w ∈ W) (hcop : Nat.Coprime (orderOf g) 6) : ∀ w ∈ W, g w = w := by
  haveI : FiniteDimensional (ZMod 2) W :=
    FiniteDimensional.of_finrank_pos (by rw [hW]; norm_num)
  let e := restrictEquiv hgW
  have hdvd : orderOf e ∣ orderOf g :=
    orderOf_dvd_of_pow_eq_one (restrictEquiv_pow_eq_one hgW (pow_orderOf_eq_one g))
  have hcop_e : Nat.Coprime (orderOf e) 6 := Nat.Coprime.coprime_dvd_left hdvd hcop
  have h6 : orderOf e ∣ 6 :=
    orderOf_dvd_of_pow_eq_one (restrictEquiv_pow_six_of_finrank_eq_two hgW hW)
  have he1 : e = 1 := orderOf_eq_one_iff.mp (hcop_e.eq_one_of_dvd h6)
  intro w hw
  have := congrArg Subtype.val (LinearEquiv.congr_fun he1 ⟨w, hw⟩)
  simpa [e, restrictEquiv_apply] using this

end CFSG.LinearAlgebra
