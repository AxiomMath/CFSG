module

public import CFSG.GF2Type.Smith1979.WidthFourKP.TriPlus.AtT
public import CFSG.GF2Type.Smith1979.WidthFourKP.TriPlus.Iso
public import CFSG.GF2Type.Smith1979.W4AsSel

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.TriPlus

open Subgroup Module CFSG.Open CFSG.GroupTheory CFSG.LargeExtraspecial
  CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S5 CFSG.LargeExtraspecial.S7

variable {G : Type} [Group G] [Finite G]

namespace TriData

variable {S : Setting G} {g : G}

theorem Rbar_ne_Lbar (T : TriData S g) (H : Hyp4 S g) (i : Fin 3) :
    Rbar S g (T.l i) ≠ S.Lbar g := by
  classical
  obtain ⟨j, hji⟩ : ∃ j : Fin 3, j ≠ i := by
    fin_cases i <;> decide
  have hcomm' : eb T.σ j * T.l i * (eb T.σ j)⁻¹ = T.l i := by
    have h : T.l i * eb T.σ j = eb T.σ j * T.l i := by
      have hc := congrArg (fun z => z * T.l i) (T.l_conj_e_of_ne (i := i) (j := j) (Ne.symm hji))
      simpa [mul_assoc] using hc
    rw [← h]
    group
  intro hR
  obtain ⟨h, hh⟩ : ∃ h : S.M, S.ρ h = eb T.σ j :=
    MonoidHom.mem_range.mp (S7.Obar_le_Mbar (T.basis.eb_mem j))
  have hmem : T.l i ∈ S.Lbar ((h : G) * g) := by
    have hconj := S4.conj_mem_Lbar_mul S h (T.l_mem i)
    rwa [hh, hcomm'] at hconj
  have hle : S.Lbar ((h : G) * g) ≤ S.Lbar g := by
    simpa [hR] using S4.Lbar_mul_le_Rbar hmem
  have hYL : ∀ x : S.O, x ∈ S7.Obar S → x ∈ S.Lbar g → x = 1 := by
    intro x hxY hxL
    have h2 : orderOf x ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact S4.mul_self_of_mem_Lbar S H.conj_mem hxL)
    have h27 : orderOf x ∣ 27 := by
      have h := Subgroup.orderOf_dvd_natCard (S7.Obar S) hxY
      rwa [T.basis.card_range] at h
    have h1 : orderOf x ∣ 1 := by
      have h := Nat.dvd_gcd h2 h27
      rwa [show Nat.gcd 2 27 = 1 from by norm_num] at h
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1)
  have hconj_mem : ∀ s ∈ S.Lbar g, eb T.σ j * s * (eb T.σ j)⁻¹ ∈ S.Lbar g := by
    intro s hs
    have hmap : S.ρ h * s * (S.ρ h)⁻¹ ∈ S.Lbar ((h : G) * g) := by
      rw [S4.Lbar_mul S h g]
      simpa [MulAut.conj_apply] using
        Subgroup.mem_map_of_mem (MulAut.conj (S.ρ h)).toMonoidHom hs
    rw [hh] at hmap
    exact hle hmap
  have hcomm_mem : ∀ s ∈ S.Lbar g, eb T.σ j * s * (eb T.σ j)⁻¹ * s⁻¹ = 1 := by
    intro s hs
    have hsM : s ∈ S.Mbar := S.Lbar_le_Mbar g hs
    have hL : eb T.σ j * s * (eb T.σ j)⁻¹ * s⁻¹ ∈ S.Lbar g :=
      (S.Lbar g).mul_mem (hconj_mem s hs) ((S.Lbar g).inv_mem hs)
    have hY : eb T.σ j * s * (eb T.σ j)⁻¹ * s⁻¹ ∈ S7.Obar S := by
      have h1 : s⁻¹ * eb T.σ j * s ∈ S7.Obar S :=
        S7.conj_mem_Obar (S.Mbar.inv_mem hsM) (T.basis.eb_mem j)
      have h2 : s⁻¹ * eb T.σ j * s * (eb T.σ j)⁻¹ ∈ S7.Obar S :=
        (S7.Obar S).mul_mem h1 ((S7.Obar S).inv_mem (T.basis.eb_mem j))
      have h3 : s * (s⁻¹ * eb T.σ j * s * (eb T.σ j)⁻¹) * s⁻¹ ∈ S7.Obar S :=
        S7.conj_mem_Obar hsM h2
      have h4 : eb T.σ j * s * (eb T.σ j)⁻¹ * s⁻¹ =
          s * (s⁻¹ * eb T.σ j * s * (eb T.σ j)⁻¹) * s⁻¹ := by group
      rw [h4]
      exact h3
    exact hYL _ hY hL
  have hcent : ∀ s ∈ S.Lbar g, s * eb T.σ j = eb T.σ j * s := by
    intro s hs
    have hone : eb T.σ j * s * (eb T.σ j)⁻¹ = s := mul_inv_eq_one.mp (hcomm_mem s hs)
    calc s * eb T.σ j = (eb T.σ j * s * (eb T.σ j)⁻¹) * eb T.σ j := by rw [hone]
      _ = eb T.σ j * s := by group
  have hodd : Odd (Nat.card (S7.Obar S)) := by
    rw [S7.card_Obar]
    exact S5.odd_card_timmesfeldOddCore S.Mbar
  exact T.e_ne_one j (S5.eq_one_of_mem_of_commute H hodd (T.basis.eb_mem j) hcent)

theorem four_le_finrank_Vt (T : TriData S g) (H : Hyp4 S g) (i : Fin 3) :
    4 ≤ finrank (ZMod 2) (Vt S g (T.l i)) := by
  classical
  let y : (Fin 3 → ZMod 3) → S.O := fun c => T.σ (Multiplicative.ofAdd c)
  have hyY : ∀ c, y c ∈ S7.Obar S := fun c => T.basis.mem_iff.mpr ⟨c, rfl⟩
  have hyM : ∀ c, y c ∈ S.Mbar := fun c => S7.Obar_le_Mbar (hyY c)
  let hof : (Fin 3 → ZMod 3) → S.M := fun c =>
    Classical.choose (MonoidHom.mem_range.mp (hyM c))
  have hof_spec : ∀ c, S.ρ (hof c) = y c := fun c =>
    Classical.choose_spec (MonoidHom.mem_range.mp (hyM c))
  have hneg : ∀ c : Fin 3 → ZMod 3, c i = 0 → negAt i c = c := by
    intro c hc
    funext j
    by_cases hj : j = i
    · subst hj
      simp [negAt, hc]
    · simp [negAt, hj]
  have hconj_l : ∀ c, c i = 0 → y c * T.l i * (y c)⁻¹ = T.l i := by
    intro c hc
    have hact := T.basis.act i c
    rw [hneg c hc] at hact
    have hcomm : T.l i * y c = y c * T.l i := by
      have hc' := congrArg (fun z => z * T.l i) hact
      simpa [mul_assoc] using hc'
    rw [← hcomm]
    group
  have hlt : ∀ c, c i = 0 → T.l i ∈ S.Lbar ((hof c : G) * g) := by
    intro c hc
    have hmem := S4.conj_mem_Lbar_mul S (hof c) (T.l_mem i)
    rwa [hof_spec c, hconj_l c hc] at hmem
  let f : {c : Fin 3 → ZMod 3 // c i = 0} → Vt S g (T.l i) := fun c =>
    ⟨S.cl ((hof c.1 : G) * g * S.z * ((hof c.1 : G) * g)⁻¹), S4.cl_mem_Vt (hlt c.1 c.2)⟩
  have hf : Function.Injective f := by
    intro c c' hcc
    have hcl : S.cl ((hof c.1 : G) * g * S.z * ((hof c.1 : G) * g)⁻¹) =
        S.cl ((hof c'.1 : G) * g * S.z * ((hof c'.1 : G) * g)⁻¹) :=
      congrArg Subtype.val hcc
    have hA : ((y c.1 : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) =
        S.cl ((hof c.1 : G) * g * S.z * ((hof c.1 : G) * g)⁻¹) := by
      have h := S4.ρ_cl_conj_z S (hof c.1) H.conj_mem
      rwa [hof_spec c.1] at h
    have hB : ((y c'.1 : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) =
        S.cl ((hof c'.1 : G) * g * S.z * ((hof c'.1 : G) * g)⁻¹) := by
      have h := S4.ρ_cl_conj_z S (hof c'.1) H.conj_mem
      rwa [hof_spec c'.1] at h
    have heq : ((y c.1 : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) =
        ((y c'.1 : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) := by
      rw [hA, hcl, ← hB]
    have hy_eq : y (c'.1 - c.1) = (y c.1)⁻¹ * y c'.1 := by
      show T.σ (Multiplicative.ofAdd (c'.1 - c.1)) =
        (T.σ (Multiplicative.ofAdd c.1))⁻¹ * T.σ (Multiplicative.ofAdd c'.1)
      rw [← map_inv, ← ofAdd_neg, ← map_mul, ← ofAdd_add,
        show c'.1 - c.1 = -c.1 + c'.1 from by abel]
    have hfix : ((y (c'.1 - c.1) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
        (S.cl (g * S.z * g⁻¹)) = S.cl (g * S.z * g⁻¹) := by
      rw [hy_eq, coe_mul_apply, ← heq]
      exact inv_apply_apply_O (y c.1) _
    have hsub : c'.1 - c.1 = 0 := T.fix_cl (c'.1 - c.1) hfix
    exact Subtype.ext (sub_eq_zero.mp hsub).symm
  have hcard : Nat.card {c : Fin 3 → ZMod 3 // c i = 0} = 9 := by
    rw [Nat.card_eq_fintype_card]
    fin_cases i <;> decide
  have h9 : 9 ≤ Nat.card (Vt S g (T.l i)) := by
    rw [← hcard]
    exact Nat.card_le_card_of_injective f hf
  have hpow : 9 ≤ 2 ^ finrank (ZMod 2) (Vt S g (T.l i)) := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Vt S g (T.l i))
    rw [h] at h9
    simpa using h9
  by_contra hlt
  have hle : finrank (ZMod 2) (Vt S g (T.l i)) ≤ 3 := by omega
  have h8 : 2 ^ finrank (ZMod 2) (Vt S g (T.l i)) ≤ 2 ^ 3 :=
    Nat.pow_le_pow_right (by norm_num) hle
  norm_num at h8
  omega

theorem iso_of_fixed (T : TriData S g) (hw : S.width = 4)
    (hnoAll : S11.NoA2All S) (H : Hyp4 S g) (C : Cons311 S g) {k0 : Fin 3}
    (hk0 : ∀ x : S.Mbar, T.perm x k0 = k0) :
    ∃ q : QuadraticForm (ZMod 2) (Fin 4 → ZMod 2), timmesfeldNondegenerate q ∧
      (Nonempty (S.Mbar ≃* Equiv.Perm (Fin 3) × timmesfeldOmega q) ∨
        Nonempty (S.Mbar ≃* Equiv.Perm (Fin 3) × timmesfeldIsometries q)) := by
  classical
  have hNo : NoA2 S g := fun α h1 h2 h3 =>
    hnoAll g H.conj_mem H.conj_ne ⟨α, h1, h2, h3⟩
  rcases W4As.classify_four hw H hNo C (T.l_mem k0) (T.l_ne_one k0)
    (T.Rbar_ne_Lbar H k0) with ⟨-, hdim⟩ | ⟨hVQ, hΩ, h4⟩
  · have h4 := T.four_le_finrank_Vt H k0
    omega
  · refine iso_of_normal_line hw hnoAll H C (T.l_mem k0) (T.l_ne_one k0) hVQ hΩ h4
      (D := zpowers (eb T.σ k0)) (Subgroup.zpowers_le.mpr (T.e_mem_Mbar k0))
      (T.card_zpowers_e k0) ?_ ?_
    · intro x hx y hy
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      obtain ⟨s, hs, hconj⟩ := T.conj_e ⟨x, hx⟩ k0
      rw [hk0 ⟨x, hx⟩] at hconj
      have hpow : (x : S.O) * eb T.σ k0 * (x : S.O)⁻¹ = eb T.σ k0 ^ s.val := by
        rw [hconj, T.basis.sigma_single_eq_pow]
      refine Subgroup.mem_zpowers_iff.mpr ⟨(s.val : ℤ) * n, ?_⟩
      calc (eb T.σ k0 : S.O) ^ ((s.val : ℤ) * n)
          = ((eb T.σ k0) ^ s.val) ^ n := by rw [zpow_mul, zpow_natCast]
        _ = ((x : S.O) * eb T.σ k0 * (x : S.O)⁻¹) ^ n := by rw [hpow]
        _ = (x : S.O) * eb T.σ k0 ^ n * (x : S.O)⁻¹ := conj_zpow
    · intro x hx
      exact T.comm_mem_zpowers ⟨x, hx⟩ (hk0 ⟨x, hx⟩)

end TriData

end CFSG.GF2Type.Smith1979.TriPlus

end
