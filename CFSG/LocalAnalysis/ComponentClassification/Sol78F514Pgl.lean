module

public import CFSG.LocalAnalysis.ComponentClassification.Sol78F514Dih
public import CFSG.GH74.GLS.Stage1.Thm6.Glue.Dihedral
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12b.Lemma12_9b

public noncomputable section

namespace CFSG.ComponentClassification.Sol78.F514

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools CFSG.ComponentClassification.Foote5 CFSG.GH74.GLS.Stage1.Thm6.Sec12b

variable {G : Type} [Group G] [Finite G]

namespace Hyp

variable {L₀ L Q S T : Subgroup G} {z t s : G} {𝕊 : Type} [Group 𝕊] [Finite 𝕊]
  {ε : L ⧸ pPrimeCore 2 L ≃* 𝕊} {Lin : Subgroup (MulAut 𝕊)} (H : Hyp L₀ L Q S T z t s ε Lin)
include H

theorem exists_dihData_R :
    ∃ (ρ b : G) (j : ℕ), DihData (S ⊓ L) ρ b j ∧ ρ ^ DihData.zc j = t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, -, ⟨e⟩⟩ := H.sec5.exists_dihedral_R
  have hm2 : 2 ≤ m := by
    by_contra hlt
    obtain ⟨a, ha, b, hb, hab⟩ := H.nonab
    apply hab
    have hc : ∀ x y : DihedralGroup (2 ^ m), x * y = y * x := by
      rcases (show m = 0 ∨ m = 1 by omega) with rfl | rfl
      · decide
      · decide
    have h1 : e (⟨a, ha⟩ * ⟨b, hb⟩) = e (⟨b, hb⟩ * ⟨a, ha⟩) := by
      rw [map_mul, map_mul]; exact hc _ _
    exact congrArg Subtype.val (e.injective h1)
  have h8 : 8 ≤ Nat.card ↥(S ⊓ L) := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    calc 8 = 2 * 2 ^ 2 := by norm_num
      _ ≤ 2 * 2 ^ m := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hm2)
  obtain ⟨ρ, b, j, hD⟩ := dihData_of_dih H.sec5.R_sylow.isPGroup le_rfl
    (CFSG.GH74.GLS.Stage1.Thm6.Glue.Dihedral.isDihedral2_of_equiv e) h8
  refine ⟨ρ, b, j, hD, (hD.central_inv_eq H.sec5.tR H.mul_self_t H.t_ne_one ?_).symm⟩
  intro r hr
  exact (H.sec5.tZ r (mem_inf.mp hr).1).symm

theorem exists_dihData_Rs :
    ∃ (ρ b : G) (j : ℕ), DihData (conjugate (S ⊓ L) s) ρ b j ∧ ρ ^ DihData.zc j = z := by
  obtain ⟨ρ, b, j, hD, hc⟩ := H.exists_dihData_R
  refine ⟨s⁻¹ * ρ * s, s⁻¹ * b * s, j, dihData_conjugate hD s, ?_⟩
  rw [conj_inv_zpow, hc, H.conj_s_inv_t]

theorem mem_R_iff_conj {y : G} (hyS : y ∈ S) (x : G) : x ∈ S ⊓ L ↔ y * x * y⁻¹ ∈ S ⊓ L :=
  ⟨fun hx => H.sec5.conj_mem_R hyS hx, fun hx => by
    have := H.sec5.conj_mem_R (inv_mem hyS) hx
    rwa [show y⁻¹ * (y * x * y⁻¹) * y⁻¹⁻¹ = x by group] at this⟩

theorem mem_Rs_iff_conj {y : G} (hyS : y ∈ S) (x : G) :
    x ∈ conjugate (S ⊓ L) s ↔ y * x * y⁻¹ ∈ conjugate (S ⊓ L) s := by
  have hN := H.S_le_normalizer_Rs hyS
  exact ⟨fun hx => (mem_normalizer_iff.mp hN x).mp hx,
    fun hx => (mem_normalizer_iff.mp hN x).mpr hx⟩

theorem pgl_of_conj {x : G} (hx : x ∈ centralizer ({z * t} : Set G))
    (hxT : x⁻¹ * z * x ∈ T) (hxz : x⁻¹ * z * x ≠ z) (hxt : x⁻¹ * z * x ≠ t) :
    x⁻¹ * z * x ∈ S ∧ actG L ε (x⁻¹ * z * x) ∈ Lin ∧ actG L ε (x⁻¹ * z * x) ∉ innAut5 𝕊 := by
  refine ⟨H.l512 x hxT, ?_⟩
  rcases H.l513 x hxT with h1 | h1 | h1
  · exfalso
    rcases H.conj_z_eq_of_mem_sup hx (mem_sup_left h1) with h2 | h2
    · exact hxz h2
    · exact hxt h2
  · exfalso
    rcases H.conj_z_eq_of_mem_sup hx (mem_sup_right h1) with h2 | h2
    · exact hxz h2
    · exact hxt h2
  · exact h1

theorem conj_z_mul_self (x : G) : x⁻¹ * z * x * (x⁻¹ * z * x) = 1 := by
  rw [show x⁻¹ * z * x * (x⁻¹ * z * x) = x⁻¹ * (z * z) * x by group, H.mul_self_z]; group

theorem fix_R_of_conj {x : G} (hx : x ∈ centralizer ({z * t} : Set G))
    (hxT : x⁻¹ * z * x ∈ T) (hxz : x⁻¹ * z * x ≠ z) (hxt : x⁻¹ * z * x ≠ t) :
    ∀ r ∈ S ⊓ L, r * (x⁻¹ * z * x) = (x⁻¹ * z * x) * r → r = 1 ∨ r = t := by
  obtain ⟨hS, hlin, hinn⟩ := H.pgl_of_conj hx hxT hxz hxt
  intro r hr hrc
  exact H.sec5.eq_one_or_eq_t_of_pgl ε H.autData hS (H.conj_z_mul_self x) hlin hinn hr hrc

theorem fix_Rs_of_conj {x : G} (hx : x ∈ centralizer ({z * t} : Set G))
    (hxT : x⁻¹ * z * x ∈ T) (hxz : x⁻¹ * z * x ≠ z) (hxt : x⁻¹ * z * x ≠ t) :
    ∀ r ∈ conjugate (S ⊓ L) s, r * (x⁻¹ * z * x) = (x⁻¹ * z * x) * r → r = 1 ∨ r = z := by
  set x' := x * s⁻¹ with hx'
  have he : x'⁻¹ * z * x' = s * (x⁻¹ * z * x) * s⁻¹ := by rw [hx']; group
  have hx'C : x' ∈ centralizer ({z * t} : Set G) :=
    mul_mem hx (inv_mem (H.T_le_centralizer_d H.sT))
  have hx'T : x'⁻¹ * z * x' ∈ T := by
    rw [he]; exact mul_mem (mul_mem H.sT hxT) (inv_mem H.sT)
  have hx'z : x'⁻¹ * z * x' ≠ z := fun e => hxt (by
    have : x⁻¹ * z * x = s⁻¹ * (x'⁻¹ * z * x') * s := by rw [he]; group
    rw [this, e, H.conj_s_inv_z])
  have hx't : x'⁻¹ * z * x' ≠ t := fun e => hxz (by
    have : x⁻¹ * z * x = s⁻¹ * (x'⁻¹ * z * x') * s := by rw [he]; group
    rw [this, e, H.conj_s_inv_t])
  have hfix := H.fix_R_of_conj hx'C hx'T hx'z hx't
  intro r hr hrc
  have h1 : s * r * s⁻¹ ∈ S ⊓ L := mem_conjugate_iff.mp hr
  have h2 : s * r * s⁻¹ * (x'⁻¹ * z * x') = x'⁻¹ * z * x' * (s * r * s⁻¹) := by
    rw [he]
    calc s * r * s⁻¹ * (s * (x⁻¹ * z * x) * s⁻¹) = s * (r * (x⁻¹ * z * x)) * s⁻¹ := by group
      _ = s * ((x⁻¹ * z * x) * r) * s⁻¹ := by rw [hrc]
      _ = s * (x⁻¹ * z * x) * s⁻¹ * (s * r * s⁻¹) := by group
  rcases hfix _ h1 h2 with e | e
  · left
    calc r = s⁻¹ * (s * r * s⁻¹) * s := by group
      _ = 1 := by rw [e]; group
  · right
    calc r = s⁻¹ * (s * r * s⁻¹) * s := by group
      _ = z := by rw [e, H.conj_s_inv_t]

theorem false_of_elemAbelian_R {y : G} (hyS : y ∈ S) (hy2 : y * y = 1)
    (hfix : ∀ r ∈ S ⊓ L, r * y = y * r → r = 1 ∨ r = t) {x : G} (hxR : x ∈ S ⊓ L)
    (hx2 : x * x = 1) (hx1 : x ≠ 1) (hxt : x ≠ t)
    (hV : ∀ g ∈ S, x * (g * x * g⁻¹) * (x * (g * x * g⁻¹)) = 1) : False := by
  obtain ⟨ρ, b, j, hD, hc⟩ := H.exists_dihData_R
  rw [← hc] at hfix hxt
  exact false_of_elemAbelian hD hy2 (H.mem_R_iff_conj hyS) hfix hxR hx2 hx1 hxt
    (hV ρ (mem_inf.mp (hD.ρ_mem)).1) (hV y hyS)

theorem false_of_elemAbelian_Rs {y : G} (hyS : y ∈ S) (hy2 : y * y = 1)
    (hfix : ∀ r ∈ conjugate (S ⊓ L) s, r * y = y * r → r = 1 ∨ r = z) {x : G}
    (hxR : x ∈ conjugate (S ⊓ L) s) (hx2 : x * x = 1) (hx1 : x ≠ 1) (hxz : x ≠ z)
    (hV : ∀ g ∈ S, x * (g * x * g⁻¹) * (x * (g * x * g⁻¹)) = 1) : False := by
  obtain ⟨ρ, b, j, hD, hc⟩ := H.exists_dihData_Rs
  rw [← hc] at hfix hxz
  exact false_of_elemAbelian hD hy2 (H.mem_Rs_iff_conj hyS) hfix hxR hx2 hx1 hxz
    (hV ρ (H.Rs_le_S hD.ρ_mem)) (hV y hyS)

theorem exists_conj_refl_R {y : G} (hyS : y ∈ S) (hy2 : y * y = 1)
    (hfix : ∀ r ∈ S ⊓ L, r * y = y * r → r = 1 ∨ r = t) :
    ∃ b ∈ S ⊓ L, b * b = 1 ∧ b ≠ 1 ∧ b ≠ t ∧ ∀ x ∈ S ⊓ L, x * x = 1 → x ≠ 1 → x ≠ t →
      ∃ g ∈ S ⊓ L, g * x * g⁻¹ = b ∨ g * (y * x * y⁻¹) * g⁻¹ = b := by
  obtain ⟨ρ, b, j, hD, hc⟩ := H.exists_dihData_R
  rw [← hc] at hfix
  refine ⟨b, hD.s_mem, hD.s_sq, hD.s_ne_one, by rw [← hc]; exact hD.s_ne_z0, ?_⟩
  intro x hxR hx2 hx1 hxt
  rw [← hc] at hxt
  exact exists_conj_refl hD hy2 (H.mem_R_iff_conj hyS) hfix (refl_of_mem hD hxR hx2 hx1 hxt)

end Hyp

end CFSG.ComponentClassification.Sol78.F514
