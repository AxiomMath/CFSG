module

public import CFSG.LargeExtraspecial.S13TwoF
public import CFSG.LargeExtraspecial.S13Gen
public import CFSG.LargeExtraspecial.S13TwoB
public import CFSG.LargeExtraspecial.S13TwoC
public import CFSG.LargeExtraspecial.S13TwoE

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S13

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.S10

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g g₁ : G} {K : Subgroup S.O}

section Four

variable (Y : Hyp13 S g K) {h : S.M} (hg : g₁ = (h : G) * g)
  (hperp : ∀ u ∈ Fbar S g K, ∀ v ∈ Fbar S g₁ K, polar S.q u v = 0)
  (hne : Fbar S g₁ K ≠ Fbar S g K)
include Y hg hperp hne

omit hne in
theorem Fbar_inf_clSub_eq_bot
    (h4 : Nat.card (Ebar S g K) =
      4 * Nat.card (Ebar S g K ⊓ ptStab S (Fbar S g K ⊔ Fbar S g₁ K) : Subgroup S.O))
    {m : S.M} (hm : S.ρ m ∈ K) :
    Fbar S g K ⊓ S.clSub (S.QG ⊓ S.Qa ((m : G) * g₁)) = ⊥ := by
  set D : Submodule (ZMod 2) S.Qt := Fbar S g K ⊔ Fbar S g₁ K with hD
  have Y₁ : Hyp13 S g₁ K := Y.mul hg
  have hperp' : ∀ u ∈ Fbar S g₁ K, ∀ v ∈ Fbar S g K, polar S.q u v = 0 := fun u hu v hv => by
    rw [QuadraticMap.polar_comm]; exact hperp v hv u hu
  have hD' : (Fbar S g₁ K ⊔ Fbar S g K : Submodule (ZMod 2) S.Qt) = D := sup_comm _ _
  obtain ⟨y, hyX, hyE⟩ := Y.exists_conj_Ebar hg
  have hE₁S : Ebar S g₁ K ≤ stab2 S D := by
    have := Ebar_le_stab2 Y₁ hperp'
    rwa [hD'] at this
  have hyS : y ∈ stab2 S D := (sup_le (Ebar_le_stab2 Y hperp) hE₁S) hyX
  obtain ⟨hy1, hy2, -⟩ := hyS
  have hC : (Ebar S g K ⊓ ptStab S D).map (MulAut.conj y).toMonoidHom =
      Ebar S g₁ K ⊓ ptStab S D := by
    rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj y).injective, hyE, ptStab_map_conj hy1 hy2]
  have h4₁ : Nat.card (Ebar S g₁ K) = 4 * Nat.card (Ebar S g₁ K ⊓ ptStab S D : Subgroup S.O) := by
    rw [← hC, ← hyE, Subgroup.card_map_of_injective (MulAut.conj y).injective,
      Subgroup.card_map_of_injective (MulAut.conj y).injective]
    exact h4
  by_contra hb
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
  have hcQ := conj_mem_QG' S m.2 Y₁.haQ
  obtain ⟨r, hr, hcard⟩ := card_Ebar_eq_mul Y₁ Y hperp' hu.1 hu0
    (Λ := (ZMod 2) ∙ S.cl ((m : G) * g₁ * S.z * ((m : G) * g₁)⁻¹))
    (fun e he => Lbar_apply_sub_mem_span' hcQ hu.2 (Hyp13.Ebar_le_Lbar_mul (g := g₁) hm he))
  rw [hD'] at hcard
  have h2 : Nat.card ((ZMod 2) ∙ S.cl ((m : G) * g₁ * S.z * ((m : G) * g₁)⁻¹) :
      Submodule (ZMod 2) S.Qt) = 2 := by
    rw [S.card_submodule, finrank_span_singleton
      (cl_conj_z_ne_zero S hcQ (conj_ne_z' S m.2 Y₁.hne)), pow_one]
  rw [h2] at hr
  have hr2 : r ≤ 2 := Nat.le_of_dvd (by norm_num) hr
  have hpos : 0 < Nat.card (Ebar S g₁ K ⊓ ptStab S D : Subgroup S.O) := Nat.card_pos
  rw [h4₁] at hcard
  nlinarith

omit hne in
theorem not_card_Ebar_eq_four_mul
    (h4 : Nat.card (Ebar S g K) =
      4 * Nat.card (Ebar S g K ⊓ ptStab S (Fbar S g K ⊔ Fbar S g₁ K) : Subgroup S.O)) :
    False := by
  set D : Submodule (ZMod 2) S.Qt := Fbar S g K ⊔ Fbar S g₁ K with hD
  have Y₁ : Hyp13 S g₁ K := Y.mul hg
  have hperp' : ∀ u ∈ Fbar S g₁ K, ∀ v ∈ Fbar S g K, polar S.q u v = 0 := fun u hu v hv => by
    rw [QuadraticMap.polar_comm]; exact hperp v hv u hu
  have hD' : (Fbar S g₁ K ⊔ Fbar S g K : Submodule (ZMod 2) S.Qt) = D := sup_comm _ _
  have hDperp : D ≤ perp S D := Dbar_le_perp Y Y₁ hperp
  obtain ⟨y, hyX, hyE⟩ := Y.exists_conj_Ebar hg
  have hE₁S : Ebar S g₁ K ≤ stab2 S D := by
    have := Ebar_le_stab2 Y₁ hperp'
    rwa [hD'] at this
  have hyS : y ∈ stab2 S D := (sup_le (Ebar_le_stab2 Y hperp) hE₁S) hyX
  have hyS' : y⁻¹ ∈ stab2 S D := inv_mem hyS
  obtain ⟨hy1, hy2, -⟩ := hyS
  have hyM : y ∈ S.Mbar := (sup_le Hyp13.Ebar_le_Mbar Hyp13.Ebar_le_Mbar) hyX
  obtain ⟨m₀, hm₀⟩ : ∃ m₀ : S.M, S.ρ m₀ = y := MonoidHom.mem_range.mp hyM
  have hyF : ∀ v ∈ Fbar S g K, (y : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ Fbar S g₁ K := by
    intro v hv
    change _ ∈ fixSub S (Ebar S g₁ K)
    rw [← hyE, mem_fixSub_map_conj_iff, inv_apply_apply_O]
    exact hv
  set C₀ := (Ebar S g K ⊓ ptStab S D : Subgroup S.O) with hC₀
  have key : ∀ m' : S.M, S.ρ m' ∈ K → ∀ c ∈ C₀,
      ∀ w ∈ S.clSub (S.QG ⊓ S.Qa ((m₀ : G) * ((m' : G) * g))) ⊓ perp S D,
        (c : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w := by
    intro m' hm' c hc w hw
    have hbQ : (m' : G) * g * S.z * ((m' : G) * g)⁻¹ ∈ S.QG := conj_mem_QG' S m'.2 Y.haQ
    have hcQ : (m₀ : G) * ((m' : G) * g) * S.z * ((m₀ : G) * ((m' : G) * g))⁻¹ ∈ S.QG :=
      conj_mem_QG' S m₀.2 hbQ
    have hcz : (m₀ : G) * ((m' : G) * g) * S.z * ((m₀ : G) * ((m' : G) * g))⁻¹ ≠ S.z :=
      conj_ne_z' S m₀.2 (conj_ne_z' S m'.2 Y.hne)
    have hpt : S.cl ((m₀ : G) * ((m' : G) * g) * S.z * ((m₀ : G) * ((m' : G) * g))⁻¹) ∈
        Fbar S g₁ K := by
      rw [← ρ_cl_conj_z S m₀ hbQ, hm₀]
      apply hyF
      rw [← ρ_cl_conj_z S m' Y.haQ]
      exact Hyp13.K_apply_mem_Fbar hm' (cl_mem_Fbar Y.H)
    obtain ⟨m'', hm'', hcl⟩ := Y₁.exists_eq_cl_of_mem_Fbar hpt (cl_conj_z_ne_zero S hcQ hcz)
    have hQQ := clSub_eq_of_cl_eq hcQ hcz (conj_mem_QG' S m''.2 Y₁.haQ) hcl
    have h1 : (c : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Fbar S g K :=
      Y.Ebar_apply_sub_mem_Fbar (fun f hf => by
        rw [QuadraticMap.polar_comm]
        exact (mem_perp.mp hw.2) f (Submodule.mem_sup_left hf)) hc.1
    have hfix := hc.2 _ (Submodule.mem_sup_right hpt)
    have hcM : (c : S.O) ∈ S.Mbar := Hyp13.Ebar_le_Mbar hc.1
    have h2 : (c : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈
        S.clSub (S.QG ⊓ S.Qa ((m₀ : G) * ((m' : G) * g))) :=
      sub_mem (apply_mem_clSub_of_fix hcQ hcz hcM hfix hw.1) hw.1
    rw [← hQQ] at h2
    have h3 := Fbar_inf_clSub_eq_bot Y hg hperp h4 hm''
    have h5 : (c : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ (⊥ : Submodule (ZMod 2) S.Qt) := h3 ▸ ⟨h1, h2⟩
    exact sub_eq_zero.mp ((Submodule.mem_bot _).mp h5)
  obtain ⟨k, hk, hk1⟩ := Y.exists_K
  obtain ⟨m, rfl⟩ := Y.exists_ρ_eq hk
  have hm2 : S.ρ (m * m) ∈ K := by rw [map_mul]; exact mul_mem hk hk
  have h1K : S.ρ (1 : S.M) ∈ K := by rw [map_one]; exact one_mem _
  set P : G → Submodule (ZMod 2) S.Qt := fun b => S.clSub (S.QG ⊓ S.Qa b) ⊓ perp S D with hP
  set V₁ : Submodule (ZMod 2) S.Qt := D ⊔ P (((1 : S.M) : G) * g) ⊔ P ((m : G) * g) ⊔
    P (((m * m : S.M) : G) * g) with hV₁
  set W₂ : Submodule (ZMod 2) S.Qt := D ⊔ P ((m₀ : G) * (((1 : S.M) : G) * g)) ⊔
    P ((m₀ : G) * ((m : G) * g)) ⊔ P ((m₀ : G) * (((m * m : S.M) : G) * g)) with hW₂
  have hW₂fix : ∀ c ∈ C₀, ∀ w ∈ W₂, (c : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w := by
    intro c hc
    have hle : W₂ ≤ LinearMap.ker ((c : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1) := by
      refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
      · intro d hd
        simp [hc.2 d hd]
      · intro w hw
        simp [key 1 h1K c hc w hw]
      · intro w hw
        simp [key m hk c hc w hw]
      · intro w hw
        simp [key (m * m) hm2 c hc w hw]
    intro w hw
    have := hle hw
    simpa [sub_eq_zero] using this
  have hV₁perp : V₁ ≤ perp S D :=
    sup_le (sup_le (sup_le hDperp inf_le_right) inf_le_right) inf_le_right
  have hPmap : ∀ b : G, ∀ w ∈ P b, (y : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ P ((m₀ : G) * b) := by
    rintro b w ⟨hw1, hw2⟩
    refine ⟨?_, apply_mem_perp hy2 hw2⟩
    rw [← hm₀]
    exact apply_mem_clSub_Qa_mul m₀ b hw1
  have hyV : V₁ ≤ W₂.comap (y : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap := by
    refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
    · intro d hd
      exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left (hy1 d hd)))
    · intro w hw
      exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_right
        (hPmap _ w hw)))
    · intro w hw
      exact Submodule.mem_sup_left (Submodule.mem_sup_right (hPmap _ w hw))
    · intro w hw
      exact Submodule.mem_sup_right (hPmap _ w hw)
  have hVW : V₁ ≤ W₂ := by
    intro v hv
    have h1 : ((y⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ V₁ := by
      have := hyS'.2.2 v (hV₁perp hv)
      have e : ((y⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v =
          (((y⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v) + v := by abel
      rw [e]
      exact add_mem (Submodule.mem_sup_left (Submodule.mem_sup_left
        (Submodule.mem_sup_left this))) hv
    have h2 := hyV h1
    simp only [Submodule.mem_comap, LinearEquiv.coe_coe] at h2
    rwa [apply_inv_apply_O] at h2
  have hPg : P g ≤ fixSub S C₀ := by
    intro w hw c hc
    have hw' : w ∈ P (((1 : S.M) : G) * g) := by
      simpa [hP] using hw
    exact hW₂fix c hc w (hVW (Submodule.mem_sup_left (Submodule.mem_sup_left
      (Submodule.mem_sup_right hw'))))
  have hdimA := finrank_clSub_QG_inf_Qa Y.haQ Y.hne Y.C.card_QG_inf_Qa
  have hPge : S.width ≤ finrank (ZMod 2) (P g) + 2 := by
    have h := finrank_inf_perp_ge (S.clSub (S.QG ⊓ S.Qa g)) (Fbar S g₁ K)
    rw [hdimA, Y₁.finrank_Fbar] at h
    have hle : S.clSub (S.QG ⊓ S.Qa g) ⊓ perp S (Fbar S g₁ K) ≤ P g := by
      rintro w ⟨hw1, hw2⟩
      refine ⟨hw1, mem_perp.mpr fun d hd => ?_⟩
      obtain ⟨f, hf, f₁, hf₁, rfl⟩ := Submodule.mem_sup.mp hd
      rw [polar_add_left, polar_eq_zero_of_mem_clSub Y.hne (Y.Fbar_le_clSub hf) hw1,
        (mem_perp.mp hw2) f₁ hf₁, add_zero]
    have := Submodule.finrank_mono hle
    omega
  have hcard := card_mul_two_pow_finrank_fix Y.H Y.C (K := C₀) (inf_le_left.trans Ebar_le_Lbar)
  have hd := Submodule.finrank_mono (le_inf inf_le_left hPg :
    P g ≤ S.clSub (S.QG ⊓ S.Qa g) ⊓ fixSub S C₀)
  have hE := Y.card_Ebar
  have h7 := Y.seven_le
  set c := Nat.card C₀ with hc
  set d := finrank (ZMod 2) ↥(S.clSub (S.QG ⊓ S.Qa g) ⊓ fixSub S C₀) with hdd
  have hpow : c * 2 ^ (S.width - 2) ≤ c * 2 ^ d :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))
  have h2n : 2 ^ S.width = 4 * 2 ^ (S.width - 2) := by
    rw [show S.width = (S.width - 2) + 2 by omega, pow_add]
    simp only [Nat.add_sub_cancel]
    ring
  have hc4 : c ≤ 4 := by
    have hpos : 0 < 2 ^ (S.width - 2) := by positivity
    have : c * 2 ^ (S.width - 2) ≤ 4 * 2 ^ (S.width - 2) := by rw [← h2n, ← hcard]; exact hpow
    exact Nat.le_of_mul_le_mul_right this hpos
  have h16 : 2 ^ (S.width - 2) ≤ 2 ^ 4 := by rw [← hE, h4]; norm_num; omega
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h16
  omega

end Four

end CFSG.LargeExtraspecial.S13
