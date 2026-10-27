module

public import CFSG.GF2Type.Smith1979.CaseIIA8
public import CFSG.LargeExtraspecial.S45QLin

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.Case2

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.LargeExtraspecial
  CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

theorem isSimpleGroup_GL_three (V : Type*) [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (hV : Module.finrank (ZMod 2) V = 3) :
    IsSimpleGroup (V ≃ₗ[ZMod 2] V) := by
  classical
  let b : Module.Basis (Fin 3) (ZMod 2) V := Module.finBasisOfFinrankEq (ZMod 2) V hV
  let e : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2) ≃* (V ≃ₗ[ZMod 2] V) :=
    (Matrix.GeneralLinearGroup.toLin' b).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V)
  haveI := CFSG.LargeExtraspecial.S45Q.isSimpleGroup_GL_zmod_two (n := 3) le_rfl
  exact e.symm.isSimpleGroup

theorem dichotomy_of_simple {A H : Type*} [Group A] [Group H] [IsSimpleGroup H] (ψ : A →* H)
    (hψ : Function.Surjective ψ) (hab : ∀ a ∈ ψ.ker, ∀ b ∈ ψ.ker, a * b = b * a) :
    (∀ c : A, (∀ k ∈ ψ.ker, k * c = c * k) → c ∈ ψ.ker) ∨
      (∀ c : A, ∀ k ∈ ψ.ker, k * c = c * k) := by
  classical
  set C : Subgroup A := Subgroup.centralizer (ψ.ker : Set A) with hC
  have hCmem : ∀ c : A, c ∈ C ↔ ∀ k ∈ ψ.ker, k * c = c * k := by
    intro c
    rw [hC]
    exact Subgroup.mem_centralizer_iff
  have hCn : C.Normal := by
    refine ⟨fun c hc p => ?_⟩
    rw [hCmem] at hc ⊢
    intro k hk
    have hk' : p⁻¹ * k * p ∈ ψ.ker := by
      have h := (MonoidHom.normal_ker ψ).conj_mem k hk p⁻¹
      rwa [inv_inv] at h
    have h1 : (p⁻¹ * k * p) * c = c * (p⁻¹ * k * p) := hc _ hk'
    calc k * (p * c * p⁻¹) = p * ((p⁻¹ * k * p) * c) * p⁻¹ := by group
      _ = p * (c * (p⁻¹ * k * p)) * p⁻¹ := by rw [h1]
      _ = p * c * p⁻¹ * k := by group
  have hmapN : (C.map ψ).Normal := Subgroup.Normal.map hCn ψ hψ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (C.map ψ) with h | h
  · left
    intro c hc
    have hcC : c ∈ C := (hCmem c).mpr hc
    have hmem : ψ c ∈ C.map ψ := Subgroup.mem_map_of_mem ψ hcC
    rw [h, Subgroup.mem_bot] at hmem
    exact MonoidHom.mem_ker.mpr hmem
  · right
    intro c k hk
    have hc : c ∈ C := by
      have hmem : ψ c ∈ C.map ψ := by
        rw [h]
        exact Subgroup.mem_top _
      obtain ⟨d, hd, hdc⟩ := Subgroup.mem_map.mp hmem
      have hdk : d⁻¹ * c ∈ ψ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hdc, inv_mul_cancel]
      have hkC : d⁻¹ * c ∈ C := (hCmem _).mpr fun k' hk' => hab k' hk' _ hdk
      have hsplit : c = d * (d⁻¹ * c) := by group
      rw [hsplit]
      exact mul_mem hd hkC
    exact (hCmem c).mp hc k hk

namespace Data

variable (D : Data S g t)
include D

theorem mem_Rder_or_mul_t (hCE : S4.CentralExtInput.{u}) :
    ∀ r ∈ Rbar S g t, r ∈ Rder S g t ∨ r * t ∈ Rder S g t := by
  obtain ⟨χ, hχ⟩ := D.exists_chiR
  rw [← Rprime_eq_Rder D hχ hCE]
  intro r hr
  by_cases h : χ ⟨r, hr⟩ = 1
  · exact Or.inl (mem_Rprime.mpr ⟨hr, h⟩)
  · right
    have h1 : χ ⟨r, hr⟩ = Multiplicative.ofAdd 1 := (mult_zmod2_cases _).resolve_left h
    have hrt : r * t ∈ Rbar S g t := mul_mem hr (Lbar_le_Rbar D.ht D.ht)
    refine mem_Rprime.mpr ⟨hrt, ?_⟩
    have e : (⟨r * t, hrt⟩ : ↥(Rbar S g t)) = ⟨r, hr⟩ * D.tR := rfl
    rw [e, map_mul, h1, hχ]
    exact mult_zmod2_mul_self _

end Data

theorem Rder_le_Rbar' (D : Data S g t) (hCE : S4.CentralExtInput.{u}) :
    Rder S g t ≤ Rbar S g t :=
  (Rbar_structure_II D hCE).2.2.2.1

@[expose] noncomputable def psiP (haQ : g * S.z * g⁻¹ ∈ S.QG) (t : S.O)
    (hle : Rder S g t ≤ Rbar S g t) : ↥(Rder S g t) →* (Vt S g t ≃ₗ[ZMod 2] Vt S g t) :=
  (resV haQ t).comp (Subgroup.inclusion hle)

theorem psiP_eq_one_iff (haQ : g * S.z * g⁻¹ ∈ S.QG) (t : S.O)
    (hle : Rder S g t ≤ Rbar S g t) (p : ↥(Rder S g t)) :
    psiP haQ t hle p = 1 ↔ (p : S.O) ∈ Nbar S g t :=
  resV_eq_one_iff haQ (⟨(p : S.O), hle p.2⟩ : ↥(Rbar S g t))

namespace Data

variable (D : Data S g t)
include D

theorem psiP_surjective (hCE : S4.CentralExtInput.{u}) (hle : Rder S g t ≤ Rbar S g t) :
    Function.Surjective (psiP D.H.conj_mem t hle) := by
  intro e
  have he : e ∈ (resV D.H.conj_mem t).range := by
    rw [range_resV, D.hL.eq_top]
    exact Subgroup.mem_top _
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp he
  rcases D.mem_Rder_or_mul_t hCE x.1 x.2 with h | h
  · exact ⟨⟨x.1, h⟩, hx⟩
  · refine ⟨⟨x.1 * t, h⟩, ?_⟩
    have htN : resV D.H.conj_mem t D.tR = 1 :=
      (resV_eq_one_iff D.H.conj_mem D.tR).mpr (self_mem_Nbar D.H D.ht)
    have e2 : (Subgroup.inclusion hle ⟨x.1 * t, h⟩ : ↥(Rbar S g t)) = x * D.tR :=
      Subtype.ext rfl
    show resV D.H.conj_mem t (Subgroup.inclusion hle ⟨x.1 * t, h⟩) = e
    rw [e2, map_mul, htN, mul_one, hx]

theorem not_central_Nbar (hCE : S4.CentralExtInput.{u}) :
    ¬ ∀ n ∈ Nbar S g t, ∀ r ∈ Rbar S g t, r * n = n * r := by
  intro hC
  obtain ⟨n, hn, hnL⟩ := D.exists_Nbar_not_Lbar
  apply hnL
  rw [D.Nbar_eq_N0bar hCE] at hn
  have hle : N0bar S g t ≤ S.Lbar g := by
    refine iSup₂_le fun k hk => ?_
    rintro x ⟨hxL, hxN⟩
    rw [Lbar_mul S k g] at hxL
    obtain ⟨l, hl, hxe⟩ := hxL
    have hxe' : S.ρ k * l * (S.ρ k)⁻¹ = x := hxe
    have hc : S.ρ k * x = x * S.ρ k := hC x hxN (S.ρ k) hk
    have hlx : l = x := by
      calc l = (S.ρ k)⁻¹ * (S.ρ k * l * (S.ρ k)⁻¹) * S.ρ k := by group
        _ = (S.ρ k)⁻¹ * x * S.ρ k := by rw [hxe']
        _ = (S.ρ k)⁻¹ * (x * S.ρ k) := by group
        _ = (S.ρ k)⁻¹ * (S.ρ k * x) := by rw [hc]
        _ = x := by group
    rw [← hlx]
    exact hl
  exact hle hn

theorem Nbar_central_of (hCE : S4.CentralExtInput.{u})
    (hS : ∀ s ∈ Rder S g t ⊓ Nbar S g t, ∀ r ∈ Rbar S g t, r * s = s * r) :
    ∀ n ∈ Nbar S g t, ∀ r ∈ Rbar S g t, r * n = n * r := by
  intro n hn r hr
  have htc : r * t = t * r := commute_of_mem_Rbar D.H.conj_mem hr
  rcases D.mem_Rder_or_mul_t hCE n (Nbar_le_Rbar hn) with h | h
  · exact hS n ⟨h, hn⟩ r hr
  · have hnt : n * t ∈ Nbar S g t := mul_mem hn (self_mem_Nbar D.H D.ht)
    have hs : r * (n * t) = n * t * r := hS (n * t) ⟨h, hnt⟩ r hr
    calc r * n = r * n * t * t⁻¹ := by group
      _ = n * t * r * t⁻¹ := by rw [mul_assoc r n t, hs]
      _ = n * (t * r) * t⁻¹ := by group
      _ = n * (r * t) * t⁻¹ := by rw [htc]
      _ = n * r := by group

end Data

theorem Rder_faithful_on_Sbar (D : Data S g t) (hCE : S4.CentralExtInput.{u}) :
    ∀ r ∈ Rder S g t, (∀ s ∈ Rder S g t ⊓ Nbar S g t, r * s * r⁻¹ = s) → r ∈ Nbar S g t := by
  intro r hr hcent
  have hle : Rder S g t ≤ Rbar S g t := Rder_le_Rbar' D hCE
  haveI := isSimpleGroup_GL_three (Vt S g t) D.h3
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hNcomm, -⟩ := Rbar_structure_II D hCE
  have hab : ∀ a ∈ (psiP D.H.conj_mem t hle).ker, ∀ b ∈ (psiP D.H.conj_mem t hle).ker,
      a * b = b * a := by
    intro a ha b hb
    exact Subtype.ext (hNcomm _ ((psiP_eq_one_iff D.H.conj_mem t hle a).mp
      (MonoidHom.mem_ker.mp ha)) _ ((psiP_eq_one_iff D.H.conj_mem t hle b).mp
      (MonoidHom.mem_ker.mp hb)))
  rcases dichotomy_of_simple (psiP D.H.conj_mem t hle) (D.psiP_surjective hCE hle) hab with
    h | h
  · have hc : (⟨r, hr⟩ : ↥(Rder S g t)) ∈ (psiP D.H.conj_mem t hle).ker := by
      apply h
      intro k hk
      apply Subtype.ext
      have hkN : (k : S.O) ∈ Rder S g t ⊓ Nbar S g t :=
        ⟨k.2, (psiP_eq_one_iff D.H.conj_mem t hle k).mp (MonoidHom.mem_ker.mp hk)⟩
      exact (mul_inv_eq_iff_eq_mul.mp (hcent _ hkN)).symm
    exact (psiP_eq_one_iff D.H.conj_mem t hle ⟨r, hr⟩).mp (MonoidHom.mem_ker.mp hc)
  · exfalso
    apply D.not_central_Nbar hCE
    apply D.Nbar_central_of hCE
    intro s hs r' hr'
    have hsP : s ∈ Rder S g t := hs.1
    have hsN : s ∈ Nbar S g t := hs.2
    have hPc : ∀ p ∈ Rder S g t, s * p = p * s := by
      intro p hp
      have hk : (⟨s, hsP⟩ : ↥(Rder S g t)) ∈ (psiP D.H.conj_mem t hle).ker :=
        MonoidHom.mem_ker.mpr ((psiP_eq_one_iff D.H.conj_mem t hle ⟨s, hsP⟩).mpr hsN)
      exact congrArg Subtype.val (h ⟨p, hp⟩ ⟨s, hsP⟩ hk)
    have htc : s * t = t * s := commute_of_mem_Rbar D.H.conj_mem (Nbar_le_Rbar hsN)
    rcases D.mem_Rder_or_mul_t hCE r' hr' with hp | hp
    · exact (hPc r' hp).symm
    · have h1 : (r' * t) * s = s * (r' * t) := (hPc _ hp).symm
      calc r' * s = r' * s * t * t⁻¹ := by group
        _ = r' * (s * t) * t⁻¹ := by rw [mul_assoc r' s t]
        _ = r' * (t * s) * t⁻¹ := by rw [htc]
        _ = r' * t * s * t⁻¹ := by group
        _ = s * (r' * t) * t⁻¹ := by rw [h1]
        _ = s * r' := by group

end CFSG.GF2Type.Smith1979.Case2
