module

public import CFSG.LargeExtraspecial.S13SevenD
public import CFSG.LargeExtraspecial.S13SevenC

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S13

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.S10

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {K : Subgroup S.O}

theorem mem_perp_of_span_pair {u w v : S.Qt} (hu : polar S.q u v = 0)
    (hw : polar S.q w v = 0) : v ∈ perp S (Submodule.span (ZMod 2) (Set.range ![u, w])) := by
  have hle : Submodule.span (ZMod 2) (Set.range ![u, w]) ≤
      LinearMap.ker (S.q.polarBilin.flip v) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · simpa [polarBilin_apply_apply] using hu
    · simpa [polarBilin_apply_apply] using hw
  intro x hx
  have := hle hx
  simpa [polarBilin_apply_apply] using this

namespace Hyp13

variable (hCE : CentralExtInput.{u}) (Y : Hyp13 S g K) {σ : S.O} (hσ : σ ∈ S.Lbar g)
  (hσE : σ ∉ Ebar S g K)
  (hpts : ∀ v ∈ Vt S g σ, v ≠ 0 → ∃ m : S.M, v = S.cl ((m : G) * g * S.z * ((m : G) * g)⁻¹) ∧
    σ ∈ S.Lbar ((m : G) * g) ∧ Vt S g σ ≤ S.clSub (S.QG ⊓ S.Qa ((m : G) * g)))
  (hVP : Vt S g σ ≤ S.clSub (S.QG ⊓ S.Qa g))
  {k : S.O} (hk : k ∈ K) (hk1 : k ≠ 1) {c : S.M}
  (hcU : S.cl ((c : G) * g * S.z * ((c : G) * g)⁻¹) ∉
    Vt S g σ ⊔ (Vt S g σ).map (k : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap)
  (ha : S.cl (g * S.z * g⁻¹) ∈ perp S (Fbar S ((c : G) * g) K))
include hCE Y hσ hσE hpts hVP hk hk1 hcU ha

theorem exists_x :
    ∃ x : S.M, S.cl ((x : G) * g * S.z * ((x : G) * g)⁻¹) ∈ Fbar S ((c : G) * g) K ∧
      S.cl ((x : G) * g * S.z * ((x : G) * g)⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa g) ∧
      S.cl ((x : G) * g * S.z * ((x : G) * g)⁻¹) ∉ Vt S g σ ∧
      Vt S g σ ⊓ perp S (Fbar S ((c : G) * g) K) ≤ S.clSub (S.QG ⊓ S.Qa ((x : G) * g)) ∧
      finrank (ZMod 2) (Vt S g σ) ≤
        finrank (ZMod 2) (Vt S g σ ⊓ perp S (Fbar S ((c : G) * g) K) :
          Submodule (ZMod 2) S.Qt) + 1 := by
  set V := Vt S g σ with hV
  set Fc := Fbar S ((c : G) * g) K with hFc
  have Yc : Hyp13 S ((c : G) * g) K := Y.mul rfl
  have hFcK : ∀ k' ∈ K, ∀ v ∈ Fc, (k' : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ Fc :=
    fun k' hk' v hv => apply_mem_Fbar_of_mem_K hk' hv
  have hperpF := Y.Fbar_le_perp hFcK ha
  have hperp : ∀ u ∈ Fbar S g K, ∀ v ∈ Fc, polar S.q u v = 0 := fun u hu v hv => by
    rw [QuadraticMap.polar_comm]; exact hperpF hu v hv
  have hFV := Y.Fbar_inf_Vt_eq_bot hk hk1 hcU
  have hne : Fc ≠ Fbar S g K := by
    intro h
    have : S.cl (g * S.z * g⁻¹) ∈ Fc ⊓ V :=
      Submodule.mem_inf.mpr ⟨h ▸ cl_mem_Fbar Y.H, cl_a_mem_Vt hσ⟩
    rw [hFV, Submodule.mem_bot] at this
    exact cl_conj_z_ne_zero S Y.haQ Y.hne this
  have h13 := timmesfeld_13_3 hCE Y (rfl : (c : G) * g = (c : G) * g) hperp hne
  obtain ⟨x', hx', hx'0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (fun h0 => by
    rw [h0, finrank_bot] at h13; omega : Fc ⊓ S.clSub (S.QG ⊓ S.Qa g) ≠ ⊥)
  obtain ⟨hx'F, hx'P⟩ := Submodule.mem_inf.mp hx'
  obtain ⟨mx, -, rfl⟩ := Yc.exists_eq_cl_of_mem_Fbar hx'F hx'0
  have hxc : (mx : G) * ((c : G) * g) = ((mx * c : S.M) : G) * g := by
    rw [Subgroup.coe_mul, mul_assoc]
  rw [hxc] at hx'F hx'P hx'0
  refine ⟨mx * c, hx'F, hx'P, ?_, ?_, ?_⟩
  · intro hxV
    have : _ ∈ Fc ⊓ V := Submodule.mem_inf.mpr ⟨hx'F, hxV⟩
    rw [hFV, Submodule.mem_bot] at this
    exact hx'0 this
  · intro e he
    obtain ⟨heV, hePerp⟩ := Submodule.mem_inf.mp he
    by_cases he0 : e = 0
    · rw [he0]; exact zero_mem _
    by_cases hea : e ∈ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹)
    · rcases mem_span_cl_iff.mp hea with h | h
      · exact absurd h he0
      · rw [h]
        have := cl_mem_clSub_symm Y.H (h₁ := 1) (h₂ := mx * c) (by simpa using hx'P)
        simpa using this
    · obtain ⟨me, rfl, -, -⟩ := hpts _ heV he0
      have Ye : Hyp13 S ((me : G) * g) K := Y.mul rfl
      have heD := Y.not_mem_Dbar hσ hσE hpts hk hk1 hcU heV hea
      have hperpeF := Ye.Fbar_le_perp hFcK hePerp
      have hperpe : ∀ u ∈ Fbar S ((me : G) * g) K, ∀ v ∈ Fc, polar S.q u v = 0 :=
        fun u hu v hv => by rw [QuadraticMap.polar_comm]; exact hperpeF hu v hv
      have hnee : Fc ≠ Fbar S ((me : G) * g) K := by
        intro h
        have : _ ∈ Fc ⊓ V := Submodule.mem_inf.mpr ⟨h ▸ cl_mem_Fbar Ye.H, heV⟩
        rw [hFV, Submodule.mem_bot] at this
        exact he0 this
      have hxe := Y.mem_clSub_of_not_mem_Dbar hCE hperp hne hx'F hx'P hx'0 (hVP heV) heD
        hperpe hnee
      exact cl_mem_clSub_symm Y.H hxe
  · set kx := (k : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (((mx * c : S.M) : G) * g * S.z *
      (((mx * c : S.M) : G) * g)⁻¹)) with hkx
    have hle : V ⊓ perp S ((ZMod 2) ∙ kx) ≤ V ⊓ perp S Fc := by
      intro v hv
      obtain ⟨hvV, hvk⟩ := Submodule.mem_inf.mp hv
      refine Submodule.mem_inf.mpr ⟨hvV, ?_⟩
      rw [hFc, ← Yc.span_pair_eq hx'F hx'0 hk hk1]
      exact mem_perp_of_span_pair (polar_eq_zero_of_mem_clSub Y.hne hx'P (hVP hvV))
        (hvk kx (Submodule.mem_span_singleton_self _))
    have h1 := finrank_inf_perp_ge V ((ZMod 2) ∙ kx)
    have h2 := Submodule.finrank_mono hle
    have h3 : finrank (ZMod 2) ((ZMod 2) ∙ kx) ≤ 1 := by
      by_cases h0 : kx = 0
      · rw [h0, Submodule.span_singleton_eq_bot.mpr rfl, finrank_bot]; omega
      · rw [finrank_span_singleton h0]
    omega

end Hyp13

end CFSG.LargeExtraspecial.S13
