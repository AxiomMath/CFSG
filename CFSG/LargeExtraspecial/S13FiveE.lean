module

public import CFSG.LargeExtraspecial.S13SevenC

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S13

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.S10

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {K : Subgroup S.O}

namespace Hyp13

theorem exists_x_row (hCE : CentralExtInput.{u}) (Y : Hyp13 S g K) {t : S.O}
    (X : Hyp10 S g t) (htE : t ∈ Ebar S g K) (hKR : K ≤ Rbar S g t)
    (hNK : ∀ x ∈ Nbar S g t, ∀ k ∈ K, k * x = x * k) {k : S.M}
    (hkN : S.ρ k ∈ normalizer (S.Lbar g : Set S.O))
    (hkA : S.ρ k * t * (S.ρ k)⁻¹ ∈ S.Lbar g ⊓ Nbar S g t) (hkt : S.ρ k * t * (S.ρ k)⁻¹ ≠ t)
    {e : S.M} (heP : S.cl ((e : G) * g * S.z * ((e : G) * g)⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa g))
    (heV : S.cl ((e : G) * g * S.z * ((e : G) * g)⁻¹) ∈ Vt S g t)
    (heF : S.cl ((e : G) * g * S.z * ((e : G) * g)⁻¹) ∉ Fbar S g K)
    (hte : t ∈ S.Lbar ((e : G) * g)) :
    ∃ x : S.M, S.cl ((x : G) * g * S.z * ((x : G) * g)⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa g) ∧
      S.cl ((x : G) * g * S.z * ((x : G) * g)⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa ((e : G) * g)) ∧
      S.cl ((x : G) * g * S.z * ((x : G) * g)⁻¹) ∉ Vt S g t := by
  set t' := S.ρ k * t * (S.ρ k)⁻¹ with ht'
  have X' : Hyp10 S g t' := X.conj' hkN rfl
  have ht'N : t' ∈ Nbar S g t := (Subgroup.mem_inf.mp hkA).2
  have hV' : Vt S g t' ≤ Wt S g t := Vt_le_Wt_symm (Vt_le_Wt_of_mem_Nbar X' ht'N)
  have hdim := finrank_Vt_inf_Vt_le hCE X X' ht'N hkt
  obtain ⟨c, ht'c, hcV⟩ : ∃ c : S.M, t' ∈ S.Lbar ((c : G) * g) ∧
      S.cl ((c : G) * g * S.z * ((c : G) * g)⁻¹) ∉ Vt S g t := by
    by_contra hcon
    push Not at hcon
    have hle : Vt S g t' ≤ Vt S g t := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨h, hh, rfl⟩
      exact hcon h hh
    rw [inf_eq_right.mpr hle, X'.h4] at hdim
    omega
  have Yc : Hyp13 S ((c : G) * g) K := Y.mul rfl
  have Ye : Hyp13 S ((e : G) * g) K := Y.mul rfl
  have ht'E : t' ∈ Ebar S ((c : G) * g) K := (mem_Ebar).mpr ⟨ht'c, hNK t' ht'N⟩
  have hF₂W : Fbar S ((c : G) * g) K ≤ Wt S g t :=
    (Yc.Fbar_le_Vt (g₀ := g) (h₀ := c) rfl ht'E).trans hV'
  have hFV : Fbar S g K ≤ Vt S g t := Y.Fbar_le_Vt (g₀ := g) (h₀ := 1) (by simp) htE
  have hteE : t ∈ Ebar S ((e : G) * g) K := (mem_Ebar).mpr ⟨hte, ((mem_Ebar).mp htE).2⟩
  have hFeV : Fbar S ((e : G) * g) K ≤ Vt S g t := Ye.Fbar_le_Vt (g₀ := g) (h₀ := e) rfl hteE
  have hcF : S.cl ((c : G) * g * S.z * ((c : G) * g)⁻¹) ∈ Fbar S ((c : G) * g) K :=
    cl_mem_Fbar Yc.H
  have hperp : ∀ u ∈ Fbar S g K, ∀ v ∈ Fbar S ((c : G) * g) K, polar S.q u v = 0 :=
    fun u hu v hv => (mem_Wt.mp (hF₂W hv)) u (hFV hu)
  have hne : Fbar S ((c : G) * g) K ≠ Fbar S g K := fun h => hcV (hFV (h ▸ hcF))
  obtain ⟨k₀, hk₀, hk₀1⟩ := Y.exists_K
  have hF₂0 : ∀ v ∈ Fbar S ((c : G) * g) K, v ∈ Vt S g t → v = 0 := by
    intro v hv hvV
    by_contra hv0
    apply hcV
    rw [← Yc.span_pair_eq hv hv0 hk₀ hk₀1] at hcF
    refine (Submodule.span_le.mpr ?_) hcF
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact hvV
    · exact apply_mem_Vt_of_mem_Rbar X.haQ (hKR hk₀) hvV
  have h13 := timmesfeld_13_3 hCE Y (rfl : (c : G) * g = (c : G) * g) hperp hne
  obtain ⟨x', hx', hx'0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (fun h0 => by
    rw [h0, finrank_bot] at h13; omega :
      Fbar S ((c : G) * g) K ⊓ S.clSub (S.QG ⊓ S.Qa g) ≠ ⊥)
  obtain ⟨hx'F, hx'P⟩ := Submodule.mem_inf.mp hx'
  obtain ⟨mx, -, rfl⟩ := Yc.exists_eq_cl_of_mem_Fbar hx'F hx'0
  have hxc : (mx : G) * ((c : G) * g) = ((mx * c : S.M) : G) * g := by
    rw [Subgroup.coe_mul, mul_assoc]
  rw [hxc] at hx'F hx'P hx'0
  refine ⟨mx * c, hx'P, ?_, fun h => hx'0 (hF₂0 _ hx'F h)⟩
  refine Y.mem_clSub_of_not_mem_Dbar hCE hperp hne hx'F hx'P hx'0 heP ?_ ?_ ?_
  · intro heD
    obtain ⟨f₀, hf₀, f₂, hf₂, hsum⟩ := Submodule.mem_sup.mp heD
    have hf₂V : f₂ ∈ Vt S g t := by
      have e1 : f₂ = S.cl ((e : G) * g * S.z * ((e : G) * g)⁻¹) - f₀ := by
        rw [← hsum]; abel
      rw [e1]
      exact sub_mem heV (hFV hf₀)
    have hf₂0 := hF₂0 f₂ hf₂ hf₂V
    rw [hf₂0, add_zero] at hsum
    exact heF (hsum ▸ hf₀)
  · exact fun u hu v hv => (mem_Wt.mp (hF₂W hv)) u (hFeV hu)
  · intro h
    exact hcV (hFeV (h ▸ cl_mem_Fbar Yc.H))

end Hyp13

end CFSG.LargeExtraspecial.S13
