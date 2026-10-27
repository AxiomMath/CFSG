module

public import CFSG.ClassicalInvolution.Asc77.AscC25H1
public import CFSG.ClassicalInvolution.Asc77.AscC25H2
public import CFSG.ClassicalInvolution.Asc77.AscC25V10

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25I

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Asc77.C25V CFSG.ClassicalInvolution.Asc77.C25H
open scoped MatrixGroups commutatorElement

structure IsSwap {G : Type} [Group G] (K K' : Subgroup G) (z t₀ : G) : Prop where
  sq : t₀ * t₀ = 1
  comm : t₀ * z = z * t₀
  swapK : conjSub t₀ K = K'

section Main

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' t₀ : G}


theorem IsSwap.inv (hsw : IsSwap K K' z t₀) : t₀⁻¹ = t₀ := inv_eq_of_mul_eq_one_right hsw.sq

theorem IsSwap.swapK' (hsw : IsSwap K K' z t₀) : conjSub t₀ K' = K := by
  have h1 : conjSub (t₀ * t₀) K = K := by rw [hsw.sq, conjSub_one]
  rwa [conjSub_mul, hsw.swapK] at h1

theorem IsSwap.conj_mem_normalizer (h : T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t')
    (hsw : IsSwap K K' z t₀) {x : G} (hxz : x * z = z * x) (hxK : conjSub x K = K) :
    t₀ * x * t₀ ∈ Subgroup.normalizer (K : Set G) := by
  have hxK' : conjSub x K' = K' := (cz_fix_iff h hxz).mp hxK
  refine mem_normalizer_iff_conjSub_eq.mpr ?_
  rw [conjSub_mul, conjSub_mul, hsw.swapK, hxK', hsw.swapK']

theorem IsSwap.cover (h : T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t')
    (hsw : IsSwap K K' z t₀) {g : G} (hg : g * z = z * g) :
    conjSub g K = K ∨ conjSub (g * t₀) K = K := by
  rcases cz_conj_K h hg with h1 | h1
  · exact Or.inl h1
  · right
    rw [conjSub_mul, hsw.swapK]
    rcases cz_conj_K' h hg with h2 | h2
    · exact h2
    · exact absurd (h1.symm.trans ((cz_fix_iff h hg).mpr h2)) h.hs.hne

theorem triv_of_triv_swap (h : T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t')
    (hsw : IsSwap K K' z t₀) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f)) {y : G}
    (hy : y ∈ Triv hp hq e z t₀ hsw.sq) : y ∈ Triv hp hq e z t' h.ht'2 := by
  have htz : t' * z = z * t' := t'_comm_z h
  have hwz : (t₀ * t') * z = z * (t₀ * t') :=
    ((show Commute t₀ z from hsw.comm).mul_left (show Commute t' z from htz)).eq
  have hwK : conjSub (t₀ * t') K = K := by
    rw [conjSub_mul, conjSub_t'_K h, hsw.swapK']
  have hwN : t₀ * t' ∈ Subgroup.normalizer (K : Set G) := mem_normalizer_iff_conjSub_eq.mpr hwK
  have hct : t₀ * (t₀ * t') * t₀ ∈ Subgroup.normalizer (K : Set G) :=
    hsw.conj_mem_normalizer h hwz hwK
  have hy2 := triv_conj_of_normalizer hwN hwz hct hy
  obtain ⟨hN, hz, hN', hν, hν'⟩ := hy
  obtain ⟨-, -, hN2, -, hν2⟩ := hy2
  have e1 : t' * y * t' = t₀ * ((t₀ * t') * y * (t₀ * t')⁻¹) * t₀ := by
    rw [mul_inv_rev, h.ht'inv, hsw.inv]
    calc t' * y * t' = (t₀ * t₀) * t' * y * t' * (t₀ * t₀) := by rw [hsw.sq]; group
      _ = t₀ * (t₀ * t' * y * (t' * t₀)) * t₀ := by group
  refine ⟨hN, hz, ?_, hν, ?_⟩
  · rw [e1]
    exact hN2
  · rw [e1]
    exact hν2

end Main

end CFSG.ClassicalInvolution.Asc77.C25I
