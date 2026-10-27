module

public import CFSG.ClassicalInvolution.Q3.TL4AE286Move

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

section Cit3


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem aE286Elt_of_linkAEAt (hL : TightLargeHypR r n Y R S t) {J : Subgroup Y}
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)) (hbad : NoGNbr R t J)
    {J' : Subgroup Y} (hJ' : J' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hJJ' : J' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) J) (hAE : LinkAEAt R t) :
    AE286Elt t J J' := by
  have h := TightLargeHypR.typeRFam hL
  have hd := hL.datum
  have hΩ := hd.hypOmegaGen
  have ht := hd.isUniqueInvolution_core
  obtain ⟨u, hu⟩ := Sec6Gen.exists_uniqueInvolution hΩ hJ.1
  obtain ⟨g, hg'⟩ := hJ'.1
  have hg : conjSub g (tightCore R) = J' := hg'
  have hw' : IsUniqueInvolution J' (g * t * g⁻¹) := hg ▸ ht.conj g
  have he : g * t * g⁻¹ = t * u := hbad J' hJ' hJJ' u _ hu hw'
  have hJJ := Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hJ.1 hJ'.1 hJJ'
  have hM : conjSub g⁻¹ J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R) := by
    have h1 := omegaNbr_conj hΩ.conjInvariant hJJ g⁻¹
    rwa [← hg, conjSub_inv_conjSub] at h1
  obtain ⟨y', hy'3, hy't, ⟨T, hT, hy'T, x, hx, hxne⟩, P, hP, hy'P⟩ :=
    exists_moveY_of_linkAEAt hL hAE hM
  have hv : IsUniqueInvolution (conjSub g⁻¹ J) (g⁻¹ * u * g⁻¹⁻¹) := hu.conj g⁻¹
  have hvT : g⁻¹ * u * g⁻¹⁻¹ ∈ T := Q3CP.mem_of_isSylow2In_of_isUniqueInvolution hv hT
  have hy'v : y' * (g⁻¹ * u * g⁻¹⁻¹) = (g⁻¹ * u * g⁻¹⁻¹) * y' := by
    have h1 : y' * (g⁻¹ * u * g⁻¹⁻¹) * y'⁻¹ ∈ T :=
      (Subgroup.mem_normalizer_iff.mp hy'T _).mp hvT
    have hsq : y' * (g⁻¹ * u * g⁻¹⁻¹) * y'⁻¹ * (y' * (g⁻¹ * u * g⁻¹⁻¹) * y'⁻¹) = 1 := by
      calc y' * (g⁻¹ * u * g⁻¹⁻¹) * y'⁻¹ * (y' * (g⁻¹ * u * g⁻¹⁻¹) * y'⁻¹) =
          y' * ((g⁻¹ * u * g⁻¹⁻¹) * (g⁻¹ * u * g⁻¹⁻¹)) * y'⁻¹ := by group
        _ = 1 := by rw [hv.sq, mul_one, mul_inv_cancel]
    rcases hv.unique _ (hT.1 h1) hsq with h2 | h2
    · exfalso
      apply hv.ne_one
      calc g⁻¹ * u * g⁻¹⁻¹ = y'⁻¹ * (y' * (g⁻¹ * u * g⁻¹⁻¹) * y'⁻¹) * y' := by group
        _ = 1 := by rw [h2, mul_one, inv_mul_cancel]
    · calc y' * (g⁻¹ * u * g⁻¹⁻¹) = y' * (g⁻¹ * u * g⁻¹⁻¹) * y'⁻¹ * y' := by group
        _ = (g⁻¹ * u * g⁻¹⁻¹) * y' := by rw [h2]
  have hs : g⁻¹ * t * g = t * (g⁻¹ * u * g⁻¹⁻¹) := by
    have h1 : t = (g⁻¹ * t * g) * (g⁻¹ * u * g⁻¹⁻¹) := by
      calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
        _ = g⁻¹ * (t * u) * g := by rw [he]
        _ = (g⁻¹ * t * g) * (g⁻¹ * u * g⁻¹⁻¹) := by group
    calc g⁻¹ * t * g = (g⁻¹ * t * g) * (g⁻¹ * u * g⁻¹⁻¹) * (g⁻¹ * u * g⁻¹⁻¹) := by
          rw [mul_assoc (g⁻¹ * t * g), hv.sq, mul_one]
      _ = t * (g⁻¹ * u * g⁻¹⁻¹) := by rw [← h1]
  have hy'tc : y' * t = t * y' := Subgroup.mem_centralizer_singleton_iff.mp hy't
  have hy's : y' * (g⁻¹ * t * g) = (g⁻¹ * t * g) * y' := by
    rw [hs]
    calc y' * (t * (g⁻¹ * u * g⁻¹⁻¹)) = (y' * t) * (g⁻¹ * u * g⁻¹⁻¹) := by group
      _ = t * (y' * (g⁻¹ * u * g⁻¹⁻¹)) := by rw [hy'tc]; group
      _ = t * (g⁻¹ * u * g⁻¹⁻¹) * y' := by rw [hy'v]; group
  have hconjN : ∀ {H : Subgroup Y} {c : Y}, c ∈ Subgroup.normalizer (conjSub g⁻¹ H : Set Y) →
      g * c * g⁻¹ ∈ Subgroup.normalizer (H : Set Y) := by
    intro H c hc
    rw [mem_normalizer_iff_conjSub_eq] at hc ⊢
    rw [conjSub_mul, conjSub_mul, hc, conjSub_conjSub_inv]
  have hy'M : y' ∈ Subgroup.normalizer (conjSub g⁻¹ J : Set Y) :=
    h.tight _ hM.1 _ hv (Subgroup.mem_centralizer_singleton_iff.mpr hy'v)
  have hy'K : y' ∈ Subgroup.normalizer (conjSub g⁻¹ J' : Set Y) := by
    rw [← hg, conjSub_inv_conjSub]
    exact mem_normalizer_iff_conjSub_eq.mpr (conjSub_core_of_mem_centralizer hL hy't)
  have hy'T' : y' ∈ Subgroup.normalizer (conjSub g⁻¹ (conjSub g T) : Set Y) := by
    rwa [conjSub_inv_conjSub]
  refine ⟨g * y' * g⁻¹, ?_, ?_, hconjN hy'M, hconjN hy'K,
    ⟨conjSub g T, ?_, hconjN hy'T', g * x * g⁻¹, conj_mem_conjSub hx g, ?_⟩,
    conjSub g P, ?_, ?_⟩
  · have e : g * y' * g⁻¹ = (MulAut.conj g).toMonoidHom y' := rfl
    rw [e, ← MonoidHom.map_zpowers]
    exact hy'3.map _
  · rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * y' * g⁻¹ * t = g * (y' * (g⁻¹ * t * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * t * g) * y') * g⁻¹ := by rw [hy's]
      _ = t * (g * y' * g⁻¹) := by group
  · have h1 := hT.conj g
    rwa [conjSub_conjSub_inv] at h1
  · intro he'
    apply hxne
    calc y' * x * y'⁻¹ = g⁻¹ * ((g * y' * g⁻¹) * (g * x * g⁻¹) * (g * y' * g⁻¹)⁻¹) * g := by
          group
      _ = x := by rw [he']; group
  · have h1 := hP.conj g
    rwa [hg] at h1
  · intro p hp
    rw [mem_conjSub_iff] at hp
    have h1 := hy'P _ hp
    calc g * y' * g⁻¹ * p = g * (y' * (g⁻¹ * p * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * p * g) * y') * g⁻¹ := by rw [h1]
      _ = p * (g * y' * g⁻¹) := by group

theorem tightAE286ExistR_three (n : ℕ) : TightAE286ExistR 3 n := by
  intro Y _ _ R S t hL _ J hJ hbad J' hJ' hJJ' hAE
  exact aE286Elt_of_linkAEAt hL hJ hbad hJ' hJJ' hAE

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
