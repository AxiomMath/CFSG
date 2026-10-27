module

public import CFSG.ClassicalInvolution.Asc77.AscC25H9
public import CFSG.ClassicalInvolution.Asc77.AscC25H8
public import CFSG.ClassicalInvolution.Asc77.AscC25V26
public import CFSG.ClassicalInvolution.Asc77.AscC25V36

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25H

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Asc77.C25V
open scoped MatrixGroups commutatorElement

section Main

variable {p f : ℕ} [Fact p.Prime]


theorem false_of_ff_nstar (h11 : C25_11 p f) (hN : NStar p f) {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {S : Sylow 2 G}
    {R R' : Subgroup G} {z t u₁ u₂ : G} (hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂) {a : G}
    (haS : a ∈ (S : Subgroup G)) (ha2 : a * a = 1) (hFa : IsFAut R a) (hFa' : IsFAut R' a) :
    False := by
  classical
  by_cases hZ : z ∈ zStarOf (Subgroup.centralizer ({a} : Set G))
  · exact false_of_zStar_ff h11 hyp haS ha2 hFa hFa' hZ
  obtain ⟨t', g, h, hg, hnf, hat⟩ := exists_comm_swap_of_ff h11 hyp haS ha2 hFa hFa'
  have hp : p ≠ 2 := h.hp
  have hq : 5 ≤ p ^ f := h.hs.stand.five
  obtain ⟨e⟩ := h.hΩ.nonempty_equiv_sl2 h.hK
  have hfix := fix_of_isFAut h haS hFa'
  have haK : a ∈ Subgroup.normalizer (K : Set G) :=
    mem_normalizer_iff_conjSub_eq.mpr hfix.2.2.1
  have hσ : fieldChar hp hq e ⟨a, haK⟩ ≠ 1 :=
    fieldChar_ne_one_of_isFAut hp hq e h.hRsyl.1 h.hqR h.hzR hFa ha2 haK
  let _ : CommGroup (GaloisField p f ≃+* GaloisField p f) := ringAutCommGroup _
  set C : Subgroup G := Subgroup.centralizer ({z} : Set G) with hC
  have hmemC : ∀ g : G, g ∈ C ↔ g * z = z * g := fun g => by
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
  have ht'z : t' * z = z * t' := t'_comm_z h
  have ht'C : t' ∈ C := (hmemC t').mpr ht'z
  set N : Subgroup G := C ⊓ Subgroup.normalizer (K : Set G) with hN'
  have hconjN : ∀ m ∈ N, t' * m * t' ∈ N := by
    intro m hm
    have hmz : m * z = z * m := (hmemC m).mp hm.1
    have hmK : conjSub m K = K := mem_normalizer_iff_conjSub_eq.mp hm.2
    have hmK' : conjSub m K' = K' := (cz_fix_iff h hmz).mp hmK
    have hK2 : conjSub (t' * m * t') K = K := by
      rw [conjSub_mul, conjSub_mul, conjSub_t'_K h, hmK', conjSub_t'_K' h]
    exact ⟨C.mul_mem (C.mul_mem ht'C hm.1) ht'C, mem_normalizer_iff_conjSub_eq.mpr hK2⟩
  have hcov : ∀ c ∈ C, c ∈ N ∨ c * t' ∈ N := by
    intro c hc
    have hcz : c * z = z * c := (hmemC c).mp hc
    rcases cz_cover h hcz with h1 | h1
    · exact Or.inl ⟨hc, mem_normalizer_iff_conjSub_eq.mpr h1⟩
    · exact Or.inr ⟨C.mul_mem hc ht'C, mem_normalizer_iff_conjSub_eq.mpr h1⟩
  let χ : N →* (GaloisField p f ≃+* GaloisField p f) :=
    (fieldChar hp hq e).comp (Subgroup.inclusion inf_le_right)
  let δ : N →* ℤˣ := (diagChar hp hq e).comp (Subgroup.inclusion inf_le_right)
  have haz : a * z = z * a := hyp.hzS a haS
  have haC : a ∈ C := (hmemC a).mpr haz
  have haN : a ∈ N := ⟨haC, haK⟩
  have hδa : diagChar hp hq e ⟨a, haK⟩ = 1 := diagChar_eq_one_of_involution hp hq e haK ha2 hσ
  obtain ⟨y, hyR', hy4, hya⟩ := exists_order_four_of_isFAut hFa'
  have hy4' : y ^ 4 = 1 := by rw [← hy4]; exact pow_orderOf_eq_one y
  have hyz : y * z = z * y := comm_z_of_mem h.hzR' hyR'
  have hnc4 : ∀ g : G, (g * z * g⁻¹) * y = y * (g * z * g⁻¹) → g * z * g⁻¹ = z := by
    intro g hg
    have := eq_conj_z_of_commute_order_four h (c := 1) (g := g) (y₀ := y)
      (by rw [conjSub_one]; exact h.hyp.hR'.2.1 hyR') hy4 hg
    simpa using this
  have hT : ∀ (B : Type) [CommGroup B] (π : ↥C →* B), π ⟨a, haN.1⟩ = 1 :=
    fun B _ π => hom_centralizer_apply_eq_one (exists_noncomm_of_swap h) ha2 haz hya hyz hy4' hnc4 π
  obtain ⟨⟨n, hnN⟩, hn1, hn2⟩ :=
    exists_swapDiff_eq_of_hT h.ht'2 hconjN inf_le_left hcov χ δ haN hT
  have hnK : n ∈ Subgroup.normalizer (K : Set G) := hnN.2
  have hnz : n * z = z * n := (hmemC n).mp hnN.1
  have hn'K : t' * n * t' ∈ Subgroup.normalizer (K : Set G) := (hconjN n hnN).2
  have hδ : diagGamma (nuG hp hq e n) = diagGamma (nuG hp hq e (t' * n * t')) := by
    rw [swapDiff_apply h.ht'2 hconjN δ n hnN] at hn1
    have h1 : diagChar hp hq e ⟨n, hnK⟩ * (diagChar hp hq e ⟨t' * n * t', hn'K⟩)⁻¹ =
        diagChar hp hq e ⟨a, haK⟩ := hn1
    rw [hδa] at h1
    rw [← diagChar_eq_diagGamma_nuG hp hq e hnK, ← diagChar_eq_diagGamma_nuG hp hq e hn'K]
    exact mul_inv_eq_one.mp h1
  have hχ : SemidirectProduct.rightHom (nuG hp hq e n) =
      SemidirectProduct.rightHom (nuG hp hq e (t' * n * t')) *
        SemidirectProduct.rightHom (nuG hp hq e a) := by
    rw [swapDiff_apply h.ht'2 hconjN χ n hnN] at hn2
    have h1 : fieldChar hp hq e ⟨n, hnK⟩ * (fieldChar hp hq e ⟨t' * n * t', hn'K⟩)⁻¹ =
        fieldChar hp hq e ⟨a, haK⟩ := hn2
    rw [mul_inv_eq_iff_eq_mul] at h1
    rw [← fieldChar_eq_rightHom_nuG hp hq e hnK, ← fieldChar_eq_rightHom_nuG hp hq e hn'K,
      ← fieldChar_eq_rightHom_nuG hp hq e haK, h1, mul_comm]
  have hδa' : diagGamma (nuG hp hq e a) = 1 := by
    rw [← diagChar_eq_diagGamma_nuG hp hq e haK]
    exact hδa
  have hres := exists_conj_azt h11 h hp hq e ha2 haz hat haK hnK hnz hn'K hδa' hδ hχ ⟨g, hg⟩
  have hNs := hN G Ω K K' W S R R' z t u₁ u₂ hyp a haS ha2 hFa hFa' hZ t' h ⟨g, hg⟩ hnf hat
  rcases hres with h1 | h1
  · exact hNs.2 h1
  · exact hNs.1 h1

theorem c25_16inv_of_nstar (h11 : C25_11 p f) (hmix : Mix25 p f) (hN : NStar p f) :
    T7U.C25_16inv p f := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp a haS ha2 hF'
  rcases hmix G Ω K K' W S R R' z t u₁ u₂ hyp a haS ha2 hF' with hin | ⟨r, hrR, ha'2, hFa'⟩
  · obtain ⟨e, heS, he2, hFe, hFe'⟩ := exists_ff_of_inner h11 hyp haS ha2 hF' hin
    exact (false_of_ff_nstar h11 hN hyp heS he2 hFe hFe').elim
  · obtain ⟨t₀, h₀⟩ := T7T.exists_hyp25T hyp
    have ha'S : a * r ∈ (S : Subgroup G) := S.mul_mem haS (h₀.hRS hrR)
    have hF'a' : IsFAut R' (a * r) :=
      T7U.isFAut_mul_of_centralizes (fun x hx => h₀.hcomm r hrR x hx) hF'
    exact (false_of_ff_nstar h11 hN hyp ha'S ha'2 hFa' hF'a').elim

theorem c25_16invEven_of_nstar (h11 : C25_11 p f) (hN : NStar p f) :
    Even f → T7U.C25_16inv p f :=
  fun _ => c25_16inv_of_nstar h11 mix25_all hN

end Main

end CFSG.ClassicalInvolution.Asc77.C25H
