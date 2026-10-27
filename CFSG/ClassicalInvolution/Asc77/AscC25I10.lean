module

public import CFSG.ClassicalInvolution.Asc77.AscC25I2
public import CFSG.ClassicalInvolution.Asc77.AscC25I3
public import CFSG.ClassicalInvolution.Asc77.AscC25I9
public import CFSG.ClassicalInvolution.Asc77.AscC25G5
public import CFSG.ClassicalInvolution.Asc77.AscC25V48

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25I

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
  CFSG.RankThreeCoreUniqueness CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.ClassicalInvolution.Asc77.C25V CFSG.ClassicalInvolution.Asc77.C25H
open CFSG.ClassicalInvolution.Asc77.T3
open scoped MatrixGroups commutatorElement

section Omega5

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' a : G}


theorem false_of_omega5 (h11 : C25_11 p f) (h : T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t')
    (h9 : p ^ f ≠ 9) (haS : a ∈ (S : Subgroup G)) (ha2 : a * a = 1) (hFa : IsFAut R a)
    (hF' : IsFAut R' a) (hat : a * t' = t' * a) {e₀ : ℕ} (h5 : 5 ≤ p ^ e₀)
    (hzA : z ∈ Subgroup.centralizer ({a} : Set G))
    (hL : IsClassicalMember p e₀ (perfectCoreIn K' a) ⟨z, hzA⟩)
    (hO5 : SectionOrthType p e₀ (conjFamily (perfectCoreIn K' a))
      (conjGen (perfectCoreIn K' a)) 5 true) : False := by
  classical
  have hp : p ≠ 2 := h.hp
  have hq : 5 ≤ p ^ f := h.hs.stand.five
  obtain ⟨e⟩ := h.hΩ.nonempty_equiv_sl2 h.hK
  have hfix := fix_of_isFAut h haS hF'
  have haK : a ∈ Subgroup.normalizer (K : Set G) :=
    mem_normalizer_iff_conjSub_eq.mpr hfix.2.2.1
  have hσ : fieldChar hp hq e ⟨a, haK⟩ ≠ 1 :=
    fieldChar_ne_one_of_isFAut hp hq e h.hRsyl.1 h.hqR h.hzR hFa ha2 haK
  have ha1 : a ≠ 1 := by
    intro ha
    apply hσ
    have : (⟨a, haK⟩ : Subgroup.normalizer (K : Set G)) = 1 := Subtype.ext ha
    rw [this, map_one]
  obtain ⟨t₀, y₁, c₁, hsw, hat₀, ⟨c₀, hcac, hcz⟩, hc₁a, hy₁K, hy₁4, hy₁a, hy₁x, hlast⟩ :=
    typed5_data h h9 haS ha2 ha1 hF' hat h5 hzA hL hO5
  let _ : CommGroup (GaloisField p f ≃+* GaloisField p f) := ringAutCommGroup _
  set C : Subgroup G := Subgroup.centralizer ({z} : Set G) with hC
  have hmemC : ∀ g : G, g ∈ C ↔ g * z = z * g := fun g => by
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
  have ht₀C : t₀ ∈ C := (hmemC t₀).mpr hsw.comm
  set N : Subgroup G := C ⊓ Subgroup.normalizer (K : Set G) with hN'
  have hconjN : ∀ m ∈ N, t₀ * m * t₀ ∈ N := by
    intro m hm
    have hmz : m * z = z * m := (hmemC m).mp hm.1
    have hmK : conjSub m K = K := mem_normalizer_iff_conjSub_eq.mp hm.2
    exact ⟨C.mul_mem (C.mul_mem ht₀C hm.1) ht₀C, hsw.conj_mem_normalizer h hmz hmK⟩
  have hcov : ∀ c ∈ C, c ∈ N ∨ c * t₀ ∈ N := by
    intro c hc
    have hcz : c * z = z * c := (hmemC c).mp hc
    rcases hsw.cover h hcz with h1 | h1
    · exact Or.inl ⟨hc, mem_normalizer_iff_conjSub_eq.mpr h1⟩
    · exact Or.inr ⟨C.mul_mem hc ht₀C, mem_normalizer_iff_conjSub_eq.mpr h1⟩
  let χ : N →* (GaloisField p f ≃+* GaloisField p f) :=
    (fieldChar hp hq e).comp (Subgroup.inclusion inf_le_right)
  let δ : N →* ℤˣ := (diagChar hp hq e).comp (Subgroup.inclusion inf_le_right)
  have haz : a * z = z * a := h.hyp.hzS a haS
  have haC : a ∈ C := (hmemC a).mpr haz
  have haN : a ∈ N := ⟨haC, haK⟩
  have hδa : diagChar hp hq e ⟨a, haK⟩ = 1 := diagChar_eq_one_of_involution hp hq e haK ha2 hσ
  obtain ⟨y, hyR', hy4, hya⟩ := exists_order_four_of_isFAut hF'
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
    exists_swapDiff_eq_of_hT hsw.sq hconjN inf_le_left hcov χ δ haN hT
  have hnK : n ∈ Subgroup.normalizer (K : Set G) := hnN.2
  have hnz : n * z = z * n := (hmemC n).mp hnN.1
  have hn'K : t₀ * n * t₀ ∈ Subgroup.normalizer (K : Set G) := (hconjN n hnN).2
  have hδ : diagGamma (nuG hp hq e n) = diagGamma (nuG hp hq e (t₀ * n * t₀)) := by
    rw [swapDiff_apply hsw.sq hconjN δ n hnN] at hn1
    have h1 : diagChar hp hq e ⟨n, hnK⟩ * (diagChar hp hq e ⟨t₀ * n * t₀, hn'K⟩)⁻¹ =
        diagChar hp hq e ⟨a, haK⟩ := hn1
    rw [hδa] at h1
    rw [← diagChar_eq_diagGamma_nuG hp hq e hnK, ← diagChar_eq_diagGamma_nuG hp hq e hn'K]
    exact mul_inv_eq_one.mp h1
  have hχ : SemidirectProduct.rightHom (nuG hp hq e n) =
      SemidirectProduct.rightHom (nuG hp hq e (t₀ * n * t₀)) *
        SemidirectProduct.rightHom (nuG hp hq e a) := by
    rw [swapDiff_apply hsw.sq hconjN χ n hnN] at hn2
    have h1 : fieldChar hp hq e ⟨n, hnK⟩ * (fieldChar hp hq e ⟨t₀ * n * t₀, hn'K⟩)⁻¹ =
        fieldChar hp hq e ⟨a, haK⟩ := hn2
    rw [mul_inv_eq_iff_eq_mul] at h1
    rw [← fieldChar_eq_rightHom_nuG hp hq e hnK, ← fieldChar_eq_rightHom_nuG hp hq e hn'K,
      ← fieldChar_eq_rightHom_nuG hp hq e haK, h1, mul_comm]
  have hδa' : diagGamma (nuG hp hq e a) = 1 := by
    rw [← diagChar_eq_diagGamma_nuG hp hq e haK]
    exact hδa
  have hres := exists_conj_azt' h11 h hsw hp hq e ha2 haz hat₀ haK hnK hnz hn'K hδa' hδ hχ
    ⟨c₀, hcz⟩
  rcases hres with ⟨g, hg⟩ | ⟨g, hg⟩
  ·
    have hcm : Commute y₁ (a * (z * t₀)) :=
      (show Commute y₁ a from hy₁a).mul_right (show Commute y₁ (z * t₀) from hy₁x)
    have hcomm : (g * z * g⁻¹) * y₁ = y₁ * (g * z * g⁻¹) := by
      rw [hg, mul_assoc a z t₀]
      exact hcm.eq.symm
    have h1 := eq_conj_z_of_commute_order_four h hy₁K hy₁4 hcomm
    exact hlast c₁ hc₁a (by rw [← mul_assoc, ← hg]; exact h1)
  ·
    have e1 : c₀⁻¹ * (a * c₀) = a := by rw [← hcac]; group
    have hconj : (c₀⁻¹ * g) * z * (c₀⁻¹ * g)⁻¹ = a * z := by
      calc (c₀⁻¹ * g) * z * (c₀⁻¹ * g)⁻¹ = c₀⁻¹ * (g * z * g⁻¹) * c₀ := by group
        _ = c₀⁻¹ * (a * t₀) * c₀ := by rw [hg]
        _ = c₀⁻¹ * (a * (c₀ * z * c₀⁻¹)) * c₀ := by rw [hcz]
        _ = (c₀⁻¹ * (a * c₀)) * z * (c₀⁻¹ * c₀) := by group
        _ = a * z := by rw [e1, inv_mul_cancel, mul_one]
    have hcm : Commute y (a * z) :=
      (show Commute y a from hya).mul_right (show Commute y z from hyz)
    have h2 := hnc4 (c₀⁻¹ * g) (by rw [hconj]; exact hcm.eq.symm)
    rw [hconj] at h2
    exact ha1 (mul_eq_right.mp h2)

theorem false_of_ff_typed (h11 : C25_11 p f) (h9 : p ^ f ≠ 9)
    (hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂)
    (haS : a ∈ (S : Subgroup G)) (ha2 : a * a = 1) (hFa : IsFAut R a) (hFa' : IsFAut R' a) :
    False := by
  classical
  by_cases hZ : z ∈ zStarOf (Subgroup.centralizer ({a} : Set G))
  · exact false_of_zStar_ff h11 hyp haS ha2 hFa hFa' hZ
  obtain ⟨t', g, h, hg, hnf, hat⟩ := exists_comm_swap_of_ff h11 hyp haS ha2 hFa hFa'
  obtain ⟨e₀, hfe, h5, hzA, hL, hcases⟩ := fs_typed h h9 haS ha2 hFa' hat
  rcases hcases with hz | h5' | h6'
  · exact hZ hz
  · exact false_of_omega5 h11 h h9 haS ha2 hFa hFa' hat h5 hzA hL h5'
  · exact C25G.false_of_omega6 h h9 haS ha2 hFa' hat h5 hzA hL h6'

end Omega5

section Main

variable {p f : ℕ} [Fact p.Prime]


theorem nstar_of_ne_nine (h11 : C25_11 p f) (h9 : p ^ f ≠ 9) : NStar p f := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp a haS ha2 hFa hFa' _ t' _ _ _ _
  exact (false_of_ff_typed h11 h9 hyp haS ha2 hFa hFa').elim

theorem nstar_of_nine (h11 : C25_11 p f) (hN9 : p ^ f = 9 → NStar p f) : NStar p f := by
  by_cases h9 : p ^ f = 9
  · exact hN9 h9
  · exact nstar_of_ne_nine h11 h9

theorem c25_16invEven_typed (h11 : C25_11 p f) (hN9 : p ^ f = 9 → NStar p f) :
    Even f → T7U.C25_16inv p f :=
  c25_16invEven_of_nstar h11 (nstar_of_nine h11 hN9)

theorem c25_16invEven_typed_of_diag25 (h11 : C25_11 p f) (hD9 : p ^ f = 9 → DIAG25 p f) :
    Even f → T7U.C25_16inv p f := by
  intro hf
  by_cases h9 : p ^ f = 9
  · exact c25_16invEven_of_diag25 h11 (fun _ => C25G.g1Omega6_proved) (fun _ => hD9 h9) hf
  · exact c25_16invEven_of_nstar h11 (nstar_of_ne_nine h11 h9) hf

end Main

end CFSG.ClassicalInvolution.Asc77.C25I
