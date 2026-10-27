module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S25Nu4
public import CFSG.ClassicalInvolution.Asc77.AscC25V36
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S25End
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S25Nu2

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Hat2A7S

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Hat2A7
  CFSG.ClassicalInvolution.Hat2A7S.Eps
open CFSG.ClassicalInvolution.Hat2A7M.Asc77.T7F2 (Hyp25T)
open scoped commutatorElement

section Basic

variable {G : Type} [Group G]

theorem Eps.exists_order_four_of_isFAut {R' : Subgroup G} {a : G} (hF : IsFAut R' a) :
    ∃ y₀ ∈ R', orderOf y₀ = 4 ∧ y₀ * a = a * y₀ := by
  obtain ⟨-, -, Q, -, hQ, hQuat, -, -⟩ := hF
  obtain ⟨k, hk, ⟨eQ⟩⟩ := hQuat
  have : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩
  refine ⟨((eQ.symm (QuaternionGroup.xa 0) : Q) : G), (hQ.1 (eQ.symm _).2).1, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact QuaternionGroup.orderOf_xa 0
  · exact Subgroup.mem_centralizer_singleton_iff.mp (hQ.1 (eQ.symm _).2).2

end Basic

section Main

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)}
  {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ t' t₀ : G}


theorem Eps.c25_11_mirror (h11 : A7C25_11) : Hat2A7M.Asc77.C25_11 :=
  fun G _ _ _ Ω K K' W S R R' z t u₁ u₂ h => h11 G Ω K K' W S R R' z t u₁ u₂ (Hyp25A7.of_mirror h)

theorem Eps.nc4_conj_z (h : Hyp25T Ω K K' W S R R' z t u₁ u₂ t') {c g y₀ : G}
    (hy₀ : y₀ ∈ conjSub c K') (hy4 : orderOf y₀ = 4)
    (hcomm : (g * z * g⁻¹) * y₀ = y₀ * (g * z * g⁻¹)) : g * z * g⁻¹ = c * z * c⁻¹ := by
  by_contra hne
  have hJ : conjSub c K' ∈ Ω := h.hΩ.conjInvariant c K' h.hK'
  have ha : IsUniqueInvolution (conjSub c K') (c * z * c⁻¹) := h.hz'.conj c
  exact Hat2A7M.Asc77.T7ER.not_commute_of_conj h.hs h.hyp.hW h.hyp.hE4 hJ ha hne hy₀ hy4 hcomm

theorem a7_false_of_swap_data (h11 : A7C25_11) (h : Hyp25T Ω K K' W S R R' z t u₁ u₂ t')
    {a : G} (haS : a ∈ (S : Subgroup G)) (ha2 : a * a = 1) (hFa : IsFAut R a)
    (hF' : IsFAut R' a) (_hat : a * t' = t' * a) {t₀ y₁ c₁ : G}
    (hsw : C25I.IsSwap K K' z t₀) (hat₀ : a * t₀ = t₀ * a)
    (hcz : ∃ c₀, c₀ * a = a * c₀ ∧ c₀ * z * c₀⁻¹ = t₀) (hc₁a : c₁ * a = a * c₁)
    (hy₁K : y₁ ∈ conjSub c₁ K') (hy₁4 : orderOf y₁ = 4) (hy₁a : y₁ * a = a * y₁)
    (hy₁x : y₁ * (z * t₀) = (z * t₀) * y₁)
    (hlast : ∀ c, c * a = a * c → a * (z * t₀) ≠ c * z * c⁻¹) : False := by
  classical
  have hw : A7Witness K := by
    obtain ⟨u, hu⟩ := h.hs.stand.classical K h.hK
    exact hu.witness
  obtain ⟨ρ, zE, cov, -⟩ := exists_cover_of_witness hw
  have hfix := N.fix_of_isFAut h haS hF'
  have haK : a ∈ Subgroup.normalizer (K : Set G) :=
    mem_normalizer_iff_conjSub_eq.mpr hfix.2.2.1
  have hεa : epsG cov a = -1 := epsG_eq_neg_one_of_isFAut cov h.hRsyl h.hz haK ha2 hFa
  have ha1 : a ≠ 1 := by
    intro ha
    rw [ha, epsG_one] at hεa
    exact absurd hεa (by decide)
  have haz : a * z = z * a := h.hyp.hzS a haS
  obtain ⟨c₀, hcac, hcz'⟩ := hcz
  set C : Subgroup G := Subgroup.centralizer ({z} : Set G) with hC
  have hmemC : ∀ g : G, g ∈ C ↔ g * z = z * g := fun g => by
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
  have ht₀C : t₀ ∈ C := (hmemC t₀).mpr hsw.comm
  set N' : Subgroup G := C ⊓ Subgroup.normalizer (K : Set G) with hN'
  have hconjN : ∀ m ∈ N', t₀ * m * t₀ ∈ N' := by
    intro m hm
    have hmz : m * z = z * m := (hmemC m).mp hm.1
    have hmK : conjSub m K = K := mem_normalizer_iff_conjSub_eq.mp hm.2
    exact ⟨C.mul_mem (C.mul_mem ht₀C hm.1) ht₀C, swap_conj_mem_normalizer h hsw hmz hmK⟩
  have hcov : ∀ c ∈ C, c ∈ N' ∨ c * t₀ ∈ N' := by
    intro c hc
    have hcz : c * z = z * c := (hmemC c).mp hc
    rcases swap_cover h hsw hcz with h1 | h1
    · exact Or.inl ⟨hc, mem_normalizer_iff_conjSub_eq.mpr h1⟩
    · exact Or.inr ⟨C.mul_mem hc ht₀C, mem_normalizer_iff_conjSub_eq.mpr h1⟩
  let χ : N' →* ℤˣ := (epsK cov).comp (Subgroup.inclusion inf_le_right)
  let δ : N' →* ℤˣ := 1
  have haC : a ∈ C := (hmemC a).mpr haz
  have haN : a ∈ N' := ⟨haC, haK⟩
  obtain ⟨y, hyR', hy4, hya⟩ := Eps.exists_order_four_of_isFAut hF'
  have hy4' : y ^ 4 = 1 := by rw [← hy4]; exact pow_orderOf_eq_one y
  have hyz : y * z = z * y := C25V.comm_z_of_mem h.hzR' hyR'
  have hnc4 : ∀ g : G, (g * z * g⁻¹) * y = y * (g * z * g⁻¹) → g * z * g⁻¹ = z := by
    intro g hg
    have := Eps.nc4_conj_z h (c := 1) (g := g) (y₀ := y)
      (by rw [conjSub_one]; exact h.hyp.hR'.2.1 hyR') hy4 hg
    simpa using this
  have hT : ∀ (B : Type) [CommGroup B] (π : ↥C →* B), π ⟨a, haN.1⟩ = 1 :=
    fun B _ π => C25V.hom_centralizer_apply_eq_one (N.exists_noncomm_of_swap h) ha2 haz hya hyz
      hy4' hnc4 π
  obtain ⟨⟨n, hnN⟩, -, hn2⟩ :=
    C25V.exists_swapDiff_eq_of_hT hsw.sq hconjN inf_le_left hcov χ δ haN hT
  have hnK : n ∈ Subgroup.normalizer (K : Set G) := hnN.2
  have hnz : n * z = z * n := (hmemC n).mp hnN.1
  have hn'K : t₀ * n * t₀ ∈ Subgroup.normalizer (K : Set G) := (hconjN n hnN).2
  have hε : epsG cov n = epsG cov (t₀ * n * t₀) * epsG cov a := by
    rw [C25V.swapDiff_apply hsw.sq hconjN χ n hnN] at hn2
    have h1 : epsK cov ⟨n, hnK⟩ * (epsK cov ⟨t₀ * n * t₀, hn'K⟩)⁻¹ = epsK cov ⟨a, haK⟩ := hn2
    rw [mul_inv_eq_iff_eq_mul] at h1
    rw [epsG_of_mem cov hnK, epsG_of_mem cov hn'K, epsG_of_mem cov haK]
    exact h1.trans (mul_comm _ _)
  have hres := exists_conj_azt' (Eps.c25_11_mirror h11) h cov hsw ha2 haz hat₀ haK hnK hnz hn'K hε
    ⟨c₀, hcz'⟩
  rcases hres with ⟨g, hg⟩ | ⟨g, hg⟩
  ·
    have hcm : Commute y₁ (a * (z * t₀)) :=
      (show Commute y₁ a from hy₁a).mul_right (show Commute y₁ (z * t₀) from hy₁x)
    have hcomm : (g * z * g⁻¹) * y₁ = y₁ * (g * z * g⁻¹) := by
      rw [hg, mul_assoc a z t₀]
      exact hcm.eq.symm
    have h1 := Eps.nc4_conj_z h hy₁K hy₁4 hcomm
    exact hlast c₁ hc₁a (by rw [← mul_assoc, ← hg]; exact h1)
  ·
    have e1 : c₀⁻¹ * (a * c₀) = a := by rw [← hcac]; group
    have hconj : (c₀⁻¹ * g) * z * (c₀⁻¹ * g)⁻¹ = a * z := by
      calc (c₀⁻¹ * g) * z * (c₀⁻¹ * g)⁻¹ = c₀⁻¹ * (g * z * g⁻¹) * c₀ := by group
        _ = c₀⁻¹ * (a * t₀) * c₀ := by rw [hg]
        _ = c₀⁻¹ * (a * (c₀ * z * c₀⁻¹)) * c₀ := by rw [hcz']
        _ = (c₀⁻¹ * (a * c₀)) * z * (c₀⁻¹ * c₀) := by group
        _ = a * z := by rw [e1, inv_mul_cancel, mul_one]
    have hcm : Commute y (a * z) :=
      (show Commute y a from hya).mul_right (show Commute y z from hyz)
    have h2 := hnc4 (c₀⁻¹ * g) (by rw [hconj]; exact hcm.eq.symm)
    rw [hconj] at h2
    exact ha1 (mul_eq_right.mp h2)

end Main

end CFSG.ClassicalInvolution.Hat2A7S
