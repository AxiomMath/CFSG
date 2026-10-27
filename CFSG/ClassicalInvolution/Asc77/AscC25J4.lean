module

public import CFSG.ClassicalInvolution.Asc77.AscC25J3

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25J

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
  CFSG.RankThreeCoreUniqueness CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.ClassicalInvolution.Asc77.C25V CFSG.ClassicalInvolution.Asc77.C25H
  CFSG.ClassicalInvolution.Asc77.C25X CFSG.ClassicalInvolution.Asc77.T3CII
  CFSG.ClassicalInvolution.Asc77.C25I CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Asc77.T3
open scoped MatrixGroups commutatorElement

section Omega5

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' a : G}


local notation "Lₐ" => crossIn K' a

theorem false_of_omega6_9 (h : T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t')
    (haS : a ∈ (S : Subgroup G)) (ha2 : a * a = 1) (hF' : IsFAut R' a) {e₀ : ℕ}
    (hzA : z ∈ Subgroup.centralizer ({a} : Set G))
    (ht'a : t' ∈ Subgroup.centralizer ({a} : Set G))
    (hzX : (⟨z, hzA⟩ : ↥(Subgroup.centralizer ({a} : Set G))) ∈ conjGen (crossIn K' a))
    {a₀ b₀ : ↥(conjGen (crossIn K' a)) ⧸ classicalInvolutionOddCore ↥(conjGen (crossIn K' a))}
    (T : TwinSect0 (oddQuotientFamily (restrictFamily (conjFamily (crossIn K' a))
          (conjGen (crossIn K' a))))
        (secImg (conjGen (crossIn K' a)) (crossIn K' a))
        (secImg (conjGen (crossIn K' a)) (conjSub (⟨t', ht'a⟩ :
          ↥(Subgroup.centralizer ({a} : Set G))) (crossIn K' a)))
        (QuotientGroup.mk ⟨⟨z, hzA⟩, hzX⟩) a₀ b₀)
    (hO6 : SectionOrthTypeU p e₀ (conjFamily (crossIn K' a)) (conjGen (crossIn K' a)) 6
      (!piSign p e₀)) : False := by
  classical
  obtain ⟨tg, n, hT, D, hC⟩ := hO6
  have hXn : (conjGen Lₐ).Normal := conjGen_normal _
  have hOodd : Odd (Nat.card (classicalInvolutionOddCore ↥(conjGen Lₐ))) :=
    CFSG.ComponentClassification.OddCore.odd_card _
  obtain ⟨τ, y, hτz, hτc, hτ2, hy, hτA, -⟩ := twinCent6U h.hp D hT hC T
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ↥(conjGen Lₐ), ζ = ⟨⟨z, hzA⟩, hzX⟩ := ⟨_, rfl⟩
  rw [← hζ] at hy hτc hτz
  have hzz : z * z = 1 := h.hz.sq
  have hζ2 : ζ * ζ = 1 := by
    rw [hζ]
    apply Subtype.ext
    apply Subtype.ext
    exact hzz
  obtain ⟨y₀, rfl⟩ := QuotientGroup.mk_surjective y
  have hmk : (QuotientGroup.mk (y₀ * ζ * y₀⁻¹) :
      ↥(conjGen Lₐ) ⧸ classicalInvolutionOddCore ↥(conjGen Lₐ)) = τ := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    exact hy
  have hcomm : (QuotientGroup.mk (y₀ * ζ * y₀⁻¹) :
      ↥(conjGen Lₐ) ⧸ classicalInvolutionOddCore ↥(conjGen Lₐ)) * QuotientGroup.mk ζ =
      QuotientGroup.mk ζ * QuotientGroup.mk (y₀ * ζ * y₀⁻¹) := by
    rw [hmk]
    exact hτc
  obtain ⟨g, hgc, hgm⟩ := C25G.exists_conj_comm_lift _ hOodd hζ2 y₀ hcomm
  obtain ⟨w, hw⟩ : ∃ w : ↥(conjGen Lₐ), w = g * ζ * g⁻¹ := ⟨_, rfl⟩
  rw [← hw] at hgc hgm
  have hwτ : (QuotientGroup.mk w :
      ↥(conjGen Lₐ) ⧸ classicalInvolutionOddCore ↥(conjGen Lₐ)) = τ := by
    rw [hgm]
    exact hmk
  let φ : ↥(conjGen Lₐ) →* G :=
    (Subgroup.centralizer ({a} : Set G)).subtype.comp (conjGen Lₐ).subtype
  have hφinj : Function.Injective φ :=
    (Subgroup.subtype_injective _).comp (Subgroup.subtype_injective _)
  have hφζ : φ ζ = z := by
    rw [hζ]
    rfl
  have hbC : φ w ∈ Subgroup.centralizer ({a} : Set G) :=
    (w : ↥(Subgroup.centralizer ({a} : Set G))).2
  have hba : φ w * a = a * φ w := Subgroup.mem_centralizer_singleton_iff.mp hbC
  have hbc : φ w * z = z * φ w := by
    have := congrArg φ hgc
    rw [map_mul, map_mul, hφζ] at this
    exact this
  have hbg : φ w = φ g * z * (φ g)⁻¹ := by
    rw [hw, map_mul, map_mul, map_inv, hφζ]
  have hbz : φ w ≠ z := by
    intro hbz
    apply hτz
    have hwζ : w = ζ := hφinj (hbz.trans hφζ.symm)
    rw [← hwτ, hwζ]
  have hbK' : conjSub (φ w) K' = K' := by
    rcases cz_conj_K' h hbc with h1 | h1
    · exfalso
      have hc''C : t' * φ w ∈ Subgroup.centralizer ({a} : Set G) :=
        Subgroup.mul_mem _ ht'a hbC
      have hc''K' : conjSub (t' * φ w) K' = K' := by
        rw [conjSub_mul, h1, conjSub_t'_K h]
      have hfix := conjSub_crossIn_eq (K := K') hc''C
        (mem_normalizer_iff_conjSub_eq.mpr hc''K')
      have e2 : (w : ↥(Subgroup.centralizer ({a} : Set G))) =
          (⟨t', ht'a⟩ : ↥(Subgroup.centralizer ({a} : Set G))) * ⟨t' * φ w, hc''C⟩ := by
        apply Subtype.ext
        change φ w = t' * (t' * φ w)
        calc φ w = (t' * t') * φ w := by rw [h.ht'2, one_mul]
          _ = t' * (t' * φ w) := by group
      have hbL : conjSub (w : ↥(Subgroup.centralizer ({a} : Set G))) Lₐ =
          conjSub (⟨t', ht'a⟩ : ↥(Subgroup.centralizer ({a} : Set G))) Lₐ := by
        rw [e2, conjSub_mul, hfix]
      have hLmem : Lₐ ∈ conjFamily Lₐ := ⟨1, conjSub_one _⟩
      have hLX : Lₐ ≤ conjGen Lₐ := le_conjGen hLmem
      have h2 := secAct_secImg (conjGen Lₐ) (w : ↥(Subgroup.centralizer ({a} : Set G))) hLX
      rw [hbL] at h2
      have hsecτ : conjSub τ (secImg (conjGen Lₐ) Lₐ) = secImg (conjGen Lₐ)
          (conjSub (⟨t', ht'a⟩ : ↥(Subgroup.centralizer ({a} : Set G))) Lₐ) := by
        rw [← h2, secAct_of_mem (conjGen Lₐ) (w : ↥(conjGen Lₐ)).2, ← hwτ]
        rfl
      exact T.ne (hτA.symm.trans hsecτ)
    · exact h1
  have hbN : φ w ∈ Subgroup.normalizer (K' : Set G) := mem_normalizer_iff_conjSub_eq.mpr hbK'
  exact false_of_conj_normalizer' h haS ha2 hF' hbg hbz hba hbN



theorem false_of_omega5_9 (h11 : C25_11 p f) (h : T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t')
    (haS : a ∈ (S : Subgroup G)) (ha2 : a * a = 1) (hFa : IsFAut R a)
    (hF' : IsFAut R' a) {e₀ : ℕ} (h3 : 3 ≤ p ^ e₀)
    (hzA : z ∈ Subgroup.centralizer ({a} : Set G))
    (ht'a : t' ∈ Subgroup.centralizer ({a} : Set G))
    (hzX : (⟨z, hzA⟩ : ↥(Subgroup.centralizer ({a} : Set G))) ∈ conjGen (crossIn K' a))
    {a₀ b₀ : ↥(conjGen (crossIn K' a)) ⧸ classicalInvolutionOddCore ↥(conjGen (crossIn K' a))}
    (T : TwinSect0 (oddQuotientFamily (restrictFamily (conjFamily (crossIn K' a))
          (conjGen (crossIn K' a))))
        (secImg (conjGen (crossIn K' a)) (crossIn K' a))
        (secImg (conjGen (crossIn K' a)) (conjSub (⟨t', ht'a⟩ :
          ↥(Subgroup.centralizer ({a} : Set G))) (crossIn K' a)))
        (QuotientGroup.mk ⟨⟨z, hzA⟩, hzX⟩) a₀ b₀)
    (hO5 : SectionOrthTypeU p e₀ (conjFamily (crossIn K' a)) (conjGen (crossIn K' a)) 5 true) :
    False := by
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
    typed5_data9 h ha2 ha1 h3 hzA ht'a hzX T hO5
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



end Omega5

end CFSG.ClassicalInvolution.Asc77.C25J
