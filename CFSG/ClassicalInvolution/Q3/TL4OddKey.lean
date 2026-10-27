module

public import CFSG.ClassicalInvolution.Q3.TL4OddDefs

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Balance
open CFSG.Assembly.Dichotomy (involutionOddCore)

section Quot

variable {Y : Type} [Group Y] [Finite Y]

theorem exists_lift_of_commute {u t : Y} (htu : t ∈ Subgroup.centralizer ({u} : Set Y))
    (ht2 : t * t = 1) {c : OddQuot u}
    (hc : c * oddQuotMk u ⟨t, htu⟩ = oddQuotMk u ⟨t, htu⟩ * c) :
    ∃ x : Subgroup.centralizer ({u} : Set Y), (x : Y) * t = t * x ∧ oddQuotMk u x = c := by
  set N := componentClassificationOddCore ↥(Subgroup.centralizer ({u} : Set Y)) with hN
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N c
  set τ : Subgroup.centralizer ({u} : Set Y) := ⟨t, htu⟩ with hτ
  have hA : IsPGroup 2 (Subgroup.zpowers τ) :=
    isPGroup_zpowers_of_mul_self_eq_one (Subtype.ext ht2)
  have hc' : QuotientGroup.mk' N x * QuotientGroup.mk' N τ =
      QuotientGroup.mk' N τ * QuotientGroup.mk' N x := hc
  have hx : ∀ a ∈ Subgroup.zpowers τ, x⁻¹ * (a * x * a⁻¹) ∈ N := by
    intro a ha
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have hck : QuotientGroup.mk' N τ ^ k * QuotientGroup.mk' N x =
        QuotientGroup.mk' N x * QuotientGroup.mk' N τ ^ k :=
      ((Commute.zpow_left hc'.symm k)).eq
    have h1 : QuotientGroup.mk' N (x⁻¹ * (τ ^ k * x * (τ ^ k)⁻¹)) = 1 := by
      rw [map_mul, map_inv, map_mul, map_mul, map_inv, map_zpow, hck]
      group
    exact (QuotientGroup.eq_one_iff _).mp h1
  obtain ⟨n, hn, hfix⟩ := Bootstrap.exists_fixed_mem_coset_of_isPGroup hA
    (CFSG.ComponentClassification.OddCore.odd_card _)
    (fun a _ m hm => (inferInstance : N.Normal).conj_mem m hm a) hx
  refine ⟨x * n, ?_, ?_⟩
  · have h := congrArg Subtype.val (hfix τ (Subgroup.mem_zpowers τ))
    have h' : t * ((x * n : Subgroup.centralizer ({u} : Set Y)) : Y) * t⁻¹ =
        ((x * n : Subgroup.centralizer ({u} : Set Y)) : Y) := h
    rw [mul_inv_eq_iff_eq_mul] at h'
    exact h'.symm
  · have hn1 : QuotientGroup.mk' N n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
    show QuotientGroup.mk' N (x * n) = QuotientGroup.mk' N x
    rw [map_mul, hn1, mul_one]

theorem map_oddCent_le_involutionOddCore {u t : Y} (htu : t ∈ Subgroup.centralizer ({u} : Set Y))
    (ht2 : t * t = 1)
    (hθ : oddCoreImg (Subgroup.centralizer ({t} : Set Y)) ≤ Subgroup.centralizer ({u} : Set Y)) :
    ((oddCoreImg (Subgroup.centralizer ({t} : Set Y))).subgroupOf
        (Subgroup.centralizer ({u} : Set Y))).map (oddQuotMk u) ≤
      involutionOddCore (oddQuotMk u ⟨t, htu⟩) := by
  set C := Subgroup.centralizer ({u} : Set Y) with hC
  set θt := oddCoreImg (Subgroup.centralizer ({t} : Set Y)) with hθt
  have hDC : (θt.subgroupOf C).map (oddQuotMk u) ≤
      Subgroup.centralizer ({oddQuotMk u ⟨t, htu⟩} : Set (OddQuot u)) := by
    rintro _ ⟨d, hd, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hdt : (d : Y) * t = t * d :=
      Subgroup.mem_centralizer_singleton_iff.mp (oddCoreImg_le _ (Subgroup.mem_subgroupOf.mp hd))
    have e : d * ⟨t, htu⟩ = ⟨t, htu⟩ * d := Subtype.ext hdt
    rw [← map_mul, e, map_mul]
  have hnorm : ∀ c ∈ Subgroup.centralizer ({oddQuotMk u ⟨t, htu⟩} : Set (OddQuot u)),
      ∀ m ∈ (θt.subgroupOf C).map (oddQuotMk u),
        c * m * c⁻¹ ∈ (θt.subgroupOf C).map (oddQuotMk u) := by
    intro c hc m hm
    obtain ⟨x, hxt, rfl⟩ :=
      exists_lift_of_commute htu ht2 (Subgroup.mem_centralizer_singleton_iff.mp hc)
    obtain ⟨d, hd, rfl⟩ := hm
    refine ⟨x * d * x⁻¹, ?_, by simp only [map_mul, map_inv]⟩
    have hxC : (x : Y) ∈ Subgroup.centralizer ({t} : Set Y) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hxt
    exact Subgroup.mem_subgroupOf.mpr
      (conj_mem_oddCoreImg (Subgroup.le_normalizer hxC) (Subgroup.mem_subgroupOf.mp hd))
  have hodd : Odd (Nat.card ((θt.subgroupOf C).map (oddQuotMk u))) := by
    have h1 : Nat.card ((θt.subgroupOf C).map (oddQuotMk u)) ∣ Nat.card (θt.subgroupOf C) :=
      Subgroup.card_map_dvd _ _
    have h2 : Nat.card (θt.subgroupOf C) = Nat.card θt :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hθ).toEquiv
    rw [h2] at h1
    exact (odd_natCard_oddCoreImg _).of_dvd_nat h1
  exact TC.le_oddCoreImg_of_normalizes hDC hnorm hodd

theorem oddCent_le_oddCent_of_moved {u t : Y} (htu : t ∈ Subgroup.centralizer ({u} : Set Y))
    (ht2 : t * t = 1) (ht1 : t ≠ 1)
    (hθ : oddCoreImg (Subgroup.centralizer ({t} : Set Y)) ≤ Subgroup.centralizer ({u} : Set Y))
    (hL : ∀ L : Subgroup (OddQuot u), CFSG.IsComponent L →
      oddQuotMk u ⟨t, htu⟩ ∈ Subgroup.normalizer (L : Set (OddQuot u)) →
      (∃ y ∈ L, oddQuotMk u ⟨t, htu⟩ * y ≠ y * oddQuotMk u ⟨t, htu⟩) →
      Q3NM.AutOddFreeOn ↥L (IsInducedAut L (oddQuotMk u ⟨t, htu⟩))) :
    oddCoreImg (Subgroup.centralizer ({t} : Set Y)) ≤
      oddCoreImg (Subgroup.centralizer ({u} : Set Y)) := by
  set C := Subgroup.centralizer ({u} : Set Y) with hC
  have hτ2 : (⟨t, htu⟩ : C) * ⟨t, htu⟩ = 1 := Subtype.ext ht2
  have hbt2 : oddQuotMk u ⟨t, htu⟩ * oddQuotMk u ⟨t, htu⟩ = 1 := by
    rw [← map_mul, hτ2, map_one]
  have hbt1 : oddQuotMk u ⟨t, htu⟩ ≠ 1 := by
    intro h
    have hmem : (⟨t, htu⟩ : C) ∈ componentClassificationOddCore C :=
      (QuotientGroup.eq_one_iff _).mp h
    have hord : orderOf (⟨t, htu⟩ : C) = 2 :=
      orderOf_eq_prime (by rw [sq]; exact hτ2) (fun h' => ht1 (congrArg Subtype.val h'))
    have hdvd := Subgroup.orderOf_dvd_natCard _ hmem
    rw [hord] at hdvd
    exact (Nat.not_even_iff_odd.mpr (CFSG.ComponentClassification.OddCore.odd_card C))
      (even_iff_two_dvd.mpr hdvd)
  have hbot := oddCent_eq_bot_of_components (pPrimeCore_oddQuot_eq_bot u) hbt2 hbt1 hL
  have hD := map_oddCent_le_involutionOddCore htu ht2 hθ
  rw [hbot] at hD
  intro x hx
  have hxC := hθ hx
  have h1 : oddQuotMk u ⟨x, hxC⟩ = 1 :=
    (Subgroup.mem_bot).mp (hD ⟨⟨x, hxC⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩)
  have h2 : (⟨x, hxC⟩ : C) ∈ componentClassificationOddCore C :=
    (QuotientGroup.eq_one_iff _).mp h1
  exact ⟨⟨x, hxC⟩, h2, rfl⟩

end Quot

section Transport

variable {G : Type} [Group G] [Finite G]

theorem exists_oddQuot_embedding {H : Subgroup G} (hH : IsSubnormal H ⊤) :
    ∃ χ : (↥H ⧸ classicalInvolutionOddCore ↥H) →* G ⧸ componentClassificationOddCore G,
      Function.Injective χ ∧
      (∀ h : H, χ (QuotientGroup.mk' (classicalInvolutionOddCore ↥H) h) =
        QuotientGroup.mk' (componentClassificationOddCore G) (h : G)) ∧
      χ.range = H.map (QuotientGroup.mk' (componentClassificationOddCore G)) := by
  set N := componentClassificationOddCore G with hN
  set M := classicalInvolutionOddCore ↥H with hM
  have hMN : M = N.comap H.subtype :=
    CFSG.ComponentClassification.OddCore.subnormal_intersection H hH
  refine ⟨QuotientGroup.map M N H.subtype hMN.le, ?_, fun h => rfl, ?_⟩
  · rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro q hq
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective M q
    have h1 : QuotientGroup.mk' N (h : G) = 1 := hq
    have h2 : h ∈ M := by
      rw [hMN]
      exact Subgroup.mem_comap.mpr ((QuotientGroup.eq_one_iff (h : G)).mp h1)
    rw [Subgroup.mem_bot]
    exact (QuotientGroup.eq_one_iff _).mpr h2
  · ext y
    constructor
    · rintro ⟨q, rfl⟩
      obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective M q
      exact ⟨h, h.2, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨QuotientGroup.mk' M ⟨g, hg⟩, rfl⟩

theorem movedOddFree_quot_of_subnormal {H : Subgroup G} (hH : IsSubnormal H ⊤) {τ : G}
    (hτ : τ ∈ H)
    (hsec : ∀ L : Subgroup (↥H ⧸ classicalInvolutionOddCore ↥H), CFSG.IsComponent L →
      QuotientGroup.mk' (classicalInvolutionOddCore ↥H) (⟨τ, hτ⟩ : H) ∈
        Subgroup.normalizer (L : Set (↥H ⧸ classicalInvolutionOddCore ↥H)) →
      (∃ y ∈ L, QuotientGroup.mk' (classicalInvolutionOddCore ↥H) (⟨τ, hτ⟩ : H) * y ≠
        y * QuotientGroup.mk' (classicalInvolutionOddCore ↥H) (⟨τ, hτ⟩ : H)) →
      Q3NM.AutOddFreeOn ↥L
        (IsInducedAut L (QuotientGroup.mk' (classicalInvolutionOddCore ↥H) (⟨τ, hτ⟩ : H))))
    (L : Subgroup (G ⧸ componentClassificationOddCore G)) (hL : CFSG.IsComponent L)
    (hτN : QuotientGroup.mk' (componentClassificationOddCore G) τ ∈
      Subgroup.normalizer (L : Set (G ⧸ componentClassificationOddCore G)))
    (hτL : ∃ y ∈ L, QuotientGroup.mk' (componentClassificationOddCore G) τ * y ≠
      y * QuotientGroup.mk' (componentClassificationOddCore G) τ) :
    Q3NM.AutOddFreeOn ↥L
      (IsInducedAut L (QuotientGroup.mk' (componentClassificationOddCore G) τ)) := by
  set N := componentClassificationOddCore G with hN
  set M := classicalInvolutionOddCore ↥H with hM
  obtain ⟨χ, hχ, hχmk, hχR⟩ := exists_oddQuot_embedding hH
  set x : ↥H ⧸ M := QuotientGroup.mk' M ⟨τ, hτ⟩ with hx
  have hχx : χ x = QuotientGroup.mk' N τ := hχmk ⟨τ, hτ⟩
  have hHm : H.IsSubnormal :=
    CFSG.ComponentClassification.Components.mathlib_subnormal_of_chain hH
      Subgroup.IsSubnormal.top
  have hRm : χ.range.IsSubnormal := by
    rw [hχR]
    exact hHm.map (QuotientGroup.mk'_surjective N)
  have hτR : QuotientGroup.mk' N τ ∈ χ.range := ⟨x, hχx⟩
  have hle : L ≤ χ.range := by
    rcases CFSG.LocalCores.component_subnormal_subgroup hL hRm with h | h
    · exact h
    · exfalso
      obtain ⟨y, hy, hne⟩ := hτL
      apply hne
      have hc := Subgroup.commutator_mem_commutator hy hτR
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
      exact hc.symm
  set L₂ : Subgroup (↥H ⧸ M) := L.comap χ with hL₂def
  have hmap : L₂.map χ = L := Subgroup.map_comap_eq_self hle
  set e : ↥L₂ ≃* ↥L := (L₂.equivMapOfInjective χ hχ).trans (MulEquiv.subgroupCongr hmap) with he
  have he' : ∀ y : ↥L₂, ((e y : ↥L) : G ⧸ N) = χ y := fun y => rfl
  have hL₂ : CFSG.IsComponent L₂ := by
    set χ' : (↥H ⧸ M) ≃* ↥χ.range := MonoidHom.ofInjective hχ with hχ'
    have h1 := CFSG.LocalCores.isComponent_map_mulEquiv χ'.symm
      (CFSG.LocalCores.component_overgroup hL hle)
    have h2 : (L.subgroupOf χ.range).map χ'.symm.toMonoidHom = L₂ := by
      ext z
      rw [Subgroup.mem_map_equiv, MulEquiv.symm_symm, Subgroup.mem_subgroupOf, hL₂def,
        Subgroup.mem_comap]
      rfl
    rwa [h2] at h1
  have hxN : x ∈ Subgroup.normalizer (L₂ : Set (↥H ⧸ M)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro z
    rw [hL₂def, Subgroup.mem_comap, Subgroup.mem_comap, map_mul, map_mul, map_inv, hχx]
    exact Subgroup.mem_normalizer_iff.mp hτN (χ z)
  have hxmv : ∃ y ∈ L₂, x * y ≠ y * x := by
    obtain ⟨y, hy, hne⟩ := hτL
    obtain ⟨w, rfl⟩ := hle hy
    refine ⟨w, hy, fun h => hne ?_⟩
    have h2 := congrArg χ h
    rwa [map_mul, map_mul, hχx] at h2
  have hfree := hsec L₂ hL₂ hxN hxmv
  refine (autOddFreeOn_of_mulEquiv' e _ hfree).mono fun f' hf' y => ?_
  apply hχ
  have h1 : (MulAut.congr e).symm f' y = e.symm (f' (e y)) := rfl
  have h2 : χ (((MulAut.congr e).symm f' y : ↥L₂) : ↥H ⧸ M) = ((f' (e y) : ↥L) : G ⧸ N) := by
    rw [h1, ← he', MulEquiv.apply_symm_apply]
  rw [h2, hf' (e y), he', map_mul, map_mul, map_inv, hχx]

theorem movedOddFree_sub_of_quot {H : Subgroup G} (hH : IsSubnormal H ⊤) {τ : G} (hτ : τ ∈ H)
    (hq : ∀ L : Subgroup (G ⧸ componentClassificationOddCore G), CFSG.IsComponent L →
      QuotientGroup.mk' (componentClassificationOddCore G) τ ∈
        Subgroup.normalizer (L : Set (G ⧸ componentClassificationOddCore G)) →
      (∃ y ∈ L, QuotientGroup.mk' (componentClassificationOddCore G) τ * y ≠
        y * QuotientGroup.mk' (componentClassificationOddCore G) τ) →
      Q3NM.AutOddFreeOn ↥L
        (IsInducedAut L (QuotientGroup.mk' (componentClassificationOddCore G) τ)))
    (L : Subgroup (↥H ⧸ classicalInvolutionOddCore ↥H)) (hL : CFSG.IsComponent L)
    (hxN : QuotientGroup.mk' (classicalInvolutionOddCore ↥H) (⟨τ, hτ⟩ : H) ∈
      Subgroup.normalizer (L : Set (↥H ⧸ classicalInvolutionOddCore ↥H)))
    (hxL : ∃ y ∈ L, QuotientGroup.mk' (classicalInvolutionOddCore ↥H) (⟨τ, hτ⟩ : H) * y ≠
      y * QuotientGroup.mk' (classicalInvolutionOddCore ↥H) (⟨τ, hτ⟩ : H)) :
    Q3NM.AutOddFreeOn ↥L
      (IsInducedAut L (QuotientGroup.mk' (classicalInvolutionOddCore ↥H) (⟨τ, hτ⟩ : H))) := by
  set N := componentClassificationOddCore G with hN
  set M := classicalInvolutionOddCore ↥H with hM
  obtain ⟨χ, hχ, hχmk, hχR⟩ := exists_oddQuot_embedding hH
  set x : ↥H ⧸ M := QuotientGroup.mk' M ⟨τ, hτ⟩ with hx
  have hχx : χ x = QuotientGroup.mk' N τ := hχmk ⟨τ, hτ⟩
  set e : ↥L ≃* ↥(L.map χ) := L.equivMapOfInjective χ hχ with he
  have he' : ∀ y : ↥L, ((e y : ↥(L.map χ)) : G ⧸ N) = χ y := fun y => rfl
  have hLb : CFSG.IsComponent (L.map χ) := by
    set χ' : (↥H ⧸ M) ≃* ↥χ.range := MonoidHom.ofInjective hχ with hχ'
    have h1 : CFSG.IsComponent (L.map χ'.toMonoidHom) :=
      CFSG.LocalCores.isComponent_map_mulEquiv χ' hL
    have hHR : IsSubnormal χ.range ⊤ := by
      rw [hχR]
      have := CFSG.ComponentClassification.Components.chain_map
        (QuotientGroup.mk' N) hH
      rwa [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)] at this
    have h2 : IsSubnormal ((L.map χ'.toMonoidHom).map χ.range.subtype) ⊤ :=
      isSubnormal_top_map_subtype hHR
        (CFSG.ComponentClassification.Components.chain_of_mathlib_subnormal h1.2)
    have h3 : (L.map χ'.toMonoidHom).map χ.range.subtype = L.map χ := by
      rw [Subgroup.map_map]
      rfl
    rw [h3] at h2
    exact ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e hL.1,
      CFSG.ComponentClassification.Components.mathlib_subnormal_of_chain h2
        Subgroup.IsSubnormal.top⟩
  have hτN : QuotientGroup.mk' N τ ∈ Subgroup.normalizer ((L.map χ) : Set (G ⧸ N)) := by
    rw [← hχx]
    exact Subgroup.le_normalizer_map χ (Subgroup.mem_map_of_mem χ hxN)
  have hτL : ∃ y ∈ L.map χ, QuotientGroup.mk' N τ * y ≠ y * QuotientGroup.mk' N τ := by
    obtain ⟨y, hy, hne⟩ := hxL
    refine ⟨χ y, Subgroup.mem_map_of_mem χ hy, fun h => hne (hχ ?_)⟩
    rw [map_mul, map_mul, hχx]
    exact h
  have hfree := hq (L.map χ) hLb hτN hτL
  refine (autOddFreeOn_of_mulEquiv' e.symm _ hfree).mono fun f hf z => ?_
  have h1 : (MulAut.congr e.symm).symm f z = e (f (e.symm z)) := rfl
  rw [h1, he', hf (e.symm z), map_mul, map_mul, map_inv, hχx, ← he', MulEquiv.apply_symm_apply]

end Transport

section Edge

variable {Y : Type} [Group Y] [Finite Y]

theorem oddCent_le_oddCent_of_sec {R : Subgroup Y} {u t : Y}
    (htu : t ∈ Subgroup.centralizer ({u} : Set Y)) (ht2 : t * t = 1) (ht1 : t ≠ 1)
    (hθ : oddCoreImg (Subgroup.centralizer ({t} : Set Y)) ≤ Subgroup.centralizer ({u} : Set Y))
    (ht : (⟨t, htu⟩ : Subgroup.centralizer ({u} : Set Y)) ∈ secH R u)
    (hsec : SecMovedOddFree R u
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH R u)) ⟨⟨t, htu⟩, ht⟩)) :
    oddCoreImg (Subgroup.centralizer ({t} : Set Y)) ≤
      oddCoreImg (Subgroup.centralizer ({u} : Set Y)) :=
  oddCent_le_oddCent_of_moved htu ht2 ht1 hθ fun L hL hN hmv =>
    movedOddFree_quot_of_subnormal (isSubnormal_subnormalClosure _) ht hsec L hL hN hmv

end Edge

end CFSG.ClassicalInvolution.Q3.TL4
