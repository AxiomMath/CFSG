module

public import CFSG.GH74.GLS.Stage12.McLCover
public import CFSG.GH74.GLS.Stage12.Interface
public import CFSG.GH74.Uniqueness.SE
public import CFSG.LocalAnalysis.ComponentInitial.AlternatingFourGroup

public section

namespace CFSG.GH74.GLS.Stage12.McLRec

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Uniqueness

section StronglyEmbedded

variable {G : Type*} [Group G]

theorem mem_conjugate_iff (H : Subgroup G) (g u : G) :
    u ∈ CFSG.conjugate H g ↔ g * u * g⁻¹ ∈ H := by
  unfold CFSG.conjugate
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨h, hh, rfl⟩
    simpa [mul_assoc] using hh
  · intro h
    exact ⟨g * u * g⁻¹, h, by group⟩

theorem isStronglyEmbedded_of_centralizers [Finite G] (H : Subgroup G) (hH : H ≠ ⊤)
    (hev : Even (Nat.card H))
    (hone : ∀ u v : H, orderOf u = 2 → orderOf v = 2 → IsConj u v)
    (hcent : ∀ u : G, u ∈ H → orderOf u = 2 → centralizer ({u} : Set G) ≤ H) :
    CFSG.IsStronglyEmbedded H := by
  refine ⟨hH, hev, fun g hg => ?_⟩
  by_contra hodd
  have heven : Even (Nat.card ↥(H ⊓ CFSG.conjugate H g)) := by
    rwa [Nat.not_odd_iff_even] at hodd
  have h2 : 2 ∣ Nat.card ↥(H ⊓ CFSG.conjugate H g) := even_iff_two_dvd.mp heven
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(H ⊓ CFSG.conjugate H g)) 2 h2
  have hxo : orderOf (x : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hx
  have hxH : (x : G) ∈ H := (Subgroup.mem_inf.mp x.2).1
  have hxg : (x : G) ∈ CFSG.conjugate H g := (Subgroup.mem_inf.mp x.2).2
  rw [mem_conjugate_iff] at hxg
  set v : G := g * (x : G) * g⁻¹ with hv
  have hvo : orderOf v = 2 := by
    rw [hv, ← MulAut.conj_apply, MulEquiv.orderOf_eq]; exact hxo
  obtain ⟨c, hc⟩ := isConj_iff.mp (hone ⟨x, hxH⟩ ⟨v, hxg⟩ (by rw [Subgroup.orderOf_mk]; exact hxo)
    (by rw [Subgroup.orderOf_mk]; exact hvo))
  have hc' : (c : G) * (x : G) * (c : G)⁻¹ = v := by
    have := congrArg Subtype.val hc
    simpa using this
  have hg1 : g⁻¹ * (c : G) ∈ centralizer ({(x : G)} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    have e1 : (c : G) * (x : G) = g * (x : G) * g⁻¹ * (c : G) := by
      have : (c : G) * (x : G) = ((c : G) * (x : G) * (c : G)⁻¹) * (c : G) := by group
      rw [this, hc', hv]
    calc (x : G) * (g⁻¹ * (c : G)) = g⁻¹ * (g * (x : G) * g⁻¹ * (c : G)) := by group
      _ = g⁻¹ * ((c : G) * (x : G)) := by rw [e1]
      _ = g⁻¹ * (c : G) * (x : G) := by group
  have hgH : g⁻¹ * (c : G) ∈ H := hcent (x : G) hxH hxo hg1
  have : g ∈ H := by
    have h3 : g⁻¹ ∈ H := by
      have := H.mul_mem hgH (H.inv_mem c.2)
      simpa using this
    simpa using H.inv_mem h3
  exact hg this

end StronglyEmbedded

section Simple

variable {X : Type*} [Group X]

theorem involutionClosure_eq_top (hs : IsSimpleGroup X) {z : X} (hz : orderOf z = 2) :
    involutionClosure X = ⊤ := by
  have hnormal : (involutionClosure X).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hle : involutionClosure X ≤ (involutionClosure X).comap (MulAut.conj g).toMonoidHom := by
      unfold involutionClosure
      rw [Subgroup.closure_le]
      intro s hs'
      refine Subgroup.subset_closure ?_
      show orderOf (g * s * g⁻¹) = 2
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
      exact hs'
    exact hle hn
  rcases hnormal.eq_bot_or_eq_top with h | h
  · exfalso
    have hzmem : z ∈ involutionClosure X := Subgroup.subset_closure hz
    rw [h, Subgroup.mem_bot] at hzmem
    rw [hzmem, orderOf_one] at hz
    exact absurd hz (by norm_num)
  · exact h

theorem pPrimeCore_eq_bot_of_simple [Finite X] (hs : IsSimpleGroup X) (hev : Even (Nat.card X)) :
    CFSG.pPrimeCore 2 X = ⊥ := by
  unfold CFSG.pPrimeCore
  refine le_antisymm (sSup_le ?_) bot_le
  rintro K ⟨hKn, hKc⟩
  rcases hKn.eq_bot_or_eq_top with h | h
  · exact h.le
  · exfalso
    rw [h, Subgroup.card_top] at hKc
    have := Nat.coprime_two_left.mp hKc
    exact (Nat.not_even_iff_odd.mpr this) hev

theorem exists_central_involution [Finite X] (S : Subgroup X) (hS : IsPGroup 2 S)
    (hcard : 2 < Nat.card S) : ∃ z : X, z ∈ S ∧ orderOf z = 2 ∧ ∀ s ∈ S, s * z = z * s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnt : Nontrivial S := by
    refine Finite.one_lt_card_iff_nontrivial.mp ?_
    omega
  have hcnt : Nontrivial (Subgroup.center S) := hS.center_nontrivial
  have hZ : IsPGroup 2 (Subgroup.center S) := hS.to_subgroup _
  have hdvd : 2 ∣ Nat.card (Subgroup.center S) := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hZ
    have hk0 : k ≠ 0 := by
      rintro rfl
      have h1 : Nat.card (Subgroup.center S) = 1 := by simpa using hk
      have := Finite.one_lt_card_iff_nontrivial.mpr hcnt
      omega
    rw [hk]
    exact dvd_pow_self 2 hk0
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center S) 2 hdvd
  refine ⟨((y : S) : X), (y : S).2, ?_, fun s hs => ?_⟩
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact hy
  · have := Subgroup.mem_center_iff.mp y.2 ⟨s, hs⟩
    exact congrArg Subtype.val this

end Simple

theorem two_le_open_pRank_top {G : Type*} [Group G] [Finite G] {x y : G} (hx : orderOf x = 2)
    (hy : orderOf y = 2) (hxy : x * y = y * x) (hne : x ≠ y) :
    2 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup G) := by
  obtain ⟨V, -, hV, hVcard⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.AlternatingFourGroup.exists_elementary_four_of_commute
      hx hy hxy hne
  refine le_csSup ⟨Nat.card G, ?_⟩ ⟨V, le_top,
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 V).mp hV, by rw [hVcard]; norm_num⟩
  rintro r ⟨B, -, -, hB⟩
  calc r ≤ 2 ^ r := (Nat.lt_pow_self (by norm_num)).le
    _ = Nat.card B := hB.symm
    _ ≤ Nat.card G := Subgroup.card_le_card_group B

theorem exists_sylow_normalized_of_borel {G : Type} [Group G] [Finite G] (hs : IsSimpleGroup G)
    (hev : Even (Nat.card G)) (L : Subgroup G) (hL : L = ⊤) (M : Subgroup G)
    (hB : IsBorel ((M.comap L.subtype).map (QuotientGroup.mk' (CFSG.pPrimeCore 2 ↥L)))) :
    ∃ S : Subgroup G, IsPGroup 2 S ∧ Nat.card S = 2 ^ (Nat.card G).factorization 2 ∧ S ≤ M ∧
      M ≤ normalizer (S : Set G) := by
  subst hL
  have hsT : IsSimpleGroup ↥(⊤ : Subgroup G) := by
    have := hs
    exact MulEquiv.isSimpleGroup (Subgroup.topEquiv (G := G))
  have hevT : Even (Nat.card ↥(⊤ : Subgroup G)) := by rwa [Subgroup.card_top]
  have hbot : CFSG.pPrimeCore 2 ↥(⊤ : Subgroup G) = ⊥ := pPrimeCore_eq_bot_of_simple hsT hevT
  set φ : G →* ↥(⊤ : Subgroup G) ⧸ CFSG.pPrimeCore 2 ↥(⊤ : Subgroup G) :=
    (QuotientGroup.mk' (CFSG.pPrimeCore 2 ↥(⊤ : Subgroup G))).comp
      (Subgroup.topEquiv (G := G)).symm.toMonoidHom with hφ
  have hφinj : Function.Injective φ := by
    intro a b hab
    have h1 : ((Subgroup.topEquiv (G := G)).symm a)⁻¹ * (Subgroup.topEquiv (G := G)).symm b ∈
        CFSG.pPrimeCore 2 ↥(⊤ : Subgroup G) := QuotientGroup.eq.mp hab
    rw [hbot, Subgroup.mem_bot, inv_mul_eq_one] at h1
    exact (Subgroup.topEquiv (G := G)).symm.injective h1
  have hφsurj : Function.Surjective φ := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pPrimeCore 2 ↥(⊤ : Subgroup G)) q
    refine ⟨(x : G), ?_⟩
    have hx' : (Subgroup.topEquiv (G := G)).symm (x : G) = x := Subtype.ext rfl
    simp [hφ, hx']
  let ψ := MulEquiv.ofBijective φ ⟨hφinj, hφsurj⟩
  have hψ : ∀ g, ψ g = φ g := fun g => rfl
  obtain ⟨S, hS⟩ := hB
  have hBM : ∀ q, q ∈ (M.comap (⊤ : Subgroup G).subtype).map
      (QuotientGroup.mk' (CFSG.pPrimeCore 2 ↥(⊤ : Subgroup G))) ↔ ∃ g ∈ M, φ g = q := by
    intro q
    simp only [Subgroup.mem_map, Subgroup.mem_comap]
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨(x : G), hx, ?_⟩
      have hx' : (Subgroup.topEquiv (G := G)).symm (x : G) = x := Subtype.ext rfl
      simp [hφ, hx']
    · rintro ⟨g, hg, rfl⟩
      exact ⟨(Subgroup.topEquiv (G := G)).symm g, by simpa using hg, by simp [hφ]⟩
  have hSB : ∀ q : ↥(⊤ : Subgroup G) ⧸ CFSG.pPrimeCore 2 ↥(⊤ : Subgroup G),
      q ∈ normalizer (((S : Subgroup (↥(⊤ : Subgroup G) ⧸ CFSG.pPrimeCore 2 ↥(⊤ : Subgroup G)))) :
        Set (↥(⊤ : Subgroup G) ⧸ CFSG.pPrimeCore 2 ↥(⊤ : Subgroup G))) ↔ ∃ g ∈ M, φ g = q := by
    intro q
    rw [← hS]
    exact hBM q
  refine ⟨(S : Subgroup _).map ψ.symm.toMonoidHom, ?_, ?_, ?_, ?_⟩
  · exact S.isPGroup'.map ψ.symm.toMonoidHom
  · have h1 := Subgroup.card_map_of_injective (f := ψ.symm.toMonoidHom) ψ.symm.injective
      (K := (S : Subgroup _))
    have h2 := Sylow.card_eq_multiplicity S
    have h3 : Nat.card (↥(⊤ : Subgroup G) ⧸ CFSG.pPrimeCore 2 ↥(⊤ : Subgroup G)) = Nat.card G :=
      (Nat.card_congr ψ.toEquiv).symm
    rw [h1, h2, h3]
  · intro s' hs'
    obtain ⟨s, hsS, rfl⟩ := Subgroup.mem_map.mp hs'
    have : φ (ψ.symm s) = s := by
      have := ψ.apply_symm_apply s
      rwa [hψ] at this
    obtain ⟨g, hg, hgs⟩ := (hSB s).mp (Subgroup.le_normalizer hsS)
    have : g = ψ.symm s := hφinj (hgs.trans this.symm)
    rw [MulEquiv.coe_toMonoidHom]
    rw [← this]
    exact hg
  · intro m hm
    rw [Subgroup.mem_normalizer_iff]
    have hmS := (hSB (φ m)).mpr ⟨m, hm, rfl⟩
    rw [Subgroup.mem_normalizer_iff] at hmS
    intro h
    have hmem : ∀ x : G, x ∈ (S : Subgroup _).map ψ.symm.toMonoidHom ↔ ψ x ∈ (S : Subgroup _) := by
      intro x
      constructor
      · rintro hx
        obtain ⟨s, hsS, rfl⟩ := Subgroup.mem_map.mp hx
        simpa using hsS
      · intro hx
        exact Subgroup.mem_map.mpr ⟨ψ x, hx, by simp⟩
    rw [hmem, hmem, map_mul, map_mul, map_inv]
    exact hmS (ψ h)

structure CoverFacts (n c : ℕ) : Prop where
  four_dvd : 4 ∣ c
  card_eq : ∀ (K : Type) [Group K], IsDoubleCoverOfAlt K n → Nat.card K = c
  card_le_two : ∀ (K : Type) [Group K], IsDoubleCoverOfAlt K n → ∀ T : Subgroup K, T.Normal →
    IsPGroup 2 T → Nat.card T ≤ 2
  exists_noncentral : ∀ (K : Type) [Group K], IsDoubleCoverOfAlt K n →
    ∃ u : K, u ^ 2 = 1 ∧ u ∉ Subgroup.center K

theorem coverFacts_eight : CoverFacts 8 40320 where
  four_dvd := by norm_num
  card_eq := fun K _ h => card_eq_of_doubleCover h
  card_le_two := fun K _ h T hT hTp => card_le_two_of_normal_of_doubleCover h T hTp
  exists_noncentral := fun K _ h => exists_noncentral_involution_of_doubleCover h

theorem no_strongly_embedded_of_coverFacts
    {G : Type} [Group G] [Finite G] (hs : IsSimpleGroup G)
    {n c : ℕ} (hF : CoverFacts n c) (hG : OneClassDoubleCover G n) (M : Subgroup G)
    (hM : CFSG.IsStronglyEmbedded M)
    (hcent : ∀ u : G, u ∈ M → orderOf u = 2 → centralizer ({u} : Set G) ≤ M) : False := by
  obtain ⟨z, hz, hconj, hcov⟩ := hG
  have hz2 : orderOf z = 2 := hz.1
  have hcovu : ∀ u : G, orderOf u = 2 → IsDoubleCoverOfAlt ↥(centralizer ({u} : Set G)) n := by
    intro u hu
    obtain ⟨c', hc'⟩ := isConj_iff.mp (hconj z u hz2 hu)
    rw [← hc']
    exact isDoubleCoverOfAlt_congr (centralizerConjEquiv c' z) hcov
  have hcardC : Nat.card ↥(centralizer ({z} : Set G)) = c := hF.card_eq _ hcov
  obtain ⟨u, hu2, hunc⟩ := hF.exists_noncentral _ hcov
  have hu1 : (u : G) ≠ 1 := by
    intro h
    apply hunc
    have : u = 1 := Subtype.ext h
    rw [this]; exact Subgroup.one_mem _
  have huG2 : (u : G) ^ 2 = 1 := by
    have := congrArg Subtype.val hu2
    simpa using this
  have huo : orderOf (u : G) = 2 := orderOf_eq_prime huG2 hu1
  have hzu : z * (u : G) = (u : G) * z := (Subgroup.mem_centralizer_iff.mp u.2) z rfl
  have hne : z ≠ (u : G) := by
    intro h
    apply hunc
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← h]
    exact ((Subgroup.mem_centralizer_iff.mp g.2) z rfl).symm
  have hrank := two_le_open_pRank_top hz2 huo hzu hne
  have hL := involutionClosure_eq_top hs hz2
  have hcG : c ∣ Nat.card G := by
    have h1 : Nat.card ↥(centralizer ({z} : Set G)) ∣ Nat.card G :=
      Subgroup.card_subgroup_dvd_card _
    rwa [hcardC] at h1
  have hev : Even (Nat.card G) :=
    even_iff_two_dvd.mpr ((dvd_trans (by norm_num : 2 ∣ 4) hF.four_dvd).trans hcG)
  rcases S_SE_proof G M hM with h | ⟨-, -, hB⟩
  · rw [hL] at h
    omega
  · obtain ⟨S, hSp, hScard, hSM, hMN⟩ := exists_sylow_normalized_of_borel hs hev _ hL M hB
    have h4 : 2 ^ 2 ∣ Nat.card G := (by simpa using hF.four_dvd : 2 ^ 2 ∣ c).trans hcG
    have hfac : 2 ≤ (Nat.card G).factorization 2 :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (Nat.card_pos (α := G)).ne').mp h4
    have hS2 : 2 < Nat.card S := by
      rw [hScard]
      calc 2 < 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (Nat.card G).factorization 2 := Nat.pow_le_pow_right (by norm_num) hfac
    obtain ⟨z', hz'S, hz'o, hz'c⟩ := exists_central_involution S hSp hS2
    have hz'M : z' ∈ M := hSM hz'S
    have hKM : centralizer ({z'} : Set G) ≤ M := hcent z' hz'M hz'o
    have hSK : S ≤ centralizer ({z'} : Set G) := by
      intro s hsS
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact (hz'c s hsS).symm
    have hnorm : (S.subgroupOf (centralizer ({z'} : Set G))).Normal := by
      refine ⟨fun t ht k => ?_⟩
      have hkN : (k : G) ∈ normalizer (S : Set G) := hMN (hKM k.2)
      rw [Subgroup.mem_subgroupOf] at ht ⊢
      have := (Subgroup.mem_normalizer_iff.mp hkN (t : G)).mp ht
      simpa using this
    have hTp : IsPGroup 2 (S.subgroupOf (centralizer ({z'} : Set G))) :=
      hSp.of_equiv (Subgroup.subgroupOfEquivOfLe hSK).symm
    have hTc : Nat.card (S.subgroupOf (centralizer ({z'} : Set G))) = Nat.card S :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSK).toEquiv
    have hle := hF.card_le_two _ (hcovu z' hz'o) (S.subgroupOf (centralizer ({z'} : Set G)))
      hnorm hTp
    rw [hTc] at hle
    omega

theorem no_strongly_embedded
    {G : Type} [Group G] [Finite G] (hs : IsSimpleGroup G)
    (hG : OneClassDoubleCover G 8) (M : Subgroup G) (hM : CFSG.IsStronglyEmbedded M)
    (hcent : ∀ u : G, u ∈ M → orderOf u = 2 → centralizer ({u} : Set G) ≤ M) : False :=
  no_strongly_embedded_of_coverFacts hs coverFacts_eight hG M hM hcent

theorem card_centralizer_involution_of_coverFacts {G : Type} [Group G] [Finite G] {n c : ℕ}
    (hF : CoverFacts n c) (hG : OneClassDoubleCover G n) {u : G} (hu : orderOf u = 2) :
    Nat.card (centralizer ({u} : Set G)) = c := by
  obtain ⟨z, hz, hconj, hcov⟩ := hG
  obtain ⟨c', hc'⟩ := isConj_iff.mp (hconj z u hz.1 hu)
  rw [← hc', card_centralizer_conj]
  exact hF.card_eq _ hcov

theorem eq_top_of_oneClass_centralizers
    {G : Type} [Group G] [Finite G] (hs : IsSimpleGroup G)
    {n c : ℕ} (hF : CoverFacts n c) (hG : OneClassDoubleCover G n) (H : Subgroup G)
    (hev : Even (Nat.card H))
    (hone : ∀ u v : H, orderOf u = 2 → orderOf v = 2 → IsConj u v)
    (hcH : ∀ u : H, orderOf u = 2 → Nat.card (centralizer ({u} : Set H)) = c) : H = ⊤ := by
  by_contra hH
  have hcent : ∀ u : G, u ∈ H → orderOf u = 2 → centralizer ({u} : Set G) ≤ H := by
    intro u hu ho
    have hu'o : orderOf (⟨u, hu⟩ : H) = 2 := by rw [Subgroup.orderOf_mk]; exact ho
    have hcG : Nat.card (centralizer ({u} : Set G)) = c :=
      card_centralizer_involution_of_coverFacts hF hG ho
    have hmap : (centralizer ({(⟨u, hu⟩ : H)} : Set H)).map H.subtype ≤
        centralizer ({u} : Set G) := by
      rintro _ ⟨y, hy, rfl⟩
      have hy' := Subgroup.mem_centralizer_iff.mp hy
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact congrArg Subtype.val (hy' ⟨u, hu⟩ rfl)
    have hcard : Nat.card (centralizer ({u} : Set G)) ≤
        Nat.card ((centralizer ({(⟨u, hu⟩ : H)} : Set H)).map H.subtype) := by
      rw [Subgroup.card_map_of_injective H.subtype_injective, hcH _ hu'o, hcG]
    have heq := Subgroup.eq_of_le_of_card_ge hmap hcard
    rw [← heq]
    exact Subgroup.map_subtype_le _
  exact no_strongly_embedded_of_coverFacts hs hF hG H
    (isStronglyEmbedded_of_centralizers H hH hev hone hcent) hcent

end CFSG.GH74.GLS.Stage12.McLRec
