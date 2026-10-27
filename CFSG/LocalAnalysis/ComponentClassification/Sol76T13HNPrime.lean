module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76T13HPerm

public section

namespace CFSG.ComponentClassification.Sol76T13

open CFSG Subgroup CFSG.ComponentClassification.FooteLit CFSG.ComponentClassification.Sol76
  CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type} [Group G] [Finite G] {𝒜 : Thm13Ambient}

theorem mem_kStarComponents_normalizer {N K : Subgroup G} (hK : K ∈ kStarComponents N) :
    K ∈ kStarComponents (normalizer (solomonKStarOf N : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKD : K ≤ solomonKStarOf N := le_iSup₂_of_le K hK le_rfl
  have hKDc := isTwoComponentIn_of_le hK.1 hKD (solomonKStarOf_le N)
  have hDn : ((solomonKStarOf N).subgroupOf
      (normalizer ((solomonKStarOf N : Subgroup G) : Set G))).Normal :=
    Subgroup.normal_in_normalizer
  refine ⟨⟨hKD.trans le_normalizer, ?_⟩, hK.2⟩
  exact (CatalogueBPrimeJoin.pComponent_subgroupOf_iff_of_subnormal hKD le_normalizer
    hDn.isSubnormal).mpr hKDc.2

theorem lemma313NarrowInputFor_of_nPrime_twoPart (hq : QuasisimpleTwoPartInput)
    (h𝒜 : ∀ (G : Type) [Group G] [Finite G], 𝒜 G → KStarKProper G)
    (hnP : Lemma313NarrowNPrimeInputFor 𝒜) : Lemma313NarrowInputFor 𝒜 := by
  intro G _ _ hG N hN hKstar hCb K hK g hKg hβ1 hβ2 hcase
  classical
  set D := solomonKStarOf N with hD
  set M := normalizer (D : Set G) with hM
  have hLg : ∀ L ∈ kStarComponents N, conjugate L g ∈ kStarComponents (conjugate M g) := by
    intro L hL
    rw [kStarComponents_conjugate]
    exact ⟨L, mem_kStarComponents_normalizer hL, rfl⟩
  rcases hcase with ⟨L, hL, hKL⟩ | ⟨L, hL, hLM, K', hK', hLK'⟩ | hN'
  ·
    exact (hKL (le_normalizer_of_permutes hq (h𝒜 G hG) (mem_kStarComponents_normalizer hK).1
      hK.2 hKg (hCb K hK) (fun J hJ => hJ.1)
      (fun k hk J hJ => map_conj_mem_kStarComponents hJ (hKg hk)) _ (hLg L hL))).elim
  ·
    have hLgc := hLg L hL
    have hCbg : ∀ s ∈ conjugate L g, orderOf s = 2 →
        centralizer ({s} : Set G) ≤ conjugate M g := by
      intro s hs hs2 x hx
      obtain ⟨s₀, hs₀, rfl⟩ := Subgroup.mem_map.mp hs
      have hs₀2 : orderOf s₀ = 2 := by
        rw [← hs2]
        exact (orderOf_injective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective s₀).symm
      have hx1 : x * (g⁻¹ * s₀ * g) = g⁻¹ * s₀ * g * x := by
        have h := mem_centralizer_singleton_iff.mp hx
        simpa [MulAut.conj_apply] using h
      have hx' : g * x * g⁻¹ ∈ centralizer ({s₀} : Set G) := by
        rw [mem_centralizer_singleton_iff]
        calc g * x * g⁻¹ * s₀ = g * (x * (g⁻¹ * s₀ * g)) * g⁻¹ := by group
          _ = g * (g⁻¹ * s₀ * g * x) * g⁻¹ := by rw [hx1]
          _ = s₀ * (g * x * g⁻¹) := by group
      refine Subgroup.mem_map.mpr ⟨g * x * g⁻¹, hCb L hL s₀ hs₀ hs₀2 hx', ?_⟩
      simp [mul_assoc]
    exact (hLK' (le_normalizer_of_permutes hq (h𝒜 G hG) hLgc.1 hLgc.2 hLM hCbg
      (fun J hJ => hJ.1) (fun k hk J hJ => map_conj_mem_kStarComponents hJ (hLM hk)) K'
      (mem_kStarComponents_normalizer hK'))).elim
  · exact hnP G hG N hN hKstar hCb K hK g hKg hβ1 hβ2 hN'

omit [Finite G] in
theorem fusionZStar_map_le_coreActionKernel (L : Subgroup G) :
    (Open.fusionZStar ↥L).map L.subtype ≤ coreActionKernel L := by
  rintro _ ⟨u', hu'Z, rfl⟩
  refine ⟨le_normalizer u'.2, fun j hj => ?_⟩
  have hzc : QuotientGroup.mk' (pPrimeCore 2 ↥L) u' ∈ center (↥L ⧸ pPrimeCore 2 ↥L) := by
    have hu'Z' : u' ∈ Open.fusionZStar ↥L := hu'Z
    rw [Sol78.fusionZStar_eq_comap, mem_comap] at hu'Z'
    exact hu'Z'
  have hc := mem_center_iff.mp hzc (QuotientGroup.mk' (pPrimeCore 2 ↥L) ⟨j, hj⟩)
  have h1 : QuotientGroup.mk' (pPrimeCore 2 ↥L) ((⟨j, hj⟩ : ↥L)⁻¹ * u'⁻¹ * ⟨j, hj⟩ * u') = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_assoc _ _ (QuotientGroup.mk' _ u'), hc]
    group
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact ⟨_, h1, by simp⟩

theorem inf_le_fusionZStar_of_not_le {K C : Subgroup G}
    (hKq : IsQuasisimple (↥K ⧸ pPrimeCore 2 ↥K)) (hKres : oddResidualIn K = K)
    (hKC : K ≤ normalizer (C : Set G)) (hne : ¬ K ≤ C) :
    K ⊓ C ≤ (Open.fusionZStar ↥K).map K.subtype := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup ↥K := C.subgroupOf K with hNdef
  have hNn : N.Normal := ⟨fun n hn k => by
    rw [hNdef, mem_subgroupOf] at hn ⊢
    simpa using (mem_normalizer_iff.mp (hKC k.2) n).mp hn⟩
  have hNmap : (N.map (QuotientGroup.mk' (pPrimeCore 2 ↥K))).Normal :=
    hNn.map _ (QuotientGroup.mk'_surjective _)
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hKq hNmap with htop | hcen
  · exfalso
    apply hne
    have h2 : ∀ x ∈ K, (∃ k : ℕ, orderOf x = 2 ^ k) → x ∈ C := by
      rintro x hxK ⟨k, hk⟩
      have hx : QuotientGroup.mk' (pPrimeCore 2 ↥K) ⟨x, hxK⟩ ∈
          N.map (QuotientGroup.mk' (pPrimeCore 2 ↥K)) := by
        rw [htop]
        exact mem_top _
      obtain ⟨n, hnN, hn⟩ := hx
      have ho : n⁻¹ * ⟨x, hxK⟩ ∈ pPrimeCore 2 ↥K := by
        rw [← QuotientGroup.eq]
        exact hn
      have hψn : QuotientGroup.mk' N n = 1 := (QuotientGroup.eq_one_iff n).mpr hnN
      have hψx : QuotientGroup.mk' N ⟨x, hxK⟩ = QuotientGroup.mk' N (n⁻¹ * ⟨x, hxK⟩) := by
        rw [map_mul, map_inv, hψn, inv_one, one_mul]
      have hodd : Nat.Coprime (orderOf (QuotientGroup.mk' N ⟨x, hxK⟩)) 2 := by
        rw [hψx]
        have h1 := orderOf_map_dvd (QuotientGroup.mk' N) (n⁻¹ * ⟨x, hxK⟩)
        have h2 := orderOf_dvd_natCard (⟨_, ho⟩ : ↥(pPrimeCore 2 ↥K))
        rw [Subgroup.orderOf_mk] at h2
        exact Nat.Coprime.coprime_dvd_left (h1.trans h2)
          (pPrimeCore_coprime_card (p := 2) (G := ↥K)).symm
      have hpow : orderOf (QuotientGroup.mk' N ⟨x, hxK⟩) ∣ 2 ^ k := by
        have h1 := orderOf_map_dvd (QuotientGroup.mk' N) ⟨x, hxK⟩
        rwa [Subgroup.orderOf_mk, hk] at h1
      have h1 : orderOf (QuotientGroup.mk' N ⟨x, hxK⟩) = 1 :=
        Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right k hodd) hpow
      rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact h1
    rw [← hKres]
    exact (closure_le C).mpr fun x ⟨hxK, hx⟩ => h2 x hxK hx
  · intro x hx
    have hxN : (⟨x, hx.1⟩ : ↥K) ∈ N := hx.2
    have hxZ : (⟨x, hx.1⟩ : ↥K) ∈ Open.fusionZStar ↥K := by
      rw [Sol78.fusionZStar_eq_comap, mem_comap]
      exact hcen (mem_map_of_mem _ hxN)
    exact ⟨_, hxZ, rfl⟩

theorem le_sup_coreActionKernel_of_inner {K L : Subgroup G}
    (hKq : IsQuasisimple (↥K ⧸ pPrimeCore 2 ↥K)) (hKres : oddResidualIn K = K)
    (hKL : K ≤ normalizer (L : Set G)) (hnt : ¬ K ≤ coreActionKernel L)
    (hin : K ≤ L ⊔ coreActionKernel L) (hcard : Nat.card K = Nat.card L)
    (hZ : Nat.card ((Open.fusionZStar ↥K).map K.subtype) =
      Nat.card ((Open.fusionZStar ↥L).map L.subtype)) :
    L ≤ K ⊔ coreActionKernel L := by
  by_contra hLK
  set C := coreActionKernel L with hC
  have hKC : K ≤ normalizer (C : Set G) := fun k hk =>
    FooteLit.mem_normalizer_coreActionKernel (hKL hk)
  have hLC : L ≤ normalizer (C : Set G) := fun l hl =>
    FooteLit.mem_normalizer_coreActionKernel (le_normalizer hl)
  have hlt : K ⊔ C < L ⊔ C := lt_of_le_of_ne (sup_le hin le_sup_right) fun h =>
    hLK (by rw [h]; exact le_sup_left)
  have hcardlt := Subgroup.card_lt_of_lt hlt
  have h1 := Sol78.card_sup_mul_card_inf' hKC
  have h2 := Sol78.card_sup_mul_card_inf' hLC
  have h3 : Nat.card (K ⊓ C : Subgroup G) ≤ Nat.card (L ⊓ C : Subgroup G) :=
    calc Nat.card (K ⊓ C : Subgroup G) ≤ Nat.card ((Open.fusionZStar ↥K).map K.subtype) :=
          Subgroup.card_le_of_le (inf_le_fusionZStar_of_not_le hKq hKres hKC hnt)
      _ = Nat.card ((Open.fusionZStar ↥L).map L.subtype) := hZ
      _ ≤ Nat.card (L ⊓ C : Subgroup G) :=
          Subgroup.card_le_of_le (le_inf (map_subtype_le _) (fusionZStar_map_le_coreActionKernel L))
  have hpos : 0 < Nat.card (K ⊓ C : Subgroup G) := Nat.card_pos
  have h4 : Nat.card (K ⊔ C : Subgroup G) * Nat.card (K ⊓ C : Subgroup G) <
      Nat.card (L ⊔ C : Subgroup G) * Nat.card (L ⊓ C : Subgroup G) :=
    calc Nat.card (K ⊔ C : Subgroup G) * Nat.card (K ⊓ C : Subgroup G) <
          Nat.card (L ⊔ C : Subgroup G) * Nat.card (K ⊓ C : Subgroup G) :=
          Nat.mul_lt_mul_of_pos_right hcardlt hpos
      _ ≤ Nat.card (L ⊔ C : Subgroup G) * Nat.card (L ⊓ C : Subgroup G) :=
          Nat.mul_le_mul_left _ h3
  rw [h1, h2, hcard] at h4
  exact lt_irrefl _ h4

theorem le_sup_coreActionKernel_of_outer_solvable {K L : Subgroup G}
    (hOut : Group.IsSolvable (OuterAutomorphisms.Outer (↥L ⧸ pPrimeCore 2 ↥L)))
    (hKperf : ⁅K, K⁆ = K) (hKL : K ≤ normalizer (L : Set G)) :
    K ≤ L ⊔ coreActionKernel L := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := hOut
  have : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr hKperf
  set action : ↥K →* MulAut (↥L ⧸ pPrimeCore 2 ↥L) :=
    (CFSG.FiveTransitive.CharacteristicAutomorphism.quotient (pPrimeCore 2 ↥L)).comp
      (L.normalizerMonoidHom.comp (inclusion hKL)) with haction
  intro k hk
  obtain ⟨q, hq⟩ := OuterAutomorphisms.perfect_action_inner action ⟨k, hk⟩
  obtain ⟨ℓ, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥L) q
  have hc : (ℓ : G)⁻¹ * k ∈ coreActionKernel L := by
    refine mem_coreActionKernel.mpr ⟨mul_mem (inv_mem (le_normalizer ℓ.2)) (hKL hk),
      fun j hj => ?_⟩
    have h1 := congrArg (fun α : MulAut (↥L ⧸ pPrimeCore 2 ↥L) =>
      α (QuotientGroup.mk' (pPrimeCore 2 ↥L) ⟨j, hj⟩)) hq
    simp only [haction, MonoidHom.coe_comp, Function.comp_apply,
      CFSG.FiveTransitive.CharacteristicAutomorphism.quotient_apply_mk, MulAut.conj_apply] at h1
    rw [← map_inv, ← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq] at h1
    have h2 : (k : G) * j⁻¹ * k⁻¹ * ((ℓ : G) * j * (ℓ : G)⁻¹) ∈
        (pPrimeCore 2 ↥L).map L.subtype := by
      refine ⟨_, h1, ?_⟩
      simp only [coe_subtype, coe_mul, coe_inv, normalizerMonoidHom_apply_apply_coe,
        coe_inclusion]
      group
    have hkN : k⁻¹ ∈ normalizer (((pPrimeCore 2 ↥L).map L.subtype : Subgroup G) : Set G) :=
      UnbalancedGS.normalizer_le_normalizer_map_of_characteristic L (pPrimeCore 2 ↥L)
        (inv_mem (hKL hk))
    have h3 := (mem_normalizer_iff.mp hkN _).mp h2
    rw [show j⁻¹ * ((ℓ : G)⁻¹ * k)⁻¹ * j * ((ℓ : G)⁻¹ * k) =
      k⁻¹ * ((k : G) * j⁻¹ * k⁻¹ * ((ℓ : G) * j * (ℓ : G)⁻¹)) * k⁻¹⁻¹ by group]
    exact h3
  rw [show k = (ℓ : G) * ((ℓ : G)⁻¹ * k) by group]
  exact mul_mem (mem_sup_left ℓ.2) (mem_sup_right hc)

theorem le_sup_coreActionKernel_of_schreier
    (hS : CFSG.LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (hG : KStarKProper G) {H K L : Subgroup G} (hLH : IsTwoComponentIn L H)
    (hLs : L ∈ solomonKStar G) (hKperf : ⁅K, K⁆ = K) (hKL : K ≤ normalizer (L : Set G)) :
    K ≤ L ⊔ coreActionKernel L := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQq : IsQuasisimple (↥L ⧸ pPrimeCore 2 ↥L) :=
    isQuasisimple_quotient_of_isPComponent hLH.1 hLH.2
  have : Group.IsPerfect (↥L ⧸ pPrimeCore 2 ↥L) := hQq.1
  have : IsSimpleGroup ((↥L ⧸ pPrimeCore 2 ↥L) ⧸ center (↥L ⧸ pPrimeCore 2 ↥L)) := hQq.2.1
  have : Group.IsSolvable (OuterAutomorphisms.Outer
      ((↥L ⧸ pPrimeCore 2 ↥L) ⧸ center (↥L ⧸ pPrimeCore 2 ↥L))) :=
    hS _ hQq.2.2 (catalog_coreQuotient_of_mem_solomonKStar hG hLH hLs)
  have : Group.IsSolvable (OuterAutomorphisms.Outer (↥L ⧸ pPrimeCore 2 ↥L)) :=
    OuterAutomorphisms.solvable_of_centerQuotient _
  exact le_sup_coreActionKernel_of_outer_solvable inferInstance hKperf hKL

theorem lemma313NarrowNPrimeInputFor_of_schreier
    (hS : CFSG.LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (h𝒜 : ∀ (G : Type) [Group G] [Finite G], 𝒜 G → KStarKProper G) :
    Lemma313NarrowNPrimeInputFor 𝒜 := by
  intro G _ _ hG N hN hKstar hCb K hK g hKg hβ1 hβ2 hN'
  exfalso
  obtain ⟨hKN', hnt, hin⟩ := hN' K hK
  have hLc : IsTwoComponentIn (conjugate K g) (conjugate N g) :=
    Sol76.isTwoComponentIn_map (MulAut.conj g⁻¹) hK.1
  have hLs : conjugate K g ∈ solomonKStar G := Sol76.conjugate_mem_solomonKStar hK.2 g
  have hKperf : ⁅K, K⁆ = K := UnbalancedCorr.commutator_eq_of_isPComponent hK.1.1 hK.1.2
  have hinner := le_sup_coreActionKernel_of_schreier hS (h𝒜 G hG) hLc hLs hKperf hKN'
  have hKq := isQuasisimple_quotient_of_isPComponent hK.1.1 hK.1.2
  have hKres := oddResidualIn_eq_self_of_isPComponent hK.1.1 hK.1.2
  set e : ↥K ≃* ↥(conjugate K g) :=
    K.equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective with he
  have hcard : Nat.card K = Nat.card (conjugate K g) := Nat.card_congr e.toEquiv
  have hZ : Nat.card ((Open.fusionZStar ↥K).map K.subtype) =
      Nat.card ((Open.fusionZStar ↥(conjugate K g)).map (conjugate K g).subtype) := by
    rw [card_map_of_injective K.subtype_injective,
      card_map_of_injective (conjugate K g).subtype_injective,
      ← FooteLit.fusionZStar_map_mulEquiv e, card_map_of_injective e.injective]
  exact hin hinner (le_sup_coreActionKernel_of_inner hKq hKres hKN' hnt hinner hcard hZ)

theorem lemma313NarrowInputFor_of_schreier
    (hS : CFSG.LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (hq : QuasisimpleTwoPartInput)
    (h𝒜 : ∀ (G : Type) [Group G] [Finite G], 𝒜 G → KStarKProper G) :
    Lemma313NarrowInputFor 𝒜 :=
  lemma313NarrowInputFor_of_nPrime_twoPart hq h𝒜 (lemma313NarrowNPrimeInputFor_of_schreier hS h𝒜)

end CFSG.ComponentClassification.Sol76T13
