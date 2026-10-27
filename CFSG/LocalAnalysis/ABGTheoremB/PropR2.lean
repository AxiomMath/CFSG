module

public import CFSG.Adapters.QiuzhenLegacy.FeitThompson.Gorenstein.RelativeZJ
public import CFSG.LocalAnalysis.ABGTheoremB.ZJCovering
public import CFSG.LocalAnalysis.ABGTheoremB.IV7Data

public section

namespace CFSG.ABGTheoremB

open CFSG.QuasiDihedralFusion CFSG.ABGLocalTools CFSG.ABGTheoremB.RelativeZJ
open scoped Pointwise

universe u

section General

variable {G : Type u} [Group G] [Finite G]

private theorem prr2_thompsonCenter_subgroupOf_map {Y P : Subgroup G} (hPY : P ≤ Y) :
    (thompsonCenter (G := Y) (P.subgroupOf Y)).map Y.subtype = thompsonCenter (G := G) P := by
  have h1 := thompsonCenter_top_map_subtype (G := Y) (P.subgroupOf Y)
  have h2 := thompsonCenter_top_map_subtype (G := G) P
  have h3 := thompsonCenter_top_map_mulEquiv (G := P.subgroupOf Y)
    (Subgroup.subgroupOfEquivOfLe hPY)
  rw [← h1, ← h2, ← h3, Subgroup.map_map, Subgroup.map_map]
  rfl

omit [Finite G] in
private theorem prr2_map_normalizer {Y : Subgroup G} (Q : Subgroup Y) :
    (Subgroup.normalizer (Q : Set Y)).map Y.subtype =
      Y ⊓ Subgroup.normalizer ((Q.map Y.subtype : Subgroup G) : Set G) := by
  have hle : Q.map Y.subtype ≤ Y := Subgroup.map_subtype_le Q
  have hQ : (Q.map Y.subtype).subgroupOf Y = Q :=
    Subgroup.comap_map_eq_self_of_injective Y.subtype_injective Q
  have h := Subgroup.subgroupOf_normalizer_eq hle
  rw [hQ] at h
  rw [← h, Subgroup.subgroupOf_map_subtype, inf_comm]

variable {p : ℕ} [Fact p.Prime]

private theorem prr2_mk'_injective {V : Subgroup G} (hV : IsPGroup p V) :
    Function.Injective ((QuotientGroup.mk' (pPrimeCore p G)).comp V.subtype) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  have hxM : (x : G) ∈ pPrimeCore p G := (QuotientGroup.eq_one_iff (x : G)).mp hx
  have hcop : Nat.Coprime (Nat.card V) (Nat.card (pPrimeCore p G)) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hV
    rw [hn]
    exact (pPrimeCore_coprime_card (G := G) (p := p)).pow_left n
  have hinf : V ⊓ pPrimeCore p G = ⊥ := (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
  have hx' : (x : G) ∈ V ⊓ pPrimeCore p G := ⟨x.2, hxM⟩
  rw [hinf, Subgroup.mem_bot] at hx'
  exact (Subgroup.mem_bot).mpr (Subtype.ext hx')

private theorem prr2_thompsonCenter_map_mk' {V : Subgroup G} (hV : IsPGroup p V) :
    (thompsonCenter (G := G) V).map (QuotientGroup.mk' (pPrimeCore p G)) =
      thompsonCenter (G := G ⧸ pPrimeCore p G) (V.map (QuotientGroup.mk' (pPrimeCore p G))) := by
  set q := QuotientGroup.mk' (pPrimeCore p G)
  have hqinj : Function.Injective (q.comp V.subtype) := prr2_mk'_injective hV
  let f : V →* (V.map q) :=
    (q.comp V.subtype).codRestrict (V.map q) (fun x => Subgroup.mem_map_of_mem q x.2)
  let e : V ≃* (V.map q) := by
    refine MulEquiv.ofBijective f ⟨fun a b hab => hqinj (congrArg Subtype.val hab), ?_⟩
    intro x
    obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.mp x.2
    exact ⟨⟨y, hy⟩, Subtype.ext hxy⟩
  have hcomp : ((Subgroup.subtype (V.map q)).comp e.toMonoidHom) = q.comp V.subtype := rfl
  calc
    (thompsonCenter (G := G) V).map q =
        ((thompsonCenter (G := V) (⊤ : Subgroup V)).map V.subtype).map q := by
      rw [thompsonCenter_top_map_subtype]
    _ = ((thompsonCenter (G := V) (⊤ : Subgroup V)).map e.toMonoidHom).map
          (Subgroup.subtype (V.map q)) := by
      rw [Subgroup.map_map, Subgroup.map_map, hcomp]
    _ = (thompsonCenter (G := V.map q) (⊤ : Subgroup (V.map q))).map
          (Subgroup.subtype (V.map q)) := by
      rw [thompsonCenter_top_map_mulEquiv]
    _ = thompsonCenter (G := G ⧸ pPrimeCore p G) (V.map q) :=
      thompsonCenter_top_map_subtype (G := G ⧸ pPrimeCore p G) (V.map q)

omit [Finite G] [Fact p.Prime] in
private theorem prr2_le_pPrimeCoreIn {X K : Subgroup G} (hXK : X ≤ K)
    (hKX : K ≤ Subgroup.normalizer (X : Set G)) (hX : Nat.Coprime p (Nat.card X)) :
    X ≤ pPrimeCoreIn p K := by
  have hn : (X.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXK).mpr hKX
  have hc : Nat.Coprime p (Nat.card (X.subgroupOf K)) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXK).toEquiv]
  have hle : X.subgroupOf K ≤ CFSG.pPrimeCore p K := le_sSup ⟨hn, hc⟩
  intro x hx
  exact ⟨⟨x, hXK hx⟩, hle hx, rfl⟩

private theorem prr2_mem_normalizer_of_conj_mem {J : Subgroup G} {g : G}
    (h : ∀ y ∈ J, g * y * g⁻¹ ∈ J) : g ∈ Subgroup.normalizer (J : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨y, hy, rfl⟩
    exact h y hy
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]

private theorem prr2_normalizer_le_normalizer_map {Y : Subgroup G} (A : Subgroup Y)
    [hA : A.Characteristic] :
    Subgroup.normalizer (Y : Set G) ≤
      Subgroup.normalizer ((A.map Y.subtype : Subgroup G) : Set G) := by
  intro g hg
  apply prr2_mem_normalizer_of_conj_mem
  rintro _ ⟨a, ha, rfl⟩
  have hfix := hA.fixed (Subgroup.normalizerMonoidHom Y ⟨g, hg⟩)
  have hmem : a ∈ Subgroup.comap (Subgroup.normalizerMonoidHom Y ⟨g, hg⟩).toMonoidHom A := by
    rw [hfix]
    exact ha
  refine ⟨_, hmem, ?_⟩
  change (((Subgroup.normalizerMonoidHom Y ⟨g, hg⟩) a : Y) : G) = g * a * g⁻¹
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe]

private theorem prr2_pPrimeCoreIn_le {O K : Subgroup G} (hOK : O ≤ K)
    (hKO : K ≤ Subgroup.normalizer (O : Set G)) : pPrimeCoreIn p O ≤ pPrimeCoreIn p K := by
  refine prr2_le_pPrimeCoreIn ((pPrimeCoreIn_le p O).trans hOK)
    (hKO.trans (prr2_normalizer_le_normalizer_map (CFSG.pPrimeCore p O))) ?_
  rw [pPrimeCoreIn, Subgroup.card_map_of_injective O.subtype_injective]
  exact CFSG.pPrimeCore_coprime_card

end General

namespace Setting

variable {G : Type u} [Group G] [Finite G] (σ : Setting G)

theorem propR2 (hσ : σ.IsValid) {K U : Subgroup G}
    (hK : K ∈ σ.familyMstar σ.p) (hU : U ∈ signalizers K σ.D σ.p)
    (hUO : IsSylowOf σ.p (U ⊓ oddCoreIn K) (oddCoreIn K))
    (h_IV_9_1 : PConstrainedWithin σ.p K (oddCore K))
    (h_II_6_1 : IsPStable σ.p K)
    (h_R_2_3 : ∀ L : Subgroup G, oddCoreIn K < L → L ≤ K → K ≤ Subgroup.normalizer (L : Set G) →
      K ≤ L ⊔ (K ⊓ Subgroup.normalizer ((oddCoreIn K ⊔ U : Subgroup G) : Set G))) :
    pPrimeCoreIn σ.p K ⊔ (K ⊓ Subgroup.normalizer (thompsonCenter (G := G) U : Set G)) = K := by
  have : Fact σ.p.Prime := ⟨hσ.p_prime⟩
  have hp2 : σ.p ≠ 2 := hσ.p_ne_two
  set Z := thompsonCenter (G := G) U
  obtain ⟨hUK, hUp, -, -⟩ := hU
  obtain ⟨⟨X₀, hX₀, hX₀p, hKX₀⟩, -, -, hModd⟩ := hK
  have hOK : oddCoreIn K ≤ K := oddCoreIn_le K
  have hKO : K ≤ Subgroup.normalizer ((oddCoreIn K : Subgroup G) : Set G) :=
    le_normalizer_oddCoreIn K
  have hO : Odd (Nat.card (oddCoreIn K)) := odd_card_oddCoreIn K
  have hX₀odd : Odd (Nat.card X₀) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hX₀p
    rw [hk]
    exact (hσ.p_prime.eq_two_or_odd'.resolve_left hp2).pow
  have hX₀N : K ≤ Subgroup.normalizer (X₀ : Set G) := hKX₀.le
  have hX₀O : X₀ ≤ oddCoreIn K := by
    rw [hKX₀]
    exact le_oddCoreIn Subgroup.le_normalizer le_rfl hX₀odd
  obtain ⟨-, -, hRa⟩ := zjCovering_sup hp2 hOK hKO hO hUK hUp hUO hX₀ hX₀p hX₀O hX₀N
  have hRb := zjCovering_normalizer_le hp2 hOK hKO hO hUK hUp hUO hX₀ hX₀p hX₀O hX₀N
  have hR1 : oddCoreIn K ≤ pPrimeCoreIn σ.p K ⊔ (K ⊓ Subgroup.normalizer (Z : Set G)) :=
    calc oddCoreIn K ≤ oddCoreIn K ⊔ U := le_sup_left
      _ = _ := hRa.symm
      _ ≤ _ := sup_le_sup (prr2_pPrimeCoreIn_le hOK hKO) (inf_le_inf_right _ (sup_le hOK hUK))
  set U' : Subgroup K := U.subgroupOf K
  have hU'p : IsPGroup σ.p U' := hUp.comap_subtype
  set Z' : Subgroup K := thompsonCenter (G := K) U'
  have hZ'map : Z'.map K.subtype = Z := prr2_thompsonCenter_subgroupOf_map hUK
  have hNmap : (Subgroup.normalizer (Z' : Set K)).map K.subtype =
      K ⊓ Subgroup.normalizer (Z : Set G) := by
    rw [prr2_map_normalizer, hZ'map]
  set M : Subgroup K := CFSG.pPrimeCore σ.p K
  have hMO : M ≤ oddCore K := by
    apply le_oddCore_of_normal (CFSG.pPrimeCore_normal (p := σ.p) (G := K))
    rw [← Subgroup.card_map_of_injective K.subtype_injective]
    exact hModd
  have hR1' : oddCore K ≤ M ⊔ Subgroup.normalizer (Z' : Set K) := by
    rw [← Subgroup.map_le_map_iff_of_injective K.subtype_injective, Subgroup.map_sup, hNmap]
    exact hR1
  have hsylO : IsSylowOf σ.p (U' ⊓ oddCore K) (oddCore K) := by
    have hmap : (U' ⊓ oddCore K).map K.subtype = U ⊓ oddCoreIn K := by
      rw [Subgroup.map_inf_eq _ _ _ K.subtype_injective, Subgroup.subgroupOf_map_subtype]
      change U ⊓ K ⊓ oddCoreIn K = U ⊓ oddCoreIn K
      rw [inf_assoc, inf_eq_right.mpr hOK]
    rw [← isSylowOf_map_subtype_iff K, hmap]
    exact hUO
  have hsyl : IsSylowOf σ.p (U' ⊓ Op_p'p σ.p K) (Op_p'p σ.p K) := by
    have h := hsylO.inf_of_le_normalizer h_IV_9_1.1
      (by rw [Subgroup.normalizer_eq_top]; exact le_top)
    rwa [inf_assoc, inf_eq_right.mpr h_IV_9_1.1] at h
  set q : K →* K ⧸ M := QuotientGroup.mk' M with hqdef
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective M
  set Ubar : Subgroup (K ⧸ M) := U'.map q
  have hZbar : Z'.map q = thompsonCenter (G := K ⧸ M) Ubar := prr2_thompsonCenter_map_mk' hU'p
  have hNq : (Subgroup.normalizer (Z' : Set K)).map q ≤
      Subgroup.normalizer ((thompsonCenter (G := K ⧸ M) Ubar : Subgroup (K ⧸ M)) :
        Set (K ⧸ M)) := by
    rw [← hZbar]
    exact Subgroup.le_normalizer_map q
  set Ostar : Subgroup (K ⧸ M) := (oddCore K).map q with hOstardef
  have hOn : Ostar.Normal := (inferInstance : (oddCore K).Normal).map q hq
  have hcomapO : Ostar.comap q = oddCore K := by
    rw [hOstardef, hqdef, QuotientGroup.comap_map_mk', sup_eq_right.mpr hMO]
  have hOZ : Ostar ≤ Subgroup.normalizer
      ((thompsonCenter (G := K ⧸ M) Ubar : Subgroup (K ⧸ M)) : Set (K ⧸ M)) := by
    refine (Subgroup.map_mono hR1').trans ?_
    rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
    exact hNq
  have hUbarO : Ubar ⊓ Ostar = (U' ⊓ oddCore K).map q := by
    apply le_antisymm
    · rintro x ⟨⟨u, hu, rfl⟩, hx⟩
      obtain ⟨o, ho, hox⟩ := Subgroup.mem_map.mp hx
      have hmem : o / u ∈ M := (QuotientGroup.eq_iff_div_mem).1 hox
      have hu' : u ∈ oddCore K := by
        have h := (oddCore K).mul_mem ((oddCore K).inv_mem (hMO hmem)) ho
        simpa [div_eq_mul_inv, mul_assoc] using h
      exact ⟨u, ⟨hu, hu'⟩, rfl⟩
    · exact le_inf (Subgroup.map_mono inf_le_left) (Subgroup.map_mono inf_le_right)
  have hsylbar : IsSylowOf σ.p (Ubar ⊓ Ostar) Ostar := by
    rw [hUbarO, isSylowOf_iff]
    obtain ⟨-, hP, hdvd⟩ := isSylowOf_iff.mp hsylO
    refine ⟨Subgroup.map_mono inf_le_right, hP.map q, fun h => hdvd ?_⟩
    rw [Subgroup.relIndex_map_map, QuotientGroup.ker_mk', sup_eq_left.mpr hMO] at h
    exact h.trans (Subgroup.relIndex_dvd_of_le_left _ le_sup_left)
  have hcorebar : CFSG.pCore σ.p ((K ⧸ M) ⧸ Ostar) = ⊥ := by
    set φ : K →* (K ⧸ M) ⧸ Ostar := (QuotientGroup.mk' Ostar).comp q
    have hφs : Function.Surjective φ := (QuotientGroup.mk'_surjective Ostar).comp hq
    set X : Subgroup K := (CFSG.pCore σ.p ((K ⧸ M) ⧸ Ostar)).comap φ
    have hXn : X.Normal := (CFSG.pCore_normal (p := σ.p) (G := (K ⧸ M) ⧸ Ostar)).comap φ
    have hXO : ∀ x ∈ X, x ^ 2 = 1 → x ∈ oddCore K := by
      intro x hx hx2
      have h1 : φ x = 1 :=
        RelativeZJ.rzj_eq_one_of_mem_pGroup_sq_eq_one hp2 _
          (CFSG.pCore_isPGroup (p := σ.p) (G := (K ⧸ M) ⧸ Ostar)) hx
          (by rw [← map_pow, hx2, map_one])
      have h2 : q x ∈ Ostar := (QuotientGroup.eq_one_iff (q x)).mp h1
      rw [← hcomapO]
      exact h2
    have hXodd : Odd (Nat.card X) := by
      rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
      intro h2
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := X) 2 h2
      have hx1 : x ^ 2 = 1 := by
        rw [← hx]
        exact pow_orderOf_eq_one x
      have hx2 : (x : K) ^ 2 = 1 := by simpa using congrArg Subtype.val hx1
      have hdvd : orderOf (x : K) ∣ Nat.card (oddCore K) :=
        Subgroup.orderOf_dvd_natCard _ (hXO x x.2 hx2)
      rw [Subgroup.orderOf_coe, hx] at hdvd
      exact (Nat.not_even_iff_odd.mpr (CFSG.ABGTheoremB.odd_card_oddCore K))
        (even_iff_two_dvd.mpr hdvd)
    have hXle : X ≤ oddCore K := le_oddCore_of_normal hXn hXodd
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨k, rfl⟩ := hφs y
    have hk : k ∈ oddCore K := hXle hy
    rw [Subgroup.mem_bot]
    exact (QuotientGroup.eq_one_iff (q k)).mpr (Subgroup.mem_map_of_mem q hk)
  have hFr : ∀ (L : Subgroup (K ⧸ M)) [L.Normal], Ostar ≤ L →
      (IsSylowOf σ.p (Ubar ⊓ L) L ∧
          CFSG.pCore σ.p ((K ⧸ M) ⧸ L) ≤ Ubar.map (QuotientGroup.mk' L)) ∨
        L ⊔ Subgroup.normalizer
          ((thompsonCenter (G := K ⧸ M) Ubar : Subgroup (K ⧸ M)) : Set (K ⧸ M)) = ⊤ := by
    intro L hL hOL
    obtain rfl | hlt := eq_or_lt_of_le hOL
    · exact Or.inl ⟨hsylbar, hcorebar.le.trans bot_le⟩
    · right
      have hOL₁ : oddCore K < L.comap q := by
        rw [← hcomapO]
        exact (Subgroup.comap_lt_comap_of_surjective hq).mpr hlt
      have hL₂ : oddCoreIn K < (L.comap q).map K.subtype :=
        (Subgroup.map_lt_map_iff_of_injective K.subtype_injective).mpr hOL₁
      have hKL₂ : K ≤ Subgroup.normalizer (((L.comap q).map K.subtype : Subgroup G) : Set G) :=
        CFSG.ABGTheoremB.le_normalizer_map_subtype K (L.comap q)
      have h2 : K ≤ (L.comap q).map K.subtype ⊔ (K ⊓ Subgroup.normalizer (Z : Set G)) :=
        (h_R_2_3 _ hL₂ (Subgroup.map_subtype_le _) hKL₂).trans
          (sup_le le_sup_left (hRb.trans (sup_le le_sup_right (hL₂.le.trans le_sup_left))))
      have h3 : (⊤ : Subgroup K) ≤ L.comap q ⊔ Subgroup.normalizer (Z' : Set K) := by
        rw [← Subgroup.map_le_map_iff_of_injective K.subtype_injective, Subgroup.map_sup, hNmap,
          ← MonoidHom.range_eq_map, Subgroup.range_subtype]
        exact h2
      apply top_le_iff.mp
      calc (⊤ : Subgroup (K ⧸ M)) = (⊤ : Subgroup K).map q :=
            (Subgroup.map_top_of_surjective q hq).symm
        _ ≤ (L.comap q ⊔ Subgroup.normalizer (Z' : Set K)).map q := Subgroup.map_mono h3
        _ = L ⊔ (Subgroup.normalizer (Z' : Set K)).map q := by
            rw [Subgroup.map_sup, Subgroup.map_comap_eq_self_of_surjective hq]
        _ ≤ _ := sup_le_sup_left hNq _
  have hfac := relative_zj_factorization hp2 U' hU'p h_IV_9_1.2 hsyl
    (relativeStable_of_isPStable hU'p h_II_6_1) Ostar hOn hOZ hFr
  have h := congrArg (Subgroup.map K.subtype) hfac
  rw [Subgroup.map_sup, hNmap, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
  exact h

end Setting

end CFSG.ABGTheoremB
