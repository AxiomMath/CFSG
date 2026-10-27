module

public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigGood3

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Sol76T13

private theorem comm_of_sq_eq_one_aux {M : Type} [Group M] {A : Subgroup M}
    (hA2 : ∀ a ∈ A, a ^ 2 = 1) {a b : M} (ha : a ∈ A) (hb : b ∈ A) : a * b = b * a := by
  have hinv : ∀ x ∈ A, x⁻¹ = x := fun x hx =>
    inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hA2 x hx)
  calc a * b = (a * b)⁻¹ := (hinv _ (mul_mem ha hb)).symm
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by rw [hinv a ha, hinv b hb]

private theorem map_conj_map_conj_aux' {M : Type} [Group M] (E : Subgroup M) (g h : M) :
    (E.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      E.map (MulAut.conj (g * h)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  group

theorem le_of_forall_inf_centralizer_le {G : Type} [Group G] [Finite G] {O E L : Subgroup G}
    (hO : Odd (Nat.card O)) (hEO : E ≤ normalizer (O : Set G))
    (hE : CFSG.Open.IsElemAbelian 2 E) (hE8 : Nat.card E = 8)
    (hL : ∀ H : Subgroup G, H ≤ E → IsKleinFour H → O ⊓ centralizer (H : Set G) ≤ L) :
    O ≤ L := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ := Subgroup.conjMulDistribMulActionOfLeNormalizer E O hEO
  have : IsElementaryAbelian 2 E :=
    { toIsMulCommutative := hE.1
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun g =>
        Subtype.ext (hE.2 g g.2) }
  have : Nontrivial E := Finite.one_lt_card_iff_nontrivial.1 (by rw [hE8]; norm_num)
  have hp : ¬ 2 ∣ Nat.card O := fun h => (Nat.not_even_iff_odd.mpr hO) (even_iff_two_dvd.mpr h)
  have hgen := CFSG.SolvableHall.coprime_hyperplane_generation (A := E) (H := O) hp
  have hle : ⨆ (B : Subgroup E) (_ : B.index = 2), CFSG.fixedPointSubgroup B O ≤
      L.subgroupOf O := by
    refine iSup_le fun B => iSup_le fun hB => fun y hy => ?_
    have hHE : B.map E.subtype ≤ E := map_subtype_le B
    have hHc : Nat.card (B.map E.subtype) = 4 := by
      rw [Subgroup.card_map_of_injective E.subtype_injective]
      have h1 := Subgroup.card_mul_index B
      rw [hB, hE8] at h1
      omega
    have hH : IsKleinFour (B.map E.subtype) :=
      FooteLit.isKleinFour_of_card_eq_four hHc fun z hz => hE.2 z (hHE hz)
    have hyC : (y : G) ∈ centralizer ((B.map E.subtype : Subgroup G) : Set G) := by
      rw [mem_centralizer_iff]
      rintro _ ⟨b, hb, rfl⟩
      have h1 : (b : E) • y = y := hy ⟨b, hb⟩
      have h2 : (b : G) * y * (b : G)⁻¹ = y := congrArg Subtype.val h1
      show (b : G) * y = y * b
      calc (b : G) * y = (b : G) * y * (b : G)⁻¹ * b := by group
        _ = y * b := by rw [h2]
    exact hL _ hHE hH ⟨y.2, hyC⟩
  intro x hx
  have hx' : (⟨x, hx⟩ : O) ∈ (⊤ : Subgroup O) := mem_top _
  rw [← hgen] at hx'
  exact hle hx'

theorem eq_top_of_gamma_map_eq_top {M : Type} [Group M] [Finite M] {O : Subgroup M} [O.Normal]
    (hO : Odd (Nat.card O)) {T : Subgroup M} (hT : IsPGroup 2 T) {L : Subgroup M}
    (hOL : O ≤ L)
    (hN : ∀ Q : Subgroup M, Q ≤ T → 2 ≤ CFSG.Open.pRank 2 Q → normalizer (Q : Set M) ≤ L)
    (hΓ : CFSG.Open.properTwoGenCoreGamma (T.map (QuotientGroup.mk' O)) 2 = ⊤) : L = ⊤ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' O with hπ
  have hinj : ∀ x ∈ T, π x = 1 → x = 1 := by
    intro x hxT hx
    have hxO : x ∈ O := (QuotientGroup.eq_one_iff x).mp hx
    obtain ⟨n, hn⟩ := hT.exists_card_eq
    have hco : Nat.Coprime (orderOf x) (Nat.card O) :=
      Nat.Coprime.coprime_dvd_left (hn ▸ T.orderOf_dvd_natCard hxT)
        (Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hO))
    exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hco (O.orderOf_dvd_natCard hxO))
  have hcard : ∀ X : Subgroup M, X ≤ T → Nat.card (X.map π) = Nat.card X := by
    intro X hXT
    have hinj' : Function.Injective (π.comp X.subtype) :=
      (injective_iff_map_eq_one _).mpr fun x hx => Subtype.ext (hinj x (hXT x.2) hx)
    rw [show X.map π = (π.comp X.subtype).range by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]]
    exact Nat.card_congr (MonoidHom.ofInjective hinj').toEquiv.symm
  have hOn : normalizer (O : Set M) = ⊤ := Subgroup.normalizer_eq_top_iff.mpr inferInstance
  have hΓL : CFSG.Open.properTwoGenCoreGamma (T.map π) 2 ≤ L.map π := by
    refine (CFSG.ProperTwoGeneratedCore.gamma_le_iff _ _ 2).mpr fun Qb hQbT hQb nb hnb => ?_
    set Q₀ := T ⊓ Qb.comap π with hQ₀
    have hQ₀T : Q₀ ≤ T := inf_le_left
    have hmap : Q₀.map π = Qb := by
      refine le_antisymm ((Subgroup.map_mono inf_le_right).trans (Subgroup.map_comap_le _ _))
        fun q hq => ?_
      obtain ⟨t, htT, rfl⟩ := hQbT hq
      exact ⟨t, ⟨htT, hq⟩, rfl⟩
    have hQ₀ : 2 ≤ CFSG.Open.pRank 2 Q₀ := by
      obtain ⟨Eb, hEbQ, hEb, hEbc⟩ :=
        SectionRank.exists_isElemAbelian_card_of_le_pRank (p := 2) (k := 2) hQb
      set E := Q₀ ⊓ Eb.comap π with hE
      have hEQ₀ : E ≤ Q₀ := inf_le_left
      have hET : E ≤ T := hEQ₀.trans hQ₀T
      have hEmap : E.map π = Eb := by
        refine le_antisymm ((Subgroup.map_mono inf_le_right).trans (Subgroup.map_comap_le _ _))
          fun q hq => ?_
        have hq' : q ∈ Q₀.map π := by rw [hmap]; exact hEbQ hq
        obtain ⟨t, htQ, rfl⟩ := hq'
        exact ⟨t, ⟨htQ, hq⟩, rfl⟩
      have hEsq : ∀ x ∈ E, x ^ 2 = 1 := fun x hx =>
        hinj _ (pow_mem (hET hx) 2) (by rw [map_pow]; exact hEb.2 _ hx.2)
      refine SectionRank.le_pRank (by norm_num) hEQ₀
        ⟨⟨⟨fun a b => Subtype.ext (comm_of_sq_eq_one_aux hEsq a.2 b.2)⟩⟩, hEsq⟩ ?_
      rw [← hcard E hET, hEmap, hEbc]
    have hQ₀L : normalizer (Q₀ : Set M) ≤ L := hN Q₀ hQ₀T hQ₀
    have hQ₀L' : Q₀ ≤ L := le_normalizer.trans hQ₀L
    obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective O nb
    have hP : Qb.comap π = Q₀ ⊔ O := by
      refine le_antisymm (fun x hx => ?_) (sup_le inf_le_right fun x hx => ?_)
      · have hx' : π x ∈ Q₀.map π := by rw [hmap]; exact hx
        obtain ⟨q, hq, hqx⟩ := hx'
        have hqx' : q⁻¹ * x ∈ O := QuotientGroup.eq.mp hqx
        have e : x = q * (q⁻¹ * x) := by group
        rw [e]
        exact mul_mem (mem_sup_left hq) (mem_sup_right hqx')
      · show π x ∈ Qb
        have h1 : π x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
        rw [h1]
        exact one_mem _
    have hnP : n ∈ normalizer ((Q₀ ⊔ O : Subgroup M) : Set M) := by
      rw [← hP, mem_normalizer_iff]
      intro x
      show π x ∈ Qb ↔ π (n * x * n⁻¹) ∈ Qb
      rw [map_mul, map_mul, map_inv]
      exact mem_normalizer_iff.mp hnb (π x)
    have hA : Q₀.map (MulAut.conj n).toMonoidHom ≤ Q₀ ⊔ O := by
      rintro _ ⟨q, hq, rfl⟩
      exact (mem_normalizer_iff.mp hnP q).mp (mem_sup_left hq)
    obtain ⟨m, hmP, hm⟩ := exists_conj_le_of_sup_odd (M₀ := Q₀) (M := Q₀ ⊔ O) le_sup_left
      (fun x _ => by rw [hOn]; exact mem_top x) hO rfl hA ((hT.to_le hQ₀T).map _)
    have hmn : m * n ∈ normalizer (Q₀ : Set M) := by
      have hle : Q₀.map (MulAut.conj (m * n)).toMonoidHom ≤ Q₀ := by
        rw [← map_conj_map_conj_aux' Q₀ m n]
        exact hm
      exact mem_normalizer_iff_map_conj_eq.mpr (Subgroup.eq_of_le_of_card_ge hle
        (Subgroup.card_map_of_injective (MulAut.conj (m * n)).injective).ge)
    have h1 : π (m * n) ∈ L.map π := ⟨m * n, hQ₀L hmn, rfl⟩
    have h2 : π m ∈ L.map π := by
      have hm' : π m ∈ Q₀.map π := by
        rw [hmap]
        rw [← hP] at hmP
        exact hmP
      obtain ⟨q, hq, hqm⟩ := hm'
      exact ⟨q, hQ₀L' hq, hqm⟩
    have e : π n = (π m)⁻¹ * π (m * n) := by rw [map_mul]; group
    rw [e]
    exact mul_mem (inv_mem h2) h1
  have hLtop : L.map π = ⊤ := top_le_iff.mp (by rw [← hΓ]; exact hΓL)
  have hcomap := Subgroup.comap_map_eq π L
  rw [hLtop, Subgroup.comap_top, QuotientGroup.ker_mk', sup_eq_left.mpr hOL] at hcomap
  exact hcomap.symm

variable {G : Type} [Group G] [Finite G]

private theorem pRank_le_pRank_subgroupOf_aux {Q Y : Subgroup G} (hQY : Q ≤ Y) :
    CFSG.Open.pRank 2 Q ≤ CFSG.Open.pRank 2 (Q.subgroupOf Y) := by
  obtain ⟨E, hEQ, hE, hcard⟩ := SectionRank.exists_pRank (by norm_num : 1 < 2) Q
  have := hE.1
  refine SectionRank.le_pRank_of_injective (A := E) (by norm_num) (fun a b => mul_comm' a b)
    (fun a => Subtype.ext (by rw [Subgroup.coe_pow, hE.2 a a.2, Subgroup.coe_one])) hcard
    (Subgroup.inclusion (hEQ.trans hQY)) (Subgroup.inclusion_injective _) ?_
  rintro _ ⟨a, rfl⟩
  exact hEQ a.2

theorem exists_sylow_gamma_eq_top {Y K : Subgroup G} (hKY : K ≤ Y)
    (hYK : Y ≤ normalizer (K : Set G)) (h3 : 3 ≤ CFSG.Open.pRank 2 K)
    (hΓ : ∀ Tb : Sylow 2 (↥K ⧸ pPrimeCore 2 ↥K),
      CFSG.Open.properTwoGenCoreGamma (Tb : Subgroup (↥K ⧸ pPrimeCore 2 ↥K)) 2 = ⊤) :
    ∃ S' : Sylow 2 ↥Y, CFSG.Open.properTwoGenCoreGamma (S' : Subgroup ↥Y) 2 = ⊤ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set KY := K.subgroupOf Y with hKYdef
  have hKYn : KY.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKY).mpr hYK
  set e : ↥KY ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKY
  obtain ⟨P⟩ : Nonempty (Sylow 2 ↥KY) := inferInstance
  set TY : Subgroup ↥Y := (P : Subgroup ↥KY).map KY.subtype with hTYdef
  set T₀ : Sylow 2 ↥K := P.mapSurjective (f := e.toMonoidHom) e.surjective
  set T : Subgroup G := (T₀ : Subgroup ↥K).map K.subtype with hTdef
  have hT₀ : (T₀ : Subgroup ↥K) = (P : Subgroup ↥KY).map e.toMonoidHom := rfl
  have hTY : TY.map Y.subtype = T := by
    rw [hTYdef, hTdef, hT₀, Subgroup.map_map, Subgroup.map_map]
    exact congrArg (fun f => Subgroup.map f (P : Subgroup ↥KY)) (MonoidHom.ext fun x => rfl)
  have hTK : T ≤ K := map_subtype_le _
  have hT3 : 3 ≤ CFSG.Open.pRank 2 T := by
    have h1 : CFSG.Open.pRank 2 K = CFSG.Open.pRank 2 (⊤ : Subgroup ↥K) :=
      SectionRank.pRank_eq_pRank_top_subgroup K
    have h2 : CFSG.Open.pRank 2 (T₀ : Subgroup ↥K) = CFSG.Open.pRank 2 (⊤ : Subgroup ↥K) :=
      CFSG.ProperTwoGeneratedCore.sylow_two_rank_eq T₀
    have h4 : CFSG.Open.pRank 2 (T₀ : Subgroup ↥K) ≤ CFSG.Open.pRank 2 T :=
      SectionRank.pRank_le_map (by norm_num : 1 < 2) K.subtype K.subtype_injective _
    omega
  obtain ⟨E, hET, hEe, hEc⟩ :=
    SectionRank.exists_isElemAbelian_card_of_le_pRank (p := 2) (k := 3) hT3
  have hTY2 : IsPGroup 2 TY := P.isPGroup'.map _
  obtain ⟨S', hS'⟩ := hTY2.exists_le_sylow
  refine ⟨S', ?_⟩
  set Γ := CFSG.Open.properTwoGenCoreGamma (S' : Subgroup ↥Y) 2 with hΓdef
  have htr : ∀ Q : Subgroup G, Q ≤ T → 2 ≤ CFSG.Open.pRank 2 Q →
      ∀ y : ↥Y, (y : G) ∈ normalizer (Q : Set G) → y ∈ Γ := by
    intro Q hQT hQ y hy
    have hQY : Q ≤ Y := (hQT.trans hTK).trans hKY
    have hQS : Q.subgroupOf Y ≤ S' := by
      intro q hq
      have hq' : (q : G) ∈ TY.map Y.subtype := by rw [hTY]; exact hQT hq
      obtain ⟨t, ht, htq⟩ := hq'
      have htq' : t = q := Subtype.ext htq
      exact hS' (htq' ▸ ht)
    have hQr : 2 ≤ CFSG.Open.pRank 2 (Q.subgroupOf Y) :=
      hQ.trans (pRank_le_pRank_subgroupOf_aux hQY)
    have hyN : y ∈ normalizer ((Q.subgroupOf Y : Subgroup ↥Y) : Set ↥Y) := by
      rw [← Subgroup.subgroupOf_normalizer_eq hQY]
      exact hy
    exact (CFSG.ProperTwoGeneratedCore.gamma_le_iff _ Γ 2).mp le_rfl _ hQS hQr hyN
  have hO : oddCoreIn K ≤ Γ.map Y.subtype := by
    refine le_of_forall_inf_centralizer_le (Nat.coprime_two_left.mp (coprime_card_oddCoreIn K))
      ((hET.trans hTK).trans (le_normalizer_oddCoreIn K)) hEe (by rw [hEc]; norm_num)
      fun H hHE hH x hx => ?_
    have hxY : x ∈ Y := hKY (map_subtype_le _ hx.1)
    have hHr : 2 ≤ CFSG.Open.pRank 2 H :=
      SectionRank.le_pRank (by norm_num) le_rfl (isElemAbelian_of_isKleinFour hH)
        (by rw [hH.card_four]; norm_num)
    exact ⟨⟨x, hxY⟩, htr H (hHE.trans hET) hHr ⟨x, hxY⟩
      (Subgroup.centralizer_le_normalizer _ hx.2), rfl⟩
  have hK : K ≤ Γ.map Y.subtype := by
    have hL : (Γ.map Y.subtype).comap K.subtype = ⊤ := by
      refine eq_top_of_gamma_map_eq_top (O := pPrimeCore 2 ↥K)
        (Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := ↥K))) T₀.isPGroup'
        (fun x hx => hO ⟨x, hx, rfl⟩) (fun Q hQ hQr k hk => ?_)
        (hΓ (T₀.mapSurjective (QuotientGroup.mk'_surjective (pPrimeCore 2 ↥K))))
      have hkN : (k : G) ∈ normalizer ((Q.map K.subtype : Subgroup G) : Set G) :=
        Subgroup.le_normalizer_map K.subtype ⟨k, hk, rfl⟩
      have hQr' : 2 ≤ CFSG.Open.pRank 2 (Q.map K.subtype) :=
        hQr.trans (SectionRank.pRank_le_map (by norm_num) K.subtype K.subtype_injective Q)
      exact ⟨⟨k, hKY k.2⟩, htr _ (Subgroup.map_mono hQ) hQr' ⟨k, hKY k.2⟩ hkN, rfl⟩
    intro k hk
    have hk' : (⟨k, hk⟩ : ↥K) ∈ (Γ.map Y.subtype).comap K.subtype := by
      rw [hL]; exact mem_top _
    exact hk'
  have hfr := Sylow.normalizer_sup_eq_top P
  rw [eq_top_iff, ← hfr]
  refine sup_le (fun y hy => ?_) fun y hy => ?_
  · have hyT : (y : G) ∈ normalizer (T : Set G) := by
      rw [← hTY]
      exact Subgroup.le_normalizer_map Y.subtype ⟨y, hy, rfl⟩
    exact htr T le_rfl (by omega) y hyT
  · obtain ⟨z, hz, hzy⟩ := hK hy
    have hzy' : z = y := Subtype.ext hzy
    exact hzy' ▸ hz

variable {N K K' : Subgroup G}

theorem mem_normalizer_of_ncard_eq_two (hr : (kStarComponents N).ncard = 2)
    (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N) (hne : K ≠ K') {g : G}
    (hgN : g ∈ N) (hgK' : g ∈ normalizer (K' : Set G)) : g ∈ normalizer (K : Set G) := by
  have hfin : (kStarComponents N).Finite := Set.finite_of_ncard_ne_zero (by omega)
  have hpair : ({K, K'} : Set (Subgroup G)) = kStarComponents N :=
    Set.eq_of_subset_of_ncard_le (Set.insert_subset hK (Set.singleton_subset_iff.mpr hK'))
      (by rw [hr, Set.ncard_pair hne]) hfin
  have hJ : K.map (MulAut.conj g).toMonoidHom ∈ kStarComponents N :=
    ⟨Sol76.isTwoComponentIn_map_conj hK.1 (le_normalizer hgN),
      Sol76.map_mem_solomonKStar (MulAut.conj g) hK.2⟩
  rw [← hpair] at hJ
  rcases hJ with hJ | hJ
  · exact mem_normalizer_iff_map_conj_eq.mpr hJ
  · exfalso
    apply hne
    have h1 : K'.map (MulAut.conj g).toMonoidHom = K' := mem_normalizer_iff_map_conj_eq.mp hgK'
    exact Subgroup.map_injective (MulAut.conj g).injective (hJ.trans h1.symm)

theorem exists_sylow_gamma_eq_top_of_mem_kStarComponents (hr : (kStarComponents N).ncard = 2)
    (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N) (hne : K ≠ K')
    (h3 : 3 ≤ CFSG.Open.pRank 2 K)
    (hΓ : ∀ Tb : Sylow 2 (↥K ⧸ pPrimeCore 2 ↥K),
      CFSG.Open.properTwoGenCoreGamma (Tb : Subgroup (↥K ⧸ pPrimeCore 2 ↥K)) 2 = ⊤) :
    ∃ S' : Sylow 2 ↥((oddTwoCoreIn N ⊔ twoLayerIn N) ⊓ coreActionKernel K'),
      CFSG.Open.properTwoGenCoreGamma
        (S' : Subgroup ↥((oddTwoCoreIn N ⊔ twoLayerIn N) ⊓ coreActionKernel K')) 2 = ⊤ := by
  refine exists_sylow_gamma_eq_top
    (le_inf ((le_twoLayerIn_of_isTwoComponentIn hK.1).trans le_sup_right)
      (le_coreActionKernel_of_ne hK' hK hne.symm)) (fun g hg => ?_) h3 hΓ
  have hgN : g ∈ N := sup_le (map_subtype_le _) (map_subtype_le _) hg.1
  exact mem_normalizer_of_ncard_eq_two hr hK hK' hne hgN (mem_coreActionKernel.mp hg.2).1

end CFSG.ComponentClassification.Sol76.Sig
