module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5FirstConn
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5FirstDefs
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5TwoCen

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS CFSG.ABGLocalTools CFSG.OddStandard.Solomon75.Sec5Two

open scoped commutatorElement

section Quotient

variable {L : Type} [Group L] [Finite L] {N : Subgroup L} [N.Normal]

private theorem fg_disjoint {S : Subgroup L} (hS : IsPGroup 2 S) (hN : Odd (Nat.card N)) :
    Disjoint S N := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hS
  refine Subgroup.disjoint_of_coprime_natCard ?_
  rw [hk]
  exact Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hN)

private theorem fg_injOn {S : Subgroup L} (hd : Disjoint S N) :
    Set.InjOn (QuotientGroup.mk' N) (S : Set L) := by
  intro x hx y hy hxy
  have h1 : x⁻¹ * y ∈ N := QuotientGroup.eq.1 hxy
  have h2 : x⁻¹ * y ∈ S := S.mul_mem (S.inv_mem hx) hy
  have h3 : x⁻¹ * y ∈ S ⊓ N := ⟨h2, h1⟩
  rw [hd.eq_bot] at h3
  exact inv_mul_eq_one.1 (Subgroup.mem_bot.1 h3)

private theorem fg_card_map {S : Subgroup L} (hd : Disjoint S N) :
    Nat.card (S.map (QuotientGroup.mk' N)) = Nat.card S :=
  (Nat.card_congr (Set.equivOfEq (Subgroup.coe_map _ _))).trans
    (Nat.card_image_of_injOn (fg_injOn hd))

private theorem fg_two_le_pRank_iff {Q : Subgroup L} :
    2 ≤ Open.pRank 2 Q ↔ ∃ E : Subgroup L, E ≤ Q ∧ Open.IsElemAbelian 2 E ∧ Nat.card E = 4 := by
  constructor
  · intro h
    obtain ⟨E, hEQ, hE, hcard⟩ := CFSG.SectionRank.exists_pRank (p := 2) (by norm_num) Q
    have h4 : 4 ≤ Nat.card E := by
      rw [hcard]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ Open.pRank 2 Q := Nat.pow_le_pow_right (by norm_num) h
    obtain ⟨H, hHE, hH, hH4⟩ := exists_fourSub_of_le_card hE h4
    exact ⟨H, hHE.trans hEQ, hH, hH4⟩
  · rintro ⟨E, hEQ, hE, h4⟩
    exact CFSG.SectionRank.le_pRank (p := 2) (by norm_num) hEQ hE (by rw [h4]; norm_num)

private theorem fg_two_le_pRank_map {Q : Subgroup L} (hQ : IsPGroup 2 Q) (hN : Odd (Nat.card N))
    (h : 2 ≤ Open.pRank 2 Q) : 2 ≤ Open.pRank 2 (Q.map (QuotientGroup.mk' N)) := by
  obtain ⟨E, hEQ, hE, hE4⟩ := fg_two_le_pRank_iff.1 h
  have hd : Disjoint E N := fg_disjoint (hQ.to_le hEQ) hN
  refine fg_two_le_pRank_iff.2 ⟨E.map (QuotientGroup.mk' N), Subgroup.map_mono hEQ,
    CFSG.SectionRank.isElemAbelian_map hE _, ?_⟩
  rw [fg_card_map hd, hE4]

private theorem fg_two_le_pRank_of_map {Q : Subgroup L} (hQ : IsPGroup 2 Q)
    (hN : Odd (Nat.card N)) (h : 2 ≤ Open.pRank 2 (Q.map (QuotientGroup.mk' N))) :
    2 ≤ Open.pRank 2 Q := by
  obtain ⟨Eb, hEbQ, hEb, hEb4⟩ := fg_two_le_pRank_iff.1 h
  have hEQ : Q ⊓ Eb.comap (QuotientGroup.mk' N) ≤ Q := inf_le_left
  have hd : Disjoint (Q ⊓ Eb.comap (QuotientGroup.mk' N)) N :=
    fg_disjoint (hQ.to_le hEQ) hN
  have hQN : Disjoint Q N := fg_disjoint hQ hN
  have hmap : (Q ⊓ Eb.comap (QuotientGroup.mk' N)).map (QuotientGroup.mk' N) = Eb := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx.2
    · intro hy
      obtain ⟨q, hq, rfl⟩ := hEbQ hy
      exact ⟨q, ⟨hq, hy⟩, rfl⟩
  have hEbab := CoreAux.isElemAbelian_iff.mp hEb
  refine fg_two_le_pRank_iff.2 ⟨Q ⊓ Eb.comap (QuotientGroup.mk' N), hEQ, ?_, ?_⟩
  · rw [CoreAux.isElemAbelian_iff]
    refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
    · have h1 : (QuotientGroup.mk' N) (x * y * x⁻¹ * y⁻¹) = 1 := by
        have := hEbab.1 _ hx.2 _ hy.2
        simp only [map_mul, map_inv]
        rw [this]
        group
      have h2 : x * y * x⁻¹ * y⁻¹ ∈ N := (QuotientGroup.eq_one_iff _).1 h1
      have h3 : x * y * x⁻¹ * y⁻¹ ∈ Q ⊓ N :=
        ⟨Q.mul_mem (Q.mul_mem (Q.mul_mem (hEQ hx) (hEQ hy)) (Q.inv_mem (hEQ hx)))
          (Q.inv_mem (hEQ hy)), h2⟩
      rw [hQN.eq_bot] at h3
      have h4 : x * y * x⁻¹ * y⁻¹ = 1 := Subgroup.mem_bot.1 h3
      calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
        _ = y * x := by rw [h4, one_mul]
    · have h1 : (QuotientGroup.mk' N) (x ^ 2) = 1 := by
        rw [map_pow]
        exact hEbab.2 _ hx.2
      have h2 : x ^ 2 ∈ N := (QuotientGroup.eq_one_iff _).1 h1
      have h3 : x ^ 2 ∈ Q ⊓ N := ⟨Q.pow_mem (hEQ hx) 2, h2⟩
      rw [hQN.eq_bot] at h3
      exact Subgroup.mem_bot.1 h3
  · rw [← fg_card_map hd, hmap, hEb4]

private theorem fg_normalizer_map_le (hN : Odd (Nat.card N)) {Q : Subgroup L} (hQ : IsPGroup 2 Q) :
    normalizer ((Q.map (QuotientGroup.mk' N) : Subgroup (L ⧸ N)) : Set (L ⧸ N)) ≤
      (normalizer (Q : Set L)).map (QuotientGroup.mk' N) := by
  intro gb hgb
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N gb
  have hQn : Q ≤ normalizer (N : Set L) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hQself : IsSylowOf 2 Q Q := isSylowOf_iff.2 ⟨le_rfl, hQ, by simp [Subgroup.relIndex_self]⟩
  have hQR : IsSylowOf 2 Q (Q ⊔ N) := isSylowOf_sup hQself hQn hN
  have hRcomap : (Q ⊔ N : Subgroup L) =
      (Q.map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) := by
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
  have hgR : ∀ x : L, x ∈ (Q ⊔ N : Subgroup L) → g * x * g⁻¹ ∈ (Q ⊔ N : Subgroup L) := by
    intro x hx
    rw [hRcomap, Subgroup.mem_comap] at hx ⊢
    have h1 := (Subgroup.mem_normalizer_iff.1 hgb ((QuotientGroup.mk' N) x)).1 hx
    simpa [map_mul, map_inv] using h1
  have hQ'R : IsSylowOf 2 (Q.map (MulAut.conj g).toMonoidHom) (Q ⊔ N) := by
    have hcard : Nat.card (Q.map (MulAut.conj g).toMonoidHom) = Nat.card Q :=
      Subgroup.card_map_of_injective (MulAut.conj g).injective
    refine isSylowOf_of_card ?_ (by rw [hcard]; exact hQR.card_eq)
    rintro _ ⟨q, hq, rfl⟩
    exact hgR q (Subgroup.mem_sup_left hq)
  obtain ⟨k, hkR, hk⟩ := hQR.exists_mem_conj hQ'R
  have hkg : k⁻¹ * g ∈ normalizer (Q : Set L) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have h1 : y ∈ Q ↔ g * y * g⁻¹ ∈ Q.map (MulAut.conj g).toMonoidHom := by
      constructor
      · intro hy
        exact ⟨y, hy, by simp [MulAut.conj_apply]⟩
      · rintro ⟨q, hq, hqy⟩
        have : q = y := by
          have h2 : g * q * g⁻¹ = g * y * g⁻¹ := by
            simpa [MulAut.conj_apply] using hqy
          simpa using h2
        rw [← this]
        exact hq
    rw [h1, hk]
    have e : k⁻¹ * (g * y * g⁻¹) * k = k⁻¹ * g * y * (k⁻¹ * g)⁻¹ := by group
    rw [e]
  have hkb : (QuotientGroup.mk' N) k ∈ Q.map (QuotientGroup.mk' N) := by
    have := hkR
    rw [hRcomap, Subgroup.mem_comap] at this
    exact this
  have hkb' : (QuotientGroup.mk' N) k ∈ (normalizer (Q : Set L)).map (QuotientGroup.mk' N) :=
    Subgroup.map_mono (Subgroup.le_normalizer (H := Q)) hkb
  have hmain : (QuotientGroup.mk' N) (k⁻¹ * g) ∈
      (normalizer (Q : Set L)).map (QuotientGroup.mk' N) := ⟨k⁻¹ * g, hkg, rfl⟩
  have e : (QuotientGroup.mk' N) g =
      (QuotientGroup.mk' N) k * (QuotientGroup.mk' N) (k⁻¹ * g) := by
    rw [← map_mul]
    congr 1
    group
  rw [e]
  exact Subgroup.mul_mem _ hkb' hmain

private theorem fg_le_gamma {P E : Subgroup L} (hEP : E ≤ P) (hE : Open.IsElemAbelian 2 E)
    (hE8 : 8 ≤ Nat.card E) (hN : Odd (Nat.card N)) : N ≤ Open.properTwoGenCoreGamma P 2 := by
  have hEN : E ≤ normalizer (N : Set L) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hgen := le_iSup_inf_centralizer_of_hyperplane hE (by omega) hEN hN
  refine hgen.trans (iSup_le fun B => iSup_le fun hBE => iSup_le fun hBcard => ?_)
  refine inf_le_right.trans ((Subgroup.centralizer_le_normalizer (B : Set L)).trans ?_)
  have hB : Open.IsElemAbelian 2 B := CoreAux.isElemAbelian_mono hBE hE
  have hB4 : 4 ≤ Nat.card B := by omega
  obtain ⟨H, hHB, hH, hH4⟩ := exists_fourSub_of_le_card hB hB4
  exact AhatData.normalizer_le_gamma (hBE.trans hEP) (fg_two_le_pRank_iff.2 ⟨H, hHB, hH, hH4⟩)

private theorem fg_gamma_eq_comap {P E : Subgroup L} (hP : IsPGroup 2 P) (hEP : E ≤ P)
    (hE : Open.IsElemAbelian 2 E) (hE8 : 8 ≤ Nat.card E) (hN : Odd (Nat.card N)) :
    Open.properTwoGenCoreGamma P 2 =
      (Open.properTwoGenCoreGamma (P.map (QuotientGroup.mk' N)) 2).comap
        (QuotientGroup.mk' N) := by
  apply le_antisymm
  · rw [CFSG.ProperTwoGeneratedCore.gamma_le_iff]
    intro Q hQP hQ g hg
    rw [Subgroup.mem_comap]
    have hQp : IsPGroup 2 Q := hP.to_le hQP
    have h1 : QuotientGroup.mk' N g ∈
        normalizer ((Q.map (QuotientGroup.mk' N) : Subgroup (L ⧸ N)) : Set (L ⧸ N)) :=
      Subgroup.le_normalizer_map _ ⟨g, hg, rfl⟩
    exact AhatData.normalizer_le_gamma (Subgroup.map_mono hQP) (fg_two_le_pRank_map hQp hN hQ) h1
  · intro x hx
    have hbar : Open.properTwoGenCoreGamma (P.map (QuotientGroup.mk' N)) 2 ≤
        (Open.properTwoGenCoreGamma P 2).map (QuotientGroup.mk' N) := by
      rw [CFSG.ProperTwoGeneratedCore.gamma_le_iff]
      intro Qb hQbP hQb gb hgb
      have hQP : P ⊓ Qb.comap (QuotientGroup.mk' N) ≤ P := inf_le_left
      have hQp : IsPGroup 2 ↥(P ⊓ Qb.comap (QuotientGroup.mk' N)) := hP.to_le hQP
      have hQmap : (P ⊓ Qb.comap (QuotientGroup.mk' N)).map (QuotientGroup.mk' N) = Qb := by
        ext y
        constructor
        · rintro ⟨x, hx, rfl⟩
          exact hx.2
        · intro hy
          obtain ⟨q, hq, rfl⟩ := hQbP hy
          exact ⟨q, ⟨hq, hy⟩, rfl⟩
      have hQb' : 2 ≤ Open.pRank 2
          ((P ⊓ Qb.comap (QuotientGroup.mk' N)).map (QuotientGroup.mk' N)) := by
        rw [hQmap]
        exact hQb
      have hgb' : gb ∈ normalizer ((((P ⊓ Qb.comap (QuotientGroup.mk' N)).map
          (QuotientGroup.mk' N) : Subgroup (L ⧸ N))) : Set (L ⧸ N)) := by
        rw [hQmap]
        exact hgb
      have hrank := fg_two_le_pRank_of_map hQp hN hQb'
      have h1 := fg_normalizer_map_le hN hQp hgb'
      exact Subgroup.map_mono (AhatData.normalizer_le_gamma hQP hrank) h1
    obtain ⟨y, hy, hyx⟩ := hbar hx
    have hyx' : y⁻¹ * x ∈ N := QuotientGroup.eq.1 hyx
    have hNΓ := fg_le_gamma hEP hE hE8 hN hyx'
    have := (Open.properTwoGenCoreGamma P 2).mul_mem hy hNΓ
    simpa using this

end Quotient

section Component

variable {X : Type} [Group X] [Finite X] {n : ℕ} {z : X}
  {S : Sylow 2 ↥(normalizer ((zpowers z : Subgroup X) : Set X))}

private theorem fg_odd_card_core (A : Subgroup X) : Odd (Nat.card (pPrimeCore 2 ↥A)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact Nat.coprime_two_left.mp pPrimeCore_coprime_card

private theorem fg_isElemAbelian_subgroupOf {K U : Subgroup X} (hU : Open.IsElemAbelian 2 U) :
    Open.IsElemAbelian 2 (U.subgroupOf K) := by
  rw [CoreAux.isElemAbelian_iff] at hU ⊢
  exact ⟨fun x hx y hy => Subtype.ext (hU.1 x hx y hy), fun x hx => Subtype.ext (hU.2 x hx)⟩

theorem exists_isSylowTwoIn (A : Subgroup X) : ∃ P : Subgroup X, IsSylowTwoIn A P := by
  obtain ⟨P, hP⟩ := exists_isSylowOf 2 A
  exact ⟨P, isSylowOf_iff.1 hP⟩

private noncomputable abbrev FGam (A P : Subgroup X) : Subgroup X :=
  (Open.properTwoGenCoreGamma (P.subgroupOf A) 2).map A.subtype

private theorem fg_gam_le (A P : Subgroup X) : FGam A P ≤ A := Subgroup.map_subtype_le _

private theorem fg_exists_ne {B : Subgroup X} (hz2 : orderOf z = 2) (hB : 3 ≤ Nat.card B) :
    ∃ x ∈ B, x ≠ 1 ∧ x ≠ z := by
  by_contra hcon
  have hle : B ≤ zpowers z := fun x hx => by
    by_cases hx1 : x = 1
    · rw [hx1]
      exact Subgroup.one_mem _
    · have hxz : x = z := by
        by_contra hxz
        exact hcon ⟨x, hx, hx1, hxz⟩
      rw [hxz]
      exact Subgroup.mem_zpowers z
  have := Subgroup.card_le_of_le hle
  rw [Nat.card_zpowers, hz2] at this
  omega

private theorem fg_exists_E8 (h : Sec5Data X n z (zpowers z) S) {A P : Subgroup X}
    (hA : Sec5Comp X n (centralizer ({z} : Set X)) A) (hP : IsSylowTwoIn A P)
    (hR : FourInE8 P) :
    ∃ E : Subgroup X, E ≤ P ∧ Open.IsElemAbelian 2 E ∧ 8 ≤ Nat.card E := by
  obtain ⟨E₀, hE₀P, hE₀, hE₀4⟩ := exists_four_le_sylow h.maxdeg.1 hA (isSylowOf_iff.2 hP)
  obtain ⟨U, hUE, hU, hU4⟩ := exists_fourSub_of_le_card hE₀ hE₀4
  obtain ⟨E, hEP, hE, hE8, -⟩ := hR U (hUE.trans hE₀P) hU hU4
  exact ⟨E, hEP, hE, hE8⟩

private theorem fg_exists_sylow_map {A P : Subgroup X} (hP : IsSylowTwoIn A P) :
    ∃ T : Sylow 2 (↥A ⧸ pPrimeCore 2 ↥A),
      (T : Subgroup (↥A ⧸ pPrimeCore 2 ↥A)) =
        (P.subgroupOf A).map (QuotientGroup.mk' (pPrimeCore 2 ↥A)) := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hPA, hP2, hPidx⟩ := hP
  have hπ : Function.Surjective (QuotientGroup.mk' (pPrimeCore 2 ↥A)) :=
    QuotientGroup.mk'_surjective _
  let PA : Sylow 2 ↥A := IsPGroup.toSylow (P := P.subgroupOf A)
    (hP2.of_equiv (Subgroup.subgroupOfEquivOfLe hPA).symm) hPidx
  refine ⟨Sylow.mapSurjective hπ PA, ?_⟩
  rw [Sylow.coe_mapSurjective hπ PA]
  rfl

private theorem fg_exists_E8_sub (h : Sec5Data X n z (zpowers z) S) {A P : Subgroup X}
    (hA : Sec5Comp X n (centralizer ({z} : Set X)) A) (hP : IsSylowTwoIn A P)
    (hR : FourInE8 P) :
    ∃ E : Subgroup ↥A, E ≤ P.subgroupOf A ∧ Open.IsElemAbelian 2 E ∧ 8 ≤ Nat.card E := by
  obtain ⟨E, hEP, hE, hE8⟩ := fg_exists_E8 h hA hP hR
  refine ⟨E.subgroupOf A, Subgroup.comap_mono hEP, fg_isElemAbelian_subgroupOf hE, ?_⟩
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hEP.trans hP.1)).toEquiv]
  exact hE8

private theorem fg_gamma_eq_comap_comp (h : Sec5Data X n z (zpowers z) S) {A P : Subgroup X}
    (hA : Sec5Comp X n (centralizer ({z} : Set X)) A) (hP : IsSylowTwoIn A P)
    (hR : FourInE8 P) :
    Open.properTwoGenCoreGamma (P.subgroupOf A) 2 =
      (Open.properTwoGenCoreGamma
        ((P.subgroupOf A).map (QuotientGroup.mk' (pPrimeCore 2 ↥A))) 2).comap
        (QuotientGroup.mk' (pPrimeCore 2 ↥A)) := by
  obtain ⟨E, hEP, hE, hE8⟩ := fg_exists_E8_sub h hA hP hR
  exact fg_gamma_eq_comap hP.2.1.comap_subtype hEP hE hE8 (fg_odd_card_core A)

private theorem fg_oddCore_le_gam (h : Sec5Data X n z (zpowers z) S) {A P : Subgroup X}
    (hA : Sec5Comp X n (centralizer ({z} : Set X)) A) (hP : IsSylowTwoIn A P)
    (hR : FourInE8 P) : oddCoreOf A ≤ FGam A P := by
  obtain ⟨E, hEP, hE, hE8⟩ := fg_exists_E8_sub h hA hP hR
  exact Subgroup.map_mono (fg_le_gamma (N := pPrimeCore 2 ↥A) hEP hE hE8 (fg_odd_card_core A))

private theorem fg_le_gam (h : Sec5Data X n z (zpowers z) S) {A P : Subgroup X}
    (hA : Sec5Comp X n (centralizer ({z} : Set X)) A) (hP : IsSylowTwoIn A P)
    (hR : FourInE8 P) : P ≤ FGam A P := by
  obtain ⟨E, hEP, hE, hE8⟩ := fg_exists_E8_sub h hA hP hR
  have hrank : 2 ≤ Open.pRank 2 (P.subgroupOf A) := by
    obtain ⟨U, hUE, hU, hU4⟩ := exists_fourSub_of_le_card hE (by omega)
    exact fg_two_le_pRank_iff.2 ⟨U, hUE.trans hEP, hU, hU4⟩
  have h1 : P.subgroupOf A ≤ Open.properTwoGenCoreGamma (P.subgroupOf A) 2 :=
    Subgroup.le_normalizer.trans (AhatData.normalizer_le_gamma le_rfl hrank)
  intro x hx
  exact ⟨⟨x, hP.1 hx⟩, h1 hx, rfl⟩

private theorem fg_map_conj_oddCore_cen (g b : X) :
    (oddCoreOf (cen b)).map (MulAut.conj g).toMonoidHom = oddCoreOf (cen (g * b * g⁻¹)) := by
  rw [CoreAux.cen_conj, CoreAux.oddCoreOf_map_equiv (MulAut.conj g) (cen b)]

private theorem fg_oddCore_le_Wgamma {A P : Subgroup X} {x : X} (hx : x ∈ FGam A P)
    (hx2 : orderOf x = 2) : oddCoreOf (centralizer ({x} : Set X)) ≤ Wgamma A P :=
  le_iSup_of_le x (le_iSup_of_le hx (le_iSup_of_le hx2 le_rfl))

private theorem fg_map_conj_Wgamma_le {A P : Subgroup X} {g : X}
    (hg : g ∈ normalizer ((FGam A P : Subgroup X) : Set X)) :
    (Wgamma A P).map (MulAut.conj g).toMonoidHom ≤ Wgamma A P := by
  unfold Wgamma
  rw [Subgroup.map_iSup]
  refine iSup_le fun c => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hc => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hc2 => ?_
  rw [fg_map_conj_oddCore_cen g c]
  have hgc : g * c * g⁻¹ ∈ FGam A P := (Subgroup.mem_normalizer_iff.1 hg c).1 hc
  have hgc2 : orderOf (g * c * g⁻¹) = 2 := by
    have := MulEquiv.orderOf_eq (MulAut.conj g) c
    rw [hc2] at this
    exact this
  exact le_iSup_of_le (g * c * g⁻¹) (le_iSup_of_le hgc (le_iSup_of_le hgc2 le_rfl))

private theorem fg_normalizer_le_Wgamma (A P : Subgroup X) :
    normalizer ((FGam A P : Subgroup X) : Set X) ≤
      normalizer ((Wgamma A P : Subgroup X) : Set X) := by
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro w
  constructor
  · intro hw
    exact fg_map_conj_Wgamma_le hy ⟨w, hw, rfl⟩
  · intro hw
    have := fg_map_conj_Wgamma_le (Subgroup.inv_mem _ hy) ⟨y * w * y⁻¹, hw, rfl⟩
    have e : (MulAut.conj y⁻¹).toMonoidHom (y * w * y⁻¹) = w := by
      simp [MulAut.conj_apply, mul_assoc]
    rwa [e] at this

private theorem fg_cen_eq (h : Sec5Data X n z (zpowers z) S) {A₁ A₂ : Subgroup X}
    (hA₁ : Sec5Comp X n (centralizer ({z} : Set X)) A₁)
    (hA₂ : Sec5Comp X n (centralizer ({z} : Set X)) A₂) (h12 : A₁ ≠ A₂) {x : X} (hxA₂ : x ∈ A₂)
    (hx2 : orderOf x = 2) :
    centralizer ({x} : Set X) = oddCoreOf (centralizer ({x} : Set X)) ⊔
      (centralizer ({z} : Set X) ⊓ centralizer ({x} : Set X)) := by
  have hxC : x ∈ centralizer ({z} : Set X) := comp_le hA₂ hxA₂
  have hcomm : ∀ a ∈ A₁, ⁅a, x⁆ ∈ oddCoreOf A₁ :=
    (normalizes_of_comm hA₁ (Subgroup.le_normalizer hxC) fun a ha =>
      comm_mem_of_ne hA₁ hA₂ h12 a ha x hxA₂).2
  exact cen_eq_oddCoreOf_sup_of_comm h hA₁ hx2 hxC hcomm

private theorem fg_cen_nine
    (h : Sec5Data X 9 z (zpowers z) S) {A P : Subgroup X}
    (hA : Sec5Comp X 9 (centralizer ({z} : Set X)) A)
    (hcomap : Open.properTwoGenCoreGamma (P.subgroupOf A) 2 =
      (Open.properTwoGenCoreGamma
        ((P.subgroupOf A).map (QuotientGroup.mk' (pPrimeCore 2 ↥A))) 2).comap
        (QuotientGroup.mk' (pPrimeCore 2 ↥A)))
    (T : Sylow 2 (↥A ⧸ pPrimeCore 2 ↥A))
    (hT : (T : Subgroup (↥A ⧸ pPrimeCore 2 ↥A)) =
      (P.subgroupOf A).map (QuotientGroup.mk' (pPrimeCore 2 ↥A)))
    {e : X} (he : e ∈ FGam A P) (he2 : orderOf e = 2) (hez : e ≠ z) :
    centralizer ({z} : Set X) ⊓ centralizer ({e} : Set X) ≤
      normalizer ((FGam A P : Subgroup X) : Set X) := by
  have hn8 : 8 ≤ 9 := by norm_num
  have heA : e ∈ A := fg_gam_le A P he
  have he1 : e * e = 1 := by
    have := pow_orderOf_eq_one e
    rwa [he2, pow_two] at this
  have hz2 : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [h.orderOf_z, pow_two] at this
  have hzA : z ∈ A := z_mem_comp h hA
  let M : AhatModel X 9 A := AhatModel.ofCover hA.2
  let C : AhatData.CoverSetup 9 (↥A ⧸ pPrimeCore 2 ↥A) := M.C
  obtain ⟨i, hΓi, -⟩ := gamma_two_nine C T
  have hΓ' : Open.properTwoGenCoreGamma
      ((P.subgroupOf A).map (QuotientGroup.mk' (pPrimeCore 2 ↥A))) 2 =
        (MulAction.stabilizer (Equiv.Perm (Fin 9)) i).comap C.ρ := by
    rw [← hT]
    exact hΓi
  have hmemΓ : ∀ a : ↥A, a ∈ Open.properTwoGenCoreGamma (P.subgroupOf A) 2 ↔
      C.ρ (QuotientGroup.mk' (pPrimeCore 2 ↥A) a) i = i := fun a =>
    (SetLike.ext_iff.1 hcomap a).trans ((SetLike.ext_iff.1 hΓ' _).trans Iff.rfl)
  obtain ⟨τ, hτ⟩ : ∃ τ : Equiv.Perm (Fin 9),
      τ = C.ρ (QuotientGroup.mk' (pPrimeCore 2 ↥A) ⟨e, heA⟩) := ⟨_, rfl⟩
  have haΓ : (⟨e, heA⟩ : ↥A) ∈ Open.properTwoGenCoreGamma (P.subgroupOf A) 2 := by
    obtain ⟨a, haΓ, hae⟩ := he
    have : a = ⟨e, heA⟩ := Subtype.ext hae
    rwa [this] at haΓ
  have hτfix : τ i = i := by
    rw [hτ]
    exact (hmemΓ _).1 haΓ
  have hxx : QuotientGroup.mk' (pPrimeCore 2 ↥A) (⟨e, heA⟩ : ↥A) *
      QuotientGroup.mk' (pPrimeCore 2 ↥A) (⟨e, heA⟩ : ↥A) = 1 := by
    rw [← map_mul]
    have : (⟨e, heA⟩ : ↥A) * ⟨e, heA⟩ = 1 := Subtype.ext he1
    rw [this, map_one]
  have hpe1 : QuotientGroup.mk' (pPrimeCore 2 ↥A) (⟨e, heA⟩ : ↥A) ≠ 1 := by
    intro h1
    have h2 : (⟨e, heA⟩ : ↥A) ∈ pPrimeCore 2 ↥A := (QuotientGroup.eq_one_iff _).1 h1
    have h3 : e ∈ oddCoreOf A := mem_oddCoreOf_iff.2 ⟨heA, h2⟩
    have h4 := eq_one_of_mem_oddCoreOf_of_pow (k := 1) h3 (by rw [pow_one, pow_two]; exact he1)
    rw [h4, orderOf_one] at he2
    omega
  have hzc : QuotientGroup.mk' (pPrimeCore 2 ↥A) (⟨z, hzA⟩ : ↥A) ∈
      center (↥A ⧸ pPrimeCore 2 ↥A) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥A) q
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (comm_z_of_mem_comp hA a.2)
  have hpz1 : QuotientGroup.mk' (pPrimeCore 2 ↥A) (⟨z, hzA⟩ : ↥A) ≠ 1 := by
    intro h1
    have h2 : (⟨z, hzA⟩ : ↥A) ∈ pPrimeCore 2 ↥A := (QuotientGroup.eq_one_iff _).1 h1
    have h3 : z ∈ oddCoreOf A := mem_oddCoreOf_iff.2 ⟨hzA, h2⟩
    have h4 := eq_one_of_mem_oddCoreOf_of_pow (k := 1) h3 (by rw [pow_one, pow_two]; exact hz2)
    have := h.orderOf_z
    rw [h4, orderOf_one] at this
    omega
  have hτne : τ ≠ 1 := by
    intro h1
    have hmem : QuotientGroup.mk' (pPrimeCore 2 ↥A) (⟨e, heA⟩ : ↥A) ∈
        center (↥A ⧸ pPrimeCore 2 ↥A) := C.ρ_eq_one_iff.1 (by rw [← hτ]; exact h1)
    have hEq := C.center_eq_of_ne_one hmem hzc hpe1 hpz1
    have h2 : (⟨e, heA⟩ : ↥A)⁻¹ * ⟨z, hzA⟩ ∈ pPrimeCore 2 ↥A := QuotientGroup.eq.1 hEq
    have h3 : e⁻¹ * z ∈ oddCoreOf A :=
      mem_oddCoreOf_iff.2 ⟨A.mul_mem (A.inv_mem heA) hzA, h2⟩
    exact hez (eq_of_inv_mul_mem_oddCoreOf (comm_z_of_mem_comp hA heA) (k := 1)
      (by rw [pow_one, pow_two]; exact he1) (by rw [pow_one, pow_two]; exact hz2) h3)
  have hdvd : 8 ∣ τ.support.card := by
    have h1 := (C.sq_eq_one_iff_dvd hn8
      (x := QuotientGroup.mk' (pPrimeCore 2 ↥A) (⟨e, heA⟩ : ↥A))
      (by rw [← map_mul, hxx, map_one])).1 hxx
    rw [hτ]
    exact h1
  have hcard : τ.support.card = 8 := by
    have h9 : τ.support.card ≤ 9 := by simpa using Finset.card_le_univ τ.support
    have h0 : τ.support.card ≠ 0 := fun h0 =>
      hτne (Equiv.Perm.support_eq_empty_iff.1 (Finset.card_eq_zero.1 h0))
    omega
  have hfc : fixCount τ = 1 := by
    have := fixCount_add_support τ
    omega
  have huniq : ∀ j : Fin 9, τ j = j → j = i := by
    intro j hj
    obtain ⟨a, ha⟩ := Finset.card_eq_one.1 hfc
    have hi := (Finset.ext_iff.1 ha i).1 (Finset.mem_filter.2 ⟨Finset.mem_univ _, hτfix⟩)
    have hj' := (Finset.ext_iff.1 ha j).1 (Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩)
    rw [Finset.mem_singleton] at hi hj'
    rw [hj', hi]
  have key : ∀ c : X, c ∈ centralizer ({z} : Set X) ⊓ centralizer ({e} : Set X) →
      ∀ x ∈ FGam A P, c * x * c⁻¹ ∈ FGam A P := by
    intro c hc x hx
    have hcA : c ∈ normalizer (A : Set X) :=
      mem_normalizer_comp_of_mem_cen h hA heA he2 hez hc.1 hc.2
    obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin 9), σ = M.perm c hcA := ⟨_, rfl⟩
    have hind : C.Induces (M.autOf c hcA) σ := by
      rw [hσ]
      exact M.induces_perm hn8 c hcA
    have hconj : ∀ a : ↥A, C.ρ (QuotientGroup.mk' (pPrimeCore 2 ↥A) (conjAut hcA a)) =
        σ * C.ρ (QuotientGroup.mk' (pPrimeCore 2 ↥A) a) * σ⁻¹ := by
      intro a
      have h1 := hind.map_ρ (QuotientGroup.mk' (pPrimeCore 2 ↥A) a)
      have h2 : M.autOf c hcA (QuotientGroup.mk' (pPrimeCore 2 ↥A) a) =
          QuotientGroup.mk' (pPrimeCore 2 ↥A) (conjAut hcA a) := M.autOf_mk hcA a
      exact (congrArg C.ρ h2.symm).trans h1
    have hcomm' : σ * τ = τ * σ := by
      have h1 := hconj ⟨e, heA⟩
      have h2 : conjAut hcA (⟨e, heA⟩ : ↥A) = ⟨e, heA⟩ := Subtype.ext (by
        show c * e * c⁻¹ = e
        have hce' : c * e = e * c := mem_centralizer_singleton_iff.1 hc.2
        rw [hce']
        group)
      rw [h2, ← hτ] at h1
      calc σ * τ = (σ * τ * σ⁻¹) * σ := by group
        _ = τ * σ := by rw [← h1]
    have hσi : σ i = i := by
      apply huniq
      have h1 := congrArg (fun f : Equiv.Perm (Fin 9) => f i) hcomm'
      simp only [Equiv.Perm.mul_apply] at h1
      rw [hτfix] at h1
      exact h1.symm
    obtain ⟨a, haΓ, rfl⟩ := hx
    refine ⟨conjAut hcA a, (hmemΓ _).2 ?_, rfl⟩
    rw [hconj]
    have hσinv : σ⁻¹ i = i := by
      rw [Equiv.Perm.inv_eq_iff_eq]
      exact hσi.symm
    have hai : C.ρ (QuotientGroup.mk' (pPrimeCore 2 ↥A) a) i = i := (hmemΓ a).1 haΓ
    simp only [Equiv.Perm.mul_apply, hσinv, hai, hσi]
  intro c hc
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => key c hc x hx, fun hx => ?_⟩
  have hc' : c⁻¹ ∈ centralizer ({z} : Set X) ⊓ centralizer ({e} : Set X) :=
    ⟨Subgroup.inv_mem _ hc.1, Subgroup.inv_mem _ hc.2⟩
  have := key c⁻¹ hc' _ hx
  have e' : c⁻¹ * (c * x * c⁻¹) * c⁻¹⁻¹ = x := by group
  rwa [e'] at this

theorem cen_inf_cen_le_normalizer_gamma
    (h : Sec5Data X n z (zpowers z) S) {A P : Subgroup X}
    (hA : Sec5Comp X n (centralizer ({z} : Set X)) A) (hP : IsSylowTwoIn A P)
    (hR : FourInE8 P) {e : X}
    (he : e ∈ (Open.properTwoGenCoreGamma (P.subgroupOf A) 2).map A.subtype)
    (he2 : orderOf e = 2) (hez : e ≠ z) :
    centralizer ({z} : Set X) ⊓ centralizer ({e} : Set X) ≤
      normalizer (((Open.properTwoGenCoreGamma (P.subgroupOf A) 2).map A.subtype : Subgroup X) :
        Set X) := by
  have hn8 : 8 ≤ n := h.maxdeg.1
  have hcomap := fg_gamma_eq_comap_comp h hA hP hR
  obtain ⟨T, hT⟩ := fg_exists_sylow_map hP
  have heA : e ∈ A := fg_gam_le A P he
  by_cases hn9 : n = 9
  · subst hn9
    exact fg_cen_nine h hA hcomap T hT he he2 hez
  · have htop : Open.properTwoGenCoreGamma (P.subgroupOf A) 2 = ⊤ := by
      rw [hcomap, ← hT, gamma_two_eq_top_of_ne_nine hn8 hn9 hA.2 T, Subgroup.comap_top]
    have hGA : (Open.properTwoGenCoreGamma (P.subgroupOf A) 2).map A.subtype = A := by
      rw [htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [hGA]
    intro c hc
    exact mem_normalizer_comp_of_mem_cen h hA heA he2 hez hc.1 hc.2

private theorem fg_cen_le_normalizer
    (h : Sec5Data X n z (zpowers z) S) {A₁ A₂ P₂ : Subgroup X}
    (hA₁ : Sec5Comp X n (centralizer ({z} : Set X)) A₁)
    (hA₂ : Sec5Comp X n (centralizer ({z} : Set X)) A₂) (h12 : A₁ ≠ A₂)
    (hP₂ : IsSylowTwoIn A₂ P₂) (hR : FourInE8 P₂) {x : X} (hx : x ∈ FGam A₂ P₂)
    (hx2 : orderOf x = 2) (hxz : x ≠ z) :
    centralizer ({x} : Set X) ≤ normalizer ((Wgamma A₂ P₂ : Subgroup X) : Set X) := by
  have hxA₂ : x ∈ A₂ := fg_gam_le A₂ P₂ hx
  refine (fg_cen_eq h hA₁ hA₂ h12 hxA₂ hx2).le.trans (sup_le ?_ ?_)
  · exact (fg_oddCore_le_Wgamma hx hx2).trans Subgroup.le_normalizer
  · intro y hy
    exact fg_normalizer_le_Wgamma A₂ P₂
      (cen_inf_cen_le_normalizer_gamma h hA₂ hP₂ hR hx hx2 hxz hy)

private theorem fg_exists_conj_gen (h : Sec5Data X n z (zpowers z) S) {A₁ A₂ P₂ E : Subgroup X}
    (hA₁ : Sec5Comp X n (centralizer ({z} : Set X)) A₁)
    (hA₂ : Sec5Comp X n (centralizer ({z} : Set X)) A₂) (h12 : A₁ ≠ A₂) (hEP : E ≤ P₂)
    (hE : Open.IsElemAbelian 2 E) (hE8 : 8 ≤ Nat.card E) (hPG : P₂ ≤ FGam A₂ P₂)
    (hOG : oddCoreOf A₂ ≤ FGam A₂ P₂) {b : X} (hb : b ∈ A₁) (hb2 : orderOf b = 2) :
    ∃ k ∈ FGam A₂ P₂, oddCoreOf (centralizer ({b} : Set X)) ≤
      ⨆ u ∈ E, ⨆ (_ : u ≠ 1), ⨆ (_ : u ≠ z),
        (centralizer ({u} : Set X)).map (MulAut.conj k).toMonoidHom := by
  have hG₂A : FGam A₂ P₂ ≤ A₂ := fg_gam_le A₂ P₂
  have hbC : b ∈ centralizer ({z} : Set X) := comp_le hA₁ hb
  obtain ⟨hbN, hcomm⟩ := normalizes_of_comm hA₂ (Subgroup.le_normalizer hbC) fun a ha =>
    comm_mem_of_ne hA₂ hA₁ h12.symm a ha b hb
  have hb2' : b * b = 1 := by
    have := pow_orderOf_eq_one b
    rwa [hb2, pow_two] at this
  have hbO : b ∈ normalizer (oddCoreOf A₂ : Set X) :=
    mem_normalizer_oddCoreOf_of_mem_normalizer hbN
  have hcov : ∀ g ∈ FGam A₂ P₂, ∃ x ∈ centralizer ({b} : Set X), ∃ o ∈ oddCoreOf A₂,
      g = x * o := by
    intro g hg
    have hy : g⁻¹ * (b * g * b⁻¹) ∈ oddCoreOf A₂ := by
      have h1 := hcomm g⁻¹ (A₂.inv_mem (hG₂A hg))
      have e : ⁅g⁻¹, b⁆ = g⁻¹ * (b * g * b⁻¹) := by simp only [commutatorElement_def]; group
      rwa [e] at h1
    obtain ⟨p, hp, hcent⟩ := exists_mul_mem_centralizer_of_fixes_coset (odd_card_oddCoreOf A₂)
      (k := 1) (by rw [pow_one, pow_two]; exact hb2') hbO hy
    exact ⟨g * p, hcent, p⁻¹, (oddCoreOf A₂).inv_mem hp, by group⟩
  obtain ⟨Q, hQ, hQb⟩ := exists_sylow_le_of_covers (A := FGam A₂ P₂) (O := oddCoreOf A₂)
    (Xs := centralizer ({b} : Set X)) (hG₂A.trans (le_normalizer_oddCoreOf A₂))
    (odd_card_oddCoreOf A₂) (hOG.trans Subgroup.le_normalizer) hcov
  obtain ⟨k, hkG, hk⟩ := exists_conj_le_sylow' hQ (hEP.trans hPG) (isPGroup_two_of_sq hE.2)
  refine ⟨k, hkG, ?_⟩
  have hE'Q : E.map (MulAut.conj k).toMonoidHom ≤ Q := by
    rintro _ ⟨x, hx, rfl⟩
    exact hk x hx
  have hE'ab : Open.IsElemAbelian 2 (E.map (MulAut.conj k).toMonoidHom) :=
    CFSG.SectionRank.isElemAbelian_map hE _
  have hE'card : Nat.card (E.map (MulAut.conj k).toMonoidHom) = Nat.card E :=
    Subgroup.card_map_of_injective (MulAut.conj k).injective
  have hE'N : E.map (MulAut.conj k).toMonoidHom ≤
      normalizer (oddCoreOf (centralizer ({b} : Set X)) : Set X) :=
    (hE'Q.trans hQb).trans (le_normalizer_oddCoreOf _)
  have hgen := le_iSup_inf_centralizer_of_hyperplane hE'ab (by omega) hE'N
    (odd_card_oddCoreOf _)
  refine hgen.trans (iSup_le fun B => iSup_le fun hBE => iSup_le fun hBcard => ?_)
  have hB4 : 4 ≤ Nat.card B := by omega
  obtain ⟨x, hxB, hx1, hxz⟩ := fg_exists_ne h.orderOf_z (B := B) (by omega)
  obtain ⟨u, huE, hux⟩ := hBE hxB
  have hux' : k * u * k⁻¹ = x := hux
  have hkz : k * z = z * k := comm_z_of_mem_comp hA₂ (hG₂A hkG)
  have hu1 : u ≠ 1 := by
    intro hu
    apply hx1
    rw [← hux', hu]
    group
  have huz : u ≠ z := by
    intro hu
    apply hxz
    rw [← hux', hu]
    calc k * z * k⁻¹ = z * k * k⁻¹ := by rw [hkz]
      _ = z := by group
  have hCB : oddCoreOf (centralizer ({b} : Set X)) ⊓ centralizer (B : Set X) ≤
      centralizer ({x} : Set X) :=
    inf_le_right.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hxB))
  have hcx : centralizer ({x} : Set X) =
      (centralizer ({u} : Set X)).map (MulAut.conj k).toMonoidHom := by
    rw [← hux']
    exact CoreAux.cen_conj k u
  rw [hcx] at hCB
  exact hCB.trans (le_iSup_of_le u (le_iSup_of_le huE (le_iSup_of_le hu1
    (le_iSup_of_le huz le_rfl))))

theorem oddCore_le_normalizer_Wgamma
    (h : Sec5Data X n z (zpowers z) S) {A₁ A₂ P₂ : Subgroup X}
    (hA₁ : Sec5Comp X n (centralizer ({z} : Set X)) A₁)
    (hA₂ : Sec5Comp X n (centralizer ({z} : Set X)) A₂) (h12 : A₁ ≠ A₂)
    (hP₂ : IsSylowTwoIn A₂ P₂) (hR : FourInE8 P₂) {b : X} (hb : b ∈ A₁) (hb2 : orderOf b = 2) :
    oddCoreOf (centralizer ({b} : Set X)) ≤ normalizer ((Wgamma A₂ P₂ : Subgroup X) : Set X) := by
  obtain ⟨E, hEP, hE, hE8⟩ := fg_exists_E8 h hA₂ hP₂ hR
  have hPG := fg_le_gam h hA₂ hP₂ hR
  obtain ⟨k, hkG, hgen⟩ := fg_exists_conj_gen h hA₁ hA₂ h12 hEP hE hE8 hPG
    (fg_oddCore_le_gam h hA₂ hP₂ hR) hb hb2
  refine hgen.trans (iSup_le fun u => iSup_le fun huE => iSup_le fun hu1 => iSup_le fun huz => ?_)
  have hu2 : orderOf u = 2 := CoreAux.orderOf_eq_two_of_isElemAbelian hE huE hu1
  have hxG : k * u * k⁻¹ ∈ FGam A₂ P₂ :=
    (FGam A₂ P₂).mul_mem ((FGam A₂ P₂).mul_mem hkG (hPG (hEP huE))) ((FGam A₂ P₂).inv_mem hkG)
  have hx2 : orderOf (k * u * k⁻¹) = 2 := by
    have := MulEquiv.orderOf_eq (MulAut.conj k) u
    rw [hu2] at this
    exact this
  have hkz : k * z = z * k := comm_z_of_mem_comp hA₂ (fg_gam_le A₂ P₂ hkG)
  have hxz : k * u * k⁻¹ ≠ z := by
    intro hx
    apply huz
    have : u = k⁻¹ * z * k := by
      rw [← hx]
      group
    rw [this]
    calc k⁻¹ * z * k = k⁻¹ * (z * k) := by group
      _ = k⁻¹ * (k * z) := by rw [hkz]
      _ = z := by group
  rw [← CoreAux.cen_conj k u]
  exact fg_cen_le_normalizer h hA₁ hA₂ h12 hP₂ hR hxG hx2 hxz

open CFSG.ComponentClassification.HarrisLit.T1.S74.L38 in
theorem normalizer_Wgamma_ne_top
    (h : Sec5Data X n z (zpowers z) S) {A₁ A₂ P₂ : Subgroup X}
    (hA₁ : Sec5Comp X n (centralizer ({z} : Set X)) A₁)
    (hA₂ : Sec5Comp X n (centralizer ({z} : Set X)) A₂) (h12 : A₁ ≠ A₂)
    (hP₂ : IsSylowTwoIn A₂ P₂) (hR : FourInE8 P₂)
    (hbad : ∃ b ∈ A₁, orderOf b = 2 ∧
      ¬ oddCoreOf (centralizer ({b} : Set X)) ≤ centralizer ({z} : Set X)) :
    normalizer ((Wgamma A₂ P₂ : Subgroup X) : Set X) ≠ ⊤ := by
  have hsimple := h.cex.simple
  have hn8 : 8 ≤ n := h.maxdeg.1
  obtain ⟨E, hEP, hE, hE8⟩ := fg_exists_E8 h hA₂ hP₂ hR
  have hPG := fg_le_gam h hA₂ hP₂ hR
  have hOG := fg_oddCore_le_gam h hA₂ hP₂ hR
  obtain ⟨b₀, hb₀, hb₀2, hb₀bad⟩ := hbad
  have hz2 : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [h.orderOf_z, pow_two] at this
  have hz1 : z ≠ 1 := fun e => by
    have := h.orderOf_z
    rw [e, orderOf_one] at this
    omega
  have hzA₁ : z ∈ A₁ := z_mem_comp h hA₁
  have hkey : (∀ u ∈ P₂, orderOf u = 2 → u ≠ z →
      oddCoreOf (centralizer ({u} : Set X)) ≤ centralizer ({z} : Set X)) → False := by
    intro hstar
    have huC : ∀ u ∈ P₂, orderOf u = 2 → u ≠ z →
        centralizer ({u} : Set X) ≤ centralizer ({z} : Set X) := fun u huP hu2 huz =>
      (fg_cen_eq h hA₁ hA₂ h12 (hP₂.1 huP) hu2).le.trans
        (sup_le (hstar u huP hu2 huz) inf_le_left)
    obtain ⟨k, hkG, hgen⟩ := fg_exists_conj_gen h hA₁ hA₂ h12 hEP hE hE8 hPG hOG hb₀ hb₀2
    apply hb₀bad
    refine hgen.trans (iSup_le fun u => iSup_le fun huE => iSup_le fun hu1 =>
      iSup_le fun huz => ?_)
    have hu2 : orderOf u = 2 := CoreAux.orderOf_eq_two_of_isElemAbelian hE huE hu1
    have hkC : k ∈ centralizer ({z} : Set X) := comp_le hA₂ (fg_gam_le A₂ P₂ hkG)
    rintro _ ⟨w, hw, rfl⟩
    have hwz : w ∈ centralizer ({z} : Set X) := huC u (hEP huE) hu2 huz hw
    exact (centralizer ({z} : Set X)).mul_mem ((centralizer ({z} : Set X)).mul_mem hkC hwz)
      ((centralizer ({z} : Set X)).inv_mem hkC)
  have hvN : ∀ v ∈ P₂, v ∈ normalizer (A₁ : Set X) := fun v hv =>
    K0_le_normalizer_comp hA₁ (comp_le_K0 hA₂ (hP₂.1 hv))
  have hcovT : ∀ a ∈ A₁, ∃ x ∈ centralizer (P₂ : Set X), ∃ o ∈ oddCoreOf A₁, a = x * o := by
    intro a ha
    have hy : ∀ v ∈ P₂, a⁻¹ * (v * a * v⁻¹) ∈ oddCoreOf A₁ := by
      intro v hv
      have hvA : v * a * v⁻¹ ∈ A₁ := (Subgroup.mem_normalizer_iff.1 (hvN v hv) a).1 ha
      have hcg : ⁅a⁻¹, v⁆ ∈ pPrimeCoreOf 2 (K0 X n (centralizer ({z} : Set X))) :=
        comm_mem_of_ne hA₁ hA₂ h12 a⁻¹ (A₁.inv_mem ha) v (hP₂.1 hv)
      have e : a⁻¹ * (v * a * v⁻¹) = ⁅a⁻¹, v⁆ := by simp only [commutatorElement_def]; group
      have hmem : ⁅a⁻¹, v⁆ ∈ A₁ ⊓ pPrimeCoreOf 2 (K0 X n (centralizer ({z} : Set X))) :=
        ⟨by rw [← e]; exact A₁.mul_mem (A₁.inv_mem ha) hvA, hcg⟩
      rw [inf_core_eq hA₁] at hmem
      rw [e]
      exact hmem
    obtain ⟨p, hp, hcent⟩ := exists_fixed_mem_coset_of_isPGroup (odd_card_oddCoreOf A₁)
      hP₂.2.1 (fun v hv => mem_normalizer_oddCoreOf_of_mem_normalizer (hvN v hv)) hy
    exact ⟨a * p, hcent, p⁻¹, (oddCoreOf A₁).inv_mem hp, by group⟩
  obtain ⟨T, hT, hTP⟩ := exists_sylow_le_of_covers (A := A₁) (O := oddCoreOf A₁)
    (Xs := centralizer (P₂ : Set X)) (le_normalizer_oddCoreOf A₁) (odd_card_oddCoreOf A₁)
    ((oddCoreOf_le A₁).trans Subgroup.le_normalizer) hcovT
  obtain ⟨E₁, hE₁T, hE₁, hE₁4⟩ := exists_four_le_sylow hn8 hA₁ hT
  obtain ⟨v, hvE₁, hv1, hvz⟩ := fg_exists_ne h.orderOf_z (B := E₁) (by omega)
  have hvA₁ : v ∈ A₁ := hT.le (hE₁T hvE₁)
  have hv2' : v * v = 1 := AhatData.sq_of_isElemAbelian hE₁ v hvE₁
  have hcommzv : Commute z v := (comm_z_of_mem_comp hA₁ hvA₁).symm
  obtain ⟨V, hV, hV4, hVA, hzV, hPV⟩ : ∃ V : Subgroup X, Open.IsElemAbelian 2 V ∧
      Nat.card V = 4 ∧ V ≤ A₁ ∧ z ∈ V ∧ P₂ ≤ centralizer (V : Set X) := by
    refine ⟨four z v hz2 hv2' hcommzv, isElemAbelian_four z v hz2 hv2' hcommzv,
      card_four hz2 hv2' hcommzv hz1 hv1 (fun e => hvz e.symm), four_le hzA₁ hvA₁,
      left_mem_four, ?_⟩
    intro p hp
    rw [mem_centralizer_iff]
    intro x hx
    have hpz : Commute p z := comm_z_of_mem_comp hA₂ (hP₂.1 hp)
    have hpv : Commute p v := mem_centralizer_iff.1 (hTP (hE₁T hvE₁)) p hp
    exact (commute_of_mem_four hpz hpv hx).symm.eq
  obtain ⟨U, hUE, hU, hU4⟩ := exists_fourSub_of_le_card hE (by omega)
  let U' : FourSub P₂ := ⟨U, hUE.trans hEP, hU, hU4⟩
  have hprops := W1V_props h hA₂ hA₁ (Ne.symm h12) hV hV4 hVA hzV hP₂ hPV hR U'
  have hWM : Wgamma A₂ P₂ ≤ normalizer ((W1V V U : Subgroup X) : Set X) := by
    unfold Wgamma
    exact iSup_le fun c => iSup_le fun hc => iSup_le fun hc2 =>
      oddCore_le_normalizer_W1V h hA₂ hA₁ (Ne.symm h12) hV hV4 hVA hzV hP₂ hPV hR U' hc hc2
  intro hN
  have hnormW : (Wgamma A₂ P₂).Normal := ⟨fun w hw g =>
    (Subgroup.mem_normalizer_iff.1 (hN ▸ Subgroup.mem_top g) w).1 hw⟩
  haveI := hnormW
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Wgamma A₂ P₂) with hbot | htop
  · apply hkey
    intro u huP hu2 huz
    have hle : oddCoreOf (centralizer ({u} : Set X)) ≤ Wgamma A₂ P₂ :=
      fg_oddCore_le_Wgamma (hPG huP) hu2
    rw [hbot] at hle
    exact hle.trans bot_le
  · have hNW : normalizer ((W1V V U : Subgroup X) : Set X) = ⊤ := by
      rw [eq_top_iff, ← htop]
      exact hWM
    have hnormV : (W1V V U).Normal := ⟨fun w hw g =>
      (Subgroup.mem_normalizer_iff.1 (hNW ▸ Subgroup.mem_top g) w).1 hw⟩
    haveI := hnormV
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (W1V V U) with hb | ht
    · apply hkey
      intro u huP hu2 huz
      have hθ : theta V u ≤ W1V V U := hprops.2 u huP hu2
      rw [hb] at hθ
      intro y hy
      have hc : ⁅y, z⁆ ∈ (⊥ : Subgroup X) :=
        hθ ((le_sup_left : ⁅oddCoreOf (cen u), V⁆ ≤ theta V u)
          (Subgroup.commutator_mem_commutator hy hzV))
      have hc1 : ⁅y, z⁆ = 1 := Subgroup.mem_bot.1 hc
      exact mem_centralizer_singleton_iff.2 (commutatorElement_eq_one_iff_mul_comm.1 hc1)
    · exfalso
      have hodd := hprops.1
      rw [ht, Subgroup.card_top] at hodd
      have h2 : 2 ∣ Nat.card X := h.orderOf_z ▸ orderOf_dvd_natCard z
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)

private theorem fg_map_conj_W1_le {A : Subgroup X} {y : X} (hy : y ∈ normalizer (A : Set X)) :
    (W1 A).map (MulAut.conj y).toMonoidHom ≤ W1 A := by
  unfold W1
  rw [Subgroup.map_iSup]
  refine iSup_le fun b => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hb => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hb2 => ?_
  rw [fg_map_conj_oddCore_cen y b]
  have hyb : y * b * y⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.1 hy b).1 hb
  have hyb2 : orderOf (y * b * y⁻¹) = 2 := by
    have := MulEquiv.orderOf_eq (MulAut.conj y) b
    rw [hb2] at this
    exact this
  exact le_iSup_of_le (y * b * y⁻¹) (le_iSup_of_le hyb (le_iSup_of_le hyb2 le_rfl))

private theorem fg_normalizer_le_W1 (A : Subgroup X) :
    normalizer (A : Set X) ≤ normalizer ((W1 A : Subgroup X) : Set X) := by
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro w
  constructor
  · intro hw
    exact fg_map_conj_W1_le hy ⟨w, hw, rfl⟩
  · intro hw
    have := fg_map_conj_W1_le (Subgroup.inv_mem _ hy) ⟨y * w * y⁻¹, hw, rfl⟩
    have e : (MulAut.conj y⁻¹).toMonoidHom (y * w * y⁻¹) = w := by
      simp [MulAut.conj_apply, mul_assoc]
    rwa [e] at this

theorem normalizer_W1_ne_top
    (h : Sec5Data X n z (zpowers z) S) (hR : AhatFourInE8 n) (hne : TwoComps X n z)
    {A₁ : Subgroup X} (hA₁ : Sec5Comp X n (centralizer ({z} : Set X)) A₁)
    (hbad : ∃ b ∈ A₁, orderOf b = 2 ∧
      ¬ oddCoreOf (centralizer ({b} : Set X)) ≤ centralizer ({z} : Set X)) :
    normalizer ((W1 A₁ : Subgroup X) : Set X) ≠ ⊤ := by
  have hsimple := h.cex.simple
  obtain ⟨A₂, hA₂, hA₂ne⟩ := exists_comp_ne A₁ hne
  obtain ⟨P₂, hP₂⟩ := exists_isSylowTwoIn A₂
  have hR₂ : FourInE8 P₂ := fourInE8_of_ahat hR hA₂ hP₂
  have hN := normalizer_Wgamma_ne_top h hA₁ hA₂ (Ne.symm hA₂ne) hP₂ hR₂ hbad
  have hle : W1 A₁ ≤ normalizer ((Wgamma A₂ P₂ : Subgroup X) : Set X) := by
    unfold W1
    exact iSup_le fun b => iSup_le fun hb => iSup_le fun hb2 =>
      oddCore_le_normalizer_Wgamma h hA₁ hA₂ (Ne.symm hA₂ne) hP₂ hR₂ hb hb2
  have hne_bot : W1 A₁ ≠ ⊥ := by
    obtain ⟨b, hb, hb2, hbz⟩ := hbad
    intro hbot
    apply hbz
    have hmem : oddCoreOf (centralizer ({b} : Set X)) ≤ W1 A₁ :=
      le_iSup_of_le b (le_iSup_of_le hb (le_iSup_of_le hb2 le_rfl))
    rw [hbot] at hmem
    exact hmem.trans bot_le
  intro htop
  have hnorm : (W1 A₁).Normal := ⟨fun w hw g =>
    (Subgroup.mem_normalizer_iff.1 (htop ▸ Subgroup.mem_top g) w).1 hw⟩
  haveI := hnorm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (W1 A₁) with hb | ht
  · exact hne_bot hb
  · apply hN
    rw [eq_top_iff, ← ht]
    exact hle

theorem comp_le_normalizer_W1 {A₁ A : Subgroup X}
    (hA₁ : Sec5Comp X n (centralizer ({z} : Set X)) A₁)
    (hA : Sec5Comp X n (centralizer ({z} : Set X)) A) :
    A ≤ normalizer ((W1 A₁ : Subgroup X) : Set X) :=
  (comp_le_K0 hA).trans ((K0_le_normalizer_comp hA₁).trans (fg_normalizer_le_W1 A₁))

end Component

end CFSG.OddStandard.Solomon75
