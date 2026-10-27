module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3A6KFacts
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3A6Struct
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3A6Structb
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3SylowLift
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericCaseSetup
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerRank
import CFSG.LocalAnalysis.RankThreeTheoremC.InvariantTwoConstrained
public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCompetitorAux
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3M11Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

theorem a6l43_mem_of_normalizer_sylow {Y : Type*} [Group Y] [Finite Y] {p : ℕ}
    [Fact p.Prime] {S K : Subgroup Y} (hS : IsSylowOf p S K) {n : Y} (hnK : n ∈ K)
    (hnS : n ∈ normalizer (S : Set Y)) {k : ℕ} (hnk : n ^ p ^ k = 1) : n ∈ S := by
  set N : Subgroup Y := K ⊓ normalizer (S : Set Y) with hN
  have hSN : S ≤ N := le_inf hS.le Subgroup.le_normalizer
  have hNK : N ≤ K := inf_le_left
  have hnN : n ∈ N := ⟨hnK, hnS⟩
  have hSN' : IsSylowOf p S N := hS.of_le hSN hNK
  have hnorm : (S.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSN).mpr inf_le_right
  have hidx : ¬ p ∣ S.relIndex N := (isSylowOf_iff.mp hSN').2.2
  have hcop : Nat.Coprime (p ^ k) (S.relIndex N) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hidx)
  set q : ↥N →* ↥N ⧸ S.subgroupOf N := QuotientGroup.mk' (S.subgroupOf N) with hq
  have h1 : orderOf (q ⟨n, hnN⟩) ∣ p ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← map_pow]
    have : (⟨n, hnN⟩ : ↥N) ^ p ^ k = 1 :=
      Subtype.ext (by rw [SubgroupClass.coe_pow, OneMemClass.coe_one]; exact hnk)
    rw [this, map_one]
  have h2 : orderOf (q ⟨n, hnN⟩) ∣ S.relIndex N := by
    have := orderOf_dvd_natCard (q ⟨n, hnN⟩)
    rwa [← Subgroup.index_eq_card] at this
  have h3 : orderOf (q ⟨n, hnN⟩) = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  have h4 : q ⟨n, hnN⟩ = 1 := orderOf_eq_one_iff.mp h3
  exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff (⟨n, hnN⟩ : ↥N)).mp h4)

theorem a6l43_point_facts (hS : Setting G) (hU0 : FullCoreLocal G) (hA1 : A6SylowData)
    (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M)
    {x : G} (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsA6Normal M x J) :
    normalizer ((((P : Subgroup G) ⊓ J : Subgroup G)) : Set G) ≤ M ∧
      GLBPrimeCore 3 (centralizer ({x} : Set G)) ≤ M ∧
      M ⊓ centralizer ({x} : Set G) ≤
        normalizer ((((P : Subgroup G) ⊓ J) ⊔ GLBPrimeCore 3 (centralizer ({x} : Set G)) :
          Subgroup G) : Set G) := by
  have hf3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hDel : IsElemAbelian 3 ((P : Subgroup G) ⊓ J) := a6_inf_isElemAbelian hA1 hgen hJ
  have hDcard : Nat.card ↥((P : Subgroup G) ⊓ J) = 3 ^ 2 :=
    (a6_T_data hS hU0 hA1 hp hM hgen hJ).2.2
  have hD2 : 2 ≤ CFSG.Open.pRank 3 ((P : Subgroup G) ⊓ J) :=
    le_pRank_of_elemAbelian_card (p := 3) (k := 2) le_rfl hDel hDcard
  have hNΓ2 : normalizer ((((P : Subgroup G) ⊓ J : Subgroup G)) : Set G) ≤
      rankThreeGamma 2 3 (P : Subgroup G) := by
    unfold rankThreeGamma CFSG.Open.GLBCore
    exact le_sSup ⟨(P : Subgroup G) ⊓ J, inf_le_left, hD2, rfl⟩
  have hNM : normalizer ((((P : Subgroup G) ⊓ J : Subgroup G)) : Set G) ≤ M :=
    hNΓ2.trans (hU0 3 hp P M hM)
  have hOxM : GLBPrimeCore 3 (centralizer ({x} : Set G)) ≤ M :=
    (glbPrimeCore_le_pPrimeCoreIn 3 _).trans (pPrimeCoreIn_centralizer_le hS hp hM hgen.2.2.2.ge)
  refine ⟨hNM, hOxM, ?_⟩
  obtain ⟨Sbar, hSbar, hsh⟩ := exists_genericShadow3 hS hU0 hp rfl hM hgen
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  have hJC : J ≤ C := hJ.le_centralizer
  set O : Subgroup C := primeComplementCore (G := C) 3 with hO
  have hOcop : Nat.Coprime 3 (Nat.card O) := primeComplementCore_coprime 3
  set π : C →* C ⧸ O := QuotientGroup.mk' O with hπ
  set Q' : Subgroup C := ((P : Subgroup G) ⊓ C).subgroupOf C with hQ'
  have hQ'p : IsPGroup 3 Q' := (P.isPGroup'.to_le inf_le_left).comap_subtype
  set L : Subgroup (C ⧸ O) := r1sBar x J with hL
  have hLn : L.Normal := r1sBar_normal_a6 hJ
  set D' : Subgroup C := ((P : Subgroup G) ⊓ J).subgroupOf C with hD'
  have hD'Q : D' ≤ Q' := fun a ha =>
    Subgroup.mem_subgroupOf.mpr
      ⟨(Subgroup.mem_subgroupOf.mp ha).1, hJC (Subgroup.mem_subgroupOf.mp ha).2⟩
  have hD'p : IsPGroup 3 D' := hQ'p.to_le hD'Q
  set Db : Subgroup (C ⧸ O) := D'.map π with hDb
  set Γ : Subgroup (C ⧸ O) := ((C ⊓ M).subgroupOf C).map π with hΓdef
  have hSylJ : IsSylowOf 3 ((P : Subgroup G) ⊓ J) J := by
    have h := hgen.2.2.1.inf_of_le_normalizer hJC hJ.centralizer_le
    have hPJ : ((P : Subgroup G) ⊓ C) ⊓ J = (P : Subgroup G) ⊓ J := by
      rw [inf_assoc, inf_eq_right.mpr hJC]
    rwa [hPJ] at h
  obtain ⟨TJ, hTJ⟩ := hSylJ
  set S : Sylow 3 ↥L := TJ.mapSurjective (r1sHom_surjective x hJC) with hS'
  have hSmap : (S : Subgroup ↥L).map L.subtype = Db := by
    rw [hS', Sylow.coe_mapSurjective, Subgroup.map_map, hDb, hD', ← hTJ]
    have h1 : ((TJ : Subgroup ↥J).map J.subtype).subgroupOf C =
        (TJ : Subgroup ↥J).map (Subgroup.inclusion hJC) := by
      ext c
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map]
      constructor
      · rintro ⟨j, hj, hjc⟩
        exact ⟨j, hj, Subtype.ext hjc⟩
      · rintro ⟨j, hj, rfl⟩
        exact ⟨j, hj, rfl⟩
    rw [h1, Subgroup.map_map]
    rfl
  have hDbL : Db ≤ L := by
    rw [← hSmap]
    exact Subgroup.map_subtype_le _
  have hDbS : Db ≤ (Sbar : Subgroup (C ⧸ O)) := by
    rw [hSbar]
    exact Subgroup.map_mono fun a ha => Subgroup.mem_subgroupOf.mpr
      ⟨(Subgroup.mem_subgroupOf.mp ha).1, a.2⟩
  have hDbcard : Nat.card Db = 3 ^ 2 := by
    rw [hDb, CFSG.AGLEmbedding.card_map_mk_of_isPGroup Nat.prime_three O hOcop hD'p,
      hD', Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right.trans hJC)).toEquiv, hDcard]
  have hDbel : IsElemAbelian 3 Db := by
    have hcomm := hDel.1
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun z hz => ?_⟩
    · obtain ⟨a', ha', ha'π⟩ := a.2
      obtain ⟨b', hb', hb'π⟩ := b.2
      apply Subtype.ext
      show (a : C ⧸ O) * b = b * a
      rw [← ha'π, ← hb'π, ← map_mul, ← map_mul]
      exact congrArg π (Subtype.ext (setLike_mul_comm (Subgroup.mem_subgroupOf.mp ha')
        (Subgroup.mem_subgroupOf.mp hb')))
    · obtain ⟨z', hz', rfl⟩ := hz
      rw [← map_pow]
      have : z' ^ 3 = 1 :=
        Subtype.ext (by simpa using hDel.2 (z' : G) (Subgroup.mem_subgroupOf.mp hz'))
      rw [this, map_one]
  have hDb2 : 2 ≤ CFSG.Open.pRank 3 Db :=
    le_pRank_of_elemAbelian_card (p := 3) (k := 2) le_rfl hDbel hDbcard
  have hNΓ : normalizer (Db : Set (C ⧸ O)) ≤ Γ := hsh.normalizer_le Db hDbS hDb2
  have hLΓ : ¬ L ≤ Γ := by
    intro hle
    apply hJ.not_le
    intro j hj
    have hjL : π ⟨j, hJC hj⟩ ∈ L := ⟨⟨j, hJC hj⟩, Subgroup.mem_subgroupOf.mpr hj, rfl⟩
    obtain ⟨c, hc, hcπ⟩ := hle hjL
    have hco : c⁻¹ * ⟨j, hJC hj⟩ ∈ O := QuotientGroup.eq.mp hcπ
    have hOx : ((c⁻¹ * ⟨j, hJC hj⟩ : C) : G) ∈ GLBPrimeCore 3 C :=
      (CFSG.AGLEmbedding.mem_primeComplementCore_iff_mem_glbPrimeCore 3 _).mp hco
    have hcM : (c : G) ∈ M := (Subgroup.mem_subgroupOf.mp hc).2
    have e : j = (c : G) * ((c⁻¹ * ⟨j, hJC hj⟩ : C) : G) := by
      change j = (c : G) * ((c : G)⁻¹ * j)
      group
    rw [e]
    exact M.mul_mem hcM (hOxM hOx)
  have hmaxS := (hA1 ↥L (r1sBar_isA6 hJ) S).2.2 (Γ.comap L.subtype) (by
    intro n hn
    have h1 := Subgroup.le_normalizer_map L.subtype ⟨n, hn, rfl⟩
    rw [hSmap] at h1
    exact hNΓ h1)
  have hΓL : ∀ g ∈ Γ, ∀ hgL : g ∈ L,
      (⟨g, hgL⟩ : ↥L) ∈ normalizer ((S : Subgroup ↥L) : Set ↥L) := by
    intro g hg hgL
    rcases hmaxS with h | h
    · have : (⟨g, hgL⟩ : ↥L) ∈ Γ.comap L.subtype := hg
      rwa [h] at this
    · exfalso
      apply hLΓ
      intro l hl
      have : (⟨l, hl⟩ : ↥L) ∈ Γ.comap L.subtype := by rw [h]; exact Subgroup.mem_top _
      exact this
  have hSsyl : IsSylowOf 3 (S : Subgroup ↥L) ⊤ := by
    refine isSylowOf_iff.mpr ⟨le_top, S.isPGroup', ?_⟩
    rw [Subgroup.relIndex_top_right]
    exact S.not_dvd_index
  have hΓS : ∀ g ∈ Γ, ∀ s ∈ Db, g * s * g⁻¹ ∈ Db := by
    intro g hg s hs
    have hsΓ : s ∈ Γ := hNΓ (Subgroup.le_normalizer hs)
    have hgsΓ : g * s * g⁻¹ ∈ Γ := Γ.mul_mem (Γ.mul_mem hg hsΓ) (Γ.inv_mem hg)
    have hgsL : g * s * g⁻¹ ∈ L := hLn.conj_mem s (hDbL hs) g
    have hnorm := hΓL _ hgsΓ hgsL
    have hDbp : IsPGroup 3 Db := elementary_isPGroup 3 Db hDbel
    obtain ⟨k, hk⟩ := hDbp ⟨s, hs⟩
    have hk' : s ^ 3 ^ k = 1 := congrArg Subtype.val hk
    have hk3 : (⟨g * s * g⁻¹, hgsL⟩ : ↥L) ^ 3 ^ k = 1 :=
      Subtype.ext (by
        rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
        change (g * s * g⁻¹) ^ 3 ^ k = 1
        rw [conj_pow, hk', mul_one, mul_inv_cancel])
    have hmemS := a6l43_mem_of_normalizer_sylow hSsyl (Subgroup.mem_top _) hnorm hk3
    rw [← hSmap]
    exact ⟨_, hmemS, rfl⟩
  have hOxn : ∀ c ∈ C, ∀ o ∈ GLBPrimeCore 3 C, c * o * c⁻¹ ∈ GLBPrimeCore 3 C :=
    fun c hc o ho => (mem_normalizer_iff.mp
      (CFSG.AGLEmbedding.le_normalizer_glbPrimeCore 3 C hc) o).mp ho
  have hDOx : ∀ c ∈ M ⊓ C, ∀ d ∈ (P : Subgroup G) ⊓ J,
      c * d * c⁻¹ ∈ ((P : Subgroup G) ⊓ J) ⊔ GLBPrimeCore 3 C := by
    intro c hc d hd
    have hcC : c ∈ C := hc.2
    have hdC : d ∈ C := hJC hd.2
    set cC : C := ⟨c, hcC⟩ with hcC'
    set dC : C := ⟨d, hdC⟩ with hdC'
    have hcΓ : π cC ∈ Γ := ⟨cC, Subgroup.mem_subgroupOf.mpr ⟨hcC, hc.1⟩, rfl⟩
    have hdSL : π dC ∈ Db := ⟨dC, Subgroup.mem_subgroupOf.mpr hd, rfl⟩
    have h1 := hΓS _ hcΓ _ hdSL
    obtain ⟨d', hd', hd'π⟩ := h1
    have hd'π' : π d' = π (cC * dC * cC⁻¹) := by
      rw [hd'π, map_mul, map_mul, map_inv]
    have hco : d'⁻¹ * (cC * dC * cC⁻¹) ∈ O := QuotientGroup.eq.mp hd'π'
    have hOx : ((d'⁻¹ * (cC * dC * cC⁻¹) : C) : G) ∈ GLBPrimeCore 3 C :=
      (CFSG.AGLEmbedding.mem_primeComplementCore_iff_mem_glbPrimeCore 3 _).mp hco
    have hd'D : (d' : G) ∈ (P : Subgroup G) ⊓ J := Subgroup.mem_subgroupOf.mp hd'
    have hprod : (d' : G) * ((d'⁻¹ * (cC * dC * cC⁻¹) : C) : G) = c * d * c⁻¹ := by
      change (d' : G) * ((d' : G)⁻¹ * (c * d * c⁻¹)) = c * d * c⁻¹
      exact mul_inv_cancel_left _ _
    rw [← hprod]
    exact Subgroup.mul_mem_sup hd'D hOx
  refine Subgroup.le_normalizer_iff.mpr fun c hc k hk => ?_
  have hmap : (((P : Subgroup G) ⊓ J) ⊔ GLBPrimeCore 3 C).map (MulAut.conj c).toMonoidHom ≤
      ((P : Subgroup G) ⊓ J) ⊔ GLBPrimeCore 3 C := by
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨d, hd, rfl⟩
      exact hDOx c hc d hd
    · rintro _ ⟨o, ho, rfl⟩
      exact Subgroup.mem_sup_right (hOxn c hc.2 o ho)
  exact hmap ⟨k, hk, rfl⟩

theorem a6l43_strongClosed (hS : Setting G) (hU0 : FullCoreLocal G) (hA1 : A6SylowData)
    (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M)
    {x : G} (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsA6Normal M x J)
    (hPab : IsMulCommutative (P : Subgroup G))
    (hwc : ∀ g : G, (zpowers x).map (MulAut.conj g).toMonoidHom ≤ (P : Subgroup G) →
      (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers x) :
    ∀ a ∈ (P : Subgroup G) ⊓ J, ∀ g : G, g * a * g⁻¹ ∈ (P : Subgroup G) →
      g * a * g⁻¹ ∈ (P : Subgroup G) ⊓ J := by
  intro a ha g hg
  have hf3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hDel := a6_inf_isElemAbelian hA1 hgen hJ
  have ha3 : a ^ 3 = 1 := hDel.2 a ha
  have hxP : x ∈ (P : Subgroup G) := hgen.1
  by_cases ha1 : a = 1
  · rw [ha1, mul_one, mul_inv_cancel]
    exact one_mem _
  have := hPab
  obtain ⟨n, hnP, hn⟩ :=
    P.conj_eq_normalizer_conj_of_mem a g⁻¹ ha.1 (by rw [inv_inv]; exact hg)
  rw [inv_inv] at hn
  have hnP' : n ∈ normalizer ((P : Subgroup G) : Set G) := hnP
  have hle : (zpowers x).map (MulAut.conj n).toMonoidHom ≤ (P : Subgroup G) := by
    rintro _ ⟨y, hy, rfl⟩
    exact (mem_normalizer_iff.mp hnP' y).mp (zpowers_le.mpr hxP hy)
  have hnx : n * x * n⁻¹ ∈ zpowers x := by
    have h2 : n * x * n⁻¹ ∈ (zpowers x).map (MulAut.conj n).toMonoidHom :=
      ⟨x, mem_zpowers x, rfl⟩
    rwa [hwc n hle] at h2
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  have hJC : J ≤ C := hJ.le_centralizer
  have hnC : ∀ c ∈ C, n⁻¹ * c * n ∈ C := by
    intro c hc
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hnx
    have hcx : Commute c x := mem_centralizer_singleton_iff.mp hc
    have hcy : c * (n * x * n⁻¹) = (n * x * n⁻¹) * c := by
      rw [← hk]
      exact (Commute.zpow_right hcx k).eq
    refine mem_centralizer_singleton_iff.mpr ?_
    calc n⁻¹ * c * n * x = n⁻¹ * (c * (n * x * n⁻¹)) * n := by group
      _ = n⁻¹ * ((n * x * n⁻¹) * c) * n := by rw [hcy]
      _ = x * (n⁻¹ * c * n) := by group
  have hCmap : C.map (MulAut.conj n⁻¹).toMonoidHom = C := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨c, hc, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      exact hnC c hc
    · rw [Subgroup.card_map_of_injective (MulAut.conj n⁻¹).injective]
  set ψ : C ≃* C := ((MulAut.conj n⁻¹).subgroupMap C).trans (MulEquiv.subgroupCongr hCmap)
    with hψ
  have hψval : ∀ c : C, (ψ c : G) = n⁻¹ * c * n := fun c => by
    show ((MulAut.conj n⁻¹).subgroupMap C c : G) = n⁻¹ * c * n
    rw [MulEquiv.coe_subgroupMap_apply, MulAut.conj_apply, inv_inv]
  set O : Subgroup C := primeComplementCore (G := C) 3 with hO
  have hOψ : O.map ψ.toMonoidHom = O :=
    Subgroup.characteristic_iff_map_eq.mp (primeComplementCore_characteristic 3) ψ
  set ψb : C ⧸ O ≃* C ⧸ O := QuotientGroup.congr O O ψ hOψ with hψb
  set π : C →* C ⧸ O := QuotientGroup.mk' O with hπ
  have hψbπ : ∀ c, ψb (π c) = π (ψ c) := fun c => QuotientGroup.congr_mk' O O ψ hOψ c
  set L : Subgroup (C ⧸ O) := r1sBar x J with hL
  have hLn : L.Normal := r1sBar_normal_a6 hJ
  set L' : Subgroup (C ⧸ O) := L.map ψb.toMonoidHom with hL'
  have hL'n : L'.Normal := hLn.map ψb.toMonoidHom ψb.surjective
  have haC : a ∈ C := hJC ha.2
  have hbC : n⁻¹ * a * n ∈ C := hnC a haC
  have hbL' : π ⟨n⁻¹ * a * n, hbC⟩ ∈ L' := by
    refine ⟨π ⟨a, haC⟩, ⟨⟨a, haC⟩, Subgroup.mem_subgroupOf.mpr ha.2, rfl⟩, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, hψbπ]
    congr 1
    exact Subtype.ext (hψval _)
  have haπ : π ⟨a, haC⟩ ≠ 1 := by
    intro h1
    have h2 : (⟨a, haC⟩ : C) ∈ O := (QuotientGroup.eq_one_iff _).mp h1
    have h3 : orderOf (⟨a, haC⟩ : C) ∣ Nat.card O := by
      have := orderOf_dvd_natCard (⟨⟨a, haC⟩, h2⟩ : O)
      rwa [Subgroup.orderOf_mk] at this
    have h4 : orderOf (⟨a, haC⟩ : C) ∣ 3 := by
      apply orderOf_dvd_of_pow_eq_one
      exact Subtype.ext (by rw [SubgroupClass.coe_pow]; exact ha3)
    have h5 : orderOf (⟨a, haC⟩ : C) = 1 :=
      Nat.eq_one_of_dvd_coprimes (primeComplementCore_coprime 3) h4 h3
    apply ha1
    have := orderOf_eq_one_iff.mp h5
    exact congrArg Subtype.val this
  have haL : π ⟨a, haC⟩ ∈ L := ⟨⟨a, haC⟩, Subgroup.mem_subgroupOf.mpr ha.2, rfl⟩
  have hLL' : L' = L := by
    have hcard : Nat.card L' = Nat.card L := Subgroup.card_map_of_injective ψb.injective
    have := hLn
    have := hL'n
    have hN : ((L' ⊓ L).subgroupOf L).Normal := inferInstance
    rcases a6s_bar_normal_eq_bot_or_eq_top hJ _ hN with h | h
    · exfalso
      have hdis : Disjoint L' L := by
        rw [Subgroup.disjoint_def]
        intro z hz1 hz2
        have hz : (⟨z, hz2⟩ : L) ∈ (L' ⊓ L).subgroupOf L :=
          Subgroup.mem_subgroupOf.mpr ⟨hz1, hz2⟩
        rw [h] at hz
        exact congrArg Subtype.val (Subgroup.mem_bot.mp hz)
      have hL'C : L' ≤ reducedCentralizerOfJ x J := by
        intro u hu
        rw [r1s_reducedCentralizerOfJ_eq, mem_centralizer_iff]
        intro v hv
        exact (Subgroup.commute_of_normal_of_disjoint L' L hL'n hLn hdis u v hu hv).eq.symm
      have hcyc := a6_reducedCentralizer_isCyclic hS hU0 hA1 hp hM hgen hJ
      let _ : CommGroup ↥(reducedCentralizerOfJ x J) := hcyc.commGroup
      have hLc : ∀ u ∈ L, ∀ v ∈ L, u * v = v * u := by
        intro u hu v hv
        apply ψb.injective
        rw [map_mul, map_mul]
        have hu' : ψb u ∈ reducedCentralizerOfJ x J := hL'C ⟨u, hu, rfl⟩
        have hv' : ψb v ∈ reducedCentralizerOfJ x J := hL'C ⟨v, hv, rfl⟩
        exact congrArg Subtype.val
          (mul_comm (⟨_, hu'⟩ : ↥(reducedCentralizerOfJ x J)) ⟨_, hv'⟩)
      have hper := r1sBar_perfect_a6 hJ
      have htop : _root_.commutator ↥L = ⊤ := Group.isPerfect_def.mp hper
      have hbot : _root_.commutator ↥L = ⊥ := by
        rw [_root_.commutator, Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro u _
        rw [mem_centralizer_iff]
        intro v _
        exact Subtype.ext (hLc _ v.2 _ u.2)
      have h1 : (⟨π ⟨a, haC⟩, haL⟩ : L) ∈ _root_.commutator ↥L := by
        rw [htop]
        exact Subgroup.mem_top _
      rw [hbot, Subgroup.mem_bot] at h1
      exact haπ (congrArg Subtype.val h1)
    · have hle : L ≤ L' := fun z hz => by
        have hz' : (⟨z, hz⟩ : L) ∈ (L' ⊓ L).subgroupOf L := by
          rw [h]
          exact Subgroup.mem_top _
        exact (Subgroup.mem_subgroupOf.mp hz').1
      exact (Subgroup.eq_of_le_of_card_ge hle hcard.le).symm
  have hbL : π ⟨n⁻¹ * a * n, hbC⟩ ∈ L := by rw [← hLL']; exact hbL'
  have hb3 : (n⁻¹ * a * n) ^ 3 = 1 := by
    rw [show n⁻¹ * a * n = n⁻¹ * a * n⁻¹⁻¹ by rw [inv_inv], conj_pow, ha3, mul_one,
      mul_inv_cancel]
  have hbJ : n⁻¹ * a * n ∈ J := r1s_mem_of_mk_mem_a6 hJ hbC hb3 hbL
  refine ⟨hg, ?_⟩
  rw [hn]
  exact hbJ

end CFSG.LocalAnalysis.RankThreeTheoremC
