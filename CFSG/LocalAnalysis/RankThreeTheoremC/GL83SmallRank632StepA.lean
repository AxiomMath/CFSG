module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank632Defs
public import CFSG.RankThree.PartTwo.KFacts.KS44OutSz
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank632NearCyclic
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank632LemmaA
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank632Coprime
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank632StepASetup

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.RankThree.PartTwo.KFacts Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem stepA_primeCore_eq_map (p : ℕ) (M : Subgroup G) :
    rankThreePrimeCore p M = (primeComplementCore (G := M) p).map M.subtype := by
  apply le_antisymm
  · refine sSup_le fun N hN => ?_
    obtain ⟨hNM, hnormal, hcop⟩ := hN
    rw [← map_subgroupOf_eq_of_le hNM]
    refine map_mono (normal_coprime_le_primeComplementCore p _ hnormal ?_)
    rwa [Nat.card_congr (subgroupOfEquivOfLe hNM).toEquiv]
  · refine le_sSup ⟨map_subtype_le _, ?_, ?_⟩
    · rw [show ((primeComplementCore (G := M) p).map M.subtype).subgroupOf M =
          primeComplementCore (G := M) p from
          comap_map_eq_self_of_injective M.subtype_injective _]
      infer_instance
    · rw [card_map_of_injective M.subtype_injective]
      exact primeComplementCore_coprime p

omit [Finite G] in
private theorem stepA_isSolvable_map {M : Subgroup G} (D : Subgroup M) [Group.IsSolvable D] :
    Group.IsSolvable ↥(D.map M.subtype) :=
  Group.isSolvable_of_surjective
    (f := (D.equivMapOfInjective M.subtype M.subtype_injective).toMonoidHom)
    (MulEquiv.surjective _)

private theorem stepA_subgroupOf_le {p : ℕ} {M T : Subgroup G}
    (hT : T ≤ rankThreePrimeCore p M) : T.subgroupOf M ≤ primeComplementCore (G := M) p := by
  intro t ht
  have hmem : (t : G) ∈ (primeComplementCore (G := M) p).map M.subtype :=
    stepA_primeCore_eq_map p M ▸ hT ht
  obtain ⟨d, hd, hdt⟩ := hmem
  rwa [← Subtype.ext hdt]

private theorem stepA_index_subgroupOf {p : ℕ} {M T : Subgroup G} :
    ((T.subgroupOf M).subgroupOf (primeComplementCore (G := M) p)).index =
      (T.subgroupOf (rankThreePrimeCore p M)).index := by
  rw [stepA_primeCore_eq_map]
  exact relIndex_comap T M.subtype _

omit [Finite G] in
private theorem stepA_le_normalizer {M T K : Subgroup G} (hTM : T ≤ M)
    (hK : K ≤ normalizer (T : Set G)) :
    K.subgroupOf M ≤ normalizer ((T.subgroupOf M : Subgroup M) : Set M) := by
  rw [← subgroupOf_normalizer_eq hTM]
  exact comap_mono hK

omit [Finite G] in
private theorem stepA_mem_centralizer_map {M : Subgroup G} {K : Subgroup M} {a : M}
    (ha : a ∈ centralizer (K : Set M)) :
    (a : G) ∈ centralizer ((K.map M.subtype : Subgroup G) : Set G) := by
  rw [mem_centralizer_iff] at ha ⊢
  rintro _ ⟨k, hk, rfl⟩
  exact congrArg Subtype.val (ha k hk)

omit [Finite G] in
private theorem stepA_isCyclic_of_map_le {M : Subgroup G} {K : Subgroup M} {C : Subgroup G}
    [IsCyclic C] (h : K.map M.subtype ≤ C) : IsCyclic K :=
  have : IsCyclic ↥(K.map M.subtype) := isCyclic_of_le h
  isCyclic_of_surjective _ (K.equivMapOfInjective M.subtype M.subtype_injective).symm.surjective

private theorem stepA_nearCyclic_of_map_le {M : Subgroup G} {K : Subgroup M} {C : Subgroup G}
    (hC : NearCyclic C) (h : K.map M.subtype ≤ C) : NearCyclic K :=
  NearCyclic.of_injective
    ((inclusion h).comp (K.equivMapOfInjective M.subtype M.subtype_injective).toMonoidHom)
    ((inclusion_injective h).comp (MulEquiv.injective _)) hC

section Sections

variable {M : Type*} [Group M] [Finite M] {D R A T : Subgroup M} [D.Normal] [R.Normal]

omit [Finite M] [D.Normal] [R.Normal] in
private theorem stepA_zpowers_le_comap {Y : Type*} [Group Y] (π : M →* Y) {Q : Subgroup Y}
    {a : M} (ha : ∀ q ∈ Q, π a * q = q * π a) :
    zpowers a ≤ (centralizer (Q : Set Y)).comap π :=
  zpowers_le.mpr (mem_centralizer_iff.mpr fun q hq => (ha q hq).symm)

omit [Finite M] [D.Normal] [R.Normal] in
private theorem stepA_commute_of_le_comap {Y : Type*} [Group Y] (π : M →* Y) {Q : Subgroup Y}
    (hA : A ≤ (centralizer (Q : Set Y)).comap π) : ∀ a ∈ A, ∀ q ∈ Q, π a * q = q * π a :=
  fun _ ha q hq => ((mem_centralizer_iff.mp (hA ha)) q hq).symm

private theorem stepA_isCyclic_of_section (hRD : R ≤ D) (hD3 : ¬ 3 ∣ Nat.card D)
    (hA : IsPGroup 3 A) (hT : T ≤ D) (hT2 : IsPGroup 2 T)
    (hTsyl : ¬ 2 ∣ (T.subgroupOf D).index) (hAT : A ≤ normalizer (T : Set M))
    (hcyc : IsCyclic ↥(T ⊓ centralizer (A : Set M))) {Q : Subgroup (M ⧸ R)}
    (hQ2 : IsPGroup 2 Q) (hQD : Q ≤ D.map (QuotientGroup.mk' R))
    (hQA : ∀ a ∈ A, ∀ q ∈ Q, QuotientGroup.mk' R a * q = q * QuotientGroup.mk' R a) :
    IsCyclic Q := by
  obtain ⟨H, c, hH, hHQ⟩ := exists_section_of_two_subgroup_centralizer hRD hD3 hA hT hT2 hTsyl
    hAT hQ2 hQD hQA
  have : IsCyclic H := isCyclic_of_le hH
  have hmap : IsCyclic ↥(H.map (QuotientGroup.mk' R)) :=
    isCyclic_of_surjective _ ((QuotientGroup.mk' R).subgroupMap_surjective H)
  rw [hHQ] at hmap
  exact isCyclic_of_surjective _
    (Q.equivMapOfInjective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective).symm.surjective

private theorem stepA_nearCyclic_of_section (hRD : R ≤ D) (hD3 : ¬ 3 ∣ Nat.card D)
    (hA : IsPGroup 3 A) (hT : T ≤ D) (hT2 : IsPGroup 2 T)
    (hTsyl : ¬ 2 ∣ (T.subgroupOf D).index) (hAT : A ≤ normalizer (T : Set M))
    (hnear : NearCyclic ↥(T ⊓ centralizer (A : Set M))) {Q : Subgroup (M ⧸ R)}
    (hQ2 : IsPGroup 2 Q) (hQD : Q ≤ D.map (QuotientGroup.mk' R))
    (hQA : ∀ a ∈ A, ∀ q ∈ Q, QuotientGroup.mk' R a * q = q * QuotientGroup.mk' R a) :
    NearCyclic Q := by
  obtain ⟨H, c, hH, hHQ⟩ := exists_section_of_two_subgroup_centralizer hRD hD3 hA hT hT2 hTsyl
    hAT hQ2 hQD hQA
  have hH' : NearCyclic H := NearCyclic.of_injective (inclusion hH) (inclusion_injective hH) hnear
  have hmap : NearCyclic ↥(H.map (QuotientGroup.mk' R)) :=
    NearCyclic.of_surjective _ ((QuotientGroup.mk' R).subgroupMap_surjective H) hH'
  rw [hHQ] at hmap
  exact NearCyclic.of_mulEquiv
    (Q.equivMapOfInjective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective) hmap

omit [Finite M] [D.Normal] in
private theorem stepA_index_ne_three (hO3 : ∀ K : Subgroup M, K.Normal → K.index ≠ 3) :
    ∀ K : Subgroup (M ⧸ R), K.Normal → K.index ≠ 3 := fun K hK h3 =>
  hO3 (K.comap (QuotientGroup.mk' R)) (hK.comap _)
    ((index_comap_of_surjective K (QuotientGroup.mk'_surjective R)).trans h3)

end Sections

private theorem stepA_false {M : Type} [Group M] [Finite M]
    {D R : Subgroup M} [D.Normal] [R.Normal] (hRD : R ≤ D) (hD3 : ¬ 3 ∣ Nat.card D)
    {N : Subgroup (M ⧸ R)} [N.Normal] {r : ℕ} {S : Fin r → Subgroup (M ⧸ R)}
    (hND : N ≤ D.map (QuotientGroup.mk' R)) (hN3 : ¬ 3 ∣ Nat.card N) (hr : 1 ≤ r)
    (hSF : SimpleFactorData N S) (hSz : ∀ i, ∃ f, CFSG.Blueprint.SuzukiModel (S i) 2 f)
    {P T : Subgroup M} (hP : IsPGroup 3 P) (hT : T ≤ D) (hT2 : IsPGroup 2 T)
    (hTsyl : ¬ 2 ∣ (T.subgroupOf D).index) (hPT : P ≤ normalizer (T : Set M)) {x z g : M}
    (hxP : x ∈ P) (hzP : z ∈ P) (hx : x ^ 3 = 1) (hz : z ^ 3 = 1) (hxz : x * z = z * x)
    {b : ℕ} (hb : ¬ 3 ∣ b) (hg : g * x * g⁻¹ = x * z ^ b)
    (hcyc : IsCyclic ↥(T ⊓ centralizer ((zpowers x ⊔ zpowers z : Subgroup M) : Set M)))
    (hnear : NearCyclic ↥(T ⊓ centralizer ((zpowers x : Subgroup M) : Set M)))
    (hO3 : ∀ K : Subgroup M, K.Normal → K.index ≠ 3) : False := by
  have hBP : zpowers x ⊔ zpowers z ≤ P := sup_le (zpowers_le.mpr hxP) (zpowers_le.mpr hzP)
  refine false_of_normal_suzuki_product hN3 hr hSF hSz (x := QuotientGroup.mk' R x)
    (z := QuotientGroup.mk' R z) (g := QuotientGroup.mk' R g) (by rw [← map_pow, hx, map_one])
    (by rw [← map_pow, hz, map_one]) (by rw [← map_mul, ← map_mul, hxz]) hb
    (by rw [← map_inv, ← map_mul, ← map_mul, ← map_pow, ← map_mul, hg]) ?_ ?_
    (stepA_index_ne_three hO3)
  · intro Q hQN hQ2 hQx hQz
    exact stepA_isCyclic_of_section hRD hD3 (hP.to_le hBP) hT hT2 hTsyl (hBP.trans hPT) hcyc hQ2
      (hQN.trans hND) (stepA_commute_of_le_comap _ (sup_le (stepA_zpowers_le_comap _ hQx)
        (stepA_zpowers_le_comap _ hQz)))
  · intro Q hQN hQ2 hQx
    exact stepA_nearCyclic_of_section hRD hD3 (hP.to_le (zpowers_le.mpr hxP)) hT hT2 hTsyl
      ((zpowers_le.mpr hxP).trans hPT) hnear hQ2 (hQN.trans hND)
      (stepA_commute_of_le_comap _ (stepA_zpowers_le_comap _ hQx))

omit [Finite G] in
private theorem stepA_primeCore_le (p : ℕ) (M : Subgroup G) : rankThreePrimeCore p M ≤ M :=
  sSup_le fun _ hN => hN.1

omit [Finite G] in
private theorem stepA_isCyclic_centralizer_sup {M T : Subgroup G} {x z : G} (hx : x ∈ M)
    (hz : z ∈ M)
    (h : IsCyclic ↥(T ⊓ centralizer ((zpowers x ⊔ zpowers z : Subgroup G) : Set G))) :
    IsCyclic ↥(T.subgroupOf M ⊓
      centralizer ((zpowers (⟨x, hx⟩ : M) ⊔ zpowers ⟨z, hz⟩ : Subgroup M) : Set M)) := by
  refine stepA_isCyclic_of_map_le
    (C := T ⊓ centralizer ((zpowers x ⊔ zpowers z : Subgroup G) : Set G)) ?_
  rintro _ ⟨a, ⟨haT, haC⟩, rfl⟩
  refine ⟨haT, ?_⟩
  have hmem := stepA_mem_centralizer_map haC
  rwa [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers] at hmem

private theorem stepA_nearCyclic_centralizer {M T : Subgroup G} {x : G} (hx : x ∈ M)
    (h : NearCyclic ↥(T ⊓ centralizer ({x} : Set G))) :
    NearCyclic
      ↥(T.subgroupOf M ⊓ centralizer ((zpowers (⟨x, hx⟩ : M) : Subgroup M) : Set M)) := by
  refine stepA_nearCyclic_of_map_le h ?_
  rintro _ ⟨a, ⟨haT, haC⟩, rfl⟩
  refine ⟨haT, mem_centralizer_singleton_iff.mpr ?_⟩
  exact (congrArg Subtype.val (mem_centralizer_iff.mp haC _ (mem_zpowers _))).symm

theorem isSolvable_primeCore_of_data (hKP : KPSz) (hS : Setting G)
    {P : Sylow 3 G} {M : Subgroup G} (hs : SmallRankSituation G 3 P M) {x z g : G}
    {T : Subgroup G} (hd : SmallRank3Data P M x z g T)
    (hO3 : ∀ K : Subgroup M, K.Normal → K.index ≠ 3) :
    Group.IsSolvable ↥(rankThreePrimeCore 3 M) := by
  have hPM : (P : Subgroup G) ≤ M :=
    (sylow_le_of_isCoreMaxLocal hS hs.mem_sigmaA hs.isCoreMaxLocal).1
  have hMtop : M ≠ ⊤ := by
    have := hS.simple
    exact CFSG.RankThreeCoreUniqueness.Helpers.twoLocal_ne_top hS.nonab M hs.isCoreMaxLocal.1.1
  have hTM : T ≤ M := hd.sylowTwo.le_core.trans (stepA_primeCore_le 3 M)
  rw [stepA_primeCore_eq_map]
  by_contra hsol
  have hD3 : ¬ 3 ∣ Nat.card (primeComplementCore (G := M) 3) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (primeComplementCore_coprime 3)
  obtain ⟨R, hRn, hRD, -, N, hNn, r, S, hND, hN3, hr, hSF, hSz⟩ :=
    exists_suzuki_normal_product hKP
      (CFSG.AGLEmbedding.catalogSimpleSections_of_isKProper hS.kProper M hMtop) hD3
      (fun h => hsol (stepA_isSolvable_map _))
  have := hRn
  have := hNn
  obtain ⟨b, hb, hgx⟩ := hd.g_act
  have hxz : x * z = z * x := mem_centralizer_iff.mp hd.central.centralizes x hd.point.mem
  have hTD : T.subgroupOf M ≤ primeComplementCore (G := M) 3 :=
    stepA_subgroupOf_le hd.sylowTwo.le_core
  have hTsyl : ¬ 2 ∣ ((T.subgroupOf M).subgroupOf (primeComplementCore (G := M) 3)).index := by
    rw [stepA_index_subgroupOf]
    exact hd.sylowTwo.index_odd
  exact stepA_false (M := M) hRD hD3 hND hN3 hr hSF hSz P.isPGroup'.comap_subtype hTD
    hd.sylowTwo.isPGroup.comap_subtype hTsyl (stepA_le_normalizer hTM hd.sylowTwo.normalized)
    (x := ⟨x, hPM hd.point.mem⟩) (z := ⟨z, hPM hd.central.mem⟩) (g := ⟨g, hPM hd.g_mem⟩)
    hd.point.mem hd.central.mem (Subtype.ext hd.point.pow_eq_one)
    (Subtype.ext hd.central.pow_eq_one) (Subtype.ext hxz) hb (Subtype.ext hgx)
    (stepA_isCyclic_centralizer_sup _ _ hd.cyc) (stepA_nearCyclic_centralizer _ hd.near) hO3

end CFSG.LocalAnalysis.RankThreeTheoremC
