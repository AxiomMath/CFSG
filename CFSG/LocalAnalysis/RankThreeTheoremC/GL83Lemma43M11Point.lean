module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3M11P34S
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1L44b
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericCaseSetup
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerRank
import CFSG.LocalAnalysis.RankThreeTheoremC.InvariantTwoConstrained
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1P34c

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem m11_mem_of_normalizer_sylow {Y : Type*} [Group Y] [Finite Y] {p : ℕ}
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

private theorem m11_commutator_mem {Y : Type*} [Group Y] {L : Subgroup Y} [L.Normal]
    (hdec : ∀ y : Y, ∃ ℓ ∈ L, ∃ d ∈ centralizer (L : Set Y), y = ℓ * d)
    (hcomm : ∀ a ∈ centralizer (L : Set Y), ∀ b ∈ centralizer (L : Set Y), a * b = b * a)
    (y₁ y₂ : Y) : y₁ * y₂ * y₁⁻¹ * y₂⁻¹ ∈ L := by
  obtain ⟨ℓ₁, hℓ₁, d₁, hd₁, rfl⟩ := hdec y₁
  obtain ⟨ℓ₂, hℓ₂, d₂, hd₂, rfl⟩ := hdec y₂
  set q : Y →* Y ⧸ L := QuotientGroup.mk' L with hq
  have hq₁ : q ℓ₁ = 1 := (QuotientGroup.eq_one_iff ℓ₁).mpr hℓ₁
  have hq₂ : q ℓ₂ = 1 := (QuotientGroup.eq_one_iff ℓ₂).mpr hℓ₂
  have hd : q d₁ * q d₂ = q d₂ * q d₁ := by
    rw [← map_mul, ← map_mul, hcomm d₁ hd₁ d₂ hd₂]
  have key : q (ℓ₁ * d₁ * (ℓ₂ * d₂) * (ℓ₁ * d₁)⁻¹ * (ℓ₂ * d₂)⁻¹) = 1 := by
    simp only [map_mul, map_inv, hq₁, hq₂, one_mul]
    rw [hd]
    group
  exact (QuotientGroup.eq_one_iff (ℓ₁ * d₁ * (ℓ₂ * d₂) * (ℓ₁ * d₁)⁻¹ * (ℓ₂ * d₂)⁻¹)).mp key

theorem m11_point_facts (hS : Setting G) (hU0 : FullCoreLocal G)
    (hKM : CFSG.AGLEmbeddingD2.KFactM11Three) (hKA : KFactM11TwoSignalizer)
    (hKT : KFactM11SylowTransitive) (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G}
    {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M) {x : G} (hgen : IsGenericPoint 3 P M x)
    {J : Subgroup G} (hJ : IsM11Normal M x J) :
    normalizer ((((P : Subgroup G) ⊓ J : Subgroup G)) : Set G) ≤ M ∧
      GLBPrimeCore 3 (centralizer ({x} : Set G)) ≤ M ∧
      (∀ a ∈ (P : Subgroup G) ⊓ J, ∀ b ∈ (P : Subgroup G) ⊓ J, a ≠ 1 → b ≠ 1 →
        ∃ n ∈ centralizer ({x} : Set G),
          n ∈ normalizer ((((P : Subgroup G) ⊓ J : Subgroup G)) : Set G) ∧ n * a * n⁻¹ = b) ∧
      M ⊓ centralizer ({x} : Set G) ≤
        normalizer ((((P : Subgroup G) ⊓ J) ⊔ GLBPrimeCore 3 (centralizer ({x} : Set G)) :
          Subgroup G) : Set G) := by
  have hf3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hDel, hDcard, -⟩ := p34_inf_data hS hU0 hKM hKA hp hM hgen hJ
  have hD2 : 2 ≤ CFSG.Open.pRank 3 ((P : Subgroup G) ⊓ J) :=
    le_pRank_of_elemAbelian_card (p := 3) (k := 2) le_rfl hDel hDcard
  have hNΓ2 : normalizer ((((P : Subgroup G) ⊓ J : Subgroup G)) : Set G) ≤
      rankThreeGamma 2 3 (P : Subgroup G) := by
    unfold rankThreeGamma CFSG.Open.GLBCore
    exact le_sSup ⟨(P : Subgroup G) ⊓ J, inf_le_left, hD2, rfl⟩
  have hOxM : GLBPrimeCore 3 (centralizer ({x} : Set G)) ≤ M :=
    (glbPrimeCore_le_pPrimeCoreIn 3 _).trans (pPrimeCoreIn_centralizer_le hS hp hM hgen.2.2.2.ge)
  have hY := p34_yData hS hU0 hKM hKA hp hM hgen hJ
  obtain ⟨Sbar, hSbar, hsh⟩ := exists_genericShadow3 hS hU0 hp rfl hM hgen
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  have hJC : J ≤ C := hJ.le_centralizer
  set O : Subgroup C := primeComplementCore (G := C) 3 with hO
  have hOcop : Nat.Coprime 3 (Nat.card O) := primeComplementCore_coprime 3
  set π : C →* C ⧸ O := QuotientGroup.mk' O with hπ
  set Q' : Subgroup C := ((P : Subgroup G) ⊓ C).subgroupOf C with hQ'
  have hQ'p : IsPGroup 3 Q' := (P.isPGroup'.to_le inf_le_left).comap_subtype
  set L : Subgroup (C ⧸ O) := r1sBar x J with hL
  set SL : Subgroup (C ⧸ O) := (Sbar : Subgroup (C ⧸ O)) ⊓ L with hSL
  have hJn : (J.subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJC).mpr hJ.centralizer_le
  set D' : Subgroup C := ((P : Subgroup G) ⊓ J).subgroupOf C with hD'
  have hD'Q : D' ≤ Q' := fun a ha =>
    Subgroup.mem_subgroupOf.mpr ⟨(Subgroup.mem_subgroupOf.mp ha).1, a.2⟩
  have hD'p : IsPGroup 3 D' := hQ'p.to_le hD'Q
  have hπQ : Q'.map π = (Sbar : Subgroup (C ⧸ O)) := hSbar.symm
  have hmapD : D'.map π = SL := by
    apply le_antisymm
    · rintro _ ⟨a, ha, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [← hπQ]
        exact Subgroup.mem_map_of_mem _ (hD'Q ha)
      · exact ⟨a, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp ha).2, rfl⟩
    · intro s hs
      obtain ⟨k, hkQ, rfl⟩ : s ∈ Q'.map π := by
        rw [hπQ]
        exact hs.1
      obtain ⟨j, hj, hjk⟩ := hs.2
      have hjo : j⁻¹ * k ∈ O := QuotientGroup.eq.mp hjk
      obtain ⟨a, ha⟩ := IsPGroup.iff_orderOf.mp hQ'p ⟨k, hkQ⟩
      have hka : orderOf k = 3 ^ a := by
        rw [← Subgroup.orderOf_mk k hkQ]
        exact ha
      have hkJ : k ∈ J.subgroupOf C :=
        mem_of_mul_core (J := J.subgroupOf C) hOcop hj hjo (by group) ⟨a, hka⟩
      exact ⟨k, Subgroup.mem_subgroupOf.mpr
        ⟨(Subgroup.mem_subgroupOf.mp hkQ).1, Subgroup.mem_subgroupOf.mp hkJ⟩, rfl⟩
  have hπD : ∀ a ∈ D', π a ∈ SL := fun a ha => hmapD ▸ Subgroup.mem_map_of_mem _ ha
  have hmapG : D'.map C.subtype = (P : Subgroup G) ⊓ J :=
    Subgroup.map_subgroupOf_eq_of_le (inf_le_right.trans hJC)
  refine ⟨hNΓ2.trans (hU0 3 hp P M hM), hOxM, ?_, ?_⟩
  ·
    intro a ha b hb ha1 hb1
    have haD : a ∈ D'.map C.subtype := by rw [hmapG]; exact ha
    have hbD : b ∈ D'.map C.subtype := by rw [hmapG]; exact hb
    obtain ⟨a', ha', rfl⟩ := haD
    obtain ⟨b', hb', rfl⟩ := hbD
    have hπa1 : π a' ≠ 1 := fun h => ha1 (by
      have : a' = 1 := p34_mk_inj hOcop hQ'p (hD'Q ha') Q'.one_mem (by rw [h, map_one])
      rw [this]; rfl)
    have hπb1 : π b' ≠ 1 := fun h => hb1 (by
      have : b' = 1 := p34_mk_inj hOcop hQ'p (hD'Q hb') Q'.one_mem (by rw [h, map_one])
      rw [this]; rfl)
    obtain ⟨nb, -, hnbN, hnb⟩ :=
      hY.sylow_transitive hKT Sbar (hπD a' ha') (hπD b' hb') hπa1 hπb1
    obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective O nb
    have hn : n ∈ (normalizer ((D'.map π : Subgroup (C ⧸ O)) : Set (C ⧸ O))).comap π := by
      rw [Subgroup.mem_comap, hmapD]
      exact hnbN
    have hfr := CFSG.AGLEmbedding.comap_normalizer_map_le_sup Nat.prime_three O hOcop hD'p hn
    have hfr' : n ∈ ((O ⊔ normalizer (D' : Set C) : Subgroup C) : Set C) := hfr
    rw [Subgroup.normal_mul] at hfr'
    obtain ⟨o, ho, n₁, hn₁, hon⟩ := hfr'
    have hon' : o * n₁ = n := hon
    have ho' : π o = 1 := (QuotientGroup.eq_one_iff o).mpr ho
    have hπn : π n = π n₁ := by rw [← hon', map_mul, ho', one_mul]
    have hmem : n₁ * a' * n₁⁻¹ ∈ D' := (mem_normalizer_iff.mp hn₁ a').mp ha'
    have heq : n₁ * a' * n₁⁻¹ = b' := by
      refine p34_mk_inj hOcop hQ'p (hD'Q hmem) (hD'Q hb') ?_
      rw [map_mul, map_mul, map_inv, ← hπn]
      exact hnb
    refine ⟨(n₁ : G), n₁.2, ?_, congrArg Subtype.val heq⟩
    have hnorm : (n₁ : G) ∈ normalizer ((D'.map C.subtype : Subgroup G) : Set G) :=
      Subgroup.le_normalizer_map C.subtype ⟨n₁, hn₁, rfl⟩
    rw [hmapG] at hnorm
    exact hnorm
  ·
    have hLn : L.Normal := hY.normal
    have hdec : ∀ y : C ⧸ O, ∃ ℓ ∈ L, ∃ d ∈ centralizer (L : Set (C ⧸ O)), y = ℓ * d :=
      hY.decomp hKM
    have hDS : centralizer (L : Set (C ⧸ O)) ≤ (Sbar : Subgroup (C ⧸ O)) :=
      hY.centralizer_le_sylow Sbar
    set Γ : Subgroup (C ⧸ O) := ((C ⊓ M).subgroupOf C).map π with hΓdef
    have hΓ : Γ ≠ ⊤ := hsh.ne_top
    have hNΓ : normalizer ((Sbar : Subgroup (C ⧸ O)) : Set (C ⧸ O)) ≤ Γ :=
      hsh.normalizer_le _ le_rfl (by rw [hsh.rank_eq]; norm_num)
    obtain ⟨T, hT⟩ := hY.exists_sylow_eq_inf Sbar
    obtain ⟨e⟩ := hY.equiv
    obtain ⟨-, hsyl⟩ := hKM ↥L ⟨e⟩
    obtain ⟨-, -, hmaxT⟩ := hsyl T
    have hmax' : ∀ Z : Subgroup (C ⧸ O), Z ≤ L →
        L ⊓ normalizer (((Sbar : Subgroup (C ⧸ O)) ⊓ L : Subgroup (C ⧸ O)) : Set (C ⧸ O)) ≤ Z →
        Z ≤ L ⊓ normalizer (((Sbar : Subgroup (C ⧸ O)) ⊓ L : Subgroup (C ⧸ O)) :
          Set (C ⧸ O)) ∨ L ≤ Z := by
      intro Z hZL hNZ
      have hle : normalizer (T : Set L) ≤ Z.subgroupOf L := by
        intro n hn
        have h1 := Subgroup.le_normalizer_map L.subtype ⟨n, hn, rfl⟩
        rw [hT] at h1
        exact hNZ ⟨n.2, h1⟩
      rcases hmaxT (Z.subgroupOf L) hle with h | h
      · refine Or.inl fun z hz => ⟨hZL hz, ?_⟩
        have h2 : (⟨z, hZL hz⟩ : L) ∈ Z.subgroupOf L := hz
        rw [h] at h2
        have h3 := Subgroup.le_normalizer_map L.subtype ⟨⟨z, hZL hz⟩, h2, rfl⟩
        rwa [hT] at h3
      · exact Or.inr fun l hl =>
          (h ▸ mem_top (⟨l, hl⟩ : L) : (⟨l, hl⟩ : L) ∈ Z.subgroupOf L)
    have hnormEq := l44_normalizer_inf_eq hdec hDS hΓ hNΓ hmax'
    have hSyl : IsSylowOf 3 SL L := ⟨T, hT⟩
    have hΓS : ∀ g ∈ Γ, ∀ s ∈ SL, g * s * g⁻¹ ∈ SL := by
      intro g hg s hs
      have hsS : s ∈ (Sbar : Subgroup (C ⧸ O)) := hs.1
      have hsΓ : s ∈ Γ := hNΓ (Subgroup.le_normalizer hsS)
      have hgsΓ : g * s * g⁻¹ ∈ Γ := Γ.mul_mem (Γ.mul_mem hg hsΓ) (Γ.inv_mem hg)
      have hgsL : g * s * g⁻¹ ∈ L := hLn.conj_mem s hs.2 g
      have hnorm := hnormEq _ hgsΓ hgsL
      obtain ⟨k, hk⟩ := Sbar.isPGroup' ⟨s, hsS⟩
      have hk' : s ^ 3 ^ k = 1 := congrArg Subtype.val hk
      have hk3 : (g * s * g⁻¹) ^ 3 ^ k = 1 := by
        rw [conj_pow, hk', mul_one, mul_inv_cancel]
      exact m11_mem_of_normalizer_sylow hSyl hgsL hnorm hk3
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
      have hdSL : π dC ∈ SL := hπD dC (Subgroup.mem_subgroupOf.mpr hd)
      have h1 := hΓS _ hcΓ _ hdSL
      rw [← hmapD] at h1
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

theorem m11_point_strongClosed (hS : Setting G) (hU0 : FullCoreLocal G)
    (hKM : CFSG.AGLEmbeddingD2.KFactM11Three) (hKA : KFactM11TwoSignalizer)
    (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M)
    {x : G} (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsM11Normal M x J)
    (hPab : IsMulCommutative (P : Subgroup G))
    (hwc : ∀ g : G, (zpowers x).map (MulAut.conj g).toMonoidHom ≤ (P : Subgroup G) →
      (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers x) :
    ∀ a ∈ (P : Subgroup G) ⊓ J, ∀ g : G, g * a * g⁻¹ ∈ (P : Subgroup G) →
      g * a * g⁻¹ ∈ (P : Subgroup G) ⊓ J := by
  intro a ha g hg
  have hf3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hY := p34_yData hS hU0 hKM hKA hp hM hgen hJ
  obtain ⟨hDel, -, -⟩ := p34_inf_data hS hU0 hKM hKA hp hM hgen hJ
  have ha3 : a ^ 3 = 1 := hDel.2 a ha
  have hxP : x ∈ (P : Subgroup G) := hgen.1
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
  set O : Subgroup C := primeComplementCore (G := C) 3 with hO
  set π : C →* C ⧸ O := QuotientGroup.mk' O with hπ
  set L : Subgroup (C ⧸ O) := r1sBar x J with hL
  have hLn : L.Normal := hY.normal
  have hcommL : ∀ y₁ y₂ : C ⧸ O, y₁ * y₂ * y₁⁻¹ * y₂⁻¹ ∈ L :=
    m11_commutator_mem (hY.decomp hKM) fun u hu v hv =>
      p34_comm_of_isMulCommutative hY.commutative hu hv
  let Z0 : ↥J →* ↥C :=
    { toFun := fun j => ⟨n⁻¹ * (j : G) * n, hnC _ (hJC j.2)⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun j₁ j₂ => Subtype.ext (by
        change n⁻¹ * ((j₁ : G) * j₂) * n = (n⁻¹ * (j₁ : G) * n) * (n⁻¹ * (j₂ : G) * n)
        group) }
  have hZL : ∀ j : ↥J, π (Z0 j) ∈ L := by
    have hle' : ⁅(⊤ : Subgroup ↥J), (⊤ : Subgroup ↥J)⁆ ≤ L.comap (π.comp Z0) := by
      refine Subgroup.commutator_le.mpr fun j₁ _ j₂ _ => ?_
      rw [Subgroup.mem_comap, map_commutatorElement, commutatorElement_def]
      exact hcommL _ _
    have htop : _root_.commutator ↥J = ⊤ := Group.isPerfect_def.mp hJ.perfect
    intro j
    have hj : j ∈ _root_.commutator ↥J := by
      rw [htop]
      exact Subgroup.mem_top j
    exact hle' hj
  have hbC : n⁻¹ * a * n ∈ C := hnC a (hJC ha.2)
  have hb3 : (n⁻¹ * a * n) ^ 3 = 1 := by
    rw [← hn, conj_pow, ha3, mul_one, mul_inv_cancel]
  have hbL : π ⟨n⁻¹ * a * n, hbC⟩ ∈ L := hZL ⟨a, ha.2⟩
  have hbJ : n⁻¹ * a * n ∈ J := r1s_mem_of_mk_mem hJ hbC hb3 hbL
  refine ⟨hg, ?_⟩
  rw [hn]
  exact hbJ

end CFSG.LocalAnalysis.RankThreeTheoremC
