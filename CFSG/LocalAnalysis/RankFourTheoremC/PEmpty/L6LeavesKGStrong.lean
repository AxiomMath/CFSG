module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKGCfg
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesNSSection
import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseCCore
import CFSG.LocalAnalysis.AGLEmbeddingD2.EscapeMaxTools
import CFSG.Holt.PermFactsInvolutions
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKGDefs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KGC

open CFSG.Open CFSG.GH74.Uniqueness.SU Subgroup

theorem isSimpleSection_comap {Y Z : Type} [Group Y] [Group Z] (π : Y →* Z)
    (hπ : Function.Surjective π) {K N : Subgroup Z} (h : S622IsSimpleSection K N) :
    S622IsSimpleSection (K.comap π) (N.comap π) := by
  obtain ⟨hNK, hNn, hne, hmin, hnab⟩ := h
  have hNn' := (Subgroup.normal_subgroupOf_iff hNK).1 hNn
  have hNK' : N.comap π ≤ K.comap π := Subgroup.comap_mono hNK
  refine ⟨hNK', ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.normal_subgroupOf_iff hNK']
    intro n k hn hk
    have hn' : π n ∈ N := hn
    have hk' : π k ∈ K := hk
    show π (k * n * k⁻¹) ∈ N
    rw [map_mul, map_mul, map_inv]
    exact hNn' _ _ hn' hk'
  · intro heq
    exact hne (Subgroup.comap_injective hπ heq)
  · intro N' hN'1 hN'2 hN'n
    have hker : π.ker ≤ N' := fun x hx => hN'1 (by
      show π x ∈ N
      rw [MonoidHom.mem_ker.mp hx]
      exact N.one_mem)
    set N'' := N'.map π with hN''
    have hN''1 : N ≤ N'' := fun w hw => by
      obtain ⟨y, rfl⟩ := hπ w
      exact ⟨y, hN'1 hw, rfl⟩
    have hN''2 : N'' ≤ K := by
      rintro _ ⟨y, hy, rfl⟩
      exact hN'2 hy
    have hN''n : (N''.subgroupOf K).Normal := by
      rw [Subgroup.normal_subgroupOf_iff hN''2]
      rintro _ w ⟨y, hy, rfl⟩ hw
      obtain ⟨y2, rfl⟩ := hπ w
      have := (Subgroup.normal_subgroupOf_iff hN'2).1 hN'n y y2 hy hw
      exact ⟨_, this, by simp⟩
    have hcomap : N' = N''.comap π := (Subgroup.comap_map_eq_self hker).symm
    rcases hmin N'' hN''1 hN''2 hN''n with h | h
    · left
      rw [hcomap, h]
    · right
      rw [hcomap, h]
  · intro hall
    apply hnab
    intro a ha b hb
    obtain ⟨a', rfl⟩ := hπ a
    obtain ⟨b', rfl⟩ := hπ b
    have := hall a' ha b' hb
    simpa [map_mul, map_inv] using this

variable {G : Type} [Group G] [Finite G] {p : ℕ} {H D S B L M : Subgroup G} {z : G}

theorem pre_isSimpleSection [hDn : (D.subgroupOf H).Normal] {K N : Subgroup (QA H D)}
    (h : S622IsSimpleSection K N) : S622IsSimpleSection (pre H D K) (pre H D N) :=
  L6LeavesNS.s622IsSimpleSection_map H.subtype H.subtype_injective
    (isSimpleSection_comap (qmk H D) qmk_surjective h)

theorem relIndex_pre [hDn : (D.subgroupOf H).Normal] {N Y : Subgroup (QA H D)} :
    (pre H D N).relIndex (pre H D Y) = N.relIndex Y := by
  unfold pre
  rw [Subgroup.relIndex_map_map_of_injective _ _ H.subtype_injective, Subgroup.relIndex_comap,
    Subgroup.map_comap_eq_self_of_surjective qmk_surjective]

theorem mem_normalizer_map_subtype {H : Subgroup G} {P : Subgroup ↥H} {n : ↥H}
    (hn : n ∈ normalizer (P : Set ↥H)) :
    (n : G) ∈ normalizer ((P.map H.subtype : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff] at hn ⊢
  intro g
  constructor
  · intro hg
    obtain ⟨u, hu, rfl⟩ := hg
    exact ⟨n * u * n⁻¹, (hn u).mp hu, rfl⟩
  · intro hg
    obtain ⟨w, hw, hwg⟩ := hg
    have hwg' : (w : G) = (n : G) * g * (n : G)⁻¹ := hwg
    have hgH : g ∈ H := by
      have : g = (n : G)⁻¹ * (w : G) * n := by
        rw [hwg']
        group
      rw [this]
      exact H.mul_mem (H.mul_mem (H.inv_mem n.2) w.2) n.2
    refine ⟨⟨g, hgH⟩, ?_, rfl⟩
    refine (hn _).mpr ?_
    have e : n * ⟨g, hgH⟩ * n⁻¹ = w := Subtype.ext hwg'.symm
    rw [e]
    exact hw

namespace KGData

variable (d : KGData p H D S B L M z) [hDn : (D.subgroupOf H).Normal]

include d

theorem coprime_D'_of_ne_two {f : ℕ} (hf : f.Prime) (hf2 : f ≠ 2) :
    Nat.Coprime f (Nat.card (D.subgroupOf H)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe d.D_le_H).toEquiv]
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp d.D_two
  rw [hk]
  exact Nat.Coprime.pow_right k ((Nat.coprime_primes hf Nat.prime_two).mpr hf2)

theorem coprime_pre {T : Subgroup (QA H D)} (hT : Nat.Coprime p (Nat.card T)) :
    Nat.Coprime p (Nat.card (pre H D T)) := by
  haveI : Fact p.Prime := ⟨d.prime⟩
  rw [Nat.Prime.coprime_iff_not_dvd d.prime] at hT ⊢
  intro hdvd
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥(pre H D T)) p hdvd
  obtain ⟨h, hh, hmem⟩ := mem_pre.mp g.2
  have hgp : (g : G) ^ p = 1 := by
    have := pow_orderOf_eq_one g
    rw [hg] at this
    simpa using congrArg Subtype.val this
  have hhp : (h : G) ^ p = 1 := by rw [hh]; exact hgp
  have hg1 : (g : G) ≠ 1 := by
    intro h1
    have : g = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hg
    exact d.prime.one_lt.ne hg
  have hh1 : (h : G) ≠ 1 := by rw [hh]; exact hg1
  by_cases hq : qmk H D h = 1
  · have hD' : (h : G) ∈ D := qmk_eq_one_iff.mp hq
    have hord : orderOf (⟨(h : G), hD'⟩ : D) = p :=
      orderOf_eq_prime (Subtype.ext (by simpa using hhp)) fun h1 => hh1 (by
        simpa using congrArg Subtype.val h1)
    exact d.not_dvd_D (hord ▸ orderOf_dvd_natCard _)
  · have hord : orderOf (⟨qmk H D h, hmem⟩ : T) = p :=
      orderOf_eq_prime (Subtype.ext (by
        show (qmk H D h) ^ p = 1
        rw [← map_pow]
        have : h ^ p = 1 := Subtype.ext (by simpa using hhp)
        rw [this, map_one])) fun h1 => hq (by simpa using congrArg Subtype.val h1)
    exact hT (hord ▸ orderOf_dvd_natCard _)

theorem rank3_pre {Y : Subgroup (QA H D)} :
    rankThreePrimeCore p (pre H D Y) = pre H D (rankThreePrimeCore p Y) := by
  haveI : Fact p.Prime := ⟨d.prime⟩
  apply le_antisymm
  ·
    set Y' := pre H D Y with hY'
    obtain ⟨hOY, hYO, hcop⟩ := CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec p Y'
    set O := rankThreePrimeCore p Y' with hO
    have hOH : O ≤ H := hOY.trans (pre_le Y)
    have hOY' : img H D O ≤ Y := by
      intro x hx
      obtain ⟨o, hoO, rfl⟩ := mem_img.mp hx
      obtain ⟨h', hh', hmem⟩ := mem_pre.mp (hOY hoO)
      have : h' = o := Subtype.ext hh'
      rw [← this]
      exact hmem
    have himg : img H D O ≤ rankThreePrimeCore p Y := by
      refine le_sSup ⟨hOY', ?_, ?_⟩
      · rw [Subgroup.normal_subgroupOf_iff hOY']
        intro n y hn hy
        obtain ⟨o, hoO, rfl⟩ := mem_img.mp hn
        obtain ⟨k, rfl⟩ := qmk_surjective y
        have hkY' : (k : G) ∈ Y' := mem_pre.mpr ⟨k, rfl, hy⟩
        have hko : (k : G) * o * (k : G)⁻¹ ∈ O :=
          (mem_normalizer_iff.mp (hYO hkY') (o : G)).mp hoO
        refine mem_img.mpr ⟨k * o * k⁻¹, hko, ?_⟩
        rw [map_mul, map_mul, map_inv]
      · refine Nat.Coprime.coprime_dvd_right
          (Subgroup.card_map_dvd (H := O.subgroupOf H) (qmk H D)) ?_
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOH).toEquiv]
        exact hcop
    intro g hg
    have hgH : g ∈ H := hOH hg
    exact mem_pre.mpr ⟨⟨g, hgH⟩, rfl, himg (mem_img.mpr ⟨⟨g, hgH⟩, hg, rfl⟩)⟩
  ·
    obtain ⟨hNbY, hYNb, hcopNb⟩ := CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec p Y
    have hNY' : pre H D (rankThreePrimeCore p Y) ≤ pre H D Y := by
      intro g hg
      obtain ⟨h, rfl, hmem⟩ := mem_pre.mp hg
      exact mem_pre.mpr ⟨h, rfl, hNbY hmem⟩
    refine le_sSup ⟨hNY', ?_, d.coprime_pre hcopNb⟩
    rw [Subgroup.normal_subgroupOf_iff hNY']
    intro n y hn hy
    obtain ⟨h, rfl, hh⟩ := mem_pre.mp hn
    obtain ⟨k, rfl, hk⟩ := mem_pre.mp hy
    refine mem_pre.mpr ⟨k * h * k⁻¹, by simp, ?_⟩
    rw [map_mul, map_mul, map_inv]
    exact (mem_normalizer_iff.mp (hYNb hk) _).mp hh

theorem stronglyEmbedded_of_img (hs : KGStrongEmb p M z) {f : ℕ} (hf : f.Prime) (hf2 : f ≠ 2)
    (hfp : f ≠ p)
    {Y : Subgroup (QA H D)} (hYM : Y ≤ img H D M) (hzY : qmk H D ⟨z, d.z_mem_H⟩ ∈ Y)
    (hsec : S622IsSimpleSection Y (rankThreePrimeCore p Y))
    (hrel : f ∣ (rankThreePrimeCore p Y).relIndex Y) : CFSG.Open.GLBStronglyEmbedded f M := by
  haveI : Fact p.Prime := ⟨d.prime⟩
  set Y' := pre H D Y with hY'
  have hY'M : Y' ≤ M := fun g hg => by
    obtain ⟨h, rfl, hmem⟩ := mem_pre.mp hg
    have : (h : G) ∈ pre H D (img H D M) := mem_pre.mpr ⟨h, rfl, hYM hmem⟩
    exact ((mem_pre_img d.D_le_M).mp this).1
  have hzY' : z ∈ Y' := mem_pre.mpr ⟨⟨z, d.z_mem_H⟩, rfl, hzY⟩
  have hsec' : S622IsSimpleSection Y' (rankThreePrimeCore p Y') := by
    rw [hY', d.rank3_pre]
    exact pre_isSimpleSection hsec
  have hrel' : f ∣ (rankThreePrimeCore p Y').relIndex Y' := by
    rw [hY', d.rank3_pre, relIndex_pre]
    exact hrel
  exact hs f hf hf2 hfp Y' hY'M hzY' hsec' hrel'

theorem strong_img (hs : KGStrongEmb p M z) :
    ∀ f : ℕ, f.Prime → f ≠ 2 → f ≠ p → ∀ Y : Subgroup (QA H D),
    Y ≤ img H D M → qmk H D ⟨z, d.z_mem_H⟩ ∈ Y →
    S622IsSimpleSection Y (rankThreePrimeCore p Y) → f ∣ (rankThreePrimeCore p Y).relIndex Y →
    ∀ F : Subgroup (QA H D), IsPGroup f F → F ⊓ Y ≠ ⊥ → ∀ F₁ : Subgroup (QA H D), F₁ ≤ F →
      F₁ ≠ ⊥ → normalizer (F₁ : Set (QA H D)) ≤ img H D M := by
  intro f hf hf2 hfp Y hYM hzY hsec hrel F hF hFY F₁ hF₁F hF₁1
  haveI : Fact p.Prime := ⟨d.prime⟩
  haveI : Fact f.Prime := ⟨hf⟩
  set Y' := pre H D Y with hY'
  have hY'M : Y' ≤ M := fun g hg => by
    obtain ⟨h, rfl, hmem⟩ := mem_pre.mp hg
    have : (h : G) ∈ pre H D (img H D M) := mem_pre.mpr ⟨h, rfl, hYM hmem⟩
    exact ((mem_pre_img d.D_le_M).mp this).1
  have hsE := d.stronglyEmbedded_of_img hs hf hf2 hfp hYM hzY hsec hrel
  obtain ⟨P, -, hP, hPmap⟩ := CFSG.Holt.exists_isPGroup_le_map_eq (p := f) (qmk H D)
    (K := ⊤) hF (fun x _ => by
      obtain ⟨h, rfl⟩ := qmk_surjective x
      exact ⟨h, Subgroup.mem_top _, rfl⟩)
  set Fg : Subgroup G := P.map H.subtype with hFg
  have hFgp : IsPGroup f Fg := hP.map _
  have hFgM : Fg ⊓ M ≠ ⊥ := by
    obtain ⟨a, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hFY
    have haF : (a : QA H D) ∈ P.map (qmk H D) := by
      rw [hPmap]
      exact a.2.1
    obtain ⟨h, hhP, hha⟩ := haF
    have hhY : (h : G) ∈ Y' := mem_pre.mpr ⟨h, rfl, by rw [hha]; exact a.2.2⟩
    have hh1 : (h : G) ≠ 1 := by
      intro h1
      apply ha1
      apply Subtype.ext
      show (a : QA H D) = 1
      rw [← hha]
      exact qmk_eq_one_iff.mpr (by rw [h1]; exact D.one_mem)
    intro hbot
    have : (h : G) ∈ Fg ⊓ M := ⟨⟨h, hhP, rfl⟩, hY'M hhY⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact hh1 this
  have hFgM' : Fg ≤ M := CFSG.AGLEmbeddingD2.le_of_stronglyEmbedded_of_inf_ne_bot hf hsE hFgp hFgM
  set P₁ : Subgroup ↥H := P ⊓ F₁.comap (qmk H D) with hP₁
  have hP₁map : P₁.map (qmk H D) = F₁ := by
    ext x
    constructor
    · rintro ⟨h, ⟨-, hh⟩, rfl⟩
      exact hh
    · intro hx
      have hxF : x ∈ P.map (qmk H D) := by
        rw [hPmap]
        exact hF₁F hx
      obtain ⟨h, hhP, rfl⟩ := hxF
      exact ⟨h, ⟨hhP, hx⟩, rfl⟩
  have hP₁p : IsPGroup f P₁ := hP.to_le inf_le_left
  have hP₁ne : P₁ ≠ ⊥ := by
    intro h
    apply hF₁1
    rw [← hP₁map, h, Subgroup.map_bot]
  set F₁g : Subgroup G := P₁.map H.subtype with hF₁g
  have hF₁gp : IsPGroup f F₁g := hP₁p.map _
  have hF₁gM : F₁g ≤ M := by
    refine le_trans ?_ hFgM'
    exact Subgroup.map_mono inf_le_left
  have hF₁gne : F₁g ≠ ⊥ := by
    intro h
    apply hP₁ne
    rw [← Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective]
    exact h
  have hdvd : f ∣ Nat.card F₁g := by
    rcases hF₁gp.card_eq_or_dvd with h1 | h1
    · exact absurd (Subgroup.card_eq_one.mp h1) hF₁gne
    · exact h1
  have hNM : normalizer (F₁g : Set G) ≤ M :=
    CFSG.LocalAnalysis.RankFourTheoremC.normalizer_le_of_stronglyEmbedded hsE hF₁gM hdvd
  intro x hx
  obtain ⟨a, rfl⟩ := qmk_surjective x
  have hfr := CFSG.AGLEmbedding.comap_normalizer_map_le_sup hf (D.subgroupOf H)
    (d.coprime_D'_of_ne_two hf hf2) hP₁p
  have ha : a ∈ (normalizer (((P₁.map (QuotientGroup.mk' (D.subgroupOf H))) :
      Subgroup (QA H D)) : Set (QA H D))).comap (QuotientGroup.mk' (D.subgroupOf H)) := by
    rw [Subgroup.mem_comap]
    have : P₁.map (QuotientGroup.mk' (D.subgroupOf H)) = F₁ := hP₁map
    rw [this]
    exact hx
  obtain ⟨y, hy, n, hn, hyn⟩ := Subgroup.mem_sup_of_normal_left.mp (hfr ha)
  have hnM : (n : G) ∈ M := hNM (mem_normalizer_map_subtype hn)
  have hyM : (y : G) ∈ M := d.D_le_M hy
  refine mem_img.mpr ⟨a, ?_, rfl⟩
  rw [← hyn]
  exact M.mul_mem hyM hnM

theorem strongEmb_img (hs : KGStrongEmb p M z) :
    ∀ f : ℕ, f.Prime → f ≠ 2 → f ≠ p → ∀ Y : Subgroup (QA H D),
    Y ≤ img H D M → qmk H D ⟨z, d.z_mem_H⟩ ∈ Y →
    S622IsSimpleSection Y (rankThreePrimeCore p Y) → f ∣ (rankThreePrimeCore p Y).relIndex Y →
    ∀ g : QA H D, g ∉ img H D M →
      ¬ f ∣ Nat.card ↥(img H D M ⊓ CFSG.Open.GLBConj g (img H D M)) := by
  intro f hf hf2 hfp Y hYM hzY hsec hrel g hg hdvd
  haveI : Fact f.Prime := ⟨hf⟩
  have hsE := d.stronglyEmbedded_of_img hs hf hf2 hfp hYM hzY hsec hrel
  obtain ⟨h, rfl⟩ := qmk_surjective g
  have hhM : (h : G) ∉ M := fun hh => hg (mem_img.mpr ⟨h, hh, rfl⟩)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(img H D M ⊓ CFSG.Open.GLBConj (qmk H D h) (img H D M))) f hdvd
  have hxo : orderOf (x : QA H D) = f := by rw [Subgroup.orderOf_coe]; exact hx
  have hF : IsPGroup f (zpowers (x : QA H D)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hxo, pow_one])
  obtain ⟨P, -, hP, hPmap⟩ := CFSG.Holt.exists_isPGroup_le_map_eq (p := f) (qmk H D)
    (K := ⊤) hF (fun y _ => by
      obtain ⟨h', rfl⟩ := qmk_surjective y
      exact ⟨h', Subgroup.mem_top _, rfl⟩)
  have hx1 : (x : QA H D) ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hxo
    exact hf.one_lt.ne hxo
  have hPne : P ≠ ⊥ := by
    intro hP0
    have hxF : (x : QA H D) ∈ zpowers (x : QA H D) := mem_zpowers _
    rw [← hPmap, hP0, Subgroup.map_bot, Subgroup.mem_bot] at hxF
    exact hx1 hxF
  have hle : P.map H.subtype ≤ M ⊓ CFSG.Open.GLBConj (h : G) M := by
    rintro _ ⟨u, hu, rfl⟩
    have hqu : qmk H D u ∈ zpowers (x : QA H D) := by
      rw [← hPmap]
      exact Subgroup.mem_map_of_mem _ hu
    have hqX : qmk H D u ∈ img H D M ⊓ CFSG.Open.GLBConj (qmk H D h) (img H D M) :=
      zpowers_le.mpr x.2 hqu
    refine ⟨((mem_pre_img d.D_le_M).mp (mem_pre.mpr ⟨u, rfl, hqX.1⟩)).1, ?_⟩
    obtain ⟨y, hyM, hyu⟩ := Subgroup.mem_map.mp hqX.2
    have hyu' : (qmk H D h)⁻¹ * y * ((qmk H D h)⁻¹)⁻¹ = qmk H D u := by
      simpa [MulAut.conj_apply] using hyu
    have hy : y = qmk H D (h * u * h⁻¹) := by
      rw [map_mul, map_mul, map_inv, ← hyu']
      group
    have hmem : (h : G) * u * (h : G)⁻¹ ∈ M := by
      have := (mem_pre_img d.D_le_M).mp (mem_pre.mpr ⟨h * u * h⁻¹, rfl, hy ▸ hyM⟩)
      exact this.1
    refine Subgroup.mem_map.mpr ⟨(h : G) * u * (h : G)⁻¹, hmem, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]
  have hdvd' : f ∣ Nat.card ↥(M ⊓ CFSG.Open.GLBConj (h : G) M) := by
    have h1 : f ∣ Nat.card ↥(P.map H.subtype) := by
      rw [Subgroup.card_map_of_injective H.subtype_injective]
      exact hP.card_eq_or_dvd.resolve_left fun h1 => hPne (Subgroup.card_eq_one.mp h1)
    exact h1.trans (Subgroup.card_dvd_of_le hle)
  exact hsE.2.2 (h : G) hhM hdvd'

theorem cfg : KQCfg (QA H D) p (img H D L) (img H D S) (img H D B) (img H D M)
    (qmk H D ⟨z, d.z_mem_H⟩) where
  prime := d.prime
  five_le := d.five_le
  simple := d.simple_img
  nonab := d.nonab_img
  rank := d.rank_img
  z_mem_K := mem_img.mpr ⟨⟨z, d.z_mem_H⟩, d.z_mem_L, rfl⟩
  z_mem_B := mem_img.mpr ⟨⟨z, d.z_mem_H⟩, d.z_mem_B, rfl⟩
  z_order := d.zb_order
  S_two := d.img_S_two
  S_ne := d.img_S_ne
  B_elem := d.img_B_isElemAbelian
  B_card := d.img_B_card
  B_le_S := d.img_B_le_S
  S_le_K := d.img_S_le_K
  B_le_K := d.img_B_le_K
  max_S := d.max_S_img
  cover := d.cover_img
  cover_Z := d.cover_Z_img
  not_le := d.not_le_img

end KGData

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KGC
