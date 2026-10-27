module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.Setting
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.Within
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma213Weak
import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.Plane
import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.Self

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.LocalAnalysis.RankThreeTheoremC Subgroup

theorem pCore_quotient_ne_bot {H : Type*} [Group H] [Finite H] {p : ℕ} (hp : p.Prime)
    {Q : Subgroup H} (hQn : Q.Normal) (hQ : IsPGroup p Q) (hQ1 : Q ≠ ⊥) :
    CFSG.pCore p (H ⧸ primeComplementCore (G := H) p) ≠ ⊥ := by
  intro hbot
  have hN := primeComplementCore_coprime (G := H) p
  have hinj := injOn_mk_of_isPGroup_coprime (primeComplementCore (G := H) p) hp hN hQ
  have hnormal : (Q.map (QuotientGroup.mk' (primeComplementCore (G := H) p))).Normal :=
    hQn.map _ (QuotientGroup.mk'_surjective _)
  have hle : Q.map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ≤
      CFSG.pCore p (H ⧸ primeComplementCore (G := H) p) :=
    le_sSup ⟨hnormal, hQ.map _⟩
  rw [hbot, le_bot_iff] at hle
  apply hQ1
  rw [eq_bot_iff]
  intro x hx
  have hx' : QuotientGroup.mk' (primeComplementCore (G := H) p) x ∈
      Q.map (QuotientGroup.mk' (primeComplementCore (G := H) p)) := mem_map_of_mem _ hx
  rw [hle, mem_bot] at hx'
  rw [mem_bot]
  exact hinj hx Q.one_mem (by rw [hx', map_one])

variable {G : Type} [Group G] [Finite G]

theorem invariantTwoMaximalWithin_le_sup_of_isSylow {n : ℕ} (hS : KFactSetting n G)
    (hD1 : TheoremD1 G) (h212 : KFactLemma212Ge n) (h213 : KFactLemma213GeC n) {p : ℕ}
    (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M D : Subgroup G}
    (hext : ExtremalObstruction p P M D) (hPD : ¬ (P : Subgroup G) ≤ normalizer (D : Set G))
    (hab : IsMulCommutative D) {z : G} (hzD : z ∈ D) (hz1 : z ≠ 1)
    (hzc : z ∈ centralizer ((P : Subgroup G) : Set G)) (hzp : z ^ p = 1)
    (hN₀M : normalizer ((zpowers z : Subgroup G) : Set G) ≤ M)
    (hcon : ¬ HasPrimeConstraint (G := M) p)
    (hSyl : CFSG.ABGLocalTools.IsSylowOf p D (centralizer (D : Set G))) {T : Subgroup G}
    (hT : invariantTwoMaximalWithin D M T) :
    T ≤ CFSG.ABGTheoremB.pPrimeCoreIn p M ⊔
      CFSG.ABGTheoremB.pPrimeCoreIn p (normalizer ((zpowers z : Subgroup G) : Set G)) := by
  have hprime := sigmaA_prime p hp
  have hodd := sigmaA_odd p hp
  have : Fact p.Prime := ⟨hprime⟩
  obtain ⟨hM, hDP, -, hDM⟩ := hext.obstruction
  have hPM := hS.obstruction.sylow_le hp hM
  have hDM' : D ≤ M := hDP.trans hPM
  have hzM : z ∈ M := hDM' hzD
  have hCD : centralizer (D : Set G) ≤ M :=
    (centralizer_le (Set.singleton_subset_iff.mpr hzD)).trans
      ((RankThreeTheoremC.centralizer_singleton_le_normalizer_zpowers z).trans hN₀M)
  have := hS.simple
  have hMtop : M ≠ ⊤ := CFSG.PreuniquenessRankFour.Helpers.twoLocal_ne_top hS.nonab hM.1.1
  have hcat : CFSG.AGLEmbedding.CatalogSimpleSections M :=
    CFSG.AGLEmbedding.catalogSimpleSections_of_isKProper hS.kProper M hMtop
  have hconf := Lemma212ConfigGe.of_extremal hS.obstruction hp hext (hS.le_pRank p hp P) hPD hab
    hzD hz1 hzc hzp hSyl hPM hCD hzM
  obtain ⟨g, hg⟩ := hS.obstruction.exists_isPlaneDiagonal hD1 hp hext hPD hab hCD hzD hz1 hzc hN₀M
  have hgN : g ∈ normalizer ((zpowers z : Subgroup G) : Set G) := by
    obtain ⟨-, -, a, b, -, -, hga, -⟩ := hg
    exact mem_normalizer_zpowers_of_conj_mem (hga ▸ pow_mem (mem_zpowers z) a)
  have hgM : g ∈ M := hN₀M hgN
  have hg' := hg.subgroupOf hDM' hzM hgM
  have hemb := hS.obstruction.centralizerEmbeds_of_extremal hD1 hp hext hPD hab hCD hzD hz1 hzc
    hN₀M hzM
  set N₀ : Subgroup G := normalizer ((zpowers z : Subgroup G) : Set G) with hN₀
  have hPN₀ : (P : Subgroup G) ≤ N₀ := le_normalizer_zpowers_of_le_centralizer hzc
  have hCN₀ : centralizer (D : Set G) ≤ N₀ :=
    (centralizer_le (Set.singleton_subset_iff.mpr hzD)).trans
      (RankThreeTheoremC.centralizer_singleton_le_normalizer_zpowers z)
  have hDN₀ : D ≤ N₀ := by
    refine le_trans ?_ (centralizer_le_normalizer _)
    refine le_centralizer_iff.mp (zpowers_le.mpr (mem_centralizer_iff.mpr fun d hd => ?_))
    exact congrArg Subtype.val (hab.is_comm.comm ⟨d, hd⟩ ⟨z, hzD⟩)
  have hzN₀ : z ∈ N₀ := hDN₀ hzD
  have hN₀top : N₀ ≠ ⊤ := fun h => hMtop (top_le_iff.mp (h ▸ hN₀M))
  have hcat₀ : CFSG.AGLEmbedding.CatalogSimpleSections N₀ :=
    CFSG.AGLEmbedding.catalogSimpleSections_of_isKProper hS.kProper N₀ hN₀top
  have hconf₀ := Lemma212ConfigGe.of_extremal hS.obstruction hp hext (hS.le_pRank p hp P) hPD hab
    hzD hz1 hzc hzp hSyl hPN₀ hCN₀ hzN₀
  have hg₀ := hg.subgroupOf hDN₀ hzN₀ hgN
  have hzpg : IsPGroup p (zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime hzp hz1, pow_one])
  have hN₀con : HasPrimeConstraint (G := N₀) p := by
    rcases h212 p hprime hodd N₀ hcat₀ (P.subtype hPN₀) ⟨z, hzN₀⟩ (D.subgroupOf N₀) hconf₀
      ⟨_, hg₀⟩ with hc | hpc
    · exact hc
    · exfalso
      have hzle : zpowers z ≤ N₀ := zpowers_le.mpr hzN₀
      have hQn : ((zpowers z).subgroupOf N₀).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hzle).mpr le_rfl
      refine pCore_quotient_ne_bot hprime hQn hzpg.comap_subtype ?_ hpc
      intro hbot
      have hmem : (⟨z, hzN₀⟩ : N₀) ∈ (zpowers z).subgroupOf N₀ := mem_zpowers z
      rw [hbot, mem_bot] at hmem
      exact hz1 (congrArg Subtype.val hmem)
  have hDp : IsPGroup p D := P.isPGroup'.to_le hDP
  have hDC : D ≤ centralizer (D : Set G) := fun d hd =>
    mem_centralizer_iff.mpr fun d' hd' =>
      congrArg Subtype.val (hab.is_comm.comm ⟨d', hd'⟩ ⟨d, hd⟩)
  have hcontains : ∀ x ∈ N₀, x ∈ centralizer (D : Set G) → orderOf x = p → x ∈ D := by
    intro x _ hxC hxo
    have hxp : IsPGroup p (zpowers x) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hxo, pow_one])
    have hxN : zpowers x ≤ normalizer (D : Set G) :=
      (zpowers_le.mpr hxC).trans (centralizer_le_normalizer _)
    have hQp : IsPGroup p ↥(D ⊔ zpowers x) := hDp.to_sup_of_normal_left' hxp hxN
    have hQle : D ⊔ zpowers x ≤ centralizer (D : Set G) := sup_le hDC (zpowers_le.mpr hxC)
    have hEq := hSyl.eq_of_le le_sup_left hQle hQp
    have hx : x ∈ D ⊔ zpowers x := Subgroup.mem_sup_right (mem_zpowers x)
    rwa [hEq] at hx
  have hBT : ∀ U : Subgroup G, U ≤ N₀ → p.Coprime (Nat.card U) →
      D ≤ normalizer (U : Set G) → U ≤ CFSG.ABGTheoremB.pPrimeCoreIn p N₀ :=
    fun U hUN hUc hDU =>
      (CFSG.AGLEmbedding.signalizer_le_glbPrimeCore_of_contains hprime hodd hN₀con hDp hDN₀
        hcontains hUN hUc hDU).trans (glbPrimeCore_le_pPrimeCoreIn p N₀)
  rcases h212 p hprime hodd M hcat (P.subtype hPM) ⟨z, hzM⟩ (D.subgroupOf M) hconf ⟨_, hg'⟩ with
    hc | hpc
  · exact absurd hc hcon
  · rcases h213 p hprime hodd M hcat hcon hpc (P.subtype hPM) ⟨z, hzM⟩ (D.subgroupOf M) hconf
      ⟨_, hg'⟩ hemb with h1 | h2
    ·
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hTM : T ≤ M := hT.1
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hT.2.1
      have hTcop : p.Coprime (Nat.card (T.subgroupOf M)) := by
        rw [Nat.card_congr (subgroupOfEquivOfLe hTM).toEquiv, hk]
        exact ((Nat.coprime_primes hprime Nat.prime_two).mpr hodd).pow_right k
      have hDT : D.subgroupOf M ≤ normalizer ((T.subgroupOf M : Subgroup M) : Set M) := by
        rw [← Subgroup.subgroupOf_normalizer_eq hTM]
        exact Subgroup.comap_mono hT.2.2.1
      have hTC := h1 (T.subgroupOf M) hTcop hDT
      have hNcop : p.Coprime (Nat.card (primeComplementCore (G := M) p)) :=
        primeComplementCore_coprime (G := M) p
      have hNT : p.Coprime (Nat.card ↥(T.subgroupOf M ⊔ primeComplementCore (G := M) p)) :=
        normal_coprime_sup_coprime p _ _ inferInstance hTcop hNcop
      set U' : Subgroup M := centralizer ({(⟨z, hzM⟩ : M)} : Set M) ⊓
        (T.subgroupOf M ⊔ primeComplementCore (G := M) p) with hU'
      have hU'cop : p.Coprime (Nat.card U') :=
        hNT.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right)
      have hDC' : D.subgroupOf M ≤ centralizer ({(⟨z, hzM⟩ : M)} : Set M) := fun d hd => by
        have hcomm : (d : G) * z = z * (d : G) :=
          congrArg Subtype.val (hab.is_comm.comm ⟨(d : G), hd⟩ ⟨z, hzD⟩)
        exact mem_centralizer_singleton_iff.mpr (Subtype.ext hcomm)
      have hDU' : D.subgroupOf M ≤ normalizer (U' : Set M) := by
        refine (le_inf (hDC'.trans Subgroup.le_normalizer) ?_).trans
          Subgroup.inf_normalizer_le_normalizer_inf
        refine (le_inf hDT fun d _ => ?_).trans (Subgroup.inf_normalizer_le_normalizer_sup _ _)
        exact (le_normalizer_of_normal :
          (⊤ : Subgroup M) ≤ normalizer ((primeComplementCore (G := M) p : Subgroup M) : Set M))
          (mem_top d)
      have hT'le : T.subgroupOf M ≤ U' ⊔ primeComplementCore (G := M) p := by
        intro t ht
        obtain ⟨c, hc, n, hn, hcn⟩ := Subgroup.mem_sup_of_normal_right.mp (hTC ht)
        have hct : c = t * n⁻¹ := by rw [← hcn]; group
        have hcU : c ∈ U' := ⟨hc, by
          rw [hct]
          exact mul_mem (Subgroup.mem_sup_left ht) (Subgroup.mem_sup_right (inv_mem hn))⟩
        rw [← hcn]
        exact mul_mem (Subgroup.mem_sup_left hcU) (Subgroup.mem_sup_right hn)
      have hUN₀ : U'.map M.subtype ≤ N₀ := by
        rintro _ ⟨u, hu, rfl⟩
        have hu1 : u ∈ centralizer ({(⟨z, hzM⟩ : M)} : Set M) := hu.1
        have hu2 : (u : G) ∈ centralizer ({z} : Set G) := by
          rw [mem_centralizer_singleton_iff] at hu1 ⊢
          exact congrArg Subtype.val hu1
        exact RankThreeTheoremC.centralizer_singleton_le_normalizer_zpowers z hu2
      have hUcop : p.Coprime (Nat.card (U'.map M.subtype)) := by
        rw [Subgroup.card_map_of_injective M.subtype_injective]
        exact hU'cop
      have hDU : D ≤ normalizer ((U'.map M.subtype : Subgroup G) : Set G) := fun d hd =>
        Subgroup.le_normalizer_map M.subtype
          ⟨⟨d, hDM' hd⟩, hDU' (show (⟨d, hDM' hd⟩ : M) ∈ D.subgroupOf M from hd), rfl⟩
      have hUO := hBT _ hUN₀ hUcop hDU
      have hTle : T ≤ U'.map M.subtype ⊔ CFSG.ABGTheoremB.pPrimeCoreIn p M := by
        have h := Subgroup.map_mono (f := M.subtype) hT'le
        rw [map_subgroupOf_eq_of_le hTM, Subgroup.map_sup] at h
        exact h
      exact hTle.trans (sup_le (hUO.trans le_sup_right) le_sup_left)
    ·
      exfalso
      obtain ⟨g₀, hg₀N, hg₀M⟩ := IsConcreteLE.not_le_iff_exists.mp hDM
      have hyD : g₀ * z * g₀⁻¹ ∈ D := (mem_normalizer_iff.mp hg₀N z).mp hzD
      have hyM : g₀ * z * g₀⁻¹ ∈ M := hDM' hyD
      have hy : (⟨g₀ * z * g₀⁻¹, hyM⟩ : M) ∈ D.subgroupOf M := hyD
      have hy1 : (⟨g₀ * z * g₀⁻¹, hyM⟩ : M) ≠ 1 := by
        intro h1
        have h2 : g₀ * z * g₀⁻¹ = 1 := congrArg Subtype.val h1
        exact hz1 (by simpa [mul_inv_eq_one] using h2)
      obtain ⟨h, -, hzp⟩ := h2 _ hy hy1
      have hzG : zpowers (g₀ * z * g₀⁻¹) = zpowers ((h : G) * z * (h : G)⁻¹) := by
        have := congrArg (Subgroup.map M.subtype) hzp
        rw [MonoidHom.map_zpowers, Subgroup.map_map, MonoidHom.map_zpowers] at this
        exact this
      have hmem : g₀ * z * g₀⁻¹ ∈ zpowers ((h : G) * z * (h : G)⁻¹) := by
        rw [← hzG]
        exact mem_zpowers _
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hmem
      have hx : (h : G)⁻¹ * g₀ ∈ normalizer ((zpowers z : Subgroup G) : Set G) := by
        apply mem_normalizer_zpowers_of_conj_mem
        rw [mem_zpowers_iff]
        refine ⟨k, ?_⟩
        have e1 : ((h : G) * z * (h : G)⁻¹) ^ k = (h : G) * z ^ k * (h : G)⁻¹ := conj_zpow
        calc z ^ k = (h : G)⁻¹ * ((h : G) * z * (h : G)⁻¹) ^ k * (h : G) := by rw [e1]; group
          _ = (h : G)⁻¹ * (g₀ * z * g₀⁻¹) * (h : G) := by rw [hk]
          _ = ((h : G)⁻¹ * g₀) * z * ((h : G)⁻¹ * g₀)⁻¹ := by group
      apply hg₀M
      have := M.mul_mem h.2 (hN₀M hx)
      simpa using this

theorem invariantTwoMaximalWithin_le_sup {n : ℕ} (hS : KFactSetting n G) (hD1 : TheoremD1 G)
    (h212 : KFactLemma212Ge n) (h213 : KFactLemma213GeC n) {p : ℕ}
    (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M D : Subgroup G}
    (hext : ExtremalObstruction p P M D) (hPD : ¬ (P : Subgroup G) ≤ normalizer (D : Set G))
    (hab : IsMulCommutative D) {z : G} (hzD : z ∈ D) (hz1 : z ≠ 1)
    (hzc : z ∈ centralizer ((P : Subgroup G) : Set G)) (hzp : z ^ p = 1)
    (hN₀M : normalizer ((zpowers z : Subgroup G) : Set G) ≤ M)
    (hcon : ¬ HasPrimeConstraint (G := M) p) {T : Subgroup G}
    (hT : invariantTwoMaximalWithin D M T) :
    T ≤ CFSG.ABGTheoremB.pPrimeCoreIn p M ⊔
      CFSG.ABGTheoremB.pPrimeCoreIn p (normalizer ((zpowers z : Subgroup G) : Set G)) := by
  have hCM : centralizer (D : Set G) ≤ M :=
    (centralizer_le (Set.singleton_subset_iff.mpr hzD)).trans
      ((RankThreeTheoremC.centralizer_singleton_le_normalizer_zpowers z).trans hN₀M)
  exact invariantTwoMaximalWithin_le_sup_of_isSylow hS hD1 h212 h213 hp hext hPD hab hzD hz1 hzc
    hzp hN₀M hcon
    ((hS.obstruction.isSylowOf_centralizer_iff hD1 hp hext hPD hab hCM hzD hz1 hzc hN₀M).mpr
      (hS.obstruction.inf_centralizer_le_self hD1 hp hext hPD hab hzD hz1 hzc hN₀M)) hT

theorem gl83InvariantTwoWithin_of_kfactsC {n : ℕ} (hS : KFactSetting n G) (hD1 : TheoremD1 G)
    (h212 : KFactLemma212Ge n) (h213 : KFactLemma213GeC n) : GL83InvariantTwoWithin G :=
  hS.obstruction.gl83InvariantTwoWithin_of_nonConstrained hD1
    fun p hp P M D hext hPD hab z hzD hz1 hzc hzp hN₀M hcon T hT =>
      invariantTwoMaximalWithin_le_sup hS hD1 h212 h213 hp hext hPD hab hzD hz1 hzc hzp hN₀M
        hcon hT

theorem gl83InvariantTwoSylow_of_kfactsC {n : ℕ} (hS : KFactSetting n G) (hD1 : TheoremD1 G)
    (hR : TransitivityReduction G) (h212 : KFactLemma212Ge n) (h213 : KFactLemma213GeC n) :
    GL83InvariantTwoSylow G :=
  hS.obstruction.gl83InvariantTwoSylow_of_within hR
    (gl83InvariantTwoWithin_of_kfactsC hS hD1 h212 h213)

theorem invariantTwoSylowOfD1Rank4_of_kfactsC (h212 : KFactLemma212Ge 4)
    (h213 : KFactLemma213GeC 4) : InvariantTwoSylowOfD1Rank4 := by
  intro G _ _ _ hnonab hKpr hchar he hpre hD1 hR
  have hS : D1Global G := ⟨inferInstance, hnonab, hKpr, hchar, he, hpre⟩
  exact gl83InvariantTwoSylow_of_kfactsC (KFactSetting.of_d1Global hS)
    (theoremD1_of_d1For hS.rank hD1) hR h212 h213

end CFSG.LocalAnalysis.RankFourTheoremC
