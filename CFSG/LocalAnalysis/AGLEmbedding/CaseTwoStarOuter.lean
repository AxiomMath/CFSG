module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNoSPCz
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVStar
public import CFSG.LocalAnalysis.RankThreeTheoremC.RelativePairCore
import CFSG.LocalAnalysis.AGLEmbedding.A15ComponentsAux
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoCompetitorAux
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoStarCore
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoStarProj
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoStarPsi

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ComponentClassification.OuterAutomorphisms

theorem mem_sup_centralizer_of_kFactOuterSylowInner
    (hKO : LocalAnalysis.RankThreeTheoremC.KFactOuterSylowInner) {Y : Type} [Group Y] [Finite Y]
    {K : Subgroup Y} (hK : IsComponentOf K ⊤) (hcat : IsCatalogGroup (↥K ⧸ Subgroup.center ↥K))
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (T : Sylow p ↥K) (hTc : IsCyclic (T : Subgroup ↥K))
    (hT1 : (T : Subgroup ↥K) ≠ ⊥) {x : Y} (hxN : x ∈ Subgroup.normalizer (K : Set Y))
    (hxp : x ^ p = 1) (hxT : ∀ t ∈ (T : Subgroup ↥K), x * (t : Y) = (t : Y) * x) :
    x ∈ K ⊔ Subgroup.centralizer (K : Set Y) := by
  have hSsub : ((T : Subgroup K).map K.subtype).subgroupOf K = (T : Subgroup K) :=
    Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
  have hpK : p ∣ Nat.card K := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp T.isPGroup'
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hT1 (Subgroup.eq_bot_of_card_eq _ (by simpa using hn))
    exact (dvd_pow_self p hn0).trans (hn ▸ (T : Subgroup K).card_subgroup_dvd_card)
  refine hKO Y K p hp2 hK hcat hpK ((T : Subgroup K).map K.subtype)
    (Subgroup.map_subtype_le _) (T.isPGroup'.map K.subtype)
    (by rw [hSsub]; exact T.not_dvd_index)
    (isCyclic_of_surjective
      ((T : Subgroup K).equivMapOfInjective _ K.subtype_injective).toMonoidHom
      (MulEquiv.surjective _)) x hxN hxp ?_
  rintro _ ⟨t, ht, rfl⟩
  exact hxT t ht

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M R : Subgroup G}

theorem d1StarElt_commute_rbar_at {z : G} (hRz : R ≤ Subgroup.centralizer ({z} : Set G))
    {Hs : Subgroup G} (hCHs : Subgroup.centralizer ({z} : Set G) ≤ Hs)
    {Rbars : Sylow p (Hs ⧸ primeComplementCore (G := Hs) p)}
    (hcfg : D1ComponentConfigU p P M Hs R Rbars) {t : Hs ⧸ primeComplementCore (G := Hs) p}
    (ht : t ∈ (Rbars : Subgroup _)) : d1StarElt p hCHs * t = t * d1StarElt p hCHs := by
  rw [hcfg.rbar] at ht
  obtain ⟨r, hrR, rfl⟩ := ht
  have hrz : (r : G) * z = z * r := Subgroup.mem_centralizer_singleton_iff.mp (hRz hrR)
  have hr : (⟨z, mem_of_centralizer_le hCHs⟩ : Hs) * r = r * ⟨z, mem_of_centralizer_le hCHs⟩ :=
    Subtype.ext hrz.symm
  rw [d1StarElt, ← map_mul, ← map_mul, hr]

theorem d1StarElt_mem_normalizer_at {z : G} (hRz : R ≤ Subgroup.centralizer ({z} : Set G))
    {Hs : Subgroup G} (hCHs : Subgroup.centralizer ({z} : Set G) ≤ Hs)
    {Rbars : Sylow p (Hs ⧸ primeComplementCore (G := Hs) p)}
    (hcfg : D1ComponentConfigU p P M Hs R Rbars)
    {L : Subgroup (Hs ⧸ primeComplementCore (G := Hs) p)} (hL : IsComponentOf L ⊤) :
    d1StarElt p hCHs ∈ Subgroup.normalizer (L : Set _) := by
  have hp := hcfg.red.prime
  have hp2 := hcfg.red.ne_two
  set zs := d1StarElt p hCHs with hzs
  obtain ⟨t, ⟨htR, htL⟩, -, htC⟩ := exists_mem_sylow_inf_component hp hp2
    hcfg.red.core_eq_bot Rbars hL
  have hzt : zs * t = t * zs := d1StarElt_commute_rbar_at hRz hCHs hcfg htR
  set L' := L.map (MulAut.conj zs).toMonoidHom with hL'
  have hL'c : IsComponentOf L' ⊤ :=
    (ComponentClassification.LocalComponents.equiv_iff (MulAut.conj zs) L).mpr hL
  have heq : L' = L := by
    by_contra hne
    have hcomm := ComponentClassification.LocalComponents.commute_of_ne L L' hL hL'c (Ne.symm hne)
    apply htC
    have htL' : t ∈ L' := ⟨t, htL, by
      show zs * t * zs⁻¹ = t
      rw [hzt, mul_assoc, mul_inv_cancel, mul_one]⟩
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h1 : l * t * l⁻¹ * t⁻¹ ∈ ⁅L, L'⁆ := Subgroup.commutator_mem_commutator hl htL'
    rw [hcomm, Subgroup.mem_bot] at h1
    calc l * t = l * t * l⁻¹ * t⁻¹ * (t * l) := by group
      _ = t * l := by rw [h1, one_mul]
  exact (conjSub_eq_iff zs L).mp heq

theorem exists_centralized_component_at (hKO : LocalAnalysis.RankThreeTheoremC.KFactOuterSylowInner)
    (hInv : KFactCaseTwoInvIn G) (hSch : KFactCatalogSchreier) {z : G}
    {T : Sylow p (Subgroup.centralizer ({z} : Set G))} {Pbar : Sylow p (D1CzQuot p z)}
    {KC : Subgroup (D1CzQuot p z)} (hc : D1CzReduced p M z T Pbar KC) (hzK : d1CzElt p z ∉ KC)
    (hK : IsCaseTwoGroup p KC) (hzp : orderOf z = p) (hzM : z ∈ M)
    (hRz : R ≤ Subgroup.centralizer ({z} : Set G)) {Hs : Subgroup G}
    (hCHs : Subgroup.centralizer ({z} : Set G) ≤ Hs)
    {Rbars : Sylow p (Hs ⧸ primeComplementCore (G := Hs) p)}
    (hcfg : D1ComponentConfigU p P M Hs R Rbars)
    (h3R : Open.pRank p (Rbars : Subgroup (Hs ⧸ primeComplementCore (G := Hs) p)) ≤ 3)
    (hIII : ∀ K : Subgroup (Hs ⧸ primeComplementCore (G := Hs) p), IsComponentOf K ⊤ →
      (∀ L : Subgroup (Hs ⧸ primeComplementCore (G := Hs) p), IsComponentOf L ⊤ → L = K) →
      ¬ IsCyclic ((Rbars : Subgroup (Hs ⧸ primeComplementCore (G := Hs) p)) ⊓ K : Subgroup (Hs ⧸
          primeComplementCore (G := Hs) p)) →
      (∀ c ∈ (Rbars : Subgroup (Hs ⧸ primeComplementCore (G := Hs) p)) ⊓ Subgroup.centralizer (K :
          Set (Hs ⧸ primeComplementCore (G := Hs) p)),
        orderOf c = p → c ∈ (Subgroup.center K).map K.subtype) → False) :
    ∃ Ks : Subgroup (Hs ⧸ primeComplementCore (G := Hs) p), IsComponentOf Ks ⊤ ∧
      d1StarElt p hCHs ∈ Subgroup.centralizer (Ks : Set _) := by
  have hp := hcfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  have hred := hcfg.red
  have hZC : Subgroup.center KC = ⊥ :=
    (hc.red.center_eq_bot_and_rankOne_of_not_mem hc.center hc.order hc.comp hzK).1
  let eC : KC ≃* KC ⧸ Subgroup.center KC :=
    ((QuotientGroup.quotientMulEquivOfEq hZC).trans QuotientGroup.quotientBot).symm
  have : IsSimpleGroup (KC ⧸ Subgroup.center KC) := hc.comp.2.2.2
  obtain ⟨hKCs, hKCnab, -⟩ := hc.catalog.isSimpleGroup_of_center_eq_bot hc.comp hZC
  have hKCperf : Group.IsPerfect KC := ⟨hc.comp.2.2.1⟩
  have hKCp : ⁅KC, KC⁆ = KC := Subgroup.isPerfect_iff.mp hKCperf
  have hKCtop : ⁅(⊤ : Subgroup KC), (⊤ : Subgroup KC)⁆ = ⊤ := hc.comp.2.2.1
  have hpKC : p ∣ Nat.card KC := by
    have h1 := prime_dvd_card_center_quotient_of_isComponentOf hp hc.red.core_eq_bot hc.comp
    rw [Nat.card_congr eC.symm.toEquiv] at h1
    exact h1
  obtain ⟨W, hWA, hWp, θ, hθs, hθ⟩ := exists_inner_cover p hCHs hKCp
  have hkerp : ∀ w : W, θ w = 1 → p.Coprime (orderOf w) := by
    intro w hw
    have h1 : d1StarPsi p hCHs ⟨w, hWA w.2⟩ = 1 := by
      rw [← hθ w, hw]
      rfl
    have h2 := coprime_orderOf_of_d1StarPsi_eq_one p hCHs _ h1
    rw [Subgroup.orderOf_mk] at h2
    rwa [← Subgroup.orderOf_coe]
  obtain ⟨K₀, hK₀⟩ := hcfg.exists_isComponentOf
  obtain ⟨Ks, hKs, hWN, hker⟩ := exists_component_ker_le hred.core_eq_bot
    (hred.isCyclic_pCore_of_component hK₀)
    (fun L₁ L₂ L₃ h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ => hred.false_of_three_components h₁ h₂ h₃ h₁₂ h₁₃ h₂₃)
    hWp hKCtop θ hθs
  refine ⟨Ks, hKs, ?_⟩
  have : IsSimpleGroup (Ks ⧸ Subgroup.center Ks) := hKs.2.2.2
  have : Group.IsPerfect Ks := ⟨hKs.2.2.1⟩
  have : Group.IsSolvable (Outer (Ks ⧸ Subgroup.center Ks)) :=
    hSch _ inferInstance
      (ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hKs.2.2)
      (hcfg.catalog.isCatalogGroup_center_quotient hKs)
  have hout : Group.IsSolvable (Outer Ks) := solvable_of_centerQuotient Ks
  have hWK : W ≤ Ks ⊔ Subgroup.centralizer (Ks : Set _) :=
    perfect_le_sup_centralizer_of_outer hout hWp hWN
  by_cases hcyc : IsCyclic ((Rbars : Subgroup _) ⊓ Ks : Subgroup _)
  ·
    have hZ := hred.center_eq_bot_of_isCyclic hKs hcyc
    obtain ⟨TK, hTK⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal Rbars
      (ComponentClassification.Components.mathlib_subnormal_of_chain hKs.2.1
        Subgroup.IsSubnormal.top)
    have hTKc : IsCyclic (TK : Subgroup Ks) := by
      rw [← hTK] at hcyc
      exact isCyclic_of_surjective
        ((TK : Subgroup Ks).equivMapOfInjective _ Ks.subtype_injective).symm.toMonoidHom
        (MulEquiv.surjective _)
    have hTK1 : (TK : Subgroup Ks) ≠ ⊥ := by
      obtain ⟨t, htRK, htp, -⟩ := exists_mem_sylow_inf_component hp hred.ne_two
        hred.core_eq_bot Rbars hKs
      intro hbot
      rw [← hTK, hbot, Subgroup.map_bot, Subgroup.mem_bot] at htRK
      rw [htRK, orderOf_one] at htp
      exact hp.one_lt.ne htp
    have hzsN := d1StarElt_mem_normalizer_at hRz hCHs hcfg hKs
    have hzsp : d1StarElt p hCHs ^ p = 1 := by
      have hz1 : (⟨z, mem_of_centralizer_le hCHs⟩ : Hs) ^ p = 1 :=
        Subtype.ext (by rw [Subgroup.coe_pow, ← hzp, pow_orderOf_eq_one, Subgroup.coe_one])
      rw [d1StarElt, ← map_pow, hz1, map_one]
    have hzsT : ∀ t ∈ (TK : Subgroup Ks),
        d1StarElt p hCHs * (t : _) = (t : _) * d1StarElt p hCHs :=
      fun t ht => d1StarElt_commute_rbar_at hRz hCHs hcfg
        ((hTK ▸ ⟨t, ht, rfl⟩ : (t : Hs ⧸ primeComplementCore (G := Hs) p) ∈
          (Rbars : Subgroup _) ⊓ Ks).1)
    have hsup := mem_sup_centralizer_of_kFactOuterSylowInner hKO hKs
      (hcfg.catalog.isCatalogGroup_center_quotient hKs) hred.ne_two TK hTKc hTK1 hzsN hzsp hzsT
    have hWx : ∀ w ∈ W, d1StarElt p hCHs * w = w * d1StarElt p hCHs := by
      intro w hw
      have h1 := hWA hw
      rw [d1StarMap_range hp hzp hCHs] at h1
      exact (Subgroup.mem_centralizer_singleton_iff.mp h1).symm
    exact mem_centralizer_of_cyclic_sylow hZ hTKc hsup hzsp hWx hWK hKCnab hpKC θ hθs hker hkerp
  ·
    rcases hred.rankOne_or_center hKs hcyc with ⟨z', hz'R, hz'K, hz'p, hz'c, -⟩ | hcent
    · exfalso
      refine hred.false_of_surjective_of_rankOne_at hcfg.catalog hInv.on hSch h3R hKs hcyc
        ⟨z', hz'R, hz'K, hz'p, hz'c⟩ hKCs hKCnab hK θ hθs ?_
      intro htop
      apply hc.red.not_le_of_not_mem_of_center hc.center hc.order hc.comp hc.normal hzK
      intro k hk
      obtain ⟨w, hwX, hwk⟩ : (⟨k, hk⟩ : KC) ∈ Subgroup.map θ ((((Hs ⊓ M).subgroupOf Hs).map
          (QuotientGroup.mk' (primeComplementCore (G := Hs) p))).subgroupOf W) :=
        htop ▸ Subgroup.mem_top _
      have h1 := d1StarPsi_mem_of_mem_X0 hp hzp hzM hCHs ⟨w, hWA w.2⟩ hwX
      rw [← hθ w, hwk] at h1
      exact h1
    · exact (hIII Ks hKs
        (fun L hL => hred.eq_of_forall_mem_center hKs hL hcent) hcyc hcent).elim

end CFSG.AGLEmbedding
