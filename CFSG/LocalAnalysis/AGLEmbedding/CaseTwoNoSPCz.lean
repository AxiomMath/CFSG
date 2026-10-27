module

import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNoSPLayer
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDataAt
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEscapeK
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCompetitorAux2
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallPoszAux

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Data

variable {G : Type} [Group G] [Finite G]

structure D1CzReduced (p : ℕ) (M : Subgroup G) (z : G)
    (T : Sylow p (Subgroup.centralizer ({z} : Set G))) (Pbar : Sylow p (D1CzQuot p z))
    (K : Subgroup (D1CzQuot p z)) : Prop where
  sylow_eq : (Pbar : Subgroup (D1CzQuot p z)) =
    (T : Subgroup _).map (QuotientGroup.mk' (primeComplementCore p))
  red : ReducedNongeneration p (D1CzQuot p z) Pbar
    (((Subgroup.centralizer ({z} : Set G) ⊓ M).subgroupOf
      (Subgroup.centralizer ({z} : Set G))).map (QuotientGroup.mk' (primeComplementCore p)))
  catalog : CatalogSimpleSections (D1CzQuot p z)
  center : d1CzElt p z ∈ Subgroup.center (D1CzQuot p z)
  order : orderOf (d1CzElt p z) = p
  comp : IsComponentOf K ⊤
  normal : K.Normal
  unique : ∀ L : Subgroup (D1CzQuot p z), IsComponentOf L ⊤ → L = K

end Data

section Config

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}

theorem D1CaseTwoDataAt.exists_surjective_czQuot (hd : D1CaseTwoDataAt p P M H R Rbar)
    {L : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hL : IsComponentOf L ⊤) {z : H}
    (hzp : orderOf (z : G) = p)
    (hzL : QuotientGroup.mk' (primeComplementCore (G := H) p) z ∈
      Subgroup.centralizer (L : Set (H ⧸ primeComplementCore (G := H) p))) :
    ∃ (A : Subgroup (D1CzQuot p (z : G))) (f : A →* L), Function.Surjective f := by
  have hred := hd.cfg.red
  have hp := hred.prime
  have : Fact p.Prime := ⟨hp⟩
  have hO := primeComplementCore_coprime (G := H) p
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p)
  set W : Subgroup G := Subgroup.centralizer ({(z : G)} : Set G) ⊓ (L.comap π).map H.subtype
  have hWH : W ≤ H := inf_le_right.trans (Subgroup.map_subtype_le _)
  have hWC : W ≤ Subgroup.centralizer ({(z : G)} : Set G) := inf_le_left
  have hφ₀ : ∀ w : W, π (Subgroup.inclusion hWH w) ∈ L := by
    rintro ⟨w, -, h, hh, rfl⟩
    exact hh
  set φ : W →* L := (π.comp (Subgroup.inclusion hWH)).codRestrict L hφ₀
  have hzH' : orderOf z = p := (Subgroup.orderOf_coe z).symm.trans hzp
  have hφ : Function.Surjective φ := by
    intro k
    obtain ⟨g, hg, hgk⟩ := exists_mem_centralizer_mk_eq hp _ hO
      (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzH', pow_one]))
      (Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hzL k k.2))
    have hgC : (g : G) ∈ Subgroup.centralizer ({(z : G)} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hg))
    have hgK : g ∈ L.comap π := by
      rw [Subgroup.mem_comap, hgk]
      exact k.2
    exact ⟨⟨g, hgC, g, hgK, rfl⟩, Subtype.ext hgk⟩
  have hZ := hred.center_eq_bot_of_isCyclic hL (hd.cyclic L hL)
  have : IsSimpleGroup (L ⧸ Subgroup.center L) := hL.2.2.2
  have : IsSimpleGroup L :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.isSimpleGroup
  obtain ⟨t, htRL, ht, -⟩ := exists_mem_sylow_inf_component hp hred.ne_two hred.core_eq_bot Rbar
    hL
  have hx : (⟨t, htRL.2⟩ : L) ≠ 1 := fun h1 =>
    hp.one_lt.ne' (by rw [← ht, show t = 1 from congrArg Subtype.val h1, orderOf_one])
  have hxp : (⟨t, htRL.2⟩ : L) ^ p ^ 1 = 1 := by
    rw [pow_one]
    exact Subtype.ext (by
      rw [Subgroup.coe_pow, orderOf_dvd_iff_pow_eq_one.mp (dvd_of_eq ht), Subgroup.coe_one])
  have hOC := primeComplementCore_coprime (G := Subgroup.centralizer ({(z : G)} : Set G)) p
  have hN : ∀ n ∈ (primeComplementCore (G := Subgroup.centralizer ({(z : G)} : Set G)) p).comap
      (Subgroup.inclusion hWC), p.Coprime (orderOf n) := by
    intro n hn
    have h1 : orderOf (Subgroup.inclusion hWC n) ∣ Nat.card
        (primeComplementCore (G := Subgroup.centralizer ({(z : G)} : Set G)) p) :=
      Subgroup.orderOf_dvd_natCard _ hn
    rw [orderOf_injective _ (Subgroup.inclusion_injective hWC)] at h1
    exact hOC.coprime_dvd_right h1
  have hker := le_ker_of_isSimpleGroup φ hφ _ hN hx hxp
  set ρ : W →* D1CzQuot p (z : G) := (QuotientGroup.mk' _).comp (Subgroup.inclusion hWC) with hρ
  obtain ⟨f, -, hf, -⟩ := exists_surjective_comp_eq ρ.rangeRestrict ρ.rangeRestrict_surjective
    φ hφ (by
      rw [MonoidHom.ker_rangeRestrict]
      intro w hw
      have h1 : ρ w = 1 := hw
      rw [hρ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact hker h1)
  exact ⟨ρ.range, f, hf⟩

theorem D1CaseTwoDataAt.exists_czReduced (hd : D1CaseTwoDataAt p P M H R Rbar) (hAut : KFactCycAut)
    (hS : KFactSeitzCyc) (hSyl : KFactCaseTwoSylow) {z : H} (hz : D1CaseTwoCand p M H R z)
    {m : G} (hm : m ∈ M) {T : Sylow p (Subgroup.centralizer ({(z : G)} : Set G))}
    (hRT : R ≤ (T : Subgroup _).map (Subgroup.centralizer ({(z : G)} : Set G)).subtype)
    (hTP : (T : Subgroup _).map (Subgroup.centralizer ({(z : G)} : Set G)).subtype ≤
      (P : Subgroup G).map (MulAut.conj m).toMonoidHom) :
    ∃ (Pbar : Sylow p (D1CzQuot p (z : G))) (K : Subgroup (D1CzQuot p (z : G))),
      D1CzReduced p M (z : G) T Pbar K := by
  obtain ⟨L, hL, hLX, hzR, hzp, hRz, hzL⟩ := hz
  have hp := hd.cfg.red.prime
  have hp2 := hd.cfg.red.ne_two
  have : Fact p.Prime := ⟨hp⟩
  set P' : Sylow p G := m • P with hP'def
  have hP'eq : (P' : Subgroup G) = (P : Subgroup G).map (MulAut.conj m).toMonoidHom := by
    rw [hP'def, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  have hP'M : (P' : Subgroup G) ≤ M := by
    rw [hP'eq]
    rintro _ ⟨x, hx, rfl⟩
    exact M.mul_mem (M.mul_mem hm (hd.cfg.ext.sylow_le hx)) (M.inv_mem hm)
  have hW' : GLBWeakCore p (P' : Subgroup G) ≤ M := by
    rw [hP'eq]
    exact weakCore_conj_le hp hd.cfg.ext.weakCore_le hm
  have hTP' : (T : Subgroup (Subgroup.centralizer ({(z : G)} : Set G))).map
      (Subgroup.centralizer ({(z : G)} : Set G)).subtype ≤ P' := by
    rw [hP'eq]
    exact hTP
  have hCM := hd.cfg.centralizer_not_le hLX z.2 hzp hzL
  have hcore : GLBPrimeCore p (Subgroup.centralizer ({(z : G)} : Set G)) ≤ M :=
    intersecting_local_primeCore_le p hp P hd.cfg.ext.sylow_le hd.cfg.ext.weakCore_le
      (hd.cfg.ext.three_le_pRank.trans (pRank_mono p hp (le_inf hRz hd.cfg.ext.le_M)))
  have hT3 : 3 ≤ Open.pRank p ((T : Subgroup (Subgroup.centralizer ({(z : G)} : Set G))).map
      (Subgroup.centralizer ({(z : G)} : Set G)).subtype) :=
    hd.cfg.ext.three_le_pRank.trans (pRank_mono p hp hRT)
  obtain ⟨Pbar, hPbar, hred⟩ :=
    reducedNongeneration_of_not_le hp hp2 P' hP'M hW' hCM T hTP' hT3 hcore
  obtain ⟨A, f, hf⟩ := D1CaseTwoDataAt.exists_surjective_czQuot hd hL hzp hzL
  have hiso : IsCaseTwoGroup p L :=
    hd.cfg.red.isCaseTwoGroup_of_not_le_of_aut hd.cfg.catalog (hAut _ _ _ _ hd.cfg.red
        hd.cfg.catalog) hS hd.cyclic hd.rank hL hLX
  obtain ⟨hLs, hLn, -⟩ :=
    hd.cfg.red.isSimpleGroup_of_isCyclic hd.cfg.catalog hL (hd.cyclic L hL)
  have : IsSimpleGroup L := hLs
  obtain ⟨TL⟩ := (inferInstance : Nonempty (Sylow p L))
  have hlayer := ReducedNongeneration.layer_ne_bot_of_surjective_of_card hred hLn TL
    (hSyl p L hiso TL) f hf
  obtain ⟨K, hK⟩ := exists_isComponentOf_of_layer_ne_bot hlayer
  have hzZ : d1CzElt p (z : G) ∈ Subgroup.center (D1CzQuot p (z : G)) :=
    mk_mem_center_centralizer _ rfl
  have hzbp : orderOf (d1CzElt p (z : G)) = p := orderOf_mk_of_coprime hp _
    (primeComplementCore_coprime p) (by rw [← Subgroup.orderOf_coe]; exact hzp)
  have hz1 : (z : G) ≠ 1 := fun h1 => hp.one_lt.ne (by rw [← hzp, h1, orderOf_one])
  refine ⟨Pbar, K, hPbar, hred, ?_, hzZ, hzbp, hK,
    hred.normal_of_isComponentOf_of_center hzZ hzbp hK,
    fun L' hL' => hred.eq_of_isComponentOf_of_center hzZ hzbp hL' hK⟩
  exact (catalogSimpleSections_of_isKProper hd.cfg.glob.kProper _
    (centralizer_singleton_ne_top hd.cfg.glob.simple hd.cfg.glob.nonab hz1)).quotient _

end Config

end CFSG.AGLEmbedding
