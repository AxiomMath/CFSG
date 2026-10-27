module

import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizer
import CFSG.LocalAnalysis.AGLEmbedding.GapROneBSAux
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoDataAux
import CFSG.LocalAnalysis.AGLEmbedding.OneLieLambdaAux
import CFSG.LocalAnalysis.AGLEmbedding.OneLieMData
import CFSG.LocalAnalysis.AGLEmbedding.OneLieMSideCore
import CFSG.LocalAnalysis.AGLEmbedding.OneLieZZClose
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieDefs
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCompetitorAux

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Lambda

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneLieData.inf_centralizer_eq_bot (hd : D1OneLieData p P M H R Rbar K) :
    K ⊓ Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxK, hxC⟩
  have hcen : (⟨x, hxK⟩ : K) ∈ Subgroup.center K := Subgroup.mem_center_iff.mpr fun k =>
    Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC _ k.2)
  rw [hd.center, Subgroup.mem_bot] at hcen
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val hcen)

theorem D1OneLieData.mk_mem_sup_of_mem (hK : KFactOneLie) (h84 : Asc81bEightFour)
    (hD2 : D1NoXBlock) (hd : D1OneLieData p P M H R Rbar K)
    (hY : pCorePreimage p M ⊓ d1LiftX p H R K ≠ ⊥)
    (hU3 : ¬ (IsUnitaryGroup p K ∧
      d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) =
        centerOf ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K)))
    {L : Subgroup G} (hL : IsTwoPrimeComponent M L) {x : G} (hxH : x ∈ H) (hxL : x ∈ L) :
    QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨x, hxH⟩ ∈
      ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) ⊔
        Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) := by
  have : Fact p.Prime := ⟨hd.cfg.red.prime⟩
  exact hd.centralizer_d1MapPCore_le hK h84 hD2 hY hU3
    (mk_mem_centralizer_d1MapPCore (hd.toPhaseThree hK).twoCore_M_le_glbPrimeCore
      (hL.le_pCoreCentralizerPreimage p hxL) hxH)

theorem D1OneLieData.mem_d1PlusCore_of_mul_conj_mem (hK : KFactOneLie) (h84 : Asc81bEightFour)
    (hD2 : D1NoXBlock) (hd : D1OneLieData p P M H R Rbar K)
    (hY : pCorePreimage p M ⊓ d1LiftX p H R K ≠ ⊥)
    (hU3 : ¬ (IsUnitaryGroup p K ∧
      d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) =
        centerOf ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K)))
    {L : Subgroup G} (hL : IsTwoPrimeComponent M L) {a g : G} (haH : a ∈ H) (haL : a ∈ L)
    (hgH : g ∈ H) (hgL : g ∈ L) (hga : g * a * g⁻¹ * a ∈ pCoreOf 2 M) :
    a ∈ d1PlusCore p H K := by
  have hp : p.Prime := hd.cfg.red.prime
  have hKn : K.Normal := hd.cfg.red.normal_of_rankOne hd.comp hd.noncyclic
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p) with hπ
  set T := (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K with hT
  set C := Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) with hC
  have hTp : IsPGroup p T := Rbar.isPGroup'.to_le inf_le_left
  have hTC : T ⊓ C = ⊥ :=
    le_bot_iff.mp (hd.inf_centralizer_eq_bot ▸ inf_le_inf_right C inf_le_right)
  have hcomm : ∀ t ∈ T, ∀ c ∈ C, t * c = c * t := fun t ht c hc =>
    Subgroup.mem_centralizer_iff.mp hc t ht.2
  have hx := hd.mk_mem_sup_of_mem hK h84 hD2 hY hU3 hL haH haL
  have hy := hd.mk_mem_sup_of_mem hK h84 hD2 hY hU3 hL hgH hgL
  have hinv : π ⟨g, hgH⟩ * π ⟨a, haH⟩ * (π ⟨g, hgH⟩)⁻¹ = (π ⟨a, haH⟩)⁻¹ := by
    have h1 : π (⟨g, hgH⟩ * ⟨a, haH⟩ * (⟨g, hgH⟩ : H)⁻¹ * ⟨a, haH⟩) = 1 :=
      (mk'_primeComplementCore_eq_one_iff p _).mpr
        ((hd.toPhaseThree hK).twoCore_M_le_glbPrimeCore hga)
    rw [map_mul, map_mul, map_mul, map_inv] at h1
    exact eq_inv_of_mul_eq_one_left h1
  exact ⟨⟨a, haH⟩, mem_of_conj_eq_inv_of_mem_sup hp hd.cfg.red.ne_two hTp hTC hcomm hx hy hinv,
    rfl⟩

theorem D1OneLieData.le_d1PlusCore_of_perfect (hK : KFactOneLie) (h84 : Asc81bEightFour)
    (hD2 : D1NoXBlock) (hd : D1OneLieData p P M H R Rbar K)
    (hY : pCorePreimage p M ⊓ d1LiftX p H R K ≠ ⊥)
    (hU3 : ¬ (IsUnitaryGroup p K ∧
      d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) =
        centerOf ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K)))
    {L V : Subgroup G} (hL : IsTwoPrimeComponent M L) (hVH : V ≤ H) (hVL : V ≤ L)
    (hV : ⁅V, V⁆ = V) : V ≤ d1PlusCore p H K := by
  have hp : p.Prime := hd.cfg.red.prime
  have hKn : K.Normal := hd.cfg.red.normal_of_rankOne hd.comp hd.noncyclic
  refine le_d1PlusCore_of_map_le hVH (le_of_perfect_of_le_sup hp
    (T := (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K)
    (Rbar.isPGroup'.to_le inf_le_left) (commutator_map_eq_self hVH hV) ?_)
  rintro _ ⟨⟨v, hvH⟩, hv, rfl⟩
  exact hd.mk_mem_sup_of_mem hK h84 hD2 hY hU3 hL hvH (hVL (Subgroup.mem_subgroupOf.mp hv))

theorem D1OneLieData.exists_conj_zpowers_eq (hd : D1OneLieData p P M H R Rbar K) {a z : G}
    (haN : a ∈ d1PlusCore p H K) (hap : orderOf a = p) (hzR : z ∈ R)
    (hzN : z ∈ d1PlusCore p H K) (hzp : orderOf z = p) :
    ∃ k ∈ d1PlusCore p H K, Subgroup.zpowers (k * a * k⁻¹) = Subgroup.zpowers z := by
  have hp : p.Prime := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hNle, hHN, -⟩ := hd.d1PlusCore_facts
  have hNH : d1PlusCore p H K ≤ H := hNle.trans inf_le_left
  set C' := (d1PlusCore p H K).subgroupOf H with hC'
  have : C'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mpr hHN
  obtain ⟨T, hT⟩ := hd.cfg.ext.isSylow
  have hTC : IsCyclic ((T : Subgroup H) ⊓ C' : Subgroup H) := by
    have hmap : (((T : Subgroup H) ⊓ C' : Subgroup H).map H.subtype) ≤ d1PlusCore p H K := by
      rintro _ ⟨x, ⟨-, hx⟩, rfl⟩
      exact Subgroup.mem_subgroupOf.mp hx
    have hcyc := hd.isCyclic_of_le_d1PlusCore hmap ((T.isPGroup'.to_le inf_le_left).map _)
    let e := (((T : Subgroup H) ⊓ C' : Subgroup H)).equivMapOfInjective H.subtype
      H.subtype_injective
    exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
  have hzH : z ∈ H := hd.cfg.ext.le_H hzR
  have haH : a ∈ H := hNH haN
  have hzT : (⟨z, hzH⟩ : H) ∈ (T : Subgroup H) := by
    rw [← hT] at hzR
    obtain ⟨z', hz', hzz'⟩ := hzR
    rwa [show z' = ⟨z, hzH⟩ from Subtype.ext hzz'] at hz'
  obtain ⟨c, hc, hca⟩ := exists_conj_zpowers_eq_of_isCyclic T hTC
    (a := ⟨a, haH⟩) (z := ⟨z, hzH⟩) (Subgroup.mem_subgroupOf.mpr haN)
    (by rw [Subgroup.orderOf_mk, hap]) hzT (Subgroup.mem_subgroupOf.mpr hzN)
    (by rw [Subgroup.orderOf_mk, hzp])
  refine ⟨c, Subgroup.mem_subgroupOf.mp hc, ?_⟩
  have hmap := congrArg (Subgroup.map H.subtype) hca
  rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers] at hmap
  simpa using hmap

theorem D1OneLieData.exists_mem_map_conj (hd : D1OneLieData p P M H R Rbar K) {L : Subgroup G}
    (hL : IsTwoPrimeComponent M L) {a z : G} (haL : a ∈ L) (haN : a ∈ d1PlusCore p H K)
    (hap : orderOf a = p) (hzR : z ∈ R) (hzN : z ∈ d1PlusCore p H K) (hzp : orderOf z = p) :
    ∃ k ∈ d1PlusCore p H K, IsTwoPrimeComponent M (L.map (MulAut.conj k).toMonoidHom) ∧
      z ∈ L.map (MulAut.conj k).toMonoidHom := by
  obtain ⟨k, hkN, hk⟩ := hd.exists_conj_zpowers_eq haN hap hzR hzN hzp
  have hkM : k ∈ M := (hd.d1PlusCore_facts.1 hkN).2
  have hz : z ∈ Subgroup.zpowers (k * a * k⁻¹) := hk ▸ Subgroup.mem_zpowers z
  have hmem : k * a * k⁻¹ ∈ L.map (MulAut.conj k).toMonoidHom := ⟨a, haL, by simp⟩
  exact ⟨k, hkN, hL.map_conj hkM, (Subgroup.zpowers_le.mpr hmem) hz⟩

theorem D1OneLieData.exists_mul_ne_of_mem (hd : D1OneLieData p P M H R Rbar K)
    (hWK : d1MapPCore p M H ≤ K) {z : G} (hzR : z ∈ R) (hzN : z ∈ d1PlusCore p H K)
    (hzp : orderOf z = p) {L : Subgroup G} (hL : IsTwoPrimeComponent M L) (hzL : z ∈ L) :
    ∃ l ∈ barM M L, QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hL.le hzL⟩ * l ≠
      l * QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hL.le hzL⟩ := by
  have hp : p.Prime := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  by_contra hno
  push Not at hno
  apply hd.not_mem_pCorePreimage hWK hzR hzN hzp
  have hzM : z ∈ M := hL.le hzL
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set A := barM M (Subgroup.zpowers z) with hA
  have hAL : A ≤ barM M L := barM_mono (Subgroup.zpowers_le.mpr hzL)
  have hAC : A ≤ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    rintro _ ⟨⟨w, hwM⟩, hw, rfl⟩
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_subgroupOf.mp hw)
    have hwz : (⟨w, hwM⟩ : M) = ⟨z, hzM⟩ ^ j := Subtype.ext (by simpa using hj.symm)
    rw [hwz, map_zpow]
    refine Subgroup.zpow_mem _ ?_ j
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact (hno l hl).symm
  have hAp : IsPGroup p A := by
    have h1 : IsPGroup p (Subgroup.zpowers z) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzp, pow_one])
    exact (h1.comap_subtype (K := M)).map _
  have hcomp : ∀ Lb : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsComponentOf Lb ⊤ →
      A ≤ Subgroup.centralizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    intro Lb hLb
    by_cases he : Lb = barM M L
    · rw [he]
      exact hAC
    · have hc := CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ hL.component hLb
        (Ne.symm he)
      exact hAL.trans ((Subgroup.commutator_eq_bot_iff_le_centralizer).mp hc)
  have hcore : ∀ l : ℕ, l.Prime → A ≤ Subgroup.centralizer
      (CFSG.pCore l (↥M ⧸ CFSG.pCore 2 ↥M) : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    intro l hl
    have := Fact.mk hl
    exact hAL.trans (Subgroup.le_centralizer_iff.mp (pCore_le_centralizer_component l hL.component))
  have hle := le_pCore_of_le_centralizer_components hAp hcomp hcore
  exact ⟨⟨z, hzM⟩, hle ⟨⟨z, hzM⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers z), rfl⟩, rfl⟩

end Lambda

end CFSG.AGLEmbedding
