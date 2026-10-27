module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNoSPCz
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNoSPCyclic
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNoSPIdent
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNoSPOmega
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallCentralizer

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Cz

variable {G : Type} [Group G] [Finite G] {p : ℕ} {M : Subgroup G} {z : G}
  {T : Sylow p (Subgroup.centralizer ({z} : Set G))} {Pbar : Sylow p (D1CzQuot p z)}
  {K : Subgroup (D1CzQuot p z)}

theorem D1CzReduced.twoCore_inf_le (hc : D1CzReduced p M z T Pbar K) (hzK : d1CzElt p z ∉ K)
    (hK : IsCaseTwoGroup p K) (hNo2 : KFactCaseTwoNoTwo)
    (hTM : (T : Subgroup _).map (Subgroup.centralizer ({z} : Set G)).subtype ≤ M) :
    pCoreOf 2 M ⊓ Subgroup.centralizer ({z} : Set G) ≤
      GLBPrimeCore p (Subgroup.centralizer ({z} : Set G)) := by
  have hp := hc.red.prime
  have : Fact p.Prime := ⟨hp⟩
  have hKn := hc.normal
  set C := Subgroup.centralizer ({z} : Set G) with hCdef
  set π := QuotientGroup.mk' (primeComplementCore (G := C) p) with hπ
  set U₀ : Subgroup C := (pCoreOf 2 M ⊓ C).subgroupOf C with hU₀
  set U : Subgroup (D1CzQuot p z) := U₀.map π with hU
  have hU₀2 : IsPGroup 2 U₀ :=
    ((RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M).to_le inf_le_left).comap_subtype
  have hU2 : IsPGroup 2 U := hU₀2.map π
  obtain ⟨t, htA, htp, -⟩ := exists_mem_sylow_inf_component hp hc.red.ne_two hc.red.core_eq_bot
    Pbar hc.comp
  have htP := htA.1
  rw [hc.sylow_eq] at htP
  obtain ⟨τ, hτT, hτt⟩ := htP
  subst hτt
  have hτM : (τ : G) ∈ M := hTM ⟨τ, hτT, rfl⟩
  have hτU₀ : τ ∈ Subgroup.normalizer (U₀ : Set C) := by
    apply mem_normalizer_of_conj_map_le
    rintro _ ⟨u, hu, rfl⟩
    have h1 := (Subgroup.mem_normalizer_iff.mp (localGroup_le_normalizer_pCoreOf 2 M hτM) u).mp
      hu.1
    exact ⟨by simpa using h1, (MulAut.conj τ u).2⟩
  have hπτU : π τ ∈ Subgroup.normalizer (U : Set (D1CzQuot p z)) := by
    apply mem_normalizer_of_conj_map_le
    rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    refine ⟨τ * u * τ⁻¹, (Subgroup.mem_normalizer_iff.mp hτU₀ u).mp hu, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]
  set V : Subgroup (MulAut K) := U.map (MulAut.conjNormal (H := K)) with hV
  have hV2 : IsPGroup 2 V := hU2.map _
  have hconj : MulAut.conjNormal (H := K) (π τ) = MulAut.conj (⟨π τ, htA.2⟩ : K) := by
    ext k
    simp [MulAut.conjNormal_apply]
  have hVn : MulAut.conj (⟨π τ, htA.2⟩ : K) ∈ Subgroup.normalizer (V : Set (MulAut K)) := by
    rw [← hconj]
    apply mem_normalizer_of_conj_map_le
    rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    refine ⟨π τ * u * (π τ)⁻¹, (Subgroup.mem_normalizer_iff.mp hπτU u).mp hu, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]
  have hτp : orderOf (⟨π τ, htA.2⟩ : K) = p := by rw [Subgroup.orderOf_mk]; exact htp
  have hVbot := hNo2 p K hK _ hτp V hV2 hVn
  have hUC : U ≤ Subgroup.centralizer (K : Set (D1CzQuot p z)) := by
    rw [← ker_conjNormal_eq_centralizer]
    exact (Subgroup.map_eq_bot_iff _).mp hVbot
  have hUbot : U = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    obtain ⟨k, hk⟩ := hU2 ⟨u, hu⟩
    have huk : u ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    exact Subgroup.mem_bot.mpr (hc.eq_one_of_mem_centralizer hzK (hUC hu) huk)
  have hU₀le : U₀ ≤ primeComplementCore (G := C) p := by
    have := (Subgroup.map_eq_bot_iff _).mp hUbot
    rwa [hπ, QuotientGroup.ker_mk'] at this
  intro x hx
  rw [glbPrimeCore_eq_primeComplementCoreOf]
  exact ⟨⟨x, hx.2⟩, hU₀le hx, rfl⟩

end Cz

theorem D1CaseTwoDataAt.czShape {G : Type} [Group G] [Finite G] (hAut : KFactCycAut) (hS :
    KFactSeitzCyc) (hL2 : KFactCaseTwoLocal)
    (hInv : KFactCaseTwoInvIn G) (hSch : KFactCatalogSchreier) (hSyl : KFactCaseTwoSylow)
    (hNo2 : KFactCaseTwoNoTwo) {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
    {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)} (hd : D1CaseTwoDataAt p P M H R Rbar)
    {z : H} (hz : D1CaseTwoCand p M H R z) (hnSP : ¬ D1CzSP p (z : G))
    (hout : D1CzOutside p (z : G)) : D1CzShape p P M R (z : G) := by
  obtain ⟨L, hL, hLX, hzR, hzp, hRz, hzL⟩ := hz
  have hcand : D1CaseTwoCand p M H R z := ⟨L, hL, hLX, hzR, hzp, hRz, hzL⟩
  obtain ⟨A₀, φ, hφ⟩ := D1CaseTwoDataAt.exists_surjective_czQuot hd hL hzp hzL
  have hiso : IsCaseTwoGroup p L :=
    hd.cfg.red.isCaseTwoGroup_of_not_le_of_aut hd.cfg.catalog (hAut _ _ _ _ hd.cfg.red
        hd.cfg.catalog)
      hS hd.cyclic hd.rank hL hLX
  have hLp : Group.IsPerfect L := ⟨hL.2.2.1⟩
  refine ⟨fun m hm T hRT hTP => ?_, ?_⟩
  · obtain ⟨Pbar, K, hc⟩ := D1CaseTwoDataAt.exists_czReduced hd hAut hS hSyl hcand hm hRT hTP
    have hzK : d1CzElt p (z : G) ∉ K := hout K hc.comp
    obtain ⟨hcyc, hK⟩ := hc.isCyclic_and_isCaseTwoGroup_at hAut hS hSch hInv hnSP hzK hiso hLp φ hφ
    exact hc.shape_omega hL2 hzK hcyc hK hzp
  · obtain ⟨m, hm, T, hRT, hTP⟩ := hd.cfg.exists_sylow_centralizer hRz
    obtain ⟨Pbar, K, hc⟩ := D1CaseTwoDataAt.exists_czReduced hd hAut hS hSyl hcand hm hRT hTP
    have hzK : d1CzElt p (z : G) ∉ K := hout K hc.comp
    obtain ⟨-, hK⟩ := hc.isCyclic_and_isCaseTwoGroup_at hAut hS hSch hInv hnSP hzK hiso hLp φ hφ
    have hQ'M : (P : Subgroup G).map (MulAut.conj m).toMonoidHom ≤ M := by
      rintro _ ⟨x, hx, rfl⟩
      exact M.mul_mem (M.mul_mem hm (hd.cfg.ext.sylow_le hx)) (M.inv_mem hm)
    exact hc.twoCore_inf_le hzK hK hNo2 (hTP.trans hQ'M)

theorem d1CaseTwoShape_of (hβ : KFactBeta) (hS : KFactSeitzCyc) (hL2 : KFactCaseTwoLocal)
    (hInv : KFactCaseTwoInv) (hSch : KFactCatalogSchreier) (hSyl : KFactCaseTwoSylow)
    (hNo2 : KFactCaseTwoNoTwo) : D1CaseTwoShape := fun _ _ _ _ _ _ _ _ _ hd _ hz hnSP hout =>
  hd.toAt.czShape (kFactCycAut_of_kFactBeta hβ) hS hL2 (kFactCaseTwoInvIn_of_kFactCaseTwoInv hInv)
    hSch hSyl hNo2 hz hnSP hout
end CFSG.AGLEmbedding
