module

public import CFSG.ClassicalInvolution.AschTight.S1911E2b
public import CFSG.ClassicalInvolution.AschTight.Sec19Targets5
public import CFSG.ClassicalInvolution.AschTight.Hall196Idx
public import CFSG.ClassicalInvolution.AschTight.Hall196Basic

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1911

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.GorensteinWalter

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {K : Subgroup G} {z : G} {S : Sylow 2 G} {W : Subgroup G}

theorem innerDiagonalTwo_of_c19_16F (h16F : C19_16FTmp p f) (hd : Sec19Data p f K z S W) :
    InnerDiagonalTwo p f K := by
  intro e hFcard hF h3 x hx
  have hNC := normalizer_eq_centralizer_of_tight hd.tight.toTightBranch
  set H : Subgroup (Subgroup.normalizer (K : Set G)) :=
    ((SemidirectProduct.inl : PGL2 (GaloisField p f) →* PGammaL2 (GaloisField p f)).range).comap
      (normalizerToPGammaL2Mod e hFcard hF h3) with hH
  have hle : sec19X K z ⊔ centralizerModOdd ⊤ K ≤
      H.map (Subgroup.normalizer (K : Set G)).subtype := by
    refine sup_le (fun a ha => ?_) (fun c hc => ?_)
    · have haN : a ∈ Subgroup.normalizer (K : Set G) :=
        hNC ▸ Hall196.gammaGen_le_centralizer _ z ha
      refine ⟨⟨a, haN⟩, ?_, rfl⟩
      exact c19_5Tmp_of_l6_2 p f (l6_2ModTmp p f) G K z hd.tight e hFcard hF h3 ⟨a, haN⟩
        (by rw [xGroup_eq_gammaGen]; exact ha)
    · have hc1 : normalizerToPGammaL2Mod e hFcard hF h3 ⟨c, hc.2.1⟩ = 1 :=
        (Hall196.normalizerToPGammaL2Mod_eq_one_iff e hFcard hF h3 ⟨c, hc.2.1⟩).mpr hc.2.2.2
      refine ⟨⟨c, hc.2.1⟩, ?_, rfl⟩
      show normalizerToPGammaL2Mod e hFcard hF h3 ⟨c, hc.2.1⟩ ∈
        (SemidirectProduct.inl : PGL2 (GaloisField p f) →* PGammaL2 (GaloisField p f)).range
      rw [hc1]
      exact Subgroup.one_mem _
  have hxC : (x : G) ∈ Subgroup.centralizer ({z} : Set G) := hNC ▸ x.2
  have hx2 : IsPGroup 2 (Subgroup.zpowers (x : G)) := by
    have := hx.map (Subgroup.normalizer (K : Set G)).subtype
    rwa [MonoidHom.map_zpowers] at this
  obtain ⟨c, hc, hcx⟩ := exists_conj_le_of_sylow_le S hd.hSz (Subgroup.zpowers_le.mpr hxC) hx2
  have hyS : c * (x : G) * c⁻¹ ∈ (S : Subgroup G) :=
    hcx (conj_mem_conjSub (Subgroup.mem_zpowers _))
  obtain ⟨y, hyH, hy⟩ := hle (h16F G K z S W hd hyS)
  set c' : Subgroup.normalizer (K : Set G) := ⟨c, hNC ▸ hc⟩ with hc'
  have hyx : y = c' * x * c'⁻¹ := Subtype.ext (by simpa [hc'] using hy)
  have hx' : x = c'⁻¹ * y * c' := by rw [hyx]; group
  rw [hx', map_mul, map_mul, map_inv]
  have hN := pGammaL2PGLRangeNormal (GaloisField p f)
  simpa using hN.conj_mem _ hyH (normalizerToPGammaL2Mod e hFcard hF h3 c')⁻¹

variable (p f) in
theorem tightControlledD_of_targets5 (hB3 : GoldschmidtB3Tmp) (h11b : C19_11bTmp p f)
    (h16F : C19_16FTmp p f) (hIH : IHAllD p f) : TightControlledD p f := by
  intro G _ _ _ K z ht0
  have ht := S19R.tightStd_of_tightBranchD ht0
  by_cases hc : ConcOrTF4 G
  · exact hc.conclusionD ht.branch.notFourGenerated
  exfalso
  by_cases hA : AllTypeTwo K z
  · exact false_of_allTypeTwo hB3 ht hA
  obtain ⟨Q₀, S, hRS, -, hSz, -⟩ := exists_sylow_setup ht
  obtain ⟨W, hWmem, hWS⟩ := exists_wSet_le ht S
  have hd : Sec19Data p f K z S W :=
    ⟨ht, hA, hIH G K z ht.branch, hc, ⟨Q₀, hRS⟩, hSz, hWmem, hWS⟩
  have hE3 := normalizerQuotientTwoGeneratedStar_of_innerDiagonalTwo ht.branch.odd
    ht.branch.five ht.branch.member (innerDiagonalTwo_of_c19_16F h16F hd)
  exact ht.branch.notFourGenerated
    (twoSubgroupsFourGenerated_of_e2Prime (c19_E2PrimeTmp_of p f h11b) hd hE3)

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
