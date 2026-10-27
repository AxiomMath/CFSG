module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S152He12E
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S152U21
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223KcLocal

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace S15223

theorem input1210Kc_of_F4 (h11 : StageLemma15211_F4) (h12 : He12.StageLemma15212W_F4) (h13 : StageLemma15213_F4)
    (hN : StageNotation15209_F4) : Input1210Kc_F4 := by
  intro G _ _ T Mc M hs B₀ hB₀ H hH hne hO
  obtain ⟨B, hB⟩ := (hN G T Mc M hs H hH).sigmaPrime_nonempty
  have h11' := h11 G T Mc M hs H hH B hB
  have h12' := h12 G T Mc M hs H hH B hB
  obtain ⟨B₀', -, huniq, hdata⟩ := (h13 G T Mc M hs H hH).exists_B0
  have hZS : zSOf T Mc M B₀ = ⁅V154 T Mc M, B⁆ := by
    rw [huniq B₀ hB₀]
    exact (hdata B hB).2.2.1.symm
  have hT : IsSylowTwoOf T H := S152N.isSylowTwoOf_hStar hs hH
  have hBT : B ≤ T := by
    obtain ⟨⟨A, -, hAB⟩, -⟩ := hB
    rw [hAB]
    exact inf_le_right.trans (B6.pCoreOf_two_le_of_isSylowTwoOf hT)
  have hZT : ⁅V154 T Mc M, B⁆ ≤ T := by
    refine Subgroup.commutator_le.mpr fun v hv b hb => ?_
    have hVT := S152N.V154_le_T hs hv
    rw [commutatorElement_def]
    exact T.mul_mem (T.mul_mem (T.mul_mem hVT (hBT hb)) (T.inv_mem hVT)) (T.inv_mem (hBT hb))
  have hZe := h11'.elemAbelian
  have hZn := h11'.normal
  have hTMc : T ≤ Mc := hs.qtfe.t_le_mc
  have hO2 : pCoreOf 2 (conjClosure (oTwoUpper H) Mc ⊔ T) ≤
      Subgroup.centralizer ((⁅V154 T Mc M, B⁆ : Subgroup G) : Set G) := by
    have := hO.trans (inf_le_right : sOf152 T Mc M B₀ ≤
      Subgroup.centralizer (zSOf T Mc M B₀ : Set G))
    rwa [hZS] at this
  rw [hZS]
  have hO' : ∀ X : Subgroup G, X ⊔ T = conjClosure (oTwoUpper H) Mc ⊔ T →
      pCoreOf 2 (X ⊔ T) ≤ Subgroup.centralizer ((⁅V154 T Mc M, B⁆ : Subgroup G) : Set G) :=
    fun X hX => by
      rw [hX]
      exact hO2
  have hKn : Mc ≤ Subgroup.normalizer (conjClosure (oTwoUpper H) Mc : Set G) :=
    le_normalizer_conjClosure (oTwoUpper H) Mc
  have hsingle : quasithinIsMaximalLocal T (conjClosure (oTwoUpper H) Mc) →
      conjClosure (oTwoUpper H) Mc ≤ Subgroup.centralizer
        ((⁅V154 T Mc M, B⁆ : Subgroup G) : Set G) := fun hmax => by
    refine le_centralizer_of_not_faithful hs.qtfe hmax.1 hZT hZe (hO' _ rfl) ?_
    exact (pCoreOf_le 2 _).trans (sup_le Subgroup.le_normalizer (hTMc.trans hKn))
  rcases h12'.cases with h | hii | hiii | hHe
  · exact absurd h hne
  · exact hsingle hii.1
  · obtain ⟨L, t, hmax, hL, ht, -, hKc, hcomm, -⟩ := hiii
    have hloc := hmax.1
    set K := conjClosure (oTwoUpper H) Mc with hKdef
    have hLMc : L ≤ Mc := le_of_mem_cComp hL
    have htMc : t ∈ Mc := hTMc ht
    have hLtle : conjSub t L ≤ L ⊔ T := by
      rintro _ ⟨l, hl, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact (L ⊔ T).mul_mem ((L ⊔ T).mul_mem (Subgroup.mem_sup_right ht) (Subgroup.mem_sup_left hl))
        ((L ⊔ T).inv_mem (Subgroup.mem_sup_right ht))
    have hLtMc : conjSub t L ≤ Mc := by
      rintro _ ⟨l, hl, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact Mc.mul_mem (Mc.mul_mem htMc (hLMc hl)) (Mc.inv_mem htMc)
    have hKT : K ⊔ T = L ⊔ T := by
      rw [hKc]
      exact le_antisymm (sup_le (sup_le le_sup_left hLtle) le_sup_right)
        (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
    have hKMc : K ≤ Mc := by rw [hKc]; exact sup_le hLMc hLtMc
    have hKH : K ≤ L ⊔ T := le_sup_left.trans hKT.le
    have hQ2 : IsPGroup 2 (pCoreOf 2 (L ⊔ T)) := pCoreOf_isPGroup 2 _
    have hSyl : IsSylowTwoOf T (L ⊔ T) := ⟨le_sup_right, hloc.1, hloc.2.2.1⟩
    have hQT : pCoreOf 2 (L ⊔ T) ≤ T := B6.pCoreOf_two_le_of_isSylowTwoOf hSyl
    have hQn : L ⊔ T ≤ Subgroup.normalizer (pCoreOf 2 (L ⊔ T) : Set G) :=
      le_normalizer_pCoreOf 2 _
    have hLQ : ∀ q ∈ pCoreOf 2 (L ⊔ T), q ∈ Subgroup.normalizer (L : Set G) := by
      intro q hq
      refine mem_normalizer_of_case_iii hL htMc hKc hKn hcomm (hTMc (hQT hq)) fun l hl => ?_
      have hlQ : l * q⁻¹ * l⁻¹ ∈ pCoreOf 2 (L ⊔ T) :=
        (Subgroup.mem_normalizer_iff.mp (hQn (Subgroup.mem_sup_left hl)) q⁻¹).mp
          ((pCoreOf 2 _).inv_mem hq)
      have e : q * l * q⁻¹ * l⁻¹ = q * (l * q⁻¹ * l⁻¹) := by group
      have h1 : q * l * q⁻¹ * l⁻¹ ∈ pCoreOf 2 (L ⊔ T) := by
        rw [e]
        exact (pCoreOf 2 _).mul_mem hq hlQ
      have hlK : l ∈ K := by rw [hKc]; exact Subgroup.mem_sup_left hl
      have hqK : q * l * q⁻¹ ∈ K :=
        (Subgroup.mem_normalizer_iff.mp (hKn (hTMc (hQT hq))) l).mp hlK
      have h2 : q * l * q⁻¹ * l⁻¹ ∈ K := K.mul_mem hqK (K.inv_mem hlK)
      have hinf : pCoreOf 2 (L ⊔ T) ⊓ K ≤ pCoreOf 2 K :=
        le_pCoreOf_of_le_normalizer 2 inf_le_right
          (le_normalizer_inf_of_both (hKH.trans hQn) Subgroup.le_normalizer) (hQ2.to_inf_left)
      have hKnorm : (K.subgroupOf Mc).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hKMc).mpr hKn
      exact CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 K Mc hKMc
        hKnorm (hinf ⟨h1, h2⟩)
    have hLc : L ≤ Subgroup.centralizer ((⁅V154 T Mc M, B⁆ : Subgroup G) : Set G) :=
      le_centralizer_of_not_faithful hs.qtfe hloc hZT hZe (hO' L hKT.symm) hLQ
    rw [hKc]
    refine sup_le hLc ?_
    rintro _ ⟨l, hl, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have h0 := (Subgroup.mem_normalizer_iff.mp (hZn (T.inv_mem ht)) z).mp hz
    have hz' : t⁻¹ * z * t ∈ ⁅V154 T Mc M, B⁆ := by simpa using h0
    have hc := Subgroup.mem_centralizer_iff.mp (hLc hl) _ hz'
    calc z * (t * l * t⁻¹) = t * ((t⁻¹ * z * t) * l) * t⁻¹ := by group
      _ = t * (l * (t⁻¹ * z * t)) * t⁻¹ := by rw [hc]
      _ = t * l * t⁻¹ * z := by group
  · exact hsingle hHe.1

end S15223

end CFSG.Quasithin
