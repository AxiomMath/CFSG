module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P2Ctx
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S152He12E

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace S15223

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem ctx15223_of_F4 (h5 : StageLemma15205_F4) (h159 : StageLemma1519)
    (h11 : StageLemma15211_F4) (h12 : He12.StageLemma15212W_F4) (h13 : StageLemma15213_F4)
    (h14 : StageLemma15214_F4) (hN : StageNotation15209_F4) (h16 : StageLemma15216_F4)
    (h17 : StageLemma15217_F4) (h18 : StageLemma15218_F4) {T Mc M H : Subgroup G}
    (hs : Setting152 T Mc M) (hH : IsHStar T M H) {B₀ : Subgroup (MulAut (V154 T Mc M))}
    (hB₀ : IsB0 T Mc M B₀) {I : Subgroup G} (hI : Hyp15215.Min T Mc M B₀ I) :
    Ctx15223 T Mc M H B₀ I := by
  classical
  have hD : Inputs152 T Mc M H B₀ I :=
    ⟨h5 G T Mc M hs, h159 G T Mc M hs.qtfe hs.mf hs.ce, h13 G T Mc M hs H hH,
      h14 G T Mc M hs B₀ hB₀, h11 G T Mc M hs H hH, hN G T Mc M hs H hH,
      h16 G T Mc M hs H hH B₀ hB₀ I hI.1, h17 G T Mc M hs B₀ hB₀ I hI.1⟩
  have hsyl : IsSylowTwoOf (sOf152 T Mc M B₀) I := (h18 G T Mc M hs H hH B₀ hB₀ I hI.1).sylow
  have hKI : oTwoUpper H ≤ I := (le_sup_left.trans hD.h16.KS_le).trans inf_le_right
  obtain ⟨B, hB⟩ := hD.hN.sigmaPrime_nonempty
  have hZ := commutator_eq_zSOf hD.h13 hB₀ hB
  have hKZ' : oTwoUpper H ≤ Subgroup.centralizer (zSOf T Mc M B₀ : Set G) := by
    have := (hD.h11 B hB).centralizes
    rwa [hZ] at this
  have hKZ : ∀ k ∈ oTwoUpper H, ∀ z ∈ zSOf T Mc M B₀, k * z = z * k := fun k hk z hz =>
    (Subgroup.mem_centralizer_iff.mp (hKZ' hk) z hz).symm
  have hzS := hD.h14.zS_eq
  have hZS : ∀ z ∈ zSOf T Mc M B₀,
      z ∈ sOf152 T Mc M B₀ ∧ z ^ 2 = 1 ∧ ∀ s ∈ sOf152 T Mc M B₀, z * s = s * z := fun z hz => by
    have hz' : z ∈ omegaOneCenterOf (sOf152 T Mc M B₀) := hzS ▸ hz
    exact ⟨omegaOneCenterOf_le _ hz', sq_eq_one_of_mem_omegaOneCenterOf hz',
      fun s hs => (mem_centralizer_of_mem_omegaOneCenterOf hz' hs).symm⟩
  have hZmax : ∀ w ∈ sOf152 T Mc M B₀, w ^ 2 = 1 → (∀ s ∈ sOf152 T Mc M B₀, w * s = s * w) →
      w ∈ zSOf T Mc M B₀ := fun w hw hw2 hwc =>
    hzS ▸ mem_omegaOneCenterOf hw (fun y hy => (hwc y hy).symm) hw2
  have hC : Subgroup.centralizer (zSOf T Mc M B₀ : Set G) ≤ Mc :=
    (Subgroup.centralizer_le hD.h14.le_zS).trans hD.h14.mc_eq.ge
  have hMc : ∀ g : G, (∀ z ∈ zSOf T Mc M B₀, g * z = z * g) → g ∈ Mc := fun g hg =>
    hC (Subgroup.mem_centralizer_iff.mpr fun z hz => (hg z hz).symm)
  have hsq : IsSQTKIn I := by
    have := hs.qtfe.simple
    exact sqtkGroup_of_pCoreOf_ne_bot hs.qtfe.qtke hs.qtfe.simple hs.qtfe.nonabelian
      hI.1.inH.2
  have hrank : CFSG.Open.pRank 3 (⊤ : Subgroup ↥I) ≤ 2 :=
    sqt_iff.mp hsq.1 3 Nat.prime_three (by norm_num)
  have hT9 : T.relIndex H = 9 := by
    have h := hD.hN.card_conj
    rw [← hD.hN.eq_normalizer, ← hD.hN.eq_inf] at h
    exact h
  obtain ⟨P, hPK, hPS, hP9⟩ := exists_sylow_three_oTwoUpper hH.1.1 hs.qtfe.sylow.1 hT9
  have hXi : IsXi T (oTwoUpper H) := (h12 G T Mc M hs H hH B hB).xi
  exact ⟨hD, hsyl, hKI, hKZ, hZS, hZmax, hMc, hsq, hrank,
    ⟨P, hPK, isElemAbelian_of_isXi_sylow hXi hPS hP9, hP9, hPS⟩,
    isSolvable_of_isXi_sylow hXi hPS hP9⟩

end S15223

end CFSG.Quasithin
