module

import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.Covered
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.F5Baum
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239ListedBasic
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.GlaubermanNiles
public import CFSG.LocalAnalysis.RankThreeUC.TheoremDThreeConstrained
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Monster.B.TwoA.Base.ElemAut
import CFSG.RankThree.PartTwo.Sec3.TwoThreeStructure

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.AGLEmbeddingD2 CFSG.AGLEmbedding
open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound CFSG.AGLEmbeddingD2.Tits.MsidePrelim
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbeddingD2.GN
open scoped Pointwise

variable {X : Type} [Group X] [Finite X] {T T₁ T₂ : Subgroup X}

private theorem charTwo_sup_of_normal (hX : GNSetting X T) (K : Subgroup X) : CharTwo (K ⊔ T) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQT : pCoreOf 2 (⊤ : Subgroup X) ≤ T := B6.pCoreOf_two_le_of_isSylowTwoOf hX.sylow
  have hQnormal : (pCoreOf 2 (⊤ : Subgroup X)).Normal := by
    rw [B6.pCoreOf_top]; infer_instance
  have hQn : (K ⊔ T) ≤ Subgroup.normalizer ((pCoreOf 2 (⊤ : Subgroup X) : Subgroup X) : Set X) :=
    fun g _ => (Subgroup.normalizer_eq_top_iff.mpr hQnormal).symm ▸ Subgroup.mem_top g
  have hQM : pCoreOf 2 (⊤ : Subgroup X) ≤ pCoreOf 2 (K ⊔ T) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hQT.trans le_sup_right) hQn
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  intro x hx
  exact hQM (hX.charTwo ⟨Subgroup.mem_top x, Subgroup.centralizer_le hQM hx.2⟩)

private theorem isSubnormal_inf_normal {A B N : Subgroup X} (h : IsSubnormal A B) (hNB : N ≤ B)
    (hN : (N.subgroupOf B).Normal) : IsSubnormal (A ⊓ N) N := by
  induction h with
  | refl A =>
    rw [inf_eq_right.mpr hNB]
    exact IsSubnormal.refl _
  | step hAM hn _ ih =>
    refine IsSubnormal.step (inf_le_inf_right N hAM) ?_ (ih hNB hN)
    rw [Subgroup.normal_subgroupOf_iff hAM] at hn
    rw [Subgroup.normal_subgroupOf_iff (inf_le_inf_right N hAM)]
    intro x g hx hg
    exact ⟨hn x g hx.1 hg.1, N.mul_mem (N.mul_mem hg.2 hx.2) (N.inv_mem hg.2)⟩

private theorem isSubnormal_top_of_le {K Y : Subgroup X} (hK : K.Normal)
    (hY : IsSubnormal Y (K ⊔ T)) (hYK : Y ≤ K) : IsSubnormal Y ⊤ := by
  have h1 : IsSubnormal (Y ⊓ K) K := isSubnormal_inf_normal hY le_sup_left (hK.subgroupOf _)
  rw [inf_eq_left.2 hYK] at h1
  exact h1.trans (IsSubnormal.step le_top (hK.subgroupOf _) (IsSubnormal.refl _))

private theorem s3Factor_covered_rel (hX : GNSetting X T) (hP : IsC118Pair T T₁ T₂)
    {K : Subgroup X} (hK : K.Normal)
    (hU : IsElemAbelian 2 (conjClosure (quasithinOmegaOneCenter T) (K ⊔ T)))
    (I : Finset (Subgroup (MulAut (IntMod (conjClosure (quasithinOmegaOneCenter T) (K ⊔ T)) hU))))
    (hMN : K ⊔ T ≤ Subgroup.normalizer
      ((conjClosure (quasithinOmegaOneCenter T) (K ⊔ T) : Subgroup X) : Set X))
    (hcard : ∀ L ∈ I, Nat.card L = 6)
    (hJM : autI hU (thompsonJ (K ⊔ T)) = ⨆ L ∈ I, L)
    (hSyl : IsSylowTwoOf (autI hU (thompsonJ T)) (autI hU (thompsonJ (K ⊔ T))))
    (hperm : ∀ g ∈ autI hU (K ⊔ T), ∀ L ∈ I, B1.conjAut g L ∈ I) (hfam : S3Family I) :
    ∀ L ∈ I, ∃ H₀ : Subgroup X, H₀ ≤ K ⊔ T ∧ L ≤ autI hU H₀ ∧
      (H₀ ≤ Subgroup.centralizer (T₁ : Set X) ∨ H₀ ≤ Subgroup.normalizer (T₂ : Set X)) := by
  intro L hL
  have hSylM : IsSylowTwoOf T (K ⊔ T) := B6.isSylowTwoOf_mono hX.sylow le_sup_right le_top
  obtain ⟨H₀, hHM, hHL, -, hGcl, hblock⟩ := ffGroupStepGen (charTwo_sup_of_normal hX K) hSylM hU I
    hMN hcard hJM hSyl hperm hfam L hL
  refine ⟨H₀, hHM, hHL, ?_⟩
  obtain ⟨-, h1Z, -, -, h2B, -, hall⟩ := hP
  have hC₁B : T₁ ≤ baum T := h1Z.trans (C1GN.omegaOneCenterOf_le_baum T)
  have hd := hall X H₀ (baum T).subtype (baum T).subtype_injective
    (by rwa [Subgroup.range_subtype])
  rw [Subgroup.map_subgroupOf_eq_of_le hC₁B, Subgroup.map_subgroupOf_eq_of_le h2B] at hd
  rcases hd with h | h | h
  · left
    intro x hx
    exact Subgroup.mem_centralizer_iff.2 fun c hc =>
      ((Subgroup.mem_centralizer_iff.1 (h hc).2 x hx)).symm
  · exact Or.inr h
  · exfalso
    obtain ⟨Y, hYM, hYs, hYX⟩ := hblock h
    have hYK : Y ≤ K := CFSG.QuasithinUnique.Vol2Native.L239.le_of_isShort2_of_le_sup hX.sylow.2.1
      (Subgroup.normalizer_eq_top_iff.mpr hK ▸ le_top) hYX.1 hYM
    exact hX.noXBlock Y (isSubnormal_top_of_le hK hYs hYK) hYX

private theorem normalizer_thompsonJ_inf_mul (hX : GNSetting X T) {M : Subgroup X} (hTM : T ≤ M)
    (h1 : T₁ ≤ omegaOneCenterOf T) (h2 : T₂ ≤ baum T)
    (h2c : (T₂.subgroupOf (baum T)).Characteristic) {x : X}
    (hx : x ∈ M ⊓ Subgroup.normalizer (thompsonJ T : Set X)) :
    ∃ k ∈ Subgroup.centralizer (T₁ : Set X) ⊓ M, ∃ n ∈ Subgroup.normalizer (T₂ : Set X) ⊓ M,
      x = k * n := by
  set J : Subgroup X := thompsonJ T
  set E : Subgroup X := omegaOneCenterOf J
  set N : Subgroup X := M ⊓ Subgroup.normalizer (J : Set X)
  set K : Subgroup X := N ⊓ Subgroup.centralizer (E : Set X)
  have hTN : T ≤ N :=
    le_inf hTM (Subgroup.le_normalizer.trans (normalizer_le_normalizer_thompsonJ T))
  have hNE : N ≤ Subgroup.normalizer (E : Set X) :=
    inf_le_right.trans (normalizer_le_normalizer_of_map_mulEquiv omegaOneCenterOf_map_mulEquiv J)
  have hNK : N ≤ Subgroup.normalizer (K : Set X) := fun n hn =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hn,
      CFSG.GorensteinWalter.normalizer_le_normalizer_centralizer_subgroup E (hNE hn)⟩
  have hKN : K ≤ N := inf_le_left
  have hTsyl : IsSylowTwoOf T N := B6.isSylowTwoOf_mono hX.sylow hTN le_top
  have hKsyl : IsSylowTwoOf (T ⊓ K) K := B6.isSylowTwoOf_inf_normal hTsyl hKN hNK
  have hTK : T ⊓ K = baum T := by
    ext y
    simp only [Subgroup.mem_inf, K, baum, E, J]
    constructor
    · rintro ⟨hyT, -, hyc⟩
      exact ⟨hyT, hyc⟩
    · rintro ⟨hyT, hyc⟩
      exact ⟨hyT, hTN hyT, hyc⟩
  have hfr := B6.frattini_two hKN hNK hKsyl
  have hxs : x ∈ K ⊔ (N ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup X) : Set X)) := hfr hx
  have hle : N ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup X) : Set X) ≤
      Subgroup.normalizer (K : Set X) := fun n hn => hNK hn.1
  have hmem : x ∈ ((K ⊔ (N ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup X) : Set X)) :
      Subgroup X) : Set X) := hxs
  rw [Subgroup.coe_mul_of_right_le_normalizer_left K _ hle] at hmem
  obtain ⟨k, hk, n, hn, rfl⟩ := hmem
  refine ⟨k, ⟨Subgroup.centralizer_le
      (h1.trans (omegaOneCenterOf_le_omegaOneCenterOf_thompsonJ T)) hk.2, hk.1.1⟩, n, ⟨?_, hn.1.1⟩,
    rfl⟩
  rw [hTK] at hn
  exact normalizer_le_normalizer_of_characteristic_subgroupOf h2 h2c
    (Subgroup.mem_normalizer_iff.mpr (fun z => by
      simpa using (Subgroup.mem_normalizer_iff.mp hn.2 z)))

theorem factor_of_threeConstrained_rel (hI59 : AGL81I59) (hX : GNSetting X T)
    (hP : IsC118Pair T T₁ T₂) {K : Subgroup X} (hK : K.Normal)
    (hcon : CFSG.ABGLocalTools.IsPConstrained 3
      ↥(autOn (K ⊔ T) (conjClosure (quasithinOmegaOneCenter T) (K ⊔ T)))) :
    ∀ x ∈ K ⊔ T, ∃ a ∈ Subgroup.centralizer (T₁ : Set X) ⊓ (K ⊔ T),
      ∃ b ∈ Subgroup.normalizer (T₂ : Set X) ⊓ (K ⊔ T), x = a * b := by
  obtain ⟨-, h1Z, -, -, h2B, h2c, -⟩ := id hP
  have hTM : T ≤ K ⊔ T := le_sup_right
  have hSylM : IsSylowTwoOf T (K ⊔ T) := B6.isSylowTwoOf_mono hX.sylow hTM le_top
  have hFM : CharTwo (K ⊔ T) := charTwo_sup_of_normal hX K
  have hZV : quasithinOmegaOneCenter T ≤ conjClosure (quasithinOmegaOneCenter T) (K ⊔ T) :=
    le_conjClosure _ _
  have hT1V : T₁ ≤ conjClosure (quasithinOmegaOneCenter T) (K ⊔ T) :=
    fun z hz => hZV (h1Z hz)
  obtain ⟨hU, h | h⟩ := B2_15 (H := K ⊔ T) (T := T) hFM hSylM
  ·
    obtain ⟨hJ, -, -⟩ := h
    have hFC := hI59 X (K ⊔ T) T _
      (CFSG.Open.IsKGroup.subgroup (CFSG.KCore.KGroupAllSimple.kGroupNonab hX.kGroup) _)
      hFM hSylM rfl hcon hJ
    obtain ⟨hU', hMN, I, -, hcard, hJM, hSyl, hperm, hfam⟩ :=
      exists_family_of_ffConclusion hSylM hJ hFC
    have hcov := s3Factor_covered_rel hX hP hK hU' I hMN hcard hJM hSyl hperm hfam
    have hcov' : ∀ L ∈ I, L ≤ autI hU' (Subgroup.centralizer (T₁ : Set X) ⊓ (K ⊔ T)) ∨
        L ≤ autI hU' (Subgroup.normalizer (T₂ : Set X) ⊓ (K ⊔ T)) := by
      intro L hL
      obtain ⟨H₀, hHM, hLH, hH⟩ := hcov L hL
      rcases hH with h' | h'
      · exact Or.inl (hLH.trans (autI_mono hU' (le_inf h' hHM)))
      · exact Or.inr (hLH.trans (autI_mono hU' (le_inf h' hHM)))
    have hVT : conjClosure (quasithinOmegaOneCenter T) (K ⊔ T) ≤ T := by
      obtain ⟨hle, -, -⟩ := conjClosure_isTwoReducedIn_of_charTwo hSylM hFM (le_refl _)
      exact hle.trans (inf_le_left.trans (B6.pCoreOf_two_le_of_isSylowTwoOf hSylM))
    have hBS := autI_baum_le_autI_thompsonJ hMN hSylM hVT hfam hJM
      (thompsonJ_le_thompsonJ_of_isSylowTwoOf hSylM) hperm
    have hSylB : IsSylowTwoOf (autI hU' (baum T)) (autI hU' (thompsonJ (K ⊔ T))) :=
      isSylowTwoOf_of_le_of_le hSyl (autI_mono hU' (thompsonJ_le_baum T)) hBS
        (isPGroup_autI hU' (hX.sylow.2.1.to_le (C1GN.baum_le T)))
    intro x hx
    obtain ⟨c, hc, a, ha, b, hb, n, hn, rfl⟩ := exists_factor_of_covering hMN hSylM
      (C1GN.baum_le T) (Subgroup.le_normalizer.trans (normalizer_le_normalizer_baum T))
      (normalizer_inf_sup_le_normalizer_baum T _) hfam hSylB hJM
      (KA := Subgroup.centralizer (T₁ : Set X) ⊓ (K ⊔ T))
      (KB := Subgroup.normalizer (T₂ : Set X) ⊓ (K ⊔ T)) inf_le_right inf_le_right hcov' x hx
    refine ⟨c * a, ⟨mul_mem (Subgroup.centralizer_le hT1V hc.1) ha.1, mul_mem hc.2 ha.2⟩, b * n,
      ⟨mul_mem hb.1 ?_, mul_mem hb.2 hn.1⟩, by group⟩
    exact normalizer_le_normalizer_of_characteristic_subgroupOf h2B h2c hn.2
  ·
    obtain ⟨-, hfac⟩ := h
    intro x hx
    obtain ⟨c, hc, n, hn, rfl⟩ := hfac x hx
    obtain ⟨a', ha', b', hb', hnab⟩ := normalizer_thompsonJ_inf_mul hX hTM h1Z h2B h2c hn
    have hcC : c ∈ Subgroup.centralizer (T₁ : Set X) :=
      Subgroup.mem_centralizer_iff.mpr fun z hz =>
        Subgroup.mem_centralizer_iff.mp hc.2 z (h1Z hz)
    exact ⟨c * a', ⟨mul_mem hcC ha'.1, mul_mem hc.1 ha'.2⟩, b', hb', by rw [hnab, mul_assoc]⟩

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15
