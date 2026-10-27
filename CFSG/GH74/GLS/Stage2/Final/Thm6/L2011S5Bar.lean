module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2011S5Diag
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2012CBar
public import CFSG.GH74.GLS.Stage2.Local.P34Bar
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der75Main

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L2011

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Final.Thm6.L2012 CFSG.GH74.GLS.Stage2.Final.Thm6.SL2Bound
  CFSG.GH74.GLS.Stage2.Final.Thm6.L208g2 CFSG.GH74.GLS.Stage1.Thm6.Prod CFSG.GH74.GLS.Stage2.Bender.Thm1

section Pair

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} {q : ℕ}
  {L₁ L₂ : Subgroup (CentralizerBar z)}

theorem prodSL2_of_pair (hP : Stage1Pair G z S q L₁ L₂) :
    ∃ (F₁ F₂ : Type) (_ : Field F₁) (_ : Field F₂) (_ : Finite F₁) (_ : Finite F₂),
      Nat.card F₁ = q ∧ Nat.card F₂ = q ∧ IVK.ProdSL2 (CentralizerBar z) L₁ L₂ F₁ F₂ := by
  obtain ⟨F₁, iF₁, fF₁, hF₁q, ⟨e₁⟩⟩ := hP.sl₁
  obtain ⟨F₂, iF₂, fF₂, hF₂q, ⟨e₂⟩⟩ := hP.sl₂
  have hnormal : (L₁ ⊔ L₂).Normal := by
    rw [hP.prod.1]
    exact Stage1.Thm6.Prod.LBar_isNormal z
  have hcent : centralizer ((L₁ ⊔ L₂ : Subgroup (CentralizerBar z)) : Set (CentralizerBar z)) ≤
      L₁ ⊔ L₂ := by
    rw [hP.prod.1, ← hP.fitting]
    exact CFSG.centralizer_generalizedFitting_le _
  exact ⟨F₁, F₂, iF₁, iF₂, fF₁, fF₂, hF₁q, hF₂q,
    ⟨hP.prod.2.1, ⟨e₁⟩, ⟨e₂⟩, hP.prod.2.2, hnormal, hcent⟩⟩

theorem zbar_mem_inf (hP : Stage1Pair G z S q L₁ L₂) (hz : orderOf z = 2) :
    toBar z ⟨z, mem_Cen_self z⟩ ∈ L₁ ⊓ L₂ := by
  have hzL : z ∈ LC z := z_mem_LC_of_pair hP hz
  have hb : toBar z ⟨z, mem_Cen_self z⟩ ∈ LBar z :=
    ⟨⟨z, mem_Cen_self z⟩, Subgroup.mem_subgroupOf.mpr hzL, rfl⟩
  rw [← hP.prod.1] at hb
  have hcom : ∀ c : CentralizerBar z, c * toBar z ⟨z, mem_Cen_self z⟩ = toBar z ⟨z, mem_Cen_self z⟩ * c :=
    Subgroup.mem_center_iff.mp (toBar_z_mem_center z)
  have p₁ := pair₁_of_stage1 hP
  have p₂ := pair₂_of_stage1 hP
  have h2 : toBar z ⟨z, mem_Cen_self z⟩ ∈ L₂ := p₁.mem_of_cen hb (fun c _ => (hcom c).symm)
  have h1 : toBar z ⟨z, mem_Cen_self z⟩ ∈ L₁ :=
    p₂.mem_of_cen (by rwa [sup_comm] at hb) (fun c _ => (hcom c).symm)
  exact ⟨h1, h2⟩


theorem exists_sylow_barOf {k : Kind} (hctx : Stage2Ctx G z k S) :
    ∃ T : Sylow 2 (CentralizerBar z), (T : Subgroup (CentralizerBar z)) = barOf z S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS := isSylowOf_barOf hctx.sylow
  rw [CFSG.ABGLocalTools.isSylowOf_iff] at hS
  obtain ⟨-, hp, hdvd⟩ := hS
  rw [Subgroup.relIndex_top_right] at hdvd
  exact ⟨hp.toSylow hdvd, rfl⟩

theorem frattini_bar (h31a : IVK.IVK_3_1a) (h31c : IVK.IVK_3_1c) (h31g : IVK.Proofs2.IVK_3_1g_fixed)
    {k : Kind} (hctx : Stage2Ctx G z k S) (hP : Stage1Pair G z S q L₁ L₂)
    (hdiag : ∀ u : G, ∀ hu : u ∈ Cen z, u ∈ S → orderOf u = 2 →
      toBar z ⟨u, hu⟩ ∈ normalizer (L₁ : Set (CentralizerBar z)) →
      toBar z ⟨u, hu⟩ ∈ normalizer (L₂ : Set (CentralizerBar z)) → u ∉ LC z →
        PGLOver L₁ (zpowers (toBar z ⟨u, hu⟩)) q ∧ PGLOver L₂ (zpowers (toBar z ⟨u, hu⟩)) q)
    {t : G} (htS : t ∈ S) (htC : t ∈ Cen z) (ht2 : orderOf t = 2)
    (htN : toBar z ⟨t, htC⟩ ∈ normalizer (L₁ : Set (CentralizerBar z))) :
    ∀ c : CentralizerBar z, ∃ l ∈ L₁ ⊔ L₂, ∃ σ ∈ barOf z S,
      ∃ d ∈ centralizer ({toBar z ⟨t, htC⟩} : Set (CentralizerBar z)), c = l * σ * d := by
  obtain ⟨F₁, F₂, iF₁, iF₂, fF₁, fF₂, hF₁q, hF₂q, hPr⟩ := prodSL2_of_pair hP
  have hz2 := hctx.orderOf_z
  obtain ⟨T, hT⟩ := exists_sylow_barOf hctx
  have htb2 : orderOf (toBar z ⟨t, htC⟩) = 2 :=
    P34.orderOf_mk_eq_two (Cen z) ((Subgroup.orderOf_coe (⟨t, htC⟩ : ↥(Cen z))).symm.trans ht2)
  have hzb2 : orderOf (toBar z ⟨z, mem_Cen_self z⟩) = 2 :=
    P34.orderOf_mk_eq_two (Cen z) ((Subgroup.orderOf_coe (⟨z, mem_Cen_self z⟩ : ↥(Cen z))).symm.trans hz2)
  have hζK := zbar_mem_inf hP hz2
  have hζ1 : toBar z ⟨z, mem_Cen_self z⟩ ≠ 1 := by
    intro h; rw [h, orderOf_one] at hzb2; omega
  have hζc : ∀ c : CentralizerBar z, c * toBar z ⟨z, mem_Cen_self z⟩ = toBar z ⟨z, mem_Cen_self z⟩ * c :=
    Subgroup.mem_center_iff.mp (toBar_z_mem_center z)
  have hF₁3 : 3 < Nat.card F₁ := by rw [hF₁q]; exact hP.gt3
  have hF₂3 : 3 < Nat.card F₂ := by rw [hF₂q]; exact hP.gt3
  have hNT : normalizer (L₁ : Set (CentralizerBar z)) ⊔ (T : Subgroup (CentralizerBar z)) = ⊤ := by
    rw [hT]; exact nrm_sup_barS hP
  have htT : toBar z ⟨t, htC⟩ ∈ (T : Subgroup (CentralizerBar z)) := by
    rw [hT]; exact bar_mem_barOf_iff.2 ⟨t, htC, htS, rfl⟩
  have hww : toBar z ⟨t, htC⟩ * toBar z ⟨t, htC⟩ = 1 := by
    have := pow_orderOf_eq_one (toBar z ⟨t, htC⟩)
    rwa [htb2, sq] at this
  have core : ∀ c : CentralizerBar z, ∃ l ∈ L₁ ⊔ L₂, ∃ d ∈ centralizer ({toBar z ⟨t, htC⟩} : Set (CentralizerBar z)),
      ∃ σ ∈ (T : Subgroup (CentralizerBar z)), c = l * d * σ := by
    by_cases hK : toBar z ⟨t, htC⟩ ∈ L₁ ⊔ L₂
    · by_cases hζ : toBar z ⟨t, htC⟩ = toBar z ⟨z, mem_Cen_self z⟩
      · intro c
        refine ⟨1, Subgroup.one_mem _, c, ?_, 1, Subgroup.one_mem _, by simp⟩
        rw [Subgroup.mem_centralizer_singleton_iff, hζ]
        exact hζc c
      · exact frattini_generic hPr hF₁3 hF₂3 h31a h31c h31g T (nrm_normal hP) hNT hζK hζ1 hζc htT htb2
          (Or.inl ⟨hK, hζ⟩)
    · have hLC : t ∉ LC z := by
        intro hLC
        apply hK
        rw [hP.prod.1]
        exact bar_mem_barOf_iff.2 ⟨t, htC, hLC, rfl⟩
      obtain ⟨hp₁, hp₂⟩ := hdiag t htC htS ht2 htN (nrm_normalizes₂ hP htN) hLC
      have hD := isDiagInv_of_pgl hPr hF₁q hF₂q hww htN (nrm_normalizes₂ hP htN) hK hp₁ hp₂
      exact frattini_generic hPr hF₁3 hF₂3 h31a h31c h31g T (nrm_normal hP) hNT hζK hζ1 hζc htT htb2
        (Or.inr hD)
  intro c
  obtain ⟨l₁, hl₁, d₁, hd₁, σ₁, hσ₁, hc⟩ := core c⁻¹
  have hKn : (L₁ ⊔ L₂).Normal := hPr.fstar_normal
  have hl₂ : d₁⁻¹ * l₁⁻¹ * d₁ ∈ L₁ ⊔ L₂ := by
    have := hKn.conj_mem _ ((L₁ ⊔ L₂).inv_mem hl₁) d₁⁻¹
    simpa using this
  have hl₃ : σ₁⁻¹ * (d₁⁻¹ * l₁⁻¹ * d₁) * σ₁ ∈ L₁ ⊔ L₂ := by
    have := hKn.conj_mem _ hl₂ σ₁⁻¹
    simpa using this
  have hd₂ : d₁⁻¹ ∈ centralizer ({toBar z ⟨t, htC⟩} : Set (CentralizerBar z)) :=
    (centralizer ({toBar z ⟨t, htC⟩} : Set (CentralizerBar z))).inv_mem hd₁
  refine ⟨_, hl₃, σ₁⁻¹, ?_, d₁⁻¹, hd₂, ?_⟩
  · rw [← hT]; exact (T : Subgroup (CentralizerBar z)).inv_mem hσ₁
  · have : c = (c⁻¹)⁻¹ := (inv_inv c).symm
    rw [this, hc]
    group


theorem mem_S1_of_normalizes (hP : Stage1Pair G z S q L₁ L₂) {u : G} (hu : u ∈ S) (huC : u ∈ Cen z)
    (hn₁ : toBar z ⟨u, huC⟩ ∈ normalizer (L₁ : Set (CentralizerBar z)))
    (hn₂ : toBar z ⟨u, huC⟩ ∈ normalizer (L₂ : Set (CentralizerBar z))) : u ∈ S1 S z :=
  bar_mem_S1_iff.2 ⟨hu, huC, fun _ hK _ => bar_mem_normalizer_comp hP.comps hn₁ hn₂ hK⟩

theorem pgl_pair_of_l4 {ε : Bool} (hSC : S ≤ Cen z) (h4 : Stage1L4 G z S ε q L₁ L₂) :
    ∀ u : G, ∀ hu : u ∈ Cen z, u ∈ S → orderOf u = 2 →
      toBar z ⟨u, hu⟩ ∈ normalizer (L₁ : Set (CentralizerBar z)) →
      toBar z ⟨u, hu⟩ ∈ normalizer (L₂ : Set (CentralizerBar z)) → u ∉ LC z →
        PGLOver L₁ (zpowers (toBar z ⟨u, hu⟩)) q ∧ PGLOver L₂ (zpowers (toBar z ⟨u, hu⟩)) q := by
  intro u huC hu hord hn₁ hn₂ hLC
  have hP := h4.pair
  have hu2 : u * u = 1 := by
    have := pow_orderOf_eq_one u
    rwa [hord, sq] at this
  have hS1 := mem_S1_of_normalizes hP hu huC hn₁ hn₂
  have hbarS1 : toBar z ⟨u, huC⟩ ∈ SBar (S1 S z) z := bar_mem_barOf_iff.2 ⟨u, huC, hS1, rfl⟩
  have hu2b : toBar z ⟨u, huC⟩ * toBar z ⟨u, huC⟩ = 1 := by
    rw [← map_mul, show (⟨u, huC⟩ : ↥(Cen z)) * ⟨u, huC⟩ = 1 from Subtype.ext hu2, map_one]
  refine ⟨?_, ?_⟩
  · have hnin : toBar z ⟨u, huC⟩ ∉ L₁ ⊔ centralizer (L₁ : Set (CentralizerBar z)) := fun hin =>
      hLC (inner_mem_LC_bar hSC hP.ne hP.prod hP.comps hP.sl₁ h4.pgl.1 hP.swap h4.index_le hu huC hn₁ hin)
    exact pgl_of_nrm hP.odd hP.sl₁ h4.pgl.1 hbarS1 hu2b hn₁ hnin
  · have hcomps₂ : {K : Subgroup (CentralizerBar z) | IsComponent K} = {L₂, L₁} := by
      rw [hP.comps]; exact Set.pair_comm _ _
    have hswap₂ : ∃ s ∈ S, Swaps z s L₂ L₁ := by
      obtain ⟨s, hs, hsC, h1, h2⟩ := hP.swap
      exact ⟨s, hs, hsC, h2, h1⟩
    have hnin : toBar z ⟨u, huC⟩ ∉ L₂ ⊔ centralizer (L₂ : Set (CentralizerBar z)) := fun hin =>
      hLC (inner_mem_LC_bar hSC hP.ne.symm (bar_isCentralProd_symm hP.prod) hcomps₂ hP.sl₂ h4.pgl.2
        hswap₂ h4.index_le hu huC hn₂ hin)
    exact pgl_of_nrm hP.odd hP.sl₂ h4.pgl.2 hbarS1 hu2b hn₂ hnin

theorem S1_le_LC_of_psp4 (hSC : S ≤ Cen z) (hP : Stage1PSp4 G z S q L₁ L₂) : S1 S z ≤ LC z := by
  have hRS1 : RC S z ≤ S1 S z := rc_le_S1 hSC hP.pair
  have e2 := Subgroup.relIndex_mul_relIndex (RC S z) (S1 S z) S hRS1 bar_S1_le_S
  rw [hP.index] at e2
  have h0 : (S1 S z).relIndex S ≠ 0 := bar_relIndex_ne_zero _ _
  have h1 : (S1 S z).relIndex S ≠ 1 := fun h => not_S_le_S1 hP.pair (Subgroup.relIndex_eq_one.1 h)
  have h3 : (RC S z).relIndex (S1 S z) = 1 := by
    by_contra hne
    have ha : 2 ≤ (RC S z).relIndex (S1 S z) := by
      have : (RC S z).relIndex (S1 S z) ≠ 0 := bar_relIndex_ne_zero _ _
      omega
    have hb : 2 ≤ (S1 S z).relIndex S := by omega
    have := Nat.mul_le_mul ha hb
    omega
  intro s hs
  exact ((Subgroup.relIndex_eq_one.1 h3 hs : s ∈ RC S z)).2

theorem pgl_pair_of_psp4 (hSC : S ≤ Cen z) (hP : Stage1PSp4 G z S q L₁ L₂) :
    ∀ u : G, ∀ hu : u ∈ Cen z, u ∈ S → orderOf u = 2 →
      toBar z ⟨u, hu⟩ ∈ normalizer (L₁ : Set (CentralizerBar z)) →
      toBar z ⟨u, hu⟩ ∈ normalizer (L₂ : Set (CentralizerBar z)) → u ∉ LC z →
        PGLOver L₁ (zpowers (toBar z ⟨u, hu⟩)) q ∧ PGLOver L₂ (zpowers (toBar z ⟨u, hu⟩)) q := by
  intro u huC hu _ hn₁ hn₂ hLC
  exact absurd (S1_le_LC_of_psp4 hSC hP (mem_S1_of_normalizes hP.pair hu huC hn₁ hn₂)) hLC


end Pair

end CFSG.GH74.GLS.Stage2.Final.Thm6.L2011
