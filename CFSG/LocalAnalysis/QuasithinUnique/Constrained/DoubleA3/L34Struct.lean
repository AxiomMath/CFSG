module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.L34Comp
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Claim1Assembly

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Subgroup
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {T M H S L K : Subgroup G} {s x z₁ z₂ : G}

section Struct

variable (hD : AppC.C56DoubleA3) (h27_1 : Lemma2_4_27_1A3) (hI : Inputs2436)
  (hK : A3A3K T M H S L s x z₁ z₂ K) (hc : blockU2 L s ≤ Subgroup.centralizer (K : Set G))
include hD h27_1 hI hK hc

theorem A3A3K.comm_K_Ks
    : ∀ a ∈ K, ∀ b ∈ conjR K s, a * b = b * a := fun _ ha b hb =>
  (Subgroup.mem_centralizer_iff.mp (hK.K_le_centralizer_Ks hD h27_1 hI hc ha) b hb).symm

theorem A3A3K.inf_K_Ks
    : K ⊓ conjR K s = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  rw [Subgroup.mem_bot]
  exact BenderBranch.eq_one_of_commute_of_simple hK.isSimpleGroup hK.nonabelian hy.1 fun k hk =>
    hK.comm_K_Ks hD h27_1 hI hc k hk y hy.2

theorem A3A3K.nonempty_psl27
    : Nonempty (↥K ≃* PSL(2, ZMod 7)) := by
  rcases hK.K_iso with ⟨⟨e⟩⟩ | h
  · exfalso
    have hcs := hK.cs
    have hKK' := hK.K_le_centralizer_Ks hD h27_1 hI hc
    have hAs := hK.isA4s
    obtain ⟨c, hcL, hc3', hcN, -, -⟩ := hAs.exists_c
    have hcK' : c ∈ conjR K s := by
      have : conjR L s ≤ conjR K s := by
        intro y hy
        rw [mem_conjR] at hy ⊢
        exact hK.L_le_K hy
      exact this hcL
    have hc3 : c ^ 3 = 1 := by rw [← hc3']; exact pow_orderOf_eq_one c
    have hc1 : c ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hc3'
      omega
    have hU₂1 : blockU2 L s ≠ ⊥ := by
      intro h
      have hz : z₂ ∈ blockU2 L s := hK.toA3A3x.z₂_mem.1
      rw [h] at hz
      exact hK.toA3A3x.z₂_ne (Subgroup.mem_bot.mp hz)
    have hNloc : IsTwoLocal (normalizer ((blockU2 L s : Subgroup G) : Set G)) :=
      ⟨blockU2 L s, hU₂1, hAs.isPGroup_U, rfl⟩
    have hKN : K ≤ normalizer ((blockU2 L s : Subgroup G) : Set G) := by
      apply C5.le_normalizer_of_commute
      intro κ hκ u hu
      exact (Subgroup.mem_centralizer_iff.mp (hc hu) κ hκ)
    have hrank : ∀ E : Subgroup G, E ≤ normalizer ((blockU2 L s : Subgroup G) : Set G) →
        IsElemAbelian 3 E → Nat.card E ≤ 9 :=
      fun E hE hEa => card_isElemAbelian_three_le hcs.setting.qtke.2.2 hNloc hE hEa
    exact false_of_centralizing_order_three e hKN hrank hcN hc3 hc1 fun a ha =>
      (Subgroup.mem_centralizer_iff.mp (hKK' ha) c hcK').symm
  · exact h

theorem A3A3K.normalizer_blockU2_le :
    normalizer (blockU2 L s : Set G) ≤ normalizer (K : Set G) := by
  intro g hg
  have hz₂U : z₂ ∈ blockU2 L s := hK.toA3A3x.z₂_mem.1
  have hz₂1 : z₂ ≠ 1 := hK.toA3A3x.z₂_ne
  have hv : g⁻¹ * z₂ * g ∈ blockU2 L s := by
    have := (Subgroup.mem_normalizer_iff.mp ((normalizer (blockU2 L s : Set G)).inv_mem hg) z₂).mp
      hz₂U
    simpa using this
  have hv1 : g⁻¹ * z₂ * g ≠ 1 := by
    intro h
    apply hz₂1
    calc z₂ = g * (g⁻¹ * z₂ * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; group
  exact (hK.uniqComp_z₂ hD h27_1).mem_normalizer (hK.uniqComp_of_mem_U₂ hD h27_1 hI hc hv hv1)

theorem A3A3K.baum_le_normalizer_K : baum S ≤ normalizer (K : Set G) :=
  (hK.baum_le_normalizer_blockU2).trans (hK.normalizer_blockU2_le hD h27_1 hI hc)

theorem A3A3K.baum_le_normalizer_Ks : baum S ≤ normalizer ((conjR K s : Subgroup G) : Set G) :=
  (baum_le_normalizer_blockU hK.cs hK.a3).trans (hK.normalizer_blockU_le hD h27_1 hI hc)

omit hD h27_1 hI hc in
theorem A3A3K.x_mem_normalizer_K : x ∈ normalizer (K : Set G) :=
  hK.K_norm (Subgroup.mem_centralizer_singleton_iff.mpr hK.x_comm₂)

theorem A3A3K.conjR_Ks_eq : conjR (conjR K s) s = K := by
  have hB := basic31 hD h27_1 hK.toA3A3
  have hss : s * s ∈ baum S := (s_mul_self_mem_baum hB hK.toA3A3).2
  rw [conjR_conjR_eq]
  exact mem_normalizer_iff_conjR_eq.mp (hK.baum_le_normalizer_K hD h27_1 hI hc hss)

theorem A3A3K.T_le_normalizer_sup :
    T ≤ normalizer ((K ⊔ conjR K s : Subgroup G) : Set G) := by
  have hB := basic31 hD h27_1 hK.toA3A3
  have hRn : baum S ≤ normalizer ((K ⊔ conjR K s : Subgroup G) : Set G) := fun r hr =>
    C1.mem_normalizer_sup (hK.baum_le_normalizer_K hD h27_1 hI hc hr)
      (hK.baum_le_normalizer_Ks hD h27_1 hI hc hr)
  have hxn : x ∈ normalizer ((K ⊔ conjR K s : Subgroup G) : Set G) :=
    C1.mem_normalizer_sup (hK.x_mem_normalizer_K)
      (hK.x_mem_normalizer_Ks hD h27_1 hI hc)
  have hsn : s ∈ normalizer ((K ⊔ conjR K s : Subgroup G) : Set G) := by
    rw [mem_normalizer_iff_conjR_eq, Lin2.conjR_sup, hK.conjR_Ks_eq hD h27_1 hI hc, sup_comm]
  have hSn : S ≤ normalizer ((K ⊔ conjR K s : Subgroup G) : Set G) := by
    rw [hB.S_eq]
    exact sup_le hRn (Subgroup.zpowers_le.mpr hsn)
  have hTle := le_sup_zpowers_of_relIndex_two hB.idx_T hK.x_mem hK.x_not_mem
  exact hTle.trans (sup_le hSn (Subgroup.zpowers_le.mpr hxn))

theorem A3A3K.centralizer_T_sup_eq_bot :
    T ⊓ Subgroup.centralizer ((K ⊔ conjR K s : Subgroup G) : Set G) = ⊥ := by
  by_contra hne
  have hcs := hK.cs
  have hB := basic31 hD h27_1 hK.toA3A3
  have hz := z_central hB hK.toA3A3x
  have hTN := hK.T_le_normalizer_sup hD h27_1 hI hc
  have hCn : T ≤ normalizer ((T ⊓ Subgroup.centralizer ((K ⊔ conjR K s : Subgroup G) : Set G) :
      Subgroup G) : Set G) := by
    intro t ht
    apply mem_normalizer_of_conj_mem
    rintro c ⟨hcT, hcD⟩
    refine ⟨T.mul_mem (T.mul_mem ht hcT) (T.inv_mem ht), ?_⟩
    apply Subgroup.mem_centralizer_iff.mpr
    intro n hn
    have hn' : t⁻¹ * n * t ∈ (K ⊔ conjR K s : Subgroup G) := by
      have := (Subgroup.mem_normalizer_iff.mp (hTN (T.inv_mem ht)) n).mp hn
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.mp hcD _ hn'
    calc n * (t * c * t⁻¹) = t * ((t⁻¹ * n * t) * c) * t⁻¹ := by group
      _ = t * (c * (t⁻¹ * n * t)) * t⁻¹ := by rw [h1]
      _ = (t * c * t⁻¹) * n := by group
  obtain ⟨y, hyC, hy1, hyZ⟩ := Lin2.exists_mem_inf_center_of_normal hcs.setting.isPGroup
    inf_le_left hCn hne
  have hyM : Subgroup.centralizer ({y} : Set G) ≤ M :=
    hcs.setting.centralizer_le_of_mem_center_isSylowTwoOf hcs.setting.isSylowTwoOf_M
      ⟨hyC.1, hyZ⟩ hy1
  have hNy : (K ⊔ conjR K s : Subgroup G) ≤ centralizerElem y := fun n hn =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hyC.2 n hn)
  have hLM : L ≤ M := fun l hl => hyM (hNy (mem_sup_left (hK.L_le_K hl)))
  exact hcs.not_le hLM

theorem A3A3K.centralizer_sup_eq_bot :
    Subgroup.centralizer ((K ⊔ conjR K s : Subgroup G) : Set G) = ⊥ := by
  have hcs := hK.cs
  have hB := basic31 hD h27_1 hK.toA3A3
  have hz := z_central hB hK.toA3A3x
  have hz1 : z₁ * z₂ ≠ 1 := hK.toA3A3x.z_ne
  have hz2 : (z₁ * z₂) ^ 2 = 1 := hK.toA3A3x.sq_z
  have hCT := hK.centralizer_T_sup_eq_bot hD h27_1 hI hc
  have hTN := hK.T_le_normalizer_sup hD h27_1 hI hc
  have hzN : z₁ * z₂ ∈ (K ⊔ conjR K s : Subgroup G) :=
    mul_mem (mem_sup_left hK.z₁_mem_K) (mem_sup_right hK.z₂_mem_conjR)
  set D : Subgroup G := Subgroup.centralizer ((K ⊔ conjR K s : Subgroup G) : Set G) with hDdef
  have hDz : D ≤ centralizerElem (z₁ * z₂) := fun d hd =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hd _ hzN).symm
  have hTz : T ≤ centralizerElem (z₁ * z₂) := fun t ht =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hz.2 t ht)
  have hpc : pCoreOf 2 (centralizerElem (z₁ * z₂)) ≠ ⊥ := pCoreOf_centralizerElem_ne_bot hz1 hz2
  have hchar : CharTwo (centralizerElem (z₁ * z₂)) :=
    charTwo_of_isSylowTwoOf_le_of_pCore_ne_bot hcs.setting.qtke.2.1 hcs.setting.sylow hTz hpc
  have hSyl : IsSylowTwoOf T (centralizerElem (z₁ * z₂)) :=
    isSylowTwoOf_of_le hcs.setting.sylow hTz
  have hYT : pCoreOf 2 (centralizerElem (z₁ * z₂)) ≤ T := hSyl.pCoreOf_le
  have hTD : T ≤ normalizer (D : Set G) := by
    intro t ht
    apply mem_normalizer_of_conj_mem
    intro d hd
    rw [hDdef, Subgroup.mem_centralizer_iff]
    intro n hn
    have hn' : t⁻¹ * n * t ∈ (K ⊔ conjR K s : Subgroup G) := by
      have := (Subgroup.mem_normalizer_iff.mp (hTN (T.inv_mem ht)) n).mp hn
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.mp hd _ hn'
    calc n * (t * d * t⁻¹) = t * ((t⁻¹ * n * t) * d) * t⁻¹ := by group
      _ = t * (d * (t⁻¹ * n * t)) * t⁻¹ := by rw [h1]
      _ = (t * d * t⁻¹) * n := by group
  rw [eq_bot_iff]
  intro d hd
  rw [Subgroup.mem_bot]
  have hdY : d ∈ pCoreOf 2 (centralizerElem (z₁ * z₂)) := by
    apply hchar
    refine ⟨hDz hd, ?_⟩
    apply Subgroup.mem_centralizer_iff.mpr
    intro y hy
    have hy' : y ∈ pCoreOf 2 (centralizerElem (z₁ * z₂)) := hy
    have hyT : y ∈ T := hYT hy'
    have hc1 : y * d * y⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp (hTD hyT) d).mp hd
    have hc2 : y * d * y⁻¹ * d⁻¹ ∈ D := D.mul_mem hc1 (D.inv_mem hd)
    have hc3 : y * d * y⁻¹ * d⁻¹ ∈ pCoreOf 2 (centralizerElem (z₁ * z₂)) := by
      have hdn : d ∈ normalizer ((pCoreOf 2 (centralizerElem (z₁ * z₂)) : Subgroup G) : Set G) :=
        CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 _ (hDz hd)
      have h1 := (Subgroup.mem_normalizer_iff.mp hdn y⁻¹).mp (inv_mem hy')
      have h2 : d * y⁻¹ * d⁻¹ ∈ pCoreOf 2 (centralizerElem (z₁ * z₂)) := by simpa using h1
      have h3 : y * (d * y⁻¹ * d⁻¹) ∈ pCoreOf 2 (centralizerElem (z₁ * z₂)) := mul_mem hy' h2
      have e : y * d * y⁻¹ * d⁻¹ = y * (d * y⁻¹ * d⁻¹) := by group
      rw [e]; exact h3
    have hmem : y * d * y⁻¹ * d⁻¹ ∈ T ⊓ D := ⟨hYT hc3, hc2⟩
    rw [hCT, Subgroup.mem_bot] at hmem
    have : y * d = d * y := by
      calc y * d = (y * d * y⁻¹ * d⁻¹) * (d * y) := by group
        _ = d * y := by rw [hmem]; group
    exact this
  have hdT : d ∈ T := hYT hdY
  have hdCT : d ∈ T ⊓ D := ⟨hdT, hd⟩
  rw [hCT, Subgroup.mem_bot] at hdCT
  exact hdCT

end Struct

end CFSG.QuasithinUnique.DoubleA3
