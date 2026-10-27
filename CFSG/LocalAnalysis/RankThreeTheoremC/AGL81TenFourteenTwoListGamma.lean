module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenFourteenTwoList
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentTenFourteenNarrow
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentTenFourteenCenter
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenFourteenTwoA5Lift
import CFSG.LocalAnalysis.EvenBN.Common.Diagonal

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenFourteenTwo

open CFSG.Open CFSG.AGLEmbedding Subgroup

@[expose] def KFactTenFourteenTwoA5Gamma : Prop :=
  ∀ (p : ℕ) (K : Type) [Group K] [Finite K] (T : Sylow p K) (K₁ J : Subgroup K),
    p.Prime → p ≠ 2 → RankOneCent.TenFourteenOneGroup p K → center K = ⊥ →
    CFSG.Open.pRank p (T : Subgroup K) ≤ 2 → RankOneCent.narrowGamma p (T : Subgroup K) ≤ K₁ →
    K₁ ≠ ⊤ → IsSubnormal J K₁ → ⁅J, J⁆ = J → J ≠ ⊥ →
    (∀ N₁ N₂ : Subgroup J, N₁.Normal → N₂.Normal → N₁ ⊔ N₂ = ⊤ → N₁ = ⊤ ∨ N₂ = ⊤) →
    p = 5 ∧ Nonempty (J ≃* alternatingGroup (Fin 5))

theorem kFactTenFourteenTwoA5_of_gamma
    (hSch : KFactCatalogSchreier) (hΓ : KFactTenFourteenTwoA5Gamma) :
    KFactTenFourteenTwoA5 := by
  intro p Y _ _ K Y₀ J R c hp hp2 hKn hL hKY hCK hc hco hR3 hN hJY hJs hJp hJirr hJC
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := hKn
  have hnc : ∃ a b : K, a * b ≠ b * a := by
    by_contra h
    push Not at h
    exact hKY fun k hk => hCK (mem_centralizer_iff.mpr fun m hm =>
      congrArg Subtype.val (h ⟨m, hm⟩ ⟨k, hk⟩))
  have hZ : center K = ⊥ := RankOneCent.center_eq_bot_of_tenFourteenOneGroup hL hnc
  obtain ⟨i, hi, ⟨e⟩⟩ := hL
  haveI := RankOneCent.isSimpleGroup_of_isTenFourteenOneIndex hi
  haveI hKs : IsSimpleGroup K := e.isSimpleGroup
  haveI := hSch K hKs hnc ⟨i, ⟨e⟩⟩
  haveI : Group.IsPerfect J :=
    (CFSG.LocalAnalysis.EvenBN.Common.isPerfect_subgroup_iff_commutator_eq J).mpr hJp
  set θ : Y →* MulAut K := MulAut.conjNormal with hθ
  set φ : K →* MulAut K := θ.comp K.subtype with hφ
  have hθker : ∀ y : Y, θ y = 1 ↔ y ∈ centralizer (K : Set Y) := by
    intro y
    refine ⟨fun h => mem_centralizer_iff.mpr fun m hm => ?_, fun h => ?_⟩
    · have := congrArg Subtype.val (DFunLike.congr_fun h ⟨m, hm⟩)
      simp only [hθ, MulAut.conjNormal_apply, MulAut.one_apply] at this
      exact (mul_inv_eq_iff_eq_mul.mp this).symm
    · refine MulEquiv.ext fun m => Subtype.ext ?_
      simp only [hθ, MulAut.conjNormal_apply, MulAut.one_apply]
      rw [(mem_centralizer_iff.mp h m m.2).symm, mul_inv_cancel_right]
  have hφinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro k hk
    have hkc := (hθker k).mp hk
    rw [mem_bot, ← mem_bot, ← hZ]
    exact mem_center_iff.mpr fun m => Subtype.ext (mem_centralizer_iff.mp hkc m m.2)
  have hJφ : ∀ j ∈ J, ∃ k : K, φ k = θ j := by
    intro j hj
    obtain ⟨k, hk, hkj⟩ :=
      CFSG.ComponentClassification.ComponentInnerActions.perfect_normalizer_action_inner J K
        (by rw [normalizer_eq_top]; exact le_top) ⟨j, hj⟩
    refine ⟨⟨k, hk⟩, MulEquiv.ext fun m => Subtype.ext ?_⟩
    simp only [hφ, hθ, MonoidHom.comp_apply, Subgroup.coe_subtype, MulAut.conjNormal_apply]
    exact (hkj m m.2).symm
  have hJrange : J.map θ ≤ φ.range := by
    rintro _ ⟨j, hj, rfl⟩
    obtain ⟨k, hk⟩ := hJφ j hj
    exact ⟨k, hk⟩
  set Jt : Subgroup K := (J.map θ).comap φ with hJt
  have hJtmap : Jt.map φ = J.map θ := Subgroup.map_comap_eq_self hJrange
  set K₁ : Subgroup K := Y₀.comap K.subtype with hK₁
  have hJK₁ : J.map θ ≤ K₁.map φ := by
    rintro _ ⟨j, hj, rfl⟩
    obtain ⟨k, hk⟩ := hJφ j hj
    refine ⟨k, ?_, hk⟩
    have hjk : j⁻¹ * (k : Y) ∈ centralizer (K : Set Y) := by
      rw [← hθker, map_mul, map_inv, ← hk, hφ, MonoidHom.comp_apply]
      exact inv_mul_cancel _
    have := Y₀.mul_mem (hJY hj) (hCK hjk)
    rwa [mul_inv_cancel_left] at this
  have hK₁Y : K₁.map φ ≤ Y₀.map θ := by
    rintro _ ⟨k, hk, rfl⟩
    exact ⟨k, hk, rfl⟩
  have hJts : IsSubnormal Jt K₁ := by
    have h1 := (hJs.map θ).inf_of_le hK₁Y
    rw [inf_eq_left.mpr hJK₁] at h1
    have h2 := h1.comap φ
    rwa [Subgroup.comap_map_eq_self_of_injective hφinj] at h2
  set σ : J →* Jt := (Subgroup.equivMapOfInjective Jt φ hφinj).symm.toMonoidHom.comp
    ((MulEquiv.subgroupCongr hJtmap.symm).toMonoidHom.comp (θ.subgroupMap J)) with hσ
  have hσs : Function.Surjective σ := by
    simp only [hσ, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom]
    exact (MulEquiv.surjective _).comp ((MulEquiv.surjective _).comp (θ.subgroupMap_surjective J))
  have hσker : σ.ker = (centralizer (K : Set Y)).subgroupOf J := by
    ext x
    rw [MonoidHom.mem_ker, mem_subgroupOf, ← hθker]
    simp only [hσ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [MulEquiv.map_eq_one_iff, MulEquiv.map_eq_one_iff, ← Subtype.val_inj]
    rfl
  have hJtp : ⁅Jt, Jt⁆ = Jt := by
    apply Subgroup.map_injective hφinj
    rw [Subgroup.map_commutator, hJtmap, ← Subgroup.map_commutator, hJp]
  have hJt1 : Jt ≠ ⊥ := by
    intro h
    apply hJC
    intro j hj
    rw [← hθker]
    have : θ j ∈ Jt.map φ := hJtmap ▸ mem_map_of_mem θ hj
    rw [h, Subgroup.map_bot, mem_bot] at this
    exact this
  have hJtirr := joinIrreducible_map σ hσs hJirr
  have hcK : c ∉ K := fun hcK => by
    have h1 : (⟨c, hcK⟩ : K) ∈ center K :=
      mem_center_iff.mpr fun g => Subtype.ext (mem_center_iff.mp hc g)
    rw [hZ, mem_bot] at h1
    have : c = 1 := congrArg Subtype.val h1
    exact hp.one_lt.ne' (by rw [← hco, this, orderOf_one])
  have hzc : zpowers c ≤ center Y := zpowers_le.mpr hc
  haveI : (zpowers c).Normal := ⟨fun n hn g => by
    rw [mem_center_iff.mp (hzc hn) g, mul_inv_cancel_right]
    exact hn⟩
  have hcR : c ∈ (R : Subgroup Y) :=
    (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hco, pow_one])).le_sylow_of_normal R
      (mem_zpowers c)
  have hcp : c ^ p = 1 := hco ▸ pow_orderOf_eq_one c
  have hcc : ∀ y : Y, y * c = c * y := fun y => (mem_center_iff.mp hc y)
  obtain ⟨T, hT⟩ := CFSG.QuasithinUnique.exists_sylow_map_eq_inf_of_normal R K
  have hTR : ∀ B : Subgroup K, B ≤ T → B.map K.subtype ≤ R := fun B hB =>
    (map_mono hB).trans (hT ▸ inf_le_left)
  have hadj : ∀ {E : Subgroup K} {k : ℕ}, IsElemAbelian p E → Nat.card E = p ^ k →
      IsElemAbelian p (E.map K.subtype ⊔ zpowers c) ∧
        Nat.card ↥(E.map K.subtype ⊔ zpowers c) = p ^ (k + 1) := by
    intro E k hE hEc
    obtain ⟨h1, h2⟩ := OtherCfg.isElemAbelian_sup_zpowers_gen hp
      (RankOneCent.isElemAbelian_map K.subtype hE) hcp
      (fun h => hcK (map_subtype_le E h)) (fun e _ => hcc e)
    refine ⟨h1, ?_⟩
    rw [h2, card_map_of_injective K.subtype_injective, hEc, pow_succ]
  have hrank : CFSG.Open.pRank p (T : Subgroup K) ≤ 2 := by
    by_contra h3
    obtain ⟨E, hET, hE, hEc⟩ :=
      CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := p) (H := (T : Subgroup K))
        (k := 3) (by omega)
    obtain ⟨hF, hFc⟩ := hadj hE hEc
    have := CFSG.SectionRank.le_pRank hp.one_lt
      (sup_le (hTR E hET) (zpowers_le.mpr hcR)) hF hFc
    omega
  have hΓK₁ : RankOneCent.narrowGamma p (T : Subgroup K) ≤ K₁ := by
    refine sup_le (iSup₂_le fun A ⟨hAT, hA, hAc⟩ => ?_) (iSup₂_le fun x ⟨hx, hxo, h2⟩ => ?_)
    · set Ah := A.map K.subtype
      have hAhc : Nat.card Ah = p ^ 2 := by
        rw [card_map_of_injective K.subtype_injective, hAc]
      obtain ⟨hF, hFc⟩ := hadj hA hAc
      have hAhcomm : Ah ≤ centralizer (Ah : Set Y) := fun a ha =>
        mem_centralizer_iff.mpr fun b hb => congrArg Subtype.val
          ((RankOneCent.isElemAbelian_map K.subtype hA).1.is_comm.comm ⟨b, hb⟩ ⟨a, ha⟩)
      have h3 : 3 ≤ CFSG.Open.pRank p ((R : Subgroup Y) ⊓ centralizer (Ah : Set Y)) :=
        CFSG.SectionRank.le_pRank hp.one_lt
          (sup_le (le_inf (hTR A hAT) hAhcomm) (zpowers_le.mpr
            ⟨hcR, center_le_centralizer _ hc⟩)) hF hFc
      have hNY := hN Ah (hTR A hAT) (RankOneCent.isElemAbelian_map K.subtype hA) hAhc h3
      intro k hk
      exact hNY (le_normalizer_map K.subtype ⟨k, hk, rfl⟩)
    · set xh : Y := (x : Y)
      have hxhR : xh ∈ (R : Subgroup Y) := hTR _ (zpowers_le.mpr hx) ⟨x, by simp, rfl⟩
      have hxho : orderOf xh = p := by rw [Subgroup.orderOf_coe, hxo]
      obtain ⟨hX, hXc⟩ := RankOneCent.isElemAbelian_zpowers hp hxho
      have hcx : c ∉ zpowers xh := fun h => hcK ((zpowers_le.mpr x.2) h)
      obtain ⟨hAh, hAhc⟩ := OtherCfg.isElemAbelian_sup_zpowers_gen hp hX hcp hcx
        (fun e _ => hcc e)
      set Ah := zpowers xh ⊔ zpowers c
      have hAhR : Ah ≤ R := sup_le (zpowers_le.mpr hxhR) (zpowers_le.mpr hcR)
      obtain ⟨E, hET, hE, hEc⟩ :=
        CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank
          (H := (T : Subgroup K) ⊓ centralizer ({x} : Set K)) (k := 2) h2
      obtain ⟨hF, hFc⟩ := hadj hE hEc
      have hFx : E.map K.subtype ⊔ zpowers c ≤ centralizer ({xh} : Set Y) := by
        refine sup_le ?_ (hzc.trans (center_le_centralizer _))
        rintro _ ⟨e, he, rfl⟩
        exact mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (mem_centralizer_singleton_iff.mp (hET he).2))
      have hFAh : E.map K.subtype ⊔ zpowers c ≤ centralizer (Ah : Set Y) := by
        rw [← le_centralizer_iff]
        refine sup_le (zpowers_le.mpr (mem_centralizer_iff.mpr fun f hf =>
          mem_centralizer_singleton_iff.mp (hFx hf)))
          (hzc.trans (center_le_centralizer _))
      have h3 : 3 ≤ CFSG.Open.pRank p ((R : Subgroup Y) ⊓ centralizer (Ah : Set Y)) :=
        CFSG.SectionRank.le_pRank hp.one_lt
          (le_inf (sup_le (hTR E (hET.trans inf_le_left)) (zpowers_le.mpr hcR)) hFAh)
          hF hFc
      have hNY := hN Ah hAhR hAh (by rw [hAhc, hXc, sq]) h3
      intro k hk
      refine hNY (centralizer_le_normalizer _ ?_)
      have hAk : Ah ≤ centralizer ({(k : Y)} : Set Y) :=
        sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hk)).symm))
          (hzc.trans (center_le_centralizer _))
      exact mem_centralizer_iff.mpr fun h hh => mem_centralizer_singleton_iff.mp (hAk hh)
  have hK₁ne : K₁ ≠ ⊤ := fun htop => hKY fun y hy =>
    (show (⟨y, hy⟩ : K) ∈ K₁ by rw [htop]; exact mem_top _)
  obtain ⟨hp5, ⟨e5⟩⟩ := hΓ p K T K₁ Jt hp hp2 ⟨i, hi, ⟨e⟩⟩ hZ hrank hΓK₁ hK₁ne hJts hJtp hJt1
    hJtirr
  refine ⟨hp5, e5.toMonoidHom.comp σ, e5.surjective.comp hσs, ?_⟩
  rw [← hσker]
  ext x
  simp [MonoidHom.mem_ker]

end CFSG.LocalAnalysis.RankThreeTheoremC.TenFourteenTwo
