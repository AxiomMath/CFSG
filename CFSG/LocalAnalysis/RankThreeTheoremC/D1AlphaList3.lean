module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1AlphaInner3
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1AlphaGenLift3
import CFSG.LocalAnalysis.RankThreeTheoremC.D1AlphaListE2
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1AlphaExp3

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding

variable {G : Type} [Group G] [Finite G]

@[expose] def IsLinThreeCover3 (d : TauCeti.ValidLieTypeIndex) : Prop :=
  (∃ q : TauCeti.PrimePower, d.1 = .A 2 q ∧ 3 ∣ q.card - 1) ∨
  (∃ q : TauCeti.PrimePower, d.1 = .twistedA 2 q ∧ 3 ∣ q.card + 1)

@[expose] def D1ComponentAlphaLinThree3 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (P : Sylow p G) (M H R : Subgroup G) (z : G)
    (Pbar : Sylow p (ReducedCentralizer p z)) (zbar : ReducedCentralizer p z)
    (K : Subgroup (ReducedCentralizer p z)), p = 3 →
    D1ComponentAlphaData3 p P M H R z Pbar zbar K →
    ∀ d : TauCeti.ValidLieTypeIndex, IsLinThreeCover3 d →
      Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) →
      ∃ A : Subgroup (ReducedCentralizer p z),
        A ≤ (Pbar : Subgroup (ReducedCentralizer p z)) ∧ IsElemAbelian p A ∧
        3 ≤ Open.pRank p A ∧ Subgroup.closure {k : K | ∃ f ∈ A,
          f ∉ Subgroup.centralizer (K : Set (ReducedCentralizer p z)) ∧
          f * (k : ReducedCentralizer p z) * f⁻¹ = k} = ⊤

@[expose] def D1ComponentAlphaLinThree3S (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (P : Sylow p G) (M H R : Subgroup G) (z : G)
    (Pbar : Sylow p (ReducedCentralizer p z)) (zbar : ReducedCentralizer p z)
    (K : Subgroup (ReducedCentralizer p z)), p = 3 →
    D1ComponentAlphaData3 p P M H R z Pbar zbar K →
    Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 2 →
    ∀ d : TauCeti.ValidLieTypeIndex, IsLinThreeCover3 d →
      Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) →
      ∃ A : Subgroup (ReducedCentralizer p z),
        A ≤ (Pbar : Subgroup (ReducedCentralizer p z)) ∧ IsElemAbelian p A ∧
        3 ≤ Open.pRank p A ∧ Subgroup.closure {k : K | ∃ f ∈ A,
          f ∉ Subgroup.centralizer (K : Set (ReducedCentralizer p z)) ∧
          f * (k : ReducedCentralizer p z) * f⁻¹ = k} = ⊤

theorem D1ComponentAlphaLinThree3.toS (h : D1ComponentAlphaLinThree3 G) :
    D1ComponentAlphaLinThree3S G :=
  fun p _ P M H R z Pbar zbar K hp3 hd _ d hd' e => h p P M H R z Pbar zbar K hp3 hd d hd' e

@[expose] def KFactAlphaListM3Wide : Prop :=
  ∀ (K : Type) [Group K] [Finite K], Open.IsQuasisimple K →
    IsCatalogGroup (K ⧸ Subgroup.center K) → Subgroup.center K ≠ ⊥ →
    IsPGroup 3 (Subgroup.center K) → IsCyclic (Subgroup.center K) →
    Open.pRank 3 (⊤ : Subgroup K) ≤ 3 →
    Nonempty (K ⧸ Subgroup.center K ≃* alternatingGroup (Fin 6)) ∨
    Nonempty (K ⧸ Subgroup.center K ≃* alternatingGroup (Fin 7)) ∨
    Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.sporadic .M22).Group) ∨
    Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.sporadic .ONan).Group) ∨
    ∃ d : TauCeti.ValidLieTypeIndex, IsLinThreeCover3 d ∧
      Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group)

@[expose] def KFactAlphaListM3 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], Open.IsQuasisimple K → CFSG.IsKGroup K →
    CFSG.twoLocalOddRank K ≤ 3 →
    IsCatalogGroup (K ⧸ Subgroup.center K) → Subgroup.center K ≠ ⊥ →
    IsPGroup 3 (Subgroup.center K) → IsCyclic (Subgroup.center K) →
    Open.pRank 3 (⊤ : Subgroup K) ≤ 3 →
    Nonempty (K ⧸ Subgroup.center K ≃* alternatingGroup (Fin 6)) ∨
    Nonempty (K ⧸ Subgroup.center K ≃* alternatingGroup (Fin 7)) ∨
    Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.sporadic .M22).Group) ∨
    Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.sporadic .ONan).Group) ∨
    ∃ d : TauCeti.ValidLieTypeIndex, IsLinThreeCover3 d ∧
      Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group)

@[expose] def KFactAlphaSmallAut3 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], Open.IsQuasisimple K → Subgroup.center K ≠ ⊥ →
    IsPGroup 3 (Subgroup.center K) → IsCyclic (Subgroup.center K) →
    (Nonempty (K ⧸ Subgroup.center K ≃* alternatingGroup (Fin 6)) ∨
      Nonempty (K ⧸ Subgroup.center K ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.sporadic .M22).Group)) →
    Open.pRank 3 (⊤ : Subgroup (MulAut K)) ≤ 2 ∧
      ∀ B : Subgroup (MulAut K), IsPGroup 3 B → IsMulCommutative B

@[expose] def KFactAlphaOnan3 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], Open.IsQuasisimple K → Subgroup.center K ≠ ⊥ →
    IsPGroup 3 (Subgroup.center K) → IsCyclic (Subgroup.center K) →
    Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.sporadic .ONan).Group) →
    KOutTwoGroup K ∧ ∀ T : Sylow 3 K, ∀ t ∈ (T : Subgroup K), t ^ 3 = 1

@[expose] def KFactSL3OutNormalSylow : Prop :=
  ∀ (K : Type) [Group K] [Finite K], Open.IsQuasisimple K → ∀ d : TauCeti.ValidLieTypeIndex,
    IsLinThreeCover3 d → Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) →
    KOutNormalSylow 3 K

theorem D1ComponentAlphaData3.list {p : ℕ} [Fact p.Prime] {P : Sylow p G} {M H R : Subgroup G}
    {z : G} {Pbar : Sylow p (ReducedCentralizer p z)} {zbar : ReducedCentralizer p z}
    {K : Subgroup (ReducedCentralizer p z)} (hd : D1ComponentAlphaData3 p P M H R z Pbar zbar K)
    (hp3 : p = 3) (hList : KFactAlphaListM3) :
    Nonempty (K ⧸ Subgroup.center K ≃* alternatingGroup (Fin 6)) ∨
    Nonempty (K ⧸ Subgroup.center K ≃* alternatingGroup (Fin 7)) ∨
    Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.sporadic .M22).Group) ∨
    Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.sporadic .ONan).Group) ∨
    ∃ d : TauCeti.ValidLieTypeIndex, IsLinThreeCover3 d ∧
      Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) := by
  have hKe := hd.data.isKGroup_twoLocalOddRank_le hp3
  subst hp3
  have hp : (3 : ℕ).Prime := Fact.out
  have h3 := hd.data.pRank_normal_le
  exact hList K hd.data.comp.2.2 hKe.1 hKe.2
    (hd.data.catalog.isCatalogGroup_center_quotient hd.data.comp)
    hd.center_ne_bot (isPGroup_center_of_isComponentOf hp hd.data.red.core_eq_bot hd.data.comp)
    hd.center_cyclic h3

theorem D1ComponentAlphaData3.exp_of_sylow {P : Sylow 3 G} {M H R : Subgroup G} {z : G}
    [Fact (Nat.Prime 3)] {Pbar : Sylow 3 (ReducedCentralizer 3 z)} {zbar : ReducedCentralizer 3 z}
    {K : Subgroup (ReducedCentralizer 3 z)}
    (hd : D1ComponentAlphaData3 3 P M H R z Pbar zbar K)
    (hT : ∀ T : Sylow 3 K, ∀ t ∈ (T : Subgroup K), t ^ 3 = 1) :
    ∀ t ∈ (Pbar : Subgroup (ReducedCentralizer 3 z)) ⊓ K, t ^ 3 = 1 := by
  have := hd.data.normal
  obtain ⟨T, hT'⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal Pbar
    hd.data.normal.isSubnormal
  intro t ht
  rw [← hT'] at ht
  obtain ⟨s, hs, rfl⟩ := ht
  show (K.subtype s) ^ 3 = 1
  rw [← map_pow, hT T s hs, map_one]

theorem alphaSmallInner_of_list (hList : KFactAlphaListM3) (hSmall : KFactAlphaSmallAut3)
    (hOn : KFactAlphaOnan3) (hOut : KFactSL3OutNormalSylow)
    (hL3 : D1ComponentAlphaLinThree3S G) : D1ComponentAlphaSmallInner3 G := by
  intro p _ P M H R z Pbar zbar K hp3 hd hcomm hB hrank
  have hK : Open.IsQuasisimple K := hd.data.comp.2.2
  have hp : p.Prime := Fact.out
  have hpg : IsPGroup p (Subgroup.center K) :=
    isPGroup_center_of_isComponentOf hp hd.data.red.core_eq_bot hd.data.comp
  rcases hd.list hp3 hList with e | e | e | e | ⟨d, hd', e⟩
  · subst hp3
    obtain ⟨B, hBp, hBnc⟩ := hB
    exact hBnc ((hSmall K hK hd.center_ne_bot hpg hd.center_cyclic (Or.inl e)).2 B hBp)
  · subst hp3
    obtain ⟨B, hBp, hBnc⟩ := hB
    exact hBnc ((hSmall K hK hd.center_ne_bot hpg hd.center_cyclic (Or.inr (Or.inl e))).2 B hBp)
  · subst hp3
    obtain ⟨B, hBp, hBnc⟩ := hB
    exact hBnc ((hSmall K hK hd.center_ne_bot hpg hd.center_cyclic (Or.inr (Or.inr e))).2 B hBp)
  · subst hp3
    obtain ⟨hout, hexp⟩ := hOn K hK hd.center_ne_bot hpg hd.center_cyclic e
    exact hd.false_of_exp_three rfl hout (hd.exp_of_sylow hexp)
  · subst hp3
    obtain ⟨A, hAR, hA, hA3, hclos⟩ := hL3 3 P M H R z Pbar zbar K rfl hd hrank d hd' e
    have : K.Normal := hd.data.normal
    have hKX := hd.data.red.le_of_exists_genLift hd.data.zbar_mem_center hd.data.zbar_order
      ⟨A, hAR, hA, hA3, hclos⟩
    have hnc := hd.data.red.not_isCyclic_inf_of_mem hd.data.zbar_mem_center hd.data.zbar_order
      hd.data.comp hd.mem
    have hC := hd.data.red.centralizer_le_of_not_isCyclic hd.data.normal hnc
    exact hd.data.red.false_of_kOutNormalSylow hKX hC (hOut K hK d hd' e)

@[expose] def KFactSL3LiftGen : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (R : Sylow 3 X) (K : Subgroup X) [K.Normal] (z : X)
    (d : TauCeti.ValidLieTypeIndex), IsLinThreeCover3 d → Open.IsQuasisimple K →
    Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) →
    z ∈ Subgroup.center X → z ∈ K → orderOf z = 3 →
    (∀ c ∈ (R : Subgroup X) ⊓ Subgroup.centralizer (K : Set X), orderOf c = 3 →
      c ∈ Subgroup.zpowers z) →
    Open.pRank 3 (R : Subgroup X) = 3 →
    ∃ A : Subgroup X, A ≤ (R : Subgroup X) ∧ IsElemAbelian 3 A ∧ 3 ≤ Open.pRank 3 A ∧
      Subgroup.closure {k : K | ∃ f ∈ A, f ∉ Subgroup.centralizer (K : Set X) ∧
        f * (k : X) * f⁻¹ = k} = ⊤

theorem linThree_of_kfact (h : KFactSL3LiftGen) : D1ComponentAlphaLinThree3 G := by
  intro p _ P M H R z Pbar zbar K hp3 hd d hd' e
  subst hp3
  have : K.Normal := hd.data.normal
  exact h (ReducedCentralizer 3 z) Pbar K zbar d hd' hd.data.comp.2.2 e hd.data.zbar_mem_center
    hd.mem hd.data.zbar_order (fun c hc hcp => hd.omega c hc hcp) hd.data.pRank_pbar_eq

structure D1AlphaKFacts3 : Prop where
  list : KFactAlphaListM3
  smallAut : KFactAlphaSmallAut3
  onan : KFactAlphaOnan3
  sl3Out : KFactSL3OutNormalSylow
  sl3LiftGen : KFactSL3LiftGen

theorem alphaNone_of_list (hA : D1AlphaKFacts3) (hKF1 : KF1At G) : D1ComponentAlphaNone3 G := by
  intro p _ P M H R z Pbar zbar K hd
  have hp3 := hd.eq_three hKF1
  have hK : Open.IsQuasisimple K := hd.data.comp.2.2
  have hp : p.Prime := Fact.out
  have hpg : IsPGroup p (Subgroup.center K) :=
    isPGroup_center_of_isComponentOf hp hd.data.red.core_eq_bot hd.data.comp
  have hSmallCase : D1ComponentAlphaSmallCaseThree3 G := d1ComponentAlphaSmallCaseThree3_of_inner
    (alphaSmallInner_of_list hA.list hA.smallAut hA.onan hA.sl3Out
      (linThree_of_kfact hA.sl3LiftGen).toS)
  rcases hd.list hp3 hA.list with e | e | e | e | ⟨d, hd', e⟩
  · subst hp3
    exact hSmallCase 3 P M H R z Pbar zbar K rfl hd
      (hA.smallAut K hK hd.center_ne_bot hpg hd.center_cyclic (Or.inl e)).1
  · subst hp3
    exact hSmallCase 3 P M H R z Pbar zbar K rfl hd
      (hA.smallAut K hK hd.center_ne_bot hpg hd.center_cyclic (Or.inr (Or.inl e))).1
  · subst hp3
    exact hSmallCase 3 P M H R z Pbar zbar K rfl hd
      (hA.smallAut K hK hd.center_ne_bot hpg hd.center_cyclic (Or.inr (Or.inr e))).1
  · subst hp3
    obtain ⟨hout, hexp⟩ := hA.onan K hK hd.center_ne_bot hpg hd.center_cyclic e
    exact hd.false_of_exp_three rfl hout (hd.exp_of_sylow hexp)
  · subst hp3
    obtain ⟨A, hAR, hA', hA3, hclos⟩ :=
      (linThree_of_kfact hA.sl3LiftGen : D1ComponentAlphaLinThree3 G) 3 P M H R z Pbar zbar K rfl
        hd d hd' e
    have : K.Normal := hd.data.normal
    have hKX := hd.data.red.le_of_exists_genLift hd.data.zbar_mem_center hd.data.zbar_order
      ⟨A, hAR, hA', hA3, hclos⟩
    have hnc := hd.data.red.not_isCyclic_inf_of_mem hd.data.zbar_mem_center
      hd.data.zbar_order hd.data.comp hd.mem
    have hC := hd.data.red.centralizer_le_of_not_isCyclic hd.data.normal hnc
    exact hd.data.red.false_of_kOutNormalSylow hKX hC (hA.sl3Out K hK d hd' e)

end CFSG.LocalAnalysis.RankThreeTheoremC
