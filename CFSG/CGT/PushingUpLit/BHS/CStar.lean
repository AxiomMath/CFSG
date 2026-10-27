module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellNatActual
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesExtraBasic
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.Background.C1Basic

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Campbell

variable {Γ : Type} [Group Γ]

@[expose] def cStarIn (G T : Subgroup Γ) : Subgroup Γ :=
  (G ⊓ Subgroup.centralizer (omegaOneCenterOf T : Set Γ)) ⊔ cgsIn G (baum T)

theorem cStarIn_le (G T : Subgroup Γ) : cStarIn G T ≤ G :=
  sup_le inf_le_left (cgsIn_le G (baum T))

theorem cgsIn_mono {H H' S : Subgroup Γ} (h : H ≤ H') : cgsIn H S ≤ cgsIn H' S :=
  iSup_mono fun _ => iSup_mono fun _ => iSup_mono fun _ => iSup_mono fun _ =>
    inf_le_inf_right _ h

theorem cStarIn_mono {G G' : Subgroup Γ} (T : Subgroup Γ) (h : G ≤ G') :
    cStarIn G T ≤ cStarIn G' T :=
  sup_le_sup (inf_le_inf_right _ h) (cgsIn_mono h)

theorem centralizer_le_cStarIn (G T : Subgroup Γ) :
    G ⊓ Subgroup.centralizer (omegaOneCenterOf T : Set Γ) ≤ cStarIn G T := le_sup_left

section Finite

variable [Finite Γ]

theorem inf_normalizer_le_cStarIn {G T : Subgroup Γ} (hT : IsPGroup 2 T) (hT0 : T ≠ ⊥) :
    G ⊓ Subgroup.normalizer (T : Set Γ) ≤ cStarIn G T := by
  have hb : baum T ≠ ⊥ := C1GN.baum_ne_bot hT hT0
  refine le_trans ?_ le_sup_right
  refine le_trans ?_ (inf_normalizer_le_cgsIn hb)
  exact inf_le_inf_left _ (normalizer_le_normalizer_baum T)

omit [Finite Γ] in
theorem noCharNormal_baum_of_cStarIn_ne {G T : Subgroup Γ} (h : cStarIn G T ≠ G) :
    NoCharNormal (baum T) G := by
  intro C hCB hC0 hCchar hGC
  apply h
  refine le_antisymm (cStarIn_le G T) fun g hg => ?_
  refine le_sup_right (a := G ⊓ Subgroup.centralizer (omegaOneCenterOf T : Set Γ)) ?_
  have hmem : g ∈ G ⊓ Subgroup.normalizer (C : Set Γ) := ⟨hg, hGC hg⟩
  have hle : G ⊓ Subgroup.normalizer (C : Set Γ) ≤ cgsIn G (baum T) :=
    le_iSup_of_le C (le_iSup_of_le hCB (le_iSup_of_le hC0 (le_iSup_of_le hCchar le_rfl)))
  exact hle hmem

omit [Finite Γ] in
theorem inf_normalizer_baum_le_cStarIn {G T : Subgroup Γ} (hb : baum T ≠ ⊥) :
    G ⊓ Subgroup.normalizer (baum T : Set Γ) ≤ cStarIn G T :=
  le_trans (inf_normalizer_le_cgsIn hb) le_sup_right

omit [Finite Γ] in
theorem isElemAbelian_sup_of_le_centralizer {A V : Subgroup Γ} (hA : IsElemAbelian 2 A)
    (hV : IsElemAbelian 2 V) (hAV : A ≤ Subgroup.centralizer (V : Set Γ)) :
    IsElemAbelian 2 (A ⊔ V) := by
  have hn : A ≤ Subgroup.normalizer (V : Set Γ) := hAV.trans (Subgroup.centralizer_le_normalizer _)
  have hAc : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a := fun a ha a' ha' =>
    GammaExtra.isMulCommutative_iff_forall.mp hA.1 a ha a' ha'
  have hVc : ∀ v ∈ V, ∀ v' ∈ V, v * v' = v' * v := fun v hv v' hv' =>
    GammaExtra.isMulCommutative_iff_forall.mp hV.1 v hv v' hv'
  have hAVc : ∀ a ∈ A, ∀ v ∈ V, a * v = v * a := fun a ha v hv =>
    (Subgroup.mem_centralizer_iff.mp (hAV ha) v hv).symm
  have hdec : ∀ x ∈ A ⊔ V, ∃ a ∈ A, ∃ v ∈ V, a * v = x := by
    intro x hx
    have hx' : x ∈ ((A ⊔ V : Subgroup Γ) : Set Γ) := hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right A V hn] at hx'
    exact hx'
  have hcomm : IsMulCommutative ↥(A ⊔ V) := by
    refine GammaExtra.isMulCommutative_iff_forall.mpr fun x hx y hy => ?_
    obtain ⟨a, ha, v, hv, rfl⟩ := hdec x hx
    obtain ⟨a', ha', v', hv', rfl⟩ := hdec y hy
    calc a * v * (a' * v') = a * (v * a') * v' := by group
      _ = a * (a' * v) * v' := by rw [hAVc a' ha' v hv]
      _ = (a * a') * (v * v') := by group
      _ = (a' * a) * (v' * v) := by rw [hAc a ha a' ha', hVc v hv v' hv']
      _ = a' * (a * v') * v := by group
      _ = a' * (v' * a) * v := by rw [hAVc a ha v' hv']
      _ = a' * v' * (a * v) := by group
  refine ⟨hcomm, fun x hx => ?_⟩
  obtain ⟨a, ha, v, hv, rfl⟩ := hdec x hx
  have h1 : (a * v) ^ 2 = a ^ 2 * v ^ 2 := by
    rw [pow_two, pow_two, pow_two]
    calc a * v * (a * v) = a * (v * a) * v := by group
      _ = a * (a * v) * v := by rw [hAVc a ha v hv]
      _ = a * a * (v * v) := by group
  rw [h1, hA.2 a ha, hV.2 v hv, one_mul]

theorem baum_not_le_centralizer {G T V : Subgroup Γ} (hT : IsSylowTwoOf T G) (hT0 : T ≠ ⊥)
    (hVG : G ≤ Subgroup.normalizer (V : Set Γ))
    (hC : G ⊓ Subgroup.centralizer (V : Set Γ) ≤ cStarIn G T) (hne : cStarIn G T ≠ G) :
    ¬ baum T ≤ Subgroup.centralizer (V : Set Γ) := by
  intro hb
  have hb0 : baum T ≠ ⊥ := C1GN.baum_ne_bot hT.2.1 hT0
  set N : Subgroup Γ := G ⊓ Subgroup.centralizer (V : Set Γ) with hN
  have hNG : N ≤ G := inf_le_left
  have hGN : G ≤ Subgroup.normalizer (N : Set Γ) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hg, B6.le_normalizer_centralizer hVG hg⟩
  have hsyl : IsSylowTwoOf (T ⊓ N) N := B6.isSylowTwoOf_inf_normal hT hNG hGN
  have hbTN : baum T ≤ T ⊓ N :=
    le_inf inf_le_left (le_inf (inf_le_left.trans hT.1) hb)
  have hbeq : baum T = baum (T ⊓ N) := baum_eq_of_le hbTN inf_le_left
  have hfr := B6.frattini_two hNG hGN hsyl
  apply hne
  refine le_antisymm (cStarIn_le G T) fun g hg => ?_
  have hKN : G ⊓ Subgroup.normalizer ((T ⊓ N : Subgroup Γ) : Set Γ) ≤
      Subgroup.normalizer (N : Set Γ) := inf_le_left.trans hGN
  have hg' : g ∈ ((G ⊓ Subgroup.normalizer ((T ⊓ N : Subgroup Γ) : Set Γ) ⊔ N : Subgroup Γ) :
      Set Γ) := by
    rw [sup_comm]
    exact hfr hg
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ N hKN] at hg'
  obtain ⟨m, hm, n, hn, rfl⟩ := hg'
  refine mul_mem ?_ (hC hn)
  refine inf_normalizer_baum_le_cStarIn hb0 ⟨hm.1, ?_⟩
  have := normalizer_le_normalizer_baum (T ⊓ N) hm.2
  rwa [← hbeq] at this

theorem thompsonJ_not_le_centralizer {T V : Subgroup Γ} (hVT : V ≤ T) (hVe : IsElemAbelian 2 V)
    (hb : ¬ baum T ≤ Subgroup.centralizer (V : Set Γ)) :
    ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set Γ) := by
  intro hJ
  obtain ⟨A, hA⟩ := exists_isMaxElemAbelian T
  have hAJ : A ≤ thompsonJ T := le_iSup₂_of_le A hA le_rfl
  have hAC : A ≤ Subgroup.centralizer (V : Set Γ) := hAJ.trans hJ
  have hel : IsElemAbelian 2 (A ⊔ V) := isElemAbelian_sup_of_le_centralizer hA.2.1 hVe hAC
  have hle : Nat.card ↥(A ⊔ V) ≤ Nat.card ↥A := hA.2.2 _ (sup_le hA.1 hVT) hel
  have heq : A ⊔ V = A := (Subgroup.eq_of_le_of_card_ge le_sup_left hle).symm
  have hVA : V ≤ A := heq ▸ le_sup_right
  have hVJ : V ≤ thompsonJ T := hVA.trans hAJ
  have hVZ : V ≤ omegaOneCenterOf (thompsonJ T) := by
    intro v hv
    refine Subgroup.subset_closure ⟨⟨hVJ hv, ?_⟩, hVe.2 v hv⟩
    exact Subgroup.mem_centralizer_iff.mpr fun y hy =>
      (Subgroup.mem_centralizer_iff.mp (hJ hy) v hv).symm
  exact hb (inf_le_right.trans (Subgroup.centralizer_le hVZ))

end Finite

end CFSG.CGT.PushingUpLit.BHS
