module

public import CFSG.Goldschmidt.Steps.G37Lift
public import CFSG.Goldschmidt.Steps.G37Odd
import CFSG.Goldschmidt.Steps.Completion
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.CommutatorSupLeOfCommutatorLeAndNormalize
public import CFSG.Goldschmidt.Steps.G37Fit

public section

namespace CFSG.Goldschmidt.G37

open CFSG.GorensteinWalter
open CFSG.Open (goldschmidtOddCore goldschmidtLayer)
open scoped commutatorElement

section Moved

variable {G : Type} [Group G]

@[expose] def movedComponents (X : Subgroup G) (a : G) : Set (Subgroup G) :=
  {K | IsComponentOf K X ∧ ¬ K ≤ Subgroup.centralizer ({a} : Set G)}

@[expose] def movedLayer (X : Subgroup G) (a : G) : Subgroup G := sSup (movedComponents X a)

theorem movedLayer_le (X : Subgroup G) (a : G) : movedLayer X a ≤ X :=
  sSup_le fun _ hK => hK.1.1

theorem le_movedLayer {X K : Subgroup G} {a : G} (hK : K ∈ movedComponents X a) :
    K ≤ movedLayer X a :=
  le_sSup hK

theorem isComponentOf_movedLayer {X K : Subgroup G} {a : G} (hK : K ∈ movedComponents X a) :
    IsComponentOf K (movedLayer X a) :=
  isComponentOf_of_le hK.1 (le_movedLayer hK) (movedLayer_le X a)

theorem isPerfect_movedLayer (X : Subgroup G) (a : G) : Group.IsPerfect (movedLayer X a) := by
  have h : componentLayerOf (movedLayer X a) = movedLayer X a :=
    le_antisymm (sSup_le fun _ hK => hK.1)
      (sSup_le fun _ hK => le_sSup (isComponentOf_movedLayer hK))
  rw [← h]
  exact isPerfect_componentLayerOf _

theorem map_conj_mem_movedComponents {X K : Subgroup G} {a c : G}
    (hcX : c ∈ Subgroup.normalizer (X : Set G)) (hca : c * a = a * c)
    (hK : K ∈ movedComponents X a) : K.map (MulAut.conj c).toMonoidHom ∈ movedComponents X a := by
  refine ⟨CFSG.Walter.isComponentOf_map_conj hK.1 hcX, fun h => hK.2 fun k hk => ?_⟩
  have h1 := h ⟨k, hk, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff] at h1 ⊢
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1
  have hca' : c⁻¹ * a * c = a := by
    rw [mul_assoc, ← hca, ← mul_assoc, inv_mul_cancel, one_mul]
  calc k * a = k * (c⁻¹ * a * c) := by rw [hca']
    _ = c⁻¹ * ((c * k * c⁻¹) * a) * c := by group
    _ = c⁻¹ * (a * (c * k * c⁻¹)) * c := by rw [h1]
    _ = (c⁻¹ * a * c) * k := by group
    _ = a * k := by rw [hca']

theorem mem_normalizer_movedLayer {X : Subgroup G} {a c : G}
    (hcX : c ∈ Subgroup.normalizer (X : Set G)) (hca : c * a = a * c) :
    c ∈ Subgroup.normalizer (movedLayer X a : Set G) :=
  CFSG.Walter.mem_normalizer_sSup_of_map_mem
    (fun _ hK => map_conj_mem_movedComponents hcX hca hK)
    (fun _ hK => map_conj_mem_movedComponents (Subgroup.inv_mem _ hcX)
      (show Commute c a from hca).inv_left hK)

variable [Finite G]

theorem commutator_movedLayer {X : Subgroup G} {a : G}
    (haX : a ∈ Subgroup.normalizer (X : Set G)) :
    ⁅movedLayer X a, Subgroup.zpowers a⁆ = movedLayer X a := by
  have haW : a ∈ Subgroup.normalizer (movedLayer X a : Set G) := mem_normalizer_movedLayer haX rfl
  have hVW := CFSG.Walter.commutator_zpowers_le_of_mem_normalizer haW
  refine le_antisymm hVW (sSup_le fun K hK => ?_)
  rcases CFSG.Walter.isComponentOf_le_or_commutator_eq_bot (isComponentOf_movedLayer hK) hVW
      (Subgroup.normalizer_commutator_ge_left _ _) with h | h
  · exact h
  · exfalso
    apply hK.2
    rw [← CFSG.Walter.centralizer_zpowers_eq', ← Subgroup.commutator_eq_bot_iff_le_centralizer]
    apply CFSG.LocalCores.perfect_double_commutator (Group.isPerfect_def.mpr hK.1.2.2.2.1)
    rw [← le_bot_iff, Subgroup.commutator_comm]
    calc ⁅K, ⁅K, Subgroup.zpowers a⁆⁆ ≤ ⁅K, ⁅movedLayer X a, Subgroup.zpowers a⁆⁆ :=
          Subgroup.commutator_mono le_rfl (Subgroup.commutator_mono (le_movedLayer hK) le_rfl)
      _ = ⊥ := h

end Moved

variable {G : Type} [Group G] [Finite G] {H A : Subgroup G} {a : G} {X : Subgroup G}

theorem inf_centralizer_le_centralizer_movedLayer (hXH : X ≤ H)
    (hXa : H ⊓ Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (X : Set G)) :
    oddCoreOf H ⊓ Subgroup.centralizer ({a} : Set G) ≤
      Subgroup.centralizer (movedLayer X a : Set G) := by
  intro c hc
  obtain ⟨hcV, hca⟩ := Subgroup.mem_inf.mp hc
  have hVH : oddCoreOf H ≤ H := Subgroup.map_subtype_le _
  have hcH : c ∈ H := hVH hcV
  have hcX : c ∈ Subgroup.normalizer (X : Set G) := hXa (Subgroup.mem_inf.mpr ⟨hcH, hca⟩)
  have hca' : c * a = a * c := Subgroup.mem_centralizer_singleton_iff.mp hca
  have hHV := Completion.le_normalizer_oddCoreOf H
  have key : ∀ K ∈ movedComponents X a, c ∈ Subgroup.centralizer (K : Set G) := by
    intro K hK
    have hKH : K ≤ H := hK.1.1.trans hXH
    set K' := K.map (MulAut.conj c).toMonoidHom with hK'def
    have hK' : K' ∈ movedComponents X a := map_conj_mem_movedComponents hcX hca' hK
    have hK'H : K' ≤ H := hK'.1.1.trans hXH
    have hKK' : K' = K := by
      rcases CFSG.Walter.isComponentOf_eq_or_commutator_eq_bot hK'.1 hK.1 with h | h
      · exact h
      · exfalso
        have hK'K : K' ≤ K ⊔ oddCoreOf H := by
          rintro _ ⟨k, hk, rfl⟩
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          have h1 : c * k * c⁻¹ * k⁻¹ ∈ oddCoreOf H := by
            rw [show c * k * c⁻¹ * k⁻¹ = c * (k * c⁻¹ * k⁻¹) by group]
            exact (oddCoreOf H).mul_mem hcV ((Subgroup.mem_normalizer_iff.mp (hHV (hKH hk))
              c⁻¹).mp ((oddCoreOf H).inv_mem hcV))
          rw [show c * k * c⁻¹ = (c * k * c⁻¹ * k⁻¹) * k by group]
          exact Subgroup.mul_mem _ (Subgroup.mem_sup_right h1) (Subgroup.mem_sup_left hk)
        have hb1 : barOf H K' ≤ barOf H K := by
          calc barOf H K' ≤ barOf H (K ⊔ oddCoreOf H) := barOf_mono hK'K
            _ = barOf H K ⊔ barOf H (oddCoreOf H) := barOf_sup hKH hVH
            _ = barOf H K := by rw [(barOf_eq_bot_iff hVH).mpr le_rfl, sup_bot_eq]
        have hb2 : ⁅barOf H K', barOf H K⁆ = ⊥ := by
          rw [← barOf_commutator hK'H hKH, h]
          exact (barOf_eq_bot_iff bot_le).mpr bot_le
        exact not_le_centralizer_self (isComponentOf_barOf' hXH hK'.1).2.2
          ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp hb2).trans
            (Subgroup.centralizer_le hb1))
    have hcK : c ∈ Subgroup.normalizer (K : Set G) := mem_normalizer_of_map_conj_eq hKK'
    have hKV : K ⊓ oddCoreOf H ≤ Subgroup.centralizer (K : Set G) := by
      rcases eq_or_le_centralizer_of_le_normalizer hK.1.2.2 inf_le_left (fun k hk =>
          Subgroup.inf_normalizer_le_normalizer_inf
            ⟨Subgroup.le_normalizer hk, hHV (hKH hk)⟩) with h | h
      · exact absurd (h ▸ inf_le_right) (not_le_oddCoreOf hK.1.2.2)
      · exact h
    have h1 : ⁅K, Subgroup.zpowers c⁆ ≤ K ⊓ oddCoreOf H := by
      rw [Subgroup.commutator_le]
      intro k hk z hz
      have hzK : z ∈ Subgroup.normalizer (K : Set G) := Subgroup.zpowers_le.mpr hcK hz
      have hzV : z ∈ oddCoreOf H := Subgroup.zpowers_le.mpr hcV hz
      rw [commutatorElement_def]
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · rw [show k * z * k⁻¹ * z⁻¹ = k * (z * k⁻¹ * z⁻¹) by group]
        exact K.mul_mem hk ((Subgroup.mem_normalizer_iff.mp hzK k⁻¹).mp (K.inv_mem hk))
      · exact (oddCoreOf H).mul_mem ((Subgroup.mem_normalizer_iff.mp (hHV (hKH hk)) z).mp hzV)
          ((oddCoreOf H).inv_mem hzV)
    have h2 : ⁅⁅K, Subgroup.zpowers c⁆, K⁆ = ⊥ := by
      rw [eq_bot_iff]
      calc ⁅⁅K, Subgroup.zpowers c⁆, K⁆ ≤ ⁅K ⊓ oddCoreOf H, K⁆ :=
            Subgroup.commutator_mono h1 le_rfl
        _ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hKV
        _ ≤ ⊥ := le_rfl
    have h4 := Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (CFSG.LocalCores.perfect_double_commutator (Group.isPerfect_def.mpr hK.1.2.2.2.1) h2)
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact (Subgroup.mem_centralizer_iff.mp (h4 hk) c (Subgroup.mem_zpowers c)).symm
  have hW : movedLayer X a ≤ Subgroup.centralizer ({c} : Set G) :=
    sSup_le fun K hK k hk => Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp (key K hK) k hk)
  exact Subgroup.mem_centralizer_iff.mpr fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.mp (hW hw)

theorem movedLayer_le_centralizer (hXH : X ≤ H)
    (hXa : H ⊓ Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (X : Set G))
    (haH : a ∈ H) (ha2 : a ^ 2 = 1) (ha1 : a ≠ 1) :
    oddCoreOf H ≤ Subgroup.centralizer (movedLayer X a : Set G) := by
  have haX : a ∈ Subgroup.normalizer (X : Set G) :=
    hXa (Subgroup.mem_inf.mpr ⟨haH, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩)
  have hHV := Completion.le_normalizer_oddCoreOf H
  exact le_centralizer_of_inf_centralizer_le (orderOf_eq_prime ha2 ha1)
    (isPerfect_movedLayer X a) (commutator_movedLayer haX) (oddCoreOf H)
    (Completion.odd_card_oddCoreOf H) (((movedLayer_le X a).trans hXH).trans hHV) (hHV haH)
    (inf_centralizer_le_centralizer_movedLayer hXH hXa)

variable (h31 : S_G31) (h32Q : S_G32Q) (h33 : S_G33) (h34 : S_G34) (h35 : S_G35)
  (hS : IsSStarIn H A) (hE : CFSG.Open.IsElemAbelian 2 A) (haA : a ∈ A) (hXH : X ≤ H)
  (hXa : H ⊓ Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (X : Set G))
  (hXE : X = componentLayerOf X ⊔ oddCoreOf (CFSG.fittingSubgroupOf X))

include h31 h32Q h33 h34 h35 hS hE haA hXH hXa hXE

theorem isComponentOf_of_mem_movedComponents (ha1 : a ≠ 1) {K : Subgroup G}
    (hK : K ∈ movedComponents X a) : IsComponentOf K H := by
  obtain ⟨hO, hS', hE', hā, hXba, hXbE⟩ := bar_setting hS hE haA hXH hXa hXE
  have haH : a ∈ H := hS.1 haA
  have hKH : K ≤ H := hK.1.1.trans hXH
  have hKp : Group.IsPerfect K := Group.isPerfect_def.mpr hK.1.2.2.2.1
  have hKO : K ≤ Subgroup.centralizer (oddCoreOf H : Set G) :=
    Subgroup.le_centralizer_iff.mp ((movedLayer_le_centralizer hXH hXa haH (hE.2 a haA) ha1).trans
      (Subgroup.centralizer_le (le_movedLayer hK)))
  obtain ⟨Lb, hLb, hKLb, hcase⟩ :=
    core_component h31 h32Q h33 h34 h35 hO hS' hE' hā hXba hXbE (isComponentOf_barOf' hXH hK.1)
  have heq : barOf H K = Lb := by
    rcases hcase with h | ⟨-, hKa, -, -⟩
    · exact h
    · exfalso
      have h1 := commutator_le_oddCoreOf_of_barOf_le hKH haH hKa
      have haX : Subgroup.zpowers a ≤ Subgroup.normalizer (X : Set G) :=
        Subgroup.zpowers_le.mpr (hXa (Subgroup.mem_inf.mpr
          ⟨haH, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩))
      rcases le_commutator_or_commutator_eq_bot hK.1 haX with h | h
      · exact not_le_oddCoreOf hK.1.2.2 (h.trans h1)
      · apply hK.2
        rw [← CFSG.Walter.centralizer_zpowers_eq']
        exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
  obtain ⟨L, hL, hLLb, hlift⟩ :=
    exists_isComponentOf_of_le_barOf hLb (heq ▸ barOf_mono (le_inf hKH hKO))
  have hKL : K ≤ L := hlift K hKH hKO hKp heq.le
  rwa [eq_of_barOf_eq hKL hKH hL.1 (Group.isPerfect_def.mpr hL.2.2.2.1) hKO
    (hLLb.trans heq.symm)]

theorem part1 (ha1 : a ≠ 1) :
    ⁅X, Subgroup.zpowers a⁆ ≤ generalizedFittingSubgroupOf H ∧
      (⁅X, Subgroup.zpowers a⁆.subgroupOf (generalizedFittingSubgroupOf H)).IsSubnormal := by
  obtain ⟨hO, hS', hE', hā, hXba, hXbE⟩ := bar_setting hS hE haA hXH hXa hXE
  have haH : a ∈ H := hS.1 haA
  have ha2 : a ^ 2 = 1 := hE.2 a haA
  set Y := oddCoreOf (CFSG.fittingSubgroupOf X) with hY
  set W := movedLayer X a with hW
  set Fs := generalizedFittingSubgroupOf H with hFs
  set F := CFSG.fittingSubgroupOf H with hF
  set E := componentLayerOf H with hEdef
  have hYX : Y ≤ X := oddFit_le X
  have hYH : Y ≤ H := hYX.trans hXH
  have haX : a ∈ Subgroup.normalizer (X : Set G) :=
    hXa (Subgroup.mem_inf.mpr ⟨haH, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩)
  have haY : a ∈ Subgroup.normalizer (Y : Set G) := normalizer_le_normalizer_oddFit X haX
  have hZH : Subgroup.zpowers a ≤ H := Subgroup.zpowers_le.mpr haH
  have hYa : ⁅Y, Subgroup.zpowers a⁆ ≤ oddCoreOf H := by
    rw [← barOf_eq_bot_iff ((Subgroup.commutator_mono hYH hZH).trans (commutator_self_le H)),
      barOf_commutator hYH hZH, barOf_zpowers haH, eq_bot_iff]
    calc ⁅barOf H Y, Subgroup.zpowers (QuotientGroup.mk' (goldschmidtOddCore H) ⟨a, haH⟩)⁆ ≤
          ⁅oddCoreOf (CFSG.fittingSubgroupOf (barOf H X)),
            Subgroup.zpowers (QuotientGroup.mk' (goldschmidtOddCore H) ⟨a, haH⟩)⁆ :=
          Subgroup.commutator_mono (barOf_oddFit_le hXH) le_rfl
      _ = ⊥ := core_commutator_oddFit h31 h32Q h33 h34 h35 hO hS' hE' hā hXba hXbE
      _ ≤ ⊥ := le_rfl
  have hYF : ⁅Y, Subgroup.zpowers a⁆ ≤ F := commutator_oddFit_le_fitting haH ha2 ha1 hXH hXa hYa
  have hcomp : ∀ K ∈ movedComponents X a, IsComponentOf K H := fun K hK =>
    isComponentOf_of_mem_movedComponents h31 h32Q h33 h34 h35 hS hE haA hXH hXa hXE ha1 hK
  have hWE : W ≤ E := sSup_le fun K hK => le_sSup (hcomp K hK)
  set J := ⁅Y, Subgroup.zpowers a⁆ ⊔ W with hJ
  have hYaY : ⁅Y, Subgroup.zpowers a⁆ ≤ Y := CFSG.Walter.commutator_zpowers_le_of_mem_normalizer haY
  have hYs : Group.IsSolvable Y := by
    have := isNilpotent_oddFit X
    infer_instance
  have hXY : X ≤ Subgroup.normalizer (Y : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_oddFit X)
  have hKY : ∀ K : Subgroup G, IsComponentOf K X → K ≤ Subgroup.centralizer (Y : Set G) :=
    fun K hK => Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (CFSG.Walter.isComponentOf_commutator_eq_bot_of_isSolvable hK hYs hYX hXY)
  have hEXY : componentLayerOf X ≤ Subgroup.centralizer (Y : Set G) :=
    sSup_le fun K hK => hKY K hK
  have hEXJ : componentLayerOf X ≤ Subgroup.normalizer (J : Set G) := fun e he =>
    CFSG.Walter.mem_normalizer_sup
      (Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun x hx =>
        Subgroup.mem_centralizer_iff.mp (hEXY he) x (hYaY hx)))
      (CFSG.Walter.mem_normalizer_sSup fun K hK =>
        CFSG.Walter.componentLayerOf_le_normalizer_of_isComponentOf hK.1 he)
  have hYJ : Y ≤ Subgroup.normalizer (J : Set G) := fun y hy =>
    CFSG.Walter.mem_normalizer_sup (Subgroup.normalizer_commutator_ge_left Y _ hy)
      (CFSG.Walter.mem_normalizer_sSup fun K hK => Subgroup.centralizer_le_normalizer _
        (Subgroup.le_centralizer_iff.mp (hKY K hK.1) hy))
  have hXaJ : ⁅X, Subgroup.zpowers a⁆ ≤ J := by
    refine (Subgroup.commutator_mono hXE.le le_rfl).trans ?_
    refine commutator_sup_le_of_commutator_le_and_normalize _ _ _ J ?_ le_sup_left hEXJ hYJ
    refine CFSG.Walter.commutator_sSup_le _ _ _ (fun K hK => ?_)
      (fun K hK => (hK.1.trans hXE.le).trans (sup_le hEXJ hYJ))
    by_cases hKa : K ≤ Subgroup.centralizer ({a} : Set G)
    · rw [Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
        (by rw [CFSG.Walter.centralizer_zpowers_eq']; exact hKa)]
      exact bot_le
    · calc ⁅K, Subgroup.zpowers a⁆ ≤ ⁅W, Subgroup.zpowers a⁆ :=
            Subgroup.commutator_mono (le_movedLayer ⟨hK, hKa⟩) le_rfl
        _ = W := commutator_movedLayer haX
        _ ≤ J := le_sup_right
  have hFsH : Fs ≤ H := sup_le (CFSG.fittingSubgroupOf_le H) (sSup_le fun K hK => hK.1)
  have hFFs : F ≤ Fs := le_sup_left
  have hEFs : E ≤ Fs := le_sup_right
  have hYaFs : ⁅Y, Subgroup.zpowers a⁆ ≤ Fs := hYF.trans hFFs
  have hWFs : W ≤ Fs := hWE.trans hEFs
  have hJFs : J ≤ Fs := sup_le hYaFs hWFs
  have hFn : (F.subgroupOf Fs).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hFFs).mpr
      (hFsH.trans (Subgroup.le_normalizer.trans (normalizer_le_normalizer_fitting H)))
  have hEn : (E.subgroupOf Fs).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hEFs).mpr
      (hFsH.trans (le_normalizer_of_isNormalIn (componentLayerOf_isNormalIn H)))
  have hAsn : (⁅Y, Subgroup.zpowers a⁆.subgroupOf Fs).IsSubnormal :=
    CFSG.Walter.isSubnormal_subgroupOf_trans hYF
      (isSubnormal_of_nilpotent (CFSG.fittingSubgroupOf_isNilpotent H) _ hYF) hFn.isSubnormal
  have hWsn : (W.subgroupOf Fs).IsSubnormal := by
    refine CFSG.Walter.isSubnormal_subgroupOf_trans hWE ?_ hEn.isSubnormal
    refine CFSG.Walter.isSubnormal_subgroupOf_of_le_normalizer hWE fun e he => ?_
    exact CFSG.Walter.mem_normalizer_sSup fun K hK =>
      CFSG.Walter.componentLayerOf_le_normalizer_of_isComponentOf (hcomp K hK) he
  have hJsn : (J.subgroupOf Fs).IsSubnormal := by
    rw [hJ, Subgroup.subgroupOf_sup hYaFs hWFs]
    exact CFSG.GroupTheory.isSubnormal_sup hAsn hWsn
  have hJX : J ≤ X := sup_le (hYaY.trans hYX) (movedLayer_le X a)
  refine ⟨hXaJ.trans hJFs, CFSG.Walter.isSubnormal_subgroupOf_trans hXaJ ?_ hJsn⟩
  exact CFSG.Walter.isSubnormal_subgroupOf_of_le_normalizer hXaJ
    (hJX.trans (Subgroup.normalizer_commutator_ge_left X _))

end CFSG.Goldschmidt.G37
