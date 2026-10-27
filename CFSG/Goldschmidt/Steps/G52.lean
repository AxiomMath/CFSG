module

public import CFSG.Goldschmidt.StatementsG2
import CFSG.Walter.Bender1970.S3.Tools
import CFSG.Walter.Bender1970.S1.EqualityOfMaximalFitting
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalizerEqOfNontrivialNormalInCoatom
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section1
import CFSG.FeitThompson.OddOrderTheorem
import CFSG.Goldschmidt.Steps.Balance
public import CFSG.Goldschmidt.StatementsG

public section

namespace CFSG.Goldschmidt

open CFSG.GorensteinWalter hiding oddCoreOf

namespace G52

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem orderOf_eq_two_of_mem {A : Subgroup G} (hA : CFSG.Open.IsElemAbelian 2 A) {a : G}
    (ha : a ∈ A) (ha1 : a ≠ 1) : orderOf a = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (hA.2 a ha) ha1

omit [Finite G] in
theorem isElemAbelian_conjSub_inf {A : Subgroup G} (hA : CFSG.Open.IsElemAbelian 2 A) (g : G)
    (M : Subgroup G) : CFSG.Open.IsElemAbelian 2 (conjSub g A ⊓ M) := by
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · have h : (g * x * g⁻¹) * (g * y * g⁻¹) = (g * y * g⁻¹) * (g * x * g⁻¹) :=
      congrArg Subtype.val (hA.1.is_comm.comm ⟨_, mem_conjSub.1 x.2.1⟩ ⟨_, mem_conjSub.1 y.2.1⟩)
    show (x : G) * y = y * x
    calc (x : G) * y = g⁻¹ * ((g * x * g⁻¹) * (g * y * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * y * g⁻¹) * (g * x * g⁻¹)) * g := by rw [h]
      _ = y * x := by group
  · have h := hA.2 _ (mem_conjSub.1 hx.1)
    rw [conj_pow] at h
    exact conj_eq_one_iff.mp h

omit [Finite G] in
theorem isComponentOf_componentLayerOf {H K : Subgroup G} (hK : IsComponentOf K H) :
    IsComponentOf K (componentLayerOf H) := by
  have hKE : K ≤ componentLayerOf H := le_sSup hK
  exact ⟨hKE, Walter.isSubnormal_subgroupOf_of_le hKE (componentLayerOf_isNormalIn H).1 hK.2.1,
    hK.2.2⟩

omit [Finite G] in
theorem componentLayerOf_componentLayerOf (H : Subgroup G) :
    componentLayerOf (componentLayerOf H) = componentLayerOf H :=
  le_antisymm (componentLayerOf_isNormalIn _).1
    (sSup_le fun _ hK => le_sSup (isComponentOf_componentLayerOf hK))

omit [Finite G] in
theorem componentLayerOf_eq_sup (H : Subgroup G) :
    componentLayerOf H = componentLayerOf (componentLayerOf H) ⊔
      oddCoreOf (CFSG.fittingSubgroupOf (componentLayerOf H)) := by
  rw [componentLayerOf_componentLayerOf]
  exact (sup_eq_left.mpr ((Subgroup.map_subtype_le _).trans (Subgroup.map_subtype_le _))).symm

omit [Finite G] in
theorem oddCoreOf_eq_self_of_odd {P : Subgroup G} (hodd : Odd (Nat.card P)) :
    oddCoreOf P = P := by
  have htop : CFSG.Open.goldschmidtOddCore P = ⊤ :=
    top_le_iff.mp (le_sSup ⟨inferInstance, by rwa [Subgroup.card_top]⟩)
  rw [oddCoreOf, htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem eq_componentLayerOf_sup_of_isPGroup {P : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hPp : IsPGroup p P) (hodd : Odd (Nat.card P)) :
    P = componentLayerOf P ⊔ oddCoreOf (CFSG.fittingSubgroupOf P) := by
  have : Fact p.Prime := ⟨hp⟩
  have hE : componentLayerOf P = ⊥ :=
    componentLayerOf_eq_bot_of_isPGroup P hp (hPp.to_le (generalizedFittingSubgroupOf_le P))
  rw [hE, Walter.fittingSubgroupOf_eq_self_of_isNilpotent hPp.isNilpotent, bot_sup_eq,
    oddCoreOf_eq_self_of_odd hodd]

theorem isPGroup_of_card_primesOfOrder_le_one {X P : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hX : Nat.card (primesOfOrder X) ≤ 1) (hPX : P ≤ X) (hPp : IsPGroup p P) (hP1 : P ≠ ⊥) :
    IsPGroup p X := by
  have hX1 : X ≠ ⊥ := fun h => hP1 (le_bot_iff.mp (h ▸ hPX))
  obtain ⟨r, hr, hXr, -, -⟩ := Walter.exists_isPGroup_of_card_primesOfOrder_eq_one
    (le_antisymm hX (Walter.one_le_card_primesOfOrder hX1))
  rw [Walter.eq_of_isPGroup_of_isPGroup hp hr hPp (hXr.to_le hPX) hP1]
  exact hXr

theorem le_centralizer_oddCoreOf_of_isPerfect {M P : Subgroup G} (hPM : P ≤ M)
    (hP : Group.IsPerfect P)
    (hPF : P ≤ Subgroup.centralizer (CFSG.fittingSubgroupOf M : Set G)) :
    P ≤ Subgroup.centralizer (oddCoreOf M : Set G) := by
  set O := oddCoreOf M with hOdef
  set F := CFSG.fittingSubgroupOf O with hFdef
  have hOsolv : Group.IsSolvable O := CFSG.FeitThompson.isSolvable_of_odd_natCard O (Balance.odd_card_oddCoreOf M)
  have hOn : IsNormalIn O M :=
    ⟨Subgroup.map_subtype_le _, fun _ hh _ hy => Balance.conj_mem_oddCoreOf hh hy⟩
  have hFM : F ≤ CFSG.fittingSubgroupOf M :=
    Walter.fittingSubgroupOf_le_of_isSubnormal hOn.1
      (Walter.isSubnormal_subgroupOf_of_isNormalIn hOn)
  have hPFO : P ≤ Subgroup.centralizer (F : Set G) := hPF.trans (Subgroup.centralizer_le hFM)
  have hFn : IsNormalIn F O := fittingSubgroupOf_isNormalIn O
  have hOP : ⁅O, P⁆ ≤ O := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    have hyO : y * x⁻¹ * y⁻¹ ∈ O := hOn.2 y (hPM hy) _ (O.inv_mem hx)
    rw [commutatorElement_def, mul_assoc, mul_assoc]
    exact O.mul_mem hx (by simpa [mul_assoc] using hyO)
  have hFO : ⁅F, O⁆ ≤ F := by
    rw [Subgroup.commutator_le]
    intro f hf o ho
    have hoF : o * f⁻¹ * o⁻¹ ∈ F := hFn.2 o ho _ (F.inv_mem hf)
    rw [commutatorElement_def, mul_assoc, mul_assoc]
    exact F.mul_mem hf (by simpa [mul_assoc] using hoF)
  have h1 : ⁅⁅P, F⁆, O⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hPFO, Subgroup.commutator_bot_left]
  have h2 : ⁅⁅F, O⁆, P⁆ = ⊥ :=
    le_bot_iff.mp ((Subgroup.commutator_mono hFO le_rfl).trans
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
        (Subgroup.le_centralizer_iff.mp hPFO)).le)
  have h3 : ⁅⁅O, P⁆, F⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  have hOPF : ⁅O, P⁆ ≤ F :=
    (le_inf hOP (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h3)).trans
      (fact_1_2_centralizer_fitting_le_fitting O hOsolv)
  have h4 : ⁅⁅O, P⁆, P⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    (hOPF.trans (Subgroup.le_centralizer_iff.mp hPFO))
  have h5 : ⁅⁅P, O⁆, P⁆ = ⊥ := by rw [Subgroup.commutator_comm P O]; exact h4
  have h6 : ⁅⁅P, P⁆, O⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h5 h4
  rw [Subgroup.isPerfect_iff.mp hP] at h6
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h6

end G52

open G52 in
theorem G52_of (h37 : S_G37) : S_G52 := by
  intro G _ _ S A hset a ha ha1 H hH Y hY1 hYF hYsn hCY
  have hsimple := hset.isSimpleGroup
  have ht : orderOf a = 2 := orderOf_eq_two_of_mem hset.elem ha ha1
  obtain ⟨hHco, hCH, hcase⟩ := hH
  have haC : a ∈ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have haH : a ∈ H := hCH haC
  refine ⟨hY1, hYF, hYsn, hCY haC, fun M hM hNM => ?_⟩
  by_cases hMH : M = H
  · exact Or.inl hMH
  right
  have hFH : generalizedFittingSubgroupOf H ≤ H := generalizedFittingSubgroupOf_le H
  have hVCB : Y ⊔ Subgroup.centralizer (Y : Set G) ≤ M :=
    (Walter.sup_centralizer_le_normalizer Y).trans hNM
  have hSF := Walter.subnormalHull_le_generalizedFitting hYF
  have hSsn := Walter.isSubnormal_subnormalHull hYF hYsn
  have hSC := Walter.generalizedFitting_inf_centralizer_subnormalHull_le H Y
  have hSB : Walter.subnormalHull H Y ≤ M :=
    (Walter.subnormalHull_le_sup_centralizer hYF hYsn).trans hVCB
  have hCM : Subgroup.centralizer ({a} : Set G) ≤ M := hCY.trans hNM
  have haM : a ∈ M := hCM haC
  obtain ⟨g, hAg, hstar⟩ := hset.sstar M hM.1
  have h37M := h37 G M (conjSub g A ⊓ M) hstar (isElemAbelian_conjSub_inf hset.elem g M) a
    ⟨hAg ⟨ha, haM⟩, haM⟩ ha1
  rcases hcase with ⟨p, hp, hne, hfix⟩ | ⟨hnone, hmax⟩
  ·
    obtain ⟨-, -, hodd, hPt, hPcent⟩ := Walter.qCoreOf_props_of_fixedPointFree haH ht hp hfix
    have hPn : IsNormalIn (qCoreOf H p) H := qCoreOf_normal_in H p
    have hPp : IsPGroup p (qCoreOf H p) := qCoreOf_isPGroup H p
    have hPM : qCoreOf H p ≤ M :=
      ((Subgroup.le_centralizer_iff.mp hPcent).trans (Subgroup.centralizer_le hYF)).trans
        (le_sup_right.trans hVCB)
    have hPC : M ⊓ Subgroup.centralizer ({a} : Set G) ≤
        Subgroup.normalizer (qCoreOf H p : Set G) :=
      inf_le_right.trans (hCH.trans (le_normalizer_of_isNormalIn hPn))
    obtain ⟨⟨hPFM, hPsnM⟩, -⟩ :=
      h37M (qCoreOf H p) hPM hPC (eq_componentLayerOf_sup_of_isPGroup hp hPp hodd)
    rw [hPt] at hPFM hPsnM
    have hNP : Subgroup.normalizer (qCoreOf H p : Set G) = H :=
      normalizer_eq_of_nontrivial_normal_in_coatom hsimple hHco hPn.1 hne
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hPn.1).mpr
          (le_normalizer_of_isNormalIn hPn))
    have hSbar : Walter.subnormalHull M (qCoreOf H p) ≤ H :=
      (Walter.subnormalHull_le_sup_centralizer hPFM hPsnM).trans
        ((Walter.sup_centralizer_le_normalizer _).trans hNP.le)
    have hpi : ¬ (2 ≤ Nat.card (primesOfOrder (generalizedFittingSubgroupOf H)) ∨
        2 ≤ Nat.card (primesOfOrder (generalizedFittingSubgroupOf M))) := fun hpi =>
      hMH (bender1970_1_7_iii_equalityOfMaximal hsimple H hHco _ hSF hSsn hSC hSB hM hpi
        ⟨Walter.subnormalHull M (qCoreOf H p), hSbar,
          Walter.subnormalHull_le_generalizedFitting hPFM,
          Walter.isSubnormal_subnormalHull hPFM hPsnM,
          Walter.generalizedFitting_inf_centralizer_subnormalHull_le M _⟩).symm
    rw [not_or] at hpi
    have hPFH : qCoreOf H p ≤ generalizedFittingSubgroupOf H :=
      (qCoreOf_le_fittingSubgroupOf H p hp).trans le_sup_left
    exact ⟨p, hp, isPGroup_of_card_primesOfOrder_le_one hp (by omega) hPFM hPp hne,
      isPGroup_of_card_primesOfOrder_le_one hp (by omega) hPFH hPp hne⟩
  ·
    have hO : ∀ q : ℕ, q.Prime → q ∉ primesOfOrder (CFSG.fittingSubgroupOf H) →
        qCoreOf M q = ⊥ := by
      intro q hq hqπ
      by_contra hne
      have h1 := Walter.qCoreOf_inf_eq_bot_of_sup_centralizer_le hsimple hHco hYF hYsn hVCB hq hqπ
      refine hnone M hM hCM ⟨q, hq, hne, eq_bot_iff.mpr fun x hx => ?_⟩
      rw [← h1]
      exact ⟨hx.1, hCH hx.2⟩
    have hE := hmax M hM hCM
    by_cases hpi : 2 ≤ Nat.card (primesOfOrder (generalizedFittingSubgroupOf H)) ∨
        2 ≤ Nat.card (primesOfOrder (generalizedFittingSubgroupOf M))
    · exfalso
      apply hMH
      have hFMH : CFSG.fittingSubgroupOf M ≤ H :=
        Walter.fittingSubgroupOf_le_of_pResidualOf_ne_bot hsimple H hHco _ hSF hSsn hSC hSB
          (fun _ hq _ => Walter.pResidualOf_generalizedFittingSubgroupOf_ne_bot H M hpi hE hO hq)
          hO
      have hFME : CFSG.fittingSubgroupOf M ≤ Subgroup.centralizer (componentLayerOf H : Set G) :=
        Walter.fittingSubgroupOf_le_centralizer_componentLayerOf hsimple H hHco _ hSF hSsn hSC hSB
          hO
      have hEHM : componentLayerOf H ≤ M :=
        (Walter.componentLayerOf_le_subnormalHull H Y).trans hSB
      have hEO : componentLayerOf H ≤ Subgroup.centralizer (oddCoreOf M : Set G) :=
        le_centralizer_oddCoreOf_of_isPerfect hEHM (componentLayerOf_isPerfect H)
          (Subgroup.le_centralizer_iff.mp hFME)
      have hEC : M ⊓ Subgroup.centralizer ({a} : Set G) ≤
          Subgroup.normalizer (componentLayerOf H : Set G) :=
        inf_le_right.trans (hCH.trans (le_normalizer_of_isNormalIn (componentLayerOf_isNormalIn H)))
      obtain ⟨-, h2, -⟩ := h37M (componentLayerOf H) hEHM hEC (componentLayerOf_eq_sup H)
      have hEEM : componentLayerOf H ≤ componentLayerOf M := by
        refine sSup_le fun K hK => ?_
        obtain ⟨L, hL, hKL, -⟩ :=
          h2 K (isComponentOf_componentLayerOf hK) ((le_sSup hK).trans hEO)
        exact hKL.trans (le_sSup hL)
      have hEeq : componentLayerOf H = componentLayerOf M := Subgroup.eq_of_le_of_card_ge hEEM hE
      have hFsMH : generalizedFittingSubgroupOf M ≤ H := by
        refine sup_le hFMH ?_
        rw [← hEeq]
        exact le_sup_right.trans hFH
      exact (bender1970_1_7_iii_equalityOfMaximal hsimple H hHco _ hSF hSsn hSC hSB hM hpi
        ⟨generalizedFittingSubgroupOf M, hFsMH, le_rfl, by
          rw [Subgroup.subgroupOf_self]; exact Subgroup.IsSubnormal.top, inf_le_left⟩).symm
    ·
      rw [not_or] at hpi
      have hH1 : H ≠ ⊥ := fun h => ha1 (Subgroup.mem_bot.mp (h ▸ haH))
      have hM1 : M ≠ ⊥ := fun h => ha1 (Subgroup.mem_bot.mp (h ▸ haM))
      obtain ⟨p, hp, hFp, -, -⟩ := Walter.exists_isPGroup_of_card_primesOfOrder_eq_one
        (le_antisymm (by omega)
          (Walter.one_le_card_primesOfOrder (Walter.generalizedFittingSubgroupOf_ne_bot hH1)))
      obtain ⟨r, hr, hFr, hF1, -⟩ := Walter.exists_isPGroup_of_card_primesOfOrder_eq_one
        (le_antisymm (by omega)
          (Walter.one_le_card_primesOfOrder (Walter.generalizedFittingSubgroupOf_ne_bot hM1)))
      have hEM : componentLayerOf M = ⊥ := componentLayerOf_eq_bot_of_isPGroup M hr hFr
      have hOr : qCoreOf M r = CFSG.fittingSubgroupOf M :=
        qCoreOf_eq_fittingSubgroupOf_of_isPGroup M hr hFr
      have hOr1 : qCoreOf M r ≠ ⊥ := by
        rw [hOr]
        intro h
        apply hF1
        rw [generalizedFittingSubgroupOf, hEM,
          show CFSG.GorensteinWalter.fittingSubgroupOf M = ⊥ from h, sup_bot_eq]
      have hrπ : r ∈ primesOfOrder (CFSG.fittingSubgroupOf H) := by
        by_contra h
        exact hOr1 (hO r hr h)
      have hrp : r = p := Walter.primesOfOrder_subset_of_isPGroup hp (hFp.to_le le_sup_left) hrπ
      subst hrp
      exact ⟨r, hr, hFr, hFp⟩

end CFSG.Goldschmidt
