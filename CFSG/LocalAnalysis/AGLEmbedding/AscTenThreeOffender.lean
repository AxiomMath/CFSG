module

public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
public import CFSG.Quasithin.Background.B2Thompson
import CFSG.LocalAnalysis.AGLEmbedding.AscTenThreeModule
import CFSG.LocalAnalysis.AGLEmbedding.AscEightFourAux
import CFSG.Quasithin.Background.B15P4Layer2Final
public import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.CGT.PushingUpLit.BHS.CStar
import CFSG.CGT.PushingUpLit.BHS.Replacement

public section

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

namespace CFSG.AGLEmbedding

namespace AscTenThree

variable {G : Type} [Group G] [Finite G] {X S L : Subgroup G}

section Action

noncomputable def conjActV (X : Subgroup G) :
    ↥X →* MulAut ↥(omegaOneCenterOf (pCoreOf 2 X)) :=
  (conjAct (omegaOneCenterOf (pCoreOf 2 X))).comp
    (Subgroup.inclusion (le_normalizer_omegaOneCenterOf_twoCore X))

omit [Finite G] in
theorem conjActV_apply_coe (x : ↥X) (v : ↥(omegaOneCenterOf (pCoreOf 2 X))) :
    ((conjActV X x v : ↥(omegaOneCenterOf (pCoreOf 2 X))) : G) = x * v * (x : G)⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe _ _ v

omit [Finite G] in
theorem conjActV_eq_one_iff (x : ↥X) :
    conjActV X x = 1 ↔
      (x : G) ∈ Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 X) : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro h v hv
    have := congrArg (fun φ : MulAut ↥(omegaOneCenterOf (pCoreOf 2 X)) =>
      ((φ ⟨v, hv⟩ : ↥(omegaOneCenterOf (pCoreOf 2 X))) : G)) h
    simp only [conjActV_apply_coe, MulAut.one_apply] at this
    calc v * (x : G) = ((x : G) * v * (x : G)⁻¹) * x := by rw [this]
      _ = x * v := by group
  · intro h
    ext v
    rw [conjActV_apply_coe, MulAut.one_apply, ← h v v.2, mul_inv_cancel_right]

omit [Finite G] in
theorem twoCore_le_ker_conjActV (X : Subgroup G) : CFSG.pCore 2 ↥X ≤ (conjActV X).ker := by
  intro q hq
  rw [MonoidHom.mem_ker, conjActV_eq_one_iff]
  exact le_centralizer_omegaOneCenterOf_self _ ⟨q, hq, rfl⟩

noncomputable def conjActVBar (X : Subgroup G) :
    (↥X ⧸ CFSG.pCore 2 ↥X) →* MulAut ↥(omegaOneCenterOf (pCoreOf 2 X)) :=
  QuotientGroup.lift (CFSG.pCore 2 ↥X) (conjActV X) (twoCore_le_ker_conjActV X)

omit [Finite G] in
theorem map_conjActVBar_barM {K : Subgroup G} (hKX : K ≤ X) :
    (barM X K).map (conjActVBar X) = autOn K (omegaOneCenterOf (pCoreOf 2 X)) := by
  rw [barM, Subgroup.map_map, conjActVBar, QuotientGroup.lift_comp_mk', conjActV, autOn,
    ← Subgroup.map_map]
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x, hKX hx⟩, hx, rfl⟩

omit [Finite G] in
theorem conjActVBar_mk (x : ↥X) :
    conjActVBar X (QuotientGroup.mk' (CFSG.pCore 2 ↥X) x) = conjActV X x :=
  QuotientGroup.lift_mk' _ _ x

end Action

theorem isFFStarOffender_autOn_of_isMaxElemAbelian {H V S A : Subgroup G}
    (hV : IsElemAbelian 2 V) (hVS : V ≤ S)
    (hVH : H ≤ Subgroup.normalizer (V : Set G)) (hAH : A ≤ H) (hA : IsMaxElemAbelian S A)
    (hA1 : ¬ A ≤ Subgroup.centralizer (V : Set G)) :
    @IsFFStarOffender ↥V (commGroupOfElemAbelian hV) (autOn H V) (autOn A V) := by
  let _ : CommGroup ↥V := commGroupOfElemAbelian hV
  have hAn : A ≤ Subgroup.normalizer (V : Set G) := hAH.trans hVH
  refine ⟨autOn_le_autOn V hAH, autOn_ne_bot_of_not_le_centralizer hAn hA1,
    isElemAbelian2_autOn hV hA.2.1 hAn, ?_⟩
  intro B hB
  set B₀ : Subgroup G := A ⊓ ((B.comap (conjAct V)).map (Subgroup.normalizer (V : Set G)).subtype)
    with hB₀def
  have hB₀A : B₀ ≤ A := inf_le_left
  have hB₀n : B₀ ≤ Subgroup.normalizer (V : Set G) := hB₀A.trans hAn
  have hconj1 : ∀ a : ↥(Subgroup.normalizer (V : Set G)),
      (a : G) ∈ Subgroup.centralizer (V : Set G) → conjAct V a = 1 := by
    intro a ha
    ext v
    have : ((conjAct V a v : ↥V) : G) = a * v * (a : G)⁻¹ :=
      Subgroup.normalizerMonoidHom_apply_apply_coe _ _ v
    rw [this, MulAut.one_apply, (Subgroup.mem_centralizer_iff.mp ha v v.2).symm,
      mul_inv_cancel_right]
  have hautB : autOn B₀ V = B := by
    apply le_antisymm
    · rintro _ ⟨b, hb, rfl⟩
      obtain ⟨-, ⟨n, hn, hnb⟩⟩ := Subgroup.mem_subgroupOf.mp hb
      have : n = b := Subtype.ext hnb
      rw [← this]
      exact hn
    · intro β hβ
      obtain ⟨a, ha, rfl⟩ := hB hβ
      refine ⟨a, Subgroup.mem_subgroupOf.mpr ⟨Subgroup.mem_subgroupOf.mp ha, ⟨a, hβ, rfl⟩⟩, rfl⟩
  have hCB : B₀ ⊓ Subgroup.centralizer (V : Set G) = A ⊓ Subgroup.centralizer (V : Set G) := by
    refine le_antisymm (inf_le_inf_right _ hB₀A) ?_
    rintro a ⟨haA, haC⟩
    refine ⟨⟨haA, ⟨⟨a, hAn haA⟩, ?_, rfl⟩⟩, haC⟩
    show conjAct V ⟨a, hAn haA⟩ ∈ B
    rw [hconj1 ⟨a, hAn haA⟩ haC]
    exact one_mem _
  rw [← hautB, card_autOn_eq_relIndex hB₀n, card_fixV_autOn_eq hV hB₀n,
    card_autOn_eq_relIndex hAn, card_fixV_autOn_eq hV hAn]
  set cA := Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) with hcA
  have hcpos : 0 < cA := Nat.card_pos
  have hAeq : (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A * cA = Nat.card A := by
    have := Subgroup.relIndex_mul_card (A ⊓ Subgroup.centralizer (V : Set G)) A
    rwa [inf_of_le_left inf_le_left] at this
  have hBeq : (B₀ ⊓ Subgroup.centralizer (V : Set G)).relIndex B₀ * cA = Nat.card B₀ := by
    have := Subgroup.relIndex_mul_card (B₀ ⊓ Subgroup.centralizer (V : Set G)) B₀
    rw [inf_of_le_left inf_le_left] at this
    rwa [show Nat.card ↥(B₀ ⊓ Subgroup.centralizer (V : Set G)) = cA by rw [hCB]] at this
  set D : Subgroup G := V ⊓ Subgroup.centralizer (B₀ : Set G) with hD
  have hBD : B₀ ≤ Subgroup.centralizer (D : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    exact (Subgroup.mem_centralizer_iff.mp hd.2 b hb).symm
  have hprod := CFSG.CGT.PushingUpLit.BHS.card_sup_mul_card_inf' (X := B₀) (Y := D)
    fun b hb d hd => (Subgroup.mem_centralizer_iff.mp (hBD hb) d hd).symm
  have hElem : IsElemAbelian 2 (B₀ ⊔ D) :=
    CFSG.CGT.PushingUpLit.BHS.isElemAbelian_sup_of_le_centralizer
      (Setup.Campbell.isElemAbelian_mono hA.2.1 hB₀A)
      (Setup.Campbell.isElemAbelian_mono hV inf_le_left) hBD
  have hSup : B₀ ⊔ D ≤ S := sup_le (hB₀A.trans hA.1) (inf_le_left.trans hVS)
  have hcardSup : Nat.card ↥(B₀ ⊔ D) ≤ Nat.card A := hA.2.2 _ hSup hElem
  have hinf : B₀ ⊓ D ≤ V ⊓ Subgroup.centralizer (A : Set G) := by
    rintro x ⟨hxB, ⟨hxV, -⟩⟩
    refine ⟨hxV, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_⟩
    have := hA.2.1.1
    exact (setLike_mul_comm (hB₀A hxB) ha).symm
  have hcardInf : Nat.card ↥(B₀ ⊓ D) ≤ Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) :=
    Subgroup.card_le_of_le hinf
  have key : Nat.card B₀ * Nat.card D ≤
      Nat.card A * Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) := by
    rw [← hprod]
    exact Nat.mul_le_mul hcardSup hcardInf
  refine Nat.le_of_mul_le_mul_right ?_ hcpos
  calc (B₀ ⊓ Subgroup.centralizer (V : Set G)).relIndex B₀ * Nat.card D * cA
      = Nat.card B₀ * Nat.card D := by rw [← hBeq]; ring
    _ ≤ Nat.card A * Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) := key
    _ = (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A *
        Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) * cA := by rw [← hAeq]; ring

theorem barM_le_normalizer_of_isMaxElemAbelian (hyp : Asc81bHyp X S)
    (hL : IsTwoPrimeComponent X L)
    (hLV : ¬ L ≤ Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 X) : Set G))
    {A : Subgroup G} (hA : IsMaxElemAbelian S A) :
    barM X A ≤ Subgroup.normalizer (barM X L : Set (↥X ⧸ CFSG.pCore 2 ↥X)) := by
  set V := omegaOneCenterOf (pCoreOf 2 X) with hVdef
  have hV : IsElemAbelian 2 V := isElemAbelian_omegaOneCenterOf _
  have hSX : S ≤ X := hyp.twoRadical.1
  have hAX : A ≤ X := hA.1.trans hSX
  have hVS : V ≤ S := (C1GN.omegaOneCenterOf_le_self _).trans hyp.twoCore_le
  by_cases hAV : A ≤ Subgroup.centralizer (V : Set G)
  · rintro _ ⟨a, ha, rfl⟩
    have h1 := mk_eq_one_of_mem_pCoreOf (inf_centralizer_V_le_twoCore hyp
      ⟨hA.1 (Subgroup.mem_subgroupOf.mp ha), hAV (Subgroup.mem_subgroupOf.mp ha)⟩)
    rw [h1]
    exact one_mem _
  let _ : CommGroup ↥V := commGroupOfElemAbelian hV
  have hVv : ∀ v : ↥V, v ^ 2 = 1 := fun v => Subtype.ext (hV.2 v v.2)
  have hoff := isFFStarOffender_autOn_of_isMaxElemAbelian hV hVS
    (le_normalizer_omegaOneCenterOf_twoCore X) hAX hA hAV
  have hLq : CFSG.IsQuasisimple ↥(barM X L) := ((CFSG.isComponent_iff_open _).mpr hL.component).1
  have hLker : ¬ barM X L ≤ (conjActVBar X).ker := by
    intro h
    apply hLV
    intro ℓ hℓ
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥X) ⟨ℓ, hL.le hℓ⟩ ∈ (conjActVBar X).ker :=
      h ⟨⟨ℓ, hL.le hℓ⟩, hℓ, rfl⟩
    rw [MonoidHom.mem_ker, conjActVBar_mk] at h1
    exact (conjActV_eq_one_iff _).mp h1
  have hq := CFSG.LocalCores.isQuasisimple_map hLq (conjActVBar X) hLker
  rw [map_conjActVBar_barM hL.le] at hq
  have htop : (⊤ : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X)).map (conjActVBar X) = autOn X V := by
    rw [← map_conjActVBar_barM (K := X) le_rfl]
    congr 1
    rw [barM, Subgroup.subgroupOf_self, Subgroup.map_top_of_surjective _
      (QuotientGroup.mk'_surjective _)]
  have hsub : CFSG.Open.IsSubnormal (autOn L V) (autOn X V) := by
    have := CFSG.RankThreeCoreUniqueness.Helpers.cfsg_isSubnormal_map (conjActVBar X)
      hL.component.2.1
    rwa [map_conjActVBar_barM hL.le, htop] at this
  have hcomp : CFSG.Open.IsComponentOf (autOn L V) (autOn X V) :=
    ⟨autOn_le_autOn V hL.le, hsub, ⟨Group.isPerfect_def.mp hq.1, hq.2.1⟩⟩
  have hN := CFSG.Quasithin.B15P4.asB15Part4 ↥V hVv (autOn X V) (autOn A V) hoff (autOn L V)
    hcomp
  rintro _ ⟨a, ha, rfl⟩
  set abar := QuotientGroup.mk' (CFSG.pCore 2 ↥X) a with habar
  have hρa : conjActVBar X abar ∈ autOn A V := by
    rw [← map_conjActVBar_barM hAX]
    exact ⟨abar, ⟨a, ha, rfl⟩, rfl⟩
  have hρN := hN hρa
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  by_contra hne
  set L' := (barM X L).map (MulAut.conj abar).toMonoidHom with hL'def
  have hL'c : IsComponentOf L' ⊤ :=
    (CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj abar) _).mpr
      hL.component
  have hc := CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ hL.component hL'c
    (Ne.symm hne)
  have hmapL' : L'.map (conjActVBar X) = autOn L V := by
    rw [hL'def, Subgroup.map_map]
    have : (conjActVBar X).comp (MulAut.conj abar).toMonoidHom =
        (MulAut.conj (conjActVBar X abar)).toMonoidHom.comp (conjActVBar X) := by
      ext y
      simp [MulAut.conj_apply]
    rw [this, ← Subgroup.map_map, map_conjActVBar_barM hL.le]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hρN
  have hc' := congrArg (Subgroup.map (conjActVBar X)) hc
  rw [Subgroup.map_commutator, map_conjActVBar_barM hL.le, hmapL', Subgroup.map_bot] at hc'
  have hperf : ⁅autOn L V, autOn L V⁆ = autOn L V := Subgroup.isPerfect_iff.mp hq.1
  rw [hperf] at hc'
  have hnt : Nontrivial ↥(autOn L V) := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    obtain ⟨u, w, huw⟩ := hq.2.1.toNontrivial.exists_pair_ne
    apply huw
    induction u using QuotientGroup.induction_on with
    | H u => induction w using QuotientGroup.induction_on with
      | H w => rw [Subsingleton.elim u w]
  exact (Subgroup.nontrivial_iff_ne_bot _).mp hnt hc'

end AscTenThree

end CFSG.AGLEmbedding
