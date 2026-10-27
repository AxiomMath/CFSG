module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalCorrespondence
public import CFSG.LocalAnalysis.ComponentClassification.PrimeComponentMinimalPerfectLift
public import CFSG.LocalAnalysis.ComponentInitial.QuasisimpleFixedLayerFull
public import CFSG.LocalAnalysis.ComponentInitial.GroupCentralQuotient
public import CFSG.LocalAnalysis.ComponentInitial.FixedComponentCorrespondence
public import CFSG.Open.FusionDefs
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancingLocal

open Subgroup CFSG.ComponentClassification.UnbalancedGS Correspondence

section Quasisimple

variable {X Y : Type*} [Group X] [Group Y]

theorem fusionOddCore_eq_pPrimeCore (X : Type*) [Group X] :
    CFSG.Open.fusionOddCore X = pPrimeCore 2 X := by
  unfold CFSG.Open.fusionOddCore pPrimeCore
  congr 1
  ext K
  simp only [Set.mem_ofPred_eq, Nat.coprime_two_left]

theorem pPrimeCore_le_center (hX : IsQuasisimple X) (hQ : IsQuasisimple (X ⧸ pPrimeCore 2 X)) :
    pPrimeCore 2 X ≤ center X := by
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hX
    (inferInstance : (pPrimeCore 2 X).Normal) with h | h
  · exfalso
    have := CFSG.LocalCores.isQuasisimple_nontrivial hQ
    obtain ⟨u, v, huv⟩ := exists_pair_ne (X ⧸ pPrimeCore 2 X)
    induction u using QuotientGroup.induction_on with | H x => ?_
    induction v using QuotientGroup.induction_on with | H y => ?_
    exact huv (QuotientGroup.eq.2 (by rw [h]; trivial))
  · exact h

theorem zStar_eq_center (hX : IsQuasisimple X) (hQ : IsQuasisimple (X ⧸ pPrimeCore 2 X)) :
    CFSG.Open.fusionZStar X = center X := by
  have hle : CFSG.Open.fusionOddCore X ≤ center X := by
    rw [fusionOddCore_eq_pPrimeCore]
    exact pPrimeCore_le_center hX hQ
  exact (CFSG.LocalCores.quasisimple_central_quotient hX _ hle).2.1

def centerQuotientCongr (e : X ≃* Y) : X ⧸ center X ≃* Y ⧸ center Y :=
  QuotientGroup.congr (center X) (center Y) e (Subgroup.map_center_eq e)

theorem nonempty_center_quotient_core (hX : IsQuasisimple X)
    (hQ : IsQuasisimple (X ⧸ pPrimeCore 2 X)) :
    Nonempty (X ⧸ center X ≃* (X ⧸ pPrimeCore 2 X) ⧸ center (X ⧸ pPrimeCore 2 X)) :=
  CFSG.LocalAnalysis.ComponentInitial.center_quotient_equiv_of_surjective hX
    (QuotientGroup.mk' (pPrimeCore 2 X)) (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk']; exact pPrimeCore_le_center hX hQ)

end Quasisimple

variable {G : Type*} [Group G]

theorem commute_and_gsFixedLayer_eq [Finite G] {a b : G} {J L : Subgroup G} (h : GSCorr a J b L)
    (hJ : IsQuasisimple J) : (∀ j ∈ J, j * b = b * j) ∧ gsFixedLayer J b = J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hbo, -, hJa, hJcomp, -, -, hbN, hcomm, -⟩ := h
  have hJq : IsQuasisimple (J ⧸ pPrimeCore 2 J) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 J _ hJa).mp hJcomp).2.2
  have hbb : b * b = 1 := by rw [← sq, ← hbo, pow_orderOf_eq_one]
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hbb
  have hzp : ∀ c ∈ zpowers b, c = 1 ∨ c = b := by
    intro c hc
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hc
    rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
    · left
      rw [zpow_mul, zpow_two, hbb, one_zpow]
    · right
      rw [zpow_add, zpow_mul, zpow_two, hbb, one_zpow, one_mul, zpow_one]
  have hBN : zpowers b ≤ normalizer (J : Set G) := zpowers_le.mpr hbN
  let α : zpowers b →* MulAut J := J.normalizerMonoidHom.comp (Subgroup.inclusion hBN)
  have hα : ∀ (c : zpowers b) (j : J), ((α c j : J) : G) = (c : G) * j * (c : G)⁻¹ :=
    fun c j => Subgroup.normalizerMonoidHom_apply_apply_coe J _ j
  have hB2 : IsPGroup 2 (zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hbo, pow_one])
  have htriv : ∀ (c : zpowers b) (j : J),
      ((α c j : J) : J ⧸ pPrimeCore 2 J) = (j : J ⧸ pPrimeCore 2 J) := by
    intro c j
    rcases hzp c c.2 with hc | hc
    · have hc1 : c = 1 := Subtype.ext hc
      rw [hc1, map_one]
      rfl
    · rw [eq_comm, QuotientGroup.eq]
      obtain ⟨o, ho, hoeq⟩ := Subgroup.mem_map.mp (hcomm (j : G) j.2)
      have hoe : o = j⁻¹ * α c j := by
        apply Subtype.ext
        rw [Subgroup.coe_mul, Subgroup.coe_inv, hα, hc, hbinv]
        rw [hbinv] at hoeq
        change J.subtype o = _
        rw [hoeq]
        group
      rwa [hoe] at ho
  have hCmem : ∀ j : J, j ∈ (centralizer ({b} : Set G)).subgroupOf J ↔ ∀ c : zpowers b,
      α c j = j := by
    intro j
    rw [Subgroup.mem_subgroupOf, mem_centralizer_singleton_iff]
    constructor
    · intro h c
      apply Subtype.ext
      rw [hα]
      rcases hzp c c.2 with hc | hc
      · rw [hc]
        group
      · rw [hc, ← h, mul_inv_cancel_right]
    · intro h
      have h1 := congrArg Subtype.val (h ⟨b, mem_zpowers b⟩)
      rw [hα] at h1
      exact (mul_inv_eq_iff_eq_mul.mp h1).symm
  set CJ := (centralizer ({b} : Set G)).subgroupOf J with hCJ
  obtain ⟨hfix, htop⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.quasisimple_fixed_layer_full_under_trivial_core_action 2
      hJ hB2 α hJq htriv CJ hCmem
  refine ⟨fun j hj => ?_, ?_⟩
  · have h1 := congrArg Subtype.val (hfix ⟨b, mem_zpowers b⟩ ⟨j, hj⟩)
    rw [hα] at h1
    exact (mul_inv_eq_iff_eq_mul.mp h1).symm
  ·
    have hTb : ((pLayer CJ 2).map CJ.subtype).map J.subtype = gsFixedLayer J b := by
      rw [Subgroup.map_map, gsFixedLayer]
      let φ : CJ ≃* (J ⊓ centralizer ({b} : Set G) : Subgroup G) :=
        { toFun := fun x => ⟨x, x.1.2, x.2⟩
          invFun := fun y => ⟨⟨y, y.2.1⟩, y.2.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
          map_mul' := fun _ _ => rfl }
      have hcomp : J.subtype.comp CJ.subtype =
          (J ⊓ centralizer ({b} : Set G)).subtype.comp φ.toMonoidHom := by
        ext x
        rfl
      rw [hcomp, ← Subgroup.map_map, FixedLayerPComponent.map_pLayer_mulEquiv 2 φ]
    rw [← hTb, htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem nonempty_center_quotient_diag {Q : Type*} [Group Q] {A B Δ : Subgroup Q}
    (α : ↥(A ⊔ B) ≃* ↥(A ⊔ B)) (hαA : ∀ u : ↥(A ⊔ B), (u : Q) ∈ A → ((α u : ↥(A ⊔ B)) : Q) ∈ B)
    (hcomm : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) (hAq : IsQuasisimple A)
    (hD : ∀ d ∈ A ⊓ B, ∀ k ∈ A ⊔ B, d * k = k * d)
    (hmem : ∀ x, x ∈ Δ ↔ ∃ u : ↥(A ⊔ B), (u : Q) ∈ A ∧ x = ((u * α u : ↥(A ⊔ B)) : Q)) :
    Nonempty (A ⧸ center A ≃* Δ ⧸ center Δ) := by
  let ι : ↥A →* ↥(A ⊔ B) := Subgroup.inclusion le_sup_left
  have hι : ∀ u : ↥A, ((ι u : ↥(A ⊔ B)) : Q) = u := fun _ => rfl
  let δ₀ : ↥A →* ↥(A ⊔ B) :=
    { toFun := fun u => ι u * α (ι u)
      map_one' := by rw [map_one, map_one, mul_one]
      map_mul' := fun u v => by
        rw [map_mul, map_mul]
        have hc : ι v * α (ι u) = α (ι u) * ι v :=
          Subtype.ext (hcomm _ (by rw [hι]; exact v.2) _ (hαA (ι u) (by rw [hι]; exact u.2)))
        rw [mul_assoc, ← mul_assoc (ι v), hc]
        group }
  have hδ₀ : ∀ u : ↥A, δ₀ u = ι u * α (ι u) := fun _ => rfl
  have hδmem : ∀ u : ↥A, ((δ₀ u : ↥(A ⊔ B)) : Q) ∈ Δ := fun u =>
    (hmem _).2 ⟨ι u, u.2, by rw [hδ₀]⟩
  let δ : ↥A →* ↥Δ := ((A ⊔ B).subtype.comp δ₀).codRestrict Δ hδmem
  have hδs : Function.Surjective δ := by
    rintro ⟨x, hx⟩
    obtain ⟨u, hu, rfl⟩ := (hmem x).1 hx
    refine ⟨⟨u, hu⟩, Subtype.ext ?_⟩
    change ((δ₀ ⟨u, hu⟩ : ↥(A ⊔ B)) : Q) = _
    rw [hδ₀]
    rfl
  have hδk : δ.ker ≤ center A := by
    intro u hu
    have h1 : ((δ₀ u : ↥(A ⊔ B)) : Q) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hu)
    rw [hδ₀, Subgroup.coe_mul, hι] at h1
    have h2 : ((α (ι u) : ↥(A ⊔ B)) : Q) = (u : Q)⁻¹ := eq_inv_of_mul_eq_one_right h1
    have hDu : (u : Q) ∈ A ⊓ B := by
      refine Subgroup.mem_inf.2 ⟨u.2, ?_⟩
      have h4 := hαA (ι u) (by rw [hι]; exact u.2)
      rw [h2] at h4
      simpa using inv_mem h4
    refine Subgroup.mem_center_iff.2 fun v => Subtype.ext ?_
    exact (hD _ hDu _ (mem_sup_left v.2)).symm
  exact CFSG.LocalAnalysis.ComponentInitial.center_quotient_equiv_of_surjective hAq δ hδs hδk

theorem swap_center_quotient_equiv [Finite G] {a b : G} {J L : Subgroup G} (h : GSCorr a J b L)
    (hJ : IsQuasisimple J) (hL : IsQuasisimple L) (hJq : IsQuasisimple (J ⧸ pPrimeCore 2 J))
    (hLq : IsQuasisimple (L ⧸ pPrimeCore 2 L)) (hT : gsFixedLayer J b = J)
    (hne : conjugate L a ≠ L) : Nonempty (J ⧸ center J ≃* L ⧸ center L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ha : a ∈ centralizer ({b} : Set G) := mem_centralizer_singleton_iff.mpr h.2.2.1
  have hao : orderOf a = 2 := h.1
  have hLb : L ≤ centralizer ({b} : Set G) := h.2.2.2.2.2.1
  have hLcomp : IsPComponent 2 (L.subgroupOf (centralizer ({b} : Set G))) := h.2.2.2.2.2.2.1
  obtain ⟨α, hαk, -, hcomm, hAq, -, hDcent, -, hmemT, ⟨eT, -⟩, -⟩ := swap_case h hne ha
  have haa : a * a = 1 := by rw [← sq, ← hao, pow_orderOf_eq_one]
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have hαA : ∀ u : ↥(corrImage b L ⊔ corrImage b (conjugate L a)),
      (u : CorrQuotient b) ∈ corrImage b L →
        ((α u : ↥(corrImage b L ⊔ corrImage b (conjugate L a))) : CorrQuotient b) ∈
          corrImage b (conjugate L a) := by
    intro u hu
    rw [hαk]
    obtain ⟨l, hl, hlu⟩ := Subgroup.mem_map.mp hu
    rw [← hlu]
    refine ⟨⟨a, ha⟩ * l * (⟨a, ha⟩ : centralizer ({b} : Set G))⁻¹, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
    refine ⟨(l : G), Subgroup.mem_subgroupOf.mp hl, ?_⟩
    change a⁻¹ * (l : G) * a⁻¹⁻¹ = a * (l : G) * a⁻¹
    rw [inv_inv, hainv]
  obtain ⟨eA⟩ := nonempty_center_quotient_diag α hαA hcomm hAq hDcent hmemT
  obtain ⟨-, ⟨eL, -⟩, -⟩ :=
    (CFSG.ComponentClassification.PrimeComponentLift.prime_component_minimal_perfect_lift
      (X := centralizer ({b} : Set G)) 2).2 _ hLcomp
  let eL' : L ⧸ pPrimeCore 2 L ≃* ↥(corrImage b L) :=
    (quotientPPrimeCoreCongr 2 (Subgroup.subgroupOfEquivOfLe hLb).symm).trans eL
  let eJ' : J ⧸ pPrimeCore 2 J ≃* ↥(corrImage b (gsFixedLayer J b)) :=
    (quotientPPrimeCoreCongr 2 (MulEquiv.subgroupCongr hT.symm)).trans eT
  obtain ⟨cJ⟩ := nonempty_center_quotient_core hJ hJq
  obtain ⟨cL⟩ := nonempty_center_quotient_core hL hLq
  exact ⟨cJ.trans ((centerQuotientCongr eJ').trans (eA.symm.trans
    ((centerQuotientCongr eL'.symm).trans cL.symm)))⟩

theorem ordinary_local_correspondence_simple_quotient_comparison [Finite G] {a b : G}
    {J L : Subgroup G} (h : GSCorr a J b L) (hJ : IsQuasisimple J) (hL : IsQuasisimple L) :
    CFSG.Open.fusionZStar J = center J ∧ CFSG.Open.fusionZStar L = center L ∧
      (∀ j ∈ J, j * b = b * j) ∧ gsFixedLayer J b = J ∧
      (conjugate L a = L → J ≤ L ∧ (J = L ∨ (center J).index < (center L).index)) ∧
      (conjugate L a ≠ L → Nonempty (J ⧸ center J ≃* L ⧸ center L)) ∧
      (CFSG.Open.fusionZStar J).index ≤ (CFSG.Open.fusionZStar L).index ∧
      ((CFSG.Open.fusionZStar J).index = (CFSG.Open.fusionZStar L).index →
        Nonempty (J ⧸ CFSG.Open.fusionZStar J ≃* L ⧸ CFSG.Open.fusionZStar L)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJq : IsQuasisimple (J ⧸ pPrimeCore 2 J) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 J _ h.2.2.2.1).mp h.2.2.2.2.1).2.2
  have hLq : IsQuasisimple (L ⧸ pPrimeCore 2 L) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 L _ h.2.2.2.2.2.1).mp
      h.2.2.2.2.2.2.1).2.2
  have hZJ := zStar_eq_center hJ hJq
  have hZL := zStar_eq_center hL hLq
  obtain ⟨hjb, hT⟩ := commute_and_gsFixedLayer_eq h hJ
  have hfixed : conjugate L a = L → J ≤ L ∧ (J = L ∨ (center J).index < (center L).index) := by
    intro hLa
    have hK : L ⊔ conjugate L a = L := by rw [hLa, sup_idem]
    have hJL : J ≤ L := hT ▸ h.gsFixedLayer_le hK
    refine ⟨hJL, ?_⟩
    rcases eq_or_lt_of_le hJL with heq | hlt
    · exact Or.inl heq
    · have : Group.IsPerfect L := hL.1
      exact Or.inr (CFSG.LocalAnalysis.ComponentInitial.index_center_lt_of_lt hlt)
  have hswap : conjugate L a ≠ L → Nonempty (J ⧸ center J ≃* L ⧸ center L) := fun hne =>
    swap_center_quotient_equiv h hJ hL hJq hLq hT hne
  refine ⟨hZJ, hZL, hjb, hT, hfixed, hswap, ?_, ?_⟩
  · rw [hZJ, hZL]
    by_cases hLa : conjugate L a = L
    · obtain ⟨-, h1 | h1⟩ := hfixed hLa
      · subst h1
        exact le_rfl
      · exact h1.le
    · obtain ⟨e⟩ := hswap hLa
      exact (Nat.card_congr e.toEquiv).le
  · intro heq
    by_cases hLa : conjugate L a = L
    · obtain ⟨-, h1 | h1⟩ := hfixed hLa
      · subst h1
        exact ⟨MulEquiv.refl _⟩
      · rw [hZJ, hZL] at heq
        exact absurd heq h1.ne
    · obtain ⟨e⟩ := hswap hLa
      exact ⟨(QuotientGroup.quotientMulEquivOfEq hZJ).trans
        (e.trans (QuotientGroup.quotientMulEquivOfEq hZL).symm)⟩

end CFSG.ComponentClassification.UnbalancingLocal
