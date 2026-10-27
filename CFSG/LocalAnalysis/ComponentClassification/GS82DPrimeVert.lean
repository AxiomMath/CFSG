module

public import CFSG.LocalAnalysis.ComponentClassification.GS82DPrimeBasic
public import CFSG.GH74.GLS.TwoThin.PumpData
public import CFSG.ClassicalInvolution.Balance.Basic

public section

namespace CFSG.ComponentClassification.GS82PumpInputs.DPrime

open CFSG Subgroup GH74.GLS GH74.GLS.TwoThin CFSG.LocalAnalysis.ComponentInitial

theorem le_of_perfect_of_twoElements {X : Type} [Group X] [Finite X] {N S : Subgroup X}
    (hN : ⁅N, N⁆ = N) (h : ∀ z ∈ N, (∃ n : ℕ, z ^ (2 ^ n) = 1) → z ∈ S) : N ≤ S := by
  have : Group.IsPerfect ↥N := Subgroup.isPerfect_iff.mpr hN
  have hres : TwoResidual.subgroup ↥N = ⊤ :=
    ClassicalInvolution.Balance.twoResidual_eq_top_of_perfect Group.IsPerfect.commutator_eq_top
  have hle : TwoResidual.subgroup ↥N ≤ S.comap N.subtype := by
    refine sSup_le fun P hP g hg => ?_
    obtain ⟨n, hn⟩ := hP ⟨g, hg⟩
    refine h g g.2 ⟨n, ?_⟩
    have := congrArg (fun x : ↥P => ((x : ↥N) : X)) hn
    simpa using this
  intro z hz
  have hz' : (⟨z, hz⟩ : ↥N) ∈ TwoResidual.subgroup ↥N := hres ▸ mem_top _
  exact hle hz'

theorem nonempty_coreQuotEquiv_of_cover {X : Type} [Group X] [Finite X] {A K : Subgroup X}
    (h : A ≤ K) (hcov : ∀ k ∈ K, ∃ c ∈ A, ∃ o ∈ pPrimeCoreOf 2 K, k = c * o) :
    Nonempty (↥A ⧸ pPrimeCore 2 ↥A ≃* ↥K ⧸ pPrimeCore 2 ↥K) :=
  ⟨(QuotientGroup.quotientMulEquivOfEq (ker_hatMap_eq_pPrimeCore h hcov).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (hatMap_surjective h hcov))⟩

theorem isTwoQuasisimple_of_isPCompIn {X : Type} [Group X] [Finite X] {H K : Subgroup X}
    (hK : IsPCompIn 2 H K) : HarrisLit.IsTwoQuasisimple ↥K :=
  ((HarrisLit.isTwoComponentIn_iff hK.1).mpr hK.2).2.2

variable {X : Type} [Group X] [Finite X]

theorem datum_cover {q₀ : ℕ} {t c : X} {K₀ N : Subgroup X} (hD : IsDatum q₀ t K₀ N c) :
    ∃ I : Subgroup X, IsPCompIn 2 (centralizer ({t} : Set X) ⊓ centralizer ({c} : Set X)) I ∧
      c ∈ I ∧ N ≤ I ∧ Nonempty (↥I ⧸ pPrimeCore 2 ↥I ≃* ↥K₀ ⧸ pPrimeCore 2 ↥K₀) := by
  obtain ⟨-, hK₀C, hK₀pc, hNK₀, hNp, -, hc, hcN, hNc, hcZ⟩ := hD
  obtain ⟨I, hIX, -, -, -, hIW, h2el, hcov⟩ :=
    pumpup_cover hc ⟨hK₀C, hK₀pc⟩ (mem_centralizerSection_of_mem_fusionZStar hcZ)
  refine ⟨I, hIW, h2el c ⟨hNK₀ hcN, mem_centralizer_singleton_iff.mpr rfl⟩ ⟨1, ?_⟩,
    le_of_perfect_of_twoElements hNp fun z hz h2 => h2el z ⟨hNK₀ hz, hNc hz⟩ h2,
    nonempty_coreQuotEquiv_of_cover (hIX.trans inf_le_left) hcov⟩
  rw [pow_one, ← hc]
  exact pow_orderOf_eq_one c

theorem conjSub_eq_of_mem_twoLayer {Y : Type} [Group Y] [Finite Y] {x : Y}
    (hx : x ∈ TwoLayer.subgroup Y) {L : Subgroup (barQ Y)} (hL : CFSG.IsComponent L) :
    conjSub (barMk Y x)⁻¹ L = L := by
  have h1 : barMk Y x ∈ CFSG.layer (barQ Y) := by
    rw [← map_barMk_twoLayer]
    exact mem_map_of_mem _ hx
  have h2 : (barMk Y x)⁻¹ ∈ Layer.subgroup (barQ Y) := by
    rw [layer_subgroup_eq_layer]
    exact inv_mem h1
  exact mem_normalizer_iff_map_conj_eq.mp
    (ClassicalInvolution.layer_le_normalizer_of_isComponentOf
      ((CFSG.isComponent_iff_open L).mp hL) h2)

theorem vertical_step {Typ Esc : ∀ (K : Type) [Group K], Prop} {q₀ : ℕ}
    (hVC : VerticalCentralEsc Typ Esc) (hCI : CoreInvariant Typ) (hCE : CoreInvariant Esc)
    {x y : X} (hx : orderOf x = 2) (hy : orderOf y = 2) (hxy : x ∈ centralizer ({y} : Set X))
    (hKy : SectionRank.IsKGroupCat ↥(centralizer ({y} : Set X))) {Λ N : Subgroup X}
    (hΛ : IsPCompIn 2 (centralizer ({x} : Set X) ⊓ centralizer ({y} : Set X)) Λ)
    (hTyp : Typ ↥Λ) (hyΛ : y ∈ Λ) (hNΛ : N ≤ Λ) (hNp : ⁅N, N⁆ = N)
    (hNSL : HarrisLit.IsSLTwoOver q₀ (↥N ⧸ pPrimeCore 2 ↥N)) (hyN : y ∈ N)
    (hNy : N ≤ centralizer ({y} : Set X))
    {L : Subgroup (barQ ↥(centralizer ({y} : Set X)))} (hL : CFSG.IsComponent L)
    (hLx : conjSub (barMk ↥(centralizer ({y} : Set X)) ⟨x, hxy⟩)⁻¹ L = L)
    (hΛL : (Λ.subgroupOf (centralizer ({y} : Set X))).map
      (barMk ↥(centralizer ({y} : Set X))) ≤ L) :
    (∃ (w : X) (J N' : Subgroup X), IsDatum q₀ w J N' w ∧ w ∈ J ∧ Typ ↥J) ∨
      ∃ (v : X) (M : Subgroup X), orderOf v = 2 ∧ M ≤ centralizer ({v} : Set X) ∧
        IsPComponent 2 (M.subgroupOf (centralizer ({v} : Set X))) ∧ Esc ↥M := by
  set x' : ↥(centralizer ({y} : Set X)) := ⟨x, hxy⟩ with hx'
  have hyY : y ∈ centralizer ({y} : Set X) := mem_centralizer_singleton_iff.mpr rfl
  set y' : ↥(centralizer ({y} : Set X)) := ⟨y, hyY⟩ with hy'
  have hΛY : Λ ≤ centralizer ({y} : Set X) := hΛ.1.trans inf_le_right
  set Λ' := Λ.subgroupOf (centralizer ({y} : Set X)) with hΛ'
  have hΛC := le_centralizer_mk hΛ.1 hxy
  have hΛ2 := isTwoComponent_centralizer_mk hΛ hxy
  have hL2 : TwoComponents.IsTwoComponent L :=
    TwoLayerTransport.ordinary_isTwoComponent_of_corefree oddCore_barQ L
      ((CFSG.isComponent_iff_open L).mp hL)
  obtain ⟨M, hM2, hML⟩ := OddKernelTwoComponents.exists_lift
    (barMk ↥(centralizer ({y} : Set X))) barMk_surjective odd_card_ker_barMk L hL2
  have hperf : ⁅Λ', Λ'⁆ = Λ' := commutator_self_of_isTwoComponent hΛC hΛ2
  have : Group.IsPerfect ↥Λ' := Subgroup.isPerfect_iff.mpr hperf
  have hΛM : Λ' ≤ M :=
    le_of_map_le_of_residual (barMk ↥(centralizer ({y} : Set X))) barMk_surjective
      odd_card_ker_barMk Λ' M (ClassicalInvolution.Balance.twoResidual_eq_top_of_perfect
        Group.IsPerfect.commutator_eq_top) hM2.1 (by rw [hML]; exact hΛL)
  have hLx' : L.map (MulAut.conj (barMk ↥(centralizer ({y} : Set X)) x')).toMonoidHom = L := by
    have h := conjSub_conjSub_inv (barMk ↥(centralizer ({y} : Set X)) x') L
    rw [hLx] at h
    exact h
  have hcomp : (barMk ↥(centralizer ({y} : Set X))).comp (MulAut.conj x').toMonoidHom =
      (MulAut.conj (barMk ↥(centralizer ({y} : Set X)) x')).toMonoidHom.comp
        (barMk ↥(centralizer ({y} : Set X))) := by
    ext a
    simp
  have hMx : M.map (MulAut.conj x').toMonoidHom = M := by
    refine OddKernelTwoComponents.lift_unique (barMk ↥(centralizer ({y} : Set X)))
      barMk_surjective odd_card_ker_barMk _ _
      ((TwoComponentTransport.equiv_iff (MulAut.conj x') M).mpr hM2) hM2 ?_
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hML, hLx']
  have hx'N : x' ∈ normalizer (M : Set ↥(centralizer ({y} : Set X))) :=
    mem_normalizer_iff_map_conj_eq.mpr hMx
  have hy'Λ' : y' ∈ Λ' := mem_subgroupOf.mpr hyΛ
  have hy'Z : y' ∈ (Open.fusionZStar ↥M).map M.subtype :=
    mem_fusionZStar_of_commute (hΛM hy'Λ') fun m _ =>
      Subtype.ext (mem_centralizer_singleton_iff.mp m.2).symm
  have hTypΛ' : Typ ↥Λ' := typ_of_mulEquiv hCI (subgroupOfEquivOfLe hΛY).symm hTyp
  set MG : Subgroup X := M.map (centralizer ({y} : Set X)).subtype with hMG
  let eMG : ↥M ≃* ↥MG := M.equivMapOfInjective (centralizer ({y} : Set X)).subtype
    (centralizer ({y} : Set X)).subtype_injective
  have hMGY : MG ≤ centralizer ({y} : Set X) := map_subtype_le M
  have hMGpc : IsPComponent 2 (MG.subgroupOf (centralizer ({y} : Set X))) := by
    have hsub : MG.subgroupOf (centralizer ({y} : Set X)) = M :=
      Subgroup.comap_map_eq_self_of_injective (centralizer ({y} : Set X)).subtype_injective M
    rw [hsub]
    exact (CatalogueBAlternating.pComponent_two_iff M).mpr hM2
  have hΛMG : Λ ≤ MG := fun a ha => ⟨⟨a, hΛY ha⟩, hΛM (mem_subgroupOf.mpr ha), rfl⟩
  rcases hVC ↥(centralizer ({y} : Set X)) hKy M
      ((CatalogueBAlternating.pComponent_two_iff M).mpr hM2) x' (orderOf_mk_centralizer hxy hx)
      hx'N Λ' hΛM hΛC
      ((CatalogueBAlternating.pComponent_two_iff _).mpr hΛ2) hTypΛ' y'
      (orderOf_mk_centralizer hyY hy) hy'Λ' hy'Z with hT | hE
  · refine Or.inl ⟨y, MG, N, ⟨hy, hMGY, hMGpc, hNΛ.trans hΛMG, hNp, hNSL, hy, hyN, hNy, ?_⟩,
      hΛMG hyΛ, typ_of_mulEquiv hCI eMG hT⟩
    exact mem_fusionZStar_of_commute (hΛMG hyΛ) fun m hm =>
      (mem_centralizer_singleton_iff.mp (hMGY hm)).symm
  · exact Or.inr ⟨y, MG, hy, hMGY, hMGpc, typ_of_mulEquiv hCE eMG hE⟩

end CFSG.ComponentClassification.GS82PumpInputs.DPrime
