module

public import CFSG.LocalAnalysis.ComponentClassification.GS82L34Pi
public import CFSG.LocalAnalysis.ComponentClassification.GS82DPrimeDStep

public section

namespace CFSG.ComponentClassification.GS82PumpInputs

open CFSG Subgroup GH74.GLS GH74.GLS.TwoThin CFSG.LocalAnalysis.ComponentInitial

@[expose] def VerticalCentralEsc' (Typ Esc : ∀ (K : Type) [Group K], Prop) : Prop :=
  ∀ (H : Type) [Group H] [Finite H], SectionRank.IsKGroupCat H →
    ∀ M : Subgroup H, IsPComponent 2 M →
    ∀ x : H, orderOf x = 2 → x ∈ normalizer (M : Set H) →
    ∀ T : Subgroup H, T ≤ M → T ≤ centralizer ({x} : Set H) →
      IsPComponent 2 (T.subgroupOf (centralizer ({x} : Set H))) → Typ ↥T →
    ∀ w : H, orderOf w = 2 → w ∈ T → w ∈ (Open.fusionZStar ↥M).map M.subtype →
      Typ ↥M ∨ (Esc ↥M ∧ ∃ y ∈ M, y⁻¹ * (x⁻¹ * y * x) ∉ pPrimeCoreOf 2 M)

namespace DPrime

variable {X : Type} [Group X] [Finite X]

theorem vertical_step' {Typ Esc : ∀ (K : Type) [Group K], Prop} {q₀ : ℕ}
    (hVC : VerticalCentralEsc' Typ Esc) (hCI : CoreInvariant Typ) (hCE : CoreInvariant Esc)
    {x y : X} (hx : orderOf x = 2) (hy : orderOf y = 2) (hxy : x ∈ centralizer ({y} : Set X))
    (hKy : SectionRank.IsKGroupCat ↥(centralizer ({y} : Set X))) {Λ N : Subgroup X}
    (hΛ : IsPCompIn 2 (centralizer ({x} : Set X) ⊓ centralizer ({y} : Set X)) Λ)
    (hTyp : Typ ↥Λ) (hyΛ : y ∈ Λ) (hNΛ : N ≤ Λ) (hNp : ⁅N, N⁆ = N)
    (hNSL : HarrisLit.IsSLTwoOver q₀ (↥N ⧸ pPrimeCore 2 ↥N)) (hyN : y ∈ N)
    (hNy : N ≤ centralizer ({y} : Set X))
    {L : Subgroup (barQ ↥(centralizer ({y} : Set X)))} (hL : CFSG.IsComponent L)
    (hLx : conjSub (barMk ↥(centralizer ({y} : Set X)) ⟨x, hxy⟩)⁻¹ L = L)
    (hΛL : (Λ.subgroupOf (centralizer ({y} : Set X))).map
      (barMk ↥(centralizer ({y} : Set X))) ≤ L)
    (hxin : x ∈ zpowers y ⊔ pLayerOf 2 (centralizer ({y} : Set X))) :
    (∃ (w : X) (J N' : Subgroup X), IsDatum q₀ w J N' w ∧ w ∈ J ∧ Typ ↥J) ∨
      ∃ (v x : X) (M Λ : Subgroup X), orderOf v = 2 ∧ M ≤ centralizer ({v} : Set X) ∧
        IsPComponent 2 (M.subgroupOf (centralizer ({v} : Set X))) ∧ Esc ↥M ∧
        orderOf x = 2 ∧ x ∈ centralizer ({v} : Set X) ∧ x ∈ normalizer (M : Set X) ∧
        x ∈ zpowers v ⊔ pLayerOf 2 (centralizer ({v} : Set X)) ∧
        (∃ m ∈ M, m⁻¹ * (x⁻¹ * m * x) ∉ pPrimeCoreOf 2 M) ∧
        Λ ≤ M ⊓ centralizer ({x} : Set X) ∧ Typ ↥Λ := by
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
  have hsub : MG.subgroupOf (centralizer ({y} : Set X)) = M :=
    Subgroup.comap_map_eq_self_of_injective (centralizer ({y} : Set X)).subtype_injective M
  have hMGpc : IsPComponent 2 (MG.subgroupOf (centralizer ({y} : Set X))) := by
    rw [hsub]
    exact (CatalogueBAlternating.pComponent_two_iff M).mpr hM2
  have hΛMG : Λ ≤ MG := fun a ha => ⟨⟨a, hΛY ha⟩, hΛM (mem_subgroupOf.mpr ha), rfl⟩
  rcases hVC ↥(centralizer ({y} : Set X)) hKy M
      ((CatalogueBAlternating.pComponent_two_iff M).mpr hM2) x' (orderOf_mk_centralizer hxy hx)
      hx'N Λ' hΛM hΛC
      ((CatalogueBAlternating.pComponent_two_iff _).mpr hΛ2) hTypΛ' y'
      (orderOf_mk_centralizer hyY hy) hy'Λ' hy'Z with hT | ⟨hE, m, hmM, hm⟩
  · refine Or.inl ⟨y, MG, N, ⟨hy, hMGY, hMGpc, hNΛ.trans hΛMG, hNp, hNSL, hy, hyN, hNy, ?_⟩,
      hΛMG hyΛ, typ_of_mulEquiv hCI eMG hT⟩
    exact mem_fusionZStar_of_commute (hΛMG hyΛ) fun m hm =>
      (mem_centralizer_singleton_iff.mp (hMGY hm)).symm
  have hxMG : x ∈ normalizer (MG : Set X) := by
    rw [mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact ⟨x' * n * x'⁻¹, (mem_normalizer_iff.mp hx'N n).mp hn, rfl⟩
    · intro hh
      have h1 : x * h * x⁻¹ ∈ centralizer ({y} : Set X) := hMGY hh
      have hhC : h ∈ centralizer ({y} : Set X) := by
        have e : h = x⁻¹ * (x * h * x⁻¹) * x := by group
        rw [e]
        exact mul_mem (mul_mem (inv_mem hxy) h1) hxy
      obtain ⟨n, hn, hneq⟩ := hh
      have e : n = x' * ⟨h, hhC⟩ * x'⁻¹ := Subtype.ext hneq
      exact ⟨⟨h, hhC⟩, (mem_normalizer_iff.mp hx'N ⟨h, hhC⟩).mpr (by rwa [← e]), rfl⟩
  have hcore : pPrimeCoreOf 2 MG = (pPrimeCoreOf 2 M).map (centralizer ({y} : Set X)).subtype := by
    rw [pPrimeCoreOf_eq_map_subgroupOf hMGY, hsub]
  have hnt : ∃ n ∈ MG, n⁻¹ * (x⁻¹ * n * x) ∉ pPrimeCoreOf 2 MG := by
    refine ⟨(m : X), ⟨m, hmM, rfl⟩, fun hc => hm ?_⟩
    rw [hcore] at hc
    obtain ⟨z, hz, hzeq⟩ := hc
    have e : z = m⁻¹ * (x'⁻¹ * m * x') := Subtype.ext hzeq
    rwa [← e]
  exact Or.inr ⟨y, x, MG, Λ, hy, hMGY, hMGpc, typ_of_mulEquiv hCE eMG hE, hx, hxy, hxMG, hxin,
    hnt, le_inf hΛMG (hΛ.1.trans inf_le_left), hTyp⟩

end DPrime

open DPrime in
theorem theoremDPrimeEscData_holds
    {Typ Esc : ∀ (K : Type) [Group K], Prop} {q₀ : ℕ} (hq₀ : Odd q₀) (h5 : 5 ≤ q₀)
    (hVC : VerticalCentralEsc' Typ Esc) (hCI : CoreInvariant Typ) (hCE : CoreInvariant Esc)
    (hDT : DiagonalTransfer q₀ Typ) {X : Type} [Group X] [Finite X]
    (hK : ∀ v : X, orderOf v = 2 → SectionRank.IsKGroupCat ↥(centralizer ({v} : Set X)))
    {t : X} {K₀ N : Subgroup X} {c : X} (hD : IsDatum q₀ t K₀ N c) (hTyp : Typ ↥K₀)
    (htL : t ∈ pLayerOf 2 (centralizer ({t} : Set X))) :
    (∃ (w : X) (J N' : Subgroup X), IsDatum q₀ w J N' w ∧ w ∈ J ∧ Typ ↥J) ∨
      ∃ (v x : X) (M Λ : Subgroup X), orderOf v = 2 ∧ M ≤ centralizer ({v} : Set X) ∧
        IsPComponent 2 (M.subgroupOf (centralizer ({v} : Set X))) ∧ Esc ↥M ∧
        orderOf x = 2 ∧ x ∈ centralizer ({v} : Set X) ∧ x ∈ normalizer (M : Set X) ∧
        x ∈ zpowers v ⊔ pLayerOf 2 (centralizer ({v} : Set X)) ∧
        (∃ m ∈ M, m⁻¹ * (x⁻¹ * m * x) ∉ pPrimeCoreOf 2 M) ∧
        Λ ≤ M ⊓ centralizer ({x} : Set X) ∧ Typ ↥Λ := by
  by_cases hct : c = t
  · subst hct
    exact Or.inl ⟨c, K₀, N, hD, hD.2.2.2.1 hD.2.2.2.2.2.2.2.1, hTyp⟩
  obtain ⟨I, hI, hcI, hNI, ⟨eI⟩⟩ := datum_cover hD
  obtain ⟨ht, hK₀C, hK₀pc, hNK₀, hNp, hNSL, hc, hcN, hNc, hcZ⟩ := hD
  have hTypI : Typ ↥I := hCI _ _ ⟨eI.symm⟩ hTyp
  have htc : t ∈ centralizer ({c} : Set X) := mem_centralizer_symm (hK₀C (hNK₀ hcN))
  obtain ⟨-, -, L, hL, hcases, -⟩ := pumpupY_structure (orderOf_mk_centralizer htc ht)
    (le_centralizer_mk hI.1 htc) (isTwoComponent_centralizer_mk hI htc)
  rcases hcases with ⟨hLt, hIL⟩ | ⟨-, hAB, hIδ⟩
  ·
    have hK₀ : IsPCompIn 2 (centralizer ({t} : Set X)) K₀ := ⟨hK₀C, hK₀pc⟩
    have hcK₀ : c ∈ K₀ := hNK₀ hcN
    have hK₀L : K₀ ≤ pLayerOf 2 (centralizer ({t} : Set X)) := le_sSup hK₀
    have hcL : c ∈ pLayerOf 2 (centralizer ({t} : Set X)) := hK₀L hcK₀
    have htLc := GSThmB.lemmaPi t c ht hc htL hcL (GSThmB.lemmaPi' t c K₀ hK₀ hcK₀ hcZ)
    exact vertical_step' hVC hCI hCE ht hc htc (hK c hc) hI hTypI hcI hNI hNp hNSL hcN hNc hL hLt
      hIL (mem_sup_right htLc)
  · obtain ⟨u, hsu, Iu, Nu, hu, hIu, hTypIu, huIu, hNuIu, hNup, hNuSL, huNu, hNuu, hsE⟩ :=
      diagonal_step hq₀ h5 hCI hDT ht hc htc hI hTypI hNI hNSL hcN hL hAB hIδ
    obtain ⟨-, -, Lu, hLu, hcasesu, -⟩ := pumpupY_structure (orderOf_mk_centralizer hsu hc)
      (le_centralizer_mk hIu.1 hsu) (isTwoComponent_centralizer_mk hIu hsu)
    have hLus := conjSub_eq_of_mem_twoLayer hsE hLu
    have hcLu : c ∈ pLayerOf 2 (centralizer ({u} : Set X)) := by
      rw [pLayerOf_two_eq_map]
      exact ⟨_, hsE, rfl⟩
    rcases hcasesu with ⟨-, hIuL⟩ | ⟨hne, -, -⟩
    · exact vertical_step' hVC hCI hCE hc hu hsu (hK u hu) hIu hTypIu huIu hNuIu hNup hNuSL huNu
        hNuu hLu hLus hIuL (mem_sup_right hcLu)
    · exact absurd hLus hne

end CFSG.ComponentClassification.GS82PumpInputs
