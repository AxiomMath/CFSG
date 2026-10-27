module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Steps

public section

namespace CFSG.ComponentClassification.GrSLit.HeSingle

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

variable {X : Type} [Group X] [Finite X]

theorem le_map_pLayer {a : X} (ha : orderOf a = 2) {N T : Subgroup X} (haN : a ∈ N)
    (hT : T ≤ centralizer ({a} : Set X) ⊓ N)
    (hTpc : IsPComponent 2 (T.subgroupOf (centralizer ({a} : Set X) ⊓ N))) :
    T ≤ (pLayer ↥N 2).map N.subtype := by
  have ha' : orderOf (⟨a, haN⟩ : N) = 2 := by rw [Subgroup.orderOf_mk]; exact ha
  have hcena := UGSChain.centralizer_mk_eq_subgroupOf haN
  have hT'C : T.subgroupOf N ≤ centralizer ({(⟨a, haN⟩ : N)} : Set N) := by
    rw [hcena]
    intro y hy
    exact mem_subgroupOf.mpr (hT (mem_subgroupOf.mp hy))
  have hT'pc : IsPComponent 2 ((T.subgroupOf N).subgroupOf
      (centralizer ({(⟨a, haN⟩ : N)} : Set N))) := by
    rw [hcena, UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' inf_le_right 2
      Nat.prime_two]
    exact hTpc
  have h1 : (T.subgroupOf N).subgroupOf (centralizer ({(⟨a, haN⟩ : N)} : Set N)) ≤
      pLayer ↥(centralizer ({(⟨a, haN⟩ : N)} : Set N)) 2 := le_sSup hT'pc
  have h2 := map_mono (f := (centralizer ({(⟨a, haN⟩ : N)} : Set N)).subtype) h1
  rw [map_subgroupOf_eq_of_le hT'C] at h2
  have hza : IsPGroup 2 (zpowers (⟨a, haN⟩ : N)) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, ha', pow_one])
  have h3 := ClassicalInvolution.l2PrimeBalance ↥N (zpowers (⟨a, haN⟩ : N)) hza
  rw [centralizer_zpowers_eq] at h3
  have h4 := h2.trans h3
  intro x hx
  exact ⟨⟨x, (hT hx).2⟩, h4 (show (⟨x, (hT hx).2⟩ : N) ∈ T.subgroupOf N from hx), rfl⟩

theorem map_pPrimeCore_le_oddIn {K N : Subgroup X} (hKN : K ≤ N)
    (hKp : IsPComponent 2 (K.subgroupOf N)) : (pPrimeCore 2 K).map K.subtype ≤ oddIn N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsub : (K.subgroupOf N).IsSubnormal :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 K N hKN).1 hKp).1
  have h := map_mono (f := N.subtype) (Walter.map_pPrimeCore_le_of_isSubnormal hsub)
  rwa [pPrimeCore_map_subgroupOf 2 K N hKN] at h

theorem not_isHeldType_of_lt (hHN : HeldNotProperFixedInput)
    (hK : Assembly.KProper Blueprint.Catalog X) {F M T : Subgroup X} (hF : F ≠ ⊤) (hMF : M ≤ F)
    (hMp : IsPComponent 2 (M.subgroupOf F)) {a : X} (ha : orderOf a = 2)
    (hMa : conjugate M a = M) (hTM : T ≤ M ⊓ centralizer ({a} : Set X))
    (hTp : IsPComponent 2 (T.subgroupOf (M ⊓ centralizer ({a} : Set X))))
    (hlt : (pPrimeCore 2 T).index < (pPrimeCore 2 M).index) :
    ¬ IsHeldType (T ⧸ Open.fusionZStar T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have haa : a * a = 1 := by rw [← pow_two, ← ha, pow_orderOf_eq_one]
  have haN : a ∈ normalizer (M : Set X) := by
    rw [mem_normalizer_iff]
    intro y
    rw [← UnbalancedLayer.mem_conjugate_iff, hMa]
  set c : MulAut M := M.normalizerMonoidHom ⟨a, haN⟩ with hcdef
  have hcapp : ∀ x : M, ((c x : M) : X) = a * x * a⁻¹ := fun x => rfl
  have hc : ∀ x, c (c x) = x := by
    intro x
    apply Subtype.ext
    rw [hcapp, hcapp]
    calc a * (a * (x : X) * a⁻¹) * a⁻¹ = (a * a) * x * (a * a)⁻¹ := by group
      _ = x := by rw [haa]; group
  have hfixC : fixedSubgroup c = (M ⊓ centralizer ({a} : Set X)).subgroupOf M := by
    ext x
    rw [LocalAnalysis.ComponentInitial.mem_fixedSubgroup_iff, mem_subgroupOf, mem_inf,
      mem_centralizer_singleton_iff]
    constructor
    · intro hx
      have h1 := congrArg Subtype.val hx
      rw [hcapp] at h1
      refine ⟨x.2, ?_⟩
      calc (x : X) * a = a * x * a⁻¹ * a := by rw [h1]
        _ = a * x := by group
    · rintro ⟨-, hx⟩
      apply Subtype.ext
      rw [hcapp]
      calc a * (x : X) * a⁻¹ = x * a * a⁻¹ := by rw [hx]
        _ = x := by group
  have hTM' : T ≤ M := hTM.trans inf_le_left
  have hT'C : T.subgroupOf M ≤ fixedSubgroup c := by
    rw [hfixC]
    intro x hx
    rw [mem_subgroupOf] at hx ⊢
    exact hTM hx
  have hT'p : IsPComponent 2 ((T.subgroupOf M).subgroupOf (fixedSubgroup c)) := by
    rw [hfixC]
    exact (UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' (L := T) inf_le_left 2
      Nat.prime_two).mpr hTp
  let eT : T ≃* T.subgroupOf M := (subgroupOfEquivOfLe hTM').symm
  have hlt' : (pPrimeCore 2 (T.subgroupOf M)).index < (pPrimeCore 2 M).index := by
    rw [index_eq_card, index_eq_card,
      ← UnbalancingLocal.Correspondence.card_quotient_pPrimeCore_congr eT, ← index_eq_card,
      ← index_eq_card]
    exact hlt
  have hMq : IsQuasisimple (M ⧸ pPrimeCore 2 M) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 M F hMF).1 hMp).2.2
  obtain ⟨σ, P, hσ, hPF, hP, hPne, ⟨e⟩⟩ := exists_simple_fixed_component hMq c hc hT'C hT'p hlt'
  obtain ⟨eS⟩ := nonempty_quotient_center_equiv_fusionZStar M
  obtain ⟨-, hS, hnab⟩ := hMq
  have hcat := catalog_fusionZStar_of_isPComponent hK hF hMF hMp
  have hP' := hHN _ hS hnab (SectionRank.catalog_of_mulEquiv eS hcat) σ hσ P hPF hP hPne
  obtain ⟨eZ⟩ := GSThmB.OddQuot.nonempty_fusionZStar_equiv_of_surjective eT.toMonoidHom
    eT.surjective (by
      rw [show eT.toMonoidHom.ker = ⊥ from (MonoidHom.ker_eq_bot_iff _).mpr eT.injective,
        card_bot]
      norm_num)
  rintro ⟨f⟩
  exact hP' ⟨(eZ.trans e).symm.trans f⟩

end CFSG.ComponentClassification.GrSLit.HeSingle
