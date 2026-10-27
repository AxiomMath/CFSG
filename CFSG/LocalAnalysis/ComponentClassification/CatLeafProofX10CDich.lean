module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10CVal
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB516PumpQuot
public import CFSG.RankThree.PartOne.S10.FiveSuccessorQuasisimple
public import CFSG.LieType.CurtisTits.Recognition
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.S10.Defs

public section

namespace CFSG.ComponentClassification.CatLeafProof.X10CD

open CFSG Subgroup CFSG.ComponentClassification.GSThmB

variable {G : Type*} [Group G]

theorem mem_normalizer_of_map_conj_le {t : G} (ht : t * t = 1) {K : Subgroup G}
    (h : K.map (MulAut.conj t).toMonoidHom ≤ K) : t ∈ normalizer (K : Set G) := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  refine LocalAnalysis.ComponentInitial.mem_normalizer_of_conjSub_le h ?_
  change K.map (MulAut.conj t⁻¹).toMonoidHom ≤ K
  rw [hti]
  exact h

theorem map_sSup_le {S : Set (Subgroup G)} (φ : G →* G) (hS : ∀ K ∈ S, K.map φ ∈ S) :
    (sSup S).map φ ≤ sSup S := by
  rw [map_le_iff_le_comap]
  refine sSup_le fun K hK => ?_
  rw [← map_le_iff_le_comap]
  exact le_sSup (hS K hK)

theorem map_conj_injective {t : G} (ht : t * t = 1) {A B : Subgroup G}
    (h : A.map (MulAut.conj t).toMonoidHom = B.map (MulAut.conj t).toMonoidHom) : A = B := by
  rw [← X10CV.map_conj_map_conj ht A, h, X10CV.map_conj_map_conj ht B]

variable [Finite G]

theorem exists_isComponent_le_sup_conj {t : G} (ht : t * t = 1) {M : Subgroup G}
    (hMC : M ≤ centralizer ({t} : Set G))
    (hM : IsPComponent 2 (M.subgroupOf (centralizer ({t} : Set G)))) (hME : M ≤ layer G) :
    ∃ W : Subgroup G, IsComponent W ∧ M ≤ W ⊔ W.map (MulAut.conj t).toMonoidHom := by
  by_contra hno
  push Not at hno
  set φ := (MulAut.conj t).toMonoidHom with hφ
  have hcent : ∀ W : Subgroup G, IsComponent W → M ≤ centralizer (W : Set G) := by
    intro W hW
    set S : Set (Subgroup G) := {K | IsComponent K ∧ K ≠ W ∧ K ≠ W.map φ} with hS
    have hWt : IsComponent (W.map φ) := LocalCores.isComponent_map_mulEquiv (MulAut.conj t) hW
    have hYc : ∀ V : Subgroup G, IsComponent V → (∀ K ∈ S, K ≠ V) →
        sSup S ≤ centralizer (V : Set G) := fun V hV hSV => sSup_le fun K hK => by
      rcases LocalCores.distinct_components_commute hK.1 hV with h | h
      · exact absurd h (hSV K hK)
      · exact commutator_eq_bot_iff_le_centralizer.mp h
    have hYW := hYc W hW fun K hK => hK.2.1
    have hYWt := hYc (W.map φ) hWt fun K hK => hK.2.2
    have hcomm : ⁅W ⊔ W.map φ, sSup S⁆ = ⊥ := by
      rw [commutator_eq_bot_iff_le_centralizer]
      exact sup_le (le_centralizer_iff.mp hYW) (le_centralizer_iff.mp hYWt)
    have hnX : t ∈ normalizer ((W ⊔ W.map φ : Subgroup G) : Set G) :=
      mem_normalizer_of_map_conj_le ht (by
        rw [Subgroup.map_sup, hφ, X10CV.map_conj_map_conj ht, sup_comm])
    have hnY : t ∈ normalizer ((sSup S : Subgroup G) : Set G) := by
      refine mem_normalizer_of_map_conj_le ht (map_sSup_le φ fun K hK => ?_)
      obtain ⟨hK, h1, h2⟩ := hK
      refine ⟨LocalCores.isComponent_map_mulEquiv (MulAut.conj t) hK, fun h => h2 ?_,
        fun h => h1 (map_conj_injective ht h)⟩
      rw [← h, hφ, X10CV.map_conj_map_conj ht]
    have hEle : layer G ≤ (W ⊔ W.map φ) ⊔ sSup S := sSup_le fun K hK => by
      by_cases h1 : K = W
      · rw [h1]
        exact le_sup_left.trans le_sup_left
      by_cases h2 : K = W.map φ
      · rw [h2]
        exact le_sup_right.trans le_sup_left
      · exact (le_sSup (show K ∈ S from ⟨hK, h1, h2⟩)).trans le_sup_right
    rcases Pump516.le_or_le_of_isPComponent_centralizer hcomm hnX hnY hMC hM (hME.trans hEle)
      with h | h
    · exact absurd h (hno W hW)
    · exact h.trans hYW
  have hML : layer G ≤ centralizer (M : Set G) :=
    sSup_le fun W hW => le_centralizer_iff.mp (hcent W hW)
  have hperf : ⁅M, M⁆ = M :=
    Subgroup.isPerfect_iff.mp (B5a.isPerfect_of_isPComponent_subgroupOf hMC hM)
  have hab : ⁅M, M⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr (hME.trans hML)
  have hnt : Nontrivial M := B5a.nontrivial_of_isPComponent_subgroupOf hMC hM
  rw [hperf] at hab
  rw [hab] at hnt
  exact not_nontrivial _ hnt

theorem map_conj_eq_of_le {t : G} {W M : Subgroup G} (hW : IsComponent W) (hMW : M ≤ W)
    (hMC : M ≤ centralizer ({t} : Set G)) (hMp : ⁅M, M⁆ = M) (hM1 : M ≠ ⊥) :
    W.map (MulAut.conj t).toMonoidHom = W :=
  X10CV.map_conj_eq_of_mem_normalizer (Pump516.mem_normalizer_of_le_centralizer hW hMW hMp hM1 hMC)

theorem commute_of_map_conj_ne {t : G} {W : Subgroup G} (hW : IsComponent W)
    (hne : W.map (MulAut.conj t).toMonoidHom ≠ W) :
    ∀ x ∈ W, ∀ y ∈ W.map (MulAut.conj t).toMonoidHom, x * y = y * x := by
  have hW' := LocalCores.isComponent_map_mulEquiv (MulAut.conj t) hW
  have hcomm := (LocalCores.distinct_components_commute hW hW').resolve_left fun h => hne h.symm
  intro x hx y hy
  exact (mem_centralizer_iff.mp ((commutator_eq_bot_iff_le_centralizer.mp hcomm) hx) y hy).symm

omit [Finite G] in
theorem isQuasisimple_range_diagHom {t : G} {W : Subgroup G} (hW : IsComponent W)
    (hc : ∀ x ∈ W, ∀ y ∈ W.map (MulAut.conj t).toMonoidHom, x * y = y * x) :
    IsQuasisimple (X10CV.diagHom t hc).range := by
  refine LieType.CurtisTits.isQuasisimple_of_surjective hW.1
    (X10CV.diagHom t hc).rangeRestrict_surjective ?_
  by_contra hall
  push Not at hall
  have hWW' : ∀ x ∈ W, x ∈ W.map (MulAut.conj t).toMonoidHom := fun x hx => by
    have h1 : (x : G) * (t * x * t⁻¹) = 1 :=
      congrArg (fun y : (X10CV.diagHom t hc).range => (y : G)) (hall ⟨x, hx⟩)
    have h2 : (x : G) = t * x⁻¹ * t⁻¹ :=
      calc (x : G) = (t * x * t⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left h1
        _ = t * x⁻¹ * t⁻¹ := by group
    rw [h2]
    exact X10CV.conj_mem_map_conj (inv_mem hx)
  obtain ⟨-, -, a, b, hab⟩ := hW.1
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  apply hab
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext (hc a a.2 b (hWW' b b.2))

omit [Finite G] in
theorem range_diagHom_le_centralizer {t : G} (ht : t * t = 1) {W : Subgroup G}
    (hc : ∀ x ∈ W, ∀ y ∈ W.map (MulAut.conj t).toMonoidHom, x * y = y * x) :
    (X10CV.diagHom t hc).range ≤ centralizer ({t} : Set G) := by
  rintro _ ⟨x, rfl⟩
  rw [mem_centralizer_singleton_iff, X10CV.diagHom_apply]
  have h1 := hc x x.2 (t * x * t⁻¹) (X10CV.conj_mem_map_conj x.2)
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have e1 : (x : G) * (t * x * t⁻¹) * t = x * t * x := by group
  have e2 : t * ((x : G) * (t * x * t⁻¹)) = x * t⁻¹ * x := by
    rw [h1]
    calc t * (t * (x : G) * t⁻¹ * x) = (t * t) * x * t⁻¹ * x := by group
      _ = x * t⁻¹ * x := by rw [ht]; group
  rw [e1, e2, hti]

theorem eq_range_diagHom {t : G} (ht : t * t = 1) {W M : Subgroup G} (hW : IsComponent W)
    (hc : ∀ x ∈ W, ∀ y ∈ W.map (MulAut.conj t).toMonoidHom, x * y = y * x)
    (hMC : M ≤ centralizer ({t} : Set G))
    (hM : IsPComponent 2 (M.subgroupOf (centralizer ({t} : Set G))))
    (hMW : M ≤ W ⊔ W.map (MulAut.conj t).toMonoidHom) : M = (X10CV.diagHom t hc).range := by
  have hperf := B5a.isPerfect_of_isPComponent_subgroupOf hMC hM
  have hMp : ⁅M, M⁆ = M := Subgroup.isPerfect_iff.mp hperf
  have hMD := X10CV.le_range_diagHom ht hc hMC hMW hMp
  have hDC := range_diagHom_le_centralizer ht hc
  have hsn : (M.subgroupOf (X10CV.diagHom t hc).range).IsSubnormal := by
    obtain ⟨-, -, hs, -, -⟩ := hM
    have h1 := hs.comap (Subgroup.inclusion hDC)
    have h2 : (M.subgroupOf (centralizer ({t} : Set G))).comap (Subgroup.inclusion hDC) =
        M.subgroupOf (X10CV.diagHom t hc).range := by
      ext y
      simp only [mem_comap, mem_subgroupOf, Subgroup.coe_inclusion]
    rwa [h2] at h1
  have hM1 : M ≠ ⊥ := by
    intro hb
    have hnt : Nontrivial M := B5a.nontrivial_of_isPComponent_subgroupOf hMC hM
    rw [hb] at hnt
    exact not_nontrivial _ hnt
  exact RankThree.PartOne.eq_of_isSubnormal_of_isPerfect_of_isQuasisimple
    (isQuasisimple_range_diagHom hW hc) hMD hperf hM1 hsn

end CFSG.ComponentClassification.CatLeafProof.X10CD
