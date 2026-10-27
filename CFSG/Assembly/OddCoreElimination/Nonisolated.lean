module

public import CFSG.Assembly.OddCoreEliminationStatements
import CFSG.Assembly.OddCoreElimination.IsolatedFour
import CFSG.Assembly.OddCoreElimination.TwoGroups
import CFSG.Assembly.OddCoreElimination.Transfer
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.NormalFourGeometry
import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.Assembly.Dichotomy

variable {G : Type*} [Group G]

private theorem le_centralizer_self {p : ℕ} {V : Subgroup G} (hV : IsElemAbelian p V) :
    V ≤ Subgroup.centralizer (V : Set G) := by
  intro v hv
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  exact congrArg Subtype.val (hV.1.is_comm.comm (⟨w, hw⟩ : V) ⟨v, hv⟩)

private theorem le_centralizer_singleton {p : ℕ} {V : Subgroup G} (hV : IsElemAbelian p V)
    {v : G} (hv : v ∈ V) : V ≤ Subgroup.centralizer ({v} : Set G) :=
  (le_centralizer_self hV).trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hv))

private theorem map_conj_centralizer_le (g x : G) :
    (Subgroup.centralizer ({x} : Set G)).map (MulAut.conj g⁻¹).toMonoidHom ≤
      Subgroup.centralizer ({(MulAut.conj g⁻¹).toMonoidHom x} : Set G) := by
  have h := Subgroup.map_centralizer_le_centralizer_image ({x} : Set G)
    (MulAut.conj g⁻¹).toMonoidHom
  rwa [Set.image_singleton] at h

private theorem sq_mem_of_relIndex_eq_two {S S₀ : Subgroup G} (h : S₀.relIndex S = 2) {s : G}
    (hs : s ∈ S) : s ^ 2 ∈ S₀ := by
  have h' := Subgroup.sq_mem_of_index_two (H := S₀.subgroupOf S) h ⟨s, hs⟩
  rwa [Subgroup.mem_subgroupOf, Subgroup.coe_pow] at h'

variable [Finite G]

private theorem pRank_centralizer_conj_le (g x : G) :
    pRank 2 (Subgroup.centralizer ({g⁻¹ * x * g} : Set G)) ≤
      pRank 2 (Subgroup.centralizer ({x} : Set G)) := by
  have h := map_conj_centralizer_le g⁻¹ (g⁻¹ * x * g)
  have hx : (MulAut.conj g⁻¹⁻¹).toMonoidHom (g⁻¹ * x * g) = x := by
    simp [MulAut.conj_apply, mul_assoc]
  rw [hx] at h
  exact (CFSG.SectionRank.pRank_le_map one_lt_two _ (MulEquiv.injective _) _).trans
    (CFSG.SectionRank.pRank_mono one_lt_two h)

private theorem exists_map_conj_le_sylow (S : Sylow 2 G) {P : Subgroup G} (hP : IsPGroup 2 P) :
    ∃ g : G, P.map (MulAut.conj g⁻¹).toMonoidHom ≤ S := by
  obtain ⟨T, hPT⟩ := hP.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq G T S
  refine ⟨h⁻¹, ?_⟩
  rw [inv_inv]
  rintro _ ⟨x, hx, rfl⟩
  rw [← hh, Sylow.coe_subgroup_smul]
  exact Subgroup.smul_mem_pointwise_smul x (MulAut.conj h) _ (hPT hx)

private theorem exists_conj_inf_centralizer_le (S : Sylow 2 G) (v : G) :
    ∃ g : G, ((S : Subgroup G) ⊓ Subgroup.centralizer ({v} : Set G)).map
        (MulAut.conj g⁻¹).toMonoidHom ≤ S ∧
      pRank 2 (Subgroup.centralizer ({v} : Set G)) ≤
        pRank 2 ((S : Subgroup G) ⊓
          Subgroup.centralizer ({(MulAut.conj g⁻¹).toMonoidHom v} : Set G)) := by
  set C := Subgroup.centralizer ({v} : Set G)
  have hP : IsPGroup 2 (((S : Subgroup G) ⊓ C).subgroupOf C) :=
    (S.isPGroup'.to_le inf_le_left).of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
  obtain ⟨T, hPT⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := exists_map_conj_le_sylow S (T.isPGroup'.map C.subtype)
  have hPT₁ : (S : Subgroup G) ⊓ C ≤ (T : Subgroup C).map C.subtype := fun x hx =>
    ⟨⟨x, hx.2⟩, hPT (show (⟨x, hx.2⟩ : C) ∈ ((S : Subgroup G) ⊓ C).subgroupOf C from hx), rfl⟩
  refine ⟨g, (Subgroup.map_mono hPT₁).trans hg, ?_⟩
  have hTC := (Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom)
    (Subgroup.map_subtype_le (T : Subgroup C))).trans (map_conj_centralizer_le g v)
  calc pRank 2 C = pRank 2 ((T : Subgroup C).map C.subtype) :=
        (CFSG.ProperTwoGeneratedCore.sylow_image_two_rank_eq C T).symm
    _ ≤ pRank 2 (((T : Subgroup C).map C.subtype).map (MulAut.conj g⁻¹).toMonoidHom) :=
        CFSG.SectionRank.pRank_le_map one_lt_two _ (MulEquiv.injective _) _
    _ ≤ _ := CFSG.SectionRank.pRank_mono one_lt_two (le_inf hg hTC)

private theorem exists_elemAbelian_eight_le {S : Subgroup G} (h3 : 3 ≤ pRank 2 S) :
    ∃ E : Subgroup G, E ≤ S ∧ IsElemAbelian 2 E ∧ Nat.card E = 8 := by
  rw [assembly_pRank_eq_open] at h3
  obtain ⟨E, hES, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank one_lt_two S
  have hdiv : 2 ^ 3 ∣ Nat.card E := by
    rw [hEcard]
    exact Nat.pow_dvd_pow 2 h3
  obtain ⟨F, hFcard, -, hFE⟩ := Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_two
    (H := (⊥ : Subgroup G)) (L := E) (by simp) hdiv bot_le
  exact ⟨F, hFE.trans hES,
    CFSG.LargeEvenClassification.Helpers.elementary_subgroup_of_le E F hE hFE,
    by simpa using hFcard⟩

private theorem three_le_pRank_centralizer_of_mem {S A : Subgroup G} (hS : IsPGroup 2 S)
    (h3 : 3 ≤ pRank 2 S) (hAS : A ≤ S) (hSA : S ≤ Subgroup.normalizer (A : Set G))
    (hA : IsElemAbelian 2 A) (hA4 : Nat.card A = 4) {w : G}
    (hw : w ∈ S ⊓ Subgroup.centralizer (A : Set G)) (hw2 : orderOf w = 2) :
    3 ≤ pRank 2 (S ⊓ Subgroup.centralizer ({w} : Set G)) := by
  by_cases hwA : w ∈ A
  · obtain ⟨E, hES, hE, hE8⟩ := exists_elemAbelian_eight_le h3
    refine (three_le_pRank_inf_centralizer hS hAS hSA hA hA4 hES hE hE8).trans
      (CFSG.SectionRank.pRank_mono one_lt_two (inf_le_inf_left S ?_))
    exact Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hwA)
  · have hcomm : A ≤ Subgroup.centralizer (Subgroup.zpowers w : Set G) :=
      Subgroup.le_centralizer_iff.mpr (Subgroup.zpowers_le.mpr hw.2)
    obtain ⟨E, -, hwE, hE, hE8, hEle⟩ :=
      CFSG.LargeEvenClassification.Helpers.commuting_disjoint_elementary_product
        (firstRank := 2) (secondRank := 1) A (Subgroup.zpowers w) hA
        (CFSG.ProperTwoGeneratedCore.involution_zpowers_elementary w hw2) (by simpa using hA4)
        (by simp [hw2]) hcomm
        (CFSG.ProperTwoGeneratedCore.involution_zpowers_disjoint A w hw2 hwA)
    refine CFSG.SectionRank.le_pRank one_lt_two (le_inf ?_ ?_) hE hE8
    · exact hEle.trans (sup_le hAS (Subgroup.zpowers_le.mpr hw.1))
    · exact le_centralizer_singleton hE (hwE (Subgroup.mem_zpowers w))

theorem nonisolatedConjugate : NonisolatedConjugateStatement := by
  intro G _ _ hperf hrank S V hVS hV hV4 h2
  have hS : IsPGroup 2 (S : Subgroup G) := S.isPGroup'
  have hS3 : 3 ≤ pRank 2 (S : Subgroup G) := (pRank_sylow_eq_twoRank S).symm ▸ hrank
  obtain ⟨A, hAS, hSA, hA, hA4⟩ := exists_normal_four_of_three_le_pRank hS hS3
  obtain ⟨hidx, hVS₀, z, hz2, hzeq, -, hvstr⟩ :=
    isolated_four_centralizer_structure hS hS3 hAS hSA hA hA4 hVS hV hV4 h2
  obtain ⟨v, hvV, hvS₀⟩ := IsConcreteLE.not_le_iff_exists.mp hVS₀
  obtain ⟨-, -, -, -, -, -, -, r, hrR, hrz⟩ := hvstr v hvV hvS₀ _ rfl
  have hzVS₀ : z ∈ V ⊓ ((S : Subgroup G) ⊓ Subgroup.centralizer (A : Set G)) := by
    rw [hzeq]
    exact Subgroup.mem_zpowers z
  have hz1 : z ≠ 1 := by
    rintro rfl
    simp at hz2
  have hv1 : v ≠ 1 := by
    rintro rfl
    exact hvS₀ (Subgroup.one_mem _)
  have hv2 : orderOf v = 2 := orderOf_eq_prime (hV.2 v hvV) hv1
  have hinv : ∀ x : G, orderOf x = 2 → 3 ≤ pRank 2 (Subgroup.centralizer ({x} : Set G)) := by
    intro x hx
    obtain ⟨g, hg⟩ := derivedInvolutionTransfer G S _ inf_le_left hidx x
      (hperf ▸ Subgroup.mem_top x) hx
    have hgx : orderOf (g⁻¹ * x * g) = 2 := by
      simpa only [MulAut.conj_apply, inv_inv, hx] using (MulAut.conj g⁻¹).orderOf_eq x
    exact (three_le_pRank_centralizer_of_mem hS hS3 hAS hSA hA hA4 hg hgx).trans
      ((CFSG.SectionRank.pRank_mono one_lt_two inf_le_right).trans
        (pRank_centralizer_conj_le g x))
  obtain ⟨g, hgS, hgrank⟩ := exists_conj_inf_centralizer_le S v
  set c := (MulAut.conj g⁻¹).toMonoidHom
  have hVSv : V ≤ (S : Subgroup G) ⊓ Subgroup.centralizer ({v} : Set G) :=
    le_inf hVS (le_centralizer_singleton hV hvV)
  have hVgS : V.map c ≤ S := (Subgroup.map_mono hVSv).trans hgS
  refine ⟨g, hVgS, ?_⟩
  change 3 ≤ pRank 2 ((S : Subgroup G) ⊓ Subgroup.centralizer (V.map c : Set G))
  have hVg : IsElemAbelian 2 (V.map c) := CFSG.SectionRank.isElemAbelian_map hV c
  have hVg4 : Nat.card (V.map c) = 4 := by
    rw [Subgroup.card_map_of_injective (MulEquiv.injective _), hV4]
  have hVg2 : 2 ≤ pRank 2 ((S : Subgroup G) ⊓ Subgroup.centralizer (V.map c : Set G)) :=
    CFSG.SectionRank.le_pRank one_lt_two (le_inf hVgS (le_centralizer_self hVg)) hVg
      (by rw [hVg4]; norm_num)
  by_contra hlt
  obtain ⟨-, -, z', -, -, hz'uniq, hvgstr⟩ :=
    isolated_four_centralizer_structure hS hS3 hAS hSA hA hA4 hVgS hVg hVg4 (by omega)
  have hzg : c z ∈ (S : Subgroup G) ⊓ Subgroup.centralizer (A : Set G) := by
    have hrS : c r ∈ (S : Subgroup G) := hgS ⟨r, ⟨hrR.1.1, hrR.2⟩, rfl⟩
    have h := sq_mem_of_relIndex_eq_two hidx hrS
    rwa [← map_pow, hrz] at h
  have hvg : c v ∉ (S : Subgroup G) ⊓ Subgroup.centralizer (A : Set G) := by
    intro hvg
    rcases hz'uniq (c z) ⟨Subgroup.mem_map_of_mem c hzVS₀.1, hzg⟩ with h | h
    · exact hz1 ((MulEquiv.injective _) (h.trans (map_one c).symm))
    rcases hz'uniq (c v) ⟨Subgroup.mem_map_of_mem c hvV, hvg⟩ with h' | h'
    · exact hv1 ((MulEquiv.injective _) (h'.trans (map_one c).symm))
    exact hvS₀ ((MulEquiv.injective _) (h'.trans h.symm) ▸ hzVS₀.2)
  obtain ⟨-, hCVg, -⟩ := hvgstr (c v) (Subgroup.mem_map_of_mem c hvV) hvg _ rfl
  have := (hinv v hv2).trans hgrank
  rw [← hCVg] at this
  omega

end CFSG.Assembly.Dichotomy
