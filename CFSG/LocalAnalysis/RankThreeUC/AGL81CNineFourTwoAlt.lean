module

public import CFSG.GroupTheory.Permutation.AltLocalClosure
public import CFSG.RankThree.PartOne.CTP.StrongPGlue
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Theorem5_1
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {X : Type} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]

theorem normalizer_map_le {A : Type*} [Group A] {N K : Subgroup X}
    (e : ↥K ≃* A) {U : Subgroup ↥K}
    (hU : Subgroup.normalizer (U.map K.subtype : Set X) ≤ N) :
    Subgroup.normalizer (U.map (e : ↥K →* A) :
        Set A) ≤
      ((N ⊓ K).subgroupOf K).map (e : ↥K →* A) := by
  intro g hg
  have hmap : (Subgroup.normalizer (U : Set ↥K)).map (e : ↥K →* A) =
      Subgroup.normalizer (U.map (e : ↥K →* A) :
        Set A) := by
    simpa only [MulEquiv.toMonoidHom_eq_coe] using Subgroup.map_equiv_normalizer_eq U e
  rw [← hmap] at hg
  have hgK : e.symm g ∈ Subgroup.normalizer (U : Set ↥K) :=
    Subgroup.mem_map_equiv.mp hg
  have hgX : K.subtype (e.symm g) ∈
      Subgroup.normalizer (U.map K.subtype : Set X) :=
    Subgroup.le_normalizer_map (H := U) K.subtype
      (Subgroup.mem_map_of_mem K.subtype hgK)
  have hgN : K.subtype (e.symm g) ∈ N := hU hgX
  have hgB : e.symm g ∈ (N ⊓ K).subgroupOf K :=
    Subgroup.mem_subgroupOf.mpr ⟨hgN, (e.symm g).2⟩
  have hgg : g = (e : ↥K →* A) (e.symm g) :=
    (e.apply_symm_apply g).symm
  rw [hgg]
  exact Subgroup.mem_map_of_mem (e : ↥K →* A) hgB

theorem map_subtype_comap_transport {A : Type*} [Group A] {N K : Subgroup X} (e : ↥K ≃* A)
    {R : Subgroup A} (hR : R ≤ ((N ⊓ K).subgroupOf K).map (e : ↥K →* A)) :
    (R.comap (e : ↥K →* A)).map K.subtype ≤ N ⊓ K ∧
      (R.comap (e : ↥K →* A)).map (e : ↥K →* A) = R ∧
      (IsPGroup p R → IsPGroup p ((R.comap (e : ↥K →* A)).map K.subtype)) ∧
      (R ≠ ⊥ → (R.comap (e : ↥K →* A)).map K.subtype ≠ ⊥) ∧
      (CFSG.Open.IsElemAbelian 3 R →
        CFSG.Open.IsElemAbelian 3 ((R.comap (e : ↥K →* A)).map K.subtype)) ∧
      Nat.card ((R.comap (e : ↥K →* A)).map K.subtype) = Nat.card R := by
  have hcomap : R.comap (e : ↥K →* A) ≤ (N ⊓ K).subgroupOf K := by
    rw [← Subgroup.comap_map_eq_self_of_injective
      (f := (e : ↥K →* A)) e.injective ((N ⊓ K).subgroupOf K)]
    exact Subgroup.comap_mono hR
  have hcomapN : R.comap (e : ↥K →* A) ≤ N.subgroupOf K := by
    rwa [Subgroup.inf_subgroupOf_right] at hcomap
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Subgroup.subgroupOf_map_subtype N K]
    exact Subgroup.map_mono hcomapN
  · exact Subgroup.map_comap_eq_self_of_surjective
      (f := (e : ↥K →* A)) e.surjective R
  · intro hRp
    exact (hRp.comap_of_injective
      (e : ↥K →* A) e.injective).map K.subtype
  · intro hRne hbot
    apply hRne
    have hU : R.comap (e : ↥K →* A) = ⊥ :=
      Subgroup.map_injective K.subtype_injective (by rw [hbot, Subgroup.map_bot])
    rw [← Subgroup.map_comap_eq_self_of_surjective
      (f := (e : ↥K →* A)) e.surjective R, hU,
      Subgroup.map_bot]
  · intro hRE
    exact (CFSG.Open.IsElemAbelian.comap hRE e.injective).map K.subtype
  · rw [Subgroup.card_map_of_injective K.subtype_injective,
      ← Subgroup.card_map_of_injective
        (f := (e : ↥K →* A)) e.injective,
      Subgroup.map_comap_eq_self_of_surjective
        (f := (e : ↥K →* A)) e.surjective]

theorem exists_sylow_le_image {A : Type*} [Group A] {N K : Subgroup X} [K.Normal]
    (hN : IsStronglyPEmbedded p N) (e : ↥K ≃* A) :
    ∃ PA : Sylow p A, (PA : Subgroup A) ≤ ((N ⊓ K).subgroupOf K).map (e : ↥K →* A) := by
  classical
  obtain ⟨P, hP, hPN⟩ := hN.exists_isSylowOf_le
  set PS : Sylow p X := hP.2.1.toSylow
    (by simpa [Subgroup.relIndex_top_right] using hP.2.2) with hPSdef
  have hPScoe : (PS : Subgroup X) = P := by
    rw [hPSdef, IsPGroup.toSylow_coe]
  obtain ⟨T, hT⟩ := CFSG.Glauberman.sylow_inf_normal PS (N := K)
  have hTB : (T : Subgroup ↥K) ≤ (N ⊓ K).subgroupOf K := by
    rw [hT, hPScoe]
    exact Subgroup.subgroupOf_mono K (inf_le_inf hPN le_rfl)
  refine ⟨T.mapSurjective (f := (e : ↥K →* A))
    e.surjective, ?_⟩
  rw [Sylow.coe_mapSurjective]
  exact Subgroup.map_mono hTB

theorem exists_e9_le_inf_of_altTwoP {X : Type} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    (hp7 : 7 ≤ p) {N K : Subgroup X} [K.Normal]
    (hN : CFSG.RankThree.PartOne.IsStronglyPEmbedded p N)
    (e : ↥K ≃* alternatingGroup (Fin (2 * p))) :
    ∃ R : Subgroup X, R ≤ N ⊓ K ∧ CFSG.Open.IsElemAbelian 3 R ∧ Nat.card R = 9 := by
  classical
  let B : Subgroup (alternatingGroup (Fin (2 * p))) :=
    ((N ⊓ K).subgroupOf K).map (e : ↥K →* alternatingGroup (Fin (2 * p)))
  obtain ⟨PA, hPAB⟩ := exists_sylow_le_image (p := p) hN e
  have hp2 : p ≠ 2 := by omega
  have hpn : p ≤ 2 * p := by omega
  obtain ⟨c, hcB, hccyc, hccard⟩ :=
    CFSG.AltLocalClosure.exists_isCycle_mem_of_sylow_le (n := 2 * p) hp2 hpn PA hPAB
  have hcne : c ≠ 1 := by
    intro hc1
    have h0 : (c : Equiv.Perm (Fin (2 * p))).support.card = 0 := by
      rw [hc1]
      simp
    rw [hccard] at h0
    omega
  let Rc : Subgroup (alternatingGroup (Fin (2 * p))) := Subgroup.zpowers c
  have hRccard : Nat.card Rc = p := by
    change Nat.card (Subgroup.zpowers c) = p
    rw [Nat.card_zpowers]
    have hord : orderOf c = p := by
      rw [← Subgroup.orderOf_coe c, hccyc.orderOf, hccard]
    rw [hord]
  have hRcp : IsPGroup p Rc := IsPGroup.of_card (n := 1) (by simpa using hRccard)
  have hRcne : Rc ≠ ⊥ := by
    rw [Ne, Subgroup.zpowers_eq_bot]
    exact hcne
  have hRcB : Rc ≤ B := Subgroup.zpowers_le.mpr hcB
  let U : Subgroup ↥K := Rc.comap (e : ↥K →* alternatingGroup (Fin (2 * p)))
  obtain ⟨hUle, hUmap, hUp, hUne, -, -⟩ :=
    map_subtype_comap_transport (p := p) (N := N) (K := K) e hRcB
  have hNnorm : Subgroup.normalizer (U.map K.subtype : Set X) ≤ N :=
    hN.normalizer_le (hUne hRcne) (hUp hRcp) (hUle.trans (inf_le_left : N ⊓ K ≤ N))
  have hNA : Subgroup.normalizer (Rc : Set (alternatingGroup (Fin (2 * p)))) ≤ B := by
    have h := normalizer_map_le (N := N) (K := K) e hNnorm
    rwa [hUmap] at h
  have hcent : Subgroup.centralizer ({c} : Set (alternatingGroup (Fin (2 * p)))) ≤ B :=
    (CFSG.RankThree.PartOne.StrongP.centralizer_singleton_le_normalizer_zpowers c).trans hNA
  have hc6 : 6 ≤ 2 * p - (c : Equiv.Perm (Fin (2 * p))).support.card := by
    rw [hccard]
    omega
  obtain ⟨E, hEcent, hEE, hEcard⟩ :=
    CFSG.AltLocalClosure.exists_isElemAbelian_nine_le_centralizer (n := 2 * p) c hc6
  have hEB : E ≤ B := hEcent.trans hcent
  obtain ⟨hEle, -, -, -, hEE', hEcard'⟩ :=
    map_subtype_comap_transport (p := p) (N := N) (K := K) e hEB
  exact ⟨(E.comap (e : ↥K →* alternatingGroup (Fin (2 * p)))).map K.subtype, hEle,
    hEE' hEE, hEcard'.trans hEcard⟩

theorem le_of_altTwoP {X : Type} [Group X] [Finite X] {p : ℕ} [Fact p.Prime] (hp7 : 7 ≤ p)
    {N K : Subgroup X} [K.Normal]
    (hN : CFSG.RankThree.PartOne.IsStronglyPEmbedded p N)
    (e : ↥K ≃* alternatingGroup (Fin (2 * p)))
    (h3 : ∀ R : Subgroup X, R ≤ N ⊓ K → CFSG.Open.IsElemAbelian 3 R → Nat.card R = 9 →
      Subgroup.normalizer (R : Set X) ≤ N) :
    K ≤ N := by
  classical
  let B : Subgroup (alternatingGroup (Fin (2 * p))) :=
    ((N ⊓ K).subgroupOf K).map (e : ↥K →* alternatingGroup (Fin (2 * p)))
  obtain ⟨PA, hPAB⟩ := exists_sylow_le_image (p := p) hN e
  have hpB : ∀ R : Subgroup (alternatingGroup (Fin (2 * p))), R ≤ B → IsPGroup p R →
      R ≠ ⊥ → Subgroup.normalizer (R : Set (alternatingGroup (Fin (2 * p)))) ≤ B := by
    intro R hRB hRp hRne
    obtain ⟨hUle, hUmap, hUp, hUne, -, -⟩ :=
      map_subtype_comap_transport (p := p) (N := N) (K := K) e hRB
    have hNnorm :
        Subgroup.normalizer
          ((R.comap (e : ↥K →* alternatingGroup (Fin (2 * p)))).map K.subtype :
            Set X) ≤ N :=
      hN.normalizer_le (hUne hRne) (hUp hRp) (hUle.trans (inf_le_left : N ⊓ K ≤ N))
    have h := normalizer_map_le (N := N) (K := K) e hNnorm
    rwa [hUmap] at h
  have h3B : ∀ R : Subgroup (alternatingGroup (Fin (2 * p))), R ≤ B →
      CFSG.Open.IsElemAbelian 3 R → Nat.card R = 9 →
      Subgroup.normalizer (R : Set (alternatingGroup (Fin (2 * p)))) ≤ B := by
    intro R hRB hRE hRcard
    obtain ⟨hUle, hUmap, -, -, hUE, hUcard⟩ :=
      map_subtype_comap_transport (p := p) (N := N) (K := K) e hRB
    have hNnorm :
        Subgroup.normalizer
          ((R.comap (e : ↥K →* alternatingGroup (Fin (2 * p)))).map K.subtype :
            Set X) ≤ N :=
      h3 ((R.comap (e : ↥K →* alternatingGroup (Fin (2 * p)))).map K.subtype)
        hUle (hUE hRE) (hUcard.trans hRcard)
    have h := normalizer_map_le (N := N) (K := K) e hNnorm
    rwa [hUmap] at h
  have hBtop : B = ⊤ :=
    CFSG.AltLocalClosure.eq_top_of_sylow_le_of_normalizer_le (p := p) hp7 PA hPAB hpB h3B
  intro x hx
  have hx' : e ⟨x, hx⟩ ∈ B := by
    rw [hBtop]
    exact Subgroup.mem_top _
  have hxb : (⟨x, hx⟩ : ↥K) ∈ (N ⊓ K).subgroupOf K := by
    simpa using (Subgroup.mem_map_equiv.mp hx')
  exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hxb)).1

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
