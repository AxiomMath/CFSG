module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParC4
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParRank1Assembly

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar

open CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.Quasithin
  CFSG.Open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
  CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGen
  CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

@[expose] def OddWitness {S : Type} [Group S] (P : Subgroup S) : Prop :=
  ∃ N : Subgroup S, N ≤ P ∧ IsPGroup 2 ↥N ∧ P ≤ Subgroup.normalizer (N : Set S) ∧
    ∃ (p : ℕ) (y c : S), p.Prime ∧ p ≠ 2 ∧ y ∈ pElementSubgroup 2 P ∧
      (∃ a : ℕ, orderOf y = p ^ a) ∧ c ∈ N ∧ y * c * y⁻¹ ≠ c

theorem iSup_comap_eq {G Q' ι : Type*} [Group G] [Group Q'] (q : G →* Q')
    (hq : Function.Surjective q) (A : ι → Subgroup Q') {J : Set ι} (hJ : J.Nonempty) :
    (⨆ j ∈ J, (A j).comap q) = (⨆ j ∈ J, A j).comap q := by
  apply le_antisymm
  · exact iSup₂_le fun j hj => Subgroup.comap_mono (le_iSup₂ (f := fun j (_ : j ∈ J) => A j) j hj)
  · obtain ⟨j₀, hj₀⟩ := hJ
    set C := ⨆ j ∈ J, (A j).comap q with hC
    have hmap : C.map q = ⨆ j ∈ J, A j := by
      rw [hC, Subgroup.map_iSup]
      simp only [Subgroup.map_iSup, Subgroup.map_comap_eq_self_of_surjective hq]
    have hker : q.ker ≤ C := fun z hz =>
      le_iSup₂ (f := fun j (_ : j ∈ J) => (A j).comap q) j₀ hj₀
        (by rw [Subgroup.mem_comap, MonoidHom.mem_ker.1 hz]; exact one_mem _)
    rw [← hmap, Subgroup.comap_map_eq, sup_eq_left.2 hker]

theorem clause_four_of_witness {Y : Type} [Group Y] [Finite Y] {L R P : Subgroup Y}
    (hR : R ≤ Subgroup.normalizer (L : Set Y)) (hS : IsSylowTwoOf (R ⊓ L) L)
    (hP : IsMinOverBorel L (R ⊓ L) P)
    (D0 : MinParData (⊤ : Subgroup (↥L ⧸ Subgroup.center ↥L))
      (((R ⊓ L).subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L))))
    (hwit : ∀ J : Set D0.ι, J.Nonempty → (⨆ j ∈ J, D0.P j) ≠ ⊤ →
      OddWitness (⨆ j ∈ J, D0.P j)) :
    conjClosure P R ≠ L →
      ⁅pCoreOf 2 (twoResidual (pElementSubgroup 2 (conjClosure P R))),
        twoResidual (pElementSubgroup 2 (conjClosure P R))⁆ ≠ ⊥ := by
  classical
  intro hQL hVD
  let DW := minParData_of_center D0 hS
  have hq : Function.Surjective (QuotientGroup.mk' (Subgroup.center ↥L)) :=
    QuotientGroup.mk'_surjective _
  have hex : ∃ J : Set D0.ι, J.Nonempty ∧ conjClosure P R =
      ⨆ k ∈ J, ((D0.P k).comap (QuotientGroup.mk' (Subgroup.center ↥L))).map L.subtype :=
    exists_iSup_conjClosure hR hP DW
  obtain ⟨J, hJne, hQ⟩ := hex
  have h1 : (⨆ k ∈ J, ((D0.P k).comap (QuotientGroup.mk' (Subgroup.center ↥L))).map L.subtype) =
      ((⨆ j ∈ J, D0.P j).comap (QuotientGroup.mk' (Subgroup.center ↥L))).map L.subtype := by
    rw [← iSup_comap_eq _ hq D0.P hJne]
    simp only [Subgroup.map_iSup]
  have hPbar : (⨆ j ∈ J, D0.P j) ≠ ⊤ := by
    intro htop
    apply hQL
    rw [hQ, h1, htop, Subgroup.comap_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  obtain ⟨N, hNP, hN2, hPN, p, y, c, hp, hp2, hyP, hyord, hcN, hne'⟩ := hwit J hJne hPbar
  set Pbar := ⨆ j ∈ J, D0.P j with hPbardef
  set Q := conjClosure P R with hQdef
  have hQ' : Q = ((Pbar).comap (QuotientGroup.mk' (Subgroup.center ↥L))).map L.subtype := by
    exact hQ.trans h1
  have hQL' : Q ≤ L := by rw [hQ']; exact Subgroup.map_subtype_le _
  have hmemQ : ∀ w₀ : ↥L, (w₀ : Y) ∈ Q → (QuotientGroup.mk' (Subgroup.center ↥L)) w₀ ∈ Pbar := by
    intro w₀ hw₀
    rw [hQ'] at hw₀
    obtain ⟨a, ha, hae⟩ := hw₀
    have : a = w₀ := Subtype.ext hae
    exact this ▸ ha
  have hWQ : pElementSubgroup 2 Q ≤ Q := pElementSubgroup_le Q
  have hodd := odd_centralizes_of_hVD (Q := Q) (L := L) (Nb := N) hQL' hN2
    (fun w₀ hw₀ => hPN (hmemQ w₀ (hWQ hw₀)))
    (fun c' hc' => by
      obtain ⟨w, hw⟩ := hq c'
      have hc'P : c' ∈ Pbar := hNP hc'
      obtain ⟨s, hs⟩ := (IsPGroup.iff_orderOf.1 hN2) ⟨c', hc'⟩
      have hs' : orderOf c' = 2 ^ s := by rw [← hs, ← Subgroup.orderOf_coe]
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨e, ⟨k, hk⟩, hfe⟩ := exists_pElement_lift (QuotientGroup.mk' (Subgroup.center ↥L))
        (p := 2) (x := w) ⟨s, by rw [hw]; exact hs'⟩
      refine ⟨w ^ e, by rw [hfe, hw], ?_, k, hk⟩
      have hwQ : (w : Y) ∈ Q := by
        rw [hQ']
        exact ⟨w, by
          show (QuotientGroup.mk' (Subgroup.center ↥L)) w ∈ Pbar
          rw [hw]; exact hc'P, rfl⟩
      have h1 : ((w ^ e : ↥L) : Y) ∈ Q := by
        have : ((w ^ e : ↥L) : Y) = (w : Y) ^ e := by simp
        rw [this]; exact Q.pow_mem hwQ e
      exact Subgroup.subset_closure ⟨h1, k, by rw [Subgroup.orderOf_coe]; exact hk⟩) hVD
  have hy1 := pElementSubgroup_le_map_pElementSubgroup_comap (L := L) Pbar hyP
  obtain ⟨a, ha, haq⟩ := hy1
  have hay : (a : Y) ∈ pElementSubgroup 2 Q := by
    have := map_pElementSubgroup_le (L := L) ((Pbar).comap (QuotientGroup.mk' (Subgroup.center ↥L)))
      ⟨a, ha, rfl⟩
    rw [← hQ'] at this
    exact this
  exact hne' (hodd p hp hp2 y ⟨a, Subgroup.mem_subgroupOf.2 hay, haq⟩ hyord c hcN)

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar
