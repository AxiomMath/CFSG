module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.Defs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.ParabLevi
public import CFSG.LocalAnalysis.AGLEmbeddingD2.SquareGeneric
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabHub
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeCore
public import CFSG.Foundations
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.AGLEmbedding.D1GlobalU
public import CFSG.LocalAnalysis.AGLEmbedding.Reduction
public import CFSG.LocalAnalysis.AGLEmbedding.TwoCoreObstruction
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.B2Thompson
public import CFSG.Quasithin.Background.SmithC27RDefs
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput

open CFSG.Open CFSG.AGLEmbedding CFSG.LieType.BorelTits CFSG.LieType.Universal
  CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime CFSG.AGLEmbeddingD2.ParabLevi

section Defs

variable {K Y : Type} [Group K] [Group Y]

@[expose] def LeviOb (D : UniversalRootDatum K) (H : Fin D.rank → Subgroup K) (π : K →* Y)
    (I : Set (Fin D.rank)) : Prop :=
  ∃ (m : ℕ) (C : Fin m → Subgroup K) (E : Subgroup K),
    (⨆ k, H k) ≤ E ∧ E ≤ (⨆ k, H k) ⊔ leviM D I ∧ Group.IsSolvable ↥E ∧
    (∀ i, C i ≤ leviM D I ∧ E ≤ Subgroup.normalizer (C i : Set K) ∧
      CFSG.IsQuasisimple ↥((C i).map π) ∧
      IsClassicalTwoOrG2 (↥((C i).map π) ⧸ Subgroup.center ↥((C i).map π))) ∧
    (∀ i j, i ≠ j → C i ≤ Subgroup.centralizer (C j : Set K)) ∧
    leviM D I ≤ E ⊔ ⨆ i, C i

@[expose] def CentOb (D : UniversalRootDatum K) (I : Set (Fin D.rank)) : Prop :=
  ∀ k : K, (∀ u ∈ leviRad D I, k * u = u * k) → k ∈ leviRad D I ⊔ Subgroup.center K

end Defs

section Helpers

theorem isSolvable_sup_of_normalizes' {G : Type} [Group G] {R S : Subgroup G}
    (hR : Group.IsSolvable ↥R) (hS : Group.IsSolvable ↥S)
    (hSN : S ≤ Subgroup.normalizer (R : Set G)) : Group.IsSolvable ↥(R ⊔ S) := by
  have hle : R ≤ R ⊔ S := le_sup_left
  have hnorm : (R.subgroupOf (R ⊔ S)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr
      (sup_le Subgroup.le_normalizer hSN)
  have hRs : Group.IsSolvable ↥(R.subgroupOf (R ⊔ S)) :=
    Group.isSolvable_of_isSolvable_injective (f := (Subgroup.subgroupOfEquivOfLe hle).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hle).injective
  let φ : ↥S →* ↥(R ⊔ S) ⧸ R.subgroupOf (R ⊔ S) :=
    (QuotientGroup.mk' (R.subgroupOf (R ⊔ S))).comp (Subgroup.inclusion le_sup_right)
  have hφ : Function.Surjective φ := by
    intro y
    obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective _ y
    have hv : (v : G) ∈ (↑(S ⊔ R) : Set G) := by rw [sup_comm]; exact v.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right S R hSN] at hv
    obtain ⟨s, hs, r, hr, hsr⟩ := hv
    refine ⟨⟨s, hs⟩, ?_⟩
    have hv' : v = Subgroup.inclusion le_sup_right ⟨s, hs⟩ *
        (⟨r, Subgroup.mem_sup_left hr⟩ : ↥(R ⊔ S)) := Subtype.ext hsr.symm
    show (QuotientGroup.mk' _) (Subgroup.inclusion le_sup_right ⟨s, hs⟩) = _
    rw [hv', map_mul]
    have : (QuotientGroup.mk' (R.subgroupOf (R ⊔ S))) (⟨r, Subgroup.mem_sup_left hr⟩ : ↥(R ⊔ S)) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (by rw [Subgroup.mem_subgroupOf]; exact hr)
    rw [this, mul_one]
  have : Group.IsSolvable (↥(R ⊔ S) ⧸ R.subgroupOf (R ⊔ S)) :=
    Group.isSolvable_of_surjective hφ
  exact Group.isSolvable_of_ker_le_range (R.subgroupOf (R ⊔ S)).subtype
    (QuotientGroup.mk' (R.subgroupOf (R ⊔ S)))
    (by rw [QuotientGroup.ker_mk']; simp)

theorem isSolvable_sup_of_normalizes {G : Type} [Group G] [Finite G] {R S : Subgroup G}
    (hR : IsPGroup 2 R) (hS : Group.IsSolvable ↥S)
    (hSN : S ≤ Subgroup.normalizer (R : Set G)) : Group.IsSolvable ↥(R ⊔ S) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRs : Group.IsSolvable ↥R := by
    have := hR.isNilpotent
    infer_instance
  exact isSolvable_sup_of_normalizes' hRs hS hSN

theorem isSolvable_iSup_of_commute {G : Type} [Group G] {ι : Type} [Fintype ι]
    (H : ι → Subgroup G) (hs : ∀ i, Group.IsSolvable ↥(H i))
    (hc : ∀ i j, i ≠ j → H i ≤ Subgroup.centralizer (H j : Set G)) :
    Group.IsSolvable ↥(⨆ i, H i) := by
  classical
  have key : ∀ s : Finset ι, Group.IsSolvable ↥(⨆ i ∈ s, H i) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have : (⨆ i ∈ (∅ : Finset ι), H i) = ⊥ := by simp
      rw [this]
      infer_instance
    | insert a s ha ih =>
      rw [Finset.iSup_insert, sup_comm]
      refine isSolvable_sup_of_normalizes' ih (hs a) ?_
      refine CFSG.LieType.Steinberg.le_normalizer_iSup fun j =>
        CFSG.LieType.Steinberg.le_normalizer_iSup fun hj => ?_
      exact (hc a j (fun e => ha (e ▸ hj))).trans (Subgroup.centralizer_le_normalizer _)
  have e : (⨆ i ∈ Finset.univ, H i) = ⨆ i, H i := iSup_congr fun i => iSup_pos (Finset.mem_univ i)
  rw [← e]
  exact key Finset.univ

end Helpers

section Parabolic

variable {K Y : Type} [Group K] [Group Y] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K} {π : K →* Y} {M : ℕ}

theorem parab_data [Finite K] [Finite Y] (h : BorelQuotient D n H π M) {A : Subgroup Y}
    (hA : A ≠ ⊤) (T : Sylow 2 Y)
    (hNT : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ A) :
    ∃ π' : K →* Y, BorelQuotient D n H π' M ∧ ∃ I : Set (Fin D.rank), I ≠ Set.univ ∧
      borel D H ≤ A.comap π' ∧ I = negIndices D (A.comap π') := by
  obtain ⟨π', hQ', -, hBA⟩ := CFSG.AGLEmbeddingD2.SquareGeneric.BorelQuotient.exists_conj_parab h T hNT
  refine ⟨π', hQ', negIndices D (A.comap π'), ?_, hBA, rfl⟩
  have hBJ : (borel D H).map π' ≤ A := fun y ⟨b, hb, hby⟩ => hby ▸ hBA hb
  obtain ⟨j, hj⟩ := CFSG.AGLEmbedding.LieOut.exists_node_not_mem_negIndices hQ' hBJ hA
  intro hI
  exact hj (hI ▸ Set.mem_univ j)

theorem map_leviRad_le_radical [Finite K] [Finite Y] (h : BorelQuotient D n H π M)
    {A R : Subgroup Y} (hR : R = pCoreOf 2 A) (hBA : borel D H ≤ A.comap π) :
    (leviRad D (negIndices D (A.comap π))).map π ≤ R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set I := negIndices D (A.comap π) with hI
  have hUP : leviRad D I ≤ A.comap π := le_sup_left.trans (leviRad_sup_leviM_le hBA)
  have hPeq : A.comap π = borel D H ⊔ ⨆ i ∈ I, rankOne D.rootGroup i :=
    eq_borel_sup_rankOne h.ct h.extras hBA
  have hPN : A.comap π ≤ Subgroup.normalizer (leviRad D I : Set K) := by
    rw [hPeq]
    exact sup_le (borel_le_normalizer_leviRad h.ct h.extras)
      (iSup₂_le fun i hi => rankOne_le_normalizer_leviRad h.extras hi)
  have hAN : A ≤ Subgroup.normalizer (((leviRad D I).map π : Subgroup Y) : Set Y) := by
    have := (Subgroup.map_mono hPN).trans (Subgroup.le_normalizer_map π)
    rwa [Subgroup.map_comap_eq_self_of_surjective h.surj] at this
  have hle : (leviRad D I).map π ≤ pCoreOf 2 A :=
    le_pCoreOf_of_le_normalizer 2 ((Subgroup.map_mono hUP).trans (Subgroup.map_comap_le π A)) hAN
      ((isPGroup_leviRad h.extras h.pGroup).map π)
  exact hle.trans hR.symm.le

theorem leviStructure_of_borelQuotient [Finite K] [Finite Y] (h : BorelQuotient D n H π M)
    {R : Subgroup Y}
    (hR : R = pCoreOf 2 ((⊤ : Subgroup Y) ⊓ Subgroup.normalizer (R : Set Y)))
    (hne : (⊤ : Subgroup Y) ⊓ Subgroup.normalizer (R : Set Y) ≠ ⊤)
    (hpar : ∃ T : Sylow 2 Y, Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤
      (⊤ : Subgroup Y) ⊓ Subgroup.normalizer (R : Set Y))
    (hOb : ∀ π' : K →* Y, BorelQuotient D n H π' M → ∀ I : Set (Fin D.rank), I ≠ Set.univ →
      LeviOb D H π' I) :
    LeviStructure (⊤ : Subgroup Y) R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨A, hAdef⟩ : ∃ A : Subgroup Y, A = (⊤ : Subgroup Y) ⊓ Subgroup.normalizer (R : Set Y) :=
    ⟨_, rfl⟩
  rw [← hAdef] at hR hne hpar
  unfold LeviStructure
  rw [← hAdef]
  obtain ⟨T, hT⟩ := hpar
  obtain ⟨π', hQ', I, hI, hBA, hIeq⟩ := parab_data h hne T hT
  obtain ⟨m, C, E, hTE, hEle, hEs, hC, hcomm, hMle⟩ := hOb π' hQ' I hI
  obtain ⟨P, hPdef⟩ : ∃ P : Subgroup K, P = A.comap π' := ⟨_, rfl⟩
  rw [← hPdef] at hBA hIeq
  have hAmap : A = P.map π' := by
    rw [hPdef, Subgroup.map_comap_eq_self_of_surjective hQ'.surj]
  have hPeq : P = borel D H ⊔ ⨆ i ∈ I, rankOne D.rootGroup i := by
    rw [hIeq]; exact eq_borel_sup_rankOne hQ'.ct hQ'.extras hBA
  have hMP : leviM D I ≤ P := iSup₂_le fun i hi => by
    rw [hIeq] at hi; exact rankOne_le_of_mem_negIndices hBA hi
  have hTP : (⨆ k, H k) ≤ P := le_sup_left.trans hBA
  have hUR : (leviRad D I).map π' ≤ R := by
    have := map_leviRad_le_radical hQ' hR (A := A) (by rw [← hPdef]; exact hBA)
    rwa [← hPdef, ← hIeq] at this
  have hRA : R ≤ A := hR ▸ pCoreOf_le 2 A
  have hAN : A ≤ Subgroup.normalizer (R : Set Y) := by rw [hAdef]; exact inf_le_right
  have hEP : E ≤ P := hEle.trans (sup_le hTP hMP)
  have hEA : E.map π' ≤ A := by rw [hAmap]; exact Subgroup.map_mono hEP
  have hR2 : IsPGroup 2 R := by rw [hR]; exact pCoreOf_isPGroup 2 A
  have hEs' : Group.IsSolvable ↥(E.map π') := by
    have : Group.IsSolvable ↥E := hEs
    exact Group.isSolvable_of_surjective (f := (π'.comp E.subtype).codRestrict (E.map π')
      (fun x => ⟨x, x.2, rfl⟩)) (fun y => by
        obtain ⟨x, hx, hxy⟩ := y.2
        exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩)
  have hDA : R ⊔ E.map π' ≤ A := sup_le hRA hEA
  refine ⟨m, fun i => (C i).map π', R ⊔ E.map π', le_sup_left, hDA,
    isSolvable_sup_of_normalizes hR2 hEs' (hEA.trans hAN), ?_, ?_, ?_⟩
  · intro i
    obtain ⟨hCM, hEN, hq, hcl⟩ := hC i
    have hCA : (C i).map π' ≤ A := by
      rw [hAmap]; exact Subgroup.map_mono (hCM.trans hMP)
    refine ⟨hCA, hq, hcl, ?_⟩
    have hEN' : E.map π' ≤ Subgroup.normalizer (((C i).map π' : Subgroup Y) : Set Y) :=
      (Subgroup.map_mono hEN).trans (Subgroup.le_normalizer_map π')
    exact sup_le ((le_sup_right : R ≤ (C i).map π' ⊔ R).trans Subgroup.le_normalizer)
      (le_normalizer_sup hEN' (hEA.trans hAN))
  · intro i j hij
    rintro _ ⟨c, hc, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨d, hd, rfl⟩
    have := Subgroup.mem_centralizer_iff.mp (hcomm i j hij hc) d hd
    rw [← map_mul, ← map_mul, this]
  · apply le_antisymm
    · have hPT : P ≤ (⨆ k, H k) ⊔ (leviRad D I ⊔ leviM D I) := by
        have := le_torus_sup_leviRad_sup_leviM hQ'.ct hQ'.extras hBA
        rwa [← hIeq] at this
      rw [hAmap]
      refine (Subgroup.map_mono hPT).trans ?_
      rw [Subgroup.map_sup, Subgroup.map_sup]
      refine sup_le ?_ (sup_le ?_ ?_)
      · exact (Subgroup.map_mono hTE).trans (le_sup_right.trans le_sup_left)
      · exact hUR.trans (le_sup_left.trans le_sup_left)
      · refine (Subgroup.map_mono hMle).trans ?_
        rw [Subgroup.map_sup, Subgroup.map_iSup]
        exact sup_le (le_sup_right.trans le_sup_left) (le_sup_right)
    · exact sup_le hDA (iSup_le fun i => by
        rw [hAmap]; exact Subgroup.map_mono ((hC i).1.trans hMP))

theorem conj_eq_of_conj_mem_ker (h : BorelQuotient D n H π M) {u k : K} {s : ℕ}
    (hu : u ^ 2 ^ s = 1) (hπ : π (k * u * k⁻¹) = π u) : k * u * k⁻¹ = u := by
  obtain ⟨c, hc⟩ : ∃ c, c = k * u * k⁻¹ := ⟨_, rfl⟩
  rw [← hc] at hπ ⊢
  obtain ⟨z, hzdef⟩ : ∃ z, z = c * u⁻¹ := ⟨_, rfl⟩
  have hz : z ∈ π.ker := by
    rw [hzdef, MonoidHom.mem_ker, map_mul, map_inv, hπ, mul_inv_cancel]
  have hzc := Subgroup.mem_center_iff.mp (h.ker_central _ hz)
  have hzM := h.ker_pow _ hz
  have hcs : c ^ 2 ^ s = 1 := by
    rw [hc, conj_pow, hu, mul_one, mul_inv_cancel]
  have hcz : c = z * u := by rw [hzdef]; group
  have hz2 : z = u⁻¹ * c := by
    calc z = u⁻¹ * (u * z) := by group
      _ = u⁻¹ * (z * u) := by rw [hzc u]
      _ = u⁻¹ * c := by rw [← hcz]
  have hcomm : Commute u c := by
    show u * c = c * u
    rw [hcz, ← mul_assoc, hzc u]
  have h1 : z = 1 := eq_one_of_central_odd h.odd hzM hz2 hcomm hu hcs
  rw [h1] at hcz
  simpa using hcz

theorem radical_data [Finite K] [Finite Y] (h : BorelQuotient D n H π M) {R : Subgroup Y}
    (hR : R = pCoreOf 2 ((⊤ : Subgroup Y) ⊓ Subgroup.normalizer (R : Set Y)))
    (hne : (⊤ : Subgroup Y) ⊓ Subgroup.normalizer (R : Set Y) ≠ ⊤)
    (hpar : ∃ T : Sylow 2 Y, Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤
      (⊤ : Subgroup Y) ⊓ Subgroup.normalizer (R : Set Y)) :
    ∃ π' : K →* Y, BorelQuotient D n H π' M ∧ ∃ I : Set (Fin D.rank), I ≠ Set.univ ∧
      (leviRad D I).map π' ≤ R := by
  obtain ⟨A, hAdef⟩ : ∃ A : Subgroup Y, A = (⊤ : Subgroup Y) ⊓ Subgroup.normalizer (R : Set Y) :=
    ⟨_, rfl⟩
  rw [← hAdef] at hR hne hpar
  obtain ⟨T, hT⟩ := hpar
  obtain ⟨π', hQ', I, hI, hBA, hIeq⟩ := parab_data h hne T hT
  refine ⟨π', hQ', I, hI, ?_⟩
  have := map_leviRad_le_radical hQ' hR hBA
  rwa [← hIeq] at this

theorem centralizer_of_borelQuotient [Finite K] [Finite Y] (h : BorelQuotient D n H π M)
    {R : Subgroup Y}
    (hR : R = pCoreOf 2 ((⊤ : Subgroup Y) ⊓ Subgroup.normalizer (R : Set Y)))
    (hne : (⊤ : Subgroup Y) ⊓ Subgroup.normalizer (R : Set Y) ≠ ⊤)
    (hpar : ∃ T : Sylow 2 Y, Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤
      (⊤ : Subgroup Y) ⊓ Subgroup.normalizer (R : Set Y))
    (hZY : Subgroup.center Y = ⊥)
    (hCent : ∀ I : Set (Fin D.rank), I ≠ Set.univ → CentOb D I) :
    ∀ x : Y, (∀ r ∈ R, x * r = r * x) → x ∈ R := by
  obtain ⟨π', hQ', I, hI, hUR⟩ := radical_data h hR hne hpar
  intro x hx
  obtain ⟨k, rfl⟩ := hQ'.surj x
  have hk : k ∈ leviRad D I ⊔ Subgroup.center K := by
    refine hCent I hI k fun u hu => ?_
    have hπu : π' u ∈ R := hUR ⟨u, hu, rfl⟩
    have hc : π' k * π' u = π' u * π' k := hx _ hπu
    obtain ⟨s, hs⟩ := isPGroup_leviRad hQ'.extras hQ'.pGroup (I := I) ⟨u, hu⟩
    have hs' : u ^ 2 ^ s = 1 := by simpa using congrArg Subtype.val hs
    have h1 : π' (k * u * k⁻¹) = π' u := by
      rw [map_mul, map_mul, map_inv, hc, mul_assoc, mul_inv_cancel, mul_one]
    exact mul_inv_eq_iff_eq_mul.mp (conj_eq_of_conj_mem_ker hQ' hs' h1)
  have : π' k ∈ (leviRad D I ⊔ Subgroup.center K).map π' := Subgroup.mem_map_of_mem π' hk
  have hcen : (Subgroup.center K).map π' = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).mpr ?_
    rintro _ ⟨z, hz, rfl⟩
    have : π' z ∈ Subgroup.center Y := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨k', rfl⟩ := hQ'.surj y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz k']
    rw [hZY] at this
    exact this
  rw [Subgroup.map_sup, hcen, sup_bot_eq] at this
  exact hUR this

end Parabolic

end CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput
