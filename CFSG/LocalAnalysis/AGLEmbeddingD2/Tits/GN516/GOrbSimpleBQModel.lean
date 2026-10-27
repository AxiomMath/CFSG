module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbNodes
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbSimpleBQAct
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GraphOrbitDefs
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbReduceBasic

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516.SimpleBQ

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.LieType.Steinberg CFSG.AGLEmbedding.ParabHub
  CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.AGLEmbeddingD2.Tits.GN516.Nodes
open scoped commutatorElement

section Generic

variable {Y : Type*} [Group Y]

theorem conjSub_le_conjClosure {X R : Subgroup Y} {r : Y} (hr : r ∈ R) :
    B6.conjSub r X ≤ conjClosure X R := by
  intro x hx
  rw [B6.mem_conjSub] at hx
  have := mem_conjClosure hr hx
  simpa [mul_assoc] using this

theorem map_top_subtype (L : Subgroup Y) : (⊤ : Subgroup ↥L).map L.subtype = L := by
  rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]

end Generic

section Nodes

variable {K S : Type} [Group K] [Group S] {D : UniversalRootDatum K}
  {H : Fin D.rank → Subgroup K} {π : K →* S}

theorem parJ_eq_sup_iSup_singleton (J : Set (Fin D.rank)) :
    parJ D H J = borel D H ⊔ ⨆ j ∈ J, parJ D H {j} := by
  have hsingle : ∀ j : Fin D.rank, parJ D H {j} = borel D H ⊔ rankOne D.rootGroup j := by
    intro j
    show borel D H ⊔ ⨆ i ∈ ({j} : Set (Fin D.rank)), rankOne D.rootGroup i = _
    rw [iSup_singleton]
  apply le_antisymm
  · show borel D H ⊔ ⨆ j ∈ J, rankOne D.rootGroup j ≤ _
    refine sup_le le_sup_left (iSup₂_le fun j hj => le_sup_of_le_right ?_)
    exact (rankOne_le_parJ (Set.mem_singleton j)).trans
      (le_iSup₂_of_le (f := fun k (_ : k ∈ J) => parJ D H {k}) j hj le_rfl)
  · refine sup_le (borel_le_parJ J) (iSup₂_le fun j hj => ?_)
    rw [hsingle j]
    exact sup_le (borel_le_parJ J) (rankOne_le_parJ hj)

theorem map_parJ_eq_sup (J : Set (Fin D.rank)) :
    (parJ D H J).map π = (borel D H).map π ⊔ ⨆ j ∈ J, (parJ D H {j}).map π := by
  rw [parJ_eq_sup_iSup_singleton J, Subgroup.map_sup]
  congr 1
  simp only [Subgroup.map_iSup]

end Nodes

section Model

variable {Y : Type} [Group Y] [Finite Y] {L R P : Subgroup Y} {K : Type} [Group K] [Finite K]
  {D : UniversalRootDatum K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {π : K →* ↥L}
  {M : ℕ}

theorem exists_borelQuotient_conj {S₀ : Subgroup Y} (hS : IsSylowTwoOf S₀ L)
    (h : BorelQuotient D n H π M) :
    ∃ π' : K →* ↥L, BorelQuotient D n H π' M ∧ S₀.subgroupOf L = (posUnipotent D).map π' := by
  obtain ⟨T, hT⟩ := McLaughlin.Lie.exists_sylow_of_isSylowTwoOf hS
  obtain ⟨π', hπ', hker, hT'⟩ := h.exists_conj_eq T
  refine ⟨π', ⟨h.ct, h.extras, h.pGroup, hπ', h.odd, h.torus_pow,
    fun z hz => h.ker_central z (hker ▸ hz), fun z hz => h.ker_pow z (hker ▸ hz)⟩, ?_⟩
  rw [← hT, hT']

theorem map_actHom_inf (hRN : R ≤ Subgroup.normalizer (L : Set Y)) (r : ↥R) :
    ((R ⊓ L).subgroupOf L).map (actHom hRN r).toMonoidHom = (R ⊓ L).subgroupOf L := by
  apply Subgroup.map_injective L.subtype_injective
  rw [map_map_subtype_eq_conjSub (actHom hRN r) (coe_actHom hRN r),
    Subgroup.map_subgroupOf_eq_of_le inf_le_right]
  exact B6.conjSub_eq_self (mem_normalizer_inf hRN r.2)

theorem range_actHom_fix (hRN : R ≤ Subgroup.normalizer (L : Set Y))
    (hT : (R ⊓ L).subgroupOf L = (posUnipotent D).map π) :
    ∀ α ∈ (actHom hRN).range,
      ((posUnipotent D).map π).map α.toMonoidHom = (posUnipotent D).map π := by
  rintro _ ⟨r, rfl⟩
  rw [← hT]
  exact map_actHom_inf hRN r

theorem exists_node (h : BorelQuotient D n H π M)
    (hT : (R ⊓ L).subgroupOf L = (posUnipotent D).map π) (hMin : IsMinOverBorel L (R ⊓ L) P) :
    ∃ i, P.subgroupOf L = (parJ D H {i}).map π := by
  apply exists_eq_map_parJ h
  rw [← hT, ← GOrbReduce.isMinOverBorel_map_iff (ψ := L.subtype) L.subtype_injective,
    map_top_subtype, Subgroup.map_subgroupOf_eq_of_le inf_le_right,
    Subgroup.map_subgroupOf_eq_of_le hMin.1]
  exact hMin

theorem map_parJ_singleton_nodeHom (h : BorelQuotient D n H π M) (𝒜 : Subgroup (MulAut ↥L))
    (h𝒜 : ∀ α ∈ 𝒜, ((posUnipotent D).map π).map α.toMonoidHom = (posUnipotent D).map π)
    (a : ↥𝒜) (j : Fin D.rank) :
    ((parJ D H {j}).map π).map a.1.toMonoidHom = (parJ D H {nodeHom h 𝒜 h𝒜 a j}).map π :=
  map_parJ_singleton_nodePerm h a.1 (h𝒜 a.1 a.2) j

theorem nodeHom_ne_of_not_mem_normalizer (h : BorelQuotient D n H π M)
    (𝒜 : Subgroup (MulAut ↥L))
    (h𝒜 : ∀ α ∈ 𝒜, ((posUnipotent D).map π).map α.toMonoidHom = (posUnipotent D).map π)
    (hPL : P ≤ L) {i : Fin D.rank} (hi : P.subgroupOf L = (parJ D H {i}).map π)
    (a : ↥𝒜) {r : Y} (ha : ∀ x : ↥L, ((a.1 x : ↥L) : Y) = r * x * r⁻¹)
    (hrP : r ∉ Subgroup.normalizer (P : Set Y)) : nodeHom h 𝒜 h𝒜 a i ≠ i := by
  intro hai
  apply hrP
  have h1 : ((parJ D H {i}).map π).map a.1.toMonoidHom = (parJ D H {i}).map π := by
    rw [map_parJ_singleton_nodeHom h 𝒜 h𝒜 a i, hai]
  have hP : (P.subgroupOf L).map L.subtype = P := Subgroup.map_subgroupOf_eq_of_le hPL
  have h2 : (P.subgroupOf L).map a.1.toMonoidHom = P.subgroupOf L := by
    rw [hi]
    exact h1
  have h3 := map_map_subtype_eq_conjSub a.1 ha (P.subgroupOf L)
  rw [h2, hP] at h3
  exact Subgroup.mem_normalizer_iff_map_conj_eq.2 h3.symm

@[expose] def nodeOrbit (h : BorelQuotient D n H π M) (𝒜 : Subgroup (MulAut ↥L))
    (h𝒜 : ∀ α ∈ 𝒜, ((posUnipotent D).map π).map α.toMonoidHom = (posUnipotent D).map π)
    (i : Fin D.rank) : Set (Fin D.rank) :=
  Set.range fun a : ↥𝒜 => nodeHom h 𝒜 h𝒜 a i

@[expose] def CoreConcl (h : BorelQuotient D n H π M) (𝒜 : Subgroup (MulAut ↥L))
    (h𝒜 : ∀ α ∈ 𝒜, ((posUnipotent D).map π).map α.toMonoidHom = (posUnipotent D).map π)
    (i : Fin D.rank) : Prop :=
  Group.IsSolvable ↥((unipJ D (nodeOrbit h 𝒜 h𝒜 i)).map π) ∨
    (∃ C : Subgroup ↥L, C ≤ pElementSubgroup 2 C ∧ C ≤ (unipJ D (nodeOrbit h 𝒜 h𝒜 i)).map π ∧
      (unipJ D (nodeOrbit h 𝒜 h𝒜 i)).map π ≤ Subgroup.normalizer (C : Set ↥L) ∧
      (unipJ D (nodeOrbit h 𝒜 h𝒜 i)).map π ≤ ⨆ a : ↥𝒜, C.map a.1.toMonoidHom ∧
      ∀ a : ↥𝒜, nodeHom h 𝒜 h𝒜 a i ≠ i →
        ⁅C, C.map a.1.toMonoidHom⁆ ≤ pCoreOf 2 ((unipJ D (nodeOrbit h 𝒜 h𝒜 i)).map π)) ∨
    QuasisimpleModTwoNonab ↥(twoResidual ((unipJ D (nodeOrbit h 𝒜 h𝒜 i)).map π))

theorem conjClosure_eq_map (h : BorelQuotient D n H π M) (hRN : R ≤ Subgroup.normalizer (L : Set Y))
    (h𝒜 : ∀ α ∈ (actHom hRN).range,
      ((posUnipotent D).map π).map α.toMonoidHom = (posUnipotent D).map π)
    (hPL : P ≤ L) {i : Fin D.rank} (hi : P.subgroupOf L = (parJ D H {i}).map π) :
    conjClosure P R =
      ((parJ D H (nodeOrbit h (actHom hRN).range h𝒜 i)).map π).map L.subtype := by
  have hP : (P.subgroupOf L).map L.subtype = P := Subgroup.map_subgroupOf_eq_of_le hPL
  apply le_antisymm
  · refine conjClosure_le fun r hr z hz => ?_
    have hzL : z ∈ L := hPL hz
    have hz' : (⟨z, hzL⟩ : ↥L) ∈ (parJ D H {i}).map π := hi ▸ Subgroup.mem_subgroupOf.2 hz
    set a : ↥(actHom hRN).range := ⟨actHom hRN ⟨r, hr⟩, ⟨⟨r, hr⟩, rfl⟩⟩
    have himg : actHom hRN ⟨r, hr⟩ ⟨z, hzL⟩ ∈
        (parJ D H {nodeHom h (actHom hRN).range h𝒜 a i}).map π := by
      rw [← map_parJ_singleton_nodeHom h _ h𝒜 a i]
      exact Subgroup.mem_map_of_mem _ hz'
    have hJ : nodeHom h (actHom hRN).range h𝒜 a i ∈ nodeOrbit h (actHom hRN).range h𝒜 i := ⟨a, rfl⟩
    have hle : (parJ D H {nodeHom h (actHom hRN).range h𝒜 a i}).map π ≤
        (parJ D H (nodeOrbit h (actHom hRN).range h𝒜 i)).map π :=
      (le_iSup₂_of_le (f := fun j (_ : j ∈ nodeOrbit h (actHom hRN).range h𝒜 i) =>
        (parJ D H {j}).map π) _ hJ le_rfl).trans (iSup_map_parJ_le _)
    exact ⟨_, hle himg, rfl⟩
  · rw [Subgroup.map_le_iff_le_comap, map_parJ_eq_sup]
    refine sup_le ?_ (iSup₂_le fun j hj => ?_)
    · refine Subgroup.map_le_iff_le_comap.1 ?_
      have hB : (borel D H).map π ≤ P.subgroupOf L := hi ▸ Subgroup.map_mono (borel_le_parJ _)
      exact (Subgroup.map_mono hB).trans (hP.le.trans (le_conjClosure P R))
    · refine Subgroup.map_le_iff_le_comap.1 ?_
      obtain ⟨a, rfl⟩ := hj
      obtain ⟨r, hr⟩ := a.2
      rw [← map_parJ_singleton_nodeHom h _ h𝒜 a i,
        map_map_subtype_eq_conjSub a.1 (fun x => by rw [← hr]; exact coe_actHom hRN r x),
        ← hi, hP]
      exact conjSub_le_conjClosure r.2

theorem concl_of_core (h : BorelQuotient D n H π M) (hRN : R ≤ Subgroup.normalizer (L : Set Y))
    (hR2 : IsPGroup 2 R) (hT : (R ⊓ L).subgroupOf L = (posUnipotent D).map π)
    (hMin : IsMinOverBorel L (R ⊓ L) P) (hnP : ¬ R ≤ Subgroup.normalizer (P : Set Y))
    (hcore : ∀ h𝒜 : (∀ α ∈ (actHom hRN).range,
        ((posUnipotent D).map π).map α.toMonoidHom = (posUnipotent D).map π),
      IsPGroup 2 ↥(actHom hRN).range → ∀ i : Fin D.rank,
      (∃ a : ↥(actHom hRN).range, nodeHom h (actHom hRN).range h𝒜 a i ≠ i) →
        CoreConcl h (actHom hRN).range h𝒜 i) :
    Group.IsSolvable ↥(pElementSubgroup 2 (conjClosure P R)) ∨
      (∃ C : Subgroup Y, C ≤ pElementSubgroup 2 C ∧ C ≤ pElementSubgroup 2 (conjClosure P R) ∧
        pElementSubgroup 2 (conjClosure P R) ≤ Subgroup.normalizer (C : Set Y) ∧
        pElementSubgroup 2 (conjClosure P R) ≤ conjClosure C R ∧
        ∀ r ∈ R, r ∉ Subgroup.normalizer (P : Set Y) →
          ⁅C, B6.conjSub r C⁆ ≤ pCoreOf 2 (pElementSubgroup 2 (conjClosure P R))) ∨
      QuasisimpleModTwoNonab ↥(twoResidual (pElementSubgroup 2 (conjClosure P R))) := by
  have hPL : P ≤ L := hMin.1
  have hι : Function.Injective L.subtype := L.subtype_injective
  have h𝒜 := range_actHom_fix hRN hT
  have h𝒜2 : IsPGroup 2 ↥(actHom hRN).range :=
    hR2.of_surjective (actHom hRN).rangeRestrict (actHom hRN).rangeRestrict_surjective
  obtain ⟨i, hi⟩ := exists_node h hT hMin
  obtain ⟨r₀, hr₀R, hr₀P⟩ := SetLike.not_le_iff_exists.1 hnP
  have hmove : ∃ a : ↥(actHom hRN).range, nodeHom h (actHom hRN).range h𝒜 a i ≠ i :=
    ⟨⟨actHom hRN ⟨r₀, hr₀R⟩, ⟨_, rfl⟩⟩, nodeHom_ne_of_not_mem_normalizer h _ h𝒜 hPL hi _
      (r := r₀) (fun x => coe_actHom hRN ⟨r₀, hr₀R⟩ x) hr₀P⟩
  have hW : pElementSubgroup 2 (conjClosure P R) =
      ((unipJ D (nodeOrbit h (actHom hRN).range h𝒜 i)).map π).map L.subtype := by
    rw [conjClosure_eq_map h hRN h𝒜 hPL hi, ← map_pElementSubgroup_two L.subtype,
      pElement_map_parJ h]
  rw [hW]
  rcases hcore h𝒜 h𝒜2 i hmove with hs | ⟨C, hCp, hCW, hWN, hWC, hcomm⟩ | hq
  · left
    haveI := hs
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.equivMapOfInjective _ L.subtype hι).symm.toMonoidHom)
      (Subgroup.equivMapOfInjective _ L.subtype hι).symm.injective
  · right
    left
    refine ⟨C.map L.subtype, (Subgroup.map_mono hCp).trans (map_pElementSubgroup_two _ C).le,
      Subgroup.map_mono hCW,
      (Subgroup.map_mono hWN).trans (Subgroup.le_normalizer_map L.subtype), ?_, ?_⟩
    · refine (Subgroup.map_mono hWC).trans ?_
      rw [Subgroup.map_iSup]
      refine iSup_le fun a => ?_
      obtain ⟨r, hr⟩ := a.2
      rw [map_map_subtype_eq_conjSub a.1 (fun x => by rw [← hr]; exact coe_actHom hRN r x) C]
      exact conjSub_le_conjClosure r.2
    · intro r hrR hrP
      have hrmove := hcomm ⟨actHom hRN ⟨r, hrR⟩, ⟨_, rfl⟩⟩
        (nodeHom_ne_of_not_mem_normalizer h _ h𝒜 hPL hi _ (r := r)
          (fun x => coe_actHom hRN ⟨r, hrR⟩ x) hrP)
      have h1 := Subgroup.map_mono (f := L.subtype) hrmove
      rw [Subgroup.map_commutator,
        map_map_subtype_eq_conjSub _ (r := r) (fun x => coe_actHom hRN ⟨r, hrR⟩ x),
        ← GOrbReduce.pCoreOf_map_injective hι] at h1
      exact h1
  · right
    right
    rw [← map_twoResidual L.subtype]
    exact GOrbReduce.quasisimpleModTwoNonab_congr (Subgroup.equivMapOfInjective _ L.subtype hι) hq

end Model

end CFSG.AGLEmbeddingD2.Tits.GN516.SimpleBQ
