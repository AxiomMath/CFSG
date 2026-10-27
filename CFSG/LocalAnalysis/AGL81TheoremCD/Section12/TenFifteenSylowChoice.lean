module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TenFifteenKFacts
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.Defs
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TenFifteenBlockNormal
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TenFifteenBlockStep
import CFSG.LocalAnalysis.StandardType.GGRootNormInner
import CFSG.LocalAnalysis.AGLEmbedding.A9MSideOneAux
import CFSG.LocalAnalysis.AGLEmbedding.BlockFactReductionsII
import TauCeti.Algebra.Group.Subgroup.ModularLaw
public import CFSG.Adapters.QiuzhenLegacy.Glauberman.RelIndexSup

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open CFSG.AGLEmbedding CFSG.ABGLocalTools
open CFSG.AGLEmbeddingD2 (NoXBlockFor)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

section Abstract

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
private theorem ker_quotient_inner_normalizerMonoidHom (B : Subgroup X) :
    ((QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner ↥B)).comp
        (Subgroup.normalizerMonoidHom (H := B))).ker =
      (B ⊔ Subgroup.centralizer (B : Set X)).subgroupOf
        (Subgroup.normalizer (B : Set X)) := by
  let N : Subgroup X := Subgroup.normalizer (B : Set X)
  let C : Subgroup X := B ⊔ Subgroup.centralizer (B : Set X)
  have hCN : C ≤ N := sup_le Subgroup.le_normalizer (Subgroup.centralizer_le_normalizer (B : Set X))
  refine le_antisymm ?_ ?_
  · intro x hx
    rw [Subgroup.mem_subgroupOf]
    have hx' : Subgroup.normalizerMonoidHom (H := B) x ∈
        CFSG.ComponentClassification.OuterAutomorphisms.inner ↥B :=
      (QuotientGroup.eq_one_iff _).mp hx
    obtain ⟨k, hk⟩ := hx'
    exact CFSG.StandardType.GGRootNorm.mem_sup_centralizer_of_induced_inner x.2 hk.symm
  · have hB : B.subgroupOf N ≤
        ((QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner ↥B)).comp
          (Subgroup.normalizerMonoidHom (H := B))).ker := by
      intro b hb
      have h1 : Subgroup.normalizerMonoidHom (H := B) b =
          MulAut.conj (⟨(b : X), hb⟩ : B) := by
        ext y
        rfl
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, h1]
      exact (QuotientGroup.eq_one_iff _).mpr (MonoidHom.mem_range.mpr ⟨_, rfl⟩)
    have hZ : (Subgroup.centralizer (B : Set X)).subgroupOf N ≤
        ((QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner ↥B)).comp
          (Subgroup.normalizerMonoidHom (H := B))).ker := by
      intro z hz
      have hz1 : Subgroup.normalizerMonoidHom (H := B) z = 1 := by
        rw [← MonoidHom.mem_ker, Subgroup.normalizerMonoidHom_ker]
        exact hz
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hz1, map_one]
    calc C.subgroupOf N
        = B.subgroupOf N ⊔ (Subgroup.centralizer (B : Set X)).subgroupOf N :=
          Subgroup.subgroupOf_sup Subgroup.le_normalizer
            (Subgroup.centralizer_le_normalizer (B : Set X))
      _ ≤ _ := sup_le hB hZ

omit [Finite X] in
theorem relIndex_sup_centralizer_dvd_card_commutator_outer (B : Subgroup X) :
    (B ⊔ Subgroup.centralizer (B : Set X)).relIndex
        (⁅Subgroup.normalizer (B : Set X), Subgroup.normalizer (B : Set X)⁆ ⊔
          (B ⊔ Subgroup.centralizer (B : Set X))) ∣
      Nat.card (commutator (Outer ↥B)) := by
  let N : Subgroup X := Subgroup.normalizer (B : Set X)
  let C : Subgroup X := B ⊔ Subgroup.centralizer (B : Set X)
  let K : Subgroup X := ⁅N, N⁆ ⊔ C
  let f : N →* Outer ↥B :=
    (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner ↥B)).comp
      (Subgroup.normalizerMonoidHom (H := B))
  change C.relIndex K ∣ Nat.card (commutator (Outer ↥B))
  have hCN : C ≤ N := sup_le Subgroup.le_normalizer (Subgroup.centralizer_le_normalizer (B : Set X))
  have hKN : K ≤ N := sup_le (Subgroup.commutator_le_self N) hCN
  have hker : f.ker = C.subgroupOf N := ker_quotient_inner_normalizerMonoidHom B
  have hcomm : (⁅N, N⁆).subgroupOf N = commutator N := by
    apply Subgroup.map_injective (f := Subgroup.subtype N) (Subgroup.subtype_injective N)
    rw [Subgroup.map_subgroupOf_eq_of_le (Subgroup.commutator_le_self N),
      Subgroup.map_subtype_commutator]
  have hle : (K.subgroupOf N).map f ≤ commutator (Outer ↥B) := by
    have hKm : K.subgroupOf N = (⁅N, N⁆).subgroupOf N ⊔ C.subgroupOf N :=
      Subgroup.subgroupOf_sup (Subgroup.commutator_le_self N) hCN
    rw [hKm, Subgroup.map_sup, ← hker, Subgroup.map_ker_self, sup_bot_eq, hcomm,
      commutator_def, Subgroup.map_commutator]
    exact Subgroup.commutator_mono le_top le_top
  have hidx : C.relIndex K = Nat.card ((K.subgroupOf N).map f) := by
    rw [← Subgroup.relIndex_subgroupOf (H := C) (K := K) (L := N) hKN, ← hker,
      Subgroup.relIndex_ker]
  rw [hidx]
  exact Subgroup.card_dvd_of_le hle

theorem card_commutator_outer_dvd_card_commutator_outer_centerQuotient (L : Type*) [Group L]
    [Group.IsPerfect L] :
    Nat.card (commutator (Outer L)) ∣
      Nat.card (commutator (Outer (L ⧸ Subgroup.center L))) := by
  rw [← Subgroup.card_map_of_injective
    (CFSG.ComponentClassification.OuterAutomorphisms.centerQuotient_outer_injective L)]
  refine Subgroup.card_dvd_of_le ?_
  rw [commutator, commutator, Subgroup.map_commutator]
  exact Subgroup.commutator_mono le_top le_top

private theorem card_normalizer_map_center_dvd {B T : Subgroup X}
    (hT : CFSG.QuasithinUnique.IsSylowTwoOf T B) :
    Nat.card (Subgroup.normalizer
      (((T.subgroupOf B).map (QuotientGroup.mk' (Subgroup.center ↥B))) :
        Set (↥B ⧸ Subgroup.center ↥B))) ∣
      Nat.card (B ⊓ Subgroup.normalizer (T : Set X) : Subgroup X) := by
  set q := QuotientGroup.mk' (Subgroup.center ↥B)
  have hT' : CFSG.QuasithinUnique.IsSylowTwoOf (T.subgroupOf B) ⊤ :=
    isSylowTwoOf_subgroupOf_top_of_isSylowTwoOf hT
  have hmap : Subgroup.normalizer
      (((T.subgroupOf B).map q) : Set (↥B ⧸ Subgroup.center ↥B)) =
      (Subgroup.normalizer ((T.subgroupOf B) : Set ↥B)).map q := by
    refine le_antisymm ?_ (Subgroup.le_normalizer_map q)
    intro y hy
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥B) y
    exact Subgroup.mem_map_of_mem q (mem_normalizer_of_mk_center_mem_normalizer hT' hy)
  have hsub : Subgroup.normalizer ((T.subgroupOf B) : Set ↥B) =
      (B ⊓ Subgroup.normalizer (T : Set X)).subgroupOf B := by
    rw [← Subgroup.subgroupOf_normalizer_eq hT.1, inf_comm,
      Subgroup.inf_subgroupOf_right]
  have hcard : Nat.card (Subgroup.normalizer ((T.subgroupOf B) : Set ↥B)) =
      Nat.card (B ⊓ Subgroup.normalizer (T : Set X) : Subgroup X) := by
    rw [hsub]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [hmap, ← hcard]
  exact Subgroup.card_map_dvd _ q

theorem coprime_relIndex_commutator_sup_of_isParabolicTwo (hOD : KFactLieOutDerived)
    {B : Subgroup X} (hB : IsComponentOf B ⊤)
    (hBY : IsClassicalTwoOrG2 (↥B ⧸ Subgroup.center ↥B)) {P : Subgroup X}
    (hP : IsParabolicTwo B P) {d : ℕ} (hd : d.Prime) (hd5 : 5 ≤ d) (hdP : ¬ d ∣ Nat.card P) :
    Nat.Coprime ((B ⊔ Subgroup.centralizer (B : Set X)).relIndex
        (⁅Subgroup.normalizer (B : Set X), Subgroup.normalizer (B : Set X)⁆ ⊔
          (B ⊔ Subgroup.centralizer (B : Set X)))) (2 * d) := by
  obtain ⟨-, T, hT, hNT⟩ := hP
  set q := QuotientGroup.mk' (Subgroup.center ↥B)
  have hT' : CFSG.QuasithinUnique.IsSylowTwoOf (T.subgroupOf B) ⊤ :=
    isSylowTwoOf_subgroupOf_top_of_isSylowTwoOf hT
  have hTbar : CFSG.QuasithinUnique.IsSylowTwoOf ((T.subgroupOf B).map q) ⊤ :=
    isSylowTwoOf_map_top_of_surjective (f := q) hT' (QuotientGroup.mk'_surjective _)
  have hnot : ¬ d ∣ Nat.card (Subgroup.normalizer
      (((T.subgroupOf B).map q) : Set (↥B ⧸ Subgroup.center ↥B))) := by
    intro hdvd
    exact hdP (hdvd.trans ((card_normalizer_map_center_dvd hT).trans
      (Subgroup.card_dvd_of_le hNT)))
  have hsimple : IsSimpleGroup (↥B ⧸ Subgroup.center ↥B) := hB.2.2.2
  have hperf : Group.IsPerfect ↥B := ⟨hB.2.2.1⟩
  have hOut := hOD (↥B ⧸ Subgroup.center ↥B) hsimple hBY d hd hd5
    ⟨(T.subgroupOf B).map q, hTbar, hnot⟩
  exact Nat.Coprime.of_dvd_left
    ((relIndex_sup_centralizer_dvd_card_commutator_outer B).trans
      (@card_commutator_outer_dvd_card_commutator_outer_centerQuotient ↥B _ hperf)) hOut

omit [Finite X] in
private theorem relIndex_inf_dvd_mul_relIndex {A O A' O' : Subgroup X} (hAO : A ≤ O)
    (hOA : O ≤ Subgroup.normalizer (A : Set X)) (hA'O' : A' ≤ O')
    (hO'A' : O' ≤ Subgroup.normalizer (A' : Set X)) :
    (A ⊓ A').relIndex (O ⊓ O') ∣ A.relIndex O * A'.relIndex O' := by
  have hNA : (A.subgroupOf O).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAO).mpr hOA
  have hNA' : (A'.subgroupOf O').Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hA'O').mpr hO'A'
  let φ : ↥(O ⊓ O') →* (↥O ⧸ (A.subgroupOf O)) × (↥O' ⧸ (A'.subgroupOf O')) :=
    ((QuotientGroup.mk' (A.subgroupOf O)).comp (Subgroup.inclusion inf_le_left)).prod
      ((QuotientGroup.mk' (A'.subgroupOf O')).comp (Subgroup.inclusion inf_le_right))
  have hker : φ.ker = (A ⊓ A').subgroupOf (O ⊓ O') := by
    ext x
    simp [φ, MonoidHom.prod_apply, Prod.mk_eq_one, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.coe_inclusion]
  have hcard : Nat.card φ.range = (A ⊓ A').relIndex (O ⊓ O') := by
    rw [← Subgroup.index_ker φ, hker, Subgroup.relIndex]
  have hdvd : Nat.card φ.range ∣ A.relIndex O * A'.relIndex O' := by
    have h := Subgroup.card_dvd_of_le (H := φ.range) (K := ⊤) le_top
    rw [Subgroup.card_top, Nat.card_prod] at h
    rwa [show Nat.card (↥O ⧸ (A.subgroupOf O)) = A.relIndex O from rfl,
      show Nat.card (↥O' ⧸ (A'.subgroupOf O')) = A'.relIndex O' from rfl] at h
  rwa [hcard] at hdvd

omit [Finite X] in
theorem coprime_relIndex_biInf {ι : Type*} {s : Set ι} (hs : s.Finite) {A O : ι → Subgroup X}
    (hAO : ∀ i ∈ s, A i ≤ O i) (hOA : ∀ i ∈ s, O i ≤ Subgroup.normalizer (A i : Set X)) {n : ℕ}
    (hn : ∀ i ∈ s, Nat.Coprime ((A i).relIndex (O i)) n) :
    Nat.Coprime ((⨅ i ∈ s, A i).relIndex (⨅ i ∈ s, O i)) n := by
  classical
  have key : ∀ u : Finset ι, (∀ i ∈ (u : Set ι), A i ≤ O i) →
      (∀ i ∈ (u : Set ι), O i ≤ Subgroup.normalizer (A i : Set X)) →
      (∀ i ∈ (u : Set ι), Nat.Coprime ((A i).relIndex (O i)) n) →
      Nat.Coprime ((⨅ i ∈ (u : Set ι), A i).relIndex (⨅ i ∈ (u : Set ι), O i)) n := by
    intro u
    induction u using Finset.induction with
    | empty => intro _ _ _; simp
    | insert a u ha ih =>
      intro hAO hOA hn
      rw [Finset.coe_insert] at hAO hOA hn ⊢; rw [iInf_insert, iInf_insert]
      have hAt : ∀ i ∈ (u : Set ι), A i ≤ O i :=
        fun i hi => hAO i (Set.mem_insert_of_mem a hi)
      have hOt : ∀ i ∈ (u : Set ι), O i ≤ Subgroup.normalizer (A i : Set X) :=
        fun i hi => hOA i (Set.mem_insert_of_mem a hi)
      have hnt : ∀ i ∈ (u : Set ι), Nat.Coprime ((A i).relIndex (O i)) n :=
        fun i hi => hn i (Set.mem_insert_of_mem a hi)
      have hA' : (⨅ i ∈ (u : Set ι), A i) ≤ ⨅ i ∈ (u : Set ι), O i := by
        intro x hx
        simp only [Subgroup.mem_iInf] at hx ⊢
        exact fun i hi => hAt i hi (hx i hi)
      have hO' : (⨅ i ∈ (u : Set ι), O i) ≤
          Subgroup.normalizer (((⨅ i ∈ (u : Set ι), A i) : Subgroup X) : Set X) := by
        intro x hx
        rw [Subgroup.mem_normalizer_iff]
        intro y
        simp only [Subgroup.mem_iInf]
        constructor
        · intro hy i hi
          exact (Subgroup.mem_normalizer_iff.mp
            (hOt i hi ((biInf_le (s := (u : Set ι)) O hi) hx)) y).mp (hy i hi)
        · intro hy i hi
          exact (Subgroup.mem_normalizer_iff.mp
            (hOt i hi ((biInf_le (s := (u : Set ι)) O hi) hx)) y).mpr (hy i hi)
      have hdvd := relIndex_inf_dvd_mul_relIndex (A := A a) (O := O a)
        (A' := ⨅ i ∈ (u : Set ι), A i) (O' := ⨅ i ∈ (u : Set ι), O i)
        (hAO a (Set.mem_insert a (u : Set ι)))
        (hOA a (Set.mem_insert a (u : Set ι))) hA' hO'
      exact Nat.Coprime.coprime_dvd_left hdvd
        (Nat.Coprime.mul_left (hn a (Set.mem_insert a (u : Set ι))) (ih hAt hOt hnt))
  have hmain := key hs.toFinset
    (fun i hi => hAO i ((Set.Finite.mem_toFinset hs).mp (by simpa using hi)))
    (fun i hi => hOA i ((Set.Finite.mem_toFinset hs).mp (by simpa using hi)))
    (fun i hi => hn i ((Set.Finite.mem_toFinset hs).mp (by simpa using hi)))
  rwa [Set.Finite.coe_toFinset hs] at hmain

theorem relIndex_sup_dvd_relIndex_of_le_normalizer {A O S : Subgroup X} (hAO : A ≤ O)
    (hSA : S ≤ Subgroup.normalizer (A : Set X)) (hSO : S ≤ Subgroup.normalizer (O : Set X)) :
    (A ⊔ S).relIndex (O ⊔ S) ∣ A.relIndex O := by
  have hXN : A ⊔ S ≤ Subgroup.normalizer (O : Set X) :=
    sup_le (hAO.trans Subgroup.le_normalizer) hSO
  have hmod : (A ⊔ S) ⊓ O = A ⊔ (S ⊓ O) := by
    have h := Subgroup.inf_sup_assoc_of_le (H := S) (K := O) (N := A) hSA hAO
    rw [inf_comm O S, sup_comm S A, sup_comm (S ⊓ O) A, inf_comm O (A ⊔ S)] at h
    exact h.symm
  have hsup : (A ⊔ S) ⊔ O = O ⊔ S := by
    rw [sup_assoc, sup_comm S O, ← sup_assoc, sup_eq_right.mpr hAO]
  have hrel := (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer
    (H := A ⊔ S) (K := O) hXN).1
  rw [hsup] at hrel
  rw [hrel, hmod]
  refine dvd_of_mul_left_eq (A.relIndex (A ⊔ (S ⊓ O))) ?_
  exact Subgroup.relIndex_mul_relIndex (H := A) (K := A ⊔ (S ⊓ O)) (L := O)
    le_sup_left (sup_le hAO inf_le_right)

theorem exists_isSylowOf_le_of_not_dvd_relIndex {K H D : Subgroup X} {d : ℕ} (hd : d.Prime)
    (hKH : K ≤ H) (hidx : ¬ d ∣ K.relIndex H) (hD : IsSylowOf d D ⊤) (hDH : D ≤ H) :
    ∃ D' : Subgroup X, IsSylowOf d D' ⊤ ∧ D' ≤ K := by
  have : Fact d.Prime := ⟨hd⟩
  obtain ⟨D', hD'K⟩ := exists_isSylowOf d K
  have hDH' : IsSylowOf d D H := hD.of_le hDH le_top
  have hD'H : IsSylowOf d D' H := by
    have hle : D' ≤ H := hD'K.le.trans hKH
    have hnd : ¬ d ∣ D'.relIndex H := by
      rw [← Subgroup.relIndex_mul_relIndex (H := D') (K := K) (L := H) hD'K.le hKH]
      intro hdvd
      rcases (Nat.Prime.dvd_mul hd).mp hdvd with h | h
      · exact (isSylowOf_iff.mp hD'K).2.2 h
      · exact hidx h
    exact isSylowOf_iff.mpr ⟨hle, hD'K.isPGroup, hnd⟩
  refine ⟨D', ?_, hD'K.le⟩
  refine isSylowOf_of_card le_top ?_
  rw [hD'H.card_eq, ← hDH'.card_eq]
  exact hD.card_eq

theorem isSylowOf_two_sup_of_odd_relIndex {A O S T : Subgroup X} (hAO : A ≤ O)
    (hSA : S ≤ Subgroup.normalizer (A : Set X)) (hSO : S ≤ Subgroup.normalizer (O : Set X))
    (hodd : Odd (A.relIndex O)) (hT : IsSylowOf 2 T (A ⊔ S)) : IsSylowOf 2 T (O ⊔ S) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAOS : A ⊔ S ≤ O ⊔ S := sup_le_sup_right hAO S
  rw [isSylowOf_iff] at hT ⊢
  refine ⟨hT.1.trans hAOS, hT.2.1, fun h2 => ?_⟩
  have hodd' : Odd ((A ⊔ S).relIndex (O ⊔ S)) :=
    Odd.of_dvd_nat hodd (relIndex_sup_dvd_relIndex_of_le_normalizer hAO hSA hSO)
  rw [← Subgroup.relIndex_mul_relIndex T (A ⊔ S) (O ⊔ S) hT.1 hAOS] at h2
  rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2 with h | h
  · exact hT.2.2 h
  · exact (Nat.not_even_iff_odd.mpr hodd') (even_iff_two_dvd.mpr h)

omit [Finite X] in
private theorem exists_isSylowOf_sup_of_isPGroup_two {A S : Subgroup X}
    (hS : IsPGroup 2 S) :
    ∃ T : Subgroup X, S ≤ T ∧ IsSylowOf 2 T (A ⊔ S) := by
  obtain ⟨Q, hSQ⟩ : ∃ Q : Sylow 2 ↥(A ⊔ S), S.comap (A ⊔ S).subtype ≤ Q :=
    (hS.comap_subtype (K := A ⊔ S)).exists_le_sylow
  refine ⟨(Q : Subgroup ↥(A ⊔ S)).map (A ⊔ S).subtype, ?_, Q, rfl⟩
  intro s hs
  have hms : s ∈ A ⊔ S := Subgroup.mem_sup_right hs
  have hq : (⟨s, hms⟩ : ↥(A ⊔ S)) ∈ (Q : Subgroup ↥(A ⊔ S)) := hSQ hs
  exact ⟨⟨s, hms⟩, hq, rfl⟩

private theorem exists_mem_inv_mul_mem_normalizer_inf_of_isSylowOf_sup
    {A O S T : Subgroup X} (hAO : A ≤ O)
    (hOA : O ≤ Subgroup.normalizer (A : Set X))
    (hSA : S ≤ Subgroup.normalizer (A : Set X))
    (hT : IsSylowOf 2 T (O ⊔ S)) (hTA : T ≤ A ⊔ S) {x : X}
    (hxA : x ∈ Subgroup.normalizer (A : Set X))
    (hxS : ∀ s ∈ S, x * s * x⁻¹ * s⁻¹ ∈ O) :
    ∃ k ∈ O ⊔ S, k⁻¹ * x ∈ Subgroup.normalizer (A : Set X) ⊓
      Subgroup.normalizer (T : Set X) := by
  let φ : X →* X := (MulAut.conj x).toMonoidHom
  let P' : Subgroup X := T.map φ
  have hP'le : P' ≤ O ⊔ S := by
    have hA : A.map φ ≤ O := by
      rintro y ⟨a, ha, rfl⟩
      exact hAO ((Subgroup.mem_normalizer_iff.mp hxA a).mp ha)
    have hS' : S.map φ ≤ O ⊔ S := by
      rintro y ⟨s, hs, rfl⟩
      have h1 := hxS s hs
      have heq : φ s = (x * s * x⁻¹ * s⁻¹) * s := by
        change x * s * x⁻¹ = (x * s * x⁻¹ * s⁻¹) * s
        group
      rw [heq]
      exact Subgroup.mul_mem_sup h1 hs
    calc P' ≤ (A ⊔ S).map φ := Subgroup.map_mono hTA
      _ = A.map φ ⊔ S.map φ := Subgroup.map_sup A S φ
      _ ≤ O ⊔ S := sup_le (hA.trans le_sup_left) hS'
  have hP'syl : IsSylowOf 2 P' (O ⊔ S) := by
    have hcard : Nat.card P' = 2 ^ (Nat.card ↥(O ⊔ S)).factorization 2 := by
      change Nat.card ↥(T.map φ) = 2 ^ (Nat.card ↥(O ⊔ S)).factorization 2
      rw [Subgroup.card_map_of_injective (f := φ) (MulAut.conj x).injective,
        hT.card_eq]
    exact isSylowOf_of_card hP'le hcard
  obtain ⟨k, hkK, hconj⟩ := hT.exists_mem_conj hP'syl
  have hkA : k ∈ Subgroup.normalizer (A : Set X) := sup_le hOA hSA hkK
  have hkxA : k⁻¹ * x ∈ Subgroup.normalizer (A : Set X) :=
    (Subgroup.normalizer (A : Set X)).mul_mem
      ((Subgroup.normalizer (A : Set X)).inv_mem hkA) hxA
  have hkxT : k⁻¹ * x ∈ Subgroup.normalizer (T : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro t
    constructor
    · intro ht
      have hmem : x * t * x⁻¹ ∈ P' := Subgroup.mem_map_of_mem φ ht
      have hconjmem := (hconj (x * t * x⁻¹)).mp hmem
      simpa only [mul_inv_rev, inv_inv, mul_assoc] using hconjmem
    · intro ht
      have ht' : k⁻¹ * (x * t * x⁻¹) * k ∈ T := by
        simpa only [mul_inv_rev, inv_inv, mul_assoc] using ht
      have hmem : x * t * x⁻¹ ∈ P' := (hconj _).mpr ht'
      change φ t ∈ T.map φ at hmem
      exact (Subgroup.mem_map_iff_mem (f := φ) (MulAut.conj x).injective).mp hmem
  exact ⟨k, hkK, Subgroup.mem_inf.mpr ⟨hkxA, hkxT⟩⟩

omit [Finite X] in
private theorem exists_mem_inv_mul_mem_normalizer_sup_of_mem_inf
    {A O S T : Subgroup X} {x k : X}
    (hSA : S ≤ Subgroup.normalizer (A : Set X))
    (hSO : S ≤ Subgroup.normalizer (O : Set X)) (hST : S ≤ T) (hTA : T ≤ A ⊔ S)
    (hk : k ∈ O ⊔ S) (hkx : k⁻¹ * x ∈ Subgroup.normalizer (A : Set X) ⊓
      Subgroup.normalizer (T : Set X)) :
    ∃ o ∈ O, o⁻¹ * x ∈ Subgroup.normalizer ((A ⊔ S : Subgroup X) : Set X) := by
  have hAT : (A ⊔ T : Subgroup X) = A ⊔ S := by
    apply le_antisymm
    · exact sup_le le_sup_left hTA
    · exact sup_le le_sup_left (hST.trans le_sup_right)
  have hk_sup : k⁻¹ * x ∈
      Subgroup.normalizer ((A ⊔ S : Subgroup X) : Set X) := by
    have h1 : k⁻¹ * x ∈
        Subgroup.normalizer ((A ⊔ T : Subgroup X) : Set X) :=
      Subgroup.inf_normalizer_le_normalizer_sup A T hkx
    rwa [hAT] at h1
  have hS_sup : S ≤ Subgroup.normalizer ((A ⊔ S : Subgroup X) : Set X) := by
    intro s hs
    exact Subgroup.inf_normalizer_le_normalizer_sup A S
      ⟨hSA hs, Subgroup.le_normalizer hs⟩
  have hkOS : k ∈ (↑(O ⊔ S) : Set X) := hk
  rw [Subgroup.coe_mul_of_right_le_normalizer_left O S hSO] at hkOS
  obtain ⟨o, ho, s, hs, hos⟩ := Set.mem_mul.mp hkOS
  refine ⟨o, ho, ?_⟩
  have heq : o⁻¹ * x = s * (k⁻¹ * x) := by
    rw [← hos]
    group
  rw [heq]
  exact (Subgroup.normalizer ((A ⊔ S : Subgroup X) : Set X)).mul_mem
    (hS_sup hs) hk_sup

theorem exists_mem_inv_mul_mem_normalizer_sup {A O S : Subgroup X} (hS : IsPGroup 2 S)
    (hAO : A ≤ O) (hOA : O ≤ Subgroup.normalizer (A : Set X))
    (hSA : S ≤ Subgroup.normalizer (A : Set X)) (hSO : S ≤ Subgroup.normalizer (O : Set X))
    (hodd : Odd (A.relIndex O)) {x : X} (hxA : x ∈ Subgroup.normalizer (A : Set X))
    (hxS : ∀ s ∈ S, x * s * x⁻¹ * s⁻¹ ∈ O) :
    ∃ o ∈ O, o⁻¹ * x ∈ Subgroup.normalizer ((A ⊔ S : Subgroup X) : Set X) := by
  obtain ⟨T, hST, hTsyl⟩ := exists_isSylowOf_sup_of_isPGroup_two (A := A) hS
  have hT : IsSylowOf 2 T (O ⊔ S) :=
    isSylowOf_two_sup_of_odd_relIndex hAO hSA hSO hodd hTsyl
  obtain ⟨k, hkK, hkx⟩ :=
    exists_mem_inv_mul_mem_normalizer_inf_of_isSylowOf_sup hAO hOA hSA hT hTsyl.le hxA hxS
  exact exists_mem_inv_mul_mem_normalizer_sup_of_mem_inf hSA hSO hST hTsyl.le hkK hkx

theorem exists_isSylowOf_le_normalizer_sup {A O S D : Subgroup X} {d : ℕ} (hd : d.Prime)
    (hS : IsPGroup 2 S) (hAO : A ≤ O) (hOA : O ≤ Subgroup.normalizer (A : Set X))
    (hSA : S ≤ Subgroup.normalizer (A : Set X)) (hSO : S ≤ Subgroup.normalizer (O : Set X))
    (hDA : D ≤ Subgroup.normalizer (A : Set X)) (hDO : D ≤ Subgroup.normalizer (O : Set X))
    (hcop : Nat.Coprime (A.relIndex O) (2 * d)) (hD : IsSylowOf d D ⊤)
    (hDS : ∀ x ∈ D, ∀ s ∈ S, x * s * x⁻¹ * s⁻¹ ∈ O) :
    ∃ D' : Subgroup X, IsSylowOf d D' ⊤ ∧
      D' ≤ Subgroup.normalizer ((A ⊔ S : Subgroup X) : Set X) := by
  have hnot2 : ¬ 2 ∣ A.relIndex O := by
    intro h2
    have hg : 2 ∣ Nat.gcd (A.relIndex O) (2 * d) := Nat.dvd_gcd h2 (dvd_mul_right 2 d)
    rw [hcop.gcd_eq_one] at hg
    exact absurd hg (by norm_num)
  have hodd : Odd (A.relIndex O) := by
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    exact hnot2
  let K : Subgroup X :=
    Subgroup.normalizer ((A ⊔ S : Subgroup X) : Set X) ⊓ Subgroup.normalizer (O : Set X)
  have hAK : A ≤ K :=
    le_inf (le_sup_left.trans Subgroup.le_normalizer) (hAO.trans Subgroup.le_normalizer)
  have hDK : D ≤ O ⊔ K := by
    intro x hx
    obtain ⟨o, hoO, hoN⟩ := exists_mem_inv_mul_mem_normalizer_sup hS hAO hOA hSA hSO hodd
      (hDA hx) (hDS x hx)
    have hoNO' : o ∈ Subgroup.normalizer (O : Set X) := Subgroup.le_normalizer hoO
    have hoinv : o⁻¹ ∈ Subgroup.normalizer (O : Set X) := Subgroup.inv_mem _ hoNO'
    have hoNO : o⁻¹ * x ∈ Subgroup.normalizer (O : Set X) :=
      Subgroup.mul_mem _ hoinv (hDO hx)
    have hxmul : x ∈ (O ⊔ K : Subgroup X) := by
      change x ∈ ((O ⊔ K : Subgroup X) : Set X)
      rw [Subgroup.coe_mul_of_right_le_normalizer_left O K inf_le_right]
      exact ⟨o, hoO, o⁻¹ * x, ⟨hoN, hoNO⟩, by group⟩
    exact hxmul
  have hOinfK : A ≤ O ⊓ K := le_inf hAO hAK
  have hrel : K.relIndex (O ⊔ K) = (O ⊓ K).relIndex O := by
    simpa [sup_comm, inf_comm] using
      (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer
        (H := K) (K := O) inf_le_right).1
  have hdA : ¬ d ∣ A.relIndex O := by
    intro hdv
    have hg : d ∣ Nat.gcd (A.relIndex O) (2 * d) :=
      Nat.dvd_gcd hdv (by simp [mul_comm])
    rw [hcop.gcd_eq_one] at hg
    exact absurd hg (Nat.Prime.not_dvd_one hd)
  have hdK : ¬ d ∣ K.relIndex (O ⊔ K) := by
    rw [hrel]
    exact fun h => hdA (h.trans (Subgroup.relIndex_dvd_of_le_left O hOinfK))
  obtain ⟨D', hD', hD'K⟩ :=
    exists_isSylowOf_le_of_not_dvd_relIndex hd le_sup_right hdK hD hDK
  exact ⟨D', hD', hD'K.trans inf_le_left⟩

omit [Finite X] in
private theorem normalizer_le_normalizer_centralizer (B : Subgroup X) :
    Subgroup.normalizer (B : Set X) ≤
      Subgroup.normalizer (Subgroup.centralizer (B : Set X) : Set X) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer
    (Subgroup.centralizer_le_normalizer (B : Set X))).mp inferInstance

omit [Finite X] in
private theorem le_normalizer_sup_centralizer {B Y : Subgroup X}
    (hYB : Y ≤ Subgroup.normalizer (B : Set X)) :
    Y ≤ Subgroup.normalizer ((B ⊔ Subgroup.centralizer (B : Set X) : Subgroup X) : Set X) :=
  (le_inf hYB (hYB.trans (normalizer_le_normalizer_centralizer B))).trans
    (Subgroup.inf_normalizer_le_normalizer_sup B (Subgroup.centralizer (B : Set X)))

omit [Finite X] in
private theorem le_normalizer_biInf (𝓑 : Set (Subgroup X)) (f : Subgroup X → Subgroup X)
    {Y : Subgroup X} (h : ∀ B ∈ 𝓑, Y ≤ Subgroup.normalizer (f B : Set X)) :
    Y ≤ Subgroup.normalizer ((⨅ B ∈ 𝓑, f B : Subgroup X) : Set X) := by
  have h' : Y ≤ ⨅ B : 𝓑, Subgroup.normalizer (f B : Set X) := by
    rw [le_iInf_iff]
    intro B
    exact h B B.2
  simpa only [iInf_subtype] using
    h'.trans (Subgroup.iInf_normalizer_le_normalizer_iInf (fun B : 𝓑 => f B))

theorem exists_isSylowOf_le_normalizer_iInf_sup {𝓑 : Set (Subgroup X)} {S D : Subgroup X}
    {d : ℕ} (hd : d.Prime) (hS : IsPGroup 2 S)
    (hSB : ∀ B ∈ 𝓑, S ≤ Subgroup.normalizer (B : Set X))
    (hDB : ∀ B ∈ 𝓑, D ≤ Subgroup.normalizer (B : Set X)) (O : Subgroup X → Subgroup X)
    (hBO : ∀ B ∈ 𝓑, B ⊔ Subgroup.centralizer (B : Set X) ≤ O B)
    (hON : ∀ B ∈ 𝓑, O B ≤ Subgroup.normalizer (B : Set X))
    (hNO : ∀ B ∈ 𝓑, Subgroup.normalizer (B : Set X) ≤ Subgroup.normalizer (O B : Set X))
    (hcop : ∀ B ∈ 𝓑,
      Nat.Coprime ((B ⊔ Subgroup.centralizer (B : Set X)).relIndex (O B)) (2 * d))
    (hD : IsSylowOf d D ⊤) (hDS : ∀ B ∈ 𝓑, ∀ x ∈ D, ∀ s ∈ S, x * s * x⁻¹ * s⁻¹ ∈ O B) :
    ∃ D' : Subgroup X, IsSylowOf d D' ⊤ ∧
      D' ≤ Subgroup.normalizer (((⨅ B ∈ 𝓑, (B ⊔ Subgroup.centralizer (B : Set X))) ⊔ S :
        Subgroup X) : Set X) := by
  let A : Subgroup X := ⨅ B ∈ 𝓑, (B ⊔ Subgroup.centralizer (B : Set X))
  let O' : Subgroup X := ⨅ B ∈ 𝓑, O B
  have hBC : ∀ B ∈ 𝓑, O B ≤ Subgroup.normalizer
      ((B ⊔ Subgroup.centralizer (B : Set X) : Subgroup X) : Set X) :=
    fun B hB => le_normalizer_sup_centralizer (hON B hB)
  have hAO : A ≤ O' := by
    intro x hx
    simp only [A, O', Subgroup.mem_iInf] at hx ⊢
    exact fun B hB => hBO B hB (hx B hB)
  have hSA : S ≤ Subgroup.normalizer (A : Set X) :=
    le_normalizer_biInf 𝓑 (fun B => B ⊔ Subgroup.centralizer (B : Set X))
      fun B hB => le_normalizer_sup_centralizer (hSB B hB)
  have hO'le : ∀ B ∈ 𝓑, O' ≤ O B := by
    intro B hB x hx
    exact (Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hx B)) hB
  have hON' : O' ≤ Subgroup.normalizer (A : Set X) :=
    le_normalizer_biInf 𝓑 (fun B => B ⊔ Subgroup.centralizer (B : Set X))
      (fun B hB => (hO'le B hB).trans (hBC B hB))
  have hSO : S ≤ Subgroup.normalizer (O' : Set X) :=
    le_normalizer_biInf 𝓑 O (fun B hB => (hSB B hB).trans (hNO B hB))
  have hDA : D ≤ Subgroup.normalizer (A : Set X) :=
    le_normalizer_biInf 𝓑 (fun B => B ⊔ Subgroup.centralizer (B : Set X))
      fun B hB => le_normalizer_sup_centralizer (hDB B hB)
  have hDO : D ≤ Subgroup.normalizer (O' : Set X) :=
    le_normalizer_biInf 𝓑 O (fun B hB => (hDB B hB).trans (hNO B hB))
  have hcop' : Nat.Coprime (A.relIndex O') (2 * d) :=
    coprime_relIndex_biInf (s := 𝓑) (A := fun B => B ⊔ Subgroup.centralizer (B : Set X))
      (O := O) (Set.toFinite 𝓑) (fun B hB => hBO B hB) (fun B hB => hBC B hB)
      (fun B hB => hcop B hB)
  have hDS' : ∀ x ∈ D, ∀ s ∈ S, x * s * x⁻¹ * s⁻¹ ∈ O' := by
    intro x hx s hs
    simp only [O', Subgroup.mem_iInf]
    exact fun B hB => hDS B hB x hx s hs
  obtain ⟨D', hD', hle⟩ := exists_isSylowOf_le_normalizer_sup (A := A) (O := O')
    hd hS hAO hON' hSA hSO hDA hDO hcop' hD hDS'
  exact ⟨D', hD', by simpa [A] using hle⟩

end Abstract

variable {G : Type} [Group G] [Finite G]

private theorem sup_centralizer_le_normalizer {X : Type} [Group X] {B : Subgroup X} :
    B ⊔ Subgroup.centralizer (B : Set X) ≤ Subgroup.normalizer (B : Set X) :=
  sup_le Subgroup.le_normalizer (Subgroup.centralizer_le_normalizer (B : Set X))

private theorem normalizer_le_normalizer_sup_centralizer {X : Type} [Group X]
    {B : Subgroup X} :
    Subgroup.normalizer (B : Set X) ≤
      Subgroup.normalizer ((B ⊔ Subgroup.centralizer (B : Set X) : Subgroup X) : Set X) := by
  have hO : B ⊔ Subgroup.centralizer (B : Set X) ≤ Subgroup.normalizer (B : Set X) :=
    sup_centralizer_le_normalizer
  have hsup : ((B ⊔ Subgroup.centralizer (B : Set X)).subgroupOf
      (Subgroup.normalizer (B : Set X))).Normal := by
    rw [Subgroup.subgroupOf_sup Subgroup.le_normalizer
      (Subgroup.centralizer_le_normalizer (B : Set X))]
    infer_instance
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hO).mp hsup

private theorem normalizer_le_normalizer_commutator_sup_centralizer {X : Type} [Group X]
    {B : Subgroup X} :
    Subgroup.normalizer (B : Set X) ≤
      Subgroup.normalizer ((⁅Subgroup.normalizer (B : Set X),
        Subgroup.normalizer (B : Set X)⁆ ⊔
        (B ⊔ Subgroup.centralizer (B : Set X)) : Subgroup X) : Set X) := by
  have h1 : Subgroup.normalizer (B : Set X) ≤
      Subgroup.normalizer ((⁅Subgroup.normalizer (B : Set X),
        Subgroup.normalizer (B : Set X)⁆ : Subgroup X) : Set X) :=
    Subgroup.normalizer_commutator_ge_left _ _
  exact (le_inf h1 normalizer_le_normalizer_sup_centralizer).trans
    (Subgroup.inf_normalizer_le_normalizer_sup _ _)

theorem exists_coprime_overgroup_of_mem_weakBlockSet (hOD : KFactLieOutDerived)
    {M H : Subgroup G} (h : TwoLocalPhaseThree M H) (hK : CFSG.Open.IsKGroup ↥M)
    (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : NoXBlockFor G) {L : Subgroup G}
    (hL : L ∈ weakBlockSet M H) {d : ℕ} (hd : d.Prime) (hd5 : 5 ≤ d)
    (hdH : ¬ d ∣ Nat.card (H ⊓ M : Subgroup G)) :
    ∃ O : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M),
      barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ≤ O ∧
      O ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∧
      Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ≤
        Subgroup.normalizer (O : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∧
      Nat.Coprime ((barM M L ⊔
        Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))).relIndex O) (2 * d) ∧
      ∀ x ∈ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)),
        (∃ k : ℕ, x ^ d ^ k = 1) → ∀ s ∈ barM M (pCoreOf 2 H), x * s * x⁻¹ * s⁻¹ ∈ O := by
  have hSL : pCoreOf 2 H ≤ Subgroup.normalizer (L : Set G) :=
    (h.weakSBlock_asc81bHyp hK h86 hL).1
  have hbarSL : barM M (pCoreOf 2 H) ≤ Subgroup.normalizer (barM M L : Set _) :=
    barM_le_normalizer_barM hSL
  rcases nineThreeTwo_or_isOrthogonalTwo_or_alternating h hK h93 hD2 hL with h32 | hOA
  · let B := barM M L
    let N := Subgroup.normalizer (B : Set (↥M ⧸ CFSG.pCore 2 ↥M))
    let O := ⁅N, N⁆ ⊔ (B ⊔ Subgroup.centralizer (B : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    have hcard : Nat.card (barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L)) ∣
        Nat.card (H ⊓ M : Subgroup G) := by
      have h1 := card_barM_dvd (M := M)
        (X := Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L) (inf_le_right.trans hL.le)
      rw [h.normalizer_twoCore_H] at h1 ⊢
      exact h1.trans (Subgroup.card_dvd_of_le (le_inf inf_le_left (inf_le_right.trans hL.le)))
    refine ⟨O, le_sup_right, ?_, ?_, ?_, ?_⟩
    · exact sup_le (Subgroup.commutator_le_self N) sup_centralizer_le_normalizer
    · exact normalizer_le_normalizer_commutator_sup_centralizer
    · exact coprime_relIndex_commutator_sup_of_isParabolicTwo hOD hL.component h32.1 h32.2.1
        hd hd5 (fun hdiv => hdH (hdiv.trans hcard))
    · intro x hx hxd s hs
      refine Subgroup.mem_sup_left ?_
      have hsN : s ∈ N := hbarSL hs
      simpa only [commutatorElement_def] using
        Subgroup.commutator_mem_commutator (H₁ := N) (H₂ := N) hx hsN
  · let B := barM M L
    let O := B ⊔ Subgroup.centralizer (B : Set (↥M ⧸ CFSG.pCore 2 ↥M))
    have hO : O ≤ Subgroup.normalizer (B : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
      sup_centralizer_le_normalizer
    have hNO : Subgroup.normalizer (B : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ≤
        Subgroup.normalizer (O : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
      normalizer_le_normalizer_sup_centralizer
    have hq : CFSG.IsQuasisimple ↥(barM M L) :=
      ⟨⟨hL.component.2.2.1⟩, hL.component.2.2.2,
        CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _
          hL.component.2.2⟩
    have hout : ¬ d ∣ Nat.card (Outer ↥(barM M L)) :=
      not_dvd_card_outer_of_isOrthogonalTwo_or_alternating hq hOA hd hd5
    refine ⟨O, le_rfl, hO, hNO, ?_, ?_⟩
    · rw [Subgroup.relIndex_self]
      exact Nat.coprime_one_left _
    · intro x hx hxd s hs
      obtain ⟨k, hk⟩ := hxd
      have hxO : x ∈ O := mem_sup_centralizer_of_not_dvd_card_outer hd hout hx hk
      have hconj : s * x⁻¹ * s⁻¹ ∈ O :=
        (Subgroup.mem_normalizer_iff.mp (hNO (hbarSL hs)) x⁻¹).mp (O.inv_mem hxO)
      simpa only [mul_assoc] using O.mul_mem hxO hconj

theorem exists_isSylowOf_le_normalizer_iInf_barM_sup (hOD : KFactLieOutDerived)
    {M H : Subgroup G} (h : TwoLocalPhaseThree M H) (hK : CFSG.Open.IsKGroup ↥M)
    (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : NoXBlockFor G)
    (hm3 : CFSG.Open.pRank 3 M ≤ 3)
    (ht : ∀ L ∈ weakBlockSet M H, ∃ t ∈ barM M L, orderOf t = 3 ∧
      t ∉ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    {d : ℕ} (hd : d.Prime) (hd5 : 5 ≤ d) (hdH : ¬ d ∣ Nat.card (H ⊓ M : Subgroup G)) :
    ∃ D : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsSylowOf d D ⊤ ∧
      D ≤ Subgroup.normalizer (((⨅ B ∈ barM M '' weakBlockSet M H,
        (B ⊔ Subgroup.centralizer (B : Set (↥M ⧸ CFSG.pCore 2 ↥M)))) ⊔ barM M (pCoreOf 2 H) :
          Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  have : Fact d.Prime := ⟨hd⟩
  obtain ⟨D, hD⟩ := exists_isSylowOf d (⊤ : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M))
  have hDB : ∀ L ∈ weakBlockSet M H,
      D ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := fun L hL =>
    le_normalizer_barM_of_isPGroup hL.toIsTwoPrimeComponent hm3 (ht L hL) hd hd5 hD.isPGroup
  have hO : ∀ B ∈ barM M '' weakBlockSet M H, ∃ O : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M),
      B ⊔ Subgroup.centralizer (B : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ≤ O ∧
      O ≤ Subgroup.normalizer (B : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∧
      Subgroup.normalizer (B : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ≤
        Subgroup.normalizer (O : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∧
      Nat.Coprime ((B ⊔ Subgroup.centralizer (B : Set (↥M ⧸ CFSG.pCore 2 ↥M))).relIndex O)
        (2 * d) ∧
      ∀ x ∈ Subgroup.normalizer (B : Set (↥M ⧸ CFSG.pCore 2 ↥M)),
        (∃ k : ℕ, x ^ d ^ k = 1) → ∀ s ∈ barM M (pCoreOf 2 H), x * s * x⁻¹ * s⁻¹ ∈ O := by
    rintro B ⟨L, hL, rfl⟩
    exact exists_coprime_overgroup_of_mem_weakBlockSet hOD h hK h86 h93 hD2 hL hd hd5 hdH
  choose! O hO using hO
  refine exists_isSylowOf_le_normalizer_iInf_sup hd ?_ ?_ ?_ O (fun B hB => (hO B hB).1)
    (fun B hB => (hO B hB).2.1) (fun B hB => (hO B hB).2.2.1) (fun B hB => (hO B hB).2.2.2.1)
    hD ?_
  · exact ((CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H).comap_of_injective
      M.subtype M.subtype_injective).map _
  · rintro B ⟨L, hL, rfl⟩
    exact barM_le_normalizer_barM (h.weakSBlock_asc81bHyp hK h86 hL).1
  · rintro B ⟨L, hL, rfl⟩
    exact hDB L hL
  · rintro B ⟨L, hL, rfl⟩ x hx s hs
    obtain ⟨k, hk⟩ := hD.isPGroup ⟨x, hx⟩
    exact (hO _ ⟨L, hL, rfl⟩).2.2.2.2 x (hDB L hL hx)
      ⟨k, by simpa using congrArg Subtype.val hk⟩ s hs

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end
