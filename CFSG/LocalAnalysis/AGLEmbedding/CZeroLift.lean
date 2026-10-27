module

public import CFSG.LocalAnalysis.AGLEmbedding.CZeroDefs
import CFSG.LocalAnalysis.AGLEmbedding.CZeroBasic

public section

namespace CFSG.AGLEmbedding.CZeroLift

open CFSG.Open Subgroup

theorem pCore_eq_bot_of_isSubnormal {Q : Type} [Group Q] [Finite Q] {T : Subgroup Q}
    (hT : IsSubnormal T ⊤) (hQ : CFSG.pCore 2 Q = ⊥) : CFSG.pCore 2 ↥T = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have key : ∀ {A B : Subgroup Q}, IsSubnormal A B → pCoreOf 2 A ≤ pCoreOf 2 B := by
    intro A B h
    induction h with
    | refl => exact le_rfl
    | @step A' M' K' hHM hn _ ih =>
      refine le_trans ?_ ih
      refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 A').trans hHM) ?_
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 A')
      exact ((normal_subgroupOf_iff_le_normalizer hHM).1 hn).trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 A')
  have htop : pCoreOf 2 (⊤ : Subgroup Q) = ⊥ := by
    have hle : pCoreOf 2 (⊤ : Subgroup Q) ≤ CFSG.pCore 2 Q := by
      refine le_sSup ⟨⟨fun n _ g => ?_⟩, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 ⊤⟩
      have hg : g ∈ Subgroup.normalizer (pCoreOf 2 (⊤ : Subgroup Q) : Set Q) :=
        CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 ⊤
          (by rw [normalizer_eq_top_iff.mpr inferInstance]; exact mem_top g)
      exact (mem_normalizer_iff.mp hg n).mp ‹_›
    rw [hQ] at hle
    exact le_bot_iff.mp hle
  have h1 := key hT
  rw [htop] at h1
  exact (map_eq_bot_iff_of_injective _ T.subtype_injective).mp (le_bot_iff.mp h1)

theorem pCore_eq_ker_of_range {A Q : Type} [Group A] [Finite A] [Group Q] (φ : A →* Q)
    (hker : IsPGroup 2 φ.ker) (hO : CFSG.pCore 2 ↥φ.range = ⊥) : CFSG.pCore 2 A = φ.ker := by
  apply le_antisymm
  · set φ' := φ.rangeRestrict
    have hs : Function.Surjective φ' := φ.rangeRestrict_surjective
    have hmap : (CFSG.pCore 2 A).map φ' ≤ CFSG.pCore 2 ↥φ.range :=
      le_sSup ⟨(CFSG.pCore_normal (p := 2) (G := A)).map φ' hs,
        (CFSG.pCore_isPGroup (p := 2) (G := A)).map φ'⟩
    rw [hO, le_bot_iff, Subgroup.map_eq_bot_iff] at hmap
    rwa [MonoidHom.ker_rangeRestrict] at hmap
  · exact le_sSup ⟨inferInstance, hker⟩

theorem subgroupOf_map_subtype' {Y : Type*} [Group Y] {K : Subgroup Y} (H : Subgroup ↥K) :
    (H.map K.subtype).subgroupOf K = H := by
  rw [← comap_subtype, comap_map_eq_self_of_injective K.subtype_injective]

variable {G : Type} [Group G] [Finite G]

abbrev restr {X I : Subgroup G} {Q : Type} [Group Q] (ψ : ↥X →* Q) (hIX : I ≤ X) : ↥I →* Q :=
  ψ.comp (inclusion hIX)

theorem range_restr {X I : Subgroup G} {Q : Type} [Group Q] (ψ : ↥X →* Q) (hIX : I ≤ X) :
    (restr ψ hIX).range = (I.subgroupOf X).map ψ := by
  rw [MonoidHom.range_comp, inclusion_range]

theorem isPGroup_ker_restr {X I : Subgroup G} {Q : Type} [Group Q] (ψ : ↥X →* Q) (hIX : I ≤ X)
    (hker : IsPGroup 2 ψ.ker) : IsPGroup 2 (restr ψ hIX).ker := by
  have : (restr ψ hIX).ker = ψ.ker.comap (inclusion hIX) := rfl
  rw [this]
  exact hker.comap_of_injective (inclusion hIX) (inclusion_injective hIX)

theorem pCore_eq_and_equiv {X I : Subgroup G} {Q : Type} [Group Q] (ψ : ↥X →* Q) (hIX : I ≤ X)
    (hker : IsPGroup 2 ψ.ker) (hO : CFSG.pCore 2 ↥((I.subgroupOf X).map ψ) = ⊥) :
    CFSG.pCore 2 ↥I = (restr ψ hIX).ker ∧
      Nonempty (↥I ⧸ CFSG.pCore 2 ↥I ≃* ↥((I.subgroupOf X).map ψ)) := by
  have hO' : CFSG.pCore 2 ↥(restr ψ hIX).range = ⊥ := by
    rw [range_restr]
    exact hO
  have hp := pCore_eq_ker_of_range (restr ψ hIX) (isPGroup_ker_restr ψ hIX hker) hO'
  refine ⟨hp, ⟨((QuotientGroup.quotientMulEquivOfEq hp).trans
    (QuotientGroup.quotientKerEquivRange (restr ψ hIX))).trans
      (MulEquiv.subgroupCongr (range_restr ψ hIX))⟩⟩

theorem pCore_eq_ker {X : Subgroup G} {Q : Type} [Group Q] (ψ : ↥X →* Q)
    (hψ : Function.Surjective ψ) (hker : IsPGroup 2 ψ.ker) (hQ : CFSG.pCore 2 Q = ⊥) :
    CFSG.pCore 2 ↥X = ψ.ker := by
  refine pCore_eq_ker_of_range ψ hker ?_
  have e : ↥ψ.range ≃* Q :=
    (MulEquiv.subgroupCongr (MonoidHom.range_eq_top.mpr hψ)).trans Subgroup.topEquiv
  rw [← CFSG.pCore_map_iso 2 e.symm, hQ, Subgroup.map_bot]

theorem pCoreOf_eq {X I : Subgroup G} {Q : Type} [Group Q] (ψ : ↥X →* Q) (hIX : I ≤ X)
    (hI : CFSG.pCore 2 ↥I = (restr ψ hIX).ker) (hX : CFSG.pCore 2 ↥X = ψ.ker)
    (hkI : ψ.ker ≤ I.subgroupOf X) : pCoreOf 2 I = pCoreOf 2 X := by
  unfold pCoreOf
  rw [hI, hX]
  ext g
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨inclusion hIX i, hi, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    have hxI : (x : G) ∈ I := mem_subgroupOf.mp (hkI hx)
    exact ⟨⟨x, hxI⟩, show ψ (inclusion hIX ⟨x, hxI⟩) = 1 from hx, rfl⟩

theorem isSubnormal_map_subtype {X : Subgroup G} {K : Subgroup ↥X} (hK : IsSubnormal K ⊤) :
    IsSubnormal (K.map X.subtype) X := by
  have := hK.map X.subtype
  rwa [← MonoidHom.range_eq_map, range_subtype] at this

theorem exists_cZero_of_symThree {X : Subgroup G} {Q : Type} [Group Q] [Finite Q] (ψ : ↥X →* Q)
    (hψ : Function.Surjective ψ) (hker : IsPGroup 2 ψ.ker) (hQ : CFSG.pCore 2 Q = ⊥)
    {T : Subgroup Q} (hT : IsSubnormal T ⊤) (hb : IsSymThreeOrSUThreeTwo ↥T) :
    ∃ I ∈ cZero X, (I.subgroupOf X).map ψ = T := by
  set I : Subgroup G := (T.comap ψ).map X.subtype with hIdef
  have hIX : I ≤ X := map_subtype_le _
  have hsub : I.subgroupOf X = T.comap ψ := by rw [hIdef, subgroupOf_map_subtype']
  have himg : (I.subgroupOf X).map ψ = T := by rw [hsub, map_comap_eq_self_of_surjective hψ]
  have hTO := pCore_eq_bot_of_isSubnormal hT hQ
  obtain ⟨hpI, ⟨e⟩⟩ := pCore_eq_and_equiv ψ hIX hker (by rw [himg]; exact hTO)
  have hpX := pCore_eq_ker ψ hψ hker hQ
  refine ⟨I, ⟨hIX, ?_, Or.inr ⟨pCoreOf_eq ψ hIX hpI hpX ?_, ?_⟩⟩, himg⟩
  · exact isSubnormal_map_subtype (by simpa using hT.comap ψ)
  · rw [hsub]
    intro x hx
    rw [mem_comap, (MonoidHom.mem_ker).mp hx]
    exact one_mem T
  · rw [himg] at e
    exact IsSymThreeOrSUThreeTwo.of_mulEquiv e.symm hb

theorem commutator_self_eq_of_commutator {Y : Type} [Group Y] {K : Subgroup Y}
    (h : commutator ↥K = ⊤) : ⁅K, K⁆ = K := by
  have := congrArg (Subgroup.map K.subtype) h
  rwa [commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_subtype] at this

theorem exists_cZero_of_component {X : Subgroup G} {Q : Type} [Group Q] [Finite Q] (ψ : ↥X →* Q)
    (hψ : Function.Surjective ψ) (hker : IsPGroup 2 ψ.ker) (hQ : CFSG.pCore 2 Q = ⊥)
    {C : Subgroup Q} (hC : IsComponentOf C ⊤) :
    ∃ I ∈ cZero X, (I.subgroupOf X).map ψ = C := by
  classical
  obtain ⟨-, hCs, hCq⟩ := hC
  have hCC : ⁅C, C⁆ = C := commutator_self_eq_of_commutator hCq.1
  let P : ℕ → Prop := fun n => ∃ K : Subgroup ↥X, IsSubnormal K ⊤ ∧ K.map ψ = C ∧ Nat.card K = n
  have hex : ∃ n, P n :=
    ⟨_, C.comap ψ, by simpa using hCs.comap ψ, map_comap_eq_self_of_surjective hψ C, rfl⟩
  obtain ⟨K, hKs, hKC, hKn⟩ := Nat.find_spec hex
  have hmin : ∀ K' : Subgroup ↥X, IsSubnormal K' ⊤ → K'.map ψ = C → K' ≤ K → K' = K := by
    intro K' hK's hK'C hle
    have hcard : Nat.card K ≤ Nat.card K' := by
      rw [hKn]
      exact Nat.find_min' hex ⟨K', hK's, hK'C, rfl⟩
    exact eq_of_le_of_card_ge hle hcard
  have hcK : ⁅K, K⁆ = (commutator ↥K).map K.subtype := by
    rw [commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_subtype]
  have hKle : ⁅K, K⁆ ≤ K := by rw [hcK]; exact map_subtype_le _
  have hKperf : ⁅K, K⁆ = K := by
    refine hmin _ ?_ ?_ hKle
    · refine IsSubnormal.trans ?_ hKs
      refine IsSubnormal.step hKle ?_ (IsSubnormal.refl K)
      rw [hcK, subgroupOf_map_subtype']
      infer_instance
    · rw [map_commutator, hKC, hCC]
  set I : Subgroup G := K.map X.subtype with hIdef
  have hIX : I ≤ X := map_subtype_le _
  have hsub : I.subgroupOf X = K := by rw [hIdef, subgroupOf_map_subtype']
  have himg : (I.subgroupOf X).map ψ = C := by rw [hsub, hKC]
  have hCO := pCore_eq_bot_of_isSubnormal hCs hQ
  obtain ⟨-, ⟨e⟩⟩ := pCore_eq_and_equiv ψ hIX hker (by rw [himg]; exact hCO)
  rw [himg] at e
  have hIperf : ⁅I, I⁆ = I := by rw [hIdef, ← map_commutator, hKperf]
  refine ⟨I, ⟨hIX, isSubnormal_map_subtype hKs, Or.inl ⟨le_rfl, IsSubnormal.refl I, hIperf,
    ?_⟩⟩, himg⟩
  have htop : barM I I = ⊤ := by
    rw [barM, subgroupOf_self, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top]
    exact QuotientGroup.mk'_surjective _
  rw [htop]
  refine ⟨le_rfl, IsSubnormal.refl ⊤, ?_⟩
  exact CFSG.Open.IsQuasisimple.of_mulEquiv (Subgroup.topEquiv.trans e) hCq

end CFSG.AGLEmbedding.CZeroLift
