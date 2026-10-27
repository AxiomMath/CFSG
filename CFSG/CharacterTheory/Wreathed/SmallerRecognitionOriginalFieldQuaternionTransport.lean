module
public import CFSG.CharacterTheory.Wreathed.SmallerRecognitionOriginalFieldQuaternionConjugation
public noncomputable section
namespace CFSG.Wreathed.SmallerRecognitionOriginalField
open scoped Classical Pointwise
universe u
variable {G : Type u} [Group G]

theorem actual_conjugation_centralizer_eq (x g : G)
    (hg : g ∈ Subgroup.centralizer ({x} : Set G)) :
    (Subgroup.centralizer ({x} : Set G)).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer ({x} : Set G) := by
  ext a
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact (Subgroup.centralizer ({x} : Set G)).mul_mem
      ((Subgroup.centralizer ({x} : Set G)).mul_mem hg hb)
      ((Subgroup.centralizer ({x} : Set G)).inv_mem hg)
  · intro ha
    refine Subgroup.mem_map.mpr ⟨g⁻¹ * a * g, ?_, ?_⟩
    · exact (Subgroup.centralizer ({x} : Set G)).mul_mem
        ((Subgroup.centralizer ({x} : Set G)).mul_mem
          ((Subgroup.centralizer ({x} : Set G)).inv_mem hg) ha) hg
    · simp [MulAut.conj_apply, mul_assoc]

theorem original_conjugation_factorization_iff
    (K : Subgroup G) (x g : G)
    (hg : g ∈ Subgroup.centralizer ({x} : Set G)) :
    let Kg := K.map (MulAut.conj g).toMonoidHom
    CFSG.oddCore Kg ⊔ (Subgroup.centralizer ({x} : Set G)).subgroupOf Kg = ⊤ ↔
      CFSG.oddCore K ⊔ (Subgroup.centralizer ({x} : Set G)).subgroupOf K = ⊤ := by
  let E := K.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  have hcore := CFSG.ComponentClassification.OddCore.equiv_invariant E
  change (CFSG.oddCore K).map E.toMonoidHom =
    CFSG.oddCore (K.map (MulAut.conj g).toMonoidHom) at hcore
  have hN : ((Subgroup.centralizer ({x} : Set G)).subgroupOf K).map E.toMonoidHom =
      (Subgroup.centralizer ({x} : Set G)).subgroupOf
        (K.map (MulAut.conj g).toMonoidHom) := by
    ext a
    constructor
    · rintro ⟨b, hb, rfl⟩
      change (g * (b : G) * g⁻¹) ∈ Subgroup.centralizer ({x} : Set G)
      exact (actual_conjugation_centralizer_eq x g hg) ▸
        Subgroup.mem_map.mpr ⟨(b : G), hb, rfl⟩
    · intro ha
      obtain ⟨b, rfl⟩ := E.surjective a
      refine Subgroup.mem_map.mpr ⟨b, ?_, rfl⟩
      change (b : G) ∈ Subgroup.centralizer ({x} : Set G)
      have hback : g⁻¹ * (g * (b : G) * g⁻¹) * g ∈
          Subgroup.centralizer ({x} : Set G) :=
        (Subgroup.centralizer ({x} : Set G)).mul_mem
          ((Subgroup.centralizer ({x} : Set G)).mul_mem
            ((Subgroup.centralizer ({x} : Set G)).inv_mem hg) ha) hg
      simpa [mul_assoc] using hback
  have hsup : (CFSG.oddCore K ⊔
      (Subgroup.centralizer ({x} : Set G)).subgroupOf K).map E.toMonoidHom =
      CFSG.oddCore (K.map (MulAut.conj g).toMonoidHom) ⊔
        (Subgroup.centralizer ({x} : Set G)).subgroupOf
          (K.map (MulAut.conj g).toMonoidHom) := by
    rw [Subgroup.map_sup, hcore, hN]
  constructor
  · intro h
    apply Subgroup.map_injective (f := E.toMonoidHom) E.injective
    rw [hsup, h, Subgroup.map_top_of_surjective _ E.surjective]
  · intro h
    rw [← hsup, h, Subgroup.map_top_of_surjective _ E.surjective]

@[expose] def actualConjugationOddCoreQuotientEquiv
    (K : Subgroup G) (g : G) :
    K ⧸ CFSG.oddCore K ≃*
      (K.map (MulAut.conj g).toMonoidHom) ⧸
        CFSG.oddCore (K.map (MulAut.conj g).toMonoidHom) :=
  QuotientGroup.congr (CFSG.oddCore K)
    (CFSG.oddCore (K.map (MulAut.conj g).toMonoidHom))
    (K.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective)
    (CFSG.ComponentClassification.OddCore.equiv_invariant _)

theorem actualConjugationOddCoreQuotientEquiv_mk
    (K : Subgroup G) (g : G) (k : K) :
    actualConjugationOddCoreQuotientEquiv K g (QuotientGroup.mk' (CFSG.oddCore K) k) =
      QuotientGroup.mk' (CFSG.oddCore (K.map (MulAut.conj g).toMonoidHom))
        ((K.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective) k) := by
  exact QuotientGroup.congr_mk' _ _ _ _ k

theorem original_conjugation_quotient_centrality_iff
    (K : Subgroup G) (x g : G) (hxK : x ∈ K)
    (hfix : g * x * g⁻¹ = x) :
    let Kg := K.map (MulAut.conj g).toMonoidHom
    let hxg : x ∈ Kg := Subgroup.mem_map.mpr ⟨x, hxK, by
      change g * x * g⁻¹ = x
      exact hfix⟩
    QuotientGroup.mk' (CFSG.oddCore Kg) (⟨x, hxg⟩ : Kg) ∈
      Subgroup.center (Kg ⧸ CFSG.oddCore Kg) ↔
    QuotientGroup.mk' (CFSG.oddCore K) (⟨x, hxK⟩ : K) ∈
      Subgroup.center (K ⧸ CFSG.oddCore K) := by
  dsimp only
  let E := K.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  let D := actualConjugationOddCoreQuotientEquiv K g
  have hcenter := Subgroup.map_center_eq D
  have hx : (E ⟨x, hxK⟩ : K.map (MulAut.conj g).toMonoidHom) =
      ⟨x, Subgroup.mem_map.mpr ⟨x, hxK, hfix⟩⟩ := by
    apply Subtype.ext
    exact hfix
  have hqx := actualConjugationOddCoreQuotientEquiv_mk K g ⟨x, hxK⟩
  change D (QuotientGroup.mk' (CFSG.oddCore K) ⟨x, hxK⟩) =
    QuotientGroup.mk' (CFSG.oddCore (K.map (MulAut.conj g).toMonoidHom)) (E ⟨x, hxK⟩) at hqx
  rw [hx] at hqx
  rw [← hqx, ← hcenter]
  constructor
  · rintro ⟨v, hv, heq⟩
    have hvEq := D.injective heq
    exact hvEq ▸ hv
  · intro hxcenter
    exact Subgroup.mem_map.mpr ⟨_, hxcenter, rfl⟩

theorem actualConjugationOddCoreQuotientEquiv_symm_mk
    (K : Subgroup G) (g : G) (k : K.map (MulAut.conj g).toMonoidHom) :
    (actualConjugationOddCoreQuotientEquiv K g).symm
      (QuotientGroup.mk' (CFSG.oddCore (K.map (MulAut.conj g).toMonoidHom)) k) =
      QuotientGroup.mk' (CFSG.oddCore K)
        ((K.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).symm k) := by
  let E := K.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  let D := actualConjugationOddCoreQuotientEquiv K g
  have h := actualConjugationOddCoreQuotientEquiv_mk K g (E.symm k)
  change D (QuotientGroup.mk' (CFSG.oddCore K) (E.symm k)) =
    QuotientGroup.mk' (CFSG.oddCore (K.map (MulAut.conj g).toMonoidHom)) (E (E.symm k)) at h
  rw [E.apply_symm_apply] at h
  have hback := congrArg D.symm h
  simpa only [MulEquiv.symm_apply_apply] using hback.symm

theorem original_conjugation_ambient_factorization_iff
    {G : Type} [Group G] (K : Subgroup G) (x g : G)
    (hg : g ∈ Subgroup.centralizer ({x} : Set G)) :
    let N := Subgroup.centralizer ({x} : Set G)
    let Kg := K.map (MulAut.conj g).toMonoidHom
    (Kg : Set G) = ((CFSG.oddCore Kg).map Kg.subtype : Set G) * (Kg ⊓ N : Set G) ↔
      (K : Set G) = ((CFSG.oddCore K).map K.subtype : Set G) * (K ⊓ N : Set G) := by
  dsimp only
  exact FullSylowCoveringObstruction.internal_odd_core_factorization_iff_ambient_product.symm.trans
    ((original_conjugation_factorization_iff K x g hg).trans
      FullSylowCoveringObstruction.internal_odd_core_factorization_iff_ambient_product)

theorem actual_conjugation_odd_core_centralizer_intersection
    (K : Subgroup G) (x g : G)
    (hg : g ∈ Subgroup.centralizer ({x} : Set G)) :
    let Kg := K.map (MulAut.conj g).toMonoidHom
    (((CFSG.oddCore K).map K.subtype) ⊓ Subgroup.centralizer ({x} : Set G)).map
      (MulAut.conj g).toMonoidHom =
      (CFSG.oddCore Kg).map Kg.subtype ⊓ Subgroup.centralizer ({x} : Set G) := by
  rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
    ← ambient_conjugation_odd_core_image, actual_conjugation_centralizer_eq x g hg]

theorem actual_centralizer_odd_core_conjugation_eq (x g : G)
    (hg : g ∈ Subgroup.centralizer ({x} : Set G)) :
    ((CFSG.oddCore (Subgroup.centralizer ({x} : Set G))).map
      (Subgroup.centralizer ({x} : Set G)).subtype).map (MulAut.conj g).toMonoidHom =
      (CFSG.oddCore (Subgroup.centralizer ({x} : Set G))).map
        (Subgroup.centralizer ({x} : Set G)).subtype := by
  let N := Subgroup.centralizer ({x} : Set G)
  let gN : N := ⟨g, hg⟩
  have hnormal := Subgroup.Normal.map_conj_eq (CFSG.oddCore N) gN
  have h := congrArg (fun A : Subgroup N => A.map N.subtype) hnormal
  rw [Subgroup.map_map] at h
  rw [Subgroup.map_map]
  exact h

theorem original_conjugation_odd_core_intersection_iff
    (K : Subgroup G) (x g : G)
    (hg : g ∈ Subgroup.centralizer ({x} : Set G)) :
    let N := Subgroup.centralizer ({x} : Set G)
    let Kg := K.map (MulAut.conj g).toMonoidHom
    (CFSG.oddCore Kg).map Kg.subtype ⊓ N = (CFSG.oddCore N).map N.subtype ⊓ Kg ↔
      (CFSG.oddCore K).map K.subtype ⊓ N = (CFSG.oddCore N).map N.subtype ⊓ K := by
  dsimp only
  have hleft := actual_conjugation_odd_core_centralizer_intersection K x g hg
  have hright : ((CFSG.oddCore (Subgroup.centralizer ({x} : Set G))).map
      (Subgroup.centralizer ({x} : Set G)).subtype ⊓ K).map (MulAut.conj g).toMonoidHom =
      (CFSG.oddCore (Subgroup.centralizer ({x} : Set G))).map
        (Subgroup.centralizer ({x} : Set G)).subtype ⊓
          K.map (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
      actual_centralizer_odd_core_conjugation_eq x g hg]
  constructor
  · intro heq
    apply Subgroup.map_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
    rw [hleft, hright, heq]
  · intro heq
    rw [← hleft, ← hright, heq]

theorem original_conjugation_factorization_center_intersection_iff
    {G : Type} [Group G]
    (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup G) (hxK : wreathModelHom S e (Original.x (2 ^ n)) ∈ K)
    (g : G) (hfix : g * wreathModelHom S e (Original.x (2 ^ n)) * g⁻¹ =
      wreathModelHom S e (Original.x (2 ^ n))) :
    let x := wreathModelHom S e (Original.x (2 ^ n))
    let N := involutionCentralizer n S e
    let Kg := K.map (MulAut.conj g).toMonoidHom
    let hxg : x ∈ Kg := Subgroup.mem_map.mpr ⟨x, hxK, by
      change g * x * g⁻¹ = x
      exact hfix⟩
    ((Kg : Set G) = ((CFSG.oddCore Kg).map Kg.subtype : Set G) * (Kg ⊓ N : Set G) ∧
      QuotientGroup.mk' (CFSG.oddCore Kg) (⟨x, hxg⟩ : Kg) ∈
        Subgroup.center (Kg ⧸ CFSG.oddCore Kg) ∧
      (CFSG.oddCore Kg).map Kg.subtype ⊓ N = (centralizerOddCore n S e).map N.subtype ⊓ Kg) ↔
    ((K : Set G) = ((CFSG.oddCore K).map K.subtype : Set G) * (K ⊓ N : Set G) ∧
      QuotientGroup.mk' (CFSG.oddCore K) (⟨x, hxK⟩ : K) ∈
        Subgroup.center (K ⧸ CFSG.oddCore K) ∧
      (CFSG.oddCore K).map K.subtype ⊓ N = (centralizerOddCore n S e).map N.subtype ⊓ K) := by
  let x := wreathModelHom S e (Original.x (2 ^ n))
  have hg : g ∈ Subgroup.centralizer ({x} : Set G) :=
    original_involution_fixing_conjugator_mem_centralizer n S e g hfix
  exact and_congr (original_conjugation_ambient_factorization_iff K x g hg)
    (and_congr (original_conjugation_quotient_centrality_iff K x g hxK hfix)
      (original_conjugation_odd_core_intersection_iff K x g hg))

end CFSG.Wreathed.SmallerRecognitionOriginalField
