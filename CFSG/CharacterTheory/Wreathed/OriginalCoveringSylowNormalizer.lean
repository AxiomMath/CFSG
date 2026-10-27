module

public import CFSG.CharacterTheory.Wreathed.OriginalSylowNormalizerWitness
public import CFSG.CharacterTheory.Wreathed.FullCenterOddCore
public import CFSG.CharacterTheory.Wreathed.BaseFourCentralizerStructure

public noncomputable section
namespace CFSG.Wreathed.OriginalCoveringSylowNormalizer
open scoped Classical Pointwise
open CFSG.Wreathed.OriginalSylowNormalizerWitness CFSG.SignalizerFunctor.Helpers
open CFSG.Wreathed.BaseFourCentralizerStructure
  (modelT modelT_isKleinFour modelT_eq_actual_generated modelT_nonidentity_order)
universe u
variable {G : Type u} [Group G] [Finite G]

theorem original_Sylow_odd {ell : ℕ} (N : Subgroup G)
    (P : Sylow ell (CFSG.oddCore N)) : Odd (Nat.card (ambientSylow N P)) := by
  have hPR : ambientSylow N P ≤ ambientOddCore N :=
    Subgroup.map_mono (Subgroup.map_subtype_le _)
  exact (ambientOddCore_odd N).of_dvd_nat (Subgroup.card_dvd_of_le hPR)

theorem original_Sylow_nontrivial {ell : ℕ} (hell : ell.Prime)
    (N : Subgroup G) (hdiv : ell ∣ Nat.card (CFSG.oddCore N))
    (P : Sylow ell (CFSG.oddCore N)) : ambientSylow N P ≠ ⊥ := by
  let : Fact ell.Prime := ⟨hell⟩
  intro h
  have hc := (Subgroup.eq_bot_iff_card (ambientSylow N P)).mp h
  rw [ambientSylow, Subgroup.card_subtype, Subgroup.card_subtype] at hc
  exact P.ne_bot_of_dvd_card hdiv ((Subgroup.eq_bot_iff_card _).mpr hc)

theorem original_invariant_prime_Sylow_exists (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    {ell : ℕ} (hell : ell.Prime) :
    ∃ P : Sylow ell (centralizerOddCore n S e),
      (S : Subgroup G) ≤ Subgroup.normalizer
        (ambientSylow (involutionCentralizer n S e) P : Set G) := by
  let N := involutionCentralizer n S e
  let SI := centralizerSylow n hn S e
  obtain ⟨P, hP⟩ := normalized_subgroup_invariant_sylow 2 ell Nat.prime_two hell
    (SI : Subgroup N) (CFSG.oddCore N) SI.isPGroup'
    Subgroup.le_normalizer_of_normal
    (CFSG.ComponentClassification.OddCore.odd_card N).coprime_two_left
  refine ⟨P, ?_⟩
  have hSmap : (SI : Subgroup N).map N.subtype = (S : Subgroup G) := by
    dsimp only [SI]
    rw [centralizerSylow_coe, Subgroup.map_subgroupOf_eq_of_le
      (sylow_le_involutionCentralizer n hn S e)]
  rw [← hSmap]
  exact (Subgroup.map_mono hP).trans (Subgroup.le_normalizer_map N.subtype)

theorem original_prime_normalizer_proper [IsSimpleGroup G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    {ell : ℕ} (hell : ell.Prime) (hdiv : ell ∣ Nat.card (centralizerOddCore n S e))
    (P : Sylow ell (centralizerOddCore n S e)) :
    Subgroup.normalizer (ambientSylow (involutionCentralizer n S e) P : Set G) < ⊤ := by
  apply lt_top_iff_ne_top.mpr
  intro hK
  let A := ambientSylow (involutionCentralizer n S e) P
  let _ : A.Normal := Subgroup.normalizer_eq_top_iff.mp hK
  have hA := original_Sylow_nontrivial hell (involutionCentralizer n S e) hdiv P
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal A with h | h
  · exact hA h
  · have hodd := original_Sylow_odd (involutionCentralizer n S e) P
    rw [show ambientSylow (involutionCentralizer n S e) P = ⊤ from h,
      Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).toEquiv] at hodd
    have hcard : Nat.card S = 2 * (2 ^ n) ^ 2 := by
      rw [Nat.card_congr e.toEquiv]
      exact (wreath_center_involution_and_quaternion_coordinates n hn).card
    apply hodd.not_two_dvd_nat
    exact dvd_trans (hcard ▸ dvd_mul_right 2 ((2 ^ n) ^ 2))
      (Subgroup.card_subgroup_dvd_card _)

theorem original_normalizer_oddCore_nontrivial
    {ell : ℕ} (hell : ell.Prime) (N : Subgroup G)
    (hdiv : ell ∣ Nat.card (CFSG.oddCore N)) (P : Sylow ell (CFSG.oddCore N)) :
    ambientOddCore (Subgroup.normalizer (ambientSylow N P : Set G)) ≠ ⊥ := by
  intro h
  exact original_Sylow_nontrivial hell N hdiv P
    (eq_bot_iff.mpr ((original_sylow_le_normalizer_oddCore N P).trans_eq h))

theorem original_normalizer_quotient_image {ell : ℕ} (hell : ell.Prime)
    (N : Subgroup G) (P : Sylow ell (CFSG.oddCore N)) :
    ((Subgroup.normalizer (ambientSylow N P : Set G)).comap N.subtype).map
      (QuotientGroup.mk' (CFSG.oddCore N)) = ⊤ := by
  let : Fact ell.Prime := ⟨hell⟩
  let P0 : Subgroup N := (P : Subgroup (CFSG.oddCore N)).map (CFSG.oddCore N).subtype
  let pi := QuotientGroup.mk' (CFSG.oddCore N)
  have hnormalizer : (Subgroup.normalizer (ambientSylow N P : Set G)).comap N.subtype =
      Subgroup.normalizer (P0 : Set N) := by
    change (Subgroup.normalizer (P0.map N.subtype : Set G)).comap N.subtype = _
    rw [Subgroup.comap_normalizer_eq_of_le_range
      ((Subgroup.map_subtype_le P0).trans_eq N.range_subtype.symm),
      Subgroup.comap_map_eq_self_of_injective N.subtype_injective]
  have hker : (CFSG.oddCore N).map pi = ⊥ := by
    apply (Subgroup.map_eq_bot_iff _).mpr
    rw [QuotientGroup.ker_mk']
  have hfrat := congrArg (Subgroup.map pi) (Sylow.normalizer_sup_eq_top P)
  rw [Subgroup.map_sup, hker, sup_bot_eq,
    Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at hfrat
  rw [hnormalizer]
  exact hfrat

theorem original_normalizer_intersection_quotient_image
    {ell : ℕ} (hell : ell.Prime) (N : Subgroup G) (P : Sylow ell (CFSG.oddCore N)) :
    ((Subgroup.normalizer (ambientSylow N P : Set G) ⊓ N).subgroupOf N).map
      (QuotientGroup.mk' (CFSG.oddCore N)) = ⊤ := by
  have hKN : (Subgroup.normalizer (ambientSylow N P : Set G) ⊓ N).subgroupOf N =
      (Subgroup.normalizer (ambientSylow N P : Set G)).comap N.subtype := by
    ext g
    change (g.val ∈ Subgroup.normalizer (ambientSylow N P : Set G) ∧ g.val ∈ N) ↔ _
    simp only [g.property, and_true, Subgroup.mem_comap, Subgroup.coe_subtype]
  rw [hKN]
  exact original_normalizer_quotient_image hell N P

theorem original_full_invariant_normalizer_core_Sylow
    {ell : ℕ} (hell : ell.Prime) (N : Subgroup G) (P : Sylow ell (CFSG.oddCore N))
    (S : Sylow 2 G)
    (hSP : (S : Subgroup G) ≤ Subgroup.normalizer (ambientSylow N P : Set G)) :
    ∃ Q : Sylow ell (ambientOddCore (Subgroup.normalizer (ambientSylow N P : Set G))),
      ambientSylow N P ≤ (Q : Subgroup _).map
        (ambientOddCore (Subgroup.normalizer (ambientSylow N P : Set G))).subtype ∧
      (S : Subgroup G) ≤ Subgroup.normalizer (((Q : Subgroup _).map
        (ambientOddCore (Subgroup.normalizer (ambientSylow N P : Set G))).subtype) : Set G) := by
  let K := Subgroup.normalizer (ambientSylow N P : Set G)
  let O := ambientOddCore K
  obtain ⟨Q, hQ⟩ := normalized_subgroup_invariant_sylow 2 ell Nat.prime_two hell
    (S : Subgroup G) O S.isPGroup' (hSP.trans (ambientOddCore_normalized K))
    (ambientOddCore_odd K).coprime_two_left
  exact ⟨Q, original_sylow_le_every_normalizer_core_sylow N P Q, hQ⟩

theorem original_covering_normalizer_structure [IsSimpleGroup G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    {ell : ℕ} (hell : ell.Prime) (hdiv : ell ∣ Nat.card (centralizerOddCore n S e))
    (P : Sylow ell (centralizerOddCore n S e))
    (hSP : (S : Subgroup G) ≤ Subgroup.normalizer
      (ambientSylow (involutionCentralizer n S e) P : Set G)) :
    let N := involutionCentralizer n S e
    let A := ambientSylow N P
    let K := Subgroup.normalizer (A : Set G)
    let O := ambientOddCore K
    K < ⊤ ∧ (S : Subgroup G) ≤ K ∧ A ≤ O ∧
      (K.comap N.subtype).map (centralizerOddCoreMap n S e) = ⊤ ∧
      O ⊓ N ≤ ambientOddCore N ∧ O ≠ ⊥ ∧
      (∃ B : Sylow ell ↥(O ⊓ N), (B : Subgroup _).map (O ⊓ N).subtype = A) ∧
      (∃ Q : Sylow ell O, A ≤ (Q : Subgroup O).map O.subtype ∧
        (S : Subgroup G) ≤ Subgroup.normalizer
          (((Q : Subgroup O).map O.subtype) : Set G)) ∧
      (∀ Q : Sylow ell O, A ≤ (Q : Subgroup O).map O.subtype ∧
        ((Q : Subgroup O).map O.subtype) ⊓ N = A) := by
  dsimp only
  refine ⟨original_prime_normalizer_proper n hn S e hell hdiv P, hSP,
    original_sylow_le_normalizer_oddCore _ P,
    original_normalizer_quotient_image hell _ P,
    original_normalizer_oddCore_intersection hell _ P,
    original_normalizer_oddCore_nontrivial hell _ hdiv P,
    original_sylow_in_normalizer_core_intersection hell _ P,
    original_full_invariant_normalizer_core_Sylow hell _ P S hSP, ?_⟩
  intro Q
  exact ⟨original_sylow_le_every_normalizer_core_sylow _ P Q,
    original_core_sylow_centralizer hell (wreathModelHom S e (Original.x (2 ^ n))) P Q⟩

theorem original_product_half_power (m : ℕ) :
    Original.x m = Original.s m ^ (m / 2) * Original.t m ^ (m / 2) := by
  change (Original.s m * Original.t m) ^ (m / 2) = _
  have hst : Commute (Original.s m) (Original.t m) := by
    change Original.s m * Original.t m = Original.t m * Original.s m
    simp [Original.s, Original.t, element_base_mul]
  exact hst.mul_pow _

omit [Finite G] in
theorem original_covering_four_group_coordinates (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    let x := wreathModelHom S e (Original.x (2 ^ n))
    let y := wreathModelHom S e (Original.x2 (2 ^ n))
    let T := modelT n S e
    x ∈ T ∧ y ∈ T ∧ orderOf x = 2 ∧ orderOf y = 2 ∧ x ≠ y ∧
      T = Subgroup.closure ({x, y} : Set G) ∧ T ≤ (S : Subgroup G) := by
  let f := wreathModelHom S e
  let x := f (Original.x (2 ^ n))
  let y := f (Original.x2 (2 ^ n))
  let T := modelT n S e
  have hy : y ∈ T := by
    change _ ∈ modelT n S e
    rw [modelT_eq_actual_generated]
    exact Subgroup.subset_closure (by simp [y, Original.x2, f, map_pow])
  have hx : x ∈ T := by
    change _ ∈ modelT n S e
    rw [modelT_eq_actual_generated]
    have hxp : x = f (Original.s (2 ^ n)) ^ ((2 ^ n) / 2) *
        f (Original.t (2 ^ n)) ^ ((2 ^ n) / 2) := by
      dsimp only [x]
      rw [original_product_half_power, map_mul, map_pow, map_pow]
    rw [hxp]
    exact (Subgroup.closure _).mul_mem
      (Subgroup.subset_closure (by simp [f])) (Subgroup.subset_closure (by simp [f]))
  have hx2 : orderOf x = 2 := by
    rw [show x = f (Original.x (2 ^ n)) from rfl,
      orderOf_injective f (wreathModelHom_injective S e)]
    exact (wreath_center_involution_and_quaternion_coordinates n hn).involution_orders.1
  have hy2 : orderOf y = 2 := by
    rw [show y = f (Original.x2 (2 ^ n)) from rfl,
      orderOf_injective f (wreathModelHom_injective S e)]
    exact (wreath_center_involution_and_quaternion_coordinates n hn).involution_orders.2.1
  have hxy : x ≠ y := by
    intro heq
    have hmodel := (wreathModelHom_injective S e) heq
    exact (wreath_center_involution_and_quaternion_coordinates n hn).distinct_classes.1
      (hmodel ▸ IsConj.refl _)
  have hx1 : x ≠ 1 := fun heq => by simp [heq] at hx2
  have hy1 : y ≠ 1 := fun heq => by simp [heq] at hy2
  let : IsKleinFour T := modelT_isKleinFour n (by omega) S e
  refine ⟨hx, hy, hx2, hy2, hxy,
    original_four_group_generated_pair T x y hx hy hx1 hy1 hxy, ?_⟩
  intro g hg
  obtain ⟨a, ha, rfl⟩ := hg
  exact (e.symm a).property

theorem original_full_Sylow_nonstationary_covering_witness
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    {ell : ℕ} (hell : ell.Prime) (hdiv : ell ∣ Nat.card (centralizerOddCore n S e))
    (P : Sylow ell (centralizerOddCore n S e))
    (hnot : ¬ ∃ J : Sylow ell (OriginalSylowNormalizerWitness.ambientOddCore (Subgroup.normalizer
      (ambientSylow (involutionCentralizer n S e) P : Set G))),
      (J : Subgroup _).map (OriginalSylowNormalizerWitness.ambientOddCore (Subgroup.normalizer
        (ambientSylow (involutionCentralizer n S e) P : Set G))).subtype =
          ambientSylow (involutionCentralizer n S e) P)
    (Q : Sylow ell (OriginalSylowNormalizerWitness.ambientOddCore (Subgroup.normalizer
      (ambientSylow (involutionCentralizer n S e) P : Set G))))
    (hSQ : (S : Subgroup G) ≤ Subgroup.normalizer (((Q : Subgroup _).map
      (OriginalSylowNormalizerWitness.ambientOddCore (Subgroup.normalizer
        (ambientSylow (involutionCentralizer n S e) P : Set G))).subtype) : Set G)) :
    let x := wreathModelHom S e (Original.x (2 ^ n))
    let y := wreathModelHom S e (Original.x2 (2 ^ n))
    let T := Subgroup.closure ({x, y} : Set G)
    let N := involutionCentralizer n S e
    let A := ambientSylow N P
    let O := OriginalSylowNormalizerWitness.ambientOddCore (Subgroup.normalizer (A : Set G))
    let B := (Q : Subgroup O).map O.subtype
    ∃ t w : G, (t = y ∨ t = x * y) ∧ w ∈ B ∧ orderOf w = ell ∧
      x⁻¹ * w * x = w⁻¹ ∧ t⁻¹ * w * t = w ∧ w ∈ Subgroup.centralizer (A : Set G) ∧
      w ∉ N ∧ T ≤ Subgroup.normalizer (Subgroup.zpowers w : Set G) ∧
      Disjoint A (Subgroup.zpowers w) ∧ A ⊔ Subgroup.zpowers w ≤ B ∧
      A ⊔ Subgroup.zpowers w ≤ O ∧
      (((A ⊔ Subgroup.zpowers w : Subgroup G) : Set G) =
        (A : Set G) * (Subgroup.zpowers w : Set G)) ∧
      Nat.card ↥(A ⊔ Subgroup.zpowers w) = ell * Nat.card P ∧
      ∃ E : A × Subgroup.zpowers w ≃* ↥(A ⊔ Subgroup.zpowers w),
        ∀ p : A, ∀ z : Subgroup.zpowers w, (E (p, z) : G) = (p : G) * (z : G) := by
  let x := wreathModelHom S e (Original.x (2 ^ n))
  let y := wreathModelHom S e (Original.x2 (2 ^ n))
  let T := modelT n S e
  let N := involutionCentralizer n S e
  let A := ambientSylow N P
  let O := OriginalSylowNormalizerWitness.ambientOddCore (Subgroup.normalizer (A : Set G))
  let B := (Q : Subgroup O).map O.subtype
  obtain ⟨hxT, hyT, hx2, hy2, hxy, hTgen, hTS⟩ :=
    original_covering_four_group_coordinates n hn S e
  change orderOf x = 2 at hx2
  change orderOf y = 2 at hy2
  let : IsKleinFour T := modelT_isKleinFour n (by omega) S e
  have hx1 : x ≠ 1 := fun heq => by simp [heq] at hx2
  have hy1 : y ≠ 1 := fun heq => by simp [heq] at hy2
  obtain ⟨t, w, ht, hwB, hord, hinv, hfix, hcent, hwN, hTinv, hdis, hprodO,
    hprod, hcard, E, hE⟩ :=
      original_nonstationary_internal_direct_product hell T x y hdiv hxT hyT hx1 hy1
        hxy P hnot Q (hTS.trans hSQ)
  have ht2 : orderOf t = 2 := by
    have htT : t ∈ T := by
      rcases ht with rfl | rfl
      · exact hyT
      · exact T.mul_mem hxT hyT
    have ht1 : t ≠ 1 := by
      rcases ht with rfl | rfl
      · exact hy1
      · intro h
        have hyx : y = x⁻¹ := (inv_eq_iff_mul_eq_one.mpr h).symm
        exact hxy ((hyx.trans (inv_eq_self_of_orderOf_eq_two hx2)).symm)
    exact modelT_nonidentity_order n (by omega) S e ⟨t, htT⟩
      (fun h => ht1 (congrArg (fun z : T => (z : G)) h))
  have hprodB : A ⊔ Subgroup.zpowers w ≤ B := sup_le
    (original_sylow_le_every_normalizer_core_sylow N P Q) (Subgroup.zpowers_le.mpr hwB)
  have hcardP : Nat.card ↥(A ⊔ Subgroup.zpowers w) = ell * Nat.card P := by
    change Nat.card ↥(A ⊔ Subgroup.zpowers w) = ell * Nat.card A at hcard
    rw [show Nat.card A = Nat.card P from original_ambientSylow_card N P] at hcard
    exact hcard
  refine ⟨t, w, ht, hwB, hord, ?_, ?_, hcent, hwN, ?_, hdis, hprodB, hprodO,
    hprod, hcardP, E, hE⟩
  · change x⁻¹ * w * x = w⁻¹
    rw [inv_eq_self_of_orderOf_eq_two hx2] at hinv ⊢
    exact hinv
  · simpa only [inv_eq_self_of_orderOf_eq_two ht2] using hfix
  · rw [← hTgen]
    exact hTinv

theorem original_odd_core_prime_has_proper_full_Sylow_covering_normalizer
    [IsSimpleGroup G] (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) {ell : ℕ} (hell : ell.Prime)
    (hdiv : ell ∣ Nat.card (centralizerOddCore n S e)) :
    (∃ P : Sylow ell (centralizerOddCore n S e),
      (S : Subgroup G) ≤ Subgroup.normalizer
        (ambientSylow (involutionCentralizer n S e) P : Set G)) ∧
    ∀ P : Sylow ell (centralizerOddCore n S e),
      (S : Subgroup G) ≤ Subgroup.normalizer
        (ambientSylow (involutionCentralizer n S e) P : Set G) →
      let x := wreathModelHom S e (Original.x (2 ^ n))
      let y := wreathModelHom S e (Original.x2 (2 ^ n))
      let T := Subgroup.closure ({x, y} : Set G)
      let N := involutionCentralizer n S e
      let A := ambientSylow N P
      let K := Subgroup.normalizer (A : Set G)
      let O := OriginalSylowNormalizerWitness.ambientOddCore K
      T = modelT n S e ∧ IsKleinFour T ∧ K < ⊤ ∧ (S : Subgroup G) ≤ K ∧
        A ≤ O ∧ O ≠ ⊥ ∧
        ((K ⊓ N).subgroupOf N).map (centralizerOddCoreMap n S e) = ⊤ ∧
        (N : Set G) = (OriginalSylowNormalizerWitness.ambientOddCore N : Set G) *
          ((K ⊓ N : Subgroup G) : Set G) ∧
        O ⊓ N ≤ OriginalSylowNormalizerWitness.ambientOddCore N ∧
        (∃ J : Sylow ell ↥(O ⊓ N), (J : Subgroup _).map (O ⊓ N).subtype = A) ∧
        (∃ Q : Sylow ell O, A ≤ (Q : Subgroup O).map O.subtype ∧
          (S : Subgroup G) ≤ Subgroup.normalizer
            (((Q : Subgroup O).map O.subtype) : Set G)) ∧
        (∀ Q : Sylow ell O, A ≤ (Q : Subgroup O).map O.subtype ∧
          ((Q : Subgroup O).map O.subtype) ⊓ N = A) ∧
        ((∃ J : Sylow ell O, (J : Subgroup O).map O.subtype = A) ∨
          ∀ Q : Sylow ell O,
            (S : Subgroup G) ≤ Subgroup.normalizer
              (((Q : Subgroup O).map O.subtype) : Set G) →
            let B := (Q : Subgroup O).map O.subtype
            ∃ t w : G, (t = y ∨ t = x * y) ∧ w ∈ B ∧ orderOf w = ell ∧
              x⁻¹ * w * x = w⁻¹ ∧ t⁻¹ * w * t = w ∧
              w ∈ Subgroup.centralizer (A : Set G) ∧ w ∉ N ∧
              T ≤ Subgroup.normalizer (Subgroup.zpowers w : Set G) ∧
              Disjoint A (Subgroup.zpowers w) ∧ A ⊔ Subgroup.zpowers w ≤ B ∧
              A ⊔ Subgroup.zpowers w ≤ O ∧
              (((A ⊔ Subgroup.zpowers w : Subgroup G) : Set G) =
                (A : Set G) * (Subgroup.zpowers w : Set G)) ∧
              Nat.card ↥(A ⊔ Subgroup.zpowers w) = ell * Nat.card P ∧
              ∃ E : A × Subgroup.zpowers w ≃* ↥(A ⊔ Subgroup.zpowers w),
                ∀ p : A, ∀ z : Subgroup.zpowers w, (E (p, z) : G) = (p : G) * (z : G)) := by
  refine ⟨original_invariant_prime_Sylow_exists n hn S e hell, ?_⟩
  intro P hSP
  dsimp only
  obtain ⟨_, _, _, _, _, hObot, hJ, hQ, hCQ⟩ :=
    original_covering_normalizer_structure n hn S e hell hdiv P hSP
  have hTgen := (original_covering_four_group_coordinates n hn S e).2.2.2.2.2.1
  have hTeq := hTgen.symm
  refine ⟨hTeq, hTeq.symm ▸ modelT_isKleinFour n (by omega) S e,
    original_prime_normalizer_proper n hn S e hell hdiv P, hSP,
    original_sylow_le_normalizer_oddCore _ P, hObot,
    original_normalizer_intersection_quotient_image hell _ P,
    original_sylow_normalizer_set_product hell _ P,
    original_normalizer_oddCore_intersection hell _ P, hJ, hQ, hCQ, ?_⟩
  by_cases hstationary : ∃ J : Sylow ell (OriginalSylowNormalizerWitness.ambientOddCore
      (Subgroup.normalizer (ambientSylow (involutionCentralizer n S e) P : Set G))),
      (J : Subgroup _).map (OriginalSylowNormalizerWitness.ambientOddCore
        (Subgroup.normalizer (ambientSylow (involutionCentralizer n S e) P : Set G))).subtype =
          ambientSylow (involutionCentralizer n S e) P
  · exact Or.inl hstationary
  · right
    intro Q hSQ
    exact original_full_Sylow_nonstationary_covering_witness n hn S e hell hdiv P hstationary Q hSQ

end CFSG.Wreathed.OriginalCoveringSylowNormalizer
