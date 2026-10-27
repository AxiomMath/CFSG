module

public import CFSG.CharacterTheory.Wreathed.OriginalCoveringSylowNormalizer

public noncomputable section

namespace CFSG.Wreathed.OriginalNonstationaryWreathAction

open scoped Classical

universe u

variable {G : Type u} [Group G]

theorem central_involution_mem_normal_two_subgroup [Finite G]
    [IsCyclic (Subgroup.center G)] (hG : IsPGroup 2 G)
    (x : G) (hx : x ∈ Subgroup.center G) (horder : orderOf x = 2)
    (D : Subgroup G) [D.Normal] (hD : D ≠ ⊥) : x ∈ D := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Group.IsNilpotent G := hG.isNilpotent
  let L := D ⊓ Subgroup.center G
  have hL : L ≠ ⊥ := Group.IsNilpotent.inf_center_ne_bot_of_normal hD
  have hcard : Nat.card L ≠ 1 := by
    intro h
    exact hL ((Subgroup.eq_bot_iff_card L).mpr h)
  have hdvd : 2 ∣ Nat.card L := (hG.to_subgroup L).card_eq_or_dvd.resolve_left hcard
  let xZ : Subgroup.center G := ⟨x, hx⟩
  have hle : Subgroup.zpowers xZ ≤ L.subgroupOf (Subgroup.center G) := by
    apply IsCyclic.subgroup_le_iff_card_dvd.mpr
    rw [Nat.card_zpowers, ← Subgroup.orderOf_coe xZ, horder,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv]
    exact hdvd
  exact (hle (Subgroup.mem_zpowers xZ)).1

@[expose] def subgroupConjugation (S Q : Subgroup G)
    (hSQ : S ≤ Subgroup.normalizer (Q : Set G)) : S →* MulAut Q :=
  Q.normalizerMonoidHom.comp (Subgroup.inclusion hSQ)

theorem subgroupConjugation_ker (S Q : Subgroup G)
    (hSQ : S ≤ Subgroup.normalizer (Q : Set G)) :
    (subgroupConjugation S Q hSQ).ker =
      (Subgroup.centralizer (Q : Set G)).subgroupOf S := by
  ext s
  change Q.normalizerMonoidHom (Subgroup.inclusion hSQ s) = 1 ↔ _
  rw [← MonoidHom.mem_ker, Subgroup.normalizerMonoidHom_ker]
  rfl

theorem subgroupCentralizer_normal (S Q : Subgroup G)
    (hSQ : S ≤ Subgroup.normalizer (Q : Set G)) :
    ((Subgroup.centralizer (Q : Set G)).subgroupOf S).Normal := by
  rw [← subgroupConjugation_ker S Q hSQ]
  infer_instance

theorem original_sylow_center_isCyclic (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    IsCyclic (Subgroup.center (S : Subgroup G)) := by
  let F : Subgroup.center (S : Subgroup G) ≃* Original.Z (2 ^ n) :=
    (e.subgroupMap (Subgroup.center (S : Subgroup G))).trans
      (MulEquiv.subgroupCongr ((Subgroup.map_center_eq e).trans
        (wreath_center_involution_and_quaternion_coordinates n hn).center))
  apply F.isCyclic.mpr
  change IsCyclic (Subgroup.zpowers (Original.a (2 ^ n)))
  infer_instance

theorem original_involution_mem_normal_sylow_subgroup [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (D : Subgroup (S : Subgroup G)) [D.Normal] (hD : D ≠ ⊥) :
    e.symm (Original.x (2 ^ n)) ∈ D := by
  let : IsCyclic (Subgroup.center (S : Subgroup G)) :=
    original_sylow_center_isCyclic n hn S e
  apply central_involution_mem_normal_two_subgroup S.isPGroup'
    (e.symm (Original.x (2 ^ n))) ?_ ?_ D hD
  · rw [← Subgroup.map_center_eq e.symm]
    refine Subgroup.mem_map.mpr ⟨Original.x (2 ^ n), ?_, rfl⟩
    rw [(wreath_center_involution_and_quaternion_coordinates n hn).center]
    exact (Original.Z _).pow_mem (Subgroup.mem_zpowers _) _
  · exact (e.symm.orderOf_eq _).trans
      (wreath_center_involution_and_quaternion_coordinates n hn).involution_orders.1

theorem original_sylow_centralizer_eq_bot [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (Q : Subgroup G) (hSQ : (S : Subgroup G) ≤ Subgroup.normalizer (Q : Set G))
    (hx : wreathModelHom S e (Original.x (2 ^ n)) ∉
      Subgroup.centralizer (Q : Set G)) :
    (S : Subgroup G) ⊓ Subgroup.centralizer (Q : Set G) = ⊥ := by
  let D := (Subgroup.centralizer (Q : Set G)).subgroupOf (S : Subgroup G)
  have : D.Normal := subgroupCentralizer_normal (S : Subgroup G) Q hSQ
  have hD : D = ⊥ := by
    by_contra h
    exact hx (original_involution_mem_normal_sylow_subgroup n hn S e D h)
  have hmap := congrArg (Subgroup.map (S : Subgroup G).subtype) hD
  rw [Subgroup.map_bot] at hmap
  change ((Subgroup.centralizer (Q : Set G)).comap
    (S : Subgroup G).subtype).map (S : Subgroup G).subtype = ⊥ at hmap
  rw [Subgroup.map_comap_eq, Subgroup.range_subtype] at hmap
  simpa only [inf_comm] using hmap

theorem original_sylow_conjugation_injective [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (Q : Subgroup G) (hSQ : (S : Subgroup G) ≤ Subgroup.normalizer (Q : Set G))
    (hx : wreathModelHom S e (Original.x (2 ^ n)) ∉
      Subgroup.centralizer (Q : Set G)) :
    Function.Injective (subgroupConjugation (S : Subgroup G) Q hSQ) := by
  apply (MonoidHom.ker_eq_bot_iff (subgroupConjugation (S : Subgroup G) Q hSQ)).mp
  rw [subgroupConjugation_ker]
  have h := original_sylow_centralizer_eq_bot n hn S e Q hSQ hx
  ext s
  change (s : G) ∈ Subgroup.centralizer (Q : Set G) ↔ s = 1
  constructor
  · intro hs
    exact Subtype.ext ((Subgroup.mem_bot.mp (h ▸ ⟨s.property, hs⟩)))
  · rintro rfl
    exact (Subgroup.centralizer (Q : Set G)).one_mem

theorem normal_subgroup_card_dvd_index_of_inf_eq_bot [Finite G]
    (D T : Subgroup G) [D.Normal] (hDT : D ⊓ T = ⊥) :
    Nat.card D ∣ T.index := by
  have hsub : D.subgroupOf T = ⊥ := by
    ext t
    change (t : G) ∈ D ↔ t = 1
    constructor
    · intro ht
      exact Subtype.ext (Subgroup.mem_bot.mp (hDT ▸ ⟨ht, t.property⟩))
    · rintro rfl
      exact D.one_mem
  have hrel : D.relIndex T = Nat.card T := by
    change (D.subgroupOf T).index = _
    rw [hsub, Subgroup.index_bot]
  have hcard : Nat.card D * Nat.card T = Nat.card (D ⊔ T : Subgroup G) := by
    have h := (D.subgroupOf (D ⊔ T)).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv] at h
    change Nat.card D * D.relIndex (D ⊔ T) = _ at h
    rw [Subgroup.relIndex_sup_left, hrel] at h
    exact h
  have hdvd : Nat.card T * Nat.card D ∣ Nat.card T * T.index := by
    rw [mul_comm (Nat.card T), hcard, T.card_mul_index]
    exact Subgroup.card_subgroup_dvd_card _
  exact Nat.dvd_of_mul_dvd_mul_left Nat.card_pos hdvd

theorem normal_subgroup_odd_card_of_sylow_inf_eq_bot [Finite G]
    (D : Subgroup G) [D.Normal] (T : Sylow 2 G)
    (hDT : D ⊓ (T : Subgroup G) = ⊥) : Odd (Nat.card D) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply Nat.not_even_iff_odd.mp
  intro h
  exact T.not_dvd_index ((even_iff_two_dvd.mp h).trans
    (normal_subgroup_card_dvd_index_of_inf_eq_bot D (T : Subgroup G) hDT))

open CFSG.Wreathed.OriginalSylowNormalizerWitness
open CFSG.Wreathed.OriginalCoveringSylowNormalizer


theorem subgroupConjugation_apply_coe (S Q : Subgroup G)
    (hSQ : S ≤ Subgroup.normalizer (Q : Set G)) (s : S) (q : Q) :
    ((subgroupConjugation S Q hSQ s) q : G) = (s : G) * (q : G) * (s : G)⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe Q (Subgroup.inclusion hSQ s) q

@[expose] def includedSubgroupConjugation (S O : Subgroup G) (Q : Subgroup O)
    (hSQ : S ≤ Subgroup.normalizer ((Q.map O.subtype) : Set G)) : S →* MulAut Q :=
  let F := Q.equivMapOfInjective O.subtype O.subtype_injective
  (MulAut.congr F.symm).toMonoidHom.comp (subgroupConjugation S (Q.map O.subtype) hSQ)

theorem includedSubgroupConjugation_apply_coe (S O : Subgroup G) (Q : Subgroup O)
    (hSQ : S ≤ Subgroup.normalizer ((Q.map O.subtype) : Set G)) (s : S) (q : Q) :
    (((includedSubgroupConjugation S O Q hSQ s) q : O) : G) =
      (s : G) * ((q : O) : G) * (s : G)⁻¹ := by
  let F := Q.equivMapOfInjective O.subtype O.subtype_injective
  let a := subgroupConjugation S (Q.map O.subtype) hSQ s
  have heq : F ((includedSubgroupConjugation S O Q hSQ s) q) = a (F q) := by
    change F (F.symm (a (F q))) = a (F q)
    exact F.apply_symm_apply _
  have hval := congrArg (fun b : Q.map O.subtype => (b : G)) heq
  simpa only [Subgroup.coe_equivMapOfInjective_apply,
    subgroupConjugation_apply_coe, Subgroup.coe_subtype, F, a] using hval

theorem includedSubgroupConjugation_injective (S O : Subgroup G) (Q : Subgroup O)
    (hSQ : S ≤ Subgroup.normalizer ((Q.map O.subtype) : Set G))
    (hfaithful : Function.Injective (subgroupConjugation S (Q.map O.subtype) hSQ)) :
    Function.Injective (includedSubgroupConjugation S O Q hSQ) := by
  let F := Q.equivMapOfInjective O.subtype O.subtype_injective
  exact (MulAut.congr F.symm).injective.comp hfaithful

theorem sylow_centralizer_in_subgroup_odd [Finite G]
    (S : Sylow 2 G) (K Q : Subgroup G)
    (hSK : (S : Subgroup G) ≤ K)
    (hSQ : (S : Subgroup G) ≤ Subgroup.normalizer (Q : Set G))
    (hC : (S : Subgroup G) ⊓ Subgroup.centralizer (Q : Set G) = ⊥) :
    Odd (Nat.card (K ⊓ Subgroup.centralizer (Q : Set G) : Subgroup G)) := by
  let C := Subgroup.centralizer (Q : Set G)
  let B := K ⊓ Subgroup.normalizer (Q : Set G)
  let D := K ⊓ C
  have hDB : D ≤ B := inf_le_inf le_rfl (Subgroup.centralizer_le_normalizer _)
  have hSB : (S : Subgroup G) ≤ B := le_inf hSK hSQ
  have : (D.subgroupOf B).Normal :=
    Subgroup.inf_subgroupOf_inf_normal_of_right K C (Subgroup.normalizer (Q : Set G))
  let T := S.subtype hSB
  have hDT : (D.subgroupOf B) ⊓ (T : Subgroup B) = ⊥ := by
    ext b
    change ((b : G) ∈ D ∧ (b : G) ∈ (S : Subgroup G)) ↔ b = 1
    constructor
    · rintro ⟨hbD, hbS⟩
      exact Subtype.ext (Subgroup.mem_bot.mp (hC ▸ ⟨hbS, hbD.2⟩))
    · rintro rfl
      exact ⟨D.one_mem, (S : Subgroup G).one_mem⟩
  have hodd := normal_subgroup_odd_card_of_sylow_inf_eq_bot (D.subgroupOf B) T hDT
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDB).toEquiv] at hodd

theorem centralizer_map_subtype (K : Subgroup G) (A : Subgroup K) :
    (Subgroup.centralizer ((A.map K.subtype) : Set G)).subgroupOf K =
      Subgroup.centralizer (A : Set K) := by
  ext k
  change (k : G) ∈ Subgroup.centralizer ((A.map K.subtype) : Set G) ↔ _
  constructor
  · intro hk
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hk (a : G)
      (Subgroup.mem_map_of_mem K.subtype ha))
  · intro hk
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    obtain ⟨aK, haK, heq⟩ := Subgroup.mem_map.mp ha
    rw [← heq]
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hk aK haK)

theorem odd_core_Sylow_centralizer_le_ambientOddCore [Finite G]
    {ell : ℕ} (hell : ell.Prime) (K : Subgroup G) (Q : Sylow ell (ambientOddCore K))
    (hodd : Odd (Nat.card (K ⊓ Subgroup.centralizer
      (((Q : Subgroup (ambientOddCore K)).map (ambientOddCore K).subtype) : Set G) :
        Subgroup G))) :
    K ⊓ Subgroup.centralizer
      (((Q : Subgroup (ambientOddCore K)).map (ambientOddCore K).subtype) : Set G) ≤
        ambientOddCore K := by
  let : Fact ell.Prime := ⟨hell⟩
  let O := ambientOddCore K
  let F : CFSG.oddCore K ≃* O :=
    (CFSG.oddCore K).equivMapOfInjective K.subtype K.subtype_injective
  let f : O →* CFSG.oddCore K := F.symm.toMonoidHom
  have hf : Function.Surjective f := by
    intro a
    exact ⟨F a, F.symm_apply_apply a⟩
  let Q0 : Sylow ell (CFSG.oddCore K) := Q.mapSurjective (f := f) hf
  let A := (Q0 : Subgroup (CFSG.oddCore K)).map (CFSG.oddCore K).subtype
  let B := (Q : Subgroup O).map O.subtype
  have hcomp : K.subtype.comp ((CFSG.oddCore K).subtype.comp f) =
      O.subtype := by
    ext o
    exact congrArg (fun z : O => (z : G)) (F.apply_symm_apply o)
  have hAB : A.map K.subtype = B := by
    dsimp only [A, Q0]
    rw [Sylow.coe_mapSurjective, Subgroup.map_map, Subgroup.map_map,
      MonoidHom.comp_assoc, hcomp]
  let C := Subgroup.centralizer (A : Set K)
  have hC : (Subgroup.centralizer (B : Set G)).subgroupOf K = C := by
    rw [← hAB]
    exact centralizer_map_subtype K A
  have hCodd : Odd (Nat.card C) := by
    rw [← hC]
    have hCK : (Subgroup.centralizer (B : Set G)).subgroupOf K =
        (K ⊓ Subgroup.centralizer (B : Set G)).subgroupOf K := by
      ext k
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, k.property, true_and]
    rw [hCK, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]
    exact hodd
  have hCO : C ≤ CFSG.oddCore K :=
    normal_odd_normalizer_subgroup_le_oddCore hell Q0 C
      (Subgroup.centralizer_le_normalizer _) (by infer_instance) hCodd
  have hmap := Subgroup.map_mono (f := K.subtype) hCO
  rw [← hC] at hmap
  change ((Subgroup.centralizer (B : Set G)).comap K.subtype).map K.subtype ≤ _ at hmap
  rw [Subgroup.map_comap_eq, Subgroup.range_subtype] at hmap
  change K ⊓ Subgroup.centralizer (B : Set G) ≤ ambientOddCore K
  simpa only [inf_comm, ambientOddCore] using hmap

theorem original_nonstationary_Sylow_lt [Finite G]
    {ell : ℕ} (N : Subgroup G) (P : Sylow ell (CFSG.oddCore N))
    (hP : ¬ ∃ Q : Sylow ell (ambientOddCore
      (Subgroup.normalizer (ambientSylow N P : Set G))),
      (Q : Subgroup _).map
        (ambientOddCore (Subgroup.normalizer (ambientSylow N P : Set G))).subtype =
          ambientSylow N P)
    (Q : Sylow ell (ambientOddCore (Subgroup.normalizer (ambientSylow N P : Set G)))) :
    ambientSylow N P < (Q : Subgroup _).map
      (ambientOddCore (Subgroup.normalizer (ambientSylow N P : Set G))).subtype := by
  apply lt_of_le_of_ne (original_sylow_le_every_normalizer_core_sylow N P Q)
  intro h
  exact hP ⟨Q, h.symm⟩

theorem original_nonstationary_involution_not_centralizing [Finite G]
    (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    {ell : ℕ} (hell : ell.Prime) (P : Sylow ell (centralizerOddCore n S e))
    (Q : Sylow ell (ambientOddCore (Subgroup.normalizer
      (ambientSylow (involutionCentralizer n S e) P : Set G))))
    (hPQ : ambientSylow (involutionCentralizer n S e) P <
      (Q : Subgroup _).map (ambientOddCore (Subgroup.normalizer
        (ambientSylow (involutionCentralizer n S e) P : Set G))).subtype) :
    wreathModelHom S e (Original.x (2 ^ n)) ∉ Subgroup.centralizer
      (((Q : Subgroup _).map (ambientOddCore (Subgroup.normalizer
        (ambientSylow (involutionCentralizer n S e) P : Set G))).subtype) : Set G) := by
  let N := involutionCentralizer n S e
  let A := ambientSylow N P
  let O := ambientOddCore (Subgroup.normalizer (A : Set G))
  let B := (Q : Subgroup O).map O.subtype
  have hBN : B ⊓ N = A :=
    original_core_sylow_centralizer hell (wreathModelHom S e (Original.x (2 ^ n))) P Q
  intro hx
  have hle : B ≤ N := by
    intro b hb
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hx b hb)
  have hBA : B = A := (inf_eq_left.mpr hle).symm.trans hBN
  exact (ne_of_lt hPQ) hBA.symm

theorem original_nonstationarity_forces_faithful_wreath_action_and_odd_core_centralizer
    [Finite G] [IsSimpleGroup G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    {ell : ℕ} (hell : ell.Prime) (hdiv : ell ∣ Nat.card (centralizerOddCore n S e))
    (P : Sylow ell (centralizerOddCore n S e))
    (hSP : (S : Subgroup G) ≤ Subgroup.normalizer
      (ambientSylow (involutionCentralizer n S e) P : Set G))
    (hP : ¬ ∃ Q : Sylow ell (ambientOddCore (Subgroup.normalizer
      (ambientSylow (involutionCentralizer n S e) P : Set G))),
      (Q : Subgroup _).map (ambientOddCore (Subgroup.normalizer
        (ambientSylow (involutionCentralizer n S e) P : Set G))).subtype =
          ambientSylow (involutionCentralizer n S e) P) :
    let N := involutionCentralizer n S e
    let A := ambientSylow N P
    let K := Subgroup.normalizer (A : Set G)
    let O := ambientOddCore K
    K < ⊤ ∧ (S : Subgroup G) ≤ K ∧
      (∃ Q : Sylow ell O, (S : Subgroup G) ≤
        Subgroup.normalizer (((Q : Subgroup O).map O.subtype) : Set G)) ∧
      (∀ Q : Sylow ell O,
        ∀ hSQ : (S : Subgroup G) ≤
          Subgroup.normalizer (((Q : Subgroup O).map O.subtype) : Set G),
        let B := (Q : Subgroup O).map O.subtype
        A < B ∧ B ⊓ N = A ∧
          (S : Subgroup G) ⊓ Subgroup.centralizer (B : Set G) = ⊥ ∧
          K ⊓ Subgroup.centralizer (B : Set G) ≤ O ∧
          Function.Injective (subgroupConjugation (S : Subgroup G) B hSQ) ∧
          Function.Injective (includedSubgroupConjugation (S : Subgroup G) O
            (Q : Subgroup O) hSQ) ∧
          Odd (Nat.card (K ⊓ Subgroup.centralizer (B : Set G) : Subgroup G))) := by
  dsimp only
  let N := involutionCentralizer n S e
  let A := ambientSylow N P
  let K := Subgroup.normalizer (A : Set G)
  let O := ambientOddCore K
  refine ⟨original_prime_normalizer_proper n hn S e hell hdiv P, hSP, ?_, ?_⟩
  · obtain ⟨Q, _, hQ⟩ := original_full_invariant_normalizer_core_Sylow hell N P S hSP
    exact ⟨Q, hQ⟩
  · intro Q hSQ
    let B := (Q : Subgroup O).map O.subtype
    have hPQ := original_nonstationary_Sylow_lt N P hP Q
    have hx := original_nonstationary_involution_not_centralizing n S e hell P Q hPQ
    have hC := original_sylow_centralizer_eq_bot n hn S e B hSQ hx
    have hodd := sylow_centralizer_in_subgroup_odd S K B hSP hSQ hC
    exact ⟨hPQ,
      original_core_sylow_centralizer hell (wreathModelHom S e (Original.x (2 ^ n))) P Q,
      hC, odd_core_Sylow_centralizer_le_ambientOddCore hell K Q hodd,
      original_sylow_conjugation_injective n hn S e B hSQ hx,
      includedSubgroupConjugation_injective (S : Subgroup G) O (Q : Subgroup O) hSQ
        (original_sylow_conjugation_injective n hn S e B hSQ hx), hodd⟩

end CFSG.Wreathed.OriginalNonstationaryWreathAction
