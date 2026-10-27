module

public import CFSG.CharacterTheory.Wreathed.BrauerWongFocal
public import CFSG.CharacterTheory.Wreathed.QuaternionOvergroupsSupport
public import CFSG.CharacterTheory.Wreathed.BrauerWongModel
public import CFSG.CharacterTheory.Wreathed.BrauerWongSupport

public noncomputable section

namespace CFSG.Wreathed.BrauerWong

open CFSG.Wreathed
open scoped commutatorElement

universe u v

@[expose] def IsTypeI (X : Type v) [Group X] : Prop :=
  ¬ ∃ H : Subgroup X, H.Normal ∧ H.index = 2

@[expose] def IsTypeII (X : Type v) [Group X] (S : Subgroup X) (n : ℕ) : Prop :=
  ∃ G₀ : Subgroup X, G₀.Normal ∧ G₀.index = 2 ^ n ∧
    Nonempty (↥(S ⊓ G₀) ≃* QuaternionGroup (2 ^ (n - 1)))

variable {G : Type u} [Group G]

theorem modelY_card (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Nat.card (modelY S e) = 2 ^ (n + 1) := by
  rw [modelY, Subgroup.card_map_of_injective (wreathModelHom_injective S e),
    (wreath_center_involution_and_quaternion_coordinates n hn).quaternion_card, pow_succ,
    mul_comm]

@[expose] def modelYEquiv (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    modelY S e ≃* QuaternionGroup (2 ^ (n - 1)) := by
  have hstr := wreath_center_involution_and_quaternion_coordinates n hn
  have hhalf : 2 ^ n / 2 = 2 ^ (n - 1) := WreathGenerators.half_eq (by omega)
  have eY : QuaternionGroup (2 ^ n / 2) ≃* Original.Y (2 ^ n) := hstr.quaternion.some
  rw [hhalf] at eY
  exact (((Original.Y (2 ^ n)).equivMapOfInjective (wreathModelHom S e)
    (wreathModelHom_injective S e)).symm.trans eY.symm)

theorem modelY_nonempty_equiv (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Nonempty (modelY S e ≃* QuaternionGroup (2 ^ (n - 1))) :=
  ⟨modelYEquiv n hn S e⟩

variable [Finite G]

theorem exists_vNormalizer_swap_eq_x2 (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n))
    (hsix : Nonempty (Subgroup.normalizer (modelV S e : Set G) ⧸ modelVInnerCentralizer S e ≃*
      Equiv.Perm (Fin 3))) :
    ∃ h ∈ Subgroup.normalizer (modelV S e : Set G),
      h⁻¹ * wreathModelHom S e (Original.z (2 ^ n)) * h =
        wreathModelHom S e (Original.x2 (2 ^ n)) := by
  obtain ⟨g, hg, hcases⟩ := modelVNormalizer_swap_fusion n hn S e hsix
  rcases hcases with h | h
  · refine ⟨g⁻¹, (Subgroup.normalizer _).inv_mem hg, ?_⟩
    rw [inv_inv, h]
  · have hzV : wreathModelHom S e (Original.z (2 ^ n)) ∈ modelV S e :=
      ⟨Original.z _, Subgroup.subset_closure (by simp), rfl⟩
    have hzN : wreathModelHom S e (Original.z (2 ^ n)) ∈ Subgroup.normalizer (modelV S e : Set G) :=
      (modelV S e).le_normalizer hzV
    refine ⟨g⁻¹ * (wreathModelHom S e (Original.z (2 ^ n)))⁻¹,
      (Subgroup.normalizer _).mul_mem ((Subgroup.normalizer _).inv_mem hg)
        ((Subgroup.normalizer _).inv_mem hzN), ?_⟩
    have hswap := congrArg (wreathModelHom S e) (swap_conj_base (2 ^ n) 0
      ((2 ^ n / 2 : ℕ) : ZMod (2 ^ n)))
    rw [← t_half_eq_element, ← x2_eq_element, map_mul, map_mul, map_inv] at hswap
    calc
      (g⁻¹ * (wreathModelHom S e (Original.z (2 ^ n)))⁻¹)⁻¹ *
          wreathModelHom S e (Original.z (2 ^ n)) *
          (g⁻¹ * (wreathModelHom S e (Original.z (2 ^ n)))⁻¹) =
        wreathModelHom S e (Original.z (2 ^ n)) *
          (g * wreathModelHom S e (Original.z (2 ^ n)) * g⁻¹) *
          (wreathModelHom S e (Original.z (2 ^ n)))⁻¹ := by group
      _ = wreathModelHom S e (Original.z (2 ^ n)) *
          wreathModelHom S e (Original.t (2 ^ n) ^ (2 ^ n / 2)) *
          (wreathModelHom S e (Original.z (2 ^ n)))⁻¹ := by rw [h]
      _ = wreathModelHom S e (Original.x2 (2 ^ n)) := by
        have hz2 : (wreathModelHom S e (Original.z (2 ^ n)))⁻¹ =
            wreathModelHom S e (Original.z (2 ^ n)) := by
          rw [← map_inv]
          congr 1
          rw [Original.z, element_swap_inv, neg_zero]
        rw [← hswap, hz2]

theorem focal_eq_modelY_of_base_order_two (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n))
    (hcard : Nat.card (Subgroup.normalizer (modelBase S e : Set G) ⧸
      (Subgroup.centralizer (modelBase S e : Set G)).subgroupOf
        (Subgroup.normalizer (modelBase S e : Set G))) = 2)
    (hsix : Nonempty (Subgroup.normalizer (modelV S e : Set G) ⧸ modelVInnerCentralizer S e ≃*
      Equiv.Perm (Fin 3))) :
    (S : Subgroup G).focalSubgroup = modelY S e :=
  le_antisymm (modelY_contains_focal_of_base_order_two n hn S e hcard)
    (modelY_le_focal_of_v_sym3 n hn S e hsix)

theorem typeII_of_base_order_two (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n))
    (hcard : Nat.card (Subgroup.normalizer (modelBase S e : Set G) ⧸
      (Subgroup.centralizer (modelBase S e : Set G)).subgroupOf
        (Subgroup.normalizer (modelBase S e : Set G))) = 2)
    (hsix : Nonempty (Subgroup.normalizer (modelV S e : Set G) ⧸ modelVInnerCentralizer S e ≃*
      Equiv.Perm (Fin 3))) :
    IsTypeII G (S : Subgroup G) n := by
  have hF := focal_eq_modelY_of_base_order_two n hn S e hcard hsix
  obtain ⟨hK, -, hinf, hidx⟩ := transferFocal_ker_spec S
  refine ⟨_, hK, ?_, ?_⟩
  · rw [hF, modelY_card n hn S e] at hidx
    have hS : Nat.card (S : Subgroup G) = 2 ^ (2 * n + 1) := by
      rw [Nat.card_congr e.toEquiv, card_wreath]
      ring
    have h2 : ((S : Subgroup G).transferFocal.ker).index * 2 ^ (n + 1) = 2 ^ n * 2 ^ (n + 1) := by
      rw [hidx, hS, ← pow_add]
      congr 1
      ring
    exact Nat.eq_of_mul_eq_mul_right (pow_pos two_pos _) h2
  · rw [hinf, hF]
    exact modelY_nonempty_equiv n hn S e

omit [Finite G] in
theorem commutator_le_of_index_two {N : Subgroup G} (hN : N.index = 2) :
    commutator G ≤ N := by
  let : N.Normal := Subgroup.normal_of_index_eq_two hN
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card (G ⧸ N) = 2 := by rw [← Subgroup.index_eq_card]; exact hN
  let : IsCyclic (G ⧸ N) := isCyclic_of_prime_card hcard
  exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mp IsCyclic.isMulCommutative

omit [Finite G] in
theorem inv_mul_mem_of_isConj_of_index_two {N : Subgroup G} (hN : N.index = 2) {x y : G}
    (hxy : IsConj x y) : x⁻¹ * y ∈ N := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp hxy
  apply commutator_le_of_index_two hN
  have h : ⁅x⁻¹, g⁆ ∈ commutator G :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top x⁻¹) (Subgroup.mem_top g)
  rw [commutatorElement_def, inv_inv] at h
  simpa only [mul_assoc] using h

theorem typeI_of_base_sym3 (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hbase : Nonempty (Subgroup.normalizer (modelBase S e : Set G) ⧸
      (Subgroup.centralizer (modelBase S e : Set G)).subgroupOf
        (Subgroup.normalizer (modelBase S e : Set G)) ≃* Equiv.Perm (Fin 3)))
    (hsix : Nonempty (Subgroup.normalizer (modelV S e : Set G) ⧸ modelVInnerCentralizer S e ≃*
      Equiv.Perm (Fin 3))) :
    IsTypeI G := by
  rintro ⟨N, -, hidx⟩
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ := wreathModelHom S e with hφ
  have hhalf : 2 ^ n / 2 = 2 ^ (n - 1) := WreathGenerators.half_eq (by omega)
  have hstr := wreath_center_involution_and_quaternion_coordinates n hn
  have hconj {x y : G} (hxy : IsConj x y) : x ∈ N ↔ y ∈ N := by
    have h := inv_mul_mem_of_isConj_of_index_two hidx hxy
    constructor
    · intro hx
      simpa using N.mul_mem hx h
    · intro hy
      have := N.mul_mem hy (N.inv_mem h)
      simpa using this
  have hsq (x : G) : x ^ 2 ∈ N := by
    rw [pow_two]
    exact Subgroup.mul_self_mem_of_index_two hidx x
  have hxN : φ (Original.x (2 ^ n)) ∈ N := by
    have hx : Original.x (2 ^ n) = (Original.a (2 ^ n) ^ (2 ^ (n - 2))) ^ 2 := by
      rw [Original.x, ← pow_mul, hhalf]
      congr 1
      rw [← pow_succ]
      congr 1
      omega
    rw [hx, map_pow]
    exact hsq _
  have hxx2 : IsConj (φ (Original.x (2 ^ n))) (φ (Original.x2 (2 ^ n))) := by
    obtain ⟨g, -, hg⟩ := modelBaseNormalizer_involutions_transitive n (by omega) S e hbase
      (φ (Original.x (2 ^ n))) (φ (Original.x2 (2 ^ n)))
      ((mem_modelBase_iff S e _).mpr (by rw [Original.x_eq, element_mem_base]))
      ((mem_modelBase_iff S e _).mpr (by rw [Original.x2_eq, element_mem_base]))
      (by rw [orderOf_injective _ (wreathModelHom_injective S e)]; exact hstr.involution_orders.1)
      (by rw [orderOf_injective _ (wreathModelHom_injective S e)];
          exact hstr.involution_orders.2.1)
    exact isConj_iff.mpr ⟨g, hg⟩
  have hx2N : φ (Original.x2 (2 ^ n)) ∈ N := (hconj hxx2).mp hxN
  have hzN : φ (Original.z (2 ^ n)) ∈ N := by
    obtain ⟨h, -, hh⟩ := exists_vNormalizer_swap_eq_x2 n hn S e hsix
    have hzc : IsConj (φ (Original.z (2 ^ n))) (φ (Original.x2 (2 ^ n))) :=
      isConj_iff.mpr ⟨h⁻¹, by rw [inv_inv]; exact hh⟩
    exact (hconj hzc).mpr hx2N
  obtain ⟨g, hgN, hg⟩ := modelBaseNormalizer_involutions_transitive n (by omega) S e hbase
    (φ (Original.x (2 ^ n))) (φ (Original.x2 (2 ^ n)))
    ((mem_modelBase_iff S e _).mpr (by rw [Original.x_eq, element_mem_base]))
    ((mem_modelBase_iff S e _).mpr (by rw [Original.x2_eq, element_mem_base]))
    (by rw [orderOf_injective _ (wreathModelHom_injective S e)]; exact hstr.involution_orders.1)
    (by rw [orderOf_injective _ (wreathModelHom_injective S e)];
        exact hstr.involution_orders.2.1)
  have haB : φ (Original.a (2 ^ n)) ∈ modelBase S e :=
    (mem_modelBase_iff S e _).mpr (by rw [Original.a_eq, element_mem_base])
  have huB : g * φ (Original.a (2 ^ n)) * g⁻¹ ∈ modelBase S e :=
    (Subgroup.mem_normalizer_iff.mp hgN _).mp haB
  obtain ⟨u, hu, hueq⟩ := huB
  obtain ⟨⟨i, j, f⟩, rfl⟩ := (coordinateEquiv (2 ^ n)).symm.surjective u
  change element _ i j f ∈ baseSubgroup _ at hu
  change φ (element _ i j f) = _ at hueq
  rw [element_mem_base] at hu
  subst hu
  have hpow : φ (element _ i j 0) ^ (2 ^ n / 2) = φ (Original.x2 (2 ^ n)) := by
    rw [hueq, conj_pow, ← map_pow, ← Original.x, hg]
  rw [← map_pow, element_base_pow, x2_eq_element] at hpow
  have hcoord := (element_eq_iff _ _ _ _ _ _ _).mp (wreathModelHom_injective S e hpow)
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hhalfk : 2 ^ (k + 1) / 2 = 2 ^ k := by rw [pow_succ, Nat.mul_div_cancel _ two_pos]
  rw [hhalfk] at hcoord
  have hiodd : ¬ Even i.val := by
    rw [← half_modulus_smul_eq_zero_iff, hcoord.1]
    exact half_residue_ne_zero k
  have hjeven : Even j.val := by
    rw [← half_modulus_smul_eq_zero_iff, hcoord.2.1]
  have hodd : Odd (i.val + j.val) := by
    rw [Nat.odd_add]
    exact ⟨fun _ => hjeven, fun _ => Nat.not_even_iff_odd.mp hiodd⟩
  have hsN : φ (Original.s (2 ^ (k + 1))) ∈ N := by
    have huN : φ (element _ i j 0) ∈ N := by
      rw [hueq]
      have ha : φ (Original.a (2 ^ (k + 1))) ∈ N := by
        rw [Original.a, map_mul]
        have hts : IsConj (φ (Original.s (2 ^ (k + 1)))) (φ (Original.t (2 ^ (k + 1)))) := by
          refine isConj_iff.mpr ⟨φ (Original.z (2 ^ (k + 1))), ?_⟩
          rw [← map_mul, ← map_inv, ← map_mul, Original.z_conjugates_s]
        have hst := inv_mul_mem_of_isConj_of_index_two hidx hts
        have := N.mul_mem (hsq (φ (Original.s (2 ^ (k + 1))))) hst
        simpa [pow_two, mul_assoc] using this
      have := (hconj (isConj_iff.mpr ⟨g, rfl⟩)).mp ha
      exact this
    have hts : (φ (Original.s (2 ^ (k + 1))))⁻¹ * φ (Original.t (2 ^ (k + 1))) ∈ N := by
      apply inv_mul_mem_of_isConj_of_index_two hidx
      refine isConj_iff.mpr ⟨φ (Original.z (2 ^ (k + 1))), ?_⟩
      rw [← map_mul, ← map_inv, ← map_mul, Original.z_conjugates_s]
    rw [Original.element_eq_powers _ (pow_pos two_pos _), ZMod.val_zero, pow_zero, mul_one,
      map_mul, map_pow, map_pow] at huN
    set sG := φ (Original.s (2 ^ (k + 1)))
    set tG := φ (Original.t (2 ^ (k + 1)))
    obtain ⟨c, hc⟩ := hodd
    let : N.Normal := Subgroup.normal_of_index_eq_two hidx
    let π := QuotientGroup.mk' N
    have hπ (x : G) : x ∈ N ↔ π x = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    have hsqπ (x : G ⧸ N) : x ^ 2 = 1 := by
      have hcard : Nat.card (G ⧸ N) = 2 := by rw [← Subgroup.index_eq_card]; exact hidx
      rw [← hcard]
      exact pow_card_eq_one'
    have htπ : π tG = π sG := by
      have := (hπ _).mp hts
      rw [map_mul, map_inv] at this
      exact (inv_mul_eq_one.mp this).symm
    have hu' : π sG ^ (i.val + j.val) = 1 := by
      have := (hπ _).mp huN
      rw [map_mul, map_pow, map_pow, htπ, ← pow_add] at this
      exact this
    rw [hc, pow_succ, pow_mul, hsqπ, one_pow, one_mul] at hu'
    exact (hπ _).mpr hu'
  have htN : φ (Original.t (2 ^ (k + 1))) ∈ N := by
    have hts : IsConj (φ (Original.s (2 ^ (k + 1)))) (φ (Original.t (2 ^ (k + 1)))) := by
      refine isConj_iff.mpr ⟨φ (Original.z (2 ^ (k + 1))), ?_⟩
      rw [← map_mul, ← map_inv, ← map_mul, Original.z_conjugates_s]
    exact (hconj hts).mp hsN
  have hSN : (S : Subgroup G) ≤ N := by
    intro x hx
    obtain ⟨w, rfl⟩ := exists_wreathModelHom_eq S e hx
    obtain ⟨⟨a, b, f⟩, rfl⟩ := (coordinateEquiv (2 ^ (k + 1))).symm.surjective w
    change φ (element _ a b f) ∈ N
    rw [Original.element_eq_powers _ (pow_pos two_pos _), map_mul, map_mul, map_pow, map_pow,
      map_pow]
    exact N.mul_mem (N.mul_mem (N.pow_mem hsN _) (N.pow_mem htN _)) (N.pow_mem hzN _)
  have hdvd : N.index ∣ (S : Subgroup G).index := Subgroup.index_dvd_of_le hSN
  rw [hidx] at hdvd
  exact S.not_dvd_index hdvd

theorem not_typeI_of_typeII {S : Subgroup G} {n : ℕ} (hn : 1 ≤ n)
    (hII : IsTypeII G S n) : ¬ IsTypeI G := by
  intro hI
  obtain ⟨G₀, hG₀, hidx, -⟩ := hII
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card (G ⧸ G₀) = 2 ^ n := by rw [← Subgroup.index_eq_card]; exact hidx
  obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime 2 (n := n - 1)
    (G := G ⧸ G₀) (by rw [hcard]; exact pow_dvd_pow 2 (by omega))
  have hHidx : H.index = 2 := by
    have h := H.card_mul_index
    rw [hH, hcard] at h
    have h2 : 2 ^ n = 2 ^ (n - 1) * 2 := by
      rw [← pow_succ]
      congr 1
      omega
    exact Nat.eq_of_mul_eq_mul_left (pow_pos two_pos _) (h.trans h2)
  refine hI ⟨H.comap (QuotientGroup.mk' G₀),
    (Subgroup.normal_of_index_eq_two hHidx).comap _, ?_⟩
  rw [Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective G₀), hHidx]

theorem typeII_subgroup_spec (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (G₀ : Subgroup G) [G₀.Normal] (hidx : G₀.index = 2 ^ n)
    (hQ : Nonempty (↥((S : Subgroup G) ⊓ G₀) ≃* QuaternionGroup (2 ^ (n - 1)))) :
    (S : Subgroup G) ⊓ G₀ = modelY S e ∧ IsCyclic (G ⧸ G₀) := by
  set φ := wreathModelHom S e
  have hstr := wreath_center_involution_and_quaternion_coordinates n hn
  have hle : (S : Subgroup G) ⊓ G₀ ≤ φ.range := by
    rw [wreathModelHom_range]
    exact inf_le_left
  obtain ⟨eQ⟩ := hQ
  let Y₁ := ((S : Subgroup G) ⊓ G₀).comap φ
  have eY₁ : Y₁ ≃* ↥((S : Subgroup G) ⊓ G₀) :=
    (Y₁.equivMapOfInjective φ (wreathModelHom_injective S e)).trans
      (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self hle))
  have hY₁ : Y₁ = Original.Y (2 ^ n) := by
    obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
    have hN : N + 1 - 1 = N := by omega
    rw [hN] at eQ
    exact CFSG.Wreathed.QuaternionOvergroups.quaternion_unique N (by omega) Y₁
      (eY₁.trans eQ).symm
  have hinter : (S : Subgroup G) ⊓ G₀ = modelY S e := by
    rw [modelY, ← hY₁]
    exact (Subgroup.map_comap_eq_self hle).symm
  refine ⟨hinter, ?_⟩
  let ψ : Wreath (2 ^ n) →* G ⧸ G₀ := (QuotientGroup.mk' G₀).comp φ
  have hker : ψ.ker = Original.Y (2 ^ n) := by
    rw [← hY₁]
    ext w
    rw [MonoidHom.mem_ker]
    change (QuotientGroup.mk' G₀ (φ w) = 1) ↔ (φ w ∈ (S : Subgroup G) ∧ φ w ∈ G₀)
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact ⟨fun h => ⟨wreathModelHom_mem S e w, h⟩, fun h => h.2⟩
  obtain ⟨hYnormal, -, hYcard, hYcyc⟩ := hstr.quaternion_quotient
  let := hYnormal
  have : IsCyclic (Wreath (2 ^ n) ⧸ Original.Y (2 ^ n)) := hYcyc
  have hrange_card : Nat.card ψ.range = 2 ^ n := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv,
      Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hker).toEquiv]
    exact hYcard
  have hsurj : Function.Surjective ψ := by
    rw [← MonoidHom.range_eq_top]
    apply Subgroup.eq_top_of_card_eq
    rw [hrange_card, ← Subgroup.index_eq_card, hidx]
  let ψ' : Wreath (2 ^ n) ⧸ Original.Y (2 ^ n) →* G ⧸ G₀ :=
    QuotientGroup.lift (Original.Y (2 ^ n)) ψ hker.ge
  have hψ' : Function.Surjective ψ' := by
    intro q
    obtain ⟨w, rfl⟩ := hsurj q
    exact ⟨w, QuotientGroup.lift_mk _ _ _⟩
  exact isCyclic_of_surjective ψ' hψ'

theorem types_of_vSym3 (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hsix : Nonempty (Subgroup.normalizer (modelV S e : Set G) ⧸ modelVInnerCentralizer S e ≃*
      Equiv.Perm (Fin 3))) :
    (Nonempty (Subgroup.normalizer (modelBase S e : Set G) ⧸
        (Subgroup.centralizer (modelBase S e : Set G)).subgroupOf
          (Subgroup.normalizer (modelBase S e : Set G)) ≃* Equiv.Perm (Fin 3)) →
        IsTypeI G ∧ ¬ IsTypeII G (S : Subgroup G) n) ∧
    (Nat.card (Subgroup.normalizer (modelBase S e : Set G) ⧸
        (Subgroup.centralizer (modelBase S e : Set G)).subgroupOf
          (Subgroup.normalizer (modelBase S e : Set G))) = 2 →
        ¬ IsTypeI G ∧ IsTypeII G (S : Subgroup G) n) := by
  refine ⟨fun hbase => ?_, fun hcard => ?_⟩
  · have hI := typeI_of_base_sym3 n hn S e hbase hsix
    exact ⟨hI, fun hII => not_typeI_of_typeII (by omega) hII hI⟩
  · have hII := typeII_of_base_order_two n hn S e hcard hsix
    exact ⟨not_typeI_of_typeII (by omega) hII, hII⟩

theorem exactly_one_type (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hsix : Nonempty (Subgroup.normalizer (modelV S e : Set G) ⧸ modelVInnerCentralizer S e ≃*
      Equiv.Perm (Fin 3))) :
    (IsTypeI G ∧ ¬ IsTypeII G (S : Subgroup G) n) ∨
      (¬ IsTypeI G ∧ IsTypeII G (S : Subgroup G) n) := by
  obtain ⟨h1, h2⟩ := types_of_vSym3 n hn S e hsix
  rcases modelBaseNormalizerQuotient_alternatives n (by omega) S e with htwo | hsixB
  · exact Or.inr (h2 htwo)
  · exact Or.inl (h1 hsixB)

theorem base_order_two_of_typeII (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hsix : Nonempty (Subgroup.normalizer (modelV S e : Set G) ⧸ modelVInnerCentralizer S e ≃*
      Equiv.Perm (Fin 3))) (hII : IsTypeII G (S : Subgroup G) n) :
    Nat.card (Subgroup.normalizer (modelBase S e : Set G) ⧸
      (Subgroup.centralizer (modelBase S e : Set G)).subgroupOf
        (Subgroup.normalizer (modelBase S e : Set G))) = 2 := by
  rcases modelBaseNormalizerQuotient_alternatives n (by omega) S e with htwo | hsixB
  · exact htwo
  · exact absurd hII ((types_of_vSym3 n hn S e hsix).1 hsixB).2

theorem base_sym3_of_typeI (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hsix : Nonempty (Subgroup.normalizer (modelV S e : Set G) ⧸ modelVInnerCentralizer S e ≃*
      Equiv.Perm (Fin 3))) (hI : IsTypeI G) :
    Nonempty (Subgroup.normalizer (modelBase S e : Set G) ⧸
      (Subgroup.centralizer (modelBase S e : Set G)).subgroupOf
        (Subgroup.normalizer (modelBase S e : Set G)) ≃* Equiv.Perm (Fin 3)) := by
  rcases modelBaseNormalizerQuotient_alternatives n (by omega) S e with htwo | hsixB
  · exact absurd hI ((types_of_vSym3 n hn S e hsix).2 htwo).1
  · exact hsixB

end CFSG.Wreathed.BrauerWong
