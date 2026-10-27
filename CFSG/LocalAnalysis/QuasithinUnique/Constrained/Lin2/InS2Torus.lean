module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InTorus
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InComplement

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin Matrix MatrixGroups Matrix.SpecialLinearGroup

variable {G : Type} [Group G] {L R : Subgroup G} {n : ℕ} {F : Type} [Field F] [Fintype F]

namespace Adapted

theorem two_eq_zero (A : Adapted L R n F) (hn : 0 < n) : (2 : F) = 0 :=
  two_eq_zero_of_card hn A.card_eq

theorem upper_of_mem (A : Adapted L R n F) {k : G} (hk : k ∈ L ⊓ Subgroup.normalizer (R : Set G)) :
    (A.α ⟨k, hk.1⟩ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 :=
  (A.normalizer_iff ⟨k, hk.1⟩).1 hk.2

@[expose] noncomputable def chiB (A : Adapted L R n F) : ↥(L ⊓ Subgroup.normalizer (R : Set G)) →* Fˣ where
  toFun k := Units.mk0 (A.chi ⟨(k : G), k.2.1⟩) (A.chi_ne_zero (A.upper_of_mem k.2))
  map_one' := by
    apply Units.ext
    exact A.chi_one
  map_mul' x y := by
    apply Units.ext
    exact A.chi_mul (ℓ₁ := ⟨(x : G), x.2.1⟩) (ℓ₂ := ⟨(y : G), y.2.1⟩) (A.upper_of_mem y.2)

theorem mem_R_of_chi_eq_one (A : Adapted L R n F) {k : G} (hk : k ∈ L ⊓ Subgroup.normalizer (R : Set G))
    (h1 : A.chi ⟨k, hk.1⟩ = 1) : k ∈ R := by
  set kL : L := ⟨k, hk.1⟩ with hkL
  have hup : (A.α kL : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := A.upper_of_mem hk
  have h00 : (A.α kL : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := h1
  have h11 : (A.α kL : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
    have := apply_zero_zero_mul_apply_one_one hup
    rw [h00, one_mul] at this
    exact this
  have hα : A.α kL = slUpper ((A.α kL : Matrix (Fin 2) (Fin 2) F) 0 1) := by
    apply Subtype.ext
    rw [slUpper_val]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00, hup, h11]
  exact (A.mem_P kL).2 (by rw [hα]; exact slUpper_mem_slUni _)

theorem chi_eq_one_of_mem_R (A : Adapted L R n F) {k : G} (hkR : k ∈ R) (hkL : k ∈ L) :
    A.chi ⟨k, hkL⟩ = 1 := by
  obtain ⟨c, hc⟩ := mem_slUni.1 ((A.mem_P ⟨k, hkL⟩).1 hkR)
  unfold Adapted.chi
  rw [hc, slUpper_val]
  rfl

theorem eq_one_of_chi_eq_one (A : Adapted L R n F) (hR2 : IsPGroup 2 R) {d : G}
    (hd : d ∈ L ⊓ Subgroup.normalizer (R : Set G)) (hodd : Odd (orderOf d))
    (h1 : A.chi ⟨d, hd.1⟩ = 1) : d = 1 := by
  have hdR : d ∈ R := A.mem_R_of_chi_eq_one hd h1
  obtain ⟨k, hk⟩ := hR2 ⟨d, hdR⟩
  have hk' : d ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have h3 : orderOf d ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have hcop : Nat.Coprime (orderOf d) (2 ^ k) := by
    have : ¬ 2 ∣ orderOf d := hodd.not_two_dvd_nat
    exact (Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr this)).symm
  exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd hcop h3)

theorem exists_chi_eq (A : Adapted L R n F) {a : F} (ha : a ≠ 0) :
    ∃ k : G, ∃ hk : k ∈ L ⊓ Subgroup.normalizer (R : Set G), A.chi ⟨k, hk.1⟩ = a := by
  let w : SL(2, F) := ⟨!![a, 0; 0, a⁻¹], by simp [Matrix.det_fin_two, ha]⟩
  obtain ⟨ℓ, hℓ⟩ := A.α_surj w
  have hup : (A.α ℓ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by rw [hℓ]; rfl
  have hN : (ℓ : G) ∈ Subgroup.normalizer (R : Set G) := (A.normalizer_iff ℓ).2 hup
  refine ⟨ℓ, ⟨ℓ.2, hN⟩, ?_⟩
  unfold Adapted.chi
  rw [hℓ]
  rfl

theorem chiB_surjective (A : Adapted L R n F) : Function.Surjective A.chiB := by
  intro u
  obtain ⟨k, hk, hchi⟩ := A.exists_chi_eq u.ne_zero
  refine ⟨⟨k, hk⟩, ?_⟩
  apply Units.ext
  exact hchi

theorem ker_chiB (A : Adapted L R n F) :
    A.chiB.ker = R.subgroupOf (L ⊓ Subgroup.normalizer (R : Set G)) := by
  ext k
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    have : A.chi ⟨(k : G), k.2.1⟩ = 1 := by
      have := congrArg Units.val h
      exact this
    exact A.mem_R_of_chi_eq_one k.2 this
  · intro h
    apply Units.ext
    exact A.chi_eq_one_of_mem_R h k.2.1

theorem card_borel (A : Adapted L R n F) :
    Nat.card ↥(L ⊓ Subgroup.normalizer (R : Set G)) = Nat.card R * (2 ^ n - 1) := by
  classical
  have h := Subgroup.card_ker_mul_card_of_surjective A.chiB_surjective
  rw [A.ker_chiB] at h
  have hRle : R ≤ L ⊓ Subgroup.normalizer (R : Set G) := le_inf A.P_le Subgroup.le_normalizer
  have h1 : Nat.card ↥(R.subgroupOf (L ⊓ Subgroup.normalizer (R : Set G))) = Nat.card R :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRle).toEquiv
  have h2 : Nat.card Fˣ = 2 ^ n - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, A.card_eq]
  rw [h1, h2] at h
  exact h.symm

theorem mem_pCore_of_comm (A : Adapted L R n F) (hn : 0 < n) {d p : G}
    (hd : d ∈ L ⊓ Subgroup.normalizer (R : Set G)) (hchi : A.chi ⟨d, hd.1⟩ ≠ 1) (hp : p ∈ R)
    (hc : d * p * d⁻¹ * p⁻¹ ∈ pCoreOf 2 L) : p ∈ pCoreOf 2 L := by
  have h2 : (2 : F) = 0 := A.two_eq_zero hn
  have hdL : d ∈ L := hd.1
  have hpL : p ∈ L := A.P_le hp
  have hup : (A.α ⟨d, hdL⟩ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := A.upper_of_mem hd
  have hsq : A.chi ⟨d, hdL⟩ ^ 2 ≠ 1 := fun h1 => hchi (eq_one_of_sq_eq_one h2 h1)
  obtain ⟨t, ht⟩ := mem_slUni.1 ((A.mem_P ⟨p, hpL⟩).1 hp)
  have hcomm : A.α (⟨d, hdL⟩ * ⟨p, hpL⟩ * ⟨d, hdL⟩⁻¹ * ⟨p, hpL⟩⁻¹) = 1 :=
    (A.mem_pCoreOf_iff _).1 hc
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, ht,
    conj_slUpper_of_apply_one_zero _ hup, slUpper_inv, ← slUpper_add] at hcomm
  have h0 : A.chi ⟨d, hdL⟩ ^ 2 * t + -t = 0 := by
    have := slUpper_injective (hcomm.trans slUpper_zero.symm)
    exact this
  have ht0 : t = 0 := by
    have h3 : (A.chi ⟨d, hdL⟩ ^ 2 - 1) * t = 0 := by linear_combination h0
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact absurd (sub_eq_zero.1 h4) hsq
    · exact h4
  rw [ht0, slUpper_zero] at ht
  exact (A.mem_pCoreOf_iff ⟨p, hpL⟩).2 ht

theorem mem_blockZ_of_comm (A : Adapted L R n F) {d u : G}
    (hd : d ∈ L ⊓ Subgroup.normalizer (R : Set G)) (hchi : A.chi ⟨d, hd.1⟩ ≠ 1)
    (hu : u ∈ blockU L) (hc : d * u * d⁻¹ * u⁻¹ ∈ blockZ L) : u ∈ blockZ L := by
  have hdL : d ∈ L := hd.1
  have hup : (A.α ⟨d, hdL⟩ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := A.upper_of_mem hd
  have hcU : d * u * d⁻¹ * u⁻¹ ∈ blockU L :=
    Subgroup.mul_mem _ (mem_blockU_conj hdL hu) (Subgroup.inv_mem _ hu)
  have h1 := (A.mem_blockZ_iff hcU).1 hc
  have e : (⟨d * u * d⁻¹ * u⁻¹, hcU⟩ : blockU L) =
      ⟨d * u * d⁻¹, mem_blockU_conj hdL hu⟩ * ⟨u, hu⟩⁻¹ := rfl
  rw [e, map_mul, map_inv, toAdd_mul, toAdd_inv, A.toAdd_beta_conj ⟨d, hdL⟩ hu] at h1
  set v : Fin 2 → F := Multiplicative.toAdd (A.β ⟨u, hu⟩) with hv
  have hdet := apply_zero_zero_mul_apply_one_one hup
  have ha' : (A.α ⟨d, hdL⟩ : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 1 := by
    intro h5
    rw [h5, mul_one] at hdet
    exact hchi hdet
  have h1_1 := congrFun h1 1
  have h1_0 := congrFun h1 0
  obtain ⟨hm0, hm1⟩ := mulVec_of_apply_one_zero hup v
  simp only [Pi.add_apply, Pi.neg_apply, Pi.zero_apply, hm1] at h1_1
  have hv1 : v 1 = 0 := by
    have : ((A.α ⟨d, hdL⟩ : Matrix (Fin 2) (Fin 2) F) 1 1 - 1) * v 1 = 0 := by
      linear_combination h1_1
    rcases mul_eq_zero.1 this with h6 | h6
    · exact absurd (sub_eq_zero.1 h6) ha'
    · exact h6
  simp only [Pi.add_apply, Pi.neg_apply, Pi.zero_apply, hm0, hv1, mul_zero, add_zero] at h1_0
  have hv0 : v 0 = 0 := by
    have : ((A.α ⟨d, hdL⟩ : Matrix (Fin 2) (Fin 2) F) 0 0 - 1) * v 0 = 0 := by
      linear_combination h1_0
    rcases mul_eq_zero.1 this with h6 | h6
    · exact absurd (sub_eq_zero.1 h6) hchi
    · exact h6
  refine (A.mem_blockZ_iff hu).2 ?_
  funext i
  fin_cases i
  · exact hv0
  · exact hv1

end Adapted

structure BlockTorus (L R Dt : Subgroup G) (n : ℕ) : Prop where
  le_borel : Dt ≤ L ⊓ Subgroup.normalizer (R : Set G)
  card : Nat.card Dt = 2 ^ n - 1
  cyclic : IsCyclic Dt
  fpf_R : ∀ d ∈ Dt, d ≠ 1 → ∀ p ∈ R, d * p * d⁻¹ * p⁻¹ ∈ pCoreOf 2 L → p ∈ pCoreOf 2 L
  fpf_U : ∀ d ∈ Dt, d ≠ 1 → ∀ u ∈ blockU L, d * u * d⁻¹ * u⁻¹ ∈ blockZ L → u ∈ blockZ L

theorem Adapted.blockTorus (A : Adapted L R n F) (hn : 0 < n) (hR2 : IsPGroup 2 R) {Dt : Subgroup G}
    (hle : Dt ≤ L ⊓ Subgroup.normalizer (R : Set G)) (hcard : Nat.card Dt = 2 ^ n - 1) :
    BlockTorus L R Dt n := by
  have hodd : Odd (Nat.card Dt) := by
    rw [hcard]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hx : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    rw [Nat.odd_iff, pow_succ]
    omega
  have hord : ∀ d ∈ Dt, Odd (orderOf d) := by
    intro d hd
    have h1 : orderOf d ∣ Nat.card Dt := by
      have := orderOf_dvd_natCard (⟨d, hd⟩ : Dt)
      rwa [Subgroup.orderOf_mk] at this
    exact Odd.of_dvd_nat hodd h1
  have hne : ∀ d : Dt, d ≠ 1 → A.chi ⟨(d : G), (hle d.2).1⟩ ≠ 1 := by
    intro d hd hchi
    exact hd (Subtype.ext (A.eq_one_of_chi_eq_one hR2 (hle d.2) (hord _ d.2) hchi))
  have hinj : Function.Injective (A.chiB.comp (Subgroup.inclusion hle)) := by
    rw [injective_iff_map_eq_one]
    intro d hd
    by_contra hd1
    apply hne d hd1
    have := congrArg Units.val hd
    exact this
  refine ⟨hle, hcard, isCyclic_of_injective _ hinj, ?_, ?_⟩
  · intro d hd hd1 p hp hc
    have hne' : A.chi ⟨d, (hle hd).1⟩ ≠ 1 := fun h => hd1 (A.eq_one_of_chi_eq_one hR2 (hle hd)
      (hord d hd) h)
    exact A.mem_pCore_of_comm hn (hle hd) hne' hp hc
  · intro d hd hd1 u hu hc
    have hne' : A.chi ⟨d, (hle hd).1⟩ ≠ 1 := fun h => hd1 (A.eq_one_of_chi_eq_one hR2 (hle hd)
      (hord d hd) h)
    exact A.mem_blockZ_of_comm (hle hd) hne' hu hc

section Complement

variable [Finite G]

theorem Adapted.exists_complement (A : Adapted L R n F) (hn : 0 < n) (hR2 : IsPGroup 2 R) :
    ∃ T : Subgroup G, IsComplementIn R (L ⊓ Subgroup.normalizer (R : Set G)) T ∧
      Nat.card T = 2 ^ n - 1 := by
  have hRB : R ≤ L ⊓ Subgroup.normalizer (R : Set G) := le_inf A.P_le Subgroup.le_normalizer
  have hN : L ⊓ Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (R : Set G) := inf_le_right
  have hcard := A.card_borel
  have hpos : 0 < Nat.card R := Nat.card_pos
  have hrel : R.relIndex (L ⊓ Subgroup.normalizer (R : Set G)) = 2 ^ n - 1 := by
    have h := Subgroup.relIndex_mul_card (H := R) (K := L ⊓ Subgroup.normalizer (R : Set G))
    rw [inf_eq_left.mpr hRB, hcard] at h
    exact Nat.eq_of_mul_eq_mul_right hpos (by rw [h, mul_comm])
  have hodd : ¬ 2 ∣ R.relIndex (L ⊓ Subgroup.normalizer (R : Set G)) := by
    rw [hrel]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hx : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    rw [pow_succ]
    omega
  obtain ⟨T, hTB, hRT, hdec⟩ := exists_complement_of_odd hRB hN hR2 hodd
  have hcomp : IsComplementIn R (L ⊓ Subgroup.normalizer (R : Set G)) T := ⟨hTB, hRT, hdec⟩
  refine ⟨T, hcomp, ?_⟩
  have h := hcomp.card_mul hRB hN
  rw [hcard] at h
  exact (Nat.eq_of_mul_eq_mul_left hpos h).symm

end Complement

end CFSG.QuasithinUnique.Lin2
