module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InBorel
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Derived
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InExclusive

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin Matrix MatrixGroups Matrix.SpecialLinearGroup

section Basics

variable {F : Type} [Field F]

theorem two_eq_zero_of_card [Fintype F] {n : ℕ} (hn : 0 < n) (hcard : Fintype.card F = 2 ^ n) :
    (2 : F) = 0 := by
  have h := FiniteField.cast_card_eq_zero F
  rw [hcard] at h
  push_cast at h
  exact pow_eq_zero_iff (by omega) |>.1 h

theorem neg_eq_self_of_two_eq_zero (h2 : (2 : F) = 0) (a : F) : -a = a := by
  have : a + a = 0 := by
    have : a + a = 2 * a := by ring
    rw [this, h2, zero_mul]
  exact neg_eq_of_add_eq_zero_right this

theorem eq_one_of_sq_eq_one (h2 : (2 : F) = 0) {a : F} (h : a ^ 2 = 1) : a = 1 := by
  have h1 : (a - 1) * (a + 1) = 0 := by linear_combination h
  rcases mul_eq_zero.1 h1 with h3 | h3
  · exact sub_eq_zero.1 h3
  · have : a = -1 := eq_neg_of_add_eq_zero_left h3
    rw [this, neg_eq_self_of_two_eq_zero h2]

end Basics

section Coordinates

variable {G : Type} [Group G] {n : ℕ} {F : Type} [Field F] [Fintype F]

theorem mem_blockU_conj {L : Subgroup G} {ℓ u : G} (hℓ : ℓ ∈ L) (hu : u ∈ blockU L) :
    ℓ * u * ℓ⁻¹ ∈ blockU L :=
  (Subgroup.mem_normalizer_iff.1 (le_normalizer_blockU L hℓ) u).1 hu

theorem Adapted.toAdd_beta_conj {L P : Subgroup G} {n : ℕ} (A : Adapted L P n F) (ℓ : L) {u : G}
    (hu : u ∈ blockU L) :
    Multiplicative.toAdd (A.β ⟨(ℓ : G) * u * (ℓ : G)⁻¹, mem_blockU_conj ℓ.2 hu⟩) =
      (A.α ℓ : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (A.β ⟨u, hu⟩)) :=
  A.β_equiv ℓ ⟨u, hu⟩ _ rfl

theorem Adapted.mem_blockZ_iff {L P : Subgroup G} {n : ℕ} (A : Adapted L P n F) {u : G}
    (hu : u ∈ blockU L) : u ∈ blockZ L ↔ Multiplicative.toAdd (A.β ⟨u, hu⟩) = 0 := by
  have : (⟨u, hu⟩ : blockU L) ∈ A.β.ker ↔ u ∈ blockZ L := by
    rw [A.β_ker]
    exact Subgroup.mem_subgroupOf
  rw [← this, MonoidHom.mem_ker]
  constructor
  · intro h; rw [h]; rfl
  · intro h; exact Multiplicative.toAdd.injective h

@[expose] def Adapted.chi {L P : Subgroup G} {n : ℕ} (A : Adapted L P n F) (ℓ : L) : F :=
  (A.α ℓ : Matrix (Fin 2) (Fin 2) F) 0 0

theorem Adapted.chi_mul {L P : Subgroup G} {n : ℕ} (A : Adapted L P n F) {ℓ₁ ℓ₂ : L}
    (h : (A.α ℓ₂ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) :
    A.chi (ℓ₁ * ℓ₂) = A.chi ℓ₁ * A.chi ℓ₂ := by
  unfold Adapted.chi
  rw [map_mul, apply_zero_zero_mul, h, mul_zero, add_zero]

theorem Adapted.chi_ne_zero {L P : Subgroup G} {n : ℕ} (A : Adapted L P n F) {ℓ : L}
    (h : (A.α ℓ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) : A.chi ℓ ≠ 0 := by
  intro h0
  have := apply_zero_zero_mul_apply_one_one h
  unfold Adapted.chi at h0
  rw [h0, zero_mul] at this
  exact zero_ne_one this

theorem Adapted.chi_one {L P : Subgroup G} {n : ℕ} (A : Adapted L P n F) : A.chi 1 = 1 := by
  unfold Adapted.chi
  simp

end Coordinates

section Torus

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ}
  {F : Type} [Field F] [Fintype F]

theorem Lin2Cfg.upper_of_mem (h : Lin2Cfg G T M H S L n D) (A : Adapted L (S ⊓ L) n F) {k : G}
    (hk : k ∈ L ⊓ M) :
    (A.α ⟨k, hk.1⟩ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 :=
  (A.normalizer_iff ⟨k, hk.1⟩).1 (h.inf_M_le_normalizer hk)

theorem Lin2Cfg.upper_of_mem_D (h : Lin2Cfg G T M H S L n D) (A : Adapted L (S ⊓ L) n F) {d : G}
    (hd : d ∈ D) :
    (A.α ⟨d, h.D_le_L hd⟩ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 :=
  h.upper_of_mem A (h.hall.1 hd)

theorem Lin2Cfg.eq_one_of_chi_eq_one (h : Lin2Cfg G T M H S L n D) (A : Adapted L (S ⊓ L) n F)
    {d : G} (hd : d ∈ D) (h1 : A.chi ⟨d, h.D_le_L hd⟩ = 1) : d = 1 := by
  have h2 : (2 : F) = 0 := two_eq_zero_of_card h.one_pos A.card_eq
  set dL : L := ⟨d, h.D_le_L hd⟩ with hdL
  have hup : (A.α dL : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := h.upper_of_mem_D A hd
  have h11 : (A.α dL : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
    have := apply_zero_zero_mul_apply_one_one hup
    have h00 : (A.α dL : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := h1
    rw [h00, one_mul] at this
    exact this
  have h00 : (A.α dL : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := h1
  have hα : A.α dL = slUpper ((A.α dL : Matrix (Fin 2) (Fin 2) F) 0 1) := by
    apply Subtype.ext
    rw [slUpper_val]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00, hup, h11]
  have hsq : A.α (dL * dL) = 1 := by
    rw [map_mul, hα, ← slUpper_add]
    have : (A.α dL : Matrix (Fin 2) (Fin 2) F) 0 1 + (A.α dL : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by
      have : ∀ a : F, a + a = 2 * a := fun a => by ring
      rw [this, h2, zero_mul]
    rw [this, slUpper_zero]
  have hmem : ((dL * dL : L) : G) ∈ pCoreOf 2 L := (A.mem_pCoreOf_iff _).2 hsq
  have hp2 : IsPGroup 2 (pCoreOf 2 L) :=
    CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 L
  obtain ⟨k, hk⟩ := hp2 ⟨_, hmem⟩
  have hk' : (d * d) ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hodd : Odd (Nat.card D) := h.hall.2.1
  have hordD : orderOf d ∣ Nat.card D := by
    have := orderOf_dvd_natCard (⟨d, hd⟩ : D)
    rwa [Subgroup.orderOf_mk] at this
  have hd2 : d ^ 2 ^ (k + 1) = 1 := by
    rw [pow_succ', pow_mul, pow_two]
    exact hk'
  have h3 : orderOf d ∣ 2 ^ (k + 1) := orderOf_dvd_of_pow_eq_one hd2
  have hcop : Nat.Coprime (orderOf d) (2 ^ (k + 1)) := by
    have : ¬ 2 ∣ orderOf d := fun h2' => hodd.not_two_dvd_nat (h2'.trans hordD)
    exact (Nat.Coprime.pow_left (k + 1)
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr this)).symm
  have : orderOf d = 1 := Nat.Coprime.eq_one_of_dvd hcop h3
  exact orderOf_eq_one_iff.1 this

theorem Lin2Cfg.exists_chi_eq (h : Lin2Cfg G T M H S L n D) (A : Adapted L (S ⊓ L) n F) {a : F}
    (ha : a ≠ 0) : ∃ d ∈ D, ∃ hd : d ∈ L, A.chi ⟨d, hd⟩ = a := by
  let w : SL(2, F) := ⟨!![a, 0; 0, a⁻¹], by simp [Matrix.det_fin_two, ha]⟩
  obtain ⟨ℓ, hℓ⟩ := A.α_surj w
  have hup : (A.α ℓ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by rw [hℓ]; rfl
  have hN : (ℓ : G) ∈ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) :=
    (A.normalizer_iff ℓ).2 hup
  have hK : (ℓ : G) ∈ L ⊓ M := by rw [h.inf_M_eq]; exact ⟨ℓ.2, hN⟩
  obtain ⟨p, hp, d, hd, hpd⟩ := h.decomp.2.2 _ hK
  have hpL : p ∈ L := hp.2
  have hdL : d ∈ L := h.D_le_L hd
  have hℓeq : ℓ = ⟨p, hpL⟩ * ⟨d, hdL⟩ := Subtype.ext hpd
  refine ⟨d, hd, hdL, ?_⟩
  have hchi : A.chi ℓ = a := by
    unfold Adapted.chi
    rw [hℓ]
    rfl
  rw [hℓeq, A.chi_mul (h.upper_of_mem_D A hd)] at hchi
  have hp1 : A.chi ⟨p, hpL⟩ = 1 := by
    obtain ⟨c, hc⟩ := mem_slUni.1 ((A.mem_P ⟨p, hpL⟩).1 hp)
    unfold Adapted.chi
    rw [hc, slUpper_val]
    rfl
  rw [hp1, one_mul] at hchi
  exact hchi

noncomputable def Lin2Cfg.chiHom (h : Lin2Cfg G T M H S L n D) (A : Adapted L (S ⊓ L) n F) :
    D →* Fˣ where
  toFun d := Units.mk0 (A.chi ⟨(d : G), h.D_le_L d.2⟩) (A.chi_ne_zero (h.upper_of_mem_D A d.2))
  map_one' := by
    apply Units.ext
    exact A.chi_one
  map_mul' x y := by
    apply Units.ext
    exact A.chi_mul (ℓ₁ := ⟨(x : G), h.D_le_L x.2⟩) (ℓ₂ := ⟨(y : G), h.D_le_L y.2⟩)
      (h.upper_of_mem_D A y.2)

theorem Lin2Cfg.chiHom_injective (h : Lin2Cfg G T M H S L n D) (A : Adapted L (S ⊓ L) n F) :
    Function.Injective (h.chiHom A) := by
  rw [injective_iff_map_eq_one]
  intro d hd
  have h1 : A.chi ⟨(d : G), h.D_le_L d.2⟩ = 1 := by
    have := congrArg Units.val hd
    exact this
  exact Subtype.ext (h.eq_one_of_chi_eq_one A d.2 h1)

theorem Lin2Cfg.chiHom_surjective (h : Lin2Cfg G T M H S L n D) (A : Adapted L (S ⊓ L) n F) :
    Function.Surjective (h.chiHom A) := by
  intro u
  obtain ⟨d, hd, hdL, hchi⟩ := h.exists_chi_eq A u.ne_zero
  refine ⟨⟨d, hd⟩, ?_⟩
  apply Units.ext
  exact hchi

theorem Lin2Cfg.card_D (h : Lin2Cfg G T M H S L n D) :
    Nat.card D = 2 ^ n - 1 := by
  classical
  obtain ⟨F, _, _, ⟨A⟩⟩ := h.coord
  have e : D ≃ Fˣ := Equiv.ofBijective _ ⟨h.chiHom_injective A, h.chiHom_surjective A⟩
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_units, A.card_eq]

theorem Lin2Cfg.isCyclic_D (h : Lin2Cfg G T M H S L n D) : IsCyclic D := by
  obtain ⟨F, _, _, ⟨A⟩⟩ := h.coord
  exact isCyclic_of_injective (h.chiHom A) (h.chiHom_injective A)

theorem Lin2Cfg.mem_pCore_of_comm (h : Lin2Cfg G T M H S L n D) {d p : G} (hd : d ∈ D)
    (hd1 : d ≠ 1) (hp : p ∈ S ⊓ L) (hc : d * p * d⁻¹ * p⁻¹ ∈ pCoreOf 2 L) :
    p ∈ pCoreOf 2 L := by
  obtain ⟨F, _, _, ⟨A⟩⟩ := h.coord
  have h2 : (2 : F) = 0 := two_eq_zero_of_card h.one_pos A.card_eq
  have hdL : d ∈ L := h.D_le_L hd
  have hpL : p ∈ L := hp.2
  have hup : (A.α ⟨d, hdL⟩ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := h.upper_of_mem_D A hd
  have ha1 : A.chi ⟨d, hdL⟩ ≠ 1 := fun h1 => hd1 (h.eq_one_of_chi_eq_one A hd h1)
  have hsq : A.chi ⟨d, hdL⟩ ^ 2 ≠ 1 := fun h1 => ha1 (eq_one_of_sq_eq_one h2 h1)
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

theorem Lin2Cfg.mem_blockZ_of_comm (h : Lin2Cfg G T M H S L n D) {d u : G} (hd : d ∈ D)
    (hd1 : d ≠ 1) (hu : u ∈ blockU L) (hc : d * u * d⁻¹ * u⁻¹ ∈ blockZ L) : u ∈ blockZ L := by
  obtain ⟨F, _, _, ⟨A⟩⟩ := h.coord
  have hdL : d ∈ L := h.D_le_L hd
  have hup : (A.α ⟨d, hdL⟩ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := h.upper_of_mem_D A hd
  have ha1 : A.chi ⟨d, hdL⟩ ≠ 1 := fun h1 => hd1 (h.eq_one_of_chi_eq_one A hd h1)
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
    exact ha1 hdet
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
    · exact absurd (sub_eq_zero.1 h6) ha1
    · exact h6
  refine (A.mem_blockZ_iff hu).2 ?_
  funext i
  fin_cases i
  · exact hv0
  · exact hv1

end Torus

end CFSG.QuasithinUnique.Lin2
