module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7StdL316X
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4L2Inv
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7StdEven

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB

namespace Catalog7Std

open Matrix Subgroup CatFactsSp4

theorem four_dvd_orderOf_mul {G : Type*} [Group G] [Finite G] {U : Subgroup G} {t : G}
    (ht : t ∈ normalizer (U : Set G)) (hU : Odd (Nat.card U)) (ht4 : orderOf t = 4) {s : G}
    (hs : s ∈ U) : 4 ∣ orderOf (t * s) := by
  have key : ∀ n : ℕ, ∃ u ∈ U, (t * s) ^ n = t ^ n * u := by
    intro n
    induction n with
    | zero => exact ⟨1, one_mem _, by simp⟩
    | succ n ih =>
      obtain ⟨u, hu, hn⟩ := ih
      refine ⟨t⁻¹ * u * t * s, mul_mem ?_ hs, ?_⟩
      · have := (mem_normalizer_iff.mp (inv_mem ht) u).mp hu
        simpa using this
      · rw [pow_succ, hn, pow_succ]
        group
  obtain ⟨u, hu, hk⟩ := key (orderOf (t * s))
  rw [pow_orderOf_eq_one] at hk
  have htk : t ^ orderOf (t * s) = u⁻¹ := by
    rw [eq_inv_iff_mul_eq_one]
    exact hk.symm
  have hmem : t ^ orderOf (t * s) ∈ U := htk ▸ inv_mem hu
  have h1 : orderOf (t ^ orderOf (t * s)) ∣ Nat.card U := by
    rw [← Subgroup.orderOf_mk _ hmem]
    exact orderOf_dvd_natCard _
  have h2 : orderOf (t ^ orderOf (t * s)) ∣ 4 := ht4 ▸ orderOf_pow_dvd _
  have h3 : orderOf (t ^ orderOf (t * s)) = 1 := by
    have h4 : orderOf (t ^ orderOf (t * s)) ∣ 2 ^ 2 := h2
    obtain ⟨k, hk2, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h4
    interval_cases k
    · simpa using hk
    · exfalso
      rw [hk] at h1
      exact (Nat.not_even_iff_odd.mpr hU) (even_iff_two_dvd.mpr (by simpa using h1))
    · exfalso
      rw [hk] at h1
      exact (Nat.not_even_iff_odd.mpr hU) (even_iff_two_dvd.mpr
        ((dvd_pow_self 2 (by norm_num)).trans h1))
  rw [orderOf_eq_one_iff] at h3
  rw [← ht4]
  exact orderOf_dvd_of_pow_eq_one h3

variable {F : Type} [Field F]

@[expose] def unipHom (F : Type) [Field F] :
    Multiplicative F →* Matrix.SpecialLinearGroup (Fin 2) F where
  toFun x := unipU x.toAdd
  map_one' := by
    apply Subtype.ext
    rw [coe_unipU, Matrix.SpecialLinearGroup.coe_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' x y := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_unipU, coe_unipU, coe_unipU]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

@[expose] def unipBar (F : Type) [Field F] :
    Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
  ((QuotientGroup.mk' (center (Matrix.SpecialLinearGroup (Fin 2) F))).comp (unipHom F)).range

@[expose] def diagTwo (z : Fˣ) : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![(z : F), 0; 0, ((z⁻¹ : Fˣ) : F)], by
    rw [Matrix.det_fin_two_of]
    simp⟩

theorem coe_diagTwo (z : Fˣ) : ((diagTwo z : Matrix.SpecialLinearGroup (Fin 2) F) :
    Matrix (Fin 2) (Fin 2) F) = !![(z : F), 0; 0, ((z⁻¹ : Fˣ) : F)] := rfl

theorem diagTwo_conj_unipU (z : Fˣ) (x : F) :
    diagTwo z * unipU x * (diagTwo z)⁻¹ = unipU ((z : F) * z * x) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, coe_diagTwo, coe_unipU, coe_unipU]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two]
  ring

theorem diagTwo_mul (a b : Fˣ) : diagTwo a * diagTwo b = (diagTwo (a * b) :
    Matrix.SpecialLinearGroup (Fin 2) F) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_diagTwo, coe_diagTwo, coe_diagTwo]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem diagTwo_one : (diagTwo 1 : Matrix.SpecialLinearGroup (Fin 2) F) = 1 := by
  apply Subtype.ext
  rw [coe_diagTwo, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem diagTwo_pow (a : Fˣ) (n : ℕ) :
    (diagTwo a : Matrix.SpecialLinearGroup (Fin 2) F) ^ n = diagTwo (a ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, diagTwo_one]
  | succ n ih => rw [pow_succ, ih, diagTwo_mul, pow_succ]

theorem diagTwo_inv (a : Fˣ) :
    (diagTwo a : Matrix.SpecialLinearGroup (Fin 2) F)⁻¹ = diagTwo a⁻¹ := by
  rw [inv_eq_iff_mul_eq_one, diagTwo_mul, mul_inv_cancel, diagTwo_one]

theorem unipHom_apply (x : Multiplicative F) : unipHom F x = unipU x.toAdd := rfl

theorem injective_unipBar :
    Function.Injective ((QuotientGroup.mk' (center (Matrix.SpecialLinearGroup (Fin 2) F))).comp
      (unipHom F)) := by
  intro x y h
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq, ← map_inv, ← map_mul] at h
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp h
  have e := congrFun (congrFun hr 0) 1
  rw [unipHom_apply, coe_unipU, Matrix.scalar_apply, Matrix.diagonal_apply_ne _ (by decide)] at e
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, toAdd_mul, toAdd_inv] at e
  have : y.toAdd = x.toAdd := by linear_combination -e
  exact Multiplicative.toAdd.injective this.symm

theorem card_unipBar [Finite F] : Nat.card (unipBar F) = Nat.card F := by
  rw [unipBar, ← Nat.card_congr (MonoidHom.ofInjective injective_unipBar).toEquiv]
  rfl

theorem diagTwo_mem_normalizer (z : Fˣ) :
    (QuotientGroup.mk (diagTwo z) : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) ∈
      normalizer ((unipBar F : Subgroup _) : Set _) := by
  have hconj : ∀ w : Fˣ, ∀ x : Multiplicative F,
      (QuotientGroup.mk (diagTwo w) : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) *
        QuotientGroup.mk (unipHom F x) * (QuotientGroup.mk (diagTwo w))⁻¹ ∈ unipBar F := by
    intro w x
    refine ⟨Multiplicative.ofAdd ((w : F) * w * x.toAdd), ?_⟩
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, ← QuotientGroup.mk_inv,
      ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, unipHom_apply, unipHom_apply,
      diagTwo_conj_unipU]
    rfl
  rw [mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨x, rfl⟩
    exact hconj z x
  · rintro ⟨x, hx⟩
    have h1 := hconj z⁻¹ x
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply] at hx
    rw [hx, ← QuotientGroup.mk_inv, diagTwo_inv] at h1
    have hDD : (QuotientGroup.mk (diagTwo z⁻¹) : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) *
        QuotientGroup.mk (diagTwo z) = 1 := by
      rw [← QuotientGroup.mk_mul, diagTwo_mul, inv_mul_cancel, diagTwo_one, QuotientGroup.mk_one]
    rw [inv_eq_of_mul_eq_one_right hDD] at h1
    have e : (QuotientGroup.mk (diagTwo z⁻¹) : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) *
        (QuotientGroup.mk (diagTwo z) * h * QuotientGroup.mk (diagTwo z⁻¹)) *
          QuotientGroup.mk (diagTwo z) = h := by
      calc _ = (QuotientGroup.mk (diagTwo z⁻¹) * QuotientGroup.mk (diagTwo z)) * h *
            (QuotientGroup.mk (diagTwo z⁻¹) * QuotientGroup.mk (diagTwo z)) := by group
        _ = h := by rw [hDD, one_mul, mul_one]
    rwa [e] at h1

theorem orderOf_tbar {ζ : Fˣ} (hζ : orderOf ζ = 8) :
    orderOf (QuotientGroup.mk (diagTwo ζ) : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) =
      4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hne4 : ζ ^ 4 ≠ 1 := by
    intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hζ] at this
    norm_num at this
  have h4 : ((ζ ^ 4 : Fˣ) : F) = -1 := by
    have hsq : ((ζ ^ 4 : Fˣ) : F) * ((ζ ^ 4 : Fˣ) : F) = 1 := by
      rw [← Units.val_mul, ← pow_add, show 4 + 4 = 8 from rfl, ← hζ, pow_orderOf_eq_one,
        Units.val_one]
    rcases mul_self_eq_one_iff.mp hsq with h | h
    · exact absurd (Units.ext (by rw [h, Units.val_one])) hne4
    · exact h
  have hcen4 : diagTwo (ζ ^ 4) ∈ center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    rw [Matrix.SpecialLinearGroup.mem_center_iff]
    refine ⟨-1, by norm_num, ?_⟩
    rw [coe_diagTwo, Units.val_inv_eq_inv_val, h4]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply]
  rw [show (4 : ℕ) = 2 ^ (1 + 1) from rfl]
  apply orderOf_eq_prime_pow
  · rw [pow_one, ← QuotientGroup.mk_pow, diagTwo_pow, QuotientGroup.eq_one_iff]
    intro hc
    obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
    have e0 := congrFun (congrFun hr 0) 0
    have e1 := congrFun (congrFun hr 1) 1
    simp [coe_diagTwo, Matrix.scalar_apply] at e0 e1
    apply hne4
    apply Units.ext
    have h1 : (ζ : F) ^ 2 = ((ζ : F) ^ 2)⁻¹ := e0.symm.trans e1
    have hz : (ζ : F) ^ 2 ≠ 0 := pow_ne_zero _ ζ.ne_zero
    rw [Units.val_pow_eq_pow_val, Units.val_one, show (4 : ℕ) = 2 + 2 from rfl, pow_add]
    calc (ζ : F) ^ 2 * (ζ : F) ^ 2 = ((ζ : F) ^ 2)⁻¹ * (ζ : F) ^ 2 := by rw [← h1]
      _ = 1 := inv_mul_cancel₀ hz
  · rw [← QuotientGroup.mk_pow, diagTwo_pow, QuotientGroup.eq_one_iff]
    exact hcen4

theorem map_mem_normalizer {A B : Type*} [Group A] [Group B] (ι : A →* B)
    {R : Subgroup A} {y : A} (hy : y ∈ normalizer (R : Set A)) :
    ι y ∈ normalizer ((R.map ι : Subgroup B) : Set B) := by
  rw [mem_normalizer_iff]
  intro b
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact ⟨y * r * y⁻¹, (mem_normalizer_iff.mp hy r).mp hr, by rw [map_mul, map_mul, map_inv]⟩
  · rintro ⟨r, hr, hrb⟩
    refine ⟨y⁻¹ * r * y, ?_, ?_⟩
    · have := (mem_normalizer_iff.mp (inv_mem hy) r).mp hr
      rwa [inv_inv] at this
    · rw [map_mul, map_mul, map_inv, hrb]
      group

variable {H : Type} [Group H] [Finite H]

theorem l316Row : L316Row := by
  intro H _ _ c hG
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hcard : Nat.card ↥(generalizedFitting H) = 1425715200 := by
    rw [card_of_lieModel_PSL (by norm_num) hG]
    decide
  have h125 : ¬ 125 ∣ Nat.card ↥(generalizedFitting H) := by rw [hcard]; decide
  have hq := ordL2sq_dvd_L316 c.five_le c.odd_q (hcard ▸ c.ordL2sq_dvd)
  have hp3 : 3 ≤ c.p := by have := c.prime.two_le; have := c.ne_two; omega
  have hf1 : c.f = 1 := by
    by_contra hne
    have : 3 ^ 2 ≤ c.p ^ c.f :=
      (Nat.pow_le_pow_left hp3 2).trans (Nat.pow_le_pow_right (by omega) (by
        have := c.one_le; omega))
    omega
  have hp5 : c.p = 5 := by rw [← hq, hf1, pow_one]
  obtain ⟨-, F', _, _, hF', ⟨φ'⟩⟩ := OddClassSelector.statedClassicalModel_of_lieModel_psl hG
  have : Fintype F' := Fintype.ofFinite F'
  have hF'16 : Fintype.card F' = 16 := by rw [← Nat.card_eq_fintype_card, hF']; norm_num
  let θ : ↥(generalizedFitting H) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) F' :=
    φ'.trans (Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 F').symm
  have hK := c.type_K
  rw [hf1, hp5] at hK
  obtain ⟨-, -, -, -, F, _, _, hF, ⟨eK⟩⟩ := AutL2Facts.lieModel_psl2_data hK
  have hF25 : Nat.card F = 25 := by rw [hF]; norm_num
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨ζ, hζ⟩ : ∃ ζ : Fˣ, orderOf ζ = 8 := by
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
    have hU : Nat.card Fˣ = 24 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hF25]
    refine ⟨g ^ 3, ?_⟩
    rw [orderOf_pow_of_dvd (by norm_num) (by rw [hg, hU]; norm_num), hg, hU]
  set φ : ↥c.K →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F :=
    eK.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 ↥c.K)) with hφ
  have hφs : Function.Surjective φ := eK.surjective.comp (QuotientGroup.mk'_surjective _)
  set U := unipBar F with hUdef
  set tb : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F := QuotientGroup.mk (diagTwo ζ)
    with htbdef
  have htb : tb ∈ normalizer (U : Set _) := diagTwo_mem_normalizer ζ
  have htb4 : orderOf tb = 4 := orderOf_tbar hζ
  have hU25 : Nat.card U = 25 := by rw [hUdef, card_unipBar, hF25]
  set D := (normalizer (U : Set _)).comap φ with hD
  set N := U.comap φ with hN
  have hND : N ≤ D := fun x hx => le_normalizer hx
  set N' := N.subgroupOf D with hN'
  have hN'n : N'.Normal := by
    refine ⟨fun n hn d => ?_⟩
    rw [hN', mem_subgroupOf] at hn ⊢
    change φ (d * n * d⁻¹ : ↥D) ∈ U
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_mul, map_inv]
    exact (mem_normalizer_iff.mp d.2 _).mp hn
  obtain ⟨P⟩ : Nonempty (Sylow 5 ↥N') := inferInstance
  have hFr := Sylow.normalizer_sup_eq_top P
  obtain ⟨k, hk⟩ := hφs tb
  have hkD : k ∈ D := by
    rw [hD, mem_comap, hk]
    exact htb
  have hmem : (⟨k, hkD⟩ : ↥D) ∈
      normalizer ((P.map N'.subtype : Subgroup ↥D) : Set ↥D) ⊔ N' := by
    rw [hFr]
    exact mem_top _
  obtain ⟨y, hy, z, hz, hyz⟩ := mem_sup_of_normal_right.mp hmem
  have hzU : φ (z : ↥c.K) ∈ U := by
    rw [hN', mem_subgroupOf] at hz
    exact hz
  have hφy : φ (y : ↥c.K) = tb * (φ (z : ↥c.K))⁻¹ := by
    have := congrArg (fun d : ↥D => φ (d : ↥c.K)) hyz
    simp only [Subgroup.coe_mul, map_mul] at this
    rw [← hk, ← this]
    group
  have h4 : 4 ∣ orderOf (φ (y : ↥c.K)) := by
    rw [hφy]
    exact four_dvd_orderOf_mul htb (by rw [hU25]; decide) htb4 (inv_mem hzU)
  have h4y : 4 ∣ orderOf y := by
    have := h4.trans (orderOf_map_dvd φ (y : ↥c.K))
    rwa [Subgroup.orderOf_coe] at this
  set ι : ↥D →* ↥(generalizedFitting H) :=
    (c.K.subtype.comp D.subtype).codRestrict (generalizedFitting H)
      (fun d => c.K_le_G (d : ↥c.K).2) with hι
  have hιi : Function.Injective ι := fun a b h =>
    Subtype.ext (Subtype.ext (congrArg (fun x : ↥(generalizedFitting H) => (x : H)) h))
  set Q := (P.map N'.subtype).map ι with hQ
  have hQcard : Nat.card Q = Nat.card P := by
    rw [hQ, Subgroup.card_map_of_injective hιi,
      Subgroup.card_map_of_injective N'.subtype_injective]
  have h25P : 25 ∣ Nat.card P := by
    have hN25 : 5 ^ 2 ∣ Nat.card ↥N' := by
      have hsurj : Function.Surjective ((φ.comp N.subtype).codRestrict U (fun x => x.2)) := by
        intro u
        obtain ⟨k', hk'⟩ := hφs u
        exact ⟨⟨k', show φ k' ∈ U by rw [hk']; exact u.2⟩, Subtype.ext hk'⟩
      have h1 := Subgroup.card_dvd_of_surjective hsurj
      rw [hU25] at h1
      rw [hN', Nat.card_congr (subgroupOfEquivOfLe hND).toEquiv]
      simpa using h1
    simpa using P.pow_dvd_card_of_pow_dvd_card hN25
  have hQ25 : Nat.card Q = 25 := by
    have hQ5 : IsPGroup 5 Q := (P.2.map N'.subtype).map ι
    obtain ⟨j, hj⟩ := hQ5.exists_card_eq
    have hdvd : 5 ^ j ∣ Nat.card ↥(generalizedFitting H) := hj ▸ Subgroup.card_subgroup_dvd_card _
    have hj2 : j ≤ 2 := by
      by_contra hlt
      exact h125 ((Nat.pow_dvd_pow 5 (by omega : 3 ≤ j)).trans hdvd)
    rw [hQcard] at hj
    have h25 : 25 ≤ 5 ^ j := hj ▸ Nat.le_of_dvd Nat.card_pos h25P
    have hj2' : 2 ≤ j := by
      by_contra hlt
      have : 5 ^ j ≤ 5 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    rw [hQcard, hj, show j = 2 by omega]
    norm_num
  have h90 := pow_ninety_of_mem_normalizer hF'16 θ h125 hQ25 (map_mem_normalizer ι hy)
  rw [← map_pow] at h90
  have hy90 : y ^ 90 = 1 := hιi (h90.trans (map_one ι).symm)
  have := h4y.trans (orderOf_dvd_of_pow_eq_one hy90)
  norm_num at this

end Catalog7Std

end CFSG.ComponentClassification.GSThmB
