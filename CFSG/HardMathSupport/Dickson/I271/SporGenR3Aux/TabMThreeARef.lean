module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterTwoBGmat
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMThreeABaby
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMThreeALeech
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMThreeAType

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Dickson.I271.TabMThreeA

open CFSG.Monster CFSG.Monster.Generated CFSG.Monster.Griess CFSG.Monster.GMS
  CFSG.Monster.Existence CFSG.YGroups CFSG.YGroups.Y443 CFSG.Open

namespace Ref

section Elementary

variable {G : Type*} [Group G]

theorem closure_comm {S : Set G} (h : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) :
    ∀ x ∈ Subgroup.closure S, ∀ y ∈ Subgroup.closure S, x * y = y * x := by
  letI : CommGroup ↥(Subgroup.closure S) :=
    Subgroup.closureCommGroupOfComm fun x hx y hy _ => h x hx y hy
  intro x hx y hy
  exact congrArg Subtype.val (mul_comm (⟨x, hx⟩ : ↥(Subgroup.closure S)) ⟨y, hy⟩)

theorem closure_mul_self {S : Set G} (h : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x)
    (hS : ∀ x ∈ S, x * x = 1) : ∀ x ∈ Subgroup.closure S, x * x = 1 := by
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact hS x hx
  | one => simp
  | mul x y hx hy hx' hy' =>
    have hc := closure_comm h x hx y hy
    calc x * y * (x * y) = x * (y * x) * y := by simp only [mul_assoc]
      _ = x * (x * y) * y := by rw [hc]
      _ = x * x * (y * y) := by simp only [mul_assoc]
      _ = 1 := by rw [hx', hy', mul_one]
  | inv x hx hx' =>
    rw [← mul_inv_rev, hx', inv_one]

theorem four_comm {a b c d : G} (hab : a * b = b * a) (hac : a * c = c * a)
    (had : a * d = d * a) (hbc : b * c = c * b) (hbd : b * d = d * b) (hcd : c * d = d * c) :
    ∀ x ∈ ({a, b, c, d} : Set G), ∀ y ∈ ({a, b, c, d} : Set G), x * y = y * x := by
  rintro x (rfl | rfl | rfl | rfl) y (rfl | rfl | rfl | rfl) <;>
    first | rfl | exact hab | exact hac | exact had | exact hbc | exact hbd | exact hcd |
      exact hab.symm | exact hac.symm | exact had.symm | exact hbc.symm | exact hbd.symm |
      exact hcd.symm

end Elementary

theorem injective_pow_triple {C : Type*} [CommGroup C] {u v w : C}
    (hu : u ^ 2 = 1) (hv : v ^ 2 = 1) (hw : w ^ 2 = 1)
    (h1 : u ≠ 1) (h2 : v ≠ 1) (h3 : w ≠ 1)
    (h12 : u * v ≠ 1) (h13 : u * w ≠ 1) (h23 : v * w ≠ 1) (h123 : u * v * w ≠ 1) :
    Function.Injective fun p : Fin 2 × Fin 2 × Fin 2 =>
      u ^ (p.1 : ℕ) * v ^ (p.2.1 : ℕ) * w ^ (p.2.2 : ℕ) := by
  have hsq : ∀ (x : C) (n : ℕ), x ^ 2 = 1 → x ^ n * x ^ n = 1 := by
    intro x n hx
    rw [← sq, pow_right_comm, hx, one_pow]
  rintro ⟨⟨i, hi⟩, ⟨j, hj⟩, ⟨k, hk⟩⟩ ⟨⟨i', hi'⟩, ⟨j', hj'⟩, ⟨k', hk'⟩⟩ h
  simp only at h
  have hq : (u ^ i' * v ^ j' * w ^ k') * (u ^ i' * v ^ j' * w ^ k') = 1 := by
    calc (u ^ i' * v ^ j' * w ^ k') * (u ^ i' * v ^ j' * w ^ k')
        = (u ^ i' * u ^ i') * (v ^ j' * v ^ j') * (w ^ k' * w ^ k') := by ac_rfl
      _ = 1 := by rw [hsq u i' hu, hsq v j' hv, hsq w k' hw]; simp
  have hp : u ^ (i + i') * v ^ (j + j') * w ^ (k + k') = 1 := by
    calc u ^ (i + i') * v ^ (j + j') * w ^ (k + k')
        = (u ^ i * v ^ j * w ^ k) * (u ^ i' * v ^ j' * w ^ k') := by
          rw [pow_add, pow_add, pow_add]; ac_rfl
      _ = (u ^ i' * v ^ j' * w ^ k') * (u ^ i' * v ^ j' * w ^ k') := by rw [h]
      _ = 1 := hq
  interval_cases i <;> interval_cases j <;> interval_cases k <;>
    interval_cases i' <;> interval_cases j' <;> interval_cases k' <;>
    first | rfl | (simp [hu, hv, hw, h1, h2, h3, h12, h13, h23, h123] at hp)

theorem injective_prod_pairs {C : Type*} [CommGroup C] {a b c d : C}
    (ha : a * a = 1) (hb : b * b = 1) (hc : c * c = 1) (hd : d * d = 1)
    (h1 : a * b ≠ 1) (h2 : a * c ≠ 1) (h3 : a * d ≠ 1) (h4 : b * c ≠ 1) (h5 : b * d ≠ 1)
    (h6 : c * d ≠ 1) (h7 : a * (b * (c * d)) ≠ 1) :
    Function.Injective fun p : Fin 2 × Fin 2 × Fin 2 =>
      (a * b) ^ (p.1 : ℕ) * (a * c) ^ (p.2.1 : ℕ) * (a * d) ^ (p.2.2 : ℕ) := by
  have sq1 : ∀ x y : C, x * x = 1 → y * y = 1 → (x * y) ^ 2 = 1 := by
    intro x y hx hy
    rw [mul_pow, sq, sq, hx, hy, mul_one]
  have e2 : ∀ x y z : C, x * x = 1 → (x * y) * (x * z) = y * z := by
    intro x y z hx
    calc x * y * (x * z) = (x * x) * (y * z) := by ac_rfl
      _ = y * z := by rw [hx, one_mul]
  refine injective_pow_triple (sq1 a b ha hb) (sq1 a c ha hc) (sq1 a d ha hd) h1 h2 h3 ?_ ?_ ?_ ?_
  · rw [e2 a b c ha]
    exact h4
  · rw [e2 a b d ha]
    exact h5
  · rw [e2 a c d ha]
    exact h6
  · have : a * b * (a * c) * (a * d) = a * (b * (c * d)) := by
      calc a * b * (a * c) * (a * d) = (a * a) * (a * (b * (c * d))) := by ac_rfl
        _ = a * (b * (c * d)) := by rw [ha, one_mul]
    rw [this]
    exact h7

theorem eight_le_card_closure {G : Type*} [Group G] [Finite G] {a b c d : G}
    (ha : a * a = 1) (hb : b * b = 1) (hc : c * c = 1) (hd : d * d = 1)
    (hab : a * b = b * a) (hac : a * c = c * a) (had : a * d = d * a)
    (hbc : b * c = c * b) (hbd : b * d = d * b) (hcd : c * d = d * c)
    (h1 : a * b ≠ 1) (h2 : a * c ≠ 1) (h3 : a * d ≠ 1) (h4 : b * c ≠ 1) (h5 : b * d ≠ 1)
    (h6 : c * d ≠ 1) (h7 : a * (b * (c * d)) ≠ 1) :
    8 ≤ Nat.card ↥(Subgroup.closure ({a * b, a * c, a * d} : Set G)) := by
  set A := Subgroup.closure ({a * b, a * c, a * d} : Set G) with hA
  set D := Subgroup.closure ({a, b, c, d} : Set G) with hD
  letI : CommGroup ↥D :=
    Subgroup.closureCommGroupOfComm fun x hx y hy _ => four_comm hab hac had hbc hbd hcd x hx y hy
  have haD : a ∈ D := Subgroup.subset_closure (by simp)
  have hbD : b ∈ D := Subgroup.subset_closure (by simp)
  have hcD : c ∈ D := Subgroup.subset_closure (by simp)
  have hdD : d ∈ D := Subgroup.subset_closure (by simp)
  have hinj := injective_prod_pairs (C := ↥D) (a := ⟨a, haD⟩) (b := ⟨b, hbD⟩) (c := ⟨c, hcD⟩)
    (d := ⟨d, hdD⟩) (Subtype.ext ha) (Subtype.ext hb) (Subtype.ext hc) (Subtype.ext hd)
    (fun h => h1 (congrArg Subtype.val h)) (fun h => h2 (congrArg Subtype.val h))
    (fun h => h3 (congrArg Subtype.val h)) (fun h => h4 (congrArg Subtype.val h))
    (fun h => h5 (congrArg Subtype.val h)) (fun h => h6 (congrArg Subtype.val h))
    (fun h => h7 (congrArg Subtype.val h))
  have hu : a * b ∈ A := Subgroup.subset_closure (by simp)
  have hv : a * c ∈ A := Subgroup.subset_closure (by simp)
  have hw : a * d ∈ A := Subgroup.subset_closure (by simp)
  let g : Fin 2 × Fin 2 × Fin 2 → ↥A := fun p =>
    ⟨(a * b) ^ (p.1 : ℕ) * (a * c) ^ (p.2.1 : ℕ) * (a * d) ^ (p.2.2 : ℕ),
      A.mul_mem (A.mul_mem (A.pow_mem hu _) (A.pow_mem hv _)) (A.pow_mem hw _)⟩
  have hg : Function.Injective g := by
    intro p q hpq
    apply hinj
    exact Subtype.ext (congrArg (fun x : ↥A => (x : G)) hpq)
  have h := Nat.card_le_card_of_injective g hg
  have h8 : Nat.card (Fin 2 × Fin 2 × Fin 2) = 8 := by
    rw [Nat.card_eq_fintype_card]
    rfl
  omega

theorem elementary_abelian_eight {G : Type*} [Group G] [Finite G] {a b c d : G}
    (ha : a * a = 1) (hb : b * b = 1) (hc : c * c = 1) (hd : d * d = 1)
    (hab : a * b = b * a) (hac : a * c = c * a) (had : a * d = d * a)
    (hbc : b * c = c * b) (hbd : b * d = d * b) (hcd : c * d = d * c)
    (h1 : a * b ≠ 1) (h2 : a * c ≠ 1) (h3 : a * d ≠ 1) (h4 : b * c ≠ 1) (h5 : b * d ≠ 1)
    (h6 : c * d ≠ 1) (h7 : a * (b * (c * d)) ≠ 1) :
    (∀ x ∈ Subgroup.closure ({a * b, a * c, a * d} : Set G),
      ∀ y ∈ Subgroup.closure ({a * b, a * c, a * d} : Set G), x * y = y * x) ∧
    (∀ x ∈ Subgroup.closure ({a * b, a * c, a * d} : Set G), x ^ 2 = 1) ∧
    8 ≤ Nat.card ↥(Subgroup.closure ({a * b, a * c, a * d} : Set G)) := by
  have hS := four_comm hab hac had hbc hbd hcd
  have hS2 : ∀ x ∈ ({a, b, c, d} : Set G), x * x = 1 := by
    rintro x (rfl | rfl | rfl | rfl)
    exacts [ha, hb, hc, hd]
  have haD : a ∈ Subgroup.closure ({a, b, c, d} : Set G) := Subgroup.subset_closure (by simp)
  have hbD : b ∈ Subgroup.closure ({a, b, c, d} : Set G) := Subgroup.subset_closure (by simp)
  have hcD : c ∈ Subgroup.closure ({a, b, c, d} : Set G) := Subgroup.subset_closure (by simp)
  have hdD : d ∈ Subgroup.closure ({a, b, c, d} : Set G) := Subgroup.subset_closure (by simp)
  have hAD : Subgroup.closure ({a * b, a * c, a * d} : Set G) ≤
      Subgroup.closure ({a, b, c, d} : Set G) := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl | rfl)
    exacts [mul_mem haD hbD, mul_mem haD hcD, mul_mem haD hdD]
  exact ⟨fun x hx y hy => closure_comm hS x (hAD hx) y (hAD hy),
    fun x hx => by rw [sq]; exact closure_mul_self hS hS2 x (hAD hx),
    eight_le_card_closure ha hb hc hd hab hac had hbc hbd hcd h1 h2 h3 h4 h5 h6 h7⟩

end Ref

@[expose] noncomputable def refT
    (hG : Gmat = AutO) (i : ℕ) : MGriess :=
  (griessEquivGmat hG).symm (fM (y443Tl i))

theorem symm_fM_C
    (hG : Gmat = AutO) : (griessEquivGmat hG).symm (fM y443C) = tGriess := by
  rw [MulEquiv.symm_apply_eq]
  exact (griessEquivGmat_tGriess hG).symm

theorem refT_mul_self
    (hG : Gmat = AutO) (i : ℕ) : refT hG i * refT hG i = 1 := by
  rw [refT, ← MulEquiv.map_mul, fM_tl_mul_self, map_one]

theorem refT_comm
    (hG : Gmat = AutO) {s t : ℕ} (hst : s < t) (ht : t < 12) (h : pairExp 4 4 3 s t = 2) :
    refT hG s * refT hG t = refT hG t * refT hG s := by
  rw [refT, refT, ← MulEquiv.map_mul, ← MulEquiv.map_mul, fM_tl_comm hst ht h]

theorem tGriess_mul_refT
    (hG : Gmat = AutO) {i : ℕ} (hi : i < 12) (hi4 : i ≠ 4) :
    tGriess * refT hG i = refT hG i * tGriess := by
  rw [← symm_fM_C hG, refT, ← MulEquiv.map_mul, ← MulEquiv.map_mul, fM_c_comm_tl hi hi4]

theorem fM_isConj_c_y' :
    IsConj (fM y443C) (fM y443Y) := by
  refine isConj_iff.2 ⟨fM y443S, ?_⟩
  rw [← map_inv, y443S_inv]
  exact fM_S_conj fM_cx_cube

theorem isConj_tGriess_refT_three
    (hG : Gmat = AutO) :
    IsConj tGriess (refT hG 3) ∧ IsConj tGriess (tGriess * refT hG 3) := by
  constructor
  · rw [← symm_fM_C hG, refT, ← y443Y_eq_Tl]
    exact MonoidHom.map_isConj (griessEquivGmat hG).symm.toMonoidHom fM_isConj_c_y'
  · rw [← symm_fM_C hG, refT, ← y443Y_eq_Tl, ← map_mul]
    exact MonoidHom.map_isConj (griessEquivGmat hG).symm.toMonoidHom fM_cy_conj

theorem tGriess_mem_twoANbr
    (hG : Gmat = AutO) : tGriess ∈ twoANbr tGriess (tGriess * refT hG 3) := by
  have hsq : tGriess * tGriess = 1 := by
    rw [← sq]
    have := pow_orderOf_eq_one tGriess
    rwa [orderOf_tGriess] at this
  have hc := tGriess_mul_refT hG (i := 3) (by norm_num) (by norm_num)
  have h : tGriess * refT hG 3 * tGriess = refT hG 3 := by
    rw [mul_assoc, ← hc, ← mul_assoc, hsq, one_mul]
  show IsConj tGriess tGriess ∧ IsConj tGriess (tGriess * refT hG 3 * tGriess)
  rw [h]
  exact ⟨IsConj.refl _, (isConj_tGriess_refT_three hG).1⟩

theorem not_isConj_of_twoA_of_twoB {t₁ t₂ : MGriess}
    (h₁ : IsConj tGriess t₁) (h₂ : IsConj xGriess t₂) : ¬ IsConj t₁ t₂ := fun h =>
  not_isConj_xGriess_tGriess (h₂.trans (h₁.trans h).symm)

section TwoB


theorem exists_twoB_refT (hG : Gmat = AutO)
    (hne : ∀ u ∈ ([[2, 6], [2, 8], [2, 10], [6, 8], [6, 10], [8, 10], [2, 6, 8, 10]] :
      List (List ℕ)), CFSG.Certificates.CosetEnumeration.evalWord (refT hG) u ≠ 1) :
    ∃ t ∈ Subgroup.closure ({refT hG 2 * refT hG 6, refT hG 2 * refT hG 8,
      refT hG 2 * refT hG 10} : Set MGriess), IsConj xGriess t := by
  have c26 := refT_comm hG (s := 2) (t := 6) (by norm_num) (by norm_num) (by decide)
  have c28 := refT_comm hG (s := 2) (t := 8) (by norm_num) (by norm_num) (by decide)
  have c2t := refT_comm hG (s := 2) (t := 10) (by norm_num) (by norm_num) (by decide)
  have c68 := refT_comm hG (s := 6) (t := 8) (by norm_num) (by norm_num) (by decide)
  have c6t := refT_comm hG (s := 6) (t := 10) (by norm_num) (by norm_num) (by decide)
  have c8t := refT_comm hG (s := 8) (t := 10) (by norm_num) (by norm_num) (by decide)
  have n1 : refT hG 2 * refT hG 6 ≠ 1 := by
    simpa [CFSG.Certificates.CosetEnumeration.evalWord] using hne [2, 6] (by simp)
  have n2 : refT hG 2 * refT hG 8 ≠ 1 := by
    simpa [CFSG.Certificates.CosetEnumeration.evalWord] using hne [2, 8] (by simp)
  have n3 : refT hG 2 * refT hG 10 ≠ 1 := by
    simpa [CFSG.Certificates.CosetEnumeration.evalWord] using hne [2, 10] (by simp)
  have n4 : refT hG 6 * refT hG 8 ≠ 1 := by
    simpa [CFSG.Certificates.CosetEnumeration.evalWord] using hne [6, 8] (by simp)
  have n5 : refT hG 6 * refT hG 10 ≠ 1 := by
    simpa [CFSG.Certificates.CosetEnumeration.evalWord] using hne [6, 10] (by simp)
  have n6 : refT hG 8 * refT hG 10 ≠ 1 := by
    simpa [CFSG.Certificates.CosetEnumeration.evalWord] using hne [8, 10] (by simp)
  have n7 : refT hG 2 * (refT hG 6 * (refT hG 8 * refT hG 10)) ≠ 1 := by
    simpa [CFSG.Certificates.CosetEnumeration.evalWord] using hne [2, 6, 8, 10] (by simp)
  obtain ⟨hAc, hAs, h8⟩ := Ref.elementary_abelian_eight (refT_mul_self hG 2) (refT_mul_self hG 6)
    (refT_mul_self hG 8) (refT_mul_self hG 10) c26 c28 c2t c68 c6t c8t n1 n2 n3 n4 n5 n6 n7
  set A : Subgroup MGriess := Subgroup.closure ({refT hG 2 * refT hG 6, refT hG 2 * refT hG 8,
    refT hG 2 * refT hG 10} : Set MGriess) with hA
  have hφc : ∀ a ∈ A.map (griessEquivGmat hG).toMonoidHom,
      ∀ b ∈ A.map (griessEquivGmat hG).toMonoidHom, a * b = b * a := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, ← map_mul, hAc x hx y hy]
  have hφs : ∀ a ∈ A.map (griessEquivGmat hG).toMonoidHom, a ^ 2 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, ← map_pow, hAs x hx, map_one]
  have hφ8 : 8 ≤ Nat.card (A.map (griessEquivGmat hG).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (griessEquivGmat hG).injective]
    exact h8
  obtain ⟨_, ⟨t, ht, rfl⟩, hu⟩ :=
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterTwoBGmat.exists_twoB_Gmat
      (A.map (griessEquivGmat hG).toMonoidHom) hφc hφs hφ8
  refine ⟨t, ht, ?_⟩
  have hx : IsConj xGmat (griessEquivGmat hG xGriess) :=
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterTwoBGmat.isConj_xGmat_of_twoB
      (griessEquivGmat hG) orderOf_xGriess (isTwoBCentralizer_MGriess xGriess (IsConj.refl _))
  have := MonoidHom.map_isConj (griessEquivGmat hG).symm.toMonoidHom (hx.symm.trans hu)
  simpa using this

end TwoB

section BabyBound


theorem card_inf_le_twoA (hB3 : TabBThreeACard) (hG : Gmat = AutO) {ζ : MGriess}
    (hζ3 : orderOf ζ = 3) (hζt : ζ * (tGriess * refT hG 3) = tGriess * refT hG 3 * ζ)
    (hinv : tGriess * ζ * tGriess⁻¹ = ζ⁻¹) :
    Nat.card ↥(Subgroup.centralizer ({ζ} : Set MGriess) ⊓
      Subgroup.centralizer ({tGriess * refT hG 3} : Set MGriess)) ≤ 3 * 258247006617600 := by
  rw [inf_comm]
  exact card_centralizer_inf_le_of_twoA_inv gmsInterfaces_MGriess gmsF1Type_MGriess_uncond hB3
    (isConj_tGriess_refT_three hG).2 (tGriess_mem_twoANbr hG) hζ3
    (Subgroup.mem_centralizer_singleton_iff.2 hζt) hinv

end BabyBound

section LeechBound


theorem card_inf_le_twoB {ζ t : MGriess} (hζ3 : orderOf ζ = 3)
    (hinv : tGriess * ζ * tGriess⁻¹ = ζ⁻¹)
    (h23 : 23 ∣ Nat.card ↥(Subgroup.centralizer ({tGriess} : Set MGriess) ⊓
      Subgroup.centralizer ({ζ} : Set MGriess)))
    (htc : t * tGriess = tGriess * t) (htζ : t * ζ = ζ * t) (htB : IsConj xGriess t) :
    Nat.card ↥(Subgroup.centralizer ({ζ} : Set MGriess) ⊓
      Subgroup.centralizer ({t} : Set MGriess)) ≤ 3 * 160526499840 := by
  have I := gmsInterfaces_MGriess
  have hG := gmsF1Type_MGriess_uncond
  have hex := oddExhaustive_MGriess I
  have hOT : OddTypeOrdersCF tGriess xGriess :=
    oddTypeOrdersCF_MGriess I hex monster_clauses_MGriess.1
      (natCard_cent_tGriess_of monster_clauses_MGriess.2.2)
      CFSG.Sporadic.Presentation.Th.finite_card_le CFSG.Monster.Existence.Compat.card_nativeTh
      exists_hn_two_point'
  have h1 : ¬ 23 ∣ oddTypeStab 1 := by norm_num [oddTypeStab]
  have h2 : ¬ 23 ∣ oddTypeStab 2 := by norm_num [oddTypeStab]
  obtain ⟨hnbr, hty, hαβ⟩ :=
    oddNbrType_zero_of_dvd I hG hex hOT (IsConj.refl tGriess) hζ3 hinv h23 h1 h2
  have hβ : ζ⁻¹ * tGriess ∈ typeSet tGriess xGriess tGriess .threeA := ⟨hnbr, hty⟩
  have ht : t ∈ Subgroup.centralizer ({tGriess} : Set MGriess) ⊓
      Subgroup.centralizer ({ζ⁻¹ * tGriess} : Set MGriess) :=
    ⟨Subgroup.mem_centralizer_singleton_iff.2 htc,
      Subgroup.mem_centralizer_singleton_iff.2
        ((Commute.inv_right (show Commute t ζ from htζ)).mul_right
          (show Commute t tGriess from htc)).eq⟩
  have h := card_centralizer_inf_le_of_threeA I hG (IsConj.refl tGriess) hβ ht htB
  rw [hαβ] at h
  rwa [inf_comm] at h

end LeechBound

end CFSG.HardMathSupport.Dickson.I271.TabMThreeA
