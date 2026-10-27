module

public import CFSG.GH74.GLS.Classes
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvAltInv
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.LieType.Ree.SuzukiOrder
public import CFSG.Timmesfeld.Orders.ClassicalLinear
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix

public section

namespace CFSG.GH74.Generic.S1.Exo

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74 CFSG.GH74.GLS Subgroup
open scoped MatrixGroups

theorem nb_false_of_alt_cover {K : Type} [Group K] [Finite K] {n : ℕ} (hn : n ≤ 11)
    (e : K ⧸ center K ≃* alternatingGroup (Fin n)) {J : Subgroup K} (hJ : Group.IsPerfect ↥J)
    {y : K} (hy : y ∈ J) (hy2 : y * y = 1) (hyz : y ∉ center K)
    (hJy : ∀ b ∈ J, y * b = b * y) : False := by
  let φ : K →* Equiv.Perm (Fin n) :=
    (alternatingGroup (Fin n)).subtype.comp (e.toMonoidHom.comp (QuotientGroup.mk' (center K)))
  have hφ1 : ∀ k, φ k = 1 → k ∈ center K := by
    intro k hk
    have h1 : e (QuotientGroup.mk' (center K) k) = 1 := by
      apply Subtype.ext
      exact hk
    have h2 : QuotientGroup.mk' (center K) k = 1 := by
      simpa using e.injective (h1.trans (map_one e).symm)
    exact (QuotientGroup.eq_one_iff k).1 h2
  have hσ1 : φ y ≠ 1 := fun h => hyz (hφ1 y h)
  have hσ2 : φ y * φ y = 1 := by rw [← map_mul, hy2, map_one]
  have hsign : Equiv.Perm.sign (φ y) = 1 :=
    Equiv.Perm.mem_alternatingGroup.1 (e (QuotientGroup.mk' (center K) y)).2
  have : Group.IsPerfect ↥J := hJ
  have : Group.IsPerfect ↥(J.map φ) := Group.IsPerfect.map φ
  obtain ⟨hsup, hsg⟩ := CFSG.GH74.GLS.IVK.GHInv.involution_cycle_data hσ2
  have hle : (φ y).support.card ≤ n := (Finset.card_le_univ _).trans (by simp)
  have hc4 : (φ y).cycleType.card ≤ 4 := by
    have heven : Even (φ y).cycleType.card := by
      rw [hsg] at hsign
      by_contra hodd
      rw [Nat.not_even_iff_odd] at hodd
      rw [hodd.neg_one_pow] at hsign
      exact absurd hsign (by decide)
    obtain ⟨m, hm⟩ := heven
    omega
  have hcomm : ∀ x ∈ J.map φ, x * φ y = φ y * x := by
    rintro _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hJy b hb]
  have hfix := CFSG.GH74.GLS.IVK.GHInv.perfect_fixes_support hσ2 hc4
    (P := J.map φ) inferInstance hcomm
  apply hσ1
  refine Equiv.ext fun a => ?_
  by_contra hne
  have := hfix (φ y) ⟨y, hy, rfl⟩ a (fun h => hne (by simpa using h))
  exact hne (by simpa using this)

theorem nb_q_dvd_card_of_hasSL2Model {K : Type} [Group K] {q : ℕ}
    (hK : HasSL2Model K (fun r => r = q)) : q ∣ Nat.card K := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hK
  rw [Nat.card_congr (e.toEquiv.trans (specialLinearGroupEquivStatedSL 2 F).symm.toEquiv),
    CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, show Nat.card F = q from hF]
  exact dvd_mul_right _ _

theorem nb_sq_dvd_card_quotient {K : Type} [Group K] [Finite K] (hZ : IsPGroup 2 ↥(center K)) {q : ℕ}
    (hodd : Odd q) {J₂ J₄ : Subgroup K} (hcomm : ∀ a ∈ J₂, ∀ b ∈ J₄, a * b = b * a)
    (hinf : J₂ ⊓ J₄ = ⊥) (h₂ : HasSL2Model ↥J₂ (fun r => r = q))
    (h₄ : HasSL2Model ↥J₄ (fun r => r = q)) : q ^ 2 ∣ Nat.card (K ⧸ center K) := by
  let f : ↥J₂ × ↥J₄ →* K :=
    MonoidHom.noncommCoprod J₂.subtype J₄.subtype (fun a b => hcomm a a.2 b b.2)
  have hf : Function.Injective f := by
    refine (MonoidHom.noncommCoprod_injective _ _ _).2
      ⟨J₂.subtype_injective, J₄.subtype_injective, ?_⟩
    rw [Subgroup.range_subtype, Subgroup.range_subtype, disjoint_iff]
    exact hinf
  have h1 : Nat.card (↥J₂ × ↥J₄) ∣ Nat.card K := Subgroup.card_dvd_of_injective f hf
  rw [Nat.card_prod] at h1
  have h2 : q ^ 2 ∣ Nat.card ↥J₂ * Nat.card ↥J₄ := by
    rw [sq]
    exact mul_dvd_mul (nb_q_dvd_card_of_hasSL2Model h₂) (nb_q_dvd_card_of_hasSL2Model h₄)
  have h3 := h2.trans h1
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center K)] at h3
  obtain ⟨a, ha⟩ := hZ.exists_card_eq
  rw [ha] at h3
  exact (Nat.Coprime.pow 2 a (Nat.coprime_two_right.mpr hodd)).dvd_of_dvd_mul_right h3

theorem nb_sq_dvd_of_dvd_two_pow_mul {q a m : ℕ} (hodd : Odd q) (h : q ^ 2 ∣ 2 ^ a * m) :
    q ^ 2 ∣ m :=
  (Nat.Coprime.pow 2 a (Nat.coprime_two_right.mpr hodd)).dvd_of_dvd_mul_left h

theorem nb_not_sq_dvd {q m : ℕ} (hq : 5 ≤ q) (hm : m = 315 ∨ m = 455 ∨ m = 1485)
    (h : q ^ 2 ∣ m) : False := by
  have hle : q ≤ 38 := by
    have h1 := Nat.le_of_dvd (by rcases hm with rfl | rfl | rfl <;> norm_num) h
    have h2 : m ≤ 1485 := by rcases hm with rfl | rfl | rfl <;> norm_num
    by_contra hlt
    have h3 : 39 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  interval_cases q <;> rcases hm with rfl | rfl | rfl <;> omega

theorem nb_card_of_lieModel_psl_three_four {G : Type} [Group G] (h : LieModel G .PSL 3 2 2) :
    Nat.card G = 2 ^ 6 * 315 := by
  rcases h with ⟨-, -, K, _, _, hK, ⟨e⟩⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · rw [Nat.card_congr e.toEquiv,
      CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num), hK]
    decide
  all_goals exact absurd h0 (by norm_num)

theorem nb_card_of_lieModel_twistedB2 {G : Type} [Group G]
    (h : LieModel G .twistedB2 0 2 3) : Nat.card G = 2 ^ 6 * 455 := by
  rcases h with ⟨h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, -, -, a, ha, K, _, _, hf, hK, ⟨e⟩⟩
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · obtain rfl : a = 1 := by omega
    rw [Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order (by rw [hK, hf])]
    norm_num

theorem nb_false_of_M12_cover {K : Type} [Group K] [Finite K]
    (hZ : IsPGroup 2 ↥(center K)) (hM : NativeSporadic.IsSporadic (K ⧸ center K) .M12) {q : ℕ}
    (hq5 : 5 ≤ q) (hodd : Odd q) {J₂ J₄ : Subgroup K} (hcomm : ∀ a ∈ J₂, ∀ b ∈ J₄, a * b = b * a)
    (hinf : J₂ ⊓ J₄ = ⊥) (h₂ : HasSL2Model ↥J₂ (fun r => r = q))
    (h₄ : HasSL2Model ↥J₄ (fun r => r = q)) : False := by
  have hdvd := nb_sq_dvd_card_quotient hZ hodd hcomm hinf h₂ h₄
  have hcard : Nat.card (K ⧸ center K) = 2 ^ 6 * 1485 := by
    rw [Nat.card_congr hM.some.toEquiv]
    exact CFSG.Sporadic.Mathieu.card_M12.trans (by norm_num)
  rw [hcard] at hdvd
  exact nb_not_sq_dvd hq5 (Or.inr (Or.inr rfl)) (nb_sq_dvd_of_dvd_two_pow_mul hodd hdvd)

theorem nb_false_of_Sz8_cover {K : Type} [Group K] [Finite K]
    (hZ : IsPGroup 2 ↥(center K)) (hM : LieModel (K ⧸ center K) .twistedB2 0 2 3) {q : ℕ}
    (hq5 : 5 ≤ q) (hodd : Odd q) {J₂ J₄ : Subgroup K} (hcomm : ∀ a ∈ J₂, ∀ b ∈ J₄, a * b = b * a)
    (hinf : J₂ ⊓ J₄ = ⊥) (h₂ : HasSL2Model ↥J₂ (fun r => r = q))
    (h₄ : HasSL2Model ↥J₄ (fun r => r = q)) : False := by
  have hdvd := nb_sq_dvd_card_quotient hZ hodd hcomm hinf h₂ h₄
  rw [nb_card_of_lieModel_twistedB2 hM] at hdvd
  exact nb_not_sq_dvd hq5 (Or.inr (Or.inl rfl)) (nb_sq_dvd_of_dvd_two_pow_mul hodd hdvd)

theorem nb_false_of_L34_cover {K : Type} [Group K] [Finite K] (hZ : IsPGroup 2 ↥(center K))
    (hM : IsL34Quotient K) {q : ℕ} (hq5 : 5 ≤ q) (hodd : Odd q) {J₂ J₄ : Subgroup K}
    (hcomm : ∀ a ∈ J₂, ∀ b ∈ J₄, a * b = b * a) (hinf : J₂ ⊓ J₄ = ⊥)
    (h₂ : HasSL2Model ↥J₂ (fun r => r = q)) (h₄ : HasSL2Model ↥J₄ (fun r => r = q)) : False := by
  have hdvd := nb_sq_dvd_card_quotient hZ hodd hcomm hinf h₂ h₄
  rw [nb_card_of_lieModel_psl_three_four hM] at hdvd
  exact nb_not_sq_dvd hq5 (Or.inl rfl) (nb_sq_dvd_of_dvd_two_pow_mul hodd hdvd)

theorem nb_two_ne_zero_of_odd_card {F : Type*} [Field F] [Finite F] (hodd : Odd (Nat.card F)) :
    (2 : F) ≠ 0 := by
  have := Fintype.ofFinite F
  have hF : ringChar F ≠ 2 := fun h => by
    have h1 := FiniteField.even_card_of_char_two h
    rw [Nat.card_eq_fintype_card] at hodd
    have h2 := Nat.odd_iff.1 hodd
    omega
  exact Ring.two_ne_zero hF

theorem nb_sl2_sq_eq_one {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) {A : SL(2, F)} (hA : A * A = 1) :
    A = 1 ∨ A = -1 := by
  have hinv : A⁻¹ = A := inv_eq_of_mul_eq_one_right hA
  have hmat : (A : Matrix (Fin 2) (Fin 2) F) = Matrix.adjugate (A : Matrix (Fin 2) (Fin 2) F) := by
    rw [← Matrix.SpecialLinearGroup.coe_inv, hinv]
  rw [Matrix.adjugate_fin_two] at hmat
  have hdet := A.2
  rw [Matrix.det_fin_two] at hdet
  have h00 := congrFun (congrFun hmat 0) 0
  have h01 := congrFun (congrFun hmat 0) 1
  have h10 := congrFun (congrFun hmat 1) 0
  simp at h00 h01 h10
  have hb : (A : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by
    have : (2 : F) * (A : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by linear_combination h01
    exact (mul_eq_zero.1 this).resolve_left h2
  have hc : (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
    have : (2 : F) * (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by linear_combination h10
    exact (mul_eq_zero.1 this).resolve_left h2
  have ha2 : (A : Matrix (Fin 2) (Fin 2) F) 0 0 * (A : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by
    rw [hb, hc] at hdet
    rw [← h00] at hdet
    linear_combination hdet
  have h11 : (A : Matrix (Fin 2) (Fin 2) F) 1 1 = (A : Matrix (Fin 2) (Fin 2) F) 0 0 := h00.symm
  rcases mul_self_eq_one_iff.1 ha2 with ha | ha
  · left
    refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, h11]
  · right
    refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, h11]

theorem nb_false_of_sl2_model {K : Type} [Group K] (hK : HasSL2Model K Odd) {w y : K}
    (hw : w * w = 1) (hy : y * y = 1) (hw1 : w ≠ 1) (hy1 : y ≠ 1) (hwy : w ≠ y) : False := by
  obtain ⟨F, _, _, hodd, ⟨e⟩⟩ := hK
  have h2 : (2 : F) ≠ 0 := nb_two_ne_zero_of_odd_card hodd
  let e' : K ≃* SL(2, F) := e.trans (specialLinearGroupEquivStatedSL 2 F).symm
  have hw' : e' w * e' w = 1 := by rw [← map_mul, hw, map_one]
  have hy' : e' y * e' y = 1 := by rw [← map_mul, hy, map_one]
  rcases nb_sl2_sq_eq_one h2 hw' with h | h
  · exact hw1 (e'.injective (h.trans (map_one e').symm))
  rcases nb_sl2_sq_eq_one h2 hy' with h' | h'
  · exact hy1 (e'.injective (h'.trans (map_one e').symm))
  exact hwy (e'.injective (h.trans h'.symm))

end CFSG.GH74.Generic.S1.Exo
