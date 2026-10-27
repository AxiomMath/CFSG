module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.C25Core
public import CFSG.Quasithin.Background.A3Structure313Core
public import CFSG.Quasithin.Background.A3Structure39Odd

public section

namespace CFSG.QuasithinUnique.A5.C25

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native

section SL2

variable {F : Type*} [Field F]

theorem sl2_eq_one_or_neg_one (h2 : (2 : F) ≠ 0) (A : Matrix.SpecialLinearGroup (Fin 2) F)
    (hA : A * A = 1) :
    (A : Matrix (Fin 2) (Fin 2) F) = 1 ∨ (A : Matrix (Fin 2) (Fin 2) F) = -1 := by
  have hA' : (A : Matrix (Fin 2) (Fin 2) F) * (A : Matrix (Fin 2) (Fin 2) F) = 1 := by
    simpa using congrArg (fun B : Matrix.SpecialLinearGroup (Fin 2) F =>
      (B : Matrix (Fin 2) (Fin 2) F)) hA
  have hdet : (A : Matrix (Fin 2) (Fin 2) F).det = 1 := A.2
  rw [Matrix.det_fin_two] at hdet
  have e00 : A 0 0 * A 0 0 + A 0 1 * A 1 0 = 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hA' 0) 0
  have e01 : A 0 0 * A 0 1 + A 0 1 * A 1 1 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hA' 0) 1
  have e10 : A 1 0 * A 0 0 + A 1 1 * A 1 0 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hA' 1) 0
  have e11 : A 1 0 * A 0 1 + A 1 1 * A 1 1 = 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hA' 1) 1
  by_cases hs : A 0 0 + A 1 1 = 0
  · exfalso
    apply h2
    linear_combination (A 0 0) * hs - e00 - hdet
  · have hb : A 0 1 = 0 := by
      have : A 0 1 * (A 0 0 + A 1 1) = 0 := by linear_combination e01
      exact (mul_eq_zero.1 this).resolve_right hs
    have hc : A 1 0 = 0 := by
      have : A 1 0 * (A 0 0 + A 1 1) = 0 := by linear_combination e10
      exact (mul_eq_zero.1 this).resolve_right hs
    have haa : A 0 0 * A 0 0 = 1 := by rw [hb, hc] at e00; simpa using e00
    have had : A 0 0 * A 1 1 = 1 := by rw [hb, hc] at hdet; simpa using hdet
    have ha0 : A 0 0 ≠ 0 := fun h => by rw [h] at haa; simp at haa
    have hd : A 1 1 = A 0 0 := by
      have : A 0 0 * (A 1 1 - A 0 0) = 0 := by linear_combination had - haa
      have := (mul_eq_zero.1 this).resolve_left ha0
      linear_combination this
    have hmat : (A : Matrix (Fin 2) (Fin 2) F) = Matrix.of ![![A 0 0, 0], ![0, A 0 0]] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hb, hc, hd]
    rcases mul_self_eq_one_iff.1 haa with h1 | h1
    · left
      rw [hmat, h1]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    · right
      rw [hmat, h1]
      ext i j
      fin_cases i <;> fin_cases j <;> simp

theorem sl2_two_involutions (h2 : (2 : F) ≠ 0) {A B : Matrix.SpecialLinearGroup (Fin 2) F}
    (hA : A * A = 1) (hB : B * B = 1) (hA1 : A ≠ 1) (hB1 : B ≠ 1) : A = B := by
  have hA' : (A : Matrix (Fin 2) (Fin 2) F) = -1 := by
    rcases sl2_eq_one_or_neg_one h2 A hA with h | h
    · exact absurd (Subtype.ext h) hA1
    · exact h
  have hB' : (B : Matrix (Fin 2) (Fin 2) F) = -1 := by
    rcases sl2_eq_one_or_neg_one h2 B hB with h | h
    · exact absurd (Subtype.ext h) hB1
    · exact h
  exact Subtype.ext (hA'.trans hB'.symm)

end SL2

section Generic

theorem false_of_sl2_image {X W : Type} [Group X] [Group W] [Finite W] {q : ℕ} [Fact q.Prime]
    (h2 : (2 : ZMod q) ≠ 0) (ψ : X →* Matrix.SpecialLinearGroup (Fin 2) (ZMod q))
    (hker : ∀ x, ψ x = 1 → Odd (orderOf x)) (ι : W →* X) (hι : Function.Injective ι)
    (hsq : ∀ w : W, w * w = 1) (hcard : 3 ≤ Nat.card W) : False := by
  have hinj : Function.Injective (ψ.comp ι) := by
    rw [injective_iff_map_eq_one]
    intro w hw
    have h1 : ψ (ι w) = 1 := hw
    have hodd := hker _ h1
    have hord : orderOf (ι w) ∣ 2 := orderOf_dvd_of_pow_eq_one (by
      rw [pow_two, ← map_mul, hsq, map_one])
    have hone : orderOf (ι w) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 hord with h | h
      · exact h
      · rw [h] at hodd
        exact absurd hodd (by decide)
    have : ι w = 1 := orderOf_eq_one_iff.1 hone
    exact hι (by rw [this, map_one])
  have : Fintype W := Fintype.ofFinite W
  have hW2 : 2 < Fintype.card W := by
    rw [← Nat.card_eq_fintype_card]
    omega
  obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.1 hW2
  have key : ∃ u v : W, u ≠ 1 ∧ v ≠ 1 ∧ u ≠ v := by
    by_cases ha : a = 1
    · exact ⟨b, c, fun h => hab (ha.trans h.symm), fun h => hac (ha.trans h.symm), hbc⟩
    · by_cases hb : b = 1
      · exact ⟨a, c, ha, fun h => hbc (hb.trans h.symm), hac⟩
      · exact ⟨a, b, ha, hb, hab⟩
  obtain ⟨u, v, hu, hv, huv⟩ := key
  have hne : ∀ w : W, w ≠ 1 → ψ (ι w) ≠ 1 := fun w hw h =>
    hw (hinj (by simpa using h))
  have hsq' : ∀ w : W, ψ (ι w) * ψ (ι w) = 1 := fun w => by
    rw [← map_mul, ← map_mul, hsq, map_one, map_one]
  exact huv (hinj (sl2_two_involutions h2 (hsq' u) (hsq' v) (hne u hu) (hne v hv)))

end Generic

section Main

variable {G : Type} [Group G] [Finite G] {Gi L SI U : Subgroup G}

noncomputable def iotaU (S : Setting Gi L SI U) {K : Subgroup G} (hLK : L ≤ K) :
    ↥U →* ↥(modO2Image Gi K) :=
  ((QuotientGroup.mk' (CFSG.pCore 2 ↥Gi)).comp
    (Subgroup.inclusion ((U_le_L S).trans S.L_le))).codRestrict (modO2Image Gi K) (fun u =>
      ⟨Subgroup.inclusion ((U_le_L S).trans S.L_le) u, ((U_le_L S).trans hLK) u.2, rfl⟩)

omit [Finite G] in
theorem iotaU_injective (S : Setting Gi L SI U) {K : Subgroup G} (hLK : L ≤ K) :
    Function.Injective (iotaU S hLK) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [injective_iff_map_eq_one]
  intro u hu
  set x : ↥Gi := Subgroup.inclusion ((U_le_L S).trans S.L_le) u with hx
  have h1 : (QuotientGroup.mk' (CFSG.pCore 2 ↥Gi)) x = 1 := congrArg Subtype.val hu
  have h2 : (x : G) ∈ pCoreOf 2 Gi :=
    ⟨x, by exact (QuotientGroup.eq_one_iff x).1 h1, rfl⟩
  have h3 : (u : G) ∈ U ⊓ pCoreOf 2 Gi := ⟨u.2, h2⟩
  rw [S.U_inf, Subgroup.mem_bot] at h3
  exact Subtype.ext h3

theorem no_sl2_quotient (S : Setting Gi L SI U) {K : Subgroup G} (hLK : L ≤ K) {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2)
    (hSL : IsSL2 q (↥(modO2Image Gi K) ⧸ CFSG.oddCore ↥(modO2Image Gi K))) : False := by
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨e₂⟩ := hSL
  have h2 : (2 : ZMod q) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod q) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 this)
  refine false_of_sl2_image h2
    (e₂.toMonoidHom.comp (QuotientGroup.mk' (CFSG.oddCore ↥(modO2Image Gi K)))) ?_
    (iotaU S hLK) (iotaU_injective S hLK) ?_ (by have := S.U_card; omega)
  · intro x hx
    have h1 : QuotientGroup.mk' (CFSG.oddCore ↥(modO2Image Gi K)) x = 1 := by
      have : e₂ (QuotientGroup.mk' (CFSG.oddCore ↥(modO2Image Gi K)) x) = 1 := hx
      exact e₂.injective (by simpa using this)
    have hxo : x ∈ CFSG.oddCore ↥(modO2Image Gi K) := (QuotientGroup.eq_one_iff x).1 h1
    have hodd := A38.odd_card_oddCore ↥(modO2Image Gi K)
    have hdvd : orderOf x ∣ Nat.card (CFSG.oddCore ↥(modO2Image Gi K)) :=
      Subgroup.orderOf_dvd_natCard _ hxo
    exact Odd.of_dvd_nat hodd hdvd
  · intro w
    apply Subtype.ext
    have := S.U_elem.2 (w : G) w.2
    simpa [pow_two] using this

theorem not_case34 (S : Setting Gi L SI U) {K : Subgroup G} (hLK : L ≤ K)
    (hcommon : A36Common ↥(modO2Image Gi K))
    (h34 : A36Case3 ↥(modO2Image Gi K) ∨ A36Case4 ↥(modO2Image Gi K)) : False := by
  have hF := hcommon.1
  rcases h34 with ⟨p, hp, hp3, -, -, hnat⟩ | h4
  · exact no_sl2_quotient S hLK hp (by omega) (A313.isSL2_quotient_of_natural hF hnat)
  · have h5 : IsSL2 5 (↥(modO2Image Gi K) ⧸ CFSG.fittingSubgroup ↥(modO2Image Gi K)) :=
      h4.2.2.1
    exact no_sl2_quotient S hLK Nat.prime_five (by norm_num)
      (IsSL2.of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hF) h5)

theorem isQuasisimple_modO2Image (h36 : A36CoreForSQTKCat) (S : Setting Gi L SI U)
    {K : Subgroup G} (hK : K ∈ cComp Gi) (hLK : L ≤ K) :
    CFSG.IsQuasisimple ↥(modO2Image Gi K) := by
  obtain ⟨hcases, hcommon, -⟩ := lemma_1_2_1_four_core S.qtke h36 S.gi_core hK
  rcases hcases with hc | h34
  · exact hc.1
  · exact (not_case34 S hLK hcommon h34).elim

theorem isQuasisimple_modO2 (h36 : A36CoreForSQTKCat) (S : Setting Gi L SI U) {K : Subgroup G}
    (hK : K ∈ cComp Gi) (hLK : L ≤ K) :
    CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) := by
  obtain ⟨e⟩ := modO2_mulEquiv hK
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm (isQuasisimple_modO2Image h36 S hK hLK)

omit [Finite G] in
theorem exists_elemAbelian_modO2Image (S : Setting Gi L SI U) {K : Subgroup G} (hLK : L ≤ K) :
    ∃ E : Subgroup ↥(modO2Image Gi K), IsElemAbelian 2 E ∧ 16 ≤ Nat.card E := by
  have hUcomm : ∀ u ∈ U, ∀ v ∈ U, u * v = v * u := fun u hu v hv => by
    have := S.U_elem.1
    exact setLike_mul_comm hu hv
  refine ⟨(iotaU S hLK).range, ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
  · obtain ⟨u, hu⟩ := a.2
    obtain ⟨v, hv⟩ := b.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hu, ← hv, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hUcomm _ u.2 _ v.2)
  · obtain ⟨u, rfl⟩ := hx
    rw [← map_pow]
    have : u ^ 2 = 1 := Subtype.ext (S.U_elem.2 _ u.2)
    rw [this, map_one]
  · have e := Nat.card_congr (MonoidHom.ofInjective (iotaU_injective S hLK)).toEquiv
    rw [← e]
    exact S.U_card

end Main

end CFSG.QuasithinUnique.A5.C25
