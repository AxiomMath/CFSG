module

public import CFSG.GH74.GLS.Stage4.T2Interfaces
public import CFSG.GH74.GLS.Stage4.T2CentSL
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.AutAlternatingFour
public import CFSG.GH74.GLS.Stage4.T2SL2A

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Equiv CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage4.Rest.T2 CFSG.GorensteinWalter

section S4

theorem t2oc3_s4_check :
    ∀ r t : Perm (Fin 4), r ^ 3 = 1 → Perm.sign t = -1 → (r * t * r⁻¹ * t⁻¹) ^ 8 = 1 → r = 1 := by
  decide +kernel

theorem t2oc3_card_perm4 : Nat.card (Perm (Fin 4)) = 24 := by
  rw [Nat.card_perm]
  norm_num [Nat.card_eq_fintype_card, Nat.factorial]

theorem t2oc3_pow_three {A : Type*} [Group A] (Θ : A →* Perm (Fin 4)) (ρ : A)
    (hρ : Odd (orderOf ρ)) : Θ ρ ^ 3 = 1 := by
  have h1 : orderOf (Θ ρ) ∣ orderOf ρ := orderOf_map_dvd Θ ρ
  have h2 : orderOf (Θ ρ) ∣ 3 * 8 := by
    have := orderOf_dvd_natCard (Θ ρ)
    rwa [t2oc3_card_perm4] at this
  have hodd : Odd (orderOf (Θ ρ)) := Odd.of_dvd_nat hρ h1
  have hcop : Nat.Coprime (orderOf (Θ ρ)) 8 := by
    have : Nat.Coprime (orderOf (Θ ρ)) 2 := Nat.coprime_two_right.mpr hodd
    simpa using Nat.Coprime.pow_right 3 this
  exact orderOf_dvd_iff_pow_eq_one.1 (hcop.dvd_of_dvd_mul_right h2)

theorem t2oc3_pow_eight {A : Type*} [Group A] (Θ : A →* Perm (Fin 4)) (c : A) {k : ℕ}
    (hk : c ^ (2 ^ k) = 1) : Θ c ^ 8 = 1 := by
  have h1 : Θ c ^ (2 ^ k) = 1 := by rw [← map_pow, hk, map_one]
  have h2 : orderOf (Θ c) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h1
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h2
  have h3 : orderOf (Θ c) ∣ 8 * 3 := by
    have := orderOf_dvd_natCard (Θ c)
    rwa [t2oc3_card_perm4] at this
  have hcop : Nat.Coprime (orderOf (Θ c)) 3 := by
    rw [hj]
    exact Nat.Coprime.pow_left j (by norm_num)
  exact orderOf_dvd_iff_pow_eq_one.1 (hcop.dvd_of_dvd_mul_right h3)

theorem t2oc3_abstract {A : Type*} [Group A] (Θ : A →* Perm (Fin 4)) (hΘ : Function.Injective Θ)
    (I : Subgroup A) (hI : ∀ a : A, Θ a ∈ alternatingGroup (Fin 4) → a ∈ I)
    (M : Subgroup A) (hM : IsPGroup 2 ↥M) (ξ : A) (hξM : ξ ∈ M) (hξI : ξ ∉ I)
    (ρ : A) (hρ : Odd (orderOf ρ)) (hnorm : ∀ φ ∈ M, ρ * φ * ρ⁻¹ ∈ M) : ρ = 1 := by
  apply hΘ
  rw [map_one]
  have hsign : Perm.sign (Θ ξ) = -1 := by
    have : Perm.sign (Θ ξ) ≠ 1 := fun h => hξI (hI ξ (Equiv.Perm.mem_alternatingGroup.2 h))
    rcases Int.units_eq_one_or (Perm.sign (Θ ξ)) with h | h
    · exact absurd h this
    · exact h
  have hc : ρ * ξ * ρ⁻¹ * ξ⁻¹ ∈ M := M.mul_mem (hnorm ξ hξM) (M.inv_mem hξM)
  obtain ⟨k, hk⟩ := hM ⟨_, hc⟩
  have hk' : (ρ * ξ * ρ⁻¹ * ξ⁻¹) ^ (2 ^ k) = 1 := by
    simpa using congrArg Subtype.val hk
  have h8 := t2oc3_pow_eight Θ _ hk'
  simp only [map_mul, map_inv] at h8
  exact t2oc3_s4_check (Θ ρ) (Θ ξ) (t2oc3_pow_three Θ ρ hρ) hsign h8

end S4

section Quot

variable (G : Type) [Group G]

theorem t2oc3_map_center_eq (φ : MulAut G) :
    (Subgroup.center G).map (φ : G →* G) = Subgroup.center G :=
  Subgroup.characteristic_iff_map_eq.1 inferInstance φ

noncomputable def t2oc3_quotAut : MulAut G →* MulAut (G ⧸ Subgroup.center G) where
  toFun φ := QuotientGroup.congr (Subgroup.center G) (Subgroup.center G) φ (t2oc3_map_center_eq G φ)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => rfl
  map_mul' φ ψ := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => rfl

theorem t2oc3_quotAut_mk (φ : MulAut G) (x : G) :
    t2oc3_quotAut G φ (x : G ⧸ Subgroup.center G) = ((φ x : G) : G ⧸ Subgroup.center G) :=
  QuotientGroup.congr_mk _ _ _ (t2oc3_map_center_eq G φ) x

end Quot

theorem t2oc3_transvection_pow_three (i j : Fin 2) (h : i ≠ j) (c : ZMod 3) :
    (Matrix.SpecialLinearGroup.transvection h c) ^ 3 = 1 := by
  have h3 : c + c + c = 0 := by
    have : (3 : ZMod 3) = 0 := by decide
    calc c + c + c = 3 * c := by ring
      _ = 0 := by rw [this, zero_mul]
  rw [pow_succ, pow_succ, pow_one, ← Matrix.SpecialLinearGroup.transvection_add,
    ← Matrix.SpecialLinearGroup.transvection_add, h3, Matrix.SpecialLinearGroup.transvection_coeff_zero]

theorem t2oc3_quotAut_injective : Function.Injective (t2oc3_quotAut (SL2 (ZMod 3))) := by
  rw [injective_iff_map_eq_one]
  intro φ hφ
  have hmk : ∀ x : SL2 (ZMod 3), (φ x)⁻¹ * x ∈ Subgroup.center (SL2 (ZMod 3)) := by
    intro x
    have h1 : t2oc3_quotAut (SL2 (ZMod 3)) φ
        (x : SL2 (ZMod 3) ⧸ Subgroup.center (SL2 (ZMod 3))) =
        (x : SL2 (ZMod 3) ⧸ Subgroup.center (SL2 (ZMod 3))) := by
      rw [hφ]; rfl
    rw [t2oc3_quotAut_mk] at h1
    exact QuotientGroup.eq.1 h1
  have h2 : (2 : ZMod 3) ≠ 0 := by decide
  have htv : ∀ (i j : Fin 2) (h : i ≠ j) (c : ZMod 3),
      φ (Matrix.SpecialLinearGroup.transvection h c) = Matrix.SpecialLinearGroup.transvection h c := by
    intro i j h c
    set t := Matrix.SpecialLinearGroup.transvection h c with ht
    have ht3 : t ^ 3 = 1 := t2oc3_transvection_pow_three i j h c
    rcases (t2C_center_sl2 _).1 (hmk t) with h1 | h1
    · exact inv_mul_eq_one.1 h1
    · exfalso
      have e1 : t = φ t * negOne (ZMod 3) := by
        rw [← h1]; group
      have hcomm : Commute (φ t) (negOne (ZMod 3)) := (negOne_central _).symm
      have e2 : (φ t * negOne (ZMod 3)) ^ 3 = negOne (ZMod 3) := by
        rw [hcomm.mul_pow, ← map_pow, ht3, map_one, one_mul, pow_succ, pow_two, negOne_mul_self,
          one_mul]
      have e3 : t ^ 3 = negOne (ZMod 3) := by rw [← e2, ← e1]
      exact t2C_negOne_ne_one h2 (e3.symm.trans ht3)
  refine MulEquiv.ext fun x => ?_
  exact Matrix.SL2.transvection_induction (fun A => φ A = A) htv
    (fun A B hA hB => by simp only [map_mul, hA, hB]) x

noncomputable def t2oc3_conjEquiv : Perm (Fin 4) ≃* MulAut (alternatingGroup (Fin 4)) :=
  MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin 4)))
    CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_four_bijective_conj

noncomputable def t2oc3_toAutA4 : MulAut (SL2 (ZMod 3)) →* MulAut (alternatingGroup (Fin 4)) :=
  (MulAut.congr psl2_three_equiv_alternatingGroup).toMonoidHom.comp (t2oc3_quotAut (SL2 (ZMod 3)))

noncomputable def t2oc3_Theta : MulAut (SL2 (ZMod 3)) →* Perm (Fin 4) :=
  t2oc3_conjEquiv.symm.toMonoidHom.comp t2oc3_toAutA4

theorem t2oc3_conjEquiv_Theta (a : MulAut (SL2 (ZMod 3))) :
    t2oc3_conjEquiv (t2oc3_Theta a) = t2oc3_toAutA4 a :=
  t2oc3_conjEquiv.apply_symm_apply _

theorem t2oc3_toAutA4_injective : Function.Injective t2oc3_toAutA4 := by
  intro a b h
  apply t2oc3_quotAut_injective
  exact (MulAut.congr psl2_three_equiv_alternatingGroup).injective h

theorem t2oc3_Theta_injective : Function.Injective t2oc3_Theta := by
  intro a b h
  apply t2oc3_toAutA4_injective
  rw [← t2oc3_conjEquiv_Theta, ← t2oc3_conjEquiv_Theta, h]

theorem t2oc3_toAutA4_conj (g : SL2 (ZMod 3)) :
    t2oc3_toAutA4 (MulAut.conj g) = t2oc3_conjEquiv
      ((psl2_three_equiv_alternatingGroup (g : SL2 (ZMod 3) ⧸ Subgroup.center (SL2 (ZMod 3))) :
        alternatingGroup (Fin 4)) : Perm (Fin 4)) := by
  refine MulEquiv.ext fun h => Subtype.ext ?_
  obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (psl2_three_equiv_alternatingGroup.symm h)
  have hh : h = psl2_three_equiv_alternatingGroup
      (y : SL2 (ZMod 3) ⧸ Subgroup.center (SL2 (ZMod 3))) := by
    rw [hy, MulEquiv.apply_symm_apply]
  subst hh
  simp [t2oc3_toAutA4, t2oc3_quotAut_mk, MulAut.congr_apply, t2oc3_conjEquiv,
    MulAut.conjNormal_apply]

theorem t2oc3_Theta_conj (g : SL2 (ZMod 3)) :
    t2oc3_Theta (MulAut.conj g) = ((psl2_three_equiv_alternatingGroup
      (g : SL2 (ZMod 3) ⧸ Subgroup.center (SL2 (ZMod 3))) : alternatingGroup (Fin 4)) :
        Perm (Fin 4)) := by
  apply t2oc3_conjEquiv.injective
  rw [t2oc3_conjEquiv_Theta, t2oc3_toAutA4_conj]

theorem t2oc3_Theta_good (a : MulAut (SL2 (ZMod 3))) (ha : t2oc3_Theta a ∈ alternatingGroup (Fin 4)) :
    a ∈ (MulAut.conj : SL2 (ZMod 3) →* MulAut (SL2 (ZMod 3))).range := by
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective
    (psl2_three_equiv_alternatingGroup.symm (⟨t2oc3_Theta a, ha⟩ : alternatingGroup (Fin 4)))
  refine ⟨g, ?_⟩
  apply t2oc3_Theta_injective
  rw [t2oc3_Theta_conj, hg, MulEquiv.apply_symm_apply]

def T2OC3Good (Q : Type) [Group Q] : Prop :=
  ∃ Θ : MulAut Q →* Perm (Fin 4), Function.Injective Θ ∧
    ∀ a : MulAut Q, Θ a ∈ alternatingGroup (Fin 4) → a ∈ (MulAut.conj : Q →* MulAut Q).range

theorem T2OC3Good.of_mulEquiv {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q')
    (h : T2OC3Good Q') : T2OC3Good Q := by
  obtain ⟨Θ, hΘ, hΘg⟩ := h
  refine ⟨Θ.comp (MulAut.congr e).toMonoidHom, hΘ.comp (MulAut.congr e).injective, fun a ha => ?_⟩
  obtain ⟨q, hq⟩ := hΘg (MulAut.congr e a) ha
  refine ⟨e.symm q, ?_⟩
  apply (MulAut.congr e).injective
  rw [← hq]
  refine MulEquiv.ext fun x => ?_
  simp [MulAut.congr_apply, MulAut.conj_apply]

noncomputable def t2oc3_slRingEquiv {R S : Type} [CommRing R] [CommRing S] (e : R ≃+* S) :
    Matrix.SpecialLinearGroup (Fin 2) R ≃* Matrix.SpecialLinearGroup (Fin 2) S :=
  MonoidHom.toMulEquiv (Matrix.SpecialLinearGroup.map e.toRingHom)
    (Matrix.SpecialLinearGroup.map e.symm.toRingHom)
    (by ext x i j; simp) (by ext x i j; simp)

theorem t2oc3_good_of_card_three {Q : Type} [Group Q] {F : Type} [Field F] [Finite F]
    (h3 : Nat.card F = 3) (e : Q ≃* SL2 F) : T2OC3Good Q := by
  have : Fintype F := Fintype.ofFinite F
  have hc : Fintype.card F = Fintype.card (ZMod 3) := by
    rw [← Nat.card_eq_fintype_card, h3, ZMod.card]
  let r : F ≃+* ZMod 3 := FiniteField.ringEquivOfCardEq hc
  exact T2OC3Good.of_mulEquiv (e.trans (t2oc3_slRingEquiv r))
    ⟨t2oc3_Theta, t2oc3_Theta_injective, t2oc3_Theta_good⟩

theorem t2_oc3 : T2OC3 := by
  intro Q _ _ F _ _ h3 e _ M hM _ hxi ρ hρ hnorm φ _
  obtain ⟨Θ, hΘ, hΘg⟩ := t2oc3_good_of_card_three h3 e
  obtain ⟨ξ, hξM, hξI⟩ := hxi
  have hρ1 : ρ = 1 :=
    t2oc3_abstract Θ hΘ (MulAut.conj : Q →* MulAut Q).range hΘg M hM ξ hξM hξI ρ hρ hnorm
  subst hρ1
  simp

end CFSG.GH74.GLS.Stage4.Rest
