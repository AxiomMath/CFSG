module

public import CFSG.GH74.GLS.Stage4.T2Interfaces
public import CFSG.GH74.GLS.Stage4.T2SylSL

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage4.Rest.T2

private theorem t2c3_pow_eight : ∀ g : SL2 (ZMod 3), g ^ 8 = 1 → g ^ 4 = 1 := by decide

private theorem t2c3_card_fourth : Fintype.card {g : SL2 (ZMod 3) // g ^ 4 = 1} = 8 := by decide

theorem t2c3_card_sl2_three : Nat.card (SL2 (ZMod 3)) = 24 := by
  rw [t2C_card_sl2, Nat.card_zmod]
  norm_num

theorem t2c3_card_sylow (P : Subgroup (SL2 (ZMod 3))) (hP : IsPGroup 2 ↥P) (hidx : ¬ 2 ∣ P.index) :
    Nat.card P = 8 := by
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hmul : Nat.card P * P.index = 24 := by
    rw [Subgroup.card_mul_index, t2c3_card_sl2_three]
  have hpos : 0 < P.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  rw [hn] at hmul ⊢
  have hn5 : n < 5 := by
    by_contra h
    have h32 : 2 ^ 5 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    nlinarith
  interval_cases n <;> omega

theorem t2c3_sylow_normal (P : Subgroup (SL2 (ZMod 3))) (hP : IsPGroup 2 ↥P)
    (hidx : ¬ 2 ∣ P.index) : P.Normal := by
  classical
  have hcard := t2c3_card_sylow P hP hidx
  have hP4 : ∀ g ∈ P, g ^ 4 = 1 := by
    intro g hg
    apply t2c3_pow_eight
    have h : (⟨g, hg⟩ : P) ^ Nat.card P = 1 := pow_card_eq_one'
    rw [hcard] at h
    simpa using congrArg Subtype.val h
  have hT : ∀ g : SL2 (ZMod 3), g ^ 4 = 1 → g ∈ P := by
    have hTf : (Finset.univ.filter (fun g : SL2 (ZMod 3) => g ^ 4 = 1)).card = 8 := by
      rw [← Fintype.card_subtype]
      exact t2c3_card_fourth
    have hPf : (Finset.univ.filter (fun g : SL2 (ZMod 3) => g ∈ P)).card = 8 := by
      rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
      exact hcard
    have hsub : Finset.univ.filter (fun g : SL2 (ZMod 3) => g ∈ P) ⊆
        Finset.univ.filter (fun g : SL2 (ZMod 3) => g ^ 4 = 1) := by
      intro g hg
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
      exact hP4 g hg
    have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hTf, hPf])
    intro g hg
    have hg' : g ∈ Finset.univ.filter (fun g : SL2 (ZMod 3) => g ^ 4 = 1) := by simp [hg]
    rw [← heq] at hg'
    simpa using hg'
  refine ⟨fun n hn g => hT _ ?_⟩
  rw [conj_pow, hP4 n hn, mul_one, mul_inv_cancel]

theorem t2c3_fixes_order_three (P : Subgroup (SL2 (ZMod 3))) (hP : IsPGroup 2 ↥P)
    (hidx : ¬ 2 ∣ P.index) (φ : MulAut (SL2 (ZMod 3))) (hφ : ∀ p ∈ P, φ p = p)
    (x : SL2 (ZMod 3)) (hx : x ^ 3 = 1) : φ x = x := by
  have hnormal := t2c3_sylow_normal P hP hidx
  have hodd : Odd (Nat.card (ZMod 3)) := by
    rw [Nat.card_zmod]
    decide
  have h2 : (2 : ZMod 3) ≠ 0 := by decide
  have hcomm : ∀ p ∈ P, (x⁻¹ * φ x) * p = p * (x⁻¹ * φ x) := by
    intro p hp
    have hp' : x * p * x⁻¹ ∈ P := hnormal.conj_mem p hp x
    have h1 : φ x * p * (φ x)⁻¹ = x * p * x⁻¹ := by
      rw [← hφ _ hp', map_mul, map_mul, map_inv, hφ p hp]
    calc x⁻¹ * φ x * p = x⁻¹ * (φ x * p * (φ x)⁻¹) * φ x := by group
      _ = p * (x⁻¹ * φ x) := by rw [h1]; group
  rcases t2C_cent_sylow_sl2 hodd P hP hidx (x⁻¹ * φ x) hcomm with h | h
  · exact (inv_mul_eq_one.1 h).symm
  · exfalso
    have hφx : φ x = x * negOne (ZMod 3) := by rw [← h]; group
    have hcube : (φ x) ^ 3 = 1 := by rw [← map_pow, hx, map_one]
    rw [hφx, (Commute.mul_pow (negOne_central x).symm 3), hx, one_mul, pow_succ, pow_two,
      negOne_mul_self, one_mul] at hcube
    exact negOne_ne_one h2 hcube

theorem t2c3_aut_eq_one (P : Subgroup (SL2 (ZMod 3))) (hP : IsPGroup 2 ↥P) (hidx : ¬ 2 ∣ P.index)
    (φ : MulAut (SL2 (ZMod 3))) (hφ : ∀ p ∈ P, φ p = p) : φ = 1 := by
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := SL2 (ZMod 3)) 3
    (by rw [t2c3_card_sl2_three]; norm_num)
  have hx3 : x ^ 3 = 1 := by
    have h := pow_orderOf_eq_one x
    rwa [hx] at h
  let K : Subgroup (SL2 (ZMod 3)) :=
    MonoidHom.eqLocus (φ : SL2 (ZMod 3) →* SL2 (ZMod 3)) (MonoidHom.id _)
  have hPK : P ≤ K := fun p hp => hφ p hp
  have hxK : x ∈ K := t2c3_fixes_order_three P hP hidx φ hφ x hx3
  have h8 : 8 ∣ Nat.card K := t2c3_card_sylow P hP hidx ▸ Subgroup.card_dvd_of_le hPK
  have h3 : 3 ∣ Nat.card K := by
    have := orderOf_dvd_natCard (⟨x, hxK⟩ : K)
    rwa [Subgroup.orderOf_mk, hx] at this
  have h24 : 24 ∣ Nat.card K := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h8 h3
  have hKtop : K = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    have hdvd : Nat.card K ∣ 24 := t2c3_card_sl2_three ▸ Subgroup.card_subgroup_dvd_card K
    exact (Nat.dvd_antisymm hdvd h24).trans t2c3_card_sl2_three.symm
  refine MulEquiv.ext fun g => ?_
  have hg : g ∈ K := by
    rw [hKtop]
    exact Subgroup.mem_top g
  exact hg

@[expose] noncomputable def t2c3_slEquiv {R K : Type} [CommRing R] [CommRing K] (f : R ≃+* K) :
    Matrix.SpecialLinearGroup (Fin 2) R ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
  MonoidHom.toMulEquiv (Matrix.SpecialLinearGroup.map f.toRingHom)
    (Matrix.SpecialLinearGroup.map f.symm.toRingHom)
    (by ext x i j; simp) (by ext x i j; simp)

theorem t2c3_exists_equiv {F : Type} [Field F] [Finite F] (hF : Nat.card F = 3) :
    Nonempty (SL2 F ≃* SL2 (ZMod 3)) := by
  have : Fintype F := Fintype.ofFinite F
  have hc : Fintype.card F = Fintype.card (ZMod 3) := by
    rw [ZMod.card, ← Nat.card_eq_fintype_card, hF]
  exact ⟨t2c3_slEquiv (FiniteField.ringEquivOfCardEq hc)⟩

theorem t2c3_of_equiv {Q : Type} [Group Q] (ψ : Q ≃* SL2 (ZMod 3)) (P : Subgroup Q)
    (hP : IsPGroup 2 ↥P) (hidx : ¬ 2 ∣ P.index) (φ : MulAut Q) (hφ : ∀ p ∈ P, φ p = p) :
    φ = 1 := by
  have hP' : IsPGroup 2 ↥(P.map (ψ : Q →* SL2 (ZMod 3))) :=
    hP.of_equiv (P.equivMapOfInjective (ψ : Q →* SL2 (ZMod 3)) ψ.injective)
  have hidx' : ¬ 2 ∣ (P.map (ψ : Q →* SL2 (ZMod 3))).index := by
    rwa [Subgroup.index_map_equiv]
  have key := t2c3_aut_eq_one (P.map (ψ : Q →* SL2 (ZMod 3))) hP' hidx' (MulAut.congr ψ φ) (by
    rintro _ ⟨p, hp, rfl⟩
    simp [MulAut.congr_apply, hφ p hp])
  refine MulEquiv.ext fun q => ?_
  have h := DFunLike.congr_fun key (ψ q)
  simpa [MulAut.congr_apply] using h

theorem t2_c3 : T2C3 := by
  intro Q _ _ F _ _ hF e P hP hidx φ hφ
  obtain ⟨r⟩ := t2c3_exists_equiv hF
  exact t2c3_of_equiv (e.trans r) P hP hidx φ hφ

end CFSG.GH74.GLS.Stage4.Rest
