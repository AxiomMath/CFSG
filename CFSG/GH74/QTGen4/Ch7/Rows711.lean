module

public import CFSG.GH74.QTGen4.Ch7.Rows

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Ch7

open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Open CFSG.GH74
open scoped IsMulCommutative Matrix

theorem card_sup_le_mul_of_comm {W : Type*} [CommGroup W] [Finite W] (A B : Subgroup W) :
    Nat.card ↥(A ⊔ B) ≤ Nat.card A * Nat.card B := by
  let φ : A × B →* W :=
    (A.subtype.comp (MonoidHom.fst A B)) * (B.subtype.comp (MonoidHom.snd A B))
  have hr : φ.range = A ⊔ B := by
    apply le_antisymm
    · rintro _ ⟨⟨a, b⟩, rfl⟩
      exact Subgroup.mul_mem_sup a.2 b.2
    · refine sup_le ?_ ?_
      · intro a ha
        exact ⟨(⟨a, ha⟩, 1), by simp [φ]⟩
      · intro b hb
        exact ⟨(1, ⟨b, hb⟩), by simp [φ]⟩
  rw [← hr, ← Nat.card_prod]
  exact Nat.card_le_card_of_surjective φ.rangeRestrict φ.rangeRestrict_surjective

theorem card_mul_le_of_inf_bot {G : Type*} [Group G] [Finite G] {I J V : Subgroup G}
    (hI : I ≤ V) (hJ : J ≤ V) (h : I ⊓ J = ⊥) : Nat.card I * Nat.card J ≤ Nat.card V := by
  let ψ : I × J → V := fun p => ⟨(p.1 : G) * p.2, V.mul_mem (hI p.1.2) (hJ p.2.2)⟩
  have hinj : Function.Injective ψ := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ hab
    have h1 : (a : G) * b = a' * b' := congrArg Subtype.val hab
    have h2 : (a' : G)⁻¹ * a = b' * (b : G)⁻¹ := by
      calc (a' : G)⁻¹ * a = (a' : G)⁻¹ * (a * b) * (b : G)⁻¹ := by group
        _ = (a' : G)⁻¹ * (a' * b') * (b : G)⁻¹ := by rw [h1]
        _ = b' * (b : G)⁻¹ := by group
    have h3 : (a' : G)⁻¹ * a ∈ I ⊓ J :=
      ⟨I.mul_mem (I.inv_mem a'.2) a.2, by rw [h2]; exact J.mul_mem b'.2 (J.inv_mem b.2)⟩
    rw [h, Subgroup.mem_bot, inv_mul_eq_one] at h3
    have h4 : a = a' := Subtype.ext h3.symm
    subst h4
    have h5 : (b : G) = b' := mul_left_cancel h1
    exact Prod.ext rfl (Subtype.ext h5)
  rw [← Nat.card_prod]
  exact Nat.card_le_card_of_injective ψ hinj

theorem card_conjugate' {G : Type*} [Group G] (A : Subgroup G) (g : G) :
    Nat.card (CFSG.conjugate A g) = Nat.card A := by
  unfold CFSG.conjugate
  exact Subgroup.card_map_of_injective (MulEquiv.injective (MulAut.conj g⁻¹))

open CFSG.Quasithin.G6 in
theorem sq_permMod (n : ℕ) (x : PermMod n) : x * x = 1 := by
  apply Multiplicative.toAdd.injective
  funext i
  simp only [toAdd_mul, toAdd_one, Pi.add_apply, Pi.zero_apply]
  exact CharTwo.add_self_eq_zero _

theorem card_zpowers_le_two {W : Type*} [Group W] (a : W) (h : a * a = 1) :
    Nat.card (Subgroup.zpowers a) ≤ 2 := by
  rw [Nat.card_zpowers]
  exact orderOf_le_of_pow_eq_one (by norm_num) (by rw [pow_two]; exact h)

open CFSG.Quasithin.G6 in
local instance decMemCoreModR57 (m : ℕ) : DecidablePred (· ∈ coreMod m) := fun x =>
  decidable_of_iff (∑ i, Multiplicative.toAdd x i = 0) mem_coreMod.symm

open CFSG.Quasithin.G6 in
theorem card_coreMod_six : Nat.card ↥(coreMod 6) = 32 := by
  have : Fintype.card {x : PermMod 6 // x ∈ coreMod 6} = 32 := by decide +kernel
  rw [← this, ← Nat.card_eq_fintype_card]

section NatRows

variable {V : Type*} [CommGroup V] [Finite V] {H : Subgroup (MulAut V)} {U Z : Subgroup V}

instance finite_nat_amb {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K]
    (Γ : Subgroup (Matrix.GeneralLinearGroup ι K)) : Finite (FFModel.nat Γ).Amb :=
  inferInstanceAs (Finite (Multiplicative (ι → K)))

theorem rowNat_card {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K]
    {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)} (h : (FFModel.nat Γ).Realizes H U Z) :
    Nat.card K ^ Fintype.card ι ≤ Nat.card U := by
  have h1 := sec_le_card_mul h
  have h2 : Nat.card (FFModel.nat Γ).sec = Nat.card K ^ Fintype.card ι := by
    show Nat.card (⊤ : Subgroup (Multiplicative (ι → K))) = _
    rw [Subgroup.card_top,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (ι → K) ≃ (ι → K)), Nat.card_fun,
      Nat.card_eq_fintype_card (α := ι)]
  have h3 : Nat.card (FFModel.nat Γ).ker = 1 := Subgroup.card_bot
  rw [h2, h3] at h1
  simpa using h1

theorem rowSU3_card {n : ℕ} (hn : 2 ≤ n) (h : BinaryNaturalSU3 (V := V) H ⊤ ⊥ n) :
    2 ^ 12 ≤ Nat.card V := by
  obtain ⟨K, _, _, hK, h⟩ := h
  have h1 := rowNat_card h
  rw [hK, Subgroup.card_top, Fintype.card_fin] at h1
  have h2 : 4 ≤ 2 ^ n :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h3 : 4 ^ 6 ≤ (2 ^ n) ^ 6 := Nat.pow_le_pow_left h2 6
  have h4 : ((2 ^ n) ^ 2) ^ 3 = (2 ^ n) ^ 6 := by rw [← pow_mul]
  rw [h4] at h1
  calc 2 ^ 12 = 4 ^ 6 := by norm_num
    _ ≤ _ := h3.trans h1

theorem rowSz_card {f : ℕ} (h : BinaryNaturalSz (V := V) H ⊤ ⊥ f) : 2 ^ 12 ≤ Nat.card V := by
  obtain ⟨a, ha, hf, K, _, _, hK, h⟩ := h
  have h1 := rowNat_card h
  rw [hK, Subgroup.card_top, Fintype.card_fin] at h1
  have h3 : 2 ^ 12 ≤ (2 ^ f) ^ 4 := by
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  exact h3.trans h1

theorem rowMhat22_card (h : Mhat22Twelve (V := V) H ⊤ ⊥) : 2 ^ 12 ≤ Nat.card V := by
  obtain ⟨K, _, _, Γ₀, hK, -, -, h⟩ := h
  have h1 := rowNat_card h
  rw [hK, Subgroup.card_top, Fintype.card_fin] at h1
  calc 2 ^ 12 = 4 ^ 6 := by norm_num
    _ ≤ _ := h1

end NatRows

section GolayRows2

open CFSG.Quasithin.G6

variable {V : Type*} [CommGroup V] [Finite V] {H : Subgroup (MulAut V)}

theorem rowM23Code_card (h : MathieuCode23 (V := V) H ⊤ ⊥) : 2048 ≤ Nat.card V := by
  obtain ⟨x, h⟩ := h
  have h1 := golay_sec_le h
  have h2 := Nat.mul_le_mul_left (Nat.card V) card_zpowers_allOnes_le
  rw [card_golayC] at h1
  omega

theorem rowM23Cocode_card (h : MathieuCocode23 (V := V) H ⊤ ⊥) : 2048 ≤ Nat.card V := by
  obtain ⟨x, h⟩ := h
  have h1 := golay_sec_le h
  have h3 := card_coreMod_ge
  have h4 : Nat.card V * Nat.card golayC ≤ Nat.card V * 4096 := by rw [card_golayC]
  omega

theorem rowM22Cocode_card (h : MathieuCocode22 (V := V) H ⊤ ⊥) : 1024 ≤ Nat.card V := by
  obtain ⟨x, y, -, h⟩ := h
  have h1 := golay_sec_le h
  have h2 : Nat.card ↥(golayC ⊔ Subgroup.zpowers (pairVec x y)) ≤ 4096 * 2 := by
    refine (card_sup_le_mul_of_comm _ _).trans (Nat.mul_le_mul (le_of_eq card_golayC) ?_)
    exact card_zpowers_le_two _ (sq_permMod 24 _)
  have h3 := card_coreMod_ge
  have h4 := Nat.mul_le_mul_left (Nat.card V) h2
  omega

theorem rowM12_card (h : M12Ten (V := V) H ⊤ ⊥) : 1024 ≤ Nat.card V := by
  obtain ⟨eY, -, -, h⟩ := h
  have h1 := golay_sec_le h
  have h2 : Nat.card ↥(Subgroup.closure {allOnes 24, eY}) ≤ 2 * 2 := by
    have hle : Subgroup.closure {allOnes 24, eY} ≤
        Subgroup.zpowers (allOnes 24) ⊔ Subgroup.zpowers eY := by
      rw [Subgroup.closure_le]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
      · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    refine (Subgroup.card_le_of_le hle).trans ((card_sup_le_mul_of_comm _ _).trans ?_)
    exact Nat.mul_le_mul (card_zpowers_le_two _ (sq_permMod 24 _))
      (card_zpowers_le_two _ (sq_permMod 24 _))
  rw [card_golayC] at h1
  have h4 := Nat.mul_le_mul_left (Nat.card V) h2
  omega

end GolayRows2

section PairRows

open CFSG.Quasithin.G6

instance finite_altDn_amb (n : ℕ) : Finite (FFModel.altDn n).Amb :=
  inferInstanceAs (Finite (PermMod n))

instance finite_a7Four_amb
    (α : ↥(alternatingGroup (Fin 8)) ≃* Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)) :
    Finite (FFModel.a7Four α).Amb :=
  inferInstanceAs (Finite (Multiplicative (Fin 4 → ZMod 2)))

variable {V : Type*} [CommGroup V] [Finite V] {H : Subgroup (MulAut V)} {U : Subgroup V}

theorem rowAlt6_card (h : AlternatingNatural (V := V) H U ⊥ 6) : 16 ≤ Nat.card U := by
  have h1 := sec_le_card_mul h
  have h2 : Nat.card (FFModel.altDn 6).sec = 32 := card_coreMod_six
  have h3 : Nat.card (FFModel.altDn 6).ker ≤ 2 :=
    (Subgroup.card_le_of_le (inf_le_left : (Subgroup.zpowers (allOnes 6) ⊓ coreMod 6) ≤
      Subgroup.zpowers (allOnes 6))).trans (card_zpowers_le_two _ (sq_permMod 6 _))
  have h4 := Nat.mul_le_mul_left (Nat.card U) h3
  omega

theorem rowA7_card (h : A7Four (V := V) H U ⊥) : 16 ≤ Nat.card U := by
  obtain ⟨α, h⟩ := h
  have h1 := sec_le_card_mul h
  have h2 : Nat.card (FFModel.a7Four α).sec = 16 := by
    show Nat.card (⊤ : Subgroup (Multiplicative (Fin 4 → ZMod 2))) = 16
    rw [Subgroup.card_top,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fin 4 → ZMod 2) ≃ (Fin 4 → ZMod 2)),
      Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num
  have h3 : Nat.card (FFModel.a7Four α).ker = 1 := Subgroup.card_bot
  rw [h2, h3] at h1
  omega

end PairRows

section TwistedRows

variable {G : Type} [Group G] [Finite G] (T L I : Subgroup G) [IsMulCommutative ↥(fsuV T I)]

theorem card_sq_le_fsuV_of_twisted (h : IsTwistedPair T L I) :
    Nat.card I * Nat.card I ≤ Nat.card ↥(fsuV T I) := by
  obtain ⟨t, -, hsum, hinf, -⟩ := h
  have hI : I ≤ fsuV T I := hsum ▸ le_sup_left
  have hJ : CFSG.conjugate I t ≤ fsuV T I := hsum ▸ le_sup_right
  have := card_mul_le_of_inf_bot hI hJ hinf
  rwa [card_conjugate'] at this

theorem card_subgroupOf_fsuV (hI : I ≤ fsuV T I) :
    Nat.card ↥(I.subgroupOf (fsuV T I)) = Nat.card I :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe hI).toEquiv

theorem I_le_fsuV : I ≤ fsuV T I := CFSG.Quasithin.le_conjClosure I T

theorem not_rowSL3Pair (hV : Nat.card ↥(fsuV T I) ≤ 16) (n : ℕ) : ¬ Row711SL3Pair T L I n := by
  rintro ⟨hpair, K, _, _, hK, h⟩
  have h1 := rowNat_card h
  rw [card_subgroupOf_fsuV T I (I_le_fsuV T I)] at h1
  have h2 := card_sq_le_fsuV_of_twisted T L I hpair
  have hK2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have h3 : 8 ≤ Nat.card I :=
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ Nat.card K ^ Fintype.card (Fin 3) := by
          rw [Fintype.card_fin]; exact Nat.pow_le_pow_left hK2 3
      _ ≤ _ := h1
  nlinarith

theorem not_rowSp4Pair (hV : Nat.card ↥(fsuV T I) ≤ 16) : ¬ Row711Sp4Pair T L I := by
  rintro ⟨hpair, ⟨n, hn, K, _, _, hK, h⟩ | h⟩
  · have h1 := rowNat_card h
    rw [card_subgroupOf_fsuV T I (I_le_fsuV T I)] at h1
    have h5 := Subgroup.card_le_of_le (I_le_fsuV T I)
    have h2 : 4 ≤ Nat.card K := by
      rw [hK]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have h3 : 4 ^ 4 ≤ Nat.card K ^ Fintype.card (Fin 2 ⊕ Fin 2) := by
      simp only [Fintype.card_sum, Fintype.card_fin]
      exact Nat.pow_le_pow_left h2 4
    omega
  · have h1 := rowAlt6_card h
    rw [card_subgroupOf_fsuV T I (I_le_fsuV T I)] at h1
    have h2 := card_sq_le_fsuV_of_twisted T L I hpair
    nlinarith

theorem not_rowS7Pair (hV : Nat.card ↥(fsuV T I) ≤ 16) : ¬ Row711S7Pair T L I := by
  rintro ⟨hpair, h⟩
  have h1 := rowA7_card h
  rw [card_subgroupOf_fsuV T I (I_le_fsuV T I)] at h1
  have h2 := card_sq_le_fsuV_of_twisted T L I hpair
  nlinarith

end TwistedRows

section Assembly

variable {G : Type} [Group G] [Finite G] (T L I : Subgroup G) [IsMulCommutative ↥(fsuV T I)]

theorem not_rows7_1_1_of_gen4 (hG : Gen4 G) (hel : IsElemAbelian 2 (fsuV T I)) :
    ¬ Rows7_1_1 T L I := by
  have hV := card_fsuV_le T I hG hel
  obtain ⟨hr1, hr2, hr3, hr4, hr5, hr6⟩ := not_rows_of_gen4 T L I hG hel
  rintro (⟨n, hn, h⟩ | ⟨n, h⟩ | ⟨n, h⟩ | h | h | h | h | h | h | h | h | ⟨n, h⟩ | h | h | h | ⟨n, h⟩)
  · have := rowSU3_card hn h; omega
  · have := rowSz_card h; omega
  · exact hr1 ⟨n, h⟩
  · have := rowM12_card h.1; omega
  · have := rowMhat22_card h; omega
  · exact hr2 h
  · have := rowM22Cocode_card h; omega
  · have := rowM23Code_card h; omega
  · have := rowM23Cocode_card h; omega
  · exact hr3 h
  · exact hr4 h
  · exact not_rowSL3Pair T L I hV n h
  · exact not_rowSp4Pair T L I hV h
  · exact not_rowS7Pair T L I hV h
  · exact hr6 h
  · exact hr5 n h

end Assembly

end CFSG.GH74.QTGen4.Ch7
