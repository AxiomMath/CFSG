module

public import CFSG.Quasithin.H13.StatementsCh7
public import CFSG.GH74.SectionalRank

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Ch7

open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Open CFSG.GH74
open scoped IsMulCommutative Matrix

section Bound

variable {V : Type*} [CommGroup V]

theorem realizes_card_le [Finite V] {D : FFModel} {H : Subgroup (MulAut V)} {U Z : Subgroup V}
    (h : D.Realizes H U Z) :
    Nat.card (↥D.sec ⧸ D.ker.subgroupOf D.sec) ≤ Nat.card U := by
  obtain ⟨π, -, -, -, -, -, -, -, β, hβ, -⟩ := h
  exact Nat.card_le_card_of_surjective β hβ

theorem card_le_quot_mul {M : Type*} [Group M] [Finite M] (S K : Subgroup M) :
    Nat.card S ≤ Nat.card (S ⧸ K.subgroupOf S) * Nat.card K := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (K.subgroupOf S)]
  refine Nat.mul_le_mul_left _ ?_
  exact Nat.card_le_card_of_injective (fun x => (⟨x.1.1, x.2⟩ : K))
    (fun a b h => by
      have h' : a.1.1 = b.1.1 := congrArg (fun z : K => (z : M)) h
      exact Subtype.ext (Subtype.ext h'))

end Bound

section Golay


open CFSG.Quasithin.G6

theorem card_permMod (n : ℕ) : Nat.card (PermMod n) = 2 ^ n := by
  rw [Nat.card_congr (Multiplicative.toAdd : PermMod n ≃ (Fin n → ZMod 2)), Nat.card_fun,
    Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem card_golayC : Nat.card golayC = 4096 := by
  have h : Nat.card golayC = Nat.card CFSG.Monster.Code.C := by
    refine Nat.card_congr ?_
    exact
      { toFun := fun x => ⟨Multiplicative.toAdd x.1, x.2⟩
        invFun := fun x => ⟨Multiplicative.ofAdd x.1, x.2⟩
        left_inv := fun x => rfl
        right_inv := fun x => rfl }
  rw [h, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
    CFSG.Monster.Code.finrank_C]
  norm_num

theorem card_zpowers_allOnes_le : Nat.card (Subgroup.zpowers (allOnes 24)) ≤ 2 := by
  rw [Nat.card_zpowers]
  refine Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one ?_)
  apply Multiplicative.toAdd.injective
  funext i
  simp [allOnes]
  decide +revert

theorem index_ker_le_two {M N : Type*} [Group M] [Group N] [Finite N] (φ : M →* N)
    (hN : Nat.card N ≤ 2) : φ.ker.index ≤ 2 := by
  rw [Subgroup.index_ker]
  exact (Subgroup.card_le_card_group φ.range).trans hN

theorem card_mul_index_ge_half {M : Type*} [Group M] [Finite M] (S K : Subgroup M)
    (hK : K.index ≤ 2) : Nat.card S ≤ 2 * Nat.card (S ⊓ K : Subgroup M) := by
  have h1 := Subgroup.card_mul_index (S ⊓ K)
  have h2 := Subgroup.card_mul_index S
  have h3 : (S ⊓ K).index ≤ S.index * K.index := Subgroup.index_inf_le
  have hSpos : 0 < S.index := Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
  refine Nat.le_of_mul_le_mul_right ?_ hSpos
  calc Nat.card S * S.index = Nat.card M := h2
    _ = Nat.card (S ⊓ K : Subgroup M) * (S ⊓ K).index := h1.symm
    _ ≤ Nat.card (S ⊓ K : Subgroup M) * (S.index * 2) :=
        Nat.mul_le_mul_left _ (h3.trans (Nat.mul_le_mul_left _ hK))
    _ = (2 * Nat.card (S ⊓ K : Subgroup M)) * S.index := by ring

theorem card_multiplicative_zmod_two : Nat.card (Multiplicative (ZMod 2)) = 2 := by
  rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 2) ≃ ZMod 2), Nat.card_zmod]

theorem pairKer_index_le (x y : Fin 24) : (pairKer x y).index ≤ 2 := by
  let φ : PermMod 24 →* Multiplicative (ZMod 2) := AddMonoidHom.toMultiplicative
    (Pi.evalAddMonoidHom (fun _ : Fin 24 => ZMod 2) x +
      Pi.evalAddMonoidHom (fun _ : Fin 24 => ZMod 2) y)
  have h : pairKer x y = φ.ker := by
    ext z
    simp [pairKer, φ]
    rw [← ofAdd_add, ofAdd_eq_one]
  rw [h]
  exact index_ker_le_two φ card_multiplicative_zmod_two.le

theorem coreMod_index_le : (coreMod 24).index ≤ 2 := by
  let φ : PermMod 24 →* Multiplicative (ZMod 2) := AddMonoidHom.toMultiplicative
    (∑ i : Fin 24, Pi.evalAddMonoidHom (fun _ : Fin 24 => ZMod 2) i)
  have h : coreMod 24 = φ.ker := by
    ext z
    simp [mem_coreMod, φ]
  rw [h]
  exact index_ker_le_two φ card_multiplicative_zmod_two.le

theorem card_coreMod_ge : 2 ^ 23 ≤ Nat.card (coreMod 24) := by
  have h := card_mul_index_ge_half (⊤ : Subgroup (PermMod 24)) (coreMod 24) coreMod_index_le
  rw [top_inf_eq, Subgroup.card_top, card_permMod] at h
  omega

theorem card_golayC_inf_pairKer_ge (x y : Fin 24) :
    2048 ≤ Nat.card (golayC ⊓ pairKer x y : Subgroup (PermMod 24)) := by
  have h := card_mul_index_ge_half golayC (pairKer x y) (pairKer_index_le x y)
  rw [card_golayC] at h
  omega

theorem sec_le_card_mul {V : Type*} [CommGroup V] [Finite V] {D : FFModel} [Finite D.Amb]
    {H : Subgroup (MulAut V)} {U Z : Subgroup V} (h : D.Realizes H U Z) :
    Nat.card D.sec ≤ Nat.card U * Nat.card D.ker :=
  (card_le_quot_mul D.sec D.ker).trans (Nat.mul_le_mul_right _ (realizes_card_le h))

instance finite_golaySec_amb (Γ : Subgroup (Equiv.Perm (Fin 24))) (n d : Subgroup (PermMod 24)) :
    Finite (FFModel.golaySec Γ n d).Amb :=
  inferInstanceAs (Finite (PermMod 24))

variable {V : Type*} [CommGroup V] [Finite V] {H : Subgroup (MulAut V)}

theorem golay_sec_le {Γ : Subgroup (Equiv.Perm (Fin 24))} {n d : Subgroup (PermMod 24)}
    (h : (FFModel.golaySec Γ n d).Realizes H ⊤ ⊥) : Nat.card n ≤ Nat.card V * Nat.card d := by
  have h1 : Nat.card n ≤ Nat.card (⊤ : Subgroup V) * Nat.card d := sec_le_card_mul h
  rwa [Subgroup.card_top] at h1

theorem rowM24Code_card (h : MathieuCode24 (V := V) H ⊤ ⊥) : 2048 ≤ Nat.card V := by
  have h1 := golay_sec_le h
  have h2 := Nat.mul_le_mul_left (Nat.card V) card_zpowers_allOnes_le
  rw [card_golayC] at h1
  omega

theorem rowM22Code_card (h : MathieuCode22 (V := V) H ⊤ ⊥) : 1024 ≤ Nat.card V := by
  obtain ⟨x, y, -, h⟩ := h
  have h1 := golay_sec_le h
  have h2 := Nat.mul_le_mul_left (Nat.card V) card_zpowers_allOnes_le
  have h3 := card_golayC_inf_pairKer_ge x y
  omega

theorem rowM24Cocode_card (h : MathieuCocode24 (V := V) H ⊤ ⊥) : 2048 ≤ Nat.card V := by
  have h1 := golay_sec_le h
  have h3 := card_coreMod_ge
  have h4 : Nat.card V * Nat.card golayC ≤ Nat.card V * 4096 := by rw [card_golayC]
  omega

end Golay

section Tensor

theorem card_matrix_fin (m : ℕ) (K : Type) [Finite K] :
    Nat.card (Matrix (Fin m) (Fin m) K) = Nat.card K ^ (m * m) := by
  rw [Matrix, Nat.card_fun, Nat.card_fun]
  simp [Nat.card_eq_fintype_card, ← pow_mul]

variable {V : Type*} [CommGroup V] [Finite V] {H : Subgroup (MulAut V)}

instance finite_tensorPair_amb {m : ℕ} {K : Type} [Field K] [Finite K]
    (Γ₁ Γ₂ : Subgroup (Matrix.GeneralLinearGroup (Fin m) K)) :
    Finite (tensorPairModel Γ₁ Γ₂).Amb :=
  inferInstanceAs (Finite (Multiplicative (Matrix (Fin m) (Fin m) K)))

theorem rowTensorPair_card {m : ℕ} {K : Type} [Field K] [Finite K]
    {Γ₁ Γ₂ : Subgroup (Matrix.GeneralLinearGroup (Fin m) K)}
    (h : (tensorPairModel Γ₁ Γ₂).Realizes H ⊤ ⊥) :
    Nat.card K ^ (m * m) ≤ Nat.card V := by
  have h1 := sec_le_card_mul h
  have h2 : Nat.card (tensorPairModel Γ₁ Γ₂).sec = Nat.card K ^ (m * m) := by
    show Nat.card (⊤ : Subgroup (Multiplicative (Matrix (Fin m) (Fin m) K))) = _
    rw [Subgroup.card_top, Nat.card_congr (Multiplicative.toAdd :
      Multiplicative (Matrix (Fin m) (Fin m) K) ≃ Matrix (Fin m) (Fin m) K),
      card_matrix_fin]
  have h3 : Nat.card (tensorPairModel Γ₁ Γ₂).ker = 1 := Subgroup.card_bot
  rw [h2, h3, Subgroup.card_top] at h1
  simpa using h1

theorem card_hermSub_ge (a : ℕ) (K : Type) [Field K] [CharP K 2] [Finite K] :
    64 ≤ Nat.card (hermSub a (Fin 3) K) := by
  let c : Fin 3 → Fin 3 → Fin 6 := ![![0, 3, 4], ![3, 1, 5], ![4, 5, 2]]
  have hc : ∀ i j, c i j = c j i := by decide
  have hcs : ∀ t : Fin 6, ∃ i j, c i j = t := by decide
  let ψ : ZMod 2 →+* K := ZMod.castHom (dvd_refl 2) K
  let X : (Fin 6 → ZMod 2) → Matrix (Fin 3) (Fin 3) K := fun s => Matrix.of fun i j => ψ (s (c i j))
  have hfix : ∀ v : ZMod 2, (ψ v) ^ 2 ^ a = ψ v := by
    intro v
    have hv : v = 0 ∨ v = 1 := by revert v; decide
    rcases hv with rfl | rfl
    · rw [map_zero]; exact zero_pow (pow_ne_zero _ (by norm_num))
    · rw [map_one, one_pow]
  have hmem : ∀ s, X s ∈ hermSub a (Fin 3) K := by
    intro s
    show (frobPow a (X s))ᵀ = X s
    ext i j
    simp [frobPow, X, hfix, hc i j]
  let f : (Fin 6 → ZMod 2) → hermSub a (Fin 3) K := fun s => ⟨Multiplicative.ofAdd (X s), hmem s⟩
  have hf : Function.Injective f := by
    intro s s' h
    have h' : X s = X s' := by
      have := congrArg (fun z : hermSub a (Fin 3) K =>
        Multiplicative.toAdd (z : Multiplicative (Matrix (Fin 3) (Fin 3) K))) h
      simpa [f] using this
    funext t
    obtain ⟨i, j, hij⟩ := hcs t
    have := congrFun (congrFun h' i) j
    simp only [X, Matrix.of_apply, hij] at this
    exact ψ.injective this
  have := Nat.card_le_card_of_injective f hf
  rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin] at this
  simpa using this

instance finite_twistTensor_amb {K : Type} [Field K] [Finite K] [CharP K 2] (a : ℕ)
    (Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 3) K)) :
    Finite (FFModel.twistTensor a Γ).Amb :=
  inferInstanceAs (Finite (Multiplicative (Matrix (Fin 3) (Fin 3) K)))

theorem rowTwist_card {a : ℕ} {K : Type} [Field K] [CharP K 2] [Finite K]
    (h : (FFModel.twistTensor a (CFSG.Assembly.LowTwoRank.StatedSL 3 K)).Realizes H ⊤ ⊥) :
    64 ≤ Nat.card V := by
  have h1 := sec_le_card_mul h
  have h3 : Nat.card (FFModel.twistTensor a
      (CFSG.Assembly.LowTwoRank.StatedSL 3 K)).ker = 1 := Subgroup.card_bot
  have h4 : Nat.card (FFModel.twistTensor a
      (CFSG.Assembly.LowTwoRank.StatedSL 3 K)).sec = Nat.card (hermSub a (Fin 3) K) :=
    rfl
  rw [h4, h3, Subgroup.card_top] at h1
  have := card_hermSub_ge a K
  omega

end Tensor

section Rows

variable {G : Type} [Group G] [Finite G] (T L I : Subgroup G) [IsMulCommutative ↥(fsuV T I)]

omit [Finite G] [IsMulCommutative ↥(fsuV T I)] in
theorem card_fsuV_le (hG : Gen4 G) (hel : IsElemAbelian 2 (fsuV T I)) :
    Nat.card ↥(fsuV T I) ≤ 16 := by
  have := SectionalTwoRankLE.card_le_of_elementary hG (fsuV T I) hel
  simpa using this

theorem not_rows_of_gen4 (hG : Gen4 G) (hel : IsElemAbelian 2 (fsuV T I)) :
    (¬ ∃ n : ℕ, Row711L3Nine T L I n) ∧ ¬ Row711M22Code T L I ∧ ¬ Row711M24Code T L I ∧
      ¬ Row711M24Cocode T L I ∧ (∀ n : ℕ, ¬ Row711OmegaPlus T L I n) ∧
      ¬ Row711L3Wreath T L I := by
  have hle := card_fsuV_le T I hG hel
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨n, -, K, _, _, _, -, h⟩
    have := rowTwist_card h
    omega
  · intro h
    have := rowM22Code_card h
    omega
  · intro h
    have := rowM24Code_card h
    omega
  · intro h
    have := rowM24Cocode_card h
    omega
  · rintro n ⟨-, hn, K, _, _, hK, h⟩
    have h1 := rowTensorPair_card h
    rw [hK] at h1
    have h2 : 2 ^ 8 ≤ (2 ^ n) ^ (2 * 2) := by
      rw [← pow_mul]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · rintro ⟨-, h⟩
    have h1 := rowTensorPair_card h
    have h2 : Nat.card (ZMod 2) ^ (3 * 3) = 512 := by rw [Nat.card_zmod]; norm_num
    omega

end Rows

end CFSG.GH74.QTGen4.Ch7
