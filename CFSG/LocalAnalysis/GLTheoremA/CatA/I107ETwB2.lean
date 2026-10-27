module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107LCore

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I107E

open CFSG.Open CFSG.Assembly

theorem pRank_two_ge {G : Type} [Group G] [Finite G] (E : Subgroup G) (hE : IsElemAbelian 2 E) {k : ℕ}
    (hk : Nat.card E = 2 ^ k) : k ≤ CFSG.Open.pRank 2 (⊤ : Subgroup G) := by
  apply le_csSup
  · refine ⟨Nat.card G, ?_⟩
    rintro m ⟨E', -, -, hE'⟩
    have h1 : Nat.card E' ≤ Nat.card G := Subgroup.card_le_card_group E'
    rw [hE'] at h1
    have h3 : m < 2 ^ m := Nat.lt_two_pow_self
    omega
  · exact ⟨E, le_top, hE, hk⟩

section Suzuki

variable {K : Type} [Field K]

@[expose] def szM (a : ℕ) (v : K) : Matrix (Fin 4) (Fin 4) K :=
  !![1, 0, 0, 0; 0, 1, 0, 0; v, 0, 1, 0; v ^ 2 ^ (a + 1), v, 0, 1]

@[expose] def szW : Matrix (Fin 4) (Fin 4) K :=
  !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0]

theorem szM_mem (a : ℕ) (v : K) : szM a v ∈ LargeEvenSzGens a K := by
  refine Or.inl ⟨0, v, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [szM]

theorem szW_mem (a : ℕ) : (szW : Matrix (Fin 4) (Fin 4) K) ∈ LargeEvenSzGens a K :=
  Or.inr (Or.inr rfl)

theorem szM_mul_self {a : ℕ} {h2 : (2 : K) = 0} (v : K) : szM a v * szM a v = 1 := by
  have hv : ∀ x : K, x + x = 0 := fun x => by rw [← two_mul, h2, zero_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [szM, Matrix.mul_apply, Fin.sum_univ_four, hv]

theorem szM_mul [CharP K 2] (a : ℕ) (v w : K) : szM a v * szM a w = szM a (v + w) := by
  have hf : (v + w) ^ 2 ^ (a + 1) = v ^ 2 ^ (a + 1) + w ^ 2 ^ (a + 1) := add_pow_char_pow v w 2 (a + 1)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [szM, Matrix.mul_apply, Fin.sum_univ_four, hf] <;> ring

theorem szW_mul_self : (szW : Matrix (Fin 4) (Fin 4) K) * szW = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [szW, Matrix.mul_apply, Fin.sum_univ_four]

@[expose] def szUnit (a : ℕ) (h2 : (2 : K) = 0) (v : K) : Matrix.GeneralLinearGroup (Fin 4) K :=
  Units.mk (szM a v) (szM a v) (szM_mul_self (a := a) (h2 := h2) v) (szM_mul_self (a := a) (h2 := h2) v)

@[expose] def szWUnit : Matrix.GeneralLinearGroup (Fin 4) K :=
  Units.mk szW szW szW_mul_self szW_mul_self

theorem szUnit_mul [CharP K 2] (a : ℕ) (h2 : (2 : K) = 0) (v w : K) :
    szUnit a h2 (v + w) = szUnit a h2 v * szUnit a h2 w :=
  Units.ext (szM_mul a v w).symm

@[expose] def szSub (a : ℕ) (h2 : (2 : K) = 0) (v : K) : LargeEvenSzGroup a K :=
  ⟨szUnit a h2 v, Subgroup.subset_closure (szM_mem a v)⟩

theorem szSub_mul [CharP K 2] (a : ℕ) (h2 : (2 : K) = 0) (v w : K) :
    szSub a h2 (v + w) = szSub a h2 v * szSub a h2 w :=
  Subtype.ext (szUnit_mul a h2 v w)

theorem szSub_eq_zero_of_mem_center (a : ℕ) (h2 : (2 : K) = 0) (v : K)
    (hz : szSub a h2 v ∈ Subgroup.center (LargeEvenSzGroup a K)) : v = 0 := by
  rw [Subgroup.mem_center_iff] at hz
  have h := congrArg (fun g : LargeEvenSzGroup a K =>
    ((g : Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K))
    (hz ⟨szWUnit, Subgroup.subset_closure (szW_mem a)⟩)
  have h00 := congrFun (congrFun h 0) 0
  simp [szSub, szWUnit, szUnit, szM, szW, Matrix.mul_apply, Fin.sum_univ_four] at h00
  exact h00

end Suzuki

theorem szQuot_pRank {K : Type} [Field K] [Finite K] {a n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    [Finite (LargeEvenCenterQuot (LargeEvenSzGroup a K))] :
    n ≤ CFSG.Open.pRank 2 (⊤ : Subgroup (LargeEvenCenterQuot (LargeEvenSzGroup a K))) := by
  have h2 : (2 : K) = 0 := CFSG.LocalAnalysis.GLTheoremA.I107G.two_eq_zero_of_card hn hK
  haveI : CharP K 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).2 (by exact_mod_cast h2)
  have hA : ∀ x : K, x + x = 0 := fun x => by rw [← two_mul, h2, zero_mul]
  let f : Multiplicative K →* LargeEvenSzGroup a K :=
    MonoidHom.mk' (fun x => szSub a h2 (Multiplicative.toAdd x))
      (fun x y => by rw [toAdd_mul, szSub_mul])
  let Fq : Multiplicative K →* LargeEvenCenterQuot (LargeEvenSzGroup a K) :=
    (LargeEvenCenterMk (LargeEvenSzGroup a K)).comp f
  have hinj : Function.Injective Fq := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx' : (QuotientGroup.mk (szSub a h2 (Multiplicative.toAdd x)) :
        LargeEvenSzGroup a K ⧸ Subgroup.center (LargeEvenSzGroup a K)) = 1 := hx
    have hz := (QuotientGroup.eq_one_iff _).1 hx'
    have hv := szSub_eq_zero_of_mem_center a h2 _ hz
    exact Multiplicative.toAdd.injective (by rw [hv, toAdd_one])
  have hcard : Nat.card Fq.range = 2 ^ n := by
    rw [← hK]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm.trans (Nat.card_congr Multiplicative.toAdd)
  have hE : IsElemAbelian 2 Fq.range := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨p, hp⟩ := MonoidHom.mem_range.1 x.2
      obtain ⟨q, hq⟩ := MonoidHom.mem_range.1 y.2
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rw [← hp, ← hq, ← map_mul, ← map_mul, mul_comm]
    · obtain ⟨p, rfl⟩ := MonoidHom.mem_range.1 hx
      have hsq : p ^ 2 = 1 := by
        apply Multiplicative.toAdd.injective
        rw [toAdd_pow, toAdd_one, two_nsmul, hA]
      rw [← map_pow, hsq, map_one]
  exact pRank_two_ge Fq.range hE hcard

theorem twoRankLow_twB2_holds (S : Type) [Group S] [Finite S] (lab : GLALabel) (hS : IsSimpleGroup S)
    (hrk : Rk2IsLabel S lab) (ht : lab.tag = .twB2) :
    twoRankLow107 lab ≤ CFSG.Open.pRank 2 (⊤ : Subgroup S) := by
  have hlab := rk2IsLabel_inLambda2 hrk
  have hraw := rk2IsLabel_rawDatum hrk
  obtain ⟨tag, rank, n⟩ := lab
  obtain rfl : tag = .twB2 := ht
  have hodd : Odd n := by
    have h := hlab.2
    dsimp only at h
    exact h.2.1
  have hn1 : 1 ≤ n := hlab.1
  dsimp only [GLARawDatum, CFSG.Assembly.LargeEvenRawDatum, CFSG.Assembly.LargeEvenRecipeSuzuki] at hraw
  obtain ⟨K, hf, hfin, hK, hQ⟩ := hraw
  obtain ⟨hsR, hna, ⟨θ⟩⟩ := hQ
  have ha : 2 * ((n - 1) / 2) + 1 = n := by
    obtain ⟨m, rfl⟩ := hodd
    omega
  rw [ha] at hK
  haveI : Finite (LargeEvenCenterQuot (LargeEvenSzGroup ((n - 1) / 2) K)) :=
    Finite.of_equiv _ θ.toEquiv
  rw [CFSG.LocalAnalysis.GLTheoremA.I107L.pRank_eq_of_quotient θ hna]
  exact szQuot_pRank hn1 hK

end CFSG.LocalAnalysis.GLTheoremA.I107E

end
