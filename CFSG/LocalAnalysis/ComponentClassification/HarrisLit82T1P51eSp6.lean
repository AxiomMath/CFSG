module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51eDefs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Spin410RC
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10LinRecog
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitIsoTransport
public import CFSG.LieType.Classical.SteinbergBLSymplectic
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S73B

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P51e

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf

variable {K : Type} [Field K]

@[expose] def spD (K : Type) [Field K] : Matrix (Fin 3) (Fin 3) K := diagonal ![-1, 1, 1]

theorem spD_mul_self : spD K * spD K = 1 := by
  rw [spD, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  ext i
  fin_cases i <;> simp

theorem spD_transpose : (spD K)ᵀ = spD K := diagonal_transpose _

@[expose] def spInvMat (K : Type) [Field K] : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K :=
  fromBlocks (spD K) 0 0 (spD K)

theorem spInvMat_mul_self : spInvMat K * spInvMat K = 1 := by
  rw [spInvMat, fromBlocks_multiply, spD_mul_self]
  simp [fromBlocks_one]

@[expose] def spInvGL (K : Type) [Field K] : GL (Fin 3 ⊕ Fin 3) K :=
  ⟨spInvMat K, spInvMat K, spInvMat_mul_self, spInvMat_mul_self⟩

theorem spInvGL_mem : spInvGL K ∈ StatedSp 3 K := by
  rw [LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff]
  change (spInvMat K)ᵀ * fromBlocks 0 1 (-1) 0 * spInvMat K = fromBlocks 0 1 (-1) 0
  rw [spInvMat, fromBlocks_transpose, spD_transpose, fromBlocks_multiply, fromBlocks_multiply]
  simp [spD_mul_self]

@[expose] def spInv (K : Type) [Field K] : StatedSp 3 K := ⟨spInvGL K, spInvGL_mem⟩

@[expose] def spS (x : K × K × K × K) : Matrix (Fin 3) (Fin 3) K :=
  !![x.1, 0, 0; 0, x.2.1, x.2.2.2; 0, x.2.2.2, x.2.2.1]

theorem spS_add (x y : K × K × K × K) : spS (x + y) = spS x + spS y := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [spS]

theorem spS_zero : spS (0 : K × K × K × K) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [spS]

theorem spS_transpose (x : K × K × K × K) : (spS x)ᵀ = spS x := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [spS]

theorem spD_mul_spS_mul_spD (x : K × K × K × K) : spD K * spS x * spD K = spS x := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [spD, spS, Matrix.mul_apply, Fin.sum_univ_three]

@[expose] def uMat (x : K × K × K × K) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K :=
  fromBlocks 1 (spS x) 0 1

theorem uMat_mul (x y : K × K × K × K) : uMat x * uMat y = uMat (x + y) := by
  rw [uMat, uMat, uMat, fromBlocks_multiply, spS_add]
  simp [add_comm]

theorem uMat_zero : uMat (0 : K × K × K × K) = 1 := by
  rw [uMat, spS_zero, fromBlocks_one]

@[expose] def uGL (x : K × K × K × K) : GL (Fin 3 ⊕ Fin 3) K :=
  ⟨uMat x, uMat (-x), by rw [uMat_mul, add_neg_cancel, uMat_zero],
    by rw [uMat_mul, neg_add_cancel, uMat_zero]⟩

theorem uGL_mem (x : K × K × K × K) : uGL x ∈ StatedSp 3 K := by
  rw [LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff]
  change (uMat x)ᵀ * fromBlocks 0 1 (-1) 0 * uMat x = fromBlocks 0 1 (-1) 0
  rw [uMat, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply, spS_transpose]
  simp

@[expose] def uHom (K : Type) [Field K] : Multiplicative (K × K × K × K) →* StatedSp 3 K where
  toFun x := ⟨uGL x.toAdd, uGL_mem x.toAdd⟩
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    exact uMat_zero
  map_mul' x y := by
    apply Subtype.ext
    apply Units.ext
    exact (uMat_mul x.toAdd y.toAdd).symm

theorem uHom_injective : Function.Injective (uHom K) := by
  intro x y h
  have h1 := congrArg (fun g : StatedSp 3 K =>
    ((g : GL (Fin 3 ⊕ Fin 3) K) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K)) h
  change uMat x.toAdd = uMat y.toAdd at h1
  have h2 : spS x.toAdd = spS y.toAdd := by
    have := congrArg Matrix.toBlocks₁₂ h1
    simpa [uMat] using this
  have e00 := congrFun (congrFun h2 0) 0
  have e11 := congrFun (congrFun h2 1) 1
  have e22 := congrFun (congrFun h2 2) 2
  have e12 := congrFun (congrFun h2 1) 2
  simp [spS] at e00 e11 e22 e12
  apply Multiplicative.toAdd.injective
  ext <;> assumption

theorem range_uHom_le_centralizer :
    (uHom K).range ≤ centralizer ({spInv K} : Set (StatedSp 3 K)) := by
  rintro _ ⟨x, rfl⟩
  rw [mem_centralizer_singleton_iff]
  apply Subtype.ext
  apply Units.ext
  change uMat x.toAdd * spInvMat K = spInvMat K * uMat x.toAdd
  rw [spInvMat, uMat, fromBlocks_multiply, fromBlocks_multiply]
  have h := spD_mul_spS_mul_spD x.toAdd
  have h' : spD K * spS x.toAdd = spS x.toAdd * spD K := by
    calc spD K * spS x.toAdd = spD K * spS x.toAdd * (spD K * spD K) := by
          rw [spD_mul_self, Matrix.mul_one]
      _ = spS x.toAdd * spD K := by rw [← Matrix.mul_assoc, h]
  simp [h']

theorem card_range_uHom [Finite K] : Nat.card (uHom K).range = Nat.card K ^ 4 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective (uHom_injective (K := K))).toEquiv]
  change Nat.card (K × K × K × K) = _
  simp only [Nat.card_prod]
  ring

theorem spInv_sq : spInv K ^ 2 = 1 := by
  rw [pow_two]
  apply Subtype.ext
  apply Units.ext
  exact spInvMat_mul_self

theorem spInv_not_mem_center (h2 : (2 : K) ≠ 0) : spInv K ∉ center (StatedSp 3 K) := by
  intro h
  rw [LieType.Universal.Symplectic.center_eq, Subgroup.mem_subgroupOf] at h
  obtain ⟨c, hc⟩ := h
  have hm : Matrix.scalar (Fin 3 ⊕ Fin 3) (c : K) = spInvMat K := by
    have := congrArg Units.val hc
    exact this
  have e0 : spInvMat K (Sum.inl 0) (Sum.inl 0) = -1 := by simp [spInvMat, spD]
  have e1 : spInvMat K (Sum.inl 1) (Sum.inl 1) = 1 := by simp [spInvMat, spD]
  have h0 := congrFun (congrFun hm (Sum.inl 0)) (Sum.inl 0)
  have h1 := congrFun (congrFun hm (Sum.inl 1)) (Sum.inl 1)
  rw [Matrix.scalar_apply, Matrix.diagonal_apply_eq, e0] at h0
  rw [Matrix.scalar_apply, Matrix.diagonal_apply_eq, e1] at h1
  apply h2
  linear_combination h0 - h1

theorem spInv_ne_one (h2 : (2 : K) ≠ 0) : spInv K ≠ 1 := fun h =>
  spInv_not_mem_center h2 (h ▸ one_mem _)

theorem card_center_statedSp_three [Finite K] (hodd : Odd (Nat.card K)) :
    Nat.card (center (StatedSp 3 K)) = 2 := by
  rw [LieType.Universal.Symplectic.center_eq]
  have h1 : Nat.card ((StatedScalars (Fin 3 ⊕ Fin 3) K).subgroupOf (StatedSp 3 K)) =
      Nat.card ↥(StatedSp 3 K ⊓ StatedScalars (Fin 3 ⊕ Fin 3) K) := by
    rw [← Subgroup.card_map_of_injective (StatedSp 3 K).subtype_injective,
      Subgroup.subgroupOf_map_subtype, inf_comm]
  rw [h1, LieType.Classical.card_statedSp_inf_statedScalars (by norm_num),
    LieType.Classical.card_sq_eq_one_units]
  obtain ⟨k, hk⟩ := hodd
  rw [hk, Nat.add_sub_cancel]
  exact Nat.gcd_eq_left (dvd_mul_right 2 k)

theorem two_ne_zero_of_card {F : Type} [Field F] [Finite F] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hF : Nat.card F = p ^ f) : (2 : F) ≠ 0 := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype F := Fintype.ofFinite F
  have : CharP F p :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hF)
  intro h0
  have h1 : ((2 : ℕ) : F) = 0 := by exact_mod_cast h0
  have := (CharP.cast_eq_zero_iff F p 2).1 h1
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)

theorem noSpin7_of_mulEquiv_statedSp {L : Type} [Group L] [Finite K] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) (e : StatedSp 3 K ≃* L) :
    NoSpin7 p L := by
  intro r hr _ hLM
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite L := Finite.of_equiv _ e.toEquiv
  have hodd : Odd (Nat.card K) := hK ▸ (hp.odd_of_ne_two hp2).pow
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · have h1 : Nat.card K = 1 := by rw [hK, h0, pow_zero]
      have := Finite.one_lt_card (α := K)
      omega
    · exact h0
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_card hp hp2 hK
  have hq : IsQuasisimple L := by
    refine LocalCores.isQuasisimple_of_mulEquiv e
      (LieType.Universal.Symplectic.isQuasisimple 3 K (by norm_num) ?_)
    rcases Nat.lt_or_ge (Nat.card K) 4 with h4 | h4
    · have h3 : Nat.card K = 3 := by
        obtain ⟨k, hk⟩ := hodd
        have := Finite.one_lt_card (α := K)
        omega
      exact Or.inr (Or.inl ⟨h3, by norm_num⟩)
    · exact Or.inl (Or.inr h4)
  have hZL : Nat.card (center L) = 2 := by
    rw [← card_center_statedSp_three hodd]
    exact (Nat.card_congr ((MulEquiv.subgroupCongr (Subgroup.map_center_eq e)).symm.trans
      ((center (StatedSp 3 K)).equivMapOfInjective e.toMonoidHom e.injective).symm).toEquiv)
  have hadm : StatedLieAdmissible .PSp 3 p f := ⟨hp, hf, by norm_num, by simp⟩
  have hLMsp : Blueprint.LieModel (L ⧸ center L) .PSp 3 p f := by
    refine Or.inl ⟨by decide, hadm, K, inferInstance, inferInstance, hK, ⟨?_⟩⟩
    exact (QuotientGroup.congr (center L) (center (StatedSp 3 K)) e.symm
      (Subgroup.map_center_eq e.symm)).trans
      (LieType.Universal.Symplectic.centerQuotientEquiv 3 K)
  have hv1 := (CatLeafProof.X10Lin.lieOrder_of_lieModel_classical
    (Or.inr (Or.inr (Or.inl rfl))) hp2 (by norm_num) hLMsp).2
  have hv2 := (CatLeafProof.X10Lin.lieOrder_of_lieModel_classical
    (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hp2 (by norm_num) hLM).2
  have hfr : f = r := by
    rw [hv1] at hv2
    change 9 * f = 9 * r at hv2
    omega
  subst hfr
  have hs1 : e (spInv K) ≠ 1 := fun h => spInv_ne_one h2 (e.injective (h.trans e.map_one.symm))
  have hs2 : orderOf (e (spInv K)) = 2 :=
    orderOf_eq_prime (by rw [← map_pow, spInv_sq, map_one]) hs1
  have hsZ : e (spInv K) ∉ center L := by
    intro h
    apply spInv_not_mem_center h2
    rw [mem_center_iff]
    intro g
    apply e.injective
    rw [map_mul, map_mul]
    exact mem_center_iff.1 h (e g)
  obtain ⟨K', _, _, e', hK', he'⟩ : ∃ (K' : Type) (_ : Field K') (_ : Finite K')
      (e' : L ≃* spinGroup (LieType.Universal.Spin.quadOdd 3 K')),
      Nat.card K' = p ^ f ∧ e' (e (spInv K)) = tSeven K' := by
    rcases Nat.lt_or_ge (p ^ f) 5 with h5 | h5
    · have h3 : p ^ f = 3 := by
        have h1 : p ≤ p ^ f := Nat.le_self_pow (by omega) p
        have h2 : p ^ f ≠ 4 := fun h => by
          obtain ⟨k, hk⟩ := hK ▸ hodd
          omega
        have := hp.two_le
        omega
      obtain ⟨K', i1, i2, e', hK', he'⟩ :=
        exists_mulEquiv_spinSeven_three h3 ⟨hq, hZL, hLM⟩ hs2 hsZ
      exact ⟨K', i1, i2, e', hK'.trans h3.symm, he'⟩
    · obtain ⟨K', i1, i2, e', hK', -, -, he'⟩ :=
        exists_mulEquiv_spinSeven h5 ⟨hq, hZL, hLM⟩ hs2 hsZ
      exact ⟨K', i1, i2, e', hK', he'⟩
  have h2' : (2 : K') ≠ 0 := two_ne_zero_of_card hp hp2 hK'
  set E := e.trans e' with hE
  have hEs : E (spInv K) = tSeven K' := by rw [hE, MulEquiv.trans_apply, he']
  have hC : Nat.card (centralizer ({spInv K} : Set (StatedSp 3 K))) =
      Nat.card (centralizer
        ({tSeven K'} : Set (spinGroup (LieType.Universal.Spin.quadOdd 3 K')))) := by
    rw [← hEs, ← FooteLit.map_centralizer_singleton_mulEquiv E (spInv K),
      Subgroup.card_map_of_injective E.injective]
  have hd1 : Nat.card K ^ 4 ∣ Nat.card (centralizer ({spInv K} : Set (StatedSp 3 K))) := by
    rw [← card_range_uHom]
    exact Subgroup.card_dvd_of_le range_uHom_le_centralizer
  have hd2 := card_centralizer_tSeven_dvd h2'
  rw [← hC] at hd2
  have hd := hd1.trans hd2
  rw [hK', ← hK] at hd
  set q := Nat.card K with hq
  have hq2 : 2 ≤ q := Finite.one_lt_card
  have hpq : p ∣ q := by
    rw [hK]
    exact dvd_pow_self p (by omega)
  have hcop : Nat.Coprime p (8 * (q ^ 2 - 1) ^ 3) := by
    refine Nat.Coprime.mul_right ?_ (Nat.Coprime.pow_right 3 ?_)
    · rw [show (8 : ℕ) = 2 ^ 3 by norm_num]
      exact Nat.Coprime.pow_right 3 ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
    · refine (Nat.Prime.coprime_iff_not_dvd hp).2 fun h => ?_
      have h1 : p ∣ q ^ 2 := dvd_pow hpq (by norm_num)
      have h3 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
      have h4 : p ∣ q ^ 2 - (q ^ 2 - 1) := Nat.dvd_sub h1 h
      rw [Nat.sub_sub_self h3] at h4
      exact hp.ne_one (Nat.dvd_one.1 h4)
  have hcop' : Nat.Coprime (q ^ 4) (8 * (q ^ 2 - 1) ^ 3) := by
    have h1 : q ^ 4 = p ^ (f * 4) := by rw [hK, ← pow_mul]
    rw [h1]
    exact Nat.Coprime.pow_left _ hcop
  have hd' : q ^ 4 ∣ q ^ 3 * (8 * (q ^ 2 - 1) ^ 3) := by
    rw [show q ^ 3 * (8 * (q ^ 2 - 1) ^ 3) = 8 * q ^ 3 * (q ^ 2 - 1) ^ 3 by ring]
    exact hd
  have h3pos : 0 < q ^ 3 := pow_pos (by omega) 3
  have h43 := Nat.le_of_dvd h3pos (hcop'.dvd_of_dvd_mul_right hd')
  have : q ^ 4 = q * q ^ 3 := by ring
  nlinarith

end CFSG.ComponentClassification.HarrisLit.T1.P51e
