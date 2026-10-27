module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerA4UKern
public import CFSG.RankThree.PartOne.KF.UnitaryDiag
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerA4Lift

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open Matrix CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.GLTheoremA.KD264LieA4 CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.RankThree.PartOne.KCUnitaryModel

variable {p f : ℕ} {K : Type} [Field K]

theorem mem_DiagSU_of_diag [Finite K] (h : UnitaryFieldData p f K) (hdiv : 3 ∣ p ^ f + 1)
    (y : unitarySU p f K 4)
    (hoff : ∀ i j : Fin 4, i ≠ j → ((y : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) i j = 0)
    (hcube : ∀ i : Fin 4, ((y : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) i i ^ 3 = 1) :
    y ∈ DiagSU h hdiv := by
  set Y : Matrix (Fin 4) (Fin 4) K := ((y : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) with hY
  have hy0 : ∀ i, Y i i ≠ 0 := fun i hz => by
    have := hcube i
    rw [hz] at this
    norm_num at this
  let d : Fin 4 → Kˣ := fun i => Units.mk0 _ (hy0 i)
  have hdiag : Y = Matrix.diagonal (fun i => Y i i) := by
    ext a b
    by_cases hab : a = b
    · subst hab
      simp
    · rw [hoff a b hab, Matrix.diagonal_apply_ne _ hab]
  have hdet : ∏ i, Y i i = 1 := by
    have hd : Y.det = 1 := ((mem_unitarySU_iff h).mp y.2).1
    rw [hdiag, Matrix.det_diagonal] at hd
    exact hd
  have hprod : ∏ i, d i = 1 := by
    apply Units.ext
    rw [Units.coe_prod]
    simpa [d] using hdet
  have hdg : d ∈ dGroup K :=
    ⟨fun i => (mem_mu3 K).mpr (by simpa [d] using hcube i), hprod⟩
  refine MonoidHom.mem_range.mpr ⟨⟨d, hdg⟩, ?_⟩
  apply Subtype.ext
  apply Units.ext
  show diagM K d = Y
  rw [hdiag]
  unfold diagM
  congr 1

@[expose] def conjSU (h : UnitaryFieldData p f K) (Q : GL (Fin 4) K)
    (hQ : Q ∈ primeFormUnitary h (idGram K 4)) : unitarySU p f K 4 ≃* unitarySU p f K 4 where
  toFun x := ⟨Q * x * Q⁻¹, CFSG.RankThree.PartOne.KFU.conj_mem_unitarySU h hQ x.2⟩
  invFun x := ⟨Q⁻¹ * x * Q⁻¹⁻¹, CFSG.RankThree.PartOne.KFU.conj_mem_unitarySU h (inv_mem hQ) x.2⟩
  left_inv x := by
    apply Subtype.ext
    simp [mul_assoc]
  right_inv x := by
    apply Subtype.ext
    simp [mul_assoc]
  map_mul' x y := by
    apply Subtype.ext
    simp [mul_assoc]

theorem conjSU_val (h : UnitaryFieldData p f K) (Q : GL (Fin 4) K)
    (hQ : Q ∈ primeFormUnitary h (idGram K 4)) (x : unitarySU p f K 4) :
    ((conjSU h Q hQ x : unitarySU p f K 4) : GL (Fin 4) K) = Q * x * Q⁻¹ := rfl

theorem conjSU_scalar (h : UnitaryFieldData p f K) (Q : GL (Fin 4) K)
    (hQ : Q ∈ primeFormUnitary h (idGram K 4)) {y : GL (Fin 4) K}
    (hy : y ∈ StatedScalars (Fin 4) K) : Q * y * Q⁻¹ = y := by
  rw [commute_of_scalar hy Q, mul_assoc, mul_inv_cancel, mul_one]

@[expose] def conjPSU (h : UnitaryFieldData p f K) (Q : GL (Fin 4) K)
    (hQ : Q ∈ primeFormUnitary h (idGram K 4)) :
    StatedProj (unitarySU p f K 4) ≃* StatedProj (unitarySU p f K 4) :=
  QuotientGroup.congr ((StatedScalars (Fin 4) K).subgroupOf (unitarySU p f K 4))
    ((StatedScalars (Fin 4) K).subgroupOf (unitarySU p f K 4)) (conjSU h Q hQ)
    (by
      ext z
      rw [Subgroup.mem_map]
      constructor
      · rintro ⟨y, hy, rfl⟩
        have hy' : (y : GL (Fin 4) K) ∈ StatedScalars (Fin 4) K :=
          Subgroup.mem_subgroupOf.mp hy
        rw [Subgroup.mem_subgroupOf]
        show Q * (y : GL (Fin 4) K) * Q⁻¹ ∈ StatedScalars (Fin 4) K
        rw [conjSU_scalar h Q hQ hy']
        exact hy'
      · intro hz
        have hz' : (z : GL (Fin 4) K) ∈ StatedScalars (Fin 4) K :=
          Subgroup.mem_subgroupOf.mp hz
        refine ⟨z, Subgroup.mem_subgroupOf.mpr hz', ?_⟩
        apply Subtype.ext
        show Q * (z : GL (Fin 4) K) * Q⁻¹ = (z : GL (Fin 4) K)
        exact conjSU_scalar h Q hQ hz')

theorem diag_entry_pow_three_GL (y : GL (Fin 4) K)
    (hoff : ∀ i j : Fin 4, i ≠ j → (y : Matrix (Fin 4) (Fin 4) K) i j = 0)
    (h3 : y ^ 3 = 1) (i : Fin 4) : (y : Matrix (Fin 4) (Fin 4) K) i i ^ 3 = 1 := by
  have hdiag : (y : Matrix (Fin 4) (Fin 4) K) =
      Matrix.diagonal (fun i => (y : Matrix (Fin 4) (Fin 4) K) i i) := by
    ext a b
    by_cases hab : a = b
    · subst hab
      simp
    · rw [hoff a b hab, Matrix.diagonal_apply_ne _ hab]
  have h3m : (y : Matrix (Fin 4) (Fin 4) K) ^ 3 = 1 := by
    have := congrArg Units.val h3
    rwa [Units.val_pow_eq_pow_val, Units.val_one] at this
  rw [hdiag, Matrix.diagonal_pow] at h3m
  have := congrFun (congrFun h3m i) i
  simpa [Matrix.diagonal_apply_eq] using this

theorem lift_of_elemAbelian_U [Finite K] (h : UnitaryFieldData p f K)
    {E : Subgroup (StatedProj (unitarySU p f K 4))}
    (hE : CFSG.Open.IsElemAbelian 3 E) (hc : Nat.card E = 27) :
    ∃ P : Subgroup (unitarySU p f K 4), P.map (piU K p f) = E ∧
      (∀ x ∈ P, ∀ y ∈ P, x * y = y * x) ∧ (∀ x ∈ P, x ^ 3 = 1) ∧ Nat.card P = 27 := by
  let E' : Subgroup (unitarySU p f K 4) := E.comap (piU K p f)
  let ρ : E' →* E := ((piU K p f).comp E'.subtype).codRestrict E (fun x => x.2)
  have hρ : Function.Surjective ρ := by
    intro e
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective
      (e : StatedProj (unitarySU p f K 4))
    refine ⟨⟨x, ?_⟩, ?_⟩
    · show piU K p f x ∈ E
      have hx' : piU K p f x = (e : StatedProj (unitarySU p f K 4)) := hx
      rw [hx']
      exact e.2
    · apply Subtype.ext
      exact hx
  have h27 : 3 ^ 3 ∣ Nat.card E' := by
    have hq := Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ρ hρ).toEquiv
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker, hq, hc]
    norm_num
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, hQ⟩ := Sylow.exists_subgroup_card_pow_prime (G := E') 3 h27
  let P : Subgroup (unitarySU p f K 4) := Q.map E'.subtype
  have hcardP : Nat.card P = 27 := by
    rw [show P = Q.map E'.subtype from rfl,
      Subgroup.card_map_of_injective (f := E'.subtype) (Subgroup.subtype_injective E'), hQ]
    norm_num
  have hPmem : ∀ x ∈ P, piU K p f x ∈ E := by
    intro x hx
    obtain ⟨q, _, rfl⟩ := Subgroup.mem_map.mp hx
    exact q.2
  have hinj : ∀ x ∈ P, piU K p f x = 1 → x = 1 := by
    intro x hx hpi
    obtain ⟨u, hu⟩ := scalar_of_piU_eq_one hpi
    have hu4 : (u : K) ^ 4 = 1 := pow_four_of_scalar h (by rw [← hu]; exact x.2)
    have hxS : (x : GL (Fin 4) K) = Matrix.GeneralLinearGroup.scalar (Fin 4) u := hu
    have h4 : x ^ 4 = 1 := by
      apply Subtype.ext
      apply Units.ext
      rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hxS, Matrix.GeneralLinearGroup.coe_scalar,
        Matrix.scalar_apply, Matrix.diagonal_pow]
      show Matrix.diagonal ((fun _ => (u : K)) ^ 4) = (1 : Matrix (Fin 4) (Fin 4) K)
      rw [← Matrix.diagonal_one]
      congr 1
      funext i
      simp [hu4]
    have hx27 : x ^ 27 = 1 := by
      have h := pow_card_eq_one' (G := P) (x := ⟨x, hx⟩)
      have h' := congrArg Subtype.val h
      rw [hcardP] at h'
      simpa using h'
    have hg : x ^ (Nat.gcd 27 4) = 1 := pow_gcd_eq_one.mpr ⟨hx27, h4⟩
    have hg1 : Nat.gcd 27 4 = 1 := by norm_num
    rw [hg1, pow_one] at hg
    exact hg
  have hcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
    intro x hx y hy
    have h1 : piU K p f (x * y) = piU K p f (y * x) := by
      rw [map_mul, map_mul]
      have h2 := congrArg Subtype.val
        (hE.1.is_comm.comm ⟨piU K p f x, hPmem x hx⟩ ⟨piU K p f y, hPmem y hy⟩)
      simpa using h2
    have hmem : (y * x)⁻¹ * (x * y) ∈ P :=
      mul_mem (inv_mem (mul_mem hy hx)) (mul_mem hx hy)
    have hpi : piU K p f ((y * x)⁻¹ * (x * y)) = 1 := by
      rw [map_mul, map_inv, h1, inv_mul_cancel]
    exact (inv_mul_eq_one.mp (hinj _ hmem hpi)).symm
  have hpow : ∀ x ∈ P, x ^ 3 = 1 := by
    intro x hx
    apply hinj (x ^ 3) (pow_mem hx 3)
    rw [map_pow]
    exact hE.2 _ (hPmem x hx)
  have hmapE : P.map (piU K p f) = E := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨x, hx, rfl⟩
      exact hPmem x hx
    · rw [card_map_eq_of_injOn (piU K p f) P hinj, hcardP, hc]
  exact ⟨P, hmapE, hcomm, hpow, hcardP⟩

theorem kerConcl_PSU4 [Finite K] (h : UnitaryFieldData p f K) (hdiv : 3 ∣ p ^ f + 1)
    {ζ : K} (hζ : IsPrimitiveRoot ζ 3) {F : Type} [Field F] [Finite F]
    (eSL : Matrix.SpecialLinearGroup (Fin 2) F ≃* unitarySU p f K 2) (hF : 4 ≤ Nat.card F)
    {E : Subgroup (StatedProj (unitarySU p f K 4))}
    (hE : CFSG.Open.IsElemAbelian 3 E) (hc : Nat.card E = 27) : KerConcl E := by
  obtain ⟨P, hPE, hcomm, hpow, hcard⟩ := lift_of_elemAbelian_U h hE hc
  let incl : unitarySU p f K 4 →* ↥(primeFormUnitary h (idGram K 4)) :=
    ((unitarySU p f K 4).subtype).codRestrict _
      (fun x => CFSG.RankThree.PartOne.KFU.unitarySU_le_primeFormUnitary h x.2)
  let G : Subgroup ↥(primeFormUnitary h (idGram K 4)) := P.map incl
  have hGcomm : ∀ x ∈ G, ∀ y ∈ G, x * y = y * x := by
    intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
    rw [← map_mul, ← map_mul, hcomm a ha b hb]
  have hGpow : ∀ x ∈ G, x ^ 3 = 1 := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    rw [← map_pow, hpow a ha, map_one]
  obtain ⟨P0, hP0⟩ := CFSG.RankThree.PartOne.KFU.exists_unitary_conj_diag h Nat.prime_three
    hdiv G hGcomm hGpow
  let Q : GL (Fin 4) K := ((P0⁻¹ : ↥(primeFormUnitary h (idGram K 4))) : GL (Fin 4) K)
  have hQ : Q ∈ primeFormUnitary h (idGram K 4) := (P0⁻¹).2
  have hdiagQ : ∀ y ∈ P, ∀ i j : Fin 4, i ≠ j →
      (((conjSU h Q hQ y : unitarySU p f K 4) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) i j = 0 := by
    intro y hy i j hij
    have hD := hP0 (incl y) ⟨y, hy, rfl⟩
    have e : ((conjSU h Q hQ y : unitarySU p f K 4) : GL (Fin 4) K) =
        ((P0⁻¹ * incl y * P0 : ↥(primeFormUnitary h (idGram K 4))) : GL (Fin 4) K) := by
      rw [conjSU_val]
      simp [Q, incl, mul_assoc]
    rw [e]
    exact hD hij
  have hP'le : P.map (conjSU h Q hQ).toMonoidHom ≤ DiagSU h hdiv := by
    rintro _ ⟨y, hy, rfl⟩
    apply mem_DiagSU_of_diag h hdiv
    · intro i j hij
      exact hdiagQ y hy i j hij
    · intro i
      have h3 : (conjSU h Q hQ y) ^ 3 = 1 := by rw [← map_pow, hpow y hy, map_one]
      have h3GL := congrArg (fun z : unitarySU p f K 4 => (z : GL (Fin 4) K)) h3
      simp only [Subgroup.coe_pow, Subgroup.coe_one] at h3GL
      exact diag_entry_pow_three_GL _ (hdiagQ y hy) h3GL i
  have hP'eq : P.map (conjSU h Q hQ).toMonoidHom = DiagSU h hdiv := by
    apply Subgroup.eq_of_le_of_card_ge hP'le
    rw [Subgroup.card_map_of_injective (f := (conjSU h Q hQ).toMonoidHom)
      (conjSU h Q hQ).injective, hcard]
    exact card_DiagSU_le h hdiv hζ
  have hEq : E.map (conjPSU h Q hQ).toMonoidHom = (DiagSU h hdiv).map (piU K p f) := by
    rw [← hPE, Subgroup.map_map, ← hP'eq, Subgroup.map_map]
    congr 1
  apply kerConcl_of_equiv (conjPSU h Q hQ) E
  rw [hEq]
  exact kerConcl_diagonalU h hdiv hζ eSL hF

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
