module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerA4Psl
public import CFSG.RankThree.PartOne.KC.CommonEigenbasis

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open Matrix CFSG.LocalAnalysis.GLTheoremA.KD264LieA4

variable {K : Type} [Field K]

theorem det_conj_GL (A : GL (Fin 4) K) (x : Matrix.SpecialLinearGroup (Fin 4) K) :
    ((A : Matrix (Fin 4) (Fin 4) K) * (x : Matrix (Fin 4) (Fin 4) K) *
      ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)).det = 1 := by
  rw [Matrix.det_mul, Matrix.det_mul, x.2, mul_one, ← Matrix.det_mul, Units.mul_inv,
    Matrix.det_one]

@[expose] def conjSL (A : GL (Fin 4) K) :
    Matrix.SpecialLinearGroup (Fin 4) K ≃* Matrix.SpecialLinearGroup (Fin 4) K where
  toFun x := ⟨(A : Matrix (Fin 4) (Fin 4) K) * (x : Matrix (Fin 4) (Fin 4) K) *
    ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K), det_conj_GL A x⟩
  invFun x := ⟨((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
    (x : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K), by
      rw [Matrix.det_mul, Matrix.det_mul, x.2, mul_one, ← Matrix.det_mul, Units.inv_mul,
        Matrix.det_one]⟩
  left_inv x := by
    apply Subtype.ext
    have hba : ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
        (A : Matrix (Fin 4) (Fin 4) K) = 1 := Units.inv_mul A
    show ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
      ((A : Matrix (Fin 4) (Fin 4) K) * (x : Matrix (Fin 4) (Fin 4) K) *
        ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) * (A : Matrix (Fin 4) (Fin 4) K) =
      (x : Matrix (Fin 4) (Fin 4) K)
    calc ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
          ((A : Matrix (Fin 4) (Fin 4) K) * (x : Matrix (Fin 4) (Fin 4) K) *
            ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) * (A : Matrix (Fin 4) (Fin 4) K)
        = (((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K)) *
          (x : Matrix (Fin 4) (Fin 4) K) *
          (((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K)) := by
          simp only [Matrix.mul_assoc]
      _ = (x : Matrix (Fin 4) (Fin 4) K) := by rw [Units.inv_mul A, Matrix.one_mul, Matrix.mul_one]
  right_inv x := by
    apply Subtype.ext
    show (A : Matrix (Fin 4) (Fin 4) K) *
      (((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (x : Matrix (Fin 4) (Fin 4) K) *
        (A : Matrix (Fin 4) (Fin 4) K)) * ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      (x : Matrix (Fin 4) (Fin 4) K)
    calc (A : Matrix (Fin 4) (Fin 4) K) *
          (((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (x : Matrix (Fin 4) (Fin 4) K) *
            (A : Matrix (Fin 4) (Fin 4) K)) * ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
        = ((A : Matrix (Fin 4) (Fin 4) K) * ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) *
          (x : Matrix (Fin 4) (Fin 4) K) *
          ((A : Matrix (Fin 4) (Fin 4) K) * ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) := by
          simp only [Matrix.mul_assoc]
      _ = (x : Matrix (Fin 4) (Fin 4) K) := by rw [Units.mul_inv A, Matrix.one_mul, Matrix.mul_one]
  map_mul' x y := by
    apply Subtype.ext
    show (A : Matrix (Fin 4) (Fin 4) K) * ((x : Matrix (Fin 4) (Fin 4) K) *
        (y : Matrix (Fin 4) (Fin 4) K)) * ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      ((A : Matrix (Fin 4) (Fin 4) K) * (x : Matrix (Fin 4) (Fin 4) K) *
        ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) *
      ((A : Matrix (Fin 4) (Fin 4) K) * (y : Matrix (Fin 4) (Fin 4) K) *
        ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K))
    calc (A : Matrix (Fin 4) (Fin 4) K) * ((x : Matrix (Fin 4) (Fin 4) K) *
          (y : Matrix (Fin 4) (Fin 4) K)) * ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
        = (A : Matrix (Fin 4) (Fin 4) K) * (x : Matrix (Fin 4) (Fin 4) K) *
          (((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K)) *
          (y : Matrix (Fin 4) (Fin 4) K) * ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
          rw [Units.inv_mul A]
          simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]

@[expose] def conjPSL [Finite K] (A : GL (Fin 4) K) :
    Matrix.ProjectiveSpecialLinearGroup (Fin 4) K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 4) K :=
  QuotientGroup.congr (Subgroup.center (Matrix.SpecialLinearGroup (Fin 4) K))
    (Subgroup.center (Matrix.SpecialLinearGroup (Fin 4) K)) (conjSL A)
    (map_center_equiv (conjSL A))

theorem conjPSL_piSL [Finite K] (A : GL (Fin 4) K) (x : Matrix.SpecialLinearGroup (Fin 4) K) :
    conjPSL A (piSL K x) = piSL K (conjSL A x) := rfl

theorem card_map_eq_of_injOn {G H : Type} [Group G] [Group H] (f : G →* H) (P : Subgroup G)
    (hf : ∀ x ∈ P, f x = 1 → x = 1) : Nat.card (P.map f) = Nat.card P := by
  have hinj : Function.Injective (f.comp P.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    exact Subtype.ext (hf x.1 x.2 hx)
  have h1 : (f.comp P.subtype).range = P.map f := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← h1]
  exact Nat.card_congr (MonoidHom.ofInjective hinj).symm.toEquiv

theorem pow_four_of_mem_center {x : Matrix.SpecialLinearGroup (Fin 4) K}
    (hx : x ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 4) K)) : x ^ 4 = 1 := by
  obtain ⟨r, hr4, hrx⟩ := center_scalar hx
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, hrx, ← map_pow, hr4, map_one,
    Matrix.SpecialLinearGroup.coe_one]

theorem diag_entry_pow_three (y : Matrix.SpecialLinearGroup (Fin 4) K)
    (hoff : ∀ i j : Fin 4, i ≠ j → (y : Matrix (Fin 4) (Fin 4) K) i j = 0)
    (h3 : y ^ 3 = 1) (i : Fin 4) : (y : Matrix (Fin 4) (Fin 4) K) i i ^ 3 = 1 := by
  have hdiag : (y : Matrix (Fin 4) (Fin 4) K) =
      Matrix.diagonal (fun i => (y : Matrix (Fin 4) (Fin 4) K) i i) := by
    ext a b
    by_cases h : a = b
    · subst h
      simp
    · rw [hoff a b h, Matrix.diagonal_apply_ne _ h]
  have h3m : (y : Matrix (Fin 4) (Fin 4) K) ^ 3 = 1 := by
    have := congrArg Subtype.val h3
    rwa [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one] at this
  rw [hdiag, Matrix.diagonal_pow] at h3m
  have := congrFun (congrFun h3m i) i
  simpa [Matrix.diagonal_apply_eq] using this

theorem mem_DiagSL_of_diag [Finite K] (y : Matrix.SpecialLinearGroup (Fin 4) K)
    (hoff : ∀ i j : Fin 4, i ≠ j → (y : Matrix (Fin 4) (Fin 4) K) i j = 0)
    (hcube : ∀ i : Fin 4, (y : Matrix (Fin 4) (Fin 4) K) i i ^ 3 = 1) : y ∈ DiagSL K := by
  have hy0 : ∀ i, (y : Matrix (Fin 4) (Fin 4) K) i i ≠ 0 := fun i h => by
    have := hcube i
    rw [h] at this
    norm_num at this
  let d : Fin 4 → Kˣ := fun i => Units.mk0 _ (hy0 i)
  have hdiag : (y : Matrix (Fin 4) (Fin 4) K) =
      Matrix.diagonal (fun i => (y : Matrix (Fin 4) (Fin 4) K) i i) := by
    ext a b
    by_cases h : a = b
    · subst h
      simp
    · rw [hoff a b h, Matrix.diagonal_apply_ne _ h]
  have hdet : ∏ i, (y : Matrix (Fin 4) (Fin 4) K) i i = 1 := by
    have h := y.2
    rw [hdiag, Matrix.det_diagonal] at h
    exact h
  have hprod : ∏ i, d i = 1 := by
    apply Units.ext
    rw [Units.coe_prod]
    simpa [d] using hdet
  have hdg : d ∈ dGroup K :=
    ⟨fun i => (mem_mu3 K).mpr (by simpa [d] using hcube i), hprod⟩
  refine MonoidHom.mem_range.mpr ⟨⟨d, hdg⟩, ?_⟩
  apply Subtype.ext
  rw [diagHom_apply_coe]
  show diagM K d = (y : Matrix (Fin 4) (Fin 4) K)
  rw [hdiag]
  unfold diagM
  congr 1

theorem lift_of_elemAbelian [Finite K]
    {E : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 4) K)}
    (hE : CFSG.Open.IsElemAbelian 3 E) (hc : Nat.card E = 27) :
    ∃ P : Subgroup (Matrix.SpecialLinearGroup (Fin 4) K), P.map (piSL K) = E ∧
      (∀ x ∈ P, ∀ y ∈ P, x * y = y * x) ∧ (∀ x ∈ P, x ^ 3 = 1) ∧ Nat.card P = 27 := by
  let E' : Subgroup (Matrix.SpecialLinearGroup (Fin 4) K) := E.comap (piSL K)
  let ρ : E' →* E := ((piSL K).comp E'.subtype).codRestrict E (fun x => x.2)
  have hρ : Function.Surjective ρ := by
    intro e
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective
      (e : Matrix.ProjectiveSpecialLinearGroup (Fin 4) K)
    refine ⟨⟨x, ?_⟩, ?_⟩
    · show piSL K x ∈ E
      have hx' : piSL K x = (e : Matrix.ProjectiveSpecialLinearGroup (Fin 4) K) := hx
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
  let P : Subgroup (Matrix.SpecialLinearGroup (Fin 4) K) := Q.map E'.subtype
  have hcardP : Nat.card P = 27 := by
    rw [show P = Q.map E'.subtype from rfl,
      Subgroup.card_map_of_injective (f := E'.subtype) (Subgroup.subtype_injective E'), hQ]
    norm_num
  have hPmem : ∀ x ∈ P, piSL K x ∈ E := by
    intro x hx
    obtain ⟨q, _, rfl⟩ := Subgroup.mem_map.mp hx
    exact q.2
  have hinj : ∀ x ∈ P, piSL K x = 1 → x = 1 := by
    intro x hx h
    have hxc : x ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 4) K) :=
      (QuotientGroup.eq_one_iff x).mp h
    have h4 : x ^ 4 = 1 := pow_four_of_mem_center hxc
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
    have h1 : piSL K (x * y) = piSL K (y * x) := by
      rw [map_mul, map_mul]
      have h2 := congrArg Subtype.val
        (hE.1.is_comm.comm ⟨piSL K x, hPmem x hx⟩ ⟨piSL K y, hPmem y hy⟩)
      simpa using h2
    have hmem : (y * x)⁻¹ * (x * y) ∈ P :=
      mul_mem (inv_mem (mul_mem hy hx)) (mul_mem hx hy)
    have hpi : piSL K ((y * x)⁻¹ * (x * y)) = 1 := by
      rw [map_mul, map_inv, h1, inv_mul_cancel]
    exact (inv_mul_eq_one.mp (hinj _ hmem hpi)).symm
  have hpow : ∀ x ∈ P, x ^ 3 = 1 := by
    intro x hx
    apply hinj (x ^ 3) (pow_mem hx 3)
    rw [map_pow]
    exact hE.2 _ (hPmem x hx)
  have hmapE : P.map (piSL K) = E := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨x, hx, rfl⟩
      exact hPmem x hx
    · rw [card_map_eq_of_injOn (piSL K) P hinj, hcardP, hc]
  exact ⟨P, hmapE, hcomm, hpow, hcardP⟩

theorem kerConcl_PSL4 [Finite K] {ζ : K} (hζ : IsPrimitiveRoot ζ 3)
    {E : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 4) K)}
    (hE : CFSG.Open.IsElemAbelian 3 E) (hc : Nat.card E = 27) : KerConcl E := by
  obtain ⟨P, hPE, hcomm, hpow, hcard⟩ := lift_of_elemAbelian hE hc
  obtain ⟨A, hA⟩ :=
    CFSG.RankThree.PartOne.exists_conj_diagonal_of_commuting_pow_eq_one hζ P hcomm hpow
  have hDiag : P.map (conjSL A).toMonoidHom = DiagSL K := by
    have hle : P.map (conjSL A).toMonoidHom ≤ DiagSL K := by
      rintro _ ⟨x, hx, rfl⟩
      exact mem_DiagSL_of_diag _ (fun a b hab => hA x hx a b hab)
        (diag_entry_pow_three _ (fun a b hab => hA x hx a b hab)
          (by rw [← map_pow, hpow x hx, map_one]))
    have hcardP : Nat.card (P.map (conjSL A).toMonoidHom) = 27 := by
      rw [Subgroup.card_map_of_injective (f := (conjSL A).toMonoidHom) (conjSL A).injective, hcard]
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcardP]; exact card_DiagSL_le K hζ)
  have hcomp : (conjPSL A).toMonoidHom.comp (piSL K) = (piSL K).comp (conjSL A).toMonoidHom :=
    MonoidHom.ext (fun x => conjPSL_piSL A x)
  have hEq : E.map (conjPSL A).toMonoidHom = (DiagSL K).map (piSL K) := by
    rw [← hPE, Subgroup.map_map, ← hDiag, Subgroup.map_map, hcomp]
  apply kerConcl_of_equiv (conjPSL A) E
  rw [hEq]
  exact kerConcl_diagonal hζ

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
