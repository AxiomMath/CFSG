module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.Stroth.HeisD4.Transport
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Stroth.HeisD4.D4Fixed
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Stroth.HeisD4.Straighten
public import CFSG.RankThree.Chevalley.SteinbergBID4Kernel
public import CFSG.RankThree.PartOne.KE.E7FourHI
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.ClassOdd.Conj
public import CFSG.RankThree.PartOne.KE6.Phi3Arith

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.HeisD4

open CFSG.LieType.SeitzGeneration.ExcHighThree CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2
  CFSG.RankThree.Chevalley
  CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Heis


section Kernel

variable {L : Type} [Field L]

theorem units_map_d4TrialityRep (σ : L →+* L) :
    Units.map (entrywiseHom σ) (d4TrialityRep L) = d4TrialityRep L := by
  unfold d4TrialityRep wordRep
  rw [map_list_prod, List.map_map]
  exact congrArg List.prod (List.map_congr_left fun i _ =>
    E8Lift.units_map_entrywiseHom_weylElt_one σ i)


theorem d4Res_ker_pow {κ : subsystemGroup Tag.E6 L d4Support} (hκ : d4Res L κ = 1) {n : ℕ}
    (hn : ringChar L = 2 ∨ n % 2 = 0) : κ ^ n = 1 := by
  by_cases h2 : ringChar L = 2
  · have hinj := d4Res_injective_of_ringChar_eq_two (K := L) h2
    have : κ = 1 := hinj (by rw [hκ, map_one])
    rw [this, one_pow]
  · have hn' : n % 2 = 0 := hn.resolve_left h2
    obtain ⟨p, hp⟩ := (d4KernelEquiv h2).surjective ⟨κ, hκ⟩
    have hp2 : ∀ p : Multiplicative (ZMod 2 × ZMod 2), p ^ 2 = 1 := by decide
    have h1 : ((⟨κ, hκ⟩ : (d4Res L).ker)) ^ 2 = 1 := by
      rw [← hp, ← map_pow, hp2, map_one]
    have hκ2 : κ ^ 2 = 1 := congrArg Subtype.val h1
    rw [← Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hn'), pow_mul, hκ2, one_pow]

end Kernel


section Main

open CFSG.HardMathSupport.Lang.D4Three

variable {K L : Type} [Field K] [Finite K] [Field L] [Algebra K L] [IsAlgClosure K L]

theorem exists_fixed_ell_std (hK3 : ringChar K ≠ 3)
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    {y m : ModGL Tag.E6 L} {ε : ℕ} (hε : ε = 1 ∨ ε = 2)
    (hm : m ∈ torusGroup Tag.E6 L ⊔ subsystemGroup Tag.E6 L d4Support)
    (hy : y = m * d4TrialityRep L ^ ε)
    (hyF : Units.map (entrywiseHom Fr) y = y) (hy3 : y ^ 3 = 1) :
    ∃ x ∈ subsystemGroup Tag.E6 L d4Support, x ≠ 1 ∧
      x ^ ringChar K = 1 ∧ Units.map (entrywiseHom Fr) x = x ∧ y * x = x * y := by
  classical
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  haveI : Algebra.IsAlgebraic K L := IsAlgClosure.isAlgebraic
  haveI : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K (ringChar K)⟩
  haveI : CharP L (ringChar K) := charP_of_injective_algebraMap (algebraMap K L).injective _
  have hLchar : ringChar L = ringChar K := ringChar.eq L (ringChar K)
  have hmF : Units.map (entrywiseHom Fr) m = m := by
    have : m = y * (d4TrialityRep L ^ ε)⁻¹ := by rw [hy]; group
    rw [this, map_mul, map_inv, map_pow, units_map_d4TrialityRep, hyF]
  obtain ⟨b, j, hj, hγ⟩ := exists_gamma_descent Fr hFr hm hmF
  set X : ModGL Tag.D4 K := rootDiagUnit Tag.D4 b * j * d4P K ^ ε with hX
  set g'' : ↥(adjointGroup Tag.D4 K) := ⟨rootDiagUnit Tag.D4 b * j * (rootDiagUnit Tag.D4 b)⁻¹,
    conj_rootDiagUnit_mem_adjointGroup b hj⟩ with hg''
  set α : MulAut ↥(adjointGroup Tag.D4 K) :=
    MulAut.conj g'' * (exactNormalAut Tag.D4 K b 1 0 * d4Graph K ε) with hα
  have hαX : Parrott.D4Graph.ClassOdd.IsConjBy α X := by
    have := Parrott.D4Graph.ClassOdd.isConjBy_normalForm g'' b ε
    refine this.congr ?_
    rw [hX]
    simp only [hg'']
    group
  have hP : baseChangeGL (algebraMap K L) (d4P K) = d4DiagramMap L :=
    baseChangeGL_diagramMap (algebraMap K L) TwistTag.D4
  have hkey : ∀ h : subsystemGroup Tag.E6 L d4Support, ∃ h' : subsystemGroup Tag.E6 L d4Support,
      (h' : ModGL Tag.E6 L) = y * (h : ModGL Tag.E6 L) * y⁻¹ ∧
      d4Res L h' = baseChangeGL (algebraMap K L) X * d4Res L h *
        (baseChangeGL (algebraMap K L) X)⁻¹ := by
    intro h
    obtain ⟨h', hh', hr⟩ := d4Res_conj_y hm ε h
    refine ⟨h', by rw [hh', hy], ?_⟩
    rw [hr, hγ]
    have e : baseChangeGL (algebraMap K L) (rootDiagUnit Tag.D4 b * j) * d4DiagramMap L ^ ε =
        baseChangeGL (algebraMap K L) X := by
      rw [hX]
      simp only [map_mul, map_pow, hP]
    rw [e]
  have hsurj : ∀ z : ↥(adjointGroup Tag.D4 K),
      ∃ q0 : subsystemGroup Tag.E6 K d4Support, d4Res K q0 = z := by
    intro z
    have hz : (z : ModGL Tag.D4 K) ∈ (d4Res K).range := by
      rw [range_d4Res]
      exact z.2
    exact hz
  have hbc : ∀ q0 : subsystemGroup Tag.E6 K d4Support,
      d4Res L (d4QBaseChange K (algebraMap K L) q0) = baseChangeGL (algebraMap K L) (d4Res K q0) :=
    fun q0 => d4Res_baseChangeGL _ q0
  have hinj := baseChangeGL_injective (τ := Tag.D4) (algebraMap K L)
  have hα3 : α ^ 3 = 1 := by
    have hIC : Parrott.D4Graph.ClassOdd.IsConjBy (α ^ 3) (X ^ 3) := by
      have := (hαX.mul hαX).mul hαX
      rwa [← pow_three', ← pow_three'] at this
    refine MulEquiv.ext fun z => Subtype.ext ?_
    rw [hIC z]
    show X ^ 3 * (z : ModGL Tag.D4 K) * (X ^ 3)⁻¹ = z
    obtain ⟨q0, hq0⟩ := hsurj z
    set h : subsystemGroup Tag.E6 L d4Support := d4QBaseChange K (algebraMap K L) q0 with hh
    obtain ⟨h₁, hh₁, hr₁⟩ := hkey h
    obtain ⟨h₂, hh₂, hr₂⟩ := hkey h₁
    obtain ⟨h₃, hh₃, hr₃⟩ := hkey h₂
    have hyyy : y * y * y = 1 := by rw [← pow_three']; exact hy3
    have h3 : h₃ = h := Subtype.ext (by
      rw [hh₃, hh₂, hh₁]
      calc y * (y * (y * (h : ModGL Tag.E6 L) * y⁻¹) * y⁻¹) * y⁻¹ =
          (y * y * y) * (h : ModGL Tag.E6 L) * (y * y * y)⁻¹ := by group
        _ = h := by rw [hyyy]; group)
    have hres : baseChangeGL (algebraMap K L) (z : ModGL Tag.D4 K) =
        baseChangeGL (algebraMap K L) (X ^ 3 * (z : ModGL Tag.D4 K) * (X ^ 3)⁻¹) := by
      have e0 : d4Res L h = baseChangeGL (algebraMap K L) (z : ModGL Tag.D4 K) := by
        rw [hh, hbc, hq0]
      have e1 := hr₃
      rw [h3] at e1
      rw [hr₂, hr₁, e0] at e1
      rw [map_mul, map_mul, map_inv, map_pow, pow_three']
      refine e1.trans ?_
      group
    exact (hinj hres).symm
  have hαT : D4ElemType α fun ε σ => ε ≠ 0 ∧ σ = 1 :=
    ⟨g'', b, 1, ε, by omega, one_pow _, ⟨by omega, rfl⟩, rfl⟩
  have hKc : ringChar K = 2 ∨ 5 ≤ ringChar K := by
    have hp := (Fact.out : (ringChar K).Prime)
    have h2 := hp.two_le
    rcases hp.eq_two_or_odd with h | h
    · exact Or.inl h
    · right
      omega
  obtain ⟨z, hz1, hzp, hzf⟩ := d4_exists_fixed_ell hKc hα3 hαT
  obtain ⟨q0, hq0⟩ := hsurj z
  set x₁ : subsystemGroup Tag.E6 L d4Support := d4QBaseChange K (algebraMap K L) q0 with hx₁
  have hrx₁ : d4Res L x₁ = baseChangeGL (algebraMap K L) (z : ModGL Tag.D4 K) := by
    rw [hx₁, hbc, hq0]
  have hzne : baseChangeGL (algebraMap K L) (z : ModGL Tag.D4 K) ≠ 1 := by
    intro h
    apply hz1
    apply Subtype.ext
    have h' : baseChangeGL (algebraMap K L) (z : ModGL Tag.D4 K) =
        baseChangeGL (algebraMap K L) (1 : ModGL Tag.D4 K) := by rw [h, map_one]
    exact hinj h'
  have hn : ringChar L = 2 ∨ (ringChar K + 1) % 2 = 0 := by
    have hp := (Fact.out : (ringChar K).Prime)
    rcases hp.eq_two_or_odd with h | h
    · exact Or.inl (by rw [hLchar, h])
    · right
      omega
  have hzℓ : baseChangeGL (algebraMap K L) (z : ModGL Tag.D4 K) ^ ringChar K = 1 := by
    rw [← map_pow]
    have : (z : ModGL Tag.D4 K) ^ ringChar K = 1 := by
      have := congrArg Subtype.val hzp
      simpa using this
    rw [this, map_one]
  refine ⟨((x₁ ^ (ringChar K + 1) : subsystemGroup Tag.E6 L d4Support) : ModGL Tag.E6 L),
    (x₁ ^ (ringChar K + 1)).2, ?_, ?_, ?_, ?_⟩
  · intro h1
    have h1' : x₁ ^ (ringChar K + 1) = 1 := Subtype.ext h1
    have h2 : d4Res L (x₁ ^ (ringChar K + 1)) = 1 := by rw [h1', map_one]
    rw [map_pow, hrx₁, pow_succ, hzℓ, one_mul] at h2
    exact hzne h2
  · have hκ : d4Res L (x₁ ^ ringChar K) = 1 := by rw [map_pow, hrx₁, hzℓ]
    have hxℓ : (x₁ ^ (ringChar K + 1)) ^ ringChar K = 1 := by
      rw [← pow_mul, mul_comm, pow_mul]
      exact d4Res_ker_pow hκ hn
    rw [← Subgroup.coe_pow, hxℓ, Subgroup.coe_one]
  · have hx1F : Units.map (entrywiseHom Fr) (x₁ : ModGL Tag.E6 L) = (x₁ : ModGL Tag.E6 L) :=
      CFSG.RankThree.PartOne.KE.baseChangeGL_frobenius_fixed Fr hFr (q0 : ModGL Tag.E6 K)
    rw [Subgroup.coe_pow, map_pow, hx1F]
  · obtain ⟨h', hh', hr⟩ := hkey x₁
    have hXz : X * (z : ModGL Tag.D4 K) * X⁻¹ = z := by
      have := hαX z
      rw [hzf] at this
      exact this.symm
    have hr' : d4Res L h' = d4Res L x₁ := by
      rw [hr, hrx₁, ← map_mul, ← map_inv, ← map_mul, hXz]
    have hκ : d4Res L (h' * x₁⁻¹) = 1 := by rw [map_mul, map_inv, hr', mul_inv_cancel]
    have hκc := mem_center_of_d4Res_eq_one hκ
    have hκn : (h' * x₁⁻¹) ^ (ringChar K + 1) = 1 := d4Res_ker_pow hκ hn
    have hcomm : Commute (h' * x₁⁻¹) x₁ := (Subgroup.mem_center_iff.1 hκc x₁).symm
    have hpow : h' ^ (ringChar K + 1) = x₁ ^ (ringChar K + 1) := by
      have e : h' = (h' * x₁⁻¹) * x₁ := by group
      conv_lhs => rw [e]
      rw [hcomm.mul_pow, hκn, one_mul]
    have h3 : (y * (x₁ : ModGL Tag.E6 L) * y⁻¹) ^ (ringChar K + 1) =
        (x₁ : ModGL Tag.E6 L) ^ (ringChar K + 1) := by
      rw [← hh', ← Subgroup.coe_pow, hpow, Subgroup.coe_pow]
    have e2 : (y * (x₁ : ModGL Tag.E6 L) * y⁻¹) ^ (ringChar K + 1) =
        y * (x₁ : ModGL Tag.E6 L) ^ (ringChar K + 1) * y⁻¹ := by
      have := conj_pow (a := y) (b := (x₁ : ModGL Tag.E6 L)) (i := ringChar K + 1)
      exact this
    have h4 : y * (x₁ : ModGL Tag.E6 L) ^ (ringChar K + 1) * y⁻¹ =
        (x₁ : ModGL Tag.E6 L) ^ (ringChar K + 1) := e2.symm.trans h3
    rw [Subgroup.coe_pow]
    exact mul_inv_eq_iff_eq_mul.1 h4

end Main

end CFSG.LieType.SeitzGeneration.ExcWideThree.HeisD4
