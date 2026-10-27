module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.FrameSL23
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.RouteWJInv
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie6ProofACent

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.ClosingMinus.Escape

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KGD
  CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.HardMathSupport.Seitz.TrialityOdd.Inner
  CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix

section Finite

@[expose] def phiExp (i j : ZMod 3) : Exp3 := ![i, j, j, i - j]

@[expose] def transWords : List (List (Fin TwistTag.D4.tag.rank)) :=
  [[2, 1], [1, 2], [2, 3, 2, 0], [0, 2, 3, 2], [3, 1, 0, 2, 1, 0], [1, 0, 2, 3, 1, 0],
    [1, 2, 3, 2, 1, 0, 2, 0], [2, 1, 0, 2, 3, 1, 2, 1]]

theorem transWords_comm : ∀ ω ∈ transWords,
    wordMat TwistTag.D4.tag ω * d4T36M (-1) = d4T36M (-1) * wordMat TwistTag.D4.tag ω := by
  decide +kernel

theorem transCheck : ∀ i j i' j' : ZMod 3, (i, j) ≠ (0, 0) → (i', j') ≠ (0, 0) →
    (i', j') ≠ (i, j) → (i', j') ≠ (2 * i, 2 * j) →
    ∃ ω ∈ transWords, wordExp ω (phiExp i j) = phiExp i j ∧
      (wordExp ω (phiExp i' j') = phiExp (i' + i) (j' + j) ∨
        wordExp ω (phiExp i' j') = phiExp (i' - i) (j' - j)) := by
  decide +kernel

theorem phiExp_add (i j i' j' : ZMod 3) :
    phiExp (i + i') (j + j') = phiExp i j + phiExp i' j' := by
  funext k
  fin_cases k
  · show i + i' = i + i'
    rfl
  · show j + j' = j + j'
    rfl
  · show j + j' = j + j'
    rfl
  · show i + i' - (j + j') = (i - j) + (i' - j')
    ring

theorem phiExp_two_mul (i j : ZMod 3) :
    phiExp (2 * i) (2 * j) = fun k => 2 * phiExp i j k := by
  funext k
  fin_cases k
  · show 2 * i = 2 * i
    rfl
  · show 2 * j = 2 * j
    rfl
  · show 2 * j = 2 * j
    rfl
  · show 2 * i - 2 * j = 2 * (i - j)
    ring

end Finite

section Tup

variable {L : Type} [Field L] {ζ : Lˣ}

theorem tup_add (hζ : ζ ^ 3 = 1) (γ γ' : Exp3) : tup ζ (γ + γ') = tup ζ γ * tup ζ γ' := by
  funext k
  simp only [tup, Pi.mul_apply, Pi.add_apply]
  exact (pow_val_add hζ (γ k) (γ' k)).symm

theorem zpow_neg_one_pow_of_cube {u : Lˣ} (hu : u ^ 3 = 1) {q : ℕ} (hq : q % 3 = 2) :
    (u ^ q) ^ (-1 : ℤ) = u := by
  have h2 : u ^ q = u ^ 2 := by
    rw [← Nat.div_add_mod q 3, hq, pow_add, pow_mul, hu, one_pow, one_mul]
  rw [h2, zpow_neg_one, inv_eq_iff_eq_inv, eq_inv_iff_mul_eq_one, ← pow_succ, hu]

end Tup

section Frame


variable {K : Type} [Field K] [Finite K] {σ : K ≃+* K}

theorem exists_phiExp_of_frameTorus {q : ℕ} (hq : q % 3 = 2) (Φ : D4PhiFrame K σ q (-1))
    {ζ : (AlgebraicClosure K)ˣ} (hζ : orderOf ζ = 3)
    {e : graphFixedRootGroup TwistTag.D4 K σ.toRingHom} (he3 : e ^ 3 = 1)
    (heT : frameConj Φ e ∈
      twistedTorusOf Φ.n (twistHom TwistTag.D4 (AlgebraicClosure K) Φ.Fr)) :
    ∃ i j : ZMod 3, frameConj Φ e = rootDiagUnit TwistTag.D4.tag (tup ζ (phiExp i j)) := by
  have hζ3 : ζ ^ 3 = 1 := pow_three_of_orderOf hζ
  rw [twistedTorus_D4_eq_map_of_weylImage Φ.Fr Φ.hn Φ.w Φ.hnw (d4T36M (-1)) Φ.hw] at heT
  obtain ⟨a, ha, hae⟩ := heT
  have hinj0 : Function.Injective (rootDiagUnitHom TwistTag.D4.tag (AlgebraicClosure K)) :=
    rootDiagUnit_injective
  have ha3 : ∀ k, a k ^ 3 = 1 := fun k => by
    have h2 : a ^ 3 = 1 := by
      apply hinj0
      rw [map_pow, map_one, hae, ← map_pow, he3, map_one]
    exact congrFun h2 k
  obtain ⟨γ, rfl⟩ := exists_tup_of_pow_three hζ ha3
  have ha' : tup ζ γ ∈ fixedCharTuples (d4T36M (-1)) Φ.Fr := ha
  rw [mem_fixedCharTuples_d4T36 (Or.inr rfl) Φ.hFr] at ha'
  obtain ⟨h1, h3, -, -⟩ := ha'
  have hc : ∀ k, tup ζ γ k ^ 3 = 1 := ha3
  rw [zpow_neg_one_pow_of_cube (hc 2) hq] at h1
  rw [zpow_neg_one_pow_of_cube (hc 0) hq] at h3
  have h1' : γ 1 = γ 2 := pow_val_inj hζ h1
  have h3' : γ 3 = γ 0 - γ 2 := by
    have e1 : tup ζ γ 3 * tup ζ γ 2 = tup ζ γ 0 := by rw [h3]; group
    simp only [tup] at e1
    rw [pow_val_add hζ3] at e1
    have := pow_val_inj hζ e1
    rw [← this]
    ring
  have hγ : phiExp (γ 0) (γ 1) = γ := by
    funext k
    fin_cases k
    · rfl
    · rfl
    · show γ 1 = γ 2
      exact h1'
    · show γ 0 - γ 1 = γ 3
      rw [h3', h1']
  refine ⟨γ 0, γ 1, ?_⟩
  rw [hγ, ← hae]
  rfl

theorem exists_frame_transvection {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f)
    (hq : (ℓ ^ f) % 3 = 2) (hK : Nat.card K = (ℓ ^ f) ^ 3) (Φ : D4PhiFrame K σ (ℓ ^ f) (-1))
    {x y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hxT : frameConj Φ x ∈
      twistedTorusOf Φ.n (twistHom TwistTag.D4 (AlgebraicClosure K) Φ.Fr))
    (hyT : frameConj Φ y ∈
      twistedTorusOf Φ.n (twistHom TwistTag.D4 (AlgebraicClosure K) Φ.Fr))
    (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) (hy3 : y ^ 3 = 1) (hyx : y ∉ Subgroup.zpowers x) :
    ∃ c : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      c * x * c⁻¹ = x ∧ (c * y * c⁻¹ = x * y ∨ c * y * c⁻¹ = x⁻¹ * y) := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  set L := AlgebraicClosure K with hL
  have hK3 : Nat.card K = ℓ ^ (f * 3) := by rw [hK, ← pow_mul]
  have : CharP K ℓ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ (by omega) hK3
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  have h3L : (3 : L) ≠ 0 := by
    intro h
    have h' : ((3 : ℕ) : L) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff L ℓ] at h'
    exact hℓ3 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).1 h')
  obtain ⟨ζ, hζ⟩ := exists_units_orderOf_three L h3L
  have hζ3 : ζ ^ 3 = 1 := pow_three_of_orderOf hζ
  have hφ := frameConj_injective Φ
  obtain ⟨i, j, hxd⟩ := exists_phiExp_of_frameTorus hq Φ hζ hx3 hxT
  obtain ⟨i', j', hyd⟩ := exists_phiExp_of_frameTorus hq Φ hζ hy3 hyT
  have hrd : ∀ γ γ' : Exp3, rootDiagUnit TwistTag.D4.tag (tup ζ (γ + γ')) =
      rootDiagUnit TwistTag.D4.tag (tup ζ γ) * rootDiagUnit TwistTag.D4.tag (tup ζ γ') := by
    intro γ γ'
    rw [tup_add hζ3]
    exact map_mul (rootDiagUnitHom TwistTag.D4.tag L) _ _
  have hphi0 : phiExp 0 0 = 0 := by
    funext k
    fin_cases k
    · rfl
    · rfl
    · rfl
    · show (0 : ZMod 3) - 0 = 0
      exact sub_self 0
  have hd0 : rootDiagUnit TwistTag.D4.tag (tup ζ (phiExp 0 0)) = 1 := by
    rw [hphi0]
    have : tup ζ (0 : Exp3) = 1 := by
      funext k
      simp [tup]
    rw [this]
    exact map_one (rootDiagUnitHom TwistTag.D4.tag L)
  have hij : (i, j) ≠ (0, 0) := by
    intro h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact hx1 (hφ (by rw [hxd, hd0, map_one]))
  have hij' : (i', j') ≠ (0, 0) := by
    intro h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact hyx (by
      rw [show y = 1 from hφ (by rw [hyd, hd0, map_one])]
      exact one_mem _)
  have hij1 : (i', j') ≠ (i, j) := by
    intro h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact hyx (by
      rw [show y = x from hφ (by rw [hyd, hxd])]
      exact Subgroup.mem_zpowers x)
  have hij2 : (i', j') ≠ (2 * i, 2 * j) := by
    intro h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    apply hyx
    have : y = x ^ 2 := by
      apply hφ
      rw [hyd, map_pow, hxd, phiExp_two_mul, tup_two_mul hζ3]
      exact map_pow (rootDiagUnitHom TwistTag.D4.tag L) _ 2
    rw [this]
    exact Subgroup.npow_mem_zpowers x 2
  obtain ⟨ω, hω, hωx, hωy⟩ := transCheck i j i' j' hij hij' hij1 hij2
  have hq1 : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ hℓ.pos
  obtain ⟨c', hc'⟩ := exists_frameLift hq1 Φ (twistComm_of_mat Φ.hw
    (wordProd_smul_eq_wordMat_mulVec TwistTag.D4.tag ω) (transWords_comm ω hω))
  have hact : ∀ γ : Exp3, frameConj Φ (c' : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) *
      rootDiagUnit TwistTag.D4.tag (tup ζ γ) *
        (frameConj Φ (c' : graphFixedRootGroup TwistTag.D4 K σ.toRingHom))⁻¹ =
      rootDiagUnit TwistTag.D4.tag (tup ζ (wordExp ω γ)) := by
    intro γ
    rw [monomial_conj_rootDiagUnit c'.2, ← weylTuple_wordProd_tup hζ3]
    congr 2
  refine ⟨c', ?_, ?_⟩
  · apply hφ
    rw [map_mul, map_mul, map_inv, hxd, hact, hωx]
  · rcases hωy with h | h
    · left
      apply hφ
      simp only [map_mul, map_inv]
      rw [hxd, hyd, hact, h, add_comm i' i, add_comm j' j, phiExp_add, hrd]
    · right
      apply hφ
      simp only [map_mul, map_inv]
      rw [hxd, hyd, hact, h]
      have h3 : (3 : ZMod 3) = 0 := by decide
      have e : phiExp (i' - i) (j' - j) = phiExp (2 * i) (2 * j) + phiExp i' j' := by
        rw [← phiExp_add]
        congr 1
        · linear_combination (-i) * h3
        · linear_combination (-j) * h3
      rw [e, hrd, phiExp_two_mul, tup_two_mul hζ3]
      have e2 : rootDiagUnit TwistTag.D4.tag (tup ζ (phiExp i j) ^ 2) =
          (rootDiagUnit TwistTag.D4.tag (tup ζ (phiExp i j)))⁻¹ := by
        rw [show rootDiagUnit TwistTag.D4.tag (tup ζ (phiExp i j) ^ 2) =
          rootDiagUnit TwistTag.D4.tag (tup ζ (phiExp i j)) ^ 2 from
          map_pow (rootDiagUnitHom TwistTag.D4.tag L) _ 2]
        have h3 : rootDiagUnit TwistTag.D4.tag (tup ζ (phiExp i j)) ^ 3 = 1 := by
          rw [← hxd, ← map_pow, hx3, map_one]
        rw [eq_inv_iff_mul_eq_one, ← pow_succ, h3]
      rw [e2]

end Frame

end CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.ClosingMinus.Escape
