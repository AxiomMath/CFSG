module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.LowerLift
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.E6TwRank
public import CFSG.RankThree.PartTwo.Census.Classical.EvenPrimes
public import CFSG.CGT.Timmesfeld75.Sec57YAlg
public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.ExcRankSL2
public import CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoMultiplierRow
public import CFSG.Quasithin.Vol2.Ch11SecAKDc
public import CFSG.Quasithin.Background.G8Complement
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2TwAModel
public import CFSG.Monster.B.Fischer.Fi22Order
public import CFSG.Quasithin.Vol2.Ch1Sec3Solvable
public import CFSG.RankThree.PartOne.KF.ClsBasic
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.TwistedE6
open CFSG.LieType.Steinberg.Minuscule CFSG.RankThree.PartTwo.Census.Exceptional
open CFSG.RankThree.CentralCover CFSG.LieType.Steinberg.CentralExt.MinusculeClosed
open scoped MatrixGroups Pointwise

theorem hPairE_conj_xm_gen {k : Type} [Field k] (θ : k →+* k)
    (a b : Fin (Tag.rank .E6)) (t : kˣ) {γ : Fin (Tag.rank .E6) → ℤ}
    (hγ : IsRoot .E6 γ) (c : k) :
    hPairE θ a b t * e6Data_valid.xm k γ c * (hPairE θ a b t)⁻¹ =
      e6Data_valid.xm k γ
        (((t ^ MinData.toWeight γ a * Units.map (θ : k →* k) t ^ MinData.toWeight γ b : kˣ) :
          k) * c) := by
  have e : ∀ x y z : e6Data_valid.minGroup k, (x * y) * z * (x * y)⁻¹ = x * (y * z * y⁻¹) * x⁻¹ :=
    fun x y z => by group
  change e6Data_valid.hm k a t * e6Data_valid.hm k b (Units.map (θ : k →* k) t) *
      e6Data_valid.xm k γ c * (e6Data_valid.hm k a t * e6Data_valid.hm k b
        (Units.map (θ : k →* k) t))⁻¹ = _
  rw [e, e6Data_valid.hm_conj_xm k hγ, e6Data_valid.hm_conj_xm k hγ]
  congr 1
  rw [Units.val_mul, mul_assoc]

theorem hPairE_conj_xm_of_weight_eq {k : Type} [Field k] (θ : k →+* k)
    (a b : Fin (Tag.rank .E6)) {t : kˣ} (ht : t * Units.map (θ : k →* k) t = 1)
    {γ : Fin (Tag.rank .E6) → ℤ} (hγ : IsRoot .E6 γ)
    (hw : MinData.toWeight γ a = MinData.toWeight γ b) (c : k) :
    hPairE θ a b t * e6Data_valid.xm k γ c * (hPairE θ a b t)⁻¹ =
      e6Data_valid.xm k γ c := by
  rw [hPairE_conj_xm_gen θ a b t hγ, hw, ← mul_zpow, ht, one_zpow, Units.val_one, one_mul]

@[expose] noncomputable def te6TorusB {k : Type} [Field k] (θ : k →+* k)
    (hθ : ∀ c, θ (θ c) = c) (t : kˣ) : fixedGroup k θ :=
  ⟨hPairE θ (nd 2) (nd 4) t, hHatE_le_fixedGroup θ hθ (nf 2) (by
    change _ ∈ (hPairE θ (nd 2) (nd 4)).range
    exact ⟨t, rfl⟩)⟩

theorem te6TorusB_val {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) (t : kˣ) :
    (te6TorusB θ hθ t : e6Data_valid.minGroup k) = hPairE θ (nd 2) (nd 4) t := rfl

theorem te6TorusB_pow {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c)
    (t : kˣ) (n : ℕ) : te6TorusB θ hθ t ^ n = te6TorusB θ hθ (t ^ n) :=
  Subtype.ext (by rw [SubgroupClass.coe_pow, te6TorusB_val, te6TorusB_val, map_pow])

theorem te6TorusB_one {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) :
    te6TorusB θ hθ (1 : kˣ) = 1 :=
  Subtype.ext (by rw [te6TorusB_val, map_one]; rfl)

theorem te6_weight_check_24 :
    (∀ i : Fin 4, MinData.toWeight (te6Roots i) (nd 2) = MinData.toWeight (te6Roots i) (nd 4) ∧
      MinData.toWeight (-te6Roots i) (nd 2) = MinData.toWeight (-te6Roots i) (nd 4)) := by
  decide +kernel

theorem te6TorusB_commute {k F : Type} [Field k] [Field F] (θ : k →+* k)
    (hθ : ∀ c, θ (θ c) = c) (j : F →+* k) (hj : ∀ x, θ (j x) = j x) {t : kˣ}
    (ht : t * Units.map (θ : k →* k) t = 1) (i : Fin 4) (A : Matrix.SpecialLinearGroup (Fin 2) F) :
    te6TorusB θ hθ t * te6SL2 θ j hj i A = te6SL2 θ j hj i A * te6TorusB θ hθ t := by
  have hle : ∀ {γ : Fin (Tag.rank .E6) → ℤ}, IsRoot .E6 γ →
      MinData.toWeight γ (nd 2) = MinData.toWeight γ (nd 4) →
      e6Data_valid.rootGroup k γ ≤
        Subgroup.centralizer ({hPairE θ (nd 2) (nd 4) t} : Set (e6Data_valid.minGroup k)) := by
    intro γ hγ hw x hx
    obtain ⟨c, rfl⟩ := (e6Data_valid.mem_rootGroup k).1 hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := hPairE_conj_xm_of_weight_eq θ (nd 2) (nd 4) ht hγ hw c
    rw [mul_inv_eq_iff_eq_mul] at h
    exact h.symm
  have hmem := (sup_le (hle (isRoot_te6Roots i) (te6_weight_check_24 i).1)
    (hle (CFSG.LieType.Chevalley.IsRoot.neg (isRoot_te6Roots i))
      (te6_weight_check_24 i).2)) (te6SL2_mem θ j hj i A)
  rw [Subgroup.mem_centralizer_singleton_iff] at hmem
  exact Subtype.ext hmem.symm

section Witness

variable {k F : Type} [Field k] [Field F] [Finite F]

variable (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) (j : F →+* k) (hj : ∀ x, θ (j x) = j x)
  (hF2 : ringChar F = 2)

theorem te6SL2_orderOf (i : Fin 4) {g : Matrix.SpecialLinearGroup (Fin 2) F} {r : ℕ}
    (hg : orderOf g = r) : orderOf (te6SL2 θ j hj i g) = r := by
  rw [orderOf_injective (te6SL2 θ j hj i) (te6SL2_injective θ j hj i) g, hg]

theorem te6SL2_eq_one_of_centralizes (i : Fin 4) (hF2 : ringChar F = 2)
    {A : Matrix.SpecialLinearGroup (Fin 2) F}
    (h : ∀ B : Matrix.SpecialLinearGroup (Fin 2) F,
      Commute (te6SL2 θ j hj i A) (te6SL2 θ j hj i B)) : A = 1 := by
  have hc : A ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    rw [Subgroup.mem_center_iff]
    intro B
    exact te6SL2_injective θ j hj i (by rw [map_mul, map_mul]; exact (h B).eq.symm)
  rcases eq_one_or_eq_neg_one_of_mem_center F hc with h1 | ⟨hne, -⟩
  · exact h1
  · exact absurd hF2 hne

section FiveWitness

variable {k F : Type} [Field k] [Field F] [Finite F]

variable (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) (j : F →+* k) (hj : ∀ x, θ (j x) = j x)
  {r : ℕ} {μ : kˣ} {g : Matrix.SpecialLinearGroup (Fin 2) F}

theorem te6Torus_eq_minTorus {t : kˣ} :
    (te6Torus θ hθ t : e6Data_valid.minGroup k) = minTorus e6Data_valid k
      (Pi.mulSingle (nd 0) t * Pi.mulSingle (nd 5) (Units.map (θ : k →* k) t)) := by
  rw [te6Torus_val, map_mul, minTorus_mulSingle, minTorus_mulSingle]
  rfl

theorem te6TorusB_eq_minTorus {t : kˣ} :
    (te6TorusB θ hθ t : e6Data_valid.minGroup k) = minTorus e6Data_valid k
      (Pi.mulSingle (nd 2) t * Pi.mulSingle (nd 4) (Units.map (θ : k →* k) t)) := by
  rw [te6TorusB_val, map_mul, minTorus_mulSingle, minTorus_mulSingle]
  rfl

theorem te6Torus_commute_te6TorusB (t : kˣ) :
    Commute (te6Torus θ hθ t) (te6TorusB θ hθ t) := by
  refine Subtype.ext ?_
  rw [Subgroup.coe_mul, Subgroup.coe_mul, te6Torus_eq_minTorus θ hθ, te6TorusB_eq_minTorus θ hθ,
    ← map_mul, ← map_mul, mul_comm]

theorem sq_ne_one_of_orderOf_eq_prime {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {μ : kˣ}
    (hμ : orderOf μ = r) : ((μ : k)) ^ 2 ≠ 1 := by
  intro h
  have h' : μ ^ 2 = 1 := Units.ext h
  have hdvd : orderOf μ ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h'
  rw [hμ] at hdvd
  exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp hdvd)

theorem te6TorusB_ne_one {t : kˣ} (ht : ((t : k)) ^ 2 ≠ 1) : te6TorusB θ hθ t ≠ 1 := by
  intro h1
  have h1' : hPairE θ (nd 2) (nd 4) t = 1 := by
    rw [← te6TorusB_val]; exact congrArg Subtype.val h1
  have h2 : hPairE θ (nd 2) (nd 4) t * e6Data_valid.xm k (Pi.single (nd 2) 1) 1 *
      (hPairE θ (nd 2) (nd 4) t)⁻¹ = e6Data_valid.xm k (Pi.single (nd 2) 1) 1 := by
    rw [h1', one_mul, inv_one, mul_one]
  rw [hPairE_conj_xm_gen θ (nd 2) (nd 4) t (isRoot_single .E6 (nd 2)) 1,
    MinData.toWeight_single, MinData.toWeight_single,
    show Tag.cartan .E6 (nd 2) (nd 2) = 2 by decide,
    show Tag.cartan .E6 (nd 4) (nd 2) = 0 by decide, zpow_zero, mul_one, mul_one] at h2
  have hval := e6Data_valid.xm_injective k (isRoot_single .E6 (nd 2)) h2
  exact ht (by simpa using hval)

theorem te6Torus_orderOf {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {μ : kˣ}
    (hμ : orderOf μ = r) :
    orderOf (te6Torus θ hθ μ) = r := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hμr : μ ^ r = 1 := by rw [← hμ]; exact pow_orderOf_eq_one μ
  refine orderOf_eq_prime ?_ ?_
  · rw [te6Torus_pow, hμr, te6Torus_one]
  · intro h1
    exact te6Torus_not_mem_center θ hθ (sq_ne_one_of_orderOf_eq_prime hr hr2 hμ)
      (by rw [h1]; exact Subgroup.one_mem _)

theorem te6TorusB_orderOf {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {μ : kˣ}
    (hμ : orderOf μ = r) :
    orderOf (te6TorusB θ hθ μ) = r := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hμr : μ ^ r = 1 := by rw [← hμ]; exact pow_orderOf_eq_one μ
  refine orderOf_eq_prime ?_ (te6TorusB_ne_one θ hθ
    (sq_ne_one_of_orderOf_eq_prime hr hr2 hμ))
  rw [te6TorusB_pow, hμr, te6TorusB_one]

theorem zpowers_te6SL2_commute {i i' : Fin 4} (hii : i ≠ i') {x : fixedGroup k θ}
    (hx : x ∈ Subgroup.zpowers (te6SL2 θ j hj i g))
    (B : Matrix.SpecialLinearGroup (Fin 2) F) :
    Commute x (te6SL2 θ j hj i' B) := by
  rw [Subgroup.mem_zpowers_iff] at hx
  obtain ⟨n, rfl⟩ := hx
  exact (show Commute (te6SL2 θ j hj i g) (te6SL2 θ j hj i' B) from
    te6SL2_commute θ j hj hii g B).zpow_left n

theorem zpowers_te6Torus_commute {t : kˣ}
    (ht : t * Units.map (θ : k →* k) t = 1) {x : fixedGroup k θ}
    (hx : x ∈ Subgroup.zpowers (te6Torus θ hθ t)) (i : Fin 4)
    (B : Matrix.SpecialLinearGroup (Fin 2) F) :
    Commute x (te6SL2 θ j hj i B) := by
  rw [Subgroup.mem_zpowers_iff] at hx
  obtain ⟨n, rfl⟩ := hx
  exact (show Commute (te6Torus θ hθ t) (te6SL2 θ j hj i B) from
    te6Torus_commute θ j hj hθ ht i B).zpow_left n

theorem zpowers_te6TorusB_commute {t : kˣ}
    (ht : t * Units.map (θ : k →* k) t = 1) {x : fixedGroup k θ}
    (hx : x ∈ Subgroup.zpowers (te6TorusB θ hθ t)) (i : Fin 4)
    (B : Matrix.SpecialLinearGroup (Fin 2) F) :
    Commute x (te6SL2 θ j hj i B) := by
  rw [Subgroup.mem_zpowers_iff] at hx
  obtain ⟨n, rfl⟩ := hx
  exact (show Commute (te6TorusB θ hθ t) (te6SL2 θ j hj i B) from
    te6TorusB_commute θ hθ j hj ht i B).zpow_left n

theorem eq_one_of_mem_zpowers_te6SL2 (hF2 : ringChar F = 2) {i : Fin 4}
    {A : Matrix.SpecialLinearGroup (Fin 2) F} {x : fixedGroup k θ}
    (hx : x ∈ Subgroup.zpowers (te6SL2 θ j hj i A))
    (hcent : ∀ B : Matrix.SpecialLinearGroup (Fin 2) F,
      Commute x (te6SL2 θ j hj i B)) : x = 1 := by
  rw [Subgroup.mem_zpowers_iff] at hx
  obtain ⟨n, rfl⟩ := hx
  have hmap : (te6SL2 θ j hj i A) ^ n = te6SL2 θ j hj i (A ^ n) :=
    (map_zpow (te6SL2 θ j hj i) A n).symm
  rw [hmap] at hcent ⊢
  have hA : A ^ n = 1 := te6SL2_eq_one_of_centralizes θ j hj i hF2 hcent
  rw [hA, map_one]

theorem eq_one_of_mem_sup_zpowers_te6SL2 (hF2 : ringChar F = 2) {x : fixedGroup k θ}
    (hx : x ∈ (Subgroup.zpowers (te6SL2 θ j hj (0 : Fin 4) g) ⊔
       Subgroup.zpowers (te6SL2 θ j hj (1 : Fin 4) g)) ⊔
       Subgroup.zpowers (te6SL2 θ j hj (2 : Fin 4) g))
    (hc0 : ∀ C : Matrix.SpecialLinearGroup (Fin 2) F,
      Commute x (te6SL2 θ j hj (0 : Fin 4) C))
    (hc1 : ∀ C : Matrix.SpecialLinearGroup (Fin 2) F,
      Commute x (te6SL2 θ j hj (1 : Fin 4) C))
    (hc2 : ∀ C : Matrix.SpecialLinearGroup (Fin 2) F,
      Commute x (te6SL2 θ j hj (2 : Fin 4) C)) : x = 1 := by
  have h01 : (1 : Fin 4) ≠ 0 := by decide
  have h02 : (2 : Fin 4) ≠ 0 := by decide
  have h10 : (1 : Fin 4) ≠ 2 := by decide
  have hc01 : ∀ a ∈ Subgroup.zpowers (te6SL2 θ j hj (0 : Fin 4) g),
      ∀ b ∈ Subgroup.zpowers (te6SL2 θ j hj (1 : Fin 4) g), Commute a b := by
    intro a ha b hb
    rw [Subgroup.mem_zpowers_iff] at ha hb
    obtain ⟨m, rfl⟩ := ha
    obtain ⟨n, rfl⟩ := hb
    exact (show Commute (te6SL2 θ j hj (0 : Fin 4) g)
      (te6SL2 θ j hj (1 : Fin 4) g) from te6SL2_commute θ j hj (by decide) g g).zpow_zpow m n
  have hcA2 : ∀ a ∈ (Subgroup.zpowers (te6SL2 θ j hj (0 : Fin 4) g) ⊔
      Subgroup.zpowers (te6SL2 θ j hj (1 : Fin 4) g)),
      ∀ b ∈ Subgroup.zpowers (te6SL2 θ j hj (2 : Fin 4) g), Commute a b := by
    intro a ha b hb
    obtain ⟨a0, ha0, a1, ha1, hxeq⟩ :=
      CFSG.Quasithin.G8.mem_sup_of_commute
        (fun u hu v hv => (hc01 u hu v hv).eq) ha
    rw [Subgroup.mem_zpowers_iff] at ha0 ha1 hb
    obtain ⟨m, rfl⟩ := ha0
    obtain ⟨k, rfl⟩ := ha1
    obtain ⟨n, rfl⟩ := hb
    rw [hxeq]
    exact ((show Commute (te6SL2 θ j hj (0 : Fin 4) g)
        (te6SL2 θ j hj (2 : Fin 4) g) from te6SL2_commute θ j hj (by decide) g g).zpow_zpow m n).mul_left
      ((show Commute (te6SL2 θ j hj (1 : Fin 4) g)
        (te6SL2 θ j hj (2 : Fin 4) g) from te6SL2_commute θ j hj h10 g g).zpow_zpow k n)
  obtain ⟨xa, hxa, x2, hx2, hxeq⟩ :=
    CFSG.Quasithin.G8.mem_sup_of_commute (fun u hu v hv => (hcA2 u hu v hv).eq) hx
  obtain ⟨x0, hx0, x1, hx1, hxaeq⟩ :=
    CFSG.Quasithin.G8.mem_sup_of_commute (fun u hu v hv => (hc01 u hu v hv).eq) hxa
  have hx' : x0 * x1 * x2 = x := by rw [hxeq, hxaeq]
  have hx1c0 : ∀ C, Commute x1 (te6SL2 θ j hj (0 : Fin 4) C) :=
    fun C => zpowers_te6SL2_commute θ j hj h01 hx1 C
  have hx2c0 : ∀ C, Commute x2 (te6SL2 θ j hj (0 : Fin 4) C) :=
    fun C => zpowers_te6SL2_commute θ j hj h02 hx2 C
  have hc0' : ∀ C, Commute (x0 * x1 * x2) (te6SL2 θ j hj (0 : Fin 4) C) := by
    intro C; rw [hx']; exact hc0 C
  have hx0c0 : ∀ C, Commute x0 (te6SL2 θ j hj (0 : Fin 4) C) := by
    intro C
    have h12 : Commute (x1 * x2) (te6SL2 θ j hj (0 : Fin 4) C) :=
      (hx1c0 C).mul_left (hx2c0 C)
    have hxeq0 : x0 = (x0 * x1 * x2) * (x1 * x2)⁻¹ := by group
    rw [hxeq0]
    exact (hc0' C).mul_left h12.inv_left
  have hx0' : x0 = 1 := eq_one_of_mem_zpowers_te6SL2 θ j hj hF2 hx0 hx0c0
  have hx1c1 : ∀ C, Commute x1 (te6SL2 θ j hj (1 : Fin 4) C) := by
    intro C
    have hx2c1 : Commute x2 (te6SL2 θ j hj (1 : Fin 4) C) :=
      zpowers_te6SL2_commute θ j hj (Ne.symm h10) hx2 C
    have hc1' : Commute (x1 * x2) (te6SL2 θ j hj (1 : Fin 4) C) := by
      rw [hx0', one_mul] at hx'
      rw [hx']
      exact hc1 C
    have hxeq1 : x1 = (x1 * x2) * x2⁻¹ := by group
    rw [hxeq1]
    exact hc1'.mul_left hx2c1.inv_left
  have hx1' : x1 = 1 := eq_one_of_mem_zpowers_te6SL2 θ j hj hF2 hx1 hx1c1
  rw [hx0', hx1', one_mul, one_mul] at hx'
  rw [← hx'] at hc2
  rw [← hx']
  exact eq_one_of_mem_zpowers_te6SL2 θ j hj hF2 hx2 hc2

end FiveWitness

end Witness

theorem te6TorusB_zpow {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c)
    (t : kˣ) (n : ℤ) : te6TorusB θ hθ t ^ n = te6TorusB θ hθ (t ^ n) :=
  Subtype.ext (by rw [Subgroup.coe_zpow, te6TorusB_val, te6TorusB_val, map_zpow])

theorem te6Torus_zpow {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c)
    (t : kˣ) (n : ℤ) : te6Torus θ hθ t ^ n = te6Torus θ hθ (t ^ n) :=
  Subtype.ext (by rw [Subgroup.coe_zpow, te6Torus_val, te6Torus_val, map_zpow])

theorem te6Torus_inf_te6TorusB_eq_bot {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {t : kˣ} (hμ : orderOf t = r) :
    Subgroup.zpowers (te6Torus θ hθ t) ⊓ Subgroup.zpowers (te6TorusB θ hθ t) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.1 hx1
  obtain ⟨b, hb⟩ := Subgroup.mem_zpowers_iff.1 hx2
  have heq : te6Torus θ hθ t ^ a = te6TorusB θ hθ t ^ b := by rw [ha, hb]
  have hval := congrArg Subtype.val heq
  rw [te6Torus_zpow, te6TorusB_zpow, te6Torus_eq_minTorus θ hθ,
    te6TorusB_eq_minTorus θ hθ] at hval
  have htuple := minTorus_injective e6Data_valid k hval
  have h0 := congrFun htuple (0 : Fin (Tag.rank .E6))
  simp only [Pi.mul_apply, Pi.mulSingle_apply, Fin.ext_iff] at h0
  norm_num at h0
  have ht_pow : t ^ a = 1 := by simpa using h0
  have hdvd : (r : ℤ) ∣ a := by
    rw [← hμ]
    exact orderOf_dvd_iff_zpow_eq_one.mpr ht_pow
  rw [← ha]
  exact orderOf_dvd_iff_zpow_eq_one.mp (by rw [te6Torus_orderOf θ hθ hr hr2 hμ]; exact hdvd)

section Five

variable {k F : Type} [Field k] [Finite k] [Field F] [Finite F]
  (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) (j : F →+* k) (hj : ∀ x, θ (j x) = j x)
  {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)

theorem zpowers_te6SL2_order {g : SL(2, F)} (hg : orderOf g = r) (i : Fin 4) :
    orderOf (te6SL2 θ j hj i g) = r := te6SL2_orderOf θ j hj i hg

theorem card_zpowers_te6SL2 {g : SL(2, F)} (hg : orderOf g = r) (i : Fin 4) :
    Nat.card (Subgroup.zpowers (te6SL2 θ j hj i g)) = r := by
  rw [Nat.card_zpowers, zpowers_te6SL2_order θ j hj hg]

theorem zpowers_te6SL2_disjoint (hF2 : ringChar F = 2) {g : SL(2, F)} (hg : orderOf g = r)
    {i i' : Fin 4} (hii : i ≠ i') :
    Subgroup.zpowers (te6SL2 θ j hj i g) ⊓ Subgroup.zpowers (te6SL2 θ j hj i' g) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx1
  refine eq_one_of_mem_zpowers_te6SL2 θ j hj hF2
    (Subgroup.mem_zpowers_iff.2 ⟨a, rfl⟩) ?_
  intro C
  exact zpowers_te6SL2_commute θ j hj (g := g) (Ne.symm hii) hx2 C

theorem commute_zpowers_te6SL2 {g : SL(2, F)}
    {i i' : Fin 4} {x y : fixedGroup k θ}
    (hx : x ∈ Subgroup.zpowers (te6SL2 θ j hj i g))
    (hy : y ∈ Subgroup.zpowers (te6SL2 θ j hj i' g)) : Commute x y := by
  obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  obtain ⟨b, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  by_cases hii : i = i'
  · subst hii
    exact Commute.zpow_zpow_self _ a b
  · exact (show Commute (te6SL2 θ j hj i g) (te6SL2 θ j hj i' g) from
      te6SL2_commute θ j hj hii g g).zpow_zpow a b

end Five

section Cardinality

variable {k F : Type} [Field k] [Finite k] [Field F] [Finite F]
  (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) (j : F →+* k) (hj : ∀ x, θ (j x) = j x)
  {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
  {g : SL(2, F)} {t : kˣ}

theorem card_sup_two_te6SL2 (hF2 : ringChar F = 2) (hg : orderOf g = r)
    (h01 : (0 : Fin 4) ≠ 1) :
    Nat.card ↥(Subgroup.zpowers (te6SL2 θ j hj 0 g) ⊔
      Subgroup.zpowers (te6SL2 θ j hj 1 g)) = r ^ 2 := by
  rw [CFSG.CGT.Timmesfeld75.card_sup_eq_mul_of_commute (G := fixedGroup k θ)
    (fun p hp q hq => (commute_zpowers_te6SL2 θ j hj hp hq).eq)
    (zpowers_te6SL2_disjoint θ j hj hF2 hg h01),
    card_zpowers_te6SL2 θ j hj hg 0, card_zpowers_te6SL2 θ j hj hg 1]
  ring

theorem inf_sup_two_te6SL2_eq_bot (hF2 : ringChar F = 2) (hg : orderOf g = r) :
    (Subgroup.zpowers (te6SL2 θ j hj 0 g) ⊔
      Subgroup.zpowers (te6SL2 θ j hj 1 g)) ⊓
      Subgroup.zpowers (te6SL2 θ j hj 2 g) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxA, hx2⟩ := Subgroup.mem_inf.1 hx
  have hcomm : ∀ a ∈ Subgroup.zpowers (te6SL2 θ j hj 0 g),
      ∀ b ∈ Subgroup.zpowers (te6SL2 θ j hj 1 g), Commute a b :=
    fun a ha b hb => commute_zpowers_te6SL2 θ j hj ha hb
  obtain ⟨a0, ha0, a1, ha1, hxeq⟩ :=
    CFSG.Quasithin.G8.mem_sup_of_commute (fun u hu v hv => (hcomm u hu v hv).eq) hxA
  rw [hxeq] at hx2 ⊢
  have h20 : (2 : Fin 4) ≠ 0 := by decide
  have h21 : (2 : Fin 4) ≠ 1 := by decide
  have h10 : (1 : Fin 4) ≠ 0 := by decide
  have hx_c0 : ∀ C, Commute (a0 * a1) (te6SL2 θ j hj 0 C) :=
    fun C => zpowers_te6SL2_commute θ j hj (g := g) h20 hx2 C
  have ha1_c0 : ∀ C, Commute a1 (te6SL2 θ j hj 0 C) :=
    fun C => zpowers_te6SL2_commute θ j hj (g := g) h10 ha1 C
  have ha0_c0 : ∀ C, Commute a0 (te6SL2 θ j hj 0 C) := by
    intro C
    have h := (hx_c0 C).mul_left (ha1_c0 C).inv_left
    rwa [mul_inv_cancel_right] at h
  have ha0' : a0 = 1 :=
    eq_one_of_mem_zpowers_te6SL2 θ j hj hF2 ha0 ha0_c0
  rw [ha0', one_mul]
  refine eq_one_of_mem_zpowers_te6SL2 θ j hj hF2 ha1 ?_
  intro C
  have ha1z : a1 ∈ Subgroup.zpowers (te6SL2 θ j hj 2 g) := by
    simpa [ha0'] using hx2
  exact zpowers_te6SL2_commute θ j hj (g := g) h21 ha1z C

theorem card_sup_three_te6SL2 (hF2 : ringChar F = 2) (hg : orderOf g = r) :
    Nat.card ↥((Subgroup.zpowers (te6SL2 θ j hj 0 g) ⊔
      Subgroup.zpowers (te6SL2 θ j hj 1 g)) ⊔
      Subgroup.zpowers (te6SL2 θ j hj 2 g)) = r ^ 3 := by
  rw [CFSG.CGT.Timmesfeld75.card_sup_eq_mul_of_commute (G := fixedGroup k θ)
    (P := Subgroup.zpowers (te6SL2 θ j hj 0 g) ⊔ Subgroup.zpowers (te6SL2 θ j hj 1 g))
    (Q := Subgroup.zpowers (te6SL2 θ j hj 2 g))
    ?_ (inf_sup_two_te6SL2_eq_bot θ j hj hF2 hg),
    card_sup_two_te6SL2 θ j hj hF2 hg (by decide), card_zpowers_te6SL2 θ j hj hg 2]
  · ring
  · intro a ha b hb
    obtain ⟨a0, ha0, a1, ha1, hxeq⟩ :=
      CFSG.Quasithin.G8.mem_sup_of_commute
        (fun a ha b hb => (commute_zpowers_te6SL2 θ j hj ha hb).eq) ha
    rw [hxeq]
    exact ((commute_zpowers_te6SL2 θ j hj ha0 hb).mul_left
      (commute_zpowers_te6SL2 θ j hj ha1 hb)).eq

theorem card_zpowers_te6Torus (hr : r.Prime) (hr2 : r ≠ 2) (hμ : orderOf t = r) :
    Nat.card (Subgroup.zpowers (te6Torus θ hθ t)) = r := by
  rw [Nat.card_zpowers, te6Torus_orderOf θ hθ hr hr2 hμ]

theorem card_zpowers_te6TorusB (hr : r.Prime) (hr2 : r ≠ 2) (hμ : orderOf t = r) :
    Nat.card (Subgroup.zpowers (te6TorusB θ hθ t)) = r := by
  rw [Nat.card_zpowers, te6TorusB_orderOf θ hθ hr hr2 hμ]

theorem commute_zpowers_tori {a b : fixedGroup k θ}
    (ha : a ∈ Subgroup.zpowers (te6Torus θ hθ t))
    (hb : b ∈ Subgroup.zpowers (te6TorusB θ hθ t)) : Commute a b := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
  exact (show Commute (te6Torus θ hθ t) (te6TorusB θ hθ t) from
    te6Torus_commute_te6TorusB θ hθ t).zpow_zpow m n

theorem card_sup_two_te6Torus (hr : r.Prime) (hr2 : r ≠ 2) (hμ : orderOf t = r) :
    Nat.card ↥(Subgroup.zpowers (te6Torus θ hθ t) ⊔
      Subgroup.zpowers (te6TorusB θ hθ t)) = r ^ 2 := by
  rw [CFSG.CGT.Timmesfeld75.card_sup_eq_mul_of_commute (G := fixedGroup k θ)
    (fun p hp q hq => (commute_zpowers_tori θ hθ hp hq).eq)
    (te6Torus_inf_te6TorusB_eq_bot θ hθ hr hr2 hμ),
    card_zpowers_te6Torus θ hθ hr hr2 hμ, card_zpowers_te6TorusB θ hθ hr hr2 hμ]
  ring

theorem inf_sup_three_te6SL2_sup_tori (hF2 : ringChar F = 2) (hg : orderOf g = r)
    (ht : t * Units.map (θ : k →* k) t = 1) :
    ((Subgroup.zpowers (te6SL2 θ j hj 0 g) ⊔
      Subgroup.zpowers (te6SL2 θ j hj 1 g)) ⊔
      Subgroup.zpowers (te6SL2 θ j hj 2 g)) ⊓
      (Subgroup.zpowers (te6Torus θ hθ t) ⊔
        Subgroup.zpowers (te6TorusB θ hθ t)) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxA, hxB⟩ := Subgroup.mem_inf.1 hx
  have hBcent : ∀ i : Fin 4,
      Subgroup.zpowers (te6Torus θ hθ t) ⊔ Subgroup.zpowers (te6TorusB θ hθ t) ≤
        Subgroup.centralizer (Set.range (te6SL2 θ j hj i)) := by
    intro i
    refine sup_le ?_ ?_
    · rintro _ ⟨m, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨C, rfl⟩
      exact (zpowers_te6Torus_commute θ hθ j hj ht
        (Subgroup.mem_zpowers_iff.2 ⟨m, rfl⟩) i C).symm
    · rintro _ ⟨m, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨C, rfl⟩
      exact (zpowers_te6TorusB_commute θ hθ j hj ht
        (Subgroup.mem_zpowers_iff.2 ⟨m, rfl⟩) i C).symm
  have hc : ∀ i : Fin 4, ∀ C, Commute x (te6SL2 θ j hj i C) := by
    intro i C
    exact (Subgroup.mem_centralizer_iff.1 (hBcent i hxB) _ ⟨C, rfl⟩).symm
  exact eq_one_of_mem_sup_zpowers_te6SL2 θ j hj hF2 hxA
    (fun C => hc 0 C) (fun C => hc 1 C) (fun C => hc 2 C)

@[expose] noncomputable def te6WA {k F : Type} [Field k] [Field F] (θ : k →+* k) (j : F →+* k)
    (hj : ∀ x, θ (j x) = j x) (g : SL(2, F)) : Subgroup (fixedGroup k θ) :=
  Subgroup.zpowers (te6SL2 θ j hj 0 g) ⊔ Subgroup.zpowers (te6SL2 θ j hj 1 g) ⊔
    Subgroup.zpowers (te6SL2 θ j hj 2 g)

noncomputable def te6WB {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c)
    (t : kˣ) : Subgroup (fixedGroup k θ) :=
  Subgroup.zpowers (te6Torus θ hθ t) ⊔ Subgroup.zpowers (te6TorusB θ hθ t)

noncomputable def te6WE {k F : Type} [Field k] [Field F] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c)
    (j : F →+* k) (hj : ∀ x, θ (j x) = j x) (g : SL(2, F)) (t : kˣ) :
    Subgroup (fixedGroup k θ) :=
  te6WA θ j hj g ⊔ te6WB θ hθ t

noncomputable def te6WX {k : Type} [Field k] (θ : k →+* k) (u : fixedGroup k θ) :
    Subgroup (fixedGroup k θ) :=
  Subgroup.zpowers u

theorem card_te6WA (hF2 : ringChar F = 2) (hg : orderOf g = r) :
    Nat.card (te6WA θ j hj g) = r ^ 3 :=
  card_sup_three_te6SL2 θ j hj hF2 hg

theorem card_te6WB (hr : r.Prime) (hr2 : r ≠ 2) (hμ : orderOf t = r) :
    Nat.card (te6WB θ hθ t) = r ^ 2 :=
  card_sup_two_te6Torus θ hθ hr hr2 hμ

theorem isElemAbelian_te6WA (hF2 : ringChar F = 2) (hg : orderOf g = r) :
    IsElemAbelian r (te6WA θ j hj g) := by
  have h0 : (te6SL2 θ j hj 0 g) ^ r = 1 := by
    rw [← zpowers_te6SL2_order θ j hj hg]; exact pow_orderOf_eq_one _
  have h1 : (te6SL2 θ j hj 1 g) ^ r = 1 := by
    rw [← zpowers_te6SL2_order θ j hj hg]; exact pow_orderOf_eq_one _
  have h2 : (te6SL2 θ j hj 2 g) ^ r = 1 := by
    rw [← zpowers_te6SL2_order θ j hj hg]; exact pow_orderOf_eq_one _
  rw [te6WA]
  refine IsElemAbelian.sup_of_commute (p := r) ?_ (isElemAbelian_zpowers h2) ?_
  · refine IsElemAbelian.sup_of_commute (p := r) (isElemAbelian_zpowers h0)
      (isElemAbelian_zpowers h1) ?_
    intro a ha b hb
    exact (commute_zpowers_te6SL2 θ j hj ha hb).eq
  · intro a ha b hb
    obtain ⟨a0, ha0, a1, ha1, hxeq⟩ :=
      CFSG.Quasithin.G8.mem_sup_of_commute
        (fun u hu v hv => (commute_zpowers_te6SL2 θ j hj hu hv).eq) ha
    rw [hxeq]
    exact ((commute_zpowers_te6SL2 θ j hj ha0 hb).mul_left
      (commute_zpowers_te6SL2 θ j hj ha1 hb)).eq

theorem isElemAbelian_te6WB (hr : r.Prime) (hr2 : r ≠ 2) (hμ : orderOf t = r) :
    IsElemAbelian r (te6WB θ hθ t) := by
  have h0 : (te6Torus θ hθ t) ^ r = 1 := by
    rw [← te6Torus_orderOf θ hθ hr hr2 hμ]; exact pow_orderOf_eq_one _
  have h1 : (te6TorusB θ hθ t) ^ r = 1 := by
    rw [← te6TorusB_orderOf θ hθ hr hr2 hμ]; exact pow_orderOf_eq_one _
  rw [te6WB]
  refine IsElemAbelian.sup_of_commute (p := r) (isElemAbelian_zpowers h0)
    (isElemAbelian_zpowers h1) ?_
  intro a ha b hb
  exact (commute_zpowers_tori θ hθ ha hb).eq

theorem zpowers_te6SL2_le_centralizer_te6WB
    (ht : t * Units.map (θ : k →* k) t = 1) (i : Fin 4) :
    Subgroup.zpowers (te6SL2 θ j hj i g) ≤ Subgroup.centralizer (te6WB θ hθ t) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  rw [te6WB] at hb
  obtain ⟨b1, hb1, b2, hb2, hxeq⟩ :=
    CFSG.Quasithin.G8.mem_sup_of_commute
      (fun u hu v hv => (commute_zpowers_tori θ hθ hu hv).eq) hb
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  obtain ⟨n1, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb1
  obtain ⟨n2, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb2
  have e1 : Commute (te6Torus θ hθ t) (te6SL2 θ j hj i g) :=
    te6Torus_commute θ j hj hθ ht i g
  have e2 : Commute (te6TorusB θ hθ t) (te6SL2 θ j hj i g) :=
    te6TorusB_commute θ hθ j hj ht i g
  rw [hxeq]
  exact ((e1.zpow_left n1).mul_left (e2.zpow_left n2)).zpow_right m

theorem te6WA_le_centralizer_te6WB (ht : t * Units.map (θ : k →* k) t = 1) :
    te6WA θ j hj g ≤ Subgroup.centralizer (te6WB θ hθ t) := by
  rw [te6WA]
  refine sup_le (sup_le ?_ ?_) ?_
  · exact zpowers_te6SL2_le_centralizer_te6WB θ hθ j hj ht 0
  · exact zpowers_te6SL2_le_centralizer_te6WB θ hθ j hj ht 1
  · exact zpowers_te6SL2_le_centralizer_te6WB θ hθ j hj ht 2

theorem commute_te6WA_te6WB (ht : t * Units.map (θ : k →* k) t = 1) :
    ∀ a ∈ te6WA θ j hj g, ∀ b ∈ te6WB θ hθ t, a * b = b * a := by
  intro a ha b hb
  exact (Subgroup.mem_centralizer_iff.1
    (te6WA_le_centralizer_te6WB θ hθ j hj ht ha) b hb).symm

theorem isElemAbelian_te6WE (hr : r.Prime) (hr2 : r ≠ 2) (hF2 : ringChar F = 2)
    (hg : orderOf g = r) (hμ : orderOf t = r)
    (ht : t * Units.map (θ : k →* k) t = 1) :
    IsElemAbelian r (te6WE θ hθ j hj g t) := by
  rw [te6WE]
  exact IsElemAbelian.sup_of_commute (isElemAbelian_te6WA θ j hj hF2 hg)
    (isElemAbelian_te6WB θ hθ hr hr2 hμ) (commute_te6WA_te6WB θ hθ j hj ht)

theorem card_te6WE (hr : r.Prime) (hr2 : r ≠ 2) (hF2 : ringChar F = 2)
    (hg : orderOf g = r) (hμ : orderOf t = r)
    (ht : t * Units.map (θ : k →* k) t = 1) :
    Nat.card (te6WE θ hθ j hj g t) = r ^ 5 := by
  rw [te6WE,
    CFSG.CGT.Timmesfeld75.card_sup_eq_mul_of_commute (G := fixedGroup k θ)
      (commute_te6WA_te6WB θ hθ j hj ht)
      (inf_sup_three_te6SL2_sup_tori θ hθ j hj hF2 hg ht),
    card_te6WA θ j hj hF2 hg, card_te6WB θ hθ hr hr2 hμ]
  ring

end Cardinality

section Target

variable {k F : Type} [Field k] [Finite k] [Field F] [Finite F]
  (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) (j : F →+* k) (hj : ∀ x, θ (j x) = j x)
  {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hr5 : 5 ≤ r)
  {g : SL(2, F)} {t : kˣ}

theorem orderOf_te6Involution (hF2 : ringChar F = 2) :
    orderOf (te6SL2 θ j hj 3 (sl2Upper (1 : F))) = 2 := by
  rw [te6SL2_orderOf θ j hj 3 (orderOf_sl2Upper_one hF2)]

theorem te6WX_ne_bot (hF2 : ringChar F = 2) :
    te6WX θ (te6SL2 θ j hj 3 (sl2Upper (1 : F))) ≠ ⊥ := by
  rw [te6WX, Ne, Subgroup.zpowers_eq_bot]
  intro h
  have h2 := orderOf_te6Involution θ j hj hF2
  rw [h, orderOf_one] at h2
  omega

theorem isPGroup_te6WX (hF2 : ringChar F = 2) :
    IsPGroup 2 (te6WX θ (te6SL2 θ j hj 3 (sl2Upper (1 : F)))) := by
  refine IsPGroup.of_card (n := 1) ?_
  rw [te6WX, Nat.card_zpowers, orderOf_te6Involution θ j hj hF2, pow_one]

theorem te6WA_le_centralizer_involution (hF2 : ringChar F = 2) :
    te6WA θ j hj g ≤ Subgroup.centralizer
      ({te6SL2 θ j hj 3 (sl2Upper (1 : F))} : Set (fixedGroup k θ)) := by
  rw [te6WA]
  refine sup_le (sup_le ?_ ?_) ?_
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    rw [Set.mem_singleton_iff] at hb
    subst hb
    exact (zpowers_te6SL2_commute θ j hj (g := g) (i := 0) (i' := 3) (by decide) hx
      (sl2Upper 1)).eq.symm
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    rw [Set.mem_singleton_iff] at hb
    subst hb
    exact (zpowers_te6SL2_commute θ j hj (g := g) (i := 1) (i' := 3) (by decide) hx
      (sl2Upper 1)).eq.symm
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    rw [Set.mem_singleton_iff] at hb
    subst hb
    exact (zpowers_te6SL2_commute θ j hj (g := g) (i := 2) (i' := 3) (by decide) hx
      (sl2Upper 1)).eq.symm

theorem te6WB_le_centralizer_involution
    (ht : t * Units.map (θ : k →* k) t = 1) :
    te6WB θ hθ t ≤ Subgroup.centralizer
      ({te6SL2 θ j hj 3 (sl2Upper (1 : F))} : Set (fixedGroup k θ)) := by
  rw [te6WB]
  refine sup_le ?_ ?_
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    rw [Set.mem_singleton_iff] at hb
    subst hb
    exact (zpowers_te6Torus_commute θ hθ j hj ht hx 3 (sl2Upper 1)).eq.symm
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    rw [Set.mem_singleton_iff] at hb
    subst hb
    exact (zpowers_te6TorusB_commute θ hθ j hj ht hx 3 (sl2Upper 1)).eq.symm

theorem te6WE_le_normalizer_te6WX (hF2 : ringChar F = 2)
    (ht : t * Units.map (θ : k →* k) t = 1) :
    te6WE θ hθ j hj g t ≤ Subgroup.normalizer
      (te6WX θ (te6SL2 θ j hj 3 (sl2Upper (1 : F))) : Set (fixedGroup k θ)) := by
  have hle : te6WE θ hθ j hj g t ≤ Subgroup.centralizer
      ({te6SL2 θ j hj 3 (sl2Upper (1 : F))} : Set (fixedGroup k θ)) := by
    rw [te6WE]
    exact sup_le (te6WA_le_centralizer_involution θ j hj hF2)
      (te6WB_le_centralizer_involution θ hθ j hj ht)
  refine hle.trans ?_
  have h_eq : Subgroup.centralizer (Subgroup.zpowers (te6SL2 θ j hj 3 (sl2Upper (1 : F))) :
      Set (fixedGroup k θ)) =
      Subgroup.centralizer ({te6SL2 θ j hj 3 (sl2Upper (1 : F))} : Set (fixedGroup k θ)) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [← h_eq]
  exact Subgroup.centralizer_le_normalizer _

theorem te6WE_inf_center_eq_bot (hr : r.Prime) (hr2 : r ≠ 2) (hF2 : ringChar F = 2) (hg : orderOf g = r)
    (hμ : orderOf t = r) (ht : t * Units.map (θ : k →* k) t = 1)
    (hZ : ¬ r ∣ Nat.card (Subgroup.center (fixedGroup k θ))) :
    te6WE θ hθ j hj g t ⊓ Subgroup.center (fixedGroup k θ) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxE, hxZ⟩ := Subgroup.mem_inf.1 hx
  have hxr : x ^ r = 1 := (isElemAbelian_te6WE θ hθ j hj hr hr2 hF2 hg hμ ht).2 x hxE
  have hdvd : orderOf x ∣ r := orderOf_dvd_iff_pow_eq_one.mpr hxr
  have hdvdZ : orderOf x ∣ Nat.card (Subgroup.center (fixedGroup k θ)) :=
    Subgroup.orderOf_dvd_natCard _ hxZ
  rcases Nat.Prime.eq_one_or_self_of_dvd hr (orderOf x) hdvd with h1 | hr'
  · exact orderOf_eq_one_iff.mp h1
  · exact absurd (hr' ▸ hdvdZ) hZ

theorem te6WX_inf_center_eq_bot (hF2 : ringChar F = 2)
    (hZodd : Odd (Nat.card (Subgroup.center (fixedGroup k θ)))) :
    te6WX θ (te6SL2 θ j hj 3 (sl2Upper (1 : F))) ⊓
      Subgroup.center (fixedGroup k θ) = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨hyX, hyZ⟩ := Subgroup.mem_inf.1 hy
  have hy2 : orderOf y ∣ 2 := by
    have h1 := orderOf_dvd_of_mem_zpowers (x := te6SL2 θ j hj 3 (sl2Upper (1 : F)))
      (by simpa [te6WX] using hyX)
    rw [orderOf_te6Involution θ j hj hF2] at h1
    exact h1
  have hyZ' : orderOf y ∣ Nat.card (Subgroup.center (fixedGroup k θ)) :=
    Subgroup.orderOf_dvd_natCard _ hyZ
  have hyodd : Odd (orderOf y) := Odd.of_dvd_nat hZodd hyZ'
  exact Subgroup.mem_bot.mp (orderOf_eq_one_iff.mp
    ((Nat.dvd_prime Nat.prime_two).1 hy2 |>.elim id
      (fun h => absurd (h ▸ hyodd) (by decide))))

theorem te6WA_inf_center_eq_bot (hF2 : ringChar F = 2) :
    te6WA θ j hj g ⊓ Subgroup.center (fixedGroup k θ) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxA, hxZ⟩ := Subgroup.mem_inf.1 hx
  have hc : ∀ (i : Fin 4) (C : SL(2, F)), Commute x (te6SL2 θ j hj i C) := fun i C =>
    (Subgroup.mem_center_iff.1 hxZ _).symm
  exact Subgroup.mem_bot.2 (eq_one_of_mem_sup_zpowers_te6SL2 θ j hj hF2 hxA (hc 0) (hc 1) (hc 2))

end Target

theorem lieModel_of_markedModel_twE6 {X : Type} [Group X] {lab : GLALabel}
    (htag : lab.tag = .twE6) (h : CFSG.StandardType.MarkedModel lab X) :
    CFSG.Blueprint.LieModel X .twistedE6 0 2 lab.n := by
  obtain ⟨t, l, n⟩ := lab
  simp only at htag
  subst htag
  simpa [CFSG.StandardType.MarkedModel, CFSG.StandardType.markTag,
    CFSG.StandardType.markRank, CFSG.StandardType.markChar,
    CFSG.StandardType.markDeg] using h

theorem card_griessHopfMultiplier_twE6 {k : Type} [Field k] [Finite k] {σ : k →+* k}
    {q : ℕ} (hq : 3 ≤ q) (hkq : Nat.card k = q ^ 2) (hσ : ∀ c, σ c = c ^ q) :
    Nat.card (CFSG.Open.griessHopfMultiplier
      (DerivedCentralQuotient (twistedFixedGroup .E6 k σ))) = Nat.gcd 3 (q + 1) := by
  obtain ⟨-, ⟨eM⟩⟩ :=
    CFSG.LieType.Steinberg.CentralExt.GriessExceptional.twistedE6_hopfMultiplier
      (θ := σ) (q := q) hq hkq hσ
  rw [Nat.card_congr eM.toEquiv,
    Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod (Nat.gcd 3 (q + 1))) ≃
      ZMod (Nat.gcd 3 (q + 1))), Nat.card_zmod]

theorem rk2_low_twe6_of_ne_three (K : Type) [Group K] [Finite K] (lab : GLALabel)
    (hK : Rk2IsLabel K lab) (htag : lab.tag = .twE6) (hn : 2 ≤ lab.n) (hn3 : lab.n ≠ 3) :
    5 ≤ evenRank K := by
  classical
  obtain ⟨hQ, -, hM⟩ := rk2_model_of_isLabel hK
  have hQ' : CFSG.IsQuasisimple K :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff K).2.2.1.2 hQ
  have hM' : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .twistedE6 0 2 lab.n :=
    lieModel_of_markedModel_twE6 htag hM
  obtain ⟨-, hf, hT⟩ :=
    CFSG.HardMathSupport.Timmesfeld.Tables.T1b.twistedChevalleyModel_of_lieModel hM'
  obtain ⟨k, hkfield, hkfin, hkcard, σ, hσ, ⟨e⟩⟩ := hT
  letI : Field k := hkfield
  letI : Finite k := hkfin
  letI : Fintype k := Fintype.ofFinite k
  have hkcard' : Nat.card k = (2 ^ lab.n) ^ 2 := by
    rw [hkcard]
    rfl
  have h2n : 2 ≤ 2 ^ lab.n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ lab.n := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hk4 : 4 ≤ Nat.card k := by
    rw [hkcard']
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ (2 ^ lab.n) ^ 2 := Nat.pow_le_pow_left h2n 2
  obtain ⟨σ₀, hσ₀, -, hσ₀2, S, hSmem, hScard⟩ :=
    CFSG.LinearGroups.finite_field_quadratic_frobenius (K := k) Nat.prime_two (by omega)
      hkcard'
  have hσeq : (σ : k →+* k) = (σ₀ : k →+* k) := by
    ext c
    exact (hσ c).trans (hσ₀ c).symm
  have hθ : ∀ c, σ (σ c) = c := by
    intro c
    change (σ : k →+* k) ((σ : k →+* k) c) = c
    rw [hσeq]
    have h2 := congrArg (fun f : k ≃+* k => f c) hσ₀2
    simpa [pow_two, RingAut.mul_apply] using h2
  have hSs : (σ : k →+* k).eqLocusField (RingHom.id k) = S := by
    ext c
    rw [RingHom.mem_eqLocusField, hSmem c, hσ c]
    exact Iff.rfl
  let j : S →+* k := S.subtype
  have hj : ∀ x, σ (j x) = j x := by
    intro x
    have hx : (x : k) ∈ (σ : k →+* k).eqLocusField (RingHom.id k) := by
      rw [hSs]; exact x.2
    exact RingHom.mem_eqLocusField.mp hx
  haveI : CharP k 2 := charP_of_card_eq_prime_pow (f := 2 * lab.n) (by
    rw [← Nat.card_eq_fintype_card, hkcard', ← pow_mul, mul_comm])
  haveI : CharP S 2 := (RingHom.charP_iff S.subtype S.subtype.injective 2).mpr inferInstance
  have hF2 : ringChar S = 2 := ringChar.eq S 2
  obtain ⟨r, hrr, hr5, hrdvd⟩ :=
    CFSG.RankThree.PartTwo.Census.exists_prime_five_le_dvd_two_pow_add_one hn hn3
  have hr2 : r ≠ 2 := by omega
  have h2n : 2 ^ (2 * lab.n) - 1 = (2 ^ lab.n + 1) * (2 ^ lab.n - 1) := by
    rw [show 2 * lab.n = lab.n * 2 by ring, pow_mul]
    simpa using Nat.sq_sub_sq (2 ^ lab.n) 1
  have hdvd2 : r ∣ 2 ^ (2 * lab.n) - 1 := by
    rw [h2n]
    exact Dvd.dvd.mul_right hrdvd _
  haveI : Fact r.Prime := ⟨hrr⟩
  obtain ⟨g, hg⟩ := CFSG.Quasithin.Vol2.Ch11.SecA.C10KH.exists_orderOf_sl2
    (K := S) (n := lab.n) (p := r) hScard hdvd2
  have hdvdK : r ∣ Nat.card k - 1 := by
    rw [hkcard']
    have hfac : (2 ^ lab.n) ^ 2 - 1 = (2 ^ lab.n + 1) * (2 ^ lab.n - 1) :=
      Nat.sq_sub_sq (2 ^ lab.n) 1
    rw [hfac]
    exact Dvd.dvd.mul_right hrdvd _
  obtain ⟨t, hμ⟩ :=
    CFSG.HardMathSupport.Timmesfeld.Tables.T1b.exists_orderOf_units (K := k) hdvdK
  have htq : t ^ (2 ^ lab.n + 1) = 1 := orderOf_dvd_iff_pow_eq_one.1 (hμ ▸ hrdvd)
  have hθt : Units.map (σ : k →* k) t = t⁻¹ :=
    CFSG.HardMathSupport.Timmesfeld.Tables.T1b.units_map_eq_inv (σ := σ) hσ htq
  have ht : t * Units.map (σ : k →* k) t = 1 := by rw [hθt, mul_inv_cancel]
  have hZcard :=
    CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed.card_center_fixedGroup (θ := σ) hkcard' hσ
  have hZ : ¬ r ∣ Nat.card (Subgroup.center (fixedGroup k σ)) := by
    rw [hZcard.1]
    intro h
    have h3 : r ∣ 3 := h.trans (Nat.gcd_dvd_left 3 (2 ^ lab.n + 1))
    have h3' : r = 3 := (Nat.prime_dvd_prime_iff_eq hrr Nat.prime_three).1 h3
    omega
  have hZodd : Odd (Nat.card (Subgroup.center (fixedGroup k σ))) := by
    rw [hZcard.1]
    exact Odd.of_dvd_nat (by decide : Odd 3) (Nat.gcd_dvd_left 3 _)
  let E : Subgroup (fixedGroup k σ) := te6WE σ hθ j hj g t
  let X : Subgroup (fixedGroup k σ) := te6WX σ (te6SL2 σ j hj 3 (sl2Upper (1 : S)))
  have hXne : X ≠ ⊥ := te6WX_ne_bot σ j hj hF2
  have hX2 : IsPGroup 2 X := isPGroup_te6WX σ j hj hF2
  have hE : IsElemAbelian r E := isElemAbelian_te6WE σ hθ j hj hrr hr2 hF2 hg hμ ht
  have hEcard : Nat.card E = r ^ 5 := card_te6WE σ hθ j hj hrr hr2 hF2 hg hμ ht
  have hEnorm : E ≤ Subgroup.normalizer (X : Set (fixedGroup k σ)) :=
    te6WE_le_normalizer_te6WX σ hθ j hj hF2 ht
  have hXcenter : X ⊓ Subgroup.center (fixedGroup k σ) = ⊥ :=
    te6WX_inf_center_eq_bot σ j hj hF2 hZodd
  have hEcenter : E ⊓ Subgroup.center (fixedGroup k σ) = ⊥ :=
    te6WE_inf_center_eq_bot σ hθ j hj hrr hr2 hF2 hg hμ ht hZ
  have hZt : Subgroup.center ↥(CFSG.HardMathSupport.Timmesfeld.Tables.T1b.twDerived σ) = ⊥ :=
    CFSG.HardMathSupport.Timmesfeld.Tables.T1b.center_twDerived_eq_bot (σ := σ)
      Nat.prime_two (by omega) hkcard' hσ
  let θm : (K ⧸ Subgroup.center K) ≃*
      ↥(CFSG.HardMathSupport.Timmesfeld.Tables.T1b.twDerived σ) :=
    e.trans (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.derivedCentralQuotientEquiv σ hZt)
  have hZcop : ¬ r ∣ Nat.card (Subgroup.center K) := by
    have hcardM : Nat.card (CFSG.Open.griessHopfMultiplier (K ⧸ Subgroup.center K)) =
        Nat.gcd 3 (2 ^ lab.n + 1) := by
      rw [Nat.card_congr
        (CFSG.LieType.Steinberg.CentralExt.griessHopfMultiplierCongr e).toEquiv]
      exact card_griessHopfMultiplier_twE6 (q := 2 ^ lab.n) (by
        calc 3 ≤ 2 ^ 2 := by norm_num
          _ ≤ 2 ^ lab.n := Nat.pow_le_pow_right (by norm_num) hn) hkcard' hσ
    haveI : Finite (CFSG.Open.griessHopfMultiplier (K ⧸ Subgroup.center K)) :=
      Nat.finite_of_card_ne_zero (by rw [hcardM]; exact (Nat.gcd_pos_of_pos_left _ (by norm_num)).ne')
    have hdvd := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_center_dvd_hopf hQ'
      (MulEquiv.refl (K ⧸ Subgroup.center K))
    rw [hcardM] at hdvd
    intro h
    have h3 : r ∣ 3 := h.trans (hdvd.trans (Nat.gcd_dvd_left 3 (2 ^ lab.n + 1)))
    have h3' : r = 3 := (Nat.prime_dvd_prime_iff_eq hrr Nat.prime_three).1 h3
    omega
  let ψ : ↥(fixedGroup k σ) →*
      ↥(CFSG.HardMathSupport.Timmesfeld.Tables.T1b.twDerived σ) :=
    CFSG.HardMathSupport.Timmesfeld.Tables.T1b.twIsog σ hθ hk4
  have hEker : E ⊓ ψ.ker = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxE, hxK⟩ := Subgroup.mem_inf.1 hx
    have hxZ : x ∈ Subgroup.center (fixedGroup k σ) :=
      CFSG.HardMathSupport.Timmesfeld.Tables.T1b.mem_center_of_twIsog_eq_one σ hθ hk4 hxK
    have := Subgroup.mem_inf.2 ⟨hxE, hxZ⟩
    rw [hEcenter] at this
    exact Subgroup.mem_bot.mp this
  have hXker : X ⊓ ψ.ker = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨hyX, hyK⟩ := Subgroup.mem_inf.1 hy
    have hyZ : y ∈ Subgroup.center (fixedGroup k σ) :=
      CFSG.HardMathSupport.Timmesfeld.Tables.T1b.mem_center_of_twIsog_eq_one σ hθ hk4 hyK
    have := Subgroup.mem_inf.2 ⟨hyX, hyZ⟩
    rw [hXcenter] at this
    exact Subgroup.mem_bot.mp this
  have hXmap : X.map ψ ≠ ⊥ := by
    intro h
    have hle : X ≤ ψ.ker := (Subgroup.map_eq_bot_iff (f := ψ) (H := X)).1 h
    have hsub : X ≤ X ⊓ ψ.ker := fun x hx => ⟨hx, hle hx⟩
    rw [hXker] at hsub
    exact hXne (le_bot_iff.mp hsub)
  refine le_evenRank_of_center_quotient θm hrr hr2 hZcop hXmap (hX2.map ψ)
    (CFSG.SectionRank.isElemAbelian_map hE ψ) ?_
    ((Subgroup.map_mono hEnorm).trans (X.le_normalizer_map ψ))
  rw [CFSG.Quasithin.Ch1Sec3.card_map_of_inf_ker_eq_bot (φ := ψ) (P := E) hEker, hEcard]

theorem four_le_localRank_three_twDerived {k : Type} [Field k] [Finite k]
    (σ : k →+* k) (hθ : ∀ c, σ (σ c) = c) (hk : 4 ≤ Nat.card k)
    {F : Type} [Field F] [Finite F] (j : F →+* k) (hj : ∀ x, σ (j x) = j x)
    (hF2 : ringChar F = 2) {t : kˣ} (htt : t * Units.map (σ : k →* k) t = 1)
    (ht3 : t ^ 3 = 1) (ht2 : ((t : k)) ^ 2 ≠ 1) :
    4 ≤ CFSG.Assembly.RankThreeEven.localRank 3 ↥(CFSG.HardMathSupport.Timmesfeld.Tables.T1b.twDerived σ) := by
  have hinj : ∀ i, Function.Injective
      ((CFSG.HardMathSupport.Timmesfeld.Tables.T1b.twIsog σ hθ hk).comp
        (te6SL2 σ j hj i)) := by
    intro i A B hAB
    have hprod : te6SL2 σ j hj i (A * B⁻¹) =
        te6SL2 σ j hj i A * (te6SL2 σ j hj i B)⁻¹ := by rw [map_mul, map_inv]
    have hz : CFSG.HardMathSupport.Timmesfeld.Tables.T1b.twIsog σ hθ hk
        (te6SL2 σ j hj i (A * B⁻¹)) = 1 := by
      rw [hprod, map_mul, map_inv]
      exact mul_inv_eq_one.mpr hAB
    have hmem := CFSG.HardMathSupport.Timmesfeld.Tables.T1b.mem_center_of_twIsog_eq_one
      σ hθ hk hz
    have h1 : A * B⁻¹ = 1 := te6SL2_central σ j hj i hmem
    exact mul_inv_eq_one.mp h1
  exact four_le_localRank_three_te6 σ j hj hθ
    (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.twIsog σ hθ hk)
    (fun g hg =>
      CFSG.HardMathSupport.Timmesfeld.Tables.T1b.mem_center_of_twIsog_eq_one σ hθ hk hg)
    hinj hF2 htt ht3 ht2

theorem liftDatum_twDerived_two {k : Type} [Field k] [Finite k]
    (σ : k →+* k) (hθ : ∀ c, σ (σ c) = c) (hk : 4 ≤ Nat.card k)
    {F : Type} [Field F] [Finite F] (j : F →+* k) (hj : ∀ x, σ (j x) = j x)
    (hF2 : ringChar F = 2) {t : kˣ} (htt : t * Units.map (σ : k →* k) t = 1)
    (ht3 : t ^ 3 = 1) (ht2 : ((t : k)) ^ 2 ≠ 1) :
    CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.ExcRank.LiftDatum
      ↥(CFSG.HardMathSupport.Timmesfeld.Tables.T1b.twDerived σ) 2 := by
  classical
  letI := Fintype.ofFinite k
  let ψ : ↥(fixedGroup k σ) →* ↥(CFSG.HardMathSupport.Timmesfeld.Tables.T1b.twDerived σ) :=
    CFSG.HardMathSupport.Timmesfeld.Tables.T1b.twIsog σ hθ hk
  have hinj : ∀ i : Fin 4, Function.Injective (ψ.comp (te6SL2 σ j hj i)) := by
    intro i A B hAB
    have hprod : te6SL2 σ j hj i (A * B⁻¹) =
        te6SL2 σ j hj i A * (te6SL2 σ j hj i B)⁻¹ := by rw [map_mul, map_inv]
    have hz : ψ (te6SL2 σ j hj i (A * B⁻¹)) = 1 := by
      rw [hprod, map_mul, map_inv]
      exact mul_inv_eq_one.mpr hAB
    have hmem := CFSG.HardMathSupport.Timmesfeld.Tables.T1b.mem_center_of_twIsog_eq_one
      σ hθ hk hz
    have h1 : A * B⁻¹ = 1 := te6SL2_central σ j hj i hmem
    exact mul_inv_eq_one.mp h1
  let i02 : Fin 2 → Fin 4 := fun i => i.castLE (by omega)
  have hi02 : ∀ i i' : Fin 2, i ≠ i' → i02 i ≠ i02 i' := by
    intro i i' hii h
    exact hii (Fin.castLE_injective (by omega) h)
  have hcomm : ∀ i i' : Fin 2, i ≠ i' → ∀ A B : SL(2, F),
      (ψ.comp (te6SL2 σ j hj (i02 i))) A * (ψ.comp (te6SL2 σ j hj (i02 i'))) B =
      (ψ.comp (te6SL2 σ j hj (i02 i'))) B * (ψ.comp (te6SL2 σ j hj (i02 i))) A := by
    intro i i' hii A B
    simp only [MonoidHom.comp_apply, ← map_mul,
      te6SL2_commute σ j hj (hi02 i i' hii) A B]
  have hu : orderOf (ψ (te6SL2 σ j hj 3 (sl2Upper (1 : F)))) = 2 := by
    change orderOf ((ψ.comp (te6SL2 σ j hj 3)) (sl2Upper (1 : F))) = 2
    rw [orderOf_injective _ (hinj 3), orderOf_sl2Upper_one hF2]
  have hτ3 : ψ (te6Torus σ hθ t) ^ 3 = 1 := by
    rw [← map_pow, te6Torus_pow, ht3, te6Torus_one, map_one]
  have hτ1 : ψ (te6Torus σ hθ t) ≠ 1 := by
    intro h
    exact te6Torus_not_mem_center σ hθ ht2
      (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.mem_center_of_twIsog_eq_one σ hθ hk h)
  have hφu : ∀ i : Fin 2, ∀ A : SL(2, F),
      (ψ.comp (te6SL2 σ j hj (i02 i))) A * ψ (te6SL2 σ j hj 3 (sl2Upper (1 : F))) =
      ψ (te6SL2 σ j hj 3 (sl2Upper (1 : F))) * (ψ.comp (te6SL2 σ j hj (i02 i))) A := by
    intro i A
    simp only [MonoidHom.comp_apply, ← map_mul, ← map_mul]
    rw [show te6SL2 σ j hj (i02 i) A * te6SL2 σ j hj 3 (sl2Upper (1 : F)) =
      te6SL2 σ j hj 3 (sl2Upper (1 : F)) * te6SL2 σ j hj (i02 i) A from
      te6SL2_commute σ j hj (by
        have hval : (i02 i).val = i.val := rfl
        intro h
        have := congrArg Fin.val h
        simp at this
        omega) A (sl2Upper (1 : F))]
  have hτφ : ∀ i : Fin 2, ∀ A : SL(2, F),
      (ψ.comp (te6SL2 σ j hj (i02 i))) A * ψ (te6Torus σ hθ t) =
      ψ (te6Torus σ hθ t) * (ψ.comp (te6SL2 σ j hj (i02 i))) A := by
    intro i A
    change ψ ((te6SL2 σ j hj (i02 i)) A) * ψ (te6Torus σ hθ t) =
      ψ (te6Torus σ hθ t) * ψ ((te6SL2 σ j hj (i02 i)) A)
    calc ψ ((te6SL2 σ j hj (i02 i)) A) * ψ (te6Torus σ hθ t)
        = ψ ((te6SL2 σ j hj (i02 i)) A * te6Torus σ hθ t) := (map_mul ψ _ _).symm
      _ = ψ (te6Torus σ hθ t * (te6SL2 σ j hj (i02 i)) A) :=
          congrArg ψ (te6Torus_commute σ j hj hθ htt (i02 i) A).symm
      _ = ψ (te6Torus σ hθ t) * ψ ((te6SL2 σ j hj (i02 i)) A) := map_mul ψ _ _
  have hτu : ψ (te6Torus σ hθ t) * ψ (te6SL2 σ j hj 3 (sl2Upper (1 : F))) =
      ψ (te6SL2 σ j hj 3 (sl2Upper (1 : F))) * ψ (te6Torus σ hθ t) := by
    calc ψ (te6Torus σ hθ t) * ψ ((te6SL2 σ j hj 3) (sl2Upper (1 : F)))
        = ψ (te6Torus σ hθ t * (te6SL2 σ j hj 3) (sl2Upper (1 : F))) := (map_mul ψ _ _).symm
      _ = ψ ((te6SL2 σ j hj 3) (sl2Upper (1 : F)) * te6Torus σ hθ t) :=
          congrArg ψ (te6Torus_commute σ j hj hθ htt 3 (sl2Upper (1 : F)))
      _ = ψ ((te6SL2 σ j hj 3) (sl2Upper (1 : F))) * ψ (te6Torus σ hθ t) := map_mul ψ _ _
  have hgτ : ψ (nHat σ (nf 3)) * ψ (te6Torus σ hθ t) * (ψ (nHat σ (nf 3)))⁻¹ =
      (ψ (te6Torus σ hθ t))⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul, ← CFSG.HardMathSupport.Timmesfeld.Tables.T1b.twT05_eq_te6Torus, CFSG.HardMathSupport.Timmesfeld.Tables.T1b.nHat_conj_twT05, map_inv]
  exact CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.ExcRank.liftDatum_of_commuting_SL2_torus
    hF2 (m := 2) (fun i : Fin 2 => ψ.comp (te6SL2 σ j hj (i02 i))) (fun i => hinj _)
    hcomm hu hτ3 hτ1 hφu hτφ hτu hgτ

theorem center_card_dvd_twelve {K : Type} [Group K] [Finite K] (lab : GLALabel)
    (hK : Rk2IsLabel K lab) (htag : lab.tag = .twE6) (hn : lab.n = 1) :
    Nat.card (Subgroup.center K) ∣ 12 := by
  obtain ⟨hQ, -, hM⟩ := rk2_model_of_isLabel hK
  have hQ' : CFSG.IsQuasisimple K :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff K).2.2.1.2 hQ
  have hM' : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .twistedE6 0 2 lab.n :=
    lieModel_of_markedModel_twE6 htag hM
  have hM1 : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .twistedE6 0 2 1 := by
    simpa [hn] using hM'
  obtain ⟨-, ⟨eM⟩⟩ :=
    CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoCover.twistedE6TwoMultiplier
      (K ⧸ Subgroup.center K) hM1
  have hcardM : Nat.card (CFSG.Open.griessHopfMultiplier (K ⧸ Subgroup.center K)) = 12 := by
    rw [Nat.card_congr eM.toEquiv]
    simp [Nat.card_zmod]
  haveI : Finite (CFSG.Open.griessHopfMultiplier (K ⧸ Subgroup.center K)) :=
    Nat.finite_of_card_ne_zero (by rw [hcardM]; norm_num)
  have h := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_center_dvd_hopf hQ'
    (MulEquiv.refl (K ⧸ Subgroup.center K))
  rwa [hcardM] at h

theorem exists_twDerived_data_one (K : Type) [Group K] [Finite K] (lab : GLALabel)
    (hK : Rk2IsLabel K lab) (htag : lab.tag = .twE6) (hn : lab.n = 1) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k) (σ : k →+* k),
      Nonempty (K ⧸ Subgroup.center K ≃* CFSG.HardMathSupport.Timmesfeld.Tables.T1b.twDerived σ) ∧
      4 ≤ CFSG.Assembly.RankThreeEven.localRank 3 ↥(CFSG.HardMathSupport.Timmesfeld.Tables.T1b.twDerived σ) ∧
      CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.ExcRank.LiftDatum
        ↥(CFSG.HardMathSupport.Timmesfeld.Tables.T1b.twDerived σ) 2 := by
  classical
  obtain ⟨hQ, -, hM⟩ := rk2_model_of_isLabel hK
  have hM' : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .twistedE6 0 2 lab.n :=
    lieModel_of_markedModel_twE6 htag hM
  obtain ⟨-, hf, hT⟩ :=
    CFSG.HardMathSupport.Timmesfeld.Tables.T1b.twistedChevalleyModel_of_lieModel hM'
  obtain ⟨k, hkfield, hkfin, hkcard, σ, hσ, ⟨e⟩⟩ := hT
  letI : Field k := hkfield
  letI : Finite k := hkfin
  letI : Fintype k := Fintype.ofFinite k
  have hkcard' : Nat.card k = (2 ^ lab.n) ^ 2 := by
    rw [hkcard]
    rfl
  have hk4 : 4 ≤ Nat.card k := by
    rw [hkcard']
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ (2 ^ lab.n) ^ 2 := Nat.pow_le_pow_left (by
          calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ lab.n := Nat.pow_le_pow_right (by norm_num) (by omega)) 2
  obtain ⟨σ₀, hσ₀, -, hσ₀2, S, hSmem, hScard⟩ :=
    CFSG.LinearGroups.finite_field_quadratic_frobenius (K := k) Nat.prime_two (by omega) hkcard'
  have hσeq : (σ : k →+* k) = (σ₀ : k →+* k) := by
    ext c
    exact (hσ c).trans (hσ₀ c).symm
  have hθ : ∀ c, σ (σ c) = c := by
    intro c
    change (σ : k →+* k) ((σ : k →+* k) c) = c
    rw [hσeq]
    have h2 := congrArg (fun f : k ≃+* k => f c) hσ₀2
    simpa [pow_two, RingAut.mul_apply] using h2
  have hSs : (σ : k →+* k).eqLocusField (RingHom.id k) = S := by
    ext c
    rw [RingHom.mem_eqLocusField, hSmem c, hσ c]
    exact Iff.rfl
  let j : S →+* k := S.subtype
  have hj : ∀ x, σ (j x) = j x := by
    intro x
    have hx : (x : k) ∈ (σ : k →+* k).eqLocusField (RingHom.id k) := by
      rw [hSs]; exact x.2
    exact RingHom.mem_eqLocusField.mp hx
  haveI : CharP k 2 := charP_of_card_eq_prime_pow (f := 2 * lab.n) (by
    rw [← Nat.card_eq_fintype_card, hkcard', ← pow_mul, mul_comm])
  haveI : CharP S 2 := (RingHom.charP_iff S.subtype S.subtype.injective 2).mpr inferInstance
  have hF2 : ringChar S = 2 := ringChar.eq S 2
  have hdvd : 3 ∣ Nat.card k - 1 := by
    rw [hkcard']
    have hfac : (2 ^ lab.n) ^ 2 - 1 = (2 ^ lab.n + 1) * (2 ^ lab.n - 1) :=
      Nat.sq_sub_sq (2 ^ lab.n) 1
    rw [hfac]
    have h3 : (3 : ℕ) ∣ 2 ^ lab.n + 1 := by
      rw [hn]; norm_num
    exact Dvd.dvd.mul_right h3 _
  obtain ⟨t, hμ⟩ :=
    CFSG.HardMathSupport.Timmesfeld.Tables.T1b.exists_orderOf_units (K := k) hdvd
  have htq : t ^ (2 ^ lab.n + 1) = 1 := orderOf_dvd_iff_pow_eq_one.1 (hμ ▸ (by
    rw [hn]; norm_num : (3 : ℕ) ∣ 2 ^ lab.n + 1))
  have hθt : Units.map (σ : k →* k) t = t⁻¹ :=
    CFSG.HardMathSupport.Timmesfeld.Tables.T1b.units_map_eq_inv (σ := σ) hσ htq
  have ht : t * Units.map (σ : k →* k) t = 1 := by rw [hθt, mul_inv_cancel]
  have ht3 : t ^ 3 = 1 := by
    rw [← hμ]
    norm_num
  have ht2 : ((t : k)) ^ 2 ≠ 1 := by
    intro h
    have h' : t ^ 2 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, h, Units.val_one])
    have hdvd2 : orderOf t ∣ 2 := orderOf_dvd_of_pow_eq_one h'
    rw [hμ] at hdvd2
    omega
  have hZt : Subgroup.center ↥(CFSG.HardMathSupport.Timmesfeld.Tables.T1b.twDerived σ) = ⊥ :=
    CFSG.HardMathSupport.Timmesfeld.Tables.T1b.center_twDerived_eq_bot (σ := σ)
      Nat.prime_two (by omega) hkcard' hσ
  refine ⟨k, hkfield, hkfin, σ, ⟨e.trans (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.derivedCentralQuotientEquiv σ hZt)⟩, ?_, ?_⟩
  · exact four_le_localRank_three_twDerived σ hθ hk4 j hj hF2 ht ht3 ht2
  · exact liftDatum_twDerived_two σ hθ hk4 j hj hF2 ht ht3 ht2

theorem odd_card_map_center_quotient_sylow (K : Type) [Group K] [Finite K]
    (P : Sylow 2 (Subgroup.center K)) (N : Subgroup K) [N.Normal]
    (hN : N = (P : Subgroup (Subgroup.center K)).map (Subgroup.center K).subtype) :
    Odd (Nat.card ((Subgroup.center K).map (QuotientGroup.mk' N))) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  subst hN
  let Z : Subgroup K := Subgroup.center K
  let N' : Subgroup K := (P : Subgroup Z).map Z.subtype
  have hNZ : N' ≤ Z := Subgroup.map_subtype_le _
  haveI : N'.Normal := CFSG.GroupTheory.normal_of_le_center hNZ
  change Odd (Nat.card (Z.map (QuotientGroup.mk' N')))
  let f : Z →* (Z.map (QuotientGroup.mk' N')) :=
    ((QuotientGroup.mk' N').comp Z.subtype).codRestrict _
      (fun z => Subgroup.mem_map_of_mem (QuotientGroup.mk' N') z.2)
  have hfsurj : Function.Surjective f := by
    rintro ⟨x, hx⟩
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hx
    exact ⟨⟨z, hz⟩, rfl⟩
  have hfker : f.ker = (P : Subgroup Z) := by
    ext z
    rw [MonoidHom.mem_ker]
    constructor
    · intro hz
      have hz1 : (QuotientGroup.mk' N') (z : Z) = 1 := by
        have := congrArg Subtype.val hz
        simpa [f] using this
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hz1
      obtain ⟨p, hp, hpeq⟩ := Subgroup.mem_map.mp hz1
      have hzp : p = z := Subtype.ext hpeq
      simpa [hzp] using hp
    · intro hz
      apply Subtype.ext
      change (QuotientGroup.mk' N') (z : Z) = 1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact Subgroup.mem_map_of_mem Z.subtype hz
  have hcard : Nat.card (Z.map (QuotientGroup.mk' N')) = (P : Subgroup Z).index := by
    have h1 : Nat.card (Z ⧸ f.ker) = Nat.card f.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
    have h2 : Nat.card f.range = Nat.card (Z.map (QuotientGroup.mk' N')) := by
      rw [MonoidHom.range_eq_top.2 hfsurj]
      exact Nat.card_congr Subgroup.topEquiv.toEquiv
    rw [hfker] at h1
    exact (h2.symm.trans h1.symm).trans (Subgroup.index_eq_card (P : Subgroup Z)).symm
  rw [hcard]
  exact Nat.not_even_iff_odd.mp (fun he =>
    Sylow.not_dvd_index P (even_iff_two_dvd.mp he))

theorem four_le_localRank_three_of_twoPart_center (K : Type) [Group K] [Finite K]
    (hZ12 : Nat.card (Subgroup.center K) ∣ 12)
    {S : Type} [Group S] [Finite S] (e : K ⧸ Subgroup.center K ≃* S)
    (hS : 4 ≤ CFSG.Assembly.RankThreeEven.localRank 3 S)
    (hL : CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.ExcRank.LiftDatum S 2)
    (N : Subgroup K) [N.Normal] (hNZ : N ≤ Subgroup.center K)
    (hodd : Odd (Nat.card ((Subgroup.center K).map (QuotientGroup.mk' N)))) :
    4 ≤ CFSG.Assembly.RankThreeEven.localRank 3 (K ⧸ N) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Z : Subgroup K := Subgroup.center K
  have hNZ' : N ≤ Z := hNZ
  have hNZid : N ≤ Subgroup.comap (MonoidHom.id K) Z := by simpa using hNZ'
  let πZ : K ⧸ N →* K ⧸ Z :=
    QuotientGroup.map N Z (MonoidHom.id K) hNZid
  let π : K ⧸ N →* S := e.toMonoidHom.comp πZ
  have hπZsurj : Function.Surjective πZ :=
    QuotientGroup.map_surjective_of_surjective N Z (MonoidHom.id K)
      (by simpa using QuotientGroup.mk_surjective) hNZid
  have hπsurj : Function.Surjective π := e.surjective.comp hπZsurj
  have hπker : π.ker = Z.map (QuotientGroup.mk' N) := by
    change (e.toMonoidHom.comp πZ).ker = _
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective]
    exact QuotientGroup.ker_map N Z (MonoidHom.id K) hNZid
  have hπodd : Odd (Nat.card π.ker) := by rw [hπker]; exact hodd
  have hπcen : π.ker ≤ Subgroup.center (K ⧸ N) := by
    rw [hπker]
    exact Subgroup.map_center_le_center (QuotientGroup.mk'_surjective N)
  by_cases hker : π.ker = ⊥
  · have hinj : Function.Injective π := (MonoidHom.ker_eq_bot_iff π).mp hker
    let eπ : (K ⧸ N) ≃* S := MulEquiv.ofBijective π ⟨hinj, hπsurj⟩
    rw [CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv eπ Nat.prime_three]
    exact hS
  · have hkerdvd : Nat.card π.ker ∣ 12 := by
      rw [hπker]
      exact (Subgroup.card_map_dvd _ _).trans hZ12
    have hkerne : Nat.card π.ker ≠ 1 := by
      intro h1
      exact hker (Subgroup.card_eq_one.mp h1)
    have hker3 : Nat.card π.ker = 3 := by
      let n := Nat.card π.ker
      have hnodd : Odd n := hπodd
      have hnne : n ≠ 1 := hkerne
      have hn4 : n.Coprime 4 := by
        have h2 : n.Coprime 2 := Nat.coprime_two_right.mpr hnodd
        simpa using Nat.Coprime.pow_right 2 h2
      have hndvd3 : n ∣ 3 := by
        have h : n ∣ 4 * 3 := by simpa [n] using hkerdvd
        exact Nat.Coprime.dvd_of_dvd_mul_left hn4 h
      rcases (Nat.dvd_prime Nat.prime_three).1 hndvd3 with h1 | h3
      · exact absurd h1 hnne
      · exact h3
    have hA3 : ∀ x ∈ π.ker, x ^ 3 = 1 := by
      intro x hx
      have := Subgroup.orderOf_dvd_natCard π.ker hx
      rw [hker3] at this
      exact orderOf_dvd_iff_pow_eq_one.mp this
    have := CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.ExcRank.LiftDatum.cover_localRank
      (K := K ⧸ N) (S := S) (m := 2) hL hπsurj hπcen hπodd (A := π.ker) le_rfl hA3
      (k := 1) (by rw [hker3]; norm_num)
    simpa using this

private theorem four_le_evenRank_of_two_part_center (K : Type) [Group K] [Finite K]
    (hZ12 : Nat.card (Subgroup.center K) ∣ 12)
    {S : Type} [Group S] [Finite S] (e : K ⧸ Subgroup.center K ≃* S)
    (hS : 4 ≤ CFSG.Assembly.RankThreeEven.localRank 3 S)
    (hL : CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.ExcRank.LiftDatum S 2) :
    4 ≤ evenRank K := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Z : Subgroup K := Subgroup.center K
  let P : Sylow 2 Z := default
  let N : Subgroup K := (P : Subgroup Z).map Z.subtype
  have hNZ : N ≤ Z := Subgroup.map_subtype_le _
  have hNnormal : N.Normal := CFSG.GroupTheory.normal_of_le_center hNZ
  haveI : N.Normal := hNnormal
  have hNP2 : IsPGroup 2 N := P.isPGroup'.map Z.subtype
  have hN3 : ¬ 3 ∣ Nat.card N := by
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hNP2
    rw [hm]
    intro h
    exact absurd (Nat.prime_three.dvd_of_dvd_pow h) (by norm_num)
  have hodd := odd_card_map_center_quotient_sylow K P N rfl
  have hloc : 4 ≤ CFSG.Assembly.RankThreeEven.localRank 3 (K ⧸ N) :=
    four_le_localRank_three_of_twoPart_center K hZ12 e hS hL N hNZ hodd
  obtain ⟨U, hU2, hU0, E, hEN, hEel, hEcard⟩ :=
    CFSG.RankThree.PartOne.exists_elemAbelian_of_le_localRank Nat.prime_three
      (k := 4) (by norm_num) hloc
  exact CFSG.LocalAnalysis.GLTheoremA.le_evenRank_of_quotient Nat.prime_three (by norm_num)
    hN3 hU0 hU2 ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 E).1 hEel)
    hEcard hEN

theorem rk2_low_twe6_one (K : Type) [Group K] [Finite K] (lab : GLALabel)
    (hK : Rk2IsLabel K lab) (htag : lab.tag = .twE6) (hn : lab.n = 1) :
    4 ≤ evenRank K := by
  obtain ⟨k, hkfield, hkfin, σ, ⟨e⟩, hS, hL⟩ :=
    exists_twDerived_data_one K lab hK htag hn
  letI : Field k := hkfield
  letI : Finite k := hkfin
  exact four_le_evenRank_of_two_part_center K
    (center_card_dvd_twelve lab hK htag hn) e hS hL

end CFSG.LocalAnalysis.GLTheoremA
