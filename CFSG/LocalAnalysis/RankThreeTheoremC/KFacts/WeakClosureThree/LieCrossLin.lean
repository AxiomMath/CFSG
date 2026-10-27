module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureThree.Cycle
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureThree.LieDispatch
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureThree.OuterArith
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.CrossPSL

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureThree

open CFSG.Open CFSG.Open.StatedAPI CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.RankThree.PartOne.StrongP (HasNoncommPair)
open CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput)
open scoped commutatorElement

theorem exists_orderOf_eq_of_dvd_card_sub_one {F : Type} [Field F] [Finite F] {d : ℕ}
    (hd : d ∣ Nat.card F - 1) : ∃ ζ : Fˣ, orderOf ζ = d := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
  rw [Nat.card_units] at hg
  refine ⟨g ^ (orderOf g / d), orderOf_pow_orderOf_div ?_ (hg ▸ hd)⟩
  rw [hg]
  have := Finite.one_lt_card (α := F)
  omega

namespace ProjLin

variable {L : Type} [Field L]

theorem diagGL_apply_self {n : ℕ} (u : Fin n → Lˣ) (i : Fin n) :
    ((diagGL n u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i = u i := by
  rw [coe_diagGL, Matrix.diagonal_apply_eq]

theorem mk_diagGL_ne_one {n : ℕ} {H : Subgroup (GL (Fin n) L)} {u : Fin n → Lˣ}
    (hu : diagGL n u ∈ H) {i j : Fin n} (hij : u i ≠ u j) :
    (QuotientGroup.mk (⟨diagGL n u, hu⟩ : H) : StatedProj H) ≠ 1 := by
  intro h
  obtain ⟨s, hs⟩ := Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 h)
  have hs' : (Matrix.GeneralLinearGroup.scalar (Fin n) s : GL (Fin n) L) = diagGL n u := hs
  apply hij
  have hi := congrArg (fun g : GL (Fin n) L => (g : Matrix (Fin n) (Fin n) L) i i) hs'
  have hj := congrArg (fun g : GL (Fin n) L => (g : Matrix (Fin n) (Fin n) L) j j) hs'
  simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
    diagGL_apply_self] at hi hj
  exact Units.ext (hi.symm.trans hj)

theorem mk_eq_one_of_eq_scalar {n : ℕ} {H : Subgroup (GL (Fin n) L)} {g : GL (Fin n) L}
    (hg : g ∈ H) (s : Lˣ) (hs : Matrix.GeneralLinearGroup.scalar (Fin n) s = g) :
    (QuotientGroup.mk (⟨g, hg⟩ : H) : StatedProj H) = 1 :=
  (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 ⟨s, hs⟩)

theorem not_three_dvd_card_ker [Finite L] {n : ℕ} (hn : ¬ 3 ∣ n) (H : Subgroup (GL (Fin n) L))
    (hdet : ∀ g ∈ H, (g : Matrix (Fin n) (Fin n) L).det = 1) :
    ¬ 3 ∣ Nat.card (QuotientGroup.mk' ((StatedScalars (Fin n) L).subgroupOf H)).ker := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro hd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 hd
  have hmem : ((x : H) : GL (Fin n) L) ∈ StatedScalars (Fin n) L := by
    have h : QuotientGroup.mk' ((StatedScalars (Fin n) L).subgroupOf H) (x : H) = 1 := x.2
    exact Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 h)
  obtain ⟨c, hc⟩ := hmem
  have hcn : c ^ n = 1 := by
    have h := hdet _ (x : H).2
    rw [← hc, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
    exact Units.ext (by rw [Units.val_pow_eq_pow_val, h, Units.val_one])
  have hxn : x ^ n = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_pow, Subgroup.coe_one, Subgroup.coe_one, ← hc, ← map_pow,
      hcn, map_one]
  have h3 := orderOf_dvd_of_pow_eq_one hxn
  rw [hx] at h3
  exact hn h3

section Three

variable [Finite L]

theorem dichThreeLieAt_three {ζ : Lˣ} (hζ : orderOf ζ = 9) (H : Subgroup (GL (Fin 3) L))
    (hdiag : ∀ u : Fin 3 → Lˣ, (∀ i, u i ∈ Subgroup.zpowers ζ) → ∏ i, u i = 1 →
      diagGL 3 u ∈ H)
    (hperm : permGL 3 (finRotate 3) ∈ H) : DichThreeLieAt (StatedProj H) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let E : Multiplicative (ℤ × ℤ) →* (Fin 3 → Lˣ) :=
    MonoidHom.mk' (fun v => ![ζ ^ v.toAdd.1, ζ ^ v.toAdd.2, ζ ^ (-v.toAdd.1 - v.toAdd.2)])
      (fun v w => by
        funext i
        fin_cases i
        · show ζ ^ (v.toAdd.1 + w.toAdd.1) = ζ ^ v.toAdd.1 * ζ ^ w.toAdd.1
          exact zpow_add ζ _ _
        · show ζ ^ (v.toAdd.2 + w.toAdd.2) = ζ ^ v.toAdd.2 * ζ ^ w.toAdd.2
          exact zpow_add ζ _ _
        · show ζ ^ (-(v.toAdd.1 + w.toAdd.1) - (v.toAdd.2 + w.toAdd.2)) =
            ζ ^ (-v.toAdd.1 - v.toAdd.2) * ζ ^ (-w.toAdd.1 - w.toAdd.2)
          rw [← zpow_add]
          congr 1
          ring)
  have hE : ∀ v, diagGL 3 (E v) ∈ H := by
    intro v
    apply hdiag
    · intro i
      fin_cases i
      · exact Subgroup.zpow_mem_zpowers ζ _
      · exact Subgroup.zpow_mem_zpowers ζ _
      · exact Subgroup.zpow_mem_zpowers ζ _
    · rw [Fin.prod_univ_three]
      show ζ ^ v.toAdd.1 * ζ ^ v.toAdd.2 * ζ ^ (-v.toAdd.1 - v.toAdd.2) = 1
      rw [← zpow_add, ← zpow_add, show v.toAdd.1 + v.toAdd.2 + (-v.toAdd.1 - v.toAdd.2) = 0 by
        ring, zpow_zero]
  let θ : Multiplicative (ℤ × ℤ) →* StatedProj H :=
    (QuotientGroup.mk' _).comp (((diagGL 3).comp E).codRestrict H hE)
  have hθ : ∀ v, θ v = QuotientGroup.mk (⟨diagGL 3 (E v), hE v⟩ : H) := fun v => rfl
  let Y : H := ⟨permGL 3 (finRotate 3), hperm⟩
  let y : StatedProj H := QuotientGroup.mk Y
  have hζz : ∀ m n : ℤ, ζ ^ m = ζ ^ n ↔ m ≡ n [ZMOD 9] := fun m n => by
    rw [zpow_eq_zpow_iff_modEq, hζ]
    rfl
  have hσ : ∀ i : Fin 3, (finRotate 3)⁻¹ i = ![2, 0, 1] i := by
    intro i
    fin_cases i <;> rfl
  have hrot : ∀ a b : ℤ, y * θ (Multiplicative.ofAdd (a, b)) * y⁻¹ =
      θ (Multiplicative.ofAdd (-a - b, a)) := by
    intro a b
    rw [hθ, hθ]
    show (QuotientGroup.mk (Y * ⟨_, hE _⟩ * Y⁻¹) : StatedProj H) = _
    congr 1
    apply Subtype.ext
    show permGL 3 (finRotate 3) * diagGL 3 (E _) * (permGL 3 (finRotate 3))⁻¹ = diagGL 3 (E _)
    rw [permGL_mul_diagGL_mul_inv]
    congr 1
    funext i
    rw [hσ i]
    fin_cases i
    · rfl
    · rfl
    · show ζ ^ b = ζ ^ (-(-a - b) - a)
      congr 1
      ring
  have hθmul : ∀ a b c d : ℤ, θ (Multiplicative.ofAdd (a, b)) * θ (Multiplicative.ofAdd (c, d)) =
      θ (Multiplicative.ofAdd (a + c, b + d)) := fun a b c d => by
    rw [← map_mul]
    rfl
  have hθinv : ∀ a b : ℤ, (θ (Multiplicative.ofAdd (a, b)))⁻¹ =
      θ (Multiplicative.ofAdd (-a, -b)) := fun a b => by
    rw [← map_inv]
    rfl
  have hθ1 : ∀ a b : ℤ, a ≡ b [ZMOD 9] → b ≡ -a - b [ZMOD 9] →
      θ (Multiplicative.ofAdd (a, b)) = 1 := by
    intro a b h1 h2
    rw [hθ]
    refine mk_eq_one_of_eq_scalar _ (ζ ^ a) ?_
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.coe_scalar, coe_diagGL, Matrix.scalar_apply]
    congr 1
    funext i
    fin_cases i
    · rfl
    · show ((ζ ^ a : Lˣ) : L) = ((ζ ^ b : Lˣ) : L)
      rw [(hζz a b).2 h1]
    · show ((ζ ^ a : Lˣ) : L) = ((ζ ^ (-a - b) : Lˣ) : L)
      rw [(hζz a b).2 h1, (hζz b _).2 h2]
  have hθne : ∀ a b : ℤ, (¬ a ≡ b [ZMOD 9] ∨ ¬ b ≡ -a - b [ZMOD 9]) →
      θ (Multiplicative.ofAdd (a, b)) ≠ 1 := by
    intro a b h
    rw [hθ]
    rcases h with h | h
    · exact mk_diagGL_ne_one (hE _) (i := 0) (j := 1) (fun he => h ((hζz a b).1 he))
    · exact mk_diagGL_ne_one (hE _) (i := 1) (j := 2) (fun he => h ((hζz b _).1 he))
  have hy3 : y ^ 3 = 1 := by
    have hY : Y ^ 3 = 1 := by
      apply Subtype.ext
      show permGL 3 (finRotate 3) ^ 3 = 1
      rw [← map_pow, show (finRotate 3) ^ 3 = 1 by decide, map_one]
    show (QuotientGroup.mk Y : StatedProj H) ^ 3 = 1
    rw [← QuotientGroup.mk_pow, hY, QuotientGroup.mk_one]
  have hθp : IsPGroup 3 θ.range := by
    rintro ⟨_, v, rfl⟩
    refine ⟨2, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← map_pow]
    obtain ⟨⟨a, b⟩, rfl⟩ : ∃ p : ℤ × ℤ, v = Multiplicative.ofAdd p := ⟨v.toAdd, rfl⟩
    show θ (Multiplicative.ofAdd (9 • (a, b))) = 1
    rw [Prod.smul_mk, nsmul_eq_mul, nsmul_eq_mul]
    refine hθ1 _ _ ?_ ?_ <;> simp only [Int.ModEq] <;> push_cast <;> omega
  have hYp : IsPGroup 3 (Subgroup.zpowers y) := by
    intro g
    obtain ⟨k, hk⟩ := g.2
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy3, one_zpow]
  have hrot2 : ∀ a b : ℤ, ((-b - (-a - b), b) : ℤ × ℤ) = (a, b) := fun a b =>
    Prod.ext (show -b - (-a - b) = a by ring) rfl
  have hyN : y ∈ Subgroup.normalizer (θ.range : Set (StatedProj H)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨v, rfl⟩
      obtain ⟨⟨a, b⟩, rfl⟩ : ∃ p : ℤ × ℤ, v = Multiplicative.ofAdd p := ⟨v.toAdd, rfl⟩
      exact ⟨_, (hrot a b).symm⟩
    · rintro ⟨w, hw⟩
      obtain ⟨⟨a, b⟩, rfl⟩ : ∃ p : ℤ × ℤ, w = Multiplicative.ofAdd p := ⟨w.toAdd, rfl⟩
      refine ⟨Multiplicative.ofAdd (b, -a - b), ?_⟩
      have h1 : y * θ (Multiplicative.ofAdd (b, -a - b)) * y⁻¹ = y * h * y⁻¹ := by
        rw [hrot, hrot2, hw]
      exact mul_left_cancel (mul_right_cancel h1)
  set U : Subgroup (StatedProj H) := θ.range ⊔ Subgroup.zpowers y with hUdef
  have hU : IsPGroup 3 U := IsPGroup.to_sup_of_normal_left' hθp hYp ((Subgroup.zpowers_le).2 hyN)
  have hθU : ∀ v, θ v ∈ U := fun v => Subgroup.mem_sup_left ⟨v, rfl⟩
  have hyU : y ∈ U := Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have hcomm : ∀ a b : ℤ, ⁅θ (Multiplicative.ofAdd (a, b)), y⁆ =
      θ (Multiplicative.ofAdd (a + (a + b), b + -a)) := by
    intro a b
    rw [commutatorElement_def, mul_assoc (θ _ * y), show θ (Multiplicative.ofAdd (a, b)) * y *
      ((θ (Multiplicative.ofAdd (a, b)))⁻¹ * y⁻¹) =
        θ (Multiplicative.ofAdd (a, b)) * (y * (θ (Multiplicative.ofAdd (a, b)))⁻¹ * y⁻¹) by
      group, hθinv, hrot, hθmul]
    congr 3 <;> ring
  set A := θ (Multiplicative.ofAdd (1, -2)) with hAdef
  set B := θ (Multiplicative.ofAdd (1, 1)) with hBdef
  have hA : ⁅θ (Multiplicative.ofAdd (1, -1)), y⁆ = A := by rw [hcomm]; rfl
  have hB : ⁅θ (Multiplicative.ofAdd (0, 1)), y⁆ = B := by rw [hcomm]; rfl
  have hAU : A ∈ ⁅U, U⁆ := hA ▸ Subgroup.commutator_mem_commutator (hθU _) hyU
  have hBU : B ∈ ⁅U, U⁆ := hB ▸ Subgroup.commutator_mem_commutator (hθU _) hyU
  have hA3 : A ^ 3 = 1 := by
    rw [pow_three, hθmul, hθmul]
    exact hθ1 _ _ (by decide) (by decide)
  have hB3 : B ^ 3 = 1 := by
    rw [pow_three, hθmul, hθmul]
    exact hθ1 _ _ (by decide) (by decide)
  have hA1 : A ≠ 1 := hθne _ _ (Or.inl (by decide))
  have hA2 : A ^ 2 ≠ 1 := by
    rw [pow_two, hθmul]
    exact hθne _ _ (Or.inl (by decide))
  have hB1 : B ≠ 1 := hθne _ _ (Or.inr (by decide))
  have hAB : A ≠ B := by
    intro h
    have : A * B⁻¹ = 1 := by rw [h, mul_inv_cancel]
    rw [hAdef, hBdef, hθinv, hθmul] at this
    exact hθne _ _ (Or.inl (by decide)) this
  have hA2B : A ^ 2 ≠ B := by
    intro h
    have : A ^ 2 * B⁻¹ = 1 := by rw [h, mul_inv_cancel]
    rw [pow_two, hAdef, hBdef, hθinv, hθmul, hθmul] at this
    exact hθne _ _ (Or.inl (by decide)) this
  have hpair : HasNoncommPair 3 (StatedProj H) := by
    refine ⟨A, y, hA3, hy3, fun h => hAB ?_, hU.to_le ((Subgroup.closure_le _).2
      (Set.insert_subset_iff.2 ⟨Subgroup.commutator_le_self _ hAU,
        Set.singleton_subset_iff.2 hyU⟩))⟩
    have h1 : y * A * y⁻¹ = A := by rw [← h, mul_assoc, mul_inv_cancel, mul_one]
    have h2 : y * A * y⁻¹ = B := by
      rw [hAdef, hrot]
      rfl
    exact h1.symm.trans h2
  refine dichThreeLieAt_of_pair_derived hpair hU ?_
  refine not_isCyclic_of_four_cubes (H := ↥⁅U, U⁆) (a := 1) (b := ⟨A, hAU⟩)
    (c := ⟨A, hAU⟩ ^ 2) (d := ⟨B, hBU⟩) (one_pow 3) (Subtype.ext hA3) ?_ (Subtype.ext hB3) ?_ ?_
    ?_ ?_ ?_ ?_
  · rw [← pow_mul, mul_comm, pow_mul, show (⟨A, hAU⟩ : ↥⁅U, U⁆) ^ 3 = 1 from Subtype.ext hA3,
      one_pow]
  · exact fun h => hA1 (congrArg Subtype.val h).symm
  · exact fun h => hA2 (by simpa using (congrArg Subtype.val h).symm)
  · exact fun h => hB1 (congrArg Subtype.val h).symm
  · intro h
    have h1 : A = A ^ 2 := by simpa using congrArg Subtype.val h
    apply hA1
    rw [pow_two] at h1
    have h2 : A * 1 = A * A := by rw [mul_one]; exact h1
    exact (mul_left_cancel h2).symm
  · exact fun h => hAB (congrArg Subtype.val h)
  · exact fun h => hA2B (by simpa using congrArg Subtype.val h)

end Three

section Four

variable [Finite L]

@[expose] def cyc4 : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 1 2

theorem sign_cyc4 : Equiv.Perm.sign cyc4 = 1 := by decide

theorem cycleWitness_four {ω : Lˣ} (hω : orderOf ω = 3) (H : Subgroup (GL (Fin 4) L))
    (hdet : ∀ g ∈ H, (g : Matrix (Fin 4) (Fin 4) L).det = 1)
    (hdiag : ∀ u : Fin 4 → Lˣ, (∀ i, u i ∈ Subgroup.zpowers ω) → ∏ i, u i = 1 →
      diagGL 4 u ∈ H)
    (hperm : permGL 4 cyc4 ∈ H) : CycleWitness (StatedProj H) := by
  have hω3 : ω ^ 3 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  have hω1 : ω ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hω
    omega
  have hω2 : ω ^ 2 ≠ 1 := by
    intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hω] at this
    omega
  set uu : Fin 4 → Lˣ := ![ω, 1, 1, ω⁻¹] with huu
  set vv : Fin 4 → Lˣ := ![1, ω, 1, ω⁻¹] with hvv
  set ww : Fin 4 → Lˣ := ![1, 1, ω, ω⁻¹] with hww
  have hz : ∀ u : Fin 4 → Lˣ, (∀ i, u i = 1 ∨ u i = ω ∨ u i = ω⁻¹) →
      ∀ i, u i ∈ Subgroup.zpowers ω := by
    intro u hu i
    rcases hu i with h | h | h <;> rw [h]
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers ω
    · exact Subgroup.inv_mem _ (Subgroup.mem_zpowers ω)
  have hmu : diagGL 4 uu ∈ H :=
    hdiag _ (hz _ (fun i => by fin_cases i <;> simp [huu])) (by simp [huu, Fin.prod_univ_four])
  have hmv : diagGL 4 vv ∈ H :=
    hdiag _ (hz _ (fun i => by fin_cases i <;> simp [hvv])) (by simp [hvv, Fin.prod_univ_four])
  have hmw : diagGL 4 ww ∈ H :=
    hdiag _ (hz _ (fun i => by fin_cases i <;> simp [hww])) (by simp [hww, Fin.prod_univ_four])
  have hpow : ∀ u : Fin 4 → Lˣ, (∀ i, u i ^ 3 = 1) → diagGL 4 u ^ 3 = 1 := fun u hu => by
    rw [← map_pow, show u ^ 3 = 1 from funext hu, map_one]
  have hinj : ∀ u v : Fin 4 → Lˣ, diagGL 4 u = diagGL 4 v → ∀ i, u i = v i := by
    intro u v h i
    apply Units.ext
    have := congrArg (fun g : GL (Fin 4) L => (g : Matrix (Fin 4) (Fin 4) L) i i) h
    simpa [diagGL_apply_self] using this
  have hσ : ∀ i : Fin 4, cyc4⁻¹ i = ![2, 0, 1, 3] i := by decide
  have hconj : ∀ u : Fin 4 → Lˣ, permGL 4 cyc4 * diagGL 4 u * (permGL 4 cyc4)⁻¹ =
      diagGL 4 ![u 2, u 0, u 1, u 3] := by
    intro u
    rw [permGL_mul_diagGL_mul_inv]
    congr 1
    funext i
    rw [hσ i]
    fin_cases i <;> rfl
  have hGL : CycleData (diagGL 4 uu) (diagGL 4 vv) (diagGL 4 ww) (permGL 4 cyc4 : GL (Fin 4) L) :=
    { uv := by rw [← map_mul, ← map_mul, mul_comm]
      uw := by rw [← map_mul, ← map_mul, mul_comm]
      vw := by rw [← map_mul, ← map_mul, mul_comm]
      u3 := hpow _ (fun i => by fin_cases i <;> simp [huu, hω3])
      v3 := hpow _ (fun i => by fin_cases i <;> simp [hvv, hω3])
      w3 := hpow _ (fun i => by fin_cases i <;> simp [hww, hω3])
      y3 := by rw [← map_pow, show cyc4 ^ 3 = 1 by decide, map_one]
      c1 := by rw [hconj]; rfl
      c2 := by rw [hconj]; rfl
      c3 := by rw [hconj]; rfl
      ne1 := fun h => hω1 (by simpa [huu, hvv] using hinj _ _ h 0)
      ne2 := fun h => hω1 (by simpa [hvv, hww] using hinj _ _ h 1)
      ne3 := by
        rw [← map_inv, ← map_mul, ← map_inv, ← map_mul]
        exact fun h => hω1 (by simpa [huu, hvv, hww] using hinj _ _ h 0)
      ne4 := by
        rw [← map_inv, ← map_mul, ← map_pow, ← map_inv, ← map_mul]
        exact fun h => hω2 (by simpa [huu, hvv, hww] using hinj _ _ h 0) }
  have hH : CycleData (⟨diagGL 4 uu, hmu⟩ : H) ⟨diagGL 4 vv, hmv⟩ ⟨diagGL 4 ww, hmw⟩
      ⟨permGL 4 cyc4, hperm⟩ := CycleData.of_coe hGL
  exact CycleWitness.of_surjective_coprime_ker (QuotientGroup.mk' _)
    (not_three_dvd_card_ker (by norm_num) H hdet) ⟨_, _, _, _, hH⟩

end Four

end ProjLin

section PSL

variable {F : Type} [Field F] [Finite F]

theorem threeLocal_proj_SL_of_not_dvd (hF : ¬ 3 ∣ Nat.card F) (h1 : ¬ 3 ∣ Nat.card F - 1)
    (n : ℕ) : ThreeLocal (StatedProj (StatedSL n F)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fintype F := Fintype.ofFinite F
  have hF' : ¬ 3 ∣ Fintype.card F := by rwa [← Nat.card_eq_fintype_card]
  have hGL : ThreeLocal (GL (Fin n) F) :=
    threeLocal_of_sigma (PSLCross.one_le_padicValNat_card Nat.prime_three hF')
      (fun P => CFSG.GroupTheory.WeirSylow.sylow_GL (by decide) F hF' n P)
  haveI : (StatedSL n F).Normal := by rw [statedSL_eq_ker_det]; infer_instance
  have hSL : ThreeLocal (StatedSL n F) :=
    ThreeLocal.of_normal_coprime_index _
      (fun hd => h1 (hd.trans (PSLCross.index_statedSL_dvd n))) hGL
  refine ThreeLocal.of_surjective_coprime_ker (QuotientGroup.mk' _)
    (QuotientGroup.mk'_surjective _) ?_ hSL
  rw [QuotientGroup.ker_mk']
  exact fun hd => h1 (hd.trans (PSLCross.card_scalars_subgroupOf_dvd n))

theorem sylow_comm_proj_SL_of_le_two (hF : ¬ 3 ∣ Nat.card F) {n : ℕ} (hn : n ≤ 2) :
    ∀ S : Sylow 3 (StatedProj (StatedSL n F)),
      IsMulCommutative (S : Subgroup (StatedProj (StatedSL n F))) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fintype F := Fintype.ofFinite F
  have hF' : ¬ 3 ∣ Fintype.card F := by rwa [← Nat.card_eq_fintype_card]
  have hc := sylow_isMulCommutative_of_sigmaModel_of_lt Nat.prime_three
    (lt_of_le_of_lt (Nat.div_le_self _ _) (by omega : n < 3))
    (fun P => CFSG.GroupTheory.WeirSylow.sylow_GL (by decide) F hF' n P)
  exact sylow_comm_of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
    (sylow_comm_of_subgroup (StatedSL n F) hc)

end PSL

theorem dichLieCross_PSL (hLie : LieOrderFormulasInput) : DichLieCrossAt .PSL := by
  intro K _ _ _ _ n ℓ f hadm hmodel hℓ3 _
  obtain ⟨_, F, _, _, hcard, ⟨e⟩⟩ :=
    LieModel.statedClassicalModel hmodel (by simp [classicalTags])
  have hℓ : ℓ.Prime := hadm.1
  have hF3 : ¬ 3 ∣ Nat.card F := by
    rw [hcard]
    intro h
    exact hℓ3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hℓ).1
      (Nat.prime_three.dvd_of_dvd_pow h)).symm
  have hq2 : 2 ≤ Nat.card F := Finite.one_lt_card
  by_cases h1 : 3 ∣ Nat.card F - 1
  swap
  · exact DichThreeLieAt.of_mulEquiv e
      (dichThreeLieAt_of_threeLocal (threeLocal_proj_SL_of_not_dvd hF3 h1 n))
  have hdiagSL : ∀ (m : ℕ) (u : Fin m → Fˣ), ∏ i, u i = 1 → diagGL m u ∈ StatedSL m F :=
    fun m u hprod => by
      rw [mem_statedSL_iff, det_diagGL, ← Units.coe_prod, hprod, Units.val_one]
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) 3 (by rwa [Nat.card_units])
  rcases (show n ≤ 2 ∨ n = 3 ∨ n = 4 ∨ 5 ≤ n by omega) with hn | rfl | rfl | hn5
  · exact DichThreeLieAt.of_mulEquiv e
      (dichThreeLieAt_of_threeLocal (Or.inl (sylow_comm_proj_SL_of_le_two hF3 hn)))
  · by_cases h9 : 9 ∣ Nat.card F - 1
    · obtain ⟨ζ, hζ⟩ := exists_orderOf_eq_of_dvd_card_sub_one h9
      refine DichThreeLieAt.of_mulEquiv e (ProjLin.dichThreeLieAt_three hζ (StatedSL 3 F)
        (fun u _ hprod => hdiagSL 3 u hprod) ?_)
      rw [mem_statedSL_iff, det_permGL, sign_finRotate]
      simp
    ·
      haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hN : Nat.card K * Nat.gcd 3 (ℓ ^ f - 1) =
          CFSG.ComponentClassification.CatLeaf.lieOrderNumerator .PSL 3 (ℓ ^ f) :=
        (hLie K .PSL 3 ℓ f hadm hmodel).2.1
      rw [← hcard] at hN
      have hfac := OuterArith.psl_three_factorization hq2 h1 hN
      have hq1 : Nat.card F - 1 ≠ 0 := by omega
      have hv : padicValNat 3 (Nat.card F - 1) ≤ 1 := by
        by_contra hc
        push Not at hc
        exact h9 (by simpa using (padicValNat_dvd_iff_le hq1).2 hc)
      exact dichThreeLieAt_of_factorization_le_two (by omega)
  · refine DichThreeLieAt.of_mulEquiv e (dichThreeLieAt_of_cycleWitness
      (ProjLin.cycleWitness_four hω (StatedSL 4 F) (fun g hg => det_of_mem_statedSL hg)
        (fun u _ hprod => hdiagSL 4 u hprod) ?_))
    rw [mem_statedSL_iff, det_permGL, ProjLin.sign_cyc4]
    simp
  · have hnp : 6 ≤ n ∨ ¬ 3 ∣ n := by omega
    obtain ⟨E, hE, hEcard⟩ := exists_elemAbelian_four_projDiag Nat.prime_three hn5 hnp hω
      (StatedSL n F) (fun u _ _ hprod => hdiagSL n u hprod)
    exact DichThreeLieAt.of_mulEquiv e (dichThreeLieAt_of_elemAbelian hE hEcard)

end CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureThree
