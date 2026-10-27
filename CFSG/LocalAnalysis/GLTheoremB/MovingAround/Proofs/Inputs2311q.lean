module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2311m
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4TorusCent

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311q

open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311c CFSG.RankThree.PartOne.CTP

section Abstract

variable {G : Type*} [Group G] {K : Type*} [Field K]

theorem mem_of_triple_of_normalizer (M : Subgroup G) {x₀ x₁ x₂ : K → G}
    (h0 : ∀ a b, x₀ (a + b) = x₀ a * x₀ b) (h1 : ∀ a b, x₁ (a + b) = x₁ a * x₁ b)
    (h2 : ∀ a b, x₂ (a + b) = x₂ a * x₂ b) (z1 : x₁ 0 = 1) (z2 : x₂ 0 = 1)
    (c01 : ∀ a b, Commute (x₀ a) (x₁ b)) (c02 : ∀ a b, Commute (x₀ a) (x₂ b))
    (c12 : ∀ a b, Commute (x₁ a) (x₂ b)) {κ₀ κ₁ : K}
    (hu : ∀ a, x₀ a * x₁ (κ₀ * a) * x₂ (κ₁ * κ₀ * a) ∈ M)
    {d : G} (hd : d ∈ Subgroup.normalizer (M : Set G)) {μ₀ μ₁ μ₂ : K}
    (hd0 : ∀ c, d * x₀ c * d⁻¹ = x₀ (μ₀ * c)) (hd1 : ∀ c, d * x₁ c * d⁻¹ = x₁ (μ₁ * c))
    (hd2 : ∀ c, d * x₂ c * d⁻¹ = x₂ (μ₂ * c)) (h01 : μ₀ ≠ μ₁) (h02 : μ₀ ≠ μ₂) (h12 : μ₁ ≠ μ₂)
    (c : K) : x₀ c ∈ M := by
  set u : K → G := fun a => x₀ a * x₁ (κ₀ * a) * x₂ (κ₁ * κ₀ * a) with hu'
  have hconj1 : ∀ a b e, d * (x₀ a * x₁ b * x₂ e) * d⁻¹ =
      x₀ (μ₀ * a) * x₁ (μ₁ * b) * x₂ (μ₂ * e) := by
    intro a b e
    rw [← hd0, ← hd1, ← hd2]
    group
  have hconj2 : ∀ a b e, d * d * (x₀ a * x₁ b * x₂ e) * (d * d)⁻¹ =
      x₀ (μ₀ * (μ₀ * a)) * x₁ (μ₁ * (μ₁ * b)) * x₂ (μ₂ * (μ₂ * e)) := by
    intro a b e
    rw [← hconj1, show d * d * (x₀ a * x₁ b * x₂ e) * (d * d)⁻¹ =
      d * (d * (x₀ a * x₁ b * x₂ e) * d⁻¹) * d⁻¹ by group, hconj1]
  have hdd : d * d ∈ Subgroup.normalizer (M : Set G) := Subgroup.mul_mem _ hd hd
  set D := (μ₀ - μ₁) * (μ₀ - μ₂) with hD
  have hD0 : D ≠ 0 := mul_ne_zero (sub_ne_zero.2 h01) (sub_ne_zero.2 h02)
  set a₀ := μ₁ * μ₂ / D * c
  set a₁ := -(μ₁ + μ₂) / D * c
  set a₂ := 1 / D * c
  have hm0 : u a₀ ∈ M := hu a₀
  have hm1 : d * u a₁ * d⁻¹ ∈ M := (Subgroup.mem_normalizer_iff.1 hd _).1 (hu a₁)
  have hm2 : d * d * u a₂ * (d * d)⁻¹ ∈ M := (Subgroup.mem_normalizer_iff.1 hdd _).1 (hu a₂)
  have hprod := M.mul_mem (M.mul_mem hm0 hm1) hm2
  have tm := CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.triple_mul h0 h1 h2 c01 c02 c12
  rw [hu'] at hprod
  simp only at hprod
  rw [hconj1, hconj2, tm, tm] at hprod
  have ex0 : a₀ + μ₀ * a₁ + μ₀ * (μ₀ * a₂) = c := by
    simp only [a₀, a₁, a₂]
    field_simp
    ring
  have ex1 : κ₀ * a₀ + μ₁ * (κ₀ * a₁) + μ₁ * (μ₁ * (κ₀ * a₂)) = 0 := by
    simp only [a₀, a₁, a₂]
    field_simp
    ring
  have ex2 : κ₁ * κ₀ * a₀ + μ₂ * (κ₁ * κ₀ * a₁) + μ₂ * (μ₂ * (κ₁ * κ₀ * a₂)) = 0 := by
    simp only [a₀, a₁, a₂]
    field_simp
    ring
  rw [ex0, ex1, ex2, z1, z2, mul_one, mul_one] at hprod
  exact hprod

theorem closure_pair_eq_of_card_inputs2311q [Finite G] {p : ℕ} (hp : p.Prime) {E : Subgroup G}
    (hE : Nat.card E = p ^ 2) {a b : G} (ha : a ∈ E) (hb : b ∈ E) (hbp : b ^ p = 1) (hb1 : b ≠ 1)
    (hab : a ∉ Subgroup.zpowers b) : Subgroup.closure {a, b} = E := by
  haveI : Fact p.Prime := ⟨hp⟩
  set C := Subgroup.closure ({a, b} : Set G) with hC
  have hCE : C ≤ E := by
    rw [hC, Subgroup.closure_le]
    rintro y (rfl | rfl)
    · exact ha
    · exact hb
  have hbC : Subgroup.zpowers b ≤ C := (Subgroup.zpowers_le).2 (Subgroup.subset_closure (by simp))
  have hob : orderOf b = p := orderOf_eq_prime hbp hb1
  have hdvd : Nat.card C ∣ p ^ 2 := hE ▸ Subgroup.card_dvd_of_le hCE
  obtain ⟨k, hk, hCk⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  have hpC : p ∣ Nat.card C := by
    have := Subgroup.card_dvd_of_le hbC
    rwa [Nat.card_zpowers, hob] at this
  interval_cases k
  · rw [hCk, pow_zero] at hpC
    exact absurd (Nat.le_of_dvd one_pos hpC) (by have := hp.two_le; omega)
  · exfalso
    rw [pow_one] at hCk
    have heq : Subgroup.zpowers b = C := by
      refine Subgroup.eq_of_le_of_card_ge hbC ?_
      rw [hCk, Nat.card_zpowers, hob]
    exact hab (heq ▸ Subgroup.subset_closure (by simp))
  · exact Subgroup.eq_of_le_of_card_ge hCE (by rw [hE, hCk])

theorem conj_three_inputs2311q (x g : G) (hx3 : x ^ 3 = 1) : x * (x * (x * g * x⁻¹) * x⁻¹) * x⁻¹ = g := by
  have e : x * (x * (x * g * x⁻¹) * x⁻¹) * x⁻¹ = (x * (x * x)) * g * (x * (x * x))⁻¹ := by group
  rw [e, ← pow_three, hx3, one_mul, inv_one, mul_one]

end Abstract

section Numerics

open CFSG.Blueprint.Chevalley

variable {K : Type} [Field K]

theorem ringChar_facts_inputs2311q [Finite K] (hK2 : ringChar K ≠ 2) (hK3 : ringChar K ≠ 3) :
    (ringChar K).Prime ∧ ringChar K ∣ Nat.card K ∧ 5 ≤ Nat.card K := by
  classical
  have := Fintype.ofFinite K
  obtain ⟨n, hp, hn⟩ := FiniteField.card K (ringChar K)
  have h5 : 5 ≤ ringChar K := by
    have h2 := hp.two_le
    have h4 : ringChar K ≠ 4 := fun h => by rw [h] at hp; norm_num at hp
    omega
  refine ⟨hp, ?_, ?_⟩
  · rw [Nat.card_eq_fintype_card, hn]
    exact dvd_pow_self _ n.pos.ne'
  · rw [Nat.card_eq_fintype_card, hn]
    calc 5 ≤ ringChar K := h5
      _ = ringChar K ^ 1 := (pow_one _).symm
      _ ≤ ringChar K ^ (n : ℕ) := Nat.pow_le_pow_right hp.pos n.pos

open CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley in
theorem HSL_ne_one_inputs2311q {ω : Kˣ} (hω : ω ≠ 1) : HSL ω ≠ 1 := by
  intro h
  apply hω
  apply CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.HSLHom_injective (K := K)
  rw [CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.HSLHom_apply, h, map_one]

@[expose] def tupE2Sq (l : Kˣ) : Fin Tag.D4.rank → Kˣ := fun j => if j = ⟨2, by decide⟩ then l ^ 2 else 1

open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley in
theorem rootChar_tupE2Sq (l : Kˣ) (r : Fin Tag.D4.rank → ℤ) :
    rootChar (tupE2Sq l) r = l ^ (2 * r ⟨2, by decide⟩) := by
  rw [rootChar, Finset.prod_eq_single (⟨2, by decide⟩ : Fin Tag.D4.rank)]
  · have h : tupE2Sq l ⟨2, by decide⟩ = l ^ 2 := if_pos rfl
    rw [h, zpow_mul]
    norm_cast
  · intro i _ hi
    simp only [tupE2Sq, if_neg hi, one_zpow]
  · intro h
    exact absurd (Finset.mem_univ _) h

end Numerics

section RootAction

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Lang.D4Three CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph

set_option linter.unusedSectionVars false


variable {K : Type} [Field K]

local notation "𝕩" => xPar (rootOperatorFamily Tag.D4)

theorem diag_conj_xPar_inputs2311q {g : ↥(adjointGroup Tag.D4 K)} {a : Fin Tag.D4.rank → Kˣ}
    (hg : (g : ModGL Tag.D4 K) = rootDiagUnit Tag.D4 a) {r : Fin Tag.D4.rank → ℤ}
    (hr : IsRoot Tag.D4 r) (c : K) :
    g * 𝕩 r c * g⁻¹ = 𝕩 r (((rootChar a r : Kˣ) : K) * c) := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hg]
  exact CFSG.GH74.GLS.Stage2.Bender.Thm1.rootDiagUnit_conj_xPar_d4 a hr c

@[expose] def wRotA2 (r : Fin Tag.D4.rank → ℤ) : Fin Tag.D4.rank → ℤ :=
  wG2r (wG2r (wG2r (wG2r r)))

theorem wRotA2_eq_iterate (r : Fin Tag.D4.rank → ℤ) : wRotA2 r = wG2r^[4] r := rfl

theorem isRoot_wRotA2 {r : Fin Tag.D4.rank → ℤ} (hr : IsRoot Tag.D4 r) : IsRoot Tag.D4 (wRotA2 r) :=
  isRoot_wG2r (isRoot_wG2r (isRoot_wG2r (isRoot_wG2r hr)))

theorem yP_conj_xPar_inputs2311q {ω : Kˣ} (hω : ω ^ 3 = 1) {r : Fin Tag.D4.rank → ℤ}
    (hr : IsRoot Tag.D4 r) :
    ∃ κ : K, κ ≠ 0 ∧ ∀ c : K, yP hω * 𝕩 r c * (yP hω)⁻¹ = 𝕩 (wRotA2 r) (κ * c) := by
  obtain ⟨ε, hε, h⟩ := exists_weylG2_pow_conj (K := K) 4 hr
  rw [← wRotA2_eq_iterate] at h
  have hε0 : ε ≠ 0 := fun h0 => by rw [h0, zero_mul] at hε; exact zero_ne_one hε
  refine ⟨((rootChar (fun j => ω ^ vS j) (wRotA2 r) : Kˣ) : K) * ε,
    mul_ne_zero (Units.ne_zero _) hε0, fun c => ?_⟩
  have hs : ((sElt hω : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) =
      rootDiagUnit Tag.D4 (fun j => ω ^ vS j) := rfl
  unfold yP
  rw [mul_inv_rev, show sElt hω * (weylG2 : ↥(adjointGroup Tag.D4 K)) ^ 4 * 𝕩 r c *
      (((weylG2 : ↥(adjointGroup Tag.D4 K)) ^ 4)⁻¹ * (sElt hω)⁻¹) =
      sElt hω * ((weylG2 : ↥(adjointGroup Tag.D4 K)) ^ 4 * 𝕩 r c *
        ((weylG2 : ↥(adjointGroup Tag.D4 K)) ^ 4)⁻¹) * (sElt hω)⁻¹ by group, h,
    diag_conj_xPar_inputs2311q hs (isRoot_wRotA2 hr), mul_assoc]

theorem tyP_conj_xPar_inputs2311q {ω : Kˣ} (hω : ω ^ 3 = 1) {t : ↥(adjointGroup Tag.D4 K)}
    {a : Fin Tag.D4.rank → Kˣ} (ht : (t : ModGL Tag.D4 K) = rootDiagUnit Tag.D4 a)
    {r : Fin Tag.D4.rank → ℤ} (hr : IsRoot Tag.D4 r) :
    ∃ κ : K, κ ≠ 0 ∧ ∀ c : K, (t * yP hω) * 𝕩 r c * (t * yP hω)⁻¹ = 𝕩 (wRotA2 r) (κ * c) := by
  obtain ⟨κ, hκ, h⟩ := yP_conj_xPar_inputs2311q (K := K) hω hr
  refine ⟨((rootChar a (wRotA2 r) : Kˣ) : K) * κ, mul_ne_zero (Units.ne_zero _) hκ, fun c => ?_⟩
  rw [mul_inv_rev, show t * yP hω * 𝕩 r c * ((yP hω)⁻¹ * t⁻¹) =
      t * (yP hω * 𝕩 r c * (yP hω)⁻¹) * t⁻¹ by group, h,
    diag_conj_xPar_inputs2311q ht (isRoot_wRotA2 hr), mul_assoc]

@[expose] def wOrbitRoots : List (Fin Tag.D4.rank → ℤ) :=
  [![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 0, 1], ![1, 0, 1, 0], ![0, 1, 1, 0], ![0, 0, 1, 1],
    ![1, 1, 1, 0], ![0, 1, 1, 1], ![1, 0, 1, 1], ![-1, 0, 0, 0], ![0, -1, 0, 0],
    ![0, 0, 0, -1], ![-1, 0, -1, 0], ![0, -1, -1, 0], ![0, 0, -1, -1], ![-1, -1, -1, 0],
    ![0, -1, -1, -1], ![-1, 0, -1, -1]]

theorem wOrbitRoots_facts : ∀ r ∈ wOrbitRoots,
    IsRoot Tag.D4 r ∧ IsRoot Tag.D4 (wRotA2 r) ∧ IsRoot Tag.D4 (wRotA2 (wRotA2 r)) ∧
    wRotA2 (wRotA2 (wRotA2 r)) = r ∧
    r ≠ wRotA2 r ∧ r ≠ -wRotA2 r ∧ ¬IsRoot Tag.D4 (r + wRotA2 r) ∧
    r ≠ wRotA2 (wRotA2 r) ∧ r ≠ -wRotA2 (wRotA2 r) ∧ ¬IsRoot Tag.D4 (r + wRotA2 (wRotA2 r)) ∧
    wRotA2 r ≠ wRotA2 (wRotA2 r) ∧ wRotA2 r ≠ -wRotA2 (wRotA2 r) ∧
    ¬IsRoot Tag.D4 (wRotA2 r + wRotA2 (wRotA2 r)) ∧
    r ⟨2, by decide⟩ ≠ wRotA2 r ⟨2, by decide⟩ ∧ r ⟨2, by decide⟩ ≠ wRotA2 (wRotA2 r) ⟨2, by decide⟩ ∧
    wRotA2 r ⟨2, by decide⟩ ≠ wRotA2 (wRotA2 r) ⟨2, by decide⟩ ∧
    2 * r ⟨2, by decide⟩ ∈ ({2, -2, 0} : Finset ℤ) ∧
    2 * wRotA2 r ⟨2, by decide⟩ ∈ ({2, -2, 0} : Finset ℤ) ∧
    2 * wRotA2 (wRotA2 r) ⟨2, by decide⟩ ∈ ({2, -2, 0} : Finset ℤ) := by
  simp only [isRoot_iff_mem_artifactRoots]
  decide +kernel

end RootAction

section TyP

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Lang.D4Three CFSG.LieType.SeitzGeneration.ExcWideThree
  CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph
  CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2NonsplitGen

set_option linter.unusedSectionVars false


variable {K : Type} [Field K]

local notation "𝕩" => xPar (rootOperatorFamily Tag.D4)

theorem fixedSubgroup_le_normalizer_inputs2311q [Finite K] (hK2 : ringChar K ≠ 2) (hK3 : ringChar K ≠ 3)
    {B : SL2 K} (hB3 : B ^ 3 = 1) (hB1 : B ≠ 1) {x : ↥(adjointGroup Tag.D4 K)} (hαx : gammaP K B x = x)
    (hx3 : x ^ 3 = 1) :
    fixedSubgroup (gammaP K B) ≤ Subgroup.normalizer
      (uniPlaneClosure (ringChar K) (Subgroup.closure {gammaP K B, MulAut.conj x}) :
        Set ↥(adjointGroup Tag.D4 K)) := by
  classical
  obtain ⟨hrp, hrK, hK5⟩ := ringChar_facts_inputs2311q hK2 hK3
  set H := uniPlaneClosure (ringChar K) (Subgroup.closure {gammaP K B, MulAut.conj x}) with hH
  have hfix := CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHighD4Odd.d4GraphA2FixIsoOdd_holds K hK2
    hK3 hK5 B hB3 hB1
  obtain ⟨⟨w, hαw, hwx, hgen⟩, -, hns⟩ :=
    Inputs2311m.exists_rGen_escape_of_isPGLPiThree hK5 hfix hrp hK3 hrK hαx hx3
  haveI hGs : IsSimpleGroup ↥(adjointGroup Tag.D4 K) :=
    CFSG.LieType.SeitzGeneration.ExcWideThree.isSimpleGroup_adjointGroup_D4 K
  have hα1 : gammaP K B ≠ 1 := by
    intro h
    apply hns
    have htop : fixedSubgroup (gammaP K B) = ⊤ := by
      rw [eq_top_iff]
      intro y _
      rw [mem_fixedSubgroup, h]
      rfl
    rw [htop]
    exact MulEquiv.isSimpleGroup Subgroup.topEquiv
  have hαE : gammaP K B ∈ Subgroup.closure {gammaP K B, MulAut.conj x} :=
    Subgroup.subset_closure (by simp)
  have hrH : ∀ y, gammaP K B y = y → (∃ n : ℕ, y ^ (ringChar K ^ n) = 1) → y ∈ H := by
    rintro y hy ⟨n, hn⟩
    exact mem_uniPlaneClosure hαE hα1 hy hn
  have hNw : w ∈ Subgroup.normalizer (H : Set ↥(adjointGroup Tag.D4 K)) := by
    refine Inputs2311m.mem_normalizer_uniPlaneClosure_of_map_eq _ ?_
    refine Inputs2311m.map_closure_pair_eq_inputs2311m _ (Or.inl ?_) ?_
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [Inputs2311m.conj_mul_conj_inv_eq_inputs2311m, hαw, mul_inv_cancel, map_one, one_mul]
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [← map_inv, ← map_mul, ← map_mul, hwx, mul_inv_cancel_right]
  intro y hy
  refine (Subgroup.closure_le _).2 ?_ (hgen y hy)
  rintro z (⟨hz, hzn⟩ | hz)
  · exact Subgroup.le_normalizer (hrH z hz hzn)
  · rw [Set.mem_singleton_iff] at hz
    rw [hz]
    exact hNw

@[expose] noncomputable def torusE2Sq (l : Kˣ) : ↥(adjointGroup Tag.D4 K) :=
  ⟨rootDiagUnit Tag.D4 (tupE2Sq l), rootDiagUnit_mem_of_sq fun j =>
    ⟨if j = ⟨2, by decide⟩ then l else 1, by
      simp only [tupE2Sq]
      split_ifs <;> simp⟩⟩

theorem gammaP_HSL_torusE2Sq (ω l : Kˣ) : gammaP K (HSL ω) (torusE2Sq l) = torusE2Sq l := by
  apply Subtype.ext
  rw [gammaP_HSL_diag ω (show ((torusE2Sq l : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) =
    rootDiagUnit Tag.D4 (tupE2Sq l) from rfl)]
  show rootDiagUnit Tag.D4 (tupAct permM (tupE2Sq l)) = rootDiagUnit Tag.D4 (tupE2Sq l)
  congr 1
  rw [tupAct_permM]
  funext j
  have hρ : ∀ j : Fin Tag.D4.rank, rhoP.symm j = ⟨2, by decide⟩ ↔ j = ⟨2, by decide⟩ := by decide
  simp only [tupE2Sq]
  by_cases hj : j = ⟨2, by decide⟩
  · rw [if_pos ((hρ j).2 hj), if_pos hj]
  · rw [if_neg (fun h => hj ((hρ j).1 h)), if_neg hj]

theorem torusE2Sq_conj_xPar (l : Kˣ) {r : Fin Tag.D4.rank → ℤ} (hr : IsRoot Tag.D4 r) (c : K) :
    torusE2Sq l * 𝕩 r c * (torusE2Sq l)⁻¹ = 𝕩 r (((l ^ (2 * r ⟨2, by decide⟩) : Kˣ) : K) * c) := by
  rw [diag_conj_xPar_inputs2311q (show ((torusE2Sq l : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) =
    rootDiagUnit Tag.D4 (tupE2Sq l) from rfl) hr, rootChar_tupE2Sq]

theorem uniPlaneClosure_eq_top_of_tyP [Finite K] (hK2 : ringChar K ≠ 2) (hK3 : ringChar K ≠ 3)
    (hq : Nat.card K % 3 = 1) {ω : Kˣ} (hω3 : ω ^ 3 = 1) (hω : orderOf ω = 3)
    {t : ↥(adjointGroup Tag.D4 K)} {a : Fin Tag.D4.rank → Kˣ}
    (ht : (t : ModGL Tag.D4 K) = rootDiagUnit Tag.D4 a) (hx3 : (t * yP hω3) ^ 3 = 1)
    (hαx : gammaP K (HSL ω) (t * yP hω3) = t * yP hω3) {E : Subgroup (MulAut ↥(adjointGroup Tag.D4 K))}
    (hαE : gammaP K (HSL ω) ∈ E) (hxE : MulAut.conj (t * yP hω3) ∈ E) :
    uniPlaneClosure (ringChar K) E = ⊤ := by
  classical
  obtain ⟨hrp, hrK, hK5⟩ := ringChar_facts_inputs2311q hK2 hK3
  set x := t * yP hω3 with hxdef
  set E' : Subgroup (MulAut ↥(adjointGroup Tag.D4 K)) :=
    Subgroup.closure {gammaP K (HSL ω), MulAut.conj x} with hE'
  have hE'E : E' ≤ E := by
    rw [hE', Subgroup.closure_le]
    rintro φ (rfl | rfl)
    · exact hαE
    · exact hxE
  have hmono : uniPlaneClosure (ringChar K) E' ≤ uniPlaneClosure (ringChar K) E :=
    Subgroup.closure_mono fun s ⟨φ, hφ, hφ1, hφs, n, hn⟩ => ⟨φ, hE'E hφ, hφ1, hφs, n, hn⟩
  suffices h : uniPlaneClosure (ringChar K) E' = ⊤ by
    rw [eq_top_iff, ← h]
    exact hmono
  set H := uniPlaneClosure (ringChar K) E' with hH
  have hω1 : ω ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hω
    norm_num at hω
  have hNC := fixedSubgroup_le_normalizer_inputs2311q hK2 hK3 (HSL_pow_three hω3)
    (HSL_ne_one_inputs2311q hω1) hαx hx3
  have hx1 : x ≠ 1 := by
    intro h
    have hy : yP hω3 = t⁻¹ := eq_inv_of_mul_eq_one_right h
    refine yP_pow_not_diag hω3 hω (k := 1) (Or.inl rfl) (a := a⁻¹) ?_
    rw [pow_one, hy, Subgroup.coe_inv, ht, rootDiagUnit_inv]
  have hcx1 : MulAut.conj x ≠ 1 := fun h => hx1 (conj_injective_adj (h.trans (map_one _).symm))
  have hxE' : MulAut.conj x ∈ E' := Subgroup.subset_closure (by simp)
  have hrx : ∀ y, x * y * x⁻¹ = y → y ^ ringChar K = 1 → y ∈ H := fun y hy hyr =>
    mem_uniPlaneClosure (n := 1) hxE' hcx1 (by rw [MulAut.conj_apply]; exact hy)
      (by rw [pow_one]; exact hyr)
  have hK4 : 4 ≤ Nat.card K := by omega
  obtain ⟨l, hl⟩ := exists_pow_four_ne_one hq hK4
  have hsN : torusE2Sq l ∈ Subgroup.normalizer (H : Set ↥(adjointGroup Tag.D4 K)) :=
    hNC (gammaP_HSL_torusE2Sq ω l)
  have hx3' : ∀ g, x * (x * (x * g * x⁻¹) * x⁻¹) * x⁻¹ = g := fun g => conj_three_inputs2311q x g hx3
  have hchar0 : ((ringChar K : ℕ) : K) = 0 := CharP.cast_eq_zero K (ringChar K)
  have horb : ∀ r ∈ wOrbitRoots, ∀ c, 𝕩 r c ∈ H := by
    intro r hr c
    obtain ⟨h0, h1, h2, h3, n01, m01, s01, n02, m02, s02, n12, m12, s12, e01, e02, e12, em0, em1,
      em2⟩ := wOrbitRoots_facts r hr
    obtain ⟨κ₀, -, hκ₀⟩ := tyP_conj_xPar_inputs2311q hω3 ht h0
    obtain ⟨κ₁, -, hκ₁⟩ := tyP_conj_xPar_inputs2311q hω3 ht h1
    obtain ⟨κ₂, -, hκ₂⟩ := tyP_conj_xPar_inputs2311q hω3 ht h2
    rw [h3] at hκ₂
    have hκ : κ₂ * κ₁ * κ₀ = 1 := by
      have h := hx3' (𝕩 r 1)
      rw [hκ₀, hκ₁, hκ₂] at h
      have h' := xPar_injective h0 h
      linear_combination h'
    have c01 : ∀ a b : K, Commute (𝕩 r a) (𝕩 (wRotA2 r) b) := fun a b =>
      CFSG.LieType.Steinberg.TwistedD4.commute_xPar h0 h1 n01 m01 s01 a b
    have c02 : ∀ a b : K, Commute (𝕩 r a) (𝕩 (wRotA2 (wRotA2 r)) b) := fun a b =>
      CFSG.LieType.Steinberg.TwistedD4.commute_xPar h0 h2 n02 m02 s02 a b
    have c12 : ∀ a b : K, Commute (𝕩 (wRotA2 r) a) (𝕩 (wRotA2 (wRotA2 r)) b) := fun a b =>
      CFSG.LieType.Steinberg.TwistedD4.commute_xPar h1 h2 n12 m12 s12 a b
    refine mem_of_triple_of_normalizer H (fun a b => xPar_add r a b) (fun a b => xPar_add _ a b)
      (fun a b => xPar_add _ a b) (xPar_zero _) (xPar_zero _) c01 c02 c12 (κ₀ := κ₀) (κ₁ := κ₁) ?_ hsN
      (torusE2Sq_conj_xPar l h0) (torusE2Sq_conj_xPar l h1) (torusE2Sq_conj_xPar l h2)
      (val_zpow_ne_of_four hl em0 em1 (by omega)) (val_zpow_ne_of_four hl em0 em2 (by omega))
      (val_zpow_ne_of_four hl em1 em2 (by omega)) c
    intro b
    apply hrx
    · rw [show x * (𝕩 r b * 𝕩 (wRotA2 r) (κ₀ * b) * 𝕩 (wRotA2 (wRotA2 r)) (κ₁ * κ₀ * b)) * x⁻¹ =
          (x * 𝕩 r b * x⁻¹) * (x * 𝕩 (wRotA2 r) (κ₀ * b) * x⁻¹) *
            (x * 𝕩 (wRotA2 (wRotA2 r)) (κ₁ * κ₀ * b) * x⁻¹) by group, hκ₀, hκ₁, hκ₂,
        show κ₂ * (κ₁ * κ₀ * b) = b by rw [← mul_assoc, ← mul_assoc, hκ, one_mul],
        show κ₁ * (κ₀ * b) = κ₁ * κ₀ * b by ring]
      rw [mul_assoc, ← (c02 b _).eq, ← mul_assoc, ← (c01 b _).eq, mul_assoc]
    · rw [((c02 b _).mul_left (c12 _ _)).mul_pow, (c01 b _).mul_pow, xPar_pow, xPar_pow, xPar_pow,
        hchar0, zero_mul, zero_mul, zero_mul, xPar_zero, xPar_zero, xPar_zero, mul_one, mul_one]
  have hsingle : ∀ i : Fin Tag.D4.rank, i ≠ ⟨2, by decide⟩ →
      Pi.single i 1 ∈ wOrbitRoots ∧ -Pi.single i 1 ∈ wOrbitRoots := by decide
  refine eq_top_of_simple_mem fun i c => ?_
  by_cases hi : i = ⟨2, by decide⟩
  · subst hi
    have hn0 : CFSG.LieType.Steinberg.weylElement 𝕩 ⟨0, by decide⟩ (1 : Kˣ) ∈ H := by
      unfold CFSG.LieType.Steinberg.weylElement
      exact H.mul_mem (H.mul_mem (horb _ (by decide) _) (horb _ (by decide) _)) (horb _ (by decide) _)
    have hfacts : (Pi.single (⟨0, by decide⟩ : Fin Tag.D4.rank) 1 +
          Pi.single ⟨2, by decide⟩ 1) ∈ wOrbitRoots ∧
        -(Pi.single (⟨0, by decide⟩ : Fin Tag.D4.rank) 1 + Pi.single ⟨2, by decide⟩ 1) ∈
          wOrbitRoots ∧
        reflect Tag.D4 ⟨0, by decide⟩ (Pi.single ⟨0, by decide⟩ 1 + Pi.single ⟨2, by decide⟩ 1) =
          Pi.single ⟨2, by decide⟩ 1 ∧
        reflect Tag.D4 ⟨0, by decide⟩ (-(Pi.single ⟨0, by decide⟩ 1 +
          Pi.single ⟨2, by decide⟩ 1)) = -Pi.single ⟨2, by decide⟩ 1 := by decide
    obtain ⟨m1, m2, e1, e2⟩ := hfacts
    obtain ⟨hr1, -⟩ := wOrbitRoots_facts _ m1
    obtain ⟨hr2, -⟩ := wOrbitRoots_facts _ m2
    obtain ⟨ε, hε, hc⟩ := exists_weyl_conj (K := K) ⟨0, by decide⟩ hr1
    obtain ⟨ε', hε', hc'⟩ := exists_weyl_conj (K := K) ⟨0, by decide⟩ hr2
    rw [e1] at hc
    rw [e2] at hc'
    exact ⟨mem_of_conj_eq hn0 hε hc (horb _ m1) c, mem_of_conj_eq hn0 hε' hc' (horb _ m2) c⟩
  · obtain ⟨h1, h2⟩ := hsingle i hi
    exact ⟨horb _ h1 c, horb _ h2 c⟩

end TyP

section Diag

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Lang.D4Three CFSG.LieType.SeitzGeneration.ExcWideThree
  CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph
  CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2NonsplitGen

set_option linter.unusedSectionVars false


variable {K : Type} [Field K]

local notation "𝕩" => xPar (rootOperatorFamily Tag.D4)

@[expose] def posRootsD4 : List (Fin Tag.D4.rank → ℤ) :=
  [![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1], ![1, 0, 1, 0], ![0, 1, 1, 0],
    ![0, 0, 1, 1], ![1, 1, 1, 0], ![1, 0, 1, 1], ![0, 1, 1, 1], ![1, 1, 1, 1], ![1, 1, 2, 1]]

@[expose] def negRootsD4 : List (Fin Tag.D4.rank → ℤ) :=
  [![-1, 0, 0, 0], ![0, -1, 0, 0], ![0, 0, -1, 0], ![0, 0, 0, -1], ![-1, 0, -1, 0],
    ![0, -1, -1, 0], ![0, 0, -1, -1], ![-1, -1, -1, 0], ![-1, 0, -1, -1], ![0, -1, -1, -1],
    ![-1, -1, -1, -1], ![-1, -1, -2, -1]]

theorem posRootsD4_facts : (∀ r ∈ posRootsD4, IsRoot Tag.D4 r ∧ 0 < height r ∧ rhoL r ∈ posRootsD4) ∧
    ∀ i : Fin Tag.D4.rank, Pi.single i 1 ∈ posRootsD4 := by
  simp only [isRoot_iff_mem_artifactRoots]
  decide +kernel

theorem negRootsD4_facts : (∀ r ∈ negRootsD4, IsRoot Tag.D4 r ∧ height r < 0 ∧ rhoL r ∈ negRootsD4) ∧
    ∀ i : Fin Tag.D4.rank, -Pi.single i 1 ∈ negRootsD4 := by
  simp only [isRoot_iff_mem_artifactRoots]
  decide +kernel

theorem diag_mem_normalizer_spanRoots {g : ↥(adjointGroup Tag.D4 K)} {a : Fin Tag.D4.rank → Kˣ}
    (hg : (g : ModGL Tag.D4 K) = rootDiagUnit Tag.D4 a) {S : List (Fin Tag.D4.rank → ℤ)}
    (hS : ∀ s ∈ S, IsRoot Tag.D4 s) :
    g ∈ Subgroup.normalizer (spanRoots K S : Set ↥(adjointGroup Tag.D4 K)) := by
  have key : ∀ {h : ↥(adjointGroup Tag.D4 K)} {b : Fin Tag.D4.rank → Kˣ},
      (h : ModGL Tag.D4 K) = rootDiagUnit Tag.D4 b → ∀ y ∈ spanRoots K S, h * y * h⁻¹ ∈ spanRoots K S := by
    intro h b hb y hy
    have hle : (spanRoots K S).map (MulAut.conj h).toMonoidHom ≤ spanRoots K S := by
      rw [spanRoots, MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨_, ⟨s, hs, c, rfl⟩, rfl⟩
      show h * 𝕩 s c * h⁻¹ ∈ spanRoots K S
      rw [diag_conj_xPar_inputs2311q hb (hS s hs)]
      exact xPar_mem_spanRoots hs _
    exact hle ⟨y, hy, rfl⟩
  have hginv : ((g⁻¹ : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) = rootDiagUnit Tag.D4 a⁻¹ := by
    rw [Subgroup.coe_inv, hg, rootDiagUnit_inv]
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key hg y, fun hy => ?_⟩
  have h1 := key hginv _ hy
  rwa [show g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y by group] at h1

theorem isPGroup_spanRoots_pos [Finite K] {S : List (Fin Tag.D4.rank → ℤ)}
    (hS : ∀ s ∈ S, IsRoot Tag.D4 s ∧ 0 < height s) : IsPGroup (ringChar K) (spanRoots K S) := by
  have hle : (spanRoots K S).map (adjointGroup Tag.D4 K).subtype ≤ posUnipotent Tag.D4 K := by
    rw [spanRoots, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨s, hs, c, rfl⟩, rfl⟩
    obtain ⟨hsr, hsh⟩ := hS s hs
    obtain ⟨σ, -, hσ⟩ := coe_xPar_eq_pinnedX_sign (K := K) hsr
    show ((𝕩 s c : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) ∈ posUnipotent Tag.D4 K
    rw [hσ c]
    exact le_iSup₂ (f := fun α (_ : α ∈ {α : Fin Tag.D4.rank → ℤ | IsRoot Tag.D4 α ∧ 0 < height α}) =>
      rootSubgroup Tag.D4 K α) s ⟨hsr, hsh⟩ (Subgroup.subset_closure ⟨_, rfl⟩)
  haveI : CharP K (ringChar K) := ringChar.charP K
  have hP := ((positive_root_triangularity.{0, 0} Tag.D4).2 K (ringChar K)).2.1
  exact (hP.to_le hle).of_equiv
    (Subgroup.equivMapOfInjective _ _ (adjointGroup Tag.D4 K).subtype_injective).symm

theorem isPGroup_spanRoots_neg [Finite K] {S : List (Fin Tag.D4.rank → ℤ)}
    (hS : ∀ s ∈ S, IsRoot Tag.D4 s ∧ height s < 0) : IsPGroup (ringChar K) (spanRoots K S) := by
  have hle : (spanRoots K S).map (adjointGroup Tag.D4 K).subtype ≤ negUnipotent Tag.D4 K := by
    rw [spanRoots, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨s, hs, c, rfl⟩, rfl⟩
    obtain ⟨hsr, hsh⟩ := hS s hs
    obtain ⟨σ, -, hσ⟩ := coe_xPar_eq_pinnedX_sign (K := K) hsr
    show ((𝕩 s c : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) ∈ negUnipotent Tag.D4 K
    rw [hσ c]
    exact le_iSup₂ (f := fun α (_ : α ∈ {α : Fin Tag.D4.rank → ℤ | IsRoot Tag.D4 α ∧ height α < 0}) =>
      rootSubgroup Tag.D4 K α) s ⟨hsr, hsh⟩ (Subgroup.subset_closure ⟨_, rfl⟩)
  haveI : CharP K (ringChar K) := ringChar.charP K
  have hP := ((positive_root_triangularity.{0, 0} Tag.D4).2 K (ringChar K)).2.2.2
  exact (hP.to_le hle).of_equiv
    (Subgroup.equivMapOfInjective _ _ (adjointGroup Tag.D4 K).subtype_injective).symm

theorem map_eq_of_map_le_inputs2311q {G : Type*} [Group G] [Finite G] (φ : MulAut G) {U : Subgroup G}
    (h : U.map φ.toMonoidHom ≤ U) : U.map φ.toMonoidHom = U :=
  Subgroup.eq_of_le_of_card_ge h (by rw [Subgroup.card_map_of_injective φ.injective])

theorem gammaP_HSL_map_spanRoots [Finite K] (ω : Kˣ) {S : List (Fin Tag.D4.rank → ℤ)}
    (hS : ∀ s ∈ S, IsRoot Tag.D4 s ∧ rhoL s ∈ S) :
    (spanRoots K S).map (gammaP K (HSL ω)).toMonoidHom = spanRoots K S := by
  refine map_eq_of_map_le_inputs2311q _ ?_
  rintro _ ⟨y, hy, rfl⟩
  have hN : sl2At K ⟨2, by decide⟩ (HSL ω) ∈
      Subgroup.normalizer (spanRoots K S : Set ↥(adjointGroup Tag.D4 K)) := by
    rw [sl2At_HSL]
    exact diag_mem_normalizer_spanRoots (coe_torusElement _ _) fun s hs => (hS s hs).1
  exact gammaP_mem_spanRoots hS hN hy

theorem conj_diag_map_spanRoots [Finite K] {t : ↥(adjointGroup Tag.D4 K)} {a : Fin Tag.D4.rank → Kˣ}
    (ht : (t : ModGL Tag.D4 K) = rootDiagUnit Tag.D4 a) {S : List (Fin Tag.D4.rank → ℤ)}
    (hS : ∀ s ∈ S, IsRoot Tag.D4 s) :
    (spanRoots K S).map (MulAut.conj t).toMonoidHom = spanRoots K S := by
  refine map_eq_of_map_le_inputs2311q _ ?_
  rintro _ ⟨y, hy, rfl⟩
  exact (Subgroup.mem_normalizer_iff.1 (diag_mem_normalizer_spanRoots ht hS) y).1 hy

theorem uniPlaneClosure_eq_top_of_diag [Finite K] (hK2 : ringChar K ≠ 2) (hK3 : ringChar K ≠ 3)
    {ω : Kˣ} (hω : orderOf ω = 3) {t : ↥(adjointGroup Tag.D4 K)} {a : Fin Tag.D4.rank → Kˣ}
    (ht : (t : ModGL Tag.D4 K) = rootDiagUnit Tag.D4 a) (ht1 : t ≠ 1) (ht3 : t ^ 3 = 1)
    {E : Subgroup (MulAut ↥(adjointGroup Tag.D4 K))} [CFSG.IsElementaryAbelian 3 ↥E]
    (hc : Nat.card E = 3 ^ 2) (hαE : gammaP K (HSL ω) ∈ E) (htE : MulAut.conj t ∈ E) :
    uniPlaneClosure (ringChar K) E = ⊤ := by
  classical
  obtain ⟨hrp, -, hK5⟩ := ringChar_facts_inputs2311q hK2 hK3
  have hct1 : MulAut.conj t ≠ 1 := fun h => ht1 (conj_injective_adj (h.trans (map_one _).symm))
  have hct3 : MulAut.conj t ^ 3 = 1 := by rw [← map_pow, ht3, map_one]
  have hαt : gammaP K (HSL ω) ∉ Subgroup.zpowers (MulAut.conj t) := by
    intro h
    apply gammaP_HSL_not_inner hω (by omega)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h
    exact ⟨t ^ k, by rw [map_zpow, hk]⟩
  have hEgen : Subgroup.closure {gammaP K (HSL ω), MulAut.conj t} = E :=
    closure_pair_eq_of_card_inputs2311q Nat.prime_three hc hαE htE hct3 hct1 hαt
  have hinv : ∀ {S : List (Fin Tag.D4.rank → ℤ)}, (∀ s ∈ S, IsRoot Tag.D4 s ∧ rhoL s ∈ S) →
      ∀ e ∈ E, (spanRoots K S).map (e : MulAut ↥(adjointGroup Tag.D4 K)).toMonoidHom = spanRoots K S := by
    intro S hS e he
    rw [← hEgen] at he
    induction he using Subgroup.closure_induction with
    | mem φ hφ =>
      rcases hφ with rfl | rfl
      · exact gammaP_HSL_map_spanRoots ω hS
      · exact conj_diag_map_spanRoots ht fun s hs => (hS s hs).1
    | one => exact Subgroup.map_id _
    | mul φ ψ _ _ h1 h2 =>
      rw [show (φ * ψ).toMonoidHom = φ.toMonoidHom.comp ψ.toMonoidHom from rfl, ← Subgroup.map_map, h2, h1]
    | inv φ _ h =>
      conv_lhs => rw [← h]
      rw [Subgroup.map_map, show φ⁻¹.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id _ by
        ext y; simp, Subgroup.map_id]
  have hpos := Inputs2311m.le_uniPlaneClosure_of_invariant_pGroup Nat.prime_three hrp (by omega)
    (E := E) hc.ge (isPGroup_spanRoots_pos fun s hs => ⟨(posRootsD4_facts.1 s hs).1,
      (posRootsD4_facts.1 s hs).2.1⟩)
    (hinv fun s hs => ⟨(posRootsD4_facts.1 s hs).1, (posRootsD4_facts.1 s hs).2.2⟩)
  have hneg := Inputs2311m.le_uniPlaneClosure_of_invariant_pGroup Nat.prime_three hrp (by omega)
    (E := E) hc.ge (isPGroup_spanRoots_neg fun s hs => ⟨(negRootsD4_facts.1 s hs).1,
      (negRootsD4_facts.1 s hs).2.1⟩)
    (hinv fun s hs => ⟨(negRootsD4_facts.1 s hs).1, (negRootsD4_facts.1 s hs).2.2⟩)
  refine eq_top_of_simple_mem fun i c => ⟨hpos ?_, hneg ?_⟩
  · exact xPar_mem_spanRoots (posRootsD4_facts.2 i) c
  · exact xPar_mem_spanRoots (negRootsD4_facts.2 i) c

end Diag

section General

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Lang.D4Three CFSG.LieType.SeitzGeneration.ExcWideThree
  CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph

set_option linter.unusedSectionVars false


variable {K : Type} [Field K]

theorem mulAut_congr_conj_of_fixed_inputs2311q {G : Type*} [Group G] {α : MulAut G} {c : G}
    (hc : α c = c) : (MulAut.congr (MulAut.conj c)).toMonoidHom α = α := by
  refine MulEquiv.ext fun y => ?_
  show (MulAut.conj c) (α ((MulAut.conj c).symm y)) = α y
  rw [MulAut.conj_symm_apply, MulAut.conj_apply, map_mul, map_mul, map_inv, hc]
  group

theorem uniPlaneClosure_eq_top_gammaP_HSL [Finite K] (hK2 : ringChar K ≠ 2) (hK3 : ringChar K ≠ 3)
    (hq : Nat.card K % 3 = 1) {ω : Kˣ} (hω : orderOf ω = 3)
    {E : Subgroup (MulAut ↥(adjointGroup Tag.D4 K))} [hEa : CFSG.IsElementaryAbelian 3 ↥E]
    (hc : Nat.card E = 3 ^ 2) (hαE : gammaP K (HSL ω) ∈ E) {x : ↥(adjointGroup Tag.D4 K)}
    (hx1 : x ≠ 1) (hxE : MulAut.conj x ∈ E) : uniPlaneClosure (ringChar K) E = ⊤ := by
  classical
  obtain ⟨hrp, -, hK5⟩ := ringChar_facts_inputs2311q hK2 hK3
  have hω3 : ω ^ 3 = 1 := hω ▸ pow_orderOf_eq_one ω
  have hx3 : x ^ 3 = 1 := by
    apply conj_injective_adj
    rw [map_pow, map_one]
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian _ hxE
  have hαx : gammaP K (HSL ω) x = x := by
    apply conj_injective_adj
    have hcomm : gammaP K (HSL ω) * MulAut.conj x = MulAut.conj x * gammaP K (HSL ω) := by
      have := hEa.toIsMulCommutative.is_comm.comm (⟨_, hαE⟩ : E) ⟨_, hxE⟩
      exact congrArg Subtype.val this
    have e1 : MulAut.conj (gammaP K (HSL ω) x) =
        gammaP K (HSL ω) * MulAut.conj x * (gammaP K (HSL ω))⁻¹ := by
      ext y
      simp [MulAut.mul_apply, MulAut.conj_apply]
    rw [e1, hcomm, mul_inv_cancel_right]
  obtain ⟨ζ, hζ⟩ := exists_orderOf_eq_three_pow (K := K)
  obtain ⟨c, hcα, hcQ⟩ := exists_conj_mem_Q0 hq (by omega) hω3 hω hζ hαx hx3
  have hcα' : gammaP K (HSL ω) c⁻¹ = c⁻¹ := by rw [map_inv, hcα]
  set Ec := E.map (MulAut.congr (MulAut.conj c⁻¹)).toMonoidHom with hEc
  suffices h : uniPlaneClosure (ringChar K) Ec = ⊤ from
    (uniPlaneGen_map_congr (MulAut.conj c⁻¹) (ringChar K) E).1 h
  haveI : CFSG.IsElementaryAbelian 3 ↥Ec := CFSG.IsElementaryAbelian.map _
  have hcEc : Nat.card Ec = 3 ^ 2 := by
    rw [hEc, Subgroup.card_map_of_injective (MulAut.congr (MulAut.conj c⁻¹)).injective, hc]
  have hαEc : gammaP K (HSL ω) ∈ Ec := ⟨_, hαE, mulAut_congr_conj_of_fixed_inputs2311q hcα'⟩
  have hxEc : MulAut.conj (c⁻¹ * x * c) ∈ Ec := by
    refine ⟨_, hxE, ?_⟩
    rw [CFSG.LieType.SeitzGeneration.mulAut_congr_conj, MulAut.conj_apply, inv_inv]
  have hx'3 : (c⁻¹ * x * c) ^ 3 = 1 := by
    rw [show c⁻¹ * x * c = c⁻¹ * x * c⁻¹⁻¹ by rw [inv_inv], conj_pow, hx3]
    group
  have hx'1 : c⁻¹ * x * c ≠ 1 := by
    intro h
    apply hx1
    have e : x = c * (c⁻¹ * x * c) * c⁻¹ := by group
    rw [e, h]
    group
  have hαx' : gammaP K (HSL ω) (c⁻¹ * x * c) = c⁻¹ * x * c := Q0_le_fixed hω3 _ hcQ
  have hyN : Subgroup.zpowers (yP hω3) ≤ Subgroup.normalizer
      (T3fix (ω := ω) (K := K) (Subgroup.zpowers ζ) : Set ↥(adjointGroup Tag.D4 K)) :=
    (Subgroup.zpowers_le).2 (yP_mem_normalizer_T3fix hω3 _)
  obtain ⟨t, htT, y, hy, hxty⟩ :=
    CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.exists_mul_of_mem_sup hyN hcQ
  obtain ⟨⟨a, -, hat⟩, -⟩ := htT
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  rw [yP_zpow_eq] at hxty
  have hlt : (k % 3).toNat < 3 := by
    have := Int.emod_lt_of_pos k (by norm_num : (0 : ℤ) < 3)
    omega
  rcases (by omega : (k % 3).toNat = 0 ∨ (k % 3).toNat = 1 ∨ (k % 3).toNat = 2) with h0 | h1 | h2
  · rw [h0, pow_zero, mul_one] at hxty
    exact uniPlaneClosure_eq_top_of_diag hK2 hK3 hω (by rw [hxty]; exact hat) hx'1 hx'3 hcEc hαEc hxEc
  · rw [h1, pow_one] at hxty
    rw [hxty] at hx'3 hαx' hxEc
    exact uniPlaneClosure_eq_top_of_tyP hK2 hK3 hq hω3 hω hat hx'3 hαx' hαEc hxEc
  · rw [h2] at hxty
    have hsq0 : (t * yP hω3 ^ 2) ^ 2 = t * (yP hω3 ^ 2 * t * (yP hω3 ^ 2)⁻¹) * yP hω3 := by
      have h3 := yP_pow_three (K := K) hω3
      have e : (t * yP hω3 ^ 2) ^ 2 = t * (yP hω3 ^ 2 * t * (yP hω3 ^ 2)⁻¹) * (yP hω3 ^ 3 * yP hω3) := by
        simp only [sq, pow_succ, pow_zero, one_mul, mul_inv_rev, mul_assoc, inv_mul_cancel_left]
      rw [e, h3, one_mul]
    obtain ⟨t', ht'def⟩ : ∃ t', t' = t * (yP hω3 ^ 2 * t * (yP hω3 ^ 2)⁻¹) := ⟨_, rfl⟩
    have ht' : (t' : ModGL Tag.D4 K) =
        rootDiagUnit Tag.D4 (a * tupAct (weylG2M ^ (4 * 2)) a) := by
      rw [ht'def, Subgroup.coe_mul, hat, yP_pow_conj_diag hω3 2 hat, rootDiagUnit_mul]
    have hsq : (c⁻¹ * x * c) ^ 2 = t' * yP hω3 := by
      rw [hxty, hsq0, ht'def]
    have h3' : (t' * yP hω3) ^ 3 = 1 := by
      rw [← hsq, ← pow_mul, mul_comm, pow_mul, hx'3, one_pow]
    have hα' : gammaP K (HSL ω) (t' * yP hω3) = t' * yP hω3 := by
      rw [← hsq, map_pow, hαx']
    have hE' : MulAut.conj (t' * yP hω3) ∈ Ec := by
      rw [← hsq, map_pow]
      exact Ec.pow_mem hxEc 2
    exact uniPlaneClosure_eq_top_of_tyP hK2 hK3 hq hω3 hω ht' h3' hα' hαEc hE'

end General

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311q
