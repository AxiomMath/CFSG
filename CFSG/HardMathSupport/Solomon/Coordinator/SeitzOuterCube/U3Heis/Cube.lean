module

public import CFSG.HardMathSupport.Malle.Coordinator.SeitzA2Three.AssemblyU
public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.A2Heis.Cube
public import CFSG.RankThree.PartTwo.KFacts.AutPSUScalar

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.U3Heis

open CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartTwo.KFacts
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)
open CFSG.HardMathSupport.Malle.Coordinator.SeitzA2Three
open CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner (monomGL diagGL)
open CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.A2Heis
  (ncard_orbit_le_three pow_smul_eq_self monomGL_mul_Dω Dω_pow_three monomGL_pow_three)

variable {ℓ f : ℕ} {F : Type} [Field F] (h : UnitaryFieldData ℓ f F)

structure HeisHypU (σ : F ≃+* F) (lam ω : Fˣ) (D X : unitaryIsom3 h) : Prop where
  ord : orderOf σ = 3
  ω3 : ω ^ 3 = 1
  fixl : σ (lam : F) = lam
  fixω : σ (ω : F) = ω
  hD : (D : GL (Fin 3) F) = diagGL F 1 ω (ω ^ 2)
  hX : (X : GL (Fin 3) F) = monomGL F lam

variable {h}

theorem HeisHypU.pow3 {σ : F ≃+* F} {lam ω : Fˣ} {D X : unitaryIsom3 h}
    (hh : HeisHypU h σ lam ω D X) : σ ^ 3 = 1 :=
  hh.ord ▸ pow_orderOf_eq_one σ

theorem commute_psuField_psuConj {σ : F ≃+* F} {A : unitaryIsom3 h}
    (hA : glAut σ (A : GL (Fin 3) F) = A) : Commute (psuField h σ) (psuConj h A) := by
  have h1 := psuField_mul_psuConj_mul_inv σ A
  have h2 : (⟨glAut σ (A : GL (Fin 3) F), glAut_mem_unitaryIsom3 σ A.2⟩ : unitaryIsom3 h) = A :=
    Subtype.ext hA
  rw [h2] at h1
  exact mul_inv_eq_iff_eq_mul.1 h1

theorem psuConj_eq_of_eq_scalar_mul {A B : unitaryIsom3 h} {c : Fˣ}
    (hAB : (A : GL (Fin 3) F) = Matrix.GeneralLinearGroup.scalar (Fin 3) c * B) :
    psuConj h A = psuConj h B := by
  have h1 : psuConj h (A * B⁻¹) = 1 := psuConj_eq_one_of_coe_eq_scalar (c := c) (by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hAB, mul_inv_cancel_right])
  rw [map_mul, map_inv, mul_inv_eq_one] at h1
  exact h1

theorem glAut_diagGL {σ : F ≃+* F} {ω : Fˣ} (hω : σ (ω : F) = ω) :
    glAut σ (diagGL F 1 ω (ω ^ 2)) = diagGL F 1 ω (ω ^ 2) := by
  apply Units.ext
  rw [coe_glAut]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagGL, hω]

theorem glAut_monomGL {σ : F ≃+* F} {lam : Fˣ} (hl : σ (lam : F) = lam) :
    glAut σ (monomGL F lam) = monomGL F lam := by
  apply Units.ext
  rw [coe_glAut]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [monomGL, hl]

section Gens

variable {σ : F ≃+* F} {lam ω : Fˣ} {D X : unitaryIsom3 h}

theorem commute_fU_cD (hh : HeisHypU h σ lam ω D X) :
    Commute (psuField h σ) (psuConj h D) :=
  commute_psuField_psuConj (by rw [hh.hD]; exact glAut_diagGL hh.fixω)

theorem commute_fU_cX (hh : HeisHypU h σ lam ω D X) :
    Commute (psuField h σ) (psuConj h X) :=
  commute_psuField_psuConj (by rw [hh.hX]; exact glAut_monomGL hh.fixl)

theorem commute_cD_cX (hh : HeisHypU h σ lam ω D X) :
    Commute (psuConj h D) (psuConj h X) := by
  have hXD : psuConj h (X * D) = psuConj h (D * X) := by
    refine psuConj_eq_of_eq_scalar_mul (c := ω ^ 2) ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hh.hD, hh.hX]
    exact monomGL_mul_Dω hh.ω3 lam
  rw [map_mul, map_mul] at hXD
  exact hXD.symm

theorem fU_pow_three (hh : HeisHypU h σ lam ω D X) : psuField h σ ^ 3 = 1 := by
  rw [← map_pow, hh.pow3, map_one]

theorem cD_pow_three (hh : HeisHypU h σ lam ω D X) : psuConj h D ^ 3 = 1 := by
  rw [← map_pow]
  refine psuConj_eq_one_of_coe_eq_scalar (c := 1) ?_
  rw [Subgroup.coe_pow, hh.hD, Dω_pow_three hh.ω3, map_one]

theorem cX_pow_three (hh : HeisHypU h σ lam ω D X) : psuConj h X ^ 3 = 1 := by
  rw [← map_pow]
  refine psuConj_eq_one_of_coe_eq_scalar (c := lam) ?_
  rw [Subgroup.coe_pow, hh.hX, monomGL_pow_three]

theorem heisCubeU_eq (σ : F ≃+* F) (D X : unitaryIsom3 h) :
    heisCubeU h σ D X = Subgroup.zpowers (psuField h σ) ⊔
      (Subgroup.zpowers (psuConj h D) ⊔ Subgroup.zpowers (psuConj h X)) := rfl

theorem mem_zpowers_iff_pow {G : Type*} [Group G] {g c : G} (hg : g ^ 3 = 1)
    (hc : c ∈ Subgroup.zpowers g) : ∃ k : ℕ, c = g ^ k := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
  have h3 : g ^ (3 : ℤ) = 1 := by rw [zpow_ofNat]; exact hg
  refine ⟨(n % 3).toNat, ?_⟩
  rw [zpow_eq_zpow_emod n h3, ← zpow_natCast,
    Int.toNat_of_nonneg (Int.emod_nonneg n (by norm_num))]

theorem exists_of_mem_heisCubeU (hh : HeisHypU h σ lam ω D X) {b : MulAut (unitaryPSU h 3)}
    (hb : b ∈ heisCubeU h σ D X) :
    ∃ i j k : ℕ, b = psuField h σ ^ i * psuConj h D ^ j * psuConj h X ^ k := by
  rw [heisCubeU_eq] at hb
  have hA : ∀ a ∈ Subgroup.zpowers (psuConj h D) ⊔ Subgroup.zpowers (psuConj h X),
      Commute a (psuField h σ) := by
    intro a ha
    have hle : Subgroup.zpowers (psuConj h D) ⊔ Subgroup.zpowers (psuConj h X) ≤
        Subgroup.centralizer ({psuField h σ} : Set (MulAut (unitaryPSU h 3))) := by
      refine sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (commute_fU_cD hh).eq.symm
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (commute_fU_cX hh).eq.symm
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle ha)
  obtain ⟨i, a, ha, rfl⟩ := exists_pow_mul_of_mem_sup (fU_pow_three hh) hA b hb
  have hB : ∀ c ∈ Subgroup.zpowers (psuConj h X), Commute c (psuConj h D) := by
    intro c hc
    obtain ⟨k, rfl⟩ := mem_zpowers_iff_pow (cX_pow_three hh) hc
    exact ((commute_cD_cX hh).pow_right k).symm
  obtain ⟨j, c, hc, rfl⟩ := exists_pow_mul_of_mem_sup (cD_pow_three hh) hB a ha
  obtain ⟨k, rfl⟩ := mem_zpowers_iff_pow (cX_pow_three hh) hc
  exact ⟨i, j, k, by rw [mul_assoc]⟩

theorem fU_ne_one (hh : HeisHypU h σ lam ω D X) : psuField h σ ≠ 1 := by
  intro h1
  have hσ1 : σ ≠ 1 := by
    intro h2
    have := hh.ord
    rw [h2, orderOf_one] at this
    norm_num at this
  apply hσ1
  refine (eq_one_of_psuConj_mul_psuField_eq_one (h := h) 1 σ ?_).1
  rw [map_one, one_mul, h1]

variable [Finite F]

theorem card_heisCubeU (hh : HeisHypU h σ lam ω D X) :
    ∃ s : ℕ, 1 ≤ s ∧ Nat.card (heisCubeU h σ D X) = 3 ^ s := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (unitaryPSU h 3) := inferInstance
  have : Finite (MulAut (unitaryPSU h 3)) := MulEquiv.finite_left
  have hp : IsPGroup 3 (heisCubeU h σ D X) := by
    intro g
    refine ⟨1, ?_⟩
    obtain ⟨i, j, k, hg⟩ := exists_of_mem_heisCubeU hh g.2
    apply Subtype.ext
    rw [pow_one, Subgroup.coe_pow, hg, Subgroup.coe_one]
    have h1 : Commute (psuField h σ ^ i) (psuConj h D ^ j) :=
      ((commute_fU_cD hh).pow_left i).pow_right j
    have h2 : Commute (psuField h σ ^ i * psuConj h D ^ j) (psuConj h X ^ k) :=
      (((commute_fU_cX hh).pow_left i).pow_right k).mul_left
        (((commute_cD_cX hh).pow_left j).pow_right k)
    rw [h2.mul_pow, h1.mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, mul_comm i, mul_comm j,
      mul_comm k, pow_mul, pow_mul, pow_mul, fU_pow_three hh, cD_pow_three hh, cX_pow_three hh,
      one_pow, one_pow, one_pow, mul_one, mul_one]
  obtain ⟨s, hs⟩ := hp.exists_card_eq
  refine ⟨s, ?_, hs⟩
  rcases Nat.eq_zero_or_pos s with h0 | h0
  · exfalso
    rw [h0, pow_zero] at hs
    have hmem : psuField h σ ∈ heisCubeU h σ D X :=
      (le_sup_left : Subgroup.zpowers (psuField h σ) ≤ _) (Subgroup.mem_zpowers _)
    have hsub := (Subgroup.card_eq_one).1 hs
    have : psuField h σ ∈ (⊥ : Subgroup (MulAut (unitaryPSU h 3))) := hsub ▸ hmem
    exact fU_ne_one hh ((Subgroup.mem_bot).1 this)
  · exact h0

end Gens

variable (h) in
@[expose] def hyperFixU (σ : F ≃+* F) (D X : unitaryIsom3 h) : Set (unitaryPSU h 3) :=
  {x | ∃ H : Subgroup (MulAut (unitaryPSU h 3)), H ≤ heisCubeU h σ D X ∧
    H.relIndex (heisCubeU h σ D X) = 3 ∧ ∀ b ∈ H, b x = x}

theorem modelHyperGen_iff_closure (σ : F ≃+* F) (D X : unitaryIsom3 h) :
    ModelHyperGen 3 (heisCubeU h σ D X) ↔ Subgroup.closure (hyperFixU h σ D X) = ⊤ := Iff.rfl

section Orbit

variable [Finite F] {σ : F ≃+* F} {lam ω : Fˣ} {D X : unitaryIsom3 h}

theorem smul_eq_apply' (b : MulAut (unitaryPSU h 3)) (x : unitaryPSU h 3) : b • x = b x := rfl

theorem mem_hyperFixU_of_orbit (hh : HeisHypU h σ lam ω D X) {x : unitaryPSU h 3}
    (horb : (MulAction.orbit (heisCubeU h σ D X) x).ncard ≤ 3) : x ∈ hyperFixU h σ D X := by
  have : Finite (unitaryPSU h 3) := inferInstance
  have : Finite (MulAut (unitaryPSU h 3)) := MulEquiv.finite_left
  obtain ⟨s, hs, hcard⟩ := card_heisCubeU hh
  obtain ⟨H, hHB, hHi, hHx⟩ :=
    CFSG.HardMathSupport.Foote.ModuleExclusions.exists_hyperplane_of_orbit_le _ hs hcard x horb
  exact ⟨H, hHB, hHi, fun b hb => hHx b hb⟩

theorem mem_hyperFixU_of_fU_cD (hh : HeisHypU h σ lam ω D X) {x : unitaryPSU h 3}
    (hf : psuField h σ x = x) (hd : psuConj h D x = x) : x ∈ hyperFixU h σ D X := by
  refine mem_hyperFixU_of_orbit hh
    (ncard_orbit_le_three _ x (psuConj h X) (cX_pow_three hh) ?_)
  intro b hb
  obtain ⟨i, j, k, rfl⟩ := exists_of_mem_heisCubeU hh hb
  refine ⟨k, ?_⟩
  have hc : Commute (psuField h σ ^ i * psuConj h D ^ j) (psuConj h X ^ k) :=
    (((commute_fU_cX hh).pow_left i).pow_right k).mul_left
      (((commute_cD_cX hh).pow_left j).pow_right k)
  rw [hc.eq, mul_smul, mul_smul, pow_smul_eq_self (g := psuConj h D) hd j,
    pow_smul_eq_self (g := psuField h σ) hf i]

theorem mem_hyperFixU_of_fU_cX (hh : HeisHypU h σ lam ω D X) {x : unitaryPSU h 3}
    (hf : psuField h σ x = x) (hx : psuConj h X x = x) : x ∈ hyperFixU h σ D X := by
  refine mem_hyperFixU_of_orbit hh
    (ncard_orbit_le_three _ x (psuConj h D) (cD_pow_three hh) ?_)
  intro b hb
  obtain ⟨i, j, k, rfl⟩ := exists_of_mem_heisCubeU hh hb
  refine ⟨j, ?_⟩
  have hc : psuField h σ ^ i * psuConj h D ^ j * psuConj h X ^ k =
      psuConj h D ^ j * (psuField h σ ^ i * psuConj h X ^ k) := by
    rw [(((commute_fU_cD hh).pow_left i).pow_right j).eq, mul_assoc]
  rw [hc, mul_smul, mul_smul, pow_smul_eq_self (g := psuConj h X) hx k,
    pow_smul_eq_self (g := psuField h σ) hf i]

theorem mem_hyperFixU_of_cD_fUcXpow (hh : HeisHypU h σ lam ω D X) {x : unitaryPSU h 3}
    {m : ℕ} (hm : m = 1 ∨ m = 2) (hd : psuConj h D x = x)
    (hfx : (psuField h σ * psuConj h X ^ m) x = x) : x ∈ hyperFixU h σ D X := by
  refine mem_hyperFixU_of_orbit hh
    (ncard_orbit_le_three _ x (psuConj h X) (cX_pow_three hh) ?_)
  intro b hb
  obtain ⟨i, j, k, rfl⟩ := exists_of_mem_heisCubeU hh hb
  have hstep : ∀ n : ℕ, psuField h σ • (psuConj h X ^ n • x) =
      psuConj h X ^ (n + (3 - m)) • x := by
    intro n
    have hfs : psuField h σ = (psuField h σ * psuConj h X ^ m) * psuConj h X ^ (3 - m) := by
      rw [mul_assoc, ← pow_add, show m + (3 - m) = 3 by omega, cX_pow_three hh, mul_one]
    have hcm : Commute (psuField h σ * psuConj h X ^ m) (psuConj h X ^ (n + (3 - m))) :=
      ((commute_fU_cX hh).mul_left ((Commute.refl (psuConj h X)).pow_left m)).pow_right _
    have e1 : psuField h σ • (psuConj h X ^ n • x) =
        (psuField h σ * psuConj h X ^ m) • (psuConj h X ^ (n + (3 - m)) • x) := by
      conv_lhs => rw [hfs]
      rw [mul_smul, ← mul_smul (psuConj h X ^ (3 - m)), ← pow_add, add_comm (3 - m) n]
    have e2 : (psuField h σ * psuConj h X ^ m) • (psuConj h X ^ (n + (3 - m)) • x) =
        psuConj h X ^ (n + (3 - m)) • x := by
      rw [← mul_smul, hcm.eq, mul_smul, smul_eq_apply' (psuField h σ * psuConj h X ^ m) x, hfx]
    rw [e1, e2]
  have hiter : ∀ e n : ℕ, psuField h σ ^ e • (psuConj h X ^ n • x) =
      psuConj h X ^ (n + (3 - m) * e) • x := by
    intro e
    induction e with
    | zero => intro n; simp
    | succ e ih =>
      intro n
      rw [pow_succ', mul_smul, ih, hstep, show n + (3 - m) * e + (3 - m) =
        n + (3 - m) * (e + 1) by ring]
  refine ⟨k + (3 - m) * i, ?_⟩
  have hc : psuField h σ ^ i * psuConj h D ^ j * psuConj h X ^ k =
      psuField h σ ^ i * (psuConj h X ^ k * psuConj h D ^ j) := by
    rw [mul_assoc, (((commute_cD_cX hh).pow_left j).pow_right k).eq]
  rw [hc, mul_smul, mul_smul, pow_smul_eq_self (g := psuConj h D) hd j, hiter]

end Orbit

end CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.U3Heis
