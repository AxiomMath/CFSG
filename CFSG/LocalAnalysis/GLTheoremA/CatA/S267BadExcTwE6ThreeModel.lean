module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcTwE6Three
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcHRConcB
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcTwE6Conc
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcTwE6ConcOuter

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.TwE6Outer

open Matrix CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley CFSG.LieType.Chevalley.E6A5Cube CFSG.LieType.SeitzGeneration.ExcWideThree
open CFSG.LieType.Universal.Unitary (SU SUid antidiag conjTr conjEquiv)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply)
open CFSG.ClassicalInvolution.Phan (Su)
open CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary (coordBlockSU mem_coordBlockSU_iff)
open CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.TwE6Conc
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen (ModelBGen)
open scoped commutatorElement

theorem eq_one_of_conj_eq_smul_of_trace_ne_zero {K : Type} [Field K] {n : ℕ}
    {Y Yi D : Matrix (Fin n) (Fin n) K} (hYi : Yi * Y = 1) {μ : K} (h : Y * D * Yi = μ • D)
    (htr : D.trace ≠ 0) : μ = 1 := by
  have h1 : (Y * D * Yi).trace = D.trace := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hYi, Matrix.one_mul]
  rw [h, Matrix.trace_smul, smul_eq_mul] at h1
  have h2 : (μ - 1) * D.trace = 0 := by linear_combination h1
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact sub_eq_zero.1 h3
  · exact absurd h3 htr

theorem add_inv_eq_neg_one_of_orderOf_three {K : Type} [Field K] {c : Kˣ} (hc : orderOf c = 3) :
    (c : K) + ((c⁻¹ : Kˣ) : K) = -1 := by
  have h3 : (c : K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hc, pow_orderOf_eq_one, Units.val_one]
  have h1 : (c : K) ≠ 1 := fun h => by
    have : c = 1 := Units.ext h
    rw [this, orderOf_one] at hc
    exact absurd hc (by norm_num)
  have hq : (c : K) ^ 2 + c + 1 = 0 := by
    have h2 : ((c : K) - 1) * ((c : K) ^ 2 + c + 1) = 0 := by linear_combination h3
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd (sub_eq_zero.1 h) h1
    · exact h
  have hinv : ((c⁻¹ : Kˣ) : K) = (c : K) ^ 2 := by
    rw [Units.val_inv_eq_inv_val]
    have h4 : (c : K) * (c : K) ^ 2 = 1 := by rw [← h3]; ring
    exact inv_eq_of_mul_eq_one_right h4
  rw [hinv]
  linear_combination hq

section Diag


variable {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ] {p : ℕ}
  [Fact p.Prime]

@[expose] def diagGen4 : Fin 4 → Multiplicative (ZMod p) :=
  (Pi.mulSingle (0 : Fin 4) (Multiplicative.ofAdd (1 : ZMod p)) : Fin 4 → Multiplicative (ZMod p)) *
    Pi.mulSingle (1 : Fin 4) (Multiplicative.ofAdd (-1 : ZMod p))

theorem snocOneHom_diagGen4 :
    snocOneHom (Multiplicative (ZMod p)) 4 (diagGen4 (p := p)) = diagGen := by
  funext i
  fin_cases i <;> simp [snocOneHom, diagGen4, diagGen, Fin.snoc, Pi.mulSingle_apply] <;>
    first | rfl | decide

theorem diagGen4_ne_one : (diagGen4 : Fin 4 → Multiplicative (ZMod p)) ≠ 1 := by
  intro h
  apply diagGen_ne_one (p := p)
  rw [← snocOneHom_diagGen4, h, map_one]

variable (c : Kˣ) (hc : orderOf c = p) (hpQ : p ∣ ℓ ^ f + 1)

theorem diagThreeHom_diagGen4 :
    diagThreeHom c hc hpQ diagGen4 = diagSUHom c hc hpQ diagGen := by
  rw [diagThreeHom, MonoidHom.comp_apply, snocOneHom_diagGen4]

theorem diagThreeHom_diagGen4_mem : diagThreeHom c hc hpQ diagGen4 ∈ coordBlockSU K ℓ f blk01 := by
  rw [diagThreeHom_diagGen4]
  exact diagSUHom_diagGen_mem c hc hpQ

theorem trace_diagThreeHom_diagGen4 :
    (((diagThreeHom c hc hpQ diagGen4 : Su K ℓ f 6) : GL (Fin 6) K) :
      Matrix (Fin 6) (Fin 6) K).trace = (c : K) + ((c⁻¹ : Kˣ) : K) + 4 := by
  rw [diagThreeHom_diagGen4, coe_diagSUHom, Matrix.trace_diagonal, Fin.sum_univ_castSucc,
    diagTuple_last]
  have hprod : ∏ j, (diagGen : Fin 5 → Multiplicative (ZMod p)) j = 1 := by
    simp only [diagGen, Pi.mul_apply]
    rw [Finset.prod_mul_distrib, Finset.prod_pi_mulSingle', Finset.prod_pi_mulSingle',
      if_pos (Finset.mem_univ _), if_pos (Finset.mem_univ _), ofAdd_neg]
    exact mul_inv_cancel _
  rw [← map_prod, hprod, map_one, inv_one, Units.val_one]
  simp only [diagTuple_castSucc, Fin.sum_univ_five]
  have h0 : powHom c hc (diagGen 0) = c := by
    simp only [diagGen, Pi.mul_apply, Pi.mulSingle_eq_same]
    rw [Pi.mulSingle_eq_of_ne (by decide : (0 : Fin 5) ≠ 1), mul_one, powHom_apply, toAdd_ofAdd,
      ZMod.val_one, pow_one]
  have h1 : powHom c hc (diagGen 1) = c⁻¹ := by
    have e : diagGen (p := p) 1 = (Multiplicative.ofAdd (1 : ZMod p))⁻¹ := by
      simp only [diagGen, Pi.mul_apply, Pi.mulSingle_eq_same]
      rw [Pi.mulSingle_eq_of_ne (by decide : (1 : Fin 5) ≠ 0), one_mul]
      rfl
    rw [e, map_inv, powHom_apply, toAdd_ofAdd, ZMod.val_one, pow_one]
  have hj : ∀ j : Fin 5, j ≠ 0 → j ≠ 1 → powHom c hc (diagGen j) = 1 := by
    intro j hj0 hj1
    simp only [diagGen, Pi.mul_apply]
    rw [Pi.mulSingle_eq_of_ne hj0, Pi.mulSingle_eq_of_ne hj1, mul_one, map_one]
  rw [h0, h1, hj 2 (by decide) (by decide), hj 3 (by decide) (by decide),
    hj 4 (by decide) (by decide), Units.val_one]
  ring

variable {hK : Nat.card K = (ℓ ^ f) ^ 2} {hf : 1 ≤ f} {ζ : K} {hζ : ζ ≠ 0}
  {hσζ : unitaryInvolution K ℓ f ζ = -ζ} {P : GL (Fin 6) K}
  {hP : conjTr (unitaryInvolution K ℓ f) (P : Matrix (Fin 6) (Fin 6) K) *
    (P : Matrix (Fin 6) (Fin 6) K) = antidiag 6}

theorem commute_of_leviSU_commute_diagThree
    (htr : (c : K) + ((c⁻¹ : Kˣ) : K) + 4 ≠ 0) (y : Su K ℓ f 6)
    (hy : leviSU hK hf hζ hσζ P hP y * leviSU hK hf hζ hσζ P hP (diagThreeHom c hc hpQ diagGen4) =
      leviSU hK hf hζ hσζ P hP (diagThreeHom c hc hpQ diagGen4) * leviSU hK hf hζ hσζ P hP y) :
    y * diagThreeHom c hc hpQ diagGen4 = diagThreeHom c hc hpQ diagGen4 * y := by
  set h := diagThreeHom c hc hpQ diagGen4 with hh
  have h1 : leviSU hK hf hζ hσζ P hP (y * h * y⁻¹ * h⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hy]
    group
  obtain ⟨μ, hμ⟩ := exists_smul_of_leviSU_eq_one hK hf hζ hσζ P hP h1
  have hμ' : (((y * h * y⁻¹ : Su K ℓ f 6) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      μ • (((h : Su K ℓ f 6) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) := by
    have e : y * h * y⁻¹ = (y * h * y⁻¹ * h⁻¹) * h := by group
    rw [e, Subgroup.coe_mul, Units.val_mul, hμ, Matrix.smul_mul, Matrix.one_mul]
  have hY : (((y⁻¹ : Su K ℓ f 6) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
      (((y : Su K ℓ f 6) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = 1 := by
    rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, Units.val_one]
  have htr' : (((h : Su K ℓ f 6) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).trace ≠ 0 := by
    rw [hh, trace_diagThreeHom_diagGen4]
    exact htr
  have hconj : (((y : Su K ℓ f 6) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
      (((h : Su K ℓ f 6) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
      (((y⁻¹ : Su K ℓ f 6) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      μ • (((h : Su K ℓ f 6) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) := by
    rw [← hμ']
    simp only [Subgroup.coe_mul, Units.val_mul]
  have hμ1 : μ = 1 := eq_one_of_conj_eq_smul_of_trace_ne_zero hY hconj htr'
  rw [hμ1, one_smul] at hμ'
  have e : y * h * y⁻¹ = h := Subtype.ext (Units.ext hμ')
  calc y * h = y * h * y⁻¹ * y := by group
    _ = h * y := by rw [e]

end Diag

section ModelA


variable {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ]

theorem five_le_of_three_dvd_add_one (hℓ2 : ℓ ≠ 2) (h3 : 3 ∣ ℓ ^ f + 1) : 5 ≤ ℓ ^ f := by
  have hℓ : ℓ.Prime := Fact.out
  have hodd : Odd (ℓ ^ f) := (hℓ.eq_two_or_odd'.resolve_left hℓ2).pow
  have hpos : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ hℓ.pos
  obtain ⟨k, hk⟩ := hodd
  obtain ⟨j, hj⟩ := h3
  omega

theorem three_dvd_sq_sub_one_of_dvd_add_one {Q : ℕ} (hQ : 1 ≤ Q) (h3 : 3 ∣ Q + 1) :
    3 ∣ Q ^ 2 - 1 := by
  have h : Q ^ 2 - 1 = (Q + 1) * (Q - 1) := by
    have h2 : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ (by omega)
    zify [hQ, h2]
    ring
  rw [h]
  exact h3.mul_right _

theorem modelAGen_twistedE6_three_spec (hK : Nat.card K = (ℓ ^ f) ^ 2) (hf : 1 ≤ f)
    (hℓ2 : ℓ ≠ 2) (h3 : 3 ∣ ℓ ^ f + 1) :
    ∃ (ζ : K) (hζ : ζ ≠ 0) (hσζ : unitaryInvolution K ℓ f ζ = -ζ) (P : GL (Fin 6) K)
      (hP : conjTr (unitaryInvolution K ℓ f) (P : Matrix (Fin 6) (Fin 6) K) *
        (P : Matrix (Fin 6) (Fin 6) K) = antidiag 6)
      (c : Kˣ) (hc : orderOf c = 3)
      (hct : unitaryInvolution K ℓ f ((c : K) + ((c⁻¹ : Kˣ) : K)) = (c : K) + ((c⁻¹ : Kˣ) : K))
      (φ : (Fin 4 → Multiplicative (ZMod 3)) →* Su K ℓ f 6)
      (A₁₂ : Subgroup ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f))),
      Function.Injective ((leviSU hK hf hζ hσζ P hP).comp φ) ∧
      Subgroup.zpowers (twE6R0 c hct) ≤ A₁₂ ∧
      A₁₂ ≤ (twE6Phi hK hf hζ hσζ P hP (by norm_num) hc hct φ).range ∧
      Nat.card A₁₂ = 3 ^ 2 ∧
      GLAPLayer 3 ((leviJ K ℓ f).subgroupOf (twistedE6RootGroup K (unitaryInvolution K ℓ f)) ⊓
        Subgroup.centralizer (A₁₂ : Set ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f)))) ≠ ⊥ := by
  classical
  have hQ1 : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ (Fact.out : ℓ.Prime).pos
  have hpQ2 := three_dvd_sq_sub_one_of_dvd_add_one hQ1 h3
  obtain ⟨ζ, hζ, hσζ⟩ := CFSG.LieType.BorelTits.exists_unitaryInvolution_eq_neg hK
  obtain ⟨P, hP⟩ := CFSG.LieType.Universal.Unitary.exists_wittMatrix hK 6
  obtain ⟨c, hc⟩ := exists_orderOf_units_eq hK Nat.prime_three hpQ2
  have hcs := add_inv_eq_neg_one_of_orderOf_three hc
  have h3K : (3 : K) ≠ 0 := by
    have := natCast_ne_zero_of_dvd_sq (K := K) hf Nat.prime_three hpQ2
    exact_mod_cast this
  have hct : unitaryInvolution K ℓ f ((c : K) + ((c⁻¹ : Kˣ) : K)) = (c : K) + ((c⁻¹ : Kˣ) : K) := by
    rw [hcs, map_neg, map_one]
  have htr : (c : K) + ((c⁻¹ : Kˣ) : K) + 4 ≠ 0 := by
    rw [hcs]
    intro h
    apply h3K
    linear_combination h
  obtain ⟨h12A, h12c, h12L⟩ := glaPLayer_inf_centralizer_A12_ne_bot hK hf hζ hσζ P hP hℓ2
    (five_le_of_three_dvd_add_one hℓ2 h3) Nat.prime_three (by norm_num) (by exact_mod_cast h3K)
    (dvd_card_su_two hK hpQ2) hc hct (leviSU_comp_diagThreeHom_injective c hc h3)
    (diagThreeHom_diagGen4_mem c hc h3) diagGen4_ne_one (commute_of_leviSU_commute_diagThree c hc h3 htr)
  exact ⟨ζ, hζ, hσζ, P, hP, c, hc, hct, diagThreeHom c hc h3, _,
    leviSU_comp_diagThreeHom_injective c hc h3, le_sup_left, h12A, h12c, h12L⟩

theorem modelAGen_twistedE6_three_of_dvd_add_one (hK : Nat.card K = (ℓ ^ f) ^ 2) (hf : 1 ≤ f)
    (hℓ2 : ℓ ≠ 2) (h3 : 3 ∣ ℓ ^ f + 1) :
    ModelGen.ModelAGen 3 5 ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f)) := by
  obtain ⟨ζ, hζ, hσζ, P, hP, c, hc, hct, φ, A₁₂, hιφ, h1, h2, h3', h4⟩ :=
    modelAGen_twistedE6_three_spec hK hf hℓ2 h3
  obtain ⟨hAe, hAc, -, hA₁c, hJcomp, hAN, hcent, ht1, ht2, hJt, hAt⟩ :=
    modelAGen_twistedE6_spec_of_inj hK hf hζ hσζ P hP hℓ2 (by norm_num) hc hct
      (by norm_num : 0 < 4) hιφ
  exact ⟨_, _, A₁₂, _, _, hAe, hAc, h1, h2, hA₁c, h3', hJcomp, hAN, hcent, h4, ht1, ht2, hJt, hAt⟩

end ModelA

section ModelB


variable {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ]

theorem modelBGen_twistedE6_three_spec (hK : Nat.card K = (ℓ ^ f) ^ 2) (hf : 1 ≤ f)
    (hℓ2 : ℓ ≠ 2) (h3 : 3 ∣ ℓ ^ f + 1) {ε : K ≃+* K} (hε : orderOf ε = 3)
    (hout : fieldActor (unitaryInvolution K ℓ f) ε ∉
      (MulAut.conj : ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f)) →*
        MulAut ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f))).range) :
    ∃ (ζ : K) (hζ : ζ ≠ 0) (hσζ : unitaryInvolution K ℓ f ζ = -ζ) (P : GL (Fin 6) K)
      (hP : conjTr (unitaryInvolution K ℓ f) (P : Matrix (Fin 6) (Fin 6) K) *
        (P : Matrix (Fin 6) (Fin 6) K) = antidiag 6)
      (c : Kˣ) (hc : orderOf c = 3)
      (hct : unitaryInvolution K ℓ f ((c : K) + ((c⁻¹ : Kˣ) : K)) = (c : K) + ((c⁻¹ : Kˣ) : K))
      (φ : (Fin 4 → Multiplicative (ZMod 3)) →* Su K ℓ f 6),
      ε ζ = ζ ∧
      (∀ i j, ε ((P : Matrix (Fin 6) (Fin 6) K) i j) = (P : Matrix (Fin 6) (Fin 6) K) i j) ∧
      ε ((c : K) + ((c⁻¹ : Kˣ) : K)) = (c : K) + ((c⁻¹ : Kˣ) : K) ∧
      (∀ x, suidMap (unitaryInvolution K ℓ f) 6 (ringEquiv_comm_of_finite _ ε) (φ x) = φ x) ∧
      Function.Injective ((leviSU hK hf hζ hσζ P hP).comp φ) ∧
      fieldActor (t := TwistTag.E6) (unitaryInvolution K ℓ f) ε ^ 3 = 1 ∧
        fieldActor (t := TwistTag.E6) (unitaryInvolution K ℓ f) ε ∉
          (MulAut.conj : ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f)) →*
            MulAut ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f))).range ∧
        IsElemAbelian 3 (twE6Phi hK hf hζ hσζ P hP (by norm_num) hc hct φ).range ∧
        Nat.card (twE6Phi hK hf hζ hσζ P hP (by norm_num) hc hct φ).range = 3 ^ (4 + 1) ∧
        (∀ a ∈ (twE6Phi hK hf hζ hσζ P hP (by norm_num) hc hct φ).range,
          fieldActor (t := TwistTag.E6) (unitaryInvolution K ℓ f) ε a = a) ∧
        Subgroup.zpowers (twE6R0 c hct) ≤ (twE6Phi hK hf hζ hσζ P hP (by norm_num) hc hct φ).range ∧
        Nat.card (Subgroup.zpowers (twE6R0 c hct)) = 3 ∧
        GLAPComponent 3 (Subgroup.centralizer
            ((Subgroup.zpowers (twE6R0 c hct) : Subgroup _) :
              Set ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f))))
          ((leviJ K ℓ f).subgroupOf (twistedE6RootGroup K (unitaryInvolution K ℓ f))) ∧
        (twE6Phi hK hf hζ hσζ P hP (by norm_num) hc hct φ).range ≤
          Subgroup.normalizer (((leviJ K ℓ f).subgroupOf
            (twistedE6RootGroup K (unitaryInvolution K ℓ f)) : Subgroup _) :
              Set ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f))) ∧
        ((leviJ K ℓ f).subgroupOf (twistedE6RootGroup K (unitaryInvolution K ℓ f))).map
            (fieldActor (t := TwistTag.E6) (unitaryInvolution K ℓ f) ε).toMonoidHom =
          (leviJ K ℓ f).subgroupOf (twistedE6RootGroup K (unitaryInvolution K ℓ f)) ∧
        (∀ a ∈ (twE6Phi hK hf hζ hσζ P hP (by norm_num) hc hct φ).range, ∀ k : ℕ, k < 3 →
          (∀ j ∈ (leviJ K ℓ f).subgroupOf (twistedE6RootGroup K (unitaryInvolution K ℓ f)),
            j * (a * (fieldActor (t := TwistTag.E6) (unitaryInvolution K ℓ f) ε ^ k) j * a⁻¹)⁻¹ ∈
              GLAPPrimeCoreOf 3
                ((leviJ K ℓ f).subgroupOf (twistedE6RootGroup K (unitaryInvolution K ℓ f)))) →
            k = 0 ∧ a ∈ Subgroup.zpowers (twE6R0 c hct)) ∧
        GLAPLayer 3 ((leviJ K ℓ f).subgroupOf (twistedE6RootGroup K (unitaryInvolution K ℓ f)) ⊓
          fixSubgroup (fieldActor (t := TwistTag.E6) (unitaryInvolution K ℓ f) ε)) ≠ ⊥ ∧
        twE6T K ℓ f ≠ 1 ∧ twE6T K ℓ f ^ 2 = 1 ∧
        (leviJ K ℓ f).subgroupOf (twistedE6RootGroup K (unitaryInvolution K ℓ f)) ≤
          Subgroup.centralizer
            ({twE6T K ℓ f} : Set ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f))) ∧
        (twE6Phi hK hf hζ hσζ P hP (by norm_num) hc hct φ).range ≤
          Subgroup.centralizer
            ({twE6T K ℓ f} : Set ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f))) ∧
        fieldActor (t := TwistTag.E6) (unitaryInvolution K ℓ f) ε (twE6T K ℓ f) = twE6T K ℓ f := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  obtain ⟨d, rfl⟩ := exists_eq_mul_of_orderOf hK hp hp2 hε
  have hQ1 : 1 ≤ ℓ ^ (3 * d) := Nat.one_le_pow _ _ (Fact.out : ℓ.Prime).pos
  have hpQ2 := three_dvd_sq_sub_one_of_dvd_add_one hQ1 h3
  have hF := card_fixSubfield_of_orderOf hp hK hε
  haveI : Finite (fixSubfield ε) := Subtype.finite
  have h3F : 3 ∣ ℓ ^ d + 1 := by
    refine dvd_add_one_of_dvd_pow_add_one hp ?_
    rw [show (ℓ ^ d) ^ 3 = ℓ ^ (3 * d) by ring]
    exact h3
  have hpF := three_dvd_sq_sub_one_of_dvd_add_one (Nat.one_le_pow _ _ (Fact.out : ℓ.Prime).pos) h3F
  obtain ⟨ζ, hζ, hσζ, hεζ⟩ := exists_unitaryInvolution_eq_neg_fixed hp hp2 hK hε
  obtain ⟨P, hP, hPε⟩ := exists_wittMatrix_fixed hp hp2 hK hε 6
  obtain ⟨c, hc, -⟩ := exists_orderOf_eq_fixSubfield hp hε (by rw [hK]; exact hpQ2)
  have hcs := add_inv_eq_neg_one_of_orderOf_three hc
  have hct : unitaryInvolution K ℓ (3 * d) ((c : K) + ((c⁻¹ : Kˣ) : K)) =
      (c : K) + ((c⁻¹ : Kˣ) : K) := by
    rw [hcs, map_neg, map_one]
  have hεct : ε ((c : K) + ((c⁻¹ : Kˣ) : K)) = (c : K) + ((c⁻¹ : Kˣ) : K) := by
    rw [hcs, map_neg, map_one]
  obtain ⟨c₀, hc₀⟩ := CFSG.StandardType.TableBSymp.exists_orderOf_eq_of_dvd (K := fixSubfield ε)
    (p := 3) (by rw [hF]; exact hpF)
  set S₀ := suidSub hp hp2 hK hε 6 with hS₀
  set ι := leviSU hK hf hζ hσζ P hP with hι
  set φ := S₀.comp (diagThreeHom c₀ hc₀ h3F) with hφ
  have hιφ : Function.Injective (ι.comp φ) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨μ, hμ⟩ := exists_smul_of_leviSU_eq_one hK hf hζ hσζ P hP hx
    have e44 := congrFun (congrFun hμ 4) 4
    rw [hφ, MonoidHom.comp_apply, hS₀, coe_suidSub, Matrix.map_apply, coe_diagThreeHom,
      diagonal_apply_eq] at e44
    have h4 := diagThreeHom_apply_four c₀ hc₀ x
    have h4' : ((diagTuple c₀ hc₀ (snocOneHom (Multiplicative (ZMod 3)) 4 x) 4 :
        fixSubfield ε) : K) = 1 := by
      rw [h4]
      rfl
    rw [Subfield.coe_subtype, h4'] at e44
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at e44
    have h1 : φ x = 1 := by
      apply Subtype.ext
      apply Units.ext
      rw [hμ, ← e44, one_smul]
      rfl
    have h2 : diagThreeHom c₀ hc₀ h3F x = 1 :=
      suidSub_injective hp hp2 hK hε 6 (h1.trans (map_one _).symm)
    exact diagThreeHom_injective c₀ hc₀ h3F (h2.trans (map_one _).symm)
  have hφε : ∀ x, suidMap (unitaryInvolution K ℓ (3 * d)) 6 (ringEquiv_comm_of_finite _ ε)
      (φ x) = φ x := fun x => suidMap_suidSub hp hp2 hK hε _
  have hφy : ∀ x (u : Kˣ) (hu : u ^ (ℓ ^ (3 * d) + 1) = 1),
      φ x * yLam hK u hu = yLam hK u hu * φ x := by
    intro x u hu
    apply Subtype.ext
    apply Units.ext
    show (((S₀ (diagThreeHom c₀ hc₀ h3F x) : Su K ℓ (3 * d) 6) : GL (Fin 6) K) :
        Matrix (Fin 6) (Fin 6) K) * diagonal (fun i => (yTuple u i : K)) =
      diagonal (fun i => (yTuple u i : K)) *
        (((S₀ (diagThreeHom c₀ hc₀ h3F x) : Su K ℓ (3 * d) 6) : GL (Fin 6) K) :
          Matrix (Fin 6) (Fin 6) K)
    rw [hS₀, coe_suidSub, coe_diagThreeHom, diagonal_map (map_zero _), diagonal_mul_diagonal,
      diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  obtain ⟨M₂, W₂, hM₂, hMW⟩ := exists_su_two_orderOf_not_commute hF hp hp2 hpF
  set z₀ := pairBlock (K := fixSubfield ε) (ℓ := ℓ) (f := d) blk01 card_blk01 M₂ with hz₀def
  set w₀ := pairBlock (K := fixSubfield ε) (ℓ := ℓ) (f := d) blk01 card_blk01 W₂ with hw₀def
  have hM₂p : M₂ ^ 3 = 1 := hM₂ ▸ pow_orderOf_eq_one M₂
  have hz₀p : S₀ z₀ ^ 3 = 1 := by rw [← map_pow, hz₀def, ← map_pow, hM₂p, map_one, map_one]
  have hzw : ι (S₀ z₀) * ι (S₀ w₀) ≠ ι (S₀ w₀) * ι (S₀ z₀) := by
    intro h
    have h1 := commute_of_leviSU_commute_of_mem_blk01 hK hf hζ hσζ P hP
      (suidSub_mem_coordBlockSU hp hp2 hK hε (pairBlock_mem blk01 card_blk01 M₂))
      (suidSub_mem_coordBlockSU hp hp2 hK hε (pairBlock_mem blk01 card_blk01 W₂)) h
    have h2 : z₀ * w₀ = w₀ * z₀ :=
      suidSub_injective hp hp2 hK hε 6 (by rw [map_mul, map_mul]; exact h1)
    rw [hz₀def, hw₀def, ← map_mul, ← map_mul] at h2
    exact hMW (pairBlock_injective blk01 card_blk01 h2)
  exact ⟨ζ, hζ, hσζ, P, hP, c, hc, hct, φ, hεζ, hPε, hεct, hφε, hιφ,
    modelBGen_twistedE6_spec_of_inj hK hf hζ hσζ P hP hℓ2 hp2 rfl hε hout hεζ hPε hc hct hεct
      (by norm_num : 0 < 4) hιφ hφε hφy (suidSub_fixed hp hp2 hK hε z₀)
      (suidSub_fixed hp hp2 hK hε w₀) hz₀p hzw⟩

theorem modelBGen_twistedE6_three_of_dvd_add_one (hK : Nat.card K = (ℓ ^ f) ^ 2) (hf : 1 ≤ f)
    (hℓ2 : ℓ ≠ 2) (h3 : 3 ∣ ℓ ^ f + 1) {ε : K ≃+* K} (hε : orderOf ε = 3)
    (hout : fieldActor (unitaryInvolution K ℓ f) ε ∉
      (MulAut.conj : ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f)) →*
        MulAut ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f))).range) :
    ModelBGen 3 5 ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f))
      (fieldActor (unitaryInvolution K ℓ f) ε) := by
  obtain ⟨ζ, hζ, hσζ, P, hP, c, hc, hct, φ, -, -, -, -, -, h1, h2, h3', h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17⟩ := modelBGen_twistedE6_three_spec hK hf hℓ2 h3 hε hout
  exact ⟨h1, h2, _, _, _, _, h3', h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩

variable {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}

theorem concA_of_twistedE6_three_of_not_mem_inndiag (hK : Nat.card K = (ℓ ^ f) ^ 2) (hf : 1 ≤ f)
    (hℓ2 : ℓ ≠ 2) (h3 : 3 ∣ ℓ ^ f + 1) (hS : S.Normal) (hcore : GLAPPrimeCore 3 ↥S = ⊥)
    (hZ : Subgroup.center ↥S = ⊥) (hB : IsElemAbelian 3 B)
    (hBC : Nat.card ↥(B ⊓ centModSubgroup 3 S) = 3) (hBle : Nat.card B ≤ 3 ^ (5 + 2))
    {φ : ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f)) →* Ω} (hφ : Function.Injective φ)
    (hφS : φ.range = S) {b : Ω} (hb : b ∈ B)
    {β : MulAut ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f))}
    (hβ : β ∉ twistedE6Inn K (unitaryInvolution K ℓ f) ⊔ twistedE6Diag K (unitaryInvolution K ℓ f))
    (hβφ : ∀ x, φ (β x) = b * φ x * b⁻¹) : S267ConcA 3 S B :=
  concA_of_twistedE6_of_not_mem_inndiag_of_model hK hf Nat.prime_three (by norm_num)
    (by norm_num : 2 ≤ 5) hS hcore hZ hB hBC hBle hφ hφS hb hβ hβφ
    fun _ hε hout => modelBGen_twistedE6_three_of_dvd_add_one hK hf hℓ2 h3 hε hout

end ModelB

end CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.TwE6Outer

end
