module

public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.TauThirteenTypeIStatements
import CFSG.FeitThompson.Local.PCoreLinearAlternativePConfiguration
import CFSG.FeitThompson.Local.TypePInnerActionFaithful
import CFSG.FeitThompson.Foundations.DiagonalDivisorRatioForcesQThree
import CFSG.FeitThompson.Representations.TypePNoFittingInducedWitness
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
open CFSG.FeitThompson.Prep05

def zmodOddRed {a a₀ : ℕ} (h : a₀ ∣ a) :
    Multiplicative (ZMod a) →* Multiplicative (ZMod a₀) :=
  AddMonoidHom.toMultiplicative (ZMod.castHom h (ZMod a₀)).toAddMonoidHom

theorem toAdd_zmodOddRed {a a₀ : ℕ} (h : a₀ ∣ a) (x : Multiplicative (ZMod a)) :
    Multiplicative.toAdd (zmodOddRed h x)
      = ZMod.castHom h (ZMod a₀) (Multiplicative.toAdd x) := (rfl)

theorem pow_two_pow_eq_one_of_zmodOddRed_eq_one {t a₀ : ℕ} (ha₀ : a₀ ≠ 0)
    (h : a₀ ∣ 2 ^ t * a₀) {x : Multiplicative (ZMod (2 ^ t * a₀))}
    (hx : zmodOddRed h x = 1) : x ^ 2 ^ t = 1 := by
  have hne : NeZero (2 ^ t * a₀) := ⟨by positivity⟩
  have hne₀ : NeZero a₀ := ⟨ha₀⟩
  set y : ZMod (2 ^ t * a₀) := Multiplicative.toAdd x with hy
  have h0 : ZMod.castHom h (ZMod a₀) y = 0 := by
    have h1 := congrArg Multiplicative.toAdd hx
    rwa [toAdd_zmodOddRed] at h1
  have hval : a₀ ∣ y.val := by
    have h1 : ((y.val : ℕ) : ZMod a₀) = 0 := by
      rw [ZMod.castHom_apply, ← ZMod.natCast_val] at h0
      exact h0
    exact (ZMod.natCast_eq_zero_iff _ _).1 h1
  obtain ⟨m, hm⟩ := hval
  have hsm : (2 ^ t) • y = 0 := by
    have hyv : y = ((y.val : ℕ) : ZMod (2 ^ t * a₀)) := (ZMod.natCast_rightInverse y).symm
    rw [hyv, nsmul_eq_mul, ← Nat.cast_mul, hm,
      show 2 ^ t * (a₀ * m) = 2 ^ t * a₀ * m by ring]
    simp
  have hfin : Multiplicative.toAdd (x ^ 2 ^ t) = (0 : ZMod (2 ^ t * a₀)) := by
    simpa [hy] using hsm
  exact Multiplicative.toAdd.injective (by simpa using hfin)

theorem dvd_pow_of_odd_of_injective_pi_zmod {n t a₀ u : ℕ} (ha₀ : a₀ ≠ 0) (hu : Odd u)
    {D : Type*} [Group D] (hDu : Nat.card D = u)
    {φ : D →* (Fin n → Multiplicative (ZMod (2 ^ t * a₀)))} (hφ : Function.Injective φ) :
    ∃ ψ : D →* (Fin n → Multiplicative (ZMod a₀)), Function.Injective ψ := by
  have h : a₀ ∣ 2 ^ t * a₀ := dvd_mul_left a₀ (2 ^ t)
  refine ⟨((zmodOddRed h).compLeft (Fin n)).comp φ, ?_⟩
  rw [injective_iff_map_eq_one]
  intro x hx
  have hcoord : ∀ i, (φ x i) ^ 2 ^ t = 1 := by
    intro i
    have h1 : zmodOddRed h (φ x i) = 1 := by
      have := congrFun hx i
      simpa [MonoidHom.compLeft] using this
    exact pow_two_pow_eq_one_of_zmodOddRed_eq_one ha₀ h h1
  have hpow : φ (x ^ 2 ^ t) = 1 := by
    rw [map_pow]
    funext i
    simpa using hcoord i
  have hx2 : x ^ 2 ^ t = 1 := hφ (by rw [hpow, map_one])
  have hdvd2 : orderOf x ∣ 2 ^ t := orderOf_dvd_of_pow_eq_one hx2
  have hdvdu : orderOf x ∣ u := hDu ▸ orderOf_dvd_natCard x
  have hodd : Odd (orderOf x) := hu.of_dvd_nat hdvdu
  have hone : orderOf x = 1 :=
    Nat.Coprime.eq_one_of_dvd ((Nat.coprime_two_right.mpr hodd).pow_right t) hdvd2
  exact orderOf_eq_one_iff.1 hone

noncomputable def mulEquivOfInjectiveOfNatCardEq {D E : Type*} [Group D] [Group E] [Finite E]
    (φ : D →* E) (hφ : Function.Injective φ) (hcard : Nat.card D = Nat.card E) : D ≃* E :=
  MulEquiv.ofBijective φ ((Nat.bijective_iff_injective_and_card φ).2 ⟨hφ, hcard⟩)

theorem nonempty_mulEquiv_prod_zmod_of_injective {A n : ℕ} (hA : A ≠ 0) (hn : n = 2) {D : Type*}
    [Group D] (hDcard : Nat.card D = A ^ 2)
    {ψ : D →* (Fin n → Multiplicative (ZMod A))} (hψ : Function.Injective ψ) :
    Nonempty (D ≃* (Multiplicative (ZMod A) × Multiplicative (ZMod A))) := by
  subst hn
  have hne : NeZero A := ⟨hA⟩
  have hcard : Nat.card (Fin 2 → Multiplicative (ZMod A)) = A ^ 2 := by
    simp [Nat.card_eq_fintype_card, pow_succ]
  have hfin : Finite (Fin 2 → Multiplicative (ZMod A)) := inferInstance
  have hequiv : D ≃* (Fin 2 → Multiplicative (ZMod A)) :=
    mulEquivOfInjectiveOfNatCardEq ψ hψ (by rw [hDcard, hcard])
  refine ⟨hequiv.trans ?_⟩
  exact { toFun := fun f => (f 0, f 1)
          invFun := fun p => fun i => if i = 0 then p.1 else p.2
          left_inv := by
            intro f
            funext i
            fin_cases i <;> simp
          right_inv := by intro p; simp
          map_mul' := by intro f g; rfl }

end

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

public section

open Subgroup CFSG.FeitThompson
open CFSG.FeitThompson.Prep05

attribute [local instance] CFSG.FeitThompson.subgroupFintype

universe u v

theorem FNI_type_p_reducible_inner_action_order
    (h₁ : Statements.FCH_type_p_action_kernel_ratio.{u})
    (h₂ : Statements.FNI_type_p_elementary_core_structure.{u}) :
    Statements.FNI_type_p_reducible_inner_action_order.{u, v} := by
  intro G _ _ hG M U W₁ W₂ hM hc p q hp hq V _ _ e ρ hρ hW
  let _ : Fintype G := Fintype.ofFinite G
  obtain ⟨-, hpp, hqp, hop, hoq, hpq, hUne, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, -, -⟩ :=
    h₂ G hG M U W₁ W₂ hM hc p q hp hq
  have hA : CFSG.FeitThompson.Prep03.IsAmbient G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  obtain ⟨hCbot, -⟩ := FNI_type_p_inner_action_faithful.{u} h₁ h₂ G hG M U W₁ W₂ hM hc
  have hu : (centralizerIn U (hallCoreOf M)).relIndex U = Nat.card ↥U := by
    rw [hCbot, Subgroup.relIndex_bot_left]
  have hcard1 : Nat.card ↥(centralizerIn U (hallCoreOf M)) = 1 := by
    rw [hCbot]; exact Subgroup.card_bot
  set uu : ℕ := Nat.card ↥U with huudef
  have huodd : Odd uu := Odd.of_dvd_nat hG.odd_natCard U.card_subgroup_dvd_card
  have hu1 : 1 < uu := (Subgroup.one_lt_card_iff_ne_bot U).2 hUne
  have hwitness : ∃ ψ ∈ Irr ↥(CFSG.FeitThompson.fittingRaw ↥M), ψ 1 = 1 ∧
      indClassFun (CFSG.FeitThompson.fittingRaw ↥M) ψ ∈ Irr ↥M ∧
      ¬ ∀ x : ↥M, (x : G) ∈ CFSG.FeitThompson.Prep03.hallCoreIn M →
        indClassFun (CFSG.FeitThompson.fittingRaw ↥M) ψ x =
          indClassFun (CFSG.FeitThompson.fittingRaw ↥M) ψ 1 := by
    by_contra hno
    obtain ⟨-, -, -, -, -, -, -, -, -, hmin, -⟩ :=
      FCH_type_p_no_fitting_induced_witness.{u} h₂ G hA M U W₁ W₂ ⟨hA, hM, hc⟩ p q
        ((CFSG.FeitThompson.Prep03.cent U
          (CFSG.FeitThompson.Prep03.hallCoreIn M : Set G)).relIndex U)
        hp hq rfl hno
    obtain ⟨W, hWbot, hWtop, hWinv⟩ := hW
    have hHM : M ≤ normalizer ((hallCoreOf M : Subgroup G) : Set G) :=
      le_normalizer_map_subtype_hallCore M
    set N : Subgroup G := subgroupOfSubmodule e W with hNdef
    have hNle : N ≤ CFSG.FeitThompson.Prep03.hallCoreIn M :=
      subgroupOfSubmodule_le e W
    have hNbot : N ≠ ⊥ := fun hcon => hWbot (subgroupOfSubmodule_eq_bot_iff.1 hcon)
    have hNtop : N ≠ CFSG.FeitThompson.Prep03.hallCoreIn M := fun hcon =>
      hWtop (subgroupOfSubmodule_eq_top_iff.1 hcon)
    have hHab : IsMulCommutative ↥(hallCoreOf M) :=
      ⟨⟨fun x y => e.injective (by rw [map_mul, map_mul, mul_comm])⟩⟩
    have habN : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x := by
      intro x hx y hy
      have hxH : x ∈ hallCoreOf M := hNle hx
      have hyH : y ∈ hallCoreOf M := hNle hy
      exact congrArg Subtype.val (mul_comm' (⟨x, hxH⟩ : ↥(hallCoreOf M)) ⟨y, hyH⟩)
    have hexpN : ∀ x ∈ N, x ^ p = 1 := by
      intro x hx
      have hxH : x ∈ hallCoreOf M := hNle hx
      have hsm : (p : ℕ) • Multiplicative.toAdd (e ⟨x, hxH⟩) = 0 := by
        have hchar : (p : ZMod p) = 0 := ZMod.natCast_self p
        rw [← Nat.cast_smul_eq_nsmul (ZMod p), hchar, zero_smul]
      have : (⟨x, hxH⟩ : ↥(hallCoreOf M)) ^ p = 1 := by
        refine e.injective ?_
        rw [map_pow, map_one]
        exact Multiplicative.toAdd.injective (by simpa using hsm)
      exact congrArg Subtype.val this
    have hUM : U ≤ M := hc.le_M_E
    have hconj : ∀ g ∈ U, CFSG.FeitThompson.Prep03.conjSub N g = N := by
      intro g hg
      have hinvrange : ∀ x ∈ U, ∀ z ∈ N, x * z * x⁻¹ ∈ N := by
        intro x hx z hz
        obtain ⟨hzH, hzW⟩ := mem_subgroupOfSubmodule.1 hz
        refine mem_subgroupOfSubmodule.2 ⟨conj_mem_of_le_normalizer hHM (hUM hx) hzH, ?_⟩
        rw [← toAdd_e_conj hρ hHM ⟨x, hUM hx⟩ ⟨z, hzH⟩]
        exact hWinv (ρ ⟨x, hUM hx⟩)
          (Subgroup.mem_map.2 ⟨⟨x, hUM hx⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩) _ hzW
      refine le_antisymm ?_ ?_
      · rintro y ⟨z, hz, rfl⟩
        have h1 := hinvrange g⁻¹ (U.inv_mem hg) z hz
        simpa [CFSG.FeitThompson.Prep03.conjSub, MulAut.conj] using h1
      · intro y hy
        refine ⟨g * y * g⁻¹, hinvrange g hg y hy, ?_⟩
        simp [MulAut.conj]
        group
    rcases hmin N hNle habN hexpN hconj with h | h
    · exact hNbot h
    · exact hNtop h
  obtain ⟨ψ, hψIrr, hψ1, hψirr2, hψker⟩ := hwitness
  have hratio := h₁ G hA M U W₁ W₂ ⟨hA, hM, hc⟩ p q uu 1 hp hq
    (by rw [← hu]; rfl) (by rw [← hcard1]; rfl)
    (1 - 1 / ((q : ℚ) - 1) - ((q : ℚ) - 1) / (q : ℚ) ^ p
      + 1 / (((q : ℚ) - 1) * (q : ℚ) ^ p)) rfl
    ⟨ψ, hψIrr, hψ1, hψirr2, hψker⟩
  obtain ⟨-, -, hDcard, hDodd, -, -, -, -, -, hxor, -⟩ :=
    FNI_type_p_core_linear_alternative.{u, v} h₂ G hG M U W₁ W₂ hM hc p q
      ((centralizerIn U (hallCoreOf M)).relIndex U) ((p ^ q - 1) / (p - 1)) hp hq rfl rfl
      V e ρ hρ _ _ rfl rfl
  obtain ⟨a, ha1, hadvd, φ, hφ⟩ : ∃ a : ℕ, 1 < a ∧ a ∣ p - 1 ∧
      ∃ φ : ↥((U.subgroupOf M).map ρ) →* (Fin (q - 1) → Multiplicative (ZMod a)),
        Function.Injective φ := by
    rcases hxor with ⟨⟨-, L, -, -, -, -, -, hemb, -⟩, -⟩ | ⟨⟨hirr, -⟩, -⟩
    · exact hemb
    ·
      exfalso
      obtain ⟨W, hWbot, hWtop, hWinv⟩ := hW
      rcases hirr W hWinv with h | h
      · exact hWbot h
      · exact hWtop h
  have hDcardU : Nat.card ↥((U.subgroupOf M).map ρ) = uu := by rw [hDcard, hu]
  obtain ⟨t, a₀, ha₀odd, hasplit⟩ := Nat.exists_eq_two_pow_mul_odd (n := a) (by omega)
  have ha₀ne : a₀ ≠ 0 := by rintro rfl; simp at ha₀odd
  have ha₀dvd : a₀ ∣ a := hasplit ▸ dvd_mul_left a₀ (2 ^ t)
  obtain ⟨χ, hχ⟩ : ∃ χ : ↥((U.subgroupOf M).map ρ) →*
      (Fin (q - 1) → Multiplicative (ZMod a₀)), Function.Injective χ := by
    subst hasplit
    exact dvd_pow_of_odd_of_injective_pi_zmod ha₀ne hDodd hDcard hφ
  have hudvd : uu ∣ a₀ ^ (q - 1) := by
    have hne₀ : NeZero a₀ := ⟨ha₀ne⟩
    have h1 : Nat.card ↥((U.subgroupOf M).map ρ)
        ∣ Nat.card (Fin (q - 1) → Multiplicative (ZMod a₀)) :=
      Subgroup.card_dvd_of_injective χ hχ
    rw [hDcardU, show Nat.card (Fin (q - 1) → Multiplicative (ZMod a₀)) = a₀ ^ (q - 1) by
      simp [Nat.card_eq_fintype_card]] at h1
    exact h1
  have hpA : p = 2 * ((p - 1) / 2) + 1 := by
    have h := hpp.two_le
    have hodd : p % 2 = 1 := Nat.odd_iff.mp hop
    omega
  have ha₀A : a₀ ∣ (p - 1) / 2 := by
    have hdvd : a₀ ∣ p - 1 := ha₀dvd.trans hadvd
    have h2 : p - 1 = 2 * ((p - 1) / 2) := by omega
    rw [h2] at hdvd
    exact (Nat.Coprime.dvd_of_dvd_mul_left (Nat.coprime_two_right.mpr ha₀odd) hdvd)
  have huA : uu ∣ ((p - 1) / 2) ^ (q - 1) :=
    hudvd.trans (pow_dvd_pow_of_dvd ha₀A _)
  have hratioR : kernelRatioCoeff p q * (p : ℝ) ^ (q - 1) / q < uu := by
    have h := (Rat.cast_lt (K := ℝ)).2 hratio
    push_cast at h
    rw [div_one] at h
    rw [kernelRatioCoeff_eq]
    exact h
  obtain ⟨hq3, hUsq⟩ := eq_three_and_eq_sq_of_ratio_lt hpp hqp
    (by rintro rfl; simp [Nat.odd_iff] at hop) (by rintro rfl; simp [Nat.odd_iff] at hoq)
    hpq huA hratioR
  refine ⟨hq3, fun A hAdef => ?_⟩
  subst hAdef
  have hUcard : Nat.card ↥U = ((p - 1) / 2) ^ 2 := hUsq
  have hAodd : Odd ((p - 1) / 2) := by
    rcases Nat.even_or_odd ((p - 1) / 2) with hev | hod
    · exfalso
      have h2 : 2 ∣ ((p - 1) / 2) ^ 2 := dvd_pow (hev.two_dvd) (by norm_num)
      rw [← hUcard] at h2
      rw [Nat.odd_iff] at huodd
      omega
    · exact hod
  have hA1 : 1 < (p - 1) / 2 := by
    by_contra hcon
    have h1 : (p - 1) / 2 ≤ 1 := by omega
    have h2 : ((p - 1) / 2) ^ 2 ≤ 1 := by
      calc ((p - 1) / 2) ^ 2 ≤ 1 ^ 2 := Nat.pow_le_pow_left h1 2
        _ = 1 := by norm_num
    rw [← hUcard] at h2
    omega
  have hApos : 0 < (p - 1) / 2 := by omega
  have ha₀eq : a₀ = (p - 1) / 2 := by
    have hq3' : q - 1 = 2 := by omega
    rw [hq3'] at hudvd
    have h1 : ((p - 1) / 2) ^ 2 ≤ a₀ ^ 2 := by
      rw [← hUcard]
      exact Nat.le_of_dvd (by positivity) hudvd
    have h2 : a₀ ≤ (p - 1) / 2 := Nat.le_of_dvd hApos ha₀A
    have h3 : a₀ ^ 2 ≤ ((p - 1) / 2) ^ 2 := Nat.pow_le_pow_left h2 2
    have h4 : a₀ ^ 2 = ((p - 1) / 2) ^ 2 := le_antisymm h3 h1
    nlinarith [h4, h2]
  subst ha₀eq
  have hq3' : q - 1 = 2 := by omega
  have hiso : Nonempty (↥U ≃*
      (Multiplicative (ZMod ((p - 1) / 2)) × Multiplicative (ZMod ((p - 1) / 2)))) := by
    have hUM : U ≤ M := hc.le_M_E
    have hHM : M ≤ normalizer ((hallCoreOf M : Subgroup G) : Set G) :=
      le_normalizer_map_subtype_hallCore M
    set ρU : ↥U →* (V ≃ₗ[ZMod p] V) := ρ.comp (Subgroup.inclusion hUM) with hρU
    have hρUinj : Function.Injective ρU := by
      rw [injective_iff_map_eq_one]
      intro x hx
      have h1 : ρ (Subgroup.inclusion hUM x) = 1 := hx
      have h2 : ((Subgroup.inclusion hUM x : ↥M) : G) ∈
          centralizer ((hallCoreOf M : Subgroup G) : Set G) :=
        (rho_eq_one_iff hρ hHM (Subgroup.inclusion hUM x)).1 h1
      have hxG : ((Subgroup.inclusion hUM x : ↥M) : G) = (x : G) := rfl
      rw [hxG] at h2
      have h3 : (x : G) ∈ centralizerIn U (hallCoreOf M) := Subgroup.mem_inf.2 ⟨x.2, h2⟩
      rw [hCbot, Subgroup.mem_bot] at h3
      exact Subtype.ext h3
    have hmemrange : ∀ x : ↥U, ρU x ∈ (U.subgroupOf M).map ρ := fun x =>
      Subgroup.mem_map.2 ⟨Subgroup.inclusion hUM x, Subgroup.mem_subgroupOf.2 x.2, rfl⟩
    set σ : ↥U →* ↥((U.subgroupOf M).map ρ) := ρU.codRestrict _ hmemrange with hσ
    have hσinj : Function.Injective σ := fun x y hxy =>
      hρUinj (congrArg Subtype.val hxy)
    have hcomp : Function.Injective (χ.comp σ) := hχ.comp hσinj
    exact nonempty_mulEquiv_prod_zmod_of_injective (ψ := χ.comp σ) (by omega) hq3' hUcard hcomp
  exact ⟨hUcard, hiso, hApos, hAodd, hA1⟩

end

end CFSG.FeitThompson.Proofs
