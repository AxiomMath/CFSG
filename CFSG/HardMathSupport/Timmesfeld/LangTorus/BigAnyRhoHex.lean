module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyRho
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyPBigSub
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyHex

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LieType.AlgebraicGroups

set_option linter.unusedSectionVars false


section RhoHex

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)
  (h : S.HexStep) (hτ : SimplyLacedTag τ)

include h hτ

theorem hexR_defect {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    ∃ v₁ v₂ : Lˣ,
      (rootSL2 τ L (S.ρ γ) (nSL 1) * rootSL2 τ L γ (nSL 1))⁻¹ *
        S.D.step (rootSL2 τ L (S.ρ γ) (nSL 1) * rootSL2 τ L γ (nSL 1)) =
      Hel (-γ) v₁ * Hel (S.ρ γ) v₂ := by
  have hr1 : IsRoot τ (S.ρ γ) := (S.frob.isRoot_iff γ).2 hγ
  have hr2 : IsRoot τ (S.ρ (S.ρ γ)) := (S.frob.isRoot_iff _).2 hr1
  have hr2eq := h.rel6 γ hγ
  have h01 := hexR_form01 S h hτ hγ
  obtain ⟨a1, ha1⟩ := h.nsl _ hr1
  obtain ⟨a0, ha0⟩ := h.nsl _ hγ
  obtain ⟨-, hmon, hmaps⟩ := rootWeylOne_spec (K := L) hr1
  have hrefl : rootReflection (S.ρ γ) • γ = -(S.ρ (S.ρ γ)) := by
    rw [rootReflection_smul_sl hτ hr1, iform_comm, h01, one_smul, hr2eq]
    abel
  obtain ⟨s, hs⟩ := conj_rootSL2_nSL hmon hmaps hγ hrefl
  obtain ⟨a, ha⟩ := rootSL2_neg_nSL (L := L) hr2
  have hconj : rootSL2 τ L (S.ρ γ) (nSL 1) * rootSL2 τ L γ (nSL 1) =
      rootSL2 τ L (S.ρ (S.ρ γ)) (nSL (-(a * (s * 1))⁻¹)) * rootSL2 τ L (S.ρ γ) (nSL 1) := by
    have h' : rootSL2 τ L (S.ρ γ) (nSL 1) * rootSL2 τ L γ (nSL 1) *
        (rootSL2 τ L (S.ρ γ) (nSL 1))⁻¹ =
          rootSL2 τ L (-(S.ρ (S.ρ γ))) (nSL (s * 1)) := hs 1
    rw [ha] at h'
    exact mul_inv_eq_iff_eq_mul.1 h'
  have hF : S.D.step (rootSL2 τ L (S.ρ γ) (nSL 1) * rootSL2 τ L γ (nSL 1)) =
      rootSL2 τ L (S.ρ (S.ρ γ)) (nSL a1) * rootSL2 τ L (S.ρ γ) (nSL a0) := by
    rw [map_mul, ha1 1, ha0 1, one_pow, mul_one, mul_one]
  have hH := rootSL2_nSL_inv_mul hτ hr2 (-(a * (s * 1))⁻¹) a1
  have hH1 := rootSL2_nSL_inv_mul (L := L) hτ hr1 1 a0
  have hform : iform (S.ρ γ) (S.ρ (S.ρ γ)) = 1 := by
    rw [hr2eq, iform_sub_right, iform_comm (S.ρ γ) γ, h01, iform_self_eq_two hτ hr1]
    norm_num
  have hrefl2 : (rootReflection (S.ρ γ))⁻¹ • (S.ρ (S.ρ γ)) = -γ := by
    rw [rootReflection_inv hr1, rootReflection_smul_sl hτ hr1, hform, one_smul, hr2eq]
    abel
  have hconjH : ∀ v : Lˣ, (rootSL2 τ L (S.ρ γ) (nSL 1))⁻¹ * Hel (S.ρ (S.ρ γ)) v *
      ((rootSL2 τ L (S.ρ γ) (nSL 1))⁻¹)⁻¹ = Hel (-γ) v := fun v => by
    have := conj_Hel (L := L) (n := (rootSL2 τ L (S.ρ γ) (nSL 1))⁻¹) (inv_mem hmon) hmaps.inv
      (S.ρ (S.ρ γ)) v
    rw [this, hrefl2]
  refine ⟨(-(a * (s * 1))⁻¹) * a1⁻¹, 1 * a0⁻¹, ?_⟩
  rw [hF, hconj, ← hconjH ((-(a * (s * 1))⁻¹) * a1⁻¹), ← hH, ← hH1]
  group

theorem hexR_nu {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    ∃ ν : ModGL τ L, ν ∈ rootSpan τ L (hexROrbit S γ) ∧ S.D.step ν = ν ∧
      ∀ (x : Fin τ.rank → ℤ) (u : Lˣ),
        ν * Hel x u * ν⁻¹ = Hel ((rootReflection (S.ρ γ) * rootReflection γ) • x) u := by
  have hr1 : IsRoot τ (S.ρ γ) := (S.frob.isRoot_iff γ).2 hγ
  obtain ⟨v₁, v₂, hdef⟩ := hexR_defect S h hτ hγ
  obtain ⟨hsup1, hmon1, hmaps1⟩ := rootWeylOne_spec (K := L) hr1
  obtain ⟨hsup0, hmon0, hmaps0⟩ := rootWeylOne_spec (K := L) hγ
  have hshift : ∀ j : ℕ, (S.ρ : (Fin τ.rank → ℤ) → _)^[j] (S.ρ γ) =
      (S.ρ : (Fin τ.rank → ℤ) → _)^[j + 1] γ := fun j => by
    rw [Function.iterate_succ_apply]
  have hΘ1 : ∀ j : ℕ, (S.ρ : (Fin τ.rank → ℤ) → _)^[j] (S.ρ γ) ∈ hexROrbit S γ ∧
      -((S.ρ : (Fin τ.rank → ℤ) → _)^[j] (S.ρ γ)) ∈ hexROrbit S γ := fun j => by
    rw [hshift]
    exact ⟨⟨j + 1, rfl⟩, hexR_neg_mem S h hγ (j + 1)⟩
  have hΘ0 : ∀ j : ℕ, (S.ρ : (Fin τ.rank → ℤ) → _)^[j] (-γ) ∈ hexROrbit S γ ∧
      -((S.ρ : (Fin τ.rank → ℤ) → _)^[j] (-γ)) ∈ hexROrbit S γ := fun j => by
    rw [hexR_iter_neg, neg_neg]
    exact ⟨hexR_neg_mem S h hγ j, ⟨j, rfl⟩⟩
  have h6neg : (S.ρ : (Fin τ.rank → ℤ) → _)^[6] (-γ) = -γ := by
    rw [hexR_iter_neg, hexR_iter_six S h hγ]
  obtain ⟨b₁, b₁', hF₁, hb₁, hm₁⟩ := hexR_lang S h hτ (IsRoot.neg hγ) (N := 6) (by norm_num)
    h6neg v₁ hΘ0
  obtain ⟨b₂, b₂', hF₂, hb₂, hm₂⟩ := hexR_lang S h hτ hr1 (N := 6) (by norm_num)
    (hexR_iter_six S h hr1) v₂ hΘ1
  set N1 : ModGL τ L := rootSL2 τ L (S.ρ γ) (nSL 1) with hN1
  set N0 : ModGL τ L := rootSL2 τ L γ (nSL 1) with hN0
  set s : ModGL τ L := rootDiagUnit τ (b₁ * b₂) with hs
  have hFs : S.D.step s = rootDiagUnit τ (b₁' * b₂') := by
    rw [hs, rootDiagUnit_mul, map_mul, hF₁, hF₂, rootDiagUnit_mul]
  have ht : Hel (-γ) v₁ * Hel (S.ρ γ) v₂ = s * (S.D.step s)⁻¹ := by
    unfold Hel
    rw [hFs, hs, rootDiagUnit_inv, ← rootDiagUnit_mul, ← rootDiagUnit_mul,
      ← hb₁, ← hb₂, mul_inv, mul_mul_mul_comm]
  have hneg1 : -(S.ρ γ) ∈ hexROrbit S γ := by
    have := hexR_neg_mem S h hγ 1
    simpa using this
  have hneg0 : -γ ∈ hexROrbit S γ := by
    have := hexR_neg_mem S h hγ 0
    simpa using this
  have hN1m : N1 ∈ rootSpan τ L (hexROrbit S γ) := by
    have hsub : ({S.ρ γ, -(S.ρ γ)} : Set (Fin τ.rank → ℤ)) ⊆ hexROrbit S γ := by
      rintro x (rfl | rfl)
      · exact ⟨1, by simp⟩
      · exact hneg1
    exact rootSpan_mono hsub (rootSL2_mem_rootSpan_pair hr1 _)
  have hN0m : N0 ∈ rootSpan τ L (hexROrbit S γ) := by
    have hsub : ({γ, -γ} : Set (Fin τ.rank → ℤ)) ⊆ hexROrbit S γ := by
      rintro x (rfl | rfl)
      · exact ⟨0, by simp⟩
      · exact hneg0
    exact rootSpan_mono hsub (rootSL2_mem_rootSpan_pair hγ _)
  have hsm : s ∈ rootSpan τ L (hexROrbit S γ) := by
    rw [hs, rootDiagUnit_mul]
    exact mul_mem hm₁ hm₂
  refine ⟨N1 * N0 * s, mul_mem (mul_mem hN1m hN0m) hsm, ?_, ?_⟩
  · rw [map_mul, inv_mul_eq_iff_eq_mul.1 hdef, ht]
    group
  · intro x u
    have hcomm : s * Hel x u = Hel x u * s := by
      unfold Hel
      rw [hs, ← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]
    have hconj := conj_Hel (L := L) (n := N1 * N0) (mul_mem hmon1 hmon0) (hmaps1.mul hmaps0) x u
    rw [← hconj]
    calc N1 * N0 * s * Hel x u * (N1 * N0 * s)⁻¹
        = N1 * N0 * (s * Hel x u) * s⁻¹ * (N1 * N0)⁻¹ := by group
      _ = N1 * N0 * Hel x u * (N1 * N0)⁻¹ := by rw [hcomm]; group

end RhoHex


section RhoY

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)

@[expose] noncomputable def hexRY (q : ℕ) (γ : Fin τ.rank → ℤ) (ω : Lˣ) : Fin τ.rank → Lˣ :=
  Hchar γ ω * Hchar (S.ρ γ) (ω ^ q) * Hchar (S.ρ (S.ρ γ)) (ω ^ q ^ 2)

theorem hexRY_pow (q p : ℕ) (γ : Fin τ.rank → ℤ) (ω : Lˣ) (hω : ω ^ p = 1) :
    (rootDiagUnit τ (hexRY S q γ ω)) ^ p = 1 := by
  rw [rootDiagUnit_pow, ← rootDiagUnit_one (τ := τ) (K := L)]
  congr 1
  unfold hexRY
  have h1 : ∀ k : ℕ, (ω ^ k) ^ p = 1 := fun k => by
    rw [← pow_mul, mul_comm, pow_mul, hω, one_pow]
  rw [mul_pow, mul_pow, Hchar_pow_nat, Hchar_pow_nat, Hchar_pow_nat, hω, h1, h1]
  simp [Hchar_one']


section RhoYH

variable (h : S.HexStep) (hτ : SimplyLacedTag τ)

include h hτ

theorem hexRY_step {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (ω : Lˣ)
    (hω : ω ^ (S.D.q ^ 3 + 1) = 1) :
    S.D.step (rootDiagUnit τ (hexRY S S.D.q γ ω)) = rootDiagUnit τ (hexRY S S.D.q γ ω) := by
  have hr1 : IsRoot τ (S.ρ γ) := (S.frob.isRoot_iff γ).2 hγ
  have hr2 : IsRoot τ (S.ρ (S.ρ γ)) := (S.frob.isRoot_iff _).2 hr1
  have hst : ∀ (x : Fin τ.rank → ℤ) (u : Lˣ), IsRoot τ x →
      S.D.step (rootDiagUnit τ (Hchar x u)) =
        rootDiagUnit τ (Hchar (S.ρ x) (u ^ S.D.q)) :=
    fun x u hx => h.hel x hx u
  have h3 : S.ρ (S.ρ (S.ρ γ)) = -γ := hexR_rho3 S h hγ
  have hω3 : (ω ^ S.D.q ^ 2) ^ S.D.q = ω⁻¹ := by
    rw [← pow_mul, ← pow_succ]
    have : ω ^ S.D.q ^ 3 * ω = 1 := by rw [← pow_succ]; exact hω
    exact eq_inv_of_mul_eq_one_left this
  unfold hexRY
  rw [rootDiagUnit_mul, rootDiagUnit_mul, map_mul, map_mul, hst _ _ hγ, hst _ _ hr1,
    hst _ _ hr2, h3, hω3, Hchar_neg, inv_inv, ← pow_mul]
  rw [show S.D.q * S.D.q = S.D.q ^ 2 from (sq _).symm, ← rootDiagUnit_mul, ← rootDiagUnit_mul,
    ← rootDiagUnit_mul, ← rootDiagUnit_mul]
  congr 1
  ac_rfl

theorem hexRY_ne_one (q p : ℕ) (hp : p.Prime)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (ω : Lˣ) (hω : ω ^ p = 1) (hω1 : ω ≠ 1)
    (hE : ¬ (p : ℤ) ∣ 2 + (q : ℤ) - (q : ℤ) ^ 2) : rootDiagUnit τ (hexRY S q γ ω) ≠ 1 := by
  intro hy
  have hY : hexRY S q γ ω = 1 := by
    have : rootDiagUnit τ (hexRY S q γ ω) = rootDiagUnit τ (1 : Fin τ.rank → Lˣ) := by
      rw [hy, rootDiagUnit_one]
    exact CFSG.LieType.Chevalley.rootDiagUnit_injective this
  have hc : rootChar (hexRY S q γ ω) γ = 1 := by rw [hY, rootChar_one']
  have hr1 : IsRoot τ (S.ρ γ) := (S.frob.isRoot_iff γ).2 hγ
  have h01 := hexR_form01 S h hτ hγ
  have hf1 : iform (S.ρ γ) γ = 1 := by rw [iform_comm]; exact h01
  have hf2 : iform (S.ρ (S.ρ γ)) γ = -1 := by
    rw [h.rel6 γ hγ, iform_sub_left, hf1, iform_self_eq_two hτ hγ]
    norm_num
  unfold hexRY at hc
  rw [rootChar_mul_tuple, rootChar_mul_tuple, rootChar_Hchar, rootChar_Hchar, rootChar_Hchar,
    iform_self_eq_two hτ hγ, hf1, hf2] at hc
  have hz : ω ^ ((2 : ℤ) + q - (q : ℤ) ^ 2) = 1 := by
    rw [← hc, zpow_sub, zpow_add, zpow_one, zpow_neg_one, ← Nat.cast_pow, zpow_natCast,
      zpow_natCast]
  have : Fact p.Prime := ⟨hp⟩
  have hord : orderOf ω = p := orderOf_eq_prime hω hω1
  exact hE (hord ▸ orderOf_dvd_iff_zpow_eq_one.2 hz)


theorem hexRY_conj (q p : ℕ) (hp : 1 ≤ p)
    (hq3 : (p : ℤ) ∣ (q : ℤ) ^ 3 + 1) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (ω : Lˣ)
    (hω : ω ^ p = 1) {ν : ModGL τ L}
    (hν : ∀ (x : Fin τ.rank → ℤ) (u : Lˣ),
      ν * Hel x u * ν⁻¹ = Hel ((rootReflection (S.ρ γ) * rootReflection γ) • x) u) :
    ν * rootDiagUnit τ (hexRY S q γ ω) * ν⁻¹ =
      (rootDiagUnit τ (hexRY S q γ ω)) ^ ((p - 1) * q) := by
  have hr1 : IsRoot τ (S.ρ γ) := (S.frob.isRoot_iff γ).2 hγ
  have h01 := hexR_form01 S h hτ hγ
  have hr2eq := h.rel6 γ hγ
  have hform : iform (S.ρ γ) (S.ρ (S.ρ γ)) = 1 := by
    rw [hr2eq, iform_sub_right, iform_comm (S.ρ γ) γ, h01, iform_self_eq_two hτ hr1]
    norm_num
  have hrefl1 : rootReflection (S.ρ γ) • γ = -(S.ρ (S.ρ γ)) := by
    rw [rootReflection_smul_sl hτ hr1, iform_comm, h01, one_smul, hr2eq]
    abel
  have hrefl2 : rootReflection (S.ρ γ) • (S.ρ (S.ρ γ)) = -γ := by
    rw [rootReflection_smul_sl hτ hr1, hform, one_smul, hr2eq]
    abel
  have hc0 : (rootReflection (S.ρ γ) * rootReflection γ) • γ = S.ρ (S.ρ γ) := by
    rw [mul_smul, rootReflection_smul_self hγ, smul_neg, hrefl1, neg_neg]
  have hc1 : (rootReflection (S.ρ γ) * rootReflection γ) • (S.ρ γ) = -γ := by
    rw [mul_smul, rootReflection_smul_sl hτ hγ, h01, one_smul, ← hr2eq, hrefl2]
  have hc2 : (rootReflection (S.ρ γ) * rootReflection γ) • (S.ρ (S.ρ γ)) = -(S.ρ γ) := by
    have hf : iform γ (S.ρ (S.ρ γ)) = -1 := by
      rw [hr2eq, iform_sub_right, h01, iform_self_eq_two hτ hγ]
      norm_num
    rw [mul_smul, rootReflection_smul_sl hτ hγ, hf, neg_smul, one_smul, sub_neg_eq_add, hr2eq,
      sub_add_cancel, rootReflection_smul_self hr1]
  have hconj : ν * rootDiagUnit τ (hexRY S q γ ω) * ν⁻¹ = rootDiagUnit τ
      (Hchar (S.ρ (S.ρ γ)) ω * Hchar (-γ) (ω ^ q) * Hchar (-(S.ρ γ)) (ω ^ q ^ 2)) := by
    have e : rootDiagUnit τ (hexRY S q γ ω) = Hel γ ω * Hel (S.ρ γ) (ω ^ q) *
        Hel (S.ρ (S.ρ γ)) (ω ^ q ^ 2) := by
      unfold hexRY Hel
      rw [rootDiagUnit_mul, rootDiagUnit_mul]
    calc ν * rootDiagUnit τ (hexRY S q γ ω) * ν⁻¹
        = (ν * Hel γ ω * ν⁻¹) * (ν * Hel (S.ρ γ) (ω ^ q) * ν⁻¹) *
            (ν * Hel (S.ρ (S.ρ γ)) (ω ^ q ^ 2) * ν⁻¹) := by rw [e]; group
      _ = _ := by
        rw [hν, hν, hν, hc0, hc1, hc2]
        unfold Hel
        rw [← rootDiagUnit_mul, ← rootDiagUnit_mul]
  rw [hconj, rootDiagUnit_pow]
  congr 1
  have hY : hexRY S q γ ω = Hchar γ (ω * (ω ^ q ^ 2)⁻¹) * Hchar (S.ρ γ) (ω ^ q * ω ^ q ^ 2) := by
    unfold hexRY
    rw [hr2eq, Hchar_sub, ← Hchar_mul, ← Hchar_mul]
    ac_rfl
  rw [hY, mul_pow, Hchar_pow_nat, Hchar_pow_nat, ← hex_exp2 hp ω hω q hq3, ← hex_exp1 hp ω hω q hq3,
    hr2eq, Hchar_sub, Hchar_neg, Hchar_neg, ← Hchar_mul, ← Hchar_mul]
  ac_rfl


end RhoYH

end RhoY


section HexGamma

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

@[expose] def LangSetup.HexGroupInGamma (S : LangSetup τ L p) : Prop :=
  ∀ γ : Fin τ.rank → ℤ, IsRoot τ γ → rootSpan τ L (hexROrbit S γ) ⊓ S.D.model ≤ S.Γ

theorem LangSetup.HexGroupInGamma.of_model_le (S : LangSetup τ L p) (hM : S.D.model ≤ S.Γ) :
    S.HexGroupInGamma := fun _ _ => inf_le_right.trans hM

end HexGamma


section HexMain

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)
  (h : S.HexStep) (hτ : SimplyLacedTag τ)

include h hτ

theorem hexR_Hel_mem {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (j : ℕ) (u : Lˣ) :
    Hel ((S.ρ : (Fin τ.rank → ℤ) → _)^[j] γ) u ∈ rootSpan τ L (hexROrbit S γ) := by
  have hr : IsRoot τ ((S.ρ : (Fin τ.rank → ℤ) → _)^[j] γ) := S.iterate_isRoot j hγ
  have hsub : ({(S.ρ : (Fin τ.rank → ℤ) → _)^[j] γ,
      -((S.ρ : (Fin τ.rank → ℤ) → _)^[j] γ)} : Set (Fin τ.rank → ℤ)) ⊆ hexROrbit S γ := by
    rintro x (rfl | rfl)
    · exact ⟨j, rfl⟩
    · exact hexR_neg_mem S h hγ j
  exact rootSpan_mono hsub (Hel_root_mem_rootSpan hτ hr u)

theorem bigAnyPBig_of_hexStep (hp7 : 7 ≤ p) (hΓ : S.HexGroupInGamma) : BigAnyPBig S := by
  intro D₁ hD₁E hc a ha a' ha' γ hγ hχa hχa' i hγi
  have hp := S.hp
  have hE' : rootDiagUnit τ a' ∈ S.E := hD₁E ha'
  have htor : rootDiagUnit τ a' ∈ S.D.torus := (Subgroup.mem_inf.1 (S.E_le hE')).1
  have hpow : (rootDiagUnit τ a') ^ p = 1 := S.E_exp _ hE'
  have hpow' : a' ^ p = 1 := by
    apply CFSG.LieType.Chevalley.rootDiagUnit_injective (τ := τ) (K := L)
    rw [← rootDiagUnit_pow, hpow, rootDiagUnit_one]
  set q := S.D.q with hq
  set ω : Lˣ := rootChar a' γ with hω
  have hωp : ω ^ p = 1 := by
    rw [hω, ← rootChar_pow, hpow', rootChar_one']
  have hχ : ∀ δ, IsRoot τ δ → rootChar a' (S.ρ δ) = rootChar a' δ ^ q := fun δ hδ =>
    S.frob.rootChar_eq a' htor δ hδ
  have hr1 : IsRoot τ (S.ρ γ) := (S.frob.isRoot_iff γ).2 hγ
  have h1 : rootChar a' (S.ρ γ) = ω ^ q := hχ γ hγ
  have h2 : rootChar a' (S.ρ (S.ρ γ)) = ω ^ q ^ 2 := by
    rw [hχ _ hr1, h1, ← pow_mul, sq]
  have h2' : rootChar a' (S.ρ (S.ρ γ)) = rootChar a' (S.ρ γ) * ω⁻¹ := by
    rw [h.rel6 γ hγ, rootChar_sub]
  have hω1 : ω ≠ 1 := hχa'
  have hord : orderOf ω = p := by
    have : Fact p.Prime := ⟨hp⟩
    exact orderOf_eq_prime hωp hω1
  have hq2 : (p : ℤ) ∣ (q : ℤ) ^ 2 - q + 1 := by
    have hz : ω ^ (((q : ℤ) ^ 2 - q + 1)) = 1 := by
      have : ω ^ q ^ 2 = ω ^ q * ω⁻¹ := by rw [← h2, h2', h1]
      rw [zpow_add, zpow_sub, zpow_one, ← Nat.cast_pow, zpow_natCast, zpow_natCast, this]
      group
    exact hord ▸ orderOf_dvd_iff_zpow_eq_one.2 hz
  have hq3 : (p : ℤ) ∣ (q : ℤ) ^ 3 + 1 := by
    have : (q : ℤ) ^ 3 + 1 = ((q : ℤ) + 1) * ((q : ℤ) ^ 2 - q + 1) := by ring
    rw [this]
    exact dvd_mul_of_dvd_right hq2 _
  have hp3 : ¬ (p : ℤ) ∣ 3 := by
    intro h3
    have : p ∣ 3 := by exact_mod_cast h3
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have hE : ¬ (p : ℤ) ∣ 2 + (q : ℤ) - (q : ℤ) ^ 2 := by
    intro h3
    apply hp3
    have : (3 : ℤ) = (2 + (q : ℤ) - (q : ℤ) ^ 2) + ((q : ℤ) ^ 2 - q + 1) := by ring
    rw [this]
    exact dvd_add h3 hq2
  have hp1 : 1 ≤ p := hp.one_lt.le
  have hk : ¬ (p : ℤ) ∣ (((p - 1) * q : ℕ) : ℤ) - 1 := by
    intro h3
    apply hp3
    have e1 : (((p - 1) * q : ℕ) : ℤ) - 1 = p * q - ((q : ℤ) + 1) := by
      push_cast [Nat.cast_sub hp1]
      ring
    rw [e1] at h3
    have h' : (p : ℤ) ∣ (q : ℤ) + 1 := by
      have := dvd_sub (dvd_mul_right (p : ℤ) q) h3
      simpa using this
    have : (3 : ℤ) = ((q : ℤ) ^ 2 - q + 1) - ((q : ℤ) + 1) * ((q : ℤ) - 2) := by ring
    rw [this]
    exact dvd_sub hq2 (dvd_mul_of_dvd_left h' _)
  have hωq : ω ^ (q ^ 3 + 1) = 1 := by
    have : p ∣ q ^ 3 + 1 := by exact_mod_cast hq3
    exact orderOf_dvd_iff_pow_eq_one.1 (hord ▸ this)
  obtain ⟨ν, hνm, hνF, hνc⟩ := hexR_nu S h hτ hγ
  have hΘ : hexROrbit S γ ⊆ rationalRoots S.ρ (rootCharHom a) i := by
    rintro x ⟨j, rfl⟩
    exact ⟨j, γ, hγi, rfl⟩
  have hy : rootDiagUnit τ (hexRY S q γ ω) ∈ rootSpan τ L (hexROrbit S γ) := by
    unfold hexRY
    rw [rootDiagUnit_mul, rootDiagUnit_mul]
    refine mul_mem (mul_mem ?_ ?_) ?_
    · exact hexR_Hel_mem S h hτ hγ 0 ω
    · exact hexR_Hel_mem S h hτ hγ 1 (ω ^ q)
    · exact hexR_Hel_mem S h hτ hγ 2 (ω ^ q ^ 2)
  exact not_coprime_of_commutator_pair_sub S i hΘ (hΓ γ hγ) hy (hexRY_step S h hτ hγ ω hωq)
    (hexRY_pow S q p γ ω hωp) (hexRY_ne_one S h hτ q p hp hγ ω hωp hω1 hE) hνm hνF
    (hexRY_conj S h hτ q p hp1 hq3 hγ ω hωp hνc) hk

end HexMain

end CFSG.HardMathSupport.Timmesfeld.LangTorus
