module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyLang
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyPBig
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyPlane
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ExcRoots

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LieType.AlgebraicGroups

set_option linter.unusedSectionVars false


section Torus

variable {τ : Tag} {L : Type} [Field L]

theorem iform_neg_left' (x y : Fin τ.rank → ℤ) : iform (-x) y = -iform x y := by
  have := iform_smul_left (τ := τ) (-1) x y
  simpa using this

theorem Hchar_neg (x : Fin τ.rank → ℤ) (u : Lˣ) :
    Hchar (τ := τ) (-x) u = Hchar x u⁻¹ := by
  funext l
  simp only [Hchar, iform_neg_left', zpow_neg, inv_zpow']

theorem Hchar_sub (x y : Fin τ.rank → ℤ) (u : Lˣ) :
    Hchar (τ := τ) (x - y) u = Hchar x u * Hchar y u⁻¹ := by
  rw [sub_eq_add_neg, ← Hchar_add, Hchar_neg]

end Torus

section HexData

variable {τ : Tag} {w : WeylGroup τ}

theorem rootReflection_smul_sl (hτ : SimplyLacedTag τ) {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β)
    (v : Fin τ.rank → ℤ) : rootReflection β • v = v - iform β v • β := by
  rw [rootReflection_smul hβ, corootPair, iform_self_eq_two hτ hβ]
  simp

theorem hex_form01 (hτ : SimplyLacedTag τ)
    (hw6 : ∀ δ : Fin τ.rank → ℤ, IsRoot τ δ → w • w • δ = w • δ - δ) {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) : iform γ (w • γ) = 1 := by
  have h1 : iform (w • γ) (w • w • γ) = iform γ (w • γ) := iform_smul w γ (w • γ)
  rw [hw6 γ hγ, iform_sub_right, iform_comm (w • γ) γ,
    iform_self_eq_two hτ ((isRoot_smul_iff w).2 hγ)] at h1
  omega

theorem hex_w3 (hw6 : ∀ δ : Fin τ.rank → ℤ, IsRoot τ δ → w • w • δ = w • δ - δ)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) : w • w • w • γ = -γ := by
  have h1 := hw6 (w • γ) ((isRoot_smul_iff w).2 hγ)
  rw [h1, hw6 γ hγ]
  abel

@[expose] def hexOrbit (w : WeylGroup τ) (γ : Fin τ.rank → ℤ) : Set (Fin τ.rank → ℤ) :=
  {x | ∃ j : ℕ, x = (w ^ j) • γ}

theorem pow_smul_w3 (hw6 : ∀ δ : Fin τ.rank → ℤ, IsRoot τ δ → w • w • δ = w • δ - δ)
    {δ : Fin τ.rank → ℤ} (hδ : IsRoot τ δ) (j : ℕ) : (w ^ (j + 3)) • δ = -((w ^ j) • δ) := by
  rw [pow_add, mul_smul, show (w ^ 3) • δ = w • w • w • δ by simp [pow_succ, mul_smul],
    hex_w3 hw6 hδ, smul_neg]

theorem pow_six_smul (hw6 : ∀ δ : Fin τ.rank → ℤ, IsRoot τ δ → w • w • δ = w • δ - δ)
    {δ : Fin τ.rank → ℤ} (hδ : IsRoot τ δ) : (w ^ 6) • δ = δ := by
  have := pow_smul_w3 hw6 hδ 3
  rw [show (3 + 3 : ℕ) = 6 from rfl] at this
  rw [this, show (w ^ 3) • δ = w • w • w • δ by simp [pow_succ, mul_smul], hex_w3 hw6 hδ, neg_neg]

theorem neg_mem_hexOrbit (hw6 : ∀ δ : Fin τ.rank → ℤ, IsRoot τ δ → w • w • δ = w • δ - δ)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (j : ℕ) : -((w ^ j) • γ) ∈ hexOrbit w γ :=
  ⟨j + 3, (pow_smul_w3 hw6 hγ j).symm ▸ rfl⟩

end HexData

section HexStep

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)
  {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ S.D.q) (hΦ : S.D.Φ = Units.map (entrywiseHom Fr))
  {w : WeylGroup τ} (hn : S.D.n = canonicalRep (coxeterSystem τ) L w)
  (hτ : SimplyLacedTag τ)
  (hw6 : ∀ δ : Fin τ.rank → ℤ, IsRoot τ δ → w • w • δ = w • δ - δ)

include hFr hΦ hn hτ hw6

theorem LangSetup.hex_defect {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    ∃ v₁ v₂ : Lˣ,
      (rootSL2 τ L (w • γ) (nSL 1) * rootSL2 τ L γ (nSL 1))⁻¹ *
        S.D.step (rootSL2 τ L (w • γ) (nSL 1) * rootSL2 τ L γ (nSL 1)) =
      Hel (-γ) v₁ * Hel (w • γ) v₂ := by
  have hr1 : IsRoot τ (w • γ) := (isRoot_smul_iff w).2 hγ
  have hr2 : IsRoot τ (w • w • γ) := (isRoot_smul_iff w).2 hr1
  have hr2eq := hw6 γ hγ
  have h01 := hex_form01 hτ hw6 hγ
  obtain ⟨a1, ha1⟩ := S.step_nSL hFr hΦ hn hr1
  obtain ⟨a0, ha0⟩ := S.step_nSL hFr hΦ hn hγ
  obtain ⟨-, hmon, hmaps⟩ := rootWeylOne_spec (K := L) hr1
  have hrefl : rootReflection (w • γ) • γ = -(w • w • γ) := by
    rw [rootReflection_smul_sl hτ hr1, iform_comm, h01, one_smul, hr2eq]
    abel
  obtain ⟨s, hs⟩ := conj_rootSL2_nSL hmon hmaps hγ hrefl
  obtain ⟨a, ha⟩ := rootSL2_neg_nSL (L := L) hr2
  have hconj : rootSL2 τ L (w • γ) (nSL 1) * rootSL2 τ L γ (nSL 1) =
      rootSL2 τ L (w • w • γ) (nSL (-(a * (s * 1))⁻¹)) * rootSL2 τ L (w • γ) (nSL 1) := by
    have h : rootSL2 τ L (w • γ) (nSL 1) * rootSL2 τ L γ (nSL 1) *
        (rootSL2 τ L (w • γ) (nSL 1))⁻¹ = rootSL2 τ L (-(w • w • γ)) (nSL (s * 1)) := hs 1
    rw [ha] at h
    exact mul_inv_eq_iff_eq_mul.1 h
  have hF : S.D.step (rootSL2 τ L (w • γ) (nSL 1) * rootSL2 τ L γ (nSL 1)) =
      rootSL2 τ L (w • w • γ) (nSL a1) * rootSL2 τ L (w • γ) (nSL a0) := by
    rw [map_mul, ha1 1, ha0 1, one_pow, mul_one, mul_one]
  have hH := rootSL2_nSL_inv_mul hτ hr2 (-(a * (s * 1))⁻¹) a1
  have hH1 := rootSL2_nSL_inv_mul (L := L) hτ hr1 1 a0
  have hform : iform (w • γ) (w • w • γ) = 1 := by
    rw [hr2eq, iform_sub_right, iform_comm (w • γ) γ, h01, iform_self_eq_two hτ hr1]
    norm_num
  have hrefl2 : (rootReflection (w • γ))⁻¹ • (w • w • γ) = -γ := by
    rw [rootReflection_inv hr1, rootReflection_smul_sl hτ hr1, hform, one_smul, hr2eq]
    abel
  have hconjH : ∀ v : Lˣ, (rootSL2 τ L (w • γ) (nSL 1))⁻¹ * Hel (w • w • γ) v *
      ((rootSL2 τ L (w • γ) (nSL 1))⁻¹)⁻¹ = Hel (-γ) v := fun v => by
    have := conj_Hel (L := L) (n := (rootSL2 τ L (w • γ) (nSL 1))⁻¹) (inv_mem hmon) hmaps.inv
      (w • w • γ) v
    rw [this, hrefl2]
  refine ⟨(-(a * (s * 1))⁻¹) * a1⁻¹, 1 * a0⁻¹, ?_⟩
  rw [hF, hconj, ← hconjH ((-(a * (s * 1))⁻¹) * a1⁻¹), ← hH, ← hH1]
  group

theorem LangSetup.hex_nu {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    ∃ ν : ModGL τ L, ν ∈ rootSpan τ L (hexOrbit w γ) ∧ S.D.step ν = ν ∧
      ∀ (x : Fin τ.rank → ℤ) (u : Lˣ),
        ν * Hel x u * ν⁻¹ = Hel ((rootReflection (w • γ) * rootReflection γ) • x) u := by
  have hr1 : IsRoot τ (w • γ) := (isRoot_smul_iff w).2 hγ
  obtain ⟨v₁, v₂, hdef⟩ := S.hex_defect hFr hΦ hn hτ hw6 hγ
  obtain ⟨hsup1, hmon1, hmaps1⟩ := rootWeylOne_spec (K := L) hr1
  obtain ⟨hsup0, hmon0, hmaps0⟩ := rootWeylOne_spec (K := L) hγ
  have hshift : ∀ j : ℕ, (w ^ j) • (w • γ) = (w ^ (j + 1)) • γ := fun j => by
    rw [pow_succ, mul_smul]
  have hΘ1 : ∀ j : ℕ, (w ^ j) • (w • γ) ∈ hexOrbit w γ ∧ -((w ^ j) • (w • γ)) ∈ hexOrbit w γ :=
    fun j => by
      rw [hshift]
      exact ⟨⟨j + 1, rfl⟩, neg_mem_hexOrbit hw6 hγ (j + 1)⟩
  have hΘ0 : ∀ j : ℕ, (w ^ j) • (-γ) ∈ hexOrbit w γ ∧ -((w ^ j) • (-γ)) ∈ hexOrbit w γ :=
    fun j => by
      rw [smul_neg, neg_neg]
      exact ⟨neg_mem_hexOrbit hw6 hγ j, ⟨j, rfl⟩⟩
  have h6neg : (w ^ 6) • (-γ) = -γ := by rw [smul_neg, pow_six_smul hw6 hγ]
  obtain ⟨b₁, b₁', hF₁, hb₁, hm₁⟩ := S.exists_lang_Hchar hFr hΦ hn hτ (IsRoot.neg hγ)
    (N := 6) (by norm_num) h6neg v₁ hΘ0
  obtain ⟨b₂, b₂', hF₂, hb₂, hm₂⟩ := S.exists_lang_Hchar hFr hΦ hn hτ hr1
    (N := 6) (by norm_num) (pow_six_smul hw6 hr1) v₂ hΘ1
  set N1 : ModGL τ L := rootSL2 τ L (w • γ) (nSL 1) with hN1
  set N0 : ModGL τ L := rootSL2 τ L γ (nSL 1) with hN0
  set s : ModGL τ L := rootDiagUnit τ (b₁ * b₂) with hs
  have hFs : S.D.step s = rootDiagUnit τ (b₁' * b₂') := by
    rw [hs, rootDiagUnit_mul, map_mul, hF₁, hF₂, rootDiagUnit_mul]
  have ht : Hel (-γ) v₁ * Hel (w • γ) v₂ = s * (S.D.step s)⁻¹ := by
    unfold Hel
    rw [hFs, hs, rootDiagUnit_inv, ← rootDiagUnit_mul, ← rootDiagUnit_mul,
      ← hb₁, ← hb₂, mul_inv, mul_mul_mul_comm]
  have hneg1 : -(w • γ) ∈ hexOrbit w γ := by
    have := neg_mem_hexOrbit hw6 hγ 1
    simpa using this
  have hneg0 : -γ ∈ hexOrbit w γ := by
    have := neg_mem_hexOrbit hw6 hγ 0
    simpa using this
  have hN1m : N1 ∈ rootSpan τ L (hexOrbit w γ) := by
    have hsub : ({w • γ, -(w • γ)} : Set (Fin τ.rank → ℤ)) ⊆ hexOrbit w γ := by
      rintro x (rfl | rfl)
      · exact ⟨1, by simp⟩
      · exact hneg1
    exact rootSpan_mono hsub (rootSL2_mem_rootSpan_pair hr1 _)
  have hN0m : N0 ∈ rootSpan τ L (hexOrbit w γ) := by
    have hsub : ({γ, -γ} : Set (Fin τ.rank → ℤ)) ⊆ hexOrbit w γ := by
      rintro x (rfl | rfl)
      · exact ⟨0, by simp⟩
      · exact hneg0
    exact rootSpan_mono hsub (rootSL2_mem_rootSpan_pair hγ _)
  have hsm : s ∈ rootSpan τ L (hexOrbit w γ) := by
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

@[expose] noncomputable def hexY (w : WeylGroup τ) (q : ℕ) (γ : Fin τ.rank → ℤ) (ω : Lˣ) :
    Fin τ.rank → Lˣ :=
  Hchar γ ω * Hchar (w • γ) (ω ^ q) * Hchar (w • w • γ) (ω ^ q ^ 2)

theorem LangSetup.step_hexY {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (ω : Lˣ)
    (hω : ω ^ (S.D.q ^ 3 + 1) = 1) :
    S.D.step (rootDiagUnit τ (hexY w S.D.q γ ω)) = rootDiagUnit τ (hexY w S.D.q γ ω) := by
  have hst : ∀ (x : Fin τ.rank → ℤ) (u : Lˣ),
      S.D.step (rootDiagUnit τ (Hchar x u)) = rootDiagUnit τ (Hchar (w • x) (u ^ S.D.q)) :=
    fun x u => S.step_Hel hFr hΦ hn x u
  have h3 : (w • w • w • γ) = -γ := hex_w3 hw6 hγ
  have hω3 : (ω ^ S.D.q ^ 2) ^ S.D.q = ω⁻¹ := by
    rw [← pow_mul, ← pow_succ]
    have : ω ^ S.D.q ^ 3 * ω = 1 := by rw [← pow_succ]; exact hω
    exact eq_inv_of_mul_eq_one_left this
  unfold hexY
  rw [rootDiagUnit_mul, rootDiagUnit_mul, map_mul, map_mul, hst, hst, hst, h3, hω3, Hchar_neg,
    inv_inv, ← pow_mul]
  rw [show S.D.q * S.D.q = S.D.q ^ 2 from (sq _).symm, ← rootDiagUnit_mul, ← rootDiagUnit_mul,
    ← rootDiagUnit_mul, ← rootDiagUnit_mul]
  congr 1
  ac_rfl

end HexStep

section HexY

variable {τ : Tag} {L : Type} [Field L] {w : WeylGroup τ}

theorem Hchar_one' (x : Fin τ.rank → ℤ) : Hchar (τ := τ) (L := L) x 1 = 1 := by
  funext l
  simp [Hchar]

theorem Hchar_pow_nat (x : Fin τ.rank → ℤ) (u : Lˣ) (n : ℕ) :
    Hchar (τ := τ) x u ^ n = Hchar x (u ^ n) := by
  have := Hchar_pow (τ := τ) x u (n : ℤ)
  simpa [zpow_natCast] using this

theorem hexY_pow (q p : ℕ) (γ : Fin τ.rank → ℤ) (ω : Lˣ) (hω : ω ^ p = 1) :
    (rootDiagUnit τ (hexY w q γ ω)) ^ p = 1 := by
  rw [rootDiagUnit_pow, ← rootDiagUnit_one (τ := τ) (K := L)]
  congr 1
  unfold hexY
  have h1 : ∀ k : ℕ, (ω ^ k) ^ p = 1 := fun k => by
    rw [← pow_mul, mul_comm, pow_mul, hω, one_pow]
  rw [mul_pow, mul_pow, Hchar_pow_nat, Hchar_pow_nat, Hchar_pow_nat, hω, h1, h1]
  simp [Hchar_one']

theorem rootChar_mul_tuple (a b : Fin τ.rank → Lˣ) (v : Fin τ.rank → ℤ) :
    rootChar (a * b) v = rootChar a v * rootChar b v := by
  simp only [rootChar, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]

theorem rootChar_one' (v : Fin τ.rank → ℤ) : rootChar (1 : Fin τ.rank → Lˣ) v = 1 := by
  simp [rootChar]

theorem hexY_ne_one (hτ : SimplyLacedTag τ)
    (hw6 : ∀ δ : Fin τ.rank → ℤ, IsRoot τ δ → w • w • δ = w • δ - δ) (q p : ℕ) (hp : p.Prime)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (ω : Lˣ) (hω : ω ^ p = 1) (hω1 : ω ≠ 1)
    (hE : ¬ (p : ℤ) ∣ 2 + (q : ℤ) - (q : ℤ) ^ 2) : rootDiagUnit τ (hexY w q γ ω) ≠ 1 := by
  intro h
  have hY : hexY w q γ ω = 1 := by
    have : rootDiagUnit τ (hexY w q γ ω) = rootDiagUnit τ (1 : Fin τ.rank → Lˣ) := by
      rw [h, rootDiagUnit_one]
    exact CFSG.LieType.Chevalley.rootDiagUnit_injective this
  have hc : rootChar (hexY w q γ ω) γ = 1 := by rw [hY, rootChar_one']
  have hr1 : IsRoot τ (w • γ) := (isRoot_smul_iff w).2 hγ
  have h01 := hex_form01 hτ hw6 hγ
  have hf1 : iform (w • γ) γ = 1 := by rw [iform_comm]; exact h01
  have hf2 : iform (w • w • γ) γ = -1 := by
    rw [hw6 γ hγ, iform_sub_left, hf1, iform_self_eq_two hτ hγ]
    norm_num
  unfold hexY at hc
  rw [rootChar_mul_tuple, rootChar_mul_tuple, rootChar_Hchar, rootChar_Hchar, rootChar_Hchar,
    iform_self_eq_two hτ hγ, hf1, hf2] at hc
  have hz : ω ^ ((2 : ℤ) + q - (q : ℤ) ^ 2) = 1 := by
    rw [← hc, zpow_sub, zpow_add, zpow_one, zpow_neg_one, ← Nat.cast_pow, zpow_natCast,
      zpow_natCast]
  have : Fact p.Prime := ⟨hp⟩
  have hord : orderOf ω = p := orderOf_eq_prime hω hω1
  exact hE (hord ▸ orderOf_dvd_iff_zpow_eq_one.2 hz)

theorem unit_zpow_eq_of_dvd {L : Type} [Field L] {p : ℕ} (ω : Lˣ) (hω : ω ^ p = 1) {e e' : ℤ}
    (h : (p : ℤ) ∣ e - e') : ω ^ e = ω ^ e' := by
  obtain ⟨t, ht⟩ := h
  have : e = e' + p * t := by linarith
  rw [this, zpow_add, zpow_mul, zpow_natCast, hω, one_zpow, mul_one]

theorem hex_exp1 {L : Type} [Field L] {p : ℕ} (hp : 1 ≤ p) (ω : Lˣ) (hω : ω ^ p = 1) (q : ℕ)
    (hq3 : (p : ℤ) ∣ (q : ℤ) ^ 3 + 1) :
    (ω ^ q)⁻¹ * ω⁻¹ = (ω * (ω ^ q ^ 2)⁻¹) ^ ((p - 1) * q) := by
  have h1 : (ω ^ q)⁻¹ * ω⁻¹ = ω ^ (-(q : ℤ) - 1) := by
    rw [zpow_sub, zpow_neg, zpow_natCast, zpow_one, ← mul_inv, mul_comm]
  have hb : ω * (ω ^ q ^ 2)⁻¹ = ω ^ ((1 : ℤ) - (q : ℤ) ^ 2) := by
    rw [zpow_sub, zpow_one, ← Nat.cast_pow, zpow_natCast]
  rw [h1, hb, ← zpow_natCast, ← zpow_mul]
  refine unit_zpow_eq_of_dvd ω hω ?_
  have : (-(q : ℤ) - 1) - ((1 - (q : ℤ) ^ 2) * (((p - 1) * q : ℕ) : ℤ)) =
      -((q : ℤ) ^ 3 + 1) - p * (q * (1 - (q : ℤ) ^ 2)) := by
    push_cast [Nat.cast_sub hp]
    ring
  rw [this]
  exact dvd_sub (dvd_neg.2 hq3) (dvd_mul_right _ _)

theorem hex_exp2 {L : Type} [Field L] {p : ℕ} (hp : 1 ≤ p) (ω : Lˣ) (hω : ω ^ p = 1) (q : ℕ)
    (hq3 : (p : ℤ) ∣ (q : ℤ) ^ 3 + 1) :
    ω * (ω ^ q ^ 2)⁻¹ = (ω ^ q * ω ^ q ^ 2) ^ ((p - 1) * q) := by
  have h1 : ω * (ω ^ q ^ 2)⁻¹ = ω ^ ((1 : ℤ) - (q : ℤ) ^ 2) := by
    rw [zpow_sub, zpow_one, ← Nat.cast_pow, zpow_natCast]
  have hb : ω ^ q * ω ^ q ^ 2 = ω ^ ((q : ℤ) + (q : ℤ) ^ 2) := by
    rw [zpow_add, ← Nat.cast_pow, zpow_natCast, zpow_natCast]
  rw [h1, hb, ← zpow_natCast, ← zpow_mul]
  refine unit_zpow_eq_of_dvd ω hω ?_
  have : ((1 : ℤ) - (q : ℤ) ^ 2) - (((q : ℤ) + (q : ℤ) ^ 2) * (((p - 1) * q : ℕ) : ℤ)) =
      ((q : ℤ) ^ 3 + 1) - p * (q * ((q : ℤ) + (q : ℤ) ^ 2)) := by
    push_cast [Nat.cast_sub hp]
    ring
  rw [this]
  exact dvd_sub hq3 (dvd_mul_right _ _)

theorem hexY_conj (hτ : SimplyLacedTag τ)
    (hw6 : ∀ δ : Fin τ.rank → ℤ, IsRoot τ δ → w • w • δ = w • δ - δ) (q p : ℕ) (hp : 1 ≤ p)
    (hq3 : (p : ℤ) ∣ (q : ℤ) ^ 3 + 1) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (ω : Lˣ)
    (hω : ω ^ p = 1) {ν : ModGL τ L}
    (hν : ∀ (x : Fin τ.rank → ℤ) (u : Lˣ),
      ν * Hel x u * ν⁻¹ = Hel ((rootReflection (w • γ) * rootReflection γ) • x) u) :
    ν * rootDiagUnit τ (hexY w q γ ω) * ν⁻¹ = (rootDiagUnit τ (hexY w q γ ω)) ^ ((p - 1) * q) := by
  have hr1 : IsRoot τ (w • γ) := (isRoot_smul_iff w).2 hγ
  have h01 := hex_form01 hτ hw6 hγ
  have hr2eq := hw6 γ hγ
  have hform : iform (w • γ) (w • w • γ) = 1 := by
    rw [hr2eq, iform_sub_right, iform_comm (w • γ) γ, h01, iform_self_eq_two hτ hr1]
    norm_num
  have hrefl1 : rootReflection (w • γ) • γ = -(w • w • γ) := by
    rw [rootReflection_smul_sl hτ hr1, iform_comm, h01, one_smul, hr2eq]
    abel
  have hrefl2 : rootReflection (w • γ) • (w • w • γ) = -γ := by
    rw [rootReflection_smul_sl hτ hr1, hform, one_smul, hr2eq]
    abel
  have hc0 : (rootReflection (w • γ) * rootReflection γ) • γ = w • w • γ := by
    rw [mul_smul, rootReflection_smul_self hγ, smul_neg, hrefl1, neg_neg]
  have hc1 : (rootReflection (w • γ) * rootReflection γ) • (w • γ) = -γ := by
    rw [mul_smul, rootReflection_smul_sl hτ hγ, h01, one_smul, ← hr2eq, hrefl2]
  have hc2 : (rootReflection (w • γ) * rootReflection γ) • (w • w • γ) = -(w • γ) := by
    have hf : iform γ (w • w • γ) = -1 := by
      rw [hr2eq, iform_sub_right, h01, iform_self_eq_two hτ hγ]
      norm_num
    rw [mul_smul, rootReflection_smul_sl hτ hγ, hf, neg_smul, one_smul, sub_neg_eq_add, hr2eq,
      sub_add_cancel, rootReflection_smul_self hr1]
  have hconj : ν * rootDiagUnit τ (hexY w q γ ω) * ν⁻¹ = rootDiagUnit τ
      (Hchar (w • w • γ) ω * Hchar (-γ) (ω ^ q) * Hchar (-(w • γ)) (ω ^ q ^ 2)) := by
    have e : rootDiagUnit τ (hexY w q γ ω) = Hel γ ω * Hel (w • γ) (ω ^ q) *
        Hel (w • w • γ) (ω ^ q ^ 2) := by
      unfold hexY Hel
      rw [rootDiagUnit_mul, rootDiagUnit_mul]
    calc ν * rootDiagUnit τ (hexY w q γ ω) * ν⁻¹
        = (ν * Hel γ ω * ν⁻¹) * (ν * Hel (w • γ) (ω ^ q) * ν⁻¹) *
            (ν * Hel (w • w • γ) (ω ^ q ^ 2) * ν⁻¹) := by rw [e]; group
      _ = _ := by
        rw [hν, hν, hν, hc0, hc1, hc2]
        unfold Hel
        rw [← rootDiagUnit_mul, ← rootDiagUnit_mul]
  rw [hconj, rootDiagUnit_pow]
  congr 1
  have hY : hexY w q γ ω = Hchar γ (ω * (ω ^ q ^ 2)⁻¹) * Hchar (w • γ) (ω ^ q * ω ^ q ^ 2) := by
    unfold hexY
    rw [hr2eq, Hchar_sub, ← Hchar_mul, ← Hchar_mul]
    ac_rfl
  rw [hY, mul_pow, Hchar_pow_nat, Hchar_pow_nat, ← hex_exp2 hp ω hω q hq3, ← hex_exp1 hp ω hω q hq3,
    hr2eq, Hchar_sub, Hchar_neg, Hchar_neg, ← Hchar_mul, ← Hchar_mul]
  ac_rfl

end HexY

section HexMem

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {w : WeylGroup τ}

theorem Hel_mem_rootSpan_hexOrbit (hτ : SimplyLacedTag τ)
    (hw6 : ∀ δ : Fin τ.rank → ℤ, IsRoot τ δ → w • w • δ = w • δ - δ) {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) (j : ℕ) (u : Lˣ) :
    Hel ((w ^ j) • γ) u ∈ rootSpan τ L (hexOrbit w γ) := by
  have hr : IsRoot τ ((w ^ j) • γ) := (isRoot_smul_iff _).2 hγ
  have hsub : ({(w ^ j) • γ, -((w ^ j) • γ)} : Set (Fin τ.rank → ℤ)) ⊆ hexOrbit w γ := by
    rintro x (rfl | rfl)
    · exact ⟨j, rfl⟩
    · exact neg_mem_hexOrbit hw6 hγ j
  exact rootSpan_mono hsub (Hel_root_mem_rootSpan hτ hr u)

end HexMem

section HexMain

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)
  {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ S.D.q) (hΦ : S.D.Φ = Units.map (entrywiseHom Fr))
  {w : WeylGroup τ} (hn : S.D.n = canonicalRep (coxeterSystem τ) L w)
  (hτ : SimplyLacedTag τ)
  (hw6 : ∀ δ : Fin τ.rank → ℤ, IsRoot τ δ → w • w • δ = w • δ - δ)

include hFr hΦ hn hτ hw6

theorem hexOrbit_subset_rationalRoots {a : Fin τ.rank → Lˣ} (i : KernelComponent (rootCharHom a))
    {γ : Fin τ.rank → ℤ} (hγ : γ ∈ componentRoots (rootCharHom a) i) (hγr : IsRoot τ γ) :
    hexOrbit w γ ⊆ rationalRoots S.ρ (rootCharHom a) i := by
  have key : ∀ j : ℕ, ((S.ρ : (Fin τ.rank → ℤ) → _)^[j] γ) = (w ^ j) • γ := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Function.iterate_succ_apply', ih, S.rho_eq_smul_of_frob hFr hΦ hn
        ((isRoot_smul_iff _).2 hγr), pow_succ', mul_smul]
  rintro x ⟨j, rfl⟩
  exact ⟨j, γ, hγ, (key j).symm⟩

theorem bigAnyPBig_of_phi6 (hp7 : 7 ≤ p) (hMΓ : S.D.model ≤ S.Γ) : BigAnyPBig S := by
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
  have hχ : ∀ δ, IsRoot τ δ → rootChar a' (w • δ) = rootChar a' δ ^ q := fun δ hδ => by
    rw [← S.rho_eq_smul_of_frob hFr hΦ hn hδ]
    exact S.frob.rootChar_eq a' htor δ hδ
  have hr1 : IsRoot τ (w • γ) := (isRoot_smul_iff w).2 hγ
  have h1 : rootChar a' (w • γ) = ω ^ q := hχ γ hγ
  have h2 : rootChar a' (w • w • γ) = ω ^ q ^ 2 := by
    rw [hχ _ hr1, h1, ← pow_mul, sq]
  have h2' : rootChar a' (w • w • γ) = rootChar a' (w • γ) * ω⁻¹ := by
    rw [hw6 γ hγ, rootChar_sub]
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
    intro h
    have : p ∣ 3 := by exact_mod_cast h
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have hE : ¬ (p : ℤ) ∣ 2 + (q : ℤ) - (q : ℤ) ^ 2 := by
    intro h
    apply hp3
    have : (3 : ℤ) = (2 + (q : ℤ) - (q : ℤ) ^ 2) + ((q : ℤ) ^ 2 - q + 1) := by ring
    rw [this]
    exact dvd_add h hq2
  have hp1 : 1 ≤ p := hp.one_lt.le
  have hk : ¬ (p : ℤ) ∣ (((p - 1) * q : ℕ) : ℤ) - 1 := by
    intro h
    apply hp3
    have e1 : (((p - 1) * q : ℕ) : ℤ) - 1 = p * q - ((q : ℤ) + 1) := by
      push_cast [Nat.cast_sub hp1]
      ring
    rw [e1] at h
    have h' : (p : ℤ) ∣ (q : ℤ) + 1 := by
      have := dvd_sub (dvd_mul_right (p : ℤ) q) h
      simpa using this
    have : (3 : ℤ) = ((q : ℤ) ^ 2 - q + 1) - ((q : ℤ) + 1) * ((q : ℤ) - 2) := by ring
    rw [this]
    exact dvd_sub hq2 (dvd_mul_of_dvd_left h' _)
  have hωq : ω ^ (q ^ 3 + 1) = 1 := by
    have : p ∣ q ^ 3 + 1 := by exact_mod_cast hq3
    exact orderOf_dvd_iff_pow_eq_one.1 (hord ▸ this)
  obtain ⟨ν, hνm, hνF, hνc⟩ := S.hex_nu hFr hΦ hn hτ hw6 hγ
  have hΘ := hexOrbit_subset_rationalRoots S hFr hΦ hn hτ hw6 i hγi hγ
  have hy : rootDiagUnit τ (hexY w q γ ω) ∈ rootSpan τ L (hexOrbit w γ) := by
    unfold hexY
    rw [rootDiagUnit_mul, rootDiagUnit_mul]
    refine mul_mem (mul_mem ?_ ?_) ?_
    · have h := Hel_mem_rootSpan_hexOrbit hτ hw6 hγ 0 ω
      rw [pow_zero, one_smul] at h
      exact h
    · have h := Hel_mem_rootSpan_hexOrbit hτ hw6 hγ 1 (ω ^ q)
      rw [pow_one] at h
      exact h
    · have h := Hel_mem_rootSpan_hexOrbit hτ hw6 hγ 2 (ω ^ q ^ 2)
      rw [pow_two, mul_smul] at h
      exact h
  exact not_coprime_of_commutator_pair S hMΓ i hΘ hy (S.step_hexY hFr hΦ hn hτ hw6 hγ ω hωq)
    (hexY_pow q p γ ω hωp) (hexY_ne_one hτ hw6 q p hp hγ ω hωp hω1 hE) hνm hνF
    (hexY_conj hτ hw6 q p hp1 hq3 hγ ω hωp hνc) hk

end HexMain

end CFSG.HardMathSupport.Timmesfeld.LangTorus
