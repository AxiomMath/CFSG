module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyTri

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LieType.AlgebraicGroups

set_option linter.unusedSectionVars false

section Orth

variable {τ : Tag}

theorem not_isRoot_add_of_orth (hτ : SimplyLacedTag τ) {β γ : Fin τ.rank → ℤ} (hβ : IsRoot τ β)
    (hγ : IsRoot τ γ) (h0 : iform β γ = 0) : ¬ IsRoot τ (β + γ) := by
  intro h
  have h2 := iform_self_eq_two hτ h
  rw [iform_add_left, iform_add_right, iform_add_right, iform_self_eq_two hτ hβ,
    iform_self_eq_two hτ hγ, h0, iform_comm γ β, h0] at h2
  omega

theorem not_isRoot_sub_of_orth (hτ : SimplyLacedTag τ) {β γ : Fin τ.rank → ℤ} (hβ : IsRoot τ β)
    (hγ : IsRoot τ γ) (h0 : iform β γ = 0) : ¬ IsRoot τ (β - γ) := by
  intro h
  have h2 := iform_self_eq_two hτ h
  rw [iform_sub_left, iform_sub_right, iform_sub_right, iform_self_eq_two hτ hβ,
    iform_self_eq_two hτ hγ, h0, iform_comm γ β, h0] at h2
  omega

theorem rootSL2_commute_of_orth' (hτ : SimplyLacedTag τ) {L : Type} [Field L]
    {β γ : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (hγ : IsRoot τ γ) (h0 : iform β γ = 0)
    (A B : SL2 L) : rootSL2 τ L β A * rootSL2 τ L γ B = rootSL2 τ L γ B * rootSL2 τ L β A :=
  exceptional_Lang_strongly_orthogonal_root_rank_one_commutation τ L hβ hγ h0
    (not_isRoot_add_of_orth hτ hβ hγ h0) (not_isRoot_sub_of_orth hτ hβ hγ h0) _ ⟨A, rfl⟩ _
    ⟨B, rfl⟩

theorem Hchar_inv_quad {L : Type} [Field L] (x : Fin τ.rank → ℤ) (u : Lˣ) :
    (Hchar (τ := τ) x u)⁻¹ = Hchar x u⁻¹ := by
  funext l
  simp only [Hchar, Pi.inv_apply, inv_zpow', zpow_neg]

end Orth

section QuadData

variable {τ : Tag} {w : WeylGroup τ}

theorem quad_form01 (hw4 : ∀ δ : Fin τ.rank → ℤ, IsRoot τ δ → w • w • δ = -δ)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) : iform γ (w • γ) = 0 := by
  have h1 : iform (w • γ) (w • w • γ) = iform γ (w • γ) := iform_smul w γ (w • γ)
  rw [hw4 γ hγ, iform_neg_right_tri, iform_comm (w • γ) γ] at h1
  omega

@[expose] def quadOrbit (w : WeylGroup τ) (γ : Fin τ.rank → ℤ) : Set (Fin τ.rank → ℤ) :=
  {x | ∃ j : ℕ, x = (w ^ j) • γ}

theorem pow_smul_w2_quad (hw4 : ∀ δ : Fin τ.rank → ℤ, IsRoot τ δ → w • w • δ = -δ)
    {δ : Fin τ.rank → ℤ} (hδ : IsRoot τ δ) (j : ℕ) : (w ^ (j + 2)) • δ = -((w ^ j) • δ) := by
  rw [pow_add, mul_smul, show (w ^ 2) • δ = w • w • δ by simp [pow_succ, mul_smul], hw4 δ hδ,
    smul_neg]

theorem pow_four_smul_quad (hw4 : ∀ δ : Fin τ.rank → ℤ, IsRoot τ δ → w • w • δ = -δ)
    {δ : Fin τ.rank → ℤ} (hδ : IsRoot τ δ) : (w ^ 4) • δ = δ := by
  have := pow_smul_w2_quad hw4 hδ 2
  rw [show (2 + 2 : ℕ) = 4 from rfl] at this
  rw [this, show (w ^ 2) • δ = w • w • δ by simp [pow_succ, mul_smul], hw4 δ hδ, neg_neg]

theorem neg_mem_quadOrbit (hw4 : ∀ δ : Fin τ.rank → ℤ, IsRoot τ δ → w • w • δ = -δ)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (j : ℕ) : -((w ^ j) • γ) ∈ quadOrbit w γ :=
  ⟨j + 2, (pow_smul_w2_quad hw4 hγ j).symm ▸ rfl⟩

end QuadData

section QuadStep

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)
  {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ S.D.q) (hΦ : S.D.Φ = Units.map (entrywiseHom Fr))
  {w : WeylGroup τ} (hn : S.D.n = canonicalRep (coxeterSystem τ) L w)
  (hτ : SimplyLacedTag τ)
  (hw4 : ∀ δ : Fin τ.rank → ℤ, IsRoot τ δ → w • w • δ = -δ)

include hFr hΦ hn hτ hw4

theorem LangSetup.quad_defect {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    ∃ v₁ v₂ : Lˣ,
      (rootSL2 τ L (w • γ) (nSL 1) * rootSL2 τ L γ (nSL 1))⁻¹ *
        S.D.step (rootSL2 τ L (w • γ) (nSL 1) * rootSL2 τ L γ (nSL 1)) =
      Hel γ v₁ * Hel (w • γ) v₂ := by
  have hr1 : IsRoot τ (w • γ) := (isRoot_smul_iff w).2 hγ
  have h01 := quad_form01 hw4 hγ
  obtain ⟨a1, ha1⟩ := S.step_nSL hFr hΦ hn hr1
  obtain ⟨a0, ha0⟩ := S.step_nSL hFr hΦ hn hγ
  obtain ⟨a, ha⟩ := rootSL2_neg_nSL (L := L) hγ
  have hF : S.D.step (rootSL2 τ L (w • γ) (nSL 1) * rootSL2 τ L γ (nSL 1)) =
      rootSL2 τ L γ (nSL (-(a * a1)⁻¹)) * rootSL2 τ L (w • γ) (nSL a0) := by
    rw [map_mul, ha1 1, ha0 1, one_pow, mul_one, mul_one, hw4 γ hγ, ha]
  have hH := rootSL2_nSL_inv_mul hτ hγ 1 (-(a * a1)⁻¹)
  have hH1 := rootSL2_nSL_inv_mul (L := L) hτ hr1 1 a0
  have hc : (rootSL2 τ L (w • γ) (nSL 1))⁻¹ * rootSL2 τ L γ (nSL (-(a * a1)⁻¹)) =
      rootSL2 τ L γ (nSL (-(a * a1)⁻¹)) * (rootSL2 τ L (w • γ) (nSL 1))⁻¹ := by
    rw [← map_inv]
    exact rootSL2_commute_of_orth' hτ hr1 hγ (by rw [iform_comm]; exact h01) _ _
  refine ⟨1 * (-(a * a1)⁻¹)⁻¹, 1 * a0⁻¹, ?_⟩
  rw [hF, ← hH, ← hH1]
  calc (rootSL2 τ L (w • γ) (nSL 1) * rootSL2 τ L γ (nSL 1))⁻¹ *
        (rootSL2 τ L γ (nSL (-(a * a1)⁻¹)) * rootSL2 τ L (w • γ) (nSL a0))
      = (rootSL2 τ L γ (nSL 1))⁻¹ * ((rootSL2 τ L (w • γ) (nSL 1))⁻¹ *
          rootSL2 τ L γ (nSL (-(a * a1)⁻¹))) * rootSL2 τ L (w • γ) (nSL a0) := by group
    _ = _ := by rw [hc]; group

theorem LangSetup.quad_nu {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    ∃ ν : ModGL τ L, ν ∈ rootSpan τ L (quadOrbit w γ) ∧ S.D.step ν = ν ∧
      ∀ (x : Fin τ.rank → ℤ) (u : Lˣ),
        ν * Hel x u * ν⁻¹ = Hel ((rootReflection (w • γ) * rootReflection γ) • x) u := by
  have hr1 : IsRoot τ (w • γ) := (isRoot_smul_iff w).2 hγ
  obtain ⟨v₁, v₂, hdef⟩ := S.quad_defect hFr hΦ hn hτ hw4 hγ
  obtain ⟨hsup1, hmon1, hmaps1⟩ := rootWeylOne_spec (K := L) hr1
  obtain ⟨hsup0, hmon0, hmaps0⟩ := rootWeylOne_spec (K := L) hγ
  have hshift : ∀ j : ℕ, (w ^ j) • (w • γ) = (w ^ (j + 1)) • γ := fun j => by
    rw [pow_succ, mul_smul]
  have hΘ1 : ∀ j : ℕ, (w ^ j) • (w • γ) ∈ quadOrbit w γ ∧ -((w ^ j) • (w • γ)) ∈ quadOrbit w γ :=
    fun j => by
      rw [hshift]
      exact ⟨⟨j + 1, rfl⟩, neg_mem_quadOrbit hw4 hγ (j + 1)⟩
  have hΘ0 : ∀ j : ℕ, (w ^ j) • γ ∈ quadOrbit w γ ∧ -((w ^ j) • γ) ∈ quadOrbit w γ :=
    fun j => ⟨⟨j, rfl⟩, neg_mem_quadOrbit hw4 hγ j⟩
  obtain ⟨b₁, b₁', hF₁, hb₁, hm₁⟩ := S.exists_lang_Hchar hFr hΦ hn hτ hγ
    (N := 4) (by norm_num) (pow_four_smul_quad hw4 hγ) v₁ hΘ0
  obtain ⟨b₂, b₂', hF₂, hb₂, hm₂⟩ := S.exists_lang_Hchar hFr hΦ hn hτ hr1
    (N := 4) (by norm_num) (pow_four_smul_quad hw4 hr1) v₂ hΘ1
  set N1 : ModGL τ L := rootSL2 τ L (w • γ) (nSL 1) with hN1
  set N0 : ModGL τ L := rootSL2 τ L γ (nSL 1) with hN0
  set s : ModGL τ L := rootDiagUnit τ (b₁ * b₂) with hs
  have hFs : S.D.step s = rootDiagUnit τ (b₁' * b₂') := by
    rw [hs, rootDiagUnit_mul, map_mul, hF₁, hF₂, rootDiagUnit_mul]
  have ht : Hel γ v₁ * Hel (w • γ) v₂ = s * (S.D.step s)⁻¹ := by
    unfold Hel
    rw [hFs, hs, rootDiagUnit_inv, ← rootDiagUnit_mul, ← rootDiagUnit_mul,
      ← hb₁, ← hb₂, mul_inv, mul_mul_mul_comm]
  have hN1m : N1 ∈ rootSpan τ L (quadOrbit w γ) := by
    have hsub : ({w • γ, -(w • γ)} : Set (Fin τ.rank → ℤ)) ⊆ quadOrbit w γ := by
      rintro x (rfl | rfl)
      · exact ⟨1, by simp⟩
      · have := neg_mem_quadOrbit hw4 hγ 1
        simpa using this
    exact rootSpan_mono hsub (rootSL2_mem_rootSpan_pair hr1 _)
  have hN0m : N0 ∈ rootSpan τ L (quadOrbit w γ) := by
    have hsub : ({γ, -γ} : Set (Fin τ.rank → ℤ)) ⊆ quadOrbit w γ := by
      rintro x (rfl | rfl)
      · exact ⟨0, by simp⟩
      · have := neg_mem_quadOrbit hw4 hγ 0
        simpa using this
    exact rootSpan_mono hsub (rootSL2_mem_rootSpan_pair hγ _)
  have hsm : s ∈ rootSpan τ L (quadOrbit w γ) := by
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

end QuadStep

@[expose] noncomputable def quadY {τ : Tag} {L : Type} [Field L] (w : WeylGroup τ) (q : ℕ)
    (γ : Fin τ.rank → ℤ) (ω : Lˣ) : Fin τ.rank → Lˣ :=
  Hchar γ ω * Hchar (w • γ) (ω ^ q)

section QuadStepY

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)
  {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ S.D.q) (hΦ : S.D.Φ = Units.map (entrywiseHom Fr))
  {w : WeylGroup τ} (hn : S.D.n = canonicalRep (coxeterSystem τ) L w)
  (hw4 : ∀ δ : Fin τ.rank → ℤ, IsRoot τ δ → w • w • δ = -δ)

include hFr hΦ hn hw4

theorem LangSetup.step_quadY {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (ω : Lˣ)
    (hω : ω ^ (S.D.q ^ 2 + 1) = 1) :
    S.D.step (rootDiagUnit τ (quadY w S.D.q γ ω)) = rootDiagUnit τ (quadY w S.D.q γ ω) := by
  have hst : ∀ (x : Fin τ.rank → ℤ) (u : Lˣ),
      S.D.step (rootDiagUnit τ (Hchar x u)) = rootDiagUnit τ (Hchar (w • x) (u ^ S.D.q)) :=
    fun x u => S.step_Hel hFr hΦ hn x u
  have hω2 : (ω ^ S.D.q) ^ S.D.q = ω⁻¹ := by
    rw [← pow_mul, ← sq]
    have : ω ^ S.D.q ^ 2 * ω = 1 := by rw [← pow_succ]; exact hω
    exact eq_inv_of_mul_eq_one_left this
  unfold quadY
  rw [rootDiagUnit_mul, map_mul, hst, hst, hw4 γ hγ, hω2, Hchar_neg, inv_inv, ← rootDiagUnit_mul,
    ← rootDiagUnit_mul]
  congr 1
  exact mul_comm _ _

end QuadStepY

section QuadY

variable {τ : Tag} {L : Type} [Field L] {w : WeylGroup τ}

theorem quadY_ne_one (hτ : SimplyLacedTag τ)
    (hw4 : ∀ δ : Fin τ.rank → ℤ, IsRoot τ δ → w • w • δ = -δ) (q p : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (ω : Lˣ) (hω : ω ^ p = 1)
    (hω1 : ω ≠ 1) : rootDiagUnit τ (quadY w q γ ω) ≠ 1 := by
  intro h
  have hY : quadY w q γ ω = 1 := by
    have : rootDiagUnit τ (quadY w q γ ω) = rootDiagUnit τ (1 : Fin τ.rank → Lˣ) := by
      rw [h, rootDiagUnit_one]
    exact CFSG.LieType.Chevalley.rootDiagUnit_injective this
  have hc : rootChar (quadY w q γ ω) γ = 1 := by rw [hY, rootChar_one']
  have hf1 : iform (w • γ) γ = 0 := by rw [iform_comm]; exact quad_form01 hw4 hγ
  unfold quadY at hc
  rw [rootChar_mul_tuple, rootChar_Hchar, rootChar_Hchar, iform_self_eq_two hτ hγ, hf1,
    zpow_zero, mul_one] at hc
  have hz : ω ^ (2 : ℕ) = 1 := by rw [← hc, zpow_ofNat]
  have : Fact p.Prime := ⟨hp⟩
  have hord : orderOf ω = p := orderOf_eq_prime hω hω1
  have h2 := orderOf_dvd_of_pow_eq_one hz
  rw [hord] at h2
  have := Nat.le_of_dvd (by norm_num) h2
  have := hp.two_le
  omega

theorem quadY_pow (q p : ℕ) (γ : Fin τ.rank → ℤ) (ω : Lˣ) (hω : ω ^ p = 1) :
    (rootDiagUnit τ (quadY w q γ ω)) ^ p = 1 := by
  rw [rootDiagUnit_pow, ← rootDiagUnit_one (τ := τ) (K := L)]
  congr 1
  unfold quadY
  have h1 : ∀ k : ℕ, (ω ^ k) ^ p = 1 := fun k => by
    rw [← pow_mul, mul_comm, pow_mul, hω, one_pow]
  rw [mul_pow, Hchar_pow_nat, Hchar_pow_nat, hω, h1]
  simp [Hchar_one']

theorem quadY_conj (hτ : SimplyLacedTag τ)
    (hw4 : ∀ δ : Fin τ.rank → ℤ, IsRoot τ δ → w • w • δ = -δ) (q p : ℕ) (hp : 1 ≤ p)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (ω : Lˣ) (hω : ω ^ p = 1) {ν : ModGL τ L}
    (hν : ∀ (x : Fin τ.rank → ℤ) (u : Lˣ),
      ν * Hel x u * ν⁻¹ = Hel ((rootReflection (w • γ) * rootReflection γ) • x) u) :
    ν * rootDiagUnit τ (quadY w q γ ω) * ν⁻¹ = (rootDiagUnit τ (quadY w q γ ω)) ^ (p - 1) := by
  have hr1 : IsRoot τ (w • γ) := (isRoot_smul_iff w).2 hγ
  have h01 := quad_form01 hw4 hγ
  have hc0 : (rootReflection (w • γ) * rootReflection γ) • γ = -γ := by
    rw [mul_smul, rootReflection_smul_self hγ, smul_neg, rootReflection_smul_sl hτ hr1,
      iform_comm, h01, zero_smul, sub_zero]
  have hc1 : (rootReflection (w • γ) * rootReflection γ) • (w • γ) = -(w • γ) := by
    rw [mul_smul, rootReflection_smul_sl hτ hγ, h01, zero_smul, sub_zero,
      rootReflection_smul_self hr1]
  have hconj : ν * rootDiagUnit τ (quadY w q γ ω) * ν⁻¹ =
      (rootDiagUnit τ (quadY w q γ ω))⁻¹ := by
    have e : rootDiagUnit τ (quadY w q γ ω) = Hel γ ω * Hel (w • γ) (ω ^ q) := by
      unfold quadY Hel
      rw [rootDiagUnit_mul]
    calc ν * rootDiagUnit τ (quadY w q γ ω) * ν⁻¹
        = (ν * Hel γ ω * ν⁻¹) * (ν * Hel (w • γ) (ω ^ q) * ν⁻¹) := by rw [e]; group
      _ = _ := by
        rw [hν, hν, hc0, hc1, e]
        unfold Hel
        rw [Hchar_neg, Hchar_neg, ← rootDiagUnit_mul, ← rootDiagUnit_mul, rootDiagUnit_inv,
          mul_inv, Hchar_inv_quad, Hchar_inv_quad, mul_comm]
  have hpow := quadY_pow (w := w) q p γ ω hω
  rw [hconj]
  refine (eq_inv_of_mul_eq_one_left ?_).symm
  rw [← pow_succ, Nat.sub_add_cancel hp, hpow]

end QuadY

section QuadMem

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {w : WeylGroup τ}

theorem Hel_mem_rootSpan_quadOrbit (hτ : SimplyLacedTag τ)
    (hw4 : ∀ δ : Fin τ.rank → ℤ, IsRoot τ δ → w • w • δ = -δ) {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) (j : ℕ) (u : Lˣ) :
    Hel ((w ^ j) • γ) u ∈ rootSpan τ L (quadOrbit w γ) := by
  have hr : IsRoot τ ((w ^ j) • γ) := (isRoot_smul_iff _).2 hγ
  have hsub : ({(w ^ j) • γ, -((w ^ j) • γ)} : Set (Fin τ.rank → ℤ)) ⊆ quadOrbit w γ := by
    rintro x (rfl | rfl)
    · exact ⟨j, rfl⟩
    · exact neg_mem_quadOrbit hw4 hγ j
  exact rootSpan_mono hsub (Hel_root_mem_rootSpan hτ hr u)

end QuadMem

section QuadMain

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)
  {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ S.D.q) (hΦ : S.D.Φ = Units.map (entrywiseHom Fr))
  {w : WeylGroup τ} (hn : S.D.n = canonicalRep (coxeterSystem τ) L w)

include hFr hΦ hn

theorem quadOrbit_subset_rationalRoots {a : Fin τ.rank → Lˣ}
    (i : KernelComponent (rootCharHom a)) {γ : Fin τ.rank → ℤ}
    (hγ : γ ∈ componentRoots (rootCharHom a) i) (hγr : IsRoot τ γ) :
    quadOrbit w γ ⊆ rationalRoots S.ρ (rootCharHom a) i := by
  have key : ∀ j : ℕ, ((S.ρ : (Fin τ.rank → ℤ) → _)^[j] γ) = (w ^ j) • γ := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Function.iterate_succ_apply', ih, S.rho_eq_smul_of_frob hFr hΦ hn
        ((isRoot_smul_iff _).2 hγr), pow_succ', mul_smul]
  rintro x ⟨j, rfl⟩
  exact ⟨j, γ, hγ, (key j).symm⟩

variable (hτ : SimplyLacedTag τ)
  (hw4 : ∀ δ : Fin τ.rank → ℤ, IsRoot τ δ → w • w • δ = -δ)

include hτ hw4

theorem bigAnyPBig_of_phi4_of_ne_two (hp2 : p ≠ 2) (hMΓ : S.D.model ≤ S.Γ) : BigAnyPBig S := by
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
  have h2' : rootChar a' (w • w • γ) = ω⁻¹ := by
    rw [hw4 γ hγ, rootChar_neg_tri]
  have hω1 : ω ≠ 1 := hχa'
  have hωq : ω ^ (q ^ 2 + 1) = 1 := by
    rw [pow_succ, ← h2, h2', inv_mul_cancel]
  have hk : ¬ (p : ℤ) ∣ ((p - 1 : ℕ) : ℤ) - 1 := by
    intro h
    have e1 : ((p - 1 : ℕ) : ℤ) - 1 = p - 2 := by
      push_cast [Nat.cast_sub hp.one_lt.le]
      ring
    rw [e1] at h
    have h2 : (p : ℤ) ∣ 2 := by
      have := dvd_sub (dvd_refl (p : ℤ)) h
      simpa using this
    have : p ∣ 2 := by exact_mod_cast h2
    have := Nat.le_of_dvd (by norm_num) this
    have := hp.two_le
    omega
  obtain ⟨ν, hνm, hνF, hνc⟩ := S.quad_nu hFr hΦ hn hτ hw4 hγ
  have hΘ := quadOrbit_subset_rationalRoots S hFr hΦ hn i hγi hγ
  have hy : rootDiagUnit τ (quadY w q γ ω) ∈ rootSpan τ L (quadOrbit w γ) := by
    unfold quadY
    rw [rootDiagUnit_mul]
    refine mul_mem ?_ ?_
    · have h := Hel_mem_rootSpan_quadOrbit (L := L) hτ hw4 hγ 0 ω
      rw [pow_zero, one_smul] at h
      exact h
    · have h := Hel_mem_rootSpan_quadOrbit (L := L) hτ hw4 hγ 1 (ω ^ q)
      rw [pow_one] at h
      exact h
  exact not_coprime_of_commutator_pair S hMΓ i hΘ hy (S.step_quadY hFr hΦ hn hw4 hγ ω hωq)
    (quadY_pow q p γ ω hωp) (quadY_ne_one hτ hw4 q p hp hp2 hγ ω hωp hω1) hνm hνF
    (quadY_conj hτ hw4 q p hp.one_lt.le hγ ω hωp hνc) hk

end QuadMain

end CFSG.HardMathSupport.Timmesfeld.LangTorus
