module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyHex

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LieType.AlgebraicGroups

set_option linter.unusedSectionVars false


section TriData

variable {τ : Tag} {w : WeylGroup τ}

theorem iform_neg_right_tri (x y : Fin τ.rank → ℤ) : iform x (-y) = -iform x y := by
  have := iform_smul_right (τ := τ) (-1) x y
  simpa using this

theorem rootChar_neg_tri {L : Type} [Field L] (a : Fin τ.rank → Lˣ) (x : Fin τ.rank → ℤ) :
    rootChar a (-x) = (rootChar a x)⁻¹ := by
  rw [← zero_sub, rootChar_sub, rootChar_zero, one_mul]

theorem tri_form01 (hτ : SimplyLacedTag τ)
    (hw3 : ∀ δ : Fin τ.rank → ℤ, IsRoot τ δ → w • w • δ = -(w • δ) - δ) {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) : iform γ (w • γ) = -1 := by
  have h1 : iform (w • γ) (w • w • γ) = iform γ (w • γ) := iform_smul w γ (w • γ)
  rw [hw3 γ hγ, iform_sub_right, iform_neg_right_tri, iform_comm (w • γ) γ,
    iform_self_eq_two hτ ((isRoot_smul_iff w).2 hγ)] at h1
  omega

theorem tri_w3 (hw3 : ∀ δ : Fin τ.rank → ℤ, IsRoot τ δ → w • w • δ = -(w • δ) - δ)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) : w • w • w • γ = γ := by
  rw [hw3 γ hγ, smul_sub, smul_neg, hw3 γ hγ]
  abel

@[expose] def triOrbit (w : WeylGroup τ) (γ : Fin τ.rank → ℤ) : Set (Fin τ.rank → ℤ) :=
  {x | ∃ j : ℕ, x = (w ^ j) • γ ∨ x = -((w ^ j) • γ)}

theorem pow_three_smul_tri (hw3 : ∀ δ : Fin τ.rank → ℤ, IsRoot τ δ → w • w • δ = -(w • δ) - δ)
    {δ : Fin τ.rank → ℤ} (hδ : IsRoot τ δ) : (w ^ 3) • δ = δ := by
  rw [show (w ^ 3) • δ = w • w • w • δ by simp [pow_succ, mul_smul], tri_w3 hw3 hδ]

theorem tri_refl10 (hτ : SimplyLacedTag τ)
    (hw3 : ∀ δ : Fin τ.rank → ℤ, IsRoot τ δ → w • w • δ = -(w • δ) - δ) {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) : rootReflection (w • γ) • γ = -(w • w • γ) := by
  rw [rootReflection_smul_sl hτ ((isRoot_smul_iff w).2 hγ), iform_comm, tri_form01 hτ hw3 hγ,
    hw3 γ hγ]
  simp only [neg_smul, one_smul, sub_neg_eq_add, neg_sub, sub_neg_eq_add]

theorem tri_form12 (hτ : SimplyLacedTag τ)
    (hw3 : ∀ δ : Fin τ.rank → ℤ, IsRoot τ δ → w • w • δ = -(w • δ) - δ) {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) : iform (w • γ) (w • w • γ) = -1 := by
  rw [hw3 γ hγ, iform_sub_right, iform_neg_right_tri, iform_comm (w • γ) γ, tri_form01 hτ hw3 hγ,
    iform_self_eq_two hτ ((isRoot_smul_iff w).2 hγ)]
  norm_num

theorem tri_refl12 (hτ : SimplyLacedTag τ)
    (hw3 : ∀ δ : Fin τ.rank → ℤ, IsRoot τ δ → w • w • δ = -(w • δ) - δ) {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) : rootReflection (w • γ) • (w • w • γ) = -γ := by
  rw [rootReflection_smul_sl hτ ((isRoot_smul_iff w).2 hγ), tri_form12 hτ hw3 hγ, hw3 γ hγ]
  simp only [neg_smul, one_smul, sub_neg_eq_add]
  abel

end TriData

section TriStep

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)
  {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ S.D.q) (hΦ : S.D.Φ = Units.map (entrywiseHom Fr))
  {w : WeylGroup τ} (hn : S.D.n = canonicalRep (coxeterSystem τ) L w)
  (hτ : SimplyLacedTag τ)
  (hw3 : ∀ δ : Fin τ.rank → ℤ, IsRoot τ δ → w • w • δ = -(w • δ) - δ)

include hFr hΦ hn hτ hw3

theorem LangSetup.tri_defect {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    ∃ v₁ v₂ : Lˣ,
      (rootSL2 τ L (w • γ) (nSL 1) * rootSL2 τ L γ (nSL 1))⁻¹ *
        S.D.step (rootSL2 τ L (w • γ) (nSL 1) * rootSL2 τ L γ (nSL 1)) =
      Hel (-γ) v₁ * Hel (w • γ) v₂ := by
  have hr1 : IsRoot τ (w • γ) := (isRoot_smul_iff w).2 hγ
  have hr2 : IsRoot τ (w • w • γ) := (isRoot_smul_iff w).2 hr1
  obtain ⟨a1, ha1⟩ := S.step_nSL hFr hΦ hn hr1
  obtain ⟨a0, ha0⟩ := S.step_nSL hFr hΦ hn hγ
  obtain ⟨-, hmon, hmaps⟩ := rootWeylOne_spec (K := L) hr1
  obtain ⟨s, hs⟩ := conj_rootSL2_nSL hmon hmaps hγ (tri_refl10 hτ hw3 hγ)
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
  have hrefl2 : (rootReflection (w • γ))⁻¹ • (w • w • γ) = -γ := by
    rw [rootReflection_inv hr1, tri_refl12 hτ hw3 hγ]
  have hconjH : ∀ v : Lˣ, (rootSL2 τ L (w • γ) (nSL 1))⁻¹ * Hel (w • w • γ) v *
      ((rootSL2 τ L (w • γ) (nSL 1))⁻¹)⁻¹ = Hel (-γ) v := fun v => by
    have := conj_Hel (L := L) (n := (rootSL2 τ L (w • γ) (nSL 1))⁻¹) (inv_mem hmon) hmaps.inv
      (w • w • γ) v
    rw [this, hrefl2]
  refine ⟨(-(a * (s * 1))⁻¹) * a1⁻¹, 1 * a0⁻¹, ?_⟩
  rw [hF, hconj, ← hconjH ((-(a * (s * 1))⁻¹) * a1⁻¹), ← hH, ← hH1]
  group

theorem LangSetup.tri_nu {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    ∃ ν : ModGL τ L, ν ∈ rootSpan τ L (triOrbit w γ) ∧ S.D.step ν = ν ∧
      ∀ (x : Fin τ.rank → ℤ) (u : Lˣ),
        ν * Hel x u * ν⁻¹ = Hel ((rootReflection (w • γ) * rootReflection γ) • x) u := by
  have hr1 : IsRoot τ (w • γ) := (isRoot_smul_iff w).2 hγ
  obtain ⟨v₁, v₂, hdef⟩ := S.tri_defect hFr hΦ hn hτ hw3 hγ
  obtain ⟨hsup1, hmon1, hmaps1⟩ := rootWeylOne_spec (K := L) hr1
  obtain ⟨hsup0, hmon0, hmaps0⟩ := rootWeylOne_spec (K := L) hγ
  have hshift : ∀ j : ℕ, (w ^ j) • (w • γ) = (w ^ (j + 1)) • γ := fun j => by
    rw [pow_succ, mul_smul]
  have hΘ1 : ∀ j : ℕ, (w ^ j) • (w • γ) ∈ triOrbit w γ ∧ -((w ^ j) • (w • γ)) ∈ triOrbit w γ :=
    fun j => by
      rw [hshift]
      exact ⟨⟨j + 1, Or.inl rfl⟩, ⟨j + 1, Or.inr rfl⟩⟩
  have hΘ0 : ∀ j : ℕ, (w ^ j) • (-γ) ∈ triOrbit w γ ∧ -((w ^ j) • (-γ)) ∈ triOrbit w γ :=
    fun j => by
      rw [smul_neg, neg_neg]
      exact ⟨⟨j, Or.inr rfl⟩, ⟨j, Or.inl rfl⟩⟩
  have h3neg : (w ^ 3) • (-γ) = -γ := by rw [smul_neg, pow_three_smul_tri hw3 hγ]
  obtain ⟨b₁, b₁', hF₁, hb₁, hm₁⟩ := S.exists_lang_Hchar hFr hΦ hn hτ (IsRoot.neg hγ)
    (N := 3) (by norm_num) h3neg v₁ hΘ0
  obtain ⟨b₂, b₂', hF₂, hb₂, hm₂⟩ := S.exists_lang_Hchar hFr hΦ hn hτ hr1
    (N := 3) (by norm_num) (pow_three_smul_tri hw3 hr1) v₂ hΘ1
  set N1 : ModGL τ L := rootSL2 τ L (w • γ) (nSL 1) with hN1
  set N0 : ModGL τ L := rootSL2 τ L γ (nSL 1) with hN0
  set s : ModGL τ L := rootDiagUnit τ (b₁ * b₂) with hs
  have hFs : S.D.step s = rootDiagUnit τ (b₁' * b₂') := by
    rw [hs, rootDiagUnit_mul, map_mul, hF₁, hF₂, rootDiagUnit_mul]
  have ht : Hel (-γ) v₁ * Hel (w • γ) v₂ = s * (S.D.step s)⁻¹ := by
    unfold Hel
    rw [hFs, hs, rootDiagUnit_inv, ← rootDiagUnit_mul, ← rootDiagUnit_mul,
      ← hb₁, ← hb₂, mul_inv, mul_mul_mul_comm]
  have hN1m : N1 ∈ rootSpan τ L (triOrbit w γ) := by
    have hsub : ({w • γ, -(w • γ)} : Set (Fin τ.rank → ℤ)) ⊆ triOrbit w γ := by
      rintro x (rfl | rfl)
      · exact ⟨1, Or.inl (by simp)⟩
      · exact ⟨1, Or.inr (by simp)⟩
    exact rootSpan_mono hsub (rootSL2_mem_rootSpan_pair hr1 _)
  have hN0m : N0 ∈ rootSpan τ L (triOrbit w γ) := by
    have hsub : ({γ, -γ} : Set (Fin τ.rank → ℤ)) ⊆ triOrbit w γ := by
      rintro x (rfl | rfl)
      · exact ⟨0, Or.inl (by simp)⟩
      · exact ⟨0, Or.inr (by simp)⟩
    exact rootSpan_mono hsub (rootSL2_mem_rootSpan_pair hγ _)
  have hsm : s ∈ rootSpan τ L (triOrbit w γ) := by
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

theorem LangSetup.step_triY {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (ω : Lˣ)
    (hω : ω ^ S.D.q ^ 3 = ω) :
    S.D.step (rootDiagUnit τ (hexY w S.D.q γ ω)) = rootDiagUnit τ (hexY w S.D.q γ ω) := by
  have hst : ∀ (x : Fin τ.rank → ℤ) (u : Lˣ),
      S.D.step (rootDiagUnit τ (Hchar x u)) = rootDiagUnit τ (Hchar (w • x) (u ^ S.D.q)) :=
    fun x u => S.step_Hel hFr hΦ hn x u
  have h3 : (w • w • w • γ) = γ := tri_w3 hw3 hγ
  have hω3 : (ω ^ S.D.q ^ 2) ^ S.D.q = ω := by
    rw [← pow_mul, ← pow_succ]
    exact hω
  unfold hexY
  rw [rootDiagUnit_mul, rootDiagUnit_mul, map_mul, map_mul, hst, hst, hst, h3, hω3, ← pow_mul]
  rw [show S.D.q * S.D.q = S.D.q ^ 2 from (sq _).symm, ← rootDiagUnit_mul, ← rootDiagUnit_mul,
    ← rootDiagUnit_mul, ← rootDiagUnit_mul]
  congr 1
  ac_rfl

end TriStep

section TriY

variable {τ : Tag} {L : Type} [Field L] {w : WeylGroup τ}

theorem triY_ne_one (hτ : SimplyLacedTag τ)
    (hw3 : ∀ δ : Fin τ.rank → ℤ, IsRoot τ δ → w • w • δ = -(w • δ) - δ) (q p : ℕ) (hp : p.Prime)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (ω : Lˣ) (hω : ω ^ p = 1) (hω1 : ω ≠ 1)
    (hE : ¬ (p : ℤ) ∣ 2 - (q : ℤ) - (q : ℤ) ^ 2) : rootDiagUnit τ (hexY w q γ ω) ≠ 1 := by
  intro h
  have hY : hexY w q γ ω = 1 := by
    have : rootDiagUnit τ (hexY w q γ ω) = rootDiagUnit τ (1 : Fin τ.rank → Lˣ) := by
      rw [h, rootDiagUnit_one]
    exact CFSG.LieType.Chevalley.rootDiagUnit_injective this
  have hc : rootChar (hexY w q γ ω) γ = 1 := by rw [hY, rootChar_one']
  have h01 := tri_form01 hτ hw3 hγ
  have hf1 : iform (w • γ) γ = -1 := by rw [iform_comm]; exact h01
  have hf2 : iform (w • w • γ) γ = -1 := by
    rw [hw3 γ hγ, iform_sub_left, iform_neg_left', hf1, iform_self_eq_two hτ hγ]
    norm_num
  unfold hexY at hc
  rw [rootChar_mul_tuple, rootChar_mul_tuple, rootChar_Hchar, rootChar_Hchar, rootChar_Hchar,
    iform_self_eq_two hτ hγ, hf1, hf2] at hc
  have hz : ω ^ ((2 : ℤ) - q - (q : ℤ) ^ 2) = 1 := by
    rw [← hc, zpow_sub, zpow_sub, zpow_neg_one, zpow_neg_one, ← Nat.cast_pow, zpow_natCast,
      zpow_natCast]
  have : Fact p.Prime := ⟨hp⟩
  have hord : orderOf ω = p := orderOf_eq_prime hω hω1
  exact hE (hord ▸ orderOf_dvd_iff_zpow_eq_one.2 hz)

theorem triY_conj (hτ : SimplyLacedTag τ)
    (hw3 : ∀ δ : Fin τ.rank → ℤ, IsRoot τ δ → w • w • δ = -(w • δ) - δ) (q : ℕ)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (ω : Lˣ) (hω : ω ^ q ^ 3 = ω) {ν : ModGL τ L}
    (hν : ∀ (x : Fin τ.rank → ℤ) (u : Lˣ),
      ν * Hel x u * ν⁻¹ = Hel ((rootReflection (w • γ) * rootReflection γ) • x) u) :
    ν * rootDiagUnit τ (hexY w q γ ω) * ν⁻¹ = (rootDiagUnit τ (hexY w q γ ω)) ^ q := by
  have hr1 : IsRoot τ (w • γ) := (isRoot_smul_iff w).2 hγ
  have h01 := tri_form01 hτ hw3 hγ
  have hr2eq := hw3 γ hγ
  have hc0 : (rootReflection (w • γ) * rootReflection γ) • γ = w • w • γ := by
    rw [mul_smul, rootReflection_smul_self hγ, smul_neg, tri_refl10 hτ hw3 hγ, neg_neg]
  have hc1 : (rootReflection (w • γ) * rootReflection γ) • (w • γ) = γ := by
    rw [mul_smul, rootReflection_smul_sl hτ hγ, h01,
      show w • γ - (-1 : ℤ) • γ = w • γ + γ by simp, smul_add, rootReflection_smul_self hr1,
      tri_refl10 hτ hw3 hγ, hr2eq]
    abel
  have hc2 : (rootReflection (w • γ) * rootReflection γ) • (w • w • γ) = w • γ := by
    have hf : iform γ (w • w • γ) = -1 := by
      rw [hr2eq, iform_sub_right, iform_neg_right_tri, h01, iform_self_eq_two hτ hγ]
      norm_num
    rw [mul_smul, rootReflection_smul_sl hτ hγ, hf, hr2eq,
      show -(w • γ) - γ - (-1 : ℤ) • γ = -(w • γ) by simp, smul_neg,
      rootReflection_smul_self hr1, neg_neg]
  have hconj : ν * rootDiagUnit τ (hexY w q γ ω) * ν⁻¹ = rootDiagUnit τ
      (Hchar (w • w • γ) ω * Hchar γ (ω ^ q) * Hchar (w • γ) (ω ^ q ^ 2)) := by
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
  unfold hexY
  rw [mul_pow, mul_pow, Hchar_pow_nat, Hchar_pow_nat, Hchar_pow_nat, ← pow_mul, ← pow_mul,
    show q * q = q ^ 2 by ring, show q ^ 2 * q = q ^ 3 by ring, hω]
  ac_rfl

end TriY

section TriMem

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {w : WeylGroup τ}

theorem Hel_mem_rootSpan_triOrbit (hτ : SimplyLacedTag τ) {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) (j : ℕ) (u : Lˣ) :
    Hel ((w ^ j) • γ) u ∈ rootSpan τ L (triOrbit w γ) := by
  have hr : IsRoot τ ((w ^ j) • γ) := (isRoot_smul_iff _).2 hγ
  have hsub : ({(w ^ j) • γ, -((w ^ j) • γ)} : Set (Fin τ.rank → ℤ)) ⊆ triOrbit w γ := by
    rintro x (rfl | rfl)
    · exact ⟨j, Or.inl rfl⟩
    · exact ⟨j, Or.inr rfl⟩
  exact rootSpan_mono hsub (Hel_root_mem_rootSpan hτ hr u)

end TriMem

section TriMain

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)
  {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ S.D.q) (hΦ : S.D.Φ = Units.map (entrywiseHom Fr))
  {w : WeylGroup τ} (hn : S.D.n = canonicalRep (coxeterSystem τ) L w)

include hFr hΦ hn

theorem triOrbit_subset_rationalRoots {a : Fin τ.rank → Lˣ} (i : KernelComponent (rootCharHom a))
    {γ : Fin τ.rank → ℤ} (hγ : γ ∈ componentRoots (rootCharHom a) i) (hγr : IsRoot τ γ) :
    triOrbit w γ ⊆ rationalRoots S.ρ (rootCharHom a) i := by
  have key : ∀ δ : Fin τ.rank → ℤ, IsRoot τ δ → ∀ j : ℕ,
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[j] δ) = (w ^ j) • δ := by
    intro δ hδ j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Function.iterate_succ_apply', ih, S.rho_eq_smul_of_frob hFr hΦ hn
        ((isRoot_smul_iff _).2 hδ), pow_succ', mul_smul]
  have hneg : -γ ∈ componentRoots (rootCharHom a) i :=
    (isRootComponent_componentRoots i).neg_mem γ hγ
  rintro x ⟨j, rfl | rfl⟩
  · exact ⟨j, γ, hγ, (key γ hγr j).symm⟩
  · refine ⟨j, -γ, hneg, ?_⟩
    rw [key (-γ) (IsRoot.neg hγr) j, smul_neg]

variable (hτ : SimplyLacedTag τ)
  (hw3 : ∀ δ : Fin τ.rank → ℤ, IsRoot τ δ → w • w • δ = -(w • δ) - δ)

include hτ hw3

theorem bigAnyPBig_of_phi3 (hp7 : 7 ≤ p) (hMΓ : S.D.model ≤ S.Γ) : BigAnyPBig S := by
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
  have h2' : rootChar a' (w • w • γ) = (rootChar a' (w • γ))⁻¹ * ω⁻¹ := by
    rw [hw3 γ hγ, rootChar_sub, rootChar_neg_tri]
  have hω1 : ω ≠ 1 := hχa'
  have hord : orderOf ω = p := by
    have : Fact p.Prime := ⟨hp⟩
    exact orderOf_eq_prime hωp hω1
  have hq2 : (p : ℤ) ∣ (q : ℤ) ^ 2 + q + 1 := by
    have hz : ω ^ (((q : ℤ) ^ 2 + q + 1)) = 1 := by
      have : ω ^ q ^ 2 = (ω ^ q)⁻¹ * ω⁻¹ := by rw [← h2, h2', h1]
      rw [zpow_add, zpow_add, zpow_one, ← Nat.cast_pow, zpow_natCast, zpow_natCast, this]
      group
    exact hord ▸ orderOf_dvd_iff_zpow_eq_one.2 hz
  have hp3 : ¬ (p : ℤ) ∣ 3 := by
    intro h
    have : p ∣ 3 := by exact_mod_cast h
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have hE : ¬ (p : ℤ) ∣ 2 - (q : ℤ) - (q : ℤ) ^ 2 := by
    intro h
    apply hp3
    have : (3 : ℤ) = (2 - (q : ℤ) - (q : ℤ) ^ 2) + ((q : ℤ) ^ 2 + q + 1) := by ring
    rw [this]
    exact dvd_add h hq2
  have hk : ¬ (p : ℤ) ∣ (q : ℤ) - 1 := by
    intro h
    apply hp3
    have : (3 : ℤ) = ((q : ℤ) ^ 2 + q + 1) - ((q : ℤ) - 1) * ((q : ℤ) + 2) := by ring
    rw [this]
    exact dvd_sub hq2 (dvd_mul_of_dvd_left h _)
  have hωq : ω ^ q ^ 3 = ω := by
    have h := unit_zpow_eq_of_dvd ω hωp (e := ((q ^ 3 : ℕ) : ℤ)) (e' := 1) (by
      have : (((q ^ 3 : ℕ) : ℤ) - 1) = ((q : ℤ) - 1) * ((q : ℤ) ^ 2 + q + 1) := by
        push_cast
        ring
      rw [this]
      exact dvd_mul_of_dvd_right hq2 _)
    rwa [zpow_natCast, zpow_one] at h
  obtain ⟨ν, hνm, hνF, hνc⟩ := S.tri_nu hFr hΦ hn hτ hw3 hγ
  have hΘ := triOrbit_subset_rationalRoots S hFr hΦ hn i hγi hγ
  have hy : rootDiagUnit τ (hexY w q γ ω) ∈ rootSpan τ L (triOrbit w γ) := by
    unfold hexY
    rw [rootDiagUnit_mul, rootDiagUnit_mul]
    refine mul_mem (mul_mem ?_ ?_) ?_
    · have h := Hel_mem_rootSpan_triOrbit (w := w) (L := L) hτ hγ 0 ω
      rw [pow_zero, one_smul] at h
      exact h
    · have h := Hel_mem_rootSpan_triOrbit (w := w) (L := L) hτ hγ 1 (ω ^ q)
      rw [pow_one] at h
      exact h
    · have h := Hel_mem_rootSpan_triOrbit (w := w) (L := L) hτ hγ 2 (ω ^ q ^ 2)
      rw [pow_two, mul_smul] at h
      exact h
  exact not_coprime_of_commutator_pair S hMΓ i hΘ hy (S.step_triY hFr hΦ hn hτ hw3 hγ ω hωq)
    (hexY_pow q p γ ω hωp) (triY_ne_one hτ hw3 q p hp hγ ω hωp hω1 hE) hνm hνF
    (triY_conj hτ hw3 q hγ ω hωq hνc) hk

end TriMain

end CFSG.HardMathSupport.Timmesfeld.LangTorus
