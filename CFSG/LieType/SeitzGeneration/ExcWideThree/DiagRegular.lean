module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.DiagAssembly
public import CFSG.LieType.SeitzGeneration.ExcWideThree.DiagNonElliptic
public import CFSG.LieType.SeitzGeneration.ExcWideThree.DiagLift
public import CFSG.LieType.SeitzGeneration.ExcWideThree.DiagFinMain

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.LieType.SeitzGeneration CFSG.LieType.SeitzGeneration.ExcOuterLeOne
  CFSG.RankThree.PartOne.CTP CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Lang.E6Descent CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Open
  CFSG.AGLEmbeddingD2 CFSG.Fischer TauCeti CFSG.LieType.SeitzGeneration.ExcHighThree
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups

section Regular


theorem e6InndiagGL_le_adjoint_of_cubes (K : Type) [Field K]
    (hc : ∀ c : Kˣ, ∃ u : Kˣ, u ^ 3 = c) : e6InndiagGL K ≤ adjointGroup Tag.E6 K := by
  refine sup_le le_rfl ?_
  rintro _ ⟨a, rfl⟩
  exact rootDiagUnit_mem_adjointGroup_of_roots fun j => by
    obtain ⟨u, hu⟩ := hc (a j)
    exact ⟨u, by rw [det_cartan_E6, show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast]; exact hu⟩

theorem units_cube_of_not_dvd (K : Type) [Field K] [Finite K] (h : ¬ 3 ∣ Nat.card K - 1) :
    ∀ c : Kˣ, ∃ u : Kˣ, u ^ 3 = c := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hcard : Nat.card Kˣ = Nat.card K - 1 := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_units]
  have hcop : Nat.Coprime (Nat.card Kˣ) 3 := by
    rw [hcard]
    exact (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h))
  intro c
  refine ⟨(powCoprime hcop).symm c, ?_⟩
  have := (powCoprime hcop).apply_symm_apply c
  simpa using this

theorem langGL_rootChar_frob_reg {K : Type} [Field K] [Finite K] {A : Subgroup (ModGL Tag.E6 K)}
    (D : LangGLData Tag.E6 K A) {y : ModGL Tag.E6 K}
    (a : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ)
    (ha : rootDiagUnit Tag.E6 a = D.g0⁻¹ *
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (D.c * y * D.c⁻¹) * D.g0)
    (v : Fin Tag.E6.rank → ℤ) : rootChar a (D.w • v) = rootChar a v ^ Nat.card K := by
  classical
  obtain ⟨e, he, hcard⟩ := card_eq_pow_ringChar K
  haveI : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K (ringChar K)⟩
  have hFrEq : D.Fr = iterateFrobenius (AlgebraicClosure K) (ringChar K) e :=
    RingHom.ext fun c => by rw [D.hFr c, iterateFrobenius_def, hcard]
  have hFrob : ∀ g : ModGL Tag.E6 (AlgebraicClosure K),
      Units.map (entrywiseHom D.Fr) g =
        entrywiseFrobGL Tag.E6 (AlgebraicClosure K) (ringChar K) e g := by
    intro g
    rw [hFrEq]
  have hg0F : entrywiseFrobGL Tag.E6 (AlgebraicClosure K) (ringChar K) e D.g0 =
      D.g0 * canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) D.w := by
    rw [← hFrob]
    exact D.hg0
  have hBF : ∀ z : ModGL Tag.E6 K, entrywiseFrobGL Tag.E6 (AlgebraicClosure K) (ringChar K) e
      (baseChangeGL (algebraMap K (AlgebraicClosure K)) z) =
      baseChangeGL (algebraMap K (AlgebraicClosure K)) z := by
    intro z
    rw [← hFrob]
    exact CFSG.RankThree.PartOne.KE.baseChangeGL_frobenius_fixed D.Fr D.hFr z
  have hF : entrywiseFrobGL Tag.E6 (AlgebraicClosure K) (ringChar K) e (rootDiagUnit Tag.E6 a) =
      (canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) D.w)⁻¹ *
        rootDiagUnit Tag.E6 a * canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) D.w := by
    rw [ha, map_mul, map_mul, map_inv, hg0F, hBF]
    group
  have hconj : rootDiagUnit Tag.E6 a =
      canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) D.w *
        entrywiseFrobGL Tag.E6 (AlgebraicClosure K) (ringChar K) e (rootDiagUnit Tag.E6 a) *
        (canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) D.w)⁻¹ := by
    rw [hF]
    group
  have h := rootChar_frob_of_conj (p := ringChar K) (e := e) a D.w hconj v
  rw [hcard]
  exact h

theorem rootChar_pow_exp {L : Type} [Field L] (ω : Lˣ) (k : Fin Tag.E6.rank → ℕ)
    (v : Fin Tag.E6.rank → ℤ) :
    rootChar (fun i => ω ^ k i) v = ω ^ (∑ i, (k i : ℤ) * v i) := by
  unfold rootChar
  rw [← liftProd_zpow_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  show (ω ^ k i) ^ v i = _
  rw [← zpow_natCast, ← zpow_mul]

theorem langGL_fix_exp {K : Type} [Field K] [Finite K] (hq : Nat.card K % 3 = 1)
    {A : Subgroup (ModGL Tag.E6 K)} (D : LangGLData Tag.E6 K A)
    (ω : (AlgebraicClosure K)ˣ) (hω : IsPrimitiveRoot (ω : AlgebraicClosure K) 3)
    {y : ModGL Tag.E6 K} (k : Fin Tag.E6.rank → ℕ)
    (ha : rootDiagUnit Tag.E6 (fun i => ω ^ k i) = D.g0⁻¹ *
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (D.c * y * D.c⁻¹) * D.g0)
    (v : Fin Tag.E6.rank → ℤ) :
    (3 : ℤ) ∣ (∑ i, (k i : ℤ) * (D.w • v) i) - ∑ i, (k i : ℤ) * v i := by
  have h := langGL_rootChar_frob_reg D _ ha v
  rw [rootChar_pow_exp, rootChar_pow_exp, ← zpow_natCast, ← zpow_mul] at h
  have h1 : ω ^ ((∑ i, (k i : ℤ) * (D.w • v) i) -
      (∑ i, (k i : ℤ) * v i) * (Nat.card K : ℤ)) = 1 := by
    rw [zpow_sub, h, mul_inv_cancel]
  have hωu : IsPrimitiveRoot ω 3 := IsPrimitiveRoot.coe_units_iff.1 hω
  have h2 := (hωu.zpow_eq_one_iff_dvd _).1 h1
  obtain ⟨t, ht⟩ : ∃ t : ℕ, Nat.card K = 3 * t + 1 := ⟨Nat.card K / 3, by omega⟩
  rw [ht] at h2
  push_cast at h2
  have h3 : (∑ i, (k i : ℤ) * (D.w • v) i) - ∑ i, (k i : ℤ) * v i =
      ((∑ i, (k i : ℤ) * (D.w • v) i) - (∑ i, (k i : ℤ) * v i) * (3 * (t : ℤ) + 1)) +
        3 * ((∑ i, (k i : ℤ) * v i) * (t : ℤ)) := by ring
  rw [h3]
  exact dvd_add h2 (dvd_mul_right _ _)

theorem langGL_kills_of_pair {K : Type} [Field K] [Finite K] {A : Subgroup (ModGL Tag.E6 K)}
    (D : LangGLData Tag.E6 K A) (ω : (AlgebraicClosure K)ˣ) (hω3 : ω ^ 3 = 1)
    {y₁ y₂ : ModGL Tag.E6 K} (hgen : Subgroup.closure ({y₁, y₂} : Set (ModGL Tag.E6 K)) = A)
    (k₁ k₂ : Fin Tag.E6.rank → ℕ)
    (ha₁ : rootDiagUnit Tag.E6 (fun i => ω ^ k₁ i) = D.g0⁻¹ *
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (D.c * y₁ * D.c⁻¹) * D.g0)
    (ha₂ : rootDiagUnit Tag.E6 (fun i => ω ^ k₂ i) = D.g0⁻¹ *
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (D.c * y₂ * D.c⁻¹) * D.g0)
    {α : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α)
    (h₁ : (3 : ℤ) ∣ ∑ i, α i * (k₁ i : ℤ)) (h₂ : (3 : ℤ) ∣ ∑ i, α i * (k₂ i : ℤ)) :
    D.Kills α := by
  have hr₁ : rootChar (fun i => ω ^ k₁ i) α = 1 := rootChar_eq_one_of_dvd hω3 (fun i => rfl) h₁
  have hr₂ : rootChar (fun i => ω ^ k₂ i) α = 1 := rootChar_eq_one_of_dvd hω3 (fun i => rfl) h₂
  set Sg : Subgroup (ModGL Tag.E6 K) :=
    ((rootCharHom (τ := Tag.E6) (L := AlgebraicClosure K) α).ker.map
      (rootDiagUnitHom Tag.E6 (AlgebraicClosure K))).comap (diagMapGL D) with hSg
  have hker : ∀ a : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ, rootChar a α = 1 →
      a ∈ (rootCharHom (τ := Tag.E6) (L := AlgebraicClosure K) α).ker :=
    fun a h => MonoidHom.mem_ker.2 (show rootCharHom (τ := Tag.E6) (L := AlgebraicClosure K) α a = 1
      from h)
  have hmem : ∀ (x : ModGL Tag.E6 K) (a : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ),
      rootDiagUnit Tag.E6 a = D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (D.c * x * D.c⁻¹ : ModGL Tag.E6 K) * D.g0 → rootChar a α = 1 → x ∈ Sg := by
    intro x a hax hr
    refine Subgroup.mem_comap.2 (Subgroup.mem_map.2 ⟨a, hker a hr, ?_⟩)
    rw [diagMapGL_apply]
    exact hax
  have hy₁S : y₁ ∈ Sg := hmem y₁ _ ha₁ hr₁
  have hy₂S : y₂ ∈ Sg := hmem y₂ _ ha₂ hr₂
  have hAS : A ≤ Sg := by
    rw [← hgen]
    refine (Subgroup.closure_le Sg).2 ?_
    intro z hz
    rcases hz with rfl | rfl
    · exact hy₁S
    · exact hy₂S
  intro y hy
  obtain ⟨a, ha, hay⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 (hAS hy))
  refine ⟨a, ?_, ?_⟩
  · rw [diagMapGL_apply] at hay
    exact hay
  · exact (show rootCharHom (τ := Tag.E6) (L := AlgebraicClosure K) α a = 1 from
      MonoidHom.mem_ker.1 ha)

theorem e6DiagRegularOuter_of_dichotomy
    (hdich : ∀ (w : WeylGroup Tag.E6) (k₁ k₂ : Fin Tag.E6.rank → ℕ),
      (∀ α : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 α →
        ¬ ((3 : ℤ) ∣ ∑ i, α i * (k₁ i : ℤ) ∧ (3 : ℤ) ∣ ∑ i, α i * (k₂ i : ℤ))) →
      (∀ t : Fin Tag.E6.rank, (3 : ℤ) ∣
        (∑ i, (k₁ i : ℤ) * (w • (Pi.single t 1 : Fin Tag.E6.rank → ℤ)) i) - (k₁ t : ℤ)) →
      (∀ t : Fin Tag.E6.rank, (3 : ℤ) ∣
        (∑ i, (k₂ i : ℤ) * (w • (Pi.single t 1 : Fin Tag.E6.rank → ℤ)) i) - (k₂ t : ℤ)) →
      (∃ l : Fin Tag.E6.rank → ℤ, l ≠ 0 ∧
          ∀ v : Fin Tag.E6.rank → ℤ, ∑ i, l i * (w • v) i = ∑ i, l i * v i) ∨
        ∃ m₁ m₂ : Fin Tag.E6.rank → ℤ,
          (∀ j, (3 : ℤ) ∣ (∑ l, Tag.E6.cartan l j * m₁ l) - (k₁ j : ℤ)) ∧
          (∀ j, (3 : ℤ) ∣ (∑ l, Tag.E6.cartan l j * m₂ l) - (k₂ j : ℤ)) ∧
          (∀ i, (3 : ℤ) ∣ (w • m₁) i - m₁ i) ∧ (∀ i, (3 : ℤ) ∣ (w • m₂) i - m₂ i)) :
    E6DiagRegularOuter := by
  intro K _ _ hK3 E hE hEab hcard D hnok hout
  classical
  obtain ⟨x, hx, hxout⟩ := hout
  have hAle : ∀ y ∈ e6PlanePre K E, y ∈ e6InndiagGL K := fun y hy => by
    obtain ⟨g, rfl, -⟩ := (mem_e6PlanePre_iff K E y).1 hy
    exact g.2
  have h3 : 3 ∣ Nat.card K - 1 := by
    by_contra hnd
    exact hxout (e6InndiagGL_le_adjoint_of_cubes K (units_cube_of_not_dvd K hnd) (hAle x hx))
  have hK2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hq : Nat.card K % 3 = 1 := by omega
  have hK4 : 4 ≤ Nat.card K := by omega
  haveI : CFSG.IsElementaryAbelian 3 E := hEab
  have hAcard : Nat.card (e6PlanePre K E) = 3 ^ 2 := by rw [card_e6PlanePre K hK4 E hE, hcard]
  have hexp : ∀ y ∈ e6PlanePre K E, y ^ 3 = 1 := fun y hy =>
    pow_three_eq_one_of_mem_e6PlanePre K hK4 E hy
  have hx3 := hexp x hx
  have hx1 : x ≠ 1 := fun h => hxout (h ▸ one_mem _)
  obtain ⟨y₂, hy₂, hy₂n⟩ := exists_mem_not_mem_zpowers (e6PlanePre K E) hAcard hx hx3 hx1
  have hgen : Subgroup.closure ({x, y₂} : Set (ModGL Tag.E6 K)) = e6PlanePre K E :=
    closure_pair_eq_of_not_mem (e6PlanePre K E) hAcard hx hy₂ hx3 hx1 hy₂n
  obtain ⟨ω, hω⟩ := exists_primCubeRoot K hK3
  have hω3 : ω ^ 3 = 1 := Units.ext (by simpa using hω.pow_eq_one)
  obtain ⟨a₁, ha₁, k₁, hk₁⟩ := langGL_diag_exponent D ω hω hx hx3
  obtain ⟨a₂, ha₂, k₂, hk₂⟩ := langGL_diag_exponent D ω hω hy₂ (hexp y₂ hy₂)
  obtain rfl : a₁ = fun i => ω ^ k₁ i := funext hk₁
  obtain rfl : a₂ = fun i => ω ^ k₂ i := funext hk₂
  have hreg : ∀ α : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 α →
      ¬ ((3 : ℤ) ∣ ∑ i, α i * (k₁ i : ℤ) ∧ (3 : ℤ) ∣ ∑ i, α i * (k₂ i : ℤ)) := by
    rintro α hα ⟨h1, h2⟩
    exact hnok ⟨α, hα, langGL_kills_of_pair D ω hω3 hgen k₁ k₂ ha₁ ha₂ hα h1 h2⟩
  have hfix : ∀ (y : ModGL Tag.E6 K) (k : Fin Tag.E6.rank → ℕ),
      rootDiagUnit Tag.E6 (fun i => ω ^ k i) = D.g0⁻¹ *
        baseChangeGL (algebraMap K (AlgebraicClosure K)) (D.c * y * D.c⁻¹) * D.g0 →
      ∀ t : Fin Tag.E6.rank, (3 : ℤ) ∣
        (∑ i, (k i : ℤ) * (D.w • (Pi.single t 1 : Fin Tag.E6.rank → ℤ)) i) - (k t : ℤ) := by
    intro y k hy t
    have h := langGL_fix_exp hq D ω hω k hy (Pi.single t 1)
    simpa [Pi.single_apply] using h
  have hAnorm : e6PlanePre K E ≤
      Subgroup.normalizer (adjointGroup Tag.E6 K : Set (ModGL Tag.E6 K)) :=
    fun y hy => e6InndiagGL_le_normalizer K (hAle y hy)
  rcases hdich D.w k₁ k₂ hreg (hfix x k₁ ha₁) (hfix y₂ k₂ ha₂) with
    ⟨l, hl, hlfix⟩ | ⟨m₁, m₂, hm₁, hm₂, hw₁, hw₂⟩
  ·
    obtain ⟨R, hRad, hR1, hRp, hRn⟩ :=
      exists_normalized_rGroup_of_fixed hK3 hAnorm D l hl hlfix
    refine ⟨R.comap (adjointGroup Tag.E6 K).subtype, ?_, ?_, ?_⟩
    · intro hbot
      apply hR1
      rw [eq_bot_iff]
      intro z hz
      have hz' : (⟨z, hRad hz⟩ : adjointGroup Tag.E6 K) ∈ R.comap (adjointGroup Tag.E6 K).subtype :=
        hz
      rw [hbot, Subgroup.mem_bot] at hz'
      exact (Subgroup.mem_bot).2 (congrArg Subtype.val hz')
    · intro g
      obtain ⟨n, hn⟩ := hRp (⟨(g : adjointGroup Tag.E6 K).1, g.2⟩ : R)
      have hpow : ((g : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) ^ (ringChar K ^ n) = 1 :=
        congrArg Subtype.val hn
      refine ⟨n, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      exact hpow
    · intro ε hε
      have hεr : ε ∈ (e6InndiagConj K).range := by
        rw [range_e6InndiagConj]
        exact hE hε
      obtain ⟨g, rfl⟩ := hεr
      have hgA : (g : ModGL Tag.E6 K) ∈ e6PlanePre K E := (mem_e6PlanePre_iff K E _).2 ⟨g, rfl, hε⟩
      have hgA' : (g : ModGL Tag.E6 K)⁻¹ ∈ e6PlanePre K E := inv_mem hgA
      ext z
      constructor
      · rintro ⟨u, hu, rfl⟩
        show ((e6InndiagConj K g u : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) ∈ R
        rw [e6InndiagConj_apply]
        exact hRn _ hgA _ hu
      · intro hz
        refine ⟨e6InndiagConj K g⁻¹ z, ?_, ?_⟩
        · show ((e6InndiagConj K g⁻¹ z : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) ∈ R
          rw [e6InndiagConj_apply]
          have := hRn _ hgA' _ hz
          simpa using this
        · change (e6InndiagConj K g) (e6InndiagConj K g⁻¹ z) = z
          rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
  ·
    exact absurd (mem_adjointGroup_of_classZero hq D ω hω hx k₁ ha₁ m₁ hm₁ hw₁) hxout

theorem e6DiagRegularOuter_holds : E6DiagRegularOuter :=
  e6DiagRegularOuter_of_dichotomy fun w k₁ k₂ => e6_regular_dichotomy w k₁ k₂

end Regular

end CFSG.LieType.SeitzGeneration.ExcWideThree
