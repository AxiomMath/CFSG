module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZQ22
public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZQ23
public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZL8

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.LieType.BorelTits CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Lang.D4Three
  CFSG.RankThree.PartTwo.Census.Carrier.D4Even


section Aux

variable {K : Type} [Field K] [Finite K]

theorem coe_diagAut (a : Fin Tag.D4.rank → Kˣ) (h : adjointGroup Tag.D4 K) :
    ((diagAut a h : adjointGroup Tag.D4 K) : ModGL Tag.D4 K) =
      rootDiagUnit Tag.D4 a * (h : ModGL Tag.D4 K) * (rootDiagUnit Tag.D4 a)⁻¹ := by
  unfold diagAut
  rw [coe_exactNormalAut_zero]
  have : Units.map (entrywiseHom (1 : K ≃+* K).toRingHom) (h : ModGL Tag.D4 K) =
      (h : ModGL Tag.D4 K) := Units.ext (entrywise_id _)
  rw [this]

theorem rootDiagUnit_conj_mem_adjointGroup (a : Fin Tag.D4.rank → Kˣ) {y : ModGL Tag.D4 K}
    (hy : y ∈ adjointGroup Tag.D4 K) :
    rootDiagUnit Tag.D4 a * y * (rootDiagUnit Tag.D4 a)⁻¹ ∈ adjointGroup Tag.D4 K := by
  have h := (diagAut a (⟨y, hy⟩ : adjointGroup Tag.D4 K)).2
  have e := coe_diagAut a (⟨y, hy⟩ : adjointGroup Tag.D4 K)
  rw [e] at h
  exact h

theorem rootDiagUnit_inv' (a : Fin Tag.D4.rank → Kˣ) :
    rootDiagUnit Tag.D4 a⁻¹ = (rootDiagUnit Tag.D4 (K := K) a)⁻¹ :=
  eq_inv_of_mul_eq_one_right (by rw [← rootDiagUnit_mul, mul_inv_cancel, rootDiagUnit_one])

theorem c_mem_parabolic {J : Set (Fin Tag.D4.rank)} {Γ c : ModGL Tag.D4 K}
    (hc : c ∈ adjointGroup Tag.D4 K) {a : Fin Tag.D4.rank → Kˣ}
    (hΓ : Γ = c * rootDiagUnit Tag.D4 a)
    (hVΓ : ∀ x ∈ adjointGroup Tag.D4 K,
      Γ * x * Γ⁻¹ ∈ parabolicRadical Tag.D4 K J ↔ x ∈ parabolicRadical Tag.D4 K J) :
    c ∈ parabolicSubgroup Tag.D4 K J := by
  rw [← adjointGroup_inf_normalizer_parabolicRadical (K := K) J]
  refine Subgroup.mem_inf.2 ⟨hc, ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro q
  have hQC : ∀ y, y ∈ parabolicRadical Tag.D4 K J → y ∈ adjointGroup Tag.D4 K := fun y hy =>
    posUnipotent_le_adjointGroup (parabolicRadical_le_posUnipotent J hy)
  have e : ∀ y : ModGL Tag.D4 K, c * y * c⁻¹ =
      Γ * ((rootDiagUnit Tag.D4 a)⁻¹ * y * rootDiagUnit Tag.D4 a) * Γ⁻¹ := by
    intro y
    rw [hΓ]
    group
  constructor
  · intro hq
    have hq0 : (rootDiagUnit Tag.D4 a)⁻¹ * q * rootDiagUnit Tag.D4 a ∈
        parabolicRadical Tag.D4 K J := by
      have := rootDiagUnit_conj_radical (K := K) (J := J) a⁻¹ hq
      rwa [rootDiagUnit_inv', inv_inv] at this
    rw [e]
    exact (hVΓ _ (hQC _ hq0)).2 hq0
  · intro hq
    rw [e] at hq
    have hqC : q ∈ adjointGroup Tag.D4 K := by
      have h1 : Γ * ((rootDiagUnit Tag.D4 a)⁻¹ * q * rootDiagUnit Tag.D4 a) * Γ⁻¹ ∈
          adjointGroup Tag.D4 K := hQC _ hq
      have h2 : c * q * c⁻¹ ∈ adjointGroup Tag.D4 K := by rw [e]; exact h1
      have := mul_mem (mul_mem (inv_mem hc) h2) hc
      simpa [mul_assoc] using this
    have hq0C : (rootDiagUnit Tag.D4 a)⁻¹ * q * rootDiagUnit Tag.D4 a ∈
        adjointGroup Tag.D4 K := by
      have := rootDiagUnit_conj_mem_adjointGroup (K := K) a⁻¹ hqC
      rwa [rootDiagUnit_inv', inv_inv] at this
    have hq0 := (hVΓ _ hq0C).1 hq
    have := rootDiagUnit_conj_radical (K := K) (J := J) a hq0
    simpa [mul_assoc] using this

end Aux

section Chev

variable {K : Type} [Field K] [Finite K] [CharP K 3]

local instance : NeZero Tag.D4.rank := ⟨by decide⟩

theorem levi_chev {n : ℕ} (hK : Nat.card K = 3 ^ n) {g : ModGL Tag.D4 K}
    (hg : g ∈ borelGroup Tag.D4 K) {a : Fin Tag.D4.rank → Kˣ} {σ : K ≃+* K} {ε : ℕ}
    (hε : ε = 1 ∨ ε = 2)
    (hφ3 : ∀ x ∈ adjointGroup Tag.D4 K,
      phiG g a σ ε (phiG g a σ ε (phiG g a σ ε x)) = x)
    (hφC : ∀ x ∈ adjointGroup Tag.D4 K, phiG g a σ ε x ∈ adjointGroup Tag.D4 K)
    {Γ₁ Γ₂ c₁ c₂ : ModGL Tag.D4 K} {a₁ a₂ : Fin Tag.D4.rank → Kˣ}
    (hc₁ : c₁ ∈ adjointGroup Tag.D4 K) (hc₂ : c₂ ∈ adjointGroup Tag.D4 K)
    (hΓ₁ : Γ₁ = c₁ * rootDiagUnit Tag.D4 a₁) (hΓ₂ : Γ₂ = c₂ * rootDiagUnit Tag.D4 a₂)
    (sq₁ : ∀ x ∈ adjointGroup Tag.D4 K, Γ₁ * Γ₁ * x * (Γ₁ * Γ₁)⁻¹ = x)
    (sq₂ : ∀ x ∈ adjointGroup Tag.D4 K, Γ₂ * Γ₂ * x * (Γ₂ * Γ₂)⁻¹ = x)
    (comm : ∀ x ∈ adjointGroup Tag.D4 K,
      Γ₁ * (Γ₂ * x * Γ₂⁻¹) * Γ₁⁻¹ = Γ₂ * (Γ₁ * x * Γ₁⁻¹) * Γ₂⁻¹)
    (rel₁ : ∀ x ∈ adjointGroup Tag.D4 K,
      phiG g a σ ε (Γ₁ * x * Γ₁⁻¹) = Γ₂ * phiG g a σ ε x * Γ₂⁻¹)
    (rel₂ : ∀ x ∈ adjointGroup Tag.D4 K,
      phiG g a σ ε (Γ₂ * x * Γ₂⁻¹) = (Γ₁ * Γ₂) * phiG g a σ ε x * (Γ₁ * Γ₂)⁻¹)
    (hne₁ : ∃ x ∈ adjointGroup Tag.D4 K, Γ₁ * x * Γ₁⁻¹ ≠ x)
    {Vm : Subgroup (ModGL Tag.D4 K)} (hVC : Vm ≤ adjointGroup Tag.D4 K) (hVp : IsPGroup 3 Vm)
    (hB : borelGroup Tag.D4 K ≤
      adjointGroup Tag.D4 K ⊓ Subgroup.normalizer (Vm : Set (ModGL Tag.D4 K)))
    (hne : adjointGroup Tag.D4 K ⊓ Subgroup.normalizer (Vm : Set (ModGL Tag.D4 K)) ≠
      adjointGroup Tag.D4 K)
    (hVc : pCoreOf 3 (adjointGroup Tag.D4 K ⊓ Subgroup.normalizer (Vm : Set (ModGL Tag.D4 K))) = Vm)
    (hVφ : ∀ x ∈ Vm, phiG g a σ ε x ∈ Vm)
    (hVΓ₁ : ∀ x ∈ adjointGroup Tag.D4 K, Γ₁ * x * Γ₁⁻¹ ∈ Vm ↔ x ∈ Vm)
    (hVΓ₂ : ∀ x ∈ adjointGroup Tag.D4 K, Γ₂ * x * Γ₂⁻¹ ∈ Vm ↔ x ∈ Vm)
    (hVU : Vm ≠ posUnipotent Tag.D4 K)
    {A : Subgroup (ModGL Tag.D4 K)} (hAV : A ≤ Vm) (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hA₁ : ∀ a ∈ A, Γ₁ * a * Γ₁⁻¹ = a) (hA₂ : ∀ a ∈ A, Γ₂ * a * Γ₂⁻¹ = a)
    (hbig : 3 ^ (4 * n) ≤ 3 * Nat.card A) : False := by
  haveI := finite_modGL (τ := Tag.D4) (K := K)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Pm := adjointGroup Tag.D4 K ⊓ Subgroup.normalizer (Vm : Set (ModGL Tag.D4 K)) with hPmdef
  have hAC : Pm ≤ adjointGroup Tag.D4 K := inf_le_left
  have hφA : ∀ x ∈ Pm, phiG g a σ ε x ∈ Pm := by
    intro x hx
    obtain ⟨hxC, hxN⟩ := Subgroup.mem_inf.1 hx
    refine Subgroup.mem_inf.2 ⟨hφC x hxC, ?_⟩
    rw [Subgroup.mem_normalizer_iff] at hxN ⊢
    intro h
    by_cases hhC : h ∈ adjointGroup Tag.D4 K
    · have hφ2C : phiG g a σ ε (phiG g a σ ε h) ∈ adjointGroup Tag.D4 K := hφC _ (hφC _ hhC)
      constructor
      · intro hh
        have h1 : phiG g a σ ε (phiG g a σ ε h) ∈ Vm := hVφ _ (hVφ _ hh)
        have h2 := (hxN _).1 h1
        have h3 := hVφ _ h2
        have e : phiG g a σ ε (x * phiG g a σ ε (phiG g a σ ε h) * x⁻¹) =
            phiG g a σ ε x * h * (phiG g a σ ε x)⁻¹ := by
          rw [map_mul, map_mul, map_inv, hφ3 h hhC]
        rwa [e] at h3
      · intro hh
        have h1 := hVφ _ (hVφ _ hh)
        have e : phiG g a σ ε (phiG g a σ ε (phiG g a σ ε x * h * (phiG g a σ ε x)⁻¹)) =
            x * phiG g a σ ε (phiG g a σ ε h) * x⁻¹ := by
          rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, hφ3 x hxC]
        rw [e] at h1
        have h2 := (hxN _).2 h1
        have h3 := hVφ _ h2
        rwa [hφ3 h hhC] at h3
    · constructor
      · intro hh; exact absurd (hVC hh) hhC
      · intro hh
        have h1 : phiG g a σ ε x * h * (phiG g a σ ε x)⁻¹ ∈ adjointGroup Tag.D4 K := hVC hh
        have := mul_mem (mul_mem (inv_mem (hφC x hxC)) h1) (hφC x hxC)
        exact absurd (by simpa [mul_assoc] using this) hhC
  have hAP := eq_parabolicSubgroup_of_borelGroup_le hB hAC
  have hcells := standard_parabolic_cells Tag.D4 K
  set J : Set (Fin Tag.D4.rank) := {i | weylElt Tag.D4 K i 1 ∈ Pm} with hJ
  have hfwd : ∀ i, i ∈ J → (d4Rho ^ ε) i ∈ J := fun i hi => jstable hg a σ ε hB hφA hi
  have hJρ : ∀ i, i ∈ J ↔ (d4Rho ^ ε) i ∈ J := fun i =>
    ⟨hfwd i, fun h => by
      have := hfwd _ (hfwd _ h)
      rwa [rho_pow_thrice] at this⟩
  have hVQ : ∀ J' : Set (Fin Tag.D4.rank), Pm = parabolicSubgroup Tag.D4 K J' →
      Vm = parabolicRadical Tag.D4 K J' := by
    intro J' hPJ
    have h := hVc
    rw [hPJ, pCoreOf_parabolicSubgroup_three] at h
    exact h.symm
  have main : ∀ J' : Set (Fin Tag.D4.rank),
      (J' = ({2} : Set (Fin Tag.D4.rank)) ∨ J' = ({0, 1, 3} : Set (Fin Tag.D4.rank))) →
      Pm = parabolicSubgroup Tag.D4 K J' → (∀ i, i ∈ J' ↔ (d4Rho ^ ε) i ∈ J') → False := by
    intro J' hJ' hPJ hJ'ρ
    have hVQ' := hVQ J' hPJ
    have hc₁P : c₁ ∈ parabolicSubgroup Tag.D4 K J' :=
      c_mem_parabolic hc₁ hΓ₁ (fun x hx => by rw [← hVQ']; exact hVΓ₁ x hx)
    have hc₂P : c₂ ∈ parabolicSubgroup Tag.D4 K J' :=
      c_mem_parabolic hc₂ hΓ₂ (fun x hx => by rw [← hVQ']; exact hVΓ₂ x hx)
    have n₁ : NormAll J' Γ₁ := by
      rw [hΓ₁]; exact (NormAll.of_parabolic hc₁P).mul (NormAll.of_rootDiagUnit _)
    have n₂ : NormAll J' Γ₂ := by
      rw [hΓ₂]; exact (NormAll.of_parabolic hc₂P).mul (NormAll.of_rootDiagUnit _)
    have G : A4Grp J' (phiG g a σ ε) Γ₁ Γ₂ :=
      ⟨fun d x hx => phi_degSeries_le hg a σ hJ'ρ d x hx, hφ3, n₁, n₂, sq₁, sq₂, comm, rel₁, rel₂⟩
    exact core_levi hK hJ' G hc₁P hc₂P hΓ₁ hΓ₂ hne₁ (by rw [← hVQ']; exact hAV) hAc hA₁ hA₂ hbig
  rcases jclass hε hJρ with h0 | h2 | h013 | huniv
  ·
    have hPJ : Pm = parabolicSubgroup Tag.D4 K ∅ := by rw [hAP, h0]
    have := hVQ ∅ hPJ
    rw [parabolicRadical_empty_three] at this
    exact hVU this
  · have hPJ : Pm = parabolicSubgroup Tag.D4 K ({2} : Set (Fin Tag.D4.rank)) := by rw [hAP, h2]
    exact main {2} (Or.inl rfl) hPJ (by rw [h2] at hJρ; exact hJρ)
  · have hPJ : Pm = parabolicSubgroup Tag.D4 K ({0, 1, 3} : Set (Fin Tag.D4.rank)) := by
      rw [hAP, h013]
    exact main {0, 1, 3} (Or.inr rfl) hPJ (by rw [h013] at hJρ; exact hJρ)
  · apply hne
    rw [hAP, huniv]
    exact hcells.2.2.2.2.2.1

end Chev

end CFSG.LocalAnalysis.GLTheoremA
