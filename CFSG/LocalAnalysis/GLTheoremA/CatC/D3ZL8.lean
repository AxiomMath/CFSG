module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZL7
public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3PLayer2
public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3FLayer

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Lang.D4Three
  CFSG.RankThree.PartTwo.Census.Carrier.D4Even
open scoped Pointwise


section NormalForm

variable {K : Type} [Field K] [Finite K]

theorem exists_normal_form_borel (α : MulAut ↥(adjointGroup Tag.D4 K)) (hα3 : α ^ 3 = 1)
    (hU : (unitU K).map α.toMonoidHom = unitU K) :
    ∃ (g : ↥(adjointGroup Tag.D4 K)) (a : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K) (ε : ℕ), ε < 3 ∧
      α = MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε) ∧
      (g : ModGL Tag.D4 K) ∈ borelGroup Tag.D4 K := by
  classical
  have hH : unitU K = (posUnipotent Tag.D4 K).subgroupOf (adjointGroup Tag.D4 K) := rfl
  have hmemH : ∀ y : ↥(adjointGroup Tag.D4 K), y ∈ unitU K ↔
      (y : ModGL Tag.D4 K) ∈ posUnipotent Tag.D4 K :=
    fun y => by rw [hH, Subgroup.mem_subgroupOf]
  obtain ⟨g, a, σ, ε, hε3, hσ3, hαeq⟩ := exists_cube_normal_form_sigma α hα3
  have hνA : (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε) ∈ unipotentPairAut Tag.D4 K :=
    mul_mem (exactNormalAut_mem a σ 0) (d4Graph_mem ε)
  have hνH : (unitU K).map (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε).toMonoidHom = unitU K := by
    rw [hH]; exact hνA.1
  have hgeq : MulAut.conj g = α * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε)⁻¹ := by
    rw [hαeq]; group
  have hgH : (unitU K).map (MulAut.conj g).toMonoidHom = unitU K := by
    rw [hgeq, map_toMonoidHom_mul_mulAut, map_inv_toMonoidHom_of_map_eq hνH, hU]
  have hgH' : (unitU K).map (MulAut.conj g)⁻¹.toMonoidHom = unitU K :=
    map_inv_toMonoidHom_of_map_eq hgH
  have hnorm : (g : ModGL Tag.D4 K) ∈
      Subgroup.normalizer (posUnipotent Tag.D4 K : Set (ModGL Tag.D4 K)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hxG : x ∈ adjointGroup Tag.D4 K := posUnipotent_le_adjointGroup hx
      have hmem : (⟨x, hxG⟩ : ↥(adjointGroup Tag.D4 K)) ∈ unitU K := (hmemH _).2 hx
      have h1 : (MulAut.conj g) ⟨x, hxG⟩ ∈ (unitU K).map (MulAut.conj g).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hmem
      rw [hgH] at h1
      exact (hmemH _).1 h1
    · intro hx
      have hxG' : (g : ModGL Tag.D4 K) * x * (g : ModGL Tag.D4 K)⁻¹ ∈ adjointGroup Tag.D4 K :=
        posUnipotent_le_adjointGroup hx
      have hxG : x ∈ adjointGroup Tag.D4 K := by
        have := mul_mem (mul_mem (inv_mem g.2) hxG') g.2
        simpa [mul_assoc] using this
      have hmem : (⟨(g : ModGL Tag.D4 K) * x * (g : ModGL Tag.D4 K)⁻¹, hxG'⟩ :
          ↥(adjointGroup Tag.D4 K)) ∈ unitU K := (hmemH _).2 hx
      have h1 : (MulAut.conj g)⁻¹ ⟨_, hxG'⟩ ∈ (unitU K).map (MulAut.conj g)⁻¹.toMonoidHom :=
        Subgroup.mem_map_of_mem _ hmem
      rw [hgH'] at h1
      have e : (MulAut.conj g)⁻¹ (⟨(g : ModGL Tag.D4 K) * x * (g : ModGL Tag.D4 K)⁻¹, hxG'⟩ :
          ↥(adjointGroup Tag.D4 K)) = ⟨x, hxG⟩ := by
        apply Subtype.ext
        simp [MulAut.conj_apply, mul_assoc]
      rw [e] at h1
      exact (hmemH _).1 h1
  have hgB : (g : ModGL Tag.D4 K) ∈ borelGroup Tag.D4 K := by
    rw [← CFSG.Quasithin.H13.NQCat.LieCartan.G2.normalizer_posUnipotent_inf_eq
      (K := K) (τ := Tag.D4)]
    exact ⟨hnorm, g.2⟩
  exact ⟨g, a, σ, ε, hε3, hαeq, hgB⟩

theorem coe_alpha_eq_phiG {α : MulAut ↥(adjointGroup Tag.D4 K)} {g : ↥(adjointGroup Tag.D4 K)}
    {a : Fin Tag.D4.rank → Kˣ} {σ : K ≃+* K} {ε : ℕ}
    (hα : α = MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε))
    (x : ↥(adjointGroup Tag.D4 K)) :
    ((α x : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) =
      phiG (g : ModGL Tag.D4 K) a σ ε (x : ModGL Tag.D4 K) := by
  rw [hα]; rfl

theorem phiG_cube {α : MulAut ↥(adjointGroup Tag.D4 K)} {g : ↥(adjointGroup Tag.D4 K)}
    {a : Fin Tag.D4.rank → Kˣ} {σ : K ≃+* K} {ε : ℕ}
    (hα : α = MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε)) (hα3 : α ^ 3 = 1)
    {x : ModGL Tag.D4 K} (hx : x ∈ adjointGroup Tag.D4 K) :
    phiG (g : ModGL Tag.D4 K) a σ ε (phiG (g : ModGL Tag.D4 K) a σ ε
      (phiG (g : ModGL Tag.D4 K) a σ ε x)) = x := by
  have h3 := congrArg (fun φ : MulAut ↥(adjointGroup Tag.D4 K) =>
    ((φ ⟨x, hx⟩ : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K)) hα3
  simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.one_apply] at h3
  rw [coe_alpha_eq_phiG hα, coe_alpha_eq_phiG hα, coe_alpha_eq_phiG hα] at h3
  exact h3

theorem phiG_mem_adjoint {α : MulAut ↥(adjointGroup Tag.D4 K)} {g : ↥(adjointGroup Tag.D4 K)}
    {a : Fin Tag.D4.rank → Kˣ} {σ : K ≃+* K} {ε : ℕ}
    (hα : α = MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε))
    {x : ModGL Tag.D4 K} (hx : x ∈ adjointGroup Tag.D4 K) :
    phiG (g : ModGL Tag.D4 K) a σ ε x ∈ adjointGroup Tag.D4 K := by
  have := (α ⟨x, hx⟩).2
  rwa [coe_alpha_eq_phiG hα] at this

end NormalForm

section Stable

variable {K : Type} [Field K] [Finite K]

theorem d4F_injective (a : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K) (ε : ℕ) :
    Function.Injective (d4F K a σ ε) := by
  intro u v huv
  have := congrArg (fun y => (MulAut.conj (d4P K ^ ε))⁻¹
    ((exactNormalAutGL Tag.D4 K a σ 0)⁻¹ y)) huv
  simpa [d4F] using this

theorem exists_d4F_pinnedX_ne (a : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K) (ε : ℕ) :
    ∃ e : (Fin Tag.D4.rank → ℤ) → K, (∀ γ, IsRoot Tag.D4 γ → e γ ≠ 0) ∧
      ∀ γ, IsRoot Tag.D4 γ → ∀ c : K, d4F K a σ ε (pinnedX Tag.D4 K γ c) =
        pinnedX Tag.D4 K (permLattice (d4Rho ^ ε) γ) (e γ * σ c) := by
  obtain ⟨e, he⟩ := exists_d4F_pinnedX (K := K) a σ ε
  refine ⟨e, fun γ hγ h => ?_, he⟩
  have h2 := he γ hγ 1
  rw [map_one, mul_one, h, pinnedX_zero] at h2
  have h3 : pinnedX Tag.D4 K γ 1 = pinnedX Tag.D4 K γ 0 := by
    rw [pinnedX_zero]
    exact d4F_injective a σ ε (h2.trans (map_one _).symm)
  exact one_ne_zero (pinnedX_injective Tag.D4 K γ h3)

theorem xUnit_mem_borel (j : Fin Tag.D4.rank) (c : K) :
    xUnit Tag.D4 K j c ∈ borelGroup Tag.D4 K := xUnit_mem_borelGroup j c

theorem torusElt_mem_borel (j : Fin Tag.D4.rank) (t : Kˣ) :
    torusElt Tag.D4 K j t ∈ borelGroup Tag.D4 K :=
  Subgroup.mem_sup_left (Subgroup.subset_closure ⟨(j, t), rfl⟩)

theorem jstable {g : ModGL Tag.D4 K} (hg : g ∈ borelGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ)
    (σ : K ≃+* K) (ε : ℕ) {A : Subgroup (ModGL Tag.D4 K)} (hB : borelGroup Tag.D4 K ≤ A)
    (hφA : ∀ x ∈ A, phiG g a σ ε x ∈ A) {i : Fin Tag.D4.rank}
    (hi : weylElt Tag.D4 K i 1 ∈ A) : weylElt Tag.D4 K ((d4Rho ^ ε) i) 1 ∈ A := by
  obtain ⟨e, he0, he⟩ := exists_d4F_pinnedX_ne (K := K) a σ ε
  set j := (d4Rho ^ ε) i with hj
  have hx : ∀ c : K, d4F K a σ ε (xUnit Tag.D4 K i c) =
      xUnit Tag.D4 K j (e (Pi.single i 1) * σ c) := by
    intro c
    rw [← pinnedX_single, he _ (isRoot_single Tag.D4 i), permLattice_single, pinnedX_single]
  have hy : ∀ c : K, d4F K a σ ε (yUnit Tag.D4 K i c) =
      yUnit Tag.D4 K j (e (-Pi.single i 1) * σ c) := by
    intro c
    have h1 : permLattice (d4Rho ^ ε) (-Pi.single i 1 : Fin Tag.D4.rank → ℤ) =
        -Pi.single j 1 := by
      rw [← permLattice_single]; rfl
    rw [← pinnedX_neg_single, he _ (isRoot_neg_single Tag.D4 i), h1, pinnedX_neg_single]
  set e₁ := e (Pi.single i 1) with he₁
  set e₂ := e (-Pi.single i 1) with he₂
  have he₂0 : e₂ ≠ 0 := he0 _ (isRoot_neg_single Tag.D4 i)
  have hn : weylElt Tag.D4 K i 1 = xUnit Tag.D4 K i 1 * yUnit Tag.D4 K i (-1) * xUnit Tag.D4 K i 1 := by
    rw [CFSG.Blueprint.Chevalley.weylElt_eq_xUnit_mul]; simp
  have h1 : phiG g a σ ε (weylElt Tag.D4 K i 1) =
      g * (xUnit Tag.D4 K j e₁ * yUnit Tag.D4 K j (-e₂) * xUnit Tag.D4 K j e₁) * g⁻¹ := by
    rw [hn, map_mul, map_mul, phiG_apply, phiG_apply, hx, hy, map_one, map_neg, map_one,
      mul_one, mul_neg_one]
    group
  have h2 : xUnit Tag.D4 K j e₁ * yUnit Tag.D4 K j (-e₂) * xUnit Tag.D4 K j e₁ ∈ A := by
    have := mul_mem (mul_mem (inv_mem (hB hg)) (hφA _ hi)) (hB hg)
    rw [h1] at this
    simpa [mul_assoc] using this
  have hxB : xUnit Tag.D4 K j e₁ ∈ A := hB (xUnit_mem_borel j e₁)
  have h3 : yUnit Tag.D4 K j (-e₂) ∈ A := by
    have := mul_mem (mul_mem (inv_mem hxB) h2) (inv_mem hxB)
    simpa [mul_assoc] using this
  set t : Kˣ := (Units.mk0 e₂ he₂0)⁻¹ with ht
  have htinv : (((t⁻¹ : Kˣ) : K)) = e₂ := by simp [ht]
  have h4 : weylElt Tag.D4 K j t ∈ A := by
    rw [CFSG.Blueprint.Chevalley.weylElt_eq_xUnit_mul, htinv]
    exact mul_mem (mul_mem (hB (xUnit_mem_borel j _)) h3) (hB (xUnit_mem_borel j _))
  have h5' : weylElt Tag.D4 K j t = torusElt Tag.D4 K j t * weylElt Tag.D4 K j 1 :=
    weylElt_eq_torusElt_mul_weylElt_one j t
  have h5 : weylElt Tag.D4 K j 1 = (torusElt Tag.D4 K j t)⁻¹ * weylElt Tag.D4 K j t := by
    rw [h5']; group
  rw [h5]
  exact mul_mem (inv_mem (hB (torusElt_mem_borel j t))) h4

theorem rho_pow_thrice {ε : ℕ} (i : Fin Tag.D4.rank) :
    (d4Rho ^ ε) ((d4Rho ^ ε) ((d4Rho ^ ε) i)) = i := by
  have h : (d4Rho ^ ε) ^ 3 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, d4Rho_pow_three, one_pow]
  have := congrArg (fun p : Equiv.Perm (Fin Tag.D4.rank) => p i) h
  simpa [pow_succ, Equiv.Perm.mul_apply] using this

theorem jclass {ε : ℕ} (hε : ε = 1 ∨ ε = 2) {J : Set (Fin Tag.D4.rank)}
    (h : ∀ i, i ∈ J ↔ (d4Rho ^ ε) i ∈ J) :
    J = ∅ ∨ J = {2} ∨ J = ({0, 1, 3} : Set (Fin Tag.D4.rank)) ∨ J = Set.univ := by
  have hconn : ∀ k j : Fin Tag.D4.rank, k ∈ ({0, 1, 3} : Set (Fin Tag.D4.rank)) →
      j ∈ ({0, 1, 3} : Set (Fin Tag.D4.rank)) → (k ∈ J ↔ j ∈ J) := by
    intro k j hk hj
    rcases (rho_cycle hε hk hj).2.2.2.2.2 with rfl | rfl | rfl
    · exact Iff.rfl
    · exact h k
    · exact (h k).trans (h _)
  have h1 : (1 : Fin Tag.D4.rank) ∈ J ↔ (0 : Fin Tag.D4.rank) ∈ J := hconn 1 0 mem_outer1 mem_outer0
  have h3 : (3 : Fin Tag.D4.rank) ∈ J ↔ (0 : Fin Tag.D4.rank) ∈ J := hconn 3 0 mem_outer3 mem_outer0
  have hi4 : ∀ i : Fin Tag.D4.rank, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by decide
  by_cases h0 : (0 : Fin Tag.D4.rank) ∈ J <;> by_cases h2 : (2 : Fin Tag.D4.rank) ∈ J
  · right; right; right
    refine Set.eq_univ_of_forall fun i => ?_
    rcases hi4 i with rfl | rfl | rfl | rfl
    exacts [h0, h1.2 h0, h2, h3.2 h0]
  · right; right; left
    ext i
    rcases hi4 i with rfl | rfl | rfl | rfl
    · exact ⟨fun _ => mem_outer0, fun _ => h0⟩
    · exact ⟨fun _ => mem_outer1, fun _ => h1.2 h0⟩
    · exact ⟨fun h => absurd h h2, fun h => absurd h (by decide)⟩
    · exact ⟨fun _ => mem_outer3, fun _ => h3.2 h0⟩
  · right; left
    ext i
    rcases hi4 i with rfl | rfl | rfl | rfl
    · exact ⟨fun h => absurd h h0, fun h => absurd h (by decide)⟩
    · exact ⟨fun h => absurd (h1.1 h) h0, fun h => absurd h (by decide)⟩
    · exact ⟨fun _ => rfl, fun _ => h2⟩
    · exact ⟨fun h => absurd (h3.1 h) h0, fun h => absurd h (by decide)⟩
  · left
    ext i
    rcases hi4 i with rfl | rfl | rfl | rfl
    · exact ⟨fun h => absurd h h0, fun h => absurd h (by simp)⟩
    · exact ⟨fun h => absurd (h1.1 h) h0, fun h => absurd h (by simp)⟩
    · exact ⟨fun h => absurd h h2, fun h => absurd h (by simp)⟩
    · exact ⟨fun h => absurd (h3.1 h) h0, fun h => absurd h (by simp)⟩

end Stable

section Level

variable {K : Type} [Field K] [Finite K]

theorem levi_c_level (hK2 : ringChar K ≠ 2) {g : ModGL Tag.D4 K} (hg : g ∈ borelGroup Tag.D4 K)
    {a : Fin Tag.D4.rank → Kˣ} {σ : K ≃+* K} {ε : ℕ} (hε : ε = 1 ∨ ε = 2)
    (hφ3 : ∀ x ∈ adjointGroup Tag.D4 K,
      phiG g a σ ε (phiG g a σ ε (phiG g a σ ε x)) = x)
    {A : Subgroup (ModGL Tag.D4 K)} (hB : borelGroup Tag.D4 K ≤ A) (hAC : A ≤ adjointGroup Tag.D4 K)
    (hAne : A ≠ adjointGroup Tag.D4 K) (hφA : ∀ x ∈ A, phiG g a σ ε x ∈ A)
    {y : ModGL Tag.D4 K} (hy : y ∈ A) (hy2 : y * y = 1) (hφy : phiG g a σ ε y = y) :
    ∃ s ∈ A, s⁻¹ * y * s ∈ borelGroup Tag.D4 K ∧ s⁻¹ * phiG g a σ ε s ∈ borelGroup Tag.D4 K := by
  have hAP := eq_parabolicSubgroup_of_borelGroup_le hB hAC
  have hcells := standard_parabolic_cells Tag.D4 K
  set J : Set (Fin Tag.D4.rank) := {i | weylElt Tag.D4 K i 1 ∈ A} with hJ
  have hfwd : ∀ i, i ∈ J → (d4Rho ^ ε) i ∈ J := fun i hi => jstable hg a σ ε hB hφA hi
  have hJρ : ∀ i, i ∈ J ↔ (d4Rho ^ ε) i ∈ J := fun i =>
    ⟨hfwd i, fun h => by
      have := hfwd _ (hfwd _ h)
      rwa [rho_pow_thrice] at this⟩
  rcases jclass hε hJρ with h0 | h2 | h013 | huniv
  ·
    have hAB : A = borelGroup Tag.D4 K := by rw [hAP, h0]; exact hcells.2.2.2.2.1
    refine ⟨1, one_mem _, ?_, ?_⟩
    · simpa [hAB] using (hAB ▸ hy : y ∈ borelGroup Tag.D4 K)
    · simpa using one_mem (borelGroup Tag.D4 K)
  ·
    have hA2 : A = parabolicSubgroup Tag.D4 K ({2} : Set (Fin Tag.D4.rank)) := by rw [hAP, h2]
    have hJρ' : ∀ i, i ∈ ({2} : Set (Fin Tag.D4.rank)) ↔
        (d4Rho ^ ε) i ∈ ({2} : Set (Fin Tag.D4.rank)) := by rw [h2] at hJρ; exact hJρ
    rw [hA2] at hy hφA
    obtain ⟨s, hsM, hs1, hs2⟩ := levi_key_two hK2 hg hJρ' hφA (phi_radical_le hg a σ hJρ')
      (fun m hm => hφ3 m (parabolicLevi_le_adjointGroup _ _ _ hm)) hy hy2 hφy
    exact ⟨s, hA2 ▸ parabolicLevi_le_parabolicSubgroup _ hsM, hs1, hs2⟩
  ·
    have hA3 : A = parabolicSubgroup Tag.D4 K ({0, 1, 3} : Set (Fin Tag.D4.rank)) := by
      rw [hAP, h013]
    have hJρ' : ∀ i, i ∈ ({0, 1, 3} : Set (Fin Tag.D4.rank)) ↔
        (d4Rho ^ ε) i ∈ ({0, 1, 3} : Set (Fin Tag.D4.rank)) := by rw [h013] at hJρ; exact hJρ
    rw [hA3] at hy hφA
    obtain ⟨s, hsM, hs1, hs2⟩ := levi_key_three hK2 hg hε hJρ' hφA (phi_radical_le hg a σ hJρ')
      (fun m hm => hφ3 m (parabolicLevi_le_adjointGroup _ _ _ hm)) hy hy2 hφy
    exact ⟨s, hA3 ▸ parabolicLevi_le_parabolicSubgroup _ hsM, hs1, hs2⟩
  ·
    exfalso
    apply hAne
    rw [hAP, huniv]
    exact hcells.2.2.2.2.2.1

end Level

end CFSG.LocalAnalysis.GLTheoremA
