module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZB2
public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZP6
public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZSyl

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Lang.D4Three CFSG.HardMathSupport.Dickson.Bal207.D4Graph
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open scoped Pointwise
local notation "Inn" => CFSG.ComponentClassification.OuterAutomorphisms.inner


section Main

variable {K : Type} [Field K] [Finite K]

theorem levi_main_pair {n : ℕ} (hK : Nat.card K = 3 ^ n) {t : MulAut (D4Model K)} (ht3 : t ^ 3 = 1)
    (htE : t ∉ D4Img K) {P : Subgroup (D4Model K)} (hPt : ∀ x ∈ P, t x ∈ P) (hPtop : P ≠ ⊤)
    {S₁ : Sylow 3 (D4Model K)} (hNS₁ : Subgroup.normalizer ((S₁ : Subgroup (D4Model K)) :
      Set (D4Model K)) ≤ P)
    (hS₁t : (S₁ : Subgroup (D4Model K)).map t.toMonoidHom = S₁)
    {y₀ y₁ : D4Model K} (hy₀P : y₀ ∈ P) (hy₁P : y₁ ∈ P) (hy₀2 : y₀ * y₀ = 1) (hy₁2 : y₁ * y₁ = 1)
    (hcomm : y₀ * y₁ = y₁ * y₀) (hty₀ : t y₀ = y₀) (hty₁ : t y₁ = y₁) :
    ∃ c ∈ P, c⁻¹ * t c ∈ Subgroup.normalizer ((S₁ : Subgroup (D4Model K)) : Set (D4Model K)) ∧
      c⁻¹ * y₀ * c ∈ Subgroup.normalizer ((S₁ : Subgroup (D4Model K)) : Set (D4Model K)) ∧
      c⁻¹ * y₁ * c ∈ Subgroup.normalizer ((S₁ : Subgroup (D4Model K)) : Set (D4Model K)) := by
  classical
  haveI := charP_three_of_card hK
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K 3]; norm_num
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (D4Model K) := inferInstance
  haveI : Finite ↥(adjointGroup Tag.D4 K) := inferInstance
  obtain ⟨ψ, x, α', g, a, σ, ε, hmem, hψα, hα'3, hε, hα'eq, hgB⟩ := exists_sylow_nf hK ht3 htE hS₁t
  obtain ⟨PC, hPCdef⟩ : ∃ PC : Subgroup ↥(adjointGroup Tag.D4 K),
      PC = (P.map ψ.symm.toMonoidHom).map (MulAut.conj x)⁻¹.toMonoidHom := ⟨_, rfl⟩
  have hPC : ∀ y : ↥(adjointGroup Tag.D4 K), y ∈ PC ↔ ψ (x * y * x⁻¹) ∈ P := by
    intro y
    rw [hPCdef]
    constructor
    · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
      have e : x * ((MulAut.conj x)⁻¹ (ψ.symm p)) * x⁻¹ = ψ.symm p := by
        rw [MulAut.conj_inv_apply]; group
      change ψ (x * ((MulAut.conj x)⁻¹ (ψ.symm p)) * x⁻¹) ∈ P
      rw [e, ψ.apply_symm_apply]; exact hp
    · intro h
      refine ⟨x * y * x⁻¹, ⟨ψ (x * y * x⁻¹), h, by simp⟩, ?_⟩
      change (MulAut.conj x)⁻¹ (x * y * x⁻¹) = y
      rw [MulAut.conj_inv_apply]; group
  have hBC : borelGroup Tag.D4 K ≤ adjointGroup Tag.D4 K := by
    rw [← (borel_self_normalizers Tag.D4 K).1]; exact inf_le_left
  have hBnorm : ∀ b : ↥(adjointGroup Tag.D4 K), (b : ModGL Tag.D4 K) ∈ borelGroup Tag.D4 K →
      ∀ u : ↥(adjointGroup Tag.D4 K), u ∈ unitU K ↔ b * u * b⁻¹ ∈ unitU K := by
    intro b hb u
    have hbN : (b : ModGL Tag.D4 K) ∈
        Subgroup.normalizer (posUnipotent Tag.D4 K : Set (ModGL Tag.D4 K)) := by
      have := hb
      rw [← (borel_self_normalizers Tag.D4 K).1] at this
      exact this.2
    have hmemH : ∀ y : ↥(adjointGroup Tag.D4 K), y ∈ unitU K ↔
        (y : ModGL Tag.D4 K) ∈ posUnipotent Tag.D4 K := fun y => Subgroup.mem_subgroupOf
    rw [hmemH, hmemH]
    exact Subgroup.mem_normalizer_iff.1 hbN _
  have hBN : ∀ b : ↥(adjointGroup Tag.D4 K), (b : ModGL Tag.D4 K) ∈ borelGroup Tag.D4 K →
      ψ (x * b * x⁻¹) ∈ Subgroup.normalizer ((S₁ : Subgroup (D4Model K)) : Set (D4Model K)) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro s
    obtain ⟨y, rfl⟩ := ψ.surjective s
    rw [← map_mul, ← map_inv, ← map_mul, hmem, hmem]
    have e : x⁻¹ * (x * b * x⁻¹ * y * (x * b * x⁻¹)⁻¹) * x = b * (x⁻¹ * y * x) * b⁻¹ := by group
    rw [e]
    exact hBnorm b hb _
  obtain ⟨Pm, hPmdef⟩ : ∃ Pm : Subgroup (ModGL Tag.D4 K),
      Pm = PC.map (adjointGroup Tag.D4 K).subtype := ⟨_, rfl⟩
  have hB : borelGroup Tag.D4 K ≤ Pm := by
    intro b hb
    rw [hPmdef]
    exact ⟨⟨b, hBC hb⟩, (hPC _).2 (hNS₁ (hBN ⟨b, hBC hb⟩ hb)), rfl⟩
  have hAC : Pm ≤ adjointGroup Tag.D4 K := by
    rw [hPmdef]
    rintro _ ⟨y, -, rfl⟩; exact y.2
  have hAne : Pm ≠ adjointGroup Tag.D4 K := by
    intro h
    apply hPtop
    rw [eq_top_iff]
    intro w _
    have hw : ((x⁻¹ * ψ.symm w * x : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) ∈ Pm := by
      rw [h]; exact (x⁻¹ * ψ.symm w * x).2
    rw [hPmdef] at hw
    obtain ⟨y, hy, hyeq⟩ := hw
    have hyy : y = x⁻¹ * ψ.symm w * x := Subtype.ext hyeq
    have h1 := (hPC y).1 hy
    rw [hyy] at h1
    have e : x * (x⁻¹ * ψ.symm w * x) * x⁻¹ = ψ.symm w := by group
    rw [e, ψ.apply_symm_apply] at h1
    exact h1
  have hφA : ∀ m ∈ Pm, phiG (g : ModGL Tag.D4 K) a σ ε m ∈ Pm := by
    rw [hPmdef]
    rintro _ ⟨y, hy, rfl⟩
    change phiG (g : ModGL Tag.D4 K) a σ ε (y : ModGL Tag.D4 K) ∈ PC.map (adjointGroup Tag.D4 K).subtype
    rw [← coe_alpha_eq_phiG hα'eq]
    refine ⟨α' y, ?_, rfl⟩
    show α' y ∈ PC
    have hy' : y ∈ PC := hy
    rw [hPC] at hy' ⊢
    rw [hψα]
    exact hPt _ hy'
  have hinv : ∀ {y₀ : D4Model K}, y₀ ∈ P → y₀ * y₀ = 1 → t y₀ = y₀ →
      ∃ y' : ↥(adjointGroup Tag.D4 K), y' = x⁻¹ * ψ.symm y₀ * x ∧ x * y' * x⁻¹ = ψ.symm y₀ ∧
        (y' : ModGL Tag.D4 K) ∈ Pm ∧ (y' : ModGL Tag.D4 K) * (y' : ModGL Tag.D4 K) = 1 ∧
        phiG (g : ModGL Tag.D4 K) a σ ε (y' : ModGL Tag.D4 K) = (y' : ModGL Tag.D4 K) := by
    intro y₀ hy₀P hy₀2 hty₀
    obtain ⟨y', hy'def⟩ : ∃ y' : ↥(adjointGroup Tag.D4 K), y' = x⁻¹ * ψ.symm y₀ * x := ⟨_, rfl⟩
    have hxy' : x * y' * x⁻¹ = ψ.symm y₀ := by rw [hy'def]; group
    have hy'PC : y' ∈ PC := by
      rw [hPC, hxy', ψ.apply_symm_apply]; exact hy₀P
    have hy'2 : (y' : ModGL Tag.D4 K) * (y' : ModGL Tag.D4 K) = 1 := by
      have h1 : y' * y' = 1 := by
        have e : y' * y' = x⁻¹ * ψ.symm (y₀ * y₀) * x := by
          rw [hy'def, map_mul]; group
        rw [e, hy₀2, map_one]; group
      exact congrArg (fun z : ↥(adjointGroup Tag.D4 K) => (z : ModGL Tag.D4 K)) h1
    have hαφ : α' y' = y' := by
      have h1 := hψα y'
      rw [hxy', ψ.apply_symm_apply, hty₀] at h1
      have h2 : x * α' y' * x⁻¹ = x * y' * x⁻¹ := by
        apply ψ.injective
        rw [h1, hxy', ψ.apply_symm_apply]
      have := congrArg (fun z => x⁻¹ * z * x) h2
      simpa [mul_assoc] using this
    refine ⟨y', hy'def, hxy', ?_, hy'2, ?_⟩
    · rw [hPmdef]; exact ⟨y', hy'PC, rfl⟩
    · rw [← coe_alpha_eq_phiG hα'eq, hαφ]
  obtain ⟨y₀', hy₀'def, hxy₀', hy₀'Pm, hy₀'2, hφy₀'⟩ := hinv hy₀P hy₀2 hty₀
  obtain ⟨y₁', hy₁'def, hxy₁', hy₁'Pm, hy₁'2, hφy₁'⟩ := hinv hy₁P hy₁2 hty₁
  have hcomm' : (y₀' : ModGL Tag.D4 K) * (y₁' : ModGL Tag.D4 K) =
      (y₁' : ModGL Tag.D4 K) * (y₀' : ModGL Tag.D4 K) := by
    have h1 : y₀' * y₁' = y₁' * y₀' := by
      have e : ∀ u v : D4Model K, x⁻¹ * ψ.symm u * x * (x⁻¹ * ψ.symm v * x) =
          x⁻¹ * ψ.symm (u * v) * x := by
        intro u v; rw [map_mul]; group
      rw [hy₀'def, hy₁'def, e, e, hcomm]
    exact congrArg (fun z : ↥(adjointGroup Tag.D4 K) => (z : ModGL Tag.D4 K)) h1
  obtain ⟨s, hsPm, hs1, hs1', hs2⟩ := levi_c_level_pair hK2 hgB hε
    (fun m hm => phiG_cube hα'eq hα'3 hm) hB hAC hAne hφA hy₀'Pm hy₁'Pm hy₀'2 hy₁'2 hcomm' hφy₀' hφy₁'
  rw [hPmdef] at hsPm
  obtain ⟨s', hs'PC, rfl⟩ := hsPm
  have hs1_ : (((s'⁻¹ * y₀' * s' : ↥(adjointGroup Tag.D4 K))) : ModGL Tag.D4 K) ∈
      borelGroup Tag.D4 K := hs1
  have hs1'_ : (((s'⁻¹ * y₁' * s' : ↥(adjointGroup Tag.D4 K))) : ModGL Tag.D4 K) ∈
      borelGroup Tag.D4 K := hs1'
  have hs2' : (((s'⁻¹ * α' s' : ↥(adjointGroup Tag.D4 K))) : ModGL Tag.D4 K) ∈
      borelGroup Tag.D4 K := by
    have h := hs2
    change (s' : ModGL Tag.D4 K)⁻¹ * phiG (g : ModGL Tag.D4 K) a σ ε (s' : ModGL Tag.D4 K) ∈ _ at h
    rw [← coe_alpha_eq_phiG hα'eq] at h
    exact h
  have hcy : ∀ (yy : D4Model K) (y' : ↥(adjointGroup Tag.D4 K)), x * y' * x⁻¹ = ψ.symm yy →
      (ψ (x * s' * x⁻¹))⁻¹ * yy * ψ (x * s' * x⁻¹) = ψ (x * (s'⁻¹ * y' * s') * x⁻¹) := by
    intro yy y' hxy
    have hy₀ : yy = ψ (x * y' * x⁻¹) := by rw [hxy, ψ.apply_symm_apply]
    conv_lhs => rw [hy₀]
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    group
  refine ⟨ψ (x * s' * x⁻¹), (hPC s').1 hs'PC, ?_, ?_, ?_⟩
  · have e : (ψ (x * s' * x⁻¹))⁻¹ * t (ψ (x * s' * x⁻¹)) = ψ (x * (s'⁻¹ * α' s') * x⁻¹) := by
      rw [← hψα, ← map_inv, ← map_mul]
      congr 1
      group
    rw [e]
    exact hBN _ hs2'
  · rw [hcy y₀ y₀' hxy₀']
    exact hBN _ hs1_
  · rw [hcy y₁ y₁' hxy₁']
    exact hBN _ hs1'_

end Main

end CFSG.LocalAnalysis.GLTheoremA
