module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZL8
public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZSyl
public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZField
public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3PCases

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

theorem levi_main {n : ℕ} (hK : Nat.card K = 3 ^ n) {t : MulAut (D4Model K)} (ht3 : t ^ 3 = 1)
    (htE : t ∉ D4Img K) {P : Subgroup (D4Model K)} (hPt : ∀ x ∈ P, t x ∈ P) (hPtop : P ≠ ⊤)
    {S₁ : Sylow 3 (D4Model K)} (hNS₁ : Subgroup.normalizer ((S₁ : Subgroup (D4Model K)) :
      Set (D4Model K)) ≤ P)
    (hS₁t : (S₁ : Subgroup (D4Model K)).map t.toMonoidHom = S₁)
    {y₀ : D4Model K} (hy₀P : y₀ ∈ P) (hy₀2 : y₀ * y₀ = 1) (hty₀ : t y₀ = y₀) :
    ∃ c ∈ P, c⁻¹ * t c ∈ Subgroup.normalizer ((S₁ : Subgroup (D4Model K)) : Set (D4Model K)) ∧
      c⁻¹ * y₀ * c ∈ Subgroup.normalizer ((S₁ : Subgroup (D4Model K)) : Set (D4Model K)) := by
  classical
  haveI := charP_three_of_card hK
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K 3]; norm_num
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (D4Model K) := inferInstance
  haveI : Finite ↥(adjointGroup Tag.D4 K) := inferInstance
  obtain ⟨ψ, hψdef⟩ : ∃ ψ : adjointGroup Tag.D4 K ≃* D4Model K,
      ψ = coordinatePlusWitnessEquiv K (isoAdj K).symm := ⟨_, rfl⟩
  obtain ⟨S', hS'coe⟩ : ∃ S' : Sylow 3 ↥(adjointGroup Tag.D4 K),
      (S' : Subgroup ↥(adjointGroup Tag.D4 K)) =
        (S₁ : Subgroup (D4Model K)).map ψ.symm.toMonoidHom :=
    ⟨Sylow.mapSurjective (f := ψ.symm.toMonoidHom) ψ.symm.surjective S₁, Sylow.coe_mapSurjective _ _⟩
  have hS'mem : ∀ y, y ∈ (S' : Subgroup ↥(adjointGroup Tag.D4 K)) ↔
      ψ y ∈ (S₁ : Subgroup (D4Model K)) := by
    intro y
    rw [hS'coe]
    constructor
    · rintro ⟨s, hs, rfl⟩
      show ψ (ψ.symm s) ∈ (S₁ : Subgroup (D4Model K))
      rw [ψ.apply_symm_apply]; exact hs
    · intro h
      exact ⟨ψ y, h, by simp⟩
  obtain ⟨x, hmemS⟩ := exists_conj_to_U S'
  have hmem : ∀ y : ↥(adjointGroup Tag.D4 K), ψ y ∈ (S₁ : Subgroup (D4Model K)) ↔
      x⁻¹ * y * x ∈ unitU K := fun y => (hS'mem y).symm.trans (hmemS y)
  obtain ⟨α, hαdef⟩ : ∃ α : MulAut ↥(adjointGroup Tag.D4 K), α = MulAut.congr ψ.symm t := ⟨_, rfl⟩
  have hψα : ∀ w, ψ (α w) = t (ψ w) := by
    intro w; simp [hαdef, MulAut.congr_apply]
  have hSα : (S' : Subgroup ↥(adjointGroup Tag.D4 K)).map α.toMonoidHom = S' := by
    refine d3z_map_eq_of_forall_mem _ α fun y hy => ?_
    rw [hS'mem] at hy ⊢
    rw [hψα]
    have := Subgroup.mem_map_of_mem t.toMonoidHom hy
    rwa [hS₁t] at this
  have hUα' := stable_of_sylow_conj hmemS hSα
  obtain ⟨α', hα'def⟩ : ∃ α' : MulAut ↥(adjointGroup Tag.D4 K),
      α' = (MulAut.conj x)⁻¹ * α * MulAut.conj x := ⟨_, rfl⟩
  rw [← hα'def] at hUα'
  have hα3 : α ^ 3 = 1 := by rw [hαdef, ← map_pow, ht3, map_one]
  have hα'3 : α' ^ 3 = 1 := by
    have h := conj_pow (a := (MulAut.conj x)⁻¹) (b := α) (i := 3)
    rw [inv_inv] at h
    rw [hα'def, h, hα3]; group
  have hα'app : ∀ w, α' w = x⁻¹ * α (x * w * x⁻¹) * x := by
    intro w; simp [hα'def, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_inv_apply]
  have hαx : ∀ w, α (x * w * x⁻¹) = x * α' w * x⁻¹ := by
    intro w; rw [hα'app]; group
  obtain ⟨g, a, σ, ε, hε3, hα'eq, hgB⟩ := exists_normal_form_borel α' hα'3 hUα'
  have ht₂eq : MulAut.congr ψ α' = (MulAut.conj (ψ x))⁻¹ * t * MulAut.conj (ψ x) := by
    rw [hα'def, map_mul, map_mul, map_inv, d3f_congr_conj, hαdef, congr_congr_symm]
  have ht₂3 : (MulAut.congr ψ α') ^ 3 = 1 := by rw [← map_pow, hα'3, map_one]
  have ht₂E : MulAut.congr ψ α' ∉ D4Img K := by
    intro h
    apply htE
    have hc : MulAut.conj (ψ x) ∈ D4Img K := inner_le_D4Img ⟨ψ x, rfl⟩
    have e : t = MulAut.conj (ψ x) * MulAut.congr ψ α' * (MulAut.conj (ψ x))⁻¹ := by
      rw [ht₂eq]; group
    rw [e]
    exact mul_mem (mul_mem hc h) (inv_mem hc)
  have hε0 : ε ≠ 0 := by
    refine eps_ne_zero hK ht₂3 ht₂E g a σ ε ?_
    rw [← hψdef, hα'eq]
  have hε : ε = 1 ∨ ε = 2 := by omega
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
    rw [hα'app, show x * (x⁻¹ * α (x * y * x⁻¹) * x) * x⁻¹ = α (x * y * x⁻¹) by group, hψα]
    exact hPt _ hy'
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
  have hαφ : α (ψ.symm y₀) = ψ.symm y₀ :=
    ψ.injective (by rw [hψα, ψ.apply_symm_apply, hty₀])
  have hφy' : phiG (g : ModGL Tag.D4 K) a σ ε (y' : ModGL Tag.D4 K) = (y' : ModGL Tag.D4 K) := by
    have h1 : α' y' = y' := by
      rw [hα'app, hxy', hαφ, hy'def]
    rw [← coe_alpha_eq_phiG hα'eq, h1]
  obtain ⟨s, hsPm, hs1, hs2⟩ := levi_c_level hK2 hgB hε
    (fun m hm => phiG_cube hα'eq hα'3 hm) hB hAC hAne hφA
    (by rw [hPmdef]; exact ⟨y', hy'PC, rfl⟩) hy'2 hφy'
  rw [hPmdef] at hsPm
  obtain ⟨s', hs'PC, rfl⟩ := hsPm
  have hs1' : (((s'⁻¹ * y' * s' : ↥(adjointGroup Tag.D4 K))) : ModGL Tag.D4 K) ∈
      borelGroup Tag.D4 K := hs1
  have hs2' : (((s'⁻¹ * α' s' : ↥(adjointGroup Tag.D4 K))) : ModGL Tag.D4 K) ∈
      borelGroup Tag.D4 K := by
    have h := hs2
    change (s' : ModGL Tag.D4 K)⁻¹ * phiG (g : ModGL Tag.D4 K) a σ ε (s' : ModGL Tag.D4 K) ∈ _ at h
    rw [← coe_alpha_eq_phiG hα'eq] at h
    exact h
  refine ⟨ψ (x * s' * x⁻¹), (hPC s').1 hs'PC, ?_, ?_⟩
  · have e : (ψ (x * s' * x⁻¹))⁻¹ * t (ψ (x * s' * x⁻¹)) = ψ (x * (s'⁻¹ * α' s') * x⁻¹) := by
      rw [← hψα, hαx, ← map_inv, ← map_mul]
      congr 1
      group
    rw [e]
    exact hBN _ hs2'
  · have e : (ψ (x * s' * x⁻¹))⁻¹ * y₀ * ψ (x * s' * x⁻¹) = ψ (x * (s'⁻¹ * y' * s') * x⁻¹) := by
      have hy₀ : y₀ = ψ (x * y' * x⁻¹) := by rw [hxy', ψ.apply_symm_apply]
      conv_lhs => rw [hy₀]
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
      group
    rw [e]
    exact hBN _ hs1'

end Main

end CFSG.LocalAnalysis.GLTheoremA
