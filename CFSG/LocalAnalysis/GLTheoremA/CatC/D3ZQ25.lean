module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZL9

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.LieType.BorelTits CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Lang.D4Three CFSG.HardMathSupport.Dickson.Bal207.D4Graph
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open scoped Pointwise
local notation "Inn" => CFSG.ComponentClassification.OuterAutomorphisms.inner


section Transport

variable {G G' : Type*} [Group G] [Group G']

theorem le_normalizer_of_forward {H N : Subgroup G'}
    (h : ∀ x ∈ H, ∀ y ∈ N, x * y * x⁻¹ ∈ N) : H ≤ Subgroup.normalizer (N : Set G') := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => h x hx y hy, fun hy => ?_⟩
  have := h x⁻¹ (inv_mem hx) _ hy
  simpa [mul_assoc] using this

theorem pCoreOf_map_of_injective [Finite G] [Finite G'] {r : ℕ} [Fact r.Prime] (f : G →* G')
    (hf : Function.Injective f) (H : Subgroup G) :
    pCoreOf r (H.map f) = (pCoreOf r H).map f := by
  apply le_antisymm
  · set M := pCoreOf r (H.map f) with hMdef
    have hMH : M ≤ H.map f := pCoreOf_le r _
    have hM' : (M.comap f).map f = M :=
      Subgroup.map_comap_eq_self (hMH.trans (Subgroup.map_le_range f H))
    have hM'H : M.comap f ≤ H := by
      intro x hx
      obtain ⟨h, hh, hhx⟩ := hMH (Subgroup.mem_comap.1 hx)
      rw [← hf hhx]
      exact hh
    have hp : IsPGroup r (M.comap f) := (pCoreOf_isPGroup r (H.map f)).comap_of_injective f hf
    have hnorm : H ≤ Subgroup.normalizer ((M.comap f : Subgroup G) : Set G) := by
      refine le_normalizer_of_forward fun x hx y hy => ?_
      have hxM : f x ∈ Subgroup.normalizer (M : Set G') :=
        le_normalizer_pCoreOf r (H.map f) (Subgroup.mem_map_of_mem f hx)
      have := (Subgroup.mem_normalizer_iff.1 hxM (f y)).1 (Subgroup.mem_comap.1 hy)
      rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
      exact this
    have := le_pCoreOf_of_le_normalizer r hM'H hnorm hp
    calc M = (M.comap f).map f := hM'.symm
      _ ≤ (pCoreOf r H).map f := Subgroup.map_mono this
  · refine le_pCoreOf_of_le_normalizer r (Subgroup.map_mono (pCoreOf_le r H)) ?_
      ((pCoreOf_isPGroup r H).map f)
    rintro _ ⟨h, hh, rfl⟩
    refine le_normalizer_of_forward (H := (H.map f)) (fun x hx y hy => ?_) (Subgroup.mem_map_of_mem f hh)
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hy
    refine ⟨x' * y' * x'⁻¹, ?_, by simp⟩
    exact (Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf r H hx') y').1 hy'

theorem inf_range_normalizer_map (f : G →* G') (hf : Function.Injective f) (H : Subgroup G) :
    f.range ⊓ Subgroup.normalizer ((H.map f : Subgroup G') : Set G') =
      (Subgroup.normalizer (H : Set G)).map f := by
  ext z
  constructor
  · intro hz
    obtain ⟨⟨g, rfl⟩, hzN⟩ := Subgroup.mem_inf.1 hz
    refine ⟨g, ?_, rfl⟩
    show g ∈ Subgroup.normalizer (H : Set G)
    rw [Subgroup.mem_normalizer_iff] at hzN ⊢
    intro y
    rw [← Subgroup.mem_map_iff_mem hf, ← Subgroup.mem_map_iff_mem hf (K := H), hzN (f y)]
    rw [map_mul, map_mul, map_inv]
  · rintro ⟨g, hg, rfl⟩
    refine Subgroup.mem_inf.2 ⟨⟨g, rfl⟩, ?_⟩
    rw [Subgroup.mem_normalizer_iff]
    intro y
    by_cases hy : y ∈ f.range
    · obtain ⟨y', rfl⟩ := hy
      have h1 := (Subgroup.mem_normalizer_iff.1 hg y')
      rw [Subgroup.mem_map_iff_mem hf, ← map_mul, ← map_inv, ← map_mul,
        Subgroup.mem_map_iff_mem hf]
      exact h1
    · have h1 : y ∉ H.map f := fun h => hy (Subgroup.map_le_range f H h)
      have h2 : f g * y * (f g)⁻¹ ∉ H.map f := by
        intro h
        apply hy
        have := Subgroup.map_le_range f H h
        obtain ⟨w, hw⟩ := this
        refine ⟨g⁻¹ * w * g, ?_⟩
        rw [map_mul, map_mul, map_inv, hw]
        group
      exact ⟨fun h => absurd h h1, fun h => absurd h h2⟩

end Transport

section Frame

variable {K : Type} [Field K] [Finite K]

theorem exists_frame {n : ℕ} (hK : Nat.card K = 3 ^ n) {b : MulAut (D4Model K)} (hb3 : b ^ 3 = 1)
    (hbE : b ∉ D4Img K) {S₁ : Sylow 3 (D4Model K)}
    (hS₁b : (S₁ : Subgroup (D4Model K)).map b.toMonoidHom = S₁) :
    ∃ (Θ : adjointGroup Tag.D4 K ≃* D4Model K) (g : adjointGroup Tag.D4 K)
      (a : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K) (ε : ℕ),
      (∀ y : adjointGroup Tag.D4 K, Θ y ∈ (S₁ : Subgroup (D4Model K)) ↔ y ∈ unitU K) ∧
      (ε = 1 ∨ ε = 2) ∧ (g : ModGL Tag.D4 K) ∈ borelGroup Tag.D4 K ∧
      MulAut.congr Θ.symm b = MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε) := by
  classical
  haveI := charP_three_of_card hK
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
  obtain ⟨Θ, hΘdef⟩ : ∃ Θ : adjointGroup Tag.D4 K ≃* D4Model K, Θ = (MulAut.conj x).trans ψ :=
    ⟨_, rfl⟩
  have hΘapp : ∀ y, Θ y = ψ (x * y * x⁻¹) := fun y => by rw [hΘdef]; rfl
  have hΘsymm : ∀ u, Θ.symm u = x⁻¹ * ψ.symm u * x := by
    intro u
    rw [MulEquiv.symm_apply_eq, hΘapp]
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
    group
  have hΘ : ∀ y, Θ y ∈ (S₁ : Subgroup (D4Model K)) ↔ y ∈ unitU K := by
    intro y
    rw [hΘapp, hmem]
    have : x⁻¹ * (x * y * x⁻¹) * x = y := by group
    rw [this]
  obtain ⟨α', hα'def⟩ : ∃ α' : MulAut ↥(adjointGroup Tag.D4 K), α' = MulAut.congr Θ.symm b :=
    ⟨_, rfl⟩
  have hΘα' : ∀ y, Θ (α' y) = b (Θ y) := by
    intro y
    rw [hα'def, MulAut.congr_apply]
    simp
  have hα'3 : α' ^ 3 = 1 := by rw [hα'def, ← map_pow, hb3, map_one]
  have hUα' : (unitU K).map α'.toMonoidHom = unitU K := by
    refine d3z_map_eq_of_forall_mem _ α' fun y hy => ?_
    rw [← hΘ] at hy ⊢
    rw [hΘα']
    have := Subgroup.mem_map_of_mem b.toMonoidHom hy
    rwa [hS₁b] at this
  obtain ⟨g, a, σ, ε, hε3, hα'eq, hgB⟩ := exists_normal_form_borel α' hα'3 hUα'
  have hα'app : ∀ y, α' y = Θ.symm (b (Θ y)) := fun y => (MulEquiv.eq_symm_apply Θ).2 (hΘα' y)
  have ht₂eq : MulAut.congr ψ α' = (MulAut.conj (ψ x))⁻¹ * b * MulAut.conj (ψ x) := by
    refine MulEquiv.ext fun s => ?_
    have h1 : Θ (ψ.symm s) = ψ x * s * (ψ x)⁻¹ := by
      rw [hΘapp]; simp
    change ψ (α' (ψ.symm s)) = ((MulAut.conj (ψ x))⁻¹ * b * MulAut.conj (ψ x)) s
    rw [hα'app, h1, hΘsymm]
    simp [MulAut.conj_inv_apply, MulAut.conj_apply]
  have ht₂3 : (MulAut.congr ψ α') ^ 3 = 1 := by rw [← map_pow, hα'3, map_one]
  have ht₂E : MulAut.congr ψ α' ∉ D4Img K := by
    intro h
    apply hbE
    have hc : MulAut.conj (ψ x) ∈ D4Img K := inner_le_D4Img ⟨ψ x, rfl⟩
    have e : b = MulAut.conj (ψ x) * MulAut.congr ψ α' * (MulAut.conj (ψ x))⁻¹ := by
      rw [ht₂eq]; group
    rw [e]
    exact mul_mem (mul_mem hc h) (inv_mem hc)
  have hε0 : ε ≠ 0 := by
    refine eps_ne_zero hK ht₂3 ht₂E g a σ ε ?_
    rw [← hψdef, hα'eq]
  have hε : ε = 1 ∨ ε = 2 := by omega
  exact ⟨Θ, g, a, σ, ε, hΘ, hε, hgB, hα'def ▸ hα'eq⟩

end Frame

end CFSG.LocalAnalysis.GLTheoremA
