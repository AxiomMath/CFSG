module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3PLayer

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Lang.D4Three

variable {K : Type} [Field K] [Finite K]


theorem isCyclic_ringEquiv' : IsCyclic (K ≃+* K) := by
  let p := ringChar K
  have : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
  let : Algebra (ZMod p) K := ZMod.algebra K p
  exact (CFSG.Semidihedral.FixedFieldData.primeFieldAutEquiv p K).isCyclic.mpr inferInstance

theorem aut_cube_cases {σ τ : K ≃+* K} (hσ : σ ^ 3 = 1) (hτ : τ ^ 3 = 1) (hσ1 : σ ≠ 1) :
    τ = 1 ∨ τ = σ ∨ τ = σ ^ 2 := by
  classical
  have := isCyclic_ringEquiv' (K := K)
  have : Fintype (K ≃+* K) := Fintype.ofFinite _
  have hle := IsCyclic.card_pow_eq_one_le (α := K ≃+* K) (n := 3) (by norm_num)
  by_contra hne
  push Not at hne
  obtain ⟨h1, h2, h3⟩ := hne
  have hσ2 : σ ^ 2 ≠ 1 := fun h => hσ1 (by
    calc σ = σ ^ 3 * (σ ^ 2)⁻¹ := by group
      _ = 1 := by rw [hσ, h]; group)
  have hσσ : σ ^ 2 ≠ σ := fun h => hσ1 (by
    calc σ = σ ^ 2 * σ⁻¹ := by group
      _ = σ * σ⁻¹ := by rw [h]
      _ = 1 := by group)
  have hsub : ({1, σ, σ ^ 2, τ} : Finset (K ≃+* K)) ⊆ Finset.univ.filter (fun a => a ^ 3 = 1) := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases ha with rfl | rfl | rfl | rfl
    · exact one_pow 3
    · exact hσ
    · calc (σ ^ 2) ^ 3 = (σ ^ 3) ^ 2 := by rw [← pow_mul, ← pow_mul, mul_comm]
        _ = 1 := by rw [hσ, one_pow]
    · exact hτ
  have hcard : ({1, σ, σ ^ 2, τ} : Finset (K ≃+* K)).card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair]
    · exact fun h => h3 h.symm
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => hσσ h.symm, fun h => h2 h.symm⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => hσ1 h.symm, fun h => hσ2 h.symm, fun h => h1 h.symm⟩
  have := (Finset.card_le_card hsub).trans hle
  omega


@[expose] def unitU (K : Type) [Field K] [Finite K] : Subgroup ↥(adjointGroup Tag.D4 K) :=
  (posUnipotent Tag.D4 K).subgroupOf (adjointGroup Tag.D4 K)

theorem eps_zero_of_fixed {ε : ℕ} (hε3 : ε < 3) (h : (d4Rho ^ (2 * ε)) 0 = 0) : ε = 0 := by
  interval_cases ε
  · rfl
  · exact absurd h (by decide)
  · exact absurd h (by decide)

theorem inner_of_trivial_layerAct {α : MulAut ↥(adjointGroup Tag.D4 K)} (hα3 : α ^ 3 = 1)
    (hU : (unitU K).map α.toMonoidHom = unitU K) {σ : K ≃+* K} (la : LayerAct Tag.D4 α σ)
    (hσ : σ = 1) (hr : ∀ k δ, la.r k δ = δ) :
    α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner ↥(adjointGroup Tag.D4 K) := by
  obtain ⟨σ', ε', la', hσ'3, hε'3, hinner, hr'⟩ := exists_layerAct_of_stable α hα3 _ rfl hU
  obtain ⟨hrr, hσσ⟩ := LayerAct.unique' la la'
  have hε0 : ε' = 0 := by
    have h1 : (la'.r 0 (δA 0)).1 = (δA 0).1 := by rw [← hrr, hr]
    rw [hr' 0 (δA 0)] at h1
    have h2 : permLattice (τ := Tag.D4) (d4Rho ^ (2 * ε')) (rA 0) = rA ((d4Rho ^ (2 * ε')) 0) :=
      permLattice_single (τ := Tag.D4) _ _
    have h3 : rA ((d4Rho ^ (2 * ε')) 0) = rA 0 := by
      rw [← h2]
      exact h1
    exact eps_zero_of_fixed hε'3 ((rA_inj _ _).1 h3)
  exact hinner (hσσ.symm.trans hσ) hε0

theorem layerAct_sigma_cube {α : MulAut ↥(adjointGroup Tag.D4 K)} (hα3 : α ^ 3 = 1)
    (hU : (unitU K).map α.toMonoidHom = unitU K) {σ : K ≃+* K} (la : LayerAct Tag.D4 α σ) :
    σ ^ 3 = 1 := by
  obtain ⟨σ', ε', la', hσ'3, -, -, -⟩ := exists_layerAct_of_stable α hα3 _ rfl hU
  obtain ⟨-, hσσ⟩ := LayerAct.unique' la la'
  rw [hσσ]
  exact hσ'3

theorem layerAct_sigma_ne_one {α : MulAut ↥(adjointGroup Tag.D4 K)} (hα3 : α ^ 3 = 1)
    (hU : (unitU K).map α.toMonoidHom = unitU K)
    (hnot : α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner ↥(adjointGroup Tag.D4 K))
    {σ : K ≃+* K} (la : LayerAct Tag.D4 α σ) (hr : ∀ k δ, la.r k δ = δ) : σ ≠ 1 :=
  fun hσ => hnot (inner_of_trivial_layerAct hα3 hU la hσ hr)


theorem fieldpair_stable {y b : MulAut ↥(adjointGroup Tag.D4 K)} (hy3 : y ^ 3 = 1) (hb3 : b ^ 3 = 1)
    (hyb : y * b = b * y)
    (hUy : (unitU K).map y.toMonoidHom = unitU K) (hUb : (unitU K).map b.toMonoidHom = unitU K)
    (hyn : y ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner ↥(adjointGroup Tag.D4 K))
    (hbn : b ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner ↥(adjointGroup Tag.D4 K))
    (hybn : y * b ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner ↥(adjointGroup Tag.D4 K))
    (hybbn : y * b * b ∉
      CFSG.ComponentClassification.OuterAutomorphisms.inner ↥(adjointGroup Tag.D4 K))
    {A : Subgroup ↥(adjointGroup Tag.D4 K)} (hA0 : A ≤ unitN Tag.D4 K 0)
    (hfy : ∀ a ∈ A, y a = a) (hfb : ∀ a ∈ A, b a = a) : Nat.card A ^ 3 ≤ Nat.card K ^ 6 := by
  obtain ⟨σy, εy, lay, hσy3, hεy3, -, hry⟩ := exists_layerAct_of_stable y hy3 _ rfl hUy
  obtain ⟨σb, εb, lab, hσb3, hεb3, -, hrb⟩ := exists_layerAct_of_stable b hb3 _ rfl hUb
  have hUyb : (unitU K).map (y * b).toMonoidHom = unitU K := by
    rw [map_toMonoidHom_mul_mulAut, hUb, hUy]
  have hUybb : (unitU K).map (y * b * b).toMonoidHom = unitU K := by
    rw [map_toMonoidHom_mul_mulAut, hUb, hUyb]
  have hcomm : Commute y b := hyb
  have hyb3 : (y * b) ^ 3 = 1 := by rw [hcomm.mul_pow, hy3, hb3, one_mul]
  have hybb3 : (y * b * b) ^ 3 = 1 := by
    have h2 : y * b * b = y * b ^ 2 := by rw [mul_assoc, ← pow_two]
    rw [h2, (hcomm.pow_right 2).mul_pow, hy3, ← pow_mul, mul_comm, pow_mul, hb3, one_pow, one_mul]
  have hfyb : ∀ a ∈ A, (y * b) a = a := fun a ha => by
    rw [MulAut.mul_apply, hfb a ha, hfy a ha]
  have hfybb : ∀ a ∈ A, (y * b * b) a = a := fun a ha => by
    rw [MulAut.mul_apply, hfb a ha, hfyb a ha]
  let layb := LayerAct.comp' lay lab
  let laybb := LayerAct.comp' layb lab
  have finish : ∀ (f g : MulAut ↥(adjointGroup Tag.D4 K)) (σf σg : K ≃+* K)
      (laf : LayerAct Tag.D4 f σf) (lag : LayerAct Tag.D4 g σg), σf ^ 3 = 1 → σf ≠ 1 →
      (∀ k δ, laf.r k δ = δ) → ∀ ε : ℕ, (ε = 1 ∨ ε = 2) →
      (∀ (k : ℕ) (δ : UnitRoots Tag.D4 k), (lag.r k δ).1 = permLattice (d4Rho ^ (2 * ε)) δ.1) →
      (∀ a ∈ A, f a = a) → (∀ a ∈ A, g a = a) → Nat.card A ^ 3 ≤ Nat.card K ^ 6 :=
    fun f g σf σg laf lag h3 h1 hrf ε hε hrg hf hg =>
      card_pow_le_of_pair h3 h1 laf lag hrf hε hrg hA0 hf hg
  have hy_triv : εy = 0 → ∀ k δ, lay.r k δ = δ := fun h k δ => Subtype.ext (by
    rw [hry, h, mul_zero, pow_zero, permLattice_one'])
  have hb_triv : εb = 0 → ∀ k δ, lab.r k δ = δ := fun h k δ => Subtype.ext (by
    rw [hrb, h, mul_zero, pow_zero, permLattice_one'])
  have hsy_ne : εy = 0 → σy ≠ 1 := fun h => layerAct_sigma_ne_one hy3 hUy hyn lay (hy_triv h)
  have hsb_ne : εb = 0 → σb ≠ 1 := fun h => layerAct_sigma_ne_one hb3 hUb hbn lab (hb_triv h)
  have hrcomp : ∀ k δ, (layb.r k δ).1 =
      permLattice (d4Rho ^ (2 * εb) * d4Rho ^ (2 * εy)) δ.1 := fun k δ => by
    show (lab.r k (lay.r k δ)).1 = _
    rw [hrb, hry, permLattice_mul']
  have hrcomp2 : ∀ k δ, (laybb.r k δ).1 =
      permLattice (d4Rho ^ (2 * εb) * (d4Rho ^ (2 * εb) * d4Rho ^ (2 * εy))) δ.1 := fun k δ => by
    show (lab.r k (layb.r k δ)).1 = _
    rw [hrb, hrcomp]
    simp only [permLattice_mul']
  have hrcomp_triv : d4Rho ^ (2 * εb) * d4Rho ^ (2 * εy) = 1 → ∀ k δ, layb.r k δ = δ :=
    fun h k δ => Subtype.ext (by rw [hrcomp, h, permLattice_one'])
  have hrcomp2_triv : d4Rho ^ (2 * εb) * (d4Rho ^ (2 * εb) * d4Rho ^ (2 * εy)) = 1 →
      ∀ k δ, laybb.r k δ = δ := fun h k δ => Subtype.ext (by rw [hrcomp2, h, permLattice_one'])
  obtain hεy | hεy | hεy : εy = 0 ∨ εy = 1 ∨ εy = 2 := by omega
  · obtain hεb | hεb | hεb : εb = 0 ∨ εb = 1 ∨ εb = 2 := by omega
    ·
      exfalso
      have hσy1 := hsy_ne hεy
      have hσb1 := hsb_ne hεb
      have h2 : σy * σb ≠ 1 := layerAct_sigma_ne_one hyb3 hUyb hybn layb
        (hrcomp_triv (by rw [hεy, hεb]; rfl))
      have h3 : σy * σb * σb ≠ 1 := layerAct_sigma_ne_one hybb3 hUybb hybbn laybb
        (hrcomp2_triv (by rw [hεy, hεb]; rfl))
      rcases aut_cube_cases hσy3 hσb3 hσy1 with h | h | h
      · exact hσb1 h
      · apply h3
        rw [h, ← pow_three']
        exact hσy3
      · apply h2
        rw [h]
        calc σy * σy ^ 2 = σy ^ 3 := by group
          _ = 1 := hσy3
    · exact finish y b σy σb lay lab hσy3 (hsy_ne hεy) (hy_triv hεy) εb (Or.inl hεb) hrb hfy hfb
    · exact finish y b σy σb lay lab hσy3 (hsy_ne hεy) (hy_triv hεy) εb (Or.inr hεb) hrb hfy hfb
  all_goals
    obtain hεb | hεb | hεb : εb = 0 ∨ εb = 1 ∨ εb = 2 := by omega
  · exact finish b y σb σy lab lay hσb3 (hsb_ne hεb) (hb_triv hεb) εy (Or.inl hεy) hry hfb hfy
  ·
    have hp : d4Rho ^ (2 * εb) * (d4Rho ^ (2 * εb) * d4Rho ^ (2 * εy)) = 1 := by
      rw [hεy, hεb]; decide
    exact finish (y * b * b) y (σy * σb * σb) σy laybb lay
      (layerAct_sigma_cube hybb3 hUybb laybb)
      (layerAct_sigma_ne_one hybb3 hUybb hybbn laybb (hrcomp2_triv hp)) (hrcomp2_triv hp)
      εy (Or.inl hεy) hry hfybb hfy
  ·
    have hp : d4Rho ^ (2 * εb) * d4Rho ^ (2 * εy) = 1 := by rw [hεy, hεb]; decide
    exact finish (y * b) y (σy * σb) σy layb lay
      (layerAct_sigma_cube hyb3 hUyb layb)
      (layerAct_sigma_ne_one hyb3 hUyb hybn layb (hrcomp_triv hp)) (hrcomp_triv hp)
      εy (Or.inl hεy) hry hfyb hfy
  · exact finish b y σb σy lab lay hσb3 (hsb_ne hεb) (hb_triv hεb) εy (Or.inr hεy) hry hfb hfy
  ·
    have hp : d4Rho ^ (2 * εb) * d4Rho ^ (2 * εy) = 1 := by rw [hεy, hεb]; decide
    exact finish (y * b) y (σy * σb) σy layb lay
      (layerAct_sigma_cube hyb3 hUyb layb)
      (layerAct_sigma_ne_one hyb3 hUyb hybn layb (hrcomp_triv hp)) (hrcomp_triv hp)
      εy (Or.inr hεy) hry hfyb hfy
  ·
    have hp : d4Rho ^ (2 * εb) * (d4Rho ^ (2 * εb) * d4Rho ^ (2 * εy)) = 1 := by
      rw [hεy, hεb]; decide
    exact finish (y * b * b) y (σy * σb * σb) σy laybb lay
      (layerAct_sigma_cube hybb3 hUybb laybb)
      (layerAct_sigma_ne_one hybb3 hUybb hybbn laybb (hrcomp2_triv hp)) (hrcomp2_triv hp)
      εy (Or.inr hεy) hry hfybb hfy

section Transport

local notation "Inn" => CFSG.ComponentClassification.OuterAutomorphisms.inner

theorem exists_conj_to_U [CharP K 3] (S : Sylow 3 ↥(adjointGroup Tag.D4 K)) :
    ∃ x : ↥(adjointGroup Tag.D4 K), ∀ y, y ∈ (S : Subgroup ↥(adjointGroup Tag.D4 K)) ↔
      x⁻¹ * y * x ∈ unitU K := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := finite_modGL (τ := Tag.D4) (K := K)
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem Tag.D4).length
  obtain ⟨P₀, hP₀⟩ := (exceptional_ordinary_Sylow_opposition Tag.D4 K 3 w₀ hw₀).1
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq (adjointGroup Tag.D4 K) P₀ S
  have hS : (S : Subgroup ↥(adjointGroup Tag.D4 K)) = (unitU K).map (MulAut.conj x).toMonoidHom := by
    rw [← hx, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def, hP₀]
    rfl
  refine ⟨x, fun y => ?_⟩
  rw [hS]
  constructor
  · rintro ⟨u, hu, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hu
  · intro hy
    exact ⟨x⁻¹ * y * x, hy, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem stable_of_sylow_conj {S : Sylow 3 ↥(adjointGroup Tag.D4 K)} {x : ↥(adjointGroup Tag.D4 K)}
    (hmemS : ∀ y, y ∈ (S : Subgroup ↥(adjointGroup Tag.D4 K)) ↔ x⁻¹ * y * x ∈ unitU K)
    {α : MulAut ↥(adjointGroup Tag.D4 K)}
    (hSα : (S : Subgroup ↥(adjointGroup Tag.D4 K)).map α.toMonoidHom = S) :
    (unitU K).map ((MulAut.conj x)⁻¹ * α * MulAut.conj x).toMonoidHom = unitU K := by
  have hαS : ∀ y ∈ (S : Subgroup ↥(adjointGroup Tag.D4 K)),
      α y ∈ (S : Subgroup ↥(adjointGroup Tag.D4 K)) := by
    intro y hy
    have := Subgroup.mem_map_of_mem α.toMonoidHom hy
    rwa [hSα] at this
  set α' : MulAut ↥(adjointGroup Tag.D4 K) := (MulAut.conj x)⁻¹ * α * MulAut.conj x with hα'
  have hα'apply : ∀ y, α' y = x⁻¹ * α (x * y * x⁻¹) * x := by
    intro y
    simp [hα', MulAut.conj_apply, MulAut.conj_inv_apply]
  have hle : (unitU K).map α'.toMonoidHom ≤ unitU K := by
    rintro _ ⟨u, hu, rfl⟩
    have h1 : x * u * x⁻¹ ∈ (S : Subgroup ↥(adjointGroup Tag.D4 K)) := by
      rw [hmemS]; simpa [mul_assoc] using hu
    have h2 := hαS _ h1
    rw [hmemS] at h2
    change α' u ∈ unitU K
    rw [hα'apply]
    exact h2
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [Subgroup.card_map_of_injective α'.injective])

theorem not_inner_conj {C : Type*} [Group C] (x : C) {γ : MulAut C} (h : γ ∉ Inn C) :
    (MulAut.conj x)⁻¹ * γ * MulAut.conj x ∉ Inn C := by
  intro h'
  apply h
  have : γ = MulAut.conj x * ((MulAut.conj x)⁻¹ * γ * MulAut.conj x) * (MulAut.conj x)⁻¹ := by
    group
  rw [this]
  exact mul_mem (mul_mem ⟨x, rfl⟩ h') (inv_mem ⟨x, rfl⟩)

end Transport



end CFSG.LocalAnalysis.GLTheoremA
