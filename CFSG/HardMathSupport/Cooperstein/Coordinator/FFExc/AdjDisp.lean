module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc.AdjRank
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc.MinPair
public import CFSG.LieType.Chevalley.RootCommutator

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg Module
open scoped commutatorElement

section Shift

variable {ι : Type*} [Fintype ι] {K : Type*} [Field K]

theorem End_apply_coord (φ : Module.End K (ι →₀ K)) (w : ι →₀ K) (j : ι) :
    φ w j = ∑ i, w i * φ (Finsupp.single i 1) j := by
  conv_lhs => rw [← Finsupp.univ_sum_single w]
  rw [map_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e : (Finsupp.single i (w i) : ι →₀ K) = w i • Finsupp.single i 1 := by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [e, map_smul, Finsupp.smul_apply, smul_eq_mul]

@[expose] def IsShiftL (F : ι → ℤ) (s : ℤ) (φ : Module.End K (ι →₀ K)) : Prop :=
  ∀ b j, φ (Finsupp.single b 1) j ≠ 0 → F b + s ≤ F j

variable {F : ι → ℤ}

theorem IsShiftL.zero (s : ℤ) : IsShiftL F s (0 : Module.End K (ι →₀ K)) := fun b j h => by
  simp at h

theorem IsShiftL.add {s : ℤ} {φ ψ : Module.End K (ι →₀ K)} (hφ : IsShiftL F s φ)
    (hψ : IsShiftL F s ψ) : IsShiftL F s (φ + ψ) := fun b j h => by
  by_cases h1 : φ (Finsupp.single b 1) j = 0
  · have : ψ (Finsupp.single b 1) j ≠ 0 := by
      intro h2; apply h; simp [h1, h2]
    exact hψ b j this
  · exact hφ b j h1

theorem IsShiftL.smul {s : ℤ} {φ : Module.End K (ι →₀ K)} (c : K) (hφ : IsShiftL F s φ) :
    IsShiftL F s (c • φ) := fun b j h => by
  apply hφ b j
  intro h0; apply h; simp [h0]

theorem IsShiftL.mono {s t : ℤ} {φ : Module.End K (ι →₀ K)} (h : t ≤ s) (hφ : IsShiftL F s φ) :
    IsShiftL F t φ := fun b j hb => by have := hφ b j hb; omega

theorem IsShiftL.neg {s : ℤ} {φ : Module.End K (ι →₀ K)} (hφ : IsShiftL F s φ) :
    IsShiftL F s (-φ) := by
  intro b j h
  apply hφ b j
  intro h0; apply h; simp [h0]

theorem IsShiftL.sub {s : ℤ} {φ ψ : Module.End K (ι →₀ K)} (hφ : IsShiftL F s φ)
    (hψ : IsShiftL F s ψ) : IsShiftL F s (φ - ψ) := by
  exact (sub_eq_add_neg φ ψ).symm ▸ hφ.add hψ.neg

theorem IsShiftL.mul {s t : ℤ} {φ ψ : Module.End K (ι →₀ K)} (hφ : IsShiftL F s φ)
    (hψ : IsShiftL F t ψ) : IsShiftL F (s + t) (φ * ψ) := fun b j h => by
  rw [Module.End.mul_apply, End_apply_coord φ] at h
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have h1 : ψ (Finsupp.single b 1) i ≠ 0 := left_ne_zero_of_mul hi
  have h2 : φ (Finsupp.single i 1) j ≠ 0 := right_ne_zero_of_mul hi
  have := hψ b i h1
  have := hφ i j h2
  omega

end Shift

section Adj

variable {τ : Tag} {K : Type*} [Field K] (f : (Fin τ.rank → ℤ) →+ ℤ)

@[expose] def lblDeg (b : Label τ) : ℤ := f b.latticeWeight

@[expose] def posS : Set (Fin τ.rank → ℤ) := {α | IsRoot τ α ∧ 0 < f α}

variable {f}

theorem pinnedCoeff_deg {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) {k : ℕ} (hk : 1 ≤ k)
    (b j : Label τ) (h : pinnedCoeff τ K α k (Finsupp.single b 1) j ≠ 0) :
    lblDeg f j = lblDeg f b + k * f α := by
  have := mapsWeights_pinnedCoeff (R := K) hα hk j b h
  have h3 : j.latticeWeight = b.latticeWeight + k • α := this
  unfold lblDeg
  rw [h3, map_add, map_nsmul, nsmul_eq_mul]

theorem pinnedX_eq_four (α : Fin τ.rank → ℤ) (c : K) :
    ((pinnedX τ K α c : (Module.End K (RootModule τ K))ˣ) : Module.End K (RootModule τ K)) =
      1 + c • pinnedE τ K α + c ^ 2 • pinnedCoeff τ K α 2 + c ^ 3 • pinnedCoeff τ K α 3 := by
  rw [pinnedX_eq_sum]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, pow_zero, one_smul,
    pinnedCoeff_zero, pinnedCoeff_one, pow_one, zero_add]

theorem isShiftL_pinnedCoeff {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) {k : ℕ}
    (hk : 1 ≤ k) : IsShiftL (lblDeg f) (k * f α) (pinnedCoeff τ K α k) := fun b j h => by
  have := pinnedCoeff_deg (f := f) (K := K) hα hk b j h
  omega

theorem isShiftL_pinnedX_sub_one {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hf : 0 < f α) (c : K) :
    IsShiftL (lblDeg f) (f α)
      (((pinnedX τ K α c : (Module.End K (RootModule τ K))ˣ) : Module.End K (RootModule τ K)) - 1) := by
  have e : ((pinnedX τ K α c : (Module.End K (RootModule τ K))ˣ) : Module.End K (RootModule τ K)) - 1 =
      c • pinnedE τ K α + c ^ 2 • pinnedCoeff τ K α 2 + c ^ 3 • pinnedCoeff τ K α 3 := by
    rw [pinnedX_eq_four]; abel
  rw [e]
  have h1 := isShiftL_pinnedCoeff (K := K) (f := f) hα (k := 1) le_rfl
  have h2 := isShiftL_pinnedCoeff (K := K) (f := f) hα (k := 2) (by norm_num)
  have h3 := isShiftL_pinnedCoeff (K := K) (f := f) hα (k := 3) (by norm_num)
  rw [pinnedCoeff_one] at h1
  exact ((h1.mono (by omega)).smul c |>.add ((h2.mono (by omega)).smul (c ^ 2))).add
    ((h3.mono (by omega)).smul (c ^ 3))

theorem isShiftL_pinnedX_sub_lead {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hf : 0 < f α) (c : K) :
    IsShiftL (lblDeg f) (2 * f α)
      (((pinnedX τ K α c : (Module.End K (RootModule τ K))ˣ) : Module.End K (RootModule τ K)) - 1 -
        c • pinnedE τ K α) := by
  have e : ((pinnedX τ K α c : (Module.End K (RootModule τ K))ˣ) : Module.End K (RootModule τ K)) - 1 -
      c • pinnedE τ K α = c ^ 2 • pinnedCoeff τ K α 2 + c ^ 3 • pinnedCoeff τ K α 3 := by
    rw [pinnedX_eq_four]; abel
  rw [e]
  have h2 := isShiftL_pinnedCoeff (K := K) (f := f) hα (k := 2) (by norm_num)
  have h3 := isShiftL_pinnedCoeff (K := K) (f := f) hα (k := 3) (by norm_num)
  exact (h2.smul (c ^ 2)).add ((h3.mono (by omega)).smul (c ^ 3))

end Adj

section Level

variable {τ : Tag} {K : Type*} [Field K] {f : (Fin τ.rank → ℤ) →+ ℤ}

theorem levelData_adj (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hinj : ∀ γ δ, IsRoot τ γ → IsRoot τ δ → f γ = f δ → γ = δ) :
    LevelData (rootSubgroup τ K) (posS f) f where
  pos γ hγ := hγ.2
  inj γ hγ δ hδ h := hinj γ δ hγ.1 hδ.1 h
  comm γ hγ δ hδ x hx y hy := by
    obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hx
    obtain ⟨d, rfl⟩ := mem_rootSubgroup.1 hy
    by_cases hγδ : γ = δ
    · subst hγδ
      have h1 : ⁅pinnedX τ K γ c, pinnedX τ K γ d⁆ = 1 := by
        rw [commutatorElement_eq_one_iff_mul_comm, ← pinnedX_add, ← pinnedX_add, add_comm]
      rw [h1]; exact one_mem _
    · have hne' : γ ≠ -δ := by
        intro h
        have := congrArg f h
        rw [map_neg] at this
        have := hγ.2; have := hδ.2; omega
      obtain ⟨hr, hc⟩ := CFSG.LieType.Chevalley.simply_laced_root_commutator_unit.{_} τ hτ hγ.1 hδ.1 hγδ hne'
      by_cases hroot : IsRoot τ (γ + δ)
      · obtain ⟨-, hform⟩ := hr hroot
        rw [hform K c d]
        have hmem : γ + δ ∈ posS f := ⟨hroot, by rw [map_add]; have := hγ.2; have := hδ.2; omega⟩
        refine le_lvl (rootSubgroup τ K) (posS f) f hmem (by rw [map_add]) ?_
        exact mem_rootSubgroup.2 ⟨_, rfl⟩
      · have := (hc hroot K _ hx _ hy).eq
        rw [commutatorElement_eq_one_iff_mul_comm.2 this]; exact one_mem _

theorem isShiftL_of_mem_lvl {r : ℤ} (hr : 0 ≤ r) {g : (Module.End K (RootModule τ K))ˣ}
    (hg : g ∈ lvl (rootSubgroup τ K) (posS f) f r) :
    IsShiftL (lblDeg f) r ((g : Module.End K (RootModule τ K)) - 1) := by
  refine lvl_induction (C := fun g : (Module.End K (RootModule τ K))ˣ =>
    IsShiftL (lblDeg f) r ((g : Module.End K (RootModule τ K)) - 1)) hg
    (fun δ hδ hrδ z hz => ?_) ?_ (fun a b ha hb => ?_)
  · obtain ⟨d, rfl⟩ := mem_rootSubgroup.1 hz
    exact (isShiftL_pinnedX_sub_one hδ.1 hδ.2 d).mono hrδ
  · rw [Units.val_one, sub_self]; exact IsShiftL.zero _
  · have e : ((a * b : (Module.End K (RootModule τ K))ˣ) : Module.End K (RootModule τ K)) - 1 =
        ((a : Module.End K (RootModule τ K)) - 1) * ((b : Module.End K (RootModule τ K)) - 1) +
          ((a : Module.End K (RootModule τ K)) - 1) + ((b : Module.End K (RootModule τ K)) - 1) := by
      rw [Units.val_mul]; noncomm_ring
    rw [e]
    exact (((ha.mul hb).mono (by omega)).add ha).add hb

theorem finrank_range_smul (c : K) (hc : c ≠ 0) {V : Type*} [AddCommGroup V] [Module K V]
    [Module.Finite K V] (φ : Module.End K V) :
    finrank K (LinearMap.range (c • φ)) = finrank K (LinearMap.range φ) := by
  have h : LinearMap.range (c • φ) = LinearMap.range φ := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨c • x, by simp [map_smul]⟩
    · rintro ⟨x, rfl⟩
      exact ⟨c⁻¹ • x, by simp [map_smul, smul_smul, hc]⟩
  rw [h]

theorem finrank_range_conj {V : Type*} [AddCommGroup V] [Module K V] [Module.Finite K V]
    (W Wi E : Module.End K V) (h1 : W * Wi = 1) (h2 : Wi * W = 1) (a : K) (ha : a ≠ 0) :
    finrank K (LinearMap.range (a • (W * E * Wi))) = finrank K (LinearMap.range E) := by
  let e : V ≃ₗ[K] V := LinearEquiv.ofLinearMap W Wi
    (by ext v; have := congrArg (fun m => m v) h1; simpa using this)
    (by ext v; have := congrArg (fun m => m v) h2; simpa using this)
  have hr : LinearMap.range (a • (W * E * Wi)) = (LinearMap.range E).map (e : V →ₗ[K] V) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨E (a • Wi x), ⟨_, rfl⟩, ?_⟩
      simp [e, map_smul]
    · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
      refine ⟨a⁻¹ • W z, ?_⟩
      have : Wi (W z) = z := by
        have := congrArg (fun m => m z) h2
        simpa using this
      simp [map_smul, smul_smul, ha, this, e]
  rw [hr]
  exact LinearEquiv.finrank_map_eq e _

theorem finrank_pinnedE_le_of_lead
    (hLD : LevelData (rootSubgroup τ K) (posS f) f) {γ : Fin τ.rank → ℤ} (hγ : γ ∈ posS f)
    {u : (Module.End K (RootModule τ K))ˣ} (hu1 : u ∈ lvl (rootSubgroup τ K) (posS f) f (f γ))
    (hu2 : u ∉ lvl (rootSubgroup τ K) (posS f) f (f γ + 1)) :
    finrank K (LinearMap.range (pinnedE τ K γ)) ≤
      finrank K (LinearMap.range ((u : Module.End K (RootModule τ K)) - 1)) := by
  have : Fintype (Label τ) := Fintype.ofFinite _
  obtain ⟨x, hx, κ, hκ, rfl⟩ := hLD.lvl_decomp hγ hu1
  obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hx
  have hf : 0 < f γ := hγ.2
  have hc : c ≠ 0 := by
    rintro rfl
    apply hu2
    rw [pinnedX_zero, one_mul]
    exact hκ
  set E := pinnedE τ K γ with hE
  have hκ' : IsShiftL (lblDeg f) (f γ + 1) ((κ : Module.End K (RootModule τ K)) - 1) :=
    isShiftL_of_mem_lvl (by omega) hκ
  have hx1 := isShiftL_pinnedX_sub_one (K := K) (f := f) hγ.1 hf c
  have hx2 := isShiftL_pinnedX_sub_lead (K := K) (f := f) hγ.1 hf c
  set n : Module.End K (RootModule τ K) :=
    ((pinnedX τ K γ c * κ : (Module.End K (RootModule τ K))ˣ) : Module.End K (RootModule τ K)) - 1 -
      c • E with hn
  have hsplit : n = (((pinnedX τ K γ c : (Module.End K (RootModule τ K))ˣ) :
      Module.End K (RootModule τ K)) - 1 - c • E) +
      (((pinnedX τ K γ c : (Module.End K (RootModule τ K))ˣ) : Module.End K (RootModule τ K)) - 1) *
        ((κ : Module.End K (RootModule τ K)) - 1) +
      ((κ : Module.End K (RootModule τ K)) - 1) := by
    rw [hn, Units.val_mul]; noncomm_ring
  have hnS : IsShiftL (lblDeg f) (f γ + 1) n := by
    rw [hsplit]
    exact ((hx2.mono (by omega)).add ((hx1.mul hκ').mono (by omega))).add hκ'
  have hψ : ∀ b j, (c • E) (Finsupp.single b 1) j ≠ 0 → lblDeg f j = lblDeg f b + f γ := by
    intro b j h
    have h' : E (Finsupp.single b 1) j ≠ 0 := by
      intro h0; apply h; simp [h0]
    have := pinnedCoeff_deg (f := f) (K := K) hγ.1 (k := 1) le_rfl b j (by rwa [pinnedCoeff_one])
    simpa using this
  have hn' : ∀ b j, n (Finsupp.single b 1) j ≠ 0 → lblDeg f b + f γ < lblDeg f j := by
    intro b j h
    have := hnS b j h
    omega
  have key := finrank_range_le_of_graded (lblDeg f) (f γ) (c • E) n hψ hn'
  have e : c • E + n = ((pinnedX τ K γ c * κ : (Module.End K (RootModule τ K))ˣ) :
      Module.End K (RootModule τ K)) - 1 := by rw [hn]; abel
  rw [e, finrank_range_smul c hc] at key
  exact key

theorem finrank_range_pinnedE (γ : Fin τ.rank → ℤ) :
    finrank K (LinearMap.range (pinnedE τ K γ)) =
      finrank K (LinearMap.range (infE τ K (pinnedData τ γ).1)) := by
  have hε : ((pinnedData τ γ).2.2 : K) ≠ 0 := by
    rcases pinnedSign_eq τ γ with h | h <;> rw [h] <;> simp
  have := finrank_range_conj
    ((pinnedWeyl τ K γ : (Module.End K (RootModule τ K))ˣ) : Module.End K (RootModule τ K))
    (((pinnedWeyl τ K γ)⁻¹ : (Module.End K (RootModule τ K))ˣ) : Module.End K (RootModule τ K))
    (infE τ K (pinnedData τ γ).1) (Units.mul_inv _) (Units.inv_mul _) _ hε
  exact this

theorem exists_lead {M : ℤ}
    (hM : ∀ γ ∈ posS f, f γ < M) {u : (Module.End K (RootModule τ K))ˣ}
    (hu : u ∈ lvl (rootSubgroup τ K) (posS f) f 1) (hu1 : u ≠ 1) :
    ∃ γ ∈ posS f, u ∈ lvl (rootSubgroup τ K) (posS f) f (f γ) ∧
      u ∉ lvl (rootSubgroup τ K) (posS f) f (f γ + 1) := by
  by_contra hcon
  push Not at hcon
  have key : ∀ r : ℤ, 1 ≤ r → u ∈ lvl (rootSubgroup τ K) (posS f) f r := by
    intro r hr
    induction r, hr using Int.leInduction with
    | base => exact hu
    | succ r hr ih =>
      by_cases hex : ∃ γ ∈ posS f, f γ = r
      · obtain ⟨γ, hγ, rfl⟩ := hex
        exact hcon γ hγ ih
      · push Not at hex
        rw [← lvl_eq_succ (rootSubgroup τ K) (posS f) f hex]
        exact ih
  have h1 := key (max M 1) (le_max_right _ _)
  rw [lvl_eq_bot (rootSubgroup τ K) (posS f) f (fun γ hγ => lt_of_lt_of_le (hM γ hγ)
    (le_max_left _ _)), Subgroup.mem_bot] at h1
  exact hu1 h1

end Level

section Main

variable {τ : Tag} {K : Type*} [Field K]

theorem displacement_ge (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {R : List (List ℤ)}
    (hPD : PosData τ R) (N : ℕ)
    (hrk : ∀ j : Fin τ.rank, N ≤ finrank K (LinearMap.range (infE τ K j)))
    {u : (Module.End K (RootModule τ K))ˣ} (hu : u ∈ posUnipotent τ K) (hu1 : u ≠ 1) :
    N ≤ finrank K (LinearMap.range ((u : Module.End K (RootModule τ K)) - 1)) := by
  set f := fWt τ.rank with hf
  have hpos : ∀ α, IsRoot τ α → (0 < f α ↔ 0 < ht α) := fun α hα => hPD.pos α hα
  have hLD := levelData_adj (K := K) (f := f) hτ (fun γ δ hγ hδ h => hPD.inj γ δ hγ hδ h)
  have hu' : u ∈ lvl (rootSubgroup τ K) (posS f) f 1 := by
    have hle : posUnipotent τ K ≤ lvl (rootSubgroup τ K) (posS f) f 1 := by
      unfold posUnipotent rootSpan
      refine iSup₂_le fun α hα => le_lvl (rootSubgroup τ K) (posS f) f ?_ ?_
      · exact ⟨hα.1, (hpos α hα.1).2 hα.2⟩
      · have := (hpos α hα.1).2 hα.2; omega
    exact hle hu
  obtain ⟨M, hM⟩ := ((isRoot_finite (τ := τ)).image f).bddAbove
  obtain ⟨γ, hγ, h1, h2⟩ := exists_lead (M := M + 1)
    (fun γ hγ => by have := hM ⟨γ, hγ.1, rfl⟩; omega) hu' hu1
  have := finrank_pinnedE_le_of_lead hLD hγ h1 h2
  rw [finrank_range_pinnedE] at this
  exact (hrk _).trans this

variable (K)

theorem displacement_E6 {u : (Module.End K (RootModule .E6 K))ˣ} (hu : u ∈ posUnipotent .E6 K)
    (hu1 : u ≠ 1) :
    22 ≤ finrank K (LinearMap.range ((u : Module.End K (RootModule .E6 K)) - 1)) :=
  displacement_ge (Or.inr (Or.inl rfl)) posData_E6 22 finrank_infE_E6 hu hu1

theorem displacement_E7 {u : (Module.End K (RootModule .E7 K))ˣ} (hu : u ∈ posUnipotent .E7 K)
    (hu1 : u ≠ 1) :
    34 ≤ finrank K (LinearMap.range ((u : Module.End K (RootModule .E7 K)) - 1)) :=
  displacement_ge (Or.inr (Or.inr (Or.inl rfl))) posData_E7 34 finrank_infE_E7 hu hu1

theorem displacement_E7_quotient
    (K : Type) [Field K] {u : (Module.End K (RootModule .E7 K))ˣ} (hu : u ∈ posUnipotent .E7 K)
    (hu1 : u ≠ 1) (L : Submodule K (RootModule .E7 K)) (hL : finrank K L ≤ 1)
    (h : L ≤ L.comap ((u : Module.End K (RootModule .E7 K)) - 1)) :
    33 ≤ finrank K (LinearMap.range (L.mapQ L ((u : Module.End K (RootModule .E7 K)) - 1) h)) := by
  have h1 := displacement_E7 K hu hu1
  have h2 := finrank_range_le_mapQ_add_one ((u : Module.End K (RootModule .E7 K)) - 1) L hL h
  omega

end Main

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc
