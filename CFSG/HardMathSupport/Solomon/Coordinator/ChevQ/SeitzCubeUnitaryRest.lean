module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzCubeUnitary
public import CFSG.LieType.Steinberg.CentralExt.SUTwo
public import CFSG.Adapters.SpecialLinearPerfect

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzCubeUnitaryRestAux

open Matrix CFSG.LieType.Seitz CFSG.LieType.SeitzGeneration CFSG.Open CFSG.AGLEmbedding
  CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.LieType.SeitzGeneration.Centers
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.LieType.BorelTits CFSG.ClassicalGroups.UnitaryFlag
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzCubeUnitaryAux

section SUTwo

variable {ℓ f : ℕ} {K : Type} [Field K] [Finite K] [Fact ℓ.Prime] [CharP K ℓ]

local notation "σ₀" => unitaryInvolution K ℓ f

theorem eq_smul_of_comm_two (hσ : IsUnitaryInvolution σ₀) {d : K} (hd : σ₀ d * d = 1)
    (hdd : d ≠ d⁻¹) {g : SUid σ₀ 2} (hg : ∀ s : SUid σ₀ 2, s * g = g * s) :
    ∃ c : K, ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = c • 1 := by
  set M := ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) with hM
  have hcomm : ∀ s : SUid σ₀ 2, ((s : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * M =
      M * ((s : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := fun s => by
    have := congrArg (fun x : SUid σ₀ 2 => ((x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) (hg s)
    simpa only [Subgroup.coe_mul, Units.val_mul] using this
  have hR : σ₀ 0 * 0 + σ₀ 1 * 1 = 1 := by simp
  have h1 := hcomm (diagTwo σ₀ hd)
  have h2 := hcomm (su2 hσ.invol hR)
  have hD : (((diagTwo σ₀ hd : SUid σ₀ 2) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      Matrix.diagonal ![d, d⁻¹] := rfl
  have hS : (((su2 hσ.invol hR : SUid σ₀ 2) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      !![0, -σ₀ 1; 1, σ₀ 0] := rfl
  rw [hD] at h1
  rw [hS] at h2
  have e01 := congrFun (congrFun h1 0) 1
  have e10 := congrFun (congrFun h1 1) 0
  have f01 := congrFun (congrFun h2 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal] at e01 e10 f01
  have hdd' : d - d⁻¹ ≠ 0 := sub_ne_zero.mpr hdd
  have m01 : M 0 1 = 0 := by
    have : (d - d⁻¹) * M 0 1 = 0 := by linear_combination e01
    exact (mul_eq_zero.mp this).resolve_left hdd'
  have m10 : M 1 0 = 0 := by
    have : (d - d⁻¹) * M 1 0 = 0 := by linear_combination -e10
    exact (mul_eq_zero.mp this).resolve_left hdd'
  refine ⟨M 0 0, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j
  · simp
  · simpa using m01
  · simpa using m10
  · simpa using f01

theorem eq_top_of_normal_two (h : UnitaryFieldData ℓ f K) (hq4 : 4 ≤ ℓ ^ f) {d : K}
    (hd : σ₀ d * d = 1) (hdd : d ≠ d⁻¹) {N : Subgroup (SUid σ₀ 2)}
    (hN : ∀ g ∈ N, ∀ s : SUid σ₀ 2, s * g * s⁻¹ ∈ N) {g : SUid σ₀ 2} (hgN : g ∈ N)
    (hg : ∀ c : K, ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) ≠ c • 1) : N = ⊤ := by
  classical
  have hF : Nat.card K = (ℓ ^ f) ^ 2 := h.card_eq_sq
  have hσ : IsUnitaryInvolution σ₀ := Nonsplit.isUnitaryInvolution h
  obtain ⟨ζ, hζ0, hζ⟩ := exists_unitaryInvolution_eq_neg hF
  obtain ⟨P, hP⟩ := exists_wittMatrix hF 2
  let φ : Matrix.SpecialLinearGroup (Fin 2) (CFSG.LieType.Steinberg.fixedSubfield K ℓ f) ≃*
      SUid σ₀ 2 := (CFSG.LieType.Steinberg.hypEquiv hζ0 hζ).trans (conjEquiv P hP)
  have hcardF : 4 ≤ Nat.card (CFSG.LieType.Steinberg.fixedSubfield K ℓ f) := by
    rw [CFSG.LieType.Steinberg.card_fixedSubfield hF]
    exact hq4
  haveI hsimple : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2)
      (CFSG.LieType.Steinberg.fixedSubfield K ℓ f)) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hcardF
  have hperf := CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card
    (CFSG.LieType.Steinberg.fixedSubfield K ℓ f) hcardF
  set N' := N.comap φ.toMonoidHom with hN'
  have hN'n : N'.Normal := ⟨fun x hx y => by
    show φ (y * x * y⁻¹) ∈ N
    rw [map_mul, map_mul, map_inv]
    exact hN _ hx _⟩
  set Z := Subgroup.center (Matrix.SpecialLinearGroup (Fin 2)
    (CFSG.LieType.Steinberg.fixedSubfield K ℓ f)) with hZ
  set ψ := QuotientGroup.mk' Z with hψ
  have hψs : Function.Surjective ψ := QuotientGroup.mk'_surjective Z
  haveI hmapn : (N'.map ψ).Normal := hN'n.map ψ hψs
  have hg' : φ.symm g ∈ N' := by
    show φ (φ.symm g) ∈ N
    rw [MulEquiv.apply_symm_apply]
    exact hgN
  rcases hsimple.eq_bot_or_eq_top_of_normal (N'.map ψ) with hbot | htop
  · exfalso
    have h1 : ψ (φ.symm g) = 1 := by
      have : ψ (φ.symm g) ∈ N'.map ψ := ⟨_, hg', rfl⟩
      rw [hbot] at this
      exact this
    have hz : φ.symm g ∈ Z := by
      rw [hψ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact h1
    have hgc : ∀ s : SUid σ₀ 2, s * g = g * s := by
      intro s
      have h2 := Subgroup.mem_center_iff.1 hz (φ.symm s)
      have h3 := congrArg φ h2
      rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h3
    obtain ⟨c, hc⟩ := eq_smul_of_comm_two hσ hd hdd hgc
    exact hg c hc
  · have hdec : ∀ y, ∃ a ∈ N', ∃ z ∈ Z, y = a * z := by
      intro y
      have : ψ y ∈ N'.map ψ := by rw [htop]; exact Subgroup.mem_top _
      obtain ⟨a, ha, hay⟩ := this
      refine ⟨a, ha, a⁻¹ * y, ?_, by group⟩
      rw [← QuotientGroup.ker_mk' Z, MonoidHom.mem_ker, map_mul, map_inv]
      rw [← hψ, hay, inv_mul_cancel]
    have hN'top : N' = ⊤ := by
      rw [eq_top_iff, ← hperf.commutator_eq_top, commutator_def, Subgroup.commutator_le]
      intro y _ y' _
      obtain ⟨a, ha, z, hz, rfl⟩ := hdec y
      obtain ⟨a', ha', z', hz', rfl⟩ := hdec y'
      have e : a * z * (a' * z') * (a * z)⁻¹ * (a' * z')⁻¹ = a * a' * a⁻¹ * a'⁻¹ := by
        have e1 : z * (a' * z') = (a' * z') * z := (Subgroup.mem_center_iff.1 hz _).symm
        have e2 : z' * a⁻¹ = a⁻¹ * z' := (Subgroup.mem_center_iff.1 hz' _).symm
        rw [_root_.mul_inv_rev, _root_.mul_inv_rev]
        calc a * z * (a' * z') * (z⁻¹ * a⁻¹) * (z'⁻¹ * a'⁻¹)
            = a * (z * (a' * z')) * (z⁻¹ * a⁻¹) * (z'⁻¹ * a'⁻¹) := by group
          _ = a * ((a' * z') * z) * (z⁻¹ * a⁻¹) * (z'⁻¹ * a'⁻¹) := by rw [e1]
          _ = a * a' * (z' * a⁻¹) * (z'⁻¹ * a'⁻¹) := by group
          _ = a * a' * (a⁻¹ * z') * (z'⁻¹ * a'⁻¹) := by rw [e2]
          _ = a * a' * a⁻¹ * a'⁻¹ := by group
      rw [commutatorElement_def, e]
      exact N'.mul_mem (N'.mul_mem (N'.mul_mem ha ha') (N'.inv_mem ha)) (N'.inv_mem ha')
    rw [eq_top_iff]
    intro s _
    have hs : φ.symm s ∈ N' := by rw [hN'top]; exact Subgroup.mem_top _
    have : φ (φ.symm s) ∈ N := hs
    rwa [MulEquiv.apply_symm_apply] at this

end SUTwo

section Dim

theorem finrank_biSup_eq_sum {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {ι : Type*} [DecidableEq ι] {W : ι → Submodule K V}
    (hW : iSupIndep W) (s : Finset ι) :
    Module.finrank K (⨆ i ∈ s, W i : Submodule K V) = ∑ i ∈ s, Module.finrank K (W i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.iSup_insert, Finset.sum_insert hi]
    have hdisj : Disjoint (W i) (⨆ j ∈ s, W j) := by
      have := hW.disjoint_biSup (y := (s : Set ι)) (by simpa using hi)
      simpa using this
    have h3 := Submodule.finrank_sup_add_finrank_inf_eq (W i) (⨆ j ∈ s, W j)
    rw [hdisj.eq_bot, finrank_bot, add_zero, ih] at h3
    exact h3

theorem sum_finrank_le {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {ι : Type*} [Fintype ι] [DecidableEq ι] {W : ι → Submodule K V}
    (hW : iSupIndep W) : ∑ i, Module.finrank K (W i) ≤ Module.finrank K V := by
  rw [← finrank_biSup_eq_sum hW Finset.univ]
  exact Submodule.finrank_le _

variable {ℓ f n p : ℕ} {K : Type} [Field K] [Finite K] [Fact ℓ.Prime] [CharP K ℓ]

local notation "σ₀" => unitaryInvolution K ℓ f

theorem iSupIndep_eigen {Y : Matrix (Fin n) (Fin n) K} {ν ζ : K} (hν : ν ≠ 0)
    (hζ : IsPrimitiveRoot ζ p) :
    iSupIndep fun l : Fin p => Module.End.eigenspace (Matrix.toLin' Y) (ν * ζ ^ (l : ℕ)) := by
  have hinj : Function.Injective fun l : Fin p => ν * ζ ^ (l : ℕ) := by
    intro a b hab
    have h1 : ζ ^ (a : ℕ) = ζ ^ (b : ℕ) := mul_left_cancel₀ hν hab
    exact Fin.ext (hζ.pow_inj a.2 b.2 h1)
  exact (Module.End.eigenspaces_iSupIndep (Matrix.toLin' Y)).comp hinj

theorem card_mul_finrank_eigen (hp : p.Prime) {X B : SUid σ₀ n} {ζ : K}
    (hζ : IsPrimitiveRoot ζ p)
    (hBX : ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ζ • (((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))
    {μ : K} (hμ : μ ≠ 0)
    (hBp : ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = (μ ^ p) • 1) (l : Fin p) :
    p * Module.finrank K (Module.End.eigenspace
      (Matrix.toLin' ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) (μ * ζ ^ (l : ℕ))) = n := by
  classical
  have hpK : (p : K) ≠ 0 := heis_natCast_ne_zero hζ hp.two_le
  have hBT : (Matrix.toLin' ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ^ p =
      algebraMap K (Module.End K (Fin n → K)) (μ ^ p) := by
    have h2 := congrArg Matrix.toLinAlgEquiv' hBp
    rw [map_pow, map_smul, map_one] at h2
    rw [Algebra.algebraMap_eq_smul_one]
    exact h2
  set W : Fin p → Submodule K (Fin n → K) := fun l => Module.End.eigenspace
    (Matrix.toLin' ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) (μ * ζ ^ (l : ℕ)) with hW
  have heq : ∀ l', Module.finrank K (W l') = Module.finrank K (W l) := fun l' =>
    le_antisymm (finrank_eigen_le hζ hBX μ l' l) (finrank_eigen_le hζ hBX μ l l')
  have hsum : ∑ l', Module.finrank K (W l') = p * Module.finrank K (W l) := by
    rw [Finset.sum_congr rfl fun l' _ => heq l', Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul]
  have hle : ∑ l', Module.finrank K (W l') ≤ n := by
    have := sum_finrank_le (iSupIndep_eigen (Y := ((B : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K)) hμ hζ)
    rwa [Module.finrank_fin_fun] at this
  have hsup : (⨆ l', W l') = ⊤ := NonPth.iSup_eigenspace_eq_top_p hp hpK hζ hμ hBT
  have hge : n ≤ ∑ l', Module.finrank K (W l') := by
    have := finrank_iSup_le_sum (K := K) W
    rwa [hsup, finrank_top, Module.finrank_fin_fun] at this
  show p * Module.finrank K (W l) = n
  omega

end Dim


section Plane

variable {ℓ f n p : ℕ} {K : Type} [Field K] [Finite K] [Fact ℓ.Prime] [CharP K ℓ]

local notation "σ₀" => unitaryInvolution K ℓ f

theorem isON_pair {σ : K ≃+* K} (hσ : ∀ c, σ (σ c) = c) {e₁ e₂ : Fin n → K}
    (h11 : herm σ e₁ e₁ = 1) (h22 : herm σ e₂ e₂ = 1) (h12 : herm σ e₁ e₂ = 0) :
    ONExt.IsON σ ![e₁, e₂] := by
  have h21 : herm σ e₂ e₁ = 0 := herm_eq_zero_comm σ hσ h12
  intro i j
  fin_cases i <;> fin_cases j <;> simp [h11, h22, h12, h21]

theorem orthoEmb_pair (e₁ e₂ : Fin n → K) (c : Fin 2 → K) :
    orthoEmb ![e₁, e₂] c = c 0 • e₁ + c 1 • e₂ := by
  simp [orthoEmb_apply, Fin.sum_univ_two]

theorem smul_orthoEmb_pair {σ : K ≃+* K} {s : SUid σ n} {e₁ e₂ : Fin n → K} {l₁ l₂ : K}
    (h₁ : s • e₁ = l₁ • e₁) (h₂ : s • e₂ = l₂ • e₂) (c : Fin 2 → K) :
    s • orthoEmb ![e₁, e₂] c = orthoEmb ![e₁, e₂] ![l₁ * c 0, l₂ * c 1] := by
  rw [orthoEmb_pair, orthoEmb_pair, smul_add, smul_comm s (c 0), smul_comm s (c 1), h₁, h₂,
    smul_smul, smul_smul]
  simp [mul_comm]

theorem inv_smul_of_eigen {σ : K ≃+* K} {s : SUid σ n} {e : Fin n → K} {l : K} (hl : l ≠ 0)
    (h₁ : s • e = l • e) : s⁻¹ • e = l⁻¹ • e := by
  rw [inv_smul_eq_iff, smul_comm, h₁, smul_smul, inv_mul_cancel₀ hl, one_smul]

theorem allCenters_plane (h : UnitaryFieldData ℓ f K) (hp : p.Prime) (hp2 : p ≠ 2)
    (hq4 : 4 ≤ ℓ ^ f) {G : Type*} [Group G] [Finite G] (π : SUid σ₀ n →* G)
    {E : Subgroup G} (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 3)
    {X B r : SUid σ₀ n} (hXE : π X ∈ E) (hBE : π B ∈ E) (hrE : π r ∈ E) (hr1 : π r ≠ 1)
    (hB1 : π B ≠ 1) (hBr : π B ∉ Subgroup.zpowers (π r)) (hXB : π X ∉ Subgroup.zpowers (π B))
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hζN : h.bar ζ * ζ = 1)
    (hBX : ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ζ • (((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))
    {β : K} (hXp : ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = β • 1)
    {lam : K} (hlamN : h.bar lam * lam = 1) {e₁ e₂ : Fin n → K}
    (hB₁ : ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ e₁ = lam • e₁)
    (hB₂ : ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ e₂ = lam • e₂)
    (h11 : herm σ₀ e₁ e₁ = 1) (h22 : herm σ₀ e₂ e₂ = 1) (h12 : herm σ₀ e₁ e₂ = 0)
    {l₁ l₂ : K} (hl₁ : l₁ ≠ 0) (hl₂ : l₂ ≠ 0)
    (hr₁ : ((r : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ e₁ = l₁ • e₁)
    (hr₂ : ((r : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ e₂ = l₂ • e₂) :
    AllCenters ((hyperClosure p ⊤ E).comap π) (Submodule.span K (Set.range ![e₁, e₂])) := by
  classical
  have hσ : IsUnitaryInvolution σ₀ := Nonsplit.isUnitaryInvolution h
  have hσi := hσ.invol
  have hσb : ∀ c, σ₀ c = h.bar c := Nonsplit.unitaryInvolution_eq_bar h
  haveI : NeZero p := ⟨hp.ne_zero⟩
  set Bm : Matrix (Fin n) (Fin n) K := ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hBm
  have he₁0 : e₁ ≠ 0 := by
    rintro rfl
    rw [herm_zero_left] at h11
    exact zero_ne_one h11
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0
      exact absurd (Subsingleton.elim e₁ 0) he₁0
    · exact h0
  have hβN := bar_mul_eq_one_of_SUid_scalar h hn hXp
  have hlam0 : lam ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hlamN
    exact zero_ne_one hlamN
  have hlamkN : ∀ k : ℕ, h.bar (lam * ζ ^ k) * (lam * ζ ^ k) = 1 := by
    intro k
    rw [map_mul, map_pow]
    calc h.bar lam * h.bar ζ ^ k * (lam * ζ ^ k) = (h.bar lam * lam) * (h.bar ζ * ζ) ^ k := by
          ring
      _ = 1 := by rw [hlamN, hζN, one_pow, one_mul]
  have horthB : ∀ a b : ℕ, a % p ≠ b % p → ∀ u v, Bm *ᵥ u = (lam * ζ ^ a) • u →
      Bm *ᵥ v = (lam * ζ ^ b) • v → herm σ₀ u v = 0 := by
    intro a b hab u v hu hv
    rw [pow_eq_pow_mod hζ a] at hu
    rw [pow_eq_pow_mod hζ b] at hv
    exact herm_eq_zero_of_eigen hu hv (bar_mul_ne_one h hlam0 hlamN hζ hζN
      (i := ⟨a % p, Nat.mod_lt _ hp.pos⟩) (i' := ⟨b % p, Nat.mod_lt _ hp.pos⟩)
      (fun he => hab (congrArg Fin.val he)))
  set xs : Fin 2 → Fin n → K := ![e₁, e₂] with hxs
  have hxsON : ONExt.IsON σ₀ xs := isON_pair hσi h11 h22 h12
  have hBe₁ : B • e₁ = lam • e₁ := by rw [smul_def]; exact hB₁
  have hBe₂ : B • e₂ = lam • e₂ := by rw [smul_def]; exact hB₂
  have hre₁ : r • e₁ = l₁ • e₁ := by rw [smul_def]; exact hr₁
  have hre₂ : r • e₂ = l₂ • e₂ := by rw [smul_def]; exact hr₂
  have hBU : ∀ c, B • orthoEmb xs c = lam • orthoEmb xs c := by
    intro c
    rw [orthoEmb_pair, smul_add, smul_comm B (c 0), smul_comm B (c 1), hBe₁, hBe₂, smul_add,
      smul_comm lam (c 0), smul_comm lam (c 1)]
  have hBUst : ∀ c, ∃ d, B • orthoEmb xs c = orthoEmb xs d :=
    fun c => ⟨_, smul_orthoEmb_pair hBe₁ hBe₂ c⟩
  have hBUst' : ∀ c, ∃ d, B⁻¹ • orthoEmb xs c = orthoEmb xs d :=
    fun c => ⟨_, smul_orthoEmb_pair (inv_smul_of_eigen hlam0 hBe₁)
      (inv_smul_of_eigen hlam0 hBe₂) c⟩
  have hrUst : ∀ c, ∃ d, r • orthoEmb xs c = orthoEmb xs d :=
    fun c => ⟨_, smul_orthoEmb_pair hre₁ hre₂ c⟩
  have hrUst' : ∀ c, ∃ d, r⁻¹ • orthoEmb xs c = orthoEmb xs d :=
    fun c => ⟨_, smul_orthoEmb_pair (inv_smul_of_eigen hl₁ hre₁) (inv_smul_of_eigen hl₂ hre₂) c⟩
  have hBres : ONExt.resMat σ₀ xs Bm = lam • 1 := resMat_eq_smul_of_eigen hxsON hBU
  set H := (hyperClosure p ⊤ E).comap π with hH
  set ε := ONExt.ext hσi hxsON with hε
  set HU := H.comap ε with hHU
  have hnorm : ∀ g ∈ HU, ∀ t : SUid σ₀ 2, t * g * t⁻¹ ∈ HU := by
    refine conj_mem_of_tv hσ le_rfl (fun h3 => absurd h3 (by norm_num)) ?_
    intro a ha c hc g hg
    set w := orthoEmb xs a with hw
    have hwB : Bm *ᵥ w = (lam * ζ ^ 0) • w := by
      rw [pow_zero, mul_one, ← smul_def]
      exact hBU a
    have hXkB : ∀ k : ℕ, Bm *ᵥ ((X ^ k) • w) = (lam * ζ ^ k) • ((X ^ k) • w) := fun k => by
      have := mulVec_pow_smul_of_qcomm hBX k 0 w hwB
      rwa [zero_add] at this
    have horthS : ∀ k k' : Fin p, herm σ₀ ((X ^ (k : ℕ)) • w) ((X ^ (k' : ℕ)) • w) = 0 := by
      intro k k'
      by_cases hkk : k = k'
      · subst hkk
        rw [herm_smul_smul, hw, herm_orthoEmb hxsON, ha]
      · refine horthB k k' ?_ _ _ (hXkB k) (hXkB k')
        rw [Nat.mod_eq_of_lt k.2, Nat.mod_eq_of_lt k'.2]
        exact fun he => hkk (Fin.ext he)
    obtain ⟨S, hS, hXS⟩ :=
      exists_siegel_orbit hσi (p := p) hXp (by rw [hσb]; exact hβN) horthS hc
    have hBS : B * S = S * B := siegel_comm_of_eigen hS
      (lam := fun k : Fin p => lam * ζ ^ (k : ℕ)) (fun k => by rw [smul_def]; exact hXkB k)
      (fun k => by rw [hσb]; exact hlamkN _)
    have hSH : S ∈ H := mem_hyperClosure_of_comm hp hE hcard hBE hXE hB1 hXB
      (by rw [← map_mul, ← map_mul, hBS]) (by rw [← map_mul, ← map_mul, hXS])
    have hSU : ∀ c', S • orthoEmb xs c' = ε (tv hσi ha hc) • orthoEmb xs c' := by
      intro c'
      have hc'B : Bm *ᵥ orthoEmb xs c' = (lam * ζ ^ 0) • orthoEmb xs c' := by
        rw [pow_zero, mul_one, ← smul_def]
        exact hBU c'
      rw [hS, ONExt.ext_tv_smul hσi hxsON ha hc, ← hw]
      congr 1
      rw [Finset.sum_eq_single (0 : Fin p)]
      · simp
      · intro k _ hk0
        have h0 : herm σ₀ ((X ^ (k : ℕ)) • w) (orthoEmb xs c') = 0 := by
          refine horthB k 0 ?_ _ _ (hXkB k) hc'B
          rw [Nat.mod_eq_of_lt k.2, Nat.zero_mod]
          exact fun he => hk0 (Fin.ext he)
        rw [h0, mul_zero, zero_smul]
      · intro h0
        exact absurd (Finset.mem_univ _) h0
    set T := (ε (tv hσi ha hc))⁻¹ * S with hT
    have hTU : ∀ c', T • orthoEmb xs c' = orthoEmb xs c' := by
      intro c'
      rw [hT, mul_smul, hSU, inv_smul_smul]
    have hTU' : ∀ c', T⁻¹ • orthoEmb xs c' = orthoEmb xs c' := by
      intro c'
      rw [inv_smul_eq_iff, hTU]
    have hTres : ONExt.resMat σ₀ xs ((T : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
      rw [resMat_eq_smul_of_eigen hxsON (lam := 1) (fun c' => by rw [hTU, one_smul]), one_smul]
    have hTg : T * ε g = ε g * T :=
      commute_ext_of_resMat hσi hxsON (fun c' => ⟨c', hTU c'⟩) (fun c' => ⟨c', hTU' c'⟩)
        (by rw [hTres, Matrix.mul_one, Matrix.one_mul])
    have hS' : S = ε (tv hσi ha hc) * T := by rw [hT, mul_inv_cancel_left]
    have hconj : T * ε g * T⁻¹ = ε g := by rw [hTg, mul_inv_cancel_right]
    have key : ε (tv hσi ha hc * g * (tv hσi ha hc)⁻¹) = S * ε g * S⁻¹ := by
      calc ε (tv hσi ha hc * g * (tv hσi ha hc)⁻¹)
          = ε (tv hσi ha hc) * ε g * (ε (tv hσi ha hc))⁻¹ := by rw [map_mul, map_mul, map_inv]
        _ = ε (tv hσi ha hc) * (T * ε g * T⁻¹) * (ε (tv hσi ha hc))⁻¹ := by rw [hconj]
        _ = (ε (tv hσi ha hc) * T) * ε g * (ε (tv hσi ha hc) * T)⁻¹ := by group
        _ = S * ε g * S⁻¹ := by rw [← hS']
    show ε (tv hσi ha hc * g * (tv hσi ha hc)⁻¹) ∈ H
    rw [key]
    exact H.mul_mem (H.mul_mem hSH hg) (H.inv_mem hSH)
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  have hζζ : ζ ≠ ζ⁻¹ := by
    intro he
    have h1 : ζ ^ 2 = 1 := by
      rw [sq]
      calc ζ * ζ = ζ * ζ⁻¹ := by rw [← he]
        _ = 1 := mul_inv_cancel₀ hζ0
    have := Nat.le_of_dvd (by norm_num) (hζ.dvd_of_pow_eq_one 2 h1)
    have := hp.two_le
    omega
  have hs₁ : r • orthoEmb xs (Pi.single 0 1) = l₁ • orthoEmb xs (Pi.single 0 1) := by
    rw [ONExt.orthoEmb_single]
    exact hre₁
  have hs₂ : r • orthoEmb xs (Pi.single 1 1) = l₂ • orthoEmb xs (Pi.single 1 1) := by
    rw [ONExt.orthoEmb_single]
    exact hre₂
  have hc₁₁ : herm σ₀ (Pi.single 0 1 : Fin 2 → K) (Pi.single 0 1) = 1 := by
    rw [herm_single_left, map_one, one_mul, Pi.single_eq_same]
  have hc₂₂ : herm σ₀ (Pi.single 1 1 : Fin 2 → K) (Pi.single 1 1) = 1 := by
    rw [herm_single_left, map_one, one_mul, Pi.single_eq_same]
  have hc₁₂ : herm σ₀ (Pi.single 0 1 : Fin 2 → K) (Pi.single 1 1) = 0 := by
    rw [herm_single_left, map_one, one_mul, Pi.single_eq_of_ne (by decide)]
  have hζσ : σ₀ ζ * ζ = 1 := by rw [hσb]; exact hζN
  obtain ⟨g₀, hg₀s, hg₀r⟩ := exists_nonscalar_comm hσ hxsON hrUst hrUst' hc₁₁ hc₂₂ hc₁₂ hl₁ hl₂
    hs₁ hs₂ hζσ hζζ
  have hg₀B : B * ε g₀ = ε g₀ * B :=
    commute_ext_of_resMat hσi hxsON hBUst hBUst'
      (by rw [hBres, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul])
  have hg₀HU : g₀ ∈ HU := by
    show π (ε g₀) ∈ hyperClosure p ⊤ E
    exact mem_hyperClosure_of_comm hp hE hcard hrE hBE hr1 hBr
      (by rw [← map_mul, ← map_mul, hg₀r]) (by rw [← map_mul, ← map_mul, hg₀B])
  have htop : HU = ⊤ := eq_top_of_normal_two h hq4 hζσ hζζ hnorm hg₀HU hg₀s
  exact ONExt.allCenters_of_forall_ext_mem hσi hxsON fun g => by
    have : g ∈ HU := by rw [htop]; exact Subgroup.mem_top g
    exact this

end Plane

section Assembly

variable {ℓ f n : ℕ} {K : Type} [Field K] [Finite K] [Fact ℓ.Prime] [CharP K ℓ]

local notation "σ₀" => unitaryInvolution K ℓ f

theorem exists_mem_fix_of_norm_two (hσ : IsUnitaryInvolution σ₀) {H : Subgroup (SUid σ₀ n)}
    {m : ℕ} (hm : m = 2) {x : Fin m → Fin n → K} (hx : ONExt.IsON σ₀ x)
    (hH : ∀ c : Fin m → K, herm σ₀ c c = 0 → IsCenter H (orthoEmb x c))
    {d d' : Fin m → K} {s : K} (hs : s ≠ 0) (hd : herm σ₀ d d = s) (hd' : herm σ₀ d' d' = s) :
    ∃ g ∈ H, g • orthoEmb x d = orthoEmb x d' ∧
      ∀ v, (∀ u, herm σ₀ (orthoEmb x u) v = 0) → g • v = v := by
  subst hm
  have hsfix : σ₀ s = s := by rw [← hd]; exact herm_self_fixed σ₀ hσ.invol d
  obtain ⟨b, hb⟩ := hσ.norm_surj s hsfix hs
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_mul] at hb
    exact hs hb.symm
  have hunit : ∀ e : Fin 2 → K, herm σ₀ e e = s →
      σ₀ ((b⁻¹ • e) 0) * (b⁻¹ • e) 0 + σ₀ ((b⁻¹ • e) 1) * (b⁻¹ • e) 1 = 1 := by
    intro e he
    have hσb0 : σ₀ b ≠ 0 := (map_ne_zero σ₀).mpr hb0
    have h1 : herm σ₀ (b⁻¹ • e) (b⁻¹ • e) = 1 := by
      rw [herm_smul_left, herm_smul_right, he, map_inv₀, ← hb]
      field_simp
    rwa [herm_fin_two] at h1
  set A := su2 hσ.invol (hunit d hd) with hA
  set A' := su2 hσ.invol (hunit d' hd') with hA'
  have hAe : ∀ e : Fin 2 → K, ∀ he : herm σ₀ e e = s,
      su2 hσ.invol (hunit e he) • (Pi.single 0 1 : Fin 2 → K) = b⁻¹ • e := by
    intro e he
    rw [su2_smul_single]
    funext i
    fin_cases i <;> rfl
  set t := A' * A⁻¹ with ht
  have htT : t ∈ T σ₀ 2 := by rw [T_two_eq_top hσ]; exact Subgroup.mem_top _
  obtain ⟨g, hg, hgφ, hgv⟩ := exists_mem_of_T (orthoEmb x) (herm_orthoEmb hx) hH htT
  refine ⟨g, hg, ?_, hgv⟩
  have hdu : d = b • (b⁻¹ • d) := by rw [smul_smul, mul_inv_cancel₀ hb0, one_smul]
  have hdu' : d' = b • (b⁻¹ • d') := by rw [smul_smul, mul_inv_cancel₀ hb0, one_smul]
  have htd : t • d = d' := by
    rw [hdu, smul_comm t b, ht, mul_smul, ← hAe d hd, inv_smul_smul, hAe d' hd', ← hdu']
  rw [hgφ, htd]

theorem allCenters_insert (h : UnitaryFieldData ℓ f K) (hq2 : ℓ ^ f ≠ 2)
    {H : Subgroup (SUid σ₀ n)} {ι : Type*} [DecidableEq ι] {e : ι → Fin n → K}
    (he : ∀ i j, herm σ₀ (e i) (e j) = if i = j then 1 else 0) {S : Finset ι}
    (hS : 2 ≤ S.card) (hA : AllCenters H (Submodule.span K (e '' ↑S))) {i j : ι} (hi : i ∉ S)
    (hj : j ∈ S) (hji : AllCenters H (Submodule.span K {e j, e i})) :
    AllCenters H (Submodule.span K (e '' ↑(insert i S))) := by
  classical
  have hσ : IsUnitaryInvolution σ₀ := Nonsplit.isUnitaryInvolution h
  have hσi := hσ.invol
  have hσb : ∀ c, σ₀ c = h.bar c := Nonsplit.unitaryInvolution_eq_bar h
  set x : Fin S.card → Fin n → K := fun k => e (S.equivFin.symm k) with hx
  have hxON : ONExt.IsON σ₀ x := by
    intro k k'
    simp only [hx]
    rw [he]
    by_cases hkk : k = k'
    · subst hkk
      simp
    · rw [if_neg (fun h0 => hkk (S.equivFin.symm.injective (Subtype.ext h0))), if_neg hkk]
  have hxS : Set.range x = e '' ↑S := by
    ext v
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨_, (S.equivFin.symm k).2, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨S.equivFin ⟨k, hk⟩, by simp [hx]⟩
  have hspanS : Submodule.span K (Set.range x) = Submodule.span K (e '' ↑S) := by rw [hxS]
  have hcent : ∀ c, herm σ₀ c c = 0 → IsCenter H (orthoEmb x c) := fun c hc =>
    hA _ (hspanS ▸ orthoEmb_mem_span x c) (by rw [herm_orthoEmb hxON]; exact hc)
  have hix : ∀ k, herm σ₀ (x k) (e i) = 0 := by
    intro k
    simp only [hx]
    rw [he, if_neg]
    intro h0
    apply hi
    rw [← h0]
    exact (S.equivFin.symm k).2
  have horth : ∀ c, herm σ₀ (orthoEmb x c) (e i) = 0 := ONExt.herm_orthoEmb_of_orth x hix
  have hij : i ≠ j := fun h0 => hi (h0 ▸ hj)
  have hii : herm σ₀ (e i) (e i) = 1 := by rw [he, if_pos rfl]
  have hjj : herm σ₀ (e j) (e j) = 1 := by rw [he, if_pos rfl]
  have hie : herm σ₀ (e i) (e j) = 0 := by rw [he, if_neg hij]
  have hje : herm σ₀ (e j) (e i) = 0 := by rw [he, if_neg (Ne.symm hij)]
  set j' := S.equivFin ⟨j, hj⟩ with hj'
  have hxj : x j' = e j := by simp [hx, hj']
  intro v hv hvi
  rw [Finset.coe_insert, Set.image_insert_eq, Submodule.span_insert] at hv
  obtain ⟨y, hy, w, hw, rfl⟩ := Submodule.mem_sup.1 hv
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
  obtain ⟨dd, rfl⟩ := (mem_span_range_iff x w).1 (hspanS ▸ hw)
  have hiw : herm σ₀ (e i) (orthoEmb x dd) = 0 := herm_eq_zero_comm σ₀ hσi (horth dd)
  have hnorm : herm σ₀ (c • e i + orthoEmb x dd) (c • e i + orthoEmb x dd) =
      σ₀ c * c + herm σ₀ dd dd := by
    simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, hii, hiw, horth,
      herm_orthoEmb hxON]
    ring
  rw [hnorm] at hvi
  by_cases hs : herm σ₀ dd dd = 0
  · have hc : σ₀ c * c = 0 := by rw [hs, add_zero] at hvi; exact hvi
    have hc0 : c = 0 := by
      rcases mul_eq_zero.1 hc with h0 | h0
      · exact (map_eq_zero σ₀).1 h0
      · exact h0
    rw [hc0, zero_smul, zero_add]
    exact hcent dd hs
  · set s := herm σ₀ dd dd with hsdef
    have hsfix : σ₀ s = s := herm_self_fixed σ₀ hσi dd
    obtain ⟨a, ha⟩ := hσ.norm_surj s hsfix hs
    set d' : Fin S.card → K := a • Pi.single j' 1 with hd'def
    have hd' : herm σ₀ d' d' = s := by
      rw [hd'def, herm_smul_left, herm_smul_right, herm_single_left, map_one, one_mul,
        Pi.single_eq_same, mul_one, ha]
    have hd'e : orthoEmb x d' = a • e j := by
      rw [hd'def, map_smul, ONExt.orthoEmb_single, hxj]
    obtain ⟨g, hg, hgd, hgfix⟩ : ∃ g ∈ H, g • orthoEmb x dd = orthoEmb x d' ∧
        ∀ v, (∀ u, herm σ₀ (orthoEmb x u) v = 0) → g • v = v := by
      rcases Nat.lt_or_ge S.card 3 with hm3 | hm3
      · exact exists_mem_fix_of_norm_two hσ (by omega) hxON hcent hs rfl hd'
      · obtain ⟨s₀, hs₀, hs₀1⟩ := Nonsplit.exists_norm_ne_one h hq2
        exact exists_mem_fix_of_norm hσ (Or.inr ⟨hm3, s₀, hs₀, by rw [hσb]; exact hs₀1⟩)
          (herm_orthoEmb hxON) hcent hs rfl hd'
    have hgi : g • e i = e i := hgfix _ horth
    have hgv : g • (c • e i + orthoEmb x dd) = c • e i + a • e j := by
      rw [smul_add, smul_comm, hgi, hgd, hd'e]
    have hmem : c • e i + a • e j ∈ Submodule.span K ({e j, e i} : Set (Fin n → K)) :=
      Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    have hiso : herm σ₀ (c • e i + a • e j) (c • e i + a • e j) = 0 := by
      simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, hii, hjj, hie,
        hje]
      linear_combination hvi + ha
    have hcen := (hji _ hmem hiso).map (H.inv_mem hg)
    rwa [← hgv, inv_smul_smul] at hcen

theorem allCenters_union (h : UnitaryFieldData ℓ f K) (hq2 : ℓ ^ f ≠ 2)
    {H : Subgroup (SUid σ₀ n)} {ι : Type*} [DecidableEq ι] {e : ι → Fin n → K}
    (he : ∀ i j, herm σ₀ (e i) (e j) = if i = j then 1 else 0) {S : Finset ι}
    (hS : 2 ≤ S.card) (hA : AllCenters H (Submodule.span K (e '' ↑S))) (D : Finset ι)
    (hnbr : ∀ i ∈ D, i ∉ S ∧ ∃ j ∈ S, AllCenters H (Submodule.span K {e j, e i})) :
    AllCenters H (Submodule.span K (e '' ↑(S ∪ D))) := by
  induction D using Finset.induction_on with
  | empty => simpa using hA
  | insert i D hiD ih =>
    have ih' := ih fun k hk => hnbr k (Finset.mem_insert_of_mem hk)
    obtain ⟨hiS, j, hj, hji⟩ := hnbr i (Finset.mem_insert_self i D)
    have hrw : S ∪ insert i D = insert i (S ∪ D) := by
      ext k
      simp only [Finset.mem_union, Finset.mem_insert]
      tauto
    rw [hrw]
    refine allCenters_insert h hq2 he (le_trans hS (Finset.card_le_card Finset.subset_union_left))
      ih' ?_ (Finset.mem_union_left _ hj) hji
    simp [hiS, hiD]

end Assembly


section Two

variable {ℓ f n p : ℕ} {K : Type} [Field K] [Finite K] [Fact ℓ.Prime] [CharP K ℓ]

local notation "σ₀" => unitaryInvolution K ℓ f

theorem four_le_of_dvd_succ (hp : p.Prime) (hp2 : p ≠ 2) {q : ℕ} (hq0 : q ≠ 0) (hpq : p ∣ q + 1)
    (hq2 : q ≠ 2) : 4 ≤ q := by
  by_contra hlt
  push Not at hlt
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  interval_cases q
  · exact hq0 rfl
  · have := Nat.le_of_dvd (by norm_num) hpq
    omega
  · exact hq2 rfl
  · have h4 := Nat.le_of_dvd (by norm_num) hpq
    have hp4 : p = 3 ∨ p = 4 := by omega
    rcases hp4 with rfl | rfl
    · exact absurd hpq (by norm_num)
    · exact absurd hp (by norm_num)

theorem linearIndependent_of_orthonormal {σ : K ≃+* K} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {e : ι → Fin n → K} (he : ∀ i j, herm σ (e i) (e j) = if i = j then 1 else 0) :
    LinearIndependent K e := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h1 := congrArg (herm σ (e i)) hg
  rw [herm_zero_right, herm_sum_right] at h1
  simp only [herm_smul_right, he, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true] at h1
  exact h1

theorem hyperGen_of_nonab_two (h : UnitaryFieldData ℓ f K) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ ℓ ^ f + 1) (hq2 : ℓ ^ f ≠ 2) (hn : n ≤ 2 * p) {G : Type*} [Group G] [Finite G]
    (π : SUid σ₀ n →* G) (hπ : Function.Surjective π)
    (hker' : ∀ g : SUid σ₀ n, (∃ c : K,
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = c • 1) → π g = 1)
    {E : Subgroup G} (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 3)
    {X Y r : SUid σ₀ n} (hXE : π X ∈ E) (hYE : π Y ∈ E) (hrE : π r ∈ E) (hr1 : π r ≠ 1)
    (hYr : π Y ∉ Subgroup.zpowers (π r))
    (hXcl : π X ∉ Subgroup.closure ({π r, π Y} : Set G))
    (hrX : r * X = X * r) (hrY : r * Y = Y * r)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hζN : h.bar ζ * ζ = 1)
    (hYX : ((Y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ζ • (((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((Y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))
    {β ν ρ : K} (hXp : ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = β • 1)
    (hν : ν ≠ 0) (hYp : ((Y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = (ν ^ p) • 1)
    (hρ : ρ ≠ 0) (hrp : ((r : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = (ρ ^ p) • 1) :
    HyperGen p (⊤ : Subgroup G) E := by
  classical
  have hfp : Fact p.Prime := ⟨hp⟩
  have hσ : IsUnitaryInvolution σ₀ := Nonsplit.isUnitaryInvolution h
  have hσi := hσ.invol
  have hσb : ∀ c, σ₀ c = h.bar c := Nonsplit.unitaryInvolution_eq_bar h
  have hpK : (p : K) ≠ 0 := heis_natCast_ne_zero hζ hp.two_le
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hq4 : 4 ≤ ℓ ^ f :=
    four_le_of_dvd_succ hp hp2 (pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero) hpq hq2
  have hrs : ∀ c : K, ((r : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ≠ c • 1 :=
    fun c hc => hr1 (hker' r ⟨c, hc⟩)
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0
      exact absurd (Subsingleton.elim _ _) (hrs 0)
    · exact h0
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  set Xm : Matrix (Fin n) (Fin n) K := ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hXm
  set Ym : Matrix (Fin n) (Fin n) K := ((Y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hYm
  set rm : Matrix (Fin n) (Fin n) K := ((r : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hrm
  have hmemE : ∀ (M : Matrix (Fin n) (Fin n) K) (a : K) (v : Fin n → K),
      v ∈ Module.End.eigenspace (Matrix.toLin' M) a ↔ M *ᵥ v = a • v := fun M a v => by
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
  have hpowT : ∀ (M : Matrix (Fin n) (Fin n) K) (c : K), M ^ p = c • 1 →
      (Matrix.toLin' M) ^ p = algebraMap K (Module.End K (Fin n → K)) c := by
    intro M c hM
    have h2 := congrArg Matrix.toLinAlgEquiv' hM
    rw [map_pow, map_smul, map_one] at h2
    rw [Algebra.algebraMap_eq_smul_one]
    exact h2
  have hνN := bar_mul_eq_one_of_SUid_pow h hp hp2 hpq hn0 hν hYp
  have hρN := bar_mul_eq_one_of_SUid_pow h hp hp2 hpq hn0 hρ hrp
  have hrcl : π r ∈ Subgroup.closure ({π r, π Y} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hYcl : π Y ∈ Subgroup.closure ({π r, π Y} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hYr' : Y * r = r * Y := hrY.symm
  have hBm : ∀ t : ℕ, (((Y * r ^ t : SUid σ₀ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      Ym * rm ^ t := fun t => by
    simp only [Subgroup.coe_mul, Subgroup.coe_pow, Units.val_mul, Units.val_pow_eq_pow_val, hYm,
      hrm]
  have hBE : ∀ t : ℕ, π (Y * r ^ t) ∈ E := fun t => by
    rw [map_mul, map_pow]
    exact E.mul_mem hYE (E.pow_mem hrE t)
  have hBX : ∀ t : ℕ, (((Y * r ^ t : SUid σ₀ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Xm =
      ζ • (Xm * (((Y * r ^ t : SUid σ₀ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
    intro t
    have hc : Commute rm Xm := coe_comm hrX
    rw [hBm, Matrix.mul_assoc, (hc.pow_left t).eq, ← Matrix.mul_assoc, hYX, Matrix.smul_mul,
      Matrix.mul_assoc]
  have hBr : ∀ t : ℕ, π (Y * r ^ t) ∉ Subgroup.zpowers (π r) := by
    intro t hmem
    apply hYr
    have : π Y = π (Y * r ^ t) * ((π r) ^ t)⁻¹ := by
      rw [map_mul, map_pow, mul_inv_cancel_right]
    rw [this]
    exact Subgroup.mul_mem _ hmem (Subgroup.inv_mem _ (Subgroup.npow_mem_zpowers _ _))
  have hB1 : ∀ t : ℕ, π (Y * r ^ t) ≠ 1 := fun t h1 => hBr t (h1 ▸ Subgroup.one_mem _)
  have hXB : ∀ t : ℕ, π X ∉ Subgroup.zpowers (π (Y * r ^ t)) := by
    intro t hmem
    apply hXcl
    refine (Subgroup.zpowers_le.2 ?_) hmem
    rw [map_mul, map_pow]
    exact Subgroup.mul_mem _ hYcl (Subgroup.pow_mem _ hrcl t)
  set W : Fin p → Submodule K (Fin n → K) :=
    fun l => Module.End.eigenspace (Matrix.toLin' Ym) (ν * ζ ^ (l : ℕ)) with hW
  have horthE : ∀ (s : SUid σ₀ n) (c : K), c ≠ 0 → h.bar c * c = 1 → ∀ a b : Fin p, a ≠ b →
      ∀ u v, ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ u = (c * ζ ^ (a : ℕ)) • u →
        ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v = (c * ζ ^ (b : ℕ)) • v →
        herm σ₀ u v = 0 := fun s c hc0 hcN a b hab u v hu hv =>
    herm_eq_zero_of_eigen hu hv (bar_mul_ne_one h hc0 hcN hζ hζN hab)
  have hWorth : ∀ l l' : Fin p, l ≠ l' → ∀ u ∈ W l, ∀ v ∈ W l', herm σ₀ u v = 0 :=
    fun l l' hll u hu v hv => horthE Y ν hν hνN l l' hll u v ((hmemE _ _ u).1 hu)
      ((hmemE _ _ v).1 hv)
  have hW0 : W ⟨0, hp.pos⟩ ≠ ⊥ := by
    intro h0
    have hc := card_mul_finrank_eigen hp hζ hYX hν hYp ⟨0, hp.pos⟩
    have : Module.finrank K (W ⟨0, hp.pos⟩) = 0 := by rw [h0, finrank_bot]
    rw [show Module.finrank K (Module.End.eigenspace (Matrix.toLin' Ym)
      (ν * ζ ^ ((⟨0, hp.pos⟩ : Fin p) : ℕ))) = 0 from this, mul_zero] at hc
    omega
  have hYr_lin : Matrix.toLin' Ym * Matrix.toLin' rm = Matrix.toLin' rm * Matrix.toLin' Ym := by
    apply LinearMap.ext
    intro v
    rw [Module.End.mul_apply, Module.End.mul_apply, Matrix.toLin'_apply, Matrix.toLin'_apply,
      Matrix.toLin'_apply, Matrix.toLin'_apply, mulVec_mulVec, mulVec_mulVec, coe_comm hrY]
  set J : Fin p × Fin p → Submodule K (Fin n → K) := fun ij =>
    W ij.1 ⊓ Module.End.eigenspace (Matrix.toLin' rm) (ρ * ζ ^ (ij.2 : ℕ)) with hJ
  have hJtop : ⨆ ij, J ij = ⊤ :=
    iSup_inf_eigenspace_eq_top hp hpK hζ hYr_lin hν hρ (hpowT _ _ hYp) (hpowT _ _ hrp)
  have hJorth : ∀ ij ij' : Fin p × Fin p, ij ≠ ij' → ∀ u ∈ J ij, ∀ v ∈ J ij',
      herm σ₀ u v = 0 := by
    intro ij ij' hne u hu v hv
    by_cases h1 : ij.1 = ij'.1
    · have h2 : ij.2 ≠ ij'.2 := fun h2 => hne (Prod.ext h1 h2)
      exact horthE r ρ hρ hρN ij.2 ij'.2 h2 u v ((hmemE _ _ u).1 hu.2) ((hmemE _ _ v).1 hv.2)
    · exact hWorth ij.1 ij'.1 h1 u hu.1 v hv.1
  have hJsep : ∀ ij, ((idForm h n).domRestrict₁₂ (J ij) (J ij)).SeparatingLeft :=
    NonCube.separatingLeft_of_orth_iSup (idForm_separatingLeft h n) J
      (fun ij ij' hne u hu v hv => by
        rw [Nonsplit.idForm_eq_herm h]; exact hJorth ij ij' hne u hu v hv) hJtop
  have hJshift : ∀ (l l' c : Fin p), J (l, c) ≠ ⊥ → J (l', c) ≠ ⊥ := by
    intro l l' c hne h0
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    set k := (l' : ℕ) + p - l with hk
    have h1 := mulVec_pow_smul_of_qcomm hYX k l v ((hmemE _ _ v).1 hv.1)
    have hlk : (l : ℕ) + k = l' + p := by have := l.2; omega
    rw [hlk, pow_add, hζ.pow_eq_one, mul_one] at h1
    have h2 : rm *ᵥ ((X ^ k) • v) = (ρ * ζ ^ (c : ℕ)) • ((X ^ k) • v) := by
      rw [smul_def, mulVec_mulVec, coe_comm (Commute.pow_right hrX k).eq, ← mulVec_mulVec,
        (hmemE _ _ v).1 hv.2, mulVec_smul]
    have hmem : (X ^ k) • v ∈ J (l', c) := ⟨(hmemE _ _ _).2 h1, (hmemE _ _ _).2 h2⟩
    rw [h0, Submodule.mem_bot] at hmem
    exact hv0 (by simpa using congrArg (fun w => (X ^ k)⁻¹ • w) hmem)
  obtain ⟨c₁, c₂, hc12, hJ₁, hJ₂⟩ :=
    exists_two_eigen hζ hpK hp hrX hrY hYX hν hYp hρ hrp hrs ⟨0, hp.pos⟩ hW0
  have hunit : ∀ ij, J ij ≠ ⊥ → ∃ e, e ∈ J ij ∧ herm σ₀ e e = 1 := fun ij hne => by
    obtain ⟨e, he, he1⟩ := exists_unit_of_separatingLeft h hne (hJsep ij)
    exact ⟨e, he, he1⟩
  choose a haJ ha using fun l : Fin p => hunit (l, c₁) (hJshift _ l c₁ hJ₁)
  choose b hbJ hb using fun l : Fin p => hunit (l, c₂) (hJshift _ l c₂ hJ₂)
  set e : Fin p ⊕ Fin p → Fin n → K := Sum.elim a b with he_def
  have hc21 : c₂ ≠ c₁ := Ne.symm hc12
  have he : ∀ i j, herm σ₀ (e i) (e j) = if i = j then 1 else 0 := by
    rintro (l | l) (l' | l')
    · by_cases hll : l = l'
      · subst hll
        simp [he_def, ha]
      · rw [if_neg (by simpa using hll)]
        exact hJorth (l, c₁) (l', c₁) (fun h0 => hll (congrArg Prod.fst h0)) _ (haJ l) _ (haJ l')
    · rw [if_neg (by simp)]
      exact hJorth (l, c₁) (l', c₂) (fun h0 => hc12 (congrArg Prod.snd h0)) _ (haJ l) _ (hbJ l')
    · rw [if_neg (by simp)]
      exact hJorth (l, c₂) (l', c₁) (fun h0 => hc21 (congrArg Prod.snd h0)) _ (hbJ l) _ (haJ l')
    · by_cases hll : l = l'
      · subst hll
        simp [he_def, hb]
      · rw [if_neg (by simpa using hll)]
        exact hJorth (l, c₂) (l', c₂) (fun h0 => hll (congrArg Prod.fst h0)) _ (hbJ l) _ (hbJ l')
  set H := (hyperClosure p ⊤ E).comap π with hH
  have hcz : ((c₁ : ℕ) : ZMod p) - ((c₂ : ℕ) : ZMod p) ≠ 0 := by
    intro h0
    apply hc12
    rw [sub_eq_zero, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt c₁.2,
      Nat.mod_eq_of_lt c₂.2] at h0
    exact Fin.ext h0
  have hρζ : ∀ c : ℕ, ρ * ζ ^ c ≠ 0 := fun c => mul_ne_zero hρ (pow_ne_zero _ hζ0)
  have hplane : ∀ l l' : Fin p, AllCenters H (Submodule.span K (Set.range ![a l, b l'])) := by
    intro l l'
    set t : ℕ := ((((l' : ℕ) : ZMod p) - ((l : ℕ) : ZMod p)) *
      (((c₁ : ℕ) : ZMod p) - ((c₂ : ℕ) : ZMod p))⁻¹).val with ht
    have htZ : (t : ZMod p) = (((l' : ℕ) : ZMod p) - ((l : ℕ) : ZMod p)) *
        (((c₁ : ℕ) : ZMod p) - ((c₂ : ℕ) : ZMod p))⁻¹ := ZMod.natCast_zmod_val _
    have hcong : ((l : ℕ) + c₁ * t) % p = ((l' : ℕ) + c₂ * t) % p := by
      rw [← ZMod.natCast_eq_natCast_iff']
      push_cast
      have key : ((c₁ : ℕ) : ZMod p) * t - ((c₂ : ℕ) : ZMod p) * t =
          ((l' : ℕ) : ZMod p) - ((l : ℕ) : ZMod p) := by
        rw [← sub_mul, htZ, mul_comm, mul_assoc, inv_mul_cancel₀ hcz, mul_one]
      linear_combination key
    have hBv : ∀ (a' c : Fin p) (v : Fin n → K), v ∈ J (a', c) →
        (((Y * r ^ t : SUid σ₀ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v =
          ((ν * ρ ^ t) * ζ ^ (((a' : ℕ) + c * t) % p)) • v := by
      intro a' c v hv
      rw [hBm, ← mulVec_mulVec, pow_mulVec_of_eigen ((hmemE _ _ v).1 hv.2), mulVec_smul,
        (hmemE _ _ v).1 hv.1, smul_smul, ← pow_eq_pow_mod hζ]
      congr 1
      rw [pow_add, mul_pow, ← pow_mul]
      ring
    have hB₁ := hBv l c₁ (a l) (haJ l)
    have hB₂ := hBv l' c₂ (b l') (hbJ l')
    rw [← hcong] at hB₂
    have hlamN : h.bar ((ν * ρ ^ t) * ζ ^ (((l : ℕ) + c₁ * t) % p)) *
        ((ν * ρ ^ t) * ζ ^ (((l : ℕ) + c₁ * t) % p)) = 1 := by
      rw [map_mul, map_mul, map_pow, map_pow]
      calc h.bar ν * h.bar ρ ^ t * h.bar ζ ^ (((l : ℕ) + c₁ * t) % p) *
            (ν * ρ ^ t * ζ ^ (((l : ℕ) + c₁ * t) % p))
          = (h.bar ν * ν) * (h.bar ρ * ρ) ^ t * (h.bar ζ * ζ) ^ (((l : ℕ) + c₁ * t) % p) := by
            ring
        _ = 1 := by rw [hνN, hρN, hζN, one_pow, one_pow, one_mul, one_mul]
    have hab : herm σ₀ (a l) (b l') = 0 := by
      have := he (Sum.inl l) (Sum.inr l')
      simpa [he_def] using this
    exact allCenters_plane h hp hp2 hq4 π hE hcard hXE (hBE t) hrE hr1 (hB1 t) (hBr t) (hXB t)
      hζ hζN (hBX t) hXp hlamN hB₁ hB₂ (ha l) (hb l') hab (hρζ c₁) (hρζ c₂)
      ((hmemE _ _ _).1 (haJ l).2) ((hmemE _ _ _).1 (hbJ l').2)
  set i0 : Fin p := ⟨0, hp.pos⟩ with hi0
  set S₀ : Finset (Fin p ⊕ Fin p) := {Sum.inl i0, Sum.inr i0} with hS₀
  have hS₀card : 2 ≤ S₀.card := by
    rw [hS₀, Finset.card_pair (by simp)]
  have hS₀A : AllCenters H (Submodule.span K (e '' ↑S₀)) := by
    have : e '' ↑S₀ = Set.range ![a i0, b i0] := by
      ext v
      simp only [hS₀, Finset.coe_insert, Finset.coe_singleton, Set.image_insert_eq,
        Set.image_singleton, he_def, Sum.elim_inl, Sum.elim_inr, Matrix.range_cons,
        Matrix.range_empty, Set.union_empty, Set.mem_insert_iff, Set.mem_singleton_iff,
        Set.mem_union]
    rw [this]
    exact hplane i0 i0
  have hnbr : ∀ i ∈ (Finset.univ \ S₀), i ∉ S₀ ∧
      ∃ j ∈ S₀, AllCenters H (Submodule.span K {e j, e i}) := by
    rintro (l | l) hi
    · refine ⟨(Finset.mem_sdiff.1 hi).2, Sum.inr i0, by simp [hS₀], ?_⟩
      have : ({e (Sum.inr i0), e (Sum.inl l)} : Set (Fin n → K)) = Set.range ![a l, b i0] := by
        simp only [he_def, Sum.elim_inl, Sum.elim_inr, Matrix.range_cons, Matrix.range_empty,
          Set.union_empty]
        exact Set.pair_comm _ _
      rw [this]
      exact hplane l i0
    · refine ⟨(Finset.mem_sdiff.1 hi).2, Sum.inl i0, by simp [hS₀], ?_⟩
      have : ({e (Sum.inl i0), e (Sum.inr l)} : Set (Fin n → K)) = Set.range ![a i0, b l] := by
        simp only [he_def, Sum.elim_inl, Sum.elim_inr, Matrix.range_cons, Matrix.range_empty,
          Set.union_empty]
        rfl
      rw [this]
      exact hplane i0 l
  have hall := allCenters_union h hq2 he hS₀card hS₀A (Finset.univ \ S₀) hnbr
  rw [Finset.union_sdiff_of_subset (Finset.subset_univ _), Finset.coe_univ, Set.image_univ] at hall
  have hli : LinearIndependent K e := linearIndependent_of_orthonormal he
  have hcardι : Fintype.card (Fin p ⊕ Fin p) = 2 * p := by
    rw [Fintype.card_sum, Fintype.card_fin, two_mul]
  have hle : 2 * p ≤ n := by
    have := hli.fintype_card_le_finrank
    rwa [hcardι, Module.finrank_fin_fun] at this
  have htop : Submodule.span K (Set.range e) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (by rw [hcardι, Module.finrank_fin_fun]; omega)
  rw [htop] at hall
  have hHtop : H = ⊤ := eq_top_of_forall_isCenter hσ (by omega) (fun h3 => by omega)
    fun v hv => hall v Submodule.mem_top hv
  intro k _
  obtain ⟨g, rfl⟩ := hπ k
  have hg : g ∈ H := by rw [hHtop]; exact Subgroup.mem_top g
  exact hg

end Two


section Model

variable {ℓ f n : ℕ} {K : Type} [Field K] [Finite K] [Fact ℓ.Prime] [CharP K ℓ]

local notation "σ₀" => unitaryInvolution K ℓ f

theorem map_scalar_eq_one {d : TauCeti.ValidLieTypeIndex} {m : ℕ} {q : TauCeti.PrimePower}
    (hd : d.1 = .twistedA m q) (h : UnitaryFieldData ℓ f K) (hq2 : ℓ ^ f ≠ 2) (hn : 3 ≤ n)
    (π : SUid σ₀ n →* Cat d) (hπ : Function.Surjective π)
    (hker : ∀ g ∈ π.ker, ∃ c : K, ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = c • 1)
    {x y : SUid σ₀ n} (hxy : x * y ≠ y * x) (g : SUid σ₀ n)
    (hg : ∃ c : K, ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = c • 1) : π g = 1 := by
  classical
  obtain ⟨d, hv⟩ := d
  simp only at hd
  subst hd
  set ℓ' := TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA m q, hv⟩ with hℓ'
  set f' := TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA m q, hv⟩ with hf'
  have hU := CFSG.RankThree.PartTwo.Census.unitaryFieldData_galoisField ℓ' f'
    (TauCeti.ValidLieTypeIndex.fieldExponent_pos ⟨.twistedA m q, hv⟩)
  have : Fact ℓ'.Prime := ⟨hU.prime⟩
  have hqcard : ℓ' ^ f' = q.card := by simp [hℓ', hf', TauCeti.ValidLieTypeIndex.characteristic,
    TauCeti.ValidLieTypeIndex.fieldExponent, TauCeti.PrimePower.card_def]
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hm2 : 2 ≤ m := hrange.1
  have hfin := hU.finite
  let e := CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj m q hv
  have hsimpleP : IsSimpleGroup (StatedProj (StatedSU (m + 1) (ℓ' ^ f')
      (GaloisField ℓ' (2 * f')))) :=
    CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU (GaloisField ℓ' (2 * f')) ℓ'
      f' (by rw [hU.card, pow_mul']) (m + 1) (by omega) (by
        intro h32
        obtain ⟨h31, h2⟩ := Prod.mk.inj h32
        have h3 := hrange.2 (by omega)
        rw [hqcard] at h2
        omega)
  haveI : IsSimpleGroup (Cat ⟨.twistedA m q, hv⟩) := MulEquiv.isSimpleGroup e
  have hσ : IsUnitaryInvolution σ₀ := Nonsplit.isUnitaryInvolution h
  have hσb : ∀ c, σ₀ c = h.bar c := Nonsplit.unitaryInvolution_eq_bar h
  have hcen : Subgroup.center (Cat ⟨.twistedA m q, hv⟩) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (Subgroup.center (Cat ⟨.twistedA m q, hv⟩)) with h0 | h0
    · exact h0
    · exfalso
      have hperf := isPerfect_SUid hσ hn (fun _ => by
        obtain ⟨s, hs0, hs1⟩ := Nonsplit.exists_norm_ne_one h hq2
        exact ⟨s, hs0, by rw [hσb]; exact hs1⟩)
      have hle : commutator (SUid σ₀ n) ≤ π.ker := by
        rw [commutator_def, Subgroup.commutator_le]
        intro g₁ _ g₂ _
        rw [MonoidHom.mem_ker, map_commutatorElement]
        have hc : π g₁ ∈ Subgroup.center (Cat ⟨.twistedA m q, hv⟩) := by
          rw [h0]; exact Subgroup.mem_top _
        rw [commutatorElement_def, ← Subgroup.mem_center_iff.1 hc (π g₂)]
        group
      have hxk : x ∈ π.ker := hle (by rw [hperf.commutator_eq_top]; exact Subgroup.mem_top _)
      obtain ⟨c, hc⟩ := hker x hxk
      exact hxy (comm_of_scalar hc y)
  have hgc : π g ∈ Subgroup.center (Cat ⟨.twistedA m q, hv⟩) := by
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨s, rfl⟩ := hπ z
    obtain ⟨c, hc⟩ := hg
    rw [← map_mul, ← map_mul, comm_of_scalar hc s]
  rw [hcen] at hgc
  exact hgc

end Model

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzCubeUnitaryRestAux
