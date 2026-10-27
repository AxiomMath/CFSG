module

public import CFSG.GH74.Generic.S1.KL5Lift
public import CFSG.GH74.Filter.Small.Eigenbasis

public section

open Module Module.End Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped commutatorElement

namespace CFSG.GH74.Generic.S1

theorem kl5_comb : ∀ n ≤ 4, ∀ (e₀ e₁ : Fin n → Bool),
    Even (Finset.univ.filter (fun j => e₀ j = true)).card →
    Even (Finset.univ.filter (fun j => e₁ j = true)).card →
    (∃ j k, e₀ j ≠ e₀ k) → (∃ j k, e₁ j ≠ e₁ k) →
    (∃ j k, xor (e₀ j) (e₁ j) ≠ xor (e₀ k) (e₁ k)) →
    ∀ j k, e₀ j = e₀ k → e₁ j = e₁ k → j = k := by
  intro n hn
  interval_cases n <;> decide

open Classical in
theorem kl5_prod_eq_one_iff_even {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) {n : ℕ} (μ : Fin n → K)
    (hμ : ∀ j, μ j * μ j = 1) :
    ∏ j, μ j = 1 ↔ Even (Finset.univ.filter (fun j => decide (μ j = -1) = true)).card := by
  classical
  have hneg : (-1 : K) ≠ 1 := by
    intro h
    apply h2
    have : (2 : K) = 1 - (-1) := by ring
    rw [this, h]; ring
  have h1 : ∀ j, μ j = if decide (μ j = -1) = true then -1 else 1 := by
    intro j
    have : (μ j - 1) * (μ j + 1) = 0 := by linear_combination hμ j
    rcases mul_eq_zero.1 this with h | h
    · have : μ j = 1 := sub_eq_zero.1 h
      have hn' : ¬ (μ j = -1) := by rw [this]; exact fun h => hneg h.symm
      simp [this]
    · have : μ j = -1 := eq_neg_of_add_eq_zero_left h
      simp [this]
  have : ∏ j, μ j = (-1) ^ (Finset.univ.filter (fun j => decide (μ j = -1) = true)).card := by
    calc ∏ j, μ j = ∏ j, (if decide (μ j = -1) = true then (-1 : K) else 1) :=
          Finset.prod_congr rfl fun j _ => h1 j
      _ = _ := by rw [Finset.prod_ite]; simp
  rw [this]
  exact neg_one_pow_eq_one_iff_even hneg


open Classical in
theorem kl5_commute_of_fourgroup {ι : Type} [Fintype ι] [DecidableEq ι] (hι : Fintype.card ι ≤ 4)
    {K : Type} [Field K] (h2 : (2 : K) ≠ 0) (h₁ h₂ : GL ι K)
    (hs₁ : h₁ * h₁ = 1) (hs₂ : h₂ * h₂ = 1) (hc : h₁ * h₂ = h₂ * h₁)
    (hd₁ : (h₁ : Matrix ι ι K).det = 1) (hd₂ : (h₂ : Matrix ι ι K).det = 1)
    (hn₁ : ¬ ∃ c : K, (h₁ : Matrix ι ι K) = c • 1) (hn₂ : ¬ ∃ c : K, (h₂ : Matrix ι ι K) = c • 1)
    (hn₃ : ¬ ∃ c : K, ((h₁ * h₂ : GL ι K) : Matrix ι ι K) = c • 1)
    (g g' : GL ι K) (hg₁ : g * h₁ = h₁ * g) (hg₂ : g * h₂ = h₂ * g)
    (hg'₁ : g' * h₁ = h₁ * g') (hg'₂ : g' * h₂ = h₂ * g') : g * g' = g' * g := by
  set V := ι → K with hV
  let T : GL ι K → (V →ₗ[K] V) := fun x => Matrix.toLin' (x : Matrix ι ι K)
  have hT_mul : ∀ x y : GL ι K, T (x * y) = T x * T y := fun x y => by
    show Matrix.toLin' ((x * y : GL ι K) : Matrix ι ι K) = Matrix.toLin' (x : Matrix ι ι K) * Matrix.toLin' (y : Matrix ι ι K)
    rw [Units.val_mul, Matrix.toLin'_mul]
    rfl
  have hT_one : T 1 = 1 := by
    show Matrix.toLin' ((1 : GL ι K) : Matrix ι ι K) = 1
    rw [Units.val_one, Matrix.toLin'_one]
    rfl
  have hTinj : Function.Injective T := fun x y h => Units.ext (Matrix.toLin'.injective h)
  let F : Fin 2 → End K V := ![T h₁, T h₂]
  have hFcomm : ∀ i j, Commute (F i) (F j) := by
    intro i j
    have h12 : Commute (T h₁) (T h₂) := by
      show T h₁ * T h₂ = T h₂ * T h₁
      rw [← hT_mul, ← hT_mul, hc]
    fin_cases i <;> fin_cases j <;> simp [F, Commute.refl, h12, h12.symm]
  have hFsq : ∀ i, F i ^ 2 = 1 := by
    intro i
    fin_cases i
    · show T h₁ ^ 2 = 1
      rw [sq, ← hT_mul, hs₁, hT_one]
    · show T h₂ ^ 2 = 1
      rw [sq, ← hT_mul, hs₂, hT_one]
  obtain ⟨b, μ, hb⟩ := CFSG.GH74.Filter.exists_basis_common_eigenvectors_of_sq_eq_one h2 F hFcomm hFsq
  have hn4 : Module.finrank K V ≤ 4 := by
    have : Module.finrank K V = Fintype.card ι := Module.finrank_fintype_fun_eq_card K
    rw [this]; exact hι
  have hneg : (-1 : K) ≠ 1 := by
    intro h
    apply h2
    have : (2 : K) = 1 - (-1) := by ring
    rw [this, h]; ring
  have hμsq : ∀ i j, μ i j * μ i j = 1 := fun i j => by
    have h1 : (F i ^ 2) (b j) = b j := by rw [hFsq, Module.End.one_apply]
    rw [sq, Module.End.mul_apply, hb, map_smul, hb, smul_smul] at h1
    have h3 : (μ i j * μ i j - 1) • b j = 0 := by rw [sub_smul, h1, one_smul, sub_self]
    exact sub_eq_zero.1 ((smul_eq_zero.1 h3).resolve_right (b.ne_zero j))
  have hsign : ∀ i j, μ i j = 1 ∨ μ i j = -1 := fun i j => by
    have : (μ i j - 1) * (μ i j + 1) = 0 := by linear_combination hμsq i j
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl (sub_eq_zero.1 h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  have hdiag : ∀ i, LinearMap.toMatrix b b (F i) = Matrix.diagonal (μ i) := fun i => by
    ext k j
    by_cases hkj : k = j
    · subst hkj; simp [LinearMap.toMatrix_apply, hb]
    · simp [LinearMap.toMatrix_apply, hb, hkj]
  have hprod₀ : ∏ j, μ 0 j = 1 := by
    have h : (LinearMap.toMatrix b b (F 0)).det = 1 := by
      rw [LinearMap.det_toMatrix]
      show LinearMap.det (Matrix.toLin' (h₁ : Matrix ι ι K)) = 1
      rw [LinearMap.det_toLin']; exact hd₁
    rw [hdiag, Matrix.det_diagonal] at h; exact h
  have hprod₁ : ∏ j, μ 1 j = 1 := by
    have h : (LinearMap.toMatrix b b (F 1)).det = 1 := by
      rw [LinearMap.det_toMatrix]
      show LinearMap.det (Matrix.toLin' (h₂ : Matrix ι ι K)) = 1
      rw [LinearMap.det_toLin']; exact hd₂
    rw [hdiag, Matrix.det_diagonal] at h; exact h
  have hscalar : ∀ (x : GL ι K) (c : K), (∀ j, T x (b j) = c • b j) →
      (x : Matrix ι ι K) = c • 1 := by
    intro x c hx
    have h1 : T x = c • (1 : End K V) := b.ext fun j => by
      rw [hx j]; rfl
    have h' : Matrix.toLin' (x : Matrix ι ι K) = Matrix.toLin' (c • (1 : Matrix ι ι K)) := by
      rw [map_smul, Matrix.toLin'_one]; exact h1
    exact Matrix.toLin'.injective h'
  have hnonconst : ∀ (x : GL ι K) (ν : Fin (Module.finrank K V) → K),
      (∀ j, T x (b j) = ν j • b j) → (¬ ∃ c : K, (x : Matrix ι ι K) = c • 1) →
      ∃ j k, ν j ≠ ν k := by
    intro x ν hx hnx
    by_contra hcon
    push Not at hcon
    apply hnx
    rcases isEmpty_or_nonempty (Fin (Module.finrank K V)) with hemp | hne
    · refine ⟨0, ?_⟩
      have : IsEmpty ι := by
        have h0 : Fintype.card ι = 0 := by
          have : Module.finrank K V = Fintype.card ι := Module.finrank_fintype_fun_eq_card K
          rw [← this]
          have h00 := Fintype.card_eq_zero_iff.2 hemp
          rwa [Fintype.card_fin] at h00
        exact Fintype.card_eq_zero_iff.1 h0
      exact Matrix.ext fun i => (IsEmpty.false i).elim
    · obtain ⟨j₀⟩ := hne
      exact ⟨ν j₀, hscalar x (ν j₀) fun j => by rw [hx j, hcon j j₀]⟩
  let e₀ : Fin (Module.finrank K V) → Bool := fun j => decide (μ 0 j = -1)
  let e₁ : Fin (Module.finrank K V) → Bool := fun j => decide (μ 1 j = -1)
  have hcnt₀ := (kl5_prod_eq_one_iff_even h2 (μ 0) (hμsq 0)).1 hprod₀
  have hcnt₁ := (kl5_prod_eq_one_iff_even h2 (μ 1) (hμsq 1)).1 hprod₁
  have hT₁ : ∀ j, T h₁ (b j) = μ 0 j • b j := fun j => hb 0 j
  have hT₂ : ∀ j, T h₂ (b j) = μ 1 j • b j := fun j => hb 1 j
  have hT₃ : ∀ j, T (h₁ * h₂) (b j) = (μ 0 j * μ 1 j) • b j := fun j => by
    rw [hT_mul]
    show T h₁ (T h₂ (b j)) = _
    rw [hT₂ j, map_smul, hT₁ j, smul_smul, mul_comm]
  obtain ⟨j₁, k₁, hjk₁⟩ := hnonconst h₁ (μ 0) hT₁ hn₁
  obtain ⟨j₂, k₂, hjk₂⟩ := hnonconst h₂ (μ 1) hT₂ hn₂
  obtain ⟨j₃, k₃, hjk₃⟩ := hnonconst (h₁ * h₂) (fun j => μ 0 j * μ 1 j) hT₃ hn₃
  have he : ∀ i j k, decide (μ i j = -1) = decide (μ i k = -1) → μ i j = μ i k := by
    intro i j k h
    rcases hsign i j with h1 | h1 <;> rcases hsign i k with h2' | h2' <;>
      simp [h1, h2', hneg.symm] at h ⊢
  have hxor : ∀ j, μ 0 j * μ 1 j = if xor (e₀ j) (e₁ j) = true then -1 else 1 := by
    intro j
    rcases hsign 0 j with h0 | h0 <;> rcases hsign 1 j with h1 | h1 <;>
      simp [e₀, e₁, h0, h1, hneg.symm]
  have hinj := kl5_comb (Module.finrank K V) hn4 e₀ e₁ hcnt₀ hcnt₁
    ⟨j₁, k₁, fun h => hjk₁ (he 0 j₁ k₁ h)⟩ ⟨j₂, k₂, fun h => hjk₂ (he 1 j₂ k₂ h)⟩
    ⟨j₃, k₃, fun h => hjk₃ (by simp only [hxor, h])⟩
  have hinj' : ∀ j k, μ 0 j = μ 0 k → μ 1 j = μ 1 k → j = k := fun j k h0 h1 =>
    hinj j k (by simp [e₀, h0]) (by simp [e₁, h1])
  have hdiagonal : ∀ x : GL ι K, x * h₁ = h₁ * x → x * h₂ = h₂ * x →
      ∀ j, ∃ c : K, T x (b j) = c • b j := by
    intro x hx₁ hx₂ j
    refine ⟨b.repr (T x (b j)) j, ?_⟩
    have hcm : ∀ y : GL ι K, y * x = x * y → T y (T x (b j)) = T x (T y (b j)) := fun y hy => by
      have := congrArg (fun z => T z (b j)) hy
      simpa [hT_mul] using this
    have hv : ∀ i, F i (T x (b j)) = μ i j • T x (b j) := by
      intro i
      fin_cases i
      · show T h₁ (T x (b j)) = μ 0 j • T x (b j)
        rw [hcm h₁ hx₁.symm, hT₁ j, map_smul]
      · show T h₂ (T x (b j)) = μ 1 j • T x (b j)
        rw [hcm h₂ hx₂.symm, hT₂ j, map_smul]
    have hcoord : ∀ i k, μ i k * b.repr (T x (b j)) k = μ i j * b.repr (T x (b j)) k := by
      intro i k
      have h1 : b.repr (F i (T x (b j))) k = μ i k * b.repr (T x (b j)) k := by
        have := LinearMap.toMatrix_mulVec_repr b b (F i) (T x (b j))
        have h' := congrFun this k
        rw [hdiag i, Matrix.mulVec_diagonal] at h'
        exact h'.symm
      rw [hv i, map_smul] at h1
      simpa [mul_comm] using h1.symm
    have hzero : ∀ k, k ≠ j → b.repr (T x (b j)) k = 0 := by
      intro k hkj
      by_contra hne
      have e0 : μ 0 k = μ 0 j := mul_right_cancel₀ hne (hcoord 0 k)
      have e1 : μ 1 k = μ 1 j := mul_right_cancel₀ hne (hcoord 1 k)
      exact hkj (hinj' k j e0 e1)
    apply b.repr.injective
    ext k
    by_cases hk : k = j
    · subst hk; simp
    · simp [hzero k hk, hk]
  have hcomm_on : ∀ j, T (g * g') (b j) = T (g' * g) (b j) := by
    intro j
    obtain ⟨c, hc⟩ := hdiagonal g hg₁ hg₂ j
    obtain ⟨c', hc'⟩ := hdiagonal g' hg'₁ hg'₂ j
    rw [hT_mul, hT_mul]
    show T g (T g' (b j)) = T g' (T g (b j))
    rw [hc', hc, map_smul, map_smul, hc, hc', smul_smul, smul_smul, mul_comm]
  exact hTinj (b.ext hcomm_on)



theorem kl5_det_eq_one_of_perfect {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]
    {H : Subgroup (GL ι K)} {P : Subgroup ↥H} (hP : ⁅P, P⁆ = P) :
    ∀ x ∈ P, (((x : ↥H) : GL ι K) : Matrix ι ι K).det = 1 := by
  let φ : ↥H →* Kˣ := (Matrix.GeneralLinearGroup.det).comp H.subtype
  have hle : P ≤ φ.ker := by
    rw [← hP]
    refine Subgroup.commutator_le.2 fun a _ b _ => ?_
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (mul_comm _ _)
  intro x hx
  have h1 : φ x = 1 := hle hx
  have h2 : ((φ x : Kˣ) : K) = 1 := by rw [h1]; rfl
  exact h2

theorem kl5_commute_of_scalar {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K] {x : GL ι K}
    {c : K} (hx : (x : Matrix ι ι K) = c • 1) (y : GL ι K) : x * y = y * x := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hx, smul_mul_assoc, one_mul, mul_smul_comm, mul_one]

theorem kl5_core (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    {ι : Type} [Fintype ι] [DecidableEq ι] (hι : Fintype.card ι ≤ 4)
    {K : Type} [Field K] [Finite K] (h2 : (2 : K) ≠ 0) {H : Subgroup (GL ι K)}
    {S : Type} [Group S] (π : ↥H →* S) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center ↥H) {A B : Subgroup S} (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hAq : CFSG.IsQuasisimple ↥A) (hBq : CFSG.IsQuasisimple ↥B) {p f : ℕ} (hp2 : p ≠ 2)
    (hmodel : StatedClassicalModel (↥A ⧸ Subgroup.center ↥A) .PSL 3 p f ∨
      StatedClassicalModel (↥A ⧸ Subgroup.center ↥A) .PSU 3 p f) : False := by
  classical
  have hfin : Finite ↥H := inferInstance
  obtain ⟨Ã, hÃp, hÃm, h₁, hh₁, h₂, hh₂, hs₁, hs₂, hc, hne, ⟨a₁, ha₁, hn₁⟩, ⟨a₂, ha₂, hn₂⟩,
    ⟨a₃, ha₃, hn₃⟩⟩ := kl5_liftA hGA π hπ hker A.subtype A.subtype_injective hAq hp2 hmodel
  have hAr : A.subtype.range = A := Subgroup.range_subtype A
  have hBperf : ⁅B, B⁆ = B := Subgroup.isPerfect_iff.1 hBq.1
  obtain ⟨Bt, hBtp, hBtm⟩ := kl5_exists_perfect_lift π hπ B hBperf
  have hcommÃB : ∀ b ∈ Bt, ∀ y ∈ Ã, b * y = y * b := by
    intro b hb y hy
    refine kl5_commute_of_perfect_of_commutator_mem_center (G := ↥H) (P := Ã) hÃp (x := b)
      (fun y' hy' => ?_) y hy
    apply hker
    rw [MonoidHom.mem_ker, map_commutatorElement]
    have hb' : π b ∈ B := hBtm ▸ Subgroup.mem_map_of_mem π hb
    have hy'' : π y' ∈ A := by rw [← hAr, ← hÃm]; exact Subgroup.mem_map_of_mem π hy'
    exact commutatorElement_eq_one_iff_mul_comm.2 (hcomm _ hy'' _ hb').symm
  have hdet : ∀ x ∈ Ã, (((x : ↥H) : GL ι K) : Matrix ι ι K).det = 1 := kl5_det_eq_one_of_perfect hÃp
  have hns : ∀ x : ↥H, (∃ a ∈ Ã, x * a ≠ a * x) →
      ¬ ∃ c : K, ((x : GL ι K) : Matrix ι ι K) = c • 1 := by
    rintro x ⟨a, -, ha⟩ ⟨c, hc'⟩
    exact ha (Subtype.ext (kl5_commute_of_scalar hc' (a : GL ι K)))
  have hcm : ∀ g ∈ Bt, ∀ g' ∈ Bt, g * g' = g' * g := by
    intro g hg g' hg'
    have := kl5_commute_of_fourgroup hι h2 (h₁ : GL ι K) (h₂ : GL ι K)
      (congrArg Subtype.val hs₁) (congrArg Subtype.val hs₂) (congrArg Subtype.val hc)
      (hdet h₁ hh₁) (hdet h₂ hh₂) (hns h₁ ⟨a₁, ha₁, hn₁⟩) (hns h₂ ⟨a₂, ha₂, hn₂⟩)
      (hns (h₁ * h₂) ⟨a₃, ha₃, hn₃⟩) (g : GL ι K) (g' : GL ι K)
      (congrArg Subtype.val (hcommÃB g hg h₁ hh₁)) (congrArg Subtype.val (hcommÃB g hg h₂ hh₂))
      (congrArg Subtype.val (hcommÃB g' hg' h₁ hh₁)) (congrArg Subtype.val (hcommÃB g' hg' h₂ hh₂))
    exact Subtype.ext this
  obtain ⟨u, v, huv⟩ := hBq.2.2
  obtain ⟨u', rfl⟩ := QuotientGroup.mk_surjective u
  obtain ⟨v', rfl⟩ := QuotientGroup.mk_surjective v
  apply huv
  obtain ⟨x, hx, hxu⟩ := Subgroup.mem_map.1 (hBtm ▸ u'.2 : (u' : S) ∈ Bt.map π)
  obtain ⟨y, hy, hyv⟩ := Subgroup.mem_map.1 (hBtm ▸ v'.2 : (v' : S) ∈ Bt.map π)
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  apply Subtype.ext
  show (u' : S) * (v' : S) = (v' : S) * (u' : S)
  rw [← hxu, ← hyv, ← map_mul, ← map_mul, hcm x hx y hy]


theorem kl5_of_statedProj (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    {ι : Type} [Fintype ι] [DecidableEq ι] (hι : Fintype.card ι ≤ 4)
    {K : Type} [Field K] [Finite K] (h2 : (2 : K) ≠ 0) {H : Subgroup (GL ι K)}
    {S : Type} [Group S] (e : S ≃* StatedProj H) {A B : Subgroup S}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hAq : CFSG.IsQuasisimple ↥A) (hBq : CFSG.IsQuasisimple ↥B) {p f : ℕ} (hp2 : p ≠ 2)
    (hmodel : StatedClassicalModel (↥A ⧸ Subgroup.center ↥A) .PSL 3 p f ∨
      StatedClassicalModel (↥A ⧸ Subgroup.center ↥A) .PSU 3 p f) : False := by
  let π : ↥H →* S := e.symm.toMonoidHom.comp (QuotientGroup.mk' ((StatedScalars ι K).subgroupOf H))
  have hπ : Function.Surjective π := fun s => by
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (e s)
    exact ⟨x, by simp [π, hx]⟩
  have hker : π.ker ≤ Subgroup.center ↥H := by
    intro x hx
    have h1 : QuotientGroup.mk' ((StatedScalars ι K).subgroupOf H) x = 1 := by
      have : e.symm (QuotientGroup.mk' ((StatedScalars ι K).subgroupOf H) x) = 1 := hx
      simpa using this
    have h2' : (x : GL ι K) ∈ StatedScalars ι K := (QuotientGroup.eq_one_iff x).1 h1
    have h3 : (x : GL ι K) ∈ Subgroup.center (GL ι K) := by
      rw [StatedScalars, ← Matrix.GeneralLinearGroup.center_eq_range_scalar] at h2'
      exact h2'
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.1 h3 (g : GL ι K))
  exact kl5_core hGA hι h2 π hπ hker hcomm hAq hBq hp2 hmodel

end CFSG.GH74.Generic.S1
