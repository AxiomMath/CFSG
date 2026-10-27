module

public import CFSG.RankThree.PartOne.CTP.SeitzUSplit
public import CFSG.RankThree.PartOne.CTP.SeitzUFrame

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.CTP

section Abstract

variable {ℓ f p : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K)
  {V : Type*} [AddCommGroup V] [Module K V]

theorem eigenvalue_pow_eq_one {S : Module.End K V} {x : V} {c : K} (hx : x ≠ 0)
    (hxc : S x = c • x) (hS : S ^ p = 1) : c ^ p = 1 := by
  have h1 : (S ^ p) x = c ^ p • x :=
    Module.End.HasEigenvector.pow_apply (f := S) (μ := c) (v := x)
      ⟨Module.End.mem_eigenspace_iff.mpr hxc, hx⟩ p
  rw [hS, Module.End.one_apply] at h1
  have h2 : (c ^ p - 1) • x = 0 := by rw [sub_smul, ← h1, one_smul, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right hx)

theorem isotropic_of_eigenvalue_ne_one {B : V →ₛₗ[h.bar] V →ₗ[K] K} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ ℓ ^ f - 1) {S : Module.End K V}
    (hiso : ∀ v w, B (S v) (S w) = B v w) (hS : S ^ p = 1) {x : V} (hx : x ≠ 0) {c : K}
    (hxc : S x = c • x) (hc : c ≠ 1) : B x x = 0 := by
  have hcp := eigenvalue_pow_eq_one hx hxc hS
  have hbar := bar_eq_self_of_pow_eq_one h hpq hcp
  have h1 := hiso x x
  rw [hxc] at h1
  simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, hbar] at h1
  have hsq : c * c ≠ 1 := fun hh =>
    hc (eq_one_of_sq_eq_one_of_pow_eq_one hp2 hp hcp (by linear_combination hh))
  have h2 : (c * c - 1) * B x x = 0 := by linear_combination h1
  exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hsq)

variable [FiniteDimensional K V]

theorem exists_hyperbolic_pair_of_ne_one {B : V →ₛₗ[h.bar] V →ₗ[K] K} (hBl : B.SeparatingLeft)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ ℓ ^ f - 1) {ι : Type*} [Finite ι]
    (S : ι → Module.End K V) (hcomm : ∀ i j, Commute (S i) (S j)) (hpow : ∀ i, S i ^ p = 1)
    (hiso : ∀ i v w, B (S i v) (S i w) = B v w) (i₀ : ι) (hi₀ : S i₀ ≠ 1) :
    ∃ a b : V, a ≠ 0 ∧ B a a = 0 ∧ B b b = 0 ∧ B a b = 1 ∧
      ∀ i, ∃ c : K, c ≠ 0 ∧ S i a = c • a ∧ S i b = c⁻¹ • b := by
  classical
  have hfin := h.finite
  have : Fact ℓ.Prime := ⟨h.prime⟩
  have hdvd : p ∣ Nat.card K - 1 := by
    have h1 : Nat.card K - 1 = (ℓ ^ f - 1) * (ℓ ^ f + 1) := by
      rw [h.card_eq_sq, mul_comm]
      have := Nat.mul_self_sub_mul_self_eq (ℓ ^ f) 1
      simpa [sq] using this
    rw [h1]
    exact Dvd.dvd.mul_right hpq _
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_of_dvd_natCard_sub_one hdvd
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨b, μ, hb⟩ := exists_basis_common_eigenvectors_of_pow_eq_one hζ S hcomm hpow
  have hb0 : ∀ j, b j ≠ 0 := fun j => b.ne_zero j
  have hμp : ∀ i j, μ i j ^ p = 1 := fun i j => eigenvalue_pow_eq_one (hb0 j) (hb i j) (hpow i)
  have hbar : ∀ i j, h.bar (μ i j) = μ i j := fun i j => bar_eq_self_of_pow_eq_one h hpq (hμp i j)
  obtain ⟨j₀, hj₀⟩ : ∃ j, μ i₀ j ≠ 1 := by
    by_contra hcon
    push Not at hcon
    refine hi₀ (b.ext fun j => ?_)
    rw [hb, hcon j, one_smul, Module.End.one_apply]
  have hiso₀ : B (b j₀) (b j₀) = 0 :=
    isotropic_of_eigenvalue_ne_one h hp hp2 hpq (hiso i₀) (hpow i₀) (hb0 j₀) (hb i₀ j₀) hj₀
  obtain ⟨j₁, hj₁⟩ : ∃ j, B (b j₀) (b j) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h0 : B (b j₀) = 0 := b.ext fun j => by simpa using hcon j
    exact hb0 j₀ (hBl _ fun y => by rw [h0]; rfl)
  have hprod : ∀ i, μ i j₀ * μ i j₁ = 1 := by
    intro i
    have h1 := hiso i (b j₀) (b j₁)
    rw [hb, hb] at h1
    simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, hbar] at h1
    have h2 : (μ i j₀ * μ i j₁ - 1) * B (b j₀) (b j₁) = 0 := by linear_combination h1
    exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_right hj₁)
  have hne0 : ∀ i, μ i j₀ ≠ 0 := fun i h0 => by
    have := hprod i
    rw [h0, zero_mul] at this
    exact zero_ne_one this
  have hj₁ne : μ i₀ j₁ ≠ 1 := fun h1 => hj₀ (by simpa [h1] using hprod i₀)
  have hiso₁ : B (b j₁) (b j₁) = 0 :=
    isotropic_of_eigenvalue_ne_one h hp hp2 hpq (hiso i₀) (hpow i₀) (hb0 j₁) (hb i₀ j₁) hj₁ne
  refine ⟨b j₀, (B (b j₀) (b j₁))⁻¹ • b j₁, hb0 j₀, hiso₀, ?_, ?_,
    fun i => ⟨μ i j₀, hne0 i, hb i j₀, ?_⟩⟩
  · simp [map_smulₛₗ, hiso₁]
  · rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hj₁]
  · rw [map_smul, hb, smul_comm, eq_inv_of_mul_eq_one_right (hprod i)]

theorem exists_adapted_hypFamily (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ ℓ ^ f - 1)
    {ι : Type*} [Finite ι] {ε : ℕ} (hε : ε ≤ 1) (r : ℕ) :
    ∀ {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      {B : V →ₛₗ[h.bar] V →ₗ[K] K}, B.IsSymm → B.SeparatingLeft →
      Module.finrank K V = 2 * r + ε →
      ∀ (S : ι → Module.End K V), (∀ i j, Commute (S i) (S j)) → (∀ i, S i ^ p = 1) →
      (∀ i v w, B (S i v) (S i w) = B v w) →
      ∃ w : HypIndex r ε → V, (∀ x y, B (w x) (w y) = hypGram r ε K x y) ∧
        ∀ i x, ∃ c : K, S i (w x) = c • w x := by
  induction r with
  | zero =>
    intro V _ _ _ B hB hBl hn S hcomm hpow hiso
    obtain ⟨w, hw⟩ := exists_hypBasis h hB hBl (r := 0) (ε := ε) (by simpa using hn)
    refine ⟨w, hw, fun i x => ?_⟩
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
    · rcases x with ⟨k, hk⟩ | ⟨k, hk⟩ | ⟨k, hk⟩ <;> omega
    · have hn1 : Module.finrank K V = 1 := by simpa using hn
      obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hn1 (w.ne_zero x) (S i (w x))
      exact ⟨c, hc.symm⟩
  | succ r ih =>
    intro V _ _ _ B hB hBl hn S hcomm hpow hiso
    by_cases hall : ∀ i, S i = 1
    · obtain ⟨w, hw⟩ := exists_hypBasis h hB hBl hn
      exact ⟨w, hw, fun i x => ⟨1, by rw [hall i, one_smul, Module.End.one_apply]⟩⟩
    · push Not at hall
      obtain ⟨i₀, hi₀⟩ := hall
      obtain ⟨a, b, ha0, haa, hbb, hab, hev⟩ :=
        exists_hyperbolic_pair_of_ne_one h hBl hp hp2 hpq S hcomm hpow hiso i₀ hi₀
      obtain ⟨-, hsplit⟩ := hermitian_hyperbolic_splitting h hB hBl ha0 haa
      obtain ⟨-, -, -, hWsep, hWdim⟩ := hsplit b hab hbb
      set W := (Submodule.span K {a, b}).orthogonalBilin B with hW
      have haW : ∀ x : W, B a x = 0 := fun x =>
        (Submodule.mem_orthogonalBilin.mp x.2) a (Submodule.subset_span (by simp))
      have hbW : ∀ x : W, B b x = 0 := fun x =>
        (Submodule.mem_orthogonalBilin.mp x.2) b (Submodule.subset_span (by simp))
      have hWa : ∀ x : W, B x a = 0 := fun x => by rw [← hB.eq a x, haW, map_zero]
      have hWb : ∀ x : W, B x b = 0 := fun x => by rw [← hB.eq b x, hbW, map_zero]
      have hba : B b a = 1 := by rw [← hB.eq a b, hab, map_one]
      have hWstab : ∀ i, ∀ w ∈ W, S i w ∈ W := by
        intro i w hw
        obtain ⟨c, hc0, hca, hcb⟩ := hev i
        have hwa : B a w = 0 := haW ⟨w, hw⟩
        have hwb : B b w = 0 := hbW ⟨w, hw⟩
        have h1 : B a (S i w) = 0 := by
          have := hiso i a w
          rw [hca, hwa] at this
          simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul] at this
          exact (mul_eq_zero.mp this).resolve_left ((map_ne_zero _).mpr hc0)
        have h2 : B b (S i w) = 0 := by
          have := hiso i b w
          rw [hcb, hwb] at this
          simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul] at this
          exact (mul_eq_zero.mp this).resolve_left ((map_ne_zero _).mpr (inv_ne_zero hc0))
        rw [hW, Submodule.mem_orthogonalBilin]
        intro y hy
        obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hy
        simp [map_add, map_smulₛₗ, h1, h2]
      have hcommW : ∀ i j, Commute ((S i).restrict (hWstab i)) ((S j).restrict (hWstab j)) :=
        fun i j => by
          refine LinearMap.ext fun w => Subtype.ext ?_
          have := congrArg (fun T : Module.End K V => T (w : V)) (hcomm i j).eq
          simpa using this
      have hpowW : ∀ i, ((S i).restrict (hWstab i)) ^ p = 1 := fun i => by
        rw [Module.End.pow_restrict p (hWstab i)]
        refine LinearMap.ext fun w => Subtype.ext ?_
        simp [hpow i]
      have hisoW : ∀ i (x y : W), B.domRestrict₁₂ W W ((S i).restrict (hWstab i) x)
          ((S i).restrict (hWstab i) y) = B.domRestrict₁₂ W W x y := fun i x y => by
        simp only [LinearMap.domRestrict₁₂_apply]
        exact hiso i x y
      obtain ⟨w', hw', hev'⟩ := ih (V := W) (B := B.domRestrict₁₂ W W) (hB.domRestrict W) hWsep
        (by rw [hWdim, hn]; omega) (fun i => (S i).restrict (hWstab i)) hcommW hpowW hisoW
      have hw'' : ∀ x y, B (w' x) (w' y) = hypGram r ε K x y := fun x y => by
        rw [← hw' x y, LinearMap.domRestrict₁₂_apply]
      let v : HypIndex (r + 1) ε → V
        | .inl i => Fin.cases a (fun j => (w' (.inl j) : V)) i
        | .inr (.inl k) => (w' (.inr (.inl k)) : V)
        | .inr (.inr i) => Fin.cases b (fun j => (w' (.inr (.inr j)) : V)) i
      have hv : ∀ x y, B (v x) (v y) = hypGram (r + 1) ε K x y := by
        intro x y
        rcases x with i | k | i <;> rcases y with j | l | j <;>
          [cases i using Fin.cases <;> cases j using Fin.cases;
           cases i using Fin.cases;
           cases i using Fin.cases <;> cases j using Fin.cases;
           cases j using Fin.cases;
           skip;
           cases j using Fin.cases;
           cases i using Fin.cases <;> cases j using Fin.cases;
           cases i using Fin.cases;
           cases i using Fin.cases <;> cases j using Fin.cases] <;>
          simp [v, haa, hbb, hab, hba, haW, hbW, hWa, hWb, hw'', Fin.succ_ne_zero,
            (Fin.succ_ne_zero _).symm]
      refine ⟨v, hv, fun i x => ?_⟩
      obtain ⟨c, hc0, hca, hcb⟩ := hev i
      have hev'' : ∀ y, ∃ d : K, S i (w' y : V) = d • (w' y : V) := fun y => by
        obtain ⟨d, hd⟩ := hev' i y
        exact ⟨d, by simpa using congrArg Subtype.val hd⟩
      rcases x with j | k | j
      · cases j using Fin.cases with
        | zero => exact ⟨c, hca⟩
        | succ j => simpa [v] using hev'' (.inl j)
      · simpa [v] using hev'' (.inr (.inl k))
      · cases j using Fin.cases with
        | zero => exact ⟨c⁻¹, hcb⟩
        | succ j => simpa [v] using hev'' (.inr (.inr j))

end Abstract

section Split

noncomputable def hypEquivFin (r ε : ℕ) : HypIndex r ε ≃ Fin (2 * r + ε) :=
  Equiv.ofBijective (fun a => ⟨fullPos a, fullPos_lt a⟩) (by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨fun a b hab => fullPos_injective (congrArg Fin.val hab), ?_⟩
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega)

theorem hypEquivFin_apply_inl {r ε : ℕ} (i : Fin r) :
    hypEquivFin r ε (.inl i) = ⟨i.val, by omega⟩ := by
  apply Fin.ext
  simp only [hypEquivFin, Equiv.ofBijective_apply, fullPos_inl]

theorem hypEquivFin_hypPartner {r ε : ℕ} (hε : ε ≤ 1) (a : HypIndex r ε) :
    hypEquivFin r ε (hypPartner a) = Fin.rev (hypEquivFin r ε a) := by
  have := fullPos_lt a
  apply Fin.ext
  simp only [hypEquivFin, Equiv.ofBijective_apply, Fin.val_rev]
  rw [fullPos_hypPartner hε]
  omega

variable {ℓ f p : ℕ} {K : Type} [Field K]

theorem unitarySU_planeGen_split {n : ℕ} (h : UnitaryFieldData ℓ f K) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ ℓ ^ f - 1) (hn : 2 ≤ n) (E : Subgroup (unitarySU ℓ f K n))
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ p = 1)
    (hcard : Nat.card E = p ^ 2) :
    Subgroup.closure {g : unitarySU ℓ f K n | ∃ x ∈ E, x ≠ 1 ∧ g * x = x * g} = ⊤ := by
  classical
  have hfin := h.finite
  have : Fact ℓ.Prime := ⟨h.prime⟩
  have : CharP K ℓ := h.charP
  obtain ⟨r, ε, hε, rfl⟩ : ∃ r ε : ℕ, ε ≤ 1 ∧ n = 2 * r + ε :=
    ⟨n / 2, n - 2 * (n / 2), by omega, by omega⟩
  have hB : (stdB h (2 * r + ε)).IsSymm := gramForm_isSymm h (by simp)
  have hBl : (stdB h (2 * r + ε)).SeparatingLeft := gramForm_separatingLeft h (by simp)
  set ρ := unitaryRep (ℓ := ℓ) (f := f) (n := 2 * r + ε) (K := K) E with hρdef
  let S : E → Module.End K (Fin (2 * r + ε) → K) := fun x =>
    ((ρ x : LinearMap.GeneralLinearGroup K (Fin (2 * r + ε) → K)) :
      Module.End K (Fin (2 * r + ε) → K))
  have hScomm : ∀ x y, Commute (S x) (S y) := fun x y => by
    have hxy : x * y = y * x := Subtype.ext (hcomm x x.2 y y.2)
    show S x * S y = S y * S x
    simp only [S, ← Units.val_mul, ← map_mul, hxy]
  have hSpow : ∀ x, S x ^ p = 1 := fun x => by
    have hx : x ^ p = 1 := Subtype.ext (hexp x x.2)
    show ((ρ x : LinearMap.GeneralLinearGroup K (Fin (2 * r + ε) → K)) :
      Module.End K (Fin (2 * r + ε) → K)) ^ p = 1
    rw [← Units.val_pow_eq_pow_val, ← map_pow, hx, map_one, Units.val_one]
  have hSiso : ∀ x v w, stdB h (2 * r + ε) (S x v) (S x w) = stdB h (2 * r + ε) v w :=
    fun x v w => mem_sesqUnitaryGroup.mp (unitaryRep_mem h E x) v w
  obtain ⟨w, hw, hev⟩ := exists_adapted_hypFamily h hp hp2 hpq hε r
    (V := Fin (2 * r + ε) → K) hB hBl (by simp) S hScomm hSpow hSiso
  let e := hypEquivFin r ε
  obtain ⟨P, hPJ, hPdiag⟩ := exists_frame_of_family h E (fun c => w (e.symm c))
    (fun i j => by
      rw [hw, hypGram_apply]
      have : e.symm j = hypPartner (e.symm i) ↔ j = Fin.rev i := by
        rw [Equiv.symm_apply_eq, hypEquivFin_hypPartner hε, Equiv.apply_symm_apply]
      simp only [this])
    (fun x hx => by
      choose d hd using fun c => hev ⟨x, hx⟩ (e.symm c)
      exact ⟨d, hd⟩)
  exact closure_centralizers_unitarySU_of_frame h hp hp2 hpq hn E hexp hcard P hPJ hPdiag

end Split

end CFSG.LieType.SeitzGeneration
