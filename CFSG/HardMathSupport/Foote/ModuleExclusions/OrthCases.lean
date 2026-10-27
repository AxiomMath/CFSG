module

public import CFSG.CGT.PushingUpLit.CGT6M.FiveInvLA
public import CFSG.HardMathSupport.Foote.ModuleExclusions.OrthEichler

public section

open Matrix LinearMap
open scoped commutatorElement

namespace CFSG.HardMathSupport.Foote.ModuleExclusions

open CFSG CFSG.Open CFSG.CGT.PushingUpLit.CGT6M

section Proj

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

theorem c55_proj_of_hom (H : Subgroup (GL ι K)) (Mu : GL ι K) (hMH : Mu ∈ H)
    (Ψ : C55 →* GL ι K) (hmem : ∀ u, Ψ u ∈ H)
    (hinj : ∀ u, (∃ s : K, ((Ψ u : GL ι K) : Matrix ι ι K) = s • 1) → u = 1)
    (hinv : ∀ u, Mu * Ψ u * Mu⁻¹ = (Ψ u)⁻¹) :
    ∃ Φ : C55 →* StatedProj H, Function.Injective Φ ∧
      ∀ u : C55, (QuotientGroup.mk (⟨Mu, hMH⟩ : H) : StatedProj H) * Φ u *
        (QuotientGroup.mk (⟨Mu, hMH⟩ : H) : StatedProj H)⁻¹ = (Φ u)⁻¹ := by
  let E' : C55 →* H := Ψ.codRestrict H hmem
  refine ⟨(QuotientGroup.mk' ((StatedScalars ι K).subgroupOf H)).comp E', ?_, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro u hu
    exact hinj u (scalar_of_mk_eq_one (E' u) hu)
  · intro u
    have hc : (⟨Mu, hMH⟩ : H) * E' u * (⟨Mu, hMH⟩ : H)⁻¹ = (E' u)⁻¹ := by
      apply Subtype.ext
      exact hinv u
    show QuotientGroup.mk (⟨Mu, hMH⟩ : H) * QuotientGroup.mk (E' u) *
      (QuotientGroup.mk (⟨Mu, hMH⟩ : H))⁻¹ = (QuotientGroup.mk (E' u))⁻¹
    rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hc,
      QuotientGroup.mk_inv]

theorem heisData_proj (H : Subgroup (GL ι K)) (Mu : GL ι K) (hMH : Mu ∈ H) (X Y : GL ι K)
    (hX : X ∈ H) (hY : Y ∈ H) (hX5 : X ^ 5 = 1) (hY5 : Y ^ 5 = 1)
    (h1 : Commute ⁅Y, X⁆ X) (h2 : Commute ⁅Y, X⁆ Y)
    (h3 : ¬ ∃ s : K, ((⁅Y, X⁆ : GL ι K) : Matrix ι ι K) = s • 1)
    (hinv : Mu * X * Mu⁻¹ = X⁻¹) :
    ∃ X' Y' : StatedProj H, X' ^ 5 = 1 ∧ Y' ^ 5 = 1 ∧ Commute ⁅Y', X'⁆ X' ∧ Commute ⁅Y', X'⁆ Y' ∧
      ⁅Y', X'⁆ ≠ 1 ∧ (QuotientGroup.mk (⟨Mu, hMH⟩ : H) : StatedProj H) * X' *
        (QuotientGroup.mk (⟨Mu, hMH⟩ : H) : StatedProj H)⁻¹ = X'⁻¹ := by
  let π : H →* StatedProj H := QuotientGroup.mk' ((StatedScalars ι K).subgroupOf H)
  let Xh : H := ⟨X, hX⟩
  let Yh : H := ⟨Y, hY⟩
  have hc : (((⁅Yh, Xh⁆ : H)) : GL ι K) = ⁅Y, X⁆ := by
    simp [commutatorElement_def, Xh, Yh]
  refine ⟨π Xh, π Yh, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_pow]
    have : Xh ^ 5 = 1 := Subtype.ext (by simpa [Xh] using hX5)
    rw [this, map_one]
  · rw [← map_pow]
    have : Yh ^ 5 = 1 := Subtype.ext (by simpa [Yh] using hY5)
    rw [this, map_one]
  · rw [← map_commutatorElement]
    refine Commute.map ?_ π
    exact Subtype.ext (by simpa [hc, Xh] using h1.eq)
  · rw [← map_commutatorElement]
    refine Commute.map ?_ π
    exact Subtype.ext (by simpa [hc, Yh] using h2.eq)
  · rw [← map_commutatorElement]
    intro h
    obtain ⟨s, hs⟩ := scalar_of_mk_eq_one ⁅Yh, Xh⁆ h
    exact h3 ⟨s, by rw [← hc]; exact hs⟩
  · have : (⟨Mu, hMH⟩ : H) * Xh * (⟨Mu, hMH⟩ : H)⁻¹ = Xh⁻¹ := Subtype.ext (by simpa [Xh] using hinv)
    show π ⟨Mu, hMH⟩ * π Xh * (π ⟨Mu, hMH⟩)⁻¹ = (π Xh)⁻¹
    rw [← map_inv, ← map_mul, ← map_mul, this, map_inv]

end Proj

section Good

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

structure Good (B : LinearMap.BilinForm K (ι → K)) : Prop where
  symm : ∀ x y, B x y = B y x
  nd : ∀ x, (∀ y, B x y = 0) → x = 0
  two : (2 : K) ≠ 0

variable {B : LinearMap.BilinForm K (ι → K)}

omit [Fintype ι] [DecidableEq ι] in
theorem Good.exists_dual (G : Good B) {a : ι → K} (ha : a ≠ 0) : ∃ y, B a y = 1 := by
  by_contra h
  push Not at h
  apply ha
  apply G.nd
  intro y
  by_contra hy
  apply h ((B a y)⁻¹ • y)
  simp [hy]

theorem eichU_scalar (G : Good B) {a w : ι → K} (haa : B a a = 0) (haw : B a w = 0)
    (ha0 : a ≠ 0) {y : ι → K} (hy : B a y = 1) {s : K}
    (h : ((eichU B a w : GL ι K) : Matrix ι ι K) = s • 1) :
    w = (B w y + qd B w) • a := by
  have hwa : B w a = 0 := by rw [G.symm]; exact haw
  have h1 := congrArg (fun A : Matrix ι ι K => A *ᵥ a) h
  simp only [eichU_mulVec G.symm G.two haa haw, Matrix.smul_mulVec, Matrix.one_mulVec,
    eichLin_apply, haa, hwa] at h1
  have hs1 : s = 1 := by
    have h3 : (1 - s) • a = 0 := by
      rw [sub_smul, one_smul, ← h1]
      simp
    rcases smul_eq_zero.mp h3 with h4 | h4
    · exact (sub_eq_zero.mp h4).symm
    · exact absurd h4 ha0
  subst hs1
  have h2 := congrArg (fun A : Matrix ι ι K => A *ᵥ y) h
  simp only [eichU_mulVec G.symm G.two haa haw, Matrix.one_mulVec,
    eichLin_apply, hy, one_smul, mul_one] at h2
  have h3 : w - (B w y + qd B w) • a = 0 := by
    have : y + w - B w y • a - qd B w • a = y := h2
    calc w - (B w y + qd B w) • a = (y + w - B w y • a - qd B w • a) - y := by module
      _ = 0 := by rw [this]; simp
  exact sub_eq_zero.mp h3

theorem eichU_mem_omega (G : Good B) {a w : ι → K} (haa : B a a = 0) (haw : B a w = 0)
    (hw : w = 0 ∨ ∀ p r : K, p • a + r • w = 0 → p = 0 ∧ r = 0) :
    eichU B a w ∈ omegaGroup B := by
  rcases hw with rfl | hind
  · rw [eichU_zero]; exact Subgroup.one_mem _
  · obtain ⟨a', haa', ha'a', ha'w⟩ := exists_partner B G.symm G.two G.nd haa haw hind
    exact eichU_mem_commutator G.symm G.two haa haw ha'a' haa' ha'w

variable [CharP K 5]

@[expose] noncomputable def wOf (w₁ w₂ : ι → K) (u : C55) : ι → K :=
  zi K (Multiplicative.toAdd u).1 • w₁ + zi K (Multiplicative.toAdd u).2 • w₂

omit [Fintype ι] [DecidableEq ι] in
theorem wOf_mul (w₁ w₂ : ι → K) (u v : C55) : wOf w₁ w₂ (u * v) = wOf w₁ w₂ u + wOf w₁ w₂ v := by
  simp only [wOf, toAdd_mul, Prod.fst_add, Prod.snd_add, map_add, add_smul]
  abel

theorem c55_case (G : Good B) {M : GL ι K} (hM : M ∈ omegaGroup B)
    {a w₁ w₂ : ι → K} {lam mu : K} (hlm : lam * mu = -1)
    (haa : B a a = 0) (haw₁ : B a w₁ = 0) (haw₂ : B a w₂ = 0)
    (hind : ∀ r t₁ t₂ : K, r • a + t₁ • w₁ + t₂ • w₂ = 0 → r = 0 ∧ t₁ = 0 ∧ t₂ = 0)
    (hMa : (M : Matrix ι ι K) *ᵥ a = lam • a) (hMw₁ : (M : Matrix ι ι K) *ᵥ w₁ = mu • w₁)
    (hMw₂ : (M : Matrix ι ι K) *ᵥ w₂ = mu • w₂) :
    ∃ Φ : C55 →* StatedProj (omegaGroup B), Function.Injective Φ ∧
      ∀ u : C55, (QuotientGroup.mk (⟨M, hM⟩ : omegaGroup B) :
        StatedProj (omegaGroup B)) * Φ u *
        (QuotientGroup.mk (⟨M, hM⟩ : omegaGroup B) :
          StatedProj (omegaGroup B))⁻¹ = (Φ u)⁻¹ := by
  have haw : ∀ u, B a (wOf w₁ w₂ u) = 0 := fun u => by
    simp [wOf, haw₁, haw₂]
  let Ψ : C55 →* GL ι K := MonoidHom.mk' (fun u => eichU B a (wOf w₁ w₂ u)) (fun u v => by
    rw [eichU_mul G.symm G.two haa (haw u) (haw v), wOf_mul])
  have hΨ : ∀ u, Ψ u = eichU B a (wOf w₁ w₂ u) := fun u => rfl
  have hMG : M ∈ isomGroup B := omegaGroup_le B hM
  refine c55_proj_of_hom _ M hM Ψ (fun u => ?_) (fun u => ?_) (fun u => ?_)
  · rw [hΨ]
    refine eichU_mem_omega G haa (haw u) ?_
    by_cases hw0 : wOf w₁ w₂ u = 0
    · exact Or.inl hw0
    · right
      intro p r hpr
      have h1 := hind p (r * zi K (Multiplicative.toAdd u).1) (r * zi K (Multiplicative.toAdd u).2)
        (by rw [← hpr]; simp only [wOf, mul_smul, smul_add]; abel)
      by_cases hr : r = 0
      · exact ⟨h1.1, hr⟩
      · exfalso
        apply hw0
        simp only [wOf]
        rw [(mul_eq_zero.mp h1.2.1).resolve_left hr, (mul_eq_zero.mp h1.2.2).resolve_left hr]
        simp
  · intro hs
    obtain ⟨s, hs⟩ := hs
    rw [hΨ] at hs
    have ha0 : a ≠ 0 := by
      intro h0
      have := hind 1 0 0 (by simp [h0])
      exact one_ne_zero this.1
    have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    obtain ⟨y, hy⟩ := G.exists_dual ha0
    obtain ⟨c, hc⟩ : ∃ c : K, wOf w₁ w₂ u = c • a := ⟨_, eichU_scalar G haa (haw u) ha0 hy hs⟩
    have h1 := hind (-c) (zi K (Multiplicative.toAdd u).1)
      (zi K (Multiplicative.toAdd u).2) (by
        have : wOf w₁ w₂ u = zi K (Multiplicative.toAdd u).1 • w₁ + zi K (Multiplicative.toAdd u).2 • w₂ := rfl
        rw [neg_smul, add_assoc, ← this, hc]
        simp)
    obtain ⟨-, h2, h3⟩ := h1
    obtain ⟨⟨i, j⟩, rfl⟩ : ∃ w, u = Multiplicative.ofAdd w := ⟨Multiplicative.toAdd u, rfl⟩
    have h4 : i = 0 := (zi K).injective (by simpa using h2)
    have h5 : j = 0 := (zi K).injective (by simpa using h3)
    rw [h4, h5]
    rfl
  · rw [hΨ, eichU_conj G.symm G.two hMG haa (haw u), hMa]
    have hMw : (M : Matrix ι ι K) *ᵥ wOf w₁ w₂ u = mu • wOf w₁ w₂ u := by
      simp only [wOf, Matrix.mulVec_add, Matrix.mulVec_smul, hMw₁, hMw₂, smul_add, smul_comm mu]
    rw [hMw, eichU_scale, hlm, eichU_inv G.symm G.two haa (haw u), neg_one_smul]

omit [Fintype ι] [DecidableEq ι] in
theorem five_nsmul_eq_zero (x : ι → K) : (5 : ℕ) • x = 0 := by
  rw [← Nat.cast_smul_eq_nsmul K, CharP.cast_eq_zero K 5, zero_smul]

theorem heis_case (G : Good B) {M : GL ι K} (hM : M ∈ omegaGroup B)
    {a b e : ι → K} {lam mu : K} (hlm : lam * mu = -1)
    (haa : B a a = 0) (hbb : B b b = 0) (hab : B a b = 0) (hae : B a e = 0) (hbe : B b e = 0)
    (hee : B e e ≠ 0) (hind : ∀ r t : K, r • a + t • b = 0 → r = 0 ∧ t = 0)
    (hMa : (M : Matrix ι ι K) *ᵥ a = lam • a) (hMe : (M : Matrix ι ι K) *ᵥ e = mu • e) :
    ∃ X' Y' : StatedProj (omegaGroup B), X' ^ 5 = 1 ∧ Y' ^ 5 = 1 ∧ Commute ⁅Y', X'⁆ X' ∧
      Commute ⁅Y', X'⁆ Y' ∧ ⁅Y', X'⁆ ≠ 1 ∧
      (QuotientGroup.mk (⟨M, hM⟩ : omegaGroup B) : StatedProj (omegaGroup B)) * X' *
        (QuotientGroup.mk (⟨M, hM⟩ : omegaGroup B) : StatedProj (omegaGroup B))⁻¹ = X'⁻¹ := by
  have hba : B b a = 0 := by rw [G.symm]; exact hab
  have hea : B e a = 0 := by rw [G.symm]; exact hae
  have heb : B e b = 0 := by rw [G.symm]; exact hbe
  have ha0 : a ≠ 0 := by
    intro h0
    have := hind 1 0 (by simp [h0])
    exact one_ne_zero this.1
  have hb0 : b ≠ 0 := by
    intro h0
    have := hind 0 1 (by simp [h0])
    exact one_ne_zero this.2
  have hind' : ∀ {x : ι → K}, x ≠ 0 → B x e = 0 → ∀ p r : K, p • x + r • e = 0 →
      p = 0 ∧ r = 0 := by
    intro x hx0 hxe p r h
    have h1 := congrArg (fun v => B e v) h
    simp only [map_add, map_smul, smul_eq_mul, map_zero] at h1
    have hex : B e x = 0 := by rw [G.symm]; exact hxe
    rw [hex] at h1
    have hr : r = 0 := by
      have : r * B e e = 0 := by simpa using h1
      exact (mul_eq_zero.mp this).resolve_right hee
    rw [hr, zero_smul, add_zero] at h
    exact ⟨(smul_eq_zero.mp h).resolve_right hx0, hr⟩
  have hX : eichU B a e ∈ omegaGroup B := eichU_mem_omega G haa hae (Or.inr (hind' ha0 hae))
  have hY : eichU B b e ∈ omegaGroup B := eichU_mem_omega G hbb hbe (Or.inr (hind' hb0 hbe))
  have hXG : eichU B a e ∈ isomGroup B := eichU_mem G.symm G.two haa hae
  have hYG : eichU B b e ∈ isomGroup B := eichU_mem G.symm G.two hbb hbe
  have hMG : M ∈ isomGroup B := omegaGroup_le B hM
  have hX5 : (eichU B a e) ^ 5 = 1 := by
    rw [eichU_pow G.symm G.two haa hae, five_nsmul_eq_zero, eichU_zero]
  have hY5 : (eichU B b e) ^ 5 = 1 := by
    rw [eichU_pow G.symm G.two hbb hbe, five_nsmul_eq_zero, eichU_zero]
  have hYa : ((eichU B b e : GL ι K) : Matrix ι ι K) *ᵥ a = a := by
    rw [eichU_mulVec G.symm G.two hbb hbe, eichLin_apply, hba, hea]
    simp
  have hYe : ((eichU B b e : GL ι K) : Matrix ι ι K) *ᵥ e = e - B e e • b := by
    rw [eichU_mulVec G.symm G.two hbb hbe, eichLin_apply, hbe]
    simp
  have hconj := eichU_conj G.symm G.two hYG haa hae
  rw [hYa, hYe] at hconj
  have hab' : B a (e - B e e • b) = 0 := by simp [map_sub, hae, hab]
  have hZ : ⁅eichU B b e, eichU B a e⁆ = eichU B a ((-B e e) • b) := by
    rw [commutatorElement_def, hconj, eichU_inv G.symm G.two haa hae,
      eichU_mul G.symm G.two haa hab' (by simp [hae])]
    congr 1
    module
  have hcb : B a ((-B e e) • b) = 0 := by simp [hab]
  have hcc : B ((-B e e) • b) ((-B e e) • b) = 0 := by simp [hbb]
  refine heisData_proj (omegaGroup B) M hM _ _ hX hY hX5 hY5 ?_ ?_ ?_ ?_
  · rw [hZ]
    show _ * _ = _ * _
    rw [eichU_mul G.symm G.two haa hcb hae, eichU_mul G.symm G.two haa hae hcb, add_comm]
  · rw [hZ, eichU_swap haa hcc, ← neg_one_smul K a, eichU_scale]
    have hba' : B b ((-B e e * -1) • a) = 0 := by simp [hba]
    show _ * _ = _ * _
    rw [eichU_mul G.symm G.two hbb hba' hbe, eichU_mul G.symm G.two hbb hbe hba', add_comm]
  · rw [hZ]
    rintro ⟨s, hs⟩
    obtain ⟨y, hy⟩ := G.exists_dual ha0
    obtain ⟨c, hc⟩ : ∃ c : K, (-B e e) • b = c • a := ⟨_, eichU_scalar G haa hcb ha0 hy hs⟩
    have := hind (-c) (-B e e) (by rw [neg_smul, hc]; simp)
    exact hee (neg_eq_zero.mp this.2)
  · rw [eichU_conj G.symm G.two hMG haa hae, hMa, hMe, eichU_scale, hlm,
      eichU_inv G.symm G.two haa hae, neg_one_smul]

end Good

end CFSG.HardMathSupport.Foote.ModuleExclusions
