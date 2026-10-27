module

public import CFSG.ClassicalInvolution.AschTight.S19FGraph
public import CFSG.ClassicalInvolution.Asc77.AscIH8Model

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19F

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.ClassicalInvolution.G2D4Models
  CFSG.ClassicalInvolution.Generic CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley Matrix
open scoped MatrixGroups

theorem false_of_conj_fixes_nonabelian {G : Type*} [Group G] (α ψ β : MulAut G)
    (hψ : ψ * α * ψ⁻¹ = β) {R : Subgroup G} {P' : Subgroup G} (hP'2 : IsPGroup 2 P')
    (hP'R : P' ≤ R.map ψ.toMonoidHom) (hP'fix : ∀ x ∈ P', β x = x) {x y : G} (hx : x ∈ P')
    (hy : y ∈ P') (hxy : x * y ≠ y * x)
    (hab : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ R → (∀ x ∈ P, α x = x) →
      ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) : False := by
  have hα : ∀ z, α (ψ⁻¹ z) = ψ⁻¹ (β z) := fun z => by
    rw [← hψ]
    simp [MulAut.mul_apply]
  refine hxy ?_
  have h := hab (P'.map (ψ⁻¹).toMonoidHom) (hP'2.map _) ?_ ?_ (ψ⁻¹ x) ⟨x, hx, rfl⟩ (ψ⁻¹ y)
    ⟨y, hy, rfl⟩
  · have h' := congrArg ψ h
    simpa [map_mul] using h'
  · rintro _ ⟨z, hz, rfl⟩
    obtain ⟨w, hw, rfl⟩ := hP'R hz
    change ψ⁻¹ (ψ w) ∈ R
    rwa [MulAut.inv_apply_self]
  · rintro _ ⟨z, hz, rfl⟩
    change α (ψ⁻¹ z) = ψ⁻¹ z
    rw [hα, hP'fix z hz]

section G2

variable {K : Type} [Field K]

theorem exists_conj_of_inner_formula_g2 (α : MulAut ↥(adjointGroup .G2 K))
    (g : adjointGroup .G2 K) (a : Fin Tag.G2.rank → Kˣ)
    (hga : ∀ h : adjointGroup .G2 K, (α h : ModGL .G2 K) =
      (g : ModGL .G2 K) * rootDiagUnit .G2 a * h * (rootDiagUnit .G2 a)⁻¹ * (g : ModGL .G2 K)⁻¹) :
    ∃ x, α = MulAut.conj x := by
  obtain ⟨⟨B, hB, -⟩, hrest⟩ := G2_F4_root_character_diagonals_inner .G2 (Or.inl rfl) K
  have hda : rootDiagUnit .G2 a ∈ adjointGroup .G2 K := (hrest B hB a).2.2.1
  refine ⟨g * ⟨rootDiagUnit .G2 a, hda⟩, MulEquiv.ext fun h => Subtype.ext ?_⟩
  rw [hga h, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
    Subgroup.coe_mul]
  group

theorem false_of_quadratic_g2 [Finite K] (hodd : Odd (Nat.card K)) {p' e₀ : ℕ}
    (hp' : p'.Prime) (he₀ : 1 ≤ e₀) (hK : Nat.card K = (p' ^ e₀) ^ 2) (δ : K ≃+* K)
    (hδ : ∀ c, δ c = c ^ (p' ^ e₀)) (α : MulAut ↥(adjointGroup .G2 K))
    (g : adjointGroup .G2 K) (a : Fin Tag.G2.rank → Kˣ)
    (hga : ∀ h : adjointGroup .G2 K, (α h : ModGL .G2 K) = (g : ModGL .G2 K) *
      rootDiagUnit .G2 a * Units.map (entrywiseHom δ.toRingHom) (h : ModGL .G2 K) *
        (rootDiagUnit .G2 a)⁻¹ * (g : ModGL .G2 K)⁻¹)
    (hα : α * α = 1) {R : Subgroup ↥(adjointGroup .G2 K)}
    (hR : R ∈ fundamentalSubgroups .G2 (CFSG.LieType.Steinberg.Adjoint.g2Datum K))
    (hαR : R.map α.toMonoidHom = R)
    (hab : ∀ P : Subgroup ↥(adjointGroup .G2 K), IsPGroup 2 P → P ≤ R → (∀ x ∈ P, α x = x) →
      ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) : False := by
  obtain ⟨hQ, -⟩ := exceptional_Lang_quadratic_field_coset_conjugacy hp' he₀ K hK δ.toRingHom hδ
  obtain ⟨_β, -, hall⟩ := hQ .G2
  obtain ⟨-, hψall⟩ := hall g a
  obtain ⟨ψ, hψβ, -⟩ := hψall α hga hα
  have hp'2 : p' ≠ 2 := by
    rintro rfl
    rw [hK, ← pow_mul] at hodd
    exact Nat.not_even_iff_odd.2 hodd ((Nat.even_pow' (by omega)).2 even_two)
  have hR' := map_mem_fund_g2 hp' hp'2 (f := e₀ * 2) (by omega) (by rw [hK, ← pow_mul]) ψ hR
  have hβR : (R.map ψ.toMonoidHom).map (ψ * α * ψ⁻¹).toMonoidHom = R.map ψ.toMonoidHom := by
    rw [Subgroup.map_map]
    conv_rhs => rw [← hαR, Subgroup.map_map]
    congr 1
    ext x
    simp
  obtain ⟨P', hP'2, hP'R, hP'fix, x, hx, y, hy, hxy⟩ :=
    fieldInvolution_fixes_nonabelian_g2 hK hodd δ hδ (ψ * α * ψ⁻¹) hψβ hR' hβR
  exact false_of_conj_fixes_nonabelian α ψ _ rfl hP'2 hP'R hP'fix hx hy hxy hab

theorem factM1_g2 {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {e : ℕ} (he : 1 ≤ e)
    (α : MulAut ↥(adjointGroup .G2 (GaloisField p e))) (hα : α * α = 1)
    {R : Subgroup ↥(adjointGroup .G2 (GaloisField p e))}
    (hR : R ∈ fundamentalSubgroups .G2 (CFSG.LieType.Steinberg.Adjoint.g2Datum (GaloisField p e)))
    (hαR : R.map α.toMonoidHom = R)
    (hab : ∀ P : Subgroup ↥(adjointGroup .G2 (GaloisField p e)), IsPGroup 2 P → P ≤ R →
      (∀ x ∈ P, α x = x) → ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) :
    ∃ x, α = MulAut.conj x := by
  have hK : Nat.card (GaloisField p e) = p ^ e := GaloisField.card p e (by omega)
  have hodd : Odd (Nat.card (GaloisField p e)) := by
    rw [hK]
    exact ((Fact.out : p.Prime).odd_of_ne_two hp2).pow
  have hα2 : α ^ 2 = 1 := by rw [sq, hα]
  by_cases h3 : p = 3
  · subst h3
    have : CharP (GaloisField 3 e) CFSG.LieType.Ree.ReeTag.G2.prime :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
        Nat.prime_three he hK
    rcases CFSG.LieType.AlgebraicGroups.G2_three_involution_inner_quadratic_or_exceptional he hK
      hα2 with ⟨g, a, hga⟩ | ⟨e₀, he₀, hKe, δ, hδ, g, a, hga⟩ | ⟨b, g, -, hαe⟩
    · exact exists_conj_of_inner_formula_g2 α g a hga
    · exact (false_of_quadratic_g2 hodd Nat.prime_three he₀ hKe δ hδ α g a hga hα hR hαR
        hab).elim
    · exact absurd (hαe ▸ hαR) (graphInvolution_not_normalize b g hR)
  · have h3' : ringChar (GaloisField p e) ≠ 3 := by rwa [ringChar.eq (GaloisField p e) p]
    rcases CFSG.LieType.AlgebraicGroups.odd_F4_E8_G2_involution_inner_or_quadratic
      (Or.inr (Or.inr ⟨rfl, h3'⟩)) hodd hα2 with ⟨g, a, hga⟩ | ⟨p', e₀, hp', he₀, hKe, δ, hδ, g, a,
        hga⟩
    · exact exists_conj_of_inner_formula_g2 α g a hga
    · exact (false_of_quadratic_g2 hodd hp' he₀ hKe δ hδ α g a hga hα hR hαR hab).elim

end G2

theorem transport_conj {G H : Type*} [Group G] [Group H] (eT : G ≃* H) (α : MulAut G)
    (ψ₁ F : MulAut H) (h : ψ₁ * eT.symm.trans (α.trans eT) * ψ₁⁻¹ = F) :
    eT.trans (ψ₁.trans eT.symm) * α * (eT.trans (ψ₁.trans eT.symm))⁻¹ =
      eT.trans (F.trans eT.symm) := by
  refine MulEquiv.ext fun x => ?_
  have hx := DFunLike.congr_fun h (eT x)
  simp only [MulAut.mul_apply, MulEquiv.trans_apply] at hx ⊢
  have hinv : (eT.trans (ψ₁.trans eT.symm))⁻¹ x = eT.symm (ψ₁⁻¹ (eT x)) := rfl
  rw [hinv, hx]

section D4

open CFSG.LieType.Steinberg.TwistedD4

variable {p : ℕ} [Fact p.Prime]

theorem false_of_quadratic_d4 (hp2 : p ≠ 2) {e a : ℕ} (he : 1 ≤ e) (hea : e = 2 * a)
    (α : MulAut ↥(twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e))) (hα : α * α = 1)
    {R : Subgroup ↥(twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e))}
    (hR : R ∈ fundamentalSubgroups .trialityD4
      (twistedDatum (iterateFrobenius (GaloisField p (3 * e)) p e)))
    (hαR : R.map α.toMonoidHom = R)
    (hab : ∀ P : Subgroup ↥(twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e)),
      IsPGroup 2 P → P ≤ R → (∀ x ∈ P, α x = x) → ∀ x ∈ P, ∀ y ∈ P, x * y = y * x)
    (g₁ : ↥(graphFixedRootGroup TwistTag.D4 (GaloisField p (3 * e)) (frobEquiv p e).toRingHom))
    (δ₁ : GaloisField p (3 * e) ≃+* GaloisField p (3 * e)) (hδ₁ : ∀ c, δ₁ c = c ^ (p ^ (3 * a)))
    (hgδ : (twistedEquivC0 p e hp2 he).symm.trans (α.trans (twistedEquivC0 p e hp2 he)) =
      MulAut.conj g₁ * fieldActor (t := TwistTag.D4) (frobEquiv p e) δ₁) : False := by
  obtain ⟨eT, heT⟩ : ∃ eT : ↥(twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e)) ≃*
      ↥(graphFixedRootGroup TwistTag.D4 (GaloisField p (3 * e)) (frobEquiv p e).toRingHom),
      eT = twistedEquivC0 p e hp2 he := ⟨_, rfl⟩
  rw [← heT] at hgδ
  have hcoeT : ∀ u, ((eT u : graphFixedRootGroup TwistTag.D4 (GaloisField p (3 * e))
      (frobEquiv p e).toRingHom) : ModGL d4 (GaloisField p (3 * e))) = twistedIncl _ u := by
    intro u
    rw [heT]
    rfl
  have hα2 : (MulAut.conj g₁ * fieldActor (t := TwistTag.D4) (frobEquiv p e) δ₁) ^ 2 = 1 := by
    rw [← hgδ, sq]
    refine MulEquiv.ext fun y => ?_
    have h1 : α (α (eT.symm y)) = eT.symm y := by
      rw [← MulAut.mul_apply, hα, MulAut.one_apply]
    rw [MulAut.mul_apply, MulAut.one_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, h1,
      MulEquiv.apply_symm_apply]
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  have hpow2 : p ^ e = (p ^ a) ^ 2 := by rw [← pow_mul, hea, mul_comm]
  have hpow3 : p ^ (3 * a) = (p ^ a) ^ 3 := by rw [← pow_mul, mul_comm]
  have hK6 : Nat.card (GaloisField p (3 * e)) = (p ^ a) ^ 6 := by
    rw [GaloisField.card p (3 * e) (by omega), show 3 * e = a * 6 by omega, pow_mul]
  have hσ' : ∀ c, frobEquiv p e c = c ^ ((p ^ a) ^ 2) := fun c => by
    rw [← hpow2]
    exact iterateFrobenius_def p e c
  have hδ' : ∀ c, δ₁ c = c ^ ((p ^ a) ^ 3) := fun c => by
    rw [hδ₁, hpow3]
  have hr : IsPrimePow (p ^ a) := (Fact.out : p.Prime).isPrimePow.pow (by omega)
  obtain ⟨-, ⟨ψ₁, hψ₁⟩, -⟩ := odd_triality_field_coset_involution_fixed_p_components (r := p ^ a)
    hr hpodd.pow (GaloisField p (3 * e)) hK6 (frobEquiv p e) hσ' δ₁ hδ' g₁ hα2
  rw [← hgδ] at hψ₁
  have htr := transport_conj eT α ψ₁ _ hψ₁
  have hβ : ∀ u, twistedIncl _ (eT.trans ((fieldActor (t := TwistTag.D4) (frobEquiv p e)
      δ₁).trans eT.symm) u) = Units.map (entrywiseHom δ₁.toRingHom) (twistedIncl _ u) := by
    intro u
    have h1 := hcoeT (eT.symm (fieldActor (t := TwistTag.D4) (frobEquiv p e) δ₁ (eT u)))
    rw [MulEquiv.apply_symm_apply] at h1
    rw [MulEquiv.trans_apply, MulEquiv.trans_apply, ← h1, ← hcoeT]
    exact (odd_triality_exact_automorphism_normal_form (Fact.out : p.Prime) hp2 he
      (GaloisField p (3 * e)) (by rw [GaloisField.card p (3 * e) (by omega), pow_mul'])
        (frobEquiv p e) (fun c => iterateFrobenius_def p e c)).1 δ₁ (eT u)
  have hR' := map_mem_fund_d4 hp2 he (eT.trans (ψ₁.trans eT.symm)) hR
  have hβR : (R.map (eT.trans (ψ₁.trans eT.symm)).toMonoidHom).map
      (eT.trans ((fieldActor (t := TwistTag.D4) (frobEquiv p e) δ₁).trans eT.symm)).toMonoidHom =
      R.map (eT.trans (ψ₁.trans eT.symm)).toMonoidHom := by
    rw [← htr, Subgroup.map_map]
    conv_rhs => rw [← hαR, Subgroup.map_map]
    congr 1
    ext x
    simp
  obtain ⟨P', hP'2, hP'R, hP'fix, x, hx, y, hy, hxy⟩ :=
    fieldInvolution_fixes_nonabelian_d4 hp2 hea (by omega) δ₁ hδ₁ _ hβ hR' hβR
  exact false_of_conj_fixes_nonabelian α _ _ htr hP'2 hP'R hP'fix hx hy hxy hab

theorem factM1_d4 (hp2 : p ≠ 2) {e : ℕ} (he : 1 ≤ e)
    (α : MulAut ↥(twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e))) (hα : α * α = 1)
    {R : Subgroup ↥(twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e))}
    (hR : R ∈ fundamentalSubgroups .trialityD4
      (twistedDatum (iterateFrobenius (GaloisField p (3 * e)) p e)))
    (hαR : R.map α.toMonoidHom = R)
    (hab : ∀ P : Subgroup ↥(twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e)),
      IsPGroup 2 P → P ≤ R → (∀ x ∈ P, α x = x) → ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) :
    ∃ x, α = MulAut.conj x := by
  have hK3 : Nat.card (GaloisField p (3 * e)) = (p ^ e) ^ 3 := by
    rw [GaloisField.card p (3 * e) (by omega), pow_mul']
  have hσq : ∀ c : GaloisField p (3 * e), frobEquiv p e c = c ^ (p ^ e) := fun c =>
    iterateFrobenius_def p e c
  obtain ⟨hcoe, hNF, ⟨Θ, hΘ, -, -, hinv⟩, -⟩ :=
    odd_triality_exact_automorphism_normal_form (Fact.out : p.Prime) hp2 he
      (GaloisField p (3 * e)) hK3 (frobEquiv p e) hσq
  obtain ⟨eT, heT⟩ : ∃ eT : ↥(twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e)) ≃*
      ↥(graphFixedRootGroup TwistTag.D4 (GaloisField p (3 * e)) (frobEquiv p e).toRingHom),
      eT = twistedEquivC0 p e hp2 he := ⟨_, rfl⟩
  obtain ⟨α₁, hα₁def⟩ : ∃ α₁ : MulAut ↥(graphFixedRootGroup TwistTag.D4 (GaloisField p (3 * e))
      (frobEquiv p e).toRingHom), α₁ = eT.symm.trans (α.trans eT) := ⟨_, rfl⟩
  have hα₁x : ∀ y, α₁ y = eT (α (eT.symm y)) := fun y => by rw [hα₁def]; rfl
  have hαx : ∀ x, α x = eT.symm (α₁ (eT x)) := fun x => by
    rw [hα₁x, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
  have hα₁2 : α₁ ^ 2 = 1 := by
    rw [sq]
    refine MulEquiv.ext fun y => ?_
    have h1 : α (α (eT.symm y)) = eT.symm y := by
      rw [← MulAut.mul_apply, hα, MulAut.one_apply]
    rw [MulAut.mul_apply, MulAut.one_apply, hα₁x, hα₁x, MulEquiv.symm_apply_apply, h1,
      MulEquiv.apply_symm_apply]
  have hN1 := hNF α₁
  rcases hN1 with ⟨⟨g₁, δ₁⟩, hgδ, -⟩
  have hΘα := hΘ α₁ g₁ δ₁ hgδ
  have hinv1 := hinv α₁ hα₁2
  rcases hinv1 with h1 | ⟨hev, hδc⟩
  ·
    rw [hΘα] at h1
    have hF1 : ∀ y, fieldActor (t := TwistTag.D4) (frobEquiv p e) δ₁ y = y := fun y =>
      Subtype.ext (by
        rw [hcoe, h1]
        exact Units.ext (entrywise_id _))
    refine ⟨eT.symm g₁, MulEquiv.ext fun x => ?_⟩
    have e1 : (MulAut.conj g₁ * fieldActor (t := TwistTag.D4) (frobEquiv p e) δ₁) (eT x) =
        g₁ * eT x * g₁⁻¹ :=
      (congrArg (MulAut.conj g₁) (hF1 (eT x))).trans (MulAut.conj_apply g₁ (eT x))
    have e2 : eT.symm (g₁ * eT x * g₁⁻¹) = MulAut.conj (eT.symm g₁) x := by
      rw [MulAut.conj_apply, MulEquiv.map_mul, MulEquiv.map_mul, MulEquiv.map_inv,
        MulEquiv.symm_apply_apply]
    exact (hαx x).trans ((congrArg (fun φ => eT.symm (φ (eT x))) hgδ).trans
      ((congrArg eT.symm e1).trans e2))
  ·
    obtain ⟨a, hea'⟩ := hev
    have hδ₁ : ∀ c, δ₁ c = c ^ (p ^ (3 * a)) := fun c => by
      rw [← hΘα]
      exact (hδc c).trans (congrArg (fun n => c ^ p ^ n) (by omega))
    have hα₁' : (twistedEquivC0 p e hp2 he).symm.trans (α.trans (twistedEquivC0 p e hp2 he)) =
        α₁ := by
      rw [hα₁def, heT]
    exact (false_of_quadratic_d4 hp2 he (a := a) (by omega) α hα hR hαR hab g₁ δ₁ hδ₁
      (hα₁'.trans hgδ)).elim

end D4

theorem exists_conj_of_transport {K E : Type*} [Group K] [Group E] (f : K →* E)
    (hf : Function.Bijective f) (φ : MulAut E) (hφ : φ * φ = 1) {R : Subgroup K}
    (hφR : (R.map f).map φ.toMonoidHom = R.map f)
    (hab : ∀ P : Subgroup E, IsPGroup 2 P → P ≤ R.map f → (∀ x ∈ P, φ x = x) →
      ∀ x ∈ P, ∀ y ∈ P, x * y = y * x)
    (hK : ∀ α : MulAut K, α * α = 1 → R.map α.toMonoidHom = R →
      (∀ P : Subgroup K, IsPGroup 2 P → P ≤ R → (∀ x ∈ P, α x = x) →
        ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) → ∃ g, α = MulAut.conj g) :
    ∃ x, φ = MulAut.conj x := by
  set ψ := MulEquiv.ofBijective f hf with hψ
  have hψf : ∀ k, ψ k = f k := fun k => rfl
  set α : MulAut K := ψ.trans (φ.trans ψ.symm) with hαdef
  have hαx : ∀ k, f (α k) = φ (f k) := fun k => by
    rw [← hψf, hαdef, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.apply_symm_apply,
      hψf]
  have hα : α * α = 1 := MulEquiv.ext fun k => hf.1 (by
    rw [MulAut.mul_apply, hαx, hαx, ← MulAut.mul_apply, hφ, MulAut.one_apply, MulAut.one_apply])
  have hαR : R.map α.toMonoidHom = R := by
    have hmap : (R.map α.toMonoidHom).map f = R.map f := by
      rw [Subgroup.map_map, ← hφR, Subgroup.map_map]
      congr 1
      ext k
      exact hαx k
    exact Subgroup.map_injective hf.1 hmap
  obtain ⟨g, hg⟩ := hK α hα hαR fun P hP2 hPR hPfix x hx y hy => by
    have h := hab (P.map f) (hP2.map f) (Subgroup.map_mono hPR) (by
      rintro _ ⟨z, hz, rfl⟩
      rw [← hαx, hPfix z hz]) (f x) ⟨x, hx, rfl⟩ (f y) ⟨y, hy, rfl⟩
    exact hf.1 (by rw [map_mul, map_mul, h])
  refine ⟨f g, MulEquiv.ext fun x => ?_⟩
  obtain ⟨k, rfl⟩ := hf.2 x
  rw [← hαx, hg, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]

theorem factM1Core :
    ∀ (p e : ℕ) [Fact p.Prime], p ≠ 2 → 5 ≤ p ^ e →
      ∀ (E : Type) [Group E] [Finite E] [IsSimpleGroup E] (Ω : Set (Subgroup E))
        (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (k e' : ℕ),
          ((t = .G2 ∧ k = 0) ∨ (t = .trialityD4 ∧ k = 0)) →
          Nonempty (CFSG.ClassicalInvolution.Asc77.Ih8Model p e Ω t k e') →
          ∀ φ : MulAut E, φ * φ = 1 → (∀ L ∈ Ω, L.map φ.toMonoidHom ∈ Ω) →
            ∀ L ∈ Ω, L.map φ.toMonoidHom = L →
              (∀ P : Subgroup E, IsPGroup 2 P → P ≤ L → (∀ x ∈ P, φ x = x) →
                ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) →
              ∃ x : E, φ = MulAut.conj x := by
  intro p e _ hp2 _ E _ _ _ Ω t k e' ht ⟨M⟩ φ hφ _ L hL hφL hab
  have he' : 1 ≤ e' := M.admissible.2.1
  have htag : t = .G2 ∨ t = .trialityD4 := by
    rcases ht with ⟨rfl, -⟩ | ⟨rfl, -⟩
    exacts [Or.inl rfl, Or.inr rfl]
  obtain ⟨R, hRcls, rfl⟩ := (M.mem_iff L).mp hL
  have hRfund := M.cls_sub hRcls
  have hinj : Function.Injective M.ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact M.ker_le_center.trans
      (RouteD.G2D4.center_modelUniv_g2d4_eq_bot hp2 htag k he').le
  refine exists_conj_of_transport M.ψ ⟨hinj, M.surj⟩ φ hφ hφL hab fun α hα hαR habα => ?_
  rcases ht with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact factM1_g2 hp2 he' α hα hRfund hαR habα
  · exact factM1_d4 hp2 he' α hα hRfund hαR habα

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19F
