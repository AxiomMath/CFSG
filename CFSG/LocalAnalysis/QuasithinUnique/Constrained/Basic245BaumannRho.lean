module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245Lin2Act
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245BaumannTwist
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellGamma

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin Subgroup CFSG.QuasithinUnique.Setup.Campbell
open scoped commutatorElement MatrixGroups

namespace C56

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {F : Type} [Field F]

theorem exists_rho_phi [Fintype F] [CharP F 2] (hF : 2 < Fintype.card F) (D : Lin2Data L F)
    {H R : Subgroup G} (hHN : H ≤ normalizer (L : Set G)) (hHLR : H = L ⊔ R)
    (hR2 : IsPGroup 2 R) (hRH : R ≤ H) (hLH : L ≤ H) :
    ∃ (ρ : ↥H →* Gamma F) (φ : ↥(blockU L) →* Multiplicative (Fin 2 → F)),
      Function.Surjective φ ∧ φ.ker = D.β.ker ∧
      (∀ (h : ↥H) (u v : ↥(blockU L)), (v : G) = (h : G) * u * (h : G)⁻¹ →
        Multiplicative.toAdd (φ v) = (ρ h : Equiv.Perm (Fin 2 → F)) (Multiplicative.toAdd (φ u))) ∧
      (∀ l : ↥L, ((ρ ⟨l, hLH l.2⟩ : Gamma F) : Equiv.Perm (Fin 2 → F)) = slPerm F (D.α l)) := by
  classical
  have hRN : R ≤ normalizer (L : Set G) := fun g hg => hHN (hRH hg)
  obtain ⟨Ψ, hΨ⟩ := exists_psi D hHN
  obtain ⟨Φ, hΦ⟩ := exists_phi D hHN Ψ hΨ
  have hΨmul : ∀ (h h' : ↥H) (v : Fin 2 → F), Ψ (h * h') v = Ψ h (Ψ h' v) := fun h h' v => by
    rw [map_mul]; rfl
  have hΨone : ∀ v : Fin 2 → F, Ψ 1 v = v := fun v => by rw [map_one]; rfl
  obtain ⟨dd, hdd⟩ : ∃ dd : ↥H → F, ∀ h,
      dd h = omega (Ψ h (Pi.single 0 1)) (Ψ h (Pi.single 1 1)) := ⟨_, fun _ => rfl⟩
  have hsemi : ∀ (h : ↥H) (v w : Fin 2 → F),
      omega (Ψ h v) (Ψ h w) = dd h * Φ h (omega v w) := fun h v w => by
    rw [hdd]; exact omega_semilinear (Ψ h) (Φ h) (fun c v => hΦ h c v) v w
  have hcocycle : ∀ h h' : ↥H, dd (h * h') = dd h * Φ h (dd h') := by
    intro h h'
    rw [hdd (h * h'), hΨmul h h', hΨmul h h', hsemi, hdd h']
  have hsurj : ∀ (h : ↥H) (w : Fin 2 → F), ∃ v, Ψ h v = w := fun h w =>
    ⟨Ψ h⁻¹ w, by rw [← hΨmul, mul_inv_cancel, hΨone]⟩
  have hne : ∀ h, dd h ≠ 0 := by
    intro h h0
    obtain ⟨v, hv⟩ := hsurj h (Pi.single 0 1)
    obtain ⟨w, hw⟩ := hsurj h (Pi.single 1 1)
    have := hsemi h v w
    rw [hv, hw, omega_basis, h0, zero_mul] at this
    exact one_ne_zero this
  have hΨL : ∀ (l : ↥L) (w : Fin 2 → F),
      Ψ ⟨l, hLH l.2⟩ w = (D.α l : Matrix (Fin 2) (Fin 2) F).mulVec w := by
    intro l w
    obtain ⟨u, hu⟩ := D.surj_β (Multiplicative.ofAdd w)
    have hw : Multiplicative.toAdd (D.β u) = w := by rw [hu]; rfl
    have hlu : (l : G) * u * (l : G)⁻¹ ∈ blockU L :=
      (Subgroup.mem_normalizer_iff.mp (C1.le_normalizer_blockU L l.2) u).mp u.2
    rw [← hw]
    exact (hΨ ⟨l, hLH l.2⟩ u ⟨_, hlu⟩ rfl).trans (D.equiv l u ⟨_, hlu⟩ rfl)
  have hΦL : ∀ l : ↥L, Φ ⟨l, hLH l.2⟩ = 1 := by
    intro l
    refine sigma_unique (Ψ.toHomUnits ⟨l, hLH l.2⟩) (σ := Φ ⟨l, hLH l.2⟩) (σ' := 1) ?_ ?_
    · intro c v; exact hΦ _ c v
    · intro c v
      show Ψ ⟨l, hLH l.2⟩ (c • v) = (1 : RingAut F) c • Ψ ⟨l, hLH l.2⟩ v
      rw [hΨL, hΨL, Matrix.mulVec_smul]; rfl
  have hddL : ∀ l : ↥L, dd ⟨l, hLH l.2⟩ = 1 := by
    intro l
    rw [hdd, hΨL, hΨL, omega_mulVec, Matrix.SpecialLinearGroup.det_coe, one_mul, omega_basis]
  have : Fintype ↥R := Fintype.ofFinite _
  obtain ⟨M, hM0, hM⟩ := exists_coboundary hF hR2 (Φ.comp (Subgroup.inclusion hRH))
    (fun r => dd (Subgroup.inclusion hRH r)) (fun r => hne _)
    (fun p q => by rw [map_mul]; exact hcocycle _ _)
  have hMall : ∀ h : ↥H, dd h * Φ h M = M := by
    intro h
    have hh : (h : G) ∈ R ⊔ L := by rw [sup_comm, ← hHLR]; exact h.2
    obtain ⟨r, hr, l, hl, hrl⟩ := C5.mem_sup_of_le_normalizer hRN hh
    have hh' : h = Subgroup.inclusion hRH ⟨r, hr⟩ * ⟨l, hLH hl⟩ := Subtype.ext hrl
    have h1 : dd ⟨l, hLH hl⟩ = 1 := hddL ⟨l, hl⟩
    have h2 : Φ ⟨l, hLH hl⟩ = 1 := hΦL ⟨l, hl⟩
    have h3 : dd h = dd (Subgroup.inclusion hRH ⟨r, hr⟩) := by
      rw [hh', hcocycle, h1, map_one, mul_one]
    have h4 : Φ h M = Φ (Subgroup.inclusion hRH ⟨r, hr⟩) M := by
      rw [hh', map_mul, h2]; rfl
    rw [h3, h4]
    exact hM ⟨r, hr⟩
  obtain ⟨μ, hμ⟩ : IsSquare M⁻¹ := FiniteField.isSquare_of_char_two (ringChar.eq F 2) M⁻¹
  have hμ0 : μ ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hμ
    exact inv_ne_zero hM0 hμ
  have hMμ : M = (μ * μ)⁻¹ := by rw [← hμ, inv_inv]
  have hdet : ∀ h : ↥H, (μ * (Φ h μ)⁻¹) ^ 2 * dd h = 1 := by
    intro h
    have e1 := hMall h
    have hΦμ : Φ h μ ≠ 0 := by simpa using hμ0
    have e2 : Φ h M = (Φ h μ * Φ h μ)⁻¹ := by rw [hMμ, map_inv₀, map_mul]
    rw [e2, hMμ] at e1
    field_simp at e1 ⊢
    linear_combination e1
  let μu : Fˣ := Units.mk0 μ hμ0
  let sc : Equiv.Perm (Fin 2 → F) := MulAction.toPermHom Fˣ (Fin 2 → F) μu
  have hsc : ∀ w, sc w = μ • w := fun w => rfl
  have hsc' : ∀ w, sc⁻¹ w = μ⁻¹ • w := by
    intro w
    rw [Equiv.Perm.inv_def, Equiv.symm_apply_eq, hsc, smul_inv_smul₀ hμ0]
  let Ψp : ↥H →* Equiv.Perm (Fin 2 → F) :=
    (MulAction.toPermHom (AddMonoid.End (Fin 2 → F))ˣ (Fin 2 → F)).comp Ψ.toHomUnits
  have hΨp : ∀ h w, Ψp h w = Ψ h w := fun h w => rfl
  let ρ₀ : ↥H →* Equiv.Perm (Fin 2 → F) := (MulAut.conj sc).toMonoidHom.comp Ψp
  have hρ₀ : ∀ h w, ρ₀ h w = μ • Ψ h (μ⁻¹ • w) := by
    intro h w
    show (sc * Ψp h * sc⁻¹) w = _
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hsc', hΨp, hsc]
  let Ψa : ↥H → ((Fin 2 → F) →+ (Fin 2 → F)) := fun h => Ψ h
  have hmem : ∀ h, ρ₀ h ∈ Gamma F := by
    intro h
    have hdetg : (colMat (Ψa h)).det = dd h := by
      rw [det_colMat]; exact (hdd h).symm
    have hdet' : ((μ * (Φ h μ)⁻¹) • colMat (Ψa h)).det = 1 := by
      rw [Matrix.det_smul, hdetg, Fintype.card_fin]
      exact hdet h
    let A : SL(2, F) := ⟨(μ * (Φ h μ)⁻¹) • colMat (Ψa h), hdet'⟩
    refine ⟨A, Φ h, ?_⟩
    ext w : 1
    have hv := colMat_mulVec (Ψa h) (Φ h) (fun c v => hΦ h c v) (μ⁻¹ • w)
    rw [hρ₀, semilinPerm_apply, Matrix.SpecialLinearGroup.smul_def]
    show μ • Ψa h (μ⁻¹ • w) = ((μ * (Φ h μ)⁻¹) • colMat (Ψa h)).mulVec (fun i => Φ h (w i))
    rw [hv]
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, map_mul] <;> ring
  let ρ : ↥H →* Gamma F := ρ₀.codRestrict (Gamma F) hmem
  have hρ : ∀ h, ((ρ h : Gamma F) : Equiv.Perm (Fin 2 → F)) = ρ₀ h := fun h => rfl
  let sm : (Fin 2 → F) →+ (Fin 2 → F) := AddMonoidHom.mk' (fun w : Fin 2 → F => μ • w) (fun v w => smul_add μ v w)
  let φ : ↥(blockU L) →* Multiplicative (Fin 2 → F) :=
    (AddMonoidHom.toMultiplicative sm).comp D.β
  have hφ : ∀ u, Multiplicative.toAdd (φ u) = μ • Multiplicative.toAdd (D.β u) := fun u => rfl
  refine ⟨ρ, φ, ?_, ?_, ?_, ?_⟩
  · intro w
    obtain ⟨u, hu⟩ := D.surj_β (Multiplicative.ofAdd (μ⁻¹ • Multiplicative.toAdd w))
    refine ⟨u, ?_⟩
    apply Multiplicative.toAdd.injective
    rw [hφ, hu]
    show μ • (μ⁻¹ • Multiplicative.toAdd w) = Multiplicative.toAdd w
    exact smul_inv_smul₀ hμ0 _
  · ext u
    simp only [MonoidHom.mem_ker]
    constructor
    · intro h
      have h' : μ • Multiplicative.toAdd (D.β u) = 0 := by
        have := congrArg Multiplicative.toAdd h
        simpa [hφ] using this
      have : Multiplicative.toAdd (D.β u) = 0 := by
        rcases smul_eq_zero.mp h' with h0 | h0
        · exact absurd h0 hμ0
        · exact h0
      apply Multiplicative.toAdd.injective
      simpa using this
    · intro h
      apply Multiplicative.toAdd.injective
      rw [hφ, h]
      simp
  · intro h u v hv
    rw [hρ, hρ₀, hφ v, hφ u, ← hΨ h u v hv, inv_smul_smul₀ hμ0]
  · intro l
    rw [hρ]
    ext w
    rw [hρ₀, slPerm_apply, hΨL, Matrix.mulVec_smul, smul_inv_smul₀ hμ0]
    rfl

end C56

end CFSG.QuasithinUnique
