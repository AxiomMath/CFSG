module

public import CFSG.LieType.Steinberg.CentralExt.HermitianBasis
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary Matrix

section Fix

variable {F : Type} [Field F]

@[expose] def fixF (σ : F ≃+* F) : Subfield F := FixedPoints.subfield (Subgroup.zpowers σ) F

theorem mem_fixF {σ : F ≃+* F} {x : F} : x ∈ fixF σ ↔ σ x = x := by
  unfold fixF
  constructor
  · intro h
    exact h ⟨σ, Subgroup.mem_zpowers σ⟩
  · intro h g
    obtain ⟨k, hk⟩ := g.2
    have hg : (g : F ≃+* F) = σ ^ k := hk.symm
    have hk' : ∀ k : ℤ, (σ ^ k) x = x := by
      intro k
      induction k using Int.induction_on with
      | zero => simp
      | succ n ih => rw [_root_.zpow_add_one, RingAut.mul_apply, h, ih]
      | pred n ih =>
        rw [_root_.zpow_sub_one]
        have : σ⁻¹ x = x := σ.symm_apply_eq.mpr h.symm
        rw [RingAut.mul_apply, this, ih]
    show (g : F ≃+* F) x = x
    rw [hg]
    exact hk' k

end Fix

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

theorem exists_card_fixF (hF : Nat.card F = (p ^ f) ^ 2) {σ : F ≃+* F} (hσ : orderOf σ = 3) :
    ∃ k : ℕ, f = 3 * k ∧ Nat.card (fixF σ) = (p ^ k) ^ 2 := by
  have hc := CFSG.GorensteinWalter.nat_card_eq_fixedSubfield_card_pow_orderOf F σ
  simp only [hσ] at hc
  have : Fintype F := Fintype.ofFinite F
  let _ : Fintype (fixF σ) := Fintype.ofFinite _
  have : CharP (fixF σ) p := (fixF σ).charP p
  obtain ⟨m, -, hm⟩ := FiniteField.card (fixF σ) p
  have hm' : Nat.card (fixF σ) = p ^ (m : ℕ) := by rw [Nat.card_eq_fintype_card, hm]
  have hp := (Fact.out : p.Prime)
  have hc' : Nat.card F = Nat.card (fixF σ) ^ 3 := hc
  have h1 : p ^ (3 * (m : ℕ)) = p ^ (2 * f) :=
    calc p ^ (3 * (m : ℕ)) = (p ^ (m : ℕ)) ^ 3 := by ring
      _ = Nat.card (fixF σ) ^ 3 := by rw [hm']
      _ = Nat.card F := hc'.symm
      _ = (p ^ f) ^ 2 := hF
      _ = p ^ (2 * f) := by ring
  have h2 := Nat.pow_right_injective hp.two_le h1
  refine ⟨f / 3, by omega, ?_⟩
  rw [hm', ← pow_mul]
  congr 1
  omega

theorem unitaryInvolution_eq_pow_of_mem {k : ℕ}
    {σ : F ≃+* F} (hk : Nat.card (fixF σ) = (p ^ k) ^ 2) {x : F} (hx : x ∈ fixF σ) :
    unitaryInvolution F p (3 * k) x = x ^ p ^ k := by
  have : Fintype (fixF σ) := Fintype.ofFinite _
  have h1 : (⟨x, hx⟩ : fixF σ) ^ (p ^ k) ^ 2 = ⟨x, hx⟩ := by
    rw [← hk, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card _
  have h2 : x ^ (p ^ k) ^ 2 = x := congrArg Subtype.val h1
  have h3 : p ^ (3 * k) = (p ^ k) ^ 2 * p ^ k := by ring
  rw [unitaryInvolution_apply, h3, pow_mul, h2]

theorem exists_fixed_conjTr {n k : ℕ} {σ : F ≃+* F} (hk : Nat.card (fixF σ) = (p ^ k) ^ 2)
    {J : Matrix (Fin n) (Fin n) F} (hJσ : ∀ i j, σ (J i j) = J i j)
    (hJh : conjTr (unitaryInvolution F p (3 * k)) J = J) (hdet : J.det ≠ 0) :
    ∃ N : GL (Fin n) F, (∀ i j, σ ((N : Matrix (Fin n) (Fin n) F) i j) = N i j) ∧
      conjTr (unitaryInvolution F p (3 * k)) (N : Matrix (Fin n) (Fin n) F) * J *
        (N : Matrix (Fin n) (Fin n) F) = 1 := by
  have : Finite (fixF σ) := inferInstanceAs (Finite (fixF σ))
  have : CharP (fixF σ) p := (fixF σ).charP p
  obtain ⟨ι, hιd⟩ : ∃ ι : fixF σ →+* F, ∀ x, ι x = x := ⟨(fixF σ).subtype, fun _ => rfl⟩
  have hιinj : Function.Injective ι := fun a b h => Subtype.ext (by rwa [hιd, hιd] at h)
  let J₀ : Matrix (Fin n) (Fin n) (fixF σ) := Matrix.of fun i j => ⟨J i j, mem_fixF.2 (hJσ i j)⟩
  have hJ₀ : J₀.map ι = J := by
    ext i j
    simp [J₀, hιd]
  have hbar : ∀ x : fixF σ, ι (unitaryInvolution (fixF σ) p k x) =
      unitaryInvolution F p (3 * k) (ι x) := by
    intro x
    rw [hιd, hιd, unitaryInvolution_eq_pow_of_mem hk x.2, unitaryInvolution_apply]
    rfl
  have hUI := isUnitaryInvolution_unitaryInvolution (K := fixF σ) (p := p) (f := k) hk
  have hJ₀h : conjTr (unitaryInvolution (fixF σ) p k) J₀ = J₀ := by
    refine Matrix.ext fun i j => hιinj ?_
    have := congrFun (congrFun hJh i) j
    simp only [conjTr, Matrix.transpose_apply, Matrix.map_apply] at this ⊢
    rw [hbar]
    simpa [J₀, hιd] using this
  have hdet₀ : J₀.det ≠ 0 := by
    intro h
    apply hdet
    rw [← hJ₀, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h, map_zero]
  obtain ⟨P, hP⟩ := CFSG.LieType.Steinberg.exists_conjTr_mul_mul_eq_one_of_isUnitaryInvolution
    hUI hJ₀h hdet₀
  refine ⟨Matrix.GeneralLinearGroup.map ι P, fun i j => ?_, ?_⟩
  · have h1 : ((Matrix.GeneralLinearGroup.map ι P : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j =
        ι ((P : Matrix (Fin n) (Fin n) (fixF σ)) i j) := rfl
    rw [h1, hιd]
    exact mem_fixF.1 (((P : Matrix (Fin n) (Fin n) (fixF σ)) i j).2)
  · have h := congrArg (RingHom.mapMatrix ι) hP
    have hc : ι.mapMatrix (conjTr (unitaryInvolution (fixF σ) p k)
        (P : Matrix (Fin n) (Fin n) (fixF σ))) =
        conjTr (unitaryInvolution F p (3 * k)) (ι.mapMatrix (P : Matrix (Fin n) (Fin n) _)) := by
      ext i j
      exact hbar _
    rw [map_mul, map_mul, map_one, hc] at h
    have hN : ((Matrix.GeneralLinearGroup.map ι P : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        ι.mapMatrix (P : Matrix (Fin n) (Fin n) (fixF σ)) := rfl
    have hJ' : J = ι.mapMatrix J₀ := hJ₀.symm
    rw [hN, hJ']
    exact h

end CFSG.HardMathSupport.Solomon.Coordinator
