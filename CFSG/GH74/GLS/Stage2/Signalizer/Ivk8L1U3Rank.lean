module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Defs
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67U3Aut
import CFSG.RankThree.SubgroupLists.SL3Involutions
import CFSG.GH74.GLS.IVK.L2.Lemma12
import CFSG.GH74.Generic.Context
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSemilinearInvolution

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L1

open Matrix CFSG CFSG.Blueprint CFSG.GH74.GLS.Stage2.Signalizer.Odd87
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.GH74.GLS.Stage2.Bender.Thm1

section Sim

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

def u3LinSim : Subgroup (semilinearSimilitudes h 1 1) :=
  (SemidirectProduct.rightHom.comp (semilinearSimilitudes h 1 1).subtype).ker

theorem mem_u3LinSim {x : semilinearSimilitudes h 1 1} :
    x ∈ u3LinSim h ↔ (x : SemiGL (HypIndex 1 1) K).right = 1 :=
  Iff.rfl

def u3LinLeft : u3LinSim h →* GL (HypIndex 1 1) K where
  toFun x := (x : SemiGL (HypIndex 1 1) K).left
  map_one' := rfl
  map_mul' x y := by
    have hx : (x : SemiGL (HypIndex 1 1) K).right = 1 := x.2
    show ((x : SemiGL (HypIndex 1 1) K) * (y : SemiGL (HypIndex 1 1) K)).left = _
    rw [SemidirectProduct.mul_left, hx, map_one, MulAut.one_apply]

theorem u3LinLeft_apply (x : u3LinSim h) :
    u3LinLeft h x = (x : SemiGL (HypIndex 1 1) K).left := by
  simp [u3LinLeft]

theorem u3LinLeft_injective : Function.Injective (u3LinLeft h) := by
  intro x y hxy
  apply Subtype.ext
  apply Subtype.ext
  apply SemidirectProduct.ext
  · exact hxy
  · rw [(mem_u3LinSim h).mp x.2, (mem_u3LinSim h).mp y.2]

noncomputable def u3Phi : u3LinSim h →* MulAut (hypPSU h 1 1) :=
  (semilinearAutHom h (le_refl 1) (le_refl 1)).comp (u3LinSim h).subtype

theorem u3Phi_eq_one_iff (x : u3LinSim h) :
    u3Phi h x = 1 ↔ ∃ c : Kˣ, u3LinLeft h x = GeneralLinearGroup.scalar (HypIndex 1 1) c := by
  have := semilinearAutHom_eq_one_iff h (le_refl 1) (le_refl 1) (by norm_num) x.1
  constructor
  · intro h1
    exact (this.mp h1).2
  · intro h2
    exact this.mpr ⟨x.2, h2⟩

def u3ScalarSim (c : Kˣ) : u3LinSim h :=
  ⟨⟨SemidirectProduct.inl (GeneralLinearGroup.scalar (HypIndex 1 1) c), scalarSim_mem h c⟩, by
    rw [mem_u3LinSim]
    exact SemidirectProduct.right_inl (φ := glAut) (GeneralLinearGroup.scalar (HypIndex 1 1) c)⟩

theorem u3LinLeft_scalarSim (c : Kˣ) :
    u3LinLeft h (u3ScalarSim h c) = GeneralLinearGroup.scalar (HypIndex 1 1) c := by
  rw [u3LinLeft_apply]
  exact SemidirectProduct.left_inl (φ := glAut) (GeneralLinearGroup.scalar (HypIndex 1 1) c)

theorem u3Phi_scalarSim (c : Kˣ) : u3Phi h (u3ScalarSim h c) = 1 :=
  (u3Phi_eq_one_iff h _).mpr ⟨c, u3LinLeft_scalarSim h c⟩

theorem exists_u3Phi_eq (hp : p ≠ 2) {v : MulAut (hypPSU h 1 1)} (hv : u3Sigma h hp v = 1) :
    ∃ x : u3LinSim h, u3Phi h x = v := by
  obtain ⟨x, hx⟩ := semilinearAutHom_surjective h (le_refl 1) (le_refl 1) hp (by norm_num) v
  have hxr : (x : SemiGL (HypIndex 1 1) K).right = 1 := by
    rw [← u3Sigma_apply h hp x, hx, hv]
  exact ⟨⟨x, hxr⟩, hx⟩

end Sim

section Mat

variable {K : Type} [Field K]

theorem u3_det_scalar (c : Kˣ) :
    GeneralLinearGroup.det (GeneralLinearGroup.scalar (HypIndex 1 1) c) = c ^ 3 := by
  rw [GeneralLinearGroup.det_scalar]
  simp

theorem u3_scalar_eq_one {c : Kˣ} (hc : GeneralLinearGroup.scalar (HypIndex 1 1) c = 1) :
    c = 1 := by
  have h1 := congrArg Units.val hc
  rw [GeneralLinearGroup.coe_scalar, Units.val_one,
    ← map_one (Matrix.scalar (HypIndex 1 1) : K →+* Matrix (HypIndex 1 1) (HypIndex 1 1) K),
    Matrix.scalar_inj] at h1
  exact Units.ext h1

theorem u3_square_eq_one {A B : GL (HypIndex 1 1) K} (hA : A * A = 1) (hB : B * B = 1)
    (hdA : GeneralLinearGroup.det A = 1) (hdB : GeneralLinearGroup.det B = 1) {c : Kˣ}
    (hc : A * B * A * B = GeneralLinearGroup.scalar (HypIndex 1 1) c) :
    A * B * (A * B) = 1 := by
  have h3 : c ^ 3 = 1 := by
    have := congrArg GeneralLinearGroup.det hc
    rw [u3_det_scalar] at this
    rw [← this]
    simp only [map_mul, hdA, hdB, mul_one]
  have h1 : GeneralLinearGroup.scalar (HypIndex 1 1) c = B * A * B * A := by
    calc GeneralLinearGroup.scalar (HypIndex 1 1) c
        = A * GeneralLinearGroup.scalar (HypIndex 1 1) c * A := by
          rw [← GeneralLinearGroup.scalar_commute c A, mul_assoc, hA, mul_one]
      _ = A * (A * B * A * B) * A := by rw [hc]
      _ = (A * A) * B * A * B * A := by group
      _ = B * A * B * A := by rw [hA, one_mul]
  have h2 : c * c = 1 := by
    apply u3_scalar_eq_one
    calc GeneralLinearGroup.scalar (HypIndex 1 1) (c * c)
        = GeneralLinearGroup.scalar (HypIndex 1 1) c *
          GeneralLinearGroup.scalar (HypIndex 1 1) c := map_mul _ _ _
      _ = (A * B * A * B) * (B * A * B * A) := congrArg₂ (· * ·) hc.symm h1
      _ = A * B * A * (B * B) * A * B * A := by group
      _ = A * B * (A * A) * B * A := by rw [hB]; group
      _ = A * (B * B) * A := by rw [hA]; group
      _ = A * A := by rw [hB]; group
      _ = 1 := hA
  have hc1 : c = 1 := by
    calc c = c ^ 3 * (c * c)⁻¹ := by group
      _ = 1 := by rw [h3, h2]; simp
  rw [hc1, map_one] at hc
  rw [← hc]
  group

theorem u3_exists_normalized {A₀ : GL (HypIndex 1 1) K} {c : Kˣ}
    (h2 : A₀ * A₀ = GeneralLinearGroup.scalar (HypIndex 1 1) c) :
    ∃ s : Kˣ, (A₀ * GeneralLinearGroup.scalar (HypIndex 1 1) s) *
        (A₀ * GeneralLinearGroup.scalar (HypIndex 1 1) s) = 1 ∧
      GeneralLinearGroup.det (A₀ * GeneralLinearGroup.scalar (HypIndex 1 1) s) = 1 := by
  have hd : (GeneralLinearGroup.det A₀) ^ 2 = c ^ 3 := by
    have := congrArg GeneralLinearGroup.det h2
    rw [u3_det_scalar, map_mul] at this
    rw [pow_two]; exact this
  obtain ⟨s, hs⟩ : ∃ s : Kˣ, s = c * (GeneralLinearGroup.det A₀)⁻¹ := ⟨_, rfl⟩
  have hc3 : c * c * c = (GeneralLinearGroup.det A₀) ^ 2 := by rw [hd, pow_three']
  have hss : c * (s * s) = 1 := by
    rw [hs]
    calc c * (c * (GeneralLinearGroup.det A₀)⁻¹ * (c * (GeneralLinearGroup.det A₀)⁻¹))
        = c * c * c * ((GeneralLinearGroup.det A₀)⁻¹ * (GeneralLinearGroup.det A₀)⁻¹) := by
          ac_rfl
      _ = 1 := by rw [hc3]; group
  refine ⟨s, ?_, ?_⟩
  · calc (A₀ * GeneralLinearGroup.scalar (HypIndex 1 1) s) *
          (A₀ * GeneralLinearGroup.scalar (HypIndex 1 1) s)
        = A₀ * (GeneralLinearGroup.scalar (HypIndex 1 1) s * A₀) *
          GeneralLinearGroup.scalar (HypIndex 1 1) s := by group
      _ = A₀ * (A₀ * GeneralLinearGroup.scalar (HypIndex 1 1) s) *
          GeneralLinearGroup.scalar (HypIndex 1 1) s := by
          rw [GeneralLinearGroup.scalar_commute s A₀]
      _ = (A₀ * A₀) * (GeneralLinearGroup.scalar (HypIndex 1 1) s *
          GeneralLinearGroup.scalar (HypIndex 1 1) s) := by group
      _ = GeneralLinearGroup.scalar (HypIndex 1 1) (c * (s * s)) := by
          rw [h2, map_mul, map_mul]
      _ = 1 := by rw [hss, map_one]
  · rw [map_mul, u3_det_scalar, hs, mul_pow, ← hd]
    group

end Mat

section Main

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

noncomputable def u3Reindex : GL (HypIndex 1 1) K ≃* GL (Fin 3) K :=
  Units.mapEquiv (Matrix.reindexAlgEquiv K K (Fintype.equivFinOfCardEq
    (by simp : Fintype.card (HypIndex 1 1) = 3))).toMulEquiv

theorem u3Reindex_det (g : GL (HypIndex 1 1) K) :
    ((u3Reindex g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det =
      ((g : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K).det :=
  Matrix.det_reindexAlgEquiv K K _ _

theorem u3_card_le_four (hp : p ≠ 2) (X : Subgroup (MulAut (hypPSU h 1 1)))
    (hσ : ∀ v ∈ X, u3Sigma h hp v = 1) (hsq : ∀ v ∈ X, v * v = 1)
    (hcomm : ∀ v ∈ X, ∀ w ∈ X, v * w = w * v) : Nat.card X ≤ 4 := by
  classical
  have hfin : Finite K := h.finite
  have h2 : (2 : K) ≠ 0 := by
    have := h.charP
    intro h20
    have h21 : ((2 : ℕ) : K) = 0 := by exact_mod_cast h20
    rw [CharP.cast_eq_zero_iff K p] at h21
    exact hp ((Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_two).mp h21)
  let N : Subgroup (u3LinSim h) :=
    { carrier := {x | u3Phi h x ∈ X ∧ GeneralLinearGroup.det (u3LinLeft h x) = 1 ∧
        u3LinLeft h x * u3LinLeft h x = 1}
      mul_mem' := by
        rintro x y ⟨hxX, hxd, hxs⟩ ⟨hyX, hyd, hys⟩
        refine ⟨by rw [map_mul]; exact X.mul_mem hxX hyX, ?_, ?_⟩
        · rw [map_mul, map_mul, hxd, hyd, mul_one]
        · have h1 : u3Phi h (x * y * x * y) = 1 := by
            have hxx' := hsq _ hxX
            have hyy' := hsq _ hyX
            have hyx := hcomm _ hyX _ hxX
            simp only [map_mul]
            calc u3Phi h x * u3Phi h y * u3Phi h x * u3Phi h y
                = u3Phi h x * (u3Phi h y * u3Phi h x) * u3Phi h y := by group
              _ = u3Phi h x * (u3Phi h x * u3Phi h y) * u3Phi h y := by rw [hyx]
              _ = (u3Phi h x * u3Phi h x) * (u3Phi h y * u3Phi h y) := by group
              _ = 1 := by rw [hxx', hyy', one_mul]
          obtain ⟨c, hc⟩ := (u3Phi_eq_one_iff h _).mp h1
          simp only [map_mul] at hc
          rw [map_mul]
          exact u3_square_eq_one hxs hys hxd hyd hc
      one_mem' := ⟨by rw [map_one]; exact X.one_mem, by rw [map_one, map_one], by simp⟩
      inv_mem' := by
        rintro x ⟨hxX, hxd, hxs⟩
        have hxi : (u3LinLeft h x)⁻¹ = u3LinLeft h x := inv_eq_of_mul_eq_one_right hxs
        refine ⟨by rw [map_inv]; exact X.inv_mem hxX, ?_, ?_⟩
        · rw [map_inv, hxi]; exact hxd
        · rw [map_inv, hxi]; exact hxs }
  have hN : Nat.card N ≤ 4 := by
    let ψ : u3LinSim h →* GL (Fin 3) K := (u3Reindex (K := K)).toMonoidHom.comp (u3LinLeft h)
    have hψ : Function.Injective ψ := (u3Reindex (K := K)).injective.comp (u3LinLeft_injective h)
    have := CFSG.RankThree.SubgroupLists.card_le_four_of_sq_eq_one_sl3 h2 (N.map ψ)
      (by
        rintro _ ⟨x, hx, rfl⟩
        change u3Reindex (u3LinLeft h x) * u3Reindex (u3LinLeft h x) = 1
        rw [← map_mul, hx.2.2, map_one])
      (by
        rintro _ ⟨x, hx, rfl⟩
        change ((u3Reindex (u3LinLeft h x) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1
        rw [u3Reindex_det, ← GeneralLinearGroup.val_det_apply, hx.2.1, Units.val_one])
    rwa [Subgroup.card_map_of_injective hψ] at this
  have hfinN : Finite N := by
    have : Finite (GL (HypIndex 1 1) K) := inferInstance
    exact Finite.of_injective (fun x : N => u3LinLeft h x)
      (fun x y hxy => Subtype.ext (u3LinLeft_injective h hxy))
  have hsurj : Function.Surjective (fun x : N => (⟨u3Phi h x, x.2.1⟩ : X)) := by
    rintro ⟨v, hv⟩
    obtain ⟨x₀, hx₀⟩ := exists_u3Phi_eq h hp (hσ v hv)
    have h1 : u3Phi h (x₀ * x₀) = 1 := by rw [map_mul, hx₀]; exact hsq v hv
    obtain ⟨c, hc⟩ := (u3Phi_eq_one_iff h _).mp h1
    rw [map_mul] at hc
    obtain ⟨s, hs1, hs2⟩ := u3_exists_normalized hc
    rw [← u3LinLeft_scalarSim h s, ← map_mul] at hs1 hs2
    refine ⟨⟨x₀ * u3ScalarSim h s, ?_, hs2, hs1⟩, Subtype.ext ?_⟩
    · simp only [map_mul, u3Phi_scalarSim, mul_one, hx₀]; exact hv
    · change u3Phi h (x₀ * u3ScalarSim h s) = v
      simp only [map_mul, u3Phi_scalarSim, mul_one, hx₀]
  exact (Nat.card_le_card_of_surjective _ hsurj).trans hN

end Main

section Rank

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem u3_elemAbelian_le_eight (hp : p ≠ 2) (E : Subgroup (MulAut (hypPSU h 1 1)))
    (hE : IsElementaryAbelian 2 ↥E) : Nat.card ↥E ≤ 8 := by
  classical
  have := hE
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfin : Finite K := h.finite
  have hpow : ∀ a : ↥E, a ^ 2 = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 ↥E)
  set φ : ↥E →* (K ≃+* K) := (u3Sigma h hp).comp E.subtype with hφ
  have hker : Nat.card φ.ker ≤ 4 := by
    set X : Subgroup (MulAut (hypPSU h 1 1)) := φ.ker.map E.subtype with hX
    have hcard : Nat.card X = Nat.card φ.ker :=
      Subgroup.card_map_of_injective E.subtype_injective
    have h4 := u3_card_le_four h hp X
      (by
        rintro _ ⟨a, ha, rfl⟩
        exact MonoidHom.mem_ker.mp ha)
      (by
        rintro _ ⟨a, -, rfl⟩
        have h1 := hpow a
        rw [pow_two] at h1
        exact congrArg Subtype.val h1)
      (by
        rintro _ ⟨a, -, rfl⟩ _ ⟨b, -, rfl⟩
        exact congrArg Subtype.val (hE.toIsMulCommutative.is_comm.comm a b))
    omega
  have hrange : Nat.card φ.range ≤ 2 := by
    have := CFSG.GH74.GLS.IVK.ringAut_isCyclic K
    have : IsCyclic φ.range := Subgroup.isCyclic _
    have h1 : Monoid.exponent φ.range ∣ 2 := by
      rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
      rintro ⟨_, a, rfl⟩
      apply Subtype.ext
      show φ a ^ 2 = 1
      rw [← map_pow, hpow a, map_one]
    rw [IsCyclic.exponent_eq_card] at h1
    exact Nat.le_of_dvd (by norm_num) h1
  have := Subgroup.card_ker_mul_card_range φ
  nlinarith

end Rank

theorem fu3_elemAbelian_le_eight {Y : Type} [Group Y] [Finite Y] (hY : FU3 Y)
    (E : Subgroup (MulAut Y)) (hE : CFSG.IsElementaryAbelian 2 ↥E) : Nat.card ↥E ≤ 8 := by
  obtain ⟨p, f, hp, hf, hp2, hLie⟩ := hY
  obtain ⟨-, -, F, _, _, hF, ⟨e₀⟩⟩ := CFSG.GH74.Generic.lieModel_psu_data hLie
  have h : UnitaryFieldData p f F := ⟨hp, hf, by rw [hF, ← pow_mul, mul_comm]⟩
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := 1) (ε := 1) h
  let e : Y ≃* hypPSU h 1 1 := e₀.trans (hypPSUEquivStatedProj h hR (by norm_num)).symm
  let c : MulAut Y ≃* MulAut (hypPSU h 1 1) := MulAut.congr e
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hE
  have hE' : IsElementaryAbelian 2 ↥(E.map c.toMonoidHom) := IsElementaryAbelian.map c.toMonoidHom
  have h8 := u3_elemAbelian_le_eight h hp2 (E.map c.toMonoidHom) hE'
  rwa [Subgroup.card_map_of_injective c.injective] at h8

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L1
