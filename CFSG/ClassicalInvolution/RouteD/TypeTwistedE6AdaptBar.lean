module

public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6AdaptClass
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6AdaptReal
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate120
public import Certificates.Certificate123

public section

namespace CFSG.ClassicalInvolution.RouteD.NonClassical

open Matrix CFSG.Open CFSG.ClassicalGroups.Unitary CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models CFSG.LieType.Universal.Unitary
  CFSG.ClassicalInvolution.ModelFacts.UnitaryAut CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Exotic Module
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply)
open scoped MatrixGroups

variable {p f : ℕ} [Fact p.Prime]

local notation "σU" => unitaryInvolution (GaloisField p (2 * f)) p f

section Bar

theorem mapMatrix_suMat_te6Inv (φ : GaloisField p (2 * f) ≃+* GaloisField p (2 * f)) :
    φ.mapMatrix (suMat (te6Inv p f)) = suMat (te6Inv p f) := by
  show (suMat (te6Inv p f)).map φ = suMat (te6Inv p f)
  have h : suMat (te6Inv p f) =
      zMat (GaloisField p (2 * f)) (5 + 1) (nodePair 5 0 (by norm_num)).1 := rfl
  rw [h, zMat, Matrix.diagonal_map (map_zero φ)]
  congr 1
  funext r
  split_ifs <;> simp

variable {g : GL (Fin 6) (GaloisField p (2 * f))}
  {α : Su (GaloisField p (2 * f)) p f 6 →* Su (GaloisField p (2 * f)) p f 6}

theorem sq_scalar_bar (hf : 1 ≤ f) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hα : ∀ x : Su (GaloisField p (2 * f)) p f 6,
      ((α x : GL (Fin 6) (GaloisField p (2 * f))) :
        Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) =
        (g : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) *
          (unitaryInvolution (GaloisField p (2 * f)) p f).mapMatrix
            ((x : GL (Fin 6) (GaloisField p (2 * f))) :
              Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) *
          ((g⁻¹ : GL (Fin 6) (GaloisField p (2 * f))) :
            Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))))
    (hα2 : α.comp α = MonoidHom.id _) :
    ∃ a : GaloisField p (2 * f), (g : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) *
      (unitaryInvolution (GaloisField p (2 * f)) p f).mapMatrix
        (g : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) =
        a • (1 : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) := by
  have hK : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2 := card_galoisField_two_mul_eq hq
  have hσ := isUnitaryInvolution_unitaryInvolution (p := p) (f := f) hK
  have hSS : ∀ A : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f)),
      (σU).mapMatrix ((σU).mapMatrix A) = A := fun A => Matrix.ext fun i j => hσ.invol _
  refine eq_smul_one_of_commute (unitaryFieldData_te6 hf) hp2 (by norm_num : 3 ≤ 6) _ ?_
  intro y hy
  set x : Su (GaloisField p (2 * f)) p f 6 :=
    (suEquivUnitarySU (GaloisField p (2 * f)) p f hK 6).symm ⟨y, hy⟩ with hx
  have hxy : ((x : GL (Fin 6) (GaloisField p (2 * f))) : Matrix (Fin 6) (Fin 6)
      (GaloisField p (2 * f))) = (y : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) := rfl
  have e0 : α (α x) = x := DFunLike.congr_fun hα2 x
  have e := congrArg (fun z : Su (GaloisField p (2 * f)) p f 6 =>
    ((z : GL (Fin 6) (GaloisField p (2 * f))) : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f)))) e0
  simp only [hα] at e
  set Gm : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f)) :=
    ((g : GL (Fin 6) (GaloisField p (2 * f))) : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f)))
    with hGm
  set Gi : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f)) :=
    ((g⁻¹ : GL (Fin 6) (GaloisField p (2 * f))) :
      Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) with hGi
  have hGiG : Gi * Gm = 1 := by rw [hGi, hGm, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [hxy] at e
  simp only [map_mul, hSS] at e
  set yy : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f)) :=
    ((y : GL (Fin 6) (GaloisField p (2 * f))) : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f)))
    with hyy
  have hN : (σU).mapMatrix Gi * (σU).mapMatrix Gm = 1 := by
    rw [← map_mul, hGiG, map_one]
  have hM : Gm * (σU).mapMatrix Gm * yy * ((σU).mapMatrix Gi * Gi) = yy := by
    simpa only [Matrix.mul_assoc] using e
  have hNM : ((σU).mapMatrix Gi * Gi) * (Gm * (σU).mapMatrix Gm) = 1 := by
    calc _ = (σU).mapMatrix Gi * (Gi * Gm) * (σU).mapMatrix Gm := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hGiG, Matrix.mul_one, hN]
  calc Gm * (σU).mapMatrix Gm * yy
      = (Gm * (σU).mapMatrix Gm * yy) *
          (((σU).mapMatrix Gi * Gi) * (Gm * (σU).mapMatrix Gm)) := by
        rw [hNM, Matrix.mul_one]
    _ = (Gm * (σU).mapMatrix Gm * yy * ((σU).mapMatrix Gi * Gi)) *
          (Gm * (σU).mapMatrix Gm) := by
        simp only [Matrix.mul_assoc]
    _ = yy * (Gm * (σU).mapMatrix Gm) := by rw [hM]

end Bar

section Mu

variable {K : Type*} [Field K] {n : ℕ}

theorem mu_eq_one_or_neg_one (σ : K ≃+* K) {Gm : Matrix (Fin n) (Fin n) K} {μ : K}
    (hiso : conjTr σ Gm * Gm = 1) (hμ : Gm * σ.mapMatrix Gm = μ • (1 : Matrix (Fin n) (Fin n) K))
    [NeZero n] : μ = 1 ∨ μ = -1 := by
  set S : Matrix (Fin n) (Fin n) K := σ.mapMatrix Gm with hS
  have hT : conjTr σ Gm = Sᵀ := rfl
  rw [hT] at hiso
  have h1 : S = μ • Sᵀ := by
    calc S = (Sᵀ * Gm) * S := by rw [hiso, Matrix.one_mul]
      _ = Sᵀ * (Gm * S) := by rw [Matrix.mul_assoc]
      _ = μ • Sᵀ := by rw [hμ, Matrix.mul_smul, Matrix.mul_one]
  have h2 : Sᵀ = μ • S := by
    have := congrArg Matrix.transpose h1
    rwa [Matrix.transpose_smul, Matrix.transpose_transpose] at this
  have h3 : (μ ^ 2 - 1) • S = 0 := by
    have : S = (μ * μ) • S := by
      calc S = μ • Sᵀ := h1
        _ = μ • (μ • S) := by rw [h2]
        _ = (μ * μ) • S := by rw [smul_smul]
    rw [sub_smul, sq, ← this, one_smul, sub_self]
  have hS0 : S ≠ 0 := by
    intro h0
    rw [h0, Matrix.transpose_zero, Matrix.zero_mul] at hiso
    exact zero_ne_one hiso
  have : μ ^ 2 - 1 = 0 := (smul_eq_zero.mp h3).resolve_right hS0
  have h4 : (μ - 1) * (μ + 1) = 0 := by linear_combination this
  rcases mul_eq_zero.mp h4 with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (eq_neg_of_add_eq_zero_left h)

end Mu

section Node

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

omit [Finite G] in
theorem g_commutes_te6Inv (c : UCtx p f 5 Ω K z) (nd : UNodes c)
    {Θ : Su (GaloisField p (2 * f)) p f 6 →* G} (hΘ : TE6Chart c nd Θ) {N : Subgroup G}
    (hN : N ∈ centralizingMembers Ω {z * nd.w 0}) {v : G} (hv : IsClassicalMember p f N v)
    (hNK : ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W K N)
    {g : GL (Fin 6) (GaloisField p (2 * f))}
    {α : Su (GaloisField p (2 * f)) p f 6 →* Su (GaloisField p (2 * f)) p f 6}
    (φ : GaloisField p (2 * f) ≃+* GaloisField p (2 * f))
    (hα : ∀ x, Θ (α x) = v * Θ x * v⁻¹)
    (hmat : ∀ x : Su (GaloisField p (2 * f)) p f 6,
      ((α x : GL (Fin 6) (GaloisField p (2 * f))) :
        Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) =
        (g : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) *
          φ.mapMatrix ((x : GL (Fin 6) (GaloisField p (2 * f))) :
            Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) *
          ((g⁻¹ : GL (Fin 6) (GaloisField p (2 * f))) :
            Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f)))) :
    (g : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) * suMat (te6Inv p f) =
      suMat (te6Inv p f) * (g : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) := by
  classical
  have hK := c.card_eq
  have hvz : v * z * v⁻¹ = z := partner_involution_commutes c.hp2 c.hz hv hNK
  have hw0 : Θ (te6Inv p f) = nd.w 0 := map_te6Inv_eq hΘ
  have hvw : v * nd.w 0 * v⁻¹ = nd.w 0 := by
    have h1 : v * (z * nd.w 0) = (z * nd.w 0) * v :=
      Subgroup.mem_centralizer_singleton_iff.mp (hN.2 hv.mem)
    have h2 : v * z = z * v := by
      have := hvz
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this
    have h3 : z * (v * nd.w 0) = z * (nd.w 0 * v) := by
      calc z * (v * nd.w 0) = (z * v) * nd.w 0 := by rw [mul_assoc]
        _ = (v * z) * nd.w 0 := by rw [h2]
        _ = v * (z * nd.w 0) := by rw [mul_assoc]
        _ = (z * nd.w 0) * v := h1
        _ = z * (nd.w 0 * v) := by rw [mul_assoc]
    rw [mul_left_cancel h3, mul_inv_cancel_right]
  have hfixw : (MulAut.conj v) (Θ (te6Inv p f)) = Θ (te6Inv p f) := by
    rw [hw0]
    exact hvw
  obtain ⟨u, hu⟩ := lift_matrix_of_fixed (n := 6) hK (by norm_num : 3 ≤ 6) hΘ.ker_le
    (σ := MulAut.conj v) (α := α) (fun x => hα x) (x := te6Inv p f) hfixw
  set Gm : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f)) :=
    ((g : GL (Fin 6) (GaloisField p (2 * f))) : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f)))
    with hGm
  set Gi : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f)) :=
    ((g⁻¹ : GL (Fin 6) (GaloisField p (2 * f))) :
      Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) with hGi
  set W : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f)) := suMat (te6Inv p f) with hWdef
  have hGiG : Gi * Gm = 1 := by rw [hGi, hGm, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h1 : Gm * W * Gi = (u : GaloisField p (2 * f)) • W := by
    have := (hmat (te6Inv p f)).symm.trans hu
    have e : φ.mapMatrix ((((te6Inv p f : Su (GaloisField p (2 * f)) p f 6) :
        GL (Fin 6) (GaloisField p (2 * f))) : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f)))) =
        W := mapMatrix_suMat_te6Inv φ
    rw [e] at this
    exact this
  have htr : Matrix.trace (Gm * W * Gi) = Matrix.trace W := by
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, hGiG, Matrix.mul_one]
  have hu1 : (u : GaloisField p (2 * f)) = 1 := by
    rw [h1, Matrix.trace_smul, trace_te6Inv, smul_eq_mul] at htr
    have h2 : (2 : GaloisField p (2 * f)) ≠ 0 := c.h2
    have h3 : ((u : GaloisField p (2 * f)) - 1) * 2 = 0 := by linear_combination htr
    exact sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_right h2)
  rw [hu1, one_smul] at h1
  calc Gm * W = Gm * W * (Gi * Gm) := by rw [hGiG, Matrix.mul_one]
    _ = (Gm * W * Gi) * Gm := by simp only [Matrix.mul_assoc]
    _ = W * Gm := by rw [h1]

end Node

section RealMatrix

variable {K : Type*} [Field K] {σ : K ≃+* K} {m : ℕ}

@[expose] def realStrOfMatrix (hσ : ∀ c, σ (σ c) = c) (g : Matrix (Fin m) (Fin m) K)
    (hg1 : g * σ.mapMatrix g = 1) (hgu : conjTr σ g * g = 1) : RealStr σ m where
  τ u := g *ᵥ (fun i => σ (u i))
  map_add u w := by
    rw [← Matrix.mulVec_add]
    congr 1
    funext i
    simp
  map_smul c u := by
    rw [← Matrix.mulVec_smul]
    congr 1
    funext i
    simp
  invol u := by
    have h : (fun i => σ ((g *ᵥ fun j => σ (u j)) i)) = (σ.mapMatrix g) *ᵥ u := by
      funext i
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, hσ]
      rfl
    rw [h, Matrix.mulVec_mulVec, hg1, Matrix.one_mulVec]
  herm_τ u w := by
    rw [herm_mulVec, hgu, Matrix.one_mulVec]
    simp only [herm_def, map_sum, map_mul, hσ]

end RealMatrix

end CFSG.ClassicalInvolution.RouteD.NonClassical
