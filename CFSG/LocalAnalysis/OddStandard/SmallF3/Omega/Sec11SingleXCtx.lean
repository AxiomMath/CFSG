module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L115dF
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10K5Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L1110Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

structure S11sCtx (t z : G) (K1 K2 T R : Subgroup G)
    (ρ : ↥R →* MulAut ↥(K1 ⊔ K2)) (a x : G) : Prop where
  rho : Sec11dRho t z K1 K2 R ρ
  set : Sec11dSet t z K1 K2 R
  QKD : secQ K1 K2 ≤ secKD (secD K1 K2 R)
  RQ : R ≤ normalizer (secQ K1 K2 : Set G)
  pair : K5.SL23Pair ↥(K1 ⊔ K2) (K1.subgroupOf (K1 ⊔ K2)) (K2.subgroupOf (K1 ⊔ K2))
  q8 : Sec11Q8Pair z (twoCoreIn K1) (twoCoreIn K2)
  Q_eq : secQ K1 K2 = twoCoreIn K1 ⊔ twoCoreIn K2
  Q1_pow : ∀ g ∈ K1, g ^ 4 = 1 → g ∈ twoCoreIn K1
  Q2_pow : ∀ g ∈ K2, g ^ 4 = 1 → g ∈ twoCoreIn K2
  inf : ∀ g ∈ K1, g ∈ K2 → g ∈ zpowers z
  t_D : t ∈ secD K1 K2 R
  z_D : z ∈ secD K1 K2 R
  t_sq : t * t = 1
  R_H : R ≤ centralizer ({z} : Set G)
  T_R : T ≤ R
  Q_T : secQ K1 K2 ≤ T
  T_N : T ≤ normalizer (secK0 t z : Set G)
  D2 : IsPGroup 2 ↥(secD K1 K2 R)
  a_T : a ∈ T
  a_sq : a * a = 1
  a_swap : ∀ g ∈ K1, a * g * a⁻¹ ∈ K2
  a_swap' : ∀ g ∈ K2, a * g * a⁻¹ ∈ K1
  a_CTQ : ∀ g ∈ secCTQ K1 K2 T, a * g = g * a
  x_T : x ∈ T
  x_out1 : IsOuterOn x (K1 ⊔ oddCoreIn (secK0 t z)) (oddCoreIn (secK0 t z))
  x_out2 : IsOuterOn x (K2 ⊔ oddCoreIn (secK0 t z)) (oddCoreIn (secK0 t z))
  gen : T = closure ((secCTQ K1 K2 T : Set G) ∪ (secQ K1 K2 : Set G) ∪ ({a, x} : Set G))
  dih : ∀ g ∈ R, g ∉ T ⊔ secD K1 K2 R →
    secD K1 K2 R = zpowers t ⊔ zpowers (g * t * g⁻¹) ∧ ∃ w ∈ secCTQ K1 K2 T, orderOf w = 4
  star : ∀ h ∈ centralizer ({z} : Set G), ∀ h' ∈ centralizer ({z} : Set G),
    (h'⁻¹ * t * h') * (h⁻¹ * t * h) = (h⁻¹ * t * h) * (h'⁻¹ * t * h') →
      h'⁻¹ * t * h' = h⁻¹ * t * h ∨ h'⁻¹ * t * h' = h⁻¹ * t * h * z

end CFSG.OddStandard.SmallF3.Omega
