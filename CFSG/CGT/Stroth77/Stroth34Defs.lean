module

public import CFSG.CGT.Stroth77.WeakType

public section

namespace CFSG.CGT.Stroth77

variable {G : Type*} [Group G] {B : Subgroup G} {τ : StrothTypeIndex}

structure StrothExt (dD : StrothWeakTypeData B τ) (e ic ia ib s xuv xt : G) : Prop where
  c_conj : e⁻¹ * (dD.c : G) * e = ic
  a_conj : e⁻¹ * (dD.a : G) * e = ia
  b_conj : e⁻¹ * (dD.b : G) * e = ib
  e_sq : e * e = s
  uv_conj : e⁻¹ * dD.uv * e = xuv * dD.uv
  t_conj : e⁻¹ * dD.t * e = xt * dD.t
  u_conj : e⁻¹ * dD.u * e = dD.u

variable (dD : StrothWeakTypeData B τ)

abbrev Rel34i (e : G) (N : ℕ) : Prop :=
  StrothExt dD e (dD.c : G) ((dD.a : G) * (dD.a : G) ^ N) ((dD.b : G) * (dD.b : G) ^ N)
    (dD.c : G)⁻¹ (((dD.c : G) * dD.a * dD.b) ^ 2) ((dD.a : G) ^ 2)⁻¹

abbrev Rel34inv (e : G) (j : ℕ) (s : G) (p : ℕ) : Prop :=
  StrothExt dD e (dD.c : G)⁻¹ ((dD.a : G)⁻¹ * (dD.a : G) ^ j) ((dD.b : G)⁻¹ * (dD.b : G) ^ j) s
    (((dD.c : G) * dD.a * dD.b) ^ p) ((dD.a : G) ^ p)⁻¹

abbrev Rel34x (f : G) (N M p : ℕ) : Prop :=
  StrothExt dD f (dD.c : G) ((dD.a : G) * (dD.a : G) ^ N) ((dD.b : G) * (dD.b : G) ^ N) (f * f)
    (((dD.c : G) * dD.a * dD.b) ^ p) ((dD.a : G) ^ p)⁻¹ ∧
    f * f * (f * f) = ((dD.c : G) ^ p)⁻¹ * (dD.c : G) ^ M

end CFSG.CGT.Stroth77
