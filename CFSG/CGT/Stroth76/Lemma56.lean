module

public import CFSG.CGT.Stroth76.Lemma7Two

public section

namespace CFSG.CGT.Stroth76

open CFSG.CGT.Stroth77.Arch76

variable {G : Type*} [Group G] [Finite G] (K : Config G)

theorem arch76Lemma5
    (hfusE : ∀ e ∈ Subgroup.closure {K.x ^ 2, K.y ^ 2, K.uv, K.t}, e ≠ 1 →
      IsConj e ((K.x * K.y) ^ 2))
    (hwu : IsConj (K.w * K.u) (K.x * K.y * K.uv)) {g : G} {q : Tc} (hq : q ∈ xyuvClass)
    (hg : g⁻¹ * K.uv * g = tElt K q) : IsConj (K.w * K.u) ((K.x * K.y) ^ 2) :=
  hwu.trans (isConj_xyuv_sq K hfusE hq (isConj_of_conj g hg))

theorem false_of_lemma2_iii
    (hfusE : ∀ e ∈ Subgroup.closure {K.x ^ 2, K.y ^ 2, K.uv, K.t}, e ≠ 1 →
      IsConj e ((K.x * K.y) ^ 2))
    (huw : IsConj K.u K.w) (hwu : IsConj (K.w * K.u) (K.x * K.y * K.uv))
    (hAnn1 : ¬ IsConj K.w ((K.x * K.y) ^ 2)) {s : G}
    (hsuv : s⁻¹ * K.uv * s = K.x⁻¹ * K.y * K.uv) (hsu : s⁻¹ * K.u * s = K.w * K.u) : False := by
  have hq : (((0, 3, 1), (1, 0, 0)) : Tc) ∈ xyuvClass := by decide
  have hel : tElt K ((0, 3, 1), (1, 0, 0)) = K.x⁻¹ * K.y * K.uv := by
    rw [show ((0, 3, 1), (1, 0, 0)) = tmul ((0, 3, 1), 0) (0, (1, 0, 0)) from rfl, tElt_mul,
      tElt_ev, tElt_gen_uv]
    simp [Config.ev, K.x_inv_eq, show (1 : ZMod 4).val = 1 from rfl,
      show (3 : ZMod 4).val = 3 from rfl]
  have h5 := arch76Lemma5 K hfusE hwu hq (hsuv.trans hel.symm)
  exact hAnn1 ((huw.symm.trans (isConj_of_conj s hsu)).trans h5)

end CFSG.CGT.Stroth76
