module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2BigDefs
public import CFSG.CGT.PushingUpLit.SolKNA.R4.QuatAlg
public import CFSG.CGT.PushingUpLit.SolKNA.R4.QuatAut

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.QSub

open CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big (quatInvolution)

variable {G : Type} [Group G] {Q : Subgroup G} {r : ℕ}
  (e : ↥Q ≃* QuaternionGroup (2 ^ (r - 2)))

@[expose] def zeta : G :=
  ((e.symm (QuaternionGroup.a ((2 ^ (r - 3) : ℕ) : ZMod (2 * 2 ^ (r - 2)))) : ↥Q) : G)

theorem zeta_mem : zeta e ∈ Q := (e.symm _).2

theorem zeta_mem_xc : zeta e ∈ xc e :=
  (mem_xc_iff e).mpr ⟨((2 ^ (r - 3) : ℕ) : ZMod (2 * 2 ^ (r - 2))), rfl⟩

theorem zeta_mul_self (hr : 4 ≤ r) : zeta e * zeta e = quatInvolution r e := by
  unfold zeta quatInvolution
  rw [Alg.coe_symm_mul e, QuaternionGroup.a_mul_a, Alg.coe_symm_inj e]
  congr 1
  have h := QAut.half_add_half (m := r - 2) (by omega : 1 ≤ r - 2)
  rwa [show r - 2 - 1 = r - 3 by omega] at h

theorem involution_cases (hr : 4 ≤ r) {g : G} (hg : ∀ q ∈ Q, g * q * g⁻¹ ∈ Q)
    (hgx : ∀ x ∈ xc e, g * x = x * g) (hg2 : g * g = 1) :
    (∀ q ∈ Q, g * q * g⁻¹ = q) ∨ ∀ q ∈ Q, g * q * g⁻¹ = zeta e * q * (zeta e)⁻¹ := by
  have hm : 2 ≤ r - 2 := by omega
  haveI : NeZero (2 ^ (r - 2)) := ⟨by positivity⟩
  obtain ⟨α, β, -, ha, hxa⟩ := QAut.aut_data (m := r - 2) hm (QAut.conjHom e hg)
    (QAut.conjHom_injective e hg)
  have hα1 : α = 1 := by
    have hmem : ((e.symm (QuaternionGroup.a 1) : ↥Q) : G) ∈ xc e :=
      (mem_xc_iff e).mpr ⟨1, rfl⟩
    have hcomm : g * ((e.symm (QuaternionGroup.a 1) : ↥Q) : G) =
        ((e.symm (QuaternionGroup.a 1) : ↥Q) : G) * g := hgx _ hmem
    have hconj := QAut.conj_eq e hg (QuaternionGroup.a 1)
    rw [ha 1] at hconj
    have hx1 : g * ((e.symm (QuaternionGroup.a 1) : ↥Q) : G) * g⁻¹ =
        ((e.symm (QuaternionGroup.a 1) : ↥Q) : G) := by
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    have heq : ((e.symm (QuaternionGroup.a (α * 1)) : ↥Q) : G) =
        ((e.symm (QuaternionGroup.a 1) : ↥Q) : G) := by
      rw [← hconj, hx1]
    have h2 := (Alg.coe_symm_inj e).mp heq
    rw [mul_one] at h2
    exact QuaternionGroup.a.inj h2
  have hββ : β + β = 0 := by
    have h1 : QAut.conjHom e hg (QuaternionGroup.xa 0) = QuaternionGroup.xa β := by
      rw [hxa 0, mul_zero, add_zero]
    have h2 : QAut.conjHom e hg (QuaternionGroup.xa β) = QuaternionGroup.xa (β + β) := by
      rw [hxa β, hα1, one_mul]
    have hfix : QAut.conjHom e hg (QAut.conjHom e hg (QuaternionGroup.xa 0)) =
        QuaternionGroup.xa 0 := by
      apply (Alg.coe_symm_inj e).mp
      rw [← QAut.conj_comp e hg hg, hg2]
      group
    rw [h1, h2] at hfix
    exact QuaternionGroup.xa.inj hfix
  have h2β : 2 * β = 0 := by
    calc 2 * β = β + β := two_mul β
      _ = 0 := hββ
  rcases (Alg.two_mul_eq_zero_iff (n := 2 ^ (r - 2))).mp h2β with hβ0 | hβn
  ·
    left
    have hfix : ∀ x : QuaternionGroup (2 ^ (r - 2)), QAut.conjHom e hg x = x := by
      intro x
      rcases x with i | j
      · rw [ha i, hα1, one_mul]
      · rw [hxa j, hβ0, hα1, one_mul, zero_add]
    intro q hq
    obtain ⟨x, rfl⟩ := Alg.exists_coe_symm e hq
    rw [QAut.conj_eq e hg, hfix x]
  ·
    right
    have hk : ((2 ^ (r - 3) : ℕ) : ZMod (2 * 2 ^ (r - 2))) +
        ((2 ^ (r - 3) : ℕ) : ZMod (2 * 2 ^ (r - 2))) =
        ((2 ^ (r - 2) : ℕ) : ZMod (2 * 2 ^ (r - 2))) := by
      have h := QAut.half_add_half (m := r - 2) (by omega : 1 ≤ r - 2)
      rwa [show r - 2 - 1 = r - 3 by omega] at h
    have hfixn : ∀ x : QuaternionGroup (2 ^ (r - 2)),
        QAut.conjHom e hg x =
          QuaternionGroup.a ((2 ^ (r - 3) : ℕ) : ZMod (2 * 2 ^ (r - 2))) * x *
            (QuaternionGroup.a ((2 ^ (r - 3) : ℕ) : ZMod (2 * 2 ^ (r - 2))))⁻¹ := by
      intro x
      rcases x with i | j
      · rw [ha i, hα1, one_mul, Alg.inv_a, QuaternionGroup.a_mul_a, QuaternionGroup.a_mul_a]
        congr 1
        ring
      · rw [hxa j, hβn, hα1, one_mul, Alg.inv_a, QuaternionGroup.a_mul_xa,
          QuaternionGroup.xa_mul_a]
        congr 1
        linear_combination hk + (Alg.n_add_n (n := 2 ^ (r - 2)))
    have hzeta : ∀ x : QuaternionGroup (2 ^ (r - 2)),
        zeta e * ((e.symm x : ↥Q) : G) * (zeta e)⁻¹ =
          ((e.symm (QuaternionGroup.a ((2 ^ (r - 3) : ℕ) : ZMod (2 * 2 ^ (r - 2))) * x *
            (QuaternionGroup.a ((2 ^ (r - 3) : ℕ) : ZMod (2 * 2 ^ (r - 2))))⁻¹) : ↥Q) : G) := by
      intro x
      unfold zeta
      rw [Alg.coe_symm_inv e, Alg.coe_symm_mul e, Alg.coe_symm_mul e]
    intro q hq
    obtain ⟨x, rfl⟩ := Alg.exists_coe_symm e hq
    rw [QAut.conj_eq e hg, hfixn x, hzeta x]

end CFSG.CGT.PushingUpLit.SolKNA.R4.QSub
