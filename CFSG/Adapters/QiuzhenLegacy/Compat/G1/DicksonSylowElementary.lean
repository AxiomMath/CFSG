module

public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonSylow
public import Mathlib.Algebra.CharP.CharAndCard
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian

public section

namespace CFSG.Glauberman.Dickson

open BenderSuzuki.MatrixGroups

universe u

theorem h826_sylow_elementary
    {F : Type u} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f) (H : Subgroup (PSL2MatrixGroup F))
    (P : Sylow p H) :
    IsElementaryAbelian p P := by
  classical
  let : Fintype F := Fintype.ofFinite F
  let : CharP F p :=
    charP_of_card_eq_prime_pow (by simpa using hFcard)
  obtain ⟨Q, hQcomap⟩ := P.exists_comap_subtype_eq
  have hPmemQ (x : P) :
      (((x : P) : H) : PSL2MatrixGroup F) ∈ (Q : Subgroup _) := by
    have hx :
        (x : H) ∈ (Q : Subgroup (PSL2MatrixGroup F)).comap H.subtype := by
      rw [hQcomap]
      exact x.property
    exact hx
  have hFieldElementary : IsElementaryAbelian p (Multiplicative F) := by
    refine
      { toIsMulCommutative :=
          { is_comm := ⟨fun x y => mul_comm x y⟩ }
        exponent_dvd_p := ?_ }
    rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro x
    change Multiplicative.ofAdd x.toAdd ^ p = 1
    rw [← ofAdd_nsmul]
    simp
  obtain ⟨eQ⟩ := huppert_II_8_2_a_sylow_equiv_additive hFcard Q
  have hQElementary : IsElementaryAbelian p Q := by
    refine
      { toIsMulCommutative :=
          { is_comm := ⟨fun x y => ?_⟩ }
        exponent_dvd_p := ?_ }
    · apply eQ.symm.injective
      simpa using
        hFieldElementary.toIsMulCommutative.is_comm.comm
          (eQ.symm x) (eQ.symm y)
    · rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
      intro x
      apply eQ.symm.injective
      have hx : (eQ.symm x) ^ p = 1 :=
        Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          hFieldElementary.exponent_dvd_p (eQ.symm x)
      simpa using hx
  refine
    { toIsMulCommutative :=
        { is_comm := ⟨fun x y => ?_⟩ }
      exponent_dvd_p := ?_ }
  · apply Subtype.ext
    apply Subtype.ext
    let xQ : Q := ⟨((x : H) : PSL2MatrixGroup F), hPmemQ x⟩
    let yQ : Q := ⟨((y : H) : PSL2MatrixGroup F), hPmemQ y⟩
    have hxy := congrArg Subtype.val
      (hQElementary.toIsMulCommutative.is_comm.comm xQ yQ)
    simpa [xQ, yQ] using hxy
  · rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro x
    apply Subtype.ext
    apply Subtype.ext
    let xQ : Q := ⟨((x : H) : PSL2MatrixGroup F), hPmemQ x⟩
    have hxpow : xQ ^ p = 1 :=
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        hQElementary.exponent_dvd_p xQ
    simpa [xQ] using congrArg Subtype.val hxpow

end CFSG.Glauberman.Dickson
