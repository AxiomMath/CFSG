module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.GroupTheory

theorem not_dvd_card_range_of_conj_action {H : Type*} [Group H] [Finite H]
    {E : Subgroup H} {p : ℕ} [Fact p.Prime] (hEp : IsPGroup p E)
    (hAb : ∀ P : Subgroup H, IsPGroup p P → IsMulCommutative P)
    (f : H →* MulAut ↥E)
    (hf : ∀ (h : H) (x : ↥E), ((f h x : ↥E) : H) = h * (x : H) * h⁻¹) :
    ¬ p ∣ Nat.card f.range := by
  classical
  obtain ⟨P, hEP⟩ := hEp.exists_le_sylow
  have hPab : IsMulCommutative ↥(P : Subgroup H) := hAb P P.isPGroup'
  have hPker : (P : Subgroup H) ≤ f.ker := by
    intro q hq
    rw [MonoidHom.mem_ker]
    ext x
    rw [MulAut.one_apply, hf q x]
    have hcomm : q * (x : H) = (x : H) * q := by
      simpa using congrArg (fun z : ↥P => (z : H))
        (hPab.is_comm.comm (⟨q, hq⟩ : ↥P) ⟨x, hEP x.2⟩)
    rw [hcomm]
    group
  let pcard := Nat.card (P : Subgroup H)
  let r := Nat.card f.range
  let k := Nat.card f.ker
  have hkr : k * r = Nat.card H := Subgroup.card_ker_mul_card_range f
  have hpi : pcard * (P : Subgroup H).index = Nat.card H :=
    Subgroup.card_mul_index (H := (P : Subgroup H))
  have hpk : pcard ∣ k := Subgroup.card_dvd_of_le hPker
  obtain ⟨d, hd⟩ := hpk
  have hri : r ∣ (P : Subgroup H).index := by
    refine ⟨d, ?_⟩
    have hEq : d * r = (P : Subgroup H).index := by
      have h := hkr
      rw [hd, ← hpi, mul_assoc] at h
      exact Nat.mul_left_cancel (Nat.card_pos (α := ↥(P : Subgroup H))) h
    rw [← hEq, Nat.mul_comm d r]
  have hPndvd : ¬ p ∣ (P : Subgroup H).index := P.not_dvd_index
  intro hp
  exact hPndvd (hp.trans hri)

end CFSG.GroupTheory

end
