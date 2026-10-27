module

public import CFSG.LieType.ChevTwo.OppCl.ToolkitBase
public import CFSG.LieType.ChevTwo.Defs

public section

namespace CFSG.LieType.ChevTwo.OppCl.TK

open CFSG.Open CFSG.LieType.BorelTits

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V] {H : Type} [Group H]

theorem commR_of_fixed (Z : Subgroup H) [Z.Normal] (hZo : Nat.Coprime (Nat.card Z) 2)
    {ρ : H →* Module.End F V} (hρ : Function.Injective ρ) {Q : Subgroup H} (hQ : IsPGroup 2 Q)
    {R : Subgroup (MulAut (H ⧸ Z))} {Rh : Subgroup (Equiv.Perm V)}
    (hind : ∀ r ∈ Rh, ∃ α ∈ R, Induces (QuotientGroup.mk' Z) ρ r α)
    (hN : ∀ r ∈ Rh, NormQ ρ r Q) {x : H} (hx : x ∈ Q)
    (hfix : QuotientGroup.mk' Z x ∈ autCentralizer R) : CommR ρ Rh x := by
  intro r hr
  obtain ⟨α, hαR, hind_r⟩ := hind r hr
  obtain ⟨hI, -⟩ := hind_r
  obtain ⟨h', hh', hαh'⟩ := hI x
  have hfix' : ∀ β ∈ R, β (QuotientGroup.mk' Z x) = QuotientGroup.mk' Z x := hfix
  have hpi : QuotientGroup.mk' Z x = QuotientGroup.mk' Z h' := (hfix' α hαR).symm.trans hαh'
  obtain ⟨z, hzZ, hxz⟩ := (QuotientGroup.mk'_eq_mk' Z).mp hpi
  obtain ⟨x', hx'Q, hx'⟩ := hN r hr x hx
  have hEq : h' = x' := eq_of_forall_apply_perm hρ r fun v => (hh' v).symm.trans (hx' v)
  have hh'Q : h' ∈ Q := by
    rw [hEq]
    exact hx'Q
  have hzQ : z ∈ Q := by
    have h1 := Q.mul_mem (Q.inv_mem hx) hh'Q
    rwa [← hxz, inv_mul_cancel_left] at h1
  obtain ⟨k, hk⟩ := hQ ⟨z, hzQ⟩
  have hzk : z ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hcop : Nat.Coprime (orderOf z) (2 ^ k) :=
    Nat.Coprime.pow_right k (Nat.Coprime.coprime_dvd_left (Z.orderOf_dvd_natCard hzZ) hZo)
  have hord : orderOf z = 1 := Nat.Coprime.eq_one_of_dvd hcop (orderOf_dvd_of_pow_eq_one hzk)
  have hz1 : z = 1 := orderOf_eq_one_iff.mp hord
  have hh'x : h' = x := by
    rw [← hxz, hz1, mul_one]
  intro v
  have hv := hh' v
  rw [hh'x] at hv
  exact hv

theorem fixed_of_commR (Z : Subgroup H) [Z.Normal] {ρ : H →* Module.End F V}
    (hρ : Function.Injective ρ) {R : Subgroup (MulAut (H ⧸ Z))} {Rh : Subgroup (Equiv.Perm V)}
    (hind : ∀ α ∈ R, ∃ r ∈ Rh, Induces (QuotientGroup.mk' Z) ρ r α) {y : H}
    (hy : CommR ρ Rh y) : QuotientGroup.mk' Z y ∈ autCentralizer R := by
  have key : ∀ α ∈ R, α (QuotientGroup.mk' Z y) = QuotientGroup.mk' Z y := by
    intro α hαR
    obtain ⟨r, hr, hind_r⟩ := hind α hαR
    obtain ⟨hI, -⟩ := hind_r
    obtain ⟨h', hh', hαh'⟩ := hI y
    have hEq : y = h' := eq_of_forall_apply_perm hρ r fun v => (hy r hr v).symm.trans (hh' v)
    rw [hαh', hEq]
  exact key

end CFSG.LieType.ChevTwo.OppCl.TK
