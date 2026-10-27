module

public import CFSG.CGT.PushingUpLit.CGT6.EmbModDefs
public import CFSG.LieType.Steinberg.CentralExt.SL2CentrallyClosed

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG.LieType.Steinberg.CentralExt.SL2Closed

theorem schurMultL2Two_holds :
    SchurMultL2Two := by
  intro n hn E _ _ hE Z _ hZc _ ⟨e⟩
  have hk : 5 ≤ Nat.card (GaloisField 2 n) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [GaloisField.card 2 n (by omega)]
    calc 5 ≤ 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hk9 : Nat.card (GaloisField 2 n) ≠ 9 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [GaloisField.card 2 n (by omega)]
    intro h
    have h2 : 2 ^ n % 2 = 1 := by rw [h]
    have h3 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
    omega
  let π : E →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n) :=
    e.toMonoidHom.comp (QuotientGroup.mk' Z)
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective Z)
  have hker : π.ker = Z := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff e e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  obtain ⟨σ, hσ⟩ := sl2_exists_section_of_central hk hk9 hπ (hker ▸ hZc)
  have := ker_eq_bot_of_section (U := E) π (hker ▸ hZc) σ hσ
  rwa [hker] at this

end CFSG.CGT.PushingUpLit.CGT6
