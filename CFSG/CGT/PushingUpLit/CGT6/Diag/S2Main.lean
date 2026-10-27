module

public import CFSG.CGT.PushingUpLit.CGT6.Diag.S2Delta
public import CFSG.CGT.PushingUpLit.CGT6.Diag.S2Transfer
public import CFSG.LieType.Steinberg.CentralExt.SL2CentrallyClosed

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG.CGT.PushingUpLit.CGT6.Diag.S2 CFSG.LieType.Steinberg.CentralExt.SL2Closed

theorem diagModS2_holds :
    DiagMod_s2 := by
  intro V _ _ _ K K' Y t h f hf ⟨θY⟩
  have hperf : commutator ↥K = ⊤ := h.quasi.1
  have : Group.IsPerfect ↥K := ⟨hperf⟩
  let π : ↥K →* Matrix.SpecialLinearGroup (Fin 2) (Fq f) :=
    θY.toMonoidHom.comp (deltaY h.toDiagPre)
  have hπs : Function.Surjective π := θY.surjective.comp (deltaY_surjective h.toDiagPre)
  have hπk : π.ker = Subgroup.center ↥K := by
    rw [← ker_deltaY_eq_center h.toDiagPre]
    ext x
    simp only [π, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    exact map_eq_one_iff θY θY.injective
  have hbot : π.ker = ⊥ := by
    rcases Nat.lt_or_ge f 3 with hf3 | hf3
    · obtain rfl : f = 2 := by omega
      refine ker_eq_bot_of_odd_central hperf π (hπk ▸ le_rfl) ?_ not_odd_prime_sq_dvd_sl2_four
      rw [hπk]
      exact h.oddZ
    · have hk : 5 ≤ Nat.card (Fq f) := by
        rw [GaloisField.card 2 f (by omega)]
        calc 5 ≤ 2 ^ 3 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf3
      have hk9 : Nat.card (Fq f) ≠ 9 := by
        rw [GaloisField.card 2 f (by omega)]
        intro h9
        have h2 : 2 ^ f % 2 = 1 := by rw [h9]
        have h3 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
        omega
      obtain ⟨σ, hσ⟩ := sl2_exists_section_of_central hk hk9 hπs (hπk ▸ le_rfl)
      exact ker_eq_bot_of_section π (hπk ▸ le_rfl) σ hσ
  refine ⟨⟨MulEquiv.ofBijective π ⟨?_, hπs⟩⟩, ?_⟩
  · rwa [← MonoidHom.ker_eq_bot_iff]
  · rw [eq_bot_iff]
    intro k hk
    have hkc : (⟨k, hk.1⟩ : ↥K) ∈ Subgroup.center ↥K :=
      Subgroup.mem_center_iff.mpr fun g => Subtype.ext (h.comm g g.2 k hk.2)
    rw [← hπk, hbot] at hkc
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val (Subgroup.mem_bot.mp hkc))

end CFSG.CGT.PushingUpLit.CGT6
