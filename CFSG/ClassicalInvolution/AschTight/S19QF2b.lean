module

public import CFSG.ClassicalInvolution.AschTight.S1911P3f

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19Q

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G]

abbrev secY (K : Subgroup G) (a : G) : Subgroup ↥(Subgroup.centralizer ({a} : Set G)) :=
  S1911.conjGen (S1911.perfectCoreIn K a)

instance secY_normal (K : Subgroup G) (a : G) : (secY K a).Normal := S1911.conjGen_normal _

abbrev secE (K : Subgroup G) (a : G) : Type :=
  ↥(secY K a) ⧸ classicalInvolutionOddCore ↥(secY K a)

abbrev secFam (K : Subgroup G) (a : G) : Set (Subgroup (secE K a)) :=
  oddQuotientFamily (restrictFamily (S1911.conjFamily (S1911.perfectCoreIn K a))
    (omegaGen (S1911.conjFamily (S1911.perfectCoreIn K a))))

abbrev secK (K : Subgroup G) (a : G) : Subgroup (secE K a) :=
  S1911.secImg (secY K a) (S1911.perfectCoreIn K a)

theorem isPGroup_zpowers_iff_exists_pow {X : Type} [Group X] (x : X) :
    IsPGroup 2 (Subgroup.zpowers x) ↔ ∃ n : ℕ, x ^ (2 ^ n) = 1 := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h ⟨x, Subgroup.mem_zpowers x⟩
    exact ⟨n, congrArg Subtype.val hn⟩
  · rintro ⟨n, hn⟩
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hdvd : orderOf x ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])

theorem conj_injective_of_simple {X : Type} [Group X] [IsSimpleGroup X]
    (hnab : ∃ a b : X, a * b ≠ b * a) : Function.Injective (MulAut.conj : X →* MulAut X) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (MulAut.conj : X →* MulAut X).ker with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    have hb : MulAut.conj b = 1 := (MonoidHom.mem_ker).mp (h ▸ Subgroup.mem_top b)
    have := congrArg (fun φ : MulAut X => φ a) hb
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    apply hab
    calc a * b = b * a * b⁻¹ * b := by rw [this]
      _ = b * a := by group

variable [Finite G] {p f : ℕ} [Fact p.Prime] {K : Subgroup G} {z : G}
  {S : Sylow 2 G} {W : Subgroup G}

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19Q
