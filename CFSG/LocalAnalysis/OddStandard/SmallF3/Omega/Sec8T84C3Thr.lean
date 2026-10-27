module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84C3Sec

public section

namespace CFSG.OddStandard.SmallF3.Omega

namespace C10

open Subgroup CFSG.GH74.GLS.Bg.TwoGroups.L218

theorem alt6_commutator_pow_four_ne_one :
    ∃ a b : alternatingGroup (Fin 6), (a * b * a⁻¹ * b⁻¹) ^ 4 ≠ 1 := by
  refine ⟨⟨Equiv.swap 3 4 * Equiv.swap 4 5, ?_⟩, ⟨Equiv.swap 1 3 * Equiv.swap 2 4, ?_⟩, ?_⟩
  · rw [Equiv.Perm.mem_alternatingGroup]
    decide
  · rw [Equiv.Perm.mem_alternatingGroup]
    decide
  · intro h
    have h' := congrArg Subtype.val h
    simp only [Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one] at h'
    revert h'
    decide +kernel

theorem false_of_order_seventeen {V : Type} [CommGroup V] [Finite V] (hsq : ∀ v : V, v * v = 1)
    (hcard : Nat.card V = 2 ^ 8) (ζ x : MulAut V) (hζ : ζ ^ 17 = 1)
    (hfix : ∀ v : V, ζ v = v → v = 1) (hx2 : x * x = 1) (hx1 : x ≠ 1)
    (hcomm : ζ * x = x * ζ) : False := by
  classical
  have hTmem : ∀ v, v ∈ fixE x ↔ x v = v := fun v => mem_fixE x v
  have hsq16 : 2 ^ 8 ≤ Nat.card (fixE x) ^ 2 := by
    have := card_le_fixE_sq hsq x hx2
    rwa [hcard] at this
  have hTinv : ∀ e, e ∈ fixE x → ζ e ∈ fixE x := by
    intro e he
    rw [hTmem] at he ⊢
    have h1 : x (ζ e) = ζ (x e) := by
      have := congrArg (fun m : MulAut V => m e) hcomm
      simpa [MulAut.mul_apply] using this.symm
    rw [h1, he]
  haveI : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  have hmod := card_fix_modEq ζ (fixE x) hTinv 17 1 (by simpa using hζ)
  have hone : Nat.card {d : fixE x // ζ d = d} = 1 := by
    haveI : Unique {d : fixE x // ζ d = d} :=
      { default := ⟨1, by simp⟩
        uniq := fun d => Subtype.ext (Subtype.ext (hfix _ d.2)) }
    exact Nat.card_unique
  rw [hone] at hmod
  have hdvd : Nat.card (fixE x) ∣ 2 ^ 8 := hcard ▸ Subgroup.card_subgroup_dvd_card (fixE x)
  obtain ⟨k, hk8, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  rw [hk] at hmod hsq16
  have hk8' : k = 8 := by
    interval_cases k <;> simp_all [Nat.ModEq]
  have hTtop : fixE x = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [hk, hk8', ← hcard]
  apply hx1
  ext v
  have : v ∈ fixE x := hTtop ▸ Subgroup.mem_top v
  simpa using (hTmem v).1 this

theorem false_of_order_three {V : Type} [CommGroup V] [Finite V] (hsq : ∀ v : V, v * v = 1)
    (hcard : Nat.card V = 2 ^ 8) (ζ x : MulAut V) (hζ : ζ ^ 3 = 1)
    (hfix : ∀ v : V, ζ v = v → v = 1) (hx2 : x * x = 1) (hx1 : x ≠ 1)
    (M N : Subgroup (MulAut V)) (hζM : ζ ∈ M) (hMζ : ∀ m ∈ M, m * ζ = ζ * m)
    (hMx : ∀ m ∈ M, m * x = x * m) (hNc : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a)
    (hq : QuotEquivTo M N (alternatingGroup (Fin 6))) : False := by
  classical
  have hcomm : ζ * x = x * ζ := hMx ζ hζM
  obtain ⟨T, R, hRT, hTmem, hRmem, hcardRT, hR416⟩ :=
    card_comm_sections hsq hcard ζ x hζ hfix hx2 hx1 hcomm
  have hxm : ∀ m ∈ M, ∀ v : V, x (m v) = m (x v) := fun m hm v => by
    have := congrArg (fun f : MulAut V => f v) (hMx m hm)
    simpa [MulAut.mul_apply] using this.symm
  have hTinv : ∀ m ∈ M, ∀ t ∈ T, m t ∈ T := fun m hm t ht => by
    rw [hTmem] at ht ⊢
    rw [hxm m hm, ht]
  have hRinv : ∀ m ∈ M, ∀ r ∈ R, m r ∈ R := fun m hm r hr => by
    obtain ⟨v, rfl⟩ := (hRmem r).1 hr
    refine (hRmem _).2 ⟨m v, ?_⟩
    rw [map_mul, map_inv, hxm m hm]
  have hbotinv : ∀ m ∈ M, ∀ r ∈ (⊥ : Subgroup V), m r ∈ (⊥ : Subgroup V) := fun m _ r hr => by
    rw [Subgroup.mem_bot] at hr ⊢
    rw [hr, map_one]
  have hsec1 := card_section (⊥ : Subgroup V) R bot_le
  rw [Subgroup.card_bot, mul_one] at hsec1
  have hS1 : Nat.card (↥R ⧸ (⊥ : Subgroup V).subgroupOf R) ≤ 16 := by
    rw [hsec1]
    rcases hR416 with h | h <;> omega
  have hsec2 := card_section R T hRT
  have hS2 : Nat.card (↥T ⧸ R.subgroupOf T) ≤ 16 := by
    rcases hR416 with h | h <;> rw [h] at hcardRT hsec2 <;> omega
  have hsec3 := card_section T ⊤ le_top
  have hS3 : Nat.card (↥(⊤ : Subgroup V) ⧸ T.subgroupOf ⊤) ≤ 16 := by
    have h3 : Nat.card (↥(⊤ : Subgroup V) ⧸ T.subgroupOf ⊤) = Nat.card R := by
      apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥T))
      rw [hsec3, Subgroup.card_top, hcard, hcardRT]
      norm_num
    rw [h3]
    rcases hR416 with h | h <;> omega
  have hA1 := sec_comm_trivial hsq ζ hζ hfix M N hζM hMζ hNc hq ⊥ R bot_le hRinv hbotinv hS1
  have hA2 := sec_comm_trivial hsq ζ hζ hfix M N hζM hMζ hNc hq R T hRT hTinv hRinv hS2
  have hA3 := sec_comm_trivial hsq ζ hζ hfix M N hζM hMζ hNc hq T ⊤ le_top
    (fun m _ t _ => Subgroup.mem_top _) hTinv hS3
  obtain ⟨φ, hφ, -⟩ := hq
  obtain ⟨a0, b0, hne⟩ := alt6_commutator_pow_four_ne_one
  obtain ⟨a, rfl⟩ := hφ a0
  obtain ⟨b, rfl⟩ := hφ b0
  apply hne
  have hc4 : ((a * b * a⁻¹ * b⁻¹ : ↥M) : MulAut V) ^ 4 = 1 := by
    refine pow_four_eq_one hsq R T _ ?_ ?_ ?_
    · intro r hr
      have := hA1 a b r hr
      rw [Subgroup.mem_bot, mul_inv_eq_one] at this
      exact this
    · intro t ht
      exact hA2 a b t ht
    · intro v
      exact hA3 a b v (Subgroup.mem_top v)
  have hc4' : (a * b * a⁻¹ * b⁻¹ : ↥M) ^ 4 = 1 := Subtype.ext (by simpa using hc4)
  calc (φ a * φ b * (φ a)⁻¹ * (φ b)⁻¹) ^ 4 = φ ((a * b * a⁻¹ * b⁻¹) ^ 4) := by
        simp only [map_pow, map_mul, map_inv]
    _ = 1 := by rw [hc4', map_one]

end C10

end CFSG.OddStandard.SmallF3.Omega
