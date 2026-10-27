module

public import CFSG.ClassicalInvolution.Q3.TL3T44
public import CFSG.ClassicalInvolution.Q3.TL3T36

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf19

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.TC.Thin.Amalg
  CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

theorem exists_lift_pow_five {H W : Type*} [Group H] [Group W] (ψ : H →* W)
    (hk : IsPGroup 2 ψ.ker) (x : H) (hx : ψ x ^ 5 = 1) : ∃ t : H, ψ t = ψ x ∧ t ^ 5 = 1 := by
  have h5 : x ^ 5 ∈ ψ.ker := by rw [MonoidHom.mem_ker, map_pow, hx]
  obtain ⟨a, ha⟩ := hk ⟨x ^ 5, h5⟩
  have ha' : x ^ (5 * 2 ^ a) = 1 := by
    have := congrArg Subtype.val ha
    rw [Subgroup.coe_pow, Subgroup.coe_one] at this
    rw [pow_mul]
    exact this
  have h16 : 16 ^ a % 5 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  refine ⟨x ^ (16 ^ a), ?_, ?_⟩
  · rw [map_pow, pow_eq_pow_mod _ hx, h16, pow_one]
  · rw [← pow_mul, show 16 ^ a * 5 = (5 * 2 ^ a) * 8 ^ a by
      rw [show (16 : ℕ) = 2 * 8 by norm_num, mul_pow]; ring, pow_mul, ha', one_pow]

theorem fin5_facts :
    (finRotate 5) ^ 5 = 1 ∧ Equiv.Perm.sign (finRotate 5) = 1 ∧
      Equiv.Perm.sign (Equiv.swap (0 : Fin 5) 1 * Equiv.swap 0 2) = 1 ∧
      finRotate 5 * (Equiv.swap (0 : Fin 5) 1 * Equiv.swap 0 2) ≠
        (Equiv.swap (0 : Fin 5) 1 * Equiv.swap 0 2) * finRotate 5 := by
  decide

variable {G : Type} [Group G] {P : Set (Subgroup G)} {n : ℕ}

theorem exists_pow_five_not_comm (I : AEIdent P n) (hn : 5 ≤ n) (hk : IsPGroup 2 I.φ.ker) :
    ∃ x : ↥(pSpan P), x ^ 5 = 1 ∧ ∃ w : ↥(pSpan P), x * w ≠ w * x := by
  obtain ⟨h1, h2, h3, h4⟩ := fin5_facts
  set c : Fin 5 ↪ Fin n := Fin.castLEEmb hn with hc
  set σ := extPerm c (finRotate 5) with hσ
  set τ := extPerm c (Equiv.swap (0 : Fin 5) 1 * Equiv.swap 0 2) with hτ
  have hσA : σ ∈ alternatingGroup (Fin n) := by
    rw [Equiv.Perm.mem_alternatingGroup, hσ, sign_extPerm, h2]
  have hτA : τ ∈ alternatingGroup (Fin n) := by
    rw [Equiv.Perm.mem_alternatingGroup, hτ, sign_extPerm, h3]
  have hrange : ∀ {ρ : Equiv.Perm (Fin n)}, ρ ∈ alternatingGroup (Fin n) →
      ∃ x : ↥(pSpan P), I.φ x = mkQ n (ofPerm ρ) := by
    intro ρ hρ
    have : mkQ n (ofPerm ρ) ∈ I.φ.range := by
      rw [I.range_eq]
      exact mem_aeModel_ofPerm hρ
    exact this
  obtain ⟨x₀, hx₀⟩ := hrange hσA
  obtain ⟨w, hw⟩ := hrange hτA
  have hx5 : I.φ x₀ ^ 5 = 1 := by
    rw [hx₀, ← map_pow, ofPerm_pow, hσ, ← map_pow, h1, map_one, ofPerm_one, map_one]
  obtain ⟨x, hx, hx1⟩ := exists_lift_pow_five I.φ hk x₀ hx5
  refine ⟨x, hx1, w, fun hxw => h4 (extPerm_injective c ?_)⟩
  have e := congrArg (fun y => permQ n (I.φ y)) hxw
  simp only [map_mul, hx, hx₀, hw, permQ_mkQ] at e
  have hστ : σ * τ = τ * σ := e
  calc extPerm c (finRotate 5 * (Equiv.swap (0 : Fin 5) 1 * Equiv.swap 0 2)) = σ * τ :=
        map_mul _ _ _
    _ = τ * σ := hστ
    _ = extPerm c ((Equiv.swap (0 : Fin 5) 1 * Equiv.swap 0 2) * finRotate 5) :=
        (map_mul _ _ _).symm

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf19
