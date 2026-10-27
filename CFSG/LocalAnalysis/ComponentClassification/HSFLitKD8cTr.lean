module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8cMod
public import CFSG.Quasithin.Background.A1cTransferVariants
public import CFSG.RankThree.PartTwo.Sec8.TransferExtremal
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8cCharB

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace KD8c

open KD7 KD8ab Sec8

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : L2Data t L}
  {C : A.CaseKD} {S : KDBase A C} {T₁ : Subgroup X}

omit [Finite X] in
theorem commutator_eq_top' [IsSimpleGroup X] (hnonab : ∃ a b : X, a * b ≠ b * a) :
    commutator X = ⊤ := by
  rcases (Subgroup.commutator_normal (⊤ : Subgroup X) (⊤ : Subgroup X)).eq_bot_or_eq_top with
    h | h
  · obtain ⟨a, b, hab⟩ := hnonab
    exact (hab ((isMulCommutative_iff.mp ((commutator_eq_bot_iff X).mp h)) a b)).elim
  · exact h

theorem z2_cases : ∀ a : Multiplicative (ZMod 2), a = 1 ∨ a = Multiplicative.ofAdd 1 := by
  decide

theorem z2_comm : ∀ a b : Multiplicative (ZMod 2), a * b * a⁻¹ * b⁻¹ = 1 := by decide

theorem z2_sq : ∀ a : Multiplicative (ZMod 2), a * a = 1 := by decide

theorem z2_cube : (Multiplicative.ofAdd (1 : ZMod 2)) ^ 3 = Multiplicative.ofAdd 1 := by decide

namespace Conf

namespace T2

namespace Lift

variable {K : Conf S T₁} {T : K.T2} (W : T.Lift)

noncomputable abbrev Kχ (χ : Ext W.D' →* Multiplicative (ZMod 2)) : Subgroup X := χ.ker.map W.ψ

theorem mem_Kχ {χ : Ext W.D' →* Multiplicative (ZMod 2)} {x : Ext W.D'} :
    W.ψ x ∈ W.Kχ χ ↔ χ x = 1 := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    rw [← W.ψ_injective hyx]
    exact hy
  · exact fun h => ⟨x, h, rfl⟩

theorem Kχ_le (χ : Ext W.D' →* Multiplicative (ZMod 2)) : W.Kχ χ ≤ T.P := by
  rintro _ ⟨y, -, rfl⟩
  exact W.ψ_mem y

theorem comm_mem_Kχ (χ : Ext W.D' →* Multiplicative (ZMod 2)) {a b : X} (ha : a ∈ T.P)
    (hb : b ∈ T.P) : a * b * a⁻¹ * b⁻¹ ∈ W.Kχ χ := by
  obtain ⟨x, rfl⟩ := W.exists_ψ ha
  obtain ⟨y, rfl⟩ := W.exists_ψ hb
  rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, W.mem_Kχ, map_mul, map_mul,
    map_mul, map_inv, map_inv, z2_comm]

theorem conj_mem_Kχ (χ : Ext W.D' →* Multiplicative (ZMod 2)) {a b : X} (ha : a ∈ T.P)
    (hb : b ∈ W.Kχ χ) : a * b * a⁻¹ ∈ W.Kχ χ := by
  have := mul_mem (W.comm_mem_Kχ χ ha (W.Kχ_le χ hb)) hb
  rwa [inv_mul_cancel_right] at this

theorem false_of_A137 [IsSimpleGroup X] (hnonab : ∃ a b : X, a * b ≠ b * a)
    (χ : Ext W.D' →* Multiplicative (ZMod 2))
    (hA2 : ∀ x : Ext W.D', x * x = 1 → χ x ≠ 1 → ¬ ConjTo t (W.ψ x))
    (hA3 : ∀ x : Ext W.D', χ x = 1 → x * x ≠ 1 → x * x * (x * x) = 1 →
      ¬ ConjTo t (W.ψ (x * x)))
    {g : Ext W.D'} (hg : χ g ≠ 1) (hg4 : g * g * (g * g) = 1)
    (hgt : ConjTo t (W.ψ (g * g))) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht1 : t ≠ 1 := L2K.t_ne_one (A := A)
  set G := W.ψ g with hG
  have hG4 : G ^ 4 = 1 := by
    rw [show G ^ 4 = W.ψ (g * g * (g * g)) by simp [hG, map_mul, pow_succ, mul_assoc], hg4,
      map_one]
  have hχg : χ g = Multiplicative.ofAdd 1 := (z2_cases _).resolve_left hg
  have hred : ∀ m : ℤ, ∃ r : ℕ, r < 4 ∧ G ^ m = G ^ r := by
    intro m
    refine ⟨(m % 4).toNat, ?_, ?_⟩
    · have := Int.emod_lt_of_pos m (by norm_num : (0 : ℤ) < 4)
      omega
    · have h0 : 0 ≤ m % 4 := Int.emod_nonneg m (by norm_num)
      have e : m % 4 = (((m % 4).toNat : ℕ) : ℤ) := (Int.toNat_of_nonneg h0).symm
      have hG4' : G ^ (4 : ℤ) = 1 := by exact_mod_cast hG4
      calc G ^ m = G ^ (4 * (m / 4) + m % 4) := by rw [Int.mul_ediv_add_emod]
        _ = G ^ (m % 4) := by rw [zpow_add, zpow_mul, hG4', one_zpow, one_mul]
        _ = G ^ (m % 4).toNat := by conv_lhs => rw [e]; rw [zpow_natCast]
  have hmain : G ∉ ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ := by
    refine CFSG.Quasithin.generalized_thompson_transfer_one_subgroup (p := 2) (X := ⊤) (H := T.P)
      (K := W.Kχ χ) le_top ?_ (W.Kχ_le χ) (fun h hh k hk => W.conj_mem_Kχ χ hh hk) ?_
      (W.ψ_mem g) (fun h => hg (W.mem_Kχ.mp h)) ⟨2, by simpa using hG4⟩ ?_
    · rw [relIndex_top_right]
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr W.sylow.not_dvd_index
    · rw [Subgroup.commutator_le]
      intro a ha b hb
      rw [commutatorElement_def]
      exact W.comm_mem_Kχ χ ha hb
    · intro m a _ ha
      obtain ⟨r, hr, hm⟩ := hred m
      rw [hm, hG, ← map_pow] at ha ⊢
      obtain ⟨y, hy⟩ := W.exists_ψ ha
      have hconj2 : ConjTo t (a⁻¹ * W.ψ (g * g) * a) := by
        have := (conjTo_conj_iff a⁻¹ (W.ψ (g * g))).mpr hgt
        rwa [inv_inv] at this
      have hyy : W.ψ (y * y) = a⁻¹ * W.ψ (g ^ r * g ^ r) * a := by
        rw [map_mul, hy, map_mul]
        group
      have h4 : W.ψ (g * g) * W.ψ (g * g) = 1 := by rw [← map_mul, hg4, map_one]
      have hodd : g ^ r * g ^ r = g * g →
          (Multiplicative.ofAdd (1 : ZMod 2)) ^ r = Multiplicative.ofAdd 1 →
          (W.ψ (g ^ r))⁻¹ * (a⁻¹ * W.ψ (g ^ r) * a) ∈ W.Kχ χ := by
        intro hrr hpar
        rw [← hy]
        rw [hrr] at hyy
        have hyc : ConjTo t (W.ψ (y * y)) := hyy ▸ hconj2
        have hχy : χ y ≠ 1 := by
          intro h1
          refine hA3 y h1 (fun h => ht1 ?_) ?_ hyc
          · rw [h, map_one] at hyc
            obtain ⟨c, hc⟩ := hyc
            calc t = c⁻¹ * (c * t * c⁻¹) * c := by group
              _ = 1 := by rw [hc]; group
          · apply W.ψ_injective
            rw [map_mul, hyy, map_one]
            calc a⁻¹ * W.ψ (g * g) * a * (a⁻¹ * W.ψ (g * g) * a) =
                a⁻¹ * (W.ψ (g * g) * W.ψ (g * g)) * a := by group
              _ = 1 := by rw [h4]; group
        rw [← map_inv, ← map_mul, W.mem_Kχ, map_mul, map_inv, map_pow, hχg,
          (z2_cases _).resolve_left hχy, hpar]
        exact inv_mul_cancel _
      interval_cases r
      · simp
      · exact hodd (by rw [pow_one]) (pow_one _)
      ·
        have hgg : g ^ 2 = g * g := pow_two g
        rw [hgg] at hy ⊢
        have hyc : ConjTo t (W.ψ y) := hy ▸ hconj2
        have hy2 : y * y = 1 := by
          apply W.ψ_injective
          rw [map_mul, hy, map_one]
          calc a⁻¹ * W.ψ (g * g) * a * (a⁻¹ * W.ψ (g * g) * a) =
              a⁻¹ * (W.ψ (g * g) * W.ψ (g * g)) * a := by group
            _ = 1 := by rw [h4]; group
        have hχy : χ y = 1 := by
          by_contra h1
          exact hA2 y hy2 h1 hyc
        rw [← hy, ← map_inv, ← map_mul, W.mem_Kχ, map_mul, map_inv, hχy, map_mul, z2_sq]
        exact inv_mul_cancel _
      · exact hodd (by
          calc g ^ 3 * g ^ 3 = g * g * (g * g) * (g * g) := by
                simp only [pow_succ, pow_zero, one_mul, mul_assoc]
            _ = g * g := by rw [hg4, one_mul]) z2_cube
  apply hmain
  rw [show ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ = commutator X from rfl, commutator_eq_top' hnonab]
  trivial

theorem false_of_ext [IsSimpleGroup X] (hnonab : ∃ a b : X, a * b ≠ b * a)
    (χ : Ext W.D' →* Multiplicative (ZMod 2)) (hu64 : 64 ≤ ccE W.uh) (hu : χ W.uh ≠ 1)
    (hE : ∀ x : Ext W.D', x * x = 1 → 64 ≤ ccE x → χ x ≠ χ W.uh → ¬ ConjTo t (W.ψ x)) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U := W.ψ W.uh with hU
  have hU2 : U * U = 1 := by
    rw [hU, ← map_mul, show W.uh * W.uh = 1 from
      (by rw [← map_mul, show MC.u * MC.u = 1 by decide +kernel, map_one]), map_one]
  refine CFSG.RankThree.PartTwo.Sec8.commutator_ne_top_of_extremal (p := 2) W.sylow (N := W.Kχ χ)
    (fun y hy z hz => W.comm_mem_Kχ χ hy hz) (x := U) (W.ψ_mem _)
    (fun h => hu (W.mem_Kχ.mp h)) (by rw [pow_two]; exact hU2) (fun g hg => ?_)
    (commutator_eq_top' hnonab)
  have hUC : U ∈ T.P ⊓ centralizer ({U} : Set X) :=
    ⟨W.ψ_mem _, mem_centralizer_singleton_iff.mpr rfl⟩
  have hhP : g⁻¹ * U * g ∈ T.P := hg U hUC
  obtain ⟨x, hx⟩ := W.exists_ψ hhP
  have hx2 : x * x = 1 := by
    apply W.ψ_injective
    rw [map_mul, hx, map_one, show g⁻¹ * U * g * (g⁻¹ * U * g) = g⁻¹ * (U * U) * g by group, hU2]
    group
  have hcard : 64 ≤ ccE x := by
    rw [← W.card_PC, hx]
    refine hu64.trans ?_
    rw [← W.card_PC]
    refine Nat.card_le_card_of_injective
      (fun y : (T.P ⊓ centralizer ({U} : Set X) : Subgroup X) =>
        (⟨g⁻¹ * y * g, hg y y.2, mem_centralizer_singleton_iff.mpr ?_⟩ :
          (T.P ⊓ centralizer ({g⁻¹ * U * g} : Set X) : Subgroup X))) ?_
    · have hyU := mem_centralizer_singleton_iff.mp y.2.2
      calc g⁻¹ * y * g * (g⁻¹ * U * g) = g⁻¹ * (y * U) * g := by group
        _ = g⁻¹ * (U * y) * g := by rw [hyU]
        _ = g⁻¹ * U * g * (g⁻¹ * y * g) := by group
    · intro a b hab
      have := congrArg (fun y : (T.P ⊓ centralizer ({g⁻¹ * U * g} : Set X) : Subgroup X) =>
        g * (y : X) * g⁻¹) hab
      simp only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] at this
      exact Subtype.ext this
  have hconj : ConjTo t (W.ψ x) := by
    rw [hx]
    have := (conjTo_conj_iff g⁻¹ U).mpr W.conjTo_u
    rwa [inv_inv] at this
  have hχ : χ x = χ W.uh := by
    by_contra h
    exact hE x hx2 hcard h hconj
  rw [← hx, ← map_inv, ← map_mul, W.mem_Kχ, map_mul, map_inv, hχ]
  exact inv_mul_cancel _

end Lift

end T2

end Conf

end KD8c

end CFSG.ComponentClassification.HSFLit
