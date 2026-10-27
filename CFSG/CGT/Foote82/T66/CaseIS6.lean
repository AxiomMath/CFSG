module

public import CFSG.CGT.Foote82.T66.CaseIS2
public import CFSG.CGT.Foote82.T66.CaseIS6D8
public import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.CGT.Foote82

namespace CaseIAux

open CFSG.Open CFSG.Quasithin.G11 CFSG.RankThree.PartTwo CFSG.QuasithinUnique
open Equiv Equiv.Perm CaseIPerm CaseIHeart CaseIS6D8

@[expose] def pa (m : ℕ) : Perm (Fin (m + 6)) := swap 0 1 * swap 2 5 * swap 2 4 * swap 2 3

@[expose] def pb (m : ℕ) : Perm (Fin (m + 6)) := swap 0 1 * swap 2 4

variable {m : ℕ}

theorem pa_mem (hm : m ≤ 1) : pa m ∈ alternatingGroup (Fin (m + 6)) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  interval_cases m <;> decide

theorem pb_mem (hm : m ≤ 1) : pb m ∈ alternatingGroup (Fin (m + 6)) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  interval_cases m <;> decide

theorem pa_pow_four (hm : m ≤ 1) : pa m ^ 4 = 1 := by interval_cases m <;> decide

theorem pb_mul_self (hm : m ≤ 1) : pb m * pb m = 1 := by interval_cases m <;> decide

theorem pb_pa (hm : m ≤ 1) : pb m * pa m * (pb m)⁻¹ = (pa m)⁻¹ := by
  interval_cases m <;> decide

theorem pa_sq (hm : m ≤ 1) : pa m ^ 2 = swap 2 4 * swap 3 5 := by interval_cases m <;> decide

theorem pa_comm (hm : m ≤ 1) : pa m * swap 0 1 = swap 0 1 * pa m := by
  interval_cases m <;> decide

theorem pb_comm (hm : m ≤ 1) : pb m * swap 0 1 = swap 0 1 * pb m := by
  interval_cases m <;> decide

theorem orderOf_pa (hm : m ≤ 1) : orderOf (pa m) = 4 := by
  have h1 : ¬ pa m ^ (2 ^ 1) = 1 := by interval_cases m <;> decide
  have h2 : pa m ^ (2 ^ (1 + 1)) = 1 := pa_pow_four hm
  have := orderOf_eq_prime_pow (p := 2) h1 h2
  simpa using this

theorem pb_ne_pow (hm : m ≤ 1) (k : ℕ) : pb m ≠ pa m ^ k := by
  have hred : pa m ^ k = pa m ^ (k % 4) := by
    conv_lhs => rw [← Nat.div_add_mod k 4, pow_add, pow_mul, pa_pow_four hm, one_pow, one_mul]
  rw [hred]
  have hk : k % 4 < 4 := Nat.mod_lt _ (by norm_num)
  interval_cases (k % 4) <;> interval_cases m <;> decide

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
variable {G L H₁ : Subgroup (GLV V)} {z : GLV V} {v : V}
  {ψ : ↥H₁ ≃* Equiv.Perm (Fin (m + 6 + 2))}

theorem Hyp.eq_one_of_mem_K_L (h : Hyp G L z v H₁ m ψ) {x : GLV V} (hxK : x ∈ KK G L)
    (hxL : x ∈ L) : x = 1 := by
  rw [← h.range_jL] at hxL
  obtain ⟨a, rfl⟩ := hxL
  have hc : ∀ b ∈ alternatingGroup (Fin (m + 6)), (a : Perm (Fin (m + 6))) * b = b * a := by
    intro b hb
    have h1 := Subgroup.mem_centralizer_iff.1 hxK.2 _ (h.jL_mem ⟨b, hb⟩)
    rw [← map_mul, ← map_mul] at h1
    exact congrArg Subtype.val (jL_injective h1).symm
  have h1 := CaseIAut.eq_one_of_commute_alternatingGroup (by omega) hc
  rw [show a = 1 from Subtype.ext h1, map_one]

theorem Hyp.yy_mul_not_mem_L (h : Hyp G L z v H₁ m ψ) {k : GLV V} (hkK : k ∈ KK G L) :
    yy ψ * k ∉ L := by
  intro hL
  obtain ⟨θ, -, hθ1, hθ3⟩ := h.exists_thetaL
  have hkN : k ∈ NN G L := h.K_le_N hkK
  have hθy : θ ⟨yy ψ, h.yy_mem_N⟩ = swap 0 1 := hθ3 _ _ yy_eq_pe_iota2
  have hθk : θ ⟨k, hkN⟩ = 1 := h.theta_of_mem_K hθ1 _ hkK
  rw [← h.range_jL] at hL
  obtain ⟨a, ha⟩ := hL
  have hθa : θ ⟨jL ψ a, h.jL_mem_N a⟩ = a := theta_jL hθ3 a _
  have e : (⟨jL ψ a, h.jL_mem_N a⟩ : ↥(NN G L)) = ⟨yy ψ, h.yy_mem_N⟩ * ⟨k, hkN⟩ :=
    Subtype.ext ha
  rw [e, map_mul, hθy, hθk, mul_one] at hθa
  have h1 := a.2
  rw [← hθa, Equiv.Perm.mem_alternatingGroup, sign_swap ne01'] at h1
  exact absurd h1 (by decide)

variable {S : Subgroup (GLV V)}

theorem SBad.exists_P (h : Hyp G L z v H₁ m ψ) (hS : SBad G L z ψ S) (h4 : Nat.card S = 4)
    (hm : m ≤ 1) :
    ∃ P : Subgroup (GLV V), P ≤ G ∧ Nonempty (↥P ≃* DihedralGroup 4 × DihedralGroup 4) ∧
      Nat.card P = 64 ∧ Nat.card (Subgroup.center ↥P) = 4 ∧
      z ∈ (Subgroup.center ↥P).map P.subtype ∧
      jL ψ ⟨swap 2 4 * swap 3 5, by
        rw [← pa_sq hm]; exact (alternatingGroup _).pow_mem (pa_mem hm) 2⟩ ∈
        (Subgroup.center ↥P).map P.subtype := by
  obtain ⟨s, hsS, hs4, hss, hgen⟩ := hS.exists_gen h h4
  have hys := hS.y_inv h hsS hs4 hgen
  have hyy : yy ψ * yy ψ = 1 := mul_self_of_orderOf_two h.yy_orderOf
  have hs4' : s ^ 4 = 1 := by rw [← hs4]; exact pow_orderOf_eq_one s
  set f₁ := dihHom s (yy ψ) hs4' hyy hys with hf₁
  have hy_ne : ∀ k : ℕ, yy ψ ≠ s ^ k := by
    intro k hk
    have hyS : yy ψ ∈ S := by rw [hk]; exact S.pow_mem hsS k
    have h1 : yy ψ * s * (yy ψ)⁻¹ = s := by
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 (hgen _ hyS)
      rw [← hi]; group
    rw [hys] at h1
    have h2 : s * s = 1 := by
      calc s * s = s * s⁻¹⁻¹ := by rw [inv_inv]
        _ = 1 := by rw [h1, mul_inv_cancel]
    rw [hss] at h2
    have h3 := h.std.orderOf_s
    rw [h2, orderOf_one] at h3
    exact absurd h3 (by norm_num)
  have hf₁inj : Function.Injective f₁ := dihHom_injective hs4 hy_ne
  set A := jL ψ ⟨pa m, pa_mem hm⟩ with hA
  set B := jL ψ ⟨pb m, pb_mem hm⟩ with hB
  have hA4 : A ^ 4 = 1 := by
    rw [hA, ← map_pow]
    have : (⟨pa m, pa_mem hm⟩ : alternatingGroup (Fin (m + 6))) ^ 4 = 1 :=
      Subtype.ext (pa_pow_four hm)
    rw [this, map_one]
  have hBB : B * B = 1 := by
    rw [hB, ← map_mul]
    have : (⟨pb m, pb_mem hm⟩ : alternatingGroup (Fin (m + 6))) * ⟨pb m, pb_mem hm⟩ = 1 :=
      Subtype.ext (pb_mul_self hm)
    rw [this, map_one]
  have hBA : B * A * B⁻¹ = A⁻¹ := by
    have e : (⟨pb m, pb_mem hm⟩ : alternatingGroup (Fin (m + 6))) * ⟨pa m, pa_mem hm⟩ *
        (⟨pb m, pb_mem hm⟩)⁻¹ = (⟨pa m, pa_mem hm⟩)⁻¹ := Subtype.ext (pb_pa hm)
    have := congrArg (jL ψ) e
    rw [map_mul, map_mul, map_inv, map_inv] at this
    exact this
  set f₂ := dihHom A B hA4 hBB hBA with hf₂
  have hA4' : orderOf A = 4 := by
    rw [hA, orderOf_injective _ jL_injective, ← Subgroup.orderOf_coe]
    exact orderOf_pa hm
  have hB_ne : ∀ k : ℕ, B ≠ A ^ k := by
    intro k hk
    rw [hA, hB, ← map_pow] at hk
    have := congrArg Subtype.val (jL_injective hk)
    exact pb_ne_pow hm k this
  have hf₂inj : Function.Injective f₂ := dihHom_injective hA4' hB_ne
  have hyA : Commute A (yy ψ) := by
    show A * yy ψ = yy ψ * A
    rw [yy_eq_pe_iota2]
    show pe ψ (iota2 (m + 6) (pa m)) * pe ψ (iota2 (m + 6) (swap 0 1)) =
      pe ψ (iota2 (m + 6) (swap 0 1)) * pe ψ (iota2 (m + 6) (pa m))
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, pa_comm hm]
  have hyB : Commute B (yy ψ) := by
    show B * yy ψ = yy ψ * B
    rw [yy_eq_pe_iota2]
    show pe ψ (iota2 (m + 6) (pb m)) * pe ψ (iota2 (m + 6) (swap 0 1)) =
      pe ψ (iota2 (m + 6) (swap 0 1)) * pe ψ (iota2 (m + 6) (pb m))
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, pb_comm hm]
  have hf₂L : ∀ d, f₂ d ∈ L := dihHom_mem (h.jL_mem _) (h.jL_mem _)
  have hcomm : ∀ d₁ d₂, Commute (f₁ d₁) (f₂ d₂) := by
    intro d₁ d₂
    refine dihHom_commute ?_ ?_ d₁
    · exact (Subgroup.mem_centralizer_iff.1 (hS.le hsS).2 _ (hf₂L d₂)).symm
    · exact (dihHom_commute hyA hyB d₂).symm
  have hdisj : Disjoint f₁.range f₂.range := by
    rw [disjoint_iff_inf_le]
    rintro x ⟨⟨d₁, rfl⟩, ⟨d₂, hd₂⟩⟩
    have hxL : f₁ d₁ ∈ L := hd₂ ▸ hf₂L d₂
    rcases d₁ with i | i
    · rw [dihHom_r] at hxL ⊢
      exact h.eq_one_of_mem_K_L ((KK G L).pow_mem (hS.le hsS) _) hxL
    · rw [dihHom_sr] at hxL
      exact absurd hxL (h.yy_mul_not_mem_L ((KK G L).pow_mem (hS.le hsS) _))
  set f := MonoidHom.noncommCoprod f₁ f₂ hcomm with hf
  have hfinj : Function.Injective f :=
    (MonoidHom.noncommCoprod_injective f₁ f₂ hcomm).2 ⟨hf₁inj, hf₂inj, hdisj⟩
  set P := f.range with hP
  let eP : (DihedralGroup 4 × DihedralGroup 4) ≃* ↥P := MonoidHom.ofInjective hfinj
  have hfG : ∀ d, f d ∈ G := by
    rintro ⟨d₁, d₂⟩
    show f₁ d₁ * f₂ d₂ ∈ G
    refine G.mul_mem (dihHom_mem (hS.le hsS).1 h.yy_mem_N.1 d₁) ?_
    exact h.H_le_G (h.L_le_H (hf₂L d₂))
  have hcent : ∀ d : DihedralGroup 4 × DihedralGroup 4, d ∈ Subgroup.center _ →
      f d ∈ (Subgroup.center ↥P).map P.subtype := by
    intro d hd
    refine ⟨⟨f d, d, rfl⟩, Subgroup.mem_center_iff.2 fun p => ?_, rfl⟩
    obtain ⟨_, ⟨e, rfl⟩⟩ := p
    apply Subtype.ext
    show f e * f d = f d * f e
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hd e)]
  have hz : f (DihedralGroup.r 2, 1) = z := by
    show f₁ (DihedralGroup.r 2) * f₂ 1 = z
    rw [map_one, mul_one, dihHom_r, show (2 : ZMod 4).val = 2 from rfl, sq, hss]
  have hx : f (1, DihedralGroup.r 2) = jL ψ ⟨swap 2 4 * swap 3 5, by
      rw [← pa_sq hm]; exact (alternatingGroup _).pow_mem (pa_mem hm) 2⟩ := by
    show f₁ 1 * f₂ (DihedralGroup.r 2) = _
    rw [map_one, one_mul, dihHom_r, show (2 : ZMod 4).val = 2 from rfl, hA, ← map_pow]
    congr 1
    exact Subtype.ext (pa_sq hm)
  refine ⟨P, ?_, ⟨eP.symm⟩, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨d, rfl⟩
    exact hfG d
  · rw [← Nat.card_congr eP.toEquiv, card_prod]
  · rw [← Nat.card_congr (Subgroup.centerCongr eP).toEquiv, card_center_prod]
  · rw [← hz]
    exact hcent _ (by
      rw [Subgroup.center_prod]
      exact Subgroup.mem_prod.2 ⟨r_two_mem_center, Subgroup.one_mem _⟩)
  · rw [← hx]
    exact hcent _ (by
      rw [Subgroup.center_prod]
      exact Subgroup.mem_prod.2 ⟨Subgroup.one_mem _, r_two_mem_center⟩)

end CaseIAux

end CFSG.CGT.Foote82
