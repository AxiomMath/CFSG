module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L129JAct
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L129JG

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Open

private theorem sec12J_fintype_card_sl : Fintype.card Sec12SL = 60 := by
  rw [← Nat.card_eq_fintype_card]
  exact sec12F4_card_sl

theorem sec12J_elemAb_sl_card_le (P : Subgroup Sec12SL) (hP : IsElemAbelian 2 P) :
    Nat.card P ≤ 4 := by
  obtain ⟨n, hn⟩ := sec12J_card_two_pow hP
  have hdvd : 2 ^ n ∣ 60 := by
    rw [← hn]
    simpa [sec12J_fintype_card_sl] using Subgroup.card_subgroup_dvd_card P
  have hn2 : n ≤ 2 := sec12J_two_pow_dvd_sixty hdvd
  calc Nat.card P = 2 ^ n := hn
    _ ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hn2
    _ = 4 := by norm_num

private theorem sec12J_inf_ker_ne_bot {Ψ : Subgroup (Sec12SL × Sec12SL)}
    (hΨ : IsElemAbelian 2 Ψ) (hbig : 4 < Nat.card Ψ) (π : Sec12SL × Sec12SL →* Sec12SL) :
    Ψ ⊓ π.ker ≠ ⊥ := by
  have hmap : Nat.card (Ψ.map π) ≤ 4 := sec12J_elemAb_sl_card_le _ (hΨ.map π)
  have hmul := sec12J_card_inf_ker_mul π Ψ
  have h2 : 2 ≤ Nat.card (Ψ ⊓ π.ker : Subgroup (Sec12SL × Sec12SL)) := by
    by_contra h
    push Not at h
    have h1 : Nat.card (Ψ ⊓ π.ker : Subgroup (Sec12SL × Sec12SL)) ≤ 1 := by omega
    have hle : Nat.card (Ψ ⊓ π.ker : Subgroup (Sec12SL × Sec12SL)) *
        Nat.card (Ψ.map π) ≤ 4 := by
      calc Nat.card (Ψ ⊓ π.ker : Subgroup (Sec12SL × Sec12SL)) * Nat.card (Ψ.map π)
          ≤ 1 * 4 := Nat.mul_le_mul h1 hmap
        _ = 4 := by norm_num
    rw [hmul] at hle
    omega
  exact (Subgroup.one_lt_card_iff_ne_bot (Ψ ⊓ π.ker)).mp (by omega)

theorem sec12J_hstar {W Γ : Type} [Group W] [Finite W] [Group Γ] {ψ : Γ →* MulAut W}
    {φ : Sec12SL × Sec12SL →* Γ} (hS : Sec12Act ψ φ) {Ψ : Subgroup (Sec12SL × Sec12SL)}
    (hΨ : IsElemAbelian 2 Ψ) (hne : Ψ ≠ ⊥) :
    Nat.card Ψ * Nat.card {w : W // ∀ p ∈ Ψ, ψ (φ p) w = w} ≤ 64 := by
  obtain ⟨n, hn⟩ := sec12J_card_two_pow hΨ
  have hdvd : 2 ^ n ∣ 3600 := by
    rw [← hn]
    have h : Nat.card Ψ ∣ 60 * 60 := by
      simpa [Nat.card_prod, sec12J_fintype_card_sl] using Subgroup.card_subgroup_dvd_card Ψ
    norm_num at h
    exact h
  have hn4 : n ≤ 4 := sec12J_two_pow_dvd hdvd
  have hΨ16 : Nat.card Ψ ≤ 16 := by
    rw [hn]
    calc 2 ^ n ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hn4
      _ = 16 := by norm_num
  by_cases hsmall : Nat.card Ψ ≤ 4
  · obtain ⟨p, hp⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    have hpne : (p : Sec12SL × Sec12SL) ≠ 1 := fun h => hp (Subtype.ext h)
    have hfix : Nat.card {w : W // ∀ p ∈ Ψ, ψ (φ p) w = w} ≤ 16 :=
      (sec12J_card_subtype_le
        (P := fun w => ∀ p ∈ Ψ, ψ (φ p) w = w)
        (Q := fun w => ψ (φ (p : Sec12SL × Sec12SL)) w = w)
        (fun w hw => hw p p.2)).trans (hS.fix1 p hpne)
    calc Nat.card Ψ * Nat.card {w : W // ∀ p ∈ Ψ, ψ (φ p) w = w}
        ≤ 4 * 16 := Nat.mul_le_mul hsmall hfix
      _ = 64 := by norm_num
  · have hbig : 4 < Nat.card Ψ := Nat.lt_of_not_le hsmall
    have hne2 : Ψ ⊓ (MonoidHom.snd Sec12SL Sec12SL).ker ≠ ⊥ :=
      sec12J_inf_ker_ne_bot hΨ hbig (MonoidHom.snd Sec12SL Sec12SL)
    obtain ⟨q, hq1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne2
    have hqmem : (q : Sec12SL × Sec12SL) ∈ Ψ := (Subgroup.mem_inf.mp q.2).1
    have hqker : (q : Sec12SL × Sec12SL) ∈ (MonoidHom.snd Sec12SL Sec12SL).ker :=
      (Subgroup.mem_inf.mp q.2).2
    have hq2 : (q : Sec12SL × Sec12SL).2 = 1 := MonoidHom.mem_ker.mp hqker
    let A : Sec12SL := (q : Sec12SL × Sec12SL).1
    have hA : A ≠ 1 := by
      intro hA1
      refine hq1 (Subtype.ext ?_)
      exact Prod.ext hA1 hq2
    have hmemA : (A, 1) ∈ Ψ := by
      have hqeq : (q : Sec12SL × Sec12SL) = (A, 1) := Prod.ext rfl hq2
      simpa [hqeq] using hqmem
    have hne1 : Ψ ⊓ (MonoidHom.fst Sec12SL Sec12SL).ker ≠ ⊥ :=
      sec12J_inf_ker_ne_bot hΨ hbig (MonoidHom.fst Sec12SL Sec12SL)
    obtain ⟨q', hq'1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne1
    have hq'mem : (q' : Sec12SL × Sec12SL) ∈ Ψ := (Subgroup.mem_inf.mp q'.2).1
    have hq'ker : (q' : Sec12SL × Sec12SL) ∈ (MonoidHom.fst Sec12SL Sec12SL).ker :=
      (Subgroup.mem_inf.mp q'.2).2
    have hq'fst : (q' : Sec12SL × Sec12SL).1 = 1 := MonoidHom.mem_ker.mp hq'ker
    let B : Sec12SL := (q' : Sec12SL × Sec12SL).2
    have hB : B ≠ 1 := by
      intro hB1
      refine hq'1 (Subtype.ext ?_)
      exact Prod.ext hq'fst hB1
    have hmemB : (1, B) ∈ Ψ := by
      have hq'eq : (q' : Sec12SL × Sec12SL) = (1, B) := Prod.ext hq'fst rfl
      simpa [hq'eq] using hq'mem
    have hfix : Nat.card {w : W // ∀ p ∈ Ψ, ψ (φ p) w = w} ≤ 4 :=
      (sec12J_card_subtype_le
        (P := fun w => ∀ p ∈ Ψ, ψ (φ p) w = w)
        (Q := fun w => ψ (φ (A, 1)) w = w ∧ ψ (φ (1, B)) w = w)
        (fun w hw => ⟨hw (A, 1) hmemA, hw (1, B) hmemB⟩)).trans (hS.fix2 A B hA hB)
    calc Nat.card Ψ * Nat.card {w : W // ∀ p ∈ Ψ, ψ (φ p) w = w}
        ≤ 16 * 4 := Nat.mul_le_mul hΨ16 hfix
      _ = 64 := by norm_num

end CFSG.OddStandard.SmallF3.Omega
