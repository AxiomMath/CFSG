module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenSwapQ

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup Equiv Equiv.Perm CFSG.OddStandard.AltStdSec.SwapPattern

private def a2 : Perm (Fin 8) := swap 0 2 * swap 1 3

private def b2 : Perm (Fin 8) := swap 2 4 * swap 3 5

private theorem a2_mul_self : a2 * a2 = 1 := by decide

private theorem b2_mul_self : b2 * b2 = 1 := by decide

private theorem a2_mem_centralizer : a2 ∈ centralizer ({ρ₄'} : Set (Perm (Fin 8))) := by
  rw [mem_centralizer_singleton_iff]
  decide

private theorem b2_mem_centralizer : b2 ∈ centralizer ({ρ₄'} : Set (Perm (Fin 8))) := by
  rw [mem_centralizer_singleton_iff]
  decide

private theorem a2_mul_b2_orderOf : orderOf (a2 * b2) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact orderOf_eq_prime (by decide) (by decide)

private theorem commute_tau0_apply_eight_or_nine {σ : Perm (Fin 10)}
    (h : σ * τ₀ = τ₀ * σ) :
    (σ 8 = 8 ∧ σ 9 = 9) ∨ (σ 8 = 9 ∧ σ 9 = 8) := by
  have h9 : σ 9 = τ₀ (σ 8) := by
    have h' := congrArg (fun f : Perm (Fin 10) => f 8) h
    simpa [Equiv.Perm.mul_apply, τ₀_apply_eight] using h'
  by_cases h88 : σ 8 = 8
  · exact Or.inl ⟨h88, by rw [h9, h88, τ₀_apply_eight]⟩
  · by_cases h89 : σ 8 = 9
    · refine Or.inr ⟨h89, ?_⟩
      rw [h9, h89]
      decide
    · exfalso
      have hfix : τ₀ (σ 8) = σ 8 := Equiv.swap_apply_of_ne_of_ne h88 h89
      have hcontra : σ 9 = σ 8 := by rw [h9, hfix]
      exact absurd (σ.injective hcontra) (by decide)

private theorem mem_of_sq_one_of_normalizes {C : Subgroup (Perm (Fin 8))}
    (hcardC : Nat.card C = 2 ^ 7 * 3) {P : Subgroup (Perm (Fin 8))}
    (hcardP : Nat.card P = 2 ^ 7) (hPle : P ≤ C) {x : Perm (Fin 8)}
    (hx : x ∈ C) (hx2 : x * x = 1)
    (hnorm : x ∈ normalizer (P : Set (Perm (Fin 8)))) : x ∈ P := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hx1 : x = 1
  · rw [hx1]; exact P.one_mem
  · have hxord : orderOf x = 2 := orderOf_eq_prime (by rwa [pow_two]) hx1
    have hZpg : IsPGroup 2 (zpowers x : Subgroup (Perm (Fin 8))) := by
      apply IsPGroup.of_card (n := 1)
      rw [Nat.card_zpowers, hxord, pow_one]
    have hPpg : IsPGroup 2 P := IsPGroup.of_card (n := 7) hcardP
    have hnorm' : zpowers x ≤ normalizer (P : Set (Perm (Fin 8))) :=
      zpowers_le.2 hnorm
    have hsup_pg : IsPGroup 2 (P ⊔ zpowers x : Subgroup (Perm (Fin 8))) :=
      (sup_comm (zpowers x) P) ▸ IsPGroup.to_sup_of_normal_right' hZpg hPpg hnorm'
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hsup_pg
    have hle : P ⊔ zpowers x ≤ C := sup_le hPle (zpowers_le.2 hx)
    have hdvd : Nat.card (P ⊔ zpowers x : Subgroup (Perm (Fin 8))) ∣ Nat.card C :=
      Subgroup.card_dvd_of_le hle
    rw [hcardC, hn] at hdvd
    have hdvd27 : 2 ^ 7 ∣ 2 ^ n := by
      have h1 : Nat.card P ∣ Nat.card (P ⊔ zpowers x : Subgroup (Perm (Fin 8))) :=
        Subgroup.card_dvd_of_le le_sup_left
      rwa [hcardP, hn] at h1
    have hnpos : 0 < n := by
      by_contra hn0
      have hn0' : n = 0 := by omega
      rw [hn0', pow_zero] at hdvd27
      have := Nat.le_of_dvd (by norm_num : 0 < 1) hdvd27
      norm_num at this
    have hcop : Nat.Coprime (2 ^ n) 3 :=
      (Nat.coprime_pow_left_iff hnpos 2 3).2 (by norm_num)
    have h2ndvd : 2 ^ n ∣ 2 ^ 7 := hcop.dvd_of_dvd_mul_right hdvd
    have hpow : 2 ^ n = 2 ^ 7 := Nat.dvd_antisymm h2ndvd hdvd27
    have hn7 : n = 7 := Nat.pow_right_injective (by norm_num : 2 ≤ 2) hpow
    have hle2 : Nat.card (P ⊔ zpowers x : Subgroup (Perm (Fin 8))) ≤ Nat.card P :=
      le_of_eq (by rw [hn, hn7, hcardP])
    have hsup_eq : P ⊔ zpowers x = P :=
      (Subgroup.eq_of_le_of_card_ge le_sup_left hle2).symm
    have hxmem : x ∈ P ⊔ zpowers x := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
    rwa [hsup_eq] at hxmem

theorem liftS8_mem_of_normalizes {Q : Subgroup (Perm (Fin 10))} (hQ : GoodQ Q) {ρ : Perm (Fin 8)}
    (hn : ∀ q : Perm (Fin 10), q ∈ Q → liftS8 ρ * q * (liftS8 ρ)⁻¹ ∈ Q) : liftS8 ρ ∈ Q := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardC : Nat.card (centralizer ({ρ₄'} : Set (Perm (Fin 8)))) = 2 ^ 7 * 3 := by
    rw [CFSG.OddStandard.AltStdSec.nat_card_centralizer_of_mul_self ρ₄'_mul_self,
      card_cycleType_ρ₄']
    norm_num [Nat.factorial]
  have hinv : ∀ q ∈ Q, (liftS8 ρ)⁻¹ * q * liftS8 ρ ∈ Q := by
    intro q hq
    let f : Q → Q := fun y =>
      ⟨liftS8 ρ * (y : Perm (Fin 10)) * (liftS8 ρ)⁻¹, hn (y : Perm (Fin 10)) y.2⟩
    have hf : Function.Injective f := by
      intro y z hyz
      have hval : liftS8 ρ * (y : Perm (Fin 10)) * (liftS8 ρ)⁻¹
          = liftS8 ρ * (z : Perm (Fin 10)) * (liftS8 ρ)⁻¹ := congrArg Subtype.val hyz
      exact Subtype.ext (mul_left_cancel (mul_right_cancel hval))
    obtain ⟨y, hy⟩ := (Finite.injective_iff_surjective.1 hf) ⟨q, hq⟩
    have hval : liftS8 ρ * (y : Perm (Fin 10)) * (liftS8 ρ)⁻¹ = q := congrArg Subtype.val hy
    have hy' : (y : Perm (Fin 10)) = (liftS8 ρ)⁻¹ * q * liftS8 ρ := by rw [← hval]; group
    rw [← hy']; exact y.2
  have hcommρ4 : liftS8 ρ * ρ₄ = ρ₄ * liftS8 ρ := by
    have hcard_c : Multiset.card (liftS8 ρ * ρ₄ * (liftS8 ρ)⁻¹).cycleType = 4 := by
      have hconj : IsConj (liftS8 ρ * ρ₄ * (liftS8 ρ)⁻¹) ρ₄ :=
        isConj_iff.2 ⟨(liftS8 ρ)⁻¹, by group⟩
      rw [Equiv.Perm.isConj_iff_cycleType_eq] at hconj
      rw [hconj, ← liftS8_ρ₄', cycleType_liftS8, card_cycleType_ρ₄']
    have hccent : ∀ p ∈ Q,
        (liftS8 ρ * ρ₄ * (liftS8 ρ)⁻¹) * p = p * (liftS8 ρ * ρ₄ * (liftS8 ρ)⁻¹) := by
      intro p hp
      have hp' : (liftS8 ρ)⁻¹ * p * liftS8 ρ ∈ Q := hinv p hp
      calc (liftS8 ρ * ρ₄ * (liftS8 ρ)⁻¹) * p
          = liftS8 ρ * (ρ₄ * ((liftS8 ρ)⁻¹ * p * liftS8 ρ)) * (liftS8 ρ)⁻¹ := by group
        _ = liftS8 ρ * (((liftS8 ρ)⁻¹ * p * liftS8 ρ) * ρ₄) * (liftS8 ρ)⁻¹ := by
              rw [hQ.ρ₄_comm ((liftS8 ρ)⁻¹ * p * liftS8 ρ) hp']
        _ = p * (liftS8 ρ * ρ₄ * (liftS8 ρ)⁻¹) := by group
    have hc : liftS8 ρ * ρ₄ * (liftS8 ρ)⁻¹ = ρ₄ := by
      rcases hQ.center (liftS8 ρ * ρ₄ * (liftS8 ρ)⁻¹) (hn ρ₄ hQ.ρ₄_mem) hccent with
        h1 | h2 | h3 | h4
      · rw [h1, Equiv.Perm.cycleType_one] at hcard_c
        simp at hcard_c
      · rw [h2, card_cycleType_of_isSwap isSwap_τ₀] at hcard_c
        omega
      · exact h3
      · rw [h4, card_cycleType_τ₀_mul_ρ₄] at hcard_c
        omega
    rwa [mul_inv_eq_iff_eq_mul] at hc
  have hρC : ρ ∈ centralizer ({ρ₄'} : Set (Perm (Fin 8))) := by
    rw [mem_centralizer_singleton_iff]
    apply liftS8_injective
    rw [map_mul, map_mul, liftS8_ρ₄']
    exact hcommρ4
  let P' : Subgroup (Perm (Fin 8)) := Q.comap liftS8
  have hτ0order : orderOf τ₀ = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact τ₀_mul_self) (by decide)
  have hτ0_not_mem_map : τ₀ ∉ P'.map liftS8 := by
    rintro ⟨p, -, hp⟩
    have h8 := congrArg (fun f : Perm (Fin 10) => f 8) hp
    rw [liftS8_apply_eight, τ₀_apply_eight] at h8
    exact absurd h8 (by decide)
  have hnorm_map : P'.map liftS8 ≤
      Subgroup.normalizer (Subgroup.zpowers τ₀ : Subgroup (Perm (Fin 10))) := by
    rw [Subgroup.le_normalizer_iff]
    intro h hh k hk
    obtain ⟨p, -, rfl⟩ := Subgroup.mem_map.1 hh
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hk
    rw [← hm]
    have hcommT : Commute (liftS8 p) τ₀ := liftS8_mul_τ₀ p
    have hcomm : Commute (liftS8 p) (τ₀ ^ m) := hcommT.zpow_right m
    rw [hcomm.eq]
    rw [show τ₀ ^ m * liftS8 p * (liftS8 p)⁻¹ = τ₀ ^ m by group]
    rw [hm]
    exact hk
  have hQ_eq : Q = P'.map liftS8 ⊔ zpowers τ₀ := by
    apply le_antisymm
    · intro q hq
      have hcomm : q * τ₀ = τ₀ * q := (hQ.τ₀_comm q hq).symm
      rcases commute_tau0_apply_eight_or_nine hcomm with ⟨h8, h9⟩ | ⟨h8, h9⟩
      · obtain ⟨p, hp⟩ := mem_stab2_iff_exists_liftS8.1 (mem_stab2.2 ⟨h8, h9⟩)
        refine Subgroup.mem_sup_left (Subgroup.mem_map.2 ⟨p, ?_, hp⟩)
        show liftS8 p ∈ Q
        rw [hp]; exact hq
      · have hmem : τ₀ * q ∈ stab2 8 9 := by
          refine mem_stab2.2 ⟨?_, ?_⟩
          · rw [Equiv.Perm.mul_apply, h8]; decide
          · rw [Equiv.Perm.mul_apply, h9]; decide
        obtain ⟨p, hp⟩ := mem_stab2_iff_exists_liftS8.1 hmem
        have hpQ : liftS8 p ∈ Q := by rw [hp]; exact mul_mem hQ.τ₀_mem hq
        have hqeq : q = liftS8 p * τ₀ := by
          have h1 : q = τ₀ * liftS8 p := by rw [hp, ← mul_assoc, τ₀_mul_self, one_mul]
          rw [h1, ← liftS8_mul_τ₀ p]
        rw [hqeq]
        exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_map.2 ⟨p, hpQ, rfl⟩))
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers τ₀))
    · exact sup_le (Subgroup.map_le_iff_le_comap.2 le_rfl) (Subgroup.zpowers_le.2 hQ.τ₀_mem)
  have hcardP' : Nat.card P' = 2 ^ 7 := by
    have hcard_sup : Nat.card (P'.map liftS8 ⊔ zpowers τ₀ : Subgroup (Perm (Fin 10))) =
        2 * Nat.card (P'.map liftS8) :=
      card_sup_zpowers_of_notMem hτ0order hnorm_map hτ0_not_mem_map
    have hcard_map : Nat.card (P'.map liftS8) = Nat.card P' :=
      Subgroup.card_map_of_injective liftS8_injective
    have h : Nat.card Q = 2 * Nat.card P' := by rw [hQ_eq, hcard_sup, hcard_map]
    rw [hQ.card] at h
    omega
  have hP'leC : P' ≤ centralizer ({ρ₄'} : Set (Perm (Fin 8))) := by
    intro p hp
    rw [mem_centralizer_singleton_iff]
    apply liftS8_injective
    rw [map_mul, map_mul, liftS8_ρ₄']
    exact (hQ.ρ₄_comm (liftS8 p) (show liftS8 p ∈ Q from hp)).symm
  have hρN : ρ ∈ normalizer (P' : Set (Perm (Fin 8))) := by
    rw [Subgroup.mem_normalizer_iff]
    intro p
    constructor
    · intro hp
      show liftS8 (ρ * p * ρ⁻¹) ∈ Q
      simpa [map_mul, map_inv] using (hn (liftS8 p) (show liftS8 p ∈ Q from hp))
    · intro hp
      have hp' : liftS8 (ρ * p * ρ⁻¹) ∈ Q := by
        rw [← Subgroup.mem_comap]
        exact hp
      have h1 : liftS8 ρ * liftS8 p * (liftS8 ρ)⁻¹ ∈ Q := by
        simpa [map_mul, map_inv] using hp'
      have h2 : (liftS8 ρ)⁻¹ * (liftS8 ρ * liftS8 p * (liftS8 ρ)⁻¹) * liftS8 ρ ∈ Q :=
        hinv _ h1
      have heq : (liftS8 ρ)⁻¹ * (liftS8 ρ * liftS8 p * (liftS8 ρ)⁻¹) * liftS8 ρ
          = liftS8 p := by group
      rwa [heq] at h2
  let M : Subgroup (Perm (Fin 8)) :=
    centralizer ({ρ₄'} : Set (Perm (Fin 8))) ⊓ normalizer (P' : Set (Perm (Fin 8)))
  have hMleC : M ≤ centralizer ({ρ₄'} : Set (Perm (Fin 8))) := inf_le_left
  have hP'leM : P' ≤ M := fun x hx => ⟨hP'leC hx, Subgroup.le_normalizer hx⟩
  have hcardM_dvd : Nat.card M ∣ 2 ^ 7 * 3 := by
    have h := Subgroup.card_dvd_of_le hMleC
    rwa [hcardC] at h
  have hMcard : Nat.card M = 2 ^ 7 := by
    obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hP'leM
    have hk_dvd : k ∣ 3 := by
      have h : 2 ^ 7 * k ∣ 2 ^ 7 * 3 := by
        have h' : Nat.card M ∣ 2 ^ 7 * 3 := hcardM_dvd
        rwa [hk, hcardP'] at h'
      exact (mul_dvd_mul_iff_left (pow_ne_zero 7 (by norm_num : (2 : ℕ) ≠ 0))).1 h
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).1 hk_dvd with hk1 | hk3
    · rw [hk, hk1, mul_one, hcardP']
    · exfalso
      have hMcard' : Nat.card M = 2 ^ 7 * 3 := by rw [hk, hk3, hcardP']
      have hMC : centralizer ({ρ₄'} : Set (Perm (Fin 8))) ≤
          normalizer (P' : Set (Perm (Fin 8))) := by
        have h_eq : M = centralizer ({ρ₄'} : Set (Perm (Fin 8))) :=
          Subgroup.eq_of_le_of_card_ge hMleC (le_of_eq (hcardC.trans hMcard'.symm))
        rw [← h_eq]; exact inf_le_right
      have ha2P : a2 ∈ P' :=
        mem_of_sq_one_of_normalizes hcardC hcardP' hP'leC a2_mem_centralizer a2_mul_self
          (hMC a2_mem_centralizer)
      have hb2P : b2 ∈ P' :=
        mem_of_sq_one_of_normalizes hcardC hcardP' hP'leC b2_mem_centralizer b2_mul_self
          (hMC b2_mem_centralizer)
      have habP : a2 * b2 ∈ P' := mul_mem ha2P hb2P
      have h3dvd : 3 ∣ Nat.card P' := by
        have h := Subgroup.orderOf_dvd_natCard P' habP
        rwa [a2_mul_b2_orderOf] at h
      rw [hcardP'] at h3dvd
      norm_num at h3dvd
  have hMP' : P' = M :=
    Subgroup.eq_of_le_of_card_ge hP'leM (le_of_eq (hMcard.trans hcardP'.symm))
  have hρM : ρ ∈ M := ⟨hρC, hρN⟩
  have hρP' : ρ ∈ P' := by rw [hMP']; exact hρM
  show liftS8 ρ ∈ Q
  exact hρP'

end CFSG.OddStandard.AltStdSec.SwapPartner
