module

public import CFSG.LocalAnalysis.Mason73.Powers
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.LocalAnalysis.Mason73

open CFSG.CGT.Stroth77.L4Sylow CFSG.GH74.GLS.Stage1.Thm3.Sec8 Equiv Subgroup
open scoped commutatorElement

variable {n : ℕ}

theorem detSum_wx2 : detSum (![-1, 1, -1, 1] : Fin 4 → ZMod (2 ^ n)) 1 := by
  rw [detSum_one_iff, Fin.sum_univ_four]
  simp only [Matrix.cons_val]
  ring

theorem x1T_mem_commutator_centralizer (hn : 3 ≤ n) {m m' : Fin 4 → ZMod (2 ^ n)}
    (hm : detSum m tP) (hm' : detSum m' zP)
    (hcomm : el m' zP hm' * el m tP hm = el m tP hm * el m' zP hm') :
    x1T (by omega) ∈ ⁅centralizer {el m tP hm}, centralizer {el m tP hm}⁆ := by
  have ha : el ![-1, 1, -1, 1] 1 detSum_wx2 ∈ centralizer {el m tP hm} := by
    rw [mem_centralizer_singleton_iff, el_comm_tP_iff (by omega) hm detSum_wx2]
    refine ⟨by decide, ?_⟩
    rw [pv_tP, OneMemClass.coe_one, pv_one]
    refine isConst_of_eq_four 0 ?_ ?_ ?_ ?_ <;>
      simp only [Pi.sub_apply, Matrix.cons_val] <;> ring1
  have hb : el m' zP hm' ∈ centralizer {el m tP hm} := mem_centralizer_singleton_iff.2 hcomm
  have hc := Subgroup.commutator_mem_commutator ha hb
  rw [commutatorElement_el (by omega) detSum_wx2 hm' (by decide)] at hc
  have h4 := four_mul_ss hn
  have hh2 := hh_add_hh (n := n) (by omega)
  have hx : x1T (n := n) (by omega) = el (![-1, 1, -1, 1] + pv ((1 : Fin81.R0) : Perm (Fin 4)) m' -
      (m' + pv ((zP : Fin81.R0) : Perm (Fin 4)) ![-1, 1, -1, 1])) 1
      (by rw [detSum_one_iff]; simp only [Pi.sub_apply, Pi.add_apply]
          rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, sum_pv,
            sum_pv]; ring) ^ 2 ^ (n - 3) := by
    rw [el_one_pow, x1T, el_eq_el_iff (by omega), OneMemClass.coe_one, pv_one, pv_zP]
    refine ⟨rfl, isConst_of_eq_four (2 * ss n) ?_ ?_ ?_ ?_⟩ <;>
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, hv, Matrix.cons_val, nsmul_eq_mul,
        Pi.mul_apply, Pi.natCast_apply, Nat.cast_one, Nat.cast_zero, mul_one, mul_zero] <;>
      first | ring1 | linear_combination -h4 - hh2 | linear_combination h4 + hh2 |
        linear_combination h4 - hh2 | linear_combination -h4 + hh2
  rw [hx]
  exact Subgroup.pow_mem _ hc _

theorem uvT_mul_tT_comm (hn : 2 ≤ n) :
    uvT (n := n) (by omega) * tT (by omega) = tT (by omega) * uvT (by omega) := by
  rw [uvT, tT, el_hv_mul, el_hv_mul, el_hv_eq_el_hv_iff' hn]
  decide

theorem x1T_mem_commutator_centralizer_tT (hn : 3 ≤ n) :
    x1T (n := n) (by omega) ∈ ⁅centralizer {tT (n := n) (by omega)}, centralizer {tT (by omega)}⁆ :=
  x1T_mem_commutator_centralizer hn _ _ (uvT_mul_tT_comm (by omega))

theorem uvxyT_mul_txT_comm (hn : 2 ≤ n) :
    uvxyT (n := n) (by omega) * txT n = txT n * uvxyT (by omega) := by
  rw [← diagAut_uvT, ← diagAut_tT (n := n) (by omega), ← map_mul, ← map_mul,
    uvT_mul_tT_comm hn]

theorem x1T_mem_commutator_centralizer_txT (hn : 3 ≤ n) :
    x1T (n := n) (by omega) ∈ ⁅centralizer {txT n}, centralizer {txT n}⁆ :=
  x1T_mem_commutator_centralizer hn _ _ (uvxyT_mul_txT_comm (by omega))

theorem two_mul_eq_zero_of_red_eq_zero (hn : 1 ≤ n) {x : ZMod (2 ^ n)} (hx : red n x = 0) :
    2 * x = 0 := by
  haveI : NeZero (2 ^ n) := ⟨by positivity⟩
  rw [red, ← ZMod.natCast_zmod_val x, map_natCast, ZMod.natCast_eq_zero_iff] at hx
  obtain ⟨k, hk⟩ := hx
  have h2 : (2 : ZMod (2 ^ n)) * x = ((2 * x.val : ℕ) : ZMod (2 ^ n)) := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val, Nat.cast_ofNat]
  rw [h2, ZMod.natCast_eq_zero_iff, hk]
  exact ⟨k, by rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel hn]⟩

theorem le_card_centA_of_piT_zP (hn : 2 ≤ n) {μ : L4Model n} (hπ : piT μ = zP) :
    2 ^ n ≤ Nat.card (centA μ) := by
  obtain ⟨d, π, hd, rfl⟩ := exists_eq_el μ
  rw [piT_el] at hπ
  subst hπ
  have hle : (pairHom (n := n) 0 1 2).ker ≤ (centA (el d zP hd)).comap beta := by
    intro e he
    rw [MonoidHom.mem_ker] at he
    have he' : (red n (vec e 0 + vec e 2), red n (vec e 1 - vec e 0)) =
        ((0 : ZMod (2 ^ (n - 1))), (0 : ZMod (2 ^ (n - 1)))) :=
      congrArg Multiplicative.toAdd he
    have h1 := two_mul_eq_zero_of_red_eq_zero (by omega) (congrArg Prod.fst he')
    have h2 := two_mul_eq_zero_of_red_eq_zero (by omega) (congrArg Prod.snd he')
    have hs : vec e 0 + vec e 1 + vec e 2 + vec e 3 = 0 := by
      rw [← Fin.sum_univ_four]
      exact mem_B.1 e.2
    refine Subgroup.mem_comap.2 (Subgroup.mem_inf.2 ⟨beta_mem_A e, ?_⟩)
    rw [mem_centralizer_singleton_iff, beta_apply]
    refine ((el_comm_diag_iff hn hd _).2 ?_).symm
    rw [pv_zP]
    refine isConst_of_eq_four (vec e 1 - vec e 0) ?_ ?_ ?_ ?_ <;>
      simp only [Pi.sub_apply, Matrix.cons_val] <;>
      first | ring1 | linear_combination -h2 | linear_combination hs - h1 - h2 |
        linear_combination -hs + h1
  have h1 := Subgroup.card_le_of_le hle
  rw [card_comap_beta hn inf_le_left, card_ker_pairHom (a := 0) (b := 1) (c := 2) (d' := 3)
    (by omega) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun v => by rw [Fin.sum_univ_four])] at h1
  have h2 : 2 ^ (n + 2) = 4 * 2 ^ n := by ring
  rw [h2] at h1
  exact Nat.le_of_mul_le_mul_left h1 (by norm_num)

theorem map_piT_centralizer_uvT_eq_top (hn : 2 ≤ n) :
    (centralizer {uvT (n := n) (by omega)}).map piT = ⊤ := by
  have ht : tP ∈ (centralizer {uvT (n := n) (by omega)}).map piT :=
    ⟨tT (by omega), mem_centralizer_singleton_iff.2 (uvT_mul_tT_comm hn).symm, rfl⟩
  have htu : tP * s23 ∈ (centralizer {uvT (n := n) (by omega)}).map piT := by
    refine ⟨tT (by omega) * uT (by omega), ?_, rfl⟩
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff, ← tT_mul_uT_mul_self hn]
    group
  have hs : s23 ∈ (centralizer {uvT (n := n) (by omega)}).map piT := by
    have := Subgroup.mul_mem _ (Subgroup.inv_mem _ ht) htu
    rwa [inv_mul_cancel_left] at this
  have key : ∀ σ : Fin81.R0, σ = 1 ∨ σ = s23 ∨ σ = tP ∨ σ = tP * s23 ∨ σ = s23 * tP ∨
      σ = tP * s23 * tP ∨ σ = s23 * tP * s23 ∨ σ = tP * s23 * tP * s23 := by
    decide
  rw [eq_top_iff]
  intro σ _
  rcases key σ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Subgroup.one_mem _
  · exact hs
  · exact ht
  · exact Subgroup.mul_mem _ ht hs
  · exact Subgroup.mul_mem _ hs ht
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ ht hs) ht
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hs ht) hs
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ht hs) ht) hs

theorem card_centralizer_uvT (hn : 2 ≤ n) :
    Nat.card (centralizer {uvT (n := n) (by omega)}) = 2 ^ (n + 3) := by
  refine le_antisymm (card_centralizer_le_of_piT_zP hn rfl) ?_
  rw [card_eq_card_inf_A_mul, map_piT_centralizer_uvT_eq_top hn, Subgroup.card_top,
    Fin81.card_R0]
  have h1 : 2 ^ n ≤ Nat.card (centralizer {uvT (n := n) (by omega)} ⊓ A n :
      Subgroup (L4Model n)) := by
    rw [inf_comm]
    exact le_card_centA_of_piT_zP hn rfl
  calc 2 ^ (n + 3) = 2 ^ n * 8 := by rw [pow_add]; norm_num
    _ ≤ _ := Nat.mul_le_mul_right 8 h1

theorem card_centralizer_uvxyT (hn : 2 ≤ n) :
    Nat.card (centralizer {uvxyT (n := n) (by omega)}) = 2 ^ (n + 3) := by
  rw [← diagAut_uvT, centralizer_mulEquiv_apply,
    Subgroup.card_map_of_injective (f := (diagAut n).toMonoidHom) (diagAut n).injective,
    card_centralizer_uvT hn]

theorem card_centralizer_of_piT_zP (hn : 3 ≤ n) {μ : L4Model n} (h2 : μ * μ = 1)
    (hπ : piT μ = zP) : Nat.card (centralizer {μ}) = 2 ^ (n + 3) := by
  rcases isConj_uvT_or_uvxyT hn h2 hπ with h | h
  · rw [card_centralizer_eq_of_isConj h, card_centralizer_uvT (by omega)]
  · rw [card_centralizer_eq_of_isConj h, card_centralizer_uvxyT (by omega)]

theorem le_card_centralizer_of_piT_zP (hn : 3 ≤ n) {μ : L4Model n} (h2 : μ * μ = 1)
    (hπ : piT μ = zP) : 2 ^ (n + 3) ≤ Nat.card (centralizer {μ}) :=
  (card_centralizer_of_piT_zP hn h2 hπ).ge

theorem R0_mul_self_eq_zP : ∀ σ : Fin81.R0, σ * σ = zP → σ = c4 ∨ σ = c4⁻¹ := by
  decide

theorem R0_comm_c4 : ∀ σ ρ : Fin81.R0, ρ * ρ = zP → σ * ρ = ρ * σ → σ * σ = 1 →
    σ = 1 ∨ σ = zP := by
  decide

theorem patFix_of_mul_self_eq_zP : ∀ ρ : Fin81.R0, ρ * ρ = zP → ∀ p : Fin 2 × Fin 2 × Fin 2,
    PatFix (ρ : Perm (Fin 4)) (pat p) → p = (0, 0, 0) ∨ p = (0, 1, 1) := by
  decide

theorem pv_c4 (e : Fin 4 → ZMod (2 ^ n)) : pv (c4 : Perm (Fin 4)) e = ![e 2, e 3, e 1, e 0] := by
  funext i
  fin_cases i <;> rfl

theorem pv_c4_inv (e : Fin 4 → ZMod (2 ^ n)) :
    pv ((c4⁻¹ : Fin81.R0) : Perm (Fin 4)) e = ![e 3, e 2, e 0, e 1] := by
  funext i
  fin_cases i <;> rfl

theorem mul_self_mul_self_eq_one_of_piT_zP (hn : 2 ≤ n) {b : L4Model n}
    (hb : piT b * piT b = zP) : b * b * (b * b) = 1 := by
  obtain ⟨d, ρ, hd, rfl⟩ := exists_eq_el b
  rw [piT_el] at hb
  rw [el_mul, el_mul, ← el_zero_one, el_eq_el_iff hn, hb]
  refine ⟨by decide, ?_⟩
  rw [pv_zP]
  rcases R0_mul_self_eq_zP ρ hb with rfl | rfl
  · rw [pv_c4]
    refine isConst_of_eq_four (-(d 0 + d 1 + d 2 + d 3)) ?_ ?_ ?_ ?_ <;>
      simp only [Pi.sub_apply, Pi.add_apply, Pi.zero_apply, Matrix.cons_val] <;> ring1
  · rw [pv_c4_inv]
    refine isConst_of_eq_four (-(d 0 + d 1 + d 2 + d 3)) ?_ ?_ ?_ ?_ <;>
      simp only [Pi.sub_apply, Pi.add_apply, Pi.zero_apply, Matrix.cons_val] <;> ring1

theorem eq_one_or_zT_of_comm (hn : 3 ≤ n) {r ν : L4Model n} (hr : piT r * piT r = zP)
    (hA : ν ∈ A n) (h2 : ν * ν = 1) (hν : ν * r = r * ν) : ν = 1 ∨ ν = zT (by omega) := by
  obtain ⟨p, rfl⟩ := exists_eq_omegaEl hn hA h2
  have hpat := patFix_of_comm hn hν.symm
  rcases patFix_of_mul_self_eq_zP _ hr p hpat with rfl | rfl
  · exact Or.inl (omegaEl_zero hn)
  · exact Or.inr (zT_eq_omegaEl hn).symm

theorem eq_of_mem_centralizer_of_mul_self_not_mem_A (hn : 3 ≤ n) {b e : L4Model n}
    (hb : b * b ∉ A n) (he : e ∈ centralizer {b}) (he2 : e * e = 1) (he1 : e ≠ 1) :
    e = zT (by omega) ∨ e = b * b ∨ e = b * b * zT (by omega) := by
  have hρ : piT b * piT b = zP := by
    rcases piT_mul_self b with h | h
    · exact absurd (mem_A_iff.2 h) hb
    · rwa [map_mul] at h
  have heb : e * b = b * e := mem_centralizer_singleton_iff.1 he
  have hσ : piT e = 1 ∨ piT e = zP := by
    refine R0_comm_c4 _ _ hρ ?_ ?_
    · rw [← map_mul, ← map_mul, heb]
    · rw [← map_mul, he2, map_one]
  rcases hσ with hσ | hσ
  · rcases eq_one_or_zT_of_comm hn hρ (mem_A_iff.2 hσ) he2 heb with h | h
    · exact absurd h he1
    · exact Or.inl h
  ·
    have hb4 := mul_self_mul_self_eq_one_of_piT_zP (by omega) hρ
    have hαA : e * (b * b) ∈ A n := by
      rw [mem_A_iff, map_mul, map_mul, hσ, hρ]
      decide
    have heb2 : e * (b * b) = b * b * e := by
      calc e * (b * b) = e * b * b := by group
        _ = b * e * b := by rw [heb]
        _ = b * (e * b) := by group
        _ = b * (b * e) := by rw [heb]
        _ = b * b * e := by group
    have hα2 : e * (b * b) * (e * (b * b)) = 1 := by
      calc e * (b * b) * (e * (b * b)) = e * (b * b * e) * (b * b) := by group
        _ = e * (e * (b * b)) * (b * b) := by rw [heb2]
        _ = e * e * (b * b * (b * b)) := by group
        _ = 1 := by rw [he2, hb4, one_mul]
    have hαb : e * (b * b) * b = b * (e * (b * b)) := by
      calc e * (b * b) * b = e * b * (b * b) := by group
        _ = b * e * (b * b) := by rw [heb]
        _ = b * (e * (b * b)) := by group
    have hbinv : (b * b)⁻¹ = b * b := inv_eq_of_mul_eq_one_left hb4
    rcases eq_one_or_zT_of_comm hn hρ hαA hα2 hαb with h | h
    · right; left
      calc e = e * (b * b) * (b * b)⁻¹ := by group
        _ = b * b := by rw [h, one_mul, hbinv]
    · right; right
      have hz := zT_mem_center (n := n) (by omega)
      calc e = e * (b * b) * (b * b)⁻¹ := by group
        _ = zT (by omega) * (b * b) := by rw [h, hbinv]
        _ = b * b * zT (by omega) := (Subgroup.mem_center_iff.mp hz (b * b)).symm

theorem mul_self_eq_or_of_piT_zP (hn : 3 ≤ n) {μ c : L4Model n} (h2 : μ * μ = 1)
    (hπ : piT μ = zP) (hc : c ∈ centralizer {μ}) (hA : c * c ∉ A n) :
    c * c = μ ∨ c * c = μ * zT (by omega) := by
  have hμ1 : μ ≠ 1 := by
    rintro rfl
    rw [map_one] at hπ
    exact absurd hπ (by decide)
  have hμc : μ ∈ centralizer {c} := by
    rw [mem_centralizer_singleton_iff] at hc ⊢
    exact hc.symm
  have hzz : zT (n := n) (by omega) * zT (by omega) = 1 := by
    rw [← pow_two, ← orderOf_dvd_iff_pow_eq_one, orderOf_zT (by omega)]
  rcases eq_of_mem_centralizer_of_mul_self_not_mem_A hn hA hμc h2 hμ1 with h | h | h
  · exfalso
    have hzA : zT (n := n) (by omega) ∈ A n := mem_A_of_one _
    rw [← h, mem_A_iff, hπ] at hzA
    exact absurd hzA (by decide)
  · exact Or.inl h.symm
  · right
    rw [h]
    simp only [mul_assoc, hzz, mul_one]

theorem mul_self_eq_zT_or_of_piT_zP (hn : 3 ≤ n) {μ c : L4Model n} (h2 : μ * μ = 1)
    (hπ : piT μ = zP) (hc : c ∈ centralizer {μ}) (hc1 : c * c ≠ 1)
    (hc2 : c * c * (c * c) = 1) :
    c * c = zT (by omega) ∨ c * c = μ ∨ c * c = μ * zT (by omega) := by
  by_cases hA : c * c ∈ A n
  · exact Or.inl (mul_self_eq_zT_of_piT_zP hn h2 hπ hc hA hc1 hc2)
  · exact Or.inr (mul_self_eq_or_of_piT_zP hn h2 hπ hc hA)

theorem exists_mem_A_mul_self_eq_zT_of_piT_zP (hn : 3 ≤ n) {μ : L4Model n} (hπ : piT μ = zP) :
    ∃ c ∈ A n, c ∈ centralizer {μ} ∧ c * c = zT (by omega) := by
  obtain ⟨m, π, hm, rfl⟩ := exists_eq_el μ
  rw [piT_el] at hπ
  subst hπ
  have h4 := four_mul_ss hn
  have hc : detSum (fun i => ss n * (![1, 1, -1, -1] : Fin 4 → ZMod (2 ^ n)) i) 1 := by
    rw [detSum_one_iff, Fin.sum_univ_four]
    simp only [Matrix.cons_val]
    ring
  refine ⟨el _ 1 hc, mem_A_of_one hc, ?_, ?_⟩
  · rw [mem_centralizer_singleton_iff]
    refine ((el_comm_diag_iff (by omega) _ hc).2 ?_).symm
    rw [pv_zP]
    refine isConst_of_eq_four 0 ?_ ?_ ?_ ?_ <;> simp only [Pi.sub_apply, Matrix.cons_val] <;>
      ring1
  · rw [el_mul, zT, el_eq_el_iff (by omega)]
    refine ⟨mul_one _, isConst_of_eq_four (2 * ss n) ?_ ?_ ?_ ?_⟩ <;>
      simp only [Pi.sub_apply, Pi.add_apply, OneMemClass.coe_one, pv_one, hv, Matrix.cons_val,
        Nat.cast_one, Nat.cast_zero, mul_one, mul_zero] <;>
      first | ring1 | linear_combination h4 | linear_combination -h4

theorem comm_iff_of_piT_eq (hn : 2 ≤ n) {g b b' : L4Model n} (hg : g ∈ A n)
    (hπ : piT b = piT b') : b * g = g * b ↔ b' * g = g * b' := by
  obtain ⟨e, σ, he, rfl⟩ := exists_eq_el g
  rw [el_mem_A] at hg
  subst hg
  obtain ⟨d, π, hd, rfl⟩ := exists_eq_el b
  obtain ⟨d', π', hd', rfl⟩ := exists_eq_el b'
  rw [piT_el, piT_el] at hπ
  subst hπ
  rw [el_comm_diag_iff hn hd he, el_comm_diag_iff hn hd' he]

theorem card_map_piT_le_of_forall_mem (B : Subgroup (L4Model n)) (s : Finset Fin81.R0)
    (hs : ∀ b ∈ B, piT b ∈ s) : Nat.card (B.map piT) ≤ s.card := by
  have hsub : ((B.map piT : Subgroup Fin81.R0) : Set Fin81.R0) ⊆ ↑s := by
    rintro _ ⟨g, hg, rfl⟩
    exact hs g hg
  calc Nat.card (B.map piT) = ((B.map piT : Subgroup Fin81.R0) : Set Fin81.R0).ncard :=
        Nat.card_coe_set_eq _
    _ ≤ (↑s : Set Fin81.R0).ncard := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = s.card := Set.ncard_coe_finset _

theorem mul_self_eq_one_of_comm_zP_tP (hn : 2 ≤ n) {g b₁ b₂ : L4Model n} (hg : g ∈ A n)
    (h₁ : piT b₁ = zP) (h₂ : piT b₂ = tP) (hg₁ : b₁ * g = g * b₁) (hg₂ : b₂ * g = g * b₂) :
    g * g = 1 := by
  obtain ⟨e, σ, he, rfl⟩ := exists_eq_el g
  rw [el_mem_A] at hg
  subst hg
  obtain ⟨d₁, π₁, hd₁, rfl⟩ := exists_eq_el b₁
  obtain ⟨d₂, π₂, hd₂, rfl⟩ := exists_eq_el b₂
  rw [piT_el] at h₁ h₂
  subst h₁ h₂
  have K₁ := (el_comm_diag_iff hn hd₁ he).1 hg₁
  have K₂ := (el_comm_diag_iff hn hd₂ he).1 hg₂
  rw [pv_zP] at K₁
  rw [pv_tP] at K₂
  have A01 := K₁ 0 1
  have A02 := K₁ 0 2
  have B02 := K₂ 0 2
  simp only [Pi.sub_apply, Matrix.cons_val] at A01 A02 B02
  rw [el_mul, ← el_zero_one, el_eq_el_iff hn, OneMemClass.coe_one, pv_one]
  refine ⟨by decide, isConst_of_eq_four (-(e 0 + e 0)) ?_ ?_ ?_ ?_⟩ <;>
    simp only [Pi.sub_apply, Pi.add_apply, Pi.zero_apply] <;>
    first | ring1 | linear_combination -A01 | linear_combination -B02 |
      linear_combination 2 * A02 - A01 - B02

theorem card_inf_A_le_four_of_comm (hn : 3 ≤ n) (B : Subgroup (L4Model n))
    (hc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) {b₁ b₂ : L4Model n} (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ B)
    (h₁ : piT b₁ = zP) (h₂ : piT b₂ = tP) : Nat.card (B ⊓ A n : Subgroup (L4Model n)) ≤ 4 := by
  classical
  set P : Finset (Fin 2 × Fin 2 × Fin 2) := {(0, 0, 0), (0, 1, 1), (1, 0, 1), (1, 1, 0)}
  have hsub : ((B ⊓ A n : Subgroup (L4Model n)) : Set (L4Model n)) ⊆ ↑(P.image (omegaEl hn)) := by
    intro g hg
    obtain ⟨hgB, hgA⟩ := Subgroup.mem_inf.1 hg
    have hg₁ := hc _ hb₁ _ hgB
    have hg₂ := hc _ hb₂ _ hgB
    obtain ⟨p, rfl⟩ := exists_eq_omegaEl hn hgA
      (mul_self_eq_one_of_comm_zP_tP (by omega) hgA h₁ h₂ hg₁ hg₂)
    have hp := patFix_of_comm hn hg₁
    rw [h₁] at hp
    rw [Finset.coe_image]
    refine ⟨p, ?_, rfl⟩
    rcases patFix_zP_cases p hp with rfl | rfl | rfl | rfl <;> simp [P]
  calc Nat.card (B ⊓ A n : Subgroup (L4Model n)) =
        ((B ⊓ A n : Subgroup (L4Model n)) : Set (L4Model n)).ncard := Nat.card_coe_set_eq _
    _ ≤ (↑(P.image (omegaEl hn)) : Set (L4Model n)).ncard :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = (P.image (omegaEl hn)).card := Set.ncard_coe_finset _
    _ ≤ P.card := Finset.card_image_le
    _ = 4 := by decide

theorem le_A_of_comm_of_le_centralizer_x1T (hn : 3 ≤ n) (B : Subgroup (L4Model n))
    (hB : B ≤ centralizer {x1T (n := n) (by omega)}) (hc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (h : 2 ^ (2 * n - 1) ≤ Nat.card B) : B ≤ A n := by
  intro b hbB
  by_contra hbA
  have hV : ∀ g ∈ B, piT g ∈ V2 := fun g hg => by
    have := hB hg
    rwa [centralizer_x1T hn, mem_comap] at this
  have hV2 : ∀ σ : Fin81.R0, σ ∈ V2 → σ = 1 ∨ σ = zP ∨ σ = tP ∨ σ = tzP := by decide
  have hBA1 : Nat.card (B ⊓ A n : Subgroup (L4Model n)) ≤ 2 ^ n := by
    refine (Subgroup.card_le_of_le ?_).trans (card_centA_le_of_fpf (g := b) (by omega) ?_)
    · intro g hg
      obtain ⟨hgB, hgA⟩ := Subgroup.mem_inf.1 hg
      exact Subgroup.mem_inf.2 ⟨hgA, mem_centralizer_singleton_iff.2 (hc _ hgB _ hbB)⟩
    · have hb1 : piT b ≠ 1 := fun h1 => hbA (mem_A_iff.2 h1)
      rcases hV2 _ (hV b hbB) with h' | h' | h' | h'
      · exact absurd h' hb1
      all_goals rw [h']; decide
  rw [card_eq_card_inf_A_mul] at h
  have hlt : 2 ^ n * 2 < 2 ^ (2 * n - 1) := by
    rw [← pow_succ]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have two : Nat.card (B.map piT) ≤ 2 → False := fun h2 =>
    absurd (h.trans (Nat.mul_le_mul hBA1 h2)) (not_le.2 hlt)
  by_cases hz : ∃ b₁ ∈ B, piT b₁ = zP
  · obtain ⟨b₁, hb₁, h₁⟩ := hz
    by_cases ht : ∃ b₂ ∈ B, piT b₂ = tP
    · obtain ⟨b₂, hb₂, h₂⟩ := ht
      have h4 := card_inf_A_le_four_of_comm hn B hc hb₁ hb₂ h₁ h₂
      have hπ4 : Nat.card (B.map piT) ≤ 4 :=
        (card_map_piT_le_of_forall_mem B {1, zP, tP, tzP} fun g hg => by
          rcases hV2 _ (hV g hg) with h' | h' | h' | h' <;> simp [h']).trans (by decide)
      have h16 : 4 * 4 < 2 ^ (2 * n - 1) := by
        calc 4 * 4 = 2 ^ 4 := by norm_num
          _ < 2 ^ (2 * n - 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
      exact absurd (h.trans (Nat.mul_le_mul h4 hπ4)) (not_le.2 h16)
    · refine two ((card_map_piT_le_of_forall_mem B {1, zP} fun g hg => ?_).trans (by decide))
      rcases hV2 _ (hV g hg) with h' | h' | h' | h'
      · simp [h']
      · simp [h']
      · exact absurd ⟨g, hg, h'⟩ ht
      · exact absurd ⟨b₁ * g, Subgroup.mul_mem _ hb₁ hg, by rw [map_mul, h₁, h']; decide⟩ ht
  · by_cases ht : ∃ b₂ ∈ B, piT b₂ = tP
    · obtain ⟨b₂, hb₂, h₂⟩ := ht
      refine two ((card_map_piT_le_of_forall_mem B {1, tP} fun g hg => ?_).trans (by decide))
      rcases hV2 _ (hV g hg) with h' | h' | h' | h'
      · simp [h']
      · exact absurd ⟨g, hg, h'⟩ hz
      · simp [h']
      · exact absurd ⟨b₂ * g, Subgroup.mul_mem _ hb₂ hg, by rw [map_mul, h₂, h']; decide⟩ hz
    · refine two ((card_map_piT_le_of_forall_mem B {1, tzP} fun g hg => ?_).trans (by decide))
      rcases hV2 _ (hV g hg) with h' | h' | h' | h'
      · simp [h']
      · exact absurd ⟨g, hg, h'⟩ hz
      · exact absurd ⟨g, hg, h'⟩ ht
      · simp [h']

theorem mem_centA_uT_inf_of_comm (hn : 2 ≤ n) {g l b : L4Model n} (hg : g ∈ A n)
    (hl : piT l = s23) (hb : piT b = s01 ∨ piT b = zP) (hgl : l * g = g * l)
    (hgb : b * g = g * b) :
    g ∈ centA (uT (n := n) (by omega)) ⊓ centA (uvT (n := n) (by omega)) := by
  have hgu : uT (n := n) (by omega) * g = g * uT (by omega) :=
    (comm_iff_of_piT_eq hn hg (hl.trans (piT_uT _).symm)).1 hgl
  refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hg, mem_centralizer_singleton_iff.2 hgu.symm⟩,
    Subgroup.mem_inf.2 ⟨hg, mem_centralizer_singleton_iff.2 ?_⟩⟩
  rcases hb with hb | hb
  · have hgv : vT (n := n) (by omega) * g = g * vT (by omega) :=
      (comm_iff_of_piT_eq hn hg (hb.trans (piT_vT _).symm)).1 hgb
    have h1 : Commute g (uT (n := n) (by omega)) := hgu.symm
    have h2 : Commute g (vT (n := n) (by omega)) := hgv.symm
    rw [← uT_mul_vT hn]
    exact h1.mul_right h2
  · exact ((comm_iff_of_piT_eq hn hg (hb.trans (piT_uvT _).symm)).1 hgb).symm

theorem card_centA_uT_inf_le (hn : 2 ≤ n) :
    Nat.card (centA (uT (n := n) (by omega)) ⊓ centA (uvT (n := n) (by omega)) :
      Subgroup (L4Model n)) ≤ 2 ^ (n - 1) := by
  have hSK : centA (uT (n := n) (by omega)) ⊓ centA (uvT (n := n) (by omega)) ≤
      centA (uvT (n := n) (by omega)) := inf_le_right
  have hK : Nat.card (centA (uvT (n := n) (by omega))) ≤ 2 ^ n :=
    card_centA_le_of_fpf hn (by rw [piT_uvT]; decide)
  have hx : x1T (n := n) (by omega) ∈ centA (uvT (n := n) (by omega)) := by
    refine Subgroup.mem_inf.2 ⟨x1T_mem_A _, mem_centralizer_singleton_iff.2 ?_⟩
    rw [x1T, uvT, el_hv_mul, el_hv_mul, el_hv_eq_el_hv_iff' hn]
    decide
  have hxS : x1T (n := n) (by omega) ∉
      centA (uT (n := n) (by omega)) ⊓ centA (uvT (n := n) (by omega)) := by
    intro hS
    have h := mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hS).1).2
    rw [x1T, uT, el_hv_mul, el_hv_mul, el_hv_eq_el_hv_iff' hn] at h
    revert h
    decide
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hSK
  have hk1 : k ≠ 1 := by
    rintro rfl
    rw [mul_one] at hk
    exact hxS ((Subgroup.eq_of_le_of_card_ge hSK hk.le).symm ▸ hx)
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hk
    exact (Nat.card_pos (α := centA (uvT (n := n) (by omega)))).ne' hk
  have h2 : Nat.card (centA (uT (n := n) (by omega)) ⊓ centA (uvT (n := n) (by omega)) :
      Subgroup (L4Model n)) * 2 ≤ 2 ^ (n - 1) * 2 := by
    calc _ ≤ Nat.card (centA (uT (n := n) (by omega)) ⊓ centA (uvT (n := n) (by omega)) :
          Subgroup (L4Model n)) * k := Nat.mul_le_mul_left _ (by omega)
      _ = Nat.card (centA (uvT (n := n) (by omega))) := hk.symm
      _ ≤ 2 ^ n := hK
      _ = 2 ^ (n - 1) * 2 := by rw [← pow_succ]; congr 1; omega
  exact Nat.le_of_mul_le_mul_right h2 (by norm_num)

theorem inf_A_eq_centA_of_comm_of_le_centralizer (hn : 3 ≤ n) {l : L4Model n}
    (hl : piT l = s23) (B : Subgroup (L4Model n)) (hB : B ≤ centralizer {l})
    (hc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (h : 2 ^ (2 * n - 1) ≤ Nat.card B) :
    B ⊓ A n = centA l := by
  have hπC : ∀ g ∈ B, piT g = 1 ∨ piT g = s23 ∨ piT g = s01 ∨ piT g = zP := by
    intro g hg
    have hgl : g * l = l * g := mem_centralizer_singleton_iff.1 (hB hg)
    have key : ∀ σ : Fin81.R0, σ * s23 = s23 * σ → σ = 1 ∨ σ = s23 ∨ σ = s01 ∨ σ = zP := by
      decide
    refine key _ ?_
    rw [← hl, ← map_mul, ← map_mul, hgl]
  rw [card_eq_card_inf_A_mul] at h
  by_cases hb : ∃ b ∈ B, piT b = s01 ∨ piT b = zP
  · exfalso
    obtain ⟨b, hbB, hbπ⟩ := hb
    have hS : B ⊓ A n ≤ centA (uT (n := n) (by omega)) ⊓ centA (uvT (n := n) (by omega)) := by
      intro g hg
      obtain ⟨hgB, hgA⟩ := Subgroup.mem_inf.1 hg
      exact mem_centA_uT_inf_of_comm (by omega) hgA hl hbπ
        (mem_centralizer_singleton_iff.1 (hB hgB)).symm (hc _ hbB _ hgB)
    have h1 := (Subgroup.card_le_of_le hS).trans (card_centA_uT_inf_le (by omega))
    have h2 : Nat.card (B.map piT) ≤ 4 :=
      (card_map_piT_le_of_forall_mem B {1, s23, s01, zP} fun g hg => by
        rcases hπC g hg with h' | h' | h' | h' <;> simp [h']).trans (by decide)
    have h4 : 2 ^ (n - 1) * 4 < 2 ^ (2 * n - 1) := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
      exact Nat.pow_lt_pow_right (by norm_num) (by omega)
    exact absurd (h.trans (Nat.mul_le_mul h1 h2)) (not_le.2 h4)
  · push Not at hb
    have h2 : Nat.card (B.map piT) ≤ 2 :=
      (card_map_piT_le_of_forall_mem B {1, s23} fun g hg => by
        rcases hπC g hg with h' | h' | h' | h'
        · simp [h']
        · simp [h']
        · exact absurd h' (hb g hg).1
        · exact absurd h' (hb g hg).2).trans (by decide)
    have hK : B ⊓ A n ≤ centA l := fun g hg => by
      obtain ⟨hgB, hgA⟩ := Subgroup.mem_inf.1 hg
      exact Subgroup.mem_inf.2 ⟨hgA, hB hgB⟩
    have hKc : Nat.card (centA l) ≤ 2 ^ (2 * n - 2) :=
      card_centA_le (by omega) fun hA => by
        rw [mem_A_iff, hl] at hA
        exact absurd hA (by decide)
    refine Subgroup.eq_of_le_of_card_ge hK (hKc.trans ?_)
    have h3 := h.trans (Nat.mul_le_mul_left _ h2)
    have h4 : 2 ^ (2 * n - 1) = 2 ^ (2 * n - 2) * 2 := by
      rw [← pow_succ]
      congr 1
      omega
    rw [h4] at h3
    exact Nat.le_of_mul_le_mul_right h3 (by norm_num)

theorem w1T_mem_centA_of_piT_s23 (hn : 3 ≤ n) {l : L4Model n} (hl : piT l = s23) :
    w1T hn ∈ centA l := by
  have huw : uT (n := n) (by omega) * w1T hn = w1T hn * uT (by omega) := by
    rw [uT, w1T, el_comm_diag_iff (by omega), pv_s23]
    refine isConst_of_eq_four 0 ?_ ?_ ?_ ?_ <;>
      simp only [Pi.sub_apply, Matrix.cons_val, wv, hv] <;> ring1
  have hlw := (comm_iff_of_piT_eq (by omega) (w1T_mem_A hn) ((piT_uT _).trans hl.symm)).1 huw
  exact Subgroup.mem_inf.2 ⟨w1T_mem_A hn, mem_centralizer_singleton_iff.2 hlw.symm⟩

theorem w1T_mem_of_comm_of_le_centralizer (hn : 3 ≤ n) {l : L4Model n} (hl : piT l = s23)
    (B : Subgroup (L4Model n)) (hB : B ≤ centralizer {l})
    (hc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (h : 2 ^ (2 * n - 1) ≤ Nat.card B) : w1T hn ∈ B := by
  have hw := w1T_mem_centA_of_piT_s23 hn hl
  rw [← inf_A_eq_centA_of_comm_of_le_centralizer hn hl B hB hc h] at hw
  exact (Subgroup.mem_inf.1 hw).1

theorem w1T_mem_of_comm_of_le_centralizer_uT (hn : 3 ≤ n) (B : Subgroup (L4Model n))
    (hB : B ≤ centralizer {uT (n := n) (by omega)}) (hc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (h : 2 ^ (2 * n - 1) ≤ Nat.card B) : w1T hn ∈ B :=
  w1T_mem_of_comm_of_le_centralizer hn rfl B hB hc h

abbrev E1x (hn : 2 ≤ n) : Subgroup (L4Model n) :=
  closure {x1T (by omega), y1T (by omega), uvxyT (by omega), txT n}

theorem E1x_eq_map (hn : 2 ≤ n) : E1x (n := n) hn = (E1 hn).map (diagAut n).toMonoidHom := by
  rw [E1, MonoidHom.map_closure, Set.image_insert_eq, Set.image_insert_eq, Set.image_insert_eq,
    Set.image_singleton, MulEquiv.coe_toMonoidHom, diagAut_x1T, diagAut_y1T, diagAut_uvT,
    diagAut_tT]

theorem card_E1x (hn : 3 ≤ n) : Nat.card (E1x (n := n) (by omega)) = 16 := by
  rw [E1x_eq_map, Subgroup.card_map_of_injective (f := (diagAut n).toMonoidHom)
    (diagAut n).injective, card_E1 hn]

theorem E1x_mul_self (hn : 2 ≤ n) : ∀ x ∈ E1x (n := n) hn, x * x = 1 := by
  rw [E1x_eq_map]
  rintro _ ⟨y, hy, rfl⟩
  rw [MulEquiv.coe_toMonoidHom, ← map_mul, E1_mul_self hn y hy, map_one]

theorem E1x_le_centralizer_txT (hn : 2 ≤ n) : E1x (n := n) hn ≤ centralizer {txT n} := by
  rw [E1x_eq_map, ← diagAut_tT (n := n) (by omega), centralizer_mulEquiv_apply]
  exact Subgroup.map_mono (E1_le_centralizer_tT hn)

theorem exists_mul_self_eq_uvxyT (hn : 2 ≤ n) :
    ∃ r ∈ centralizer {uvxyT (n := n) (by omega)}, r * r = uvxyT (by omega) := by
  have htu := tT_mul_uT_mul_self (n := n) hn
  refine ⟨diagAut n (tT (by omega) * uT (by omega)), ?_, ?_⟩
  · rw [← diagAut_uvT, centralizer_mulEquiv_apply]
    refine ⟨tT (by omega) * uT (by omega), ?_, rfl⟩
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff, ← htu]
    group
  · rw [← map_mul, htu, diagAut_uvT]

end CFSG.LocalAnalysis.Mason73
