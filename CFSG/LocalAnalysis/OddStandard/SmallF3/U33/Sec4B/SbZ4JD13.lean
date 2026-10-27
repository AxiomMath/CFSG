module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JD12
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JD11

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped commutatorElement

variable {H : Type} [Group H] [Finite H] {Q Y V V' B : Subgroup H} {ρ t τ l y z v₁ v₂ : H}

@[expose] def ZJNoAb (σ : H) : Prop :=
  ∀ A : Subgroup H, IsPGroup 2 A → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → σ ∈ A →
    (∃ w ∈ A, orderOf w = 8) → Nat.card A ≤ 16

namespace ZJData

variable (h : ZJData Q Y V V' B ρ t τ l y z v₁ v₂) include h

variable {Mh : Subgroup H} (hMh : IsZJMh y z v₁ v₂ Mh) include hMh

variable {Mc : Subgroup H} (hMc : IsZJMc ρ Q Mh Mc) include hMc

private theorem lt_mul_self : (l * t) * (l * t) = 1 := by
  calc (l * t) * (l * t) = l * (t * l) * t := by group
    _ = l * (l * t) * t := by rw [h.t_l]
    _ = (l * l) * (t * t) := by group
    _ = 1 := by rw [h.l_sq, h.t_sq, one_mul]

private theorem ttau_mul_self : (t * τ) * (t * τ) = 1 := by
  calc (t * τ) * (t * τ) = t * (τ * t) * τ := by group
    _ = t * (t * τ) * τ := by rw [← h.t_tau]
    _ = (t * t) * (τ * τ) := by group
    _ = 1 := by rw [h.t_sq, h.tau_sq, one_mul]

private theorem lt_ttau_mul_left : (l * t) * (t * τ) = l * τ := by
  calc (l * t) * (t * τ) = l * (t * t) * τ := by group
    _ = l * τ := by rw [h.t_sq]; group

private theorem ttau_lt_mul : (t * τ) * (l * t) = l * τ := by
  calc (t * τ) * (l * t) = t * (τ * l) * t := by group
    _ = t * (l * τ) * t := by rw [h.tau_l]
    _ = (t * l) * (τ * t) := by group
    _ = (l * t) * (t * τ) := by rw [h.t_l, ← h.t_tau]
    _ = l * (t * t) * τ := by group
    _ = l * τ := by rw [h.t_sq]; group

private theorem lt_ttau_comm : (l * t) * (t * τ) = (t * τ) * (l * t) :=
  (lt_ttau_mul_left h hMh hMc).trans (ttau_lt_mul h hMh hMc).symm

private theorem lt_conj_y : (l * t) * y * (l * t)⁻¹ = y * z := by
  have hyV : y ∈ V := by
    rw [h.V_eq]
    exact Subgroup.subset_closure (by simp)
  have hty : t * y * t⁻¹ = y := by
    have hcomm : t * y = y * t := h.V_cent_t y hyV
    rw [hcomm]; group
  calc (l * t) * y * (l * t)⁻¹ = l * (t * y * t⁻¹) * l⁻¹ := by group
    _ = l * y * l⁻¹ := by rw [hty]
    _ = y * z := h.l_y

private theorem lt_conj_mem_Mc {x : H} (hx : x ∈ Mc) :
    (l * t) * x * (l * t)⁻¹ ∈ Mc := by
  have h1 : t * x * t⁻¹ ∈ Mc := Mc_conj_t h hMh hMc hx
  have h2 : l * (t * x * t⁻¹) * l⁻¹ ∈ Mc := Mc_conj_l h hMh hMc h1
  convert h2 using 1
  group

private theorem lt_conj_mem_C {x : H} (hx : x ∈ Mc ⊓ centralizer ({t * τ} : Set H)) :
    (l * t) * x * (l * t)⁻¹ ∈ Mc ⊓ centralizer ({t * τ} : Set H) := by
  refine Subgroup.mem_inf.mpr ⟨lt_conj_mem_Mc h hMh hMc hx.1, ?_⟩
  have hxCent : x ∈ centralizer ({t * τ} : Set H) := hx.2
  rw [Subgroup.mem_centralizer_singleton_iff] at hxCent ⊢
  have hxs : Commute x (t * τ) := hxCent
  have hσcomm : Commute (l * t) (t * τ) := lt_ttau_comm h hMh hMc
  have hsconj : Commute ((l * t) * x * (l * t)⁻¹)
      ((l * t) * (t * τ) * (l * t)⁻¹) := hxs.conj (l * t)
  have hsfix : (l * t) * (t * τ) * (l * t)⁻¹ = t * τ := hσcomm.mul_inv_cancel
  rw [hsfix] at hsconj
  exact hsconj

private theorem exists_N_of_order_eight
    (hab : ∀ a ∈ Mc ⊓ centralizer ({t * τ} : Set H),
      ∀ b ∈ Mc ⊓ centralizer ({t * τ} : Set H), a * b = b * a)
    {c : H} (hcC : c ∈ Mc ⊓ centralizer ({t * τ} : Set H))
    (hc4 : c * c * (c * c) = y) :
    ∃ N ∈ Mc ⊓ centralizer ({t * τ} : Set H),
      orderOf N = 8 ∧ (l * t) * N * (l * t)⁻¹ = N := by
  have hσσ : (l * t) * (l * t) = 1 := lt_mul_self h hMh hMc
  have hσinv : (l * t)⁻¹ = l * t := inv_eq_of_mul_eq_one_right hσσ
  let c1 : H := (l * t) * c * (l * t)⁻¹
  have hc1C : c1 ∈ Mc ⊓ centralizer ({t * τ} : Set H) := lt_conj_mem_C h hMh hMc hcC
  let N : H := c * c1
  have hNC : N ∈ Mc ⊓ centralizer ({t * τ} : Set H) := by
    refine Subgroup.mem_inf.mpr ⟨Mc.mul_mem hcC.1 hc1C.1, ?_⟩
    exact (centralizer ({t * τ} : Set H)).mul_mem hcC.2 hc1C.2
  have hNcomm : c * c1 = c1 * c := hab c hcC c1 hc1C
  have hc4' : c ^ 4 = y := by
    have hp : c ^ 4 = c * c * (c * c) := by
      rw [show (4 : ℕ) = 2 + 2 by norm_num, pow_add, pow_two]
    rw [hp, hc4]
  have hc1pow : c1 ^ 4 = (l * t) * y * (l * t)⁻¹ := by
    show ((l * t) * c * (l * t)⁻¹) ^ 4 = (l * t) * y * (l * t)⁻¹
    rw [conj_pow, hc4']
  have hyV : y ∈ V := by
    rw [h.V_eq]
    exact Subgroup.subset_closure (by simp)
  have hyY : y ∈ Y := by rw [h.Y_eq]; exact Subgroup.mem_sup_left hyV
  have hzV : z ∈ V := by
    rw [h.V_eq]
    exact Subgroup.subset_closure (by simp)
  have hzY : z ∈ Y := by rw [h.Y_eq]; exact Subgroup.mem_sup_left hzV
  have hN4 : N ^ 4 = z := by
    show (c * c1) ^ 4 = z
    have hcomm : Commute c c1 := hNcomm
    rw [hcomm.mul_pow 4, hc4', hc1pow, lt_conj_y h hMh hMc]
    calc y * (y * z) = (y * y) * z := by group
      _ = z := by rw [h.Y_sq y hyY]; group
  have hN8 : N ^ 8 = 1 := by
    have hp : N ^ 8 = N ^ 4 * N ^ 4 := by
      rw [show (8 : ℕ) = 4 + 4 by norm_num, pow_add]
    rw [hp, hN4, h.Y_sq z hzY]
  have hordN : orderOf N = 8 := by
    have hnot : ¬ N ^ 2 ^ 2 = 1 := by
      rw [show (2 : ℕ) ^ 2 = 4 by norm_num, hN4]
      exact h.z_ne_one
    have hfin : N ^ 2 ^ (2 + 1) = 1 := by
      rw [show (2 : ℕ) ^ (2 + 1) = 8 by norm_num]
      exact hN8
    have hord := orderOf_eq_prime_pow (x := N) (p := 2) (n := 2) hnot hfin
    simpa using hord
  have hconj1 : (l * t) * c1 * (l * t)⁻¹ = c := by
    show (l * t) * ((l * t) * c * (l * t)⁻¹) * (l * t)⁻¹ = c
    rw [hσinv]
    calc (l * t) * ((l * t) * c * (l * t)) * (l * t)
        = ((l * t) * (l * t)) * c * ((l * t) * (l * t)) := by group
      _ = c := by rw [hσσ]; group
  have hNσfix : (l * t) * N * (l * t)⁻¹ = N := by
    show (l * t) * (c * c1) * (l * t)⁻¹ = c * c1
    calc (l * t) * (c * c1) * (l * t)⁻¹
        = ((l * t) * c * (l * t)⁻¹) * ((l * t) * c1 * (l * t)⁻¹) := by group
      _ = c1 * c := by rw [hconj1]
      _ = c * c1 := hNcomm.symm
  exact ⟨N, hNC, hordN, hNσfix⟩

private theorem closure_isPGroup_comm {N : H}
    (hNC : N ∈ Mc ⊓ centralizer ({t * τ} : Set H)) (hordN : orderOf N = 8)
    (hNσfix : (l * t) * N * (l * t)⁻¹ = N) :
    ∃ A : Subgroup H, IsPGroup 2 A ∧ (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧
      N ∈ A ∧ (t * τ) ∈ A ∧ (l * t) ∈ A := by
  have hNs : Commute N (t * τ) := Subgroup.mem_centralizer_singleton_iff.mp hNC.2
  have hNσ : Commute N (l * t) := by
    have h2 : N * (l * t) = (l * t) * N := by
      calc N * (l * t) = ((l * t) * N * (l * t)⁻¹) * (l * t) := by rw [hNσfix]
        _ = (l * t) * N := by group
    exact h2
  have hsσ : Commute (t * τ) (l * t) := (lt_ttau_comm h hMh hMc).symm
  let A : Subgroup H := Subgroup.closure ({N, t * τ, l * t} : Set H)
  have hpw : ({N, t * τ, l * t} : Set H).Pairwise Commute := by
    intro a ha b hb hne
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
    · exact absurd rfl hne
    · exact hNs
    · exact hNσ
    · exact hNs.symm
    · exact absurd rfl hne
    · exact hsσ
    · exact hNσ.symm
    · exact hsσ.symm
    · exact absurd rfl hne
  haveI hAcomm : IsMulCommutative A := Subgroup.isMulCommutative_closure hpw
  have hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    intro a ha b hb
    exact congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨a, ha⟩ : A) (⟨b, hb⟩ : A))
  have hNA : N ∈ A := Subgroup.subset_closure (by simp)
  have hsA : (t * τ) ∈ A := Subgroup.subset_closure (by simp)
  have hσA : (l * t) ∈ A := Subgroup.subset_closure (by simp)
  have hN8 : N ^ 8 = 1 := by rw [← hordN]; exact pow_orderOf_eq_one N
  have hs8 : (t * τ) ^ 8 = 1 := by
    rw [show (8 : ℕ) = 2 * 4 by norm_num, pow_mul, pow_two, ttau_mul_self h hMh hMc,
      one_pow]
  have hσ8 : (l * t) ^ 8 = 1 := by
    rw [show (8 : ℕ) = 2 * 4 by norm_num, pow_mul, pow_two, lt_mul_self h hMh hMc,
      one_pow]
  have h8 : ∀ a ∈ A, a ^ 8 = 1 := by
    intro a ha
    refine Subgroup.closure_induction (p := fun x _ => x ^ 8 = 1) ?_ ?_ ?_ ?_ ha
    · intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact hN8
      · exact hs8
      · exact hσ8
    · exact one_pow 8
    · intro x y hx hy hpx hpy
      have hcxy : Commute x y := hAab x hx y hy
      rw [hcxy.mul_pow 8, hpx, hpy, mul_one]
    · intro x hx hpx
      rw [inv_pow, hpx, inv_one]
  have hApg : IsPGroup 2 A := by
    rw [isPGroup_iff_pow_pow_eq_one]
    intro a
    have ha8 : (a : A) ^ 8 = 1 := by
      apply Subtype.ext
      simpa using h8 (a : H) a.2
    have hdvd : orderOf a ∣ 2 ^ 3 := by
      rw [show (2 : ℕ) ^ 3 = 8 by norm_num]
      exact orderOf_dvd_of_pow_eq_one ha8
    obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact ⟨k, by rw [← hk]; exact pow_orderOf_eq_one a⟩
  exact ⟨A, hApg, hAab, hNA, hsA, hσA⟩

private theorem card_gt_sixteen {N : H} {A : Subgroup H}
    (hApg : IsPGroup 2 A) (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hNA : N ∈ A) (hsA : (t * τ) ∈ A) (hσA : (l * t) ∈ A)
    (hNMc : N ∈ Mc) (hordN : orderOf N = 8) : 16 < Nat.card A := by
  haveI : IsMulCommutative A :=
    IsMulCommutative.of_comm (fun a b => Subtype.ext (hAab a a.2 b b.2))
  have hσσ : (l * t) * (l * t) = 1 := lt_mul_self h hMh hMc
  have hσinv : (l * t)⁻¹ = l * t := inv_eq_of_mul_eq_one_right hσσ
  have hsMc : (t * τ) ∉ Mc := by
    intro hs
    have hτMh : τ ∈ Mh := tau_mem_Mh h hMh
    have hmem : (t * τ) * τ ∈ Mh := Mh.mul_mem (Mc_le_Mh h hMh hMc hs) hτMh
    have heq : (t * τ) * τ = t := by rw [mul_assoc, h.tau_sq, mul_one]
    rw [heq] at hmem
    exact t_not_mem_Mh h hMh hmem
  have hσMc : (l * t) ∉ Mc := by
    intro hs
    have hσMh : (l * t) ∈ Mh := Mc_le_Mh h hMh hMc hs
    have hinv : (l * t)⁻¹ ∈ Mh := Mh.inv_mem hσMh
    have heq : (l * t)⁻¹ = t * l := by
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_right h.t_sq,
        inv_eq_of_mul_eq_one_right h.l_sq]
    rw [heq] at hinv
    exact tl_not_mem_Mh h hMh hinv
  have hlτMc : l * τ ∉ Mc := by
    intro hs
    have hMh' : l * τ ∈ Mh := Mc_le_Mh h hMh hMc hs
    have hτMh : τ ∈ Mh := tau_mem_Mh h hMh
    have hmem : (l * τ) * τ ∈ Mh := Mh.mul_mem hMh' hτMh
    have heq : (l * τ) * τ = l := by rw [mul_assoc, h.tau_sq, mul_one]
    rw [heq] at hmem
    exact l_not_mem_Mh h hMh hmem
  have hzpowMc : Subgroup.zpowers N ≤ Mc := Subgroup.zpowers_le.mpr hNMc
  have hsNz : (t * τ) ∉ Subgroup.zpowers N := fun hs => hsMc (hzpowMc hs)
  have hσNz : (l * t) ∉ Subgroup.zpowers N := fun hs => hσMc (hzpowMc hs)
  have hlτNz : l * τ ∉ Subgroup.zpowers N := fun hs => hlτMc (hzpowMc hs)
  let K : Subgroup A := (Subgroup.zpowers N).subgroupOf A
  have hzpow_le : Subgroup.zpowers N ≤ A := Subgroup.zpowers_le.mpr hNA
  have hKcard : Nat.card K = 8 := by
    calc Nat.card K = Nat.card (Subgroup.zpowers N) :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzpow_le).toEquiv
      _ = orderOf N := Nat.card_zpowers N
      _ = 8 := hordN
  haveI : K.Normal := Subgroup.normal_of_isMulCommutative K
  let sA : A := ⟨t * τ, hsA⟩
  let σA : A := ⟨l * t, hσA⟩
  have hsAK : sA ∉ K := fun h => hsNz (Subgroup.mem_subgroupOf.mp h)
  have hσAK : σA ∉ K := fun h => hσNz (Subgroup.mem_subgroupOf.mp h)
  have hne1 : K.index ≠ 1 := by
    intro h1
    have htop : K = ⊤ := (Subgroup.index_eq_one (H := K)).mp h1
    exact hsAK (by rw [htop]; exact Subgroup.mem_top sA)
  have hne2 : K.index ≠ 2 := by
    intro h2
    obtain ⟨a, ha⟩ := (Subgroup.index_eq_two_iff (H := K)).mp h2
    have hsK : sA * a ∈ K := by
      rcases ((xor_iff_or_and_not_and (sA * a ∈ K) (sA ∈ K)).mp (ha sA)).1 with h | h
      · exact h
      · exact absurd h hsAK
    have hσK : σA * a ∈ K := by
      rcases ((xor_iff_or_and_not_and (σA * a ∈ K) (σA ∈ K)).mp (ha σA)).1 with h | h
      · exact h
      · exact absurd h hσAK
    have hmem : (sA * a) * (σA * a)⁻¹ ∈ K := K.mul_mem hsK (K.inv_mem hσK)
    have hprod : (sA * a) * (σA * a)⁻¹ = sA * σA⁻¹ := by group
    rw [hprod] at hmem
    have hval : (((sA * σA⁻¹ : A) : H)) = l * τ := by
      change (t * τ) * (l * t)⁻¹ = l * τ
      rw [hσinv]
      exact ttau_lt_mul h hMh hMc
    have hzmem : l * τ ∈ Subgroup.zpowers N := by
      have h := Subgroup.mem_subgroupOf.mp hmem
      rwa [hval] at h
    exact hlτNz hzmem
  have hIdx4 : 4 ≤ K.index := by
    obtain ⟨n, hn⟩ := hApg.index K
    have hn2 : 2 ≤ n := by
      by_contra h
      have hle : n ≤ 1 := by omega
      interval_cases n
      · exact hne1 (by simpa using hn)
      · exact hne2 (by simpa using hn)
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
      _ = K.index := hn.symm
  have hmul : K.index * Nat.card K = Nat.card A := K.index_mul_card
  rw [← hmul, hKcard]
  nlinarith

theorem exists_abelian_big
    (hab : ∀ a ∈ Mc ⊓ centralizer ({t * τ} : Set H), ∀ b ∈ Mc ⊓ centralizer ({t * τ} : Set H),
      a * b = b * a)
    (hy : ∃ c ∈ Mc ⊓ centralizer ({t * τ} : Set H), c * c * (c * c) = y) :
    ∃ A : Subgroup H, IsPGroup 2 A ∧ (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧ l * t ∈ A ∧
      (∃ w ∈ A, orderOf w = 8) ∧ 16 < Nat.card A := by
  obtain ⟨c, hcC, hc4⟩ := hy
  obtain ⟨N, hNC, hordN, hNσfix⟩ := exists_N_of_order_eight h hMh hMc hab hcC hc4
  obtain ⟨A, hApg, hAab, hNA, hsA, hσA⟩ :=
    closure_isPGroup_comm h hMh hMc hNC hordN hNσfix
  have hAcard : 16 < Nat.card A :=
    card_gt_sixteen h hMh hMc hApg hAab hNA hsA hσA hNC.1 hordN
  exact ⟨A, hApg, hAab, hσA, ⟨N, hNA, hordN⟩, hAcard⟩

theorem not_sq_mem_Cq (hb : ZJBound t) (hno : ZJNoAb (l * t))
    (hZ : ∀ m ∈ Mc, m ∉ Q → m * m ∉ Y) {m₀ : H} (hm₀ : m₀ ∈ Mc) (hm₀Q : m₀ ∉ Q)
    (hβ : m₀ * τ * (m₀ * τ) = 1) {x : H} (hx : x ∈ Mc) (hxQ : x ∉ Q)
    (hxC : x * x ∈ Q ⊓ centralizer ({t * τ} : Set H)) : False := by
  have hsq := sq_mem_Cq_all h hMh hMc hx hxQ hxC
  have hcomm := comm_tau_mem_Cq_all h hMh hMc hm₀ hm₀Q hβ hsq
  have hV := comm_tt_mem_V h hMh hMc hcomm
  have hcard := card_cent_tt_ge h hMh hMc hV
  have hcen := Cq_le_center h hMh hMc hb hZ hsq hx hxQ
  have hab := cent_tt_comm h hMh hMc hcen
  have hyV : y ∈ V := by
    rw [h.V_eq]
    exact Subgroup.subset_closure (by simp)
  have hy := exists_c_fourth h hMh hMc hb hZ hsq hab hcard hyV
  obtain ⟨A, hApg, hAab, hσA, hw, hAcard⟩ := exists_abelian_big h hMh hMc hab hy
  have hle := hno A hApg hAab hσA hw
  omega

theorem Il_t (hb : ZJBound t)
    (hK : ∀ x ∈ Mc, x ∉ Q → x * x ∉ Q ⊓ centralizer ({t * τ} : Set H)) {m : H} (hm : m ∈ Mc)
    (h2 : t * m * (t * m) = 1) : ∃ w ∈ Mc, w * t * w⁻¹ = t * m := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.t_sq
  have htm : t * m = m⁻¹ * t := by
    have h3 : (t * m)⁻¹ = t * m := inv_eq_of_mul_eq_one_right h2
    calc t * m = (t * m)⁻¹ := h3.symm
      _ = m⁻¹ * t⁻¹ := mul_inv_rev t m
      _ = m⁻¹ * t := by rw [hti]
  have h4 : m * t * m = t := by
    calc m * t * m = m * (t * m) := by group
      _ = m * (m⁻¹ * t) := by rw [htm]
      _ = t := by group
  have ht' : t * m⁻¹ = m * t := by
    have h5 : m * t = t * m⁻¹ := by
      calc m * t = m * t * (m * m⁻¹) := by rw [mul_inv_cancel, mul_one]
        _ = (m * t * m) * m⁻¹ := by group
        _ = t * m⁻¹ := by rw [h4]
    exact h5.symm
  have hconj : m * t * m⁻¹ * t⁻¹ = m * m := by
    rw [hti]
    calc m * t * m⁻¹ * t = m * (t * m⁻¹) * t := by group
      _ = m * (m * t) * t := by rw [ht']
      _ = (m * m) * (t * t) := by group
      _ = m * m := by rw [h.t_sq]; group
  have hmmC : m * m ∈ Q ⊓ centralizer ({t * τ} : Set H) := by
    have hc := comm_t_mem_Cq h hMh (Mc_le_Mh h hMh hMc hm)
    rw [hconj] at hc
    exact hc
  have hmQ : m ∈ Q := by
    by_contra hmQ
    exact hK m hm hmQ hmmC
  obtain ⟨w, hw, hwe⟩ := Il_tQ h hMh hMc hb hmQ h2
  exact ⟨w, hw, hwe.symm⟩

end ZJData

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
