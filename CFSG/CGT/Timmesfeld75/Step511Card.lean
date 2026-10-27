module

public import CFSG.CGT.Timmesfeld75.Sec3Iso
public import CFSG.CGT.Timmesfeld75.Sec3TwelveIrr
public import CFSG.CGT.Timmesfeld75.Sec5Basic

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped MatrixGroups

theorem two_mul_dvd_of_two_pow_add_one_dvd {g a : ℕ} (hg : 0 < g)
    (h : 2 ^ g + 1 ∣ 2 ^ a - 1) : 2 * g ∣ a := by
  have h1 : ((2 ^ a - 1 : ℕ) : ZMod (2 ^ g + 1)) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h
  rw [Nat.cast_sub Nat.one_le_two_pow] at h1
  push_cast at h1
  have h2 : (2 : ZMod (2 ^ g + 1)) ^ a = 1 := sub_eq_zero.mp h1
  have hg2 : (2 : ZMod (2 ^ g + 1)) ^ g = -1 := by
    have h0 : ((2 ^ g + 1 : ℕ) : ZMod (2 ^ g + 1)) = 0 := ZMod.natCast_self _
    push_cast at h0
    linear_combination h0
  have h2g : (2 : ZMod (2 ^ g + 1)) ^ (2 * g) = 1 := by
    rw [two_mul, pow_add, hg2]
    norm_num
  have hord : orderOf (2 : ZMod (2 ^ g + 1)) = 2 * g := by
    refine (orderOf_eq_iff (by omega)).2 ⟨h2g, fun j hj hj0 => ?_⟩
    exact irr_two_pow_ne_one hj0 hj
  rw [← hord]
  exact orderOf_dvd_of_pow_eq_one h2

theorem step511_card (h214 : Lemma214) (hInv : InvolutionClassInput)
    (hIso : Section3IsoInput) {G : Type} [Group G] {T T₁ : Subgroup G} (hyp : StepHyp T T₁) :
    ∃ m r : ℕ, 1 ≤ m ∧ 1 ≤ r ∧ Nat.card T / Nat.card (normIn T T₁) = 2 ^ m ∧
      Nat.card T = (2 ^ m) ^ (r + 1) := by
  have : Finite G := hyp.finite
  have : IsSimpleGroup G := hyp.simple
  obtain ⟨x, hx⟩ := hyp.pair.conj
  have hS : Sec3 T T₁ := by
    have h := Sec3Global.of_inputs h214 hInv hyp.pair.wc x (hx ▸ hyp.pair.ne)
      (hx ▸ hyp.pair.nontriv)
    rwa [← hx] at h
  obtain ⟨hN, f, hf, hiso⟩ := hIso G hyp.nonab T T₁ hS
  have hX := hS.isL2Pair_quotient hf hiso
  have hcardT := hS.card_eq_mul hf hiso
  obtain ⟨n, hn0, hLn, -, hMn⟩ := hS.card_normIn_eq_two_pow
  set X := T ⊔ T₁ with hXdef
  set N : Subgroup ↥X := (cfgM T T₁).subgroupOf X with hNdef
  have hN2 : IsPGroup 2 N :=
    (isPGroup_two_of_isElemAbelian hS.cfg.isElemAbelian_cfgM).comap_subtype
  have hfpf : ∀ y : ↥X, Odd (orderOf (QuotientGroup.mk y : ↥X ⧸ N)) →
      (QuotientGroup.mk y : ↥X ⧸ N) ≠ 1 → ∀ n ∈ N, y * n * y⁻¹ = n → n = 1 := by
    intro y hodd hy1 n hn hfix
    have hn' : (n : G) ∈ cfgM T T₁ := Subgroup.mem_subgroupOf.1 hn
    have hfix' : (y : G) * n * (y : G)⁻¹ = n := congrArg Subtype.val hfix
    exact Subtype.ext (hS.centralizer_cfgM_eq_bot_of_odd hX y.2 hodd hy1 n hn' hfix')
  have hdY : 2 ^ f + 1 ∣ Nat.card ↥X := by
    rw [← Subgroup.card_mul_index N, Subgroup.index_eq_card, hX.card_eq_mul]
    refine Dvd.dvd.mul_left (Dvd.dvd.mul_left ?_ _) _
    have hsq := Nat.sq_sub_sq (2 ^ f) 1
    rw [one_pow] at hsq
    rw [hsq]
    exact Dvd.intro _ rfl
  have hodd : Odd (2 ^ f + 1) :=
    (Nat.even_pow.mpr ⟨even_two, (Nat.pos_of_ne_zero hf).ne'⟩).add_one
  have hdvd := irr_dvd_natCard_sub_one N N le_rfl hN2 hfpf hodd hdY
  have hcardN : Nat.card N = 2 ^ (2 * n) := by
    rw [← hMn]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (cfgM_le_sup T T₁)).toEquiv
  rw [hcardN] at hdvd
  have h2f : 2 * f ∣ 2 * n := two_mul_dvd_of_two_pow_add_one_dvd (Nat.pos_of_ne_zero hf) hdvd
  have hfn : f ∣ n := Nat.dvd_of_mul_dvd_mul_left two_pos h2f
  obtain ⟨r, hr⟩ := hfn
  have hfpos : 0 < f := Nat.pos_of_ne_zero hf
  have hr0 : 1 ≤ r := by
    rcases Nat.eq_zero_or_pos r with rfl | h
    · rw [mul_zero] at hr
      omega
    · exact h
  refine ⟨f, r, hfpos, hr0, ?_, ?_⟩
  · rw [hcardT]
    exact Nat.mul_div_cancel_left _ (Nat.card_pos)
  · rw [hcardT, hLn, hr, pow_mul, ← pow_succ]

@[expose] def Step511Core : Prop :=
  ∀ (G : Type) [Group G] (T T₁ : Subgroup G), StepHyp T T₁ → 4 < Nat.card T →
    ∀ n m : ℕ, Nat.card T / Nat.card (normIn T T₁) = 2 ^ m → Nat.card T = (2 ^ m) ^ n →
      (NaturalSL T (hSub T (normIn T₁ T)) n m ∨
        (Nat.card T = 16 ∧ ∃ _ : (T.subgroupOf (hSub T (normIn T₁ T))).Normal,
          (IsHatA 6 (↥(hSub T (normIn T₁ T)) ⧸ T.subgroupOf (hSub T (normIn T₁ T))) ∨
            IsHatA 7 (↥(hSub T (normIn T₁ T)) ⧸ T.subgroupOf (hSub T (normIn T₁ T))))))

theorem step511_of_core (h214 : Lemma214) (hInv : InvolutionClassInput)
    (hIso : Section3IsoInput) (hc : Step511Core) : Step511 := by
  intro G _ T T₁ hyp h4
  obtain ⟨m, r, -, -, hq, hT⟩ := step511_card h214 hInv hIso hyp
  exact ⟨r + 1, m, hq, hT, hc G T T₁ hyp h4 (r + 1) m hq hT⟩

end CFSG.CGT.Timmesfeld75
