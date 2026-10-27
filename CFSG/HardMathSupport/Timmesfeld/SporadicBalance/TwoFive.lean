module

public import CFSG.Assembly.Defs
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPPrimeCoreBasics
public import CFSG.Sporadic.SmallOddCore.GroupFacts

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Proving CFSG.Sporadic.SmallOddCore

variable {S : Type*} [Group S]

theorem factorization_five_three_pow_mul_forty (a : ℕ) : (3 ^ a * 40).factorization 5 = 1 := by
  have h40 : (40 : ℕ) = 2 ^ 3 * 5 := by norm_num
  rw [Nat.factorization_mul (by positivity) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow (by norm_num)]
  have : (40 : ℕ).factorization 5 = 1 := by
    rw [h40, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two]
    simp [Nat.Prime.factorization_self (by norm_num : Nat.Prime 5)]
  rw [this]
  simp

theorem not_normal_five_of_witness [Finite S] {C : Subgroup S} {a : ℕ}
    (hC : Nat.card C = 3 ^ a * 40) {u g : S} (hu : u ∈ C) (hu5 : orderOf u = 5) (hg : g ∈ C)
    (hgu : g * u * g⁻¹ ∉ Subgroup.zpowers u) :
    ∀ W : Subgroup S, W ≤ C → Nat.card W = 5 → ¬ ∀ x ∈ C, ∀ w ∈ W, x * w * x⁻¹ ∈ W := by
  intro W hWC hW5 hWn
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hf : (Nat.card C).factorization 5 = 1 := by
    rw [hC]
    exact factorization_five_three_pow_mul_forty a
  have hUle : Subgroup.zpowers u ≤ C := Subgroup.zpowers_le.2 hu
  have hWc : Nat.card (W.subgroupOf C) = 5 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWC).toEquiv]
    exact hW5
  have hUc : Nat.card ((Subgroup.zpowers u).subgroupOf C) = 5 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUle).toEquiv, Nat.card_zpowers, hu5]
  let SW : Sylow 5 C := Sylow.ofCard (W.subgroupOf C) (by rw [hf, pow_one]; exact hWc)
  let SU : Sylow 5 C :=
    Sylow.ofCard ((Subgroup.zpowers u).subgroupOf C) (by rw [hf, pow_one]; exact hUc)
  have hnorm : (SW : Subgroup C).Normal := by
    rw [show (SW : Subgroup C) = W.subgroupOf C from Sylow.coe_ofCard _ _]
    exact (Subgroup.normal_subgroupOf_iff hWC).2 fun h k hh hk => hWn k hk h hh
  have hsub : Unique (Sylow 5 C) := Sylow.unique_of_normal SW hnorm
  have hEq : (SU : Subgroup C) = (SW : Subgroup C) := congrArg _ (Subsingleton.elim SU SW)
  rw [show (SU : Subgroup C) = (Subgroup.zpowers u).subgroupOf C from Sylow.coe_ofCard _ _,
    show (SW : Subgroup C) = W.subgroupOf C from Sylow.coe_ofCard _ _] at hEq
  have huW : u ∈ W := by
    have : (⟨u, hu⟩ : C) ∈ (Subgroup.zpowers u).subgroupOf C := Subgroup.mem_zpowers u
    rw [hEq] at this
    exact this
  have hWeq : Subgroup.zpowers u = W := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 huW)
    rw [Nat.card_zpowers, hu5, hW5]
  apply hgu
  rw [hWeq]
  exact hWn g hg u huW

theorem gLAPPrimeCoreOf_eq_bot_of_card_forty [Finite S] {C : Subgroup S} {a : ℕ} (ha : 1 ≤ a)
    (hC : Nat.card C = 3 ^ a * 40)
    (h2 : ∀ w : S, orderOf w = 2 → ∀ Q : Subgroup S, IsPGroup 3 Q →
      Q ≤ Subgroup.centralizer ({w} : Set S) → Nat.card Q < 3 ^ (a - 1))
    (h5 : ∀ W : Subgroup S, W ≤ C → Nat.card W = 5 → ¬ ∀ x ∈ C, ∀ w ∈ W, x * w * x⁻¹ ∈ W) :
    GLAPPrimeCoreOf 3 C = ⊥ := by
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hL
  set L := GLAPPrimeCoreOf 3 C with hLdef
  have hLC : L ≤ C := GLAPPrimeCoreOf_le C
  have hcop : Nat.Coprime 3 (Nat.card L) := coprime_card_GLAPPrimeCoreOf Nat.prime_three C
  have hL40 : Nat.card L ∣ 40 := by
    have h1 : Nat.card L ∣ 3 ^ a * 40 := hC ▸ Subgroup.card_dvd_of_le hLC
    exact (Nat.Coprime.pow_left a hcop).symm.dvd_of_dvd_mul_left h1
  have hLne : Nat.card L ≠ 1 := fun h => hL (Subgroup.card_eq_one.1 h)
  by_cases h5L : 5 ∣ Nat.card L
  ·
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    obtain ⟨WL⟩ : Nonempty (Sylow 5 L) := inferInstance
    have hfL : (Nat.card L).factorization 5 = 1 := by
      apply le_antisymm
      · have := (Nat.factorization_le_iff_dvd (Nat.card_pos).ne' (by norm_num)).2 hL40 5
        have h40 : (40 : ℕ).factorization 5 = 1 := by
          have := factorization_five_three_pow_mul_forty 0
          simpa using this
        omega
      · exact (Nat.Prime.factorization_pos_of_dvd (by norm_num) Nat.card_pos.ne' h5L)
    have hWL : Nat.card (WL : Subgroup L) = 5 := by
      rw [Sylow.card_eq_multiplicity, hfL, pow_one]
    have hn : Nat.card (Sylow 5 L) = 1 := by
      have hmod := card_sylow_modEq_one 5 L
      have hdvd := Sylow.card_dvd_index WL
      have hidx : (WL : Subgroup L).index ∣ 8 := by
        have h1 := Subgroup.card_mul_index (WL : Subgroup L)
        rw [hWL] at h1
        have h2 : 5 * (WL : Subgroup L).index ∣ 5 * 8 := by
          rw [h1]; exact hL40
        exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h2
      have h8 : Nat.card (Sylow 5 L) ∣ 8 := hdvd.trans hidx
      have hle : Nat.card (Sylow 5 L) ≤ 8 := Nat.le_of_dvd (by norm_num) h8
      have hpos : 0 < Nat.card (Sylow 5 L) := Nat.card_pos
      unfold Nat.ModEq at hmod
      interval_cases hm : Nat.card (Sylow 5 L) <;> simp_all
    have hsub : Subsingleton (Sylow 5 L) := (Nat.card_eq_one_iff_unique.1 hn).1
    set W : Subgroup S := (WL : Subgroup L).map L.subtype with hW
    have hWcard : Nat.card W = 5 := by
      rw [hW, Subgroup.card_map_of_injective L.subtype_injective, hWL]
    have hWC : W ≤ C := (Subgroup.map_subtype_le _).trans hLC
    refine h5 W hWC hWcard fun x hx w hw => ?_
    obtain ⟨wl, hwl, rfl⟩ := Subgroup.mem_map.1 hw
    have hxL : x * (wl : S) * x⁻¹ ∈ L := GLAPPrimeCoreOf_conj_mem x hx wl wl.2
    have hord : orderOf (⟨x * (wl : S) * x⁻¹, hxL⟩ : L) ∣ 5 := by
      have h1 : orderOf wl ∣ 5 := hWL ▸ Subgroup.orderOf_dvd_natCard _ hwl
      have h2 : orderOf (⟨x * (wl : S) * x⁻¹, hxL⟩ : L) = orderOf wl := by
        rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe wl]
        have := (MulAut.conj x : S ≃* S).orderOf_eq (wl : S)
        simpa [MulAut.conj_apply] using this
      rw [h2]; exact h1
    have hmemWL : (⟨x * (wl : S) * x⁻¹, hxL⟩ : L) ∈ (WL : Subgroup L) := by
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).1 hord with h | h
      · rw [orderOf_eq_one_iff] at h
        rw [h]
        exact (WL : Subgroup L).one_mem
      · have hK : IsPGroup 5 ↥(Subgroup.zpowers (⟨x * (wl : S) * x⁻¹, hxL⟩ : L)) :=
          IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])
        obtain ⟨Q, hQ⟩ := hK.exists_le_sylow
        rw [Subsingleton.elim Q WL] at hQ
        exact hQ (Subgroup.mem_zpowers _)
    exact Subgroup.mem_map.2 ⟨_, hmemWL, rfl⟩
  · have h8 : Nat.card L ∣ 8 := by
      have hc : Nat.Coprime (Nat.card L) 5 :=
        ((Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 5)).2 h5L).symm
      exact hc.dvd_of_dvd_mul_right (by simpa using hL40 : Nat.card L ∣ 8 * 5)
    obtain ⟨q, hq, hqL⟩ := Nat.exists_prime_and_dvd hLne
    have hq2 : q = 2 := by
      have : q ∣ 2 ^ 3 := hqL.trans (by simpa using h8)
      exact (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow this)
    subst hq2
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := L) 2 hqL
    set w : S := (x : S) with hw
    have hwo : orderOf w = 2 := by rw [hw, Subgroup.orderOf_coe, hx]
    have hwL : w ∈ L := x.2
    obtain ⟨Pc⟩ : Nonempty (Sylow 3 C) := inferInstance
    set P : Subgroup S := (Pc : Subgroup C).map C.subtype with hP
    have hPC : P ≤ C := Subgroup.map_subtype_le _
    have hPp : IsPGroup 3 P := Pc.isPGroup'.map C.subtype
    have hr0 : (40 : ℕ) ≠ 0 := by norm_num
    have hPcard : Nat.card P = 3 ^ a := by
      rw [hP, Subgroup.card_map_of_injective C.subtype_injective, Sylow.card_eq_multiplicity, hC,
        Nat.factorization_mul (pow_ne_zero _ (by norm_num)) hr0,
        Nat.Prime.factorization_pow Nat.prime_three, Finsupp.add_apply, Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]
    have hcls : conjClass P w ⊆ (L : Set S) := by
      rintro _ ⟨g, hg, rfl⟩
      exact GLAPPrimeCoreOf_conj_mem g (hPC hg) w hwL
    have hncard : (conjClass P w).ncard ≤ 8 := by
      calc (conjClass P w).ncard ≤ (L : Set S).ncard := Set.ncard_le_ncard hcls (Set.toFinite _)
        _ = Nat.card L := (Nat.card_coe_set_eq (L : Set S)).symm
        _ ≤ 8 := Nat.le_of_dvd (by norm_num) h8
    have horb := ncard_conjClass_mul_card P w
    rw [hPcard] at horb
    have hQ := h2 w hwo (P ⊓ Subgroup.centralizer ({w} : Set S)) (hPp.to_le inf_le_left)
      inf_le_right
    obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_three).1
      (Dvd.intro _ horb : (conjClass P w).ncard ∣ 3 ^ a)
    have hj1 : j ≤ 1 := by
      by_contra hj2
      have : 3 ^ 2 ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have h3le : (conjClass P w).ncard ≤ 3 := by
      rw [hjeq]
      calc 3 ^ j ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hj1
        _ = 3 := by norm_num
    have ha' : 3 ^ a = 3 * 3 ^ (a - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    have : (conjClass P w).ncard * Nat.card ↥(P ⊓ Subgroup.centralizer ({w} : Set S)) <
        3 * 3 ^ (a - 1) :=
      calc _ ≤ 3 * Nat.card ↥(P ⊓ Subgroup.centralizer ({w} : Set S)) :=
            Nat.mul_le_mul_right _ h3le
        _ < 3 * 3 ^ (a - 1) := by omega
    omega

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
