module

public import CFSG.CGT.PushingUpLit.BHS6.FaithfulAlt

public section

namespace CFSG.CGT.PushingUpLit.BHS6

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.G6 CFSG.QuasithinUnique
  CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS
open scoped commutatorElement

variable {Γ : Type} [Group Γ]

omit [Group Γ] in
theorem autOn_iSup_le [Group Γ] {V : Subgroup Γ} {P : Subgroup Γ → Prop}
    {U : Subgroup (MulAut ↥V)}
    (hN : ∀ A, P A → A ≤ Subgroup.normalizer (V : Set Γ))
    (h : ∀ A, P A → autOn A V ≤ U) : autOn (⨆ A, ⨆ (_ : P A), A) V ≤ U := by
  let K : Subgroup Γ := (U.comap (conjAct V)).map (Subgroup.normalizer (V : Set Γ)).subtype
  have hAK : ∀ A, P A → A ≤ K := by
    intro A hA x hx
    refine ⟨⟨x, hN A hA hx⟩, ?_, rfl⟩
    exact h A hA (mem_autOn_iff.mpr ⟨⟨x, hN A hA hx⟩, hx, rfl⟩)
  have hJK : (⨆ A, ⨆ (_ : P A), A) ≤ K := iSup_le fun A => iSup_le fun hA => hAK A hA
  intro y hy
  obtain ⟨x, hx, rfl⟩ := mem_autOn_iff.mp hy
  obtain ⟨x', hx'U, hx'⟩ := hJK hx
  have : x' = x := Subtype.ext hx'
  rw [← this]
  exact hx'U

section Finite

variable [Finite Γ] {G T E : Subgroup Γ}

theorem block_structure_sl (hG : CharTwo G) (hT : IsSylowOf 2 T G) (hE : IsBTBlock G T E)
    {n : ℕ} (hn2 : 2 ≤ n) (hn : IsNaturalSLTwoModule ↥E n) :
    autOn (baum T) (blockW E) ≤ autOn E (blockW E) ∧
      Nat.card ↥(autOn (baum T) (blockW E)) = 2 ^ n ∧
      autOn (thompsonJ T) (blockW E) = autOn (baum T) (blockW E) := by
  classical
  have hBN : baum T ≤ Subgroup.normalizer (E : Set Γ) := baum_le_normalizer_of_isBTBlock hE
  have hJB : thompsonJ T ≤ baum T := B6.thompsonJ_le_baum T
  have hJ : thompsonJ T ≤ Subgroup.normalizer (E : Set Γ) := hJB.trans hBN
  have h6 := six_four_d hG hT hE
  rw [blockW_eq_pCoreOf hE] at h6 ⊢
  set W : Subgroup Γ := pCoreOf 2 E with hWdef
  have hWe : IsElemAbelian 2 W := isElemAbelian_of_forall' hE.elemAbelian.1 hE.elemAbelian.2
  let _ : CommGroup ↥W := commGroupOfElemAbelian hWe
  have hEW : E ≤ Subgroup.normalizer (W : Set Γ) := le_normalizer_pCoreOf_self E
  have hperf : ⁅E, W⁆ = W := by rw [Subgroup.commutator_comm]; exact hE.perfect
  have hT' : IsSylowTwoOf T G := isSylowTwoOf_of_isSylowOf hT
  have hWT : W ≤ T := pCoreOf_le_sylow hG hT hE hT
  have hJW : thompsonJ T ≤ Subgroup.normalizer (W : Set Γ) :=
    hJ.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 E)
  have hBW : baum T ≤ Subgroup.normalizer (W : Set Γ) :=
    hBN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 E)
  have hT2 : IsPGroup 2 ↥T := hT.2.1
  have hJT : thompsonJ T ≤ T := iSup_le fun _ => iSup_le fun hA => hA.1
  have hJ2 : IsPGroup 2 ↥(thompsonJ T) := hT2.to_le hJT
  have hBT : baum T ≤ T := inf_le_left
  have hB2 : IsPGroup 2 ↥(baum T) := hT2.to_le hBT
  have hnat : IsNatSL E W n := by
    have := isNatSL_of_isBTBlock hG hT hE hn
    rwa [blockW_eq_pCoreOf hE] at this
  obtain ⟨D⟩ := nonempty_slNatData hWe hEW hperf hnat
  have hF : 2 ≤ Nat.card (GaloisField 2 n) := by
    rw [GaloisField.card 2 n (by omega)]
    exact Nat.le_self_pow (by omega) 2
  have hQ : IsPGroup 2 ↥(autOn (thompsonJ T) W) := isPGroup_autOn hJ2 hJW
  have hQN : autOn (thompsonJ T) W ≤ Subgroup.normalizer (autOn E W : Set (MulAut ↥W)) :=
    autOn_le_normalizer_autOn hJW hJ
  have hB : ∃ A, IsMaxElemAbelian T A ∧ ¬ A ≤ Subgroup.centralizer (W : Set Γ) := by
    by_contra hcon
    apply h6
    have hAc : ∀ A, IsMaxElemAbelian T A → A ≤ Subgroup.centralizer (W : Set Γ) := fun A hA => by
      by_contra hA'
      exact hcon ⟨A, hA, hA'⟩
    have hJC : thompsonJ T ≤ Subgroup.centralizer (W : Set Γ) :=
      iSup_le fun A => iSup_le fun hA => hAc A hA
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro w hw j hj
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact Subgroup.mem_centralizer_iff.mp (hJC hj) w hw
  let 𝒜 : Set (Subgroup (MulAut ↥W)) :=
    {B | ∃ A, IsMaxElemAbelian T A ∧ ¬ A ≤ Subgroup.centralizer (W : Set Γ) ∧ B = autOn A W}
  have hne : 𝒜.Nonempty := by
    obtain ⟨A, hA, hAc⟩ := hB
    exact ⟨autOn A W, A, hA, hAc, rfl⟩
  have h𝒜 : ∀ B ∈ 𝒜, B ≤ autOn (thompsonJ T) W ∧ IsElemAbelian2 B ∧ B ≠ ⊥ ∧
      Nat.card ↥W ≤ Nat.card ↥B * Nat.card ↥(fixV B) := by
    rintro B ⟨A, hA, hAc, rfl⟩
    have hAJ : A ≤ thompsonJ T := B6.le_thompsonJ hA
    have hAN : A ≤ Subgroup.normalizer (W : Set Γ) := hAJ.trans hJW
    refine ⟨autOn_le_autOn W hAJ, isElemAbelian2_autOn hWe hA.2.1 hAN,
      autOn_ne_bot_of_not_le_centralizer hAN hAc, ?_⟩
    rw [card_autOn_eq_relIndex hAN, card_fixV_autOn_eq hWe hAN]
    exact card_le_relIndex_mul_card_of_isMaxElemAbelian hA hWe hWT hAN
  obtain ⟨U, hUE, hUcard, hUeq, -, hfixed⟩ := sl_family D hF hQ hQN hne h𝒜
  have hJU : autOn (thompsonJ T) W = U := by
    refine le_antisymm ?_ ?_
    · refine autOn_iSup_le (P := fun A => IsMaxElemAbelian T A) (fun A hA => ?_) fun A hA => ?_
      · exact (B6.le_thompsonJ hA).trans hJW
      · by_cases hAc : A ≤ Subgroup.centralizer (W : Set Γ)
        · rw [autOn_eq_bot_of_le_centralizer hAc]
          exact bot_le
        · exact (hUeq _ ⟨A, hA, hAc, rfl⟩).le
    · obtain ⟨A, hA, hAc⟩ := hB
      rw [← hUeq _ ⟨A, hA, hAc, rfl⟩]
      exact autOn_le_autOn W (B6.le_thompsonJ hA)
  have hfix : fixV U ≤ fixV (autOn (baum T) W) := by
    intro w hw b hb
    obtain ⟨x, hxB, rfl⟩ := mem_autOn_iff.mp hb
    rw [← hJU, ← fixOn, fixOn_eq hWe hJW] at hw
    have hwJ : ∀ j ∈ thompsonJ T, j * (w : Γ) = (w : Γ) * j := fun j hj =>
      Subgroup.mem_centralizer_iff.mp (Subgroup.mem_subgroupOf.mp hw) j hj
    have hwΩ : (w : Γ) ∈ omegaOneCenterOf (thompsonJ T) :=
      mem_omegaOneCenter_thompsonJ_of_centralizes (hWT w.2) (hWe.2 w w.2)
        fun A hA a ha => hwJ a (B6.le_thompsonJ hA ha)
    have hxw : (w : Γ) * (x : Γ) = (x : Γ) * (w : Γ) :=
      Subgroup.mem_centralizer_iff.mp hxB.2 w hwΩ
    apply Subtype.ext
    rw [conjAct_apply']
    calc (x : Γ) * (w : Γ) * (x : Γ)⁻¹ = ((w : Γ) * x) * (x : Γ)⁻¹ := by rw [hxw]
      _ = w := by group
  have hQB : IsPGroup 2 ↥(autOn (baum T) W) := isPGroup_autOn hB2 hBW
  have hQBN : autOn (baum T) W ≤ Subgroup.normalizer (autOn E W : Set (MulAut ↥W)) :=
    autOn_le_normalizer_autOn hBW hBN
  obtain ⟨hBE, hBcard⟩ := hfixed _ hQB hQBN hfix
  have hUB : U ≤ autOn (baum T) W := hJU ▸ autOn_le_autOn W hJB
  have hUB' : U = autOn (baum T) W :=
    Subgroup.eq_of_le_of_card_ge hUB (hBcard.trans hUcard.symm.le)
  refine ⟨hBE, ?_, hJU.trans hUB'⟩
  rw [← hUB', hUcard, GaloisField.card 2 n (by omega)]

theorem block_structure_alt (hG : CharTwo G) (hT : IsSylowOf 2 T G) (hE : IsBTBlock G T E)
    {m : ℕ} (hm2 : 2 ≤ m) (hn : IsNaturalAltModule ↥E m) {W : Subgroup Γ}
    (hWE : W = pCoreOf 2 E) (hWe : IsElemAbelian 2 W) :
    letI : CommGroup ↥W := commGroupOfElemAbelian hWe
    ∃ (D : AltNatData (autOn E W) (2 * m + 1))
      (ψ : ↥(Subgroup.normalizer (autOn E W : Set (MulAut ↥W))) →*
        Equiv.Perm (Fin (2 * m + 1))),
      (∀ (x : ↥(Subgroup.normalizer (autOn E W : Set (MulAut ↥W)))) (w : ↥W),
        D.β ((x : MulAut ↥W) w) = coreAct (2 * m + 1) (ψ x) (D.β w)) ∧
      Function.Bijective D.β ∧ Function.Bijective ψ ∧
      autOn E W ⊔ autOn (baum T) W = Subgroup.normalizer (autOn E W : Set (MulAut ↥W)) ∧
      autOn (thompsonJ T) W = autOn (baum T) W ∧
      ∃ k : ℕ, 1 ≤ k ∧ 2 * k ≤ 2 * m + 1 ∧
        IsSwapGroupOfSize (((autOn (baum T) W).subgroupOf
          (Subgroup.normalizer (autOn E W : Set (MulAut ↥W)))).map ψ) k ∧
        Nat.card ↥(autOn (baum T) W) = 2 ^ k ∧
        ((∃ A, IsMaxElemAbelian T A ∧ Nat.card ↥(autOn A W) = 2 ^ m) →
          IsMaxSwapGroup (((autOn (baum T) W).subgroupOf
            (Subgroup.normalizer (autOn E W : Set (MulAut ↥W)))).map ψ)) := by
  classical
  subst hWE
  have hBN : baum T ≤ Subgroup.normalizer (E : Set Γ) := baum_le_normalizer_of_isBTBlock hE
  have hJB : thompsonJ T ≤ baum T := B6.thompsonJ_le_baum T
  have hJ : thompsonJ T ≤ Subgroup.normalizer (E : Set Γ) := hJB.trans hBN
  have h6 := six_four_d hG hT hE
  rw [blockW_eq_pCoreOf hE] at h6
  set W : Subgroup Γ := pCoreOf 2 E with hWdef
  let _ : CommGroup ↥W := commGroupOfElemAbelian hWe
  have hW2 : ∀ v : ↥W, v ^ 2 = 1 := fun v => Subtype.ext (by simpa [sq] using hWe.2 v v.2)
  have hEW : E ≤ Subgroup.normalizer (W : Set Γ) := le_normalizer_pCoreOf_self E
  have hperf : ⁅E, W⁆ = W := by rw [Subgroup.commutator_comm]; exact hE.perfect
  have hWT : W ≤ T := pCoreOf_le_sylow hG hT hE hT
  have hJW : thompsonJ T ≤ Subgroup.normalizer (W : Set Γ) :=
    hJ.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 E)
  have hBW : baum T ≤ Subgroup.normalizer (W : Set Γ) :=
    hBN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 E)
  have hT2 : IsPGroup 2 ↥T := hT.2.1
  have hJT : thompsonJ T ≤ T := iSup_le fun _ => iSup_le fun hA => hA.1
  have hJ2 : IsPGroup 2 ↥(thompsonJ T) := hT2.to_le hJT
  have hBT : baum T ≤ T := inf_le_left
  have hB2 : IsPGroup 2 ↥(baum T) := hT2.to_le hBT
  have hnat : IsNatAlt E W (2 * m + 1) := by
    have := isNatAlt_of_isBTBlock hG hT hE hn
    rwa [blockW_eq_pCoreOf hE] at this
  obtain ⟨D⟩ := nonempty_altNatData hWe hEW hperf hnat
  have hodd : Odd (2 * m + 1) := ⟨m, rfl⟩
  have h5 : 5 ≤ 2 * m + 1 := by omega
  have hQ : IsPGroup 2 ↥(autOn (thompsonJ T) W) := isPGroup_autOn hJ2 hJW
  have hQN : autOn (thompsonJ T) W ≤ Subgroup.normalizer (autOn E W : Set (MulAut ↥W)) :=
    autOn_le_normalizer_autOn hJW hJ
  have hB : ∃ A, IsMaxElemAbelian T A ∧ ¬ A ≤ Subgroup.centralizer (W : Set Γ) := by
    by_contra hcon
    apply h6
    have hAc : ∀ A, IsMaxElemAbelian T A → A ≤ Subgroup.centralizer (W : Set Γ) := fun A hA => by
      by_contra hA'
      exact hcon ⟨A, hA, hA'⟩
    have hJC : thompsonJ T ≤ Subgroup.centralizer (W : Set Γ) :=
      iSup_le fun A => iSup_le fun hA => hAc A hA
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro w hw j hj
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact Subgroup.mem_centralizer_iff.mp (hJC hj) w hw
  let 𝒜 : Set (Subgroup (MulAut ↥W)) :=
    {B | ∃ A, IsMaxElemAbelian T A ∧ ¬ A ≤ Subgroup.centralizer (W : Set Γ) ∧ B = autOn A W}
  have hne : 𝒜.Nonempty := by
    obtain ⟨A, hA, hAc⟩ := hB
    exact ⟨autOn A W, A, hA, hAc, rfl⟩
  have h𝒜 : ∀ B ∈ 𝒜, B ≤ autOn (thompsonJ T) W ∧ IsElemAbelian2 B ∧ B ≠ ⊥ ∧
      Nat.card ↥W ≤ Nat.card ↥B * Nat.card ↥(fixV B) := by
    rintro B ⟨A, hA, hAc, rfl⟩
    have hAJ : A ≤ thompsonJ T := B6.le_thompsonJ hA
    have hAN : A ≤ Subgroup.normalizer (W : Set Γ) := hAJ.trans hJW
    refine ⟨autOn_le_autOn W hAJ, isElemAbelian2_autOn hWe hA.2.1 hAN,
      autOn_ne_bot_of_not_le_centralizer hAN hAc, ?_⟩
    rw [card_autOn_eq_relIndex hAN, card_fixV_autOn_eq hWe hAN]
    exact card_le_relIndex_mul_card_of_isMaxElemAbelian hA hWe hWT hAN
  obtain ⟨-, hβbij, hψbij, hsup, ⟨k, hk1, hk2, hswap, hcard, hmax⟩, hfixed⟩ :=
    alt_family hW2 hodd h5 D hQ hQN hne h𝒜
  have hJU : autOn (thompsonJ T) W = ⨆ B ∈ 𝒜, B := by
    refine le_antisymm ?_ (iSup₂_le fun B hB' => ?_)
    · refine autOn_iSup_le (P := fun A => IsMaxElemAbelian T A) (fun A hA => ?_) fun A hA => ?_
      · exact (B6.le_thompsonJ hA).trans hJW
      · by_cases hAc : A ≤ Subgroup.centralizer (W : Set Γ)
        · rw [autOn_eq_bot_of_le_centralizer hAc]
          exact bot_le
        · exact le_iSup₂_of_le (autOn A W) ⟨A, hA, hAc, rfl⟩ le_rfl
    · obtain ⟨A, hA, -, rfl⟩ := hB'
      exact autOn_le_autOn W (B6.le_thompsonJ hA)
  have hfix : fixV (⨆ B ∈ 𝒜, B) ≤ fixV (autOn (baum T) W) := by
    intro w hw b hb
    obtain ⟨x, hxB, rfl⟩ := mem_autOn_iff.mp hb
    rw [← hJU, ← fixOn, fixOn_eq hWe hJW] at hw
    have hwJ : ∀ j ∈ thompsonJ T, j * (w : Γ) = (w : Γ) * j := fun j hj =>
      Subgroup.mem_centralizer_iff.mp (Subgroup.mem_subgroupOf.mp hw) j hj
    have hwΩ : (w : Γ) ∈ omegaOneCenterOf (thompsonJ T) :=
      mem_omegaOneCenter_thompsonJ_of_centralizes (hWT w.2) (hWe.2 w w.2)
        fun A hA a ha => hwJ a (B6.le_thompsonJ hA ha)
    have hxw : (w : Γ) * (x : Γ) = (x : Γ) * (w : Γ) :=
      Subgroup.mem_centralizer_iff.mp hxB.2 w hwΩ
    apply Subtype.ext
    rw [conjAct_apply']
    calc (x : Γ) * (w : Γ) * (x : Γ)⁻¹ = ((w : Γ) * x) * (x : Γ)⁻¹ := by rw [hxw]
      _ = w := by group
  have hQB : IsPGroup 2 ↥(autOn (baum T) W) := isPGroup_autOn hB2 hBW
  have hQBN : autOn (baum T) W ≤ Subgroup.normalizer (autOn E W : Set (MulAut ↥W)) :=
    autOn_le_normalizer_autOn hBW hBN
  have hBJ : autOn (baum T) W ≤ ⨆ B ∈ 𝒜, B := hfixed _ hQB hQBN hfix
  have hJeq : autOn (thompsonJ T) W = autOn (baum T) W :=
    le_antisymm (autOn_le_autOn W hJB) (hJU ▸ hBJ)
  have hJ'eq : (⨆ B ∈ 𝒜, B) = autOn (baum T) W := hJU.symm.trans hJeq
  have hN : autOn E W ⊔ autOn (baum T) W = Subgroup.normalizer (autOn E W : Set (MulAut ↥W)) := by
    refine le_antisymm (sup_le Subgroup.le_normalizer hQBN) ?_
    obtain ⟨A₀, hA₀⟩ := hne
    rw [← hsup A₀ hA₀]
    exact sup_le_sup_left (hJ'eq ▸ le_iSup₂_of_le A₀ hA₀ le_rfl) _
  rw [hJ'eq] at hswap hcard hmax
  refine ⟨D, D.psi hodd h5, fun x w => D.psi_spec hodd h5 x w, hβbij, hψbij, hN, hJeq, k, hk1, hk2,
    hswap, hcard, fun hH => hmax ?_⟩
  obtain ⟨A, hA, hAcard⟩ := hH
  have hAc : ¬ A ≤ Subgroup.centralizer (W : Set Γ) := by
    intro hAc
    rw [autOn_eq_bot_of_le_centralizer hAc, Subgroup.card_bot] at hAcard
    have : 2 ≤ 2 ^ m := Nat.le_self_pow (by omega) 2
    omega
  refine ⟨autOn A W, ⟨A, hA, hAc, rfl⟩, ?_⟩
  rw [hAcard]
  congr 1
  omega

end Finite

end CFSG.CGT.PushingUpLit.BHS6
