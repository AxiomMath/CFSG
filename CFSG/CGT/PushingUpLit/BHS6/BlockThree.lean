module

public import CFSG.CGT.PushingUpLit.BHS6.BlockStructure
public import CFSG.CGT.PushingUpLit.BHS.TwoSixteenThree

public section

namespace CFSG.CGT.PushingUpLit.BHS6

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.G6 CFSG.QuasithinUnique
  CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS
open scoped commutatorElement

theorem isSwap_of_sq_eq_one_fin_three :
    ∀ σ : Equiv.Perm (Fin 3), σ ≠ 1 → σ ^ 2 = 1 → σ.IsSwap := by
  have h : ∀ σ : Equiv.Perm (Fin 3), σ ≠ 1 → σ ^ 2 = 1 →
      ∃ x y : Fin 3, x ≠ y ∧ σ = Equiv.swap x y := by
    decide
  exact h

variable {Γ : Type} [Group Γ]

section Finite

variable [Finite Γ] {G T E : Subgroup Γ}

theorem block_structure_three (hG : CharTwo G) (hT : IsSylowOf 2 T G) (hE : IsBTBlock G T E)
    (hn : IsNaturalAltModule ↥E 1) {W : Subgroup Γ} (hWE : W = pCoreOf 2 E)
    (hWe : IsElemAbelian 2 W) :
    letI : CommGroup ↥W := commGroupOfElemAbelian hWe
    ∃ (D : AltNatData (autOn E W) 3)
      (ψ : ↥(Subgroup.normalizer (autOn E W : Set (MulAut ↥W))) →* Equiv.Perm (Fin 3)),
      (∀ (x : ↥(Subgroup.normalizer (autOn E W : Set (MulAut ↥W)))) (w : ↥W),
        D.β ((x : MulAut ↥W) w) = coreAct 3 (ψ x) (D.β w)) ∧
      Function.Bijective D.β ∧ Function.Bijective ψ ∧
      autOn E W ⊔ autOn (baum T) W = Subgroup.normalizer (autOn E W : Set (MulAut ↥W)) ∧
      autOn (thompsonJ T) W = autOn (baum T) W ∧ Nat.card ↥(autOn (baum T) W) = 2 ∧
      IsMaxSwapGroup (((autOn (baum T) W).subgroupOf
        (Subgroup.normalizer (autOn E W : Set (MulAut ↥W)))).map ψ) := by
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
  have hJW : thompsonJ T ≤ Subgroup.normalizer (W : Set Γ) :=
    hJ.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 E)
  have hBW : baum T ≤ Subgroup.normalizer (W : Set Γ) :=
    hBN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 E)
  have hT2 : IsPGroup 2 ↥T := hT.2.1
  have hBT : baum T ≤ T := inf_le_left
  have hB2 : IsPGroup 2 ↥(baum T) := hT2.to_le hBT
  have hnat : IsNatAlt E W 3 := by
    have := isNatAlt_of_isBTBlock hG hT hE hn
    rw [blockW_eq_pCoreOf hE] at this
    exact this
  obtain ⟨D⟩ := nonempty_altNatData hWe hEW hperf hnat
  have hodd : Odd 3 := by decide
  have hE'card : Nat.card ↥(autOn E W) = 3 := by
    rw [Nat.card_congr D.θ.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  have hfixE : fixV (autOn E W) = ⊥ := by
    have hodd' : Odd (Nat.card ↥(autOn E W)) := by rw [hE'card]; decide
    have h := (isCompl_fixV_commV_of_odd (autOn E W) hodd' hW2).inf_eq_bot
    rwa [D.comm_top, inf_top_eq] at h
  have hβinj : Function.Injective D.β := by
    rw [injective_iff_map_eq_one]
    intro w hw
    have := (D.ker_iff hodd (le_refl 3) w).mp hw
    rw [hfixE, Subgroup.mem_bot] at this
    exact this
  have hβbij : Function.Bijective D.β := ⟨hβinj, D.surj⟩
  have hWcard : Nat.card ↥W = 4 := by
    rw [Nat.card_congr (Equiv.ofBijective D.β hβbij)]
    exact card_coreMod_three'
  have hrk : rk ↥W = 2 := by
    have h := card_eq_two_pow_rk hW2
    rw [hWcard] at h
    have h2 : (2 : ℕ) ^ rk ↥W = 2 ^ 2 := by
      rw [← h]
      norm_num
    exact Nat.pow_right_injective le_rfl h2
  have hautcard : Nat.card (MulAut ↥W) = 6 := by
    rw [card_mulAut_eq hW2, hrk]
    simp [Fin.prod_univ_two]
  let βe : ↥W ≃* ↥(coreMod 3) := MulEquiv.ofBijective D.β hβbij
  let Φ : Equiv.Perm (Fin 3) →* MulAut ↥W :=
    (MulAut.congr βe.symm).toMonoidHom.comp (coreAct 3)
  have hΦβ : ∀ (σ : Equiv.Perm (Fin 3)) (w : ↥W), D.β (Φ σ w) = coreAct 3 σ (D.β w) := by
    intro σ w
    show βe (βe.symm (coreAct 3 σ (βe w))) = _
    rw [MulEquiv.apply_symm_apply]
    rfl
  have hΦinj : Function.Injective Φ :=
    (MulAut.congr βe.symm).injective.comp (coreAct_injective (le_refl 3))
  have hperm3 : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    rfl
  have hΦbij : Function.Bijective Φ :=
    ⟨hΦinj, by
      have := hΦinj.bijective_of_nat_card_le (by rw [hautcard, hperm3])
      exact this.2⟩
  let Φe : Equiv.Perm (Fin 3) ≃* MulAut ↥W := MulEquiv.ofBijective Φ hΦbij
  have hind : (autOn E W).index = 2 := by
    have h1 := Subgroup.card_mul_index (autOn E W)
    rw [hE'card, hautcard] at h1
    omega
  have hnorm : (autOn E W).Normal := Subgroup.normal_of_index_eq_two hind
  have hNtop : Subgroup.normalizer (autOn E W : Set (MulAut ↥W)) = ⊤ :=
    @Subgroup.normalizer_eq_top _ _ (autOn E W) hnorm
  let ψ : ↥(Subgroup.normalizer (autOn E W : Set (MulAut ↥W))) →* Equiv.Perm (Fin 3) :=
    Φe.symm.toMonoidHom.comp (Subgroup.normalizer (autOn E W : Set (MulAut ↥W))).subtype
  have hψβ : ∀ (x : ↥(Subgroup.normalizer (autOn E W : Set (MulAut ↥W)))) (w : ↥W),
      D.β ((x : MulAut ↥W) w) = coreAct 3 (ψ x) (D.β w) := by
    intro x w
    have hx : Φ (ψ x) = (x : MulAut ↥W) := Φe.apply_symm_apply (x : MulAut ↥W)
    rw [← hΦβ (ψ x) w, hx]
  have hψinj : Function.Injective ψ := fun a b h =>
    Subtype.ext (Φe.symm.injective h)
  have hψsurj : Function.Surjective ψ := fun σ =>
    ⟨⟨Φ σ, by rw [hNtop]; exact Subgroup.mem_top _⟩, Φe.symm_apply_apply σ⟩
  have hcard2 : ∀ X : Subgroup (MulAut ↥W), IsPGroup 2 ↥X → Nat.card ↥X ≤ 2 := by
    intro X hX
    have hdvd : Nat.card ↥X ∣ 2 ^ 1 * 3 := by
      have := Subgroup.card_subgroup_dvd_card X
      rwa [hautcard] at this
    have := card_le_of_isPGroup_of_dvd hX (n := 1) (m := 3) (by decide) hdvd
    simpa using this
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
  obtain ⟨A₀, hA₀, hA₀c⟩ := hB
  have hA₀N : A₀ ≤ Subgroup.normalizer (W : Set Γ) := (B6.le_thompsonJ hA₀).trans hJW
  have hA₀ne : autOn A₀ W ≠ ⊥ := autOn_ne_bot_of_not_le_centralizer hA₀N hA₀c
  have hA₀J : autOn A₀ W ≤ autOn (thompsonJ T) W := autOn_le_autOn W (B6.le_thompsonJ hA₀)
  have hJB' : autOn (thompsonJ T) W ≤ autOn (baum T) W := autOn_le_autOn W hJB
  have hBcard : Nat.card ↥(autOn (baum T) W) ≤ 2 := hcard2 _ (isPGroup_autOn hB2 hBW)
  have hA₀card : 2 ≤ Nat.card ↥(autOn A₀ W) := by
    have := (Subgroup.one_lt_card_iff_ne_bot _).mpr hA₀ne
    omega
  have hJeq : autOn (thompsonJ T) W = autOn (baum T) W :=
    Subgroup.eq_of_le_of_card_ge hJB' (by
      have := Subgroup.card_le_of_le hA₀J
      omega)
  have hB2card : Nat.card ↥(autOn (baum T) W) = 2 := by
    have := Subgroup.card_le_of_le (hA₀J.trans hJB')
    omega
  have hsup : autOn E W ⊔ autOn (baum T) W = Subgroup.normalizer (autOn E W : Set (MulAut ↥W)) := by
    rw [hNtop]
    have h3 : 3 ∣ Nat.card ↥(autOn E W ⊔ autOn (baum T) W) := by
      rw [← hE'card]
      exact Subgroup.card_dvd_of_le le_sup_left
    have h2 : 2 ∣ Nat.card ↥(autOn E W ⊔ autOn (baum T) W) := by
      rw [← hB2card]
      exact Subgroup.card_dvd_of_le le_sup_right
    have h6' : 6 ∣ Nat.card ↥(autOn E W ⊔ autOn (baum T) W) :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 3 2) h3 h2
    have hd : Nat.card ↥(autOn E W ⊔ autOn (baum T) W) ∣ 6 := by
      have := Subgroup.card_subgroup_dvd_card (autOn E W ⊔ autOn (baum T) W)
      rwa [hautcard] at this
    exact Subgroup.card_eq_iff_eq_top _ |>.mp (by rw [hautcard]; exact Nat.dvd_antisymm hd h6')
  have hBN' : autOn (baum T) W ≤ Subgroup.normalizer (autOn E W : Set (MulAut ↥W)) :=
    autOn_le_normalizer_autOn hBW hBN
  set Y : Subgroup (Equiv.Perm (Fin 3)) := ((autOn (baum T) W).subgroupOf
    (Subgroup.normalizer (autOn E W : Set (MulAut ↥W)))).map ψ with hYdef
  have hY : Nat.card ↥Y = 2 := by
    rw [hYdef, Subgroup.card_map_of_injective hψinj, ← hB2card]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBN').toEquiv
  obtain ⟨⟨t, htY⟩, htne⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
    ((Subgroup.one_lt_card_iff_ne_bot _).mp (by omega : 1 < Nat.card ↥Y))
  have ht1 : t ≠ 1 := fun h => htne (Subtype.ext (by simpa using h))
  have ht2 : t ^ 2 = 1 := by
    have := pow_card_eq_one' (G := ↥Y) (x := ⟨t, htY⟩)
    rw [hY] at this
    exact congrArg Subtype.val this
  have htswap : t.IsSwap := isSwap_of_sq_eq_one_fin_three t ht1 ht2
  have hord : orderOf t = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime ht2 ht1
  have hYeq : Y = Subgroup.closure {t} := by
    rw [← Subgroup.zpowers_eq_closure]
    refine (Subgroup.eq_of_le_of_card_ge ?_ ?_).symm
    · rw [Subgroup.zpowers_le]
      exact htY
    · rw [Nat.card_zpowers, hord, hY]
  have hmax : IsMaxSwapGroup Y :=
    ⟨{t}, fun s hs => by rw [Set.mem_singleton_iff] at hs; exact hs ▸ htswap,
      fun s hs s' hs' => by rw [Set.mem_singleton_iff] at hs hs'; rw [hs, hs'],
      by rw [Set.ncard_singleton], hYeq⟩
  exact ⟨D, ψ, hψβ, hβbij, ⟨hψinj, hψsurj⟩, hsup, hJeq, hB2card, hmax⟩

theorem block_structure_symm (hG : CharTwo G) (hT : IsSylowOf 2 T G) (hE : IsBTBlock G T E)
    {m : ℕ} (hm : 1 ≤ m) (hn : IsNaturalAltModule ↥E m) {W : Subgroup Γ}
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
  rcases Nat.lt_or_ge m 2 with hm2 | hm2
  · obtain rfl : m = 1 := by omega
    obtain ⟨D, ψ, h1, h2, h3, h4, h5, h6, h7⟩ := block_structure_three hG hT hE hn hWE hWe
    exact ⟨D, ψ, h1, h2, h3, h4, h5, 1, le_rfl, by norm_num, h7, h6, fun _ => h7⟩
  · exact block_structure_alt hG hT hE hm2 hn hWE hWe

end Finite

end CFSG.CGT.PushingUpLit.BHS6
