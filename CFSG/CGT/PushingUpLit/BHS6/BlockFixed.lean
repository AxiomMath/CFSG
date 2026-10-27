module

public import CFSG.CGT.PushingUpLit.BHS6.BlockModule
public import CFSG.CGT.PushingUpLit.BHS6.FaithfulSL
public import CFSG.Quasithin.EmptyFaithful.S145Cop

public section

namespace CFSG.CGT.PushingUpLit.BHS6

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS
open scoped commutatorElement

variable {Γ : Type} [Group Γ]

omit [Group Γ] in
theorem isPGroup_autOn [Group Γ] {V J : Subgroup Γ} (hJ : IsPGroup 2 ↥J)
    (hJV : J ≤ Subgroup.normalizer (V : Set Γ)) : IsPGroup 2 ↥(autOn J V) :=
  CFSG.Quasithin.AutOn.isPGroup_autOn hJ

omit [Group Γ] in
theorem autOn_le_normalizer_autOn [Group Γ] {V X E : Subgroup Γ}
    (hXV : X ≤ Subgroup.normalizer (V : Set Γ)) (hXE : X ≤ Subgroup.normalizer (E : Set Γ)) :
    autOn X V ≤ Subgroup.normalizer (autOn E V : Set (MulAut ↥V)) :=
  CFSG.Quasithin.AutOn.autOn_le_normalizer_autOn hXE

section Finite

variable [Finite Γ]

theorem card_le_relIndex_mul_card_of_isMaxElemAbelian {S A V : Subgroup Γ}
    (hA : IsMaxElemAbelian S A) (hV : IsElemAbelian 2 V) (hVS : V ≤ S)
    (hAV : A ≤ Subgroup.normalizer (V : Set Γ)) :
    Nat.card V ≤ (A ⊓ Subgroup.centralizer (V : Set Γ)).relIndex A *
      Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set Γ)) := by
  by_cases hc : A ≤ Subgroup.centralizer (V : Set Γ)
  · have h1 : (A ⊓ Subgroup.centralizer (V : Set Γ)).relIndex A = 1 := by
      rw [inf_eq_left.mpr hc]
      exact Subgroup.relIndex_self A
    have h2 : V ⊓ Subgroup.centralizer (A : Set Γ) = V := by
      refine inf_eq_left.mpr fun v hv => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact (Subgroup.mem_centralizer_iff.mp (hc ha) v hv).symm
    rw [h1, h2, one_mul]
  · have hOff : IsOffG V A :=
      isOffG_of_isMaxElemAbelian (S := A ⊔ V) hV le_sup_right
        (sup_le hAV Subgroup.le_normalizer)
        ⟨le_sup_left, hA.2.1, fun B hB hBe => hA.2.2 B (hB.trans (sup_le hA.1 hVS)) hBe⟩ hc
    have h1 := hOff.2.2.2.2 ⊥ bot_le
    have h2 : V ⊓ Subgroup.centralizer ((⊥ : Subgroup Γ) : Set Γ) = V := by
      refine inf_eq_left.mpr fun v hv => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [SetLike.mem_coe, Subgroup.mem_bot] at hh
      subst hh
      simp
    unfold wtG at h1
    rw [bot_inf_eq, Subgroup.relIndex_self, h2, one_mul] at h1
    exact h1

theorem exists_ne_one_fixed_of_isPGroup {W P : Subgroup Γ}
    (hW : IsPGroup 2 ↥W) (hWne : W ≠ ⊥) (hP : IsPGroup 2 ↥P)
    (hPW : P ≤ Subgroup.normalizer (W : Set Γ)) :
    ∃ w ∈ W, w ≠ 1 ∧ ∀ p ∈ P, p * w * p⁻¹ = w := by
  classical
  let _ : MulAction ↥P ↥W := MulAction.compHom ↥W (actOn W P hPW)
  have hsm : ∀ (p : ↥P) (w : ↥W), ((p • w : ↥W) : Γ) = (p : Γ) * w * (p : Γ)⁻¹ := fun p w =>
    actOn_apply_coe hPW p w
  have hmod := hP.card_modEq_card_fixedPoints ↥W
  have h2 : 2 ∣ Nat.card ↥W := by
    have : Nontrivial ↥W := (Subgroup.nontrivial_iff_ne_bot W).mpr hWne
    obtain ⟨n, hn, hcard⟩ := (hW.nontrivial_iff_card).mp inferInstance
    rw [hcard]
    exact dvd_pow_self 2 hn.ne'
  have h3 : 2 ∣ Nat.card (MulAction.fixedPoints ↥P ↥W) := by
    have := (Nat.modEq_zero_iff_dvd).mpr h2
    exact (Nat.modEq_zero_iff_dvd).mp (hmod.symm.trans this)
  have h1mem : (1 : ↥W) ∈ MulAction.fixedPoints ↥P ↥W := fun p => map_one (actOn W P hPW p)
  have : Nonempty ↑(MulAction.fixedPoints ↥P ↥W) := ⟨⟨1, h1mem⟩⟩
  have hgt : 1 < Nat.card (MulAction.fixedPoints ↥P ↥W) := by
    have hpos : 0 < Nat.card (MulAction.fixedPoints ↥P ↥W) := Nat.card_pos
    have := Nat.le_of_dvd hpos h3
    omega
  have hnt : Nontrivial ↑(MulAction.fixedPoints ↥P ↥W) := Finite.one_lt_card_iff_nontrivial.mp hgt
  obtain ⟨⟨w, hw⟩, hwne⟩ := exists_ne (⟨1, h1mem⟩ : ↑(MulAction.fixedPoints ↥P ↥W))
  refine ⟨(w : Γ), w.2, ?_, fun p hp => ?_⟩
  · intro h
    apply hwne
    apply Subtype.ext
    apply Subtype.ext
    simpa using h
  · have := congrArg (fun x : ↥W => (x : Γ)) (hw ⟨p, hp⟩)
    rw [hsm] at this
    exact this

variable {G T E S : Subgroup Γ}

theorem pCoreOf_le_sylow (hG : CharTwo G) (hT : IsSylowOf 2 T G) (hE : IsBTBlock G T E)
    (hS : IsSylowOf 2 S G) : pCoreOf 2 E ≤ S := by
  have h1 := (six_four_a hG hT hE).2
  rw [blockW_eq_pCoreOf hE] at h1
  exact (h1.trans (omegaOneCenter_le_pCoreOf G)).trans
    (isSylowTwoOf_of_isSylowOf hS).pCoreOf_le

theorem mem_omegaOneCenter_thompsonJ_of_centralizes {S : Subgroup Γ} {w : Γ} (hwS : w ∈ S)
    (hw2 : w ^ 2 = 1)
    (hc : ∀ A, IsMaxElemAbelian S A → ∀ a ∈ A, a * w = w * a) :
    w ∈ omegaOneCenterOf (thompsonJ S) := by
  have hz : IsElemAbelian 2 (Subgroup.zpowers w) := by
    refine isElemAbelian_of_forall' (fun x hx y hy => ?_) (fun x hx => ?_)
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact (zpow_add w i j).symm.trans ((add_comm i j ▸ zpow_add w j i))
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      rw [← zpow_natCast (w ^ i) 2, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hw2, one_zpow]
  have hwA : ∀ A, IsMaxElemAbelian S A → w ∈ A := by
    intro A hA
    have hcomm : ∀ a ∈ A, ∀ y ∈ Subgroup.zpowers w, a * y = y * a := by
      intro a ha y hy
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact ((show Commute a w from hc A hA a ha).zpow_right i).eq
    have hel := isElemAbelian_sup' hA.2.1 hz hcomm
    have hle : Nat.card ↥(A ⊔ Subgroup.zpowers w) ≤ Nat.card ↥A :=
      hA.2.2 _ (sup_le hA.1 ((Subgroup.zpowers_le).mpr hwS)) hel
    have heq : A ⊔ Subgroup.zpowers w = A :=
      (Subgroup.eq_of_le_of_card_ge le_sup_left hle).symm
    exact heq ▸ (le_sup_right : Subgroup.zpowers w ≤ _) (Subgroup.mem_zpowers w)
  obtain ⟨A₀, hA₀⟩ := exists_isMaxElemAbelian S
  have hwJ : w ∈ thompsonJ S := B6.le_thompsonJ hA₀ (hwA A₀ hA₀)
  have hwC : w ∈ Subgroup.centralizer (thompsonJ S : Set Γ) := by
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    have hJ : thompsonJ S ≤ Subgroup.centralizer ({w} : Set Γ) :=
      iSup_le fun A => iSup_le fun hA a ha => by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact hc A hA a ha
    exact Subgroup.mem_centralizer_singleton_iff.mp (hJ hj)
  exact Subgroup.subset_closure ⟨⟨hwJ, hwC⟩, hw2⟩

theorem exists_fixed_noncentral_sl (hG : CharTwo G) (hT : IsSylowOf 2 T G)
    (hE : IsBTBlock G T E) {n : ℕ} (hn2 : 2 ≤ n) (hn : IsNaturalSLTwoModule ↥E n)
    (hS : IsSylowOf 2 S G) (hJ : thompsonJ S ≤ Subgroup.normalizer (E : Set Γ))
    (hB : ∃ A, IsMaxElemAbelian S A ∧ ¬ A ≤ Subgroup.centralizer (pCoreOf 2 E : Set Γ)) :
    ∃ w ∈ pCoreOf 2 E, w ∉ Subgroup.centralizer (E : Set Γ) ∧
      ∀ A, IsMaxElemAbelian S A → ∀ a ∈ A, a * w = w * a := by
  classical
  set W : Subgroup Γ := pCoreOf 2 E with hWdef
  have hWe : IsElemAbelian 2 W := isElemAbelian_of_forall' hE.elemAbelian.1 hE.elemAbelian.2
  let _ : CommGroup ↥W := commGroupOfElemAbelian hWe
  have hEW : E ≤ Subgroup.normalizer (W : Set Γ) := le_normalizer_pCoreOf_self E
  have hperf : ⁅E, W⁆ = W := by rw [Subgroup.commutator_comm]; exact hE.perfect
  have hWS : W ≤ S := pCoreOf_le_sylow hG hT hE hS
  have hJW : thompsonJ S ≤ Subgroup.normalizer (W : Set Γ) :=
    hJ.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 E)
  have hS2 : IsPGroup 2 ↥S := hS.2.1
  have hJS : thompsonJ S ≤ S := iSup_le fun _ => iSup_le fun hA => hA.1
  have hJ2 : IsPGroup 2 ↥(thompsonJ S) := hS2.to_le hJS
  have hnat : IsNatSL E W n := by
    have := isNatSL_of_isBTBlock hG hT hE hn
    rwa [blockW_eq_pCoreOf hE] at this
  obtain ⟨D⟩ := nonempty_slNatData hWe hEW hperf hnat
  have hF : 2 ≤ Nat.card (GaloisField 2 n) := by
    rw [GaloisField.card 2 n (by omega)]
    exact Nat.le_self_pow (by omega) 2
  have hQ : IsPGroup 2 ↥(autOn (thompsonJ S) W) := isPGroup_autOn hJ2 hJW
  have hQN : autOn (thompsonJ S) W ≤ Subgroup.normalizer (autOn E W : Set (MulAut ↥W)) :=
    autOn_le_normalizer_autOn hJW hJ
  let 𝒜 : Set (Subgroup (MulAut ↥W)) :=
    {B | ∃ A, IsMaxElemAbelian S A ∧ ¬ A ≤ Subgroup.centralizer (W : Set Γ) ∧ B = autOn A W}
  have hne : 𝒜.Nonempty := by
    obtain ⟨A, hA, hAc⟩ := hB
    exact ⟨autOn A W, A, hA, hAc, rfl⟩
  have h𝒜 : ∀ B ∈ 𝒜, B ≤ autOn (thompsonJ S) W ∧ IsElemAbelian2 B ∧ B ≠ ⊥ ∧
      Nat.card ↥W ≤ Nat.card ↥B * Nat.card ↥(fixV B) := by
    rintro B ⟨A, hA, hAc, rfl⟩
    have hAJ : A ≤ thompsonJ S := B6.le_thompsonJ hA
    have hAN : A ≤ Subgroup.normalizer (W : Set Γ) := hAJ.trans hJW
    refine ⟨autOn_le_autOn W hAJ, isElemAbelian2_autOn hWe hA.2.1 hAN,
      autOn_ne_bot_of_not_le_centralizer hAN hAc, ?_⟩
    rw [card_autOn_eq_relIndex hAN, card_fixV_autOn_eq hWe hAN]
    exact card_le_relIndex_mul_card_of_isMaxElemAbelian hA hWe hWS hAN
  obtain ⟨U, -, -, hUeq, hnfix, -⟩ := sl_family D hF hQ hQN hne h𝒜
  obtain ⟨w, hwU, hwE⟩ := IsConcreteLE.not_le_iff_exists.mp hnfix
  refine ⟨(w : Γ), w.2, ?_, fun A hA a ha => ?_⟩
  · intro hc
    apply hwE
    rw [← fixOn, fixOn_eq hWe hEW, Subgroup.mem_subgroupOf]
    exact hc
  · by_cases hAc : A ≤ Subgroup.centralizer (W : Set Γ)
    · exact (Subgroup.mem_centralizer_iff.mp (hAc ha) (w : Γ) w.2).symm
    · have hAU : autOn A W = U := hUeq _ ⟨A, hA, hAc, rfl⟩
      have hAN : A ≤ Subgroup.normalizer (W : Set Γ) := (B6.le_thompsonJ hA).trans hJW
      have hw : w ∈ fixV (autOn A W) := by rw [hAU]; exact hwU
      have := fixOn_eq hWe hAN
      have hw' : w ∈ (Subgroup.centralizer (A : Set Γ)).subgroupOf W := by
        rw [← this]; exact hw
      exact Subgroup.mem_centralizer_iff.mp hw' a ha

omit [Finite Γ] in
theorem alt_commutator_ne_bot {W : Type} [CommGroup W] [Finite W] {E A : Subgroup (MulAut W)}
    {n : ℕ} (D : AltNatData E n) (hn : Odd n) (h5 : 5 ≤ n)
    (hAN : A ≤ Subgroup.normalizer (E : Set (MulAut W))) (hne : A ≠ ⊥) : ⁅E, A⁆ ≠ ⊥ := by
  intro h
  apply hne
  rw [eq_bot_iff]
  intro a ha
  rw [Subgroup.mem_bot]
  have hcomm : ∀ e ∈ E, a * e = e * a := fun e he => by
    have : ⁅e, a⁆ ∈ (⁅E, A⁆ : Subgroup (MulAut W)) := Subgroup.commutator_mem_commutator he ha
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this.symm
  have hpsi : D.psi hn h5 ⟨a, hAN ha⟩ = 1 := D.psi_eq_one_of_commute hn h5 hcomm
  exact D.eq_one_of_psi_eq_one hn h5 hpsi

theorem exists_fixed_noncentral_alt (hG : CharTwo G) (hT : IsSylowOf 2 T G)
    (hE : IsBTBlock G T E) {m : ℕ} (hm : 1 ≤ m) (hn : IsNaturalAltModule ↥E m)
    (hS : IsSylowOf 2 S G) (hJ : thompsonJ S ≤ Subgroup.normalizer (E : Set Γ))
    (hB : ∃ A, IsMaxElemAbelian S A ∧ ¬ A ≤ Subgroup.centralizer (pCoreOf 2 E : Set Γ)) :
    pCoreOf 2 E ⊓ Subgroup.centralizer (E : Set Γ) = ⊥ ∧
      ∃ w ∈ pCoreOf 2 E, w ∉ Subgroup.centralizer (E : Set Γ) ∧
        ∀ A, IsMaxElemAbelian S A → ∀ a ∈ A, a * w = w * a := by
  classical
  have hchar := charTwo_of_isBTBlock hG hT hE
  set W : Subgroup Γ := pCoreOf 2 E with hWdef
  have hWe : IsElemAbelian 2 W := isElemAbelian_of_forall' hE.elemAbelian.1 hE.elemAbelian.2
  let _ : CommGroup ↥W := commGroupOfElemAbelian hWe
  have hV2 : ∀ v : ↥W, v ^ 2 = 1 := fun v => Subtype.ext (by simpa [sq] using hWe.2 v v.2)
  have hEW : E ≤ Subgroup.normalizer (W : Set Γ) := le_normalizer_pCoreOf_self E
  have hperf : ⁅E, W⁆ = W := by rw [Subgroup.commutator_comm]; exact hE.perfect
  have hWS : W ≤ S := pCoreOf_le_sylow hG hT hE hS
  have hJW : thompsonJ S ≤ Subgroup.normalizer (W : Set Γ) :=
    hJ.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 E)
  have hS2 : IsPGroup 2 ↥S := hS.2.1
  have hJS : thompsonJ S ≤ S := iSup_le fun _ => iSup_le fun hA => hA.1
  have hJ2 : IsPGroup 2 ↥(thompsonJ S) := hS2.to_le hJS
  have hnat : IsNatAlt E W (2 * m + 1) := by
    have := isNatAlt_of_isBTBlock hG hT hE hn
    rwa [blockW_eq_pCoreOf hE] at this
  obtain ⟨D⟩ := nonempty_altNatData hWe hEW hperf hnat
  have hfixbot : fixV (autOn E W) = ⊥ := by
    by_cases hm2 : 2 ≤ m
    · obtain ⟨A₁, hA₁, hA₁c⟩ := hB
      have hAJ : A₁ ≤ thompsonJ S := B6.le_thompsonJ hA₁
      have hAN : A₁ ≤ Subgroup.normalizer (W : Set Γ) := hAJ.trans hJW
      have hAN' : autOn A₁ W ≤ Subgroup.normalizer (autOn E W : Set (MulAut ↥W)) :=
        autOn_le_normalizer_autOn hAN (hAJ.trans hJ)
      have hAw : Nat.card ↥W ≤ Nat.card ↥(autOn A₁ W) * Nat.card ↥(fixV (autOn A₁ W)) := by
        rw [card_autOn_eq_relIndex hAN, card_fixV_autOn_eq hWe hAN]
        exact card_le_relIndex_mul_card_of_isMaxElemAbelian hA₁ hWe hWS hAN
      have hodd : Odd (2 * m + 1) := ⟨m, rfl⟩
      have hEA := alt_commutator_ne_bot D hodd (by omega) hAN'
        (autOn_ne_bot_of_not_le_centralizer hAN hA₁c)
      exact (alt_core hV2 hodd (by omega) D hAN' (isElemAbelian2_autOn hWe hA₁.2.1 hAN) hAw
        hEA).1
    · have hm1 : m = 1 := by omega
      subst hm1
      have hcard : Nat.card ↥(autOn E W) = 3 := by
        rw [Nat.card_congr D.θ.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
        simp [Nat.factorial]
      have hodd : Odd (Nat.card ↥(autOn E W)) := by rw [hcard]; decide
      have h := (isCompl_fixV_commV_of_odd (autOn E W) hodd hV2).inf_eq_bot
      rwa [D.comm_top, inf_top_eq] at h
  have hbot : W ⊓ Subgroup.centralizer (E : Set Γ) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h1 : (⟨x, hx.1⟩ : ↥W) ∈ fixV (autOn E W) := by
      rw [← fixOn, fixOn_eq hWe hEW, Subgroup.mem_subgroupOf]
      exact hx.2
    rw [hfixbot, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val h1)
  refine ⟨hbot, ?_⟩
  obtain ⟨w, hwW, hw1, hwfix⟩ := exists_ne_one_fixed_of_isPGroup
    (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 E) (pCoreOf_ne_bot hE hchar) hJ2 hJW
  refine ⟨w, hwW, fun hc => hw1 (Subgroup.mem_bot.mp (hbot ▸ ⟨hwW, hc⟩)), fun A hA a ha => ?_⟩
  have := hwfix a (B6.le_thompsonJ hA ha)
  calc a * w = (a * w * a⁻¹) * a := by group
    _ = w * a := by rw [this]

theorem exists_fixed_noncentral (hG : CharTwo G) (hT : IsSylowOf 2 T G) (hE : IsBTBlock G T E)
    (hS : IsSylowOf 2 S G) (hJ : thompsonJ S ≤ Subgroup.normalizer (E : Set Γ)) :
    ∃ w ∈ pCoreOf 2 E, w ∉ Subgroup.centralizer (E : Set Γ) ∧
      w ∈ omegaOneCenterOf (thompsonJ S) := by
  classical
  have hchar := charTwo_of_isBTBlock hG hT hE
  have hmk : ∀ w ∈ pCoreOf 2 E, (∀ A, IsMaxElemAbelian S A → ∀ a ∈ A, a * w = w * a) →
      w ∈ omegaOneCenterOf (thompsonJ S) := fun w hw hc =>
    mem_omegaOneCenter_thompsonJ_of_centralizes (pCoreOf_le_sylow hG hT hE hS hw)
      (hE.elemAbelian.2 w hw) hc
  by_cases hB : ∃ A, IsMaxElemAbelian S A ∧ ¬ A ≤ Subgroup.centralizer (pCoreOf 2 E : Set Γ)
  · rcases hE.type with ⟨n, hn2, hn⟩ | ⟨m, hm, hn⟩
    · obtain ⟨w, hwW, hwE, hwc⟩ := exists_fixed_noncentral_sl hG hT hE hn2 hn hS hJ hB
      exact ⟨w, hwW, hwE, hmk w hwW hwc⟩
    · obtain ⟨-, w, hwW, hwE, hwc⟩ := exists_fixed_noncentral_alt hG hT hE hm hn hS hJ hB
      exact ⟨w, hwW, hwE, hmk w hwW hwc⟩
  · have hA : ∀ A, IsMaxElemAbelian S A → A ≤ Subgroup.centralizer (pCoreOf 2 E : Set Γ) := by
      intro A hAmax
      by_contra hAc
      exact hB ⟨A, hAmax, hAc⟩
    obtain ⟨w, hwW, hwE⟩ := IsConcreteLE.exists_of_lt (inf_centralizer_lt_pCoreOf hE hchar)
    refine ⟨w, hwW, fun hc => hwE ⟨hwW, hc⟩, hmk w hwW fun A hAmax a ha => ?_⟩
    exact (Subgroup.mem_centralizer_iff.mp (hA A hAmax ha) w hwW).symm

end Finite

end CFSG.CGT.PushingUpLit.BHS6
