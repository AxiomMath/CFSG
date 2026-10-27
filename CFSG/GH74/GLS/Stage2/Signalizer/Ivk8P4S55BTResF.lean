module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTResC3
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTResE
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTResL2b
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTResHH2
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTL2Out
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55L2Core
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55E1All
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTLinkZ

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.ABGLocalTools

theorem isSolvable_L2_of_card_three {F : Type} [Field F] [Finite F] (h3 : Nat.card F = 3) :
    Group.IsSolvable (IVK.L2 F) := by
  have := CFSG.GH74.GLS.IVK.GHInv.isSolvable_sl2_of_card_three h3
  have : Group.IsSolvable (GorensteinWalter.PSL2 F) :=
    Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective _)
  exact Group.isSolvable_of_surjective (f := (IVK.L2.equivPSL F).symm.toMonoidHom)
    (IVK.L2.equivPSL F).symm.surjective

theorem three_lt_card_of_quasisimple {A : Type} [Group A] {J : Subgroup A}
    (hJ : IsQuasisimple ↥J) {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F))
    (e : (↥J ⧸ center ↥J) ≃* IVK.L2 F) : 3 < Nat.card F := by
  have h1 : 1 < Nat.card F := Finite.one_lt_card
  have h3 : Nat.card F ≠ 3 := by
    intro h3
    have := isSolvable_L2_of_card_three h3
    have hsol : Group.IsSolvable (↥J ⧸ center ↥J) :=
      Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
    have := hJ.2.1
    obtain ⟨a, b, hab⟩ := hJ.2.2
    exact hab ((IsSimpleGroup.comm_iff_isSolvable.mpr hsol) a b)
  obtain ⟨k, hk⟩ := hodd
  omega

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S T Tstar : Subgroup G} {p : ℕ}
  {H P : Subgroup G} {g : G} {X Y : Subgroup G} {t : G} {q : ℕ} {I Q₁ : Subgroup G}


theorem false_of_resB_l2 (hL31 : Lemma31Narrow) (h : Cfg55E G z k S T Tstar p H P g X Y)
    (hd : Data5A2 z k S T Tstar p H P t q I Q₁) {J : Subgroup (HBar H)}
    (hB : BridgeB k p H P g J) (hIJ : barIn H I ≤ centralizer (J : Set (HBar H)))
    (hDS : ∀ {w : G}, (w = z ∨ w = t) → ∀ {W : Subgroup (HBar H)},
      W ≤ centralizer (barIn H (zpowers w) : Set (HBar H)) →
      W ≤ centralizer (barIn H I : Set (HBar H)) → Group.IsSolvable ↥W)
    (hL2 : IVK.IsL2 (↥J ⧸ center ↥J) Odd) : False := by
  obtain ⟨Γ, _, _, V, _, _, _, ρ, K, a, P', hM, -, hL⟩ := hB
  have := hM.normal
  have hq := hM.quasi
  have hJ : IsComponent J := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hJ, _⟩ := hL
    exact hJ
  have hZJ := odd_card_center hL31 h hd hJ hIJ
  have hZK := LinkB.odd_center hq hL hZJ
  obtain ⟨e, ψ, hψ, hψγ, hψJ⟩ := exists_actUK hL31 h hd hJ hIJ hq hL
  obtain ⟨F, _, _, hFodd, ⟨eJ⟩⟩ := hL2
  set eK : (↥K ⧸ center ↥K) ≃* IVK.L2 F := e.symm.trans eJ with heK
  have hF3 := three_lt_card_of_quasisimple hJ.1 hFodd eJ
  obtain ⟨r, f, hr, hf1, hrf, hlie⟩ :=
    Prop28.lieModel_of_isL2 hF3 ⟨F, inferInstance, inferInstance, rfl, ⟨eK⟩⟩
  have hr2 : r ≠ 2 := by
    rintro rfl
    rw [← hrf] at hFodd
    exact (Nat.not_even_iff_odd.mpr hFodd) ((Nat.even_pow' (by omega)).mpr even_two)
  by_cases hrp : r = p
  · subst hrp
    have : Fact r.Prime := ⟨hr⟩
    by_cases hW : innerPart (K := K) P' = ⊥
    · exact false_of_innerPart_eq_bot hM (outerFalseNS_l2 r f hr hr2 hf1 _ hlie) hW
    have hbord : orderOf (bAut hM.normal a) = r := by
      rw [bAut_eq_actYHom]
      exact orderOf_eq_prime hM.actYHom_pow hM.actYHom_ne_one
    by_cases h9 : Nat.card F = 9
    · have hr3 : r = 3 := by
        have hdvd : r ∣ 3 ^ 2 := by
          rw [show (3 : ℕ) ^ 2 = r ^ f by rw [hrf, h9]; norm_num]
          exact dvd_pow_self r (by omega)
        exact (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp (hr.dvd_of_dvd_pow hdvd)
      subst hr3
      refine hM.false_of_hhobsAt (r := 2) (fun _ h2 => ?_) (ResHH.hhobsAt_l2_nine h9 eK hbord)
      exact (Nat.not_even_iff_odd.mpr hZK) (even_iff_two_dvd.mpr h2)
    have hUH := U_le_H h hd.u
    obtain ⟨u₀, hu₀U, hu₀1, hu₀J⟩ := exists_U_mem_J hL31 h hd hJ hIJ
    set u₀' : ↥(L52Two.U4 z t) := ⟨u₀, hu₀U⟩ with hu₀'
    have hu₀'1 : u₀' ≠ 1 := by
      intro h1
      apply hu₀1
      have h2 : (u₀ : G) = 1 := congrArg Subtype.val h1
      rw [show u₀ = 1 from Subtype.ext h2, map_one]
    have hd₀i : ψ u₀' ∈ (MulAut.conj : (↥K ⧸ center ↥K) →* MulAut (↥K ⧸ center ↥K)).range := by
      obtain ⟨hN, hψu⟩ := hψJ u₀'
      rw [hψu, actJ_of_mem J hu₀J]
      exact ⟨e _, (CFSG.ComponentClassification.OuterAutomorphisms.congr_conj e _).symm⟩
    obtain ⟨w, hw, hwU, hwne⟩ := exists_zt_ne hd (u₀ : G)
    set w' : ↥(L52Two.U4 z t) := ⟨w, hwU⟩ with hw'
    have hw'1 : w' ≠ 1 := by
      intro h1
      have h2 : w = 1 := congrArg Subtype.val h1
      rcases hw with rfl | rfl
      · exact hd.u.udata.z_ne h2
      · exact hd.u.udata.t_ne h2
    have hww₀ : w' ≠ u₀' := fun h1 => hwne (congrArg Subtype.val h1)
    have := hd.u.four.1
    have hsq : ∀ u : ↥(L52Two.U4 z t), u * u = 1 := fun u => by
      apply Subtype.ext
      rw [Subgroup.coe_mul, ← sq]
      exact elemPow_eq_one_of_isElementaryAbelian (u : G) u.2
    have hns := ResL2.not_isSolvable_fixed eK hrf.symm hr2 h9 hW
      (isPGroup_innerPart (center_quot_eq_bot hq) hM.pgrp) (D := ψ.range)
      (by
        rintro _ ⟨u, rfl⟩
        rw [← map_mul, hsq, map_one])
      (by
        rintro _ ⟨u, rfl⟩ y hy
        obtain ⟨γ, hγ, hψu⟩ := hψγ u
        rw [hψu]
        exact actYHom_mem_innerPart hγ hy)
      ⟨u₀', rfl⟩ (fun h1 => hu₀'1 (hψ (h1.trans (map_one ψ).symm))) hd₀i ⟨w', rfl⟩
      (fun h1 => hw'1 (hψ (h1.trans (map_one ψ).symm))) (fun h1 => hww₀ (hψ h1))
    obtain ⟨hN, hψw⟩ := hψJ w'
    rw [hψw] at hns
    have hx2 : QuotientGroup.mk' (pPrimeCore 2 ↥H) ⟨w, hUH hwU⟩ *
        QuotientGroup.mk' (pPrimeCore 2 ↥H) ⟨w, hUH hwU⟩ = 1 := by
      rw [← map_mul]
      have h1 : (⟨w, hUH hwU⟩ : ↥H) * ⟨w, hUH hwU⟩ = 1 := by
        have h0 : ((w' * w' : ↥(L52Two.U4 z t)) : G) = 1 := congrArg Subtype.val (hsq w')
        exact Subtype.ext h0
      rw [h1, map_one]
    apply not_isSolvable_inf_centralizer J e hN hx2 hZJ hns
    obtain ⟨h1, h2⟩ := inf_centralizer_le hIJ (hUH hwU)
    exact hDS hw h1 h2
  · obtain ⟨-, F₀, _, _, -, -, h2Z⟩ :=
      stepL2_core crossE1_all hM.toHyp89 hr hr2 hrp ⟨f, hf1, hlie⟩
    exact (Nat.not_even_iff_odd.mpr hZK) (even_iff_two_dvd.mpr h2Z)

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
