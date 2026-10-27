module

public import CFSG.LargeExtraspecial.S7SevenMain

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions Equiv
open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6
open CFSG.LargeExtraspecial.S7 CFSG.LargeExtraspecial.OrthoF2 CFSG.Open

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

section Chain

variable (hCE : CentralExtInput.{u}) (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
  {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
  (hΩ : OmegaCase H C ht ht1 hVQ) (hN : Nbar S g t = zpowers t)
  (h6 : 6 ≤ finrank (ZMod 2) (Vt S g t))
  (hSC : ∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g → x * t * x⁻¹ = t)
include hCE H hNo C ht ht1 hVQ hΩ hN h6 hSC

theorem isolated_of_omegaCase_sc {x : S.O} (hx : x ∈ S.Mbar)
    (hcomm : x * t * x⁻¹ * t = t * (x * t * x⁻¹)) : x * t * x⁻¹ = t := by
  by_contra hne
  have h67 := orbit67_of_omegaCase hCE H hNo C hΩ h6
  obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp hx
  set E : S.Qt ≃ₗ[ZMod 2] S.Qt := (t : S.Qt ≃ₗ[ZMod 2] S.Qt) with hE
  set E₁ : S.Qt ≃ₗ[ZMod 2] S.Qt :=
    ((S.ρ k * t * (S.ρ k)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) with hE₁
  have hn := width_eq_finrank_of_omegaCase H hNo C ht ht1 hN hΩ
  obtain ⟨hcV, hfW⟩ := commSpace_t_eq H C ht ht1 hVQ
  have hWV : Wt S g t = Vt S g t := by
    have h1 := finrank_Wt (S := S) (g := g) (t := t)
    have h2 := S.finrank_Qt_eq_two_mul_width
    exact (Submodule.eq_of_le_of_finrank_le (Vt_le_Wt H ht1) (by omega)).symm
  obtain ⟨Q, -, -, -, -, hsing⟩ := hΩ.exists_form
  set U : Submodule (ZMod 2) (Vt S g t) := (commSpace E₁).comap (Vt S g t).subtype with hU
  have hanis : ∀ w ∈ U, Q w = 0 → w = 0 := by
    intro w hw hQw
    by_contra hw0
    have hwo := (hsing w hw0).mp hQw
    rw [mem_orbitOf_RmodN_iff H.conj_mem ht] at hwo
    obtain ⟨h, hh, hwh⟩ := exists_of_mem_orbit hwo H.conj_mem
    have hw' : (w : S.Qt) ∈ commSpace E₁ := hw
    rw [hE₁, S7.commSpace_conj] at hw'
    obtain ⟨v, hv, hvw⟩ := hw'
    have hmem : (((S.ρ k)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
        (S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹)) ∈ Vt S g t := by
      rw [← hwh, ← hvw, LinearEquiv.coe_coe, inv_apply_apply_O, ← hcV]
      exact hv
    exact hne (strongClosed_mul H hSC hh ⟨k, rfl⟩
      (conj_mem_Lbar_of_inv_apply_mem H ht h67 k h hmem))
  have hU2 := finrank_le_two_of_anisotropic Q hanis
  have hdU : finrank (ZMod 2) U = finrank (ZMod 2) ↥(Vt S g t ⊓ commSpace E₁) := by
    rw [← Submodule.finrank_map_subtype_eq, hU, Submodule.map_comap_subtype]
  have hd₁ : finrank (ZMod 2) (commSpace E₁) = finrank (ZMod 2) (Vt S g t) := by
    rw [hE₁, S7.commSpace_conj, LinearEquiv.finrank_map_eq, hcV]
  have hEE : ∀ v, E (E₁ v) = E₁ (E v) := by
    intro v
    have := congrArg (fun y : S.O => (y : S.Qt ≃ₗ[ZMod 2] S.Qt) v) hcomm
    simp only [coe_mul_apply] at this
    rw [hE, hE₁]
    simp only [coe_mul_apply]
    exact this.symm
  have hcomp : ((E : S.Qt →ₗ[ZMod 2] S.Qt) - 1).comp ((E₁ : S.Qt →ₗ[ZMod 2] S.Qt) - 1) =
      ((E₁ : S.Qt →ₗ[ZMod 2] S.Qt) - 1).comp ((E : S.Qt →ₗ[ZMod 2] S.Qt) - 1) := by
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, Module.End.one_apply,
      LinearEquiv.coe_coe, map_sub, hEE]
    abel
  have hmap : (commSpace E₁).map ((E : S.Qt →ₗ[ZMod 2] S.Qt) - 1) =
      (Vt S g t).map ((E₁ : S.Qt →ₗ[ZMod 2] S.Qt) - 1) := by
    rw [← hcV, commSpace, commSpace, ← LinearMap.range_comp, ← LinearMap.range_comp, hcomp]
  have hle : (Vt S g t).map ((E₁ : S.Qt →ₗ[ZMod 2] S.Qt) - 1) ≤ Vt S g t ⊓ commSpace E₁ := by
    rintro _ ⟨v, hv, rfl⟩
    refine ⟨?_, ⟨v, rfl⟩⟩
    rw [← hcV] at hv ⊢
    obtain ⟨w, rfl⟩ := mem_commSpace.mp hv
    refine mem_commSpace.mpr ⟨E₁ w - w, ?_⟩
    have hEE' : ∀ v, (t : S.Qt ≃ₗ[ZMod 2] S.Qt) (E₁ v) = E₁ ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) v) :=
      hEE
    simp only [LinearMap.sub_apply, Module.End.one_apply, LinearEquiv.coe_coe, map_sub, hEE']
  have hrk := S2.finrank_map_sub_one_add E (commSpace E₁)
  rw [hmap, hfW, hWV, inf_comm] at hrk
  have h3 := Submodule.finrank_mono hle
  omega

theorem timmesfeld_7_4_sc :
    (∀ y : S.Mbar, y * ⟨t, S.Lbar_le_Mbar g ht⟩ * y⁻¹ * (⟨t, S.Lbar_le_Mbar g ht⟩ : S.Mbar)⁻¹ ∈
      timmesfeldOddCore S.Mbar) ∧ timmesfeldOddCore S.Mbar ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set tM : S.Mbar := ⟨t, S.Lbar_le_Mbar g ht⟩ with htM
  have htt : t * t = 1 := mul_self_of_mem_Lbar S H.conj_mem ht
  have hto : orderOf tM = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact Subtype.ext htt)
      (fun h => ht1 (congrArg Subtype.val h))
  have hiso : ∀ y : S.Mbar, (y * tM * y⁻¹) * tM = tM * (y * tM * y⁻¹) →
      y * tM * y⁻¹ = tM := by
    intro y hy
    apply Subtype.ext
    have h1 : (y : S.O) * t * (y : S.O)⁻¹ * t = t * ((y : S.O) * t * (y : S.O)⁻¹) :=
      congrArg Subtype.val hy
    exact isolated_of_omegaCase_sc hCE H hNo C ht ht1 hVQ hΩ hN h6 hSC y.2 h1
  have hZ := CFSG.ShultStronglyClosedTI.minimalLocalFailure_isolated_commutators_mem_oddCore hto
    hiso
  refine ⟨hZ, fun h0 => ?_⟩
  have hcen : ∀ y ∈ S.Mbar, y * t * y⁻¹ = t := by
    intro y hy
    have h1 : (⟨y, hy⟩ : S.Mbar) * tM * (⟨y, hy⟩ : S.Mbar)⁻¹ * tM⁻¹ ∈
        timmesfeldOddCore S.Mbar := hZ ⟨y, hy⟩
    rw [h0, mem_bot] at h1
    have h2 : y * t * y⁻¹ * t⁻¹ = 1 := congrArg Subtype.val h1
    exact mul_inv_eq_one.mp h2
  have hP := Setting.s12_noNormalTwo_Mbar S (zpowers t) (zpowers_le.mpr (S.Lbar_le_Mbar g ht))
    (IsPGroup.of_card (n := 1) (by rw [card_zpowers_eq_two H ht ht1, pow_one]))
    (fun m hm => S4.mem_normalizer_of_conj_le fun p hp => by
      rcases (mem_zpowers_iff_of_mem_Lbar H ht).mp hp with hp1 | hp1
      · rw [hp1, mul_one, mul_inv_cancel]
        exact one_mem _
      · rw [hp1, hcen m hm]
        exact mem_zpowers t)
  apply ht1
  have : t ∈ zpowers t := mem_zpowers t
  rwa [hP, mem_bot] at this

section Seven

theorem card_Obar_eq_three_sc : Nat.card (Obar S) = 3 := by
  have hw := width_eq_finrank_of_omegaCase H hNo C ht ht1 hN hΩ
  have h3 := S5.card_oddCore_dvd_three H hNo C (by omega : 4 < S.width)
  obtain ⟨-, hO⟩ := timmesfeld_7_4_sc hCE H hNo C ht ht1 hVQ hΩ hN h6 hSC
  rw [card_Obar]
  rcases (Nat.dvd_prime Nat.prime_three).mp h3 with h | h
  · exact absurd (Subgroup.eq_bot_of_card_eq _ h) hO
  · exact h

theorem comm_mem_Obar_sc {x : S.O} (hx : x ∈ S.Mbar) : x * t * x⁻¹ * t⁻¹ ∈ Obar S := by
  obtain ⟨hZ, -⟩ := timmesfeld_7_4_sc hCE H hNo C ht ht1 hVQ hΩ hN h6 hSC
  exact ⟨_, hZ ⟨x, hx⟩, rfl⟩

theorem nonempty_mulEquiv_Mbar_sc : Nonempty (S.Mbar ≃* Perm (Fin 3) × Cbar S t) :=
  nonempty_mulEquiv_sigma_prod Obar_le_Mbar
    (card_Obar_eq_three_sc hCE H hNo C ht ht1 hVQ hΩ hN h6 hSC)
    (fun _ hx _ hy => conj_mem_Obar hx hy) (S.Lbar_le_Mbar g ht)
    (mul_self_of_mem_Lbar S H.conj_mem ht) ht1
    (fun _ hx => comm_mem_Obar_sc hCE H hNo C ht ht1 hVQ hΩ hN h6 hSC hx)
    (exists_conj_ne H ht ht1)

theorem exists_mul_Cbar_sc {x : S.O} (hx : x ∈ S.Mbar) :
    ∃ s ∈ Obar S ⊔ zpowers t, ∃ c ∈ Cbar S t, x = s * c :=
  exists_sigma_mul_cent Obar_le_Mbar (card_Obar_eq_three_sc hCE H hNo C ht ht1 hVQ hΩ hN h6 hSC)
    (fun _ hx _ hy => conj_mem_Obar hx hy) (S.Lbar_le_Mbar g ht)
    (mul_self_of_mem_Lbar S H.conj_mem ht) ht1
    (fun _ hx => comm_mem_Obar_sc hCE H hNo C ht ht1 hVQ hΩ hN h6 hSC hx)
    (exists_conj_ne H ht ht1) hx

theorem mem_Cbar_of_comm_sc {x : S.O} (hx : x ∈ S.Mbar) (hxt : x * t = t * x) :
    x ∈ Cbar S t ∨ t * x ∈ Cbar S t :=
  mem_cent_of_comm_t Obar_le_Mbar (card_Obar_eq_three_sc hCE H hNo C ht ht1 hVQ hΩ hN h6 hSC)
    (fun _ hx _ hy => conj_mem_Obar hx hy) (S.Lbar_le_Mbar g ht)
    (mul_self_of_mem_Lbar S H.conj_mem ht) ht1
    (fun _ hx => comm_mem_Obar_sc hCE H hNo C ht ht1 hVQ hΩ hN h6 hSC hx)
    (exists_conj_ne H ht ht1) hx hxt

theorem Cbar_inf_centralizer_eq_bot_sc :
    Cbar S t ⊓ centralizer (Rbar S g t : Set S.O) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set D' := Cbar S t ⊓ centralizer (Rbar S g t : Set S.O) with hD'
  have hD'M : D' ≤ S.Mbar := inf_le_left.trans Cbar_le_Mbar
  have hP : IsPGroup 2 D' := by
    rw [IsPGroup.iff_orderOf]
    intro d
    rcases Nat.eq_two_pow_or_exists_odd_prime_and_dvd (orderOf d) with ⟨k, hk⟩ | ⟨p, hp, hpd, hpo⟩
    · exact ⟨k, hk⟩
    · exfalso
      rw [← Subgroup.orderOf_coe] at hpd
      set e := (d : S.O) ^ (orderOf (d : S.O) / p) with he
      have hd0 : orderOf (d : S.O) ≠ 0 := (orderOf_pos _).ne'
      have heo : orderOf e = p := orderOf_pow_orderOf_div hd0 hpd
      have hdR : ∀ r ∈ Rbar S g t, r * d = d * r := fun r hr =>
        mem_centralizer_iff.mp (d.2.2) r hr
      have heR : ∀ r ∈ Rbar S g t, r * e = e * r := fun r hr =>
        (Commute.pow_right (hdR r hr) _).eq
      have hK := S5.timmesfeld_5_3 H hNo C (K := zpowers e)
        (zpowers_le.mpr (pow_mem (hD'M d.2) _)) inferInstance
        (by rw [Nat.card_zpowers, heo]; exact hpo)
        (fun h0 => by
          have : e = 1 := by
            have : e ∈ zpowers e := mem_zpowers e
            rwa [h0, mem_bot] at this
          rw [this, orderOf_one] at heo
          exact hp.one_lt.ne' heo.symm)
        (fun s hs x hx => by
          obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
          have := (Commute.zpow_right (heR s (Lbar_le_Rbar ht hs)) k).eq
          rw [this, mul_assoc, mul_inv_cancel, mul_one]
          exact zpow_mem (mem_zpowers e) k)
      apply hK.2
      rw [commutator_eq_bot_iff_le_centralizer, zpowers_le, mem_centralizer_iff]
      intro s hs
      exact heR s (Lbar_le_Rbar ht hs)
  have hnorm : S.Mbar ≤ normalizer (D' : Set S.O) := by
    intro x hx
    obtain ⟨σ, hσ, c', hc', rfl⟩ := exists_mul_Cbar_sc hCE H hNo C ht ht1 hVQ hΩ hN h6 hSC hx
    refine S4.mem_normalizer_of_conj_le fun p hp => ?_
    obtain ⟨hpC, hpR⟩ := hp
    set q := c' * p * c'⁻¹ with hq
    have hqC : q ∈ Cbar S t := mul_mem (mul_mem hc' hpC) (inv_mem hc')
    have hqR : q ∈ centralizer (Rbar S g t : Set S.O) := by
      rw [mem_centralizer_iff]
      intro r hr
      obtain ⟨κ', hκ'⟩ := MonoidHom.mem_range.mp (S.Mbar.inv_mem (Cbar_le_Mbar hc'))
      have hκt : S.ρ κ' * t = t * S.ρ κ' := by
        rw [hκ']
        have := comm_of_mem_Cbar hc'
        calc c'⁻¹ * t = c'⁻¹ * (t * c') * c'⁻¹ := by group
          _ = c'⁻¹ * (c' * t) * c'⁻¹ := by rw [this]
          _ = t * c'⁻¹ := by group
      have hr' : c'⁻¹ * r * c' ∈ Rbar S g t := by
        have := conj_mem_Rbar hκt hr
        rwa [hκ', inv_inv] at this
      have h1 := mem_centralizer_iff.mp hpR _ hr'
      calc r * q = c' * ((c'⁻¹ * r * c') * p) * c'⁻¹ := by rw [hq]; group
        _ = c' * (p * (c'⁻¹ * r * c')) * c'⁻¹ := by rw [h1]
        _ = q * r := by rw [hq]; group
    have hσq : σ * q = q * σ := (mem_centralizer_iff.mp hqC.2 σ hσ)
    have e : σ * c' * p * (σ * c')⁻¹ = q := by
      calc σ * c' * p * (σ * c')⁻¹ = σ * q * σ⁻¹ := by rw [hq]; group
        _ = q := by rw [hσq]; group
    rw [e]
    exact ⟨hqC, hqR⟩
  exact Setting.s12_noNormalTwo_Mbar S D' hD'M hP hnorm

theorem resC_injective_sc (hV : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) = Vt S g t) :
    Function.Injective (resC S g hV) := by
  rw [injective_iff_map_eq_one]
  intro c hc
  have hcV : ∀ v ∈ Vt S g t, ((c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v :=
    (restrictHom_eq_one_iff _ _ _ c).mp hc
  obtain ⟨hs, hn⟩ := (S45Q.hyp45Q H C).omega ht ht1 hVQ hΩ h6
  have hperf := commutator_RmodN hs hn
  have hmem : (c : S.O) ∈ Cbar S t ⊓ centralizer (Rbar S g t : Set S.O) :=
    ⟨c.2, mem_centralizer_iff.mpr fun r hr =>
      comm_of_fix_Vt H hN hperf (Cbar_le_Mbar c.2) (comm_of_mem_Cbar c.2) hcV hr⟩
  rw [Cbar_inf_centralizer_eq_bot_sc hCE H hNo C ht ht1 hVQ hΩ hN h6 hSC, mem_bot] at hmem
  exact Subtype.ext hmem

theorem RmodN_le_range_resC_sc (hV : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) = Vt S g t) :
    RmodN S g t ≤ (resC S g hV).range := by
  intro e he
  rw [← range_resV H.conj_mem t] at he
  obtain ⟨⟨r, hr⟩, rfl⟩ := he
  have htV : ∀ v ∈ Vt S g t, (t : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := fun v hv =>
    (self_mem_Nbar H ht).2 v hv
  rcases mem_Cbar_of_comm_sc hCE H hNo C ht ht1 hVQ hΩ hN h6 hSC (Rbar_le_Mbar hr)
    (commute_of_mem_Rbar H.conj_mem hr) with hc | hc
  · exact ⟨⟨r, hc⟩, LinearEquiv.ext fun v => Subtype.ext rfl⟩
  · refine ⟨⟨t * r, hc⟩, LinearEquiv.ext fun v => Subtype.ext ?_⟩
    change ((t * r : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = (r : S.Qt ≃ₗ[ZMod 2] S.Qt) v
    rw [coe_mul_apply, htV _ (apply_mem_Vt_of_mem_Rbar H.conj_mem hr v.2)]

theorem range_resC_eq_sc (hV : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) = Vt S g t)
    {Q : QuadraticForm (ZMod 2) (Vt S g t)} {hQ : Q.polarBilin.Nondegenerate}
    (hX : RmodN S g t = omegaGroup Q hQ)
    (hsing : ∀ v : Vt S g t, v ≠ 0 → (Q v = 0 ↔ v ∈ orbitOf (RmodN S g t) (aV ht))) :
    (resC S g hV).range = omegaGroup Q hQ ∨
      (resC S g hV).range = TauCeti.QuadraticMap.orthogonalGroup Q := by
  have : Nontrivial (Vt S g t) := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  have h1 : omegaGroup Q hQ ≤ (resC S g hV).range :=
    hX ▸ RmodN_le_range_resC_sc hCE H hNo C ht ht1 hVQ hΩ hN h6 hSC hV
  have h2 := range_resC_le_orthogonalGroup H hNo C ht ht1 hVQ hΩ hV hsing
  have h3 := relIndex_omegaGroup Q hQ
  have h4 := Subgroup.relIndex_mul_relIndex _ _ _ h1 h2
  rw [h3] at h4
  rcases (Nat.dvd_prime Nat.prime_two).mp (Dvd.intro _ h4) with h5 | h5
  · left
    exact le_antisymm (Subgroup.relIndex_eq_one.mp h5) h1
  · right
    rw [h5] at h4
    exact le_antisymm h2 (Subgroup.relIndex_eq_one.mp (by omega))

theorem timmesfeld_7_7_of_omegaCase_sc :
    ∃ q : QuadraticForm (ZMod 2) (Vt S g t), q.polarBilin.Nondegenerate ∧
      (Nonempty (S.Mbar ≃* Perm (Fin 3) × timmesfeldOmega (q : Vt S g t → ZMod 2)) ∨
        Nonempty (S.Mbar ≃* Perm (Fin 3) × timmesfeldIsometries (q : Vt S g t → ZMod 2))) := by
  obtain ⟨Q, hQ, -, hX, -, hsing⟩ := hΩ.exists_form
  have hV := (commSpace_t_eq H C ht ht1 hVQ).1
  obtain ⟨e₁⟩ := nonempty_mulEquiv_Mbar_sc hCE H hNo C ht ht1 hVQ hΩ hN h6 hSC
  have hinj := resC_injective_sc hCE H hNo C ht ht1 hVQ hΩ hN h6 hSC hV
  let e₂ : Cbar S t ≃* (resC S g hV).range := MonoidHom.ofInjective hinj
  refine ⟨Q, hQ, ?_⟩
  rcases range_resC_eq_sc hCE H hNo C ht ht1 hVQ hΩ hN h6 hSC hV hX hsing with h | h
  · exact Or.inl ⟨e₁.trans (MulEquiv.prodCongr (MulEquiv.refl _)
      (e₂.trans (MulEquiv.subgroupCongr (h.trans (timmesfeldOmega_eq Q hQ).symm))))⟩
  · exact Or.inr ⟨e₁.trans (MulEquiv.prodCongr (MulEquiv.refl _)
      (e₂.trans (MulEquiv.subgroupCongr (h.trans (timmesfeldIsometries_eq Q).symm))))⟩

end Seven

end Chain

end CFSG.GF2Type.Smith1979
