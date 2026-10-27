module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Rbc.NPComp
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Rbc.NPGen

public section

namespace CFSG.EvenSporadicStandard.M12Std.Rbc

open Subgroup CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction
open CFSG.EvenSporadicStandard.HSStd

section CentralLift

variable {G : Type} [Group G] {X : Subgroup G} {u x : G}

structure IsNPCentralLift (X : Subgroup G) (u x h : G) : Prop where
  mem_Y : h ∈ npY X u x
  ne_one : h ≠ 1
  central : oddProj (npD X x) ⟨h, npY_le_npD X u x mem_Y⟩ ∈ center (OddQuot (npD X x))

variable {h : G}

theorem IsNPCentralLift.mem_D (hh : IsNPCentralLift X u x h) : h ∈ npD X x :=
  npY_le_npD X u x hh.mem_Y

theorem IsNPCentralLift.comm_u (hh : IsNPCentralLift X u x h) : u * h = h * u :=
  (mem_centralizer_singleton_iff.1 hh.mem_Y.2).symm

@[expose] def IsNPCentralLift.bar (hh : IsNPCentralLift X u x h) : OddQuot (npD X x) :=
  oddProj (npD X x) ⟨h, hh.mem_D⟩

end CentralLift

namespace NPSetting

section Lift

variable {G : Type} [Group G] [Finite G] {X : Subgroup G} {u x : G} {T₀ : Subgroup G} {s₀ : G}
  {h : G}

theorem bar_ne_one (hS : NPSetting G X u x T₀ s₀) (hh : IsNPCentralLift X u x h) :
    hh.bar ≠ 1 := by
  intro hbar
  have h1 : (⟨h, hh.mem_Y⟩ : ↥(npY X u x)) = 1 := by
    apply hS.injective_oddProj_Y
    rw [map_one]
    change hh.bar = 1
    exact hbar
  exact hh.ne_one (congrArg Subtype.val h1)

theorem exists_centralLift (hNP : KDNP) (h15 : FS79Lemma15Sec G) (hS : NPSetting G X u x T₀ s₀) :
    ∃ h : G, IsNPCentralLift X u x h := by
  obtain ⟨hbar, hord, hcen, -, -, -, -, -, -, ⟨y, hy, -⟩⟩ := hS.Dbar_eq hNP h15
  refine ⟨(y : G), y.2, ?_, ?_⟩
  · intro hy1
    have hy1' : (⟨(y : G), npY_le_npD X u x y.2⟩ : ↥(npD X x)) = 1 := by
      rw [Subtype.ext_iff]
      exact hy1
    have hbar1 : hbar = 1 := by
      rw [← hy, hy1', map_one]
    rw [hbar1, orderOf_one] at hord
    omega
  · show oddProj (npD X x) ⟨(y : G), npY_le_npD X u x y.2⟩ ∈ center (OddQuot (npD X x))
    rw [hy, hcen]
    exact Subgroup.mem_zpowers hbar

theorem Dbar_of_lift (hNP : KDNP) (h15 : FS79Lemma15Sec G) (hS : NPSetting G X u x T₀ s₀)
    (hh : IsNPCentralLift X u x h) :
    orderOf hh.bar = 2 ∧ center (OddQuot (npD X x)) = zpowers hh.bar ∧
      centralizer ((oddBar (npD X x) (npA X x s₀) : Subgroup (OddQuot (npD X x))) :
        Set (OddQuot (npD X x))) = zpowers hh.bar ∧
      oddBar (npD X x) (npA X x s₀) ⊔ zpowers hh.bar = ⊤ ∧
      oddBar (npD X x) (npA X x s₀) ⊓ zpowers hh.bar = ⊥ := by
  obtain ⟨hbar, hord, hcen, hcentA, hsup, hinf, -⟩ := hS.Dbar_eq hNP h15
  have hbarmem : hh.bar ∈ zpowers hbar := by
    rw [← hcen]
    exact hh.central
  have hbarne : hh.bar ≠ 1 := hS.bar_ne_one hh
  have heq : hh.bar = hbar := eq_of_mem_zpowers_of_orderOf_eq_two hord hbarmem hbarne
  subst hbar
  exact ⟨hord, hcen, hcentA, hsup, hinf⟩

theorem mul_self_central_lift (hNP : KDNP) (h15 : FS79Lemma15Sec G)
    (hS : NPSetting G X u x T₀ s₀) (hh : IsNPCentralLift X u x h) : h * h = 1 :=
  hS.Y_exp_two hNP h15 h hh.mem_Y

theorem exists_T_eq_zpowers (hNP : KDNP) (h15 : FS79Lemma15Sec G) (hS : NPSetting G X u x T₀ s₀)
    (hh : IsNPCentralLift X u x h) :
    ∃ h' : G, T₀ = zpowers h' ∧ h' * h' = 1 ∧ Odd (orderOf (h' * h⁻¹)) := by
  let D := npD X x
  obtain ⟨hord, -, hcentA, -, -⟩ := hS.Dbar_of_lift hNP h15 hh
  have hTD : T₀ ≤ D := hS.T_le_D
  have hAD : npA X x s₀ ≤ D := hS.A_le_D
  have hQ : IsPGroup 2 ↥(T₀.subgroupOf D) :=
    hS.T_two.of_equiv (Subgroup.subgroupOfEquivOfLe hTD).symm
  have hinj : Function.Injective ((oddProj D).comp (T₀.subgroupOf D).subtype) :=
    oddProj_comp_subtype_injective D hQ
  have hsub : T₀.subgroupOf D ≤
      centralizer (((npA X x s₀).subgroupOf D : Subgroup ↥D) : Set ↥D) := by
    rw [centralizer_subgroupOf_of_le hAD]
    exact Subgroup.subgroupOf_mono D hS.T_le_centralizer_A
  have hTbar_le : (T₀.subgroupOf D).map (oddProj D) ≤
      centralizer ((oddBar D (npA X x s₀) : Subgroup (OddQuot D)) : Set (OddQuot D)) :=
    (Subgroup.map_mono (f := oddProj D) hsub).trans
      (map_centralizer_le_centralizer_image _ (oddProj D))
  have hmem_bar : ∀ (t : G) (ht : t ∈ T₀),
      oddProj D ⟨t, hTD ht⟩ ∈ zpowers hh.bar := by
    intro t ht
    rw [← hcentA]
    exact hTbar_le (Subgroup.mem_map_of_mem (oddProj D) (Subgroup.mem_subgroupOf.mpr ht))
  have hbar_unique : ∀ (t : G) (ht : t ∈ T₀), t ≠ 1 →
      oddProj D ⟨t, hTD ht⟩ = hh.bar := by
    intro t ht ht1
    refine eq_of_mem_zpowers_of_orderOf_eq_two hord (hmem_bar t ht) ?_
    intro h1
    apply ht1
    have htT : (⟨⟨t, hTD ht⟩, Subgroup.mem_subgroupOf.mpr ht⟩ :
        ↥(T₀.subgroupOf D)) = 1 := by
      apply hinj
      simpa using h1
    have hval := congrArg (fun z : ↥(T₀.subgroupOf D) => ((z : ↥D) : G)) htT
    simpa using hval
  obtain ⟨⟨h', hh'T⟩, hh'ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hS.T_ne
  have hh'ne1 : h' ≠ 1 := fun h1 => hh'ne (Subtype.ext h1)
  have hbar_h' : oddProj D ⟨h', hTD hh'T⟩ = hh.bar := hbar_unique h' hh'T hh'ne1
  refine ⟨h', ?_, ?_, ?_⟩
  · apply le_antisymm
    · intro t ht
      by_cases ht1 : t = 1
      · rw [ht1]; exact Subgroup.one_mem _
      · have hbar_t := hbar_unique t ht ht1
        have htT : (⟨⟨t, hTD ht⟩, Subgroup.mem_subgroupOf.mpr ht⟩ :
            ↥(T₀.subgroupOf D)) =
            ⟨⟨h', hTD hh'T⟩, Subgroup.mem_subgroupOf.mpr hh'T⟩ := by
          apply hinj
          simpa using hbar_t.trans hbar_h'.symm
        have hval := congrArg (fun z : ↥(T₀.subgroupOf D) => ((z : ↥D) : G)) htT
        have hteq : t = h' := by simpa using hval
        rw [hteq]; exact Subgroup.mem_zpowers h'
    · exact Subgroup.zpowers_le.mpr hh'T
  · have hmemT : h' * h' ∈ T₀ := mul_mem hh'T hh'T
    have hbar_sq : oddProj D ⟨h' * h', hTD hmemT⟩ = 1 := by
      have hdecomp : (⟨h' * h', hTD hmemT⟩ : ↥D) =
          (⟨h', hTD hh'T⟩ : ↥D) * ⟨h', hTD hh'T⟩ := Subtype.ext rfl
      rw [hdecomp, map_mul, hbar_h', ← pow_two, ← hord, pow_orderOf_eq_one]
    have h1 : (⟨⟨h' * h', hTD hmemT⟩, Subgroup.mem_subgroupOf.mpr hmemT⟩ :
        ↥(T₀.subgroupOf D)) = 1 := by
      apply hinj
      simpa using hbar_sq
    have hval := congrArg (fun z : ↥(T₀.subgroupOf D) => ((z : ↥D) : G)) h1
    simpa using hval
  · have hD : h' * h⁻¹ ∈ D := mul_mem (hTD hh'T) (inv_mem hh.mem_D)
    have hbar_h : oddProj D (⟨h, hh.mem_D⟩ : ↥D) = hh.bar := rfl
    have hz1 : oddProj D (⟨h' * h⁻¹, hD⟩ : ↥D) = 1 := by
      have hdecomp : (⟨h' * h⁻¹, hD⟩ : ↥D) =
          (⟨h', hTD hh'T⟩ : ↥D) * (⟨h, hh.mem_D⟩ : ↥D)⁻¹ := Subtype.ext rfl
      rw [hdecomp, map_mul, map_inv, hbar_h', hbar_h]
      simp
    have hcore : (⟨h' * h⁻¹, hD⟩ : ↥D) ∈ CFSG.oddCore ↥D := by
      rw [← ker_oddProj D]
      exact MonoidHom.mem_ker.mpr hz1
    have hdvd : orderOf (h' * h⁻¹) ∣ Nat.card (CFSG.oddCore ↥D) := by
      have h := Subgroup.orderOf_dvd_natCard (CFSG.oddCore ↥D) hcore
      simpa only [Subgroup.orderOf_mk] using h
    have hcard : Odd (Nat.card (CFSG.oddCore ↥D)) :=
      Nat.not_even_iff_odd.mp fun he =>
        not_two_dvd_natCard_oddCore D (even_iff_two_dvd.mp he)
    exact Odd.of_dvd_nat hcard hdvd

end Lift

section Conj

variable {G : Type} [Group G] [Finite G] {X : Subgroup G} {u x : G} {T₀ : Subgroup G} {s₀ : G}

theorem conj (hS : NPSetting G X u x T₀ s₀) {g : G} (hg : g ∈ npD X x) :
    NPSetting G X u x (T₀.map (MulAut.conj g).toMonoidHom) (g * s₀ * g⁻¹) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ :=
    linkData_conj hg hS.T_ne hS.T_two hS.comp hS.s_two hS.s_norm hS.s_sq hS.swap
  exact ⟨hS.out, hS.xmem, hS.xinv, hS.x240, hS.cent, hS.facts, hS.rbc, h1, h2, h3, h4, h5, h6, h7⟩

theorem exists_normalized (hNP : KDNP) (h15 : FS79Lemma15Sec G) (hS : NPSetting G X u x T₀ s₀) :
    ∃ h s : G, IsNPCentralLift X u x h ∧ NPSetting G X u x (zpowers h) s := by
  obtain ⟨h, hh⟩ := hS.exists_centralLift hNP h15
  obtain ⟨h', hT, hh', hodd⟩ := hS.exists_T_eq_zpowers hNP h15 hh
  obtain ⟨d, hd, hdh⟩ :=
    exists_zpow_conj_of_involutions (hS.mul_self_central_lift hNP h15 hh) hh' hodd
  have hh'D : h' ∈ npD X x := by
    have := hS.T_le_D
    rw [hT] at this
    exact this (Subgroup.mem_zpowers h')
  have hn : h' * h⁻¹ ∈ npD X x := Subgroup.mul_mem _ hh'D (Subgroup.inv_mem _ hh.mem_D)
  have hdD : d ∈ npD X x := (Subgroup.zpowers_le.2 hn) hd
  have hS' := hS.conj (Subgroup.inv_mem _ hdD)
  refine ⟨h, d⁻¹ * s₀ * d⁻¹⁻¹, hh, ?_⟩
  have hmap : T₀.map (MulAut.conj d⁻¹).toMonoidHom = zpowers h := by
    rw [hT, MonoidHom.map_zpowers]
    have : (MulAut.conj d⁻¹).toMonoidHom h' = h := by
      rw [hdh]
      show d⁻¹ * (d * h * d⁻¹) * d⁻¹⁻¹ = h
      group
    rw [this]
  rw [hmap] at hS'
  exact hS'

end Conj

end NPSetting

end CFSG.EvenSporadicStandard.M12Std.Rbc
