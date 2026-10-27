module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Rbc.NPStep4d
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Rbc.NPQuot

public section

namespace CFSG.EvenSporadicStandard.M12Std.Rbc

open Subgroup CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction
open CFSG.EvenSporadicStandard.HSStd

namespace NPSetting

section Step5

variable {G : Type} [Group G] [Finite G] {X : Subgroup G} {u x : G} {T₀ : Subgroup G} {s₀ : G}
  {h : G}

theorem x_mem_Y (hS : NPSetting G X u x T₀ s₀) : x ∈ npY X u x := by
  refine ⟨?_, ?_⟩
  · have hx : x ∈ X ⊓ centralizer (jOf X x : Set G) := by
      rw [hS.cent]
      exact Subgroup.mem_zpowers x
    exact hx.2
  · exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hS.out.mem x hS.xmem)

theorem conj_central_lift (hNP : KDNP) (h15 : FS79Lemma15Sec G) (hh : IsNPCentralLift X u x h)
    (hS : NPSetting G X u x T₀ s₀) {n : G}
    (hn : n ∈ centralizer ({x} : Set G) ⊓ centralizer ({u} : Set G)) : n * h * n⁻¹ = h := by
  have hn' : n ∈ centralizer ({u} : Set G) ⊓ normalizer (jOf X x : Set G) := by
    rw [hS.rbc.normalizer_J]
    exact hn
  have hnD : n ∈ normalizer ((npD X x : Subgroup G) : Set G) :=
    mem_normalizer_centralizer_of_mem_normalizer hn'.2
  have h2_mem_D : n * h * n⁻¹ ∈ npD X x := by
    have hmem2 := (conjOn (npD X x) hnD ⟨h, hh.mem_D⟩).2
    rw [coe_conjOn (npD X x) hnD ⟨h, hh.mem_D⟩] at hmem2
    exact hmem2
  have h2_comm_u : n * h * n⁻¹ ∈ centralizer ({u} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    have hnu : n * u = u * n := mem_centralizer_singleton_iff.1 hn.2
    have hhu : h * u = u * h := (hh.comm_u).symm
    calc (n * h * n⁻¹) * u = n * h * (n⁻¹ * u) := by group
      _ = n * h * (u * n⁻¹) := by
            rw [show n⁻¹ * u = u * n⁻¹ from by
              calc n⁻¹ * u = n⁻¹ * (u * n) * n⁻¹ := by group
                _ = n⁻¹ * (n * u) * n⁻¹ := by rw [← hnu]
                _ = u * n⁻¹ := by group]
      _ = n * (h * u) * n⁻¹ := by group
      _ = n * (u * h) * n⁻¹ := by rw [hhu]
      _ = (n * u) * h * n⁻¹ := by group
      _ = (u * n) * h * n⁻¹ := by rw [hnu]
      _ = u * (n * h * n⁻¹) := by group
  let y₂ : ↥(npY X u x) := ⟨n * h * n⁻¹, h2_mem_D, h2_comm_u⟩
  have hbar_eq : hh.bar = oddProj (npD X x) ⟨h, npY_le_npD X u x hh.mem_Y⟩ :=
    congrArg (oddProj (npD X x)) (Subtype.ext rfl)
  obtain ⟨hbar_ord, hcenter, -⟩ := hS.Dbar_of_lift hNP h15 hh
  have hmem : conjOddQuot (npD X x) hnD hh.bar ∈ zpowers hh.bar := by
    rw [← hcenter, hbar_eq]
    exact conjOddQuot_mem_center (npD X x) hnD hh.central
  have hne : conjOddQuot (npD X x) hnD hh.bar ≠ 1 := by
    intro hzero
    exact hS.bar_ne_one hh ((conjOddQuot (npD X x) hnD).injective (by rw [hzero, map_one]))
  have halpha : conjOddQuot (npD X x) hnD hh.bar = hh.bar :=
    eq_of_mem_zpowers_of_orderOf_eq_two hbar_ord hmem hne
  have hconj : Subgroup.inclusion (npY_le_npD X u x) y₂ =
      (conjOn (npD X x) hnD ⟨h, hh.mem_D⟩ : ↥(npD X x)) := by
    apply Subtype.ext
    rw [coe_conjOn]
    rfl
  have hproj : (oddProj (npD X x)).comp (Subgroup.inclusion (npY_le_npD X u x)) y₂ = hh.bar := by
    change oddProj (npD X x) (Subgroup.inclusion (npY_le_npD X u x) y₂) = hh.bar
    calc oddProj (npD X x) (Subgroup.inclusion (npY_le_npD X u x) y₂)
        = oddProj (npD X x) (conjOn (npD X x) hnD ⟨h, hh.mem_D⟩) := by rw [hconj]
      _ = conjOddQuot (npD X x) hnD (oddProj (npD X x) ⟨h, hh.mem_D⟩) :=
            (conjOddQuot_oddProj (npD X x) hnD ⟨h, hh.mem_D⟩).symm
      _ = hh.bar := halpha
  have hf : (oddProj (npD X x)).comp (Subgroup.inclusion (npY_le_npD X u x)) ⟨h, hh.mem_Y⟩ =
      hh.bar :=
    hbar_eq.symm
  exact congrArg Subtype.val (hS.injective_oddProj_Y (hproj.trans hf.symm))

theorem eq_u_or_x_or_ux (hNP : KDNP) (h15 : FS79Lemma15Sec G) (hh : IsNPCentralLift X u x h)
    (hS : NPSetting G X u x T₀ s₀) : h = u ∨ h = x ∨ h = u * x := by
  have hexp : ∀ y ∈ centralizer (jOf X x : Set G) ⊓
      (centralizer ({x} : Set G) ⊓ centralizer ({u} : Set G)), y * y = 1 := by
    intro y hy
    rw [← hS.Y_eq] at hy
    exact hS.Y_exp_two hNP h15 y hy
  obtain ⟨hcl, -⟩ := hS.rbc.of_exp2 hexp
  have hhY : h ∈ centralizer (jOf X x : Set G) ⊓
      (centralizer ({x} : Set G) ⊓ centralizer ({u} : Set G)) := by
    rw [← hS.Y_eq]
    exact hh.mem_Y
  have hhc : h ∈ centralizer ((centralizer ({x} : Set G) ⊓ centralizer ({u} : Set G) :
      Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    exact mul_inv_eq_iff_eq_mul.1 (hS.conj_central_lift hNP h15 hh hn)
  have hmem : h ∈ closure ({u, x} : Set G) := by
    have h0 : h ∈ centralizer ((centralizer ({x} : Set G) ⊓ centralizer ({u} : Set G) :
        Subgroup G) : Set G) ⊓ (centralizer (jOf X x : Set G) ⊓
          (centralizer ({x} : Set G) ⊓ centralizer ({u} : Set G))) := ⟨hhc, hhY⟩
    rw [hcl] at h0
    exact h0
  have hux : u * x = x * u := by
    have := hS.out.mem
    rw [Subgroup.mem_centralizer_iff] at this
    exact (this x hS.xmem).symm
  have hu2 : u * u = 1 := by
    have := pow_orderOf_eq_one u
    rwa [hS.out.inv, pow_two] at this
  have hx2 : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hS.xinv, pow_two] at this
  rcases mem_closure_pair_of_commute_involutions hux hu2 hx2 hmem with h1 | h1 | h1 | h1
  · exact absurd h1 hh.ne_one
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr h1)

theorem ne_u (hNP : KDNP) (h15 : FS79Lemma15Sec G) (hh : IsNPCentralLift X u x h)
    (hS : NPSetting G X u x T₀ s₀) : h ≠ u := by
  intro hu
  subst hu
  have hbar_eq : hh.bar = hS.ubar :=
    congrArg (oddProj (npD X x)) (Subtype.ext rfl)
  have hcenter : hS.ubar ∈ center (OddQuot (npD X x)) := by
    rw [← hbar_eq]
    exact hh.central
  have htop : centralizer ({hS.ubar} : Set (OddQuot (npD X x))) = ⊤ :=
    Subgroup.centralizer_eq_top_iff_subset.2 (by
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact hcenter)
  have hcard : Nat.card (OddQuot (npD X x)) = 8 := by
    rw [← Subgroup.card_top (G := OddQuot (npD X x)), ← htop]
    exact hS.card_fixed_bar
  have hdvd : Nat.card ↥(oddBar (npD X x) (npA X x s₀)) ∣
      Nat.card (OddQuot (npD X x)) :=
    Subgroup.card_subgroup_dvd_card (oddBar (npD X x) (npA X x s₀))
  rw [hS.card_Abar, hcard] at hdvd
  exact absurd hdvd (by norm_num)

theorem bar_x_mem_Abar (hNP : KDNP) (h15 : FS79Lemma15Sec G) (hh : IsNPCentralLift X u x h)
    (hS : NPSetting G X u x T₀ s₀) :
    oddProj (npD X x) ⟨x, npY_le_npD X u x hS.x_mem_Y⟩ ∈ oddBar (npD X x) (npA X x s₀) := by
  let D := npD X x
  let Abar : Subgroup (OddQuot D) := oddBar D (npA X x s₀)
  let hx : x ∈ D := npY_le_npD X u x hS.x_mem_Y
  have hexp : ∀ y ∈ centralizer (jOf X x : Set G) ⊓
      (centralizer ({x} : Set G) ⊓ centralizer ({u} : Set G)), y * y = 1 := by
    intro y hy
    exact hS.Y_exp_two hNP h15 y (by rw [hS.Y_eq]; exact hy)
  obtain ⟨-, o, ho, n, hn, hno⟩ := hS.rbc.of_exp2 hexp
  have hnJ : n ∈ normalizer (jOf X x : Set G) := by
    have h1 : n ∈ centralizer ({u} : Set G) ⊓ normalizer (jOf X x : Set G) := by
      rw [hS.rbc.normalizer_J]
      exact hn
    exact h1.2
  have hnD : n ∈ normalizer (D : Set G) := mem_normalizer_centralizer_of_mem_normalizer hnJ
  let α : OddQuot D ≃* OddQuot D := conjOddQuot D hnD
  have hαh : α hh.bar = hh.bar := by
    change conjOddQuot D hnD (oddProj D ⟨h, hh.mem_D⟩) =
      oddProj D ⟨h, hh.mem_D⟩
    rw [conjOddQuot_oddProj]
    refine congrArg (oddProj D) (Subtype.ext ?_)
    rw [coe_conjOn]
    simpa using hS.conj_central_lift hNP h15 hh hn
  have hcomp : IsCompIn Abar ⊤ := hS.isCompIn_Abar_top hNP h15
  have hmap : Abar.map α.toMonoidHom = Abar := by
    have h1 := Hyp.isCompIn_map_mulEquiv α hcomp
    rw [Subgroup.map_top_of_surjective α.toMonoidHom α.surjective] at h1
    exact hS.comp_unique hNP h15 h1 hcomp
  have hαA : ∀ a ∈ Abar, α a ∈ Abar := by
    intro a ha
    have h : α a ∈ Abar.map α.toMonoidHom := ⟨a, ha, rfl⟩
    rwa [hmap] at h
  obtain ⟨-, hcen, -, hsup, -⟩ := hS.Dbar_of_lift hNP h15 hh
  have hcenD : center (OddQuot D) = zpowers hh.bar := hcen
  have hsupD : oddBar D (npA X x s₀) ⊔ zpowers hh.bar = ⊤ := hsup
  have hbar_cen : hh.bar ∈ center (OddQuot D) := hh.central
  haveI : (zpowers hh.bar).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.2 hbar_cen)
  have hobar : oddProj D ⟨o, ho.1⟩ ∈ Abar ⊔ zpowers hh.bar := by
    rw [show Abar = oddBar D (npA X x s₀) from rfl, hsupD]
    exact Subgroup.mem_top _
  obtain ⟨a, ha, z, hz, haz⟩ := Subgroup.mem_sup_of_normal_right.1 hobar
  have hzc : z ∈ center (OddQuot D) := by
    rw [hcenD]
    exact hz
  have hz_inv_comm : ∀ g : OddQuot D, z⁻¹ * g = g * z⁻¹ := fun g =>
    (Subgroup.mem_center_iff.1 (Subgroup.inv_mem (center (OddQuot D)) hzc) g).symm
  have hαz : α z = z := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hz
    have h1 : α (hh.bar ^ k) = (α hh.bar) ^ k := map_zpow α.toMonoidHom hh.bar k
    rw [← hk, h1, hαh]
  have hαo : α (oddProj D ⟨o, ho.1⟩) =
      oddProj D ⟨o, ho.1⟩ * oddProj D ⟨x, hx⟩ := by
    change conjOddQuot D hnD (oddProj D ⟨o, ho.1⟩) =
      oddProj D ⟨o, ho.1⟩ * oddProj D ⟨x, hx⟩
    rw [conjOddQuot_oddProj]
    rw [← map_mul]
    refine congrArg (oddProj D) (Subtype.ext ?_)
    rw [coe_conjOn, Subgroup.coe_mul]
    simpa using hno
  have hxeq : oddProj D ⟨x, hx⟩ =
      (oddProj D ⟨o, ho.1⟩)⁻¹ * α (oddProj D ⟨o, ho.1⟩) := by
    rw [hαo]
    group
  have hxeq2 : oddProj D ⟨x, hx⟩ = a⁻¹ * α a := by
    have hαaz : α (a * z) = α a * z := by rw [map_mul, hαz]
    rw [hxeq, ← haz, hαaz, mul_inv_rev]
    calc z⁻¹ * a⁻¹ * (α a * z)
        = z⁻¹ * (a⁻¹ * α a) * z := by group
      _ = (a⁻¹ * α a) * z⁻¹ * z := by rw [hz_inv_comm]
      _ = a⁻¹ * α a := by group
  have hxAbar : oddProj D ⟨x, hx⟩ ∈ Abar := by
    rw [hxeq2]
    exact Subgroup.mul_mem Abar (Subgroup.inv_mem Abar ha) (hαA a ha)
  exact hxAbar

theorem ne_x (hNP : KDNP) (h15 : FS79Lemma15Sec G) (hh : IsNPCentralLift X u x h)
    (hS : NPSetting G X u x T₀ s₀) : h ≠ x := by
  intro hx
  subst hx
  have h1 : hh.bar ∈ oddBar (npD X h) (npA X h s₀) := hS.bar_x_mem_Abar hNP h15 hh
  have h2 : hh.bar ∈ oddBar (npD X h) (npA X h s₀) ⊓ zpowers hh.bar :=
    ⟨h1, Subgroup.mem_zpowers _⟩
  rw [(hS.Dbar_of_lift hNP h15 hh).2.2.2.2] at h2
  exact hS.bar_ne_one hh (Subgroup.mem_bot.1 h2)

theorem h_eq_mul (hNP : KDNP) (h15 : FS79Lemma15Sec G) (hh : IsNPCentralLift X u x h)
    (hS : NPSetting G X u x T₀ s₀) : h = u * x :=
  (hS.eq_u_or_x_or_ux hNP h15 hh).elim (fun h1 => absurd h1 (hS.ne_u hNP h15 hh))
    fun h2 => h2.elim (fun h3 => absurd h3 (hS.ne_x hNP h15 hh)) id

theorem x_mem_A {s : G} (hNP : KDNP) (h15 : FS79Lemma15Sec G) (hh : IsNPCentralLift X u x h)
    (hS : NPSetting G X u x (zpowers h) s) : x ∈ npA X x s := by
  have hxY : x ∈ npY X u x := hS.x_mem_Y
  have hxD : x ∈ npD X x := npY_le_npD X u x hS.x_mem_Y
  obtain ⟨a, ha_sub, ha_eq⟩ : ∃ a ∈ (npA X x s).subgroupOf (npD X x),
      oddProj (npD X x) a = oddProj (npD X x) ⟨x, hxD⟩ :=
    hS.bar_x_mem_Abar hNP h15 hh
  have haA : (a : G) ∈ npA X x s := Subgroup.mem_subgroupOf.1 ha_sub
  have haD : (a : G) ∈ npD X x := a.2
  have hbA : u * (a : G) * u⁻¹ ∈ npA X x s := by
    have h1 : (MulAut.conj u) (a : G) ∈ (npA X x s).map (MulAut.conj u).toMonoidHom :=
      Subgroup.mem_map_of_mem ((MulAut.conj u).toMonoidHom) haA
    rwa [hS.map_conj_u_A hNP h15 hh] at h1
  have hbD : u * (a : G) * u⁻¹ ∈ npD X x :=
    mul_mem (mul_mem hS.u_mem_D haD) (inv_mem hS.u_mem_D)
  have hproj : oddProj (npD X x) ⟨u * (a : G) * u⁻¹, hbD⟩ = oddProj (npD X x) a := by
    let ub : ↥(npD X x) := ⟨u, hS.u_mem_D⟩
    let xb : ↥(npD X x) := ⟨x, hxD⟩
    have h1 : (⟨u * (a : G) * u⁻¹, hbD⟩ : ↥(npD X x)) = ub * a * ub⁻¹ :=
      Subtype.ext rfl
    have hxub : ub * xb * ub⁻¹ = xb := by
      apply Subtype.ext
      show u * x * u⁻¹ = x
      have hc : x * u = u * x := mem_centralizer_singleton_iff.1 hxY.2
      rw [← hc]
      group
    rw [h1]
    calc oddProj (npD X x) (ub * a * ub⁻¹)
        = oddProj (npD X x) ub * oddProj (npD X x) a * (oddProj (npD X x) ub)⁻¹ := by
          rw [map_mul, map_mul, map_inv]
      _ = oddProj (npD X x) ub * oddProj (npD X x) xb * (oddProj (npD X x) ub)⁻¹ := by
          rw [ha_eq]
      _ = oddProj (npD X x) xb := by rw [← map_inv, ← map_mul, ← map_mul, hxub]
      _ = oddProj (npD X x) a := ha_eq.symm
  have hA_eq : (⟨u * (a : G) * u⁻¹, hbA⟩ : ↥(npA X x s)) = ⟨(a : G), haA⟩ := by
    apply hS.injective_oddProj_A
    show oddProj (npD X x) ⟨u * (a : G) * u⁻¹, hS.A_le_D hbA⟩
        = oddProj (npD X x) ⟨(a : G), hS.A_le_D haA⟩
    have e1 : (⟨u * (a : G) * u⁻¹, hS.A_le_D hbA⟩ : ↥(npD X x))
        = ⟨u * (a : G) * u⁻¹, hbD⟩ := Subtype.ext rfl
    have e2 : (⟨(a : G), hS.A_le_D haA⟩ : ↥(npD X x)) = a := Subtype.ext rfl
    rw [e1, e2]
    exact hproj
  have hcomm : (a : G) * u = u * (a : G) := by
    have h : u * (a : G) * u⁻¹ = (a : G) := by
      simpa using congrArg Subtype.val hA_eq
    rw [mul_inv_eq_iff_eq_mul] at h
    exact h.symm
  have haY : (a : G) ∈ npY X u x :=
    ⟨haD, mem_centralizer_singleton_iff.2 hcomm⟩
  have hax : (a : G) = x := by
    have hY_eq : (⟨(a : G), haY⟩ : ↥(npY X u x)) = ⟨x, hxY⟩ := by
      apply hS.injective_oddProj_Y
      show oddProj (npD X x) ⟨(a : G), npY_le_npD X u x haY⟩
          = oddProj (npD X x) ⟨x, npY_le_npD X u x hxY⟩
      have e1 : (⟨(a : G), npY_le_npD X u x haY⟩ : ↥(npD X x)) = a := Subtype.ext rfl
      have e2 : (⟨x, npY_le_npD X u x hxY⟩ : ↥(npD X x)) = ⟨x, hxD⟩ := Subtype.ext rfl
      rw [e1, e2]
      exact ha_eq
    exact congrArg Subtype.val hY_eq
  exact Eq.mp (congrArg (fun t => t ∈ npA X x s) hax) haA

end Step5

end NPSetting

end CFSG.EvenSporadicStandard.M12Std.Rbc
