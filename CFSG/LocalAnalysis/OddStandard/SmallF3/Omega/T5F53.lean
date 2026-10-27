module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5F53Aux
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5Center
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5CoverAct
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5Mono3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5Tab5Cov

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

open scoped Pointwise

theorem asc82Tab5_f53_of (hS : Asc82SchurU43) :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6Z2 L →
      ∀ P : Subgroup G, IsSylow2Of P L → ∀ t : G, t ∈ centerIn L → orderOf t = 2 →
        ∀ z : G, IsI4PlusIn L z → z ∈ centerIn P →
          centerIn P = zpowers t ⊔ zpowers z ∧
            ∀ x : G, x ∈ normalizer (L : Set G) → (∀ p ∈ P, x * p = p * x) →
              ∃ c ∈ centralizer (L : Set G), ∃ w ∈ centerIn P, x = w * c := by
  intro G _ _ L hL P hP t ht ht2 z hz hzP
  classical
  obtain ⟨V, i1, i2, i3, Q, hQ, φ, h⟩ := t5_exists_cover hS hL
  letI := i1; letI := i2; letI := i3
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO : OddCentralCover φ := h.oddCentralCover hL
  have hdim : Module.finrank (ZMod 3) V = 6 := h.finrank_eq
  have hsgn : quadSign Q = -1 := h.quadSign_eq
  have hPL : P ≤ L := hP.1
  obtain ⟨K, hzK, hzKL, _, _⟩ := hz.2
  have hzL : z ∈ L := (Subgroup.mem_inf.mp (hzKL hzK)).1
  obtain ⟨t', ht'c, ht'v⟩ := Subgroup.mem_map.mp ht
  have htL : t ∈ L := ht'v ▸ t'.2
  have hzP' : z ∈ P := Subgroup.map_subtype_le _ hzP
  let tL : ↥L := ⟨t, htL⟩
  let zL : ↥L := ⟨z, hzL⟩
  have htL_center : tL ∈ Subgroup.center ↥L := by
    have h : tL = t' := Subtype.ext ht'v.symm
    rw [h]; exact ht'c
  have ht'_ord : orderOf tL = 2 := by
    rw [show orderOf tL = orderOf t from Subgroup.orderOf_mk t htL, ht2]
  let ψ : ↥P →* omegaGroup hQ := φ.comp (Subgroup.inclusion hPL)
  let Pb : Subgroup (omegaGroup hQ) := ψ.range
  have hψ_inj : Function.Injective ψ := (t5_f53_inj_card h hL hP).1
  let ψb : ↥P ≃* ↥Pb := MonoidHom.ofInjective hψ_inj
  have hψb_surj : Function.Surjective ψb := ψb.surjective
  obtain ⟨Q2, hQ2map⟩ := hP.exists_sylow
  obtain ⟨P₀, z₀, hP₀le, hP₀card, hz₀P₀, hpiP₀, hz₀type, hcent₀, hsim₀⟩ :=
    t5_f53_model hQ hdim hsgn
  obtain ⟨g, hmem, hZb_forward⟩ :=
    t5_f53_conj_center h hL hP hP₀le hP₀card hz₀P₀ hpiP₀ hcent₀
  let π' : (omgGroup hQ) := ⟨piOrth Q, hP₀le hpiP₀⟩
  let z₀' : (omgGroup hQ) := ⟨z₀, hP₀le hz₀P₀⟩
  let zb' : (omgGroup hQ) := g * z₀' * g⁻¹
  have hπ'2 : π' * π' = 1 := Subtype.ext piOrth_mul_self
  have hpi_fact : invType (piOrth Q) = (6, -1) := by rw [invType_piOrth hQ, hdim, hsgn]
  have hZ₀ := t5_f53_center_mono hP₀le hz₀P₀ hpiP₀ hcent₀
  let zP : ↥P := ⟨z, hzP'⟩
  let φz' : (omgGroup hQ) := ψ zP
  have hzP_center : zP ∈ Subgroup.center ↥P := by
    obtain ⟨z', hz', hz'val⟩ := Subgroup.mem_map.mp hzP
    have hzz : zP = z' := by
      apply Subtype.ext
      change z = (z' : G)
      rw [show (z' : G) = z from hz'val]
    rw [hzz]; exact hz'
  have hφz'_center : ψb zP ∈ Subgroup.center ↥Pb :=
    t5_map_center_le_center (ψb : ↥P →* ↥Pb) hψb_surj
      (Subgroup.mem_map_of_mem (ψb : ↥P →* ↥Pb) hzP_center)
  have hφz_cent : ∀ y ∈ Pb, φz' * y = y * φz' := by
    intro y hy
    have h := Subgroup.mem_center_iff.mp hφz'_center (⟨y, hy⟩ : ↥Pb)
    have h' : y * (ψb zP : (omgGroup hQ)) = (ψb zP : (omgGroup hQ)) * y :=
      congrArg Subtype.val h
    have hcoe : ((ψb zP : ↥Pb) : (omgGroup hQ)) = φz' := rfl
    rw [hcoe] at h'
    exact h'.symm
  have hφz_eq : φz' = φ zL := by
    change φ (Subgroup.inclusion hPL zP) = φ zL
    rw [show Subgroup.inclusion hPL zP = zL from Subtype.ext rfl]
  have hφz_type : invType (φz' : OGroup Q) = (4, 1) := by
    rw [show (φz' : OGroup Q) = ((φ zL : omegaGroup hQ) : OGroup Q) from
      congrArg Subtype.val hφz_eq]
    exact t5_phi_pocket_invType h hL hz hzL
  have hφz_ne_one : φz' ≠ 1 := by
    intro h1
    have h2 : invType (φz' : OGroup Q) = invType (1 : OGroup Q) := by
      rw [show (φz' : OGroup Q) = 1 from congrArg Subtype.val h1]
    rw [hφz_type, invType_one] at h2
    exact absurd h2 (by decide)
  have hφz_ne_pi : φz' ≠ π' := by
    intro h1
    have h2 : invType (φz' : OGroup Q) = invType (piOrth Q) := by
      rw [show (φz' : OGroup Q) = piOrth Q from congrArg Subtype.val h1]
    rw [hφz_type, hpi_fact] at h2
    exact absurd h2 (by decide)
  have hφz_mem : φz' ∈ Pb := MonoidHom.mem_range.mpr ⟨zP, rfl⟩
  have hφz_mem4 : φz' = zb' ∨ φz' = π' * zb' := by
    rcases hZb_forward φz' hφz_mem hφz_cent with h | h | h | h
    · exact absurd h hφz_ne_one
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h hφz_ne_pi
  have hZbZ : ∀ x : (omgGroup hQ), x ∈ Pb → (∀ y ∈ Pb, x * y = y * x) →
      (x = 1 ∨ x = π' ∨ x = φz' ∨ x = π' * φz') := by
    intro x hx hxc
    rcases hZb_forward x hx hxc with h | h | h | h
    · exact Or.inl h
    · rcases hφz_mem4 with hh | hh
      · exact Or.inr (Or.inr (Or.inl (h.trans hh.symm)))
      · refine Or.inr (Or.inr (Or.inr (h.trans ?_)))
        rw [hh, ← mul_assoc, hπ'2, one_mul]
    · rcases hφz_mem4 with hh | hh
      · exact Or.inr (Or.inr (Or.inr (h.trans (congrArg (fun z => π' * z) hh).symm)))
      · exact Or.inr (Or.inr (Or.inl (h.trans hh.symm)))
    · exact Or.inr (Or.inl h)
  have htP : t ∈ P := by
    haveI : (Subgroup.zpowers tL).Normal :=
      Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr htL_center)
    have hpgrp : IsPGroup 2 (Subgroup.zpowers tL) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht'_ord]; norm_num)
    have hle : Subgroup.zpowers tL ≤ (Q2 : Subgroup ↥L) :=
      IsPGroup.le_sylow_of_normal hpgrp Q2
    have hmemQ : tL ∈ (Q2 : Subgroup ↥L) := hle (Subgroup.mem_zpowers tL)
    have h := Subgroup.mem_map_of_mem L.subtype hmemQ
    rw [hQ2map] at h
    exact h
  let tP : ↥P := ⟨t, htP⟩
  have hψtP : ψ tP = π' := by
    apply Subtype.ext
    exact h.map_central hL ht ht2 htL
  have hcenter : centerIn P = zpowers t ⊔ zpowers z := by
    apply le_antisymm
    · intro a ha
      obtain ⟨a', ha'c, ha'v⟩ := Subgroup.mem_map.mp ha
      have hψa_cent : ψb a' ∈ Subgroup.center ↥Pb :=
        t5_map_center_le_center (ψb : ↥P →* ↥Pb) hψb_surj
          (Subgroup.mem_map_of_mem (ψb : ↥P →* ↥Pb) ha'c)
      have hxcent : ∀ y ∈ Pb, ((ψb a' : ↥Pb) : (omgGroup hQ)) * y =
          y * ((ψb a' : ↥Pb) : (omgGroup hQ)) := by
        intro y hy
        have h := Subgroup.mem_center_iff.mp hψa_cent (⟨y, hy⟩ : ↥Pb)
        exact (congrArg Subtype.val h).symm
      have h4 := hZbZ ((ψb a' : ↥Pb) : (omgGroup hQ)) (ψb a').2 hxcent
      have hcases : a' = 1 ∨ a' = tP ∨ a' = zP ∨ a' = tP * zP := by
        rcases h4 with hx | hx | hx | hx
        · left
          have hψ1 : ψ a' = 1 := hx
          exact hψ_inj (by rw [hψ1, map_one])
        · right; left
          apply hψ_inj
          exact hx.trans hψtP.symm
        · right; right; left
          apply hψ_inj
          exact hx
        · right; right; right
          apply hψ_inj
          rw [map_mul, hψtP]
          exact hx
      have ha_eq : a = 1 ∨ a = t ∨ a = z ∨ a = t * z := by
        rcases hcases with h' | h' | h' | h'
        · left
          calc a = (a' : G) := ha'v.symm
            _ = 1 := by rw [h']; rfl
        · right; left
          calc a = (a' : G) := ha'v.symm
            _ = t := by rw [h']
        · right; right; left
          calc a = (a' : G) := ha'v.symm
            _ = z := by rw [h']
        · right; right; right
          calc a = (a' : G) := ha'v.symm
            _ = t * z := by rw [h']; rfl
      rcases ha_eq with h' | h' | h' | h'
      · rw [h']; exact one_mem _
      · rw [h']; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers t)
      · rw [h']; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
      · rw [h']
        exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers t))
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers z))
    · apply sup_le
      · apply Subgroup.zpowers_le.mpr
        exact Subgroup.mem_map_of_mem P.subtype
          (show (⟨t, htP⟩ : ↥P) ∈ Subgroup.center ↥P from by
            rw [Subgroup.mem_center_iff]
            intro p
            apply Subtype.ext
            have hc := congrArg Subtype.val
              (Subgroup.mem_center_iff.mp htL_center ⟨(p : G), hPL p.2⟩)
            exact hc)
      · exact Subgroup.zpowers_le.mpr hzP
  refine ⟨hcenter, ?_⟩
  intro x hxN hxP
  obtain ⟨x', hx'⟩ := t5_exists_coverAct hL h hxN
  have hx'fix : ∀ y : (omgGroup hQ), y ∈ Pb → simAct Q x' (y : OGroup Q) = (y : OGroup Q) := by
    intro y hy
    obtain ⟨p, hp⟩ := MonoidHom.mem_range.mp hy
    rw [← hp]
    have hlconj : x * (p : G) * x⁻¹ = (p : G) := by
      have hh := hxP p p.2
      calc x * (p : G) * x⁻¹ = ((p : G) * x) * x⁻¹ := by rw [hh]
        _ = (p : G) := by group
    let l : ↥L := ⟨(p : G), hPL p.2⟩
    have h := hx'.2 l l (by
      show (l : G) = x * (l : G) * x⁻¹
      exact hlconj.symm)
    exact h.symm
  let gbar : OGroup Q := (g : OGroup Q)
  let x'' : simGroup Q := orthToSim Q (gbar⁻¹) * x' * orthToSim Q gbar
  have hx''fix : ∀ y ∈ P₀, simAct Q x'' y = y := by
    intro y hy
    have hyb : g * (⟨y, hP₀le hy⟩ : (omgGroup hQ)) * g⁻¹ ∈ Pb := (hmem _).mpr (by
      rw [show g⁻¹ * (g * (⟨y, hP₀le hy⟩ : (omgGroup hQ)) * g⁻¹) * g =
          (⟨y, hP₀le hy⟩ : (omgGroup hQ)) from by
        group]
      exact Subgroup.mem_subgroupOf.mpr hy)
    have hyb' : simAct Q x' (gbar * y * gbar⁻¹) = gbar * y * gbar⁻¹ := hx'fix _ hyb
    calc simAct Q x'' y
        = simAct Q (orthToSim Q (gbar⁻¹)) (simAct Q x' (simAct Q (orthToSim Q gbar) y)) := by
          dsimp only [x'']
          rw [map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply]
      _ = gbar⁻¹ * (simAct Q x' (gbar * y * gbar⁻¹)) * gbar⁻¹⁻¹ := by
          rw [simAct_orthToSim, simAct_orthToSim]
      _ = gbar⁻¹ * (gbar * y * gbar⁻¹) * gbar⁻¹⁻¹ := by rw [hyb']
      _ = y := by group
  obtain ⟨w₀, hw₀cases, hx''w₀⟩ := hsim₀ x'' hx''fix
  have hx'wb : x' = orthToSim Q (gbar * w₀ * gbar⁻¹) := by
    have h1 : (orthToSim Q gbar)⁻¹ * x' * orthToSim Q gbar = orthToSim Q w₀ := by
      rw [← hx''w₀]
      change (orthToSim Q gbar)⁻¹ * x' * orthToSim Q gbar =
        orthToSim Q (gbar⁻¹) * x' * orthToSim Q gbar
      rw [map_inv]
    calc x' = (orthToSim Q gbar) *
          ((orthToSim Q gbar)⁻¹ * x' * orthToSim Q gbar) * (orthToSim Q gbar)⁻¹ := by group
      _ = (orthToSim Q gbar) * orthToSim Q w₀ * (orthToSim Q gbar)⁻¹ := by rw [h1]
      _ = orthToSim Q (gbar * w₀ * gbar⁻¹) := by rw [map_mul, map_mul, map_inv]
  let wb : OGroup Q := gbar * w₀ * gbar⁻¹
  have hw₀P : w₀ ∈ P₀ := by
    rcases hw₀cases with h | h | h | h
    · rw [h]; exact one_mem _
    · rw [h]; exact hz₀P₀
    · rw [h]; exact mul_mem hpiP₀ hz₀P₀
    · rw [h]; exact hpiP₀
  let w₀' : (omgGroup hQ) := ⟨w₀, hP₀le hw₀P⟩
  let wb' : (omgGroup hQ) := g * w₀' * g⁻¹
  have hwb_mem : wb' ∈ Pb := (hmem wb').mpr (by
    rw [show g⁻¹ * wb' * g = w₀' from by dsimp only [wb']; group]
    exact Subgroup.mem_subgroupOf.mpr hw₀P)
  have hwb_cent : ∀ y ∈ Pb, wb' * y = y * wb' := by
    intro y hy
    have hy₀ : g⁻¹ * y * g ∈ P₀.subgroupOf (omegaGroup hQ) := (hmem y).mp hy
    have hw₀'_cent : w₀' * (g⁻¹ * y * g) = (g⁻¹ * y * g) * w₀' :=
      ((hZ₀ w₀' (Subgroup.mem_subgroupOf.mpr hw₀P)).mpr (by
        rcases hw₀cases with h | h | h | h
        · left; exact Subtype.ext h
        · right; left; exact Subtype.ext h
        · right; right; left; exact Subtype.ext h
        · right; right; right; exact Subtype.ext h)) (g⁻¹ * y * g) hy₀
    calc wb' * y = (g * w₀' * g⁻¹) * y := rfl
      _ = g * (w₀' * (g⁻¹ * y * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * y * g) * w₀') * g⁻¹ := by rw [hw₀'_cent]
      _ = y * (g * w₀' * g⁻¹) := by group
      _ = y * wb' := rfl
  let w' : ↥P := ψb.symm ⟨wb', hwb_mem⟩
  have hw'cent : w' ∈ Subgroup.center ↥P := by
    have hwb_center : (⟨wb', hwb_mem⟩ : ↥Pb) ∈ Subgroup.center ↥Pb := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (hwb_cent (y : (omgGroup hQ)) y.2).symm
    have h := Subgroup.mem_map_of_mem (ψb.symm : ↥Pb →* ↥P) hwb_center
    rw [Subgroup.map_center_eq (ψb.symm : ↥Pb ≃* ↥P)] at h
    exact h
  have hψw' : ψ w' = wb' := by
    have h := MulEquiv.apply_symm_apply ψb ⟨wb', hwb_mem⟩
    exact congrArg (fun z : ↥Pb => (z : (omgGroup hQ))) h
  let w : G := (w' : G)
  have hwP : w ∈ P := w'.2
  have hw_centerIn : w ∈ centerIn P := Subgroup.mem_map_of_mem P.subtype hw'cent
  have hwL : w ∈ L := hPL hwP
  let wL : ↥L := Subgroup.inclusion hPL w'
  let c : G := w⁻¹ * x
  have hc_norm : c ∈ normalizer (L : Set G) :=
    mul_mem (inv_mem (Subgroup.le_normalizer hwL)) hxN
  have hc_central : c ∈ centralizer (L : Set G) := by
    apply t5_centralizes_of_central_comm hL.1 (Z := centerIn L) le_rfl hc_norm
    intro l hl
    let lL : ↥L := ⟨l, hl⟩
    let l'L : ↥L := ⟨x * l * x⁻¹, (Subgroup.mem_normalizer_iff.mp hxN l).mp hl⟩
    have hx'l' : ((φ l'L : omegaGroup hQ) : OGroup Q) =
        simAct Q x' ((φ lL : omegaGroup hQ) : OGroup Q) := hx'.2 lL l'L rfl
    have hcLmem : c * l * c⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hc_norm l).mp hl
    have hcl_eq : (⟨c * l * c⁻¹, hcLmem⟩ : ↥L) = wL⁻¹ * l'L * wL := by
      apply Subtype.ext
      change c * l * c⁻¹ = (wL⁻¹ * l'L * wL : G)
      show c * l * c⁻¹ = w⁻¹ * (x * l * x⁻¹) * w
      dsimp only [c]
      group
    have hφwL : ((φ wL : omegaGroup hQ) : OGroup Q) = (wb' : OGroup Q) :=
      congrArg Subtype.val hψw'
    have hφclc : ((φ ⟨c * l * c⁻¹, hcLmem⟩ : omegaGroup hQ) : OGroup Q) =
        ((φ lL : omegaGroup hQ) : OGroup Q) := by
      rw [hcl_eq, map_mul, map_mul, map_inv]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hφwL, hx'l', hx'wb, simAct_orthToSim]
      dsimp only [gbar, wb, wb', w₀']
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    have hclliLmem : c * l * c⁻¹ * l⁻¹ ∈ L := mul_mem hcLmem (inv_mem hl)
    have hmem_l : (⟨c * l * c⁻¹ * l⁻¹, hclliLmem⟩ : ↥L) ∈ φ.ker := by
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      show ((φ (⟨c * l * c⁻¹ * l⁻¹, hclliLmem⟩ : ↥L) : omegaGroup hQ) : OGroup Q) = 1
      have heq : (⟨c * l * c⁻¹ * l⁻¹, hclliLmem⟩ : ↥L) =
          ⟨c * l * c⁻¹, hcLmem⟩ * lL⁻¹ := by
        apply Subtype.ext
        dsimp only [lL]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [heq, map_mul, map_inv]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hφclc, mul_inv_cancel]
    exact Subgroup.mem_map_of_mem L.subtype (hO.ker_le_center hmem_l)
  refine ⟨c, hc_central, w, hw_centerIn, ?_⟩
  show x = w * c
  dsimp only [c]
  group

end CFSG.OddStandard.SmallF3.Omega
