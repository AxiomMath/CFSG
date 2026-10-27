module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.DResCSG1
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.DResHLevelFData
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.DResCStruct
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.DResCSHeis

public section

namespace CFSG.EvenSporadicStandard.M24Std.DRes

open Subgroup CFSG.Open
open scoped commutatorElement

section Final

variable {G : Type} [Group G] [Finite G] {L A C : Subgroup G} {z : G}

theorem perfect_le_of_centralizer (hs : LocalSetting G L z) {H : Subgroup G}
    (hH : H ≤ centralizer ({z} : Set G)) (hperf : ⁅H, H⁆ = H) : H ≤ L := by
  have key : ∀ q ∈ centralizer ({z} : Set G), ∃ l ∈ L, ∃ x ∈ zpowers z, q = l * x := by
    intro q hq
    obtain ⟨l, hl, h | h⟩ := Quad.exists_mem_L hs (mem_centralizer_singleton_iff.1 hq)
    · exact ⟨l, hl, 1, one_mem _, by rw [h, mul_one]⟩
    · exact ⟨l, hl, z, mem_zpowers z, h⟩
  have hxl : ∀ l ∈ L, ∀ x ∈ zpowers z, x * l = l * x := by
    intro l hl x hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
    exact (Commute.zpow_right (show Commute l z from Quad.comm_z hs hl) k).symm.eq
  have hle : ⁅H, H⁆ ≤ L := by
    refine commutator_le.2 fun g₁ hg₁ g₂ hg₂ => ?_
    obtain ⟨l₁, hl₁, x₁, hx₁, rfl⟩ := key g₁ (hH hg₁)
    obtain ⟨l₂, hl₂, x₂, hx₂, rfl⟩ := key g₂ (hH hg₂)
    obtain ⟨k₁, rfl⟩ := mem_zpowers_iff.1 hx₁
    obtain ⟨k₂, rfl⟩ := mem_zpowers_iff.1 hx₂
    rw [commutator_mul_central (hxl l₂ hl₂ _ hx₁) (Commute.zpow_zpow_self z k₁ k₂).eq
      (hxl l₁ hl₁ _ hx₂), commutatorElement_def]
    exact L.mul_mem (L.mul_mem (L.mul_mem hl₁ hl₂) (L.inv_mem hl₁)) (L.inv_mem hl₂)
  intro g hg
  rw [← hperf] at hg
  exact hle hg

section Assembly


theorem exists_E (h : CSide.Setup L A C z) (hst : SextetType L A)
    (e : egaLayer (egQD C ⧸ fusionOddCore (egQD C)) ≃*
      alternatingGroup (Fin 6) × alternatingGroup (Fin 6)) :
    ∃ E : Subgroup G, CSideHalf L A z E := by
  classical
  obtain ⟨φ, hY, hHeis, hfpfm⟩ := cyhyp_of_setup h hst
  obtain ⟨S1, S2, π1, π2, hS⟩ := hY.ySplit e
  obtain ⟨f₁, f₂, -, -, -, -, hZO⟩ := hY.swap e
  obtain ⟨z1, c, d, hz1, hz1ne, hz2, hu, hune, hc, hd, hc3, hd3, hcd⟩ :=
    hY.heisenberg_pair hS hZO hHeis
  have hzN : z ∈ normalizer (C : Set G) := CSide.z_mem_normalizer_C h
  have hzz : z * z = 1 := Quad.z_mul_self h.hs
  have hzi : z⁻¹ = z := Quad.z_inv h.hs
  obtain ⟨zN, hzNdef⟩ : ∃ zN : normalizer (C : Set G), (zN : G) = z := ⟨⟨z, hzN⟩, rfl⟩
  have hzt : ((zN : normalizer (C : Set G)) :
      normalizer (C : Set G) ⧸ C.subgroupOf (normalizer (C : Set G))) = CSide.zt h := by
    have : zN = ⟨z, hzN⟩ := Subtype.ext hzNdef
    rw [this]
    rfl
  have hCN : C ≤ normalizer (C : Set G) := fun c hc => le_normalizer hc
  have hC2 : ∀ c ∈ C.subgroupOf (normalizer (C : Set G)),
      ∀ c' ∈ C.subgroupOf (normalizer (C : Set G)), c * c' = c' * c := fun c hc c' hc' =>
    Subtype.ext (h.hC.comm _ (mem_subgroupOf.1 hc) _ (mem_subgroupOf.1 hc'))
  have hCe : ∀ c ∈ C.subgroupOf (normalizer (C : Set G)), c * c = 1 := fun c hc =>
    Subtype.ext (h.hCe _ (mem_subgroupOf.1 hc))
  have hCcard : Nat.card (C.subgroupOf (normalizer (C : Set G))) = 2 ^ 12 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCN).toEquiv, h.hC.card]
    norm_num
  have hfpf : ∀ n : normalizer (C : Set G),
      (n : normalizer (C : Set G) ⧸ C.subgroupOf (normalizer (C : Set G))) =
        z1 * ((zN : normalizer (C : Set G) ⧸ C.subgroupOf (normalizer (C : Set G))) * z1 *
          (zN : normalizer (C : Set G) ⧸ C.subgroupOf (normalizer (C : Set G)))⁻¹) →
      ∀ c ∈ C.subgroupOf (normalizer (C : Set G)), n * c * n⁻¹ = c → c = 1 := by
    intro n hn c hc hnc
    rw [hzt] at hn
    have huZ : z1 * (CSide.zt h * z1 * (CSide.zt h)⁻¹) ∈ Zk φ := hu
    obtain ⟨k, -, hk⟩ := mem_Zk.1 huZ
    obtain ⟨m, hm⟩ : ∃ m : egNL L A,
        (CSide.psi h m : egQD C) = z1 * (CSide.zt h * z1 * (CSide.zt h)⁻¹) := by
      obtain ⟨m, hm⟩ := k.2
      exact ⟨m, hm.trans hk⟩
    have hmZ : CSide.psi h m ∈ Zk φ := by rw [hm]; exact huZ
    have hm1 : CSide.psi h m ≠ 1 := by rw [hm]; exact hune
    have hfp := hfpfm m hmZ hm1
    have h2 : (n : normalizer (C : Set G) ⧸ C.subgroupOf (normalizer (C : Set G))) =
        QuotientGroup.mk (Subgroup.inclusion (CSide.egNL_le_normalizer_C h) m) :=
      hn.trans hm.symm
    obtain ⟨c1, hc1def⟩ : ∃ c1 : G, c1 = (n : G)⁻¹ * (m : G) := ⟨_, rfl⟩
    have hc1 : c1 ∈ C := by
      rw [hc1def]
      exact mem_subgroupOf.1 (QuotientGroup.eq.1 h2)
    have hcc : (c : G) ∈ C := mem_subgroupOf.1 hc
    have hcomm1 : c1 * (c : G) = (c : G) * c1 := h.hC.comm _ hc1 _ hcc
    have hnc' : (n : G) * (c : G) * (n : G)⁻¹ = c := congrArg Subtype.val hnc
    have hm_eq : (m : G) = n * c1 := by rw [hc1def]; group
    have hmc : (m : G) * c * (m : G)⁻¹ = c := by
      calc (m : G) * c * (m : G)⁻¹ = (n : G) * (c1 * (c : G) * c1⁻¹) * (n : G)⁻¹ := by
            rw [hm_eq]; group
        _ = (n : G) * (c : G) * (n : G)⁻¹ := by rw [hcomm1]; group
        _ = c := hnc'
    exact Subtype.ext (hfp (c : G) hcc hmc)
  obtain ⟨D1, D2, hD1, hlev⟩ := DResH.levelFData_of_levelC
    (C.subgroupOf (normalizer (C : Set G))) hC2 hCe hCcard hS.q1 hS.q2 hS.comm zN
    (Subtype.ext (by rw [Subgroup.coe_mul, hzNdef]; exact hzz))
    (fun a ha => by rw [hzt]; exact hS.swap12 a ha)
    (fun a ha => by rw [hzt]; exact hS.swap21 a ha)
    z1 hz1 hz1ne (by rw [hzt]; exact hz2) hfpf c d hc hd hc3 hd3 (by rw [hzt]; exact hcd)
  obtain ⟨hperf, hcommN, hinfN, hcardEN⟩ := levelF hlev
  set EN : Subgroup (normalizer (C : Set G)) :=
    Ecomm (C.subgroupOf (normalizer (C : Set G))) S1 with hEN
  set E : Subgroup G := EN.map (normalizer (C : Set G)).subtype with hE
  have hEmem : ∀ a ∈ E, a ∈ normalizer (C : Set G) := by
    rintro _ ⟨a', -, rfl⟩
    exact a'.2
  have hcommE : ∀ a ∈ E, ∀ b ∈ E, a * (z * b * z⁻¹) = (z * b * z⁻¹) * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have := congrArg Subtype.val (hcommN a ha b hb)
    simpa [hzNdef] using this
  have hinfE : ∀ a ∈ E, z * a * z⁻¹ ∈ E → a = 1 := by
    rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hba⟩
    have h1 : zN * a * zN⁻¹ = b := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hzNdef]
      exact hba.symm
    have := hinfN a ha (h1 ▸ hb)
    rw [this]
    rfl
  have hconj : ∀ g : G, z * (z * g * z⁻¹) * z⁻¹ = g := fun g => by
    calc z * (z * g * z⁻¹) * z⁻¹ = (z * z) * g * (z * z)⁻¹ := by group
      _ = g := by rw [hzz]; group
  let δ : E →* G := MonoidHom.mk' (fun a : E => (a : G) * (z * (a : G) * z⁻¹)) (by
    intro a b
    have h1 := hcommE (b : G) b.2 (a : G) a.2
    show ((a : G) * (b : G)) * (z * ((a : G) * (b : G)) * z⁻¹) =
      ((a : G) * (z * (a : G) * z⁻¹)) * ((b : G) * (z * (b : G) * z⁻¹))
    calc ((a : G) * (b : G)) * (z * ((a : G) * (b : G)) * z⁻¹)
        = (a : G) * ((b : G) * (z * (a : G) * z⁻¹)) * (z * (b : G) * z⁻¹) := by group
      _ = (a : G) * ((z * (a : G) * z⁻¹) * (b : G)) * (z * (b : G) * z⁻¹) := by rw [h1]
      _ = ((a : G) * (z * (a : G) * z⁻¹)) * ((b : G) * (z * (b : G) * z⁻¹)) := by group)
  have hδz : ∀ a : E, δ a * z = z * δ a := by
    intro a
    have h1 := hcommE (a : G) a.2 (a : G) a.2
    have h2 : z * ((a : G) * (z * (a : G) * z⁻¹)) * z⁻¹ = (a : G) * (z * (a : G) * z⁻¹) := by
      calc z * ((a : G) * (z * (a : G) * z⁻¹)) * z⁻¹
          = (z * (a : G) * z⁻¹) * (z * (z * (a : G) * z⁻¹) * z⁻¹) := by group
        _ = (z * (a : G) * z⁻¹) * (a : G) := by rw [hconj]
        _ = (a : G) * (z * (a : G) * z⁻¹) := h1.symm
    show (a : G) * (z * (a : G) * z⁻¹) * z = z * ((a : G) * (z * (a : G) * z⁻¹))
    calc (a : G) * (z * (a : G) * z⁻¹) * z
        = (z * ((a : G) * (z * (a : G) * z⁻¹)) * z⁻¹) * z := by rw [h2]
      _ = z * ((a : G) * (z * (a : G) * z⁻¹)) := by group
  have hrange_le : δ.range ≤ centralizer ({z} : Set G) := by
    rintro _ ⟨a, rfl⟩
    exact mem_centralizer_singleton_iff.2 (hδz a)
  have hEperf : ⁅E, E⁆ = E := by
    rw [hE, ← Subgroup.map_commutator, hperf]
  have hEtop : commutator E = ⊤ := Group.isPerfect_def.1 (Subgroup.isPerfect_iff.2 hEperf)
  have hδperf : ⁅δ.range, δ.range⁆ = δ.range := by
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator]
    have : ⁅(⊤ : Subgroup E), ⊤⁆ = ⊤ := hEtop
    rw [this]
  have hδL : δ.range ≤ L := perfect_le_of_centralizer h.hs hrange_le hδperf
  refine ⟨E, hcommE, hinfE, ?_, ?_⟩
  · intro a ha
    have hmem : a * (z * a * z⁻¹) ∈ L := hδL ⟨⟨a, ha⟩, rfl⟩
    have hN' : a * (z * a * z⁻¹) ∈ normalizer (C : Set G) :=
      mul_mem (hEmem a ha) (mul_mem (mul_mem hzN (hEmem a ha)) (inv_mem hzN))
    exact CSide.mem_egNL_of h hmem hN'
  · rw [hE, Subgroup.card_map_of_injective (normalizer (C : Set G)).subtype_injective, hEN,
      hcardEN, hD1, DResH.LevelC.card_quasi hS.q1, (sym6Index_of_type hst).1]
    norm_num

end Assembly

end Final

theorem ega81CSideHalf :
    Ega81CSideHalf := by
  intro G _ _ L z hZ hstd hs A B C D hF hE
  obtain ⟨e⟩ := hE
  exact exists_E ⟨hs, hF.pair.1, hF.sextet, hF.cData, hF.c_elem⟩ hF.pair.sextet e

theorem residue_cStruct :
    Ega81Sit fun _ _ _ _ _ _ _ C D =>
      Nonempty (egaLayer (egQD C ⧸ fusionOddCore (egQD C)) ≃*
        alternatingGroup (Fin 6) × alternatingGroup (Fin 6)) →
      HasElemAbThree81 (egQD D ⧸ fusionOddCore (egQD D)) :=
  residue_cStruct_of_half ega81CSideHalf

end CFSG.EvenSporadicStandard.M24Std.DRes
