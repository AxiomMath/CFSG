module

public import CFSG.GH74.Generic.S3.Nontriv3

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.L5U5 CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup
open CFSG.GH74.Generic.S1 (barConj barConj_xbar barConj_barOf)

section Inner

variable {G : Type} [Group G] [Finite G]

theorem inner_false {x : G} {K : Subgroup (CentralizerBar x)} (hset : S3Setup G x K) (honly : OnlyInvX x K)
    (hfus : NoFusionAt x K) {t : StatedLieTag} {p f : ℕ} {y : G} {Iw Iv : Subgroup G}
    (hnd : NbrData G t p f x y Iw Iv) (himg : imgBar x Iw = K)
    (H0 : IsComponent (S45.barSub (y * x) Iv)) {g : G} (hne : g * x * g⁻¹ ≠ x)
    (hcx : (g * x * g⁻¹) * x = x * (g * x * g⁻¹))
    (hin : ∃ a ∈ Iw, ∀ m ∈ Iw, (g * x * g⁻¹) * m * (g * x * g⁻¹)⁻¹ = a * m * a⁻¹) : False := by
  have hxx : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hset.inv, pow_two] at this
  have hx1 : x ≠ 1 := by
    intro h
    have := hset.inv
    rw [h, orderOf_one] at this
    omega
  have hy2 : y * y = 1 := by
    have := pow_orderOf_eq_one y
    rwa [hnd.y_inv, pow_two] at this
  have hy1 : y ≠ 1 := by
    intro h
    have := hnd.y_inv
    rw [h, orderOf_one] at this
    omega
  have hx'2 : (g * x * g⁻¹) * (g * x * g⁻¹) = 1 := by
    calc g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
      _ = 1 := by rw [hxx]; group
  have hx'1 : g * x * g⁻¹ ≠ 1 := by
    intro h
    apply hx1
    calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  have hIwle : Iw ≤ centralizer ({x} : Set G) := hnd.comp_w.1.1
  have hyIw : y ∈ Iw := hnd.Iv_le hnd.y_Iv
  have hclass : ∀ a ∈ Iw, a * a = 1 → a ≠ 1 → ∃ h ∈ Iw, h * y * h⁻¹ = a := fun a ha ha2 ha1 =>
    b_L3_class G t p f hnd.tag hnd.prime.1 hnd.prime.2.1 hnd.prime.2.2 Iw
      hnd.comp_w.1.isQuasisimple hnd.odd_w hnd.model_w y hyIw a ha hy2 hy1 ha2 ha1
  obtain ⟨a, haI, hact⟩ := hin
  obtain ⟨a₂, ha₂I, c₂, hc₂C, ha₂2, hc₂2, hxeq⟩ :=
    exists_split_of_inner hnd.odd_w hx'2 haI hact
  by_cases hc : c₂ = 1
  ·
    subst hc
    have hxa : g * x * g⁻¹ = a₂ := by rw [hxeq, mul_one]
    have ha1 : a₂ ≠ 1 := fun h => hx'1 (by rw [hxa, h])
    obtain ⟨h, hhI, hht⟩ := hclass a₂ ha₂I ha₂2 ha1
    refine hfus t p f y Iw Iv hnd himg H0 ⟨h⁻¹ * g, ?_⟩
    calc h⁻¹ * g * x * (h⁻¹ * g)⁻¹ = h⁻¹ * (g * x * g⁻¹) * h := by group
      _ = h⁻¹ * (h * y * h⁻¹) * h := by rw [hxa, hht]
      _ = y := by group
  ·
    have hA : Commute a₂ x := Subgroup.mem_centralizer_singleton_iff.1 (hIwle ha₂I)
    have hB : Commute (g * x * g⁻¹) x := hcx
    have hc₂eq : c₂ = a₂⁻¹ * (g * x * g⁻¹) := (inv_mul_eq_iff_eq_mul.2 hxeq).symm
    have hc₂x : c₂ * x = x * c₂ := by
      have : Commute (a₂⁻¹ * (g * x * g⁻¹)) x := (hA.inv_left).mul_left hB
      rw [hc₂eq]; exact this
    have hc₂Cx : c₂ ∈ centralizer ({x} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 hc₂x
    have hxCx : x ∈ centralizer ({x} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 rfl
    have hxCIw : x ∈ centralizer (Iw : Set G) := by
      rw [mem_centralizer_iff]
      intro m hm
      exact Subgroup.mem_centralizer_singleton_iff.1 (hIwle hm)
    have hcx_eq : c₂ = x :=
      eq_of_commuting_involutions hset.inv honly himg hc₂Cx hxCx hc₂C hxCIw hc₂2 hxx hc hx1 hc₂x
    have hxeq' : g * x * g⁻¹ = a₂ * x := by rw [hxeq, hcx_eq]
    have ha1 : a₂ ≠ 1 := fun h => hne (by rw [hxeq', h, one_mul])
    obtain ⟨h, hhI, hht⟩ := hclass a₂ ha₂I ha₂2 ha1
    have hhx : h * x = x * h := Subgroup.mem_centralizer_singleton_iff.1 (hIwle hhI)
    have hhx' : h⁻¹ * x = x * h⁻¹ := by
      calc h⁻¹ * x = h⁻¹ * (x * h) * h⁻¹ := by group
        _ = h⁻¹ * (h * x) * h⁻¹ := by rw [hhx]
        _ = x * h⁻¹ := by group
    have hxw : g * x * g⁻¹ = h * (y * x) * h⁻¹ := by
      calc g * x * g⁻¹ = a₂ * x := hxeq'
        _ = (h * y * h⁻¹) * x := by rw [hht]
        _ = h * y * (h⁻¹ * x) := by group
        _ = h * y * (x * h⁻¹) := by rw [hhx']
        _ = h * (y * x) * h⁻¹ := by group
    have hyC : y ∈ centralizer ({y * x} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc y * (y * x) = y * (x * y) := by rw [hnd.comm]
        _ = (y * x) * y := by rw [mul_assoc]
    obtain ⟨F, hFf, hFfin, hF, ⟨e⟩⟩ := hnd.Iv_iso
    have hoddF : Odd (Nat.card F) := by
      rw [hF]; exact (hnd.prime.1.odd_of_ne_two hnd.prime.2.1).pow
    have hIvc : ∀ i ∈ Iv, i * y = y * i :=
      central_of_involution_of_equiv_sl2 hoddF e hnd.y_Iv hy2 hy1
    have hmem₀ : proj (y * x) ⟨y, hyC⟩ ∈ S45.barSub (y * x) Iv :=
      S45.proj_mem_barSub hyC hnd.y_Iv
    have hcent₀ : ∀ l ∈ S45.barSub (y * x) Iv,
        l * proj (y * x) ⟨y, hyC⟩ = proj (y * x) ⟨y, hyC⟩ * l := by
      intro l hl
      obtain ⟨g', hg', hgJ, rfl⟩ := S45.mem_barSub.1 hl
      have : (⟨g', hg'⟩ : ↥(centralizer ({y * x} : Set G))) * ⟨y, hyC⟩ =
          ⟨y, hyC⟩ * ⟨g', hg'⟩ := Subtype.ext (hIvc g' hgJ)
      rw [← map_mul, ← map_mul, this]
    have hb : h * y * h⁻¹ ∈ centralizer ({h * (y * x) * h⁻¹} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hyy : y * (y * x) = (y * x) * y := Subgroup.mem_centralizer_singleton_iff.1 hyC
      calc h * y * h⁻¹ * (h * (y * x) * h⁻¹) = h * (y * (y * x)) * h⁻¹ := by group
        _ = h * ((y * x) * y) * h⁻¹ := by rw [hyy]
        _ = h * (y * x) * h⁻¹ * (h * y * h⁻¹) := by group
    obtain ⟨hΛ, hmemΛ, hcentΛ⟩ := conj_component_central h H0 hyC hmem₀ hcent₀ hb
    have hb2 : h * y * h⁻¹ * (h * y * h⁻¹) = 1 := by
      calc h * y * h⁻¹ * (h * y * h⁻¹) = h * (y * y) * h⁻¹ := by group
        _ = 1 := by rw [hy2]; group
    have hb1 : h * y * h⁻¹ ≠ 1 := by
      intro h0
      apply hy1
      calc y = h⁻¹ * (h * y * h⁻¹) * h := by group
        _ = 1 := by rw [h0]; group
    have hbw : h * y * h⁻¹ ≠ h * (y * x) * h⁻¹ := by
      intro h0
      apply hx1
      have h3 : y = y * x := by
        have := congrArg (fun z => h⁻¹ * z * h) h0
        simpa [mul_assoc] using this
      have h4 : y * x = y := h3.symm
      calc x = y⁻¹ * (y * x) := by group
        _ = y⁻¹ * y := by rw [h4]
        _ = 1 := by group
    exact false_of_conj_component hset honly hxw _ hΛ hb hb2 hb1 hbw hmemΛ hcentΛ

theorem inner_false_of_isConj {x : G} {K : Subgroup (CentralizerBar x)} (hset : S3Setup G x K)
    (honly : OnlyInvX x K) (hfus : NoFusionAt x K) {t : StatedLieTag} {p f : ℕ} {y : G} {Iw Iv : Subgroup G}
    (hnd : NbrData G t p f x y Iw Iv) (himg : imgBar x Iw = K)
    (H0 : IsComponent (S45.barSub (y * x) Iv)) {z : G} (hz : IsConj x z) (hne : z ≠ x)
    (hcx : z * x = x * z) (hin : ∃ a ∈ Iw, ∀ m ∈ Iw, z * m * z⁻¹ = a * m * a⁻¹) : False := by
  obtain ⟨g, rfl⟩ := isConj_iff.1 hz
  exact inner_false hset honly hfus hnd himg H0 hne hcx hin

end Inner

end CFSG.GH74.Generic.S3
