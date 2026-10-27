module

public import CFSG.GH74.Generic.S45.LQData
public import CFSG.GH74.Generic.S45.LRed
public import CFSG.GH74.Generic.S45.LMod8
public import CFSG.GH74.Generic.S45.LAltCore

public section

namespace CFSG.GH74.Generic.S45.LAlt

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.Blueprint CFSG.GH74.GLS Subgroup
open CFSG.GH74.Uniqueness.Bender

theorem exists_fixed_conj {K S : Type} [Group K] [Group S] (π : K →* S)
    (hπsurj : Function.Surjective π) (hker : π.ker ≤ Subgroup.center K) (y : MulAut K)
    (ya : MulAut S) (hπy : ∀ k : K, π (y k) = ya (π k)) {s h : S} (hs : ya s = s)
    (hh : ∃ c : K, y c = c ∧ π c = h) : ∃ c : K, y c = c ∧ π c = s * h * s⁻¹ := by
  obtain ⟨sk, rfl⟩ := hπsurj s
  obtain ⟨c, hc, rfl⟩ := hh
  have hζ : y sk * sk⁻¹ ∈ Subgroup.center K := by
    apply hker
    rw [MonoidHom.mem_ker, map_mul, map_inv, hπy, hs, mul_inv_cancel]
  have hζ' := Subgroup.mem_center_iff.1 hζ
  refine ⟨sk * c * sk⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
  rw [map_mul, map_mul, map_inv, hc]
  have h1 : y sk = (y sk * sk⁻¹) * sk := by group
  calc y sk * c * (y sk)⁻¹ = ((y sk * sk⁻¹) * sk) * c * ((y sk * sk⁻¹) * sk)⁻¹ := by rw [← h1]
    _ = (y sk * sk⁻¹) * (sk * c * sk⁻¹) * (y sk * sk⁻¹)⁻¹ := by group
    _ = sk * c * sk⁻¹ := by
      have := hζ' (sk * c * sk⁻¹)
      calc (y sk * sk⁻¹) * (sk * c * sk⁻¹) * (y sk * sk⁻¹)⁻¹
          = ((sk * c * sk⁻¹) * (y sk * sk⁻¹)) * (y sk * sk⁻¹)⁻¹ := by rw [← this]
        _ = sk * c * sk⁻¹ := by group


end CFSG.GH74.Generic.S45.LAlt

namespace CFSG.GH74.Generic.S45

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.Blueprint CFSG.GH74.GLS Subgroup
open CFSG.GH74.Uniqueness.Bender CFSG.GH74.Generic.S45.LAlt
open scoped commutatorElement

theorem Hyp1310.quot_bridge {K : Type} [Group K] [Finite K] {y : MulAut K} {L : Subgroup K}
    (hyp : Hyp1310 K y L) :
    ∃ (yb : MulAut (K ⧸ Subgroup.center K)) (Lb : Subgroup (K ⧸ Subgroup.center K)) (q : ℕ),
      (∀ k : K, yb (QuotientGroup.mk k) = QuotientGroup.mk (y k)) ∧ yb * yb = 1 ∧ yb ≠ 1 ∧
      Lb ≤ autFixed yb ∧ (Lb.subgroupOf (autFixed yb)).IsSubnormal ∧
      IsSimpleGroup ↥Lb ∧ (∃ a b : ↥Lb, a * b ≠ b * a) ∧ (∀ x ∈ Lb, ¬ 4 ∣ orderOf x) ∧
      5 ≤ q ∧ Odd q ∧ (q % 8 = 3 ∨ q % 8 = 5) ∧ Nat.card ↥Lb * 2 = q * (q ^ 2 - 1) ∧
      (∀ P : ℕ → Prop, P q → HasL2Model ↥Lb P) ∧ ∀ P : ℕ → Prop, P q → HasL2Model ↥L P := by
  classical
  obtain ⟨q, hq5, hqodd, hq8, hqcard, hmodel⟩ := hyp.mod_eight
  obtain ⟨hKp, -, hy, hLfix, hno4, hLs, hLnab, -⟩ := hyp.data
  obtain ⟨yb, hyb, hyb1, hyb2⟩ := exists_induced_quotient hKp y hy
  let π : K →* K ⧸ Subgroup.center K := QuotientGroup.mk' (Subgroup.center K)
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hπker : π.ker ≤ Subgroup.center K := by rw [QuotientGroup.ker_mk']
  have hπy : ∀ k : K, π (y k) = yb (π k) := fun k => (hyb k).symm
  have hinj : Function.Injective (π.comp L.subtype) := inj_restrict π (by rw [QuotientGroup.ker_mk']) hLs hLnab
  have hC : ∀ c : K, c ∈ fixSub (Subgroup.zpowers y) ↔ y c = c := fun c =>
    ⟨fun h => h y (Subgroup.mem_zpowers y), fun h => fix_mem_zpowers h⟩
  let C : Subgroup K := fixSub (Subgroup.zpowers y)
  have hLC : L ≤ C := fun l hl => (hC l).2 (hLfix l hl)
  let eL : ↥L ≃* ↥(L.map π) :=
    MulEquiv.ofBijective (π.subgroupMap L) ⟨fun a b hab => hinj (by
      have h1 := Subtype.ext_iff.1 hab
      exact h1), π.subgroupMap_surjective L⟩
  have hLbfix : L.map π ≤ autFixed yb := by
    rintro _ ⟨l, hl, rfl⟩
    rw [mem_autFixed_iff, ← hπy, hLfix l hl]
  let H : Subgroup (K ⧸ Subgroup.center K) := C.map π
  have hHF : H ≤ autFixed yb := by
    rintro _ ⟨c, hc, rfl⟩
    rw [mem_autFixed_iff, ← hπy, (hC c).1 hc]
  have hHnorm : (H.subgroupOf (autFixed yb)).Normal := by
    refine ⟨fun h hh g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hh ⊢
    obtain ⟨c, hc, hch⟩ := hh
    have := exists_fixed_conj π hπsurj hπker y yb hπy (s := (g : K ⧸ Subgroup.center K))
      ((mem_autFixed_iff).1 g.2) ⟨c, (hC c).1 hc, hch⟩
    obtain ⟨c', hc', hc'e⟩ := this
    exact ⟨c', (hC c').2 hc', hc'e⟩
  have hLsub : (L.subgroupOf C).IsSubnormal := hyp.2.2.2.1
  let φ : ↥C →* ↥(autFixed yb) :=
    (π.comp C.subtype).codRestrict (autFixed yb) (fun c => hHF ⟨c, c.2, rfl⟩)
  have hrange : φ.range = H.subgroupOf (autFixed yb) := by
    ext ⟨x, hx⟩
    simp only [MonoidHom.mem_range, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨c, hc⟩
      exact ⟨c, c.2, congrArg Subtype.val hc⟩
    · rintro ⟨c, hc, hcx⟩
      exact ⟨⟨c, hc⟩, Subtype.ext hcx⟩
  have hφn : φ.range.Normal := by rw [hrange]; exact hHnorm
  have hsubL : ((L.subgroupOf C).map φ).IsSubnormal :=
    isSubnormal_map_of_normal_range φ hφn hLsub
  have heqL : (L.subgroupOf C).map φ = (L.map π).subgroupOf (autFixed yb) := by
    ext ⟨x, hx⟩
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨c, hcL, hc⟩
      exact ⟨c, hcL, congrArg Subtype.val hc⟩
    · rintro ⟨l, hl, hlx⟩
      exact ⟨⟨l, hLC hl⟩, hl, Subtype.ext hlx⟩
  refine ⟨yb, L.map π, q, hyb, hyb2, hyb1, hLbfix, heqL ▸ hsubL, ?_, ?_, ?_, hq5, hqodd, hq8, ?_, ?_, ?_⟩
  · have : IsSimpleGroup ↥L := hLs
    exact eL.symm.isSimpleGroup
  · obtain ⟨a, b, hab⟩ := hLnab
    exact ⟨eL a, eL b, fun h => hab (eL.injective (by rw [map_mul, map_mul, h]))⟩
  · rintro _ ⟨l, hl, rfl⟩ h4
    have h1 := orderOf_injective (π.comp L.subtype) hinj ⟨l, hl⟩
    have h2 : orderOf (π l) = orderOf l := by
      rw [show π l = (π.comp L.subtype) ⟨l, hl⟩ from rfl, h1, Subgroup.orderOf_mk]
    exact hno4 l (hLfix l hl) (by rw [← h2]; exact h4)
  · rw [← Nat.card_congr eL.toEquiv]
    exact hqcard
  · intro P hP
    obtain ⟨p, f, hp, hf, hP', hL⟩ := hmodel P hP
    exact ⟨p, f, hp, hf, hP', CFSG.LieType.CurtisTits.lieModel_of_mulEquiv eL hL⟩
  · exact hmodel


theorem Hyp1310.quot_data {K : Type} [Group K] [Finite K] {y : MulAut K} {L : Subgroup K}
    (hyp : Hyp1310 K y L) :
    ∃ (yb : MulAut (K ⧸ Subgroup.center K)) (Lb : Subgroup (K ⧸ Subgroup.center K)) (q : ℕ),
      (∀ k : K, yb (QuotientGroup.mk k) = QuotientGroup.mk (y k)) ∧ QData (K ⧸ Subgroup.center K) yb Lb q ∧
        ∀ P : ℕ → Prop, P q → HasL2Model ↥L P := by
  obtain ⟨yb, Lb, q, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := hyp.quot_bridge
  exact ⟨yb, Lb, q, h1, ⟨h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩, h14⟩

theorem Hyp1310.false_of_perfect_order_four {K : Type} [Group K] [Finite K] {y : MulAut K}
    {L : Subgroup K} (hyp : Hyp1310 K y L) {yb : MulAut (K ⧸ Subgroup.center K)}
    (hyb : ∀ k : K, yb (QuotientGroup.mk k) = QuotientGroup.mk (y k))
    {P : Subgroup (K ⧸ Subgroup.center K)} (hPle : P ≤ autFixed yb)
    (hP : ⁅P, P⁆ = P) {x : K ⧸ Subgroup.center K} (hx : x ∈ P) (h4 : 4 ∣ orderOf x) : False := by
  obtain ⟨-, -, -, -, hno4, -⟩ := hyp.data
  exact LAlt.not_four_dvd_of_perfect_fixed y hno4 yb hyb P hP
    (fun z hz => (mem_autFixed_iff).1 (hPle hz)) x hx h4

end CFSG.GH74.Generic.S45
