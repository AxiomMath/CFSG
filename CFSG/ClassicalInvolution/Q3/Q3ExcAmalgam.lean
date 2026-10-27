module

public import CFSG.ClassicalInvolution.Q3.ClassicalFundamental
public import CFSG.ClassicalInvolution.Q3.Q3PlanSplit

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution
open scoped MatrixGroups

theorem exc3_eq_neg_one_of_orderOf_eq_two {s : SL(2, ZMod 3)} (h : orderOf s = 2) : s = -1 := by
  have h1 : s * s = 1 := by
    have := pow_orderOf_eq_one s
    rwa [h, pow_two] at this
  have key : ∀ s : SL(2, ZMod 3), s * s = 1 → s = 1 ∨ s = -1 := by decide +kernel
  rcases key s h1 with h2 | h2
  · rw [h2, orderOf_one] at h
    exact absurd h (by norm_num)
  · exact h2

theorem exc3_neg_one_ne_one : (-1 : SL(2, ZMod 3)) ≠ 1 := by decide +kernel

section Amalgam

variable {G : Type} [Group G]

theorem exc3_eq_or_eq_of_isSubnormal_sup {J L₀ L : Subgroup G} {ε : G}
    (eJ : SL(2, ZMod 3) ≃* J) (eL₀ : SL(2, ZMod 3) ≃* L₀) (eL : SL(2, ZMod 3) ≃* L)
    (hcomm : ∀ a ∈ J, ∀ b ∈ L₀, a * b = b * a) (hε2 : orderOf ε = 2)
    (hεL₀ : ε ∈ L₀) (hεL : ε ∈ L) (hint : ∀ x ∈ J ⊓ L₀, x = 1 ∨ x = ε)
    (hLS : L ≤ J ⊔ L₀) (hsub : IsSubnormal L (J ⊔ L₀)) : L = J ∨ L = L₀ := by
  have : Finite J := Finite.of_equiv _ eJ.toEquiv
  have : Finite L₀ := Finite.of_equiv _ eL₀.toEquiv
  have hcard : ∀ {A : Subgroup G}, (SL(2, ZMod 3) ≃* A) → Nat.card A = 24 := fun {A} e => by
    rw [← Nat.card_congr e.toEquiv, natCard_sl2Three]
  have hε1 : ε * ε = 1 := by rw [← pow_two, ← hε2]; exact pow_orderOf_eq_one ε
  have hc' : ∀ (a : J) (b : L₀), Commute (J.subtype a) (L₀.subtype b) := fun a b =>
    hcomm a a.2 b b.2
  let Φ : ↥J × ↥L₀ →* G := J.subtype.noncommCoprod L₀.subtype hc'
  have hΦapp : ∀ p : ↥J × ↥L₀, Φ p = (p.1 : G) * (p.2 : G) := fun p => rfl
  have hrange : Φ.range = J ⊔ L₀ := by
    rw [show Φ.range = J.subtype.range ⊔ L₀.subtype.range from
      MonoidHom.noncommCoprod_range J.subtype L₀.subtype hc', Subgroup.range_subtype,
      Subgroup.range_subtype]
  let π : ↥J × ↥L₀ →* ↥Φ.range := Φ.rangeRestrict
  have hπ : Function.Surjective π := MonoidHom.rangeRestrict_surjective Φ
  have hπval : ∀ p, ((π p : ↥Φ.range) : G) = Φ p := fun p => rfl
  have hkerm : ∀ p ∈ π.ker, Φ p = 1 := fun p hp => by
    have := congrArg Subtype.val (MonoidHom.mem_ker.mp hp)
    simpa [hπval] using this
  have hker1 : ∀ p ∈ π.ker, (p.1 : G) ∈ L₀ := fun p hp => by
    have h1 := hkerm p hp
    rw [hΦapp] at h1
    have : (p.1 : G) = (p.2 : G)⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [this]
    exact L₀.inv_mem p.2.2
  have hker2 : ∀ p ∈ π.ker, (p.2 : G) ∈ J := fun p hp => by
    have h1 := hkerm p hp
    rw [hΦapp] at h1
    have : (p.2 : G) = (p.1 : G)⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [this]
    exact J.inv_mem p.1.2
  have hcen : π.ker ≤ Subgroup.center (↥J × ↥L₀) := by
    intro p hp
    rw [Subgroup.mem_center_iff]
    intro q
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · exact hcomm q.1 q.1.2 p.1 (hker1 p hp)
    · exact (hcomm p.2 (hker2 p hp) q.2 q.2.2).symm
  have h2 : IsPGroup 2 π.ker := by
    refine IsPGroup.iff_orderOf.mpr fun x => ?_
    have hx2 : (x : ↥J × ↥L₀) ^ 2 = 1 := by
      have hxa : ((x : ↥J × ↥L₀).1 : G) = 1 ∨ ((x : ↥J × ↥L₀).1 : G) = ε :=
        hint _ ⟨(x : ↥J × ↥L₀).1.2, hker1 x x.2⟩
      have hxb : ((x : ↥J × ↥L₀).2 : G) = ((x : ↥J × ↥L₀).1 : G)⁻¹ := by
        have h1 := hkerm x x.2
        rw [hΦapp] at h1
        exact eq_inv_of_mul_eq_one_right h1
      have hεinv : ε⁻¹ = ε := inv_eq_of_mul_eq_one_right hε1
      refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
      · rcases hxa with h | h <;> simp [pow_two, h, hε1]
      · simp only [pow_two, Prod.snd_mul, Subgroup.coe_mul, hxb, Prod.snd_one, Subgroup.coe_one]
        rcases hxa with h | h <;> simp [h, hε1, hεinv]
    have hdvd : orderOf x ∣ 2 := by
      rw [← Subgroup.orderOf_coe]
      exact orderOf_dvd_of_pow_eq_one hx2
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩
  have hLle : L ≤ Φ.range := hrange ▸ hLS
  let LX : Subgroup ↥Φ.range := L.subgroupOf Φ.range
  let e' : SL(2, ZMod 3) ≃* ↥LX := eL.trans (Subgroup.subgroupOfEquivOfLe hLle).symm
  obtain ⟨β, hβinj, hβ⟩ := exists_hom_lift_sl2Three π hπ hcen h2 LX e'
  have hΦβ : ∀ s, Φ (β s) = (eL s : G) := fun s => by
    have := congrArg (fun x : ↥Φ.range => (x : G)) (hβ s)
    exact this
  let L₁ : Subgroup (↥J × ↥L₀) := β.range
  let eL₁ : SL(2, ZMod 3) ≃* ↥L₁ := MonoidHom.ofInjective hβinj
  have hsubX : IsSubnormal LX ⊤ := by
    have h1 := isSubnormal_subgroupOf (hrange ▸ hsub : IsSubnormal L Φ.range) Φ.range
    rwa [Subgroup.subgroupOf_self] at h1
  have hsubT : IsSubnormal (LX.comap π) ⊤ := by
    have h1 := isSubnormal_comap₃ π hsubX
    rwa [Subgroup.comap_top] at h1
  have hL₁le : L₁ ≤ LX.comap π := by
    rintro _ ⟨s, rfl⟩
    rw [Subgroup.mem_comap, hβ]
    exact (e' s).2
  have hL₁sub : IsSubnormal L₁ ⊤ := by
    refine isSubnormal_trans ?_ hsubT
    refine isSubnormal_of_normal_subgroupOf hL₁le ?_
    rw [Subgroup.normal_subgroupOf_iff hL₁le]
    intro y x hy hx
    have hx' : π x ∈ LX := hx
    obtain ⟨s, hs⟩ := e'.surjective ⟨π x, hx'⟩
    have hs' : π (β s) = π x := by rw [hβ, hs]
    have hk : (β s)⁻¹ * x ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hs', inv_mul_cancel]
    obtain ⟨k, hkker, rfl⟩ : ∃ k ∈ π.ker, x = β s * k := ⟨(β s)⁻¹ * x, hk, by group⟩
    have hkc : y * k = k * y := Subgroup.mem_center_iff.mp (hcen hkker) y
    have hconj : β s * k * y * (β s * k)⁻¹ = β s * y * (β s)⁻¹ := by
      calc β s * k * y * (β s * k)⁻¹ = β s * (k * y) * k⁻¹ * (β s)⁻¹ := by group
        _ = β s * (y * k) * k⁻¹ * (β s)⁻¹ := by rw [hkc]
        _ = β s * y * (β s)⁻¹ := by group
    rw [hconj]
    exact L₁.mul_mem (L₁.mul_mem ⟨s, rfl⟩ hy) (L₁.inv_mem ⟨s, rfl⟩)
  have hεeq : eL (-1) = ⟨ε, hεL⟩ := by
    have h1 : orderOf (eL.symm ⟨ε, hεL⟩) = 2 := by
      have := orderOf_injective eL.symm.toMonoidHom eL.symm.injective ⟨ε, hεL⟩
      simp only [MulEquiv.coe_toMonoidHom] at this
      rw [this, Subgroup.orderOf_mk]
      exact hε2
    have h2' := exc3_eq_neg_one_of_orderOf_eq_two h1
    rw [← h2']
    exact eL.apply_symm_apply _
  set z : ↥J × ↥L₀ := β (-1) with hz
  have hzε : (z.1 : G) * (z.2 : G) = ε := by
    have := hΦβ (-1)
    rw [hεeq, hΦapp] at this
    exact this
  have hzL₁ : z ∈ L₁ := ⟨-1, rfl⟩
  have hz1 : z ≠ 1 := by
    intro h
    exact exc3_neg_one_ne_one (hβinj (by rw [← hz, h, map_one]))
  have hcL₀ : (z.1 : G) ∈ L₀ := by
    have : (z.1 : G) = ε * (z.2 : G)⁻¹ := eq_mul_inv_of_mul_eq hzε
    rw [this]
    exact L₀.mul_mem hεL₀ (L₀.inv_mem z.2.2)
  have hLsurj : ∀ y ∈ L, ∃ s, Φ (β s) = y := fun y hy => by
    obtain ⟨s, hs⟩ := eL.surjective ⟨y, hy⟩
    exact ⟨s, by rw [hΦβ, hs]⟩
  rcases hint _ ⟨z.1.2, hcL₀⟩ with hc | hc
  ·
    right
    have hd : (z.2 : G) = ε := by
      have := hzε
      rw [hc, one_mul] at this
      exact this
    let L₂ : Subgroup (↥L₀ × ↥J) := L₁.map (MulEquiv.prodComm).toMonoidHom
    have hL₂sub : IsSubnormal L₂ ⊤ := by
      have h1 := CFSG.ComponentClassification.Components.chain_map
        (MulEquiv.prodComm (M := ↥J) (N := ↥L₀)).toMonoidHom hL₁sub
      rwa [Subgroup.map_top_of_surjective _ (MulEquiv.prodComm).surjective] at h1
    let eL₂ : SL(2, ZMod 3) ≃* ↥L₂ := eL₁.trans
      (L₁.equivMapOfInjective _ (MulEquiv.prodComm).injective)
    have hzL₂ : (z.2, z.1) ∈ L₂ := ⟨z, hzL₁, rfl⟩
    have hz2' : (z.2, z.1) ≠ 1 := fun h =>
      hz1 (Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h))
    have hall := snd_eq_one_of_isSubnormal_prod eL₂ hL₂sub (Or.inr (Or.inr ⟨eJ⟩)) hzL₂ hz2'
      (Subtype.ext (by simpa using hc))
    have hLL₀ : L ≤ L₀ := by
      intro y hy
      obtain ⟨s, hs⟩ := hLsurj y hy
      have h1 := hall ((β s).2, (β s).1) ⟨β s, ⟨s, rfl⟩, rfl⟩
      have h1' : ((β s).1 : G) = 1 := congrArg Subtype.val h1
      rw [← hs, hΦapp, h1', one_mul]
      exact (β s).2.2
    exact eq_of_le_of_natCard_le eL hLL₀ (by rw [hcard eL₀])
  ·
    left
    have hd : (z.2 : G) = 1 := by
      have := hzε
      rw [hc] at this
      exact mul_left_cancel (this.trans (mul_one ε).symm)
    have hall := snd_eq_one_of_isSubnormal_prod eL₁ hL₁sub (Or.inr (Or.inr ⟨eL₀⟩)) hzL₁ hz1
      (Subtype.ext hd)
    have hLJ : L ≤ J := by
      intro y hy
      obtain ⟨s, hs⟩ := hLsurj y hy
      have h1 := hall (β s) ⟨s, rfl⟩
      have h1' : ((β s).2 : G) = 1 := congrArg Subtype.val h1
      rw [← hs, hΦapp, h1', mul_one]
      exact (β s).1.2
    exact eq_of_le_of_natCard_le eL hLJ (by rw [hcard eJ])

end Amalgam

end CFSG.ClassicalInvolution.Q3
