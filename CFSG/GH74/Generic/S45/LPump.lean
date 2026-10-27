module

public import CFSG.GH74.Generic.S45.LKCent
public import CFSG.GH74.Generic.S45.LTransfer

public section

namespace CFSG.GH74.Generic.S45

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.L5U5 CFSG.ABGLocalTools CFSG.Blueprint CFSG.GH74.GLS Subgroup
open scoped commutatorElement

section Lift

variable {G : Type} [Group G] [Finite G]

theorem mem_lift_of_involution {x : G} {K : Subgroup (CentralizerBar x)} {K₀ : Subgroup G}
    (h1 : K₀ ≤ centralizer ({x} : Set G))
    (h2 : ∀ g ∈ centralizer ({x} : Set G), ∀ k ∈ K₀, g * k * g⁻¹ ∈ K₀)
    (h4 : ∀ z ∈ K, ∃ k ∈ K₀, piC x k = z)
    (h5 : ∀ a ∈ K₀, ∀ b ∈ K₀, piC x a = piC x b → a = b)
    {v : G} (hvC : v ∈ centralizer ({x} : Set G)) (hvK : piC x v ∈ K) (hv2 : v * v = 1) :
    v ∈ K₀ := by
  obtain ⟨k, hk, hkv⟩ := h4 _ hvK
  have hkC : k ∈ centralizer ({x} : Set G) := h1 hk
  set w := k⁻¹ * v with hwdef
  have hwC : w ∈ centralizer ({x} : Set G) := mul_mem (inv_mem hkC) hvC
  have hw1 : piC x w = 1 := by
    rw [hwdef, piC_mul x (inv_mem hkC) hvC, piC_inv x hkC, hkv, inv_mul_cancel]
  have hcomm : k * w = w * k := by
    have hm : k * (w * k⁻¹ * w⁻¹) ∈ K₀ := mul_mem hk (by
      have := h2 w hwC k⁻¹ (inv_mem hk)
      simpa [mul_assoc] using this)
    have hpi : piC x (k * (w * k⁻¹ * w⁻¹)) = piC x 1 := by
      have hwk : w * k⁻¹ ∈ centralizer ({x} : Set G) := mul_mem hwC (inv_mem hkC)
      rw [piC_mul x hkC (mul_mem hwk (inv_mem hwC)), piC_mul x hwk (inv_mem hwC),
        piC_mul x hwC (inv_mem hkC), piC_inv x hkC, piC_inv x hwC, hw1, piC_one]
      simp
    have := h5 _ hm 1 (one_mem _) hpi
    have e : k * w * k⁻¹ * w⁻¹ = 1 := by
      calc k * w * k⁻¹ * w⁻¹ = k * (w * k⁻¹ * w⁻¹) := by group
        _ = 1 := this
    calc k * w = k * w * k⁻¹ * w⁻¹ * (w * k) := by group
      _ = w * k := by rw [e, one_mul]
  have hvkw : v = k * w := by rw [hwdef]; group
  have hk2 : k * k = 1 := by
    have hkk : k * k ∈ K₀ := mul_mem hk hk
    apply h5 _ hkk 1 (one_mem _)
    rw [piC_mul x hkC hkC, hkv, piC_one, ← piC_mul x hvC hvC, hv2, piC_one]
  have hw2 : w * w = 1 := by
    have : v * v = k * k * (w * w) := by
      calc v * v = k * w * (k * w) := by rw [← hvkw]
        _ = k * (w * k) * w := by group
        _ = k * (k * w) * w := by rw [← hcomm]
        _ = k * k * (w * w) := by group
    rw [hv2, hk2, one_mul] at this
    exact this.symm
  have hw : w = 1 := by
    have hwmem : (⟨w, hwC⟩ : ↥(centralizer ({x} : Set G))) ∈
        pPrimeCore 2 ↥(centralizer ({x} : Set G)) := by
      rw [piC_of_mem x hwC] at hw1
      exact (QuotientGroup.eq_one_iff _).1 hw1
    have hu2 : (⟨w, hwC⟩ : ↥(centralizer ({x} : Set G))) *
        (⟨w, hwC⟩ : ↥(centralizer ({x} : Set G))) = 1 := Subtype.ext hw2
    have h1' := eq_one_of_isPGroup_of_mem_pPrimeCore
      (isPGroup_zpowers_of_mul_self_eq_one hu2) (mem_zpowers _) hwmem
    exact congrArg Subtype.val h1'
  rw [hvkw, hw, mul_one]
  exact hk

omit [Finite G] in
theorem exists_W_of_lift {x : G} {K : Subgroup (CentralizerBar x)} (hKC : KCent ↥K)
    {K₀ : Subgroup G} (h1 : K₀ ≤ centralizer ({x} : Set G))
    (h2 : ∀ g ∈ centralizer ({x} : Set G), ∀ k ∈ K₀, g * k * g⁻¹ ∈ K₀)
    (h3 : ∀ k ∈ K₀, piC x k ∈ K) (h4 : ∀ z ∈ K, ∃ k ∈ K₀, piC x k = z)
    (h5 : ∀ a ∈ K₀, ∀ b ∈ K₀, piC x a = piC x b → a = b)
    {v : G} (hvK₀ : v ∈ K₀) (hv2 : orderOf v = 2) :
    ∃ W : Subgroup G, W ≤ centralizer ({x} : Set G) ⊓ centralizer ({v} : Set G) ∧
      (W.subgroupOf (centralizer ({x} : Set G) ⊓ centralizer ({v} : Set G))).Normal ∧
      IsSimpleGroup ↥W ∧ (∃ a b : ↥W, a * b ≠ b * a) ∧ HasL2Model ↥W Odd := by
  let φ : ↥K₀ →* ↥K :=
    { toFun := fun k => ⟨piC x k, h3 k k.2⟩
      map_one' := Subtype.ext (piC_one x)
      map_mul' := fun a b => Subtype.ext (piC_mul x (h1 a.2) (h1 b.2)) }
  have hφinj : Function.Injective φ := by
    intro a b hab
    exact Subtype.ext (h5 a a.2 b b.2 (congrArg Subtype.val hab))
  have hφsurj : Function.Surjective φ := by
    intro z
    obtain ⟨k, hk, hkz⟩ := h4 z z.2
    exact ⟨⟨k, hk⟩, Subtype.ext hkz⟩
  let e : ↥K₀ ≃* ↥K := MulEquiv.ofBijective φ ⟨hφinj, hφsurj⟩
  have hKC₀ : KCent ↥K₀ := KCent.of_mulEquiv e.symm hKC
  let v' : ↥K₀ := ⟨v, hvK₀⟩
  have hv'2 : orderOf v' = 2 := by rw [Subgroup.orderOf_mk]; exact hv2
  have hgood := hKC₀ v' hv'2
  set Cv : Subgroup G := K₀ ⊓ centralizer ({v} : Set G) with hCv
  set W : Subgroup G := ⁅Cv, Cv⁆ with hW
  have hmapC : (centralizer ({v'} : Set ↥K₀)).map K₀.subtype = Cv := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : y * v' = v' * y := mem_centralizer_singleton_iff.1 hy
      exact Subgroup.mem_inf.2 ⟨y.2, mem_centralizer_singleton_iff.2 (congrArg Subtype.val hy')⟩
    · intro hz'
      obtain ⟨hz, hzc⟩ := Subgroup.mem_inf.1 hz'
      refine ⟨⟨z, hz⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
      exact Subtype.ext (mem_centralizer_singleton_iff.1 hzc)
  have hWeq : W = (⁅centralizer ({v'} : Set ↥K₀), centralizer ({v'} : Set ↥K₀)⁆).map K₀.subtype := by
    rw [Subgroup.map_commutator, hmapC]
  have hgoodW : GoodL2 ↥W :=
    GoodL2.of_mulEquiv ((Subgroup.equivMapOfInjective _ K₀.subtype K₀.subtype_injective).trans
      (MulEquiv.subgroupCongr hWeq.symm)) hgood
  have hCvle : Cv ≤ K₀ := inf_le_left
  have hWCv : W ≤ Cv := by
    rw [hW, Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    exact Cv.mul_mem (Cv.mul_mem (Cv.mul_mem hg₁ hg₂) (Cv.inv_mem hg₁)) (Cv.inv_mem hg₂)
  refine ⟨W, ?_, ?_, hgoodW.1, hgoodW.2.1, hgoodW.2.2⟩
  · intro w hw
    exact ⟨h1 (hCvle (hWCv hw)), (hWCv hw).2⟩
  ·
    constructor
    intro n hn g
    have hnW : (n : G) ∈ W := hn
    have hgx : (g : G) ∈ centralizer ({x} : Set G) := g.2.1
    have hgv : (g : G) ∈ centralizer ({v} : Set G) := g.2.2
    have hconjCv : ∀ y : ↥(centralizer ({x} : Set G) ⊓ centralizer ({v} : Set G)),
        ∀ z ∈ Cv, (y : G) * z * (y : G)⁻¹ ∈ Cv := by
      intro y z hz
      obtain ⟨hzK, hzc⟩ := Subgroup.mem_inf.1 hz
      have hyv : Commute (y : G) v := mem_centralizer_singleton_iff.1 y.2.2
      have hzv : Commute z v := mem_centralizer_singleton_iff.1 hzc
      refine Subgroup.mem_inf.2 ⟨h2 _ y.2.1 z hzK, mem_centralizer_singleton_iff.2 ?_⟩
      exact ((hyv.mul_left hzv).mul_left hyv.inv_left).eq
    have hmapCv : Cv.map (MulAut.conj (g : G)).toMonoidHom = Cv := by
      apply le_antisymm
      · rintro _ ⟨z, hz, rfl⟩
        exact hconjCv g z hz
      · intro z hz
        refine ⟨(g : G)⁻¹ * z * (g : G), ?_, ?_⟩
        · have := hconjCv g⁻¹ z hz
          simpa using this
        · show (g : G) * ((g : G)⁻¹ * z * (g : G)) * (g : G)⁻¹ = z
          group
    have hmapW : W.map (MulAut.conj (g : G)).toMonoidHom = W := by
      rw [hW, Subgroup.map_commutator, hmapCv]
    have : (g : G) * (n : G) * (g : G)⁻¹ ∈ W.map (MulAut.conj (g : G)).toMonoidHom :=
      ⟨n, hnW, rfl⟩
    rw [hmapW] at this
    exact this

end Lift

@[expose] def B_S45_lift : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) → Gen4 G → KGH G →
    ∀ x : G, orderOf x = 2 → ∀ K : Subgroup (CentralizerBar x), IsComponent K → IsJ1OrRee ↥K →
      xbar x ∉ K → ∀ T : Subgroup G, S45Conf x K T →
      ∃ K₀ : Subgroup G, K₀ ≤ centralizer ({x} : Set G) ∧
        (∀ g ∈ centralizer ({x} : Set G), ∀ k ∈ K₀, g * k * g⁻¹ ∈ K₀) ∧
        (∀ k ∈ K₀, piC x k ∈ K) ∧ (∀ z ∈ K, ∃ k ∈ K₀, piC x k = z) ∧
        (∀ a ∈ K₀, ∀ b ∈ K₀, piC x a = piC x b → a = b)

@[expose] def B_S45_semisimple : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) → Gen4 G → KGH G →
    ∀ x : G, orderOf x = 2 → ∀ K : Subgroup (CentralizerBar x), IsComponent K → IsJ1OrRee ↥K →
      xbar x ∉ K → ∀ T : Subgroup G, S45Conf x K T →
      ∀ v : G, v ∈ T → v ∈ Pre x K → v ≠ 1 →
      ∀ W : Subgroup G, W ≤ centralizer ({x} : Set G) ⊓ centralizer ({v} : Set G) →
        (W.subgroupOf (centralizer ({x} : Set G) ⊓ centralizer ({v} : Set G))).Normal →
        IsSimpleGroup ↥W → (∃ a b : ↥W, a * b ≠ b * a) → HasL2Model ↥W Odd →
        ∃ J : Subgroup G, W ≤ J ∧ J ≤ centralizer ({v} : Set G) ∧
          (J.subgroupOf (centralizer ({v} : Set G))).IsSubnormal ∧ IsQuasisimple ↥J

theorem b_S45_pumpStruct_of_leaves
    (hl : B_S45_lift) (hs : B_S45_semisimple) :
    B_S45_pumpStruct := by
  intro G _ _ hsimple hnab hgen hKGH x hx K hKc hj hnot T hT v hvT hvK hv1
  obtain ⟨K₀, h1, h2, h3, h4, h5⟩ := hl G hsimple hnab hgen hKGH x hx K hKc hj hnot T hT
  have hvC : v ∈ centralizer ({x} : Set G) := hvK.1
  have hvK' : piC x v ∈ K := hvK.2
  have hv2 : v * v = 1 := hT.sq v hvT
  have hvord : orderOf v = 2 := orderOf_eq_prime (by rw [pow_two]; exact hv2) hv1
  have hvK₀ : v ∈ K₀ := mem_lift_of_involution h1 h2 h4 h5 hvC hvK' hv2
  obtain ⟨W, hWY, hWn, hWs, hWnab, hWL⟩ :=
    exists_W_of_lift (kCent_of_isJ1OrRee hj) h1 h2 h3 h4 h5 hvK₀ hvord
  obtain ⟨J, hWJ, hJC, hJsub, hJq⟩ :=
    hs G hsimple hnab hgen hKGH x hx K hKc hj hnot T hT v hvT hvK hv1 W hWY hWn hWs hWnab hWL
  exact ⟨W, J, hWY, hWn, hWs, hWnab, hWL, hWJ, hJC, hJsub, hJq⟩

end CFSG.GH74.Generic.S45
