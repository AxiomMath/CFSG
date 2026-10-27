module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.Fi24Inputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.Cover
public import CFSG.RankThree.PartOne.S9.OddCore.TorsionBridge

public section

namespace CFSG.EvenSporadicStandard.TwoB

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.TwoFi22

@[expose] def centralizerEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (z : X) :
    centralizer ({z} : Set X) ≃* centralizer ({e z} : Set Y) where
  toFun y := ⟨e y, by
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      mem_centralizer_singleton_iff.1 y.2]⟩
  invFun y := ⟨e.symm y, by
    rw [mem_centralizer_singleton_iff]
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, mem_centralizer_singleton_iff.1 y.2]⟩
  left_inv y := Subtype.ext (e.symm_apply_apply y)
  right_inv y := Subtype.ext (e.apply_symm_apply y)
  map_mul' a b := Subtype.ext (map_mul e (a : X) (b : X))

theorem O2In_centralizer_map {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (z : X) :
    O2In (centralizer ({e z} : Set Y)) = (O2In (centralizer ({z} : Set X))).map e.toMonoidHom := by
  have h := CFSG.pCore_map_iso 2 (centralizerEquiv e z)
  unfold O2In
  rw [← h, Subgroup.map_map, Subgroup.map_map]
  rfl

variable {X : Type} [Group X]

structure LocalAt (X : Type) [Group X] (t z : X) : Prop where
  central : t ∈ center X
  order_t : orderOf t = 2
  ne : z ≠ t
  order_z : orderOf z = 2
  twoCentral : (Nat.card (centralizer ({z} : Set X))).factorization 2 =
    (Nat.card X).factorization 2
  derived : z ∈ ⁅O2In (centralizer ({z} : Set X)), O2In (centralizer ({z} : Set X))⁆
  co2 : Nonempty (↥(centralizer ({z} : Set X)) ⧸ pCore 2 ↥(centralizer ({z} : Set X)) ≃*
    Carrier .Co2)

structure LocalR0 (X : Type) [Group X] (t z : X) : Prop where
  r0 : ∃ R₀ : Subgroup X, R₀ ≤ centralizer ({z} : Set X) ∧ IsExtraspecialPGroup 2 ↥R₀ ∧
    Nat.card R₀ = 2 ^ 23 ∧ (center R₀).map R₀.subtype = zpowers z ∧
    O2In (centralizer ({z} : Set X)) = R₀ ⊔ zpowers t ∧ Disjoint R₀ (zpowers t) ∧
    t ∈ ⁅R₀, centralizer ({z} : Set X)⁆
  irreducible : ∀ W : Subgroup X, zpowers z ⊔ zpowers t ≤ W → W ≤ O2In (centralizer ({z} : Set X)) →
    (∀ g ∈ centralizer ({z} : Set X), ∀ w ∈ W, g * w * g⁻¹ ∈ W) →
      W = zpowers z ⊔ zpowers t ∨ W = O2In (centralizer ({z} : Set X))

variable {Y : Type} [Group Y]

theorem LocalAt.map {t z : X} (h : LocalAt X t z) (e : X ≃* Y) : LocalAt Y (e t) (e z) where
  central := by
    rw [mem_center_iff]
    intro g
    have := mem_center_iff.1 h.central (e.symm g)
    have h2 := congrArg e this
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at h2
    exact h2
  order_t := by rw [MulEquiv.orderOf_eq]; exact h.order_t
  ne := fun h' => h.ne (e.injective h')
  order_z := by rw [MulEquiv.orderOf_eq]; exact h.order_z
  twoCentral := by
    rw [← Nat.card_congr (centralizerEquiv e z).toEquiv, ← Nat.card_congr e.toEquiv]
    exact h.twoCentral
  derived := by
    rw [O2In_centralizer_map, ← Subgroup.map_commutator]
    exact Subgroup.mem_map_of_mem _ h.derived
  co2 := by
    obtain ⟨f⟩ := h.co2
    refine ⟨(QuotientGroup.congr _ _ (centralizerEquiv e z).symm ?_).trans f⟩
    exact CFSG.pCore_map_iso 2 (centralizerEquiv e z).symm

theorem map_centralizer_singleton {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (z : X) :
    (centralizer ({z} : Set X)).map e.toMonoidHom = centralizer ({e z} : Set Y) := by
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply, mem_centralizer_singleton_iff,
    mem_centralizer_singleton_iff]
  constructor
  · intro h
    rw [← map_mul, ← map_mul, h]
  · intro h
    apply e.injective
    rw [map_mul, map_mul, h]

theorem LocalR0.map {t z : X} (h : LocalR0 X t z) (e : X ≃* Y) : LocalR0 Y (e t) (e z) where
  r0 := by
    obtain ⟨R₀, hle, hext, hcard, hcen, hO2, hdisj, hcomm⟩ := h.r0
    refine ⟨R₀.map e.toMonoidHom, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rintro _ ⟨r, hr, rfl⟩
      rw [mem_centralizer_singleton_iff]
      have := mem_centralizer_singleton_iff.1 (hle hr)
      show e r * e z = e z * e r
      rw [← map_mul, ← map_mul, this]
    · exact RankThree.PartOne.Torsion37.isExtraspecialPGroup_of_mulEquiv
        (R₀.equivMapOfInjective e.toMonoidHom e.injective) hext
    · rw [Subgroup.card_map_of_injective e.injective]; exact hcard
    · have := RankThree.PartOne.Torsion37.inSubgroup_center_map e.toMonoidHom e.injective R₀
      unfold inSubgroup at this
      rw [this, hcen, MonoidHom.map_zpowers]
      rfl
    · rw [O2In_centralizer_map, hO2, Subgroup.map_sup, MonoidHom.map_zpowers]
      rfl
    · rw [Subgroup.disjoint_def]
      rintro _ ⟨r, hr, rfl⟩ hy
      obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hy
      have hrt : r = t ^ k := e.injective (by rw [map_zpow]; exact hk.symm)
      have h0 := Subgroup.disjoint_def.1 hdisj hr (hrt ▸ zpow_mem (mem_zpowers t) k)
      show e r = 1
      rw [h0, map_one]
    · rw [← map_centralizer_singleton e z, ← Subgroup.map_commutator]
      exact Subgroup.mem_map_of_mem _ hcomm
  irreducible := by
    intro W' hW1 hW2 hW3
    have hpair : (zpowers z ⊔ zpowers t).map e.toMonoidHom = zpowers (e z) ⊔ zpowers (e t) := by
      rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
      rfl
    have hO2' : (O2In (centralizer ({z} : Set X))).map e.toMonoidHom =
        O2In (centralizer ({e z} : Set Y)) := (O2In_centralizer_map e z).symm
    have h1 : zpowers z ⊔ zpowers t ≤ W'.comap e.toMonoidHom := by
      rw [← Subgroup.map_le_iff_le_comap, hpair]; exact hW1
    have h2 : W'.comap e.toMonoidHom ≤ O2In (centralizer ({z} : Set X)) := by
      intro x hx
      have hx' : e x ∈ W' := hx
      have := hW2 hx'
      rw [← hO2'] at this
      obtain ⟨y, hy, hyx⟩ := this
      have : y = x := e.injective hyx
      exact this ▸ hy
    have h3 : ∀ g ∈ centralizer ({z} : Set X), ∀ w ∈ W'.comap e.toMonoidHom,
        g * w * g⁻¹ ∈ W'.comap e.toMonoidHom := by
      intro g hg w hw
      have hg' : e g ∈ centralizer ({e z} : Set Y) := by
        rw [← map_centralizer_singleton e z]; exact Subgroup.mem_map_of_mem _ hg
      have := hW3 (e g) hg' (e w) hw
      show e (g * w * g⁻¹) ∈ W'
      rwa [map_mul, map_mul, map_inv]
    have hmc : (W'.comap e.toMonoidHom).map e.toMonoidHom = W' :=
      Subgroup.map_comap_eq_self_of_surjective e.surjective W'
    rcases h.irreducible _ h1 h2 h3 with h0 | h0
    · left
      rw [← hmc, h0, hpair]
    · right
      rw [← hmc, h0, hO2']

@[expose] def TwoBLocalData : Prop :=
  ∀ (L : Type) [Group L] [Finite L], IsTwoBCover L → ∀ t : L, t ∈ center L → orderOf t = 2 →
    ∃ z : L, LocalAt L t z ∧ LocalR0 L t z

end CFSG.EvenSporadicStandard.TwoB
