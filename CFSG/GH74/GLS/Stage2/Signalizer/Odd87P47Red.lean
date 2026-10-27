module

public import CFSG.GH74.GLS.Stage2.Signalizer.Bridge
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
open scoped commutatorElement

section Sylow

theorem xBar_isSylowOf_top {G : Type} [Group G] [Finite G] {p : ℕ} {H S : Subgroup G}
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 S H) :
    CFSG.ABGLocalTools.IsSylowOf 2 (xBar p H S) (⊤ : Subgroup (Sec H (pCore p ↥H))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.ABGLocalTools.isSylowOf_iff] at hS ⊢
  obtain ⟨hSH, hSp, hdvd⟩ := hS
  refine ⟨le_top, ?_, ?_⟩
  · have h1 : IsPGroup 2 ↥(S.subgroupOf H) := hSp.of_equiv (Subgroup.subgroupOfEquivOfLe hSH).symm
    exact h1.map (QuotientGroup.mk' (pCore p ↥H))
  · rw [Subgroup.relIndex_top_right]
    unfold xBar
    rw [Subgroup.index_map]
    have hsurj : (QuotientGroup.mk' (pCore p ↥H)).range = ⊤ :=
      MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)
    rw [hsurj, Subgroup.index_top, mul_one]
    intro h2
    apply hdvd
    have : (S.subgroupOf H).index = S.relIndex H := rfl
    rw [← this]
    exact h2.trans (Subgroup.index_dvd_of_le le_sup_left)

theorem pCore_two_le_sylow {Y : Type} [Group Y] [Finite Y] {S' : Subgroup Y}
    (h : CFSG.ABGLocalTools.IsSylowOf 2 S' ⊤) : pCore 2 Y ≤ S' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.ABGLocalTools.isSylowOf_iff] at h
  obtain ⟨-, hp, hdvd⟩ := h
  rw [Subgroup.relIndex_top_right] at hdvd
  have := (pCore_isPGroup (p := 2) (G := Y)).le_sylow_of_normal (hp.toSylow hdvd)
  simpa using this

end Sylow

section Commutators

variable {Y : Type} [Group Y]

theorem commutator_eq_bot_of_normal_two {R X : Subgroup Y} [R.Normal] (hR : IsPGroup 2 R)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hX : IsPGroup p X)
    (hRX : R ≤ normalizer (X : Set Y)) : ⁅R, X⁆ = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdisj : Disjoint R X := IsPGroup.disjoint_of_ne 2 p (Ne.symm hp2) R X hR hX
  have h1 : ⁅R, X⁆ ≤ R := Subgroup.commutator_le_left R X
  have h2 : ⁅R, X⁆ ≤ X := by
    rw [Subgroup.commutator_le]
    intro r hr x hx
    have h3 := (Subgroup.mem_normalizer_iff.mp (hRX hr) x).mp hx
    rw [commutatorElement_def]
    have : r * x * r⁻¹ * x⁻¹ = (r * x * r⁻¹) * x⁻¹ := by group
    rw [this]
    exact X.mul_mem h3 (X.inv_mem hx)
  exact le_bot_iff.mp (hdisj h1 h2)

theorem comm_layer_ne_bot [Finite Y] {X : Subgroup Y} (hX : X ≠ ⊥)
    (hb : X ⊓ centralizer ((pCore 2 Y ⊔ layer Y : Subgroup Y) : Set Y) = ⊥)
    (hR : ⁅pCore 2 Y, X⁆ = ⊥) : ⁅layer Y, X⁆ ≠ ⊥ := by
  intro hL
  apply hX
  rw [← le_bot_iff, ← hb]
  refine le_inf le_rfl ?_
  rw [Subgroup.le_centralizer_iff]
  exact sup_le (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hR)
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hL)

end Commutators

section Image

variable {G : Type} [Group G]

theorem xBar_le_normalizer {z : G} {H X S : Subgroup G} {p : ℕ} (sig : Sig4Sub G z H p X)
    (hSz : S ≤ centralizer ({z} : Set G)) :
    xBar p H S ≤ normalizer
      ((xBar p H X : Subgroup (Sec H (pCore p ↥H))) : Set (Sec H (pCore p ↥H))) := by
  rintro _ ⟨s, hs, rfl⟩
  exact mk_mem_normalizer_xBar p (sig.A.inv (s : G) s.2 (hSz hs))

theorem xBar_le_centralizer_z {z : G} {H S : Subgroup G} {p : ℕ} (hz : z ∈ H)
    (hSz : S ≤ centralizer ({z} : Set G)) :
    xBar p H S ≤ centralizer
      (({zSec z H hz (pCore p ↥H)} : Set (Sec H (pCore p ↥H)))) := by
  rintro _ ⟨s, hs, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hc : (s : G) * z = z * (s : G) := Subgroup.mem_centralizer_singleton_iff.mp (hSz hs)
  have h2 : (s : ↥H) * ⟨z, hz⟩ = ⟨z, hz⟩ * (s : ↥H) := Subtype.ext hc
  have h3 := congrArg (QuotientGroup.mk' (pCore p ↥H)) h2
  simp only [map_mul] at h3
  unfold zSec
  exact h3

theorem isElemAbelian_subgroupOf {H E : Subgroup G} (hE : CFSG.Open.IsElemAbelian 2 E) :
    CFSG.Open.IsElemAbelian 2 (E.subgroupOf H) := CFSG.Open.IsElemAbelian.subgroupOf hE H

theorem exists_elemAbelian_xBar {p : ℕ} {H S E : Subgroup G} (hodd : Odd (Nat.card ↥(pCore p ↥H)))
    (hES : E ≤ S) (hSH : S ≤ H) (hE : CFSG.Open.IsElemAbelian 2 E) :
    ∃ E' : Subgroup (Sec H (pCore p ↥H)), E' ≤ xBar p H S ∧ CFSG.Open.IsElemAbelian 2 E' ∧
      Nat.card ↥E' = Nat.card ↥E := by
  have hEH : E ≤ H := hES.trans hSH
  set E₀ : Subgroup ↥H := E.subgroupOf H with hE₀
  have hE₀ab : CFSG.Open.IsElemAbelian 2 E₀ := isElemAbelian_subgroupOf hE
  let g : ↥E₀ →* Sec H (pCore p ↥H) := (QuotientGroup.mk' (pCore p ↥H)).comp E₀.subtype
  have hinj : Function.Injective g := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx' : (QuotientGroup.mk' (pCore p ↥H) (x : ↥H)) = 1 := hx
    have hxN : (x : ↥H) ∈ pCore p ↥H := (QuotientGroup.eq_one_iff _).mp hx'
    have h2 : (x : ↥H) ^ 2 = 1 := hE₀ab.2 x x.2
    have h3 : Odd (orderOf (x : ↥H)) := by
      have := orderOf_dvd_natCard (⟨(x : ↥H), hxN⟩ : ↥(pCore p ↥H))
      have h4 : orderOf (⟨(x : ↥H), hxN⟩ : ↥(pCore p ↥H)) = orderOf (x : ↥H) :=
        Subgroup.orderOf_mk _ _
      rw [h4] at this
      exact Odd.of_dvd_nat hodd this
    have h5 : orderOf (x : ↥H) ∣ 2 := orderOf_dvd_of_pow_eq_one h2
    have h6 : orderOf (x : ↥H) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp h5 with h | h
      · exact h
      · rw [h] at h3; exact absurd h3 (by decide)
    have : (x : ↥H) = 1 := orderOf_eq_one_iff.mp h6
    exact Subtype.ext this
  have hrange : g.range = E₀.map (QuotientGroup.mk' (pCore p ↥H)) := by
    simp only [g, MonoidHom.range_comp, Subgroup.range_subtype]
  refine ⟨E₀.map (QuotientGroup.mk' (pCore p ↥H)), ?_, ?_, ?_⟩
  · exact Subgroup.map_mono (fun x hx => (hES hx : (x : G) ∈ S))
  · exact CFSG.SectionRank.isElemAbelian_map hE₀ab _
  · rw [← hrange]
    have h1 : Nat.card ↥g.range = Nat.card ↥E₀ :=
      (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
    rw [h1]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEH).toEquiv

end Image

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
