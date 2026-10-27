module

public import CFSG.GH74.GLS.Stage2.Signalizer.L53Prop110Q
public import CFSG.GH74.GLS.Stage2.Signalizer.L53Clifford

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.L53

open Subgroup Module
open scoped commutatorElement

theorem Sl2Quot.of_surjective {p : ℕ} {J J' : Type} [Group J] [Group J'] (φ : J →* J')
    (hφ : Function.Surjective φ) {C' : Subgroup J'} (h : Sl2Quot p J' C') :
    Sl2Quot p J (C'.comap φ) := by
  obtain ⟨N', hN', hCN', F, hF, hFin, hcard, ⟨e⟩⟩ := h
  refine ⟨N'.comap φ, inferInstance, Subgroup.comap_mono hCN', F, hF, hFin, hcard, ?_⟩
  let ψ : J →* J' ⧸ N' := (QuotientGroup.mk' N').comp φ
  have hψ : Function.Surjective ψ := (QuotientGroup.mk'_surjective N').comp hφ
  have hker : ψ.ker = N'.comap φ := by
    ext x
    simp [ψ, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    ((QuotientGroup.quotientKerEquivOfSurjective ψ hψ).trans e)⟩

theorem isPGroup_zpowers_map {p : ℕ} [Fact p.Prime] {G G' : Type*} [Group G] [Group G'] [Finite G]
    [Finite G'] (f : G →* G')
    {g : G} (hg : IsPGroup p ↥(zpowers g)) : IsPGroup p ↥(zpowers (f g)) := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hg
  rw [Nat.card_zpowers] at hn
  have hdvd : orderOf (f g) ∣ p ^ n := hn ▸ orderOf_map_dvd f g
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hdvd
  rw [IsPGroup.iff_card]
  exact ⟨i, by rw [Nat.card_zpowers, hi]⟩

variable {p : ℕ} [Fact p.Prime]

theorem prop110_M (hp2 : p ≠ 2) {M : Type} [Group M] [Finite M] {X Y : Subgroup M}
    (hc : IsChiefPair X Y) (hXp : IsPGroup p ↥X) {g : M} (hgp : IsPGroup p ↥(zpowers g))
    (hq : ∀ x ∈ X, ⁅⁅x, g⁆, g⁆ ∈ Y) (hn : ∃ x ∈ X, ⁅x, g⁆ ∉ Y) :
    ∃ m : M, Sl2Quot p ↥(closure ({g, m * g * m⁻¹} : Set M))
      ((stabSec X Y hc.2.1).subgroupOf (closure ({g, m * g * m⁻¹} : Set M))) := by
  have hXn := hc.1
  have hYn := hc.2.1
  have hYX : Y < X := hc.2.2.1
  have hmin := hc.2.2.2
  let π : M →* M ⧸ Y := QuotientGroup.mk' Y
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective Y
  have hker : ∀ x, π x = 1 ↔ x ∈ Y := fun x => QuotientGroup.eq_one_iff x
  set H : Subgroup (M ⧸ Y) := X.map π with hH
  have hHn : H.Normal := Subgroup.Normal.map hXn π hπ
  have hHmin : IsMinimalNormal H := by
    refine ⟨fun K hKn hKH => ?_⟩
    have hKn' : (K.comap π).Normal := Subgroup.Normal.comap hKn π
    have hYK : Y ≤ K.comap π := fun y hy => by
      rw [Subgroup.mem_comap, (hker y).mpr hy]; exact K.one_mem
    have hKX : K.comap π ≤ X := by
      intro x hx
      have hπx : π x ∈ H := hKH hx
      obtain ⟨x', hx', hxx'⟩ := Subgroup.mem_map.mp hπx
      have : x'⁻¹ * x ∈ Y := by
        rw [← hker, map_mul, map_inv, hxx', inv_mul_cancel]
      have h2 : x = x' * (x'⁻¹ * x) := by group
      rw [h2]
      exact X.mul_mem hx' (hYX.le this)
    rcases hmin _ hKn' hYK hKX with h | h
    · left
      rw [eq_bot_iff]
      intro q hq'
      obtain ⟨x, rfl⟩ := hπ q
      have : x ∈ K.comap π := hq'
      rw [h] at this
      exact (Subgroup.mem_bot).mpr ((hker x).mpr this)
    · right
      refine le_antisymm hKH ?_
      intro q hq'
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hq'
      have : x ∈ K.comap π := by rw [h]; exact hx
      exact this
  have hHne : H ≠ ⊥ := by
    intro hbot
    apply hYX.not_ge
    intro x hx
    have : π x ∈ H := Subgroup.mem_map_of_mem π hx
    rw [hbot, Subgroup.mem_bot, hker] at this
    exact this
  have hHp : IsPGroup p ↥H := by
    intro y
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
    obtain ⟨k, hk⟩ := hXp ⟨x, hx⟩
    refine ⟨k, Subtype.ext ?_⟩
    have hk' : x ^ (p ^ k) = 1 := by simpa using congrArg Subtype.val hk
    show (y : M ⧸ Y) ^ (p ^ k) = 1
    rw [← hxy, ← map_pow, hk', map_one]
  have hgp' : IsPGroup p ↥(zpowers (π g)) := isPGroup_zpowers_map π hgp
  have hq' : ∀ v ∈ H, ⁅π g, ⁅π g, v⁆⁆ = 1 := by
    intro v hv
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hv
    rw [← map_commutatorElement, ← map_commutatorElement, hker]
    have h1 : ⁅x, g⁆ ∈ phiSub Y hYn g := hq x hx
    have h2 : ⁅x, g⁆⁻¹ ∈ phiSub Y hYn g := (phiSub Y hYn g).inv_mem h1
    have h3 : ⁅⁅x, g⁆⁻¹, g⁆ ∈ Y := h2
    have e : ⁅g, ⁅g, x⁆⁆ = ⁅⁅x, g⁆⁻¹, g⁆⁻¹ := by
      rw [commutatorElement_inv x g, commutatorElement_inv]
    rw [e]
    exact Y.inv_mem h3
  have hn' : ∃ v ∈ H, ⁅π g, v⁆ ≠ 1 := by
    obtain ⟨x, hx, hxY⟩ := hn
    refine ⟨π x, Subgroup.mem_map_of_mem π hx, ?_⟩
    rw [← map_commutatorElement]
    intro h
    apply hxY
    have h1 : ⁅g, x⁆ ∈ Y := (hker _).mp h
    rw [← commutatorElement_inv g x]
    exact Y.inv_mem h1
  have := hHn
  have := hHmin
  obtain ⟨m', hm⟩ := prop110_Q hp2 H hHne hHp hgp' hq' hn'
  obtain ⟨m, rfl⟩ := hπ m'
  refine ⟨m, ?_⟩
  set J : Subgroup M := closure ({g, m * g * m⁻¹} : Set M) with hJ
  have hmapJ : J.map π = closure ({π g, π m * π g * (π m)⁻¹} : Set (M ⧸ Y)) := by
    rw [hJ, MonoidHom.map_closure, Set.image_pair]
    simp
  let φ : ↥J →* ↥(closure ({π g, π m * π g * (π m)⁻¹} : Set (M ⧸ Y))) :=
    (Subgroup.inclusion hmapJ.le).comp (π.subgroupMap J)
  have hφ : Function.Surjective φ := by
    intro y
    have : (y : M ⧸ Y) ∈ J.map π := by rw [hmapJ]; exact y.2
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp this
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have h2 := Sl2Quot.of_surjective φ hφ hm
  refine Sl2Quot.mono ?_ h2
  intro c hc'
  rw [Subgroup.mem_subgroupOf] at hc'
  rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hv
  have h5 : ⁅x, (c : M)⁆ ∈ Y := hc' x hx
  have h6 := (hker _).mpr h5
  rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h6
  exact h6

end CFSG.GH74.GLS.Stage2.Signalizer.L53
