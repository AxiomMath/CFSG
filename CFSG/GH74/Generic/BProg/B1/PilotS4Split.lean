module

public import CFSG.GH74.Generic.BProg.B1.PilotS5
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvCent

public section

namespace CFSG.GH74.Generic.BProg.B1.PilotS4

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint Subgroup
open CFSG.GH74.Generic.BProg.B1.PilotS5

theorem isSplit_map {X X' : Type*} [Group X] [Group X'] (ι : X →* X') (hι : Function.Injective ι)
    {n : ℕ} {u : X} {L H : Subgroup X} (h : IsSplit n u L H) :
    IsSplit n (ι u) (L.map ι) (H.map ι) := by
  have := h.simple
  let e : ↥L ≃* ↥(L.map ι) := L.equivMapOfInjective ι hι
  refine ⟨?_, ?_, ?_, ?_, e.symm.isSimpleGroup, ?_, ?_, h.even⟩
  · rw [orderOf_injective ι hι u]; exact h.ord
  · rintro _ ⟨l, hl, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    exact congrArg ι (Subgroup.mem_centralizer_singleton_iff.1 (h.le_cent hl))
  · intro hu
    exact h.not_mem ((Subgroup.mem_map_iff_mem hι).1 hu)
  · rw [h.eq_sup, Subgroup.map_sup, MonoidHom.map_zpowers]
  · obtain ⟨a, b, hab⟩ := h.nonabelian
    exact ⟨e a, e b, fun hc => hab (e.injective (by rw [map_mul, map_mul]; exact hc))⟩
  · rw [← Nat.card_congr e.toEquiv]; exact h.card

theorem map_centralizer_singleton_eq_inf_range {J X : Type*} [Group J] [Group X] (ι : J →* X)
    (hι : Function.Injective ι) (u : J) :
    (centralizer ({u} : Set J)).map ι = centralizer ({ι u} : Set X) ⊓ ι.range := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    MonoidHom.mem_range]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨by rw [← map_mul, ← map_mul, hc], c, rfl⟩
  · rintro ⟨hy, c, rfl⟩
    refine ⟨c, ?_, rfl⟩
    apply hι
    rw [map_mul, map_mul]
    exact hy

structure SplitGrp (n : ℕ) (J : Type*) [Group J] : Prop where
  center : ∀ z : J, (∀ g : J, g * z = z * g) → z = 1
  exists_inv : ∃ u : J, orderOf u = 2
  split : ∀ u : J, orderOf u = 2 → ∃ L : Subgroup J, IsSplit n u L (centralizer ({u} : Set J))

theorem SplitGrp.map_equiv {J J' : Type*} [Group J] [Group J'] (e : J ≃* J') {n : ℕ}
    (h : SplitGrp n J) : SplitGrp n J' := by
  refine ⟨fun z hz => ?_, ?_, fun u' hu' => ?_⟩
  · apply e.symm.injective
    rw [map_one]
    apply h.center
    intro g
    have := congrArg e.symm (hz (e g))
    simpa using this
  · obtain ⟨u, hu⟩ := h.exists_inv
    exact ⟨e u, by rw [MulEquiv.orderOf_eq]; exact hu⟩
  · obtain ⟨u, rfl⟩ := e.surjective u'
    have hu : orderOf u = 2 := by rwa [MulEquiv.orderOf_eq] at hu'
    obtain ⟨L, hL⟩ := h.split u hu
    have := isSplit_map e.toMonoidHom e.injective hL
    rw [CFSG.GH74.GLS.IVK.GHInv.map_centralizer_singleton' e u] at this
    exact ⟨L.map e.toMonoidHom, this⟩

theorem SplitGrp.exists_four {J : Type} [Group J] [Finite J] {n : ℕ} (h : SplitGrp n J) :
    ∃ V : Subgroup J, CFSG.IsElementaryAbelian 2 V ∧ Nat.card V = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨u, hu⟩ := h.exists_inv
  obtain ⟨L, hL⟩ := h.split u hu
  obtain ⟨l, hl⟩ := exists_prime_orderOf_dvd_card' (G := ↥L) 2 (by rw [hL.card]; exact hL.even)
  have hl2 : orderOf (l : J) = 2 := by rw [Subgroup.orderOf_coe]; exact hl
  have hcomm : u * (l : J) = (l : J) * u :=
    (Subgroup.mem_centralizer_singleton_iff.1 (hL.le_cent l.2)).symm
  have hne : u ≠ (l : J) := fun hh => hL.not_mem (hh ▸ l.2)
  obtain ⟨-, hel, hcard⟩ := closure_pair_facts hu hl2 hcomm hne
  exact ⟨_, hel, hcard⟩

theorem SplitGrp.splitLike {X : Type} [Group X] {n : ℕ} {Y : Subgroup X} (h : SplitGrp n ↥Y) :
    SplitLike n Y := by
  refine ⟨fun z hz hcomm => ?_, fun u hu hu2 => ?_⟩
  · have := h.center ⟨z, hz⟩ (fun g => Subtype.ext (hcomm g g.2))
    exact congrArg Subtype.val this
  · have hu₀ : orderOf (⟨u, hu⟩ : ↥Y) = 2 := by rw [Subgroup.orderOf_mk]; exact hu2
    obtain ⟨L, hL⟩ := h.split ⟨u, hu⟩ hu₀
    have h1 := isSplit_map Y.subtype Y.subtype_injective hL
    rw [map_centralizer_singleton_eq_inf_range Y.subtype Y.subtype_injective, Subgroup.range_subtype]
      at h1
    exact ⟨L.map Y.subtype, Subgroup.map_subtype_le _, h1⟩

end CFSG.GH74.Generic.BProg.B1.PilotS4
