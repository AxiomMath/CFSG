module

public import CFSG.GroupTheory.Transfer.YoshidaParityClass

import CFSG.GroupTheory.ThompsonTransferCount

public section

namespace CFSG.GroupTheory

variable {G : Type*} [Group G] [Finite G]

private theorem conj_eq_of_mul_comm {t c : G} (hc : c * t = t * c) (g : G) :
    (c * g)⁻¹ * t * (c * g) = g⁻¹ * t * g := by
  have h : c⁻¹ * t * c = t := by
    calc c⁻¹ * t * c = c⁻¹ * (t * c) := mul_assoc _ _ _
      _ = c⁻¹ * (c * t) := by rw [hc]
      _ = t := inv_mul_cancel_left c t
  calc (c * g)⁻¹ * t * (c * g) = g⁻¹ * (c⁻¹ * t * c) * g := by group
    _ = g⁻¹ * t * g := by rw [h]

theorem exists_isConj_mem_of_odd_index {t : G} (ht : t ^ 2 = 1)
    (htG : t ∈ _root_.commutator G) {H K : Subgroup G} (hKH : K ≤ H) (hidx : K.relIndex H = 2)
    (hH : Odd H.index) :
    ∃ y : G, IsConj t y ∧ y ∈ K ∧
      Odd ((H ⊓ Subgroup.centralizer ({y} : Set G)).relIndex
        (Subgroup.centralizer ({y} : Set G))) := by
  classical
  haveI : Fintype (G ⧸ H) := Fintype.ofFinite _
  set C := Subgroup.centralizer ({t} : Set G) with hC
  have hKn : ∀ h ∈ H, ∀ x ∈ K, h * x * h⁻¹ ∈ K := by
    haveI : (K.subgroupOf H).Normal := Subgroup.normal_of_index_eq_two hidx
    intro h hh x hx
    exact Subgroup.mem_subgroupOf.mp
      (this.conj_mem ⟨x, hKH hx⟩ (Subgroup.mem_subgroupOf.mpr hx) ⟨h, hh⟩)
  let R : G ⧸ H → Prop := fun x => ∃ g : G, (g : G ⧸ H) = x ∧ g⁻¹ * t * g ∈ K
  have hRmem : ∀ g : G, R (g : G ⧸ H) ↔ g⁻¹ * t * g ∈ K := by
    intro g
    constructor
    · rintro ⟨g', hg', h1⟩
      have hh : g'⁻¹ * g ∈ H := QuotientGroup.eq.mp hg'
      have hconj : g⁻¹ * t * g = (g'⁻¹ * g)⁻¹ * (g'⁻¹ * t * g') * (g'⁻¹ * g) := by group
      rw [hconj]
      have := hKn _ (H.inv_mem hh) _ h1
      simpa [mul_assoc] using this
    · intro h1
      exact ⟨g, rfl, h1⟩
  have hRinv : ∀ (c : ↥C) (x : G ⧸ H), R (c • x) ↔ R x := by
    intro c x
    induction x using QuotientGroup.induction_on with
    | H g =>
      change R (((c : G) * g : G) : G ⧸ H) ↔ R (g : G ⧸ H)
      rw [hRmem, hRmem, conj_eq_of_mul_comm
        (Subgroup.mem_centralizer_singleton_iff.mp c.2)]
  have hcount : (Finset.univ.filter R).card * Nat.card H =
      Nat.card C * Set.ncard {y : G | IsConj t y ∧ y ∈ K} := by
    have h1 := card_conj_preimage_eq t (K : Set G)
    have h2 : {g : G | g⁻¹ * t * g ∈ (K : Set G)} =
        (QuotientGroup.mk : G → G ⧸ H) ⁻¹' {x | R x} := by
      ext g
      simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe]
      exact (hRmem g).symm
    have h3 : Nat.card {g : G // g⁻¹ * t * g ∈ (K : Set G)} =
        Nat.card H * Nat.card {x : G ⧸ H | R x} := by
      have h5 : Nat.card ↥{g : G | g⁻¹ * t * g ∈ (K : Set G)} =
          Nat.card H * Nat.card {x : G ⧸ H | R x} := by
        rw [h2, Nat.card_congr (QuotientGroup.preimageMkEquivSubgroupProdSet H _), Nat.card_prod]
      exact h5
    have h4 : Nat.card {x : G ⧸ H | R x} = (Finset.univ.filter R).card := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_subtype R
    have h6 : {y : G | IsConj t y ∧ y ∈ (K : Set G)} = {y : G | IsConj t y ∧ y ∈ K} := rfl
    rw [h6] at h1
    rw [h4] at h3
    rw [mul_comm, ← h3, h1]
  have hHK : Nat.card H = 2 * Nat.card K := by
    have h := (K.subgroupOf H).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKH).toEquiv] at h
    change Nat.card K * K.relIndex H = Nat.card H at h
    rw [hidx] at h
    omega
  have hFK := card_fixedBy_quotient_mul_card K t
  have hnK : Nat.card (G ⧸ K) = 2 * Nat.card (G ⧸ H) := by
    have h := Subgroup.relIndex_mul_index hKH
    rw [hidx] at h
    exact h.symm
  have h0K := four_dvd_card_sub_card_fixedBy (Ω := G ⧸ K) ht htG
  have hfle : Nat.card (MulAction.fixedBy (G ⧸ K) t) ≤ Nat.card (G ⧸ K) :=
    Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  have hkpos : 0 < Nat.card K := Nat.card_pos
  have h2F : 2 * (Finset.univ.filter R).card = Nat.card (MulAction.fixedBy (G ⧸ K) t) := by
    rw [hHK] at hcount
    apply Nat.eq_of_mul_eq_mul_right hkpos
    nlinarith [hcount, hFK]
  have hoddF : Odd (Finset.univ.filter R).card := by
    have hHidx : Odd (Nat.card (G ⧸ H)) := hH
    rw [← h2F, hnK] at h0K
    obtain ⟨m, hm⟩ := hHidx
    generalize (Finset.univ.filter R).card = n at *
    rw [hm] at h0K
    rw [Nat.odd_iff]
    omega
  haveI : Fintype (MulAction.orbitRel.Quotient ↥C (G ⧸ H)) := Fintype.ofFinite _
  have hsum := CFSG.ThompsonTransferCount.card_filter_eq_sum_orbit (H := ↥C) (α := G ⧸ H) R hRinv
  let f : MulAction.orbitRel.Quotient ↥C (G ⧸ H) → ℕ :=
    fun ω => if R ω.out then Nat.card (MulAction.orbit ↥C ω.out) else 0
  have hsum' : (Finset.univ.filter R).card = ∑ ω, f ω := hsum
  have hex : ∃ ω, Odd (f ω) := by
    by_contra hcon
    push Not at hcon
    have hev : ∀ ω ∈ Finset.univ, Even (f ω) := fun ω _ => Nat.not_odd_iff_even.mp (hcon ω)
    have : Even (∑ ω, f ω) := Finset.even_sum _ hev
    rw [← hsum'] at this
    exact (Nat.not_even_iff_odd.mpr hoddF) this
  obtain ⟨ω, hω⟩ := hex
  have hf0 : f ω ≠ 0 := by
    intro h0
    rw [h0] at hω
    exact absurd hω (by decide)
  have hRx : R ω.out := by
    by_contra hnR
    apply hf0
    simp [f, hnR]
  have hodd' : Odd (Nat.card (MulAction.orbit ↥C ω.out)) := by
    simpa [f, hRx] using hω
  obtain ⟨g, hg, hgK⟩ := hRx
  refine ⟨g⁻¹ * t * g, isConj_iff.mpr ⟨g⁻¹, by simp⟩, hgK, ?_⟩
  rw [← hg] at hodd'
  rw [card_orbit_centralizer_quotient] at hodd'
  exact hodd'

end CFSG.GroupTheory
