module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16ONat
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16OTs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16UFix

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open Subgroup Matrix

variable {G : Type} [Group G] [Finite G]

theorem O6NatData.charP {n : ℕ} {L V : Subgroup G} (d : O6NatData G n L V) (hn : 1 ≤ n) :
    CharP d.F 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Fintype d.F := Fintype.ofFinite d.F
  have h : Fintype.card d.F = 2 ^ n := by
    rw [← Nat.card_eq_fintype_card]
    exact d.card_F
  exact charP_of_card_eq_prime_pow h

theorem O6NatData.nonempty_model {n : ℕ} {L V : Subgroup G} (d : O6NatData G n L V)
    (hn : 1 ≤ n) : Nonempty (NormModel d.F d.b d.c) := by
  haveI := d.charP hn
  exact nonempty_normModel d.irred d.card_F hn

theorem O6NatData.nonsing_good {n p : ℕ} {M L V : Subgroup G} (d : O6NatData G n L V)
    (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (hn : 1 ≤ n) (hLM : L ≤ M)
    (hMV : M ≤ normalizer (V : Set G)) :
    ∀ v ∈ V, v ≠ 1 → ¬ d.sing v →
      2 ≤ CFSG.Open.pRank p (M ⊓ centralizer ({v} : Set G)) := by
  intro v hv hv1 hns
  haveI := d.charP hn
  obtain ⟨Mdl⟩ := d.nonempty_model hn
  have hp2 := prime_ne_two_of_dvd_two_pow_add_one hn hpq
  have hpq' : p ∣ Nat.card d.F + 1 := by
    rw [d.card_F]
    exact hpq
  obtain ⟨E, hEΩ, hEa, hEc, hEf⟩ := exists_stab_nonsing Mdl d.irred hp hpq'
    (w := Multiplicative.toAdd (d.φ ⟨v, hv⟩)) (fun h => hns ⟨hv, h⟩)
  obtain ⟨S, hS, hSa, hSc⟩ := d.exists_lift_fixing hp hp2 hLM hMV hv E hEΩ hEa hEc hEf
  exact CFSG.SectionRank.le_pRank hp.one_lt hS hSa hSc

theorem O6NatData.p_dvd {n p : ℕ} {M L V : Subgroup G} (d : O6NatData G n L V)
    (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (hn : 1 ≤ n) (hLM : L ≤ M)
    (hMV : M ≤ normalizer (V : Set G)) :
    ∀ v ∈ V, v ≠ 1 → p ∣ Nat.card ↥(M ⊓ centralizer ({v} : Set G)) := by
  intro v hv hv1
  haveI := d.charP hn
  obtain ⟨Mdl⟩ := d.nonempty_model hn
  have hp2 := prime_ne_two_of_dvd_two_pow_add_one hn hpq
  have hpq' : p ∣ Nat.card d.F + 1 := by
    rw [d.card_F]
    exact hpq
  have hw : Multiplicative.toAdd (d.φ ⟨v, hv⟩) ≠ 0 := by
    intro h
    have h1 : d.φ ⟨v, hv⟩ = 1 := by
      rw [← ofAdd_toAdd (d.φ ⟨v, hv⟩), h]
      rfl
    have h2 : (⟨v, hv⟩ : ↥V) = 1 := d.φ_bij.1 (h1.trans (map_one d.φ).symm)
    exact hv1 (congrArg Subtype.val h2)
  obtain ⟨k, E, hk, hEΩ, hEa, hEc, hEf⟩ := exists_stab_ne_zero Mdl d.irred hp hpq' hw
  obtain ⟨S, hS, hSa, hSc⟩ := d.exists_lift_fixing hp hp2 hLM hMV hv E hEΩ hEa hEc hEf
  have := Subgroup.card_dvd_of_le hS
  rw [hSc] at this
  exact (dvd_pow_self p (by omega)).trans this

theorem O6NatData.exists_image {n : ℕ} {L V : Subgroup G} (d : O6NatData G n L V)
    (W : Subgroup G) :
    ∃ S : AddSubgroup (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → d.F),
      ∀ x : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → d.F,
        x ∈ S ↔ ∃ w : ↥V, (w : G) ∈ W ∧ Multiplicative.toAdd (d.φ w) = x :=
  ⟨{ carrier := {x | ∃ w : ↥V, (w : G) ∈ W ∧ Multiplicative.toAdd (d.φ w) = x}
     add_mem' := by
       rintro _ _ ⟨w₁, hw₁, rfl⟩ ⟨w₂, hw₂, rfl⟩
       exact ⟨w₁ * w₂, W.mul_mem hw₁ hw₂, by rw [map_mul, toAdd_mul]⟩
     zero_mem' := ⟨1, W.one_mem, by rw [map_one, toAdd_one]⟩
     neg_mem' := by
       rintro _ ⟨w, hw, rfl⟩
       exact ⟨w⁻¹, W.inv_mem hw, by rw [map_inv, toAdd_inv]⟩ }, fun _ => Iff.rfl⟩

theorem O6NatData.card_image {n : ℕ} {L V : Subgroup G} (d : O6NatData G n L V) (W : Subgroup G)
    (hWV : W ≤ V) (S : AddSubgroup (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → d.F))
    (hSmem : ∀ x : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → d.F,
      x ∈ S ↔ ∃ w : ↥V, (w : G) ∈ W ∧ Multiplicative.toAdd (d.φ w) = x) :
    Nat.card S = Nat.card W := by
  have hmemS : ∀ w : ↥W, Multiplicative.toAdd (d.φ ⟨(w : G), hWV w.2⟩) ∈ S :=
    fun w => (hSmem _).2 ⟨⟨(w : G), hWV w.2⟩, w.2, rfl⟩
  have hbij : Function.Bijective
      (fun w : ↥W => (⟨Multiplicative.toAdd (d.φ ⟨(w : G), hWV w.2⟩), hmemS w⟩ : ↥S)) := by
    refine ⟨?_, ?_⟩
    · intro w w' h
      have h1 : Multiplicative.toAdd (d.φ ⟨(w : G), hWV w.2⟩)
          = Multiplicative.toAdd (d.φ ⟨(w' : G), hWV w'.2⟩) := congrArg Subtype.val h
      have h2 : (⟨(w : G), hWV w.2⟩ : ↥V) = ⟨(w' : G), hWV w'.2⟩ :=
        d.φ_bij.injective (Multiplicative.toAdd.injective h1)
      exact Subtype.ext (Subtype.mk.inj h2)
    · rintro ⟨s, hs⟩
      obtain ⟨w, hw, hws⟩ := (hSmem s).1 hs
      exact ⟨⟨(w : G), hw⟩, Subtype.ext hws⟩
  exact (Nat.card_congr (Equiv.ofBijective _ hbij)).symm

theorem O6NatData.ts_index {n : ℕ} {L V : Subgroup G} (d : O6NatData G n L V) (hn : 1 ≤ n) :
    ∀ W : Subgroup G, W ≤ V → (∀ w ∈ W, w ≠ 1 → d.sing w) → 2 ^ (4 * n) ≤ W.relIndex V := by
  intro W hWV hsing
  haveI := d.charP hn
  obtain ⟨S, hSmem⟩ := d.exists_image W
  have hcard : Nat.card S = Nat.card W := d.card_image W hWV S hSmem
  have hSs : ∀ x ∈ S, StatedQuadMinus 3 d.F d.b d.c x = 0 := by
    intro x hx
    obtain ⟨w, hw, rfl⟩ := (hSmem x).1 hx
    by_cases hw1 : (w : G) = 1
    · have hw' : w = 1 := Subtype.ext hw1
      rw [hw', map_one, toAdd_one]
      exact stated_quad_zero
    · obtain ⟨hV, h⟩ := hsing _ hw hw1
      exact h
  have hle : Nat.card W ≤ 2 ^ (2 * n) := by
    rw [← hcard]
    have := ts_card_le d.irred S hSs
    rw [d.card_F] at this
    calc Nat.card S ≤ (2 ^ n) ^ 2 := this
      _ = 2 ^ (2 * n) := by ring
  have hmul : W.relIndex V * Nat.card W = Nat.card V := by
    have h := Subgroup.relIndex_mul_card (H := W) (K := V)
    rw [inf_eq_left.mpr hWV] at h
    exact h
  have hpos : 0 < 2 ^ (2 * n) := by positivity
  have hsq : 2 ^ (4 * n) * 2 ^ (2 * n) = 2 ^ (6 * n) := by
    rw [← pow_add]
    congr 1
    omega
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  calc 2 ^ (4 * n) * 2 ^ (2 * n) = 2 ^ (6 * n) := hsq
    _ = Nat.card V := d.card_V.symm
    _ = W.relIndex V * Nat.card W := hmul.symm
    _ ≤ W.relIndex V * 2 ^ (2 * n) := Nat.mul_le_mul le_rfl hle

theorem O6NatData.ts_equal {n p : ℕ} {M L V : Subgroup G} (d : O6NatData G n L V)
    (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (hn : 1 ≤ n) (hLM : L ≤ M)
    (hMV : M ≤ normalizer (V : Set G)) :
    ∀ W : Subgroup G, W ≤ V → (∀ w ∈ W, w ≠ 1 → d.sing w) → W.relIndex V = 2 ^ (4 * n) →
      2 ≤ CFSG.Open.pRank p (M ⊓ normalizer (W : Set G)) := by
  intro W hWV hsing hidx
  haveI := d.charP hn
  obtain ⟨Mdl⟩ := d.nonempty_model hn
  have hp2 := prime_ne_two_of_dvd_two_pow_add_one hn hpq
  have hpq' : p ∣ Nat.card d.F + 1 := by
    rw [d.card_F]
    exact hpq
  obtain ⟨S, hSmem⟩ := d.exists_image W
  have hcard : Nat.card S = Nat.card W := d.card_image W hWV S hSmem
  have hSs : ∀ x ∈ S, StatedQuadMinus 3 d.F d.b d.c x = 0 := by
    intro x hx
    obtain ⟨w, hw, rfl⟩ := (hSmem x).1 hx
    by_cases hw1 : (w : G) = 1
    · have hw' : w = 1 := Subtype.ext hw1
      rw [hw', map_one, toAdd_one]
      exact stated_quad_zero
    · obtain ⟨hV, h⟩ := hsing _ hw hw1
      exact h
  have hmul : W.relIndex V * Nat.card W = Nat.card V := by
    have h := Subgroup.relIndex_mul_card (H := W) (K := V)
    rw [inf_eq_left.mpr hWV] at h
    exact h
  have hWcard : Nat.card W = Nat.card d.F ^ 2 := by
    have h1 : 2 ^ (4 * n) * Nat.card W = 2 ^ (6 * n) := by
      rw [← hidx, hmul, d.card_V]
    have h2 : 2 ^ (4 * n) * (2 ^ n) ^ 2 = 2 ^ (6 * n) := by
      rw [← pow_mul, ← pow_add]
      congr 1
      omega
    have hpos : 0 < 2 ^ (4 * n) := by positivity
    rw [d.card_F]
    exact Nat.eq_of_mul_eq_mul_left hpos (h1.trans h2.symm)
  obtain ⟨Y, hYS, hY2, hYs⟩ := ts_eq_plane d.irred S hSs (hcard.trans hWcard)
  obtain ⟨E, hEΩ, hEa, hEc, hEY⟩ := exists_stab_plane Mdl d.irred hp hpq' Y hY2 hYs
  have hW' : ∀ v : ↥V, (v : G) ∈ W ↔ Multiplicative.toAdd (d.φ v) ∈ (Y : Set _) := by
    intro v
    rw [SetLike.mem_coe, ← hYS, hSmem]
    constructor
    · intro hv
      exact ⟨v, hv, rfl⟩
    · rintro ⟨w, hw, hwv⟩
      have : w = v := d.φ_bij.1 (Multiplicative.toAdd.injective hwv)
      rw [← this]
      exact hw
  obtain ⟨T, hT, hTa, hTc⟩ := d.exists_lift_stab hp hp2 hLM hMV W (Y : Set _) hW' hWV E hEΩ hEa hEc
    (fun g hg x hx => hEY g hg x hx)
  exact CFSG.SectionRank.le_pRank hp.one_lt hT hTa hTc

end CFSG.LocalAnalysis.RankThreeUC
