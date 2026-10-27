module

public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.Classes
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Basic

public section

namespace CFSG.EvenSporadicStandard.RuStd

open Subgroup

structure Config (G : Type) [Group G] (L : Subgroup G) (z : G) : Prop where
  simple : IsSimpleGroup G
  nonabelian : ∃ a b : G, a * b ≠ b * a
  z_sq : z * z = 1
  z_ne_one : z ≠ 1
  comm : ∀ l ∈ L, l * z = z * l
  z_not_mem : z ∉ L
  centralizer_eq : centralizer ({z} : Set G) = L ⊔ zpowers z

section Config

variable {G : Type} [Group G] {L : Subgroup G} {z : G}

theorem Config.orderOf_z (hc : Config G L z) : orderOf z = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact hc.z_sq) hc.z_ne_one

theorem Config.zpow_cases (hc : Config G L z) (k : ℤ) : z ^ k = 1 ∨ z ^ k = z := by
  have h := zpow_mod_orderOf z k
  rw [hc.orderOf_z] at h
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · left
    rw [← h]
    simp [h0]
  · right
    rw [← h]
    simp [h1]

theorem Config.disjoint (hc : Config G L z) : Disjoint L (zpowers z) := by
  rw [disjoint_iff_inf_le]
  rintro x ⟨hxL, hxz⟩
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hxz
  rcases hc.zpow_cases k with h | h
  · rw [h]; exact one_mem _
  · exact absurd (h ▸ hxL) hc.z_not_mem

theorem Config.zpowers_le_centralizer (hc : Config G L z) :
    zpowers z ≤ centralizer (L : Set G) := by
  rw [zpowers_le]
  exact mem_centralizer_iff.2 fun l hl => hc.comm l hl

theorem Config.le_centralizer (hc : Config G L z) : L ≤ centralizer ({z} : Set G) := fun l hl =>
  mem_centralizer_singleton_iff.2 (hc.comm l hl)

theorem Config.card_centralizer (hc : Config G L z) :
    Nat.card (centralizer ({z} : Set G)) = 2 * Nat.card L := by
  rw [hc.centralizer_eq]
  have e := (mulEquivProdSup hc.zpowers_le_centralizer hc.disjoint).toEquiv
  rw [← Nat.card_congr e, Nat.card_prod, Nat.card_zpowers, hc.orderOf_z, mul_comm]

theorem Config.mem_cases (hc : Config G L z) {h : G} (hh : h ∈ centralizer ({z} : Set G)) :
    h ∈ L ∨ ∃ l ∈ L, h = z * l := by
  rw [hc.centralizer_eq] at hh
  obtain ⟨l, hl, c, hcz, rfl⟩ :=
    exists_mul_of_mem_sup_of_le_centralizer hc.zpowers_le_centralizer hh
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hcz
  rcases hc.zpow_cases k with h1 | h1
  · left
    rw [h1, mul_one]
    exact hl
  · right
    exact ⟨l, hl, by rw [h1]; exact hc.comm l hl⟩

theorem Config.conj_mul (hc : Config G L z) (c l : L) :
    (c : G) * (z * (l : G)) * (c : G)⁻¹ = z * ((c * l * c⁻¹ : L) : G) := by
  have h := hc.comm c c.2
  calc (c : G) * (z * (l : G)) * (c : G)⁻¹ = ((c : G) * z) * (l : G) * (c : G)⁻¹ := by group
    _ = (z * (c : G)) * (l : G) * (c : G)⁻¹ := by rw [h]
    _ = z * ((c * l * c⁻¹ : L) : G) := by simp [mul_assoc]

theorem Config.isConj_mul_mul (hc : Config G L z) {l l' : L} (h : IsConj l l') :
    IsConj (z * (l : G)) (z * (l' : G)) := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  exact isConj_iff.2 ⟨(c : G), hc.conj_mul c l⟩

end Config

section Fusion

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z : G}

theorem Config.even_ncard_conj (hc : Config G L z) :
    Even {y : G | y ∈ centralizer ({z} : Set G) ∧ y ∉ L ∧ IsConj z y}.ncard := by
  classical
  have := hc.simple
  set H := centralizer ({z} : Set G) with hH
  have hLH : L ≤ H := hc.le_centralizer
  have hHL : Nat.card H = 2 * Nat.card L := hc.card_centralizer
  have hposL : 0 < Nat.card L := Nat.card_pos
  have hposH : 0 < Nat.card H := Nat.card_pos
  have eH := card_fixed_mul_card' H z
  have eL := card_fixed_mul_card' L z
  set XH : Set G := {y | y ∈ H ∧ IsConj z y} with hXH
  set XL : Set G := {y | y ∈ L ∧ IsConj z y} with hXL
  set E : Set G := {y | y ∈ H ∧ y ∉ L ∧ IsConj z y} with hE
  have hFH : Nat.card {q : G ⧸ H // z • q = q} = XH.ncard :=
    Nat.eq_of_mul_eq_mul_right hposH eH
  have hFL : Nat.card {q : G ⧸ L // z • q = q} = 2 * XL.ncard := by
    refine Nat.eq_of_mul_eq_mul_right hposL ?_
    rw [eL]
    show XL.ncard * Nat.card H = _
    rw [hHL]
    ring
  have hidx : Nat.card (G ⧸ L) = 2 * Nat.card (G ⧸ H) := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup H
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup L
    refine Nat.eq_of_mul_eq_mul_right hposL ?_
    calc Nat.card (G ⧸ L) * Nat.card L = Nat.card G := h2.symm
      _ = Nat.card (G ⧸ H) * Nat.card H := h1
      _ = Nat.card (G ⧸ H) * (2 * Nat.card L) := by rw [hHL]
      _ = 2 * Nat.card (G ⧸ H) * Nat.card L := by ring
  have hsplitH := card_quot_eq_fixed_add_moved H z
  have hsplitL := card_quot_eq_fixed_add_moved L z
  have hmH := even_card_moved H hc.z_sq
  have hmL := four_dvd_card_moved hc.nonabelian L hc.z_sq
  have hunion : XH = XL ∪ E := by
    ext y
    simp only [hXH, hXL, hE, Set.mem_union, Set.mem_ofPred_eq]
    by_cases hy : y ∈ L
    · exact ⟨fun h => Or.inl ⟨hy, h.2⟩, fun h => h.elim (fun h => ⟨hLH h.1, h.2⟩)
        fun h => absurd hy h.2.1⟩
    · exact ⟨fun h => Or.inr ⟨h.1, hy, h.2⟩, fun h => h.elim (fun h => absurd h.1 hy)
        fun h => ⟨h.1, h.2.2⟩⟩
  have hdisj : Disjoint XL E := Set.disjoint_left.2 fun y hy hy' => hy'.2.1 hy.1
  have hcard : XH.ncard = XL.ncard + E.ncard := by
    rw [hunion, Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)]
  rw [even_iff_two_dvd]
  omega

theorem Config.isConj_mul_of_classA (hc : Config G L z) (hF : RuFacts L) {a : L}
    (ha2 : orderOf a = 2) (haA : Nat.card (centralizer ({a} : Set L)) = 245760) :
    IsConj z (z * (a : G)) := by
  classical
  by_contra hnot
  have hev := hc.even_ncard_conj
  set H := centralizer ({z} : Set G) with hH
  have hLH : L ≤ H := hc.le_centralizer
  set E : Set G := {y | y ∈ H ∧ y ∉ L ∧ IsConj z y} with hE
  set FB : Set L := {l | orderOf l = 2 ∧ IsConj z (z * (l : G))} with hFB
  have hzH : z ∈ H := mem_centralizer_singleton_iff.2 rfl
  have hEimg : E = (fun l : L => z * (l : G)) '' ({1} ∪ FB) := by
    ext y
    constructor
    · rintro ⟨hyH, hyL, hyz⟩
      rcases hc.mem_cases hyH with h | ⟨l, hl, rfl⟩
      · exact absurd h hyL
      · refine ⟨⟨l, hl⟩, ?_, rfl⟩
        have hsq : (z * l) * (z * l) = 1 := by
          obtain ⟨c, hcy⟩ := isConj_iff.1 hyz
          rw [← hcy]
          calc c * z * c⁻¹ * (c * z * c⁻¹) = c * (z * z) * c⁻¹ := by group
            _ = 1 := by rw [hc.z_sq]; group
        have hll : (l * l : G) = 1 := by
          have hc' := hc.comm l hl
          calc (l * l : G) = (z * z) * (l * l) := by rw [hc.z_sq, one_mul]
            _ = z * (z * l) * l := by rw [mul_assoc, mul_assoc]; simp [mul_assoc]
            _ = z * (l * z) * l := by rw [hc']
            _ = (z * l) * (z * l) := by group
            _ = 1 := hsq
        by_cases h1 : (⟨l, hl⟩ : L) = 1
        · exact Or.inl h1
        · right
          refine ⟨orderOf_eq_prime ?_ h1, hyz⟩
          exact Subtype.ext (by simpa [pow_two] using hll)
    · rintro ⟨l, hl | hl, rfl⟩
      · have hl1 : l = 1 := hl
        subst hl1
        refine ⟨by simpa using hzH, by simpa using hc.z_not_mem, by simpa using IsConj.refl z⟩
      · refine ⟨mul_mem hzH (hLH l.2), fun h => hc.z_not_mem ?_, hl.2⟩
        have := mul_mem h (inv_mem l.2)
        simpa using this
  have hinj : Function.Injective (fun l : L => z * (l : G)) := fun l l' h =>
    Subtype.ext (mul_left_cancel h)
  have hone : (1 : L) ∉ FB := fun h => by
    have := h.1
    rw [orderOf_one] at this
    omega
  have hcardE : E.ncard = 1 + FB.ncard := by
    rw [hEimg, Set.ncard_image_of_injective _ hinj,
      Set.ncard_union_eq (Set.disjoint_singleton_left.2 hone) (Set.toFinite _) (Set.toFinite _),
      Set.ncard_singleton]
  have hFB_B : ∀ l ∈ FB, Nat.card (centralizer ({l} : Set L)) = 116480 := by
    rintro l ⟨hl2, hl⟩
    rcases hF.card_centralizer l hl2 with h | h
    · exfalso
      have hconj := hF.isConj_A a l ha2 hl2 haA h
      exact hnot (hl.trans (hc.isConj_mul_mul hconj).symm)
    · exact h
  have hodd : FB.ncard = 0 ∨ FB.ncard = 1252800 := by
    by_cases hne : FB.Nonempty
    · right
      obtain ⟨l₀, hl₀⟩ := hne
      have hset : FB = {l : L | orderOf l = 2 ∧ Nat.card (centralizer ({l} : Set L)) = 116480} := by
        ext l
        constructor
        · intro hl
          exact ⟨hl.1, hFB_B l hl⟩
        · rintro ⟨hl2, hlB⟩
          have hconj := hF.isConj_B l₀ l hl₀.1 hl2 (hFB_B l₀ hl₀) hlB
          exact ⟨hl2, hl₀.2.trans (hc.isConj_mul_mul hconj)⟩
      rw [hset]
      exact hF.ncard_involB hl₀.1 (hFB_B l₀ hl₀)
    · left
      rw [Set.not_nonempty_iff_eq_empty.1 hne, Set.ncard_empty]
  rw [hcardE] at hev
  rcases hodd with h | h <;> rw [h] at hev <;> exact absurd hev (by decide)

end Fusion

end CFSG.EvenSporadicStandard.RuStd
