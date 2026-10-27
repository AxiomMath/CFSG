module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.BaseEmb

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.Open

private abbrev sigmaC2 : Multiplicative (ZMod 2) := Multiplicative.ofAdd 1

private theorem coord_cases (q : Multiplicative (ZMod 2)) :
    q = 1 ∨ q = sigmaC2 := by
  rcases (show ∀ e : ZMod 2, e = 0 ∨ e = 1 by decide) (Multiplicative.toAdd q) with h | h
  · left
    rw [← ofAdd_toAdd q, h]
    rfl
  · right
    rw [← ofAdd_toAdd q, h]

private theorem sigmaC2_mul_self : sigmaC2 * sigmaC2 = (1 : Multiplicative (ZMod 2)) := by decide

private def iota1 : alternatingGroup (Fin 5) →* A5WrTwo where
  toFun x := A5WrTwo.baseEmb (x, 1)
  map_one' := A5WrTwo.baseEmb.map_one
  map_mul' x y := by
    rw [← A5WrTwo.baseEmb.map_mul]
    congr 1

private def iota2 : alternatingGroup (Fin 5) →* A5WrTwo where
  toFun x := A5WrTwo.baseEmb (1, x)
  map_one' := A5WrTwo.baseEmb.map_one
  map_mul' x y := by
    rw [← A5WrTwo.baseEmb.map_mul]
    congr 1

@[simp]
private lemma iota1_apply (x : alternatingGroup (Fin 5)) :
    iota1 x = A5WrTwo.baseEmb (x, 1) := rfl

@[simp]
private lemma iota2_apply (x : alternatingGroup (Fin 5)) :
    iota2 x = A5WrTwo.baseEmb (1, x) := rfl

private lemma baseEmb_conj_first (g x y : alternatingGroup (Fin 5)) :
    A5WrTwo.baseEmb (g, 1) * A5WrTwo.baseEmb (x, y) * (A5WrTwo.baseEmb (g, 1))⁻¹ *
        (A5WrTwo.baseEmb (x, y))⁻¹ = A5WrTwo.baseEmb (g * x * g⁻¹ * x⁻¹, 1) := by
  simp only [← A5WrTwo.baseEmb.map_inv, ← A5WrTwo.baseEmb.map_mul]
  rw [A5WrTwo.baseEmb_injective.eq_iff]
  ext <;> simp

private lemma baseEmb_conj_second (g x y : alternatingGroup (Fin 5)) :
    A5WrTwo.baseEmb (1, g) * A5WrTwo.baseEmb (x, y) * (A5WrTwo.baseEmb (1, g))⁻¹ *
        (A5WrTwo.baseEmb (x, y))⁻¹ = A5WrTwo.baseEmb (1, g * y * g⁻¹ * y⁻¹) := by
  simp only [← A5WrTwo.baseEmb.map_inv, ← A5WrTwo.baseEmb.map_mul]
  rw [A5WrTwo.baseEmb_injective.eq_iff]
  ext <;> simp

private lemma exists_baseElem_in_normal {b : A5WrTwo} (hb : b.right = sigmaC2)
    (g : alternatingGroup (Fin 5)) (hg : g ≠ 1) :
    ∃ p : alternatingGroup (Fin 5) × alternatingGroup (Fin 5),
      A5WrTwo.baseEmb p = b * (A5WrTwo.baseEmb (g, 1) * b⁻¹ *
        (A5WrTwo.baseEmb (g, 1))⁻¹) ∧ p ≠ 1 := by
  have hbs : b * (⟨1, sigmaC2⟩ : A5WrTwo)⁻¹ ∈ commutator A5WrTwo := by
    rw [A5WrTwo.commutator_eq_ker, MonoidHom.mem_ker]
    simp [hb]
  rw [← A5WrTwo.range_baseEmb] at hbs
  obtain ⟨p₀, hp₀⟩ := MonoidHom.mem_range.mp hbs
  have hb_eq : b = A5WrTwo.baseEmb p₀ * (⟨1, sigmaC2⟩ : A5WrTwo) := by
    rw [hp₀]
    group
  refine ⟨p₀ * (1, g) * p₀⁻¹ * (g, 1)⁻¹, ?_, ?_⟩
  · rw [hb_eq]
    rw [show A5WrTwo.baseEmb p₀ * (⟨1, sigmaC2⟩ : A5WrTwo) *
          (A5WrTwo.baseEmb (g, 1) *
            (A5WrTwo.baseEmb p₀ * (⟨1, sigmaC2⟩ : A5WrTwo))⁻¹ *
            (A5WrTwo.baseEmb (g, 1))⁻¹) =
        A5WrTwo.baseEmb p₀ *
          ((⟨1, sigmaC2⟩ : A5WrTwo) * A5WrTwo.baseEmb (g, 1) *
            (⟨1, sigmaC2⟩ : A5WrTwo)⁻¹) *
          (A5WrTwo.baseEmb p₀)⁻¹ * (A5WrTwo.baseEmb (g, 1))⁻¹ from by group]
    rw [A5WrTwo.swap_mul_baseEmb_mul_inv g 1]
    simp only [← A5WrTwo.baseEmb.map_inv, ← A5WrTwo.baseEmb.map_mul]
  · intro hp1
    have hg' : g⁻¹ = 1 := by
      have := congrArg Prod.fst hp1
      simpa using this
    exact hg (inv_eq_one.mp hg')

private lemma exists_mul_conj_mul_inv_ne_one {x : alternatingGroup (Fin 5)} (hx : x ≠ 1) :
    ∃ g : alternatingGroup (Fin 5), g * x * g⁻¹ * x⁻¹ ≠ 1 := by
  by_contra h
  push Not at h
  have hxcenter : x ∈ Subgroup.center (alternatingGroup (Fin 5)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g * x * g⁻¹ = x := by
      have := h g
      rwa [mul_inv_eq_one] at this
    calc g * x = g * x * g⁻¹ * g := by group
      _ = x * g := by rw [hg]
  have hcenter := alternatingGroup.center_eq_bot (α := Fin 5) (by simp [Nat.card_fin])
  rw [hcenter] at hxcenter
  exact hx (Subgroup.mem_bot.mp hxcenter)

private lemma mem_comap_iota2_iff (B : Subgroup A5WrTwo) [B.Normal]
    (a : alternatingGroup (Fin 5)) :
    a ∈ B.comap iota2 ↔ a ∈ B.comap iota1 := by
  have hBn : B.Normal := inferInstance
  rw [Subgroup.mem_comap, Subgroup.mem_comap]
  constructor
  · intro h
    have hconj : (⟨1, sigmaC2⟩ : A5WrTwo) * iota2 a * (⟨1, sigmaC2⟩ : A5WrTwo)⁻¹ ∈ B :=
      hBn.conj_mem (iota2 a) h (⟨1, sigmaC2⟩ : A5WrTwo)
    rwa [show (⟨1, sigmaC2⟩ : A5WrTwo) * iota2 a * (⟨1, sigmaC2⟩ : A5WrTwo)⁻¹ = iota1 a by
      rw [iota2_apply, iota1_apply]
      exact A5WrTwo.swap_mul_baseEmb_mul_inv 1 a] at hconj
  · intro h
    have hconj : (⟨1, sigmaC2⟩ : A5WrTwo) * iota1 a * (⟨1, sigmaC2⟩ : A5WrTwo)⁻¹ ∈ B :=
      hBn.conj_mem (iota1 a) h (⟨1, sigmaC2⟩ : A5WrTwo)
    rwa [show (⟨1, sigmaC2⟩ : A5WrTwo) * iota1 a * (⟨1, sigmaC2⟩ : A5WrTwo)⁻¹ = iota2 a by
      rw [iota1_apply, iota2_apply]
      exact A5WrTwo.swap_mul_baseEmb_mul_inv a 1] at hconj

theorem L210_card_a5WrTwo : Nat.card A5WrTwo = 7200 := by
  haveI : Finite (Multiplicative (ZMod 2)) := inferInstance
  rw [RegularWreathProduct.card]
  have h5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    norm_num
  have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  rw [h5, h2]
  norm_num

theorem L210_card_base : Nat.card (commutator A5WrTwo) = 3600 := by
  have h := Subgroup.card_mul_index (H := commutator A5WrTwo)
  rw [A5WrTwo.index_commutator] at h
  have hw : Nat.card A5WrTwo = 7200 := L210_card_a5WrTwo
  omega

theorem L210_base_le_of_normal {B : Subgroup A5WrTwo} [B.Normal] (hB : B ≠ ⊥) :
    commutator A5WrTwo ≤ B := by
  have hBn : B.Normal := inferInstance
  obtain ⟨⟨b, hbB⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hB
  have hbne : b ≠ 1 := fun h => hb1 (Subtype.ext h)
  have hbase : ∃ p : alternatingGroup (Fin 5) × alternatingGroup (Fin 5),
      A5WrTwo.baseEmb p ∈ B ∧ p ≠ 1 := by
    by_cases hbc : b ∈ commutator A5WrTwo
    · rw [← A5WrTwo.range_baseEmb] at hbc
      obtain ⟨p, hp⟩ := MonoidHom.mem_range.mp hbc
      refine ⟨p, ?_, ?_⟩
      · rw [hp]; exact hbB
      · intro hp1
        exact hbne (by rw [← hp, hp1, A5WrTwo.baseEmb.map_one])
    · have hbr : b.right ≠ 1 := by
        intro hr
        exact hbc (by rw [A5WrTwo.commutator_eq_ker, MonoidHom.mem_ker]; exact hr)
      have hbσ : b.right = sigmaC2 := by
        rcases coord_cases b.right with h | h
        · exact absurd h hbr
        · exact h
      obtain ⟨g, hg1⟩ := exists_ne (1 : alternatingGroup (Fin 5))
      obtain ⟨p', hp', hp'ne⟩ := exists_baseElem_in_normal hbσ g hg1
      refine ⟨p', ?_, hp'ne⟩
      rw [hp']
      exact B.mul_mem hbB (hBn.conj_mem b⁻¹ (B.inv_mem hbB) (A5WrTwo.baseEmb (g, 1)))
  haveI : IsSimpleGroup (alternatingGroup (Fin 5)) :=
    alternatingGroup.isSimpleGroup (by simp [Nat.card_fin])
  have hK1ne : B.comap iota1 ≠ ⊥ := by
    obtain ⟨p, hpB, hpne⟩ := hbase
    have hxy : p.1 ≠ 1 ∨ p.2 ≠ 1 := by
      by_contra h
      push Not at h
      exact hpne (Prod.ext h.1 h.2)
    rcases hxy with hx | hy
    · obtain ⟨g, hg⟩ := exists_mul_conj_mul_inv_ne_one hx
      have hconj : A5WrTwo.baseEmb (g, 1) * A5WrTwo.baseEmb p *
          (A5WrTwo.baseEmb (g, 1))⁻¹ ∈ B :=
        hBn.conj_mem (A5WrTwo.baseEmb p) hpB (A5WrTwo.baseEmb (g, 1))
      have hmem : A5WrTwo.baseEmb (g, 1) * A5WrTwo.baseEmb p *
          (A5WrTwo.baseEmb (g, 1))⁻¹ * (A5WrTwo.baseEmb p)⁻¹ ∈ B :=
        B.mul_mem hconj (B.inv_mem hpB)
      rw [baseEmb_conj_first g p.1 p.2] at hmem
      have hcK1 : g * p.1 * g⁻¹ * p.1⁻¹ ∈ B.comap iota1 := by
        rw [Subgroup.mem_comap]
        simpa only [iota1_apply] using hmem
      refine fun hbot => hg ?_
      rw [hbot] at hcK1
      exact Subgroup.mem_bot.mp hcK1
    · obtain ⟨g, hg⟩ := exists_mul_conj_mul_inv_ne_one hy
      have hconj : A5WrTwo.baseEmb (1, g) * A5WrTwo.baseEmb p *
          (A5WrTwo.baseEmb (1, g))⁻¹ ∈ B :=
        hBn.conj_mem (A5WrTwo.baseEmb p) hpB (A5WrTwo.baseEmb (1, g))
      have hmem : A5WrTwo.baseEmb (1, g) * A5WrTwo.baseEmb p *
          (A5WrTwo.baseEmb (1, g))⁻¹ * (A5WrTwo.baseEmb p)⁻¹ ∈ B :=
        B.mul_mem hconj (B.inv_mem hpB)
      rw [baseEmb_conj_second g p.1 p.2] at hmem
      have hcK2 : g * p.2 * g⁻¹ * p.2⁻¹ ∈ B.comap iota2 := by
        rw [Subgroup.mem_comap]
        simpa only [iota2_apply] using hmem
      have hcK1 : g * p.2 * g⁻¹ * p.2⁻¹ ∈ B.comap iota1 :=
        (mem_comap_iota2_iff B _).mp hcK2
      refine fun hbot => hg ?_
      rw [hbot] at hcK1
      exact Subgroup.mem_bot.mp hcK1
  have hK1top : B.comap iota1 = ⊤ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal (B.comap iota1)).resolve_left hK1ne
  have hK2top : B.comap iota2 = ⊤ := by
    ext a
    rw [mem_comap_iota2_iff B a, hK1top]
  intro w hw
  rw [← A5WrTwo.range_baseEmb] at hw
  obtain ⟨p, hp⟩ := MonoidHom.mem_range.mp hw
  rw [← hp]
  have h1 : iota1 p.1 ∈ B := by
    have hp1 : p.1 ∈ B.comap iota1 := by rw [hK1top]; exact Subgroup.mem_top p.1
    rwa [Subgroup.mem_comap] at hp1
  have h2 : iota2 p.2 ∈ B := by
    have hp2 : p.2 ∈ B.comap iota2 := by rw [hK2top]; exact Subgroup.mem_top p.2
    rwa [Subgroup.mem_comap] at hp2
  have heq : A5WrTwo.baseEmb p = iota1 p.1 * iota2 p.2 := by
    rw [iota1_apply, iota2_apply, ← A5WrTwo.baseEmb.map_mul]
    congr 1
  rw [heq]
  exact B.mul_mem h1 h2

theorem L210_eq_bot_of_normal_isPGroup {B : Subgroup A5WrTwo} [B.Normal] (hB : IsPGroup 2 B) :
    B = ⊥ := by
  by_contra hne
  have hle : commutator A5WrTwo ≤ B := L210_base_le_of_normal hne
  have hdvd : 3600 ∣ Nat.card B := by
    have h := Subgroup.card_dvd_of_le hle
    rwa [L210_card_base] at h
  haveI : Finite A5WrTwo := inferInstance
  obtain ⟨k, hk⟩ := hB.exists_card_eq
  rw [hk] at hdvd
  have h3 : (3 : ℕ) ∣ 2 ^ k := dvd_trans (by norm_num : 3 ∣ 3600) hdvd
  have h32 : (3 : ℕ) ∣ 2 := Nat.Prime.dvd_of_dvd_pow (by norm_num) h3
  norm_num at h32

end CFSG.EvenSporadicStandard.HNRecog.Harada
