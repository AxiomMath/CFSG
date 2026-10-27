module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.BaseEmb

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

private theorem coord_cases (q : Multiplicative (ZMod 2)) :
    q = 1 ∨ q = Multiplicative.ofAdd 1 := by
  rcases (show ∀ e : ZMod 2, e = 0 ∨ e = 1 by decide) (Multiplicative.toAdd q) with h | h
  · left
    rw [← ofAdd_toAdd q, h]
    rfl
  · right
    rw [← ofAdd_toAdd q, h]

private theorem sigmaC2_ne_one : (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1 := by decide

private theorem sigmaC2_mul_self :
    (Multiplicative.ofAdd (1 : ZMod 2)) * Multiplicative.ofAdd (1 : ZMod 2) = 1 := by
  decide

private abbrev swapA5 : A5WrTwo := ⟨1, Multiplicative.ofAdd (1 : ZMod 2)⟩

private theorem swapA5_mul_self : swapA5 * swapA5 = 1 := by
  apply RegularWreathProduct.ext
  · funext q
    rcases coord_cases q with rfl | rfl <;>
      simp [swapA5, RegularWreathProduct.mul_def, sigmaC2_mul_self]
  · simp [swapA5, RegularWreathProduct.mul_def, sigmaC2_mul_self]

private abbrev centBase (x y : alternatingGroup (Fin 5)) : Subgroup A5WrTwo :=
  Subgroup.centralizer ({A5WrTwo.baseEmb (x, y)} : Set A5WrTwo)

private def centBaseHom (x y : alternatingGroup (Fin 5)) :
    ↥(centBase x y) →* Multiplicative (ZMod 2) :=
  (RegularWreathProduct.rightHom : A5WrTwo →* Multiplicative (ZMod 2)).comp
    (centBase x y).subtype

private theorem natCard_prod_subgroup {G N : Type*} [Group G] [Group N]
    (H : Subgroup G) (K : Subgroup N) :
    Nat.card ↥(H.prod K) = Nat.card ↥H * Nat.card ↥K := by
  have h : Nat.card ↥(H.prod K) = Nat.card (↥H × ↥K) :=
    Nat.card_congr
      { toFun := fun p =>
          (⟨p.1.1, (Subgroup.mem_prod.mp p.2).1⟩, ⟨p.1.2, (Subgroup.mem_prod.mp p.2).2⟩)
        invFun := fun q => ⟨(q.1.1, q.2.1), Subgroup.mem_prod.mpr ⟨q.1.2, q.2.2⟩⟩
        left_inv := fun _ => Subtype.ext rfl
        right_inv := fun _ => Prod.ext (Subtype.ext rfl) (Subtype.ext rfl) }
  rw [h, Nat.card_prod]

private theorem baseEmb_right (p : alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) :
    (A5WrTwo.baseEmb p).right = 1 := by
  have hmem : A5WrTwo.baseEmb p ∈ A5WrTwo.baseEmb.range := MonoidHom.mem_range.mpr ⟨p, rfl⟩
  rw [A5WrTwo.range_baseEmb, A5WrTwo.commutator_eq_ker] at hmem
  exact hmem

private theorem baseEmb_conj (p q : alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) :
    A5WrTwo.baseEmb p * A5WrTwo.baseEmb q * (A5WrTwo.baseEmb p)⁻¹ =
      A5WrTwo.baseEmb (p * q * p⁻¹) := by
  rw [← map_mul, ← map_inv, ← map_mul]

private theorem baseEmb_mul_swap_conj (g h x y : alternatingGroup (Fin 5)) :
    (A5WrTwo.baseEmb (g, h) * swapA5) * A5WrTwo.baseEmb (x, y) *
        (A5WrTwo.baseEmb (g, h) * swapA5)⁻¹ =
      A5WrTwo.baseEmb (g * y * g⁻¹, h * x * h⁻¹) := by
  have h1 : (A5WrTwo.baseEmb (g, h) * swapA5) * A5WrTwo.baseEmb (x, y) *
        (A5WrTwo.baseEmb (g, h) * swapA5)⁻¹ =
      A5WrTwo.baseEmb (g, h) * (swapA5 * A5WrTwo.baseEmb (x, y) * swapA5⁻¹) *
        (A5WrTwo.baseEmb (g, h))⁻¹ := by
    group
  rw [h1, A5WrTwo.swap_mul_baseEmb_mul_inv]
  exact baseEmb_conj (g, h) (y, x)

private theorem exists_baseEmb_mul_swap_of_right_eq (g : A5WrTwo)
    (hg : g.right = Multiplicative.ofAdd (1 : ZMod 2)) :
    ∃ p : alternatingGroup (Fin 5) × alternatingGroup (Fin 5),
      g = A5WrTwo.baseEmb p * swapA5 := by
  have hgs : (g * swapA5).right = 1 := by
    rw [RegularWreathProduct.mul_right, hg]
    simpa [swapA5] using sigmaC2_mul_self
  have hmem : g * swapA5 ∈ A5WrTwo.baseEmb.range := by
    rw [A5WrTwo.range_baseEmb, A5WrTwo.commutator_eq_ker]
    exact hgs
  obtain ⟨p, hp⟩ := MonoidHom.mem_range.mp hmem
  refine ⟨p, ?_⟩
  calc g = (g * swapA5) * swapA5 := by rw [mul_assoc, swapA5_mul_self, mul_one]
    _ = A5WrTwo.baseEmb p * swapA5 := by rw [← hp]

private theorem baseEmb_mem_centralizer_baseEmb
    (p q : alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) :
    A5WrTwo.baseEmb p ∈ Subgroup.centralizer ({A5WrTwo.baseEmb q} : Set A5WrTwo) ↔
      p.1 ∈ Subgroup.centralizer ({q.1} : Set (alternatingGroup (Fin 5))) ∧
        p.2 ∈ Subgroup.centralizer ({q.2} : Set (alternatingGroup (Fin 5))) := by
  constructor
  · intro h
    rw [Subgroup.mem_centralizer_singleton_iff] at h
    have h' : p * q = q * p := A5WrTwo.baseEmb_injective (by simpa only [map_mul] using h)
    exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Prod.fst h'),
      Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Prod.snd h')⟩
  · rintro ⟨h1, h2⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at h1 h2
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc A5WrTwo.baseEmb p * A5WrTwo.baseEmb q
        = A5WrTwo.baseEmb (p * q) := (map_mul A5WrTwo.baseEmb p q).symm
      _ = A5WrTwo.baseEmb (q * p) := by
        congr 1
        exact Prod.ext h1 h2
      _ = A5WrTwo.baseEmb q * A5WrTwo.baseEmb p := map_mul A5WrTwo.baseEmb q p

private theorem centBase_inf_range (x y : alternatingGroup (Fin 5)) :
    centBase x y ⊓ A5WrTwo.baseEmb.range =
      Subgroup.map A5WrTwo.baseEmb
        ((Subgroup.centralizer ({x} : Set (alternatingGroup (Fin 5)))).prod
          (Subgroup.centralizer ({y} : Set (alternatingGroup (Fin 5))))) := by
  ext w
  rw [Subgroup.mem_inf, Subgroup.mem_map]
  constructor
  · rintro ⟨hwK, hwR⟩
    obtain ⟨p, hp⟩ := MonoidHom.mem_range.mp hwR
    rw [← hp] at hwK
    refine ⟨p, Subgroup.mem_prod.mpr ((baseEmb_mem_centralizer_baseEmb p (x, y)).mp hwK), hp⟩
  · rintro ⟨p, hp_mem, hp_eq⟩
    refine ⟨?_, ?_⟩
    · rw [← hp_eq]
      exact (baseEmb_mem_centralizer_baseEmb p (x, y)).mpr (Subgroup.mem_prod.mp hp_mem)
    · rw [← hp_eq]
      exact MonoidHom.mem_range.mpr ⟨p, rfl⟩

private theorem card_ker_centBaseHom (x y : alternatingGroup (Fin 5)) :
    Nat.card ↥(centBaseHom x y).ker =
      Nat.card ↥(Subgroup.centralizer ({x} : Set (alternatingGroup (Fin 5)))) *
        Nat.card ↥(Subgroup.centralizer ({y} : Set (alternatingGroup (Fin 5)))) := by
  have h1 : (centBaseHom x y).ker =
      (MonoidHom.ker (RegularWreathProduct.rightHom :
        A5WrTwo →* Multiplicative (ZMod 2))).subgroupOf (centBase x y) := by
    show MonoidHom.ker ((RegularWreathProduct.rightHom :
      A5WrTwo →* Multiplicative (ZMod 2)).comp (centBase x y).subtype) = _
    rw [← MonoidHom.comap_ker (RegularWreathProduct.rightHom :
      A5WrTwo →* Multiplicative (ZMod 2)) (centBase x y).subtype, Subgroup.comap_subtype]
  rw [h1, ← Subgroup.card_map_of_injective (centBase x y).subtype_injective,
    Subgroup.subgroupOf_map_subtype]
  rw [(A5WrTwo.range_baseEmb.trans A5WrTwo.commutator_eq_ker).symm, inf_comm,
    centBase_inf_range, Subgroup.card_map_of_injective A5WrTwo.baseEmb_injective]
  exact natCard_prod_subgroup _ _

private theorem card_range_centBaseHom_of_isConj (x y : alternatingGroup (Fin 5))
    (hxy : IsConj x y) : Nat.card ↥(centBaseHom x y).range = 2 := by
  obtain ⟨c, hc⟩ := isConj_iff.mp hxy
  let w : A5WrTwo := A5WrTwo.baseEmb (c⁻¹, c) * swapA5
  have hw : w ∈ centBase x y := by
    change w ∈ Subgroup.centralizer ({A5WrTwo.baseEmb (x, y)} : Set A5WrTwo)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hconj : w * A5WrTwo.baseEmb (x, y) * w⁻¹ = A5WrTwo.baseEmb (x, y) := by
      dsimp only [w]
      rw [baseEmb_mul_swap_conj]
      congr 1
      exact Prod.ext (by rw [← hc]; group) hc
    calc w * A5WrTwo.baseEmb (x, y)
        = (w * A5WrTwo.baseEmb (x, y) * w⁻¹) * w := by group
      _ = A5WrTwo.baseEmb (x, y) * w := by rw [hconj]
  have hmem : (Multiplicative.ofAdd (1 : ZMod 2)) ∈ (centBaseHom x y).range := by
    refine MonoidHom.mem_range.mpr ⟨⟨w, hw⟩, ?_⟩
    change w.right = Multiplicative.ofAdd (1 : ZMod 2)
    dsimp only [w]
    rw [RegularWreathProduct.mul_right, baseEmb_right, one_mul]
  have htop : (centBaseHom x y).range = ⊤ := by
    rw [eq_top_iff]
    intro r _
    rcases coord_cases r with rfl | rfl
    · exact (centBaseHom x y).range.one_mem
    · exact hmem
  rw [htop, Subgroup.card_top, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

private theorem card_range_centBaseHom_of_not_isConj (x y : alternatingGroup (Fin 5))
    (hxy : ¬ IsConj x y) : Nat.card ↥(centBaseHom x y).range = 1 := by
  have hnotmem : (Multiplicative.ofAdd (1 : ZMod 2)) ∉ (centBaseHom x y).range := by
    rintro ⟨k, hk⟩
    have hk' : (k : A5WrTwo).right = Multiplicative.ofAdd (1 : ZMod 2) := hk
    obtain ⟨p, hp⟩ := exists_baseEmb_mul_swap_of_right_eq (k : A5WrTwo) hk'
    have hcu : (k : A5WrTwo) * A5WrTwo.baseEmb (x, y) =
        A5WrTwo.baseEmb (x, y) * (k : A5WrTwo) :=
      Subgroup.mem_centralizer_singleton_iff.mp (show (k : A5WrTwo) ∈
        Subgroup.centralizer ({A5WrTwo.baseEmb (x, y)} : Set A5WrTwo) from k.2)
    have hconj : (k : A5WrTwo) * A5WrTwo.baseEmb (x, y) * (k : A5WrTwo)⁻¹ =
        A5WrTwo.baseEmb (x, y) := by
      rw [hcu]
      group
    rw [hp, baseEmb_mul_swap_conj] at hconj
    have hprod : (p.1 * y * p.1⁻¹, p.2 * x * p.2⁻¹) = (x, y) :=
      A5WrTwo.baseEmb_injective hconj
    exact hxy (isConj_iff.mpr ⟨p.2, congrArg Prod.snd hprod⟩)
  have hbot : (centBaseHom x y).range = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro r hr
    rcases coord_cases r with h | h
    · exact h
    · rw [h] at hr
      exact absurd hr hnotmem
  rw [hbot, Subgroup.card_bot]

theorem card_centralizer_baseEmb_of_isConj {x y : alternatingGroup (Fin 5)} (hxy : IsConj x y) :
    Nat.card ↥(Subgroup.centralizer ({A5WrTwo.baseEmb (x, y)} : Set A5WrTwo)) =
      Nat.card ↥(Subgroup.centralizer ({x} : Set (alternatingGroup (Fin 5)))) *
        Nat.card ↥(Subgroup.centralizer ({y} : Set (alternatingGroup (Fin 5)))) * 2 := by
  have hmain := Subgroup.card_ker_mul_card_range (centBaseHom x y)
  rw [card_ker_centBaseHom x y, card_range_centBaseHom_of_isConj x y hxy] at hmain
  exact hmain.symm

theorem card_centralizer_baseEmb_of_not_isConj {x y : alternatingGroup (Fin 5)}
    (hxy : ¬ IsConj x y) :
    Nat.card ↥(Subgroup.centralizer ({A5WrTwo.baseEmb (x, y)} : Set A5WrTwo)) =
      Nat.card ↥(Subgroup.centralizer ({x} : Set (alternatingGroup (Fin 5)))) *
        Nat.card ↥(Subgroup.centralizer ({y} : Set (alternatingGroup (Fin 5)))) := by
  have hmain := Subgroup.card_ker_mul_card_range (centBaseHom x y)
  rw [card_ker_centBaseHom x y, card_range_centBaseHom_of_not_isConj x y hxy] at hmain
  rw [mul_one] at hmain
  exact hmain.symm

end CFSG.EvenSporadicStandard.HNRecog.Section3
