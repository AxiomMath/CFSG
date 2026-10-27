module

public import CFSG.GroupTheory.SolvableHallNodes
public import Mathlib.GroupTheory.Nilpotent
public import TauCeti.Algebra.Group.Subgroup.ModularLaw
public import TauCeti.GroupTheory.Commutator

public section

open scoped commutatorElement

namespace CFSG.GroupTheory

private lemma commutator_sup_sup_le {G : Type*} [Group G] {P Y₁ Y₂ : Subgroup G}
    (hY₁P : Y₁ ≤ Subgroup.normalizer (P : Set G))
    (hY₂P : Y₂ ≤ Subgroup.normalizer (P : Set G))
    (h11 : ∀ x ∈ Y₁, ∀ y ∈ Y₁, x * y * x⁻¹ * y⁻¹ ∈ P)
    (h12 : ∀ x ∈ Y₁, ∀ y ∈ Y₂, x * y * x⁻¹ * y⁻¹ ∈ P)
    (hY₂ab : IsMulCommutative Y₂) :
    ⁅Y₁ ⊔ Y₂, Y₁ ⊔ Y₂⁆ ≤ P := by
  classical
  have hclnorm : Subgroup.closure ((Y₁ : Set G) ∪ (Y₂ : Set G)) ≤
      Subgroup.normalizer (P : Set G) := by
    rw [← Subgroup.sup_eq_closure]
    exact sup_le hY₁P hY₂P
  have hgen : ∀ x ∈ (Y₁ : Set G) ∪ (Y₂ : Set G),
      ∀ y ∈ (Y₁ : Set G) ∪ (Y₂ : Set G), ⁅x, y⁆ ∈ P := by
    intro x hx y hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · simpa [commutatorElement_def] using h11 x hx y hy
    · simpa [commutatorElement_def] using h12 x hx y hy
    · rw [← commutatorElement_inv]
      exact P.inv_mem (by simpa [commutatorElement_def] using h12 y hy x hx)
    · have h1 : ⁅(⟨x, hx⟩ : Y₂), (⟨y, hy⟩ : Y₂)⁆ = 1 :=
        commutatorElement_eq_one_iff_mul_comm.mpr
          (hY₂ab.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
      have h2 : Y₂.subtype ⁅(⟨x, hx⟩ : Y₂), (⟨y, hy⟩ : Y₂)⁆ = 1 := by
        rw [h1]
        rfl
      rw [map_commutatorElement] at h2
      change ⁅Y₂.subtype ⟨x, hx⟩, Y₂.subtype ⟨y, hy⟩⁆ ∈ P
      rw [h2]
      exact P.one_mem
  have h := TauCeti.commutator_closure_closure_le hclnorm hclnorm hgen
  simpa [Subgroup.sup_eq_closure] using h

private lemma odd_relIndex_sup {G : Type*} [Group G] [Finite G] {P Y₁ Y₂ : Subgroup G}
    (hPY₁ : P ≤ Y₁) (hY₂Y₁ : Y₂ ≤ Subgroup.normalizer (Y₁ : Set G))
    (hodd₁ : Odd (P.relIndex Y₁)) (hodd₂ : Odd (Nat.card Y₂)) :
    Odd (P.relIndex (Y₁ ⊔ Y₂)) := by
  classical
  let Y : Subgroup G := Y₁ ⊔ Y₂
  let N : Subgroup Y := Y₁.subgroupOf Y
  let U : Subgroup Y := Y₂.subgroupOf Y
  have hY₁Y : Y₁ ≤ Y := le_sup_left
  have hY₂Y : Y₂ ≤ Y := le_sup_right
  have hNnorm : N.Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hY₁Y).mpr ?_
    exact sup_le Subgroup.le_normalizer hY₂Y₁
  letI : N.Normal := hNnorm
  have hUN : U ⊔ N = ⊤ := by
    have h := (Subgroup.subgroupOf_sup hY₂Y hY₁Y).symm
    rw [h, sup_comm Y₂ Y₁, show Y₁ ⊔ Y₂ = Y from rfl, Subgroup.subgroupOf_self]
  have hmap : U.map (QuotientGroup.mk' N) = ⊤ := by
    have hcod : Codisjoint U (QuotientGroup.mk' N).ker := by
      rw [QuotientGroup.ker_mk']
      exact codisjoint_iff.mpr hUN
    calc U.map (QuotientGroup.mk' N) = (QuotientGroup.mk' N).range :=
          Subgroup.map_eq_range_iff.mpr hcod
      _ = ⊤ := QuotientGroup.range_mk' N
  have hdvd : Nat.card (Y ⧸ N) ∣ Nat.card U := by
    have hcard : Nat.card (U.map (QuotientGroup.mk' N)) = Nat.card (Y ⧸ N) := by
      rw [hmap]
      exact Nat.card_congr (Subgroup.topEquiv (G := Y ⧸ N)).toEquiv
    rw [← hcard]
    exact Subgroup.card_map_dvd _ _
  have hcardU : Nat.card U = Nat.card Y₂ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hY₂Y).toEquiv
  have hoddQuot : Odd (Nat.card (Y ⧸ N)) :=
    Odd.of_dvd_nat hodd₂ (by rwa [hcardU] at hdvd)
  have hoddN : Odd N.index := by
    rw [Subgroup.index_eq_card]
    exact hoddQuot
  have hoddY₁ : Odd (Y₁.relIndex Y) := by
    change Odd N.index
    exact hoddN
  have hoddP : Odd (P.relIndex Y) := by
    rw [← Subgroup.relIndex_mul_relIndex P Y₁ Y hPY₁ hY₁Y]
    exact Nat.odd_mul.mpr ⟨hodd₁, hoddY₁⟩
  exact hoddP

private lemma solvable_sup_of_commutator_le {G : Type*} [Group G] [Finite G]
    {P Y : Subgroup G} (hPY : P ≤ Y) (hYnorm : Y ≤ Subgroup.normalizer (P : Set G))
    (hP : IsPGroup 2 P) (hcomm : ⁅Y, Y⁆ ≤ P) : Group.IsSolvable Y := by
  classical
  let P' : Subgroup Y := P.subgroupOf Y
  have hP' : IsPGroup 2 P' := by
    change IsPGroup 2 (P.subgroupOf Y)
    rw [← Subgroup.comap_subtype P Y]
    exact hP.comap_subtype (K := Y)
  have hP'norm : P'.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPY).mpr hYnorm
  letI : P'.Normal := hP'norm
  have hcomm' : commutator Y ≤ P' := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [Subgroup.mem_subgroupOf]
    change (Y.subtype ⁅x, y⁆ : G) ∈ P
    rw [map_commutatorElement]
    exact hcomm (Subgroup.commutator_mem_commutator x.2 y.2)
  haveI : IsMulCommutative (Y ⧸ P') :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hcomm'
  haveI : Group.IsSolvable (Y ⧸ P') := inferInstance
  haveI : Group.IsNilpotent P' := IsPGroup.isNilpotent (p := 2) hP'
  haveI : Group.IsSolvable P' := IsNilpotent.to_isSolvable
  exact Group.isSolvable_of_subgroup_quotient P'

private lemma exists_odd_hall_subgroup_sup {G : Type*} [Group G] [Finite G]
    {Y₁ Y₂ : Subgroup G} (hsolv : Group.IsSolvable ↥(Y₁ ⊔ Y₂))
    (hodd₂ : Odd (Nat.card Y₂)) :
    ∃ H' : Subgroup ↥(Y₁ ⊔ Y₂), Y₂.subgroupOf (Y₁ ⊔ Y₂) ≤ H' ∧
      IsHallSubgroup {p : Nat.Primes | (p : ℕ) ≠ 2} H' ∧ Odd (Nat.card H') := by
  classical
  let Y : Subgroup G := Y₁ ⊔ Y₂
  let π : Set Nat.Primes := {p | (p : ℕ) ≠ 2}
  let U : Subgroup Y := Y₂.subgroupOf Y
  have hY₂Y : Y₂ ≤ Y := le_sup_right
  have hcardU : Nat.card U = Nat.card Y₂ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hY₂Y).toEquiv
  have hU : IsPiSubgroup π U := by
    intro p hp
    exact Odd.ne_two_of_dvd_nat hodd₂ (by rwa [hcardU] at hp)
  obtain ⟨H', hH'hall, hUH'⟩ :=
    CFSG.SolvableHall.solvable_hall_containment hsolv π U hU
  refine ⟨H', hUH', hH'hall, ?_⟩
  have hnot2 : ¬ 2 ∣ Nat.card H' := by
    intro h2
    have hmem : (⟨2, Nat.prime_two⟩ : Nat.Primes) ∈ π :=
      hH'hall.p_in_pi_of_p_dvd_card ⟨2, Nat.prime_two⟩ h2
    exact hmem rfl
  exact Nat.not_even_iff_odd.mp fun he => hnot2 (even_iff_two_dvd.mp he)

private lemma map_hall_subgroup_odd {G : Type*} [Group G] {Y₁ Y₂ : Subgroup G}
    {H' : Subgroup ↥(Y₁ ⊔ Y₂)} (hY₂H' : Y₂.subgroupOf (Y₁ ⊔ Y₂) ≤ H')
    (hH'odd : Odd (Nat.card H')) :
    Y₂ ≤ H'.map (Y₁ ⊔ Y₂).subtype ∧ H'.map (Y₁ ⊔ Y₂).subtype ≤ Y₁ ⊔ Y₂ ∧
      Odd (Nat.card (H'.map (Y₁ ⊔ Y₂).subtype)) := by
  let Y : Subgroup G := Y₁ ⊔ Y₂
  change Y₂ ≤ H'.map Y.subtype ∧ H'.map Y.subtype ≤ Y₁ ⊔ Y₂ ∧
    Odd (Nat.card (H'.map Y.subtype))
  have hY₂Y : Y₂ ≤ Y := le_sup_right
  refine ⟨?_, Subgroup.map_subtype_le H', ?_⟩
  · rw [← Subgroup.map_subgroupOf_eq_of_le hY₂Y]
    exact Subgroup.map_mono hY₂H'
  · rw [Subgroup.card_map_of_injective Y.subtype_injective]
    exact hH'odd

private lemma inf_eq_bot_and_isMulCommutative {G : Type*} [Group G] [Finite G]
    {P Y H : Subgroup G} (hP : IsPGroup 2 P) (hHodd : Odd (Nat.card H)) (hHleY : H ≤ Y)
    (hcommY : ⁅Y, Y⁆ ≤ P) : P ⊓ H = ⊥ ∧ IsMulCommutative H := by
  have hPinfH : P ⊓ H = ⊥ := by
    obtain ⟨n, hn⟩ := hP.exists_card_eq
    have hcop : Nat.Coprime (Nat.card P) (Nat.card H) := by
      rw [hn]
      exact Nat.Coprime.pow_left n (Odd.coprime_two_left hHodd)
    exact Subgroup.inf_eq_bot_of_coprime hcop
  refine ⟨hPinfH, ?_⟩
  apply Subgroup.commutator_self_eq_bot_iff.mp
  apply le_bot_iff.mp
  rw [← hPinfH]
  exact le_inf
    ((Subgroup.commutator_mono hHleY hHleY).trans hcommY)
    (Subgroup.commutator_le_self H)

private lemma exists_hall_complement_of_isPGroup {Y : Type*} [Group Y] [Finite Y]
    {P' : Subgroup Y} [P'.Normal] (hP' : IsPGroup 2 P') (hoddP' : Odd P'.index) :
    ∃ K : Subgroup Y, P'.IsComplement' K ∧
      IsHallSubgroup {p : Nat.Primes | (p : ℕ) ≠ 2} K := by
  have hcop : Nat.Coprime (Nat.card P') P'.index := by
    obtain ⟨n, hn⟩ := hP'.exists_card_eq
    rw [hn]
    exact Nat.Coprime.pow_left n (Odd.coprime_two_left hoddP')
  obtain ⟨K, hKcomp⟩ := Subgroup.exists_right_complement'_of_coprime (N := P') hcop
  have hKorder : Nat.card K = P'.index := by
    have h1 := hKcomp.card_mul_card
    have h2 := P'.card_mul_index
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (h1.trans h2.symm)
  have hKodd : Odd (Nat.card K) := by
    rw [hKorder]
    exact hoddP'
  refine ⟨K, hKcomp, ?_⟩
  refine isHallSubgroup_of _ K ?_ ?_
  · intro p hp
    exact Odd.ne_two_of_dvd_nat hKodd hp
  · intro p hp hpidx
    have hKidx : K.index = Nat.card P' := hKcomp.index_eq_card
    rw [hKidx] at hpidx
    obtain ⟨n, hn⟩ := hP'.exists_card_eq
    rw [hn] at hpidx
    exact hp (Nat.prime_eq_prime_of_dvd_pow p.2 Nat.prime_two hpidx)

private lemma sup_eq_top_of_hall {Y : Type*} [Group Y] [Finite Y]
    (hsolv : Group.IsSolvable Y) {P' H' : Subgroup Y} [P'.Normal]
    (hP' : IsPGroup 2 P') (hoddP' : Odd P'.index)
    (hH'hall : IsHallSubgroup {p : Nat.Primes | (p : ℕ) ≠ 2} H') :
    P' ⊔ H' = ⊤ := by
  obtain ⟨K, hKcomp, hKhall⟩ := exists_hall_complement_of_isPGroup hP' hoddP'
  obtain ⟨g, hg⟩ :=
    CFSG.exists_conj_eq_of_isHallSubgroup_of_solvable hsolv hKhall hH'hall
  have hmap := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) hKcomp.sup_eq_top
  have hconjP : Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj g)) P' = P' := by
    simpa using Subgroup.Normal.map_conj_eq (H := P') g
  rw [Subgroup.map_sup, hconjP,
    Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective] at hmap
  rw [hg]
  exact hmap

private lemma sup_eq_of_hall {G : Type*} [Group G] {P Y : Subgroup G} [Finite Y]
    {H' : Subgroup Y} {H : Subgroup G} (hsolv : Group.IsSolvable Y) (hPY : P ≤ Y)
    (hYnorm : Y ≤ Subgroup.normalizer (P : Set G)) (hP : IsPGroup 2 P)
    (hodd : Odd (P.relIndex Y)) (hHmap : H = H'.map Y.subtype)
    (hH'hall : IsHallSubgroup {p : Nat.Primes | (p : ℕ) ≠ 2} H') :
    P ⊔ H = Y := by
  let P' : Subgroup Y := P.subgroupOf Y
  have hP' : IsPGroup 2 P' := by
    change IsPGroup 2 (P.subgroupOf Y)
    rw [← Subgroup.comap_subtype P Y]
    exact hP.comap_subtype (K := Y)
  have hP'norm : P'.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPY).mpr hYnorm
  have hoddP' : Odd P'.index := by
    change Odd (P.relIndex Y)
    exact hodd
  letI : P'.Normal := hP'norm
  have htop : P' ⊔ H' = ⊤ := sup_eq_top_of_hall hsolv hP' hoddP' hH'hall
  have h := congrArg (Subgroup.map Y.subtype) htop
  rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hPY,
    Subgroup.map_top, Subgroup.range_subtype, ← hHmap] at h
  exact h

theorem exists_abelian_hall_sup {G : Type*} [Group G] [Finite G]
    {P Y₁ Y₂ : Subgroup G} (hP : IsPGroup 2 P) (hPY₁ : P ≤ Y₁)
    (hY₁P : Y₁ ≤ Subgroup.normalizer (P : Set G))
    (hY₂P : Y₂ ≤ Subgroup.normalizer (P : Set G))
    (hY₂Y₁ : Y₂ ≤ Subgroup.normalizer (Y₁ : Set G))
    (hodd₁ : Odd (P.relIndex Y₁)) (hodd₂ : Odd (Nat.card Y₂))
    (hY₂ab : IsMulCommutative Y₂)
    (h11 : ∀ x ∈ Y₁, ∀ y ∈ Y₁, x * y * x⁻¹ * y⁻¹ ∈ P)
    (h12 : ∀ x ∈ Y₁, ∀ y ∈ Y₂, x * y * x⁻¹ * y⁻¹ ∈ P) :
    ∃ H : Subgroup G, Y₂ ≤ H ∧ H ≤ Y₁ ⊔ Y₂ ∧ Odd (Nat.card H) ∧ IsMulCommutative H ∧
      P ⊓ H = ⊥ ∧ P ⊔ (Y₁ ⊓ H) = Y₁ := by
  classical
  let Y : Subgroup G := Y₁ ⊔ Y₂
  have hY₁Y : Y₁ ≤ Y := le_sup_left
  have hPY : P ≤ Y := hPY₁.trans hY₁Y
  have hYnorm : Y ≤ Subgroup.normalizer (P : Set G) := sup_le hY₁P hY₂P
  have hcommY : ⁅Y, Y⁆ ≤ P := by
    simpa [Y] using commutator_sup_sup_le hY₁P hY₂P h11 h12 hY₂ab
  have hsolvY : Group.IsSolvable Y := solvable_sup_of_commutator_le hPY hYnorm hP hcommY
  have hoddY : Odd (P.relIndex Y) := by
    simpa [Y] using
      odd_relIndex_sup (P := P) (Y₁ := Y₁) (Y₂ := Y₂) hPY₁ hY₂Y₁ hodd₁ hodd₂
  obtain ⟨H', hY₂H', hH'hall, hH'odd⟩ :=
    exists_odd_hall_subgroup_sup (Y₁ := Y₁) (Y₂ := Y₂) hsolvY hodd₂
  let H : Subgroup G := H'.map Y.subtype
  have hHmap : H = H'.map Y.subtype := rfl
  obtain ⟨hY₂H, hHleY, hHodd⟩ := map_hall_subgroup_odd hY₂H' hH'odd
  obtain ⟨hPinfH, hHab⟩ :=
    inf_eq_bot_and_isMulCommutative hP hHodd hHleY hcommY
  have hPH : P ⊔ H = Y :=
    sup_eq_of_hall hsolvY hPY hYnorm hP hoddY hHmap hH'hall
  have hHnormP : H ≤ Subgroup.normalizer (P : Set G) := hHleY.trans hYnorm
  have hDed : P ⊔ (Y₁ ⊓ H) = Y₁ := by
    have h := Subgroup.inf_sup_assoc_of_le (H := H) (K := Y₁) (N := P) hHnormP hPY₁
    rw [sup_comm H P, hPH, inf_eq_left.mpr hY₁Y] at h
    rwa [sup_comm] at h
  exact ⟨H, hY₂H, hHleY, hHodd, hHab, hPinfH, hDed⟩

end CFSG.GroupTheory
