module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.DerivedOf
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.HSide.Map
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.SuborbitFacts

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3Model

open Subgroup CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3
open scoped commutatorElement

theorem isElemTwo_of_map {A G : Type} [Group A] [Group G] {f : A →* G}
    (hf : Function.Injective f) {n : ℕ} {E : Subgroup A} (h : IsElemTwo n (E.map f)) :
    IsElemTwo n E := by
  obtain ⟨⟨hcomm, hexp⟩, hcard⟩ := h
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · haveI : IsMulCommutative ↥(E.map f) := hcomm
    refine isMulCommutative_iff.mpr fun a b => ?_
    have h := mul_comm' (M := ↥(E.map f)) ⟨f a, Subgroup.mem_map_of_mem f a.2⟩
      ⟨f b, Subgroup.mem_map_of_mem f b.2⟩
    apply Subtype.ext
    apply hf
    have h' : f a * f b = f b * f a := congrArg Subtype.val h
    rw [← map_mul, ← map_mul] at h'
    exact h'
  · intro x hx
    apply hf
    rw [map_pow, map_one]
    exact hexp (f x) (Subgroup.mem_map_of_mem f hx)
  · rw [Nat.card_congr (Subgroup.equivMapOfInjective E f hf).toEquiv]
    exact hcard

theorem TwoFourData.of_map {A G : Type} [Group A] [Group G] {f : A →* G}
    (hf : Function.Injective f) {X : Subgroup A} (h : TwoFourData (X.map f)) : TwoFourData X := by
  have hd : derivedOf (X.map f) = (derivedOf X).map f := derivedOf_map_of_injective hf X
  have hp : CFSG.Open.pCoreOf 2 (derivedOf (X.map f)) =
      (CFSG.Open.pCoreOf 2 (derivedOf X)).map f := by
    rw [hd]
    exact pCoreOf_map_of_injective hf (derivedOf X)
  refine ⟨?_, ?_, ?_⟩
  · have h1 := h.card_derived
    rwa [hd, Subgroup.card_map_of_injective hf] at h1
  · have h1 := h.elem_two
    rw [hp] at h1
    exact isElemTwo_of_map hf h1
  · intro S hS hSinv
    have hS' : S.map f ≤ CFSG.Open.pCoreOf 2 (derivedOf (X.map f)) := by
      rw [hp]
      exact Subgroup.map_mono hS
    have hinv : ∀ g ∈ X.map f, ∀ s ∈ S.map f, g * s * g⁻¹ ∈ S.map f := by
      rintro _ ⟨g, hg, rfl⟩ _ ⟨s, hs, rfl⟩
      exact ⟨g * s * g⁻¹, hSinv g hg s hs, by simp only [map_mul, map_inv]⟩
    rcases h.irreducible (S.map f) hS' hinv with h1 | h1
    · exact Or.inl ((Subgroup.map_eq_bot_iff_of_injective S hf).mp h1)
    · rw [hp] at h1
      exact Or.inr (Subgroup.map_injective hf h1)

theorem commutator_mem_derivedOf {M : Type} [Group M] {X : Subgroup M} {u v : M} (hu : u ∈ X)
    (hv : v ∈ X) : u * v * u⁻¹ * v⁻¹ ∈ derivedOf X := by
  have hmem : u * v * u⁻¹ * v⁻¹ ∈ X :=
    mul_mem (mul_mem (mul_mem hu hv) (inv_mem hu)) (inv_mem hv)
  refine mem_derivedOf_iff.mpr ⟨hmem, ?_⟩
  have hc : (⟨u * v * u⁻¹ * v⁻¹, hmem⟩ : ↥X) = ⁅(⟨u, hu⟩ : ↥X), (⟨v, hv⟩ : ↥X)⁆ :=
    Subtype.ext (by rw [commutatorElement_def]; rfl)
  rw [hc, _root_.commutator_def]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

theorem pCoreOf_eq_of_hom {M : Type} [Group M] [Finite M] {Y N : Subgroup M} (hNY : N ≤ Y)
    (hY : Nat.card ↥Y = 960) (hN : Nat.card ↥N = 16) (ψ : ↥Y →* Equiv.Perm (Fin 5))
    (hrange : Nat.card ↥ψ.range = 60) (hNker : ∀ (n : M) (h : n ∈ N), ψ ⟨n, hNY h⟩ = 1) :
    CFSG.Open.pCoreOf 2 Y = N := by
  have hkerCard : Nat.card ↥ψ.ker = 16 := by
    have h := Subgroup.card_ker_mul_card_range ψ
    rw [hrange, hY] at h
    omega
  have hle : N.subgroupOf Y ≤ ψ.ker := by
    intro y hy
    rw [MonoidHom.mem_ker]
    simpa using hNker (y : M) (Subgroup.mem_subgroupOf.mp hy)
  have hNcard : Nat.card ↥(N.subgroupOf Y) = 16 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNY).toEquiv, hN]
  have hker : N.subgroupOf Y = ψ.ker :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hkerCard, hNcard])
  have hNnormal : (N.subgroupOf Y).Normal := by
    rw [hker]
    exact MonoidHom.normal_ker ψ
  have hNp : IsPGroup 2 ↥(N.subgroupOf Y) := IsPGroup.of_card (n := 4) (by rw [hNcard]; norm_num)
  apply le_antisymm
  ·
    have h120 : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
      rfl
    have hrangeEq : ψ.range = alternatingGroup (Fin 5) := by
      apply Equiv.Perm.eq_alternatingGroup_of_index_eq_two
      have h := Subgroup.card_mul_index ψ.range
      rw [hrange, h120] at h
      omega
    haveI : IsSimpleGroup ↥ψ.range := MulEquiv.isSimpleGroup (MulEquiv.subgroupCongr hrangeEq)
    have hPn : ((CFSG.pCore 2 ↥Y).map ψ.rangeRestrict).Normal :=
      Subgroup.Normal.map CFSG.pCore_normal ψ.rangeRestrict (MonoidHom.rangeRestrict_surjective ψ)
    have hPp : IsPGroup 2 ↥((CFSG.pCore 2 ↥Y).map ψ.rangeRestrict) :=
      CFSG.pCore_isPGroup.map ψ.rangeRestrict
    haveI := hPn
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((CFSG.pCore 2 ↥Y).map ψ.rangeRestrict) with
      hbot | htop
    · have hPle : CFSG.pCore 2 ↥Y ≤ ψ.ker := by
        have h := (Subgroup.map_eq_bot_iff _).mp hbot
        rwa [MonoidHom.ker_rangeRestrict] at h
      calc CFSG.Open.pCoreOf 2 Y = (CFSG.pCore 2 ↥Y).map Y.subtype := rfl
        _ ≤ (N.subgroupOf Y).map Y.subtype := Subgroup.map_mono (hker ▸ hPle)
        _ = N := Subgroup.map_subgroupOf_eq_of_le hNY
    · exfalso
      have h2 : IsPGroup 2 ↥(⊤ : Subgroup ↥ψ.range) := by
        rw [← htop]
        exact hPp
      obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp (h2.of_equiv Subgroup.topEquiv)
      have h3 : 3 ∣ 2 ^ n := by
        rw [← hn, hrange]
        norm_num
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
  ·
    have h1 : N.subgroupOf Y ≤ CFSG.pCore 2 ↥Y := le_sSup ⟨hNnormal, hNp⟩
    calc N = (N.subgroupOf Y).map Y.subtype := (Subgroup.map_subgroupOf_eq_of_le hNY).symm
      _ ≤ (CFSG.pCore 2 ↥Y).map Y.subtype := Subgroup.map_mono h1

theorem isMulCommutative_of_sq {M : Type} [Group M] {N : Subgroup M} (hNsq : ∀ n ∈ N, n * n = 1) :
    IsMulCommutative ↥N := by
  refine isMulCommutative_iff.mpr fun a b => ?_
  have h1 := hNsq _ (N.mul_mem a.2 b.2)
  have ha : (a : M)⁻¹ = a := inv_eq_of_mul_eq_one_right (hNsq _ a.2)
  have hb : (b : M)⁻¹ = b := inv_eq_of_mul_eq_one_right (hNsq _ b.2)
  have hab : ((a : M) * b)⁻¹ = (a : M) * b := inv_eq_of_mul_eq_one_right h1
  rw [mul_inv_rev, ha, hb] at hab
  exact Subtype.ext hab.symm

theorem twoFourData_of_data {M : Type} [Group M] [Finite M] {X Y N : Subgroup M}
    (hshape : IsShapeTwoTwoTimesTwoFourA5 ↥X) (hX : Nat.card ↥X = 3840)
    (hYX : Y ≤ derivedOf X) (hY : Nat.card ↥Y = 960) (hNY : N ≤ Y) (hN : Nat.card ↥N = 16)
    (hNsq : ∀ n ∈ N, n * n = 1) (ψ : ↥Y →* Equiv.Perm (Fin 5))
    (hrange : Nat.card ↥ψ.range = 60) (hNker : ∀ (n : M) (h : n ∈ N), ψ ⟨n, hNY h⟩ = 1)
    (hirr : ∀ S : Subgroup M, S ≤ N → (∀ g ∈ X, ∀ s ∈ S, g * s * g⁻¹ ∈ S) → S = ⊥ ∨ S = N) :
    TwoFourData X := by
  have hderived : derivedOf X = Y := by
    obtain ⟨Y₀, _, -, ⟨e⟩⟩ := hshape
    let χ : ↥X →* Elem2 2 := (MonoidHom.fst (Elem2 2) Y₀).comp e.toMonoidHom
    have hχ : Function.Surjective χ := fun a => ⟨e.symm (a, 1), by simp [χ]⟩
    have hE2 : Nat.card (Elem2 2) = 4 := by
      rw [Elem2, Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
      rfl
    have hker : Nat.card ↥χ.ker = 960 := by
      have h := Subgroup.card_ker_mul_card_range χ
      rw [MonoidHom.range_eq_top.mpr hχ, Subgroup.card_top, hE2, hX] at h
      omega
    have hcomm : _root_.commutator ↥X ≤ χ.ker := Abelianization.commutator_subset_ker χ
    have hle : Nat.card ↥(derivedOf X) ≤ Nat.card ↥Y := by
      rw [derivedOf, Subgroup.card_map_of_injective X.subtype_injective, hY, ← hker]
      exact Subgroup.card_le_of_le hcomm
    exact (Subgroup.eq_of_le_of_card_ge hYX hle).symm
  have hp : CFSG.Open.pCoreOf 2 (derivedOf X) = N := by
    rw [hderived]
    exact pCoreOf_eq_of_hom hNY hY hN ψ hrange hNker
  refine ⟨?_, ?_, ?_⟩
  · rw [hderived, hY]
  · rw [hp]
    exact ⟨⟨isMulCommutative_of_sq hNsq, fun x hx => by rw [pow_two]; exact hNsq x hx⟩,
      by rw [hN]; norm_num⟩
  · rw [hp]
    exact hirr

end CFSG.EvenSporadicStandard.HNRecog.Section3Model
