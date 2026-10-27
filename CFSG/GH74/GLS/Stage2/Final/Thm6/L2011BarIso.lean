module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Equiv
public import CFSG.GH74.GLS.Stage2.Local.P34Bar
public import CFSG.RankThree.PartTwo.Sec14.Notation
public import CFSG.GH74.GLS.Stage2.Final.Thm6.Defs2
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L20_14Pair

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L2011

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Final.Thm6 CFSG.GH74.GLS.Stage2.Final.Thm6.L20 CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage2.Local.P34

section Iso

variable {G : Type} [Group G]

theorem pPrimeCoreOf_conj_mem {J : Subgroup G} {x : G} (hx : x ∈ J) {n : G} (hn : n ∈ pPrimeCoreOf 2 J) :
    x * n * x⁻¹ ∈ pPrimeCoreOf 2 J := by
  obtain ⟨n', hn', rfl⟩ := hn
  exact ⟨⟨x, hx⟩ * n' * ⟨x, hx⟩⁻¹, (CFSG.pPrimeCore_normal).conj_mem n' hn' ⟨x, hx⟩, rfl⟩

variable [Finite G]

theorem inf_pPrimeCoreOf_le {H J : Subgroup G} (hJH : J ≤ H) (hJn : ∀ h ∈ H, ∀ j ∈ J, h * j * h⁻¹ ∈ J) :
    J ⊓ pPrimeCoreOf 2 H ≤ pPrimeCoreOf 2 J := by
  refine CFSG.RankThree.PartTwo.Sec14.le_pPrimeCoreOf inf_le_left ?_ ?_
  · intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro m
    have hxH : x ∈ H := hJH hx
    constructor
    · intro hm
      exact ⟨hJn x hxH m hm.1, pPrimeCoreOf_conj_mem hxH hm.2⟩
    · intro hm
      have hxi : x⁻¹ ∈ J := J.inv_mem hx
      have h1 := hJn x⁻¹ (hJH hxi) _ hm.1
      have h2 := pPrimeCoreOf_conj_mem (J := H) (H.inv_mem hxH) hm.2
      have e : x⁻¹ * (x * m * x⁻¹) * x⁻¹⁻¹ = m := by group
      rw [e] at h1 h2
      exact ⟨h1, h2⟩
  · have h1 : Nat.card ↥(J ⊓ pPrimeCoreOf 2 H) ∣ Nat.card ↥(pPrimeCoreOf 2 H) :=
      Subgroup.card_dvd_of_le inf_le_right
    have h2 : Nat.Coprime 2 (Nat.card ↥(pPrimeCoreOf 2 H)) := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact CFSG.RankThree.PartTwo.Sec14.coprime_card_pPrimeCoreOf 2 H
    exact Nat.Coprime.coprime_dvd_right h1 h2

omit [Finite G] in
theorem cmap_eq_of_normal {H J : Subgroup G} (hJn : ∀ h ∈ H, ∀ j ∈ J, h * j * h⁻¹ ∈ J) {h : G} (hh : h ∈ H) :
    cmap h J = J := by
  ext x
  rw [mem_cmap]
  constructor
  · intro hx
    have := hJn h hh _ hx
    rwa [show h * (h⁻¹ * x * h) * h⁻¹ = x by group] at this
  · intro hx
    have := hJn h⁻¹ (H.inv_mem hh) x hx
    simpa using this

omit [Finite G] in
theorem conj_mem_pPrimeCoreOf_of_normal {H J : Subgroup G} (hJn : ∀ h ∈ H, ∀ j ∈ J, h * j * h⁻¹ ∈ J) {h : G}
    (hh : h ∈ H) {m : G} (hm : m ∈ pPrimeCoreOf 2 J) : h * m * h⁻¹ ∈ pPrimeCoreOf 2 J := by
  have h1 : h * m * h⁻¹ ∈ cmap h (pPrimeCoreOf 2 J) := by
    rw [mem_cmap]
    have e : h⁻¹ * (h * m * h⁻¹) * h = m := by group
    rw [e]; exact hm
  rwa [← pPrimeCoreOf_cmap, cmap_eq_of_normal hJn hh] at h1

theorem pPrimeCoreOf_le_of_normal {H J : Subgroup G} (hJH : J ≤ H) (hJn : ∀ h ∈ H, ∀ j ∈ J, h * j * h⁻¹ ∈ J) :
    pPrimeCoreOf 2 J ≤ pPrimeCoreOf 2 H := by
  refine CFSG.RankThree.PartTwo.Sec14.le_pPrimeCoreOf ((CFSG.RankThree.PartTwo.Sec14.pPrimeCoreOf_le 2 J).trans hJH) ?_ ?_
  · intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro m
    constructor
    · exact fun hm => conj_mem_pPrimeCoreOf_of_normal hJn hh hm
    · intro hm
      have h1 := conj_mem_pPrimeCoreOf_of_normal hJn (H.inv_mem hh) hm
      have e : h⁻¹ * (h * m * h⁻¹) * h⁻¹⁻¹ = m := by group
      rwa [e] at h1
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact CFSG.RankThree.PartTwo.Sec14.coprime_card_pPrimeCoreOf 2 J

theorem exists_equiv_HBar_barIn {H J : Subgroup G} (hJH : J ≤ H)
    (hJn : ∀ h ∈ H, ∀ j ∈ J, h * j * h⁻¹ ∈ J) :
    Nonempty (HBar J ≃* ↥(barIn H J)) := by
  let φ₀ : ↥J →* HBar H := (mkH H).comp (Subgroup.inclusion hJH)
  have hmem : ∀ j : ↥J, φ₀ j ∈ barIn H J := fun j =>
    Subgroup.mem_map.2 ⟨⟨(j : G), hJH j.2⟩, Subgroup.mem_subgroupOf.2 j.2, rfl⟩
  let φ : ↥J →* ↥(barIn H J) := φ₀.codRestrict (barIn H J) hmem
  have hφs : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.1 hy
    exact ⟨⟨(h : G), Subgroup.mem_subgroupOf.1 hh⟩, Subtype.ext rfl⟩
  have hker : φ.ker = pPrimeCore 2 ↥J := by
    ext j
    rw [MonoidHom.mem_ker]
    have h1 : φ j = 1 ↔ φ₀ j = 1 := by
      constructor
      · intro h; exact congrArg Subtype.val h
      · intro h; exact Subtype.ext h
    rw [h1]
    change mkH H (Subgroup.inclusion hJH j) = 1 ↔ j ∈ pPrimeCore 2 ↥J
    rw [mkH_eq_one_iff]
    constructor
    · intro hj
      have h2 : (j : G) ∈ pPrimeCoreOf 2 H := ⟨_, hj, rfl⟩
      have h3 : (j : G) ∈ pPrimeCoreOf 2 J := inf_pPrimeCoreOf_le hJH hJn ⟨j.2, h2⟩
      obtain ⟨j', hj', hj'e⟩ := h3
      have : j' = j := Subtype.ext hj'e
      rwa [← this]
    · intro hj
      have h2 : (j : G) ∈ pPrimeCoreOf 2 J := ⟨j, hj, rfl⟩
      obtain ⟨j', hj', hj'e⟩ := pPrimeCoreOf_le_of_normal hJH hJn h2
      have : j' = Subgroup.inclusion hJH j := Subtype.ext hj'e
      rwa [← this]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hφs)⟩

theorem simple_barIn_of_simple {H J : Subgroup G} (hJH : J ≤ H)
    (hJn : ∀ h ∈ H, ∀ j ∈ J, h * j * h⁻¹ ∈ J) (hs : IsSimpleGroup (HBar J)) :
    IsSimpleGroup ↥(barIn H J) := by
  obtain ⟨e⟩ := exists_equiv_HBar_barIn hJH hJn
  have := hs
  exact MulEquiv.isSimpleGroup e.symm

theorem J0_conj_mem (z g : G) {h : G} (hh : h ∈ H0 z g) {j : G} (hj : j ∈ J0 z g) :
    h * j * h⁻¹ ∈ J0 z g := by
  have hcH : cmap h (H0 z g) = H0 z g := by
    ext x
    rw [mem_cmap]
    constructor
    · intro hx
      have := (H0 z g).mul_mem ((H0 z g).mul_mem hh hx) ((H0 z g).inv_mem hh)
      rwa [show h * (h⁻¹ * x * h) * h⁻¹ = x by group] at this
    · intro hx
      exact (H0 z g).mul_mem ((H0 z g).mul_mem ((H0 z g).inv_mem hh) hx) hh
  have hJc : cmap h (J0 z g) = J0 z g := by
    unfold J0
    rw [← pLayerOf_cmap, hcH]
  have : h * j * h⁻¹ ∈ cmap h (J0 z g) := by
    rw [mem_cmap]
    have e : h⁻¹ * (h * j * h⁻¹) * h = j := by group
    rw [e]; exact hj
  rwa [hJc] at this

omit [Finite G] in
theorem pLayerOf_le_H (X : Subgroup G) : pLayerOf 2 X ≤ X := sSup_le fun _ hL => hL.1

omit [Finite G] in
theorem J0_le_H0 (z g : G) : J0 z g ≤ H0 z g := pLayerOf_le_H _


end Iso

end CFSG.GH74.GLS.Stage2.Final.Thm6.L2011
