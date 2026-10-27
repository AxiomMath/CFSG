module

public import CFSG.GH74.Uniqueness.Section7Cor713Defs
public import CFSG.GH74.Uniqueness.Lemma311
public import CFSG.GH74.Uniqueness.Section6Defs

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

namespace Cor713

section Even

variable {G : Type} [Group G] [Finite G]

theorem mem_of_even_orderOf {Y : Subgroup G} (hY : IsStronglyEmbedded Y) {y g : G} (hyY : y ∈ Y)
    (hev : Even (orderOf y)) (hg : g⁻¹ * y * g ∈ Y) : g ∈ Y := by
  by_contra hgY
  have hpos : 0 < orderOf y := orderOf_pos y
  have hdvd : 2 ∣ orderOf y := even_iff_two_dvd.mp hev
  set y' := y ^ (orderOf y / 2) with hy'
  have hy'2 : orderOf y' = 2 := orderOf_pow_orderOf_div hpos.ne' hdvd
  have hy'Y : y' ∈ Y := Y.pow_mem hyY _
  have hy'g : g⁻¹ * y' * g ∈ Y := by
    have : g⁻¹ * y' * g = (g⁻¹ * y * g) ^ (orderOf y / 2) := by
      have h := conj_pow (a := g⁻¹) (b := y) (i := orderOf y / 2)
      rw [hy']
      simpa using h.symm
    rw [this]
    exact Y.pow_mem hg _
  have hginv : g⁻¹ ∉ Y := fun h => hgY (by simpa using Y.inv_mem h)
  have hodd := hY.2.2 g⁻¹ hginv
  have hmem : y' ∈ Y ⊓ conjugate Y g⁻¹ := by
    refine Subgroup.mem_inf.mpr ⟨hy'Y, mem_conjugate_iff.mpr ?_⟩
    simpa using hy'g
  exact (Nat.not_even_iff_odd.mpr hodd) (Simple.even_card_of_mem_orderOf_eq_two hmem hy'2)

end Even

section Odd

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem mem_of_odd_orderOf (S : ZDSetup X Z M) (hT4b : Theorem4bStmt Z M) {u : X} (huZ : u ∈ Z)
    (huM : u ∈ M) {y g : X} (hyM : y ∈ M) (hy1 : y ≠ 1) (hodd : Odd (orderOf y))
    (huy : u * y * u⁻¹ = y⁻¹) (hg : g⁻¹ * y * g ∈ M) : g ∈ M := by
  have huu : u * u = 1 := S.invariant.mul_self_eq_one huZ
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right huu
  have hyW : y ∈ zpowers y := Subgroup.mem_zpowers y
  have hWodd : Odd (Nat.card (zpowers y)) := by rwa [Nat.card_zpowers]
  have hWM : zpowers y ≤ M := Subgroup.zpowers_le.mpr hyM
  have huN : u ∈ normalizer ((zpowers y : Subgroup X) : Set X) := by
    refine mem_normalizer_zpowers_of_conj_mem ?_ ?_
    · rw [huy]
      exact Subgroup.inv_mem _ hyW
    · have huy' : u * y * u = y⁻¹ := by
        have h := huy
        rwa [hui] at h
      rw [hui, huy']
      exact Subgroup.inv_mem _ hyW
  rcases hT4b u huZ huM (zpowers y) hWodd hWM huN with hcomm | hone
  · exfalso
    have h1 : u * y = y * u := hcomm y hyW
    have h2 : y = y⁻¹ := by
      rw [← huy, hui]
      calc y = (y * u) * u := by rw [mul_assoc, huu, mul_one]
        _ = u * y * u := by rw [h1]
    have h3 : y * y = 1 := by
      calc y * y = y * y⁻¹ := by rw [← h2]
        _ = 1 := mul_inv_cancel y
    have h4 : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h3)
    have h5 : orderOf y = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp h4 with h | h
      · exact h
      · rw [h] at hodd
        exact absurd hodd (by decide)
    exact hy1 (orderOf_eq_one_iff.mp h5)
  · have hβ : conjugate M g⁻¹ ∈ omega M := ⟨g⁻¹, rfl⟩
    have hWβ : zpowers y ≤ conjugate M g⁻¹ := by
      refine Subgroup.zpowers_le.mpr (mem_conjugate_iff.mpr ?_)
      simpa using hg
    have hmem : conjugate M g⁻¹ ∈ omegaFix M ((zpowers y : Subgroup X) : Set X) :=
      S.prodDisc.mem_omegaFix_iff.mpr ⟨hβ, hWβ⟩
    have hβM := hone _ hmem
    have := conjugate_eq_iff_mem_normalizer.mp hβM
    rw [S.prodDisc.normalizer_eq_self] at this
    simpa using M.inv_mem this

end Odd

end Cor713

section Solvable

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem ZDSetup.cor713_solvable
    (S : ZDSetup X Z M) (hT4b : Theorem4bStmt Z M) {F : Subgroup X}
    (hF : F ≠ ⊤) (hFM : ¬ F ≤ M) (hne : (Z ∩ ((F ⊓ M : Subgroup X) : Set X)).Nonempty)
    (hsolv : Group.IsSolvable ↥(zHull Z F)) :
    ∃ u ∈ Z, Z ∩ ((F ⊓ M : Subgroup X) : Set X) = {u} ∧
      F ⊓ M = F ⊓ centralizer ({u} : Set X) := by
  have hSE := S.cor713_isStronglyEmbedded_zHull hF hFM hne
  obtain ⟨u, huZ, huFM⟩ := hne
  have huF : u ∈ F := (Subgroup.mem_inf.mp huFM).1
  have huM : u ∈ M := (Subgroup.mem_inf.mp huFM).2
  have huL : u ∈ zHull Z F := Cor713.mem_zHull_of_mem huZ huF
  have hu2 : orderOf u = 2 := S.invariant.1 u huZ
  set L := zHull Z F with hL
  set Y : Subgroup ↥L := (M ⊓ L).subgroupOf L with hY
  have hmemY : ∀ y : ↥L, y ∈ Y ↔ (y : X) ∈ M := fun y => by
    rw [hY, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.1, fun h => ⟨h, y.2⟩⟩
  let uL : ↥L := ⟨u, huL⟩
  have huY : uL ∈ Y := (hmemY uL).mpr huM
  have huL2 : orderOf uL = 2 := by rw [Subgroup.orderOf_mk]; exact hu2
  have hfixed : ∀ y ∈ Y, y ≠ 1 → uL * y * uL⁻¹ = y⁻¹ → ∃! ω : ↥L ⧸ Y, y • ω = ω := by
    intro y hyY hy1 huy
    have hyM : (y : X) ∈ M := (hmemY y).mp hyY
    have hy1X : (y : X) ≠ 1 := fun h => hy1 (Subtype.ext h)
    have huyX : u * (y : X) * u⁻¹ = (y : X)⁻¹ := by
      have := congrArg Subtype.val huy
      simpa using this
    refine ⟨QuotientGroup.mk 1, ?_, ?_⟩
    · show y • (QuotientGroup.mk 1 : ↥L ⧸ Y) = QuotientGroup.mk 1
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, QuotientGroup.eq]
      simpa using Y.inv_mem hyY
    · intro ω hω
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective ω
      have hω' : y • (QuotientGroup.mk g : ↥L ⧸ Y) = QuotientGroup.mk g := hω
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq] at hω'
      have hg : g⁻¹ * y * g ∈ Y := by
        have h := Y.inv_mem hω'
        have e : ((y * g)⁻¹ * g)⁻¹ = g⁻¹ * y * g := by group
        rwa [e] at h
      have hgY : g ∈ Y := by
        by_cases hev : Even (orderOf y)
        · exact Cor713.mem_of_even_orderOf hSE hyY hev hg
        · have hodd : Odd (orderOf y) := Nat.not_even_iff_odd.mp hev
          have hoddX : Odd (orderOf (y : X)) := by rwa [Subgroup.orderOf_coe]
          have hgM : (g : X)⁻¹ * (y : X) * (g : X) ∈ M := by
            have := (hmemY _).mp hg
            simpa using this
          exact (hmemY g).mpr (Cor713.mem_of_odd_orderOf S hT4b huZ huM hyM hy1X hoddX huyX hgM)
      rw [QuotientGroup.eq]
      simpa using Y.inv_mem hgY
  obtain ⟨hcent, huniq⟩ := lemma312 hsolv hSE huY huL2 hfixed
  have hZY : Z ∩ ((F ⊓ M : Subgroup X) : Set X) = {u} := by
    refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨huZ, huFM⟩, ?_⟩
    rintro y ⟨hyZ, hyFM⟩
    have hyF : y ∈ F := (Subgroup.mem_inf.mp hyFM).1
    have hyM : y ∈ M := (Subgroup.mem_inf.mp hyFM).2
    have hyL : y ∈ L := Cor713.mem_zHull_of_mem hyZ hyF
    have hyY : (⟨y, hyL⟩ : ↥L) ∈ Y := (hmemY _).mpr hyM
    have hy2 : orderOf (⟨y, hyL⟩ : ↥L) = 2 := by
      rw [Subgroup.orderOf_mk]; exact S.invariant.1 y hyZ
    exact congrArg Subtype.val (huniq _ hyY hy2)
  refine ⟨u, huZ, hZY, ?_⟩
  apply le_antisymm
  · intro x hx
    obtain ⟨hxF, hxM⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨hxF, ?_⟩
    have hyZ : x⁻¹ * u * x ∈ Z := S.invariant.2 u huZ x
    have hyF : x⁻¹ * u * x ∈ F := F.mul_mem (F.mul_mem (F.inv_mem hxF) huF) hxF
    have hyM : x⁻¹ * u * x ∈ M := M.mul_mem (M.mul_mem (M.inv_mem hxM) huM) hxM
    have hyu : x⁻¹ * u * x ∈ Z ∩ ((F ⊓ M : Subgroup X) : Set X) :=
      ⟨hyZ, Subgroup.mem_inf.mpr ⟨hyF, hyM⟩⟩
    rw [hZY] at hyu
    have h1 : x⁻¹ * u * x = u := hyu
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x * u = x * (x⁻¹ * u * x) := by rw [h1]
      _ = u * x := by group
  · intro x hx
    obtain ⟨hxF, hxC⟩ := Subgroup.mem_inf.mp hx
    exact Subgroup.mem_inf.mpr ⟨hxF, S.prodDisc.centralizer_le_of_mem huZ huM hxC⟩

end Solvable

end CFSG.GH74.Uniqueness
