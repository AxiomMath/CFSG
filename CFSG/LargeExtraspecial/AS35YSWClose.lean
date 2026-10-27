module

public import CFSG.LargeExtraspecial.AS35YSWDec
public import CFSG.LargeExtraspecial.AS35YSWNine

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

namespace AS35YS

theorem card_le_two_mul {H : Type*} [Group H] [Finite H] {A B : Subgroup H}
    (h : ∀ x ∈ A, ∀ y ∈ A, x ∉ B → y ∉ B → x⁻¹ * y ∈ B) : Nat.card A ≤ 2 * Nat.card B := by
  by_cases hAB : ∀ x ∈ A, x ∈ B
  · have := Subgroup.card_le_of_le (show A ≤ B from hAB)
    omega
  push Not at hAB
  obtain ⟨x₀, hx₀A, hx₀B⟩ := hAB
  have hsub : (A : Set H) ⊆ (B : Set H) ∪ (fun b => x₀ * b) '' (B : Set H) := by
    intro a ha
    by_cases haB : a ∈ B
    · exact Or.inl haB
    · exact Or.inr ⟨x₀⁻¹ * a, h x₀ hx₀A a ha hx₀B haB, by simp⟩
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 := Set.ncard_union_le (B : Set H) ((fun b => x₀ * b) '' (B : Set H))
  have h3 : ((fun b => x₀ * b) '' (B : Set H)).ncard = (B : Set H).ncard :=
    Set.ncard_image_of_injective _ (mul_right_injective x₀)
  have hA : Nat.card A = (A : Set H).ncard := Nat.card_coe_set_eq _
  have hB : Nat.card B = (B : Set H).ncard := Nat.card_coe_set_eq _
  omega

end AS35YS

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

omit [Finite G] in
theorem inv_mul_commute_YS {g x x' y : G} (hx : x ∈ S.Qa g) (hx' : x' ∈ S.Qa g)
    (hy : y ∈ S.Qa g) (hxy : x * y ≠ y * x) (hx'y : x' * y ≠ y * x') :
    x⁻¹ * x' * y = y * (x⁻¹ * x') := by
  set τ := g * S.z * g⁻¹ with hτ
  have hττ : τ * τ = 1 := by
    rw [hτ, show g * S.z * g⁻¹ * (g * S.z * g⁻¹) = g * (S.z * S.z) * g⁻¹ by group, S.z_mul_z]
    group
  have hcomm : ∀ {w : G}, w ∈ S.Qa g → w * y ≠ y * w → w * y = τ * y * w := by
    intro w hw hwy
    rcases AS35T.commutator_eq_one_or_of_mem_Qa S hw hy with h | h
    · exact absurd (calc w * y = w * y * w⁻¹ * y⁻¹ * (y * w) := by group
        _ = y * w := by rw [h, one_mul]) hwy
    · calc w * y = w * y * w⁻¹ * y⁻¹ * y * w := by group
        _ = τ * y * w := by rw [h]
  have h1 := hcomm hx hxy
  have h2 := hcomm hx' hx'y
  have hτx : τ * x⁻¹ = x⁻¹ * τ := by
    have e := AS35T.commute_of_mem_Qa S ((S.Qa g).inv_mem hx)
    exact e.symm
  have h3 : y * x⁻¹ = τ * (x⁻¹ * y) := by
    calc y * x⁻¹ = x⁻¹ * (x * y) * x⁻¹ := by group
      _ = x⁻¹ * (τ * y * x) * x⁻¹ := by rw [h1]
      _ = (x⁻¹ * τ) * y := by group
      _ = (τ * x⁻¹) * y := by rw [hτx]
      _ = τ * (x⁻¹ * y) := by group
  have h4 : x⁻¹ * y = τ * y * x⁻¹ := by
    calc x⁻¹ * y = τ * τ * (x⁻¹ * y) := by rw [hττ, one_mul]
      _ = τ * (τ * (x⁻¹ * y)) := by group
      _ = τ * (y * x⁻¹) := by rw [← h3]
      _ = τ * y * x⁻¹ := by group
  calc x⁻¹ * x' * y = x⁻¹ * (x' * y) := by group
    _ = x⁻¹ * (τ * y * x') := by rw [h2]
    _ = (x⁻¹ * τ) * y * x' := by group
    _ = (τ * x⁻¹) * y * x' := by rw [hτx]
    _ = τ * (x⁻¹ * y) * x' := by group
    _ = τ * (τ * y * x⁻¹) * x' := by rw [h4]
    _ = (τ * τ) * y * (x⁻¹ * x') := by group
    _ = y * (x⁻¹ * x') := by rw [hττ, one_mul]

theorem commute_of_fiveNine_YS (hS : S.SixHyp) {g : G} (ht : g * S.z * g⁻¹ ∈ S.DSet)
    {y d : G} (hyQt : y ∈ S.Qa g)
    (h59 : ∀ c : G, c * y = y * c → c * S.z * c⁻¹ = S.z ∨ c * S.z * c⁻¹ = d) :
    ∀ p ∈ S.Qa g ⊓ S.M, p * y = y * p := by
  have htM := S.mem_M_of_mem_ESet hS.sixFour ht.1
  set A : Subgroup G := S.Qa g ⊓ centralizer ({y} : Set G) with hA
  set B : Subgroup G := A ⊓ S.M with hB
  have h1 : Nat.card (S.Qa g) ≤ 2 * Nat.card A := by
    refine AS35YS.card_le_two_mul fun x hx x' hx' hxA hx'A => ?_
    have hxy : x * y ≠ y * x := fun h => hxA (mem_inf.mpr ⟨hx, mem_centralizer_singleton_iff.mpr h⟩)
    have hx'y : x' * y ≠ y * x' := fun h =>
      hx'A (mem_inf.mpr ⟨hx', mem_centralizer_singleton_iff.mpr h⟩)
    exact mem_inf.mpr ⟨(S.Qa g).mul_mem ((S.Qa g).inv_mem hx) hx',
      mem_centralizer_singleton_iff.mpr (inv_mul_commute_YS hx hx' hyQt hxy hx'y)⟩
  have h2 : Nat.card A ≤ 2 * Nat.card B := by
    refine AS35YS.card_le_two_mul fun a ha a' ha' haB ha'B => ?_
    have hconj : ∀ {w : G}, w ∈ A → w ∉ B → w * S.z * w⁻¹ = d := by
      intro w hw hwB
      rcases h59 w (mem_centralizer_singleton_iff.mp (mem_inf.mp hw).2) with h | h
      · exact absurd (mem_inf.mpr ⟨hw, S.mem_M_of_conj_eq_z h⟩) hwB
      · exact h
    have e1 := hconj ha haB
    have e2 := hconj ha' ha'B
    refine mem_inf.mpr ⟨A.mul_mem (A.inv_mem ha) ha', S.mem_M_of_conj_eq_z ?_⟩
    calc a⁻¹ * a' * S.z * (a⁻¹ * a')⁻¹ = a⁻¹ * (a' * S.z * a'⁻¹) * a := by group
      _ = a⁻¹ * (a * S.z * a⁻¹) * a := by rw [e2, e1]
      _ = S.z := by group
  have h3 : Nat.card (S.Qa g) = 4 * Nat.card (S.Qa g ⊓ S.M : Subgroup G) := by
    rw [S.card_Qa, AS35T.card_Qa_inf_M_eq hS ht]
    exact (S.fiveOne_two hS.sixFour hS.weak ht htM).2.1
  have hBP : B ≤ S.Qa g ⊓ S.M := fun x hx =>
    mem_inf.mpr ⟨(mem_inf.mp (mem_inf.mp hx).1).1, (mem_inf.mp hx).2⟩
  have hPB : B = S.Qa g ⊓ S.M := Subgroup.eq_of_le_of_card_ge hBP (by omega)
  intro p hp
  rw [← hPB] at hp
  exact mem_centralizer_singleton_iff.mp (mem_inf.mp (mem_inf.mp hp).1).2

theorem false_of_dbar_mem_pbar_YS (hS : S.SixHyp) {g : G} (ht : g * S.z * g⁻¹ ∈ S.DSet)
    (htM : g * S.z * g⁻¹ ∈ S.M) {b : G} (hb : b ∈ S.DSet) (hbM : b ∈ S.M)
    (hbP : S.ρ ⟨b, hbM⟩ ∈ S.PbarAsc g) (hbt : S.ρ ⟨b, hbM⟩ ≠ S.ρ ⟨_, htM⟩)
    (hR : ∀ U : Subgroup S.O, U ≤ S.Mbar → (∀ u ∈ U, u * u = 1) → S.ρ ⟨b, hbM⟩ ∈ U →
      (∀ c ∈ S.Mbar, c * S.ρ ⟨b, hbM⟩ = S.ρ ⟨b, hbM⟩ * c → ∀ u ∈ U, c * u * c⁻¹ ∈ U) →
        U ≤ zpowers (S.ρ ⟨b, hbM⟩)) : False := by
  obtain ⟨y, hy, d, hd, hdM, hdb, hyd⟩ := exists_mem_pbar_decomp_YS hS ht htM hb hbM hbP
  obtain ⟨hyQt, hyM⟩ := mem_inf.mp hy
  have hbQ : S.ρ ⟨b, hbM⟩ ≠ 1 := fun h =>
    S.not_mem_QG_of_mem_ESet hS.weak hb.1 ((S.ρ_eq_one_iff _).mp h)
  rcases hyd with hyd | hyd
  ·
    obtain ⟨k, hk⟩ := isConj_iff.mp (S.isConj_of_mem_ESet hd.1)
    have hkQ : k * S.z * k⁻¹ ∈ S.Qa g := by rw [hk, ← hyd]; exact hyQt
    have hkt := AS35T.conj_eq_of_conj_mem_Qa S hS.weak hkQ
    apply hbt
    rw [← hdb]
    congr 1
    exact Subtype.ext (hk.symm.trans hkt)
  ·
    have hR' : ∀ U : Subgroup S.O, U ≤ S.Mbar → (∀ u ∈ U, u * u = 1) → S.ρ ⟨d, hdM⟩ ∈ U →
        (∀ c ∈ S.Mbar, c * S.ρ ⟨d, hdM⟩ = S.ρ ⟨d, hdM⟩ * c → ∀ u ∈ U, c * u * c⁻¹ ∈ U) →
          U ≤ zpowers (S.ρ ⟨d, hdM⟩) := by
      rw [hdb]
      exact hR
    have h59 : ∀ c : G, c * y = y * c → c * S.z * c⁻¹ = S.z ∨ c * S.z * c⁻¹ = d := by
      intro c hc
      rw [hyd] at hc
      exact S.fiveNineTwo_YS hS hd hdM hR' hc
    have hcomm := commute_of_fiveNine_YS hS ht hyQt h59
    have hσ : S.ρ ⟨y, hyM⟩ ∈ S.PbarAsc g := (AS35T.mem_pbar_iff S).mpr ⟨⟨y, hyM⟩, hyQt, rfl⟩
    have hc : ∀ τ ∈ S.PbarAsc g, S.ρ ⟨y, hyM⟩ * τ = τ * S.ρ ⟨y, hyM⟩ := by
      intro τ hτ
      obtain ⟨⟨p, hpM⟩, hpQt, rfl⟩ := (AS35T.mem_pbar_iff S).mp hτ
      have e := hcomm p (mem_inf.mpr ⟨hpQt, hpM⟩)
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext e.symm
    have hρy : S.ρ ⟨y, hyM⟩ = S.ρ ⟨b, hbM⟩ := by
      have e : (⟨y, hyM⟩ : S.M) = ⟨S.z, S.z_mem_M⟩ * ⟨d, hdM⟩ := Subtype.ext hyd
      rw [e, map_mul, (S.ρ_eq_one_iff _).mpr S.z_mem_QG, one_mul, hdb]
    rcases AS35T.eq_one_or_of_commute_pbar hS ht htM hσ hc with h | h
    · exact hbQ (hρy ▸ h)
    · exact hbt (hρy ▸ h)

end Setting

end CFSG.LargeExtraspecial
