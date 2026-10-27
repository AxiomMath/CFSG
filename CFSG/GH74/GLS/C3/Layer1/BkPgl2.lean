module

public import CFSG.GH74.GLS.C3.Layer1.BkPgl0
public import CFSG.GH74.GLS.C3.Layer1.BkPgl1
public import CFSG.GH74.GLS.C3.Layer1.BackAction
public import CFSG.GH74.GLS.C3.Layer1.BackBasic

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1.Back
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_sup_zpowers_two {L : Subgroup G} {y x : G} (hy2 : orderOf y = 2)
    (hyN : y ∈ normalizer (L : Set G)) :
    x ∈ L ⊔ zpowers y ↔ x ∈ L ∨ ∃ l ∈ L, x = l * y := by
  have hZN : zpowers y ≤ normalizer (L : Set G) := zpowers_le.mpr hyN
  constructor
  · intro hx
    have hx' : x ∈ ((L ⊔ zpowers y : Subgroup G) : Set G) := hx
    rw [Subgroup.coe_mul_of_right_le_normalizer_left L (zpowers y) hZN] at hx'
    obtain ⟨l, hl, c, hc, hlc⟩ := hx'
    have hlc' : l * c = x := hlc
    rcases mem_zpowers_two hy2 hc with h | h
    · left
      rw [← hlc', h, mul_one]
      exact hl
    · right
      exact ⟨l, hl, by rw [← hlc', h]⟩
  · rintro (hx | ⟨l, hl, rfl⟩)
    · exact Subgroup.mem_sup_left hx
    · exact (L ⊔ zpowers y).mul_mem (Subgroup.mem_sup_left hl)
        (Subgroup.mem_sup_right (mem_zpowers y))

omit [Finite G] in
theorem X_inf_CMK_le {L M : Subgroup G} {y : G} (hLn : ∀ m ∈ M, ∀ l ∈ L, m * l * m⁻¹ ∈ L)
    (hyM : y ∈ M) (hy2 : orderOf y = 2) (hs : IsSimpleGroup (kBar L))
    (hn : ∃ a b : kBar L, a * b ≠ b * a)
    (hnot : Back.actHom hLn ⟨y, hyM⟩ ∉ (MulAut.conj : kBar L →* MulAut (kBar L)).range) :
    (L ⊔ zpowers y) ⊓ CMK M L ≤ pPrimeCoreOf 2 L := by
  rintro w ⟨hwX, hwC⟩
  have hyNL : y ∈ normalizer (L : Set G) := U1a.mem_normalizer_of_norm hLn hyM
  rcases (mem_sup_zpowers_two hy2 hyNL).1 hwX with hwL | ⟨l, hl, rfl⟩
  · exact Setup91.inf_CMK_le hs hn ⟨hwL, hwC⟩
  · exfalso
    apply hnot
    have hwM : l * y ∈ M := (U1a.mem_CMK_iff.1 hwC).1
    have hlM : l ∈ M := by
      have := M.mul_mem hwM (M.inv_mem hyM)
      simpa using this
    have hker : Back.actHom hLn ⟨l * y, hwM⟩ = 1 := by
      rw [← MonoidHom.mem_ker, Back.actHom_ker hLn, Subgroup.mem_subgroupOf]
      exact hwC
    have hsplit : (⟨l * y, hwM⟩ : ↥M) = ⟨l, hlM⟩ * ⟨y, hyM⟩ := rfl
    rw [hsplit, map_mul, Back.actHom_of_mem hLn hl hlM] at hker
    have h2 : Back.actHom hLn ⟨y, hyM⟩ =
        (MulAut.conj (QuotientGroup.mk (⟨l, hl⟩ : ↥L) : kBar L))⁻¹ :=
      eq_inv_of_mul_eq_one_right hker
    rw [h2, ← map_inv]
    exact MonoidHom.mem_range.2 ⟨_, rfl⟩

theorem exists_lift_commute {L M : Subgroup G} {y v z₀ : G} (hLM : L ≤ M)
    (hLn : ∀ m ∈ M, ∀ l ∈ L, m * l * m⁻¹ ∈ L) (hyM : y ∈ M) (hy2 : orderOf y = 2)
    (hs : IsSimpleGroup (kBar L)) (hn : ∃ a b : kBar L, a * b ≠ b * a)
    (hnot : Back.actHom hLn ⟨y, hyM⟩ ∉ (MulAut.conj : kBar L →* MulAut (kBar L)).range)
    (hvM : v ∈ M) (hv2 : orderOf v = 2)
    (hvX : ∀ k ∈ L ⊔ zpowers y, v * k * v⁻¹ ∈ L ⊔ zpowers y)
    (hz₀ : z₀ ∈ L ⊔ zpowers y) (hz₀M : z₀ ∈ M)
    (hcomm : Back.actHom hLn ⟨z₀, hz₀M⟩ * Back.actHom hLn ⟨v, hvM⟩ =
      Back.actHom hLn ⟨v, hvM⟩ * Back.actHom hLn ⟨z₀, hz₀M⟩) :
    ∃ z ∈ L ⊔ zpowers y, ∃ hzM : z ∈ M, z * v = v * z ∧
      Back.actHom hLn ⟨z, hzM⟩ = Back.actHom hLn ⟨z₀, hz₀M⟩ := by
  set X : Subgroup G := L ⊔ zpowers y with hX
  have hXM : X ≤ M := sup_le hLM (zpowers_le.mpr hyM)
  have hNX : pPrimeCoreOf 2 L ≤ X := (TwoThin.pPrimeCoreOf_le L).trans le_sup_left
  have hQ2 : IsPGroup 2 ↥(zpowers v) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hv2, pow_one])
  have hQX : ∀ q ∈ zpowers v, ∀ k ∈ X, q * k * q⁻¹ ∈ X := by
    intro q hq k hk
    rcases mem_zpowers_two hv2 hq with h | h
    · rw [h]
      simpa using hk
    · rw [h]
      exact hvX k hk
  have hQN : ∀ q ∈ zpowers v, ∀ n ∈ pPrimeCoreOf 2 L, q * n * q⁻¹ ∈ pPrimeCoreOf 2 L := by
    intro q hq n hn'
    rcases mem_zpowers_two hv2 hq with h | h
    · rw [h]
      simpa using hn'
    · rw [h]
      exact (mem_normalizer_iff.1 (U1a.mem_normalizer_pPrimeCoreOf hLn hvM) n).1 hn'
  have hQt : ∀ q ∈ zpowers v, z₀⁻¹ * (q * z₀ * q⁻¹) ∈ pPrimeCoreOf 2 L := by
    intro q hq
    rcases mem_zpowers_two hv2 hq with h | h
    · rw [h]
      simp
    · rw [h]
      have hwX : z₀⁻¹ * (v * z₀ * v⁻¹) ∈ X := X.mul_mem (X.inv_mem hz₀) (hvX z₀ hz₀)
      have hwM : z₀⁻¹ * (v * z₀ * v⁻¹) ∈ M :=
        M.mul_mem (M.inv_mem hz₀M) (M.mul_mem (M.mul_mem hvM hz₀M) (M.inv_mem hvM))
      have hρ : Back.actHom hLn ⟨z₀⁻¹ * (v * z₀ * v⁻¹), hwM⟩ = 1 := by
        have e : (⟨z₀⁻¹ * (v * z₀ * v⁻¹), hwM⟩ : ↥M) =
            ⟨z₀, hz₀M⟩⁻¹ * (⟨v, hvM⟩ * ⟨z₀, hz₀M⟩ * ⟨v, hvM⟩⁻¹) := rfl
        rw [e, map_mul, map_inv, map_mul, map_mul, map_inv]
        have e2 : Back.actHom hLn ⟨v, hvM⟩ * Back.actHom hLn ⟨z₀, hz₀M⟩ *
            (Back.actHom hLn ⟨v, hvM⟩)⁻¹ = Back.actHom hLn ⟨z₀, hz₀M⟩ := by
          rw [← hcomm]
          group
        rw [e2, inv_mul_cancel]
      have hwCMK : z₀⁻¹ * (v * z₀ * v⁻¹) ∈ CMK M L := by
        have h1 : (⟨z₀⁻¹ * (v * z₀ * v⁻¹), hwM⟩ : ↥M) ∈ (Back.actHom hLn).ker := hρ
        rw [Back.actHom_ker hLn, Subgroup.mem_subgroupOf] at h1
        exact h1
      exact X_inf_CMK_le hLn hyM hy2 hs hn hnot ⟨hwX, hwCMK⟩
  obtain ⟨z, hzX, hzQ, hzO⟩ :=
    exists_fixed_mem_coset_of_normal hQ2 (TwoThin.card_pPrimeCoreOf_odd L) hNX hQX hQN hz₀ hQt
  have hzM : z ∈ M := hXM hzX
  refine ⟨z, hzX, hzM, hzQ v (mem_zpowers v), ?_⟩
  have hoL : z₀⁻¹ * z ∈ L := TwoThin.pPrimeCoreOf_le L hzO
  have hoM : z₀⁻¹ * z ∈ M := hLM hoL
  have hρo : Back.actHom hLn ⟨z₀⁻¹ * z, hoM⟩ = 1 := by
    rw [Back.actHom_of_mem hLn hoL hoM]
    have h1 : (QuotientGroup.mk (⟨z₀⁻¹ * z, hoL⟩ : ↥L) : kBar L) = 1 :=
      (QuotientGroup.eq_one_iff _).2 (Back.Setup91.mem_pPrimeCoreOf_iff.1 hzO).2
    rw [h1, map_one]
  have hsplit : (⟨z, hzM⟩ : ↥M) = ⟨z₀, hz₀M⟩ * ⟨z₀⁻¹ * z, hoM⟩ := Subtype.ext (by simp)
  rw [hsplit, map_mul, hρo, mul_one]

end CFSG.GH74.GLS.C3.Layer1.Bk
