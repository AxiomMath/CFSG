module

public import CFSG.ClassicalInvolution.Q3.WeakBalance
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.Q3.Q3C

open CFSG.Open CFSG.Assembly.Dichotomy CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
open scoped commutatorElement

section OddCore

variable {G : Type} [Group G] [Finite G]

theorem conj_mem_oddCoreIn_of_normalizes {H : Subgroup G} {c : G}
    (hc : ∀ h ∈ H, c * h * c⁻¹ ∈ H) (hc' : ∀ h ∈ H, c⁻¹ * h * c ∈ H) {y : G}
    (hy : y ∈ oddCoreIn H) : c * y * c⁻¹ ∈ oddCoreIn H := by
  set S : Subgroup G := (oddCoreIn H).map (MulAut.conj c).toMonoidHom with hS
  have hSH : S ≤ H := by
    rintro _ ⟨u, hu, rfl⟩
    exact hc u (oddCoreIn_le H hu)
  have hSodd : Odd (Nat.card S) := by
    rw [hS, Subgroup.card_map_of_injective (MulAut.conj c).injective]
    exact odd_card_oddCoreIn H
  have hSn : ∀ h ∈ H, ∀ s ∈ S, h * s * h⁻¹ ∈ S := by
    intro h hh s hs
    obtain ⟨u, hu, rfl⟩ := hs
    refine ⟨(c⁻¹ * h * c) * u * (c⁻¹ * h * c)⁻¹, conj_mem_oddCoreIn (hc' h hh) hu, ?_⟩
    show c * ((c⁻¹ * h * c) * u * (c⁻¹ * h * c)⁻¹) * c⁻¹ = h * (c * u * c⁻¹) * h⁻¹
    group
  have hnorm : H ≤ Subgroup.normalizer (S : Set G) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro s
    refine ⟨fun hs => hSn h hh s hs, fun hs => ?_⟩
    have := hSn h⁻¹ (H.inv_mem hh) _ hs
    simpa [mul_assoc] using this
  have hle : S ≤ oddCoreIn H := le_oddCoreIn_of_normalizes hSH hnorm hSodd
  exact hle ⟨y, hy, rfl⟩

theorem oddCoreIn_le_involutionOddCore {H : Subgroup G} {b : G}
    (hHb : H ≤ Subgroup.centralizer ({b} : Set G))
    (hHn : ∀ c ∈ Subgroup.centralizer ({b} : Set G), ∀ h ∈ H, c * h * c⁻¹ ∈ H) :
    oddCoreIn H ≤ involutionOddCore b := by
  have hnorm : Subgroup.centralizer ({b} : Set G) ≤ Subgroup.normalizer (oddCoreIn H : Set G) := by
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hc1 : ∀ h ∈ H, c⁻¹ * h * c ∈ H := fun h hh => by
      simpa using hHn c⁻¹ ((Subgroup.centralizer ({b} : Set G)).inv_mem hc) h hh
    have hc2 : ∀ h ∈ H, c⁻¹⁻¹ * h * c⁻¹ ∈ H := fun h hh => by
      simpa using hHn c hc h hh
    refine ⟨fun hy => conj_mem_oddCoreIn_of_normalizes (hHn c hc) hc1 hy, fun hy => ?_⟩
    have := conj_mem_oddCoreIn_of_normalizes (H := H) (c := c⁻¹)
      (fun h hh => by simpa using hc1 h hh) hc2 hy
    simpa [mul_assoc] using this
  exact le_oddCoreIn_of_normalizes ((oddCoreIn_le H).trans hHb) hnorm (odd_card_oddCoreIn H)

end OddCore

section Datum

variable {G : Type} [Group G]

@[expose] def HasLieSystem3 (H : Subgroup G) : Prop :=
  ∃ Γ : Set (Subgroup ↥H), LieSystemMod3 Γ

@[expose] def SBaseDatum (A : Subgroup G) (b : G) : Prop :=
  ∃ H : Subgroup G, H ≤ Subgroup.centralizer ({b} : Set G) ∧
    (∀ c ∈ Subgroup.centralizer ({b} : Set G), ∀ h ∈ H, c * h * c⁻¹ ∈ H) ∧
    (∀ x ∈ A, x ∈ H ∨ x * b ∈ H) ∧
    (∀ X : Subgroup G, X ≤ Subgroup.centralizer ({b} : Set G) → Odd (Nat.card X) → X ≤ H) ∧
    HasLieSystem3 H

end Datum

section KeyLemma

variable {G : Type} [Group G] [Finite G]

theorem involutionOddCore_inf_le_oddCoreIn (hMF : LieSystemOddCentralizer3) {H : Subgroup G}
    (hH : HasLieSystem3 H) {x x' : G} (hx'H : x' ∈ H) (hx'2 : orderOf x' = 2)
    (hxx' : ∀ h ∈ H, x * h = h * x ↔ x' * h = h * x') :
    involutionOddCore x ⊓ H ≤ oddCoreIn H := by
  obtain ⟨Γ, hΓ⟩ := hH
  have h1 := hMF ↥H Γ hΓ ⟨x', hx'H⟩ (by rw [Subgroup.orderOf_mk]; exact hx'2)
  have h2 := Subgroup.map_mono (f := H.subtype) h1
  rw [map_oddCoreIn_subtype, map_centralizer_subtype hx'H] at h2
  have hO : oddCoreIn (H ⊓ Subgroup.centralizer ({x'} : Set G)) ≤ oddCoreIn H := h2
  set Y : Subgroup G := involutionOddCore x ⊓ H with hY
  have hCx : ∀ h ∈ H, x' * h = h * x' → h ∈ Subgroup.centralizer ({x} : Set G) := fun h hh he =>
    Subgroup.mem_centralizer_singleton_iff.mpr ((hxx' h hh).mpr he).symm
  have hYU : Y ≤ H ⊓ Subgroup.centralizer ({x'} : Set G) := by
    intro y hy
    refine ⟨hy.2, Subgroup.mem_centralizer_singleton_iff.mpr ((hxx' y hy.2).mp ?_).symm⟩
    exact (Subgroup.mem_centralizer_singleton_iff.mp (involutionOddCore_le_centralizer x hy.1)).symm
  have hYn : ∀ u ∈ H ⊓ Subgroup.centralizer ({x'} : Set G), ∀ y ∈ Y, u * y * u⁻¹ ∈ Y := by
    intro u hu y hy
    have huC : u ∈ Subgroup.centralizer ({x} : Set G) :=
      hCx u hu.1 (Subgroup.mem_centralizer_singleton_iff.mp hu.2).symm
    exact ⟨conj_mem_oddCoreIn huC hy.1,
      H.mul_mem (H.mul_mem hu.1 hy.2) (H.inv_mem hu.1)⟩
  have hnorm : (H ⊓ Subgroup.centralizer ({x'} : Set G)) ≤ Subgroup.normalizer (Y : Set G) := by
    intro u hu
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => hYn u hu y hy, fun hy => ?_⟩
    have := hYn u⁻¹ ((H ⊓ Subgroup.centralizer ({x'} : Set G)).inv_mem hu) _ hy
    simpa [mul_assoc] using this
  have hodd : Odd (Nat.card Y) :=
    Odd.of_dvd_nat (odd_card_oddCoreIn (Subgroup.centralizer ({x} : Set G)))
      (Subgroup.card_dvd_of_le inf_le_left)
  exact (le_oddCoreIn_of_normalizes hYU hnorm hodd).trans hO

end KeyLemma

section Balance

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem elem_comm {A : Subgroup G} (hA : IsElemAbelian 2 A) {x y : G} (hx : x ∈ A) (hy : y ∈ A) :
    x * y = y * x := CFSG.Open.IsElemAbelian.comm hA hx hy

omit [Finite G] in
theorem elem_sq {A : Subgroup G} (hA : IsElemAbelian 2 A) {x : G} (hx : x ∈ A) : x * x = 1 :=
  CFSG.Open.IsElemAbelian.mul_self_eq_one hA hx

omit [Finite G] in
theorem exists_involution_of_datum {A : Subgroup G} (hA : IsElemAbelian 2 A) {b : G} (hbA : b ∈ A)
    {H : Subgroup G} (hHb : H ≤ Subgroup.centralizer ({b} : Set G))
    (hAH : ∀ x ∈ A, x ∈ H ∨ x * b ∈ H) {x : G} (hxA : x ∈ A) (hx1 : x ≠ 1) (hxb : x ≠ b) :
    ∃ x' ∈ H, orderOf x' = 2 ∧ ∀ h ∈ H, (x * h = h * x ↔ x' * h = h * x') := by
  rcases hAH x hxA with h | h
  · exact ⟨x, h, orderOf_eq_prime (by rw [pow_two]; exact elem_sq hA hxA) hx1,
      fun _ _ => Iff.rfl⟩
  · refine ⟨x * b, h, ?_, ?_⟩
    · refine orderOf_eq_prime ?_ ?_
      · rw [pow_two]
        have hba : b * x = x * b := elem_comm hA hbA hxA
        calc x * b * (x * b) = x * (b * x) * b := by group
          _ = x * (x * b) * b := by rw [hba]
          _ = (x * x) * (b * b) := by group
          _ = 1 := by rw [elem_sq hA hxA, elem_sq hA hbA, one_mul]
      · intro h1
        apply hxb
        have : x = b⁻¹ := eq_inv_of_mul_eq_one_left h1
        rw [this]
        exact inv_eq_of_mul_eq_one_right (elem_sq hA hbA)
    · intro h' hh
      have hbh : h' * b = b * h' := Subgroup.mem_centralizer_singleton_iff.mp (hHb hh)
      constructor
      · intro hxh
        calc x * b * h' = x * (b * h') := by group
          _ = x * (h' * b) := by rw [hbh]
          _ = (x * h') * b := by group
          _ = (h' * x) * b := by rw [hxh]
          _ = h' * (x * b) := by group
      · intro hxh
        have : x * h' * b = h' * x * b := by
          calc x * h' * b = x * (h' * b) := by group
            _ = x * (b * h') := by rw [hbh]
            _ = x * b * h' := by group
            _ = h' * (x * b) := hxh
            _ = h' * x * b := by group
        exact mul_right_cancel this

theorem weakBalance_at_of_datum (hMF : LieSystemOddCentralizer3) {A : Subgroup G}
    (hA : IsElemAbelian 2 A) {b : G} (hbA : b ∈ A) (hd : SBaseDatum A b) :
    ∀ a ∈ A, a ≠ 1 → ⁅involutionOddCore a ⊓ Subgroup.centralizer ({b} : Set G), A⁆ ≤
      involutionOddCore b := by
  obtain ⟨H, hHb, hHn, hAH, -, hLie⟩ := hd
  have hOH : oddCoreIn H ≤ involutionOddCore b := oddCoreIn_le_involutionOddCore hHb hHn
  intro a ha ha1
  rw [Subgroup.commutator_le]
  intro r hr g hg
  have hrb : r ∈ Subgroup.centralizer ({b} : Set G) := hr.2
  by_cases hab : a = b
  · rw [hab] at hr
    have hgC : g ∈ Subgroup.centralizer ({b} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (elem_comm hA hg hbA)
    have : ⁅r, g⁆ = r * (g * r⁻¹ * g⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [this]
    exact (involutionOddCore b).mul_mem hr.1
      (conj_mem_oddCoreIn hgC ((involutionOddCore b).inv_mem hr.1))
  · obtain ⟨g₀, hg₀H, hg₀A, hg₀⟩ : ∃ g₀ ∈ H, g₀ ∈ A ∧ ⁅r, g⁆ = ⁅r, g₀⁆ := by
      rcases hAH g hg with h | h
      · exact ⟨g, h, hg, rfl⟩
      · refine ⟨g * b, h, A.mul_mem hg hbA, ?_⟩
        have hrb' : Commute r b := Subgroup.mem_centralizer_singleton_iff.mp hrb
        have e : b * r⁻¹ * b⁻¹ = r⁻¹ := by
          rw [(hrb'.inv_left.symm).eq, mul_inv_cancel_right]
        simp only [commutatorElement_def]
        calc r * g * r⁻¹ * g⁻¹ = r * g * (b * r⁻¹ * b⁻¹) * g⁻¹ := by rw [e]
          _ = r * (g * b) * r⁻¹ * (g * b)⁻¹ := by group
    rw [hg₀]
    obtain ⟨a', ha'H, ha'2, hxx'⟩ := exists_involution_of_datum hA hbA hHb hAH ha ha1 hab
    have hg₀a : g₀ ∈ Subgroup.centralizer ({a} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (elem_comm hA hg₀A ha)
    have hrg : ⁅r, g₀⁆ ∈ involutionOddCore a ⊓ H := by
      refine ⟨?_, ?_⟩
      · have : ⁅r, g₀⁆ = r * (g₀ * r⁻¹ * g₀⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [this]
        exact (involutionOddCore a).mul_mem hr.1
          (conj_mem_oddCoreIn hg₀a ((involutionOddCore a).inv_mem hr.1))
      · have h1 : r * g₀ * r⁻¹ ∈ H := hHn r hrb g₀ hg₀H
        have : ⁅r, g₀⁆ = (r * g₀ * r⁻¹) * g₀⁻¹ := by simp only [commutatorElement_def]
        rw [this]
        exact H.mul_mem h1 (H.inv_mem hg₀H)
    exact hOH (involutionOddCore_inf_le_oddCoreIn hMF hLie ha'H ha'2 hxx' hrg)

theorem twoBalanced_at_of_datum (hMF : LieSystemOddCentralizer3) {A : Subgroup G}
    (hA : IsElemAbelian 2 A) {b : G} (hbA : b ∈ A) (hb1 : b ≠ 1) (hd : SBaseDatum A b)
    {F : Subgroup G} (hFA : F ≤ A) (hF4 : Nat.card F = 4) :
    deltaCore F ⊓ Subgroup.centralizer ({b} : Set G) ≤ involutionOddCore b := by
  obtain ⟨H, hHb, hHn, hAH, hodd, hLie⟩ := hd
  have hOH : oddCoreIn H ≤ involutionOddCore b := oddCoreIn_le_involutionOddCore hHb hHn
  by_cases hbF : b ∈ F
  · exact inf_le_left.trans (deltaCore_le_involutionOddCore hbF hb1)
  · obtain ⟨f, hfF, hf1⟩ := exists_ne_one_of_card_eq_two_pow (S := F) (n := 2) (by norm_num)
      (by rw [hF4]; norm_num)
    have hfb : f ≠ b := fun h => hbF (h ▸ hfF)
    have hΔf : deltaCore F ≤ involutionOddCore f := deltaCore_le_involutionOddCore hfF hf1
    have hXodd : Odd (Nat.card ↥(deltaCore F ⊓ Subgroup.centralizer ({b} : Set G))) :=
      Odd.of_dvd_nat (odd_card_oddCoreIn (Subgroup.centralizer ({f} : Set G)))
        (Subgroup.card_dvd_of_le (inf_le_left.trans hΔf))
    have hXH := hodd (deltaCore F ⊓ Subgroup.centralizer ({b} : Set G)) inf_le_right hXodd
    obtain ⟨f', hf'H, hf'2, hxx'⟩ :=
      exists_involution_of_datum hA hbA hHb hAH (hFA hfF) hf1 hfb
    intro x hx
    exact hOH (involutionOddCore_inf_le_oddCoreIn hMF hLie hf'H hf'2 hxx' ⟨hΔf hx.1, hXH hx⟩)

end Balance

end CFSG.ClassicalInvolution.Q3.Q3C
