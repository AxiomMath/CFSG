module

public import CFSG.LocalAnalysis.OddStandard.Solomon75StdPermLift
public import CFSG.LocalAnalysis.OddStandard.Solomon75LPlusDefs
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk5AnSL23

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS
open scoped commutatorElement

section AltFour

private theorem alt4M_a4_two_cubes : ∀ a : alternatingGroup (Fin 4),
    ∃ x y : alternatingGroup (Fin 4), x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ a = x * y := by
  decide +kernel

private theorem alt4M_a4_klein_mul : ∀ a b : alternatingGroup (Fin 4), a * a = 1 → b * b = 1 →
    (a * b) * (a * b) = 1 := by
  decide +kernel

private theorem alt4M_a4_two_involutions : ∃ a b : alternatingGroup (Fin 4), a * a = 1 ∧ b * b = 1 ∧
    a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
  decide +kernel

private theorem alt4M_a4_klein_card :
    Nat.card {a : alternatingGroup (Fin 4) // a * a = 1} = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

private def alt4M_V4 : Subgroup (alternatingGroup (Fin 4)) where
  carrier := {a | a * a = 1}
  mul_mem' := fun {a b} ha hb => alt4M_a4_klein_mul a b ha hb
  one_mem' := mul_one 1
  inv_mem' := fun {a} ha => by
    have h : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
    show a⁻¹ * a⁻¹ = 1
    rw [h]
    exact ha

private theorem alt4M_V4_card : Nat.card ↥alt4M_V4 = 4 := alt4M_a4_klein_card

end AltFour

section Model

variable {n : ℕ} {K : Type} [Group K]

private theorem alt4M_sq_ne_one {W₀ : Subgroup (Perm (Fin n))} (C : AhatData.CoverSetup n K)
    (hn : 8 ≤ n) (hinv : ∀ a ∈ W₀, a ≠ 1 → a * a = 1 → a.cycleType = {2, 2}) {x : K}
    (hx : C.ρ x ∈ W₀) (hx1 : C.ρ x ≠ 1) (hx2 : C.ρ x * C.ρ x = 1) : x * x ≠ 1 := by
  have hct := hinv _ hx hx1 hx2
  have hcard : (C.ρ x).support.card = 4 := by
    rw [← Equiv.Perm.sum_cycleType, hct]
    rfl
  exact C.dblI_sq_ne_one hn ⟨hx2, hcard⟩

private theorem alt4M_exists_lift_pow_three (C : AhatData.CoverSetup n K) {w : Perm (Fin n)}
    (hw : w ^ 3 = 1) (hs : sign w = 1) : ∃ y : K, C.ρ y = w ∧ y ^ 3 = 1 := by
  obtain ⟨x, hx⟩ := C.exists_ρ_eq hs
  have hx3 : x ^ 3 ∈ center K := by
    rw [← C.ρ_eq_one_iff, map_pow, hx, hw]
  by_cases h1 : x ^ 3 = 1
  · exact ⟨x, hx, h1⟩
  · have hz2 : x ^ 3 * x ^ 3 = 1 := C.sq_of_mem_center hx3
    have hcomm : Commute x (x ^ 3) := (Commute.refl x).pow_right 3
    refine ⟨x * x ^ 3, ?_, ?_⟩
    · rw [map_mul, hx, (C.ρ_eq_one_iff).2 hx3, mul_one]
    · rw [hcomm.mul_pow]
      calc x ^ 3 * (x ^ 3) ^ 3 = (x ^ 3 * x ^ 3) * (x ^ 3 * x ^ 3) := by group
        _ = 1 := by rw [hz2, one_mul]

private theorem alt4M_exists_two_cubes {W₀ : Subgroup (Perm (Fin n))}
    (eA : ↥W₀ ≃* alternatingGroup (Fin 4)) {w : Perm (Fin n)} (hw : w ∈ W₀) :
    ∃ u ∈ W₀, ∃ v ∈ W₀, u ^ 3 = 1 ∧ v ^ 3 = 1 ∧ w = u * v := by
  obtain ⟨x, y, hx, hy, hxy⟩ := alt4M_a4_two_cubes (eA ⟨w, hw⟩)
  refine ⟨((eA.symm x : ↥W₀) : Perm (Fin n)), (eA.symm x).2,
    ((eA.symm y : ↥W₀) : Perm (Fin n)), (eA.symm y).2, ?_, ?_, ?_⟩
  · have h : (eA.symm x) ^ 3 = 1 := by rw [← map_pow, hx, map_one]
    exact congrArg Subtype.val h
  · have h : (eA.symm y) ^ 3 = 1 := by rw [← map_pow, hy, map_one]
    exact congrArg Subtype.val h
  · have h : (⟨w, hw⟩ : ↥W₀) = eA.symm x * eA.symm y := by
      apply eA.injective
      rw [map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
      exact hxy
    exact congrArg Subtype.val h

private theorem alt4M_two_involutions {W₀ : Subgroup (Perm (Fin n))}
    (eA : ↥W₀ ≃* alternatingGroup (Fin 4)) :
    ∃ w₁ ∈ W₀, ∃ w₂ ∈ W₀, w₁ * w₁ = 1 ∧ w₂ * w₂ = 1 ∧ w₁ ≠ 1 ∧ w₂ ≠ 1 ∧ w₁ ≠ w₂ := by
  obtain ⟨a, b, ha, hb, ha1, hb1, hab⟩ := alt4M_a4_two_involutions
  refine ⟨((eA.symm a : ↥W₀) : Perm (Fin n)), (eA.symm a).2,
    ((eA.symm b : ↥W₀) : Perm (Fin n)), (eA.symm b).2, ?_, ?_, ?_, ?_, ?_⟩
  · have h : eA.symm a * eA.symm a = 1 := by rw [← map_mul, ha, map_one]
    exact congrArg Subtype.val h
  · have h : eA.symm b * eA.symm b = 1 := by rw [← map_mul, hb, map_one]
    exact congrArg Subtype.val h
  · intro h
    apply ha1
    have h' : eA.symm a = 1 := Subtype.ext h
    simpa using h'
  · intro h
    apply hb1
    have h' : eA.symm b = 1 := Subtype.ext h
    simpa using h'
  · intro h
    apply hab
    have h' : eA.symm a = eA.symm b := Subtype.ext h
    exact eA.symm.injective h'

private def alt4M_klein {W₀ : Subgroup (Perm (Fin n))} (eA : ↥W₀ ≃* alternatingGroup (Fin 4)) :
    Subgroup (Perm (Fin n)) :=
  alt4M_V4.map (W₀.subtype.comp eA.symm.toMonoidHom)

private theorem alt4M_mem_klein {W₀ : Subgroup (Perm (Fin n))}
    (eA : ↥W₀ ≃* alternatingGroup (Fin 4)) {w : Perm (Fin n)} :
    w ∈ alt4M_klein eA ↔ w ∈ W₀ ∧ w * w = 1 := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨(eA.symm a).2, ?_⟩
    have h : eA.symm a * eA.symm a = 1 := by
      rw [← map_mul]
      have : a * a = 1 := ha
      rw [this, map_one]
    exact congrArg Subtype.val h
  · rintro ⟨hw, hw2⟩
    refine ⟨eA ⟨w, hw⟩, ?_, by simp⟩
    show eA ⟨w, hw⟩ * eA ⟨w, hw⟩ = 1
    rw [← map_mul, MulEquiv.map_eq_one_iff]
    exact Subtype.ext hw2

private theorem alt4M_klein_card {W₀ : Subgroup (Perm (Fin n))}
    (eA : ↥W₀ ≃* alternatingGroup (Fin 4)) : Nat.card ↥(alt4M_klein eA) = 4 := by
  have hinj : Function.Injective (W₀.subtype.comp eA.symm.toMonoidHom) :=
    Subtype.val_injective.comp eA.symm.injective
  rw [alt4M_klein, Subgroup.card_map_of_injective hinj]
  exact alt4M_V4_card

private theorem alt4M_card_comap_ρ (C : AhatData.CoverSetup n K) {E : Subgroup (Perm (Fin n))}
    (hE : E ≤ alternatingGroup (Fin n)) : Nat.card (E.comap C.ρ) = 2 * Nat.card E := by
  set B : Subgroup K := E.comap C.ρ with hB
  let Mρ : ↥B →* Perm (Fin n) := C.ρ.comp B.subtype
  have hrange : Mρ.range = E := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact C.map_comap_eq_of_le hE
  have hker : Nat.card Mρ.ker = 2 := by
    have hZE : center K ≤ B := fun x hx => by
      rw [hB, Subgroup.mem_comap, (C.ρ_eq_one_iff).2 hx]
      exact E.one_mem
    have hk : Mρ.ker = (center K).subgroupOf B := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← C.ρ_eq_one_iff]
      rfl
    rw [hk, ← C.center_card]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZE).toEquiv
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup Mρ.ker
  have h3 : Nat.card ↥Mρ.range = Nat.card ↥E := by rw [hrange]
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange Mρ).toEquiv, h3, hker] at h1
  omega

private theorem alt4M_oddGenerated {W₀ : Subgroup (Perm (Fin n))} (C : AhatData.CoverSetup n K)
    (hn : 8 ≤ n) (hW₀A : W₀ ≤ alternatingGroup (Fin n)) (eA : ↥W₀ ≃* alternatingGroup (Fin 4))
    (hinv : ∀ a ∈ W₀, a ≠ 1 → a * a = 1 → a.cycleType = {2, 2}) :
    Subgroup.closure {x : ↥(W₀.comap C.ρ) | Odd (orderOf x)} = ⊤ := by
  classical
  set E : Subgroup K := W₀.comap C.ρ with hE
  let Mρ : ↥E →* Perm (Fin n) := C.ρ.comp E.subtype
  set H₃ : Subgroup ↥E := Subgroup.closure {x : ↥E | Odd (orderOf x)} with hH₃
  have hStep0 : ∀ u ∈ W₀, u ^ 3 = 1 → u ∈ H₃.map Mρ := by
    intro u hu hu3
    obtain ⟨y, hy, hy3⟩ := alt4M_exists_lift_pow_three C hu3 (Perm.mem_alternatingGroup.1 (hW₀A hu))
    have hyE : y ∈ E := by
      rw [hE, Subgroup.mem_comap, hy]
      exact hu
    refine ⟨⟨y, hyE⟩, Subgroup.subset_closure ?_, hy⟩
    show Odd (orderOf (⟨y, hyE⟩ : ↥E))
    rw [← Subgroup.orderOf_coe]
    exact Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one hy3)
  have hStep1 : W₀ ≤ H₃.map Mρ := by
    intro w hw
    obtain ⟨u, hu, v, hv, hu3, hv3, rfl⟩ := alt4M_exists_two_cubes eA hw
    exact (H₃.map Mρ).mul_mem (hStep0 u hu hu3) (hStep0 v hv hv3)
  obtain ⟨u, hu, -, -, hu2, -, hu1, -, -⟩ := alt4M_two_involutions eA
  obtain ⟨y', hy'H, hy'ρ⟩ := hStep1 hu
  have hρy' : C.ρ (y' : K) = u := hy'ρ
  have hc₀ne : (y' : K) * (y' : K) ≠ 1 :=
    alt4M_sq_ne_one C hn hinv (by rw [hρy']; exact hu) (by rw [hρy']; exact hu1)
      (by rw [hρy']; exact hu2)
  have hc₀cen : (y' : K) * (y' : K) ∈ center K :=
    C.sq_mem_center (by rw [hρy']; exact hu2)
  have hc₀H : y' * y' ∈ H₃ := H₃.mul_mem hy'H hy'H
  rw [eq_top_iff]
  intro x _
  have hx : C.ρ (x : K) ∈ W₀ := x.2
  obtain ⟨y, hyH, hyx⟩ := hStep1 hx
  have hyx' : C.ρ (y : K) = C.ρ (x : K) := hyx
  have hcen : (y : K)⁻¹ * (x : K) ∈ center K := by
    rw [← C.ρ_eq_one_iff, map_mul, map_inv, hyx', inv_mul_cancel]
  by_cases h1 : (y : K)⁻¹ * (x : K) = 1
  · have : x = y := Subtype.ext (inv_mul_eq_one.1 h1).symm
    rw [this]
    exact hyH
  · have h2 : (y : K)⁻¹ * (x : K) = (y' : K) * (y' : K) :=
      C.center_eq_of_ne_one hcen hc₀cen h1 hc₀ne
    have h3 : x = y * (y' * y') := Subtype.ext (by
      have : (x : K) = (y : K) * ((y' : K) * (y' : K)) := by rw [← h2]; group
      simpa using this)
    rw [h3]
    exact H₃.mul_mem hyH hc₀H

variable [Finite K]

theorem exists_sl23_model_of_alt4 (C : AhatData.CoverSetup n K) (hn : 8 ≤ n) {α : MulAut K}
    {σ : Perm (Fin n)} (hα : C.Induces α σ) {W₀ : Subgroup (Perm (Fin n))}
    (hW₀A : W₀ ≤ alternatingGroup (Fin n)) (hW₀4 : Nonempty (↥W₀ ≃* alternatingGroup (Fin 4)))
    (hinv : ∀ a ∈ W₀, a ≠ 1 → a * a = 1 → a.cycleType = {2, 2})
    (hW₀σ : ∀ a ∈ W₀, a * σ = σ * a)
    (hnorm : ∀ ν : Perm (Fin n), ν * σ = σ * ν → ∀ a ∈ W₀, ν * a * ν⁻¹ ∈ W₀) :
    ∃ P Qb : Subgroup K, P ≤ AhatData.fixSub α ∧
      (∀ g ∈ AhatData.fixSub α, ∀ p ∈ P, g * p * g⁻¹ ∈ P) ∧ Nonempty (↥P ≃* SL23) ∧
      (∀ N : Subgroup K, N ≤ P → (∀ p ∈ P, ∀ x ∈ N, p * x * p⁻¹ ∈ N) → Odd (Nat.card ↥N) →
        N = ⊥) ∧
      Qb ≤ P ∧ Nat.card ↥Qb = 8 ∧ (∀ g ∈ AhatData.fixSub α, ∀ q ∈ Qb, g * q * g⁻¹ ∈ Qb) ∧
      (∀ q ∈ Qb, q ≠ 1 → ∃ k : ℕ, q ^ k ∈ center K ∧ q ^ k ≠ 1) ∧
      ∃ a ∈ Qb, ∃ b ∈ Qb, ⁅a, b⁆ ∈ center K ∧ ⁅a, b⁆ ≠ 1 := by
  obtain ⟨eA⟩ := hW₀4
  set P : Subgroup K := W₀.comap C.ρ
  set V : Subgroup (Perm (Fin n)) := alt4M_klein eA
  have hVW : ∀ w ∈ V, w ∈ W₀ ∧ w * w = 1 := fun w hw => (alt4M_mem_klein eA).1 hw
  have hVA : V ≤ alternatingGroup (Fin n) := fun w hw => hW₀A (hVW w hw).1
  have hVcard : Nat.card ↥V = 4 := alt4M_klein_card eA
  obtain ⟨c, hc1, -⟩ := (Nat.card_eq_two_iff' (1 : ↥(center K))).1 C.center_card
  have hcc : (c : K) ∈ center K := c.2
  have hc1' : (c : K) ≠ 1 := fun h => hc1 (Subtype.ext h)
  have hcP : (c : K) ∈ P := by
    show C.ρ c ∈ W₀
    rw [(C.ρ_eq_one_iff).2 hcc]
    exact W₀.one_mem
  have hfixcomm : ∀ g ∈ AhatData.fixSub α, C.ρ g * σ = σ * C.ρ g := by
    intro g hg
    have h1 := hα.map_ρ g
    rw [AhatData.mem_fixSub.1 hg] at h1
    calc C.ρ g * σ = (σ * C.ρ g * σ⁻¹) * σ := by rw [← h1]
      _ = σ * C.ρ g := by group
  have hgen : Subgroup.closure {x : ↥P | Odd (orderOf x)} = ⊤ :=
    alt4M_oddGenerated C hn hW₀A eA hinv
  have hPfix : P ≤ AhatData.fixSub α :=
    hα.le_fixSub_of_oddGenerated P (fun x hx => hW₀σ _ hx) hgen
  have hPnorm : ∀ g ∈ AhatData.fixSub α, ∀ p ∈ P, g * p * g⁻¹ ∈ P := by
    intro g hg p hp
    have hp' : C.ρ p ∈ W₀ := hp
    show C.ρ (g * p * g⁻¹) ∈ W₀
    rw [map_mul, map_mul, map_inv]
    exact hnorm _ (hfixcomm g hg) _ hp'
  let ρS : ↥P →* ↥W₀ := (C.ρ.comp P.subtype).codRestrict W₀ (fun x => x.2)
  let φ : ↥P →* alternatingGroup (Fin 4) := eA.toMonoidHom.comp ρS
  have hρS : Function.Surjective ρS := by
    intro w
    obtain ⟨k, hk⟩ := C.exists_ρ_eq (Perm.mem_alternatingGroup.1 (hW₀A w.2))
    refine ⟨⟨k, ?_⟩, Subtype.ext hk⟩
    show C.ρ k ∈ W₀
    rw [hk]
    exact w.2
  have hφ1 : ∀ x : ↥P, φ x = 1 ↔ C.ρ (x : K) = 1 := by
    intro x
    change eA (ρS x) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff]
    exact Subtype.ext_iff
  have hdata : CFSG.GH74.GLS.IVK.Proofs2.Ivk5An.SL23.Data (⟨c, hcP⟩ : ↥P) φ :=
    { surj := fun b => by
        obtain ⟨x, hx⟩ := hρS (eA.symm b)
        exact ⟨x, by change eA (ρS x) = b; rw [hx]; exact eA.apply_symm_apply b⟩
      ne_one := fun h0 => hc1' (congrArg Subtype.val h0)
      sq := Subtype.ext (C.sq_of_mem_center hcc)
      central := fun g => Subtype.ext (mem_center_iff.1 hcc g)
      φ_z := (hφ1 _).2 ((C.ρ_eq_one_iff).2 hcc)
      ker := fun x hx => by
        have hxc : (x : K) ∈ center K := (C.ρ_eq_one_iff).1 ((hφ1 x).1 hx)
        by_cases h1 : (x : K) = 1
        · exact Or.inl (Subtype.ext h1)
        · exact Or.inr (Subtype.ext (C.center_eq_of_ne_one hxc hcc h1 hc1'))
      inv := fun x hx => by
        have hx' : (x : K) * x = 1 := congrArg Subtype.val hx
        have hρ : C.ρ (x : K) * C.ρ (x : K) = 1 := by rw [← map_mul, hx', map_one]
        by_cases h1 : C.ρ (x : K) = 1
        · have hxc : (x : K) ∈ center K := (C.ρ_eq_one_iff).1 h1
          by_cases h2 : (x : K) = 1
          · exact Or.inl (Subtype.ext h2)
          · exact Or.inr (Subtype.ext (C.center_eq_of_ne_one hxc hcc h2 hc1'))
        · exact absurd hx' (alt4M_sq_ne_one C hn hinv x.2 h1 hρ) }
  have hOdd : ∀ N : Subgroup K, N ≤ P → (∀ p ∈ P, ∀ x ∈ N, p * x * p⁻¹ ∈ N) →
      Odd (Nat.card ↥N) → N = ⊥ := by
    intro N hNP hNnorm hNodd
    have hnormal : (N.subgroupOf P).Normal :=
      ⟨fun x hx g => by
        have h1 : (x : K) ∈ N := hx
        have h2 : (g : K) * x * (g : K)⁻¹ ∈ N := hNnorm g g.2 x h1
        exact h2⟩
    have hodd : Odd (Nat.card ↥(N.subgroupOf P)) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNP).toEquiv]
      exact hNodd
    have hle : N.subgroupOf P ≤ CFSG.oddCore ↥P := le_sSup ⟨hnormal, hodd⟩
    rw [hdata.oddCore_eq_bot] at hle
    rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, hNP hx⟩ : ↥P) ∈ N.subgroupOf P := hx
    have hx'' := hle hx'
    rw [Subgroup.mem_bot] at hx''
    exact (Subgroup.mem_bot).2 (congrArg Subtype.val hx'')
  have hQP : V.comap C.ρ ≤ P := Subgroup.comap_mono (fun w hw => (hVW w hw).1)
  have hQcard : Nat.card ↥(V.comap C.ρ) = 8 := by
    rw [alt4M_card_comap_ρ C hVA, hVcard]
  have hQnorm : ∀ g ∈ AhatData.fixSub α, ∀ q ∈ V.comap C.ρ, g * q * g⁻¹ ∈ V.comap C.ρ := by
    intro g hg q hq
    have hq' : C.ρ q ∈ V := hq
    obtain ⟨hqW, hqsq⟩ := hVW _ hq'
    show C.ρ (g * q * g⁻¹) ∈ V
    rw [map_mul, map_mul, map_inv]
    refine (alt4M_mem_klein eA).2 ⟨hnorm _ (hfixcomm g hg) _ hqW, ?_⟩
    calc C.ρ g * C.ρ q * (C.ρ g)⁻¹ * (C.ρ g * C.ρ q * (C.ρ g)⁻¹)
        = C.ρ g * (C.ρ q * C.ρ q) * (C.ρ g)⁻¹ := by group
      _ = 1 := by rw [hqsq]; group
  have hQpow : ∀ q ∈ V.comap C.ρ, q ≠ 1 → ∃ k : ℕ, q ^ k ∈ center K ∧ q ^ k ≠ 1 := by
    intro q hq hq1
    have hq' : C.ρ q ∈ V := hq
    obtain ⟨hqW, hqsq⟩ := hVW _ hq'
    by_cases hqc : q ∈ center K
    · exact ⟨1, by simpa using hqc, by simpa using hq1⟩
    · have hρ1 : C.ρ q ≠ 1 := fun h => hqc ((C.ρ_eq_one_iff).1 h)
      refine ⟨2, ?_, ?_⟩
      · rw [pow_two]
        exact C.sq_mem_center hqsq
      · rw [pow_two]
        exact alt4M_sq_ne_one C hn hinv hqW hρ1 hqsq
  have hcomm : ∃ a ∈ V.comap C.ρ, ∃ b ∈ V.comap C.ρ, ⁅a, b⁆ ∈ center K ∧ ⁅a, b⁆ ≠ 1 := by
    obtain ⟨w₁, hw₁, w₂, hw₂, hw₁sq, hw₂sq, hw₁1, hw₂1, hw₁₂⟩ := alt4M_two_involutions eA
    have hw₁V : w₁ ∈ V := (alt4M_mem_klein eA).2 ⟨hw₁, hw₁sq⟩
    have hw₂V : w₂ ∈ V := (alt4M_mem_klein eA).2 ⟨hw₂, hw₂sq⟩
    obtain ⟨a₁, ha₁⟩ := C.exists_ρ_eq (Perm.mem_alternatingGroup.1 (hW₀A hw₁))
    obtain ⟨a₂, ha₂⟩ := C.exists_ρ_eq (Perm.mem_alternatingGroup.1 (hW₀A hw₂))
    have hw₁₂V : w₁ * w₂ ∈ V := V.mul_mem hw₁V hw₂V
    obtain ⟨hw₁₂W, hw₁₂sq⟩ := hVW _ hw₁₂V
    have h2 : w₂⁻¹ = w₂ := inv_eq_of_mul_eq_one_right hw₂sq
    have hcomm₁₂ : w₁ * w₂ = w₂ * w₁ := by
      have h1 : (w₁ * w₂)⁻¹ = w₁ * w₂ := inv_eq_of_mul_eq_one_right hw₁₂sq
      have h3 : w₁⁻¹ = w₁ := inv_eq_of_mul_eq_one_right hw₁sq
      calc w₁ * w₂ = (w₁ * w₂)⁻¹ := h1.symm
        _ = w₂⁻¹ * w₁⁻¹ := mul_inv_rev w₁ w₂
        _ = w₂ * w₁ := by rw [h2, h3]
    have hne₁₂ : w₁ * w₂ ≠ 1 := fun h => hw₁₂ ((eq_inv_of_mul_eq_one_left h).trans h2)
    refine ⟨a₁, ?_, a₂, ?_, C.comm_mem_center (by rw [ha₁, ha₂]; exact hcomm₁₂), fun h1 => ?_⟩
    · show C.ρ a₁ ∈ V
      rw [ha₁]
      exact hw₁V
    · show C.ρ a₂ ∈ V
      rw [ha₂]
      exact hw₂V
    · have hcomm12 : a₁ * a₂ = a₂ * a₁ := commutatorElement_eq_one_iff_mul_comm.1 h1
      have h11 : a₁ * a₁ ≠ 1 :=
        alt4M_sq_ne_one C hn hinv (by rw [ha₁]; exact hw₁) (by rw [ha₁]; exact hw₁1)
          (by rw [ha₁]; exact hw₁sq)
      have h22 : a₂ * a₂ ≠ 1 :=
        alt4M_sq_ne_one C hn hinv (by rw [ha₂]; exact hw₂) (by rw [ha₂]; exact hw₂1)
          (by rw [ha₂]; exact hw₂sq)
      have hc11 : a₁ * a₁ ∈ center K := C.sq_mem_center (by rw [ha₁]; exact hw₁sq)
      have hc22 : a₂ * a₂ ∈ center K := C.sq_mem_center (by rw [ha₂]; exact hw₂sq)
      have hEq : a₁ * a₁ = a₂ * a₂ := C.center_eq_of_ne_one hc11 hc22 h11 h22
      have hsq : (a₁ * a₂) * (a₁ * a₂) = 1 := by
        calc (a₁ * a₂) * (a₁ * a₂) = a₁ * (a₂ * a₁) * a₂ := by group
          _ = a₁ * (a₁ * a₂) * a₂ := by rw [hcomm12]
          _ = (a₁ * a₁) * (a₂ * a₂) := by group
          _ = (a₁ * a₁) * (a₁ * a₁) := by rw [← hEq]
          _ = 1 := C.sq_of_mem_center hc11
      exact alt4M_sq_ne_one C hn hinv (x := a₁ * a₂) (by rw [map_mul, ha₁, ha₂]; exact hw₁₂W)
        (by rw [map_mul, ha₁, ha₂]; exact hne₁₂) (by rw [map_mul, ha₁, ha₂]; exact hw₁₂sq) hsq
  exact ⟨P, V.comap C.ρ, hPfix, hPnorm, hdata.nonempty_equiv_sl23, hOdd, hQP, hQcard, hQnorm,
    hQpow, hcomm⟩

end Model

end CFSG.OddStandard.Solomon75
