module

public import CFSG.LargeExtraspecial.S63BBasic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup CFSG.Timmesfeld CFSG.ComponentClassification

namespace S63

theorem eq_or_eq_inv_of_mem_zpowers_sq {G : Type*} [Group G] {q z : G}
    (hq4 : q * q * (q * q) = 1) (hq2 : q * q ≠ 1) (hz : z ∈ zpowers q) (hzz : z * z = q * q) :
    z = q ∨ z = q⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf q = 4 := by
    have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := q) (by
      rw [pow_one, pow_two]; exact hq2) (by
      rw [show 2 ^ (1 + 1) = 2 * 2 by norm_num, pow_mul, pow_two, pow_two, ← pow_two]
      rw [pow_two]; exact hq4)
    rw [h]; norm_num
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hz
  rw [← zpow_mod_orderOf, hord] at hzz ⊢
  have h0 : 0 ≤ k % ((4 : ℕ) : ℤ) := Int.emod_nonneg k (by norm_num)
  have h4 : k % ((4 : ℕ) : ℤ) < 4 := Int.emod_lt_of_pos k (by norm_num)
  have hq4' : q ^ (4 : ℤ) = 1 := by
    rw [show (4 : ℤ) = ((2 : ℕ) : ℤ) * ((2 : ℕ) : ℤ) by norm_num, zpow_mul, zpow_natCast,
      zpow_natCast, pow_two, pow_two]
    exact hq4
  generalize k % ((4 : ℕ) : ℤ) = j at hzz h0 h4 ⊢
  interval_cases j
  · exfalso
    apply hq2
    rw [← hzz, zpow_zero, mul_one]
  · left
    exact zpow_one q
  · exfalso
    apply hq2
    rw [← hzz, ← zpow_add, ← hq4', show (2 : ℤ) + 2 = 4 by norm_num]
  · right
    rw [eq_inv_iff_mul_eq_one, ← zpow_add_one, show (3 : ℤ) + 1 = 4 by norm_num]
    exact hq4'

variable {X : Type} [Group X] {ζ : X} {F : Subgroup X}

namespace SmithConf

section Group

variable (hC : SmithConf ζ F)
include hC

theorem comm_mul_left {x g v : X} (hx : x ∈ F) (hg : g ∈ F)
    (hv : v ∈ F ⊔ centralizer (F : Set X)) :
    x * g * v * (x * g)⁻¹ * v⁻¹ = (g * v * g⁻¹ * v⁻¹) * (x * v * x⁻¹ * v⁻¹) := by
  have hc := hC.comm_of_eq_one_or_eq (hC.comm_eq_of_mem_E (le_sup_left (a := F) hg) hv) hx
  calc x * g * v * (x * g)⁻¹ * v⁻¹ = x * (g * v * g⁻¹ * v⁻¹) * v * x⁻¹ * v⁻¹ := by group
    _ = (g * v * g⁻¹ * v⁻¹) * x * v * x⁻¹ * v⁻¹ := by rw [← hc]
    _ = (g * v * g⁻¹ * v⁻¹) * (x * v * x⁻¹ * v⁻¹) := by group

omit hC in
theorem comm_iff_commutator_eq_one {x v : X} : x * v = v * x ↔ x * v * x⁻¹ * v⁻¹ = 1 := by
  constructor
  · intro h
    rw [h]
    group
  · intro h
    calc x * v = x * v * x⁻¹ * v⁻¹ * (v * x) := by group
      _ = v * x := by rw [h, one_mul]

theorem eq_of_comm_centralizer {e u : X} (he : e ∈ F) (hu : u ∈ F)
    (h : ∀ x ∈ F, x * e = e * x → u * x = x * u) :
    u = 1 ∨ u = ζ ∨ u = e ∨ u = e * ζ := by
  have heE : e ∈ F ⊔ centralizer (F : Set X) := le_sup_left (a := F) he
  have huE : u ∈ F ⊔ centralizer (F : Set X) := le_sup_left (a := F) hu
  by_cases hcen : ∀ g ∈ F, u * g = g * u
  · rcases hC.eq_one_or_eq_of_forall_comm hu hcen with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
  push Not at hcen
  obtain ⟨g, hg, hgu⟩ := hcen
  have hgu' : ¬ (g * u = u * g) := fun h' => hgu h'.symm
  have hge : ¬ (g * e = e * g) := fun h' => hgu (h g hg h')
  have hcgu : g * u * g⁻¹ * u⁻¹ = ζ :=
    (hC.comm_eq_of_mem_E (le_sup_left (a := F) hg) huE).resolve_left
      (fun h' => hgu' (comm_iff_commutator_eq_one.mpr h'))
  have hcge : g * e * g⁻¹ * e⁻¹ = ζ :=
    (hC.comm_eq_of_mem_E (le_sup_left (a := F) hg) heE).resolve_left
      (fun h' => hge (comm_iff_commutator_eq_one.mpr h'))
  have hζζ : ζ * ζ = 1 := hC.star.mul_self
  have hcomm : ∀ x ∈ F, x * u * x⁻¹ * u⁻¹ = x * e * x⁻¹ * e⁻¹ := by
    intro x hx
    by_cases hxe : x * e = e * x
    · rw [comm_iff_commutator_eq_one.mp hxe,
        comm_iff_commutator_eq_one.mp (h x hx hxe).symm]
    · have hcxe : x * e * x⁻¹ * e⁻¹ = ζ :=
        (hC.comm_eq_of_mem_E (le_sup_left (a := F) hx) heE).resolve_left
          (fun h' => hxe (comm_iff_commutator_eq_one.mpr h'))
      rw [hcxe]
      rcases hC.comm_eq_of_mem_E (le_sup_left (a := F) hx) huE with hcxu | hcxu
      · exfalso
        have h1 : x * g * e * (x * g)⁻¹ * e⁻¹ = 1 := by
          rw [hC.comm_mul_left hx hg heE, hcge, hcxe, hζζ]
        have h2 := h (x * g) (mul_mem hx hg) (comm_iff_commutator_eq_one.mpr h1)
        have h3 : x * g * u * (x * g)⁻¹ * u⁻¹ = 1 := comm_iff_commutator_eq_one.mp h2.symm
        rw [hC.comm_mul_left hx hg huE, hcgu, hcxu, mul_one] at h3
        exact hC.zeta_ne_one h3
      · exact hcxu
  have hc : ∀ x ∈ F, (u * e⁻¹) * x = x * (u * e⁻¹) := by
    intro x hx
    have hcx := hcomm x hx
    have hval := hC.comm_eq_of_mem_E (le_sup_left (a := F) hx) heE
    have hcz := hC.comm_of_eq_one_or_eq hval (mul_mem hu (inv_mem he))
    have hxu : x * u * x⁻¹ = (x * e * x⁻¹ * e⁻¹) * u := by
      rw [← hcx]
      group
    have hxe : x * e * x⁻¹ = (x * e * x⁻¹ * e⁻¹) * e := by group
    have h1 : x * (u * e⁻¹) * x⁻¹ = u * e⁻¹ := by
      calc x * (u * e⁻¹) * x⁻¹ = (x * u * x⁻¹) * (x * e * x⁻¹)⁻¹ := by group
        _ = (x * e * x⁻¹ * e⁻¹) * u * ((x * e * x⁻¹ * e⁻¹) * e)⁻¹ := by rw [← hxu, ← hxe]
        _ = (x * e * x⁻¹ * e⁻¹) * (u * e⁻¹) * (x * e * x⁻¹ * e⁻¹)⁻¹ := by group
        _ = (u * e⁻¹) * (x * e * x⁻¹ * e⁻¹) * (x * e * x⁻¹ * e⁻¹)⁻¹ := by rw [hcz]
        _ = u * e⁻¹ := by group
    calc (u * e⁻¹) * x = x * (u * e⁻¹) * x⁻¹ * x := by rw [h1]
      _ = x * (u * e⁻¹) := by group
  rcases hC.eq_one_or_eq_of_forall_comm (mul_mem hu (inv_mem he)) hc with h1 | h1
  · right; right; left
    calc u = u * e⁻¹ * e := by group
      _ = e := by rw [h1, one_mul]
  · right; right; right
    calc u = u * e⁻¹ * e := by group
      _ = ζ * e := by rw [h1]
      _ = e * ζ := (hC.comm_zeta he).symm

theorem exists_sq_eq_zeta {τ y : X} (hτ : τ ∈ CorB.conjCent ζ) (hne : τ ≠ ζ)
    (hy : y * ζ = ζ * y) (hyc : ∀ x ∈ F, x * τ = τ * x → y * x = x * y) (hyy : y * y = τ) :
    ∃ u ∈ F, u * τ = τ * u ∧ (∀ a ∈ F, a * τ = τ * a → u * a = a * u) ∧ u * u = ζ := by
  obtain ⟨f, hf, hfτ⟩ := hC.fusionF τ hτ hne
  have hζζ : ζ * ζ = 1 := hC.star.mul_self
  have hτE := hC.hyp.conj_mem_E τ hτ.2 hτ.1
  have hfz : f * ζ = ζ * f := hC.comm_zeta hf
  have hfzi : f⁻¹ * ζ = ζ * f⁻¹ := (Commute.inv_left (show Commute f ζ from hfz)).eq
  have hnc : ∀ x ∈ F, ¬ (x * τ = τ * x) → x * τ * x⁻¹ = ζ * τ := by
    intro x hx hxn
    rcases hC.comm_eq_of_mem_E (le_sup_left (a := F) hx) hτE with h | h
    · exact absurd (comm_iff_commutator_eq_one.mpr h) hxn
    · calc x * τ * x⁻¹ = x * τ * x⁻¹ * τ⁻¹ * τ := by group
        _ = ζ * τ := by rw [h]
  have hfn : ¬ (f * τ = τ * f) := by
    intro h
    rw [h, mul_inv_cancel_right] at hfτ
    exact hC.zeta_ne_one (mul_eq_right.mp hfτ.symm)
  have hτf : f⁻¹ * τ * f = ζ * τ := by
    calc f⁻¹ * τ * f = f⁻¹ * ζ * (ζ * τ) * f := by
          rw [show f⁻¹ * ζ * (ζ * τ) * f = f⁻¹ * (ζ * ζ) * τ * f by group, hζζ, mul_one]
      _ = ζ * f⁻¹ * (f * τ * f⁻¹) * f := by rw [hfzi, hfτ]
      _ = ζ * τ := by group
  have hτf2 : τ * f * τ⁻¹ = ζ * f := by
    calc τ * f * τ⁻¹ = ζ * (ζ * τ * f) * τ⁻¹ := by
          rw [show ζ * (ζ * τ * f) = (ζ * ζ) * τ * f by group, hζζ, one_mul]
      _ = ζ * (f * τ * f⁻¹ * f) * τ⁻¹ := by rw [← hfτ]
      _ = ζ * f := by group
  set f' := y * f * y⁻¹ with hf'
  have hf'F : f' ∈ F := hC.hyp.conj_mem y (mem_centralizer_singleton_iff.mpr hy) f hf
  have hf'n : ¬ (f' * τ = τ * f') := by
    intro h
    have h1 := hyc f' hf'F h
    have : f = f' := by
      have e1 : f = y⁻¹ * (y * f * y⁻¹) * y := by group
      rw [e1, ← hf', mul_assoc, ← h1, ← mul_assoc, inv_mul_cancel, one_mul]
    exact hfn (this ▸ h)
  set u := f⁻¹ * f' with hu
  have huF : u ∈ F := mul_mem (inv_mem hf) hf'F
  have huτ : u * τ = τ * u := by
    have h1 := hnc f' hf'F hf'n
    have h2 : u * τ * u⁻¹ = τ := by
      calc u * τ * u⁻¹ = f⁻¹ * (f' * τ * f'⁻¹) * f := by rw [hu]; group
        _ = f⁻¹ * ζ * τ * f := by rw [h1]; group
        _ = ζ * (f⁻¹ * τ * f) := by rw [hfzi]; group
        _ = ζ * (ζ * τ) := by rw [hτf]
        _ = τ := by rw [← mul_assoc, hζζ, one_mul]
    calc u * τ = u * τ * u⁻¹ * u := by group
      _ = τ * u := by rw [h2]
  have hyu : y * u = u * y := hyc u huF huτ
  have hyf : y * f * y⁻¹ = f * u := by rw [hu, hf']; group
  have h3 : (y * y) * f * (y * y)⁻¹ = f * (u * u) := by
    calc (y * y) * f * (y * y)⁻¹ = y * (y * f * y⁻¹) * y⁻¹ := by group
      _ = y * (f * u) * y⁻¹ := by rw [hyf]
      _ = (y * f * y⁻¹) * (y * u * y⁻¹) := by group
      _ = (f * u) * u := by rw [hyf, hyu, mul_inv_cancel_right]
      _ = f * (u * u) := by group
  rw [hyy, hτf2] at h3
  have huu : u * u = ζ := by
    have h4 : f * (u * u) = f * ζ := by rw [← h3, hfz]
    exact mul_left_cancel h4
  refine ⟨u, huF, huτ, fun a ha haτ => ?_, huu⟩
  have haz : a * ζ = ζ * a := hC.comm_zeta ha
  have hfa : f * a * f⁻¹ ∈ F := mul_mem (mul_mem hf ha) (inv_mem hf)
  have hfaτ : (f * a * f⁻¹) * τ = τ * (f * a * f⁻¹) := by
    calc (f * a * f⁻¹) * τ = f * a * (f⁻¹ * τ * f) * f⁻¹ := by group
      _ = f * (a * ζ) * τ * f⁻¹ := by rw [hτf]; group
      _ = (f * ζ) * a * τ * f⁻¹ := by rw [haz]; group
      _ = ζ * (f * (a * τ) * f⁻¹) := by rw [hfz]; group
      _ = ζ * (f * τ * f⁻¹) * (f * a * f⁻¹) := by rw [haτ]; group
      _ = ζ * (ζ * τ) * (f * a * f⁻¹) := by rw [hfτ]
      _ = τ * (f * a * f⁻¹) := by rw [← mul_assoc ζ ζ, hζζ, one_mul]
  have h4 := hyc _ hfa hfaτ
  have hya := hyc a ha haτ
  have h5 : f * a * f⁻¹ = (f * u) * a * (f * u)⁻¹ := by
    calc f * a * f⁻¹ = y * (f * a * f⁻¹) * y⁻¹ := by rw [h4, mul_inv_cancel_right]
      _ = (y * f * y⁻¹) * (y * a * y⁻¹) * (y * f * y⁻¹)⁻¹ := by group
      _ = (f * u) * a * (f * u)⁻¹ := by rw [hyf, hya, mul_inv_cancel_right]
  have h7 : a = u * a * u⁻¹ := by
    calc a = f⁻¹ * (f * a * f⁻¹) * f := by group
      _ = f⁻¹ * ((f * u) * a * (f * u)⁻¹) * f := by rw [← h5]
      _ = u * a * u⁻¹ := by group
  calc u * a = u * a * u⁻¹ * u := by group
    _ = a * u := by rw [← h7]

theorem conj_mem_Finn_of_comm {m : X} (hm : m * ζ = ζ * m) {f : X} (hf : f ∈ Finn ζ F) :
    m * f * m⁻¹ ∈ Finn ζ F := by
  refine ⟨hC.hyp.conj_mem m (mem_centralizer_singleton_iff.mpr hm) f hf.1, ?_⟩
  change SmithConf.conjAut ζ (m * f * m⁻¹) ∈ OuterAutomorphisms.inner (UZ ζ)
  rw [map_mul, map_mul, map_inv]
  exact (OuterAutomorphisms.inner_normal (UZ ζ)).conj_mem _ hf.2 _

end Group

section Inner

variable [Finite X] (hC : SmithConf ζ F) (hs : IsSimpleGroup (UZ ζ))
include hC hs

theorem exists_involution_conj_eq {τ : X} (hτ : τ ∈ CorB.conjCent ζ)
    (hτN : piU ζ ⟨τ, mem_normalClosure_of_isConj hτ.2⟩ ∈ (iota (F := F) hs).range) :
    ∃ h ∈ F, h * h = 1 ∧ ∀ f ∈ F, h * f * h⁻¹ = τ * f * τ⁻¹ := by
  obtain ⟨h, hh⟩ := hτN
  have hhF : (h : X) ∈ F := Finn_le ζ F h.2
  have hα : SmithConf.conjAut ζ (h : X) = SmithConf.conjAut ζ τ := by
    rw [← conj_iota hs h, hh]
    exact (conjAut_of_mem_U ⟨τ, mem_normalClosure_of_isConj hτ.2⟩).symm
  refine ⟨h, hhF, ?_, fun f hf => ?_⟩
  · have h1 : iota hs (h * h) = 1 := by
      rw [map_mul, hh, ← pow_two, ← hC.orderOf_piU hs hτ.2]
      exact pow_orderOf_eq_one _
    have h2 : h * h = 1 := hC.iota_injective hs (h1.trans (map_one _).symm)
    exact congrArg Subtype.val h2
  · have hτf : τ * f * τ⁻¹ ∈ F :=
      hC.hyp.conj_mem τ (mem_centralizer_singleton_iff.mpr hτ.1) f hf
    have hmem : (h : X) * f * (h : X)⁻¹ * (τ * f * τ⁻¹)⁻¹ ∈ F :=
      mul_mem (mul_mem (mul_mem hhF hf) (inv_mem hhF)) (inv_mem hτf)
    have h1 : SmithConf.conjAut ζ ((h : X) * f * (h : X)⁻¹ * (τ * f * τ⁻¹)⁻¹) = 1 := by
      simp only [map_mul, map_inv, hα]
      group
    have h2 := hC.eq_one_of_conjAut_eq_one hs hmem h1
    calc (h : X) * f * (h : X)⁻¹ =
          (h : X) * f * (h : X)⁻¹ * (τ * f * τ⁻¹)⁻¹ * (τ * f * τ⁻¹) := by group
      _ = τ * f * τ⁻¹ := by rw [h2, one_mul]

end Inner

end SmithConf

end S63

end CFSG.LargeExtraspecial
