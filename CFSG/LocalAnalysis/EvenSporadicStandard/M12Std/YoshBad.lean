module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshCentral
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshT
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshSylow

public section

namespace CFSG.EvenSporadicStandard.M12Std.Yosh

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.GH74.M12 CFSG.GH74.M12.Hyp
open CFSG.ComponentClassification.M12Cover CFSG.Sporadic.Schreier
open CFSG.EvenSporadicStandard.Fin76b.AutETable

theorem pow_four_eq {M : Type*} [Monoid M] (a : M) : a ^ 4 = a * a * (a * a) := by
  rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]

@[expose] def pA : Equiv.Perm (Fin 12) :=
  List.formPerm [0, 3] * List.formPerm [2, 9] * List.formPerm [4, 10] * List.formPerm [5, 11]

@[expose] def mP : Equiv.Perm (Fin 12) :=
  List.formPerm [0, 5, 4] * List.formPerm [1, 9, 11] * List.formPerm [2, 6, 7] *
    List.formPerm [3, 10, 8]

theorem pA_mem_M12 : pA ∈ NativeSporadic.M12 := Subgroup.subset_closure (by simp [pA])

theorem pB_mem_M12 : pB ∈ NativeSporadic.M12 := Subgroup.subset_closure (by simp [pB])

set_option maxRecDepth 100000 in
theorem mP_eq_word :
    mP = pB⁻¹ * pA * pB * pA * pB⁻¹ * pA * pB⁻¹ * pA * pB * pA * pB⁻¹ * pA := by decide

theorem mP_mem_M12 : mP ∈ NativeSporadic.M12 := by
  rw [mP_eq_word]
  have hA := pA_mem_M12
  have hB := pB_mem_M12
  have hBi := inv_mem hB
  exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem
    (mul_mem (mul_mem hBi hA) hB) hA) hBi) hA) hBi) hA) hB) hA) hBi) hA

set_option maxRecDepth 100000 in
theorem mP_conj : mP⁻¹ * bfJ * mP⁻¹⁻¹ = u1P := by decide

set_option maxRecDepth 100000 in
theorem u1P_comm_bfJ : u1P * bfJ = bfJ * u1P := by decide

theorem card_centralizer_conj {G : Type*} [Group G] (f e : G) :
    Nat.card (centralizer ({f * e * f⁻¹} : Set G)) = Nat.card (centralizer ({e} : Set G)) := by
  refine Nat.card_congr
    { toFun := fun y => ⟨f⁻¹ * y * f, ?_⟩
      invFun := fun z => ⟨f * z * f⁻¹, ?_⟩
      left_inv := fun y => Subtype.ext (by group)
      right_inv := fun z => Subtype.ext (by group) }
  · have hy := mem_centralizer_iff.1 y.2 (f * e * f⁻¹) (Set.mem_singleton _)
    rw [mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    calc e * (f⁻¹ * (y : G) * f) = f⁻¹ * ((f * e * f⁻¹) * (y : G)) * f := by group
      _ = f⁻¹ * ((y : G) * (f * e * f⁻¹)) * f := by rw [hy]
      _ = f⁻¹ * (y : G) * f * e := by group
  · have hz := mem_centralizer_iff.1 z.2 e (Set.mem_singleton _)
    rw [mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    calc f * e * f⁻¹ * (f * (z : G) * f⁻¹) = f * (e * (z : G)) * f⁻¹ := by group
      _ = f * ((z : G) * e) * f⁻¹ := by rw [hz]
      _ = f * (z : G) * f⁻¹ * (f * e * f⁻¹) := by group

section M12Facts

theorem u1P_mem_M12 : u1P ∈ NativeSporadic.M12 := by
  rw [← mP_conj]
  exact mul_mem (mul_mem (inv_mem mP_mem_M12) Jelt.2) (inv_mem (inv_mem mP_mem_M12))

@[expose] def u1G12 : G12 := ⟨u1P, u1P_mem_M12⟩

@[expose] def nG12 : G12 := (⟨mP, mP_mem_M12⟩ : G12)⁻¹

theorem nG12_conj : nG12 * Jelt * nG12⁻¹ = u1G12 := by
  apply Subtype.ext
  simp only [nG12, u1G12, Subgroup.coe_mul, Subgroup.coe_inv]
  exact mP_conj

theorem u1G12_comm : u1G12 * Jelt = Jelt * u1G12 := Subtype.ext u1P_comm_bfJ

end M12Facts

section Bad

variable {G : Type} [Group G] {e : G}
variable (e₀ : centralizer ({e} : Set G) ≃* Multiplicative (ZMod 2) × G12)

set_option linter.unusedSectionVars false

@[expose, irreducible] noncomputable def xG : G := jH e₀ (Multiplicative.ofAdd 1, u1G12)

theorem xG_def : xG e₀ = jH e₀ (Multiplicative.ofAdd 1, u1G12) := by unfold xG; rfl

theorem xG_mem_Hc : xG e₀ ∈ HcG e₀ := by
  rw [xG_def]
  exact jH_mem_Hc e₀ _ _ u1G12_comm

include e₀ in
theorem card_cent_e : Nat.card (centralizer ({e} : Set G)) = 2 ^ 7 * 1485 := by
  rw [Nat.card_congr e₀.toEquiv, Nat.card_prod, card_G12]
  have : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  rw [this]
  norm_num

theorem ΘE_xG : (ΘE e₀ ⟨xG e₀, xG_mem_Hc e₀⟩ : Equiv.Perm (Fin 14)) =
    CFSG.Sporadic.SmallOddCore.tp 14 tauT * CFSG.Sporadic.SmallOddCore.tp 14 u1T := by
  rw [u_coe, ΘE_coe, ρH_apply]
  have hx : (⟨xG e₀, (xG_mem_Hc e₀).1⟩ : centralizer ({e} : Set G)) =
      ⟨jH e₀ (Multiplicative.ofAdd 1, u1G12), (mem_range_jH e₀).1 ⟨_, rfl⟩⟩ :=
    Subtype.ext (xG_def e₀)
  rw [hx, e₀_jH]
  show kapP (Multiplicative.ofAdd 1, u1P) = _
  rw [kapP_apply, tauPow_ofAdd_one]

theorem exists_conj_x (he2 : orderOf e = 2) {d : G} (hd : IsSwap e₀ d) :
    ∃ f : G, f * e * f⁻¹ = xG e₀ := by
  set n : G := ιH e₀ nG12 with hn
  refine ⟨n * d, ?_⟩
  have h1 : n * e * n⁻¹ = e := by
    have := ιH_comm_e e₀ nG12
    rw [hn, this]
    group
  have h2 : n * cG e₀ * n⁻¹ = ιH e₀ u1G12 := by
    rw [hn, cG_def, ← map_inv, ← map_mul, ← map_mul, nG12_conj]
  have he : e = jH e₀ (Multiplicative.ofAdd 1, 1) := e_eq_jH e₀ he2
  calc n * d * e * (n * d)⁻¹ = n * (d * e * d⁻¹) * n⁻¹ := by group
    _ = n * (e * cG e₀) * n⁻¹ := by rw [hd.1]
    _ = (n * e * n⁻¹) * (n * cG e₀ * n⁻¹) := by group
    _ = e * ιH e₀ u1G12 := by rw [h1, h2]
    _ = jH e₀ (Multiplicative.ofAdd 1, 1) * jH e₀ (1, u1G12) := by
        rw [← he]; rfl
    _ = jH e₀ ((Multiplicative.ofAdd 1, 1) * (1, u1G12)) := (map_mul _ _ _).symm
    _ = xG e₀ := by rw [xG_def]; simp

@[expose] noncomputable def θG : ↥yK →* G := (HcG e₀).subtype.comp (ΘE e₀).symm.toMonoidHom

theorem θG_injective : Function.Injective (θG e₀) :=
  Subtype.val_injective.comp (ΘE e₀).symm.injective

theorem θG_mem_Hc (z : ↥yK) : θG e₀ z ∈ HcG e₀ := ((ΘE e₀).symm z).2

@[expose] noncomputable def uY : ↥yK := ΘE e₀ ⟨xG e₀, xG_mem_Hc e₀⟩

theorem xG_eq_θG : xG e₀ = θG e₀ (uY e₀) := by
  simp [θG, uY]

theorem conj_θG {d : G} (hd : IsSwap e₀ d) (z : ↥yK) :
    d * θG e₀ z * d⁻¹ = θG e₀ (swapAut hd z) := by
  have h1 := swapAut_symm_apply hd z
  have := congrArg (fun w : ↥(HcG e₀) => (w : G)) h1
  simpa [θG, conjHc_coe] using this.symm

theorem conj_θG_mul {d : G} (hd : IsSwap e₀ d) (z : ↥yK) :
    d * θG e₀ z = θG e₀ (swapAut hd z) * d := by
  rw [← conj_θG e₀ hd]
  group

@[expose] noncomputable def TG : Subgroup G := tK.map (θG e₀)

theorem θG_mem_TG {z : ↥yK} (hz : z ∈ tK) : θG e₀ z ∈ TG e₀ := ⟨z, hz, rfl⟩

theorem card_TG : Nat.card (TG e₀) = 128 := by
  rw [TG, Subgroup.card_map_of_injective (θG_injective e₀), card_tK]

theorem d_not_mem_Hc {d : G} (hd : IsSwap e₀ d) : d ∉ HcG e₀ := by
  intro h
  have hcomm := mem_centralizer_iff.1 h.1 e (Set.mem_singleton e)
  have h1 : d * e * d⁻¹ = e := by
    rw [← hcomm]
    group
  have h2 : e * cG e₀ = e * 1 := by rw [mul_one, ← hd.1, h1]
  exact cG_ne_one e₀ (mul_left_cancel h2)

noncomputable def Tstar {d : G} (hdd : d * d = 1) (hn : ∀ y ∈ TG e₀, d * y * d⁻¹ ∈ TG e₀) :
    Subgroup G where
  carrier := {y | ∃ t ∈ TG e₀, y = t ∨ y = t * d}
  one_mem' := ⟨1, one_mem _, Or.inl rfl⟩
  mul_mem' := by
    rintro x y ⟨t₁, ht₁, h₁⟩ ⟨t₂, ht₂, h₂⟩
    have hdi : d⁻¹ = d := inv_eq_of_mul_eq_one_right hdd
    have hc := hn t₂ ht₂
    rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂ <;> rw [h₁, h₂]
    · exact ⟨t₁ * t₂, mul_mem ht₁ ht₂, Or.inl rfl⟩
    · exact ⟨t₁ * t₂, mul_mem ht₁ ht₂, Or.inr (by group)⟩
    · exact ⟨t₁ * (d * t₂ * d⁻¹), mul_mem ht₁ hc, Or.inr (by group)⟩
    · refine ⟨t₁ * (d * t₂ * d⁻¹), mul_mem ht₁ hc, Or.inl ?_⟩
      calc t₁ * d * (t₂ * d) = t₁ * (d * t₂ * d) := by group
        _ = t₁ * (d * t₂ * d⁻¹) := by rw [hdi]
  inv_mem' := by
    rintro x ⟨t, ht, h⟩
    have hdi : d⁻¹ = d := inv_eq_of_mul_eq_one_right hdd
    rcases h with h | h <;> rw [h]
    · exact ⟨t⁻¹, inv_mem ht, Or.inl rfl⟩
    · refine ⟨d * t⁻¹ * d⁻¹, hn _ (inv_mem ht), Or.inr ?_⟩
      calc (t * d)⁻¹ = d⁻¹ * t⁻¹ := mul_inv_rev _ _
        _ = d * t⁻¹ := by rw [hdi]
        _ = d * t⁻¹ * d⁻¹ * d := by group

noncomputable def T1 {d : G} (hdd : d * d = 1) (hn : ∀ y ∈ TG e₀, d * y * d⁻¹ ∈ TG e₀) :
    Subgroup G := Tstar e₀ hdd hn ⊓ centralizer ({xG e₀} : Set G)

theorem comm_xG_iff {z : ↥yK} :
    xG e₀ * θG e₀ z = θG e₀ z * xG e₀ ↔ z * uY e₀ = uY e₀ * z := by
  rw [xG_eq_θG, ← map_mul, ← map_mul]
  exact ⟨fun h => (θG_injective e₀ h).symm, fun h => by rw [h]⟩

theorem comm_xG_mul_iff {d : G} (hd : IsSwap e₀ d) {z : ↥yK} :
    xG e₀ * (θG e₀ z * d) = θG e₀ z * d * xG e₀ ↔ z * swapAut hd (uY e₀) = uY e₀ * z := by
  have e1 : θG e₀ z * d * xG e₀ = θG e₀ (z * swapAut hd (uY e₀)) * d := by
    rw [xG_eq_θG, mul_assoc, conj_θG_mul e₀ hd, map_mul, mul_assoc]
  have e2 : xG e₀ * (θG e₀ z * d) = θG e₀ (uY e₀ * z) * d := by
    rw [xG_eq_θG, map_mul, mul_assoc]
  rw [e1, e2]
  exact ⟨fun h => (θG_injective e₀ (mul_right_cancel h)).symm, fun h => by rw [h]⟩

theorem sq_θG_mul {d : G} (hd : IsSwap e₀ d) (hdd : d * d = 1) (z : ↥yK) :
    θG e₀ z * d * (θG e₀ z * d) = θG e₀ (z * swapAut hd z) := by
  rw [map_mul, ← conj_θG e₀ hd]
  calc θG e₀ z * d * (θG e₀ z * d) = θG e₀ z * (d * θG e₀ z * d⁻¹) * (d * d) := by group
    _ = θG e₀ z * (d * θG e₀ z * d⁻¹) := by rw [hdd, mul_one]

theorem T1_pow4 {d : G} (hd : IsSwap e₀ d) (hdd : d * d = 1)
    (hn : ∀ y ∈ TG e₀, d * y * d⁻¹ ∈ TG e₀) (hS : Spec.SwapType (swapAut hd) (uY e₀)) {y : G}
    (hy : y ∈ T1 e₀ hdd hn) : y ^ 4 = 1 := by
  obtain ⟨hyS, hyC⟩ := hy
  obtain ⟨t, ht, hyt⟩ := hyS
  obtain ⟨z, hz, rfl⟩ := ht
  have hx : xG e₀ * y = y * xG e₀ := mem_centralizer_iff.1 hyC (xG e₀) (Set.mem_singleton _)
  rcases hyt with rfl | rfl
  · have h1 := (comm_xG_iff e₀).1 hx
    have h2 := hS.2.1 z (mem_tK_iff.1 hz) h1
    rw [← map_pow, h2, map_one]
  · have h1 := (comm_xG_mul_iff e₀ hd).1 hx
    have h2 := hS.2.2 z (mem_tK_iff.1 hz) h1
    rw [pow_four_eq, sq_θG_mul e₀ hd hdd, ← map_mul, ← pow_two, h2, map_one]

theorem card_T1 [Finite G] {d : G} (hd : IsSwap e₀ d) (hdd : d * d = 1)
    (hn : ∀ y ∈ TG e₀, d * y * d⁻¹ ∈ TG e₀) (hS : Spec.SwapType (swapAut hd) (uY e₀)) :
    128 ≤ Nat.card (T1 e₀ hdd hn) := by
  set u := uY e₀ with hu
  let A := {t : ↥yK // (t : Equiv.Perm (Fin 14)) ∈ Spec.tK ∧ t * u = u * t}
  let B := {t : ↥yK // (t : Equiv.Perm (Fin 14)) ∈ Spec.tK ∧ t * swapAut hd u = u * t}
  have hmA : ∀ t : A, θG e₀ t.1 ∈ T1 e₀ hdd hn := fun t =>
    ⟨⟨θG e₀ t.1, θG_mem_TG e₀ (mem_tK_iff.2 t.2.1), Or.inl rfl⟩,
      mem_centralizer_iff.2 fun h hh => by
        rw [Set.mem_singleton_iff] at hh
        rw [hh]
        exact (comm_xG_iff e₀).2 t.2.2⟩
  have hmB : ∀ t : B, θG e₀ t.1 * d ∈ T1 e₀ hdd hn := fun t =>
    ⟨⟨θG e₀ t.1, θG_mem_TG e₀ (mem_tK_iff.2 t.2.1), Or.inr rfl⟩,
      mem_centralizer_iff.2 fun h hh => by
        rw [Set.mem_singleton_iff] at hh
        rw [hh]
        exact (comm_xG_mul_iff e₀ hd).2 t.2.2⟩
  let f : A ⊕ B → ↥(T1 e₀ hdd hn) := fun s => match s with
    | Sum.inl t => ⟨θG e₀ t.1, hmA t⟩
    | Sum.inr t => ⟨θG e₀ t.1 * d, hmB t⟩
  have hf : Function.Injective f := by
    have hne : ∀ a b : ↥yK, θG e₀ a ≠ θG e₀ b * d := fun a b hab => by
      apply d_not_mem_Hc e₀ hd
      have hd' : d = (θG e₀ b)⁻¹ * θG e₀ a := by rw [hab]; group
      rw [hd']
      exact mul_mem (inv_mem (θG_mem_Hc e₀ b)) (θG_mem_Hc e₀ a)
    rintro (a | a) (b | b) hab <;> have hab' := congrArg Subtype.val hab
    · exact congrArg Sum.inl (Subtype.ext (θG_injective e₀ hab'))
    · exact absurd hab' (hne _ _)
    · exact absurd hab'.symm (hne _ _)
    · exact congrArg Sum.inr (Subtype.ext (θG_injective e₀ (mul_right_cancel hab')))
  calc 128 = Nat.card A + Nat.card B := hS.1.symm
    _ = Nat.card (A ⊕ B) := (Nat.card_sum).symm
    _ ≤ Nat.card (T1 e₀ hdd hn) := Nat.card_le_card_of_injective f hf

noncomputable def QG (f : G) : Subgroup G := (TG e₀).map (MulAut.conj f).toMonoidHom

theorem QG_le_centralizer {f : G} (hf : f * e * f⁻¹ = xG e₀) :
    QG e₀ f ≤ centralizer ({xG e₀} : Set G) := by
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨z, -, rfl⟩ := hy
  rw [mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  have hye : e * θG e₀ z = θG e₀ z * e :=
    mem_centralizer_iff.1 (θG_mem_Hc e₀ z).1 e (Set.mem_singleton e)
  rw [hh, ← hf]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  calc f * e * f⁻¹ * (f * θG e₀ z * f⁻¹) = f * (e * θG e₀ z) * f⁻¹ := by group
    _ = f * (θG e₀ z * e) * f⁻¹ := by rw [hye]
    _ = f * θG e₀ z * f⁻¹ * (f * e * f⁻¹) := by group

theorem no_bad_swap [Finite G] (he2 : orderOf e = 2) {d : G} (hd : IsSwap e₀ d) (hdd : d * d = 1)
    (hds : d * sG e₀ * d⁻¹ = sG e₀)
    (hsw : ∀ u : ↥yK, (u : Equiv.Perm (Fin 14)) =
      CFSG.Sporadic.SmallOddCore.tp 14 tauT * CFSG.Sporadic.SmallOddCore.tp 14 u1T →
        Spec.SwapType (swapAut hd) u) : False := by
  have hS := hsw (uY e₀) (ΘE_xG e₀)
  obtain ⟨f, hf⟩ := exists_conj_x e₀ he2 hd
  have hn : ∀ y ∈ TG e₀, d * y * d⁻¹ ∈ TG e₀ := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := hy
    rw [conj_θG e₀ hd]
    exact ⟨swapAut hd z, swap_preserves_tK (swapAut hd) (swapAut_e e₀ he2 hd) (swapAut_c e₀ hd)
      (swapAut_s e₀ hd hds) (swapAut_inv e₀ hd hdd) hz, rfl⟩
  have hCcard : Nat.card (centralizer ({xG e₀} : Set G)) = 2 ^ 7 * 1485 := by
    rw [← hf, card_centralizer_conj, card_cent_e e₀]
  have hT1le : T1 e₀ hdd hn ≤ centralizer ({xG e₀} : Set G) := inf_le_right
  have hQle := QG_le_centralizer e₀ hf
  obtain ⟨t₀, ht₀, h8⟩ := exists_order_eight
  have hy8 : θG e₀ t₀ ^ 4 ≠ 1 := by
    intro h
    apply h8
    apply θG_injective e₀
    rw [map_pow, map_one]
    exact h
  have hyQ : f * θG e₀ t₀ * f⁻¹ ∈ centralizer ({xG e₀} : Set G) :=
    hQle ⟨θG e₀ t₀, θG_mem_TG e₀ ht₀, rfl⟩
  refine no_order_eight_of_sylow (k := 7) (m := 1485) (by decide) hCcard
    ((T1 e₀ hdd hn).subgroupOf _) ((QG e₀ f).subgroupOf _) ?_ ?_ ?_
    (y₀ := ⟨f * θG e₀ t₀ * f⁻¹, hyQ⟩) ?_ ?_
  · intro y hy
    apply Subtype.ext
    simpa using T1_pow4 e₀ hd hdd hn hS (Subgroup.mem_subgroupOf.1 hy)
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT1le).toEquiv]
    calc 2 ^ 7 = 128 := by norm_num
      _ ≤ _ := card_T1 e₀ hd hdd hn hS
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQle).toEquiv, QG,
      Subgroup.card_map_of_injective (f := (MulAut.conj f).toMonoidHom)
        (MulAut.conj f).injective, card_TG]
    norm_num
  · rw [Subgroup.mem_subgroupOf]
    exact ⟨θG e₀ t₀, θG_mem_TG e₀ ht₀, rfl⟩
  · intro h
    apply hy8
    have h1 := congrArg Subtype.val h
    have h2 : f * θG e₀ t₀ ^ 4 * f⁻¹ = 1 := by
      simpa [conj_pow] using h1
    calc θG e₀ t₀ ^ 4 = f⁻¹ * (f * θG e₀ t₀ ^ 4 * f⁻¹) * f := by group
      _ = 1 := by rw [h2]; group

end Bad

end CFSG.EvenSporadicStandard.M12Std.Yosh
