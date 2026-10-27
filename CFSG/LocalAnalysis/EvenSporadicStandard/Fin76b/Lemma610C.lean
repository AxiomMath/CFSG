module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Lemma610B

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

theorem ncard_modEq_fixed_conj {G : Type*} [Group G] {O : Set G} (hO : O.Finite) {y : G}
    (hy5 : y ^ 5 = 1) (h1 : ∀ u ∈ O, y * u * y⁻¹ ∈ O) (h2 : ∀ u ∈ O, y⁻¹ * u * y ∈ O) :
    O.ncard ≡ {u | u ∈ O ∧ y * u * y⁻¹ = u}.ncard [MOD 5] := by
  classical
  haveI : Finite ↥O := hO.to_subtype
  let σ : Equiv.Perm ↥O :=
    { toFun := fun u => ⟨y * u * y⁻¹, h1 u u.2⟩
      invFun := fun u => ⟨y⁻¹ * u * y, h2 u u.2⟩
      left_inv := fun u => Subtype.ext (by simp only; group)
      right_inv := fun u => Subtype.ext (by simp only; group) }
  have hσk : ∀ (k : ℕ) (u : ↥O), (((σ ^ k) u : ↥O) : G) = y ^ k * u * (y ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro u; simp
    | succ k ih =>
      intro u
      rw [pow_succ, Equiv.Perm.mul_apply, ih]
      show y ^ k * (y * (u : G) * y⁻¹) * (y ^ k)⁻¹ = y ^ (k + 1) * u * (y ^ (k + 1))⁻¹
      rw [pow_succ]; group
  have hσ5 : σ ^ 5 = 1 := by
    ext u
    rw [hσk, hy5]
    simp
  have hmod := card_modEq_fixed σ hσ5
  have hfix : {u | u ∈ O ∧ y * u * y⁻¹ = u} = Subtype.val '' (Function.fixedPoints σ) := by
    ext u
    constructor
    · rintro ⟨hu, hfu⟩
      exact ⟨⟨u, hu⟩, Subtype.ext hfu, rfl⟩
    · rintro ⟨⟨u, hu⟩, hfu, rfl⟩
      exact ⟨hu, congrArg Subtype.val hfu⟩
  rw [hfix, Set.ncard_image_of_injective _ Subtype.val_injective]
  rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq] at hmod
  exact hmod

namespace Hyp69

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T₀ E : Subgroup G}
  {Q : Sylow 2 G} {x β : G} {B : Subgroup G} {S : Subgroup G}
  (h : Hyp69 L z t T₀ E Q x β B S)

include h

theorem fix_X {α : G} (hα : AlphaSpec S z t α) {y : G} (hyB : y ∈ B) (hy5 : orderOf y = 5)
    {u : G} (hu : u ∈ XSet S E z) (hfix : y * u * y⁻¹ = u) : u = z ∨ u = z * t := by
  have hyz : y * z = z * y := h.BS y hyB z h.zS
  have hyα : y * α = α * y := h.BS y hyB α hα.mem
  rw [h.X_eq hα] at hu
  rcases hu with (hu | hu) | hu
  · obtain ⟨e, he, rfl⟩ := hu
    change z * e = z ∨ z * e = z * t
    rcases he with he | he
    · left; rw [he, mul_one]
    · right; rw [he]
  · obtain ⟨e, he, rfl⟩ := hu
    have hfe : y * e * y⁻¹ = e := by
      have h1 : y * (z * e) * y⁻¹ = z * (y * e * y⁻¹) := by
        calc y * (z * e) * y⁻¹ = (y * z) * e * y⁻¹ := by group
          _ = (z * y) * e * y⁻¹ := by rw [hyz]
          _ = z * (y * e * y⁻¹) := by group
      rw [h1] at hfix
      exact mul_left_cancel hfix
    rcases h.fix_E hyB hy5 he.1 hfe with h1 | h1
    · exact absurd h1 he.2.2.1
    · exact absurd h1 he.2.2.2
  · obtain ⟨e, he, rfl⟩ := hu
    have hfe : y * e * y⁻¹ = e := by
      have h1 : y * (α * z * e) * y⁻¹ = (α * z) * (y * e * y⁻¹) := by
        calc y * (α * z * e) * y⁻¹ = (y * α) * z * e * y⁻¹ := by group
          _ = (α * y) * z * e * y⁻¹ := by rw [hyα]
          _ = α * (y * z) * e * y⁻¹ := by group
          _ = α * (z * y) * e * y⁻¹ := by rw [hyz]
          _ = (α * z) * (y * e * y⁻¹) := by group
      rw [h1] at hfix
      exact mul_left_cancel hfix
    exfalso
    rcases h.fix_E hyB hy5 he.1 hfe with h1 | h1
    · rw [h1] at he
      exact h.t_ne (by rw [← he.2]; group)
    · rw [h1] at he
      have := he.2
      rw [h.t_sq] at this
      exact h.t_ne this.symm

theorem Oz_sub_X {α : G} (hα : AlphaSpec S z t α) {u : G}
    (hu : u ∈ {u : G | ∃ f ∈ Fsub h hα, u = f * z * f⁻¹}) : u ∈ XSet S E z := by
  obtain ⟨f, hf, rfl⟩ := hu
  exact h.X_inv hf.1 h.z_mem_X

theorem CFz_eq {α : G} (hα : AlphaSpec S z t α) :
    Fsub h hα ⊓ centralizer ({z} : Set G) = E ⊔ zpowers z := by
  have hzF : z ∈ Fsub h hα := h.U_le_Fsub hα (mem_sup_left h.zS)
  apply le_antisymm
  · rintro m ⟨hmF, hmc⟩
    have hmz : m * z = z * m := mem_centralizer_singleton_iff.1 hmc
    obtain ⟨w, hw, hmw⟩ := h.cent_z_mem_M hmF.1 hmz
    obtain ⟨b, hb, e, he, rfl⟩ := h.W_decomp hw
    have heF : e ∈ Fsub h hα := h.U_le_Fsub hα (mem_sup_right he)
    rcases hmw with hm | hm
    · have hbF : b ∈ Fsub h hα := by
        have : b = m * e⁻¹ := by rw [hm]; group
        rw [this]; exact mul_mem hmF (inv_mem heF)
      have hb1 := h.B_inf_F hα hb hbF
      rw [hm, hb1, one_mul]
      exact mem_sup_left he
    · have hbF : b ∈ Fsub h hα := by
        have : b = m * z⁻¹ * e⁻¹ := by rw [hm]; group
        rw [this]; exact mul_mem (mul_mem hmF (inv_mem hzF)) (inv_mem heF)
      have hb1 := h.B_inf_F hα hb hbF
      rw [hm, hb1, one_mul]
      exact mul_mem (mem_sup_left he) (mem_sup_right (mem_zpowers z))
  · refine sup_le ?_ ?_
    · intro e he
      exact ⟨h.U_le_Fsub hα (mem_sup_right he),
        mem_centralizer_singleton_iff.2 (h.S_comm_E z h.zS e he).symm⟩
    · rw [zpowers_le]
      exact ⟨hzF, mem_centralizer_singleton_iff.2 rfl⟩

theorem card_CFz {α : G} (hα : AlphaSpec S z t α) :
    Nat.card ↥(Fsub h hα ⊓ centralizer ({z} : Set G)) = 64 := by
  rw [h.CFz_eq hα]
  have hAB : zpowers z ≤ centralizer (E : Set G) := by
    rw [zpowers_le]
    exact mem_centralizer_iff.2 fun e he => (h.S_comm_E z h.zS e he).symm
  have hd : Disjoint E (zpowers z) := by
    rw [Subgroup.disjoint_def]
    intro x hxE hxz
    rcases mem_zpowers_sq_eq_one h.z_sq hxz with h1 | h1
    · exact h1
    · exfalso
      rw [h1] at hxE
      rcases h.S_inf_E h.zS hxE with h2 | h2
      · exact h.z_ne h2
      · exact h.z_ne_t h2
  have e := mulEquivProdSup hAB hd
  rw [← Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_zpowers, h.conf.cfg.z_order,
    h.wf.card_E]

theorem card_Oz_modEq {α : G} (hα : AlphaSpec S z t α) {y : G} (hyB : y ∈ B)
    (hy5 : orderOf y = 5) :
    Set.ncard {u : G | ∃ f ∈ Fsub h hα, u = f * z * f⁻¹} ≡ 2 [MOD 5] := by
  set O : Set G := {u : G | ∃ f ∈ Fsub h hα, u = f * z * f⁻¹} with hO
  have hyW := h.B_le_W hyB
  have hyt : y * t = t * y := mem_centralizer_singleton_iff.1 hyW.2
  have hyz : y * z = z * y := h.BS y hyB z h.zS
  have hOB : ∀ b ∈ B, ∀ u ∈ O, b * u * b⁻¹ ∈ O := by
    rintro b hb u ⟨f, hf, rfl⟩
    have hbz : b * z * b⁻¹ = z := by
      calc b * z * b⁻¹ = (z * b) * b⁻¹ := by rw [h.BS b hb z h.zS]
        _ = z := by group
    refine ⟨b * f * b⁻¹, h.Fsub_normal hα (h.W_mem_M (h.B_le_W hb)) hf, ?_⟩
    calc b * (f * z * f⁻¹) * b⁻¹ = (b * f * b⁻¹) * (b * z * b⁻¹) * (b * f * b⁻¹)⁻¹ := by group
      _ = (b * f * b⁻¹) * z * (b * f * b⁻¹)⁻¹ := by rw [hbz]
  have hO1 : ∀ u ∈ O, y * u * y⁻¹ ∈ O := fun u hu => hOB y hyB u hu
  have hO2 : ∀ u ∈ O, y⁻¹ * u * y ∈ O := fun u hu => by
    simpa using hOB y⁻¹ (inv_mem hyB) u hu
  have hy5' : y ^ 5 = 1 := by
    have := pow_orderOf_eq_one y
    rwa [hy5] at this
  have hmod := ncard_modEq_fixed_conj (Set.toFinite O) hy5' hO1 hO2
  have hzO : z ∈ O := ⟨1, one_mem _, by group⟩
  have hztO : z * t ∈ O :=
    ⟨α, h.U_le_Fsub hα (mem_sup_left hα.mem), (h.alpha_conj_z hα).symm⟩
  have hfixset : {u | u ∈ O ∧ y * u * y⁻¹ = u} = {z, z * t} := by
    ext u
    constructor
    · rintro ⟨hu, hfu⟩
      have := h.fix_X hα hyB hy5 (h.Oz_sub_X hα hu) hfu
      simpa using this
    · intro hu
      rcases hu with hu | hu
      · rw [hu]
        refine ⟨hzO, ?_⟩
        calc y * z * y⁻¹ = (z * y) * y⁻¹ := by rw [hyz]
          _ = z := by group
      · rw [Set.mem_singleton_iff] at hu
        rw [hu]
        refine ⟨hztO, ?_⟩
        calc y * (z * t) * y⁻¹ = (y * z) * t * y⁻¹ := by group
          _ = (z * y) * t * y⁻¹ := by rw [hyz]
          _ = z * (y * t) * y⁻¹ := by group
          _ = z * (t * y) * y⁻¹ := by rw [hyt]
          _ = z * t := by group
  have hne : z ≠ z * t := fun h1 => h.t_ne (mul_left_cancel ((mul_one z).trans h1)).symm
  rw [hfixset, Set.ncard_pair hne] at hmod
  exact hmod

theorem card_Fsub {α : G} (hα : AlphaSpec S z t α) : Nat.card ↥(Fsub h hα) = 2048 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 5 (by rw [h.B_card]; norm_num :
    5 ∣ Nat.card ↥B)
  have hy5 : orderOf (y : G) = 5 := by rw [← Subgroup.orderOf_coe] at hy; exact hy
  have hmod := h.card_Oz_modEq hα y.2 hy5
  have horb := card_conj_orbit_mul_card_cent (Fsub h hα) z
  rw [h.card_CFz hα] at horb
  have hX : Set.ncard {u : G | ∃ f ∈ Fsub h hα, u = f * z * f⁻¹} ≤ 32 := by
    rw [← h.X_card hα]
    exact Set.ncard_le_ncard (fun u hu => h.Oz_sub_X hα hu) (Set.toFinite _)
  have hM := h.card_M hα
  have hle := h.card_M_le_F hα
  have hdvd : Nat.card ↥(Fsub h hα) ∣
      Nat.card ↥(normalizer ((S ⊔ E : Subgroup G) : Set G)) :=
    Subgroup.card_dvd_of_le (h.Fsub_le_M hα)
  rw [hM] at hle hdvd
  set k := Set.ncard {u : G | ∃ f ∈ Fsub h hα, u = f * z * f⁻¹} with hk
  rw [← horb] at hle hdvd ⊢
  have hk16 : 16 ≤ k := by omega
  clear horb hk
  interval_cases k
  · exfalso; revert hmod; decide
  · exfalso; revert hdvd; decide
  · exfalso; revert hmod; decide
  · exfalso; revert hmod; decide
  · exfalso; revert hmod; decide
  · exfalso; revert hmod; decide
  · exfalso; revert hdvd; decide
  · exfalso; revert hmod; decide
  · exfalso; revert hmod; decide
  · exfalso; revert hmod; decide
  · exfalso; revert hmod; decide
  · exfalso; revert hdvd; decide
  · exfalso; revert hmod; decide
  · exfalso; revert hmod; decide
  · exfalso; revert hmod; decide
  · exfalso; revert hmod; decide
  · rfl

theorem F_pgroup {α : G} (hα : AlphaSpec S z t α) : IsPGroup 2 (Fsub h hα) :=
  IsPGroup.of_card (n := 11) (by rw [h.card_Fsub hα]; norm_num)

theorem M_eq_FB {α : G} (hα : AlphaSpec S z t α) {m : G}
    (hm : m ∈ normalizer ((S ⊔ E : Subgroup G) : Set G)) :
    ∃ f ∈ Fsub h hα, ∃ b ∈ B, m = f * b := by
  classical
  let φ : ↥(Fsub h hα) × ↥B → ↥(normalizer ((S ⊔ E : Subgroup G) : Set G)) := fun p =>
    ⟨(p.1 : G) * p.2, mul_mem (h.Fsub_le_M hα p.1.2) (h.W_mem_M (h.B_le_W p.2.2))⟩
  have hinj : Function.Injective φ := by
    rintro ⟨f, b⟩ ⟨f', b'⟩ hφ
    have h1 : (f : G) * b = f' * b' := congrArg Subtype.val hφ
    have h2 : ((f' : G)⁻¹ * f : G) = b' * (b : G)⁻¹ := by
      calc (f' : G)⁻¹ * f = (f' : G)⁻¹ * (f * b) * (b : G)⁻¹ := by group
        _ = (f' : G)⁻¹ * (f' * b') * (b : G)⁻¹ := by rw [h1]
        _ = b' * (b : G)⁻¹ := by group
    have hbB : (b' : G) * (b : G)⁻¹ ∈ B := mul_mem b'.2 (inv_mem b.2)
    have hbF : (b' : G) * (b : G)⁻¹ ∈ Fsub h hα := by
      rw [← h2]; exact mul_mem (inv_mem f'.2) f.2
    have h3 := h.B_inf_F hα hbB hbF
    have hb : (b' : G) = b := by
      calc (b' : G) = (b' * (b : G)⁻¹) * b := by group
        _ = b := by rw [h3, one_mul]
    have hf : (f : G) = f' := by
      calc (f : G) = f' * ((f' : G)⁻¹ * f) := by group
        _ = f' := by rw [h2, h3, mul_one]
    have e1 : f = f' := Subtype.ext hf
    have e2 : b = b' := Subtype.ext hb.symm
    rw [e1, e2]
  have hcard : Nat.card ↥(normalizer ((S ⊔ E : Subgroup G) : Set G)) ≤
      Nat.card (↥(Fsub h hα) × ↥B) := by
    rw [Nat.card_prod, h.card_Fsub hα, h.B_card, h.card_M hα]
  have hbij := hinj.bijective_of_nat_card_le hcard
  obtain ⟨⟨f, b⟩, hfb⟩ := hbij.2 ⟨m, hm⟩
  exact ⟨f, f.2, b, b.2, (congrArg Subtype.val hfb).symm⟩

theorem alpha_orbit_F {α : G} (hα : AlphaSpec S z t α) :
    {u : G | ∃ f ∈ Fsub h hα, u = f * α * f⁻¹} = {α, α * t} := by
  ext u
  constructor
  · rintro ⟨f, hf, rfl⟩
    rcases h.alpha_orbit hα hf.1 with h1 | h1
    · left; exact h1
    · right; exact h1
  · rintro (rfl | rfl)
    · exact ⟨1, one_mem _, by group⟩
    · refine ⟨z, h.U_le_Fsub hα (mem_sup_left h.zS), ?_⟩
      exact (h.z_conj_alpha hα).symm

theorem card_QF {α : G} (hα : AlphaSpec S z t α) :
    Nat.card ↥(Fsub h hα ⊓ centralizer ({α} : Set G)) = 1024 := by
  have horb := card_conj_orbit_mul_card_cent (Fsub h hα) α
  rw [h.alpha_orbit_F hα, Set.ncard_pair (fun h1 => h.t_ne
    (mul_left_cancel ((mul_one α).trans h1)).symm), h.card_Fsub hα] at horb
  omega

end Hyp69

end CFSG.EvenSporadicStandard.Fin76b
