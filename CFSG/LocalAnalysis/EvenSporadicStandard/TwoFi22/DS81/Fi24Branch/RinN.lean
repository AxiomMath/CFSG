module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Core

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open Subgroup

variable {G : Type} [Group G] [Finite G] {E : Subgroup G} {t z : G}

structure RPData (E : Subgroup G) (t z : G) : Prop where
  R_le_P : Rg t z ≤ Pg E z
  P_le_J : Pg E z ≤ Jg t z
  E_le_P : E ≤ Pg E z
  card_RE : Nat.card ↥(Rg t z ⊓ E) = 2 ^ 7
  P_decomp : ∀ p ∈ Pg E z, ∃ r ∈ Rg t z, ∃ e ∈ E, p = r * e

theorem E_comm (c : Core1 E t z) : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a :=
  sq_eq_one_comm c.m24.E_sq

theorem E_le_K (c : Core1 E t z) : E ≤ Kg t z := by
  intro e he
  rw [mem_Kg]
  exact ⟨E_comm c e he t c.m24.t_mem, E_comm c e he z c.isZ.1⟩

theorem card_sup_mul_card_inf_of_normal {X : Type*} [Group X] {A B : Subgroup X} [A.Normal] :
    Nat.card (A ⊔ B : Subgroup X) * Nat.card (A ⊓ B : Subgroup X) =
      Nat.card A * Nat.card B := by
  have h1 := Subgroup.relIndex_mul_card (H := A) (K := A ⊔ B)
  rw [Subgroup.relIndex_sup_left, inf_eq_left.mpr le_sup_left] at h1
  have h2 := Subgroup.relIndex_mul_card (H := A) (K := B)
  rw [← h1, ← h2]
  ring

theorem card_sup_mul_card_inf_of_le_normalizer {X : Type*} [Group X] {A B : Subgroup X}
    (hB : B ≤ normalizer (A : Set X)) :
    Nat.card (A ⊔ B : Subgroup X) * Nat.card (A ⊓ B : Subgroup X) =
      Nat.card A * Nat.card B := by
  set N := normalizer (A : Set X)
  have hAN : A ≤ N := le_normalizer
  have hN : (A.subgroupOf N).Normal := normal_in_normalizer
  haveI : (A.subgroupOf N).Normal := hN
  have h := card_sup_mul_card_inf_of_normal (A := A.subgroupOf N) (B := B.subgroupOf N)
  have hc : ∀ Y : Subgroup X, Y ≤ N → Nat.card (Y.subgroupOf N) = Nat.card Y := fun Y hY =>
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hY).toEquiv
  have hsup : A.subgroupOf N ⊔ B.subgroupOf N = (A ⊔ B).subgroupOf N := by
    apply Subgroup.map_injective N.subtype_injective
    rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hAN, inf_eq_left.mpr hB,
      inf_eq_left.mpr (sup_le hAN hB)]
  have hinf : A.subgroupOf N ⊓ B.subgroupOf N = (A ⊓ B).subgroupOf N :=
    Subgroup.ext fun _ => Iff.rfl
  rw [hsup, hinf, hc _ (sup_le hAN hB), hc _ (inf_le_left.trans hAN), hc A hAN, hc B hB] at h
  exact h

theorem mem_sup_of_le_normalizer {X : Type*} [Group X] {R E : Subgroup X}
    (h : R ≤ normalizer (E : Set X)) {p : X} :
    p ∈ R ⊔ E ↔ ∃ r ∈ R, ∃ e ∈ E, r * e = p := by
  constructor
  · intro hp
    rw [sup_eq_closure] at hp
    refine closure_induction ?_ ?_ ?_ ?_ hp
    · rintro x (hx | hx)
      · exact ⟨x, hx, 1, E.one_mem, by simp⟩
      · exact ⟨1, R.one_mem, x, hx, by simp⟩
    · exact ⟨1, R.one_mem, 1, E.one_mem, by simp⟩
    · rintro _ _ _ _ ⟨r₁, hr₁, e₁, he₁, rfl⟩ ⟨r₂, hr₂, e₂, he₂, rfl⟩
      have hconj : r₂⁻¹ * e₁ * r₂ ∈ E := by
        simpa using (mem_normalizer_iff.mp (h (R.inv_mem hr₂)) e₁).mp he₁
      exact ⟨r₁ * r₂, R.mul_mem hr₁ hr₂, (r₂⁻¹ * e₁ * r₂) * e₂,
        E.mul_mem hconj he₂, by group⟩
    · rintro _ _ ⟨r, hr, e, he, rfl⟩
      have hconj : r * e⁻¹ * r⁻¹ ∈ E :=
        (mem_normalizer_iff.mp (h hr) e⁻¹).mp (E.inv_mem he)
      exact ⟨r⁻¹, R.inv_mem hr, r * e⁻¹ * r⁻¹, hconj, by simp [mul_assoc]⟩
  · rintro ⟨r, hr, e, he, rfl⟩
    exact mul_mem_sup hr he

theorem le_of_normal_two_of_factorization {X : Type*} [Group X] [Finite X] {R H : Subgroup X}
    (hR : IsPGroup 2 R) (hRn : R.Normal)
    (hfac : (Nat.card H).factorization 2 = (Nat.card X).factorization 2) : R ≤ H := by
  haveI : R.Normal := hRn
  let P : Sylow 2 H := default
  have hPcard : Nat.card ↥(P : Subgroup H) = 2 ^ (Nat.card X).factorization 2 := by
    rw [Sylow.card_eq_multiplicity, hfac]
  have hP'card : Nat.card ↥((P : Subgroup H).map H.subtype) =
      2 ^ (Nat.card X).factorization 2 := by
    rw [Subgroup.card_map_of_injective H.subtype_injective, hPcard]
  have hle : R ≤ ((P : Subgroup H).map H.subtype : Subgroup X) := by
    have h := IsPGroup.le_sylow_of_normal hR
      (Sylow.ofCard (p := 2) ((P : Subgroup H).map H.subtype) hP'card)
    simpa only [Sylow.coe_ofCard] using h
  exact hle.trans (Subgroup.map_subtype_le (P : Subgroup H))

theorem rpData (c : Core1 E t z) : RPData E t z := by
  have hfacHN : (Nat.card ↥(Nrm E ⊓ Jg t z)).factorization 2 = 20 := by
    rw [c.cocode.card_NV, show 2 ^ 20 * 3 * 5 = 2 ^ 20 * (3 * 5) by ring]
    exact TwoB.factorization_two_pow_mul (by norm_num) (by norm_num)
  have card_J : Nat.card ↥(Jg t z) = 2 ^ 20 * (3 ^ 4 * 5) := by
    have h := Subgroup.relIndex_mul_card (H := Kg t z) (K := Jg t z)
    rw [inf_eq_left.mpr (Kg_le_Jg t z), c.jr.relIndex_KJ, c.kdata.card_K] at h
    rw [← h]
    ring
  have hfacJ : (Nat.card ↥(Jg t z)).factorization 2 = 20 := by
    rw [card_J]
    exact TwoB.factorization_two_pow_mul (by norm_num) (by norm_num)
  have hfac_sub : (Nat.card ↥((Nrm E ⊓ Jg t z).subgroupOf (Jg t z))).factorization 2 =
      (Nat.card ↥(Jg t z)).factorization 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : Nrm E ⊓ Jg t z ≤
      Jg t z)).toEquiv, hfacHN, hfacJ]
  have hR2 : IsPGroup 2 ((Rg t z).subgroupOf (Jg t z)) :=
    (IsPGroup.of_card (n := 13) c.jr.card_R).of_equiv
      (Subgroup.subgroupOfEquivOfLe (Rg_le_Jg t z)).symm
  have hRn : ((Rg t z).subgroupOf (Jg t z)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using
      c.jr.R_normal (g : G) g.2 (n : G) hn
  have hRsyl := le_of_normal_two_of_factorization (X := ↥(Jg t z))
    (R := (Rg t z).subgroupOf (Jg t z)) (H := (Nrm E ⊓ Jg t z).subgroupOf (Jg t z))
    hR2 hRn hfac_sub
  have hR_le_HN : Rg t z ≤ Nrm E ⊓ Jg t z := by
    calc Rg t z = ((Rg t z).subgroupOf (Jg t z)).map (Jg t z).subtype :=
          (Subgroup.map_subgroupOf_eq_of_le (Rg_le_Jg t z)).symm
      _ ≤ ((Nrm E ⊓ Jg t z).subgroupOf (Jg t z)).map (Jg t z).subtype :=
          Subgroup.map_mono hRsyl
      _ = Nrm E ⊓ Jg t z := Subgroup.map_subgroupOf_eq_of_le inf_le_right
  have hR_le_Nrm : Rg t z ≤ Nrm E := hR_le_HN.trans inf_le_left
  have hR_le_P : Rg t z ≤ Pg E z := by
    have hnormal : ((Rg t z).subgroupOf (Nrm E ⊓ Jg t z)).Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using
        c.jr.R_normal (g : G) g.2.2 (n : G) hn
    have hp : IsPGroup 2 (Rg t z) := IsPGroup.of_card (n := 13) c.jr.card_R
    have h := TwoB.le_O2In hR_le_HN hnormal hp
    rwa [c.cocode.O2_NV] at h
  have hP_le_J : Pg E z ≤ Jg t z := by
    rw [← c.cocode.O2_NV]
    exact (TwoB.O2In_le (Nrm E ⊓ Jg t z)).trans inf_le_right
  have hE_le_P : E ≤ Pg E z := by
    have hECz : E ≤ Cz z := by
      intro e he
      rw [mem_Cz]
      exact E_comm c e he z c.isZ.1
    have hVH : E ≤ CNz E z := le_inf Subgroup.le_normalizer hECz
    have hnormal : (E.subgroupOf (CNz E z)).Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact (mem_normalizer_iff.mp g.2.1 (n : G)).mp hn
    have hp : IsPGroup 2 E := IsPGroup.of_card (n := 11) c.m24.card_E
    exact TwoB.le_O2In hVH hnormal hp
  have hprod := card_sup_mul_card_inf_of_le_normalizer (A := E) (B := Rg t z) hR_le_Nrm
  have hprod' : Nat.card ↥(Rg t z ⊔ E) * Nat.card ↥(Rg t z ⊓ E) = 2 ^ 24 := by
    rw [sup_comm, inf_comm, c.m24.card_E, c.jr.card_R] at hprod
    rw [show (2 : ℕ) ^ 24 = 2 ^ 11 * 2 ^ 13 by norm_num]
    exact hprod
  have hRsup_le : Rg t z ⊔ E ≤ Pg E z := sup_le hR_le_P hE_le_P
  have hcard_sup_le : Nat.card ↥(Rg t z ⊔ E) ≤ 2 ^ 17 := by
    calc Nat.card ↥(Rg t z ⊔ E) ≤ Nat.card ↥(Pg E z) := Subgroup.card_le_of_le hRsup_le
      _ = 2 ^ 17 := c.cocode.card_P
  have hlow : 2 ^ 7 ≤ Nat.card ↥(Rg t z ⊓ E) := by
    have h1 : 2 ^ 17 * 2 ^ 7 ≤ 2 ^ 17 * Nat.card ↥(Rg t z ⊓ E) := by
      calc 2 ^ 17 * 2 ^ 7 = 2 ^ 24 := by norm_num
        _ = Nat.card ↥(Rg t z ⊔ E) * Nat.card ↥(Rg t z ⊓ E) := hprod'.symm
        _ ≤ 2 ^ 17 * Nat.card ↥(Rg t z ⊓ E) := Nat.mul_le_mul_right _ hcard_sup_le
    exact Nat.le_of_mul_le_mul_left h1 (by norm_num)
  have hup : Nat.card ↥(Rg t z ⊓ E) ≤ 2 ^ 7 := by
    refine c.kdata.rank (Rg t z ⊓ E) ?_ ?_ ?_
    · rw [← c.jr.R_inf_K]
      exact le_inf inf_le_left (inf_le_right.trans (E_le_K c))
    · intro b hb
      exact c.m24.E_sq b hb.2
    · intro a ha b hb
      exact E_comm c a ha.2 b hb.2
  have card_RE : Nat.card ↥(Rg t z ⊓ E) = 2 ^ 7 := le_antisymm hup hlow
  have hcard_sup : Nat.card ↥(Rg t z ⊔ E) = 2 ^ 17 := by
    have h := hprod'
    rw [card_RE] at h
    rw [show (2 : ℕ) ^ 24 = 2 ^ 17 * 2 ^ 7 by norm_num] at h
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h
  have hP_eq : Pg E z = Rg t z ⊔ E := by
    symm
    exact Subgroup.eq_of_le_of_card_ge hRsup_le (by rw [c.cocode.card_P, hcard_sup])
  exact
    { R_le_P := hR_le_P
      P_le_J := hP_le_J
      E_le_P := hE_le_P
      card_RE := card_RE
      P_decomp := fun p hp => by
        rw [hP_eq] at hp
        obtain ⟨r, hr, e, he, hre⟩ := (mem_sup_of_le_normalizer hR_le_Nrm).mp hp
        exact ⟨r, hr, e, he, hre.symm⟩ }

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
