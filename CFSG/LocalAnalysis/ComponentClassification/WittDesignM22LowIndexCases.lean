module

public import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22LowIndex
public meta import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22LowIndex
public import Certificates.Certificate2037
public import Certificates.Certificate2038
public import Certificates.Certificate2195
public import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22LowIndexCasesInputs
public import Certificates.Certificate2034
public import Certificates.Certificate2031
public import Certificates.Certificate2033
public import Certificates.Certificate3029
public import Certificates.Certificate2035

public noncomputable section

namespace CFSG.ComponentClassification.WittDesign

open MulAction
open scoped Pointwise

theorem mem_conj_smul_zpowers (g u z : M22) :
    z ∈ MulAut.conj g • Subgroup.zpowers u ↔ z ∈ Subgroup.zpowers (g * u * g⁻¹) := by
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, Subgroup.mem_zpowers_iff,
    Subgroup.mem_zpowers_iff]
  simp only [MulAut.smul_def, MulAut.conj_inv_apply]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [conj_zpow, hn]
    group
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [← hn, conj_zpow]
    group

theorem exists_zpowers_eq_conj {p m : ℕ} [Fact p.Prime] (hm : 443520 = p * m) (hpm : ¬p ∣ m)
    {x u : M22} (hx : orderOf x = p) (hu : orderOf u = p) :
    ∃ g : M22, Subgroup.zpowers x = Subgroup.zpowers (g * u * g⁻¹) := by
  obtain ⟨g, hg⟩ := exists_smul_eq M22 (sylowZpowers hm hpm u hu) (sylowZpowers hm hpm x hx)
  refine ⟨g, ?_⟩
  have h := congrArg (fun P : Sylow p M22 => (P : Subgroup M22)) hg
  simp only [coe_sylowZpowers] at h
  rw [← h, Sylow.smul_def, Sylow.pointwise_smul_def, coe_sylowZpowers]
  ext z
  exact mem_conj_smul_zpowers g u z

theorem conj_mem_normalizer {g n u : M22}
    (hn : n ∈ Subgroup.normalizer (Subgroup.zpowers u : Set M22)) :
    g * n * g⁻¹ ∈ Subgroup.normalizer (Subgroup.zpowers (g * u * g⁻¹) : Set M22) := by
  rw [mem_normalizer_zpowers_iff] at hn ⊢
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hn
  refine Subgroup.mem_zpowers_iff.2 ⟨j, ?_⟩
  rw [conj_zpow, hj]
  group

theorem w₁_mem_normalizer : w₁ ∈ Subgroup.normalizer (Subgroup.zpowers z₀ : Set M22) := by
  rw [mem_normalizer_iff_tables orderOf_z₀ coe_z₀ table_facts.2.1]
  refine ⟨9, fun x => ?_⟩
  rw [coe_w₁]
  exact table_facts.2.2.2.2.2.2.2.2.1 x

theorem c₄_mem_normalizer : c₄ ∈ Subgroup.normalizer (Subgroup.zpowers w₁ : Set M22) := by
  rw [mem_normalizer_iff_tables orderOf_w₁ coe_w₁ table_facts.2.2.1]
  refine ⟨2, fun x => ?_⟩
  rw [coe_c₄]
  exact table_facts.2.2.2.2.2.2.2.2.2 x

theorem card_normalizer_of_orderOf_eleven {x : M22} (hx : orderOf x = 11) :
    Nat.card (Subgroup.normalizer (Subgroup.zpowers x : Set M22)) = 55 := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have h := card_normalizer_sylow (sylowZpowers (m := 40320) (by norm_num) (by norm_num) x hx)
    (sylowZpowers (m := 40320) (by norm_num) (by norm_num) z₀ orderOf_z₀)
  change Nat.card (Subgroup.normalizer (Subgroup.zpowers x : Set M22)) =
    Nat.card (Subgroup.normalizer (Subgroup.zpowers z₀ : Set M22)) at h
  rw [h, card_normalizer_z₀]

theorem card_normalizer_of_orderOf_seven {x : M22} (hx : orderOf x = 7) :
    Nat.card (Subgroup.normalizer (Subgroup.zpowers x : Set M22)) = 21 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have h := card_normalizer_sylow (sylowZpowers (m := 63360) (by norm_num) (by norm_num) x hx)
    (sylowZpowers (m := 63360) (by norm_num) (by norm_num) y₀ orderOf_y₀)
  change Nat.card (Subgroup.normalizer (Subgroup.zpowers x : Set M22)) =
    Nat.card (Subgroup.normalizer (Subgroup.zpowers y₀ : Set M22)) at h
  rw [h, card_normalizer_y₀]

theorem card_normalizer_of_orderOf_five {x : M22} (hx : orderOf x = 5) :
    Nat.card (Subgroup.normalizer (Subgroup.zpowers x : Set M22)) = 20 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h := card_normalizer_sylow (sylowZpowers (m := 88704) (by norm_num) (by norm_num) x hx)
    (sylowZpowers (m := 88704) (by norm_num) (by norm_num) w₁ orderOf_w₁)
  change Nat.card (Subgroup.normalizer (Subgroup.zpowers x : Set M22)) =
    Nat.card (Subgroup.normalizer (Subgroup.zpowers w₁ : Set M22)) at h
  rw [h, card_normalizer_w₁]

theorem index_arith' : ∀ k : Fin 99, (k : ℕ) ∣ 443520 → (k : ℕ) ≠ 1 →
    (11 ∣ (k : ℕ) ∨ (k : ℕ) % 11 = 1 ∨ (k : ℕ) % 11 = 5) →
    (7 ∣ (k : ℕ) ∨ (k : ℕ) % 7 = 1 ∨ (k : ℕ) % 7 = 3) →
    (k : ℕ) = 22 ∨ (k : ℕ) = 45 ∨ (k : ℕ) = 56 ∨ (k : ℕ) = 66 ∨ (k : ℕ) = 77 := by
  decide

theorem index_arith (k : ℕ) (hk : k < 99) (h1 : k ∣ 443520) (h2 : k ≠ 1)
    (h3 : 11 ∣ k ∨ k % 11 = 1 ∨ k % 11 = 5) (h4 : 7 ∣ k ∨ k % 7 = 1 ∨ k % 7 = 3) :
    k = 22 ∨ k = 45 ∨ k = 56 ∨ k = 66 ∨ k = 77 :=
  index_arith' ⟨k, hk⟩ h1 h2 h3 h4

theorem mod_of_dvd_55 {f : ℕ} (hf : f ∣ 55) : f % 11 = 1 ∨ f % 11 = 5 ∨ f % 11 = 0 := by
  have h := Nat.le_of_dvd (by norm_num) hf
  interval_cases f <;> simp_all

theorem mod_of_dvd_21 {f : ℕ} (hf : f ∣ 21) : f % 7 = 1 ∨ f % 7 = 3 ∨ f % 7 = 0 := by
  have h := Nat.le_of_dvd (by norm_num) hf
  interval_cases f <;> simp_all

theorem index_mem (H : Subgroup M22) (h1 : H.index ≠ 1) (h99 : H.index < 99) :
    H.index = 22 ∨ H.index = 45 ∨ H.index = 56 ∨ H.index = 66 ∨ H.index = 77 := by
  have hdvd : H.index ∣ 443520 := card_M22' ▸ H.index_dvd_card
  have h11 : 11 ∣ H.index ∨ H.index % 11 = 1 ∨ H.index % 11 = 5 := by
    by_cases h : 11 ∣ H.index
    · exact Or.inl h
    · have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
      obtain ⟨x, -, hx, hmod⟩ := exists_sylow_le_of_not_dvd (p := 11) (m := 40320)
        (by norm_num) (by norm_num) H h
      have hf := Subgroup.relIndex_dvd_card H (Subgroup.normalizer (Subgroup.zpowers x : Set M22))
      rw [card_normalizer_of_orderOf_eleven hx] at hf
      rw [Nat.ModEq] at hmod
      rcases mod_of_dvd_55 hf with e | e | e
      · exact Or.inr (Or.inl (hmod.trans e))
      · exact Or.inr (Or.inr (hmod.trans e))
      · exact absurd (Nat.dvd_of_mod_eq_zero (hmod.trans e)) h
  have h7 : 7 ∣ H.index ∨ H.index % 7 = 1 ∨ H.index % 7 = 3 := by
    by_cases h : 7 ∣ H.index
    · exact Or.inl h
    · have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
      obtain ⟨x, -, hx, hmod⟩ := exists_sylow_le_of_not_dvd (p := 7) (m := 63360)
        (by norm_num) (by norm_num) H h
      have hf := Subgroup.relIndex_dvd_card H (Subgroup.normalizer (Subgroup.zpowers x : Set M22))
      rw [card_normalizer_of_orderOf_seven hx] at hf
      rw [Nat.ModEq] at hmod
      rcases mod_of_dvd_21 hf with e | e | e
      · exact Or.inr (Or.inl (hmod.trans e))
      · exact Or.inr (Or.inr (hmod.trans e))
      · exact absurd (Nat.dvd_of_mod_eq_zero (hmod.trans e)) h
  exact index_arith _ h99 hdvd h1 h11 h7

theorem card_of_index {H : Subgroup M22} {k : ℕ} (hk : H.index = k) :
    Nat.card H * k = 443520 := by
  rw [← hk, ← card_M22']
  exact Subgroup.card_mul_index H

theorem normalizer_eleven_le {H : Subgroup M22} (hk : H.index % 11 = 1) :
    ∃ x ∈ H, orderOf x = 11 ∧ Subgroup.normalizer (Subgroup.zpowers x : Set M22) ≤ H := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  obtain ⟨x, hxH, hx, hmod⟩ := exists_sylow_le_of_not_dvd (p := 11) (m := 40320)
    (by norm_num) (by norm_num) H (by omega)
  refine ⟨x, hxH, hx, Subgroup.relIndex_eq_one.1 ?_⟩
  have hf := Subgroup.relIndex_dvd_card H (Subgroup.normalizer (Subgroup.zpowers x : Set M22))
  rw [card_normalizer_of_orderOf_eleven hx] at hf
  rw [Nat.ModEq, hk] at hmod
  generalize H.relIndex (Subgroup.normalizer (Subgroup.zpowers x : Set M22)) = f at hf hmod
  have h := Nat.le_of_dvd (by norm_num) hf
  interval_cases f <;> omega

theorem index_ne_45 (H : Subgroup M22) : H.index ≠ 45 := by
  intro h45
  obtain ⟨x, -, hx, hle⟩ := normalizer_eleven_le (H := H) (by rw [h45])
  have h1 := Subgroup.card_dvd_of_le hle
  rw [card_normalizer_of_orderOf_eleven hx] at h1
  have h2 := card_of_index h45
  omega

theorem conj_mem_of_le {g u : M22} {H : Subgroup M22} {x : M22}
    (hx : Subgroup.zpowers x = Subgroup.zpowers (g * u * g⁻¹))
    (hle : Subgroup.normalizer (Subgroup.zpowers x : Set M22) ≤ H) {n : M22}
    (hn : n ∈ Subgroup.normalizer (Subgroup.zpowers u : Set M22)) : g * n * g⁻¹ ∈ H := by
  apply hle
  rw [hx]
  exact conj_mem_normalizer hn

theorem orderOf_conj' (g x : M22) : orderOf (g * x * g⁻¹) = orderOf x :=
  orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x

theorem word_check : ∀ x, ofTable wTab (ofTable zTab (ofTable zTab (ofTable wTab (ofTable cTab
    (ofTable zTab (ofTable wTab (ofTable cTab (ofTable cTab (ofTable cTab (ofTable zTab
    (ofTable wTab (ofTable cTab x)))))))))))) =
      List.formPerm [0, 12] (List.formPerm [1, 7] (List.formPerm [2, 15] (List.formPerm [3, 11]
        (List.formPerm [5, 21] (List.formPerm [6, 16] (List.formPerm [8, 9]
          (List.formPerm [10, 13] x))))))) :=
  Certificates.certificate2034.1

theorem word_a : w₁ * z₀ * z₀ * w₁ * c₄ * z₀ * w₁ * c₄ * c₄ * c₄ * z₀ * w₁ * c₄ =
    CFSG.Sporadic.Mathieu.m22a := by
  refine Subtype.ext (Equiv.ext fun x => ?_)
  simp only [Subgroup.coe_mul, Equiv.Perm.mul_apply, coe_w₁, coe_z₀, coe_c₄]
  exact word_check x

theorem closure_z₀_w₁_c₄ : Subgroup.closure ({z₀, w₁, c₄} : Set M22) = ⊤ := by
  set K := Subgroup.closure ({z₀, w₁, c₄} : Set M22)
  have hz : z₀ ∈ K := Subgroup.subset_closure (Set.mem_insert _ _)
  have hw : w₁ ∈ K := Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hc : c₄ ∈ K :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  have ha : CFSG.Sporadic.Mathieu.m22a ∈ K := by
    rw [← word_a]
    exact K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem
      (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem hw hz) hz) hw) hc) hz) hw) hc) hc)
      hc) hz) hw) hc
  have hb : CFSG.Sporadic.Mathieu.m22b ∈ K := by
    have hsq : CFSG.Sporadic.Mathieu.m22a * CFSG.Sporadic.Mathieu.m22a = 1 := by
      have h2 := pow_orderOf_eq_one CFSG.Sporadic.Mathieu.m22a
      rwa [CFSG.Sporadic.Schreier.at_m22_image_pair_count.1, sq] at h2
    have : CFSG.Sporadic.Mathieu.m22b =
        CFSG.Sporadic.Mathieu.m22a * z₀ := by
      rw [z₀, ← mul_assoc, hsq, one_mul]
    rw [this]
    exact K.mul_mem ha hz
  rw [eq_top_iff, ← CFSG.Sporadic.Mathieu.closure_pair_eq_top CFSG.Sporadic.Mathieu.m22_eq _ _,
    Subgroup.closure_le]
  intro y hy
  rcases hy with rfl | rfl
  · exact ha
  · exact hb

theorem index_ne_56 (H : Subgroup M22) : H.index ≠ 56 := by
  intro h56
  obtain ⟨x, -, hx, hle⟩ := normalizer_eleven_le (H := H) (by rw [h56])
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  obtain ⟨g, hg⟩ := exists_zpowers_eq_conj (p := 11) (m := 40320) (by norm_num) (by norm_num)
    hx orderOf_z₀
  have hz : g * z₀ * g⁻¹ ∈ H :=
    conj_mem_of_le hg hle (Subgroup.le_normalizer (Subgroup.mem_zpowers z₀))
  have hw : g * w₁ * g⁻¹ ∈ H := conj_mem_of_le hg hle w₁_mem_normalizer
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hw5 : orderOf (g * w₁ * g⁻¹) = 5 := by rw [orderOf_conj', orderOf_w₁]
  have hmod := index_modEq_relIndex_normalizer
    (sylowZpowers (p := 5) (m := 88704) (by norm_num) (by norm_num) _ hw5) (H := H)
    (by rw [coe_sylowZpowers]; exact (Subgroup.zpowers_le).2 hw)
  change H.index ≡ H.relIndex
    (Subgroup.normalizer (Subgroup.zpowers (g * w₁ * g⁻¹) : Set M22)) [MOD 5] at hmod
  have hf := Subgroup.relIndex_dvd_card H
    (Subgroup.normalizer (Subgroup.zpowers (g * w₁ * g⁻¹) : Set M22))
  rw [card_normalizer_of_orderOf_five hw5] at hf
  rw [Nat.ModEq, h56] at hmod
  have hf1 : H.relIndex (Subgroup.normalizer (Subgroup.zpowers (g * w₁ * g⁻¹) : Set M22)) = 1 := by
    generalize H.relIndex (Subgroup.normalizer (Subgroup.zpowers (g * w₁ * g⁻¹) : Set M22)) = f
      at hf hmod ⊢
    have h := Nat.le_of_dvd (by norm_num) hf
    interval_cases f <;> omega
  have hle5 := Subgroup.relIndex_eq_one.1 hf1
  have hc : g * c₄ * g⁻¹ ∈ H := conj_mem_of_le rfl hle5 c₄_mem_normalizer
  have htop : H = ⊤ := by
    rw [eq_top_iff]
    have hmap :
        (Subgroup.closure ({z₀, w₁, c₄} : Set M22)).map (MulAut.conj g).toMonoidHom ≤ H := by
      rw [Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl
      · exact hz
      · exact hw
      · exact hc
    rw [closure_z₀_w₁_c₄, Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective] at hmap
    exact hmap
  rw [htop, Subgroup.index_top] at h56
  norm_num at h56

@[expose] def orbitFinset (H : Subgroup M22) (x : Fin 22) : Finset (Fin 22) :=
  (Set.toFinite (orbit H x)).toFinset

theorem mem_orbitFinset {H : Subgroup M22} {x z : Fin 22} :
    z ∈ orbitFinset H x ↔ z ∈ orbit H x :=
  Set.Finite.mem_toFinset _

theorem self_mem_orbitFinset (H : Subgroup M22) (x : Fin 22) : x ∈ orbitFinset H x :=
  mem_orbitFinset.2 (mem_orbit_self x)

theorem orbitFinset_invariant (H : Subgroup M22) (x : Fin 22) :
    ∀ h ∈ H, ∀ z ∈ orbitFinset H x, (h : Equiv.Perm (Fin 22)) z ∈ orbitFinset H x := by
  intro h hh z hz
  rw [mem_orbitFinset] at hz ⊢
  obtain ⟨k, rfl⟩ := hz
  refine ⟨⟨h, hh⟩ * k, ?_⟩
  show (⟨h, hh⟩ * k : H) • x = (h : Equiv.Perm (Fin 22)) (k • x)
  rw [mul_smul]
  rfl

theorem card_orbitFinset_dvd (H : Subgroup M22) (x : Fin 22) :
    (orbitFinset H x).card ∣ Nat.card H := by
  have h := natCard_orbit_mul_card_stabilizer H x
  have hc : (orbitFinset H x).card = Nat.card (orbit H x) := by
    rw [← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun z => mem_orbitFinset)
  rw [hc, ← h]
  exact dvd_mul_right _ _

theorem le_stabilizer_of_invariant {H : Subgroup M22} {O : Finset (Fin 22)}
    (hO : ∀ h ∈ H, ∀ z ∈ O, (h : Equiv.Perm (Fin 22)) z ∈ O) : H ≤ stabilizer M22 O :=
  fun h hh => mem_stabilizer_finset_iff.2 fun z hz => hO h hh z hz

theorem card_stabilizer_smul (g : M22) (S : Finset (Fin 22)) :
    Nat.card (stabilizer M22 (g • S)) = Nat.card (stabilizer M22 S) := by
  rw [stabilizer_smul_eq_stabilizer_map_conj,
    Subgroup.card_map_of_injective (MulAut.conj g).injective]

theorem fixed_zpowers_iff {u : M22} {z : Fin 22} :
    (∀ k : Subgroup.zpowers u, k • z = z) ↔ (u : Equiv.Perm (Fin 22)) z = z := by
  constructor
  · intro h
    exact h ⟨u, Subgroup.mem_zpowers u⟩
  · intro h k
    have hle : Subgroup.zpowers u ≤ stabilizer M22 z := (Subgroup.zpowers_le).2 h
    exact hle k.2

theorem fix_iff_of_zpowers_eq {y u : M22} (h : Subgroup.zpowers y = Subgroup.zpowers u)
    (z : Fin 22) : (y : Equiv.Perm (Fin 22)) z = z ↔ (u : Equiv.Perm (Fin 22)) z = z := by
  have hy : y ∈ Subgroup.zpowers u := h ▸ Subgroup.mem_zpowers y
  have hu : u ∈ Subgroup.zpowers y := h.symm ▸ Subgroup.mem_zpowers u
  constructor
  · intro hz
    exact (Subgroup.zpowers_le).2 (show y ∈ stabilizer M22 z from hz) hu
  · intro hz
    exact (Subgroup.zpowers_le).2 (show u ∈ stabilizer M22 z from hz) hy

theorem card_modEq_fixed {H : Subgroup M22} {O : Finset (Fin 22)}
    (hO : ∀ h ∈ H, ∀ z ∈ O, (h : Equiv.Perm (Fin 22)) z ∈ O) {u : M22} (hu : u ∈ H) {p : ℕ}
    [Fact p.Prime] (hup : orderOf u = p) :
    O.card ≡ (O.filter fun z => (u : Equiv.Perm (Fin 22)) z = z).card [MOD p] := by
  classical
  have hp : IsPGroup p (Subgroup.zpowers u) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hup, pow_one])
  have h := card_modEq_card_filter_fixed hp O fun k z hz =>
    hO k ((Subgroup.zpowers_le).2 hu k.2) z hz
  rwa [Finset.filter_congr fun z _ => fixed_zpowers_iff] at h

theorem conj_apply_eq_self_iff (g u : M22) (z : Fin 22) :
    ((g * u * g⁻¹ : M22) : Equiv.Perm (Fin 22)) z = z ↔
      (u : Equiv.Perm (Fin 22)) (((g⁻¹ : M22) : Equiv.Perm (Fin 22)) z) =
        ((g⁻¹ : M22) : Equiv.Perm (Fin 22)) z := by
  rw [coe_mul_apply, coe_mul_apply]
  constructor
  · intro h
    calc (u : Equiv.Perm (Fin 22)) (((g⁻¹ : M22) : Equiv.Perm (Fin 22)) z) =
        ((g⁻¹ : M22) : Equiv.Perm (Fin 22)) ((g : Equiv.Perm (Fin 22))
          ((u : Equiv.Perm (Fin 22)) (((g⁻¹ : M22) : Equiv.Perm (Fin 22)) z))) :=
          (coe_inv_apply_apply g _).symm
      _ = ((g⁻¹ : M22) : Equiv.Perm (Fin 22)) z := by rw [h]
  · intro h
    rw [h, coe_apply_inv_apply]

theorem fixed_tables : (∀ z, ofTable yTab z = z ↔ z = 4) ∧
    (∀ z, ofTable wTab z = z ↔ z = 8 ∨ z = 12) :=
  Certificates.certificate2034.2.1

theorem fix_conj_y₀ (g : M22) (z : Fin 22) :
    ((g * y₀ * g⁻¹ : M22) : Equiv.Perm (Fin 22)) z = z ↔ z = (g : Equiv.Perm (Fin 22)) 4 := by
  rw [conj_apply_eq_self_iff, coe_y₀, fixed_tables.1]
  constructor
  · intro h
    rw [← h, coe_apply_inv_apply]
  · rintro rfl
    exact coe_inv_apply_apply g 4

theorem fix_conj_w₁ (g : M22) (z : Fin 22) :
    ((g * w₁ * g⁻¹ : M22) : Equiv.Perm (Fin 22)) z = z →
      z = (g : Equiv.Perm (Fin 22)) 8 ∨ z = (g : Equiv.Perm (Fin 22)) 12 := by
  rw [conj_apply_eq_self_iff, coe_w₁, fixed_tables.2]
  rintro (h | h)
  · left
    rw [← h, coe_apply_inv_apply]
  · right
    rw [← h, coe_apply_inv_apply]

theorem card_mod_five_le {H : Subgroup M22} {O : Finset (Fin 22)}
    (hO : ∀ h ∈ H, ∀ z ∈ O, (h : Equiv.Perm (Fin 22)) z ∈ O) (h5 : ¬5 ∣ H.index) :
    O.card % 5 ≤ 2 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨w, hwH, hw, -⟩ := exists_sylow_le_of_not_dvd (p := 5) (m := 88704) (by norm_num)
    (by norm_num) H h5
  obtain ⟨g, hg⟩ := exists_zpowers_eq_conj (p := 5) (m := 88704) (by norm_num) (by norm_num) hw
    orderOf_w₁
  have hmod := card_modEq_fixed hO hwH hw
  have hle : (O.filter fun z => (w : Equiv.Perm (Fin 22)) z = z).card ≤ 2 := by
    have hsub : (O.filter fun z => (w : Equiv.Perm (Fin 22)) z = z) ⊆
        {(g : Equiv.Perm (Fin 22)) 8, (g : Equiv.Perm (Fin 22)) 12} := by
      intro z hz
      rw [Finset.mem_filter, fix_iff_of_zpowers_eq hg] at hz
      rcases fix_conj_w₁ g z hz.2 with e | e <;> simp [e]
    exact (Finset.card_le_card hsub).trans (Finset.card_le_two)
  rw [Nat.ModEq] at hmod
  omega

theorem orbits_y₀ : ∀ z : Fin 22, z ≠ 4 →
    (Finset.univ.image fun k : Fin 7 => (ofTable yTab)^[k] z) ∈ [orbY1, orbY2, orbY3] :=
  Certificates.certificate2034.2.2.1

theorem card_orbY : orbY1.card = 7 ∧ orbY2.card = 7 ∧ orbY3.card = 7 :=
  Certificates.certificate2034.2.2.2.1

theorem count_orbY : m22Count (fun f => ∀ x ∈ orbY1, f x ∈ orbY1) = 2520 ∧
    m22Count (fun f => ∀ x ∈ orbY2, f x ∈ orbY2) = 168 ∧
    m22Count (fun f => ∀ x ∈ orbY3, f x ∈ orbY3) = 2520 :=
  Certificates.certificate2034.2.2.2.2.1

theorem card_stabilizer_orbY {C : Finset (Fin 22)} (hC : C = orbY1 ∨ C = orbY2 ∨ C = orbY3) :
    Nat.card (stabilizer M22 C) ≤ 2520 := by
  have e : ∀ D : Finset (Fin 22), Nat.card (stabilizer M22 D) =
      m22Count (fun f => ∀ x ∈ D, f x ∈ D) := fun D => by
    rw [← card_m22_subtype]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun g => mem_stabilizer_finset_iff)
  rcases hC with rfl | rfl | rfl
  · rw [e, count_orbY.1]
  · rw [e, count_orbY.2.1]
    norm_num
  · rw [e, count_orbY.2.2]

theorem invariant_seven {C : Finset (Fin 22)} (hinv : ∀ z ∈ C, ofTable yTab z ∈ C)
    (h4 : (4 : Fin 22) ∉ C) (hcard : C.card = 7) : C = orbY1 ∨ C = orbY2 ∨ C = orbY3 := by
  obtain ⟨z, hz⟩ : C.Nonempty := by
    rw [← Finset.card_pos, hcard]
    norm_num
  have hz4 : z ≠ 4 := fun e => h4 (e ▸ hz)
  have hiter : ∀ k : ℕ, (ofTable yTab)^[k] z ∈ C := by
    intro k
    induction k with
    | zero => exact hz
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact hinv _ ih
  have hsub : (Finset.univ.image fun k : Fin 7 => (ofTable yTab)^[k] z) ⊆ C := by
    intro y hy
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hy
    exact hiter k
  have hmem := orbits_y₀ z hz4
  have hc7 : (Finset.univ.image fun k : Fin 7 => (ofTable yTab)^[k] z).card = 7 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with e | e | e <;> rw [e]
    · exact card_orbY.1
    · exact card_orbY.2.1
    · exact card_orbY.2.2
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hcard, hc7])
  rw [← heq]
  simpa only [List.mem_cons, List.not_mem_nil, or_false] using hmem

theorem le_stabilizer_of_index (H : Subgroup M22) (hk : H.index = 22 ∨ H.index = 66) :
    ∃ a : Fin 22, H ≤ stabilizer M22 a := by
  have h7 : ¬7 ∣ H.index := by rcases hk with h | h <;> rw [h] <;> norm_num
  have h5 : ¬5 ∣ H.index := by rcases hk with h | h <;> rw [h] <;> norm_num
  have hcard : Nat.card H = 20160 ∨ Nat.card H = 6720 := by
    rcases hk with h | h
    · have := card_of_index h
      omega
    · have := card_of_index h
      omega
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨y, hyH, hy, -⟩ := exists_sylow_le_of_not_dvd (p := 7) (m := 63360) (by norm_num)
    (by norm_num) H h7
  obtain ⟨g, hg⟩ := exists_zpowers_eq_conj (p := 7) (m := 63360) (by norm_num) (by norm_num) hy
    orderOf_y₀
  set p₀ : Fin 22 := (g : Equiv.Perm (Fin 22)) 4
  set O := orbitFinset H p₀
  have hO : ∀ h ∈ H, ∀ z ∈ O, (h : Equiv.Perm (Fin 22)) z ∈ O := orbitFinset_invariant H p₀
  have hmod := card_modEq_fixed hO hyH hy
  have hfix : (O.filter fun z => (y : Equiv.Perm (Fin 22)) z = z) = {p₀} := by
    ext z
    rw [Finset.mem_filter, fix_iff_of_zpowers_eq hg, fix_conj_y₀, Finset.mem_singleton]
    constructor
    · exact fun h => h.2
    · rintro rfl
      exact ⟨self_mem_orbitFinset H _, rfl⟩
  rw [hfix, Finset.card_singleton, Nat.ModEq] at hmod
  have hmod5 := card_mod_five_le hO h5
  have hdvd : O.card ∣ Nat.card H := card_orbitFinset_dvd H p₀
  have hle : O.card ≤ 22 := (Finset.card_le_univ O).trans (by simp)
  have hcases : O.card = 1 ∨ O.card = 15 := by
    generalize O.card = n at hmod hmod5 hdvd hle ⊢
    rcases hcard with hc | hc <;> rw [hc] at hdvd <;> interval_cases n <;> omega
  have hp₀ : p₀ ∈ O := self_mem_orbitFinset H p₀
  rcases hcases with h1 | h15
  · refine ⟨p₀, fun h hh => ?_⟩
    have hmem := hO h hh p₀ hp₀
    obtain ⟨q, hq⟩ := Finset.card_eq_one.1 h1
    rw [hq, Finset.mem_singleton] at hmem hp₀
    change (h : Equiv.Perm (Fin 22)) p₀ = p₀
    rw [hmem, hp₀]
  · exfalso
    set C := Oᶜ
    have hCcard : C.card = 7 := by
      rw [Finset.card_compl, h15]
      rfl
    have hC : ∀ h ∈ H, ∀ z ∈ C, (h : Equiv.Perm (Fin 22)) z ∈ C := by
      intro h hh z hz
      rw [Finset.mem_compl] at hz ⊢
      intro hzO
      apply hz
      have := hO h⁻¹ (H.inv_mem hh) _ hzO
      rwa [coe_inv_apply_apply] at this
    have hu : g * y₀ * g⁻¹ ∈ H := by
      have : g * y₀ * g⁻¹ ∈ Subgroup.zpowers y := hg ▸ Subgroup.mem_zpowers _
      exact (Subgroup.zpowers_le).2 hyH this
    set C' := (g⁻¹ : M22) • C
    have hinv : ∀ z ∈ C', ofTable yTab z ∈ C' := by
      intro z hz
      rw [mem_smul_finset_iff, inv_inv] at hz ⊢
      have := hC _ hu _ hz
      rw [coe_mul_apply, coe_mul_apply, coe_inv_apply_apply, coe_y₀] at this
      exact this
    have h4 : (4 : Fin 22) ∉ C' := by
      rw [mem_smul_finset_iff, inv_inv, Finset.mem_compl, not_not]
      exact hp₀
    have hC'card : C'.card = 7 := by rw [Finset.card_smul_finset, hCcard]
    have hstab := card_stabilizer_orbY (invariant_seven hinv h4 hC'card)
    have hle' := Subgroup.card_le_of_le (le_stabilizer_of_invariant hC)
    have hCeq : C = g • C' := by rw [smul_inv_smul]
    rw [hCeq, card_stabilizer_smul] at hle'
    rcases hcard with hc | hc <;> omega

theorem eq_stabilizer_of_index_22 (H : Subgroup M22) (h22 : H.index = 22) :
    ∃ a : Fin 22, H = stabilizer M22 a := by
  obtain ⟨a, ha⟩ := le_stabilizer_of_index H (Or.inl h22)
  refine ⟨a, Subgroup.eq_of_le_of_card_ge ha ?_⟩
  rw [card_stabilizer_point]
  have := card_of_index h22
  omega

theorem index_ne_66 (H : Subgroup M22) : H.index ≠ 66 := by
  intro h66
  obtain ⟨a, ha⟩ := le_stabilizer_of_index H (Or.inr h66)
  have hcard := card_of_index h66
  have hJ : (H.subgroupOf (stabilizer M22 a)).index = 3 := by
    have h := Subgroup.card_mul_index (H.subgroupOf (stabilizer M22 a))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe ha).toEquiv, card_stabilizer_point] at h
    have h' : Nat.card H = 6720 := by omega
    rw [h'] at h
    omega
  have := isSimpleGroup_stabilizer a
  have htop := eq_top_of_not_dvd_factorial_index (H.subgroupOf (stabilizer M22 a))
    (by rw [hJ, card_stabilizer_point]; decide)
  rw [htop, Subgroup.index_top] at hJ
  norm_num at hJ

@[expose] def quadX4 : Finset (Fin 22) := {2, 9, 17, 19}

@[expose] def sylowTwoGroup : Subgroup M22 :=
  stabilizer M22 hexad0 ⊓ stabilizer M22 pairX2 ⊓ stabilizer M22 pairPartition

theorem count_P2 : m22Count InP2 = 128 ∧ m22Count (fun f => InP2 f ∧ f 0 = 0) = 64 ∧
    m22Count (fun f => InP2 f ∧ f 2 = 2) = 32 ∧ m22Count (fun f => InP2 f ∧ f 3 = 3) = 8 ∧
    m22Count (fun f => ∀ x ∈ pairX2, f x ∈ pairX2) = 1920 :=
  Certificates.certificate2034.2.2.2.2.2

theorem smul_finset_eq_image (g : M22) (s : Finset (Fin 22)) :
    g • s = s.image ⇑(g : Equiv.Perm (Fin 22)) := by
  rw [Subgroup.smul_def, Finset.smul_finset_def]
  rfl

theorem mem_sylowTwoGroup {g : M22} : g ∈ sylowTwoGroup ↔ InP2 ⇑(g : Equiv.Perm (Fin 22)) := by
  rw [sylowTwoGroup, Subgroup.mem_inf, Subgroup.mem_inf, mem_stabilizer_finset_iff,
    mem_stabilizer_finset_iff, mem_stabilizer_iff, InP2, and_assoc, Finset.smul_finset_def]
  simp only [smul_finset_eq_image]

theorem card_sylowTwoGroup : Nat.card sylowTwoGroup = 128 := by
  rw [← count_P2.1, ← card_m22_subtype]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun g => mem_sylowTwoGroup)

theorem card_stabilizer_P2 (z : Fin 22) :
    Nat.card (stabilizer sylowTwoGroup z) = m22Count (fun f => InP2 f ∧ f z = z) := by
  rw [← card_m22_subtype]
  exact Nat.card_congr ⟨fun g => ⟨g.1.1, mem_sylowTwoGroup.1 g.1.2, g.2⟩,
    fun g => ⟨⟨g.1, mem_sylowTwoGroup.2 g.2.1⟩, g.2.2⟩, fun _ => rfl, fun _ => rfl⟩

theorem P2_preserves {h : M22} (hh : h ∈ sylowTwoGroup) :
    (∀ x ∈ pairX2, (h : Equiv.Perm (Fin 22)) x ∈ pairX2) ∧
      (∀ x ∈ quadX4, (h : Equiv.Perm (Fin 22)) x ∈ quadX4) ∧
        ∀ x ∉ hexad0, (h : Equiv.Perm (Fin 22)) x ∉ hexad0 := by
  have hm := mem_sylowTwoGroup.1 hh
  have hB : h ∈ stabilizer M22 hexad0 := mem_stabilizer_finset_iff.2 hm.1
  have hX : h ∈ stabilizer M22 pairX2 := mem_stabilizer_finset_iff.2 hm.2.1
  have hq : quadX4 = hexad0 \ pairX2 := by decide
  refine ⟨hm.2.1, fun x hx => ?_, fun x hx hhx => hx ?_⟩
  · rw [hq, Finset.mem_sdiff] at hx ⊢
    refine ⟨hm.1 x hx.1, fun h' => hx.2 ?_⟩
    rw [← apply_mem_smul_finset_iff h pairX2 x, stabilizer_smul_eq ⟨h, hX⟩]
    exact h'
  · rw [← apply_mem_smul_finset_iff h hexad0 x, stabilizer_smul_eq ⟨h, hB⟩]
    exact hhx

theorem orbit_P2 {z : Fin 22} {S : Finset (Fin 22)} (hz : z ∈ S)
    (hpres : ∀ h ∈ sylowTwoGroup, ∀ y ∈ S, (h : Equiv.Perm (Fin 22)) y ∈ S)
    (hcount : Nat.card (stabilizer sylowTwoGroup z) * S.card = 128) :
    orbit sylowTwoGroup z = ↑S := by
  have hsub : orbit sylowTwoGroup z ⊆ ↑S := by
    rintro _ ⟨k, rfl⟩
    exact hpres k.1 k.2 z hz
  have hcard : (orbit sylowTwoGroup z).ncard = S.card := by
    have h := natCard_orbit_mul_card_stabilizer sylowTwoGroup z
    rw [card_sylowTwoGroup, ← hcount, Nat.card_coe_set_eq, mul_comm] at h
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h
  refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)
  rw [Set.ncard_coe_finset, hcard]

theorem orbit_P2_zero : orbit sylowTwoGroup (0 : Fin 22) = ↑pairX2 :=
  orbit_P2 (by decide) (fun h hh => (P2_preserves hh).1)
    (by rw [card_stabilizer_P2, count_P2.2.1]; rfl)

theorem orbit_P2_two : orbit sylowTwoGroup (2 : Fin 22) = ↑quadX4 :=
  orbit_P2 (by decide) (fun h hh => (P2_preserves hh).2.1)
    (by rw [card_stabilizer_P2, count_P2.2.2.1]; rfl)

theorem orbit_P2_three : orbit sylowTwoGroup (3 : Fin 22) = ↑hexad0ᶜ :=
  orbit_P2 (by decide) (fun h hh y hy => by
      rw [Finset.mem_compl] at hy ⊢
      exact (P2_preserves hh).2.2 y hy)
    (by rw [card_stabilizer_P2, count_P2.2.2.2.1, Finset.card_compl]; rfl)

theorem P2_invariant_cases {O : Finset (Fin 22)}
    (hO : ∀ h ∈ sylowTwoGroup, ∀ z ∈ O, (h : Equiv.Perm (Fin 22)) z ∈ O) (h0 : (0 : Fin 22) ∈ O) :
    O = pairX2 ∨ O = hexad0 ∨ O = pairX2 ∪ hexad0ᶜ ∨ O = Finset.univ := by
  have horb : ∀ {z w : Fin 22}, w ∈ orbit sylowTwoGroup z → z ∈ O → w ∈ O := by
    rintro z _ ⟨k, rfl⟩ hz
    exact hO k.1 k.2 z hz
  have hX2 : ∀ z ∈ pairX2, z ∈ O := fun z hz =>
    horb (by rw [orbit_P2_zero]; exact hz) h0
  have hX4 : ∀ z ∈ quadX4, z ∈ O ↔ (2 : Fin 22) ∈ O := by
    intro z hz
    have hz' : z ∈ orbit sylowTwoGroup (2 : Fin 22) := by rw [orbit_P2_two]; exact hz
    exact ⟨fun h => horb (mem_orbit_symm.1 hz') h, fun h => horb hz' h⟩
  have hX16 : ∀ z, z ∉ hexad0 → (z ∈ O ↔ (3 : Fin 22) ∈ O) := by
    intro z hz
    have hz' : z ∈ orbit sylowTwoGroup (3 : Fin 22) := by
      rw [orbit_P2_three]
      exact Finset.mem_compl.2 hz
    exact ⟨fun h => horb (mem_orbit_symm.1 hz') h, fun h => horb hz' h⟩
  have htri : ∀ z : Fin 22, z ∈ pairX2 ∨ z ∈ quadX4 ∨ z ∉ hexad0 := by decide
  have hB : ∀ z : Fin 22, z ∈ hexad0 ↔ z ∈ pairX2 ∨ z ∈ quadX4 := by decide
  have hdisj : ∀ z : Fin 22, z ∈ pairX2 → z ∉ quadX4 ∧ z ∈ hexad0 := by decide
  have hdisj' : ∀ z : Fin 22, z ∈ quadX4 → z ∉ pairX2 ∧ z ∈ hexad0 := by decide
  by_cases h2 : (2 : Fin 22) ∈ O <;> by_cases h3 : (3 : Fin 22) ∈ O
  · right; right; right
    ext z
    simp only [Finset.mem_univ, iff_true]
    rcases htri z with hz | hz | hz
    · exact hX2 z hz
    · exact (hX4 z hz).2 h2
    · exact (hX16 z hz).2 h3
  · right; left
    ext z
    rw [hB]
    rcases htri z with hz | hz | hz
    · exact ⟨fun _ => Or.inl hz, fun _ => hX2 z hz⟩
    · exact ⟨fun _ => Or.inr hz, fun _ => (hX4 z hz).2 h2⟩
    · have : z ∉ O := fun h => h3 ((hX16 z hz).1 h)
      refine ⟨fun h => absurd h this, fun h => absurd ((hB z).2 h) hz⟩
  · right; right; left
    ext z
    rw [Finset.mem_union, Finset.mem_compl]
    rcases htri z with hz | hz | hz
    · exact ⟨fun _ => Or.inl hz, fun _ => hX2 z hz⟩
    · have : z ∉ O := fun h => h2 ((hX4 z hz).1 h)
      refine ⟨fun h => absurd h this, fun h => ?_⟩
      rcases h with h | h
      · exact absurd h (hdisj' z hz).1
      · exact absurd (hdisj' z hz).2 h
    · exact ⟨fun _ => Or.inr hz, fun _ => (hX16 z hz).2 h3⟩
  · left
    ext z
    rcases htri z with hz | hz | hz
    · exact ⟨fun _ => hz, fun _ => hX2 z hz⟩
    · have : z ∉ O := fun h => h2 ((hX4 z hz).1 h)
      exact ⟨fun h => absurd h this, fun h => absurd hz (hdisj z h).1⟩
    · have : z ∉ O := fun h => h3 ((hX16 z hz).1 h)
      exact ⟨fun h => absurd h this, fun h => absurd (hdisj z h).2 hz⟩

theorem factorization_two_pow_mul {e m : ℕ} (hm : ¬2 ∣ m) : (2 ^ e * m).factorization 2 = e := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero 2)
  rw [Nat.factorization_mul (pow_ne_zero _ two_ne_zero) hm0, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hm, add_zero]

theorem eq_stabilizer_hexad_of_index_77 (H : Subgroup M22) (h77 : H.index = 77) :
    ∃ B ∈ hexads, H = stabilizer M22 B := by
  have hcard : Nat.card H = 5760 := by
    have := card_of_index h77
    omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨QH⟩ : Nonempty (Sylow 2 H) := inferInstance
  have hQH : Nat.card QH = 128 := by
    rw [QH.card_eq_multiplicity, hcard, show (5760 : ℕ) = 2 ^ 7 * 45 by norm_num,
      factorization_two_pow_mul (by norm_num)]
    norm_num
  set Q := (QH : Subgroup H).map H.subtype
  have hQ : Nat.card Q = 128 := by
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective H)]
    exact hQH
  have hQle : Q ≤ H := Subgroup.map_subtype_le _
  have h2M : (2 : ℕ) ^ (Nat.card M22).factorization 2 = 128 := by
    rw [card_M22', show (443520 : ℕ) = 2 ^ 7 * 3465 by norm_num,
      factorization_two_pow_mul (by norm_num)]
    norm_num
  set QS := Sylow.ofCard Q (by rw [hQ, h2M])
  set PS := Sylow.ofCard sylowTwoGroup (by rw [card_sylowTwoGroup, h2M])
  obtain ⟨g, hg⟩ := exists_smul_eq M22 PS QS
  have hconj : ∀ h ∈ sylowTwoGroup, g * h * g⁻¹ ∈ H := by
    intro h hh
    apply hQle
    have hmem : g * h * g⁻¹ ∈ ((g • PS : Sylow 2 M22) : Subgroup M22) := by
      rw [Sylow.smul_def, Sylow.pointwise_smul_def]
      refine Subgroup.mem_pointwise_smul_iff_inv_smul_mem.2 ?_
      rw [MulAut.smul_def, MulAut.conj_inv_apply,
        show g⁻¹ * (g * h * g⁻¹) * g = h by group]
      exact hh
    rw [hg] at hmem
    exact hmem
  set O := orbitFinset H ((g : Equiv.Perm (Fin 22)) 0)
  have hO : ∀ h ∈ H, ∀ z ∈ O, (h : Equiv.Perm (Fin 22)) z ∈ O :=
    orbitFinset_invariant H ((g : Equiv.Perm (Fin 22)) 0)
  set O' := (g⁻¹ : M22) • O
  have hO' : ∀ h ∈ sylowTwoGroup, ∀ z ∈ O', (h : Equiv.Perm (Fin 22)) z ∈ O' := by
    intro h hh z hz
    rw [mem_smul_finset_iff, inv_inv] at hz ⊢
    have := hO _ (hconj h hh) _ hz
    rwa [coe_mul_apply, coe_mul_apply, coe_inv_apply_apply] at this
  have h0 : (0 : Fin 22) ∈ O' := by
    rw [mem_smul_finset_iff, inv_inv]
    exact self_mem_orbitFinset H _
  have hcardO : O'.card = O.card := Finset.card_smul_finset _ _
  have h5 := card_mod_five_le hO (by rw [h77]; norm_num)
  have hdvd : O.card ∣ Nat.card H := card_orbitFinset_dvd H ((g : Equiv.Perm (Fin 22)) 0)
  rw [hcard] at hdvd
  have hOeq : ∀ S : Finset (Fin 22), O' = S → O = g • S := by
    rintro S rfl
    rw [smul_inv_smul]
  rcases P2_invariant_cases hO' h0 with e | e | e | e
  · exfalso
    have hle : H ≤ stabilizer M22 O := le_stabilizer_of_invariant hO
    rw [hOeq _ e] at hle
    have := Subgroup.card_le_of_le hle
    have h1920 : Nat.card (stabilizer M22 pairX2) = 1920 := by
      rw [← count_P2.2.2.2.2, ← card_m22_subtype]
      exact Nat.card_congr (Equiv.subtypeEquivRight fun g => mem_stabilizer_finset_iff)
    rw [card_stabilizer_smul, h1920, hcard] at this
    norm_num at this
  · have hB : g • hexad0 ∈ hexads := smul_mem_hexads g hexad0_mem
    refine ⟨g • hexad0, hB, ?_⟩
    have hle : H ≤ stabilizer M22 O := le_stabilizer_of_invariant hO
    rw [hOeq _ e] at hle
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_stabilizer_hexad hB, hcard])
  · exfalso
    have h18 : O'.card = 18 := by rw [e]; decide
    omega
  · exfalso
    have h22 : O'.card = 22 := by rw [e]; simp
    rw [← hcardO, h22] at hdvd
    norm_num at hdvd

theorem low_index_classification (H : Subgroup M22) (hH : H ≠ ⊤) (h99 : H.index < 99) :
    (H.index = 22 ∧ ∃ a : Fin 22, H = stabilizer M22 a) ∨
      (H.index = 77 ∧ ∃ B ∈ hexads, H = stabilizer M22 B) := by
  have h1 : H.index ≠ 1 := fun h => hH (Subgroup.index_eq_one.1 h)
  rcases index_mem H h1 h99 with h | h | h | h | h
  · exact Or.inl ⟨h, eq_stabilizer_of_index_22 H h⟩
  · exact absurd h (index_ne_45 H)
  · exact absurd h (index_ne_56 H)
  · exact absurd h (index_ne_66 H)
  · exact Or.inr ⟨h, eq_stabilizer_hexad_of_index_77 H h⟩

end CFSG.ComponentClassification.WittDesign
