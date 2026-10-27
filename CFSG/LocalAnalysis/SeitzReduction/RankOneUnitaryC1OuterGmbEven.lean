module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterGmbCore
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonSplitTorusMatrices

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup
open scoped MatrixGroups
open CFSG.QuasithinUnique.Setup.SL2Modules

theorem gmb_mem_map_conj_iff {G : Type*} [Group G] {S : Subgroup G} {k x : G} :
    x ∈ S.map (MulAut.conj k).toMonoidHom ↔ k⁻¹ * x * k ∈ S := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

section Even

variable {F : Type*} [Field F]

theorem gmb_eq_one_of_sq_eq_one [CharP F 2] {a : F} (ha : a ^ 2 = 1) : a = 1 := by
  have h : (a + 1) ^ 2 = 0 := by
    have : (a + 1) ^ 2 = a ^ 2 + 1 + (a + a) := by ring
    rw [this, ha, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, add_zero]
  have h1 : a + 1 = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp h
  rw [← CharTwo.neg_eq (1 : F)]
  exact eq_neg_of_add_eq_zero_left h1

theorem gmb_center_sl2_eq_bot [CharP F 2] : Subgroup.center SL(2, F) = ⊥ := by
  ext A
  rw [Matrix.SpecialLinearGroup.mem_center_iff, Subgroup.mem_bot]
  constructor
  · rintro ⟨r, hr, hA⟩
    rw [Fintype.card_fin] at hr
    have hr1 := gmb_eq_one_of_sq_eq_one hr
    apply Subtype.ext
    rw [← hA, hr1, map_one, Matrix.SpecialLinearGroup.coe_one]
  · rintro rfl
    exact ⟨1, by simp, by simp⟩

noncomputable def gmbPSL2EquivSL2 [CharP F 2] : PSL(2, F) ≃* SL(2, F) :=
  (QuotientGroup.quotientMulEquivOfEq gmb_center_sl2_eq_bot).trans QuotientGroup.quotientBot

@[expose] def gmbTorusSL2 (F : Type*) [Field F] : Subgroup SL(2, F) :=
  (CFSG.Glauberman.Dickson.splitTorusSLHom F).range

theorem gmb_splitTorus_injective :
    Function.Injective (CFSG.Glauberman.Dickson.splitTorusSLHom F) := by
  intro a b h
  have h00 := congrFun (congrFun (congrArg
    (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F)) h) 0) 0
  simp only [CFSG.Glauberman.Dickson.splitTorusSLHom_coe] at h00
  exact Units.ext (by simpa using h00)

theorem gmb_splitTorus_mem_borel (a : Fˣ) :
    CFSG.Glauberman.Dickson.splitTorusSLHom F a ∈ borelSubgroup F := by
  rw [mem_borelSubgroup_iff]
  exact ⟨a, 0, by rw [CFSG.Glauberman.Dickson.splitTorusSLHom_coe]; simp⟩

theorem gmbTorusSL2_le_borel : gmbTorusSL2 F ≤ borelSubgroup F := by
  rintro _ ⟨a, rfl⟩
  exact gmb_splitTorus_mem_borel a

theorem gmb_splitTorus_conj_uElt (a : Fˣ) (t : F) :
    CFSG.Glauberman.Dickson.splitTorusSLHom F a * uElt t *
        (CFSG.Glauberman.Dickson.splitTorusSLHom F a)⁻¹ = uElt ((a : F) ^ 2 * t) := by
  rw [borel_mul_uElt _ (gmb_splitTorus_mem_borel a), mul_inv_cancel_right,
    CFSG.Glauberman.Dickson.splitTorusSLHom_coe]
  simp

theorem gmbTorus_upperRootGroup [Finite F] [CharP F 2] (hF : 2 < Nat.card F) :
    GmbTorus (upperRootGroup F) (gmbTorusSL2 F) where
  le_normalizer := by
    rw [normalizer_upperRootGroup]
    exact gmbTorusSL2_le_borel
  odd_card := by
    have : Fintype F := Fintype.ofFinite F
    have hT : Nat.card (gmbTorusSL2 F) = Nat.card Fˣ :=
      (Nat.card_congr (MonoidHom.ofInjective gmb_splitTorus_injective).toEquiv).symm
    rw [hT, Nat.card_units]
    obtain ⟨n, -, hn⟩ := FiniteField.card F 2
    rw [Nat.card_eq_fintype_card, hn]
    have h2 : 2 ≤ 2 ^ (n : ℕ) := Nat.le_self_pow n.ne_zero 2
    have he : Even (2 ^ (n : ℕ)) := (Nat.even_pow' n.ne_zero).mpr even_two
    obtain ⟨k, hk⟩ := he
    exact ⟨k - 1, by omega⟩
  comm := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm]
  fixed := by
    intro x hx hfix
    obtain ⟨t, rfl⟩ := (mem_upperRootGroup_iff x).mp hx
    obtain ⟨a, ha0, ha1⟩ : ∃ a : F, a ≠ 0 ∧ a ≠ 1 := by
      by_contra hno
      push Not at hno
      have hsub : (Set.univ : Set F) ⊆ {0, 1} := fun a _ => by
        by_cases h : a = 0
        · exact Or.inl h
        · exact Or.inr (hno a h)
      have := Set.ncard_le_ncard hsub (Set.toFinite _)
      rw [Set.ncard_univ, Set.ncard_pair zero_ne_one] at this
      omega
    have hsq : a ^ 2 ≠ 1 := fun h => ha1 (gmb_eq_one_of_sq_eq_one h)
    have h := hfix _ ⟨Units.mk0 a ha0, rfl⟩
    rw [gmb_splitTorus_conj_uElt] at h
    have ht : (a ^ 2 - 1) * t = 0 := by
      have := uElt_injective h
      simp only [Units.val_mk0] at this
      linear_combination this
    rcases mul_eq_zero.mp ht with h0 | h0
    · exact absurd (sub_eq_zero.mp h0) hsq
    · rw [h0, uElt_zero]
  irred := by
    intro Y hYU hYT
    rcases Y.bot_or_exists_ne_one with h0 | ⟨y, hy, hy1⟩
    · exact Or.inl h0
    right
    refine le_antisymm hYU fun w hw => ?_
    obtain ⟨t, rfl⟩ := (mem_upperRootGroup_iff y).mp (hYU hy)
    obtain ⟨s, rfl⟩ := (mem_upperRootGroup_iff w).mp hw
    have ht : t ≠ 0 := fun h => hy1 (by rw [h, uElt_zero])
    by_cases hs : s = 0
    · rw [hs, uElt_zero]
      exact Y.one_mem
    obtain ⟨a, ha⟩ := FiniteField.isSquare_of_char_two (ringChar.eq F 2) (s / t)
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [mul_zero, div_eq_zero_iff] at ha
      exact ha.elim hs ht
    have h := hYT _ ⟨Units.mk0 a ha0, rfl⟩ _ hy
    rw [gmb_splitTorus_conj_uElt] at h
    convert h using 2
    simp only [Units.val_mk0]
    rw [sq, ← ha, div_mul_cancel₀ s ht]

theorem gmb_borel_entry {g : SL(2, F)} (hg : g ∈ borelSubgroup F) :
    (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
  obtain ⟨a, b, hab⟩ := (mem_borelSubgroup_iff g).mp hg
  rw [hab]
  simp

theorem gmb_exists_conj_le_torus [Finite F] [CharP F 2] {E : Subgroup SL(2, F)}
    (hEB : E ≤ borelSubgroup F) (hE : Odd (Nat.card E)) :
    ∃ c ∈ upperRootGroup F, ∀ x ∈ E, c * x * c⁻¹ ∈ gmbTorusSL2 F := by
  have hU : ∀ e ∈ E, (e : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 → e = 1 := by
    intro e he h00
    obtain ⟨a, b, hab⟩ := (mem_borelSubgroup_iff e).mp (hEB he)
    have ha : (a : F) = 1 := by
      rw [hab] at h00
      simpa using h00
    have ha' : ((a⁻¹ : Fˣ) : F) = 1 := by rw [Units.val_inv_eq_inv_val, ha, inv_one]
    have he' : e = uElt b := by
      apply Subtype.ext
      rw [hab, coe_uElt, ha, ha']
    have hee : e * e = 1 := by rw [he', ← uElt_add, CharTwo.add_self_eq_zero, uElt_zero]
    have hodd := hE.of_dvd_nat (Subgroup.orderOf_dvd_natCard E he)
    have h2 : orderOf e ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hee)
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
    · exact orderOf_eq_one_iff.mp h
    · exfalso
      rw [h] at hodd
      exact (Nat.not_odd_iff_even.mpr even_two) hodd
  let δ : E →* F :=
    { toFun := fun e => ((e : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 0
      map_one' := by simp
      map_mul' := fun a b => by
        have hb := gmb_borel_entry (hEB b.2)
        simp only [Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
          Fin.sum_univ_two, hb, mul_zero, add_zero] }
  have hδ : Function.Injective δ := by
    intro a b hab
    have h1 : δ (a * b⁻¹) = 1 := by
      rw [map_mul, hab, ← map_mul, mul_inv_cancel, map_one]
    have h2 : a * b⁻¹ = 1 := Subtype.ext (hU _ (a * b⁻¹).2 h1)
    exact mul_inv_eq_one.mp h2
  have hcyc : IsCyclic E := isCyclic_of_injective_ringHom δ hδ
  obtain ⟨e, he⟩ := hcyc.exists_generator
  have hpow : ∀ x ∈ E, ∃ k : ℤ, x = (e : SL(2, F)) ^ k := by
    intro x hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (he ⟨x, hx⟩)
    exact ⟨k, by rw [← Subgroup.coe_zpow, hk]⟩
  obtain ⟨a, b, hab⟩ := (mem_borelSubgroup_iff (e : SL(2, F))).mp (hEB e.2)
  by_cases ha : a = 1
  ·
    have he1 : (e : SL(2, F)) = 1 := hU _ e.2 (by rw [hab, ha]; simp)
    refine ⟨1, (upperRootGroup F).one_mem, fun x hx => ?_⟩
    obtain ⟨k, rfl⟩ := hpow x hx
    rw [he1, one_zpow, mul_one, inv_one, mul_one]
    exact (gmbTorusSL2 F).one_mem
  · obtain ⟨a', ha'def⟩ : ∃ a' : F, a' = ((a⁻¹ : Fˣ) : F) := ⟨_, rfl⟩
    rw [← ha'def] at hab
    have haa' : (a : F) * a' = 1 := by rw [ha'def, Units.mul_inv]
    have hden : (a : F) - a' ≠ 0 := by
      intro h
      apply ha
      have h1 : (a : F) = a' := sub_eq_zero.mp h
      have h2 : (a : F) ^ 2 = 1 := by rw [sq]; nth_rewrite 2 [h1]; exact haa'
      exact Units.ext (gmb_eq_one_of_sq_eq_one h2)
    obtain ⟨r, hr⟩ : ∃ r : F, r * ((a : F) - a') = b := ⟨_, div_mul_cancel₀ b hden⟩
    refine ⟨uElt r, (mem_upperRootGroup_iff _).mpr ⟨r, rfl⟩, ?_⟩
    have hinv : (uElt r)⁻¹ = uElt (-r) :=
      (inv_eq_of_mul_eq_one_right (by rw [← uElt_add, add_neg_cancel, uElt_zero])).trans rfl
    have hconj : uElt r * (e : SL(2, F)) * (uElt r)⁻¹ =
        CFSG.Glauberman.Dickson.splitTorusSLHom F a := by
      rw [hinv]
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_uElt,
        coe_uElt, hab, CFSG.Glauberman.Dickson.splitTorusSLHom_coe, Matrix.mul_fin_two,
        Matrix.mul_fin_two, ← Units.val_inv_eq_inv_val, ← ha'def]
      ext i j
      fin_cases i <;> fin_cases j
      · simp
      · simp
        linear_combination -hr
      · simp
      · simp
    intro x hx
    obtain ⟨k, rfl⟩ := hpow x hx
    have hc : uElt r * (e : SL(2, F)) ^ k * (uElt r)⁻¹ =
        (MulAut.conj (uElt r)) ((e : SL(2, F)) ^ k) := rfl
    rw [hc, map_zpow, MulAut.conj_apply, hconj]
    exact zpow_mem (show _ ∈ gmbTorusSL2 F from ⟨a, rfl⟩) k

theorem gmbProp_sl2_charTwo [Finite F] [CharP F 2] (hF : 2 < Nat.card F) :
    GmbProp SL(2, F) := by
  intro P E hEN hE
  have : Fintype F := Fintype.ofFinite F
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hgP, hgN, -⟩ :=
    (sl2_defining_characteristic_Sylow_normalizer_maximal_Borel (F := F) (p := 2)).2.2.2.2.2.2.2 P
  have hE₁B : E.map (MulAut.conj g⁻¹).toMonoidHom ≤ borelSubgroup F := by
    intro y hy
    rw [gmb_mem_map_conj_iff, inv_inv] at hy
    have := (hgN _).mp (hEN hy)
    rwa [show g⁻¹ * (g * y * g⁻¹) * g = y by group] at this
  have hE₁ : Odd (Nat.card (E.map (MulAut.conj g⁻¹).toMonoidHom)) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
    exact hE
  obtain ⟨c, hcU, hcT⟩ := gmb_exists_conj_le_torus hE₁B hE₁
  refine ⟨(gmbTorusSL2 F).map (MulAut.conj (g * c⁻¹)).toMonoidHom, ?_, ?_⟩
  · intro x hx
    rw [gmb_mem_map_conj_iff]
    have hx₁ : g⁻¹ * x * g ∈ E.map (MulAut.conj g⁻¹).toMonoidHom := by
      rw [gmb_mem_map_conj_iff, inv_inv, show g * (g⁻¹ * x * g) * g⁻¹ = x by group]
      exact hx
    have := hcT _ hx₁
    rwa [show c * (g⁻¹ * x * g) * c⁻¹ = (g * c⁻¹)⁻¹ * x * (g * c⁻¹) by group] at this
  · have hUP : (upperRootGroup F).map (MulAut.conj (g * c⁻¹)).toMonoidHom =
        (P : Subgroup SL(2, F)) := by
      ext x
      rw [gmb_mem_map_conj_iff, hgP,
        show (g * c⁻¹)⁻¹ * x * (g * c⁻¹) = c * (g⁻¹ * x * g) * c⁻¹ by group]
      constructor
      · intro h
        have := (upperRootGroup F).mul_mem
          ((upperRootGroup F).mul_mem ((upperRootGroup F).inv_mem hcU) h) hcU
        rwa [show c⁻¹ * (c * (g⁻¹ * x * g) * c⁻¹) * c = g⁻¹ * x * g by group] at this
      · intro h
        exact (upperRootGroup F).mul_mem ((upperRootGroup F).mul_mem hcU h)
          ((upperRootGroup F).inv_mem hcU)
    rw [← hUP]
    exact (gmbTorus_upperRootGroup hF).map _ (MulAut.conj (g * c⁻¹)).injective

end Even

end CFSG.SeitzReduction.RankOne
