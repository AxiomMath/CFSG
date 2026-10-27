module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239InspL42Core
public import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalLinearFourTwo
public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineSLFourBasic

public section

namespace CFSG.SeitzReduction.SporadicRefine

open Equiv Subgroup
open CFSG.QuasithinUnique.Vol2Native.L239.L42Insp (P0 p0L pm pn pone mem_P0 pn_mul pn_inj pn_one
  P0_le_A8 card_P0)

set_option maxRecDepth 100000 in
theorem p0_centralizer_check : ∀ a ∈ p0L, pm a a ≠ pone →
    (p0L.filter (fun b => pm a b == pm b a)).length ≤ 16 := by
  decide +kernel

theorem card_subtype_mem_le_length (l : List ℕ) : Nat.card {a // a ∈ l} ≤ l.length := by
  classical
  have e : {a // a ∈ l} ≃ ↥l.toFinset := Equiv.subtypeEquivRight fun a => by simp
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]
  exact List.toFinset_card_le l

theorem card_le_sixteen_of_le_P0 {x : Perm (Fin 8)} (hx : x ∈ P0) (hx2 : x * x ≠ 1)
    {W : Subgroup (Perm (Fin 8))} (hW : W ≤ P0) (hWx : ∀ w ∈ W, w * x = x * w) :
    Nat.card W ≤ 16 := by
  classical
  set l := p0L.filter (fun b => pm (pn x) b == pm b (pn x)) with hl
  have hxl : pn x ∈ p0L := mem_P0.1 hx
  have hpx : pm (pn x) (pn x) ≠ pone := by
    rw [← pn_mul, ← pn_one]
    exact fun h => hx2 (pn_inj h)
  have hlen : l.length ≤ 16 := p0_centralizer_check (pn x) hxl hpx
  have hmap : ∀ w : W, pn (w : Perm (Fin 8)) ∈ l := by
    intro w
    rw [hl, List.mem_filter]
    refine ⟨mem_P0.1 (hW w.2), ?_⟩
    have h : pn (x * w) = pn (w * x) := by rw [hWx w w.2]
    rw [← pn_mul, ← pn_mul, h, beq_self_eq_true]
  let f : W → {b // b ∈ l} := fun w => ⟨pn w, hmap w⟩
  have hf : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (pn_inj (congrArg Subtype.val hab))
  calc Nat.card W ≤ Nat.card {b // b ∈ l} := Nat.card_le_card_of_injective f hf
    _ ≤ l.length := card_subtype_mem_le_length l
    _ ≤ 16 := hlen

theorem card_alternatingGroup_eight : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  rfl

theorem card_P0_subgroupOf : Nat.card (P0.subgroupOf (alternatingGroup (Fin 8))) = 64 := by
  rw [Nat.card_congr (subgroupOfEquivOfLe P0_le_A8).toEquiv, card_P0]

theorem card_P0_eq_factorization :
    Nat.card (P0.subgroupOf (alternatingGroup (Fin 8))) =
      2 ^ (Nat.card (alternatingGroup (Fin 8))).factorization 2 := by
  have h6 : (2 ^ 6 * 315 : ℕ).factorization 2 = 6 := by
    rw [Nat.factorization_mul (pow_ne_zero _ (by norm_num)) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 315)]
  rw [card_P0_subgroupOf, card_alternatingGroup_eight,
    show (20160 : ℕ) = 2 ^ 6 * 315 by norm_num, h6]
  norm_num

theorem card_le_sixteen_of_alternating {T : Subgroup (alternatingGroup (Fin 8))}
    (hT : IsPGroup 2 T) {q : alternatingGroup (Fin 8)} (hqT : q ∈ T) (hq2 : q * q ≠ 1)
    {W : Subgroup (alternatingGroup (Fin 8))} (hWT : W ≤ T) (hWq : ∀ w ∈ W, w * q = q * w) :
    Nat.card W ≤ 16 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hTQ⟩ := hT.exists_le_sylow
  set P : Sylow 2 (alternatingGroup (Fin 8)) :=
    Sylow.ofCard (P0.subgroupOf (alternatingGroup (Fin 8))) card_P0_eq_factorization with hP
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 8)) P Q
  have hconj : ∀ x ∈ T, ((g⁻¹ * x * g : alternatingGroup (Fin 8)) : Perm (Fin 8)) ∈ P0 := by
    intro x hx
    have hxQ : x ∈ (Q : Subgroup (alternatingGroup (Fin 8))) := hTQ hx
    rw [← hg, Sylow.coe_subgroup_smul, mem_pointwise_smul_iff_inv_smul_mem] at hxQ
    have h1 : (MulAut.conj g)⁻¹ • x = g⁻¹ * x * g := by
      rw [MulAut.smul_def, MulAut.inv_apply, MulAut.conj_symm_apply]
    rw [h1, hP, Sylow.coe_ofCard] at hxQ
    exact mem_subgroupOf.1 hxQ
  set W₀ : Subgroup (Perm (Fin 8)) :=
    (W.map (MulAut.conj g⁻¹).toMonoidHom).map (alternatingGroup (Fin 8)).subtype with hW₀
  have hW₀P : W₀ ≤ P0 := by
    rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    have h := hconj w (hWT hw)
    simpa [MulAut.conj_apply] using h
  have hq₀ : ((g⁻¹ * q * g : alternatingGroup (Fin 8)) : Perm (Fin 8)) * (g⁻¹ * q * g :
      alternatingGroup (Fin 8)) ≠ 1 := by
    intro h
    apply hq2
    have h' : (g⁻¹ * q * g) * (g⁻¹ * q * g) = (1 : alternatingGroup (Fin 8)) :=
      Subtype.ext (by rw [Subgroup.coe_mul, h]; rfl)
    calc q * q = g * ((g⁻¹ * q * g) * (g⁻¹ * q * g)) * g⁻¹ := by group
      _ = 1 := by rw [h']; group
  have hW₀q : ∀ w ∈ W₀, w * ((g⁻¹ * q * g : alternatingGroup (Fin 8)) : Perm (Fin 8)) =
      ((g⁻¹ * q * g : alternatingGroup (Fin 8)) : Perm (Fin 8)) * w := by
    rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    have h := hWq w hw
    have h' : (g⁻¹ * w * g) * (g⁻¹ * q * g) = (g⁻¹ * q * g) * (g⁻¹ * w * g) := by
      calc (g⁻¹ * w * g) * (g⁻¹ * q * g) = g⁻¹ * (w * q) * g := by group
        _ = g⁻¹ * (q * w) * g := by rw [h]
        _ = (g⁻¹ * q * g) * (g⁻¹ * w * g) := by group
    have h'' := congrArg Subtype.val h'
    simpa [MulAut.conj_apply] using h''
  have hcard : Nat.card W₀ = Nat.card W := by
    rw [hW₀, card_map_of_injective (alternatingGroup (Fin 8)).subtype_injective,
      card_map_of_injective (MulAut.conj g⁻¹).injective]
  rw [← hcard]
  exact card_le_sixteen_of_le_P0 (hconj q hqT) hq₀ hW₀P hW₀q

theorem nonempty_mulEquiv_alternating_of_SL_four {D : Type} [Group D] {K : Type} [Field K]
    (hK : Nat.card K = 2) (eD : D ≃* Matrix.SpecialLinearGroup (Fin 4) K) :
    Nonempty (D ≃* alternatingGroup (Fin 8)) := by
  have hK' : Nat.card K = 2 ^ 1 := by rw [hK, pow_one]
  have hm := LinearPilot.lieModel_quotient_center_of_mulEquiv_specialLinear (m := 4) hK'
    (by norm_num) eD
  obtain ⟨φ⟩ := (ComponentClassification.SymmetricLocal.lie_model_linear_four_two_iff _).1 hm
  exact ⟨(QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq
    (center_eq_bot_of_mulEquiv_SL_four hK eD).symm)).trans φ⟩

theorem card_le_sixteen_of_mulEquiv_SL_four {D : Type} [Group D] {K : Type} [Field K]
    (hK : Nat.card K = 2) (eD : D ≃* Matrix.SpecialLinearGroup (Fin 4) K) {T : Subgroup D}
    (hT : IsPGroup 2 T) {q : D} (hqT : q ∈ T) (hq : orderOf q = 4) {W : Subgroup D}
    (hWT : W ≤ T) (hWq : ∀ w ∈ W, w * q = q * w) : Nat.card W ≤ 16 := by
  obtain ⟨φ⟩ := nonempty_mulEquiv_alternating_of_SL_four hK eD
  have hq2 : φ q * φ q ≠ 1 := by
    intro h
    rw [← map_mul, ← map_one φ] at h
    have h1 : q ^ 2 = 1 := by rw [sq]; exact φ.injective h
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [hq] at h2
    norm_num at h2
  have hT' : IsPGroup 2 (T.map φ.toMonoidHom) := hT.map φ.toMonoidHom
  have h := card_le_sixteen_of_alternating hT' (mem_map_of_mem φ.toMonoidHom hqT) hq2
    (map_mono hWT) (by
      rintro _ ⟨w, hw, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom]
      rw [← map_mul, ← map_mul, hWq w hw])
  rwa [card_map_of_injective φ.injective] at h

end CFSG.SeitzReduction.SporadicRefine
