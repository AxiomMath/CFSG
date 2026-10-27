module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKLift
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKDefs
public import CFSG.RankThree.SubgroupLists.SL3Involutions
public import CFSG.LinearAlgebra.LinearGroups.LinearTwoOddFourGroups
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKAbs

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.LocalAnalysis.ComponentInitial (finite_field_prime_power_characteristic)

section Three

variable {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem pow_three_eq_one_of_scalar {z : GL (Fin 3) F} (hz : z ∈ StatedScalars (Fin 3) F)
    (hdet : (z : Matrix (Fin 3) (Fin 3) F).det = 1) : z ^ 3 = 1 :=
  CFSG.Open.StatedAPI.pow_three_eq_one_of_mem_statedScalars hz hdet

theorem card_le_four_of_stated_proj (h2 : (2 : F) ≠ 0) (H : Subgroup (GL (Fin 3) F))
    (hdet : ∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) F).det = 1)
    {Ab : Subgroup (StatedProj H)} (hAb : IsElemAbelian 2 Ab) : Nat.card Ab ≤ 4 := by
  have : Finite H := inferInstance
  have hN : Odd (Nat.card ((StatedScalars (Fin 3) F).subgroupOf H)) := by
    refine odd_card_of_forall_odd_orderOf fun z => ?_
    have h3 : (z : H) ^ 3 = 1 := by
      apply Subtype.ext
      have hz : ((z : H) : GL (Fin 3) F) ∈ StatedScalars (Fin 3) F := z.2
      have := pow_three_eq_one_of_scalar hz (hdet _ (z : H).2)
      simpa using this
    have h4 : orderOf z ∣ 3 := by
      apply orderOf_dvd_of_pow_eq_one
      apply Subtype.ext
      simpa using h3
    exact Odd.of_dvd_nat (by decide) h4
  obtain ⟨E, hE, hcard⟩ := exists_isElemAbelian_lift _ hN hAb
  have hsq : ∀ x ∈ E.map H.subtype, x * x = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    have := hE.2 x hx
    rw [sq] at this
    exact congrArg Subtype.val this
  have hdet' : ∀ x ∈ E.map H.subtype, (x : Matrix (Fin 3) (Fin 3) F).det = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    exact hdet _ x.2
  have h4 := CFSG.RankThree.SubgroupLists.card_le_four_of_sq_eq_one_sl3 h2 _ hsq hdet'
  rwa [Subgroup.card_map_of_injective H.subtype_injective, hcard] at h4

omit [Finite F] in
theorem det_eq_one_of_mem_statedSL {n : ℕ} {x : GL (Fin n) F} (hx : x ∈ StatedSL n F) :
    (x : Matrix (Fin n) (Fin n) F).det = 1 :=
  CFSG.Open.StatedAPI.det_of_mem_statedSL hx

omit [Finite F] in
theorem det_eq_one_of_mem_statedSU {n q : ℕ} {x : GL (Fin n) F} (hx : x ∈ StatedSU n q F) :
    (x : Matrix (Fin n) (Fin n) F).det = 1 :=
  CFSG.Open.StatedAPI.det_of_mem_statedSU hx

end Three

section Two

open CFSG.ComponentClassification.CatalogueSchreierLinearTwo CFSG.LinearGroups CFSG.GorensteinWalter

variable {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem isElementaryAbelian_map {Y X : Type} [Group Y] [Group X] {E : Subgroup Y}
    (h : IsElemAbelian 2 E) (f : Y →* X) : CFSG.IsElementaryAbelian 2 (E.map f) := by
  have h' := isElemAbelian_map' h f
  have hexp : Monoid.exponent ↥(E.map f) ∣ 2 := by
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun x => ?_
    apply Subtype.ext
    exact h'.2 (x : X) x.2
  exact { toIsMulCommutative := h'.1, exponent_dvd_p := hexp }

theorem card_le_four_psl2
    (hF : ringChar F ≠ 2) {Ab : Subgroup (StatedProj (StatedSL 2 F))}
    (hAb : IsElemAbelian 2 Ab) : Nat.card Ab ≤ 4 := by
  have hodd := isOddPrimePower_card_of_ringChar_ne_two hF
  let ι₁ : StatedProj (StatedSL 2 F) ≃* coordinateG F :=
    (projectiveSpecialLinearGroupEquivStatedProj 2 F).symm.trans (pslEquivCoordinateG F)
  let ι : StatedProj (StatedSL 2 F) →* coordinateD F :=
    (Subgroup.inclusion (coordinateG_le_D F)).comp ι₁.toMonoidHom
  have hι : Function.Injective ι :=
    (Subgroup.inclusion_injective (coordinateG_le_D F)).comp ι₁.injective
  have := isElementaryAbelian_map hAb ι
  have h4 := card_le_four_of_isElementaryAbelian hodd (Ab.map ι)
  rwa [card_map_of_inf_ker_eq_bot Ab ι fun x _ hx => hι (by rw [hx, map_one])] at h4

end Two

section Exclusions

variable {G : Type} [Group G] [Finite G] {K B B' P R : Subgroup G} {m : ℕ}

omit [Finite G] in
theorem ExamConfig.exists_bar_elem_big (h : ExamConfig K B B' P R m) :
    ∃ Ab : Subgroup (↥K ⧸ Subgroup.center ↥K), IsElemAbelian 2 Ab ∧ 64 ≤ Nat.card Ab := by
  obtain ⟨Ab, hAb, hcard⟩ := h.toAbs.exists_bar_elem
  have hm := h.two_le
  have h6 : 2 ^ 6 ≤ 2 ^ (3 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact ⟨Ab, hAb, by omega⟩

omit [Finite G] in
theorem two_ne_zero_of_charP {F : Type} [Field F] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    [CharP F p] : (2 : F) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : F) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff F p] at h'
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h')

theorem examExcludes_oddL3 : ExamExcludes FamOddL3 := by
  rintro G _ _ K B B' P R m h ⟨p, hp, hp2, hmodel⟩
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hmodel
  obtain ⟨Ab, hAb, hcard⟩ := h.exists_bar_elem_big
  have hchar : CharP F p := finite_field_prime_power_characteristic hp le_rfl hF
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_charP hp hp2
  have hAb' : IsElemAbelian 2 (Ab.map e.toMonoidHom) := isElemAbelian_map' hAb _
  have hc : Nat.card (Ab.map e.toMonoidHom) = Nat.card Ab :=
    card_map_of_inf_ker_eq_bot Ab _ fun x _ hx => e.injective (by rw [map_one] at *; exact hx)
  have h4 := card_le_four_of_stated_proj h2 (StatedSL 3 F)
    (fun x hx => det_eq_one_of_mem_statedSL hx) hAb'
  omega

theorem examExcludes_oddU3 : ExamExcludes FamOddU3 := by
  rintro G _ _ K B B' P R m h ⟨p, hp, hp2, hmodel⟩
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hmodel
  obtain ⟨Ab, hAb, hcard⟩ := h.exists_bar_elem_big
  have hchar : CharP F p :=
    finite_field_prime_power_characteristic hp (k := 2) (by norm_num) (by rw [hF]; ring)
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_charP hp hp2
  have hAb' : IsElemAbelian 2 (Ab.map e.toMonoidHom) := isElemAbelian_map' hAb _
  have hc : Nat.card (Ab.map e.toMonoidHom) = Nat.card Ab :=
    card_map_of_inf_ker_eq_bot Ab _ fun x _ hx => e.injective (by rw [map_one] at *; exact hx)
  have h4 := card_le_four_of_stated_proj h2 (StatedSU 3 (p ^ 1) F)
    (fun x hx => det_eq_one_of_mem_statedSU hx) hAb'
  omega

theorem examExcludes_oddL2
    : ExamExcludes FamOddL2 := by
  rintro G _ _ K B B' P R m h ⟨p, hp, hp2, f, hf, hmodel⟩
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hmodel
  obtain ⟨Ab, hAb, hcard⟩ := h.exists_bar_elem_big
  have hf1 : 1 ≤ f := by rcases hf with rfl | rfl <;> norm_num
  have hchar : CharP F p := finite_field_prime_power_characteristic hp hf1 hF
  have hF2 : ringChar F ≠ 2 := by rw [ringChar.eq F p]; exact hp2
  have hAb' : IsElemAbelian 2 (Ab.map e.toMonoidHom) := isElemAbelian_map' hAb _
  have hc : Nat.card (Ab.map e.toMonoidHom) = Nat.card Ab :=
    card_map_of_inf_ker_eq_bot Ab _ fun x _ hx => e.injective (by rw [map_one] at *; exact hx)
  have h4 := card_le_four_psl2 hF2 hAb'
  omega

end Exclusions

end CFSG.QuasithinUnique.Lin2
