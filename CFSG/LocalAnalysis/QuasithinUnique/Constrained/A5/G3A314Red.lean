module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3A314Fam
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3A314Model

public section

namespace CFSG.QuasithinUnique.A5.G3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native
  CFSG.Assembly.LowTwoRank

theorem IsDelta5Group.isElemAbelian_pCore {B : Type} [Group B] (h : IsDelta5Group B) :
    IsElemAbelian 2 (CFSG.pCore 2 B) := by
  obtain ⟨α, β, -, -, hβ, -⟩ := h
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · apply hβ.1
    rw [map_mul, map_mul, mul_comm]
  · have hxx : (⟨x, hx⟩ : ↥(CFSG.pCore 2 B)) * ⟨x, hx⟩ = 1 := by
      apply hβ.1
      rw [map_mul, map_one]
      apply Multiplicative.toAdd.injective
      simp [evenWeight_add_self]
    rw [sq]
    exact congrArg Subtype.val hxx

theorem noDelta5In_of_card_lt {X : Type} [Group X] [Finite X]
    (h : ∀ E : Subgroup X, IsElemAbelian 2 E → Nat.card E < 16) : NoDelta5In X := by
  intro T hT B hB hne hTB hD
  have hE : IsElemAbelian 2 ((CFSG.pCore 2 ↥B).map B.subtype) :=
    Lin2.isElemAbelian_map' hD.isElemAbelian_pCore B.subtype
  have hcard : Nat.card ((CFSG.pCore 2 ↥B).map B.subtype) = 16 := by
    rw [Subgroup.card_map_of_injective B.subtype_injective]
    exact hD.card_pCore
  have := h _ hE
  omega

theorem card_lt_sixteen_of_card_eq {X : Type} [Group X] [Finite X] {m : ℕ}
    (hX : Nat.card X = 8 * m) (hm : ¬ 2 ∣ m) {E : Subgroup X} (hE : IsElemAbelian 2 E) :
    Nat.card E < 16 := by
  by_contra hlt
  push Not at hlt
  obtain ⟨j, hj⟩ := (Lin2.OddRank.isPGroup_two_of_isElemAbelian hE).exists_card_eq
  have hj4 : 4 ≤ j := by
    by_contra hj4
    have : 2 ^ j ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h16 : 16 ∣ Nat.card E := by
    rw [hj]
    exact pow_dvd_pow 2 hj4
  have h2 : 16 ∣ 8 * m := hX ▸ h16.trans (Subgroup.card_subgroup_dvd_card E)
  omega

theorem card_le_four_of_embedding {X : Type} [Group X] {F : Type} [Field F]
    (h2 : (2 : F) ≠ 0) (ι : X →* GL (Fin 3) F) (hι : Function.Injective ι)
    (hdet : ∀ x : X, (ι x : Matrix (Fin 3) (Fin 3) F).det = 1) {E : Subgroup X}
    (hE : IsElemAbelian 2 E) : Nat.card E ≤ 4 := by
  have hsq : ∀ x ∈ E.map ι, x * x = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← sq, hE.2 y hy, map_one]
  have hdet' : ∀ x ∈ E.map ι, (x : Matrix (Fin 3) (Fin 3) F).det = 1 := by
    rintro _ ⟨y, -, rfl⟩
    exact hdet y
  have h4 := CFSG.RankThree.SubgroupLists.card_le_four_of_sq_eq_one_sl3 h2 _ hsq hdet'
  rwa [Subgroup.card_map_of_injective hι] at h4

theorem noDelta5In_l3odd {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : IsPSL 3 p 1 X) : NoDelta5In X := by
  refine noDelta5In_of_card_lt fun E hE => ?_
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := h
  have hchar : CharP F p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp le_rfl hF
  have h2 : (2 : F) ≠ 0 := Lin2.two_ne_zero_of_charP hp hp2
  have hE' : IsElemAbelian 2 (E.map e.toMonoidHom) := Lin2.isElemAbelian_map' hE _
  have hc : Nat.card (E.map e.toMonoidHom) = Nat.card E :=
    Lin2.card_map_of_inf_ker_eq_bot E _ fun x _ hx => e.injective (by rw [map_one] at *; exact hx)
  have h4 := Lin2.card_le_four_of_stated_proj h2 (CFSG.Assembly.LowTwoRank.StatedSL 3 F)
    (fun x hx => Lin2.det_eq_one_of_mem_statedSL hx) hE'
  omega

theorem noDelta5In_u3odd {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : IsPSU 3 p 1 X) : NoDelta5In X := by
  refine noDelta5In_of_card_lt fun E hE => ?_
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := h
  have hchar : CharP F p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp
      (k := 2) (by norm_num) (by rw [hF]; ring)
  have h2 : (2 : F) ≠ 0 := Lin2.two_ne_zero_of_charP hp hp2
  have hE' : IsElemAbelian 2 (E.map e.toMonoidHom) := Lin2.isElemAbelian_map' hE _
  have hc : Nat.card (E.map e.toMonoidHom) = Nat.card E :=
    Lin2.card_map_of_inf_ker_eq_bot E _ fun x _ hx => e.injective (by rw [map_one] at *; exact hx)
  have h4 := Lin2.card_le_four_of_stated_proj h2
    (CFSG.Assembly.LowTwoRank.StatedSU 3 (p ^ 1) F)
    (fun x hx => Lin2.det_eq_one_of_mem_statedSU hx) hE'
  omega

theorem noDelta5In_sl3odd {X : Type} [Group X] [Finite X] {s : Bool} {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (h : IsSLEps3 s p X) : NoDelta5In X := by
  refine noDelta5In_of_card_lt fun E hE => ?_
  cases s
  · obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
    have hchar : CharP F p :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp
        (k := 2) (by norm_num) hF
    have h2 : (2 : F) ≠ 0 := Lin2.two_ne_zero_of_charP hp hp2
    have := card_le_four_of_embedding h2
      ((CFSG.Assembly.LowTwoRank.StatedSU 3 p F).subtype.comp e.toMonoidHom)
      ((CFSG.Assembly.LowTwoRank.StatedSU 3 p F).subtype_injective.comp e.injective)
      (fun x => Lin2.det_eq_one_of_mem_statedSU (e x).2) hE
    omega
  · obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
    have hchar : CharP F p :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp
        (k := 1) le_rfl (by rw [hF, pow_one])
    have h2 : (2 : F) ≠ 0 := Lin2.two_ne_zero_of_charP hp hp2
    have := card_le_four_of_embedding h2
      ((CFSG.Assembly.LowTwoRank.StatedSL 3 F).subtype.comp e.toMonoidHom)
      ((CFSG.Assembly.LowTwoRank.StatedSL 3 F).subtype_injective.comp e.injective)
      (fun x => Lin2.det_eq_one_of_mem_statedSL (e x).2) hE
    omega

theorem noDelta5In_hat7 {X : Type} [Group X] [Finite X]
    (h : IsHat X (alternatingGroup (Fin 7))) : NoDelta5In X := by
  obtain ⟨-, hc, ⟨e⟩⟩ := h
  have hcard := Lin2.OddRank.card_of_cover_alt (by norm_num) hc e
  refine noDelta5In_of_card_lt fun E hE => ?_
  exact card_lt_sixteen_of_card_eq (m := 945) (by rw [hcard]; decide) (by omega) hE

theorem noDelta5In_j1
    {X : Type} [Group X] [Finite X] (h : IsSporadic .J1 X) : NoDelta5In X := by
  obtain ⟨e⟩ := h
  have hcard : Nat.card X = 175560 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.J1.card_J1
  refine noDelta5In_of_card_lt fun E hE => ?_
  exact card_lt_sixteen_of_card_eq (m := 21945) (by rw [hcard]) (by omega) hE

structure Delta5Residual2 : Prop where
  rows : Delta5Rows
  m24 : ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X → IsSporadic .M24 X → NoDelta5In X
  j2 : ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X → IsSporadic .J2 X → NoDelta5In X
  hs : ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X → IsSporadic .HS X → NoDelta5In X
  he : ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X → IsSporadic .He X → NoDelta5In X
  ru : ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X → IsSporadic .Ru X → NoDelta5In X

theorem Delta5Residual2.toResidual
    (h : Delta5Residual2) : Delta5Residual where
  rows := h.rows
  l3odd := fun _ _ _ _ _ hp hp2 hm => noDelta5In_l3odd hp hp2 hm
  u3odd := fun _ _ _ _ _ hp hp2 hm => noDelta5In_u3odd hp hp2 hm
  sl3odd := fun _ _ _ _ _ _ hp hp2 hm => noDelta5In_sl3odd hp hp2 hm
  hat7 := fun _ _ _ _ hm => noDelta5In_hat7 hm
  m24 := h.m24
  j1 := fun _ _ _ _ hm => noDelta5In_j1 hm
  j2 := h.j2
  hs := h.hs
  he := h.he
  ru := h.ru

theorem a314A5Excluded_direct2
    (hT : ThreeCoverFactCat) (hcore : A36CoreForSQTKCat)
    (h37 : A37ForSQTKCat) (h39 : A39ForSQTKCat) (hR : Delta5Residual2) : A314A5Excluded :=
  a314A5Excluded_direct hT hcore h37 h39 a314ModelFacts hR.toResidual

end CFSG.QuasithinUnique.A5.G3
