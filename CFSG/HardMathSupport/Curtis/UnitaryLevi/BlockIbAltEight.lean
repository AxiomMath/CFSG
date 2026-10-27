module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.BlockIbParabCent
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.BlockIbGeneric
public import CFSG.HardMathSupport.Curtis.Proving.A8FixThree
public import CFSG.Quasithin.SteinbergCBAlternatingAut

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique CFSG.HardMathSupport.Curtis.Proving
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open scoped commutatorElement

section Eight

variable {Y : Type} [Group Y] [Finite Y] {Lb Pb : Subgroup Y}

noncomputable def mulEquivAltEight (hZ : Subgroup.center ↥Lb = ⊥)
    (e : ↥Lb ⧸ Subgroup.center ↥Lb ≃* alternatingGroup (Fin 8)) :
    ↥Lb ≃* alternatingGroup (Fin 8) :=
  MulEquiv.ofBijective (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥Lb)))
    ⟨by
      rw [injective_iff_map_eq_one]
      intro x hx
      have h1 : QuotientGroup.mk' (Subgroup.center ↥Lb) x = 1 := (MulEquiv.map_eq_one_iff e).1 hx
      have h2 : x ∈ Subgroup.center ↥Lb := (QuotientGroup.eq_one_iff x).1 h1
      rw [hZ, Subgroup.mem_bot] at h2
      exact h2, by
      intro y
      obtain ⟨q, rfl⟩ := e.surjective y
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥Lb) q
      exact ⟨x, rfl⟩⟩

omit [Finite Y] in
theorem card_outer_dvd_two_of_altEight (ε : ↥Lb ≃* alternatingGroup (Fin 8)) :
    Nat.card (Outer ↥Lb) ∣ 2 := by
  have h := (CFSG.Quasithin.SteinbergCB.isSolvable_outer_alternatingGroup
    (n := 8) (Or.inr (by norm_num))).2
  rwa [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence ε).toEquiv]

theorem card_parab_altEight (h : CompParab Lb Pb)
    (ε : ↥Lb ≃* alternatingGroup (Fin 8)) :
    Nat.card Pb = 64 ∨ Nat.card Pb = 192 ∨ Nat.card Pb = 576 ∨ Nat.card Pb = 1344 := by
  have hA8 : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  have hLcard : Nat.card ↥Lb = 20160 := by
    rw [Nat.card_congr ε.toEquiv, hA8]
  set φ : ↥Lb →* Equiv.Perm (Fin 8) :=
    (alternatingGroup (Fin 8)).subtype.comp ε.toMonoidHom with hφ
  have hφinj : Function.Injective φ := Subtype.val_injective.comp ε.injective
  obtain ⟨hJL, T, hT, hTN⟩ := h.parab
  have hTJ : T ≤ Pb := fun x hx => hTN ⟨hT.1 hx, Subgroup.le_normalizer hx⟩
  have hTL : T ≤ Lb := hT.1
  have hJc : Nat.card (Pb.subgroupOf Lb) = Nat.card Pb :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJL).toEquiv
  have hTc : Nat.card (T.subgroupOf Lb) = Nat.card T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTL).toEquiv
  have hTJb : T.subgroupOf Lb ≤ Pb.subgroupOf Lb := fun x hx =>
    Subgroup.mem_subgroupOf.2 (hTJ (Subgroup.mem_subgroupOf.1 hx))
  have hPA : (Pb.subgroupOf Lb).map φ ≤ alternatingGroup (Fin 8) := by
    rintro _ ⟨x, _, rfl⟩
    exact (ε x).2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hT.2.1
  have hodd2 := hT.2.2
  have hidx := Subgroup.card_mul_index (H := T.subgroupOf Lb)
  rw [hTc, hn, hLcard] at hidx
  have hn6 : n = 6 := by
    have hdvd : 2 ^ n ∣ 20160 := ⟨(T.subgroupOf Lb).index, hidx.symm⟩
    have hle : 2 ^ n ≤ 20160 := Nat.le_of_dvd (by norm_num) hdvd
    have hn15 : n < 15 := by
      by_contra hc
      rw [not_lt] at hc
      have := le_trans (Nat.pow_le_pow_right (by norm_num : 0 < 2) hc) hle
      norm_num at this
    interval_cases n <;> first | rfl | (norm_num at hidx; omega)
  have hPT : Nat.card ((T.subgroupOf Lb).map φ) = 64 := by
    rw [Subgroup.card_map_of_injective hφinj, hTc, hn, hn6]
    norm_num
  have hPTle : (T.subgroupOf Lb).map φ ≤ (Pb.subgroupOf Lb).map φ :=
    Subgroup.map_mono hTJb
  have hP2 : IsPGroup 2 ((T.subgroupOf Lb).map φ) :=
    (IsPGroup.iff_card).2 ⟨6, by rw [hPT]; norm_num⟩
  have hJopts := card_of_two_group_le hPA hPTle hP2 hPT
  rw [Subgroup.card_map_of_injective hφinj, hJc] at hJopts
  rcases hJopts with hJ | hJ | hJ | hJ | hJ
  · exact Or.inl hJ
  · exact Or.inr (Or.inl hJ)
  · exact Or.inr (Or.inr (Or.inl hJ))
  · exact Or.inr (Or.inr (Or.inr hJ))
  · exact absurd (Subgroup.eq_of_le_of_card_ge hJL (le_of_eq (by rw [hLcard, hJ]))) h.ne_top

theorem rank_altEight_of_card_eq (hpar : IsParabolicTwo Lb Pb) (hOut : Nat.card (Outer ↥Lb) ∣ 2)
    (hcard : Nat.card Pb = 1344) {E : Subgroup Y}
    (hEL : E ≤ Subgroup.normalizer (Lb : Set Y)) (hEP : E ≤ Subgroup.normalizer (Pb : Set Y))
    (hE3 : IsPGroup 3 E) (hE9 : Nat.card E = 3 ^ 2) :
    E ⊓ Subgroup.centralizer (Lb : Set Y) ≠ ⊥ := by
  intro hbot
  have hEW : E ≤ Pb ⊔ Subgroup.centralizer (Lb : Set Y) := by
    intro u hu
    obtain ⟨k, hk⟩ := hE3 ⟨u, hu⟩
    obtain ⟨p, hp, c, hc, rfl⟩ := exists_mul_of_normalizer_of_outer hpar hOut (hEL hu) (hEP hu)
      (k := k) (congrArg Subtype.val hk)
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hp) (Subgroup.mem_sup_right hc)
  obtain ⟨Q, _, _, θ, hθ, hQ⟩ := exists_quotient_hom hpar.1 hEW
  have hinj : Function.Injective θ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hac : (a : Y) ∈ E ⊓ Subgroup.centralizer (Lb : Set Y) := ⟨a.2, (hθ a).1 ha⟩
    rw [hbot, Subgroup.mem_bot] at hac
    exact Subtype.ext hac
  have h1 : Nat.card E ∣ Nat.card Q := Subgroup.card_dvd_of_injective θ hinj
  have h2 : 3 ^ 2 ∣ 1344 := by rw [← hE9, ← hcard]; exact h1.trans hQ
  norm_num at h2

theorem ab_altEight_of_card_eq (hpar : IsParabolicTwo Lb Pb) (hOut : Nat.card (Outer ↥Lb) ∣ 2)
    (hcard : Nat.card Pb = 1344) {U : Subgroup Y}
    (hUL : U ≤ Subgroup.normalizer (Lb : Set Y)) (hUP : U ≤ Subgroup.normalizer (Pb : Set Y))
    (hU3 : IsPGroup 3 U) :
    ∀ a ∈ U, ∀ b ∈ U, a * b * a⁻¹ * b⁻¹ ∈ Subgroup.centralizer (Lb : Set Y) := by
  have hUW : U ≤ Pb ⊔ Subgroup.centralizer (Lb : Set Y) := by
    intro u hu
    obtain ⟨k, hk⟩ := hU3 ⟨u, hu⟩
    obtain ⟨p, hp, c, hc, rfl⟩ := exists_mul_of_normalizer_of_outer hpar hOut (hUL hu) (hUP hu)
      (k := k) (congrArg Subtype.val hk)
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hp) (Subgroup.mem_sup_right hc)
  obtain ⟨Q, _, _, θ, hθ, hQ⟩ := exists_quotient_hom hpar.1 hUW
  have hR3 : IsPGroup 3 θ.range := hU3.of_surjective θ.rangeRestrict θ.rangeRestrict_surjective
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).1 hR3
  have hRQ : Nat.card θ.range ∣ Nat.card Q := Subgroup.card_subgroup_dvd_card _
  have hdvd : 3 ^ m ∣ 1344 := hm ▸ hRQ.trans (hcard ▸ hQ)
  have hm1 : m ≤ 1 := by
    by_contra hlt
    have : 3 ^ 2 ∣ 1344 :=
      (pow_dvd_pow 3 (by omega : 2 ≤ m)).trans hdvd
    norm_num at this
  have hcomm : ∀ x y : θ.range, x * y = y * x := by
    interval_cases m
    · have : Subsingleton θ.range := by
        have h1 : Nat.card θ.range = 1 := by simpa using hm
        exact (Nat.card_eq_one_iff_unique.1 h1).1
      intro x y; exact Subsingleton.elim _ _
    · have hc3 : Nat.card θ.range = 3 := by simpa using hm
      have := isCyclic_of_prime_card hc3
      intro x y
      exact (IsCyclic.isMulCommutative (α := θ.range)).is_comm.comm x y
  intro a ha b hb
  set A : ↥U := ⟨a, ha⟩
  set B : ↥U := ⟨b, hb⟩
  have key : θ A * θ B = θ B * θ A :=
    congrArg Subtype.val (hcomm ⟨θ A, ⟨A, rfl⟩⟩ ⟨θ B, ⟨B, rfl⟩⟩)
  have h1 : θ (A * B * A⁻¹ * B⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, key]
    group
  exact (hθ (A * B * A⁻¹ * B⁻¹)).1 h1

end Eight

section Assembly

variable {Y : Type} [Group Y] [Finite Y] {Lb Pb D : Subgroup Y} {x : Y}

theorem blockIb_altEight_cases (hP : BlockIbParab Lb Pb)
    (e : ↥Lb ⧸ Subgroup.center ↥Lb ≃* alternatingGroup (Fin 8)) (hD : BlockIbData Lb Pb D x) :
    Nat.card Pb = 1344 ∧ Nat.card (Outer ↥Lb) ∣ 2 := by
  have hCP : CompParab Lb Pb :=
    compParab_of_blockIb hP hD (Or.inr (Or.inl ⟨8, Or.inr (Or.inr rfl), ⟨e⟩⟩))
  have hZ : Subgroup.center ↥Lb = ⊥ := center_eq_bot_of_altEight hCP e
  set ε := mulEquivAltEight hZ e with hε
  have hOut := card_outer_dvd_two_of_altEight ε
  rcases card_parab_altEight hCP ε with h | h | h | h
  · exact (blockIb_false_of_isSolvable hP hD
      (isSolvable_of_card_two_pow_mul_three_pow (a := 6) (b := 0) (by rw [h]; norm_num))).elim
  · exact (blockIb_false_of_isSolvable hP hD
      (isSolvable_of_card_two_pow_mul_three_pow (a := 6) (b := 1) (by rw [h]; norm_num))).elim
  · exact (blockIb_false_of_isSolvable hP hD
      (isSolvable_of_card_two_pow_mul_three_pow (a := 6) (b := 2) (by rw [h]; norm_num))).elim
  · exact ⟨h, hOut⟩

theorem blockIb_altEight_rank (hP : BlockIbParab Lb Pb)
    (e : ↥Lb ⧸ Subgroup.center ↥Lb ≃* alternatingGroup (Fin 8)) (hD : BlockIbData Lb Pb D x)
    {E : Subgroup Y} (hEL : E ≤ Subgroup.normalizer (Lb : Set Y))
    (hEP : E ≤ Subgroup.normalizer (Pb : Set Y)) (hE9 : Nat.card E = 3 ^ 2) :
    E ⊓ Subgroup.centralizer (Lb : Set Y) ≠ ⊥ := by
  obtain ⟨hcard, hOut⟩ := blockIb_altEight_cases hP e hD
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact rank_altEight_of_card_eq hP.parab hOut hcard hEL hEP (IsPGroup.of_card hE9) hE9

theorem blockIb_altEight_ab (hP : BlockIbParab Lb Pb)
    (e : ↥Lb ⧸ Subgroup.center ↥Lb ≃* alternatingGroup (Fin 8)) (hD : BlockIbData Lb Pb D x)
    {U : Subgroup Y} (hUL : U ≤ Subgroup.normalizer (Lb : Set Y))
    (hUP : U ≤ Subgroup.normalizer (Pb : Set Y)) (hU3 : IsPGroup 3 U) :
    ∀ a ∈ U, ∀ b ∈ U, a * b * a⁻¹ * b⁻¹ ∈ Subgroup.centralizer (Lb : Set Y) := by
  obtain ⟨hcard, hOut⟩ := blockIb_altEight_cases hP e hD
  exact ab_altEight_of_card_eq hP.parab hOut hcard hUL hUP hU3

end Assembly

end CFSG.HardMathSupport.Curtis.UnitaryLevi
