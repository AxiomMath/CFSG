module

public import Mathlib.GroupTheory.Complement
public import Mathlib.GroupTheory.Sylow
public import CFSG.FeitThompson.Definitions.ElementaryAbelianPRank

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Pointwise Subgroup

namespace CFSG.FeitThompson

variable {Y : Type*} [Group Y] {p n : ℕ} {K : Subgroup Y}

theorem map_mk'_eq_top_of_isComplement' {P : Subgroup Y} [K.Normal] (h : IsComplement' K P) :
    Subgroup.map (QuotientGroup.mk' K) P = ⊤ := by
  have hmapK : Subgroup.map (QuotientGroup.mk' K) K = ⊥ :=
    (Subgroup.map_eq_bot_iff K).2 (QuotientGroup.ker_mk' K).ge
  calc Subgroup.map (QuotientGroup.mk' K) P
      = Subgroup.map (QuotientGroup.mk' K) K ⊔ Subgroup.map (QuotientGroup.mk' K) P := by
        rw [hmapK, bot_sup_eq]
    _ = Subgroup.map (QuotientGroup.mk' K) (K ⊔ P) := (Subgroup.map_sup _ _ _).symm
    _ = ⊤ := by
        rw [h.sup_eq_top, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective K)]

theorem inf_commutator_eq_commutator_of_isComplement' {P : Subgroup Y} [K.Normal]
    (h : IsComplement' K P) : P ⊓ commutator Y = ⁅P, P⁆ := by
  set π := QuotientGroup.mk' K with hπ
  have hker : π.ker = K := QuotientGroup.ker_mk' K
  have hbot : K ⊓ P = ⊥ := disjoint_iff.1 h.disjoint
  have key : Subgroup.map π (commutator Y) = Subgroup.map π ⁅P, P⁆ := by
    rw [_root_.commutator_def, Subgroup.map_commutator, Subgroup.map_commutator,
      map_mk'_eq_top_of_isComplement' h,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective K)]
  refine le_antisymm (fun x hx => ?_)
    (le_inf (Subgroup.commutator_le_self _) (Subgroup.commutator_mono le_top le_top))
  obtain ⟨hxP, hxY⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨y, hy, hxy⟩ : π x ∈ Subgroup.map π ⁅P, P⁆ := by
    rw [← key]; exact Subgroup.mem_map_of_mem _ hxY
  have h1 : y⁻¹ * x ∈ K := by
    rw [← hker]
    simp [MonoidHom.mem_ker, hxy]
  have h2 : y⁻¹ * x ∈ P := mul_mem (inv_mem (Subgroup.commutator_le_self _ hy)) hxP
  have h3 : y⁻¹ * x = 1 := Subgroup.mem_bot.1 (hbot ▸ Subgroup.mem_inf.2 ⟨h1, h2⟩)
  exact (inv_mul_eq_one.1 h3) ▸ hy

theorem inf_eq_bot_of_not_dvd_natCard_of_isPGroup [Finite Y] (hp : p.Prime)
    (hK : ¬ p ∣ Nat.card K) {P : Subgroup Y} (hP : IsPGroup p P) : K ⊓ P = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card (p := p) (G := (K ⊓ P : Subgroup Y))).1
    (IsPGroup.to_inf_right hP)
  have hm0 : m = 0 := by
    by_contra h
    exact hK ((dvd_pow_self p h).trans (hm ▸ Subgroup.card_dvd_of_le inf_le_left))
  exact Subgroup.card_eq_one.1 (by rw [hm, hm0, pow_zero])

section Sylow

variable [Finite Y] (hp : p.Prime) (hK : ¬ p ∣ Nat.card K) (hn : K.index = p ^ n) (P : Sylow p Y)

include hp hK hn

theorem natCard_sylow_eq_index : Nat.card P = K.index := by
  have : Fact p.Prime := ⟨hp⟩
  have hY : Nat.card Y = p ^ n * Nat.card K := by rw [← K.index_mul_card, hn]
  have hfac : (Nat.card Y).factorization p = n := by
    rw [hY, Nat.factorization_mul (pow_ne_zero n hp.pos.ne') Nat.card_pos.ne']
    simp [Nat.Prime.factorization_pow hp, Nat.factorization_eq_zero_of_not_dvd hK]
  rw [P.card_eq_multiplicity, hfac, hn]

theorem isComplement'_sylow_of_index_eq_pow : IsComplement' K P := by
  refine Subgroup.isComplement'_of_coprime ?_ ?_
  · rw [natCard_sylow_eq_index hp hK hn P, mul_comm, K.index_mul_card]
  · rw [natCard_sylow_eq_index hp hK hn P, hn]
    exact Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hp).2 hK).symm

omit hn in
theorem inf_sylow_eq_bot : K ⊓ (P : Subgroup Y) = ⊥ :=
  inf_eq_bot_of_not_dvd_natCard_of_isPGroup hp hK P.2

theorem coe_mul_coe_sylow_eq_univ :
    (K : Set Y) * ((P : Subgroup Y) : Set Y) = (Set.univ : Set Y) :=
  (isComplement'_sylow_of_index_eq_pow hp hK hn P).mul_eq

theorem sup_sylow_eq_top : K ⊔ (P : Subgroup Y) = ⊤ :=
  (isComplement'_sylow_of_index_eq_pow hp hK hn P).sup_eq_top

theorem sylow_inf_commutator_eq_commutator [K.Normal] :
    (P : Subgroup Y) ⊓ commutator Y = ⁅(P : Subgroup Y), (P : Subgroup Y)⁆ :=
  inf_commutator_eq_commutator_of_isComplement' (isComplement'_sylow_of_index_eq_pow hp hK hn P)

theorem map_subtype_commutator_eq_sylow_inf_commutator [K.Normal] :
    Subgroup.map (P : Subgroup Y).subtype (commutator (P : Subgroup Y))
      = (P : Subgroup Y) ⊓ commutator Y := by
  rw [sylow_inf_commutator_eq_commutator hp hK hn P, map_commutator_eq, Subgroup.subtype_range]

end Sylow

end CFSG.FeitThompson
