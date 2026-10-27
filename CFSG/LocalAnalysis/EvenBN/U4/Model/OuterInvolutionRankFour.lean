module

public import CFSG.LocalAnalysis.EvenBN.Common.Diagonal
public import CFSG.LocalAnalysis.SteinbergBNTwoFactorDiagonalGeneration
public import CFSG.LocalAnalysis.EvenBN.U4.Fusion

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Subgroup CFSG.Open CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_of_card)

namespace Setting

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {L : Subgroup G} {η : L ≃* gramSU h (miyamotoJ4 K)} {t : G}
  {Q T : Subgroup G}

include η in
omit [Finite G] in
theorem card_eq_card_L_mul_of_mulEquiv {A : Subgroup G}
    (ψ : A ⧸ center A ≃* gramSU h (miyamotoJ4 K)) :
    Nat.card A = Nat.card L * Nat.card (center A) := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center A), Nat.card_congr ψ.toEquiv,
    Nat.card_congr η.toEquiv]

theorem range_diagonalHom_eq_L (hS : Setting h L η t Q T) {A : Subgroup G} (hA : ⁅A, A⁆ = A)
    (ψ : A ⧸ center A ≃* gramSU h (miyamotoJ4 K))
    (hcomm : ⁅A, A.map (MulAut.conj t⁻¹).toMonoidHom⁆ = ⊥) :
    (Common.diagonalHom A t hcomm).range = L := by
  set δ := Common.diagonalHom A t hcomm with hδ
  have hAp : Group.IsPerfect A := (Common.isPerfect_subgroup_iff_commutator_eq A).2 hA
  have hle : δ.range ≤ L := by
    refine hS.perfect_le ?_ (Common.range_diagonalHom_le hcomm hS.t_mul_t)
    rw [MonoidHom.range_eq_map, ← map_commutator, ← _root_.commutator_def,
      Group.IsPerfect.commutator_eq_top]
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  have h1 := card_eq_card_L_mul_of_mulEquiv (η := η) ψ
  have h2 : Nat.card A = Nat.card δ.range * Nat.card δ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup δ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange δ).toEquiv]
  have h5 : Nat.card δ.ker ≤ Nat.card (center A) :=
    Subgroup.card_le_of_le (Common.ker_diagonalHom_le_center hcomm)
  have hpos : 0 < Nat.card (center A) := Nat.card_pos
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  calc Nat.card L * Nat.card (center A) = Nat.card δ.range * Nat.card δ.ker := by rw [← h1, h2]
    _ ≤ Nat.card δ.range * Nat.card (center A) := Nat.mul_le_mul_left _ h5

include η in
theorem factorization_card_eq {A : Subgroup G} (ψ : A ⧸ center A ≃* gramSU h (miyamotoJ4 K))
    (hZ : Odd (Nat.card (center A))) :
    (Nat.card A).factorization 2 = (Nat.card L).factorization 2 := by
  rw [card_eq_card_L_mul_of_mulEquiv (η := η) ψ, Nat.factorization_mul Nat.card_pos.ne'
    Nat.card_pos.ne', Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd
    (fun h2 => (Nat.not_even_iff_odd.2 hZ) (even_iff_two_dvd.2 h2)), add_zero]

theorem exists_isSylowOf_map_diagonalHom_eq (hS : Setting h L η t Q T) {A : Subgroup G}
    (hA : ⁅A, A⁆ = A) (ψ : A ⧸ center A ≃* gramSU h (miyamotoJ4 K))
    (hZ : Odd (Nat.card (center A)))
    (hcomm : ⁅A, A.map (MulAut.conj t⁻¹).toMonoidHom⁆ = ⊥) :
    ∃ U : Subgroup G, IsSylowOf 2 U A ∧
      (U.subgroupOf A).map (Common.diagonalHom A t hcomm) = miyamotoPG h L η := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set δ := Common.diagonalHom A t hcomm with hδ
  have hrange := hS.range_diagonalHom_eq_L hA ψ hcomm
  have hfac := factorization_card_eq (η := η) ψ hZ
  obtain ⟨U₀⟩ : Nonempty (Sylow 2 A) := inferInstance
  have hinj : Function.Injective (δ.comp (U₀ : Subgroup A).subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro u hu
    have hu1 : (u : A) ∈ δ.ker := hu
    have hZu : (u : A) ∈ center A := Common.ker_diagonalHom_le_center hcomm hu1
    obtain ⟨k, hk⟩ := U₀.isPGroup' u
    have h1 : orderOf (u : A) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (by
      simpa using congrArg Subtype.val hk)
    have h2 : orderOf (u : A) ∣ Nat.card (center A) := Subgroup.orderOf_dvd_natCard _ hZu
    have hcop : Nat.Coprime (2 ^ k) (Nat.card (center A)) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hZ)
    have := orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd (hcop.coprime_dvd_left h1) h2)
    exact mem_bot.2 (Subtype.ext this)
  set V : Subgroup G := (U₀ : Subgroup A).map δ with hV
  have hVrange : V = (δ.comp (U₀ : Subgroup A).subtype).range := by
    rw [MonoidHom.range_comp, range_subtype]
  have hVcard : Nat.card V = 2 ^ (Nat.card L).factorization 2 := by
    rw [hVrange, ← SetLike.coe_sort_coe, MonoidHom.coe_range, Nat.card_range_of_injective hinj,
      Sylow.card_eq_multiplicity, hfac]
  have hVL : V ≤ L := hrange ▸ map_le_range δ _
  have hVsyl : IsSylowOf 2 V L := isSylowOf_of_card hVL hVcard
  obtain ⟨c, hcL, hc⟩ := exists_conj_le_of_isSylowOf hS.isSylowOf_P hVL hVsyl.isPGroup
  have hVP : V.map (MulAut.conj c⁻¹).toMonoidHom = miyamotoPG h L η := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨v, hv, rfl⟩
      simpa using hc v hv
    · rw [card_map_of_injective (MulAut.conj c⁻¹).injective, hVcard,
        hS.isSylowOf_P.card_eq]
  obtain ⟨a, ha⟩ : c⁻¹ ∈ δ.range := hrange ▸ inv_mem hcL
  set U : Subgroup G := ((U₀ : Subgroup A).map (MulAut.conj a).toMonoidHom).map A.subtype
    with hU
  have hUA : U ≤ A := map_subtype_le _
  have hUcard : Nat.card U = 2 ^ (Nat.card A).factorization 2 := by
    rw [hU, card_map_of_injective A.subtype_injective,
      card_map_of_injective (MulAut.conj a).injective, Sylow.card_eq_multiplicity]
  refine ⟨U, isSylowOf_of_card hUA hUcard, le_antisymm ?_ ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨_, ⟨u, hu, rfl⟩, hux⟩ := mem_subgroupOf.1 hx
    have hxe : x = a * u * a⁻¹ := Subtype.ext hux.symm
    have e : δ x = c⁻¹ * δ u * c⁻¹⁻¹ := by rw [hxe, map_mul, map_mul, map_inv, ha]
    rw [← hVP, e]
    exact ⟨δ u, ⟨u, hu, rfl⟩, rfl⟩
  · intro p hp
    rw [← hVP] at hp
    obtain ⟨_, ⟨u, hu, rfl⟩, rfl⟩ := hp
    refine ⟨a * u * a⁻¹, ?_, ?_⟩
    · exact mem_subgroupOf.2 ⟨a * u * a⁻¹, ⟨u, hu, rfl⟩, rfl⟩
    · rw [map_mul, map_mul, map_inv, ha]
      rfl

theorem isSimpleGroup_quotient_center (hS : Setting h L η t Q T) {A : Subgroup G}
    (ψ : A ⧸ center A ≃* gramSU h (miyamotoJ4 K)) : IsSimpleGroup (A ⧸ center A) := by
  have : IsSimpleGroup (L ⧸ center L) := hS.standard.1.2
  have hZL := center_eq_bot_of_mulEquiv_gramSU h η
  let cL : L ≃* L ⧸ center L :=
    ((QuotientGroup.quotientMulEquivOfEq hZL).trans QuotientGroup.quotientBot).symm
  exact (ψ.trans (η.symm.trans cL)).isSimpleGroup

theorem even_card_L (hS : Setting h L η t Q T) : Even (Nat.card L) := by
  have h1 : Nat.card (miyamotoPG h L η) ∣ Nat.card L :=
    card_dvd_of_le (miyamotoPull_le h L η _)
  rw [card_miyamotoPG] at h1
  have h2 : 2 ∣ (2 ^ f) ^ 6 :=
    dvd_pow (dvd_pow_self 2 (by have := hS.two_le; omega)) (by norm_num)
  exact even_iff_two_dvd.2 (h2.trans h1)

theorem sup_le_of_swap (hS : Setting h L η t Q T) {A : Subgroup G} (hA : ⁅A, A⁆ = A)
    (ψ : A ⧸ center A ≃* gramSU h (miyamotoJ4 K)) (hZ : Odd (Nat.card (center A)))
    (hcomm : ⁅A, A.map (MulAut.conj t⁻¹).toMonoidHom⁆ = ⊥) {N₀ : Subgroup G} (hLN : L ≤ N₀)
    (hQN : normalizer (Q : Set G) ≤ N₀) :
    A ⊔ A.map (MulAut.conj t⁻¹).toMonoidHom ≤ N₀ := by
  have hAp : Group.IsPerfect A := (Common.isPerfect_subgroup_iff_commutator_eq A).2 hA
  set δ := Common.diagonalHom A t hcomm with hδ
  have hrange := hS.range_diagonalHom_eq_L hA ψ hcomm
  obtain ⟨U, hUsyl, hUP⟩ := hS.exists_isSylowOf_map_diagonalHom_eq hA ψ hZ hcomm
  have heven : Even (Nat.card (A ⧸ center A)) := by
    rw [Nat.card_congr ψ.toEquiv, ← Nat.card_congr η.toEquiv]
    exact hS.even_card_L
  have := hS.isSimpleGroup_quotient_center ψ
  have key := odd_center_two_factor_diagonal_normalizer_generation hS.t_two hZ this heven hcomm
    hUsyl.le hUsyl.exists_sylow_eq_subgroupOf
  simp only at key
  obtain ⟨-, -, -, -, hgen⟩ := key
  have himage : ∀ M : Subgroup G, M ≤ A → ((fun a => a * (t⁻¹ * a * t)) '' (M : Set G)) =
      ((M.subgroupOf A).map δ : Set G) := by
    intro M hM
    ext x
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact ⟨⟨m, hM hm⟩, mem_subgroupOf.2 hm, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨m, mem_subgroupOf.1 hm, rfl⟩
  have hδA : ((fun a => a * (t⁻¹ * a * t)) '' (A : Set G)) = (L : Set G) := by
    rw [himage A le_rfl, ← hrange, MonoidHom.range_eq_map]
    congr 2
    exact subgroupOf_self A
  have hδU : closure ((fun a => a * (t⁻¹ * a * t)) '' (U : Set G)) = miyamotoPG h L η := by
    rw [himage U hUsyl.le, closure_eq, hUP]
  rw [hδA, hδU, ← hS.Q_eq] at hgen
  rw [← hgen, closure_le]
  rintro x (hx | hx)
  · exact hLN hx
  · exact hQN (mem_inf.1 hx).2

end Setting

end CFSG.LocalAnalysis.EvenBN.U4
