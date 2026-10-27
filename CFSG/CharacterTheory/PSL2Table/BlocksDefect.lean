module

public import CFSG.CharacterTheory.BlockBasics.Defects
public import CFSG.CharacterTheory.PSL2Table.Blocks
public import CFSG.CharacterTheory.PSL2Table.DirectProduct

public section

namespace CFSG.PSL2Table

open Matrix
open scoped MatrixGroups
open CFSG CFSG.BrauerThirdMainTheorem.Helpers CFSG.DirectProduct

section General

variable (m : Ideal BlocksAlgInt)

theorem charP_two (hm : m.IsMaximal) (h2 : (2 : BlocksAlgInt) ∈ m) :
    CharP (BlocksAlgInt ⧸ m) 2 := by
  have := Ideal.Quotient.nontrivial_iff.mpr hm.ne_top
  rw [CharP.charP_iff_prime_eq_zero Nat.prime_two, ← map_natCast (Ideal.Quotient.mk m) 2,
    Ideal.Quotient.eq_zero_iff_mem]
  exact_mod_cast h2

theorem intCast_not_mem_localMaxIdeal (hm : m.IsMaximal) (h2 : (2 : BlocksAlgInt) ∈ m) {n : ℤ}
    (hn : Odd n) : (n : ℂ) ∉ BlocksLocalMaxIdeal m := by
  intro h
  apply odd_not_mem m hm h2 hn
  rw [← localMaxIdeal_algInt_iff m hm]
  simpa using h

theorem mem_of_odd_mul_mem (hm : m.IsMaximal) (h2 : (2 : BlocksAlgInt) ∈ m) {n : ℤ}
    (hn : Odd n) {s : ℂ} (h : (n : ℂ) * s ∈ BlocksLocalMaxIdeal m) :
    s ∈ BlocksLocalMaxIdeal m := by
  have hn0 : (n : ℂ) ≠ 0 := by
    have : n ≠ 0 := by
      rintro rfl
      exact Int.not_even_iff_odd.mpr hn ⟨0, rfl⟩
    exact_mod_cast this
  have := localMaxIdeal_mul_localRing m hm h (inv_odd_mem_localRing m hm h2 hn)
  rwa [mul_comm (n : ℂ) s, mul_assoc, mul_inv_cancel₀ hn0, mul_one] at this

theorem pow_mem_localRing (hm : m.IsMaximal) {x : ℂ} (hx : x ∈ BlocksLocalRing m) (n : ℕ) :
    x ^ n ∈ BlocksLocalRing m := by
  induction n with
  | zero => simpa using localRing_one m hm
  | succ n ih =>
    rw [pow_succ]
    exact localRing_mul m hm ih hx

theorem card_sylow_two_of_card {G : Type} [Group G] [Finite G] {a N : ℕ} (hN : Odd N)
    (hG : Nat.card G = 2 ^ a * N) (P : Sylow 2 G) : Nat.card P = 2 ^ a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp P.isPGroup'
  have hlow : 2 ^ a ∣ Nat.card P :=
    P.pow_dvd_card_of_pow_dvd_card (by rw [hG]; exact Dvd.intro N rfl)
  have hup : Nat.card P ∣ Nat.card G := Subgroup.card_subgroup_dvd_card _
  rw [hn] at hlow hup ⊢
  have h1 : a ≤ n := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hlow
  have h2 : n ≤ a := by
    by_contra hlt
    push Not at hlt
    have hdvd : 2 ^ a * 2 ∣ 2 ^ a * N := by
      rw [← hG, ← pow_succ]
      exact (pow_dvd_pow 2 hlt).trans hup
    have := Nat.dvd_of_mul_dvd_mul_left (by positivity) hdvd
    obtain ⟨c, hc⟩ := hN
    omega
  rw [le_antisymm h2 h1]

theorem mk_conj_eq {G : Type} [Group G] (g h : G) :
    ConjClasses.mk (h * g * h⁻¹) = ConjClasses.mk g :=
  ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.mpr ⟨h, rfl⟩).symm

theorem card_centralizer_eq_of_mk_eq {G : Type} [Group G] [Finite G] {e e' : G}
    (h : ConjClasses.mk e' = ConjClasses.mk e) :
    Nat.card (Subgroup.centralizer {e'}) = Nat.card (Subgroup.centralizer {e}) := by
  have h1 := card_carrier_mul_card_centralizer e
  have h2 := card_carrier_mul_card_centralizer e'
  rw [h] at h2
  have hpos : 0 < Nat.card (ConjClasses.mk e).carrier :=
    Nat.card_pos_iff.mpr ⟨⟨⟨e, ConjClasses.mem_carrier_mk⟩⟩, inferInstance⟩
  exact Nat.eq_of_mul_eq_mul_left hpos (h2.trans h1.symm)

theorem card_centralizer_one {G : Type} [Group G] [Finite G] :
    Nat.card (Subgroup.centralizer {(1 : G)}) = Nat.card G := by
  have h := card_carrier_mul_card_centralizer (1 : G)
  rwa [card_carrier_one, one_mul] at h

theorem card_classDefect {G : Type} [Group G] [Finite G] {e : G} {D : Subgroup G}
    (hD : classDefect 2 (ConjClasses.mk e) D) {a N : ℕ} (hN : Odd N)
    (hC : Nat.card (Subgroup.centralizer {e}) = 2 ^ a * N) : Nat.card D = 2 ^ a := by
  obtain ⟨e', he', S, rfl⟩ := hD
  rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  exact card_sylow_two_of_card hN ((card_centralizer_eq_of_mk_eq he').trans hC) S

theorem card_blockDefect_le {G : Type} [Group G] [Finite G] {χ : G → ℂ} {D : Subgroup G}
    (hD : blockDefect 2 m χ D) {e : G}
    (he : BlocksCentralChar χ (classCoefficients (ConjClasses.mk e)) ∉ BlocksLocalMaxIdeal m)
    {a N : ℕ} (hN : Odd N) (hC : Nat.card (Subgroup.centralizer {e}) = 2 ^ a * N) :
    Nat.card D ≤ 2 ^ a := by
  obtain ⟨D', hD'⟩ := classDefect_exists 2 (ConjClasses.mk e)
  rw [← card_classDefect hD' hN hC]
  exact subgroupSubconjugate_card_le (hD.2 _ he D' hD')

theorem two_dvd_card_blockDefect {G : Type} [Group G] [Finite G] {χ : G → ℂ}
    {D : Subgroup G} (hD : blockDefect 2 m χ D)
    (h : ∀ e : G, BlocksCentralChar χ (classCoefficients (ConjClasses.mk e)) ∉
      BlocksLocalMaxIdeal m → 2 ∣ Nat.card (Subgroup.centralizer {e})) :
    2 ∣ Nat.card D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, ⟨e, rfl, S, rfl⟩, hω⟩ := hD.1
  rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  exact S.dvd_card_of_dvd_card (h e hω)

theorem exists_trace_not_mem (hm : m.IsMaximal) (h2 : (2 : BlocksAlgInt) ∈ m) {A : Type}
    [Group A] [Finite A] (hA : Nat.card A % 4 = 2) {β : A →* ℂˣ} (hβ : β ^ 2 ≠ 1) :
    ∃ w : A, w ^ 2 ≠ 1 ∧ (β w : ℂ) + (β w⁻¹ : ℂ) ∉ BlocksLocalMaxIdeal m := by
  obtain ⟨y, hy⟩ : ∃ y : A, (β y : ℂ) ^ 2 ≠ 1 := by
    by_contra hall
    push Not at hall
    apply hβ
    ext y
    simp only [sq, MonoidHom.mul_apply, MonoidHom.one_apply, Units.val_mul, Units.val_one]
    rw [← sq]
    exact hall y
  obtain ⟨j, hj⟩ : ∃ j, Nat.card A = 4 * j + 2 := ⟨Nat.card A / 4, by omega⟩
  have hzn : (β y : ℂ) ^ (4 * j + 2) = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, ← hj, pow_card_eq_one', map_one, Units.val_one]
  have hz4 : (β y : ℂ) ^ 4 ≠ 1 := by
    intro h4
    apply hy
    have : (β y : ℂ) ^ (4 * j + 2) = ((β y : ℂ) ^ 4) ^ j * (β y : ℂ) ^ 2 := by ring
    rw [this, h4, one_pow, one_mul] at hzn
    exact hzn
  have hzInt : IsIntegral ℤ (β y : ℂ) :=
    IsIntegral.of_pow (n := 4 * j + 2) (by omega) (by rw [hzn]; exact isIntegral_one)
  have hzR := integral_mem_localRing m hm hzInt
  have hz0 : (β y : ℂ) ≠ 0 := Units.ne_zero _
  refine ⟨y ^ 2, fun h => hz4 ?_, ?_⟩
  · have := congrArg (fun a => (β a : ℂ)) h
    simp only [map_pow, Units.val_pow_eq_pow_val, map_one, Units.val_one] at this
    rw [← this]
    ring
  · have hval : (β (y ^ 2) : ℂ) + (β (y ^ 2)⁻¹ : ℂ) = (β y : ℂ) ^ 2 + ((β y : ℂ) ^ 2)⁻¹ := by
      simp only [map_inv, map_pow, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
    rw [hval]
    intro hmem
    have hξ : (β y : ℂ) ^ 4 - 1 ∈ BlocksLocalMaxIdeal m := by
      have h1 : ((β y : ℂ) ^ 2 + ((β y : ℂ) ^ 2)⁻¹) * (β y : ℂ) ^ 2 ∈ BlocksLocalMaxIdeal m :=
        localMaxIdeal_mul_localRing m hm hmem (pow_mem_localRing m hm hzR 2)
      have : (β y : ℂ) ^ 4 - 1 = ((β y : ℂ) ^ 2 + ((β y : ℂ) ^ 2)⁻¹) * (β y : ℂ) ^ 2 - 2 := by
        field_simp
        ring
      rw [this]
      exact localMaxIdeal_sub m hm h1 (two_mem_localMaxIdeal m hm h2)
    have hterm : ∀ i : ℕ, ((β y : ℂ) ^ 4) ^ i - 1 ∈ BlocksLocalMaxIdeal m := by
      intro i
      rw [← geom_sum_mul, mul_comm]
      exact localMaxIdeal_mul_localRing m hm hξ (localRing_sum m hm _ _
        (fun l _ => pow_mem_localRing m hm (pow_mem_localRing m hm hzR 4) l))
    have hsum : ∑ i ∈ Finset.range (2 * j + 1), ((β y : ℂ) ^ 4) ^ i = 0 := by
      have h := geom_sum_mul ((β y : ℂ) ^ 4) (2 * j + 1)
      have hr : ((β y : ℂ) ^ 4) ^ (2 * j + 1) = 1 := by
        rw [← pow_mul, show 4 * (2 * j + 1) = (4 * j + 2) * 2 by ring, pow_mul, hzn, one_pow]
      rw [hr, sub_self] at h
      exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr hz4)
    have hall := localMaxIdeal_sum m hm (Finset.range (2 * j + 1))
      (fun i => ((β y : ℂ) ^ 4) ^ i - 1) (fun i _ => hterm i)
    rw [Finset.sum_sub_distrib, hsum, Finset.sum_const, Finset.card_range] at hall
    apply intCast_not_mem_localMaxIdeal m hm h2 (n := 2 * j + 1) ⟨j, by ring⟩
    have := localMaxIdeal_neg m hall
    simpa using this

theorem dvd_two_of_dvd_eight {n : ℕ} (h : n ∣ 8) (h4 : ¬ 4 ∣ n) : n ∣ 2 := by
  have hpos : 0 < n := Nat.pos_of_dvd_of_pos h (by norm_num)
  have hle : n ≤ 8 := Nat.le_of_dvd (by norm_num) h
  interval_cases n <;> omega

end General

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

omit [DecidableEq F] in
theorem card_PSL_eq_four_mul_odd (hF : ringChar F ≠ 2)
    (h8 : Fintype.card F % 8 = 3 ∨ Fintype.card F % 8 = 5) :
    ∃ N, Odd N ∧ Nat.card PSL(2, F) = 2 ^ 2 * N := by
  rcases h8 with h8 | h8
  · obtain ⟨k, hk⟩ : ∃ k, Fintype.card F = 8 * k + 3 := ⟨Fintype.card F / 8, by omega⟩
    refine ⟨(8 * k + 3) * (8 * k ^ 2 + 6 * k + 1),
      Odd.mul ⟨4 * k + 1, by ring⟩ ⟨4 * k ^ 2 + 3 * k, by ring⟩, ?_⟩
    have : (Nat.card PSL(2, F) : ℂ) =
        ((2 ^ 2 * ((8 * k + 3) * (8 * k ^ 2 + 6 * k + 1)) : ℕ) : ℂ) := by
      rw [card_PSL_of_eq_three hF hk]
      push_cast
      ring
    exact_mod_cast this
  · obtain ⟨k, hk⟩ : ∃ k, Fintype.card F = 8 * k + 5 := ⟨Fintype.card F / 8, by omega⟩
    refine ⟨(8 * k + 5) * (8 * k ^ 2 + 10 * k + 3),
      Odd.mul ⟨4 * k + 2, by ring⟩ ⟨4 * k ^ 2 + 5 * k + 1, by ring⟩, ?_⟩
    have : (Nat.card PSL(2, F) : ℂ) =
        ((2 ^ 2 * ((8 * k + 5) * (8 * k ^ 2 + 10 * k + 3)) : ℕ) : ℂ) := by
      rw [card_PSL_of_eq_five hF hk]
      push_cast
      ring
    exact_mod_cast this

theorem not_four_dvd_orderOf (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F) {ν : F}
    (hν : ¬ IsSquare ν) (h8 : Fintype.card F % 8 = 3 ∨ Fintype.card F % 8 = 5)
    (g : PSL(2, F)) : ¬ 4 ∣ orderOf g := by
  have hT := card_splitTorus (Ring.two_ne_zero hF) (F := F)
  have hS := card_nonsplitTorus hF hν
  have hP := card_unipotent (Ring.two_ne_zero hF) (F := F)
  have key : ∀ {H : Subgroup PSL(2, F)}, ¬ 4 ∣ Nat.card H → ∀ x ∈ H, x ≠ 1 → ¬ 4 ∣ orderOf x :=
    fun hH x hx _ h4 => hH (h4.trans (Subgroup.orderOf_dvd_natCard _ hx))
  apply forall_of_families hF hq hν (P := fun g => ¬ 4 ∣ orderOf g)
  · intro g h hg
    have := orderOf_injective (MulAut.conj h).toMonoidHom (MulAut.conj h).injective g
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
    rwa [this] at hg
  · rw [orderOf_one]
    omega
  · exact key (by omega)
  · exact key (by omega)
  · exact key (by omega)

theorem sylow_two_psl2 (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F) {ν : F}
    (hν : ¬ IsSquare ν) (h8 : Fintype.card F % 8 = 3 ∨ Fintype.card F % 8 = 5)
    (P : Sylow 2 PSL(2, F)) : Nat.card P = 4 ∧ ∀ x ∈ P, x ^ 2 = 1 := by
  obtain ⟨N, hN, hG⟩ := card_PSL_eq_four_mul_odd hF h8
  have hcard : Nat.card P = 4 := card_sylow_two_of_card hN hG P
  refine ⟨hcard, fun x hx => ?_⟩
  have hdvd : orderOf x ∣ 8 := (hcard ▸ Subgroup.orderOf_dvd_natCard _ hx).trans (by norm_num)
  exact orderOf_dvd_iff_pow_eq_one.mp
    (dvd_two_of_dvd_eight hdvd (not_four_dvd_orderOf hF hq hν h8 x))

theorem sylow_two_prod_psl2 (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F) {ν : F}
    (hν : ¬ IsSquare ν) (h8 : Fintype.card F % 8 = 3 ∨ Fintype.card F % 8 = 5) {Z : Type}
    [Group Z] [Fintype Z] (hZ : Nat.card Z = 2) (P : Sylow 2 (Z × PSL(2, F))) :
    Nat.card P = 8 ∧ ∀ x ∈ P, x ^ 2 = 1 := by
  obtain ⟨N, hN, hG⟩ := card_PSL_eq_four_mul_odd hF h8
  have hcard : Nat.card P = 2 ^ 3 := card_sylow_two_of_card hN
    (by rw [Nat.card_prod, hZ, hG]; ring) P
  refine ⟨hcard, fun x hx => ?_⟩
  have hx8 : orderOf x ∣ 8 := by
    have := Subgroup.orderOf_dvd_natCard _ hx
    rw [hcard] at this
    norm_num at this
    exact this
  have hx2 : orderOf x.2 ∣ 8 := by
    refine (orderOf_dvd_of_pow_eq_one ?_).trans hx8
    rw [← Prod.pow_snd, pow_orderOf_eq_one, Prod.snd_one]
  have h2 : x.2 ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp
    (dvd_two_of_dvd_eight hx2 (not_four_dvd_orderOf hF hq hν h8 x.2))
  have h1 : x.1 ^ 2 = 1 := by
    rw [sq]
    exact mul_self_of_card_two hZ x.1
  exact Prod.ext h1 h2

omit [DecidableEq F] in
theorem card_carrier_unip_complex (hF : ringChar F ≠ 2) {t : F} (ht : t ≠ 0) :
    (Nat.card (ConjClasses.mk (mk (unip t) : PSL(2, F))).carrier : ℂ) =
      ((Fintype.card F : ℂ) ^ 2 - 1) / 2 := by
  have h := card_carrier_mul_card_centralizer (mk (unip t) : PSL(2, F))
  rw [card_centralizer_unip hF ht] at h
  have hc := congrArg (Nat.cast : ℕ → ℂ) h
  push_cast at hc
  rw [card_PSL_complex hF] at hc
  have hq0 : (Fintype.card F : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  apply mul_right_cancel₀ hq0
  linear_combination hc

theorem card_carrier_split_complex (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F)
    {x : PSL(2, F)} (hx : x ∈ splitTorus F) (hx1 : x ≠ 1) (hx2 : x ^ 2 ≠ 1) :
    (Nat.card (ConjClasses.mk x).carrier : ℂ) =
      (Fintype.card F : ℂ) * ((Fintype.card F : ℂ) + 1) := by
  have h := card_carrier_mul_card_centralizer x
  rw [card_centralizer_splitTorus hF hq hx hx1, ite_eq_right hx2] at h
  have hc := congrArg (Nat.cast : ℕ → ℂ) h
  push_cast at hc
  rw [card_PSL_complex hF, card_splitTorus_complex hF] at hc
  have hq1 : (Fintype.card F : ℂ) - 1 ≠ 0 := by
    rw [sub_ne_zero]
    exact_mod_cast (show Fintype.card F ≠ 1 by omega)
  apply mul_right_cancel₀ hq1
  linear_combination 2 * hc

theorem card_carrier_nonsplit_complex (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F) {ν : F}
    (hν : ¬ IsSquare ν) {x : PSL(2, F)} (hx : x ∈ nonsplitTorus ν) (hx1 : x ≠ 1)
    (hx2 : x ^ 2 ≠ 1) :
    (Nat.card (ConjClasses.mk x).carrier : ℂ) =
      (Fintype.card F : ℂ) * ((Fintype.card F : ℂ) - 1) := by
  have h := card_carrier_mul_card_centralizer x
  rw [card_centralizer_nonsplitTorus hF hq hν hx hx1, ite_eq_right hx2] at h
  have hc := congrArg (Nat.cast : ℕ → ℂ) h
  push_cast at hc
  rw [card_PSL_complex hF, card_nonsplitTorus_complex hF hν] at hc
  have hq1 : (Fintype.card F : ℂ) + 1 ≠ 0 := by
    exact_mod_cast (show Fintype.card F + 1 ≠ 0 by omega)
  apply mul_right_cancel₀ hq1
  linear_combination 2 * hc

theorem psl2_blockDefects_of_mod_eight_eq_three (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F)
    {ν : F} (hν : ¬ IsSquare ν) (h8 : Fintype.card F % 8 = 3) (m : Ideal BlocksAlgInt)
    (hm : m.IsMaximal) (h2 : (2 : BlocksAlgInt) ∈ m) :
    (∀ D : Subgroup PSL(2, F),
      (∀ χ ∈ BlocksPrincipalBlock m PSL(2, F), blockDefect 2 m χ D) ↔
        ∃ P : Sylow 2 PSL(2, F), (P : Subgroup PSL(2, F)) = D) ∧
    (∀ P : Sylow 2 PSL(2, F), Nat.card P = 4 ∧ ∀ x ∈ P, x ^ 2 = 1) ∧
    (∀ α : splitTorus F →* ℂˣ, α ^ 2 ≠ 1 →
      (∃ D, blockDefect 2 m (principal α) D) ∧
        ∀ D, blockDefect 2 m (principal α) D → Nat.card D = 1) ∧
    (∀ β : nonsplitTorus ν →* ℂˣ, β ^ 2 ≠ 1 →
      (∃ D, blockDefect 2 m (discrete β) D) ∧
        ∀ D, blockDefect 2 m (discrete β) D → Nat.card D = 2) := by
  obtain ⟨k, hk⟩ : ∃ k, Fintype.card F = 8 * k + 3 := ⟨Fintype.card F / 8, by omega⟩
  have := charP_two m hm h2
  have := hm
  have h2' : ((2 : ℕ) : BlocksAlgInt) ∈ m := by exact_mod_cast h2
  have h2ne : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have hu : (mk (unip 1) : PSL(2, F)) ∈ unipotent F := mk_unip_mem_unipotent 1
  have hu1 : (mk (unip 1) : PSL(2, F)) ≠ 1 :=
    fun h => one_ne_zero ((mk_unip_eq_one_iff h2ne 1).mp h)
  have hCu : Nat.card (Subgroup.centralizer {(mk (unip 1) : PSL(2, F))}) =
      2 ^ 0 * (8 * k + 3) := by
    rw [card_centralizer_unip hF one_ne_zero, hk]
    ring
  have hoddq : Odd (8 * k + 3) := ⟨4 * k + 1, by ring⟩
  refine ⟨(CFSG.BlockBasics.principal_block_defect 2 Nat.prime_two m PSL(2, F)).1,
    sylow_two_psl2 hF hq hν (Or.inl h8), fun α hα => ?_, fun β hβ => ?_⟩
  ·
    have hR := principal_mem_blocksIrr hF hq hν hα
    refine ⟨blockDefect_exists 2 Nat.prime_two m hm h2' _ hR, fun D hD => ?_⟩
    have hω : BlocksCentralChar (principal α)
        (classCoefficients (ConjClasses.mk (mk (unip 1) : PSL(2, F)))) ∉
          BlocksLocalMaxIdeal m := by
      rw [centralChar_classCoefficients
        (blocksVChar_isClassFunction (AddSubgroup.subset_closure hR)),
        card_carrier_unip_complex hF one_ne_zero, principal_of_mem_unipotent hF α hu hu1,
        principal_one hF, hk]
      have : (((((8 * k + 3 : ℕ) : ℂ) ^ 2 - 1) / 2 * 1) / (((8 * k + 3 : ℕ) : ℂ) + 1)) =
          ((4 * k + 1 : ℤ) : ℂ) := by
        rw [div_eq_iff (by exact_mod_cast (show 8 * k + 3 + 1 ≠ 0 by omega))]
        push_cast
        ring
      rw [this]
      exact intCast_not_mem_localMaxIdeal m hm h2 ⟨2 * k, by ring⟩
    have hle := card_blockDefect_le m hD hω hoddq hCu
    have hpos : 0 < Nat.card D := Nat.card_pos
    simp only [pow_zero] at hle
    omega
  ·
    have hD := discrete_mem_blocksIrr hF hq hν hβ
    have hDc := blocksVChar_isClassFunction (AddSubgroup.subset_closure hD)
    refine ⟨blockDefect_exists 2 Nat.prime_two m hm h2' _ hD, fun D hDD => ?_⟩
    have hS : Nat.card (nonsplitTorus ν) = 4 * k + 2 := by
      have := card_nonsplitTorus hF hν
      omega
    have hq1 : ((8 * k + 3 : ℕ) : ℂ) - 1 ≠ 0 := by
      rw [sub_ne_zero]
      exact_mod_cast (show 8 * k + 3 ≠ 1 by omega)
    obtain ⟨w, hw2, hwM⟩ := exists_trace_not_mem m hm h2 (by omega : Nat.card _ % 4 = 2) hβ
    have hx2 : (w : PSL(2, F)) ^ 2 ≠ 1 := fun h => hw2 (Subtype.ext (by simpa using h))
    have hx1 : (w : PSL(2, F)) ≠ 1 := fun h => hx2 (by rw [h, one_pow])
    have hωw : BlocksCentralChar (discrete β)
        (classCoefficients (ConjClasses.mk (w : PSL(2, F)))) ∉ BlocksLocalMaxIdeal m := by
      rw [centralChar_classCoefficients hDc, card_carrier_nonsplit_complex hF hq hν w.2 hx1 hx2,
        discrete_of_mem_nonsplitTorus hF hν β w.2 hx1, discrete_one hF hν, hk]
      intro hmem
      apply hwM
      simp only [Subtype.coe_eta] at hmem
      have hval : ((8 * k + 3 : ℕ) : ℂ) * (((8 * k + 3 : ℕ) : ℂ) - 1) *
          -((β w : ℂ) + (β w⁻¹ : ℂ)) / (((8 * k + 3 : ℕ) : ℂ) - 1) =
          ((-(8 * k + 3) : ℤ) : ℂ) * ((β w : ℂ) + (β w⁻¹ : ℂ)) := by
        rw [div_eq_iff hq1]
        push_cast
        ring
      rw [hval] at hmem
      exact mem_of_odd_mul_mem m hm h2 ⟨-(4 * k + 2), by ring⟩ hmem
    have hle := card_blockDefect_le m hDD hωw (a := 1) (N := 2 * k + 1) ⟨k, by ring⟩
      (by rw [card_centralizer_nonsplitTorus hF hq hν w.2 hx1, ite_eq_right hx2, hS]; ring)
    have hlow := two_dvd_card_blockDefect m hDD (fun e => by
      apply forall_of_families hF hq hν (P := fun e =>
        BlocksCentralChar (discrete β) (classCoefficients (ConjClasses.mk e)) ∉
          BlocksLocalMaxIdeal m → 2 ∣ Nat.card (Subgroup.centralizer {e}))
      · intro g h hP
        simpa only [mk_conj_eq, card_centralizer_eq_of_mk_eq (mk_conj_eq g h)] using hP
      · intro _
        rw [card_centralizer_one]
        obtain ⟨N, -, hG⟩ := card_PSL_eq_four_mul_odd hF (Or.inl h8)
        rw [hG]
        exact Dvd.intro (2 * N) (by ring)
      · intro x hx hx1 hω
        exfalso
        apply hω
        obtain ⟨t, rfl⟩ := (mem_unipotent_iff_exists x).mp hx
        have ht : t ≠ 0 := fun h => hx1 ((mk_unip_eq_one_iff h2ne t).mpr h)
        rw [centralChar_classCoefficients hDc, card_carrier_unip_complex hF ht,
          discrete_of_mem_unipotent hF hν β hx hx1, discrete_one hF hν, hk]
        have : (((((8 * k + 3 : ℕ) : ℂ) ^ 2 - 1) / 2 * -1) / (((8 * k + 3 : ℕ) : ℂ) - 1)) =
            2 * ((-(2 * k + 1) : ℤ) : ℂ) := by
          rw [div_eq_iff hq1]
          push_cast
          ring
        rw [this]
        exact mem_localMaxIdeal_of_eq_two_mul m hm h2 (intCast_mem_localRing m hm _) rfl
      · intro x hx hx1 hω
        exfalso
        apply hω
        rw [centralChar_classCoefficients hDc, discrete_of_mem_splitTorus hF hν β hx hx1,
          mul_zero, zero_div]
        exact localMaxIdeal_zero m hm
      · intro x hx hx1 _
        rw [card_centralizer_nonsplitTorus hF hq hν hx hx1, hS]
        split_ifs <;> omega)
    have hpos : 0 < Nat.card D := Nat.card_pos
    have := Nat.le_of_dvd hpos hlow
    simp only [pow_one] at hle
    omega

theorem psl2_blockDefects_of_mod_eight_eq_five (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F)
    {ν : F} (hν : ¬ IsSquare ν) (h8 : Fintype.card F % 8 = 5) (m : Ideal BlocksAlgInt)
    (hm : m.IsMaximal) (h2 : (2 : BlocksAlgInt) ∈ m) :
    (∀ D : Subgroup PSL(2, F),
      (∀ χ ∈ BlocksPrincipalBlock m PSL(2, F), blockDefect 2 m χ D) ↔
        ∃ P : Sylow 2 PSL(2, F), (P : Subgroup PSL(2, F)) = D) ∧
    (∀ P : Sylow 2 PSL(2, F), Nat.card P = 4 ∧ ∀ x ∈ P, x ^ 2 = 1) ∧
    (∀ β : nonsplitTorus ν →* ℂˣ, β ^ 2 ≠ 1 →
      (∃ D, blockDefect 2 m (discrete β) D) ∧
        ∀ D, blockDefect 2 m (discrete β) D → Nat.card D = 1) ∧
    (∀ α : splitTorus F →* ℂˣ, α ^ 2 ≠ 1 →
      (∃ D, blockDefect 2 m (principal α) D) ∧
        ∀ D, blockDefect 2 m (principal α) D → Nat.card D = 2) := by
  obtain ⟨k, hk⟩ : ∃ k, Fintype.card F = 8 * k + 5 := ⟨Fintype.card F / 8, by omega⟩
  have := charP_two m hm h2
  have := hm
  have h2' : ((2 : ℕ) : BlocksAlgInt) ∈ m := by exact_mod_cast h2
  have h2ne : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have hu : (mk (unip 1) : PSL(2, F)) ∈ unipotent F := mk_unip_mem_unipotent 1
  have hu1 : (mk (unip 1) : PSL(2, F)) ≠ 1 :=
    fun h => one_ne_zero ((mk_unip_eq_one_iff h2ne 1).mp h)
  have hCu : Nat.card (Subgroup.centralizer {(mk (unip 1) : PSL(2, F))}) =
      2 ^ 0 * (8 * k + 5) := by
    rw [card_centralizer_unip hF one_ne_zero, hk]
    ring
  have hoddq : Odd (8 * k + 5) := ⟨4 * k + 2, by ring⟩
  have hq1 : ((8 * k + 5 : ℕ) : ℂ) - 1 ≠ 0 := by
    rw [sub_ne_zero]
    exact_mod_cast (show 8 * k + 5 ≠ 1 by omega)
  have hq1' : ((8 * k + 5 : ℕ) : ℂ) + 1 ≠ 0 := by
    exact_mod_cast (show 8 * k + 5 + 1 ≠ 0 by omega)
  refine ⟨(CFSG.BlockBasics.principal_block_defect 2 Nat.prime_two m PSL(2, F)).1,
    sylow_two_psl2 hF hq hν (Or.inr h8), fun β hβ => ?_, fun α hα => ?_⟩
  ·
    have hD := discrete_mem_blocksIrr hF hq hν hβ
    refine ⟨blockDefect_exists 2 Nat.prime_two m hm h2' _ hD, fun D hDD => ?_⟩
    have hω : BlocksCentralChar (discrete β)
        (classCoefficients (ConjClasses.mk (mk (unip 1) : PSL(2, F)))) ∉
          BlocksLocalMaxIdeal m := by
      rw [centralChar_classCoefficients
        (blocksVChar_isClassFunction (AddSubgroup.subset_closure hD)),
        card_carrier_unip_complex hF one_ne_zero, discrete_of_mem_unipotent hF hν β hu hu1,
        discrete_one hF hν, hk]
      have : (((((8 * k + 5 : ℕ) : ℂ) ^ 2 - 1) / 2 * -1) / (((8 * k + 5 : ℕ) : ℂ) - 1)) =
          ((-(4 * k + 3) : ℤ) : ℂ) := by
        rw [div_eq_iff hq1]
        push_cast
        ring
      rw [this]
      exact intCast_not_mem_localMaxIdeal m hm h2 ⟨-(2 * k + 2), by ring⟩
    have hle := card_blockDefect_le m hDD hω hoddq hCu
    have hpos : 0 < Nat.card D := Nat.card_pos
    simp only [pow_zero] at hle
    omega
  ·
    have hR := principal_mem_blocksIrr hF hq hν hα
    have hRc := blocksVChar_isClassFunction (AddSubgroup.subset_closure hR)
    refine ⟨blockDefect_exists 2 Nat.prime_two m hm h2' _ hR, fun D hDD => ?_⟩
    have hT : Nat.card (splitTorus F) = 4 * k + 2 := by
      have := card_splitTorus h2ne (F := F)
      omega
    obtain ⟨w, hw2, hwM⟩ := exists_trace_not_mem m hm h2 (by omega : Nat.card _ % 4 = 2) hα
    have hx2 : (w : PSL(2, F)) ^ 2 ≠ 1 := fun h => hw2 (Subtype.ext (by simpa using h))
    have hx1 : (w : PSL(2, F)) ≠ 1 := fun h => hx2 (by rw [h, one_pow])
    have hωw : BlocksCentralChar (principal α)
        (classCoefficients (ConjClasses.mk (w : PSL(2, F)))) ∉ BlocksLocalMaxIdeal m := by
      rw [centralChar_classCoefficients hRc, card_carrier_split_complex hF hq w.2 hx1 hx2,
        principal_of_mem_splitTorus α w.2 hx1, principal_one hF, hk]
      intro hmem
      apply hwM
      simp only [Subtype.coe_eta] at hmem
      have hval : ((8 * k + 5 : ℕ) : ℂ) * (((8 * k + 5 : ℕ) : ℂ) + 1) *
          ((α w : ℂ) + (α w⁻¹ : ℂ)) / (((8 * k + 5 : ℕ) : ℂ) + 1) =
          ((8 * k + 5 : ℤ) : ℂ) * ((α w : ℂ) + (α w⁻¹ : ℂ)) := by
        rw [div_eq_iff hq1']
        push_cast
        ring
      rw [hval] at hmem
      exact mem_of_odd_mul_mem m hm h2 ⟨4 * k + 2, by ring⟩ hmem
    have hle := card_blockDefect_le m hDD hωw (a := 1) (N := 2 * k + 1) ⟨k, by ring⟩
      (by rw [card_centralizer_splitTorus hF hq w.2 hx1, ite_eq_right hx2, hT]; ring)
    have hlow := two_dvd_card_blockDefect m hDD (fun e => by
      apply forall_of_families hF hq hν (P := fun e =>
        BlocksCentralChar (principal α) (classCoefficients (ConjClasses.mk e)) ∉
          BlocksLocalMaxIdeal m → 2 ∣ Nat.card (Subgroup.centralizer {e}))
      · intro g h hP
        simpa only [mk_conj_eq, card_centralizer_eq_of_mk_eq (mk_conj_eq g h)] using hP
      · intro _
        rw [card_centralizer_one]
        obtain ⟨N, -, hG⟩ := card_PSL_eq_four_mul_odd hF (Or.inr h8)
        rw [hG]
        exact Dvd.intro (2 * N) (by ring)
      · intro x hx hx1 hω
        exfalso
        apply hω
        obtain ⟨t, rfl⟩ := (mem_unipotent_iff_exists x).mp hx
        have ht : t ≠ 0 := fun h => hx1 ((mk_unip_eq_one_iff h2ne t).mpr h)
        rw [centralChar_classCoefficients hRc, card_carrier_unip_complex hF ht,
          principal_of_mem_unipotent hF α hx hx1, principal_one hF, hk]
        have : (((((8 * k + 5 : ℕ) : ℂ) ^ 2 - 1) / 2 * 1) / (((8 * k + 5 : ℕ) : ℂ) + 1)) =
            2 * ((2 * k + 1 : ℤ) : ℂ) := by
          rw [div_eq_iff hq1']
          push_cast
          ring
        rw [this]
        exact mem_localMaxIdeal_of_eq_two_mul m hm h2 (intCast_mem_localRing m hm _) rfl
      · intro x hx hx1 _
        rw [card_centralizer_splitTorus hF hq hx hx1, hT]
        split_ifs <;> omega
      · intro x hx hx1 hω
        exfalso
        apply hω
        rw [centralChar_classCoefficients hRc, principal_of_mem_nonsplitTorus hF hν α hx hx1,
          mul_zero, zero_div]
        exact localMaxIdeal_zero m hm)
    have hpos : 0 < Nat.card D := Nat.card_pos
    have := Nat.le_of_dvd hpos hlow
    simp only [pow_one] at hle
    omega

theorem prod_psl2_principalBlockDefect (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F) {ν : F}
    (hν : ¬ IsSquare ν) (h8 : Fintype.card F % 8 = 3 ∨ Fintype.card F % 8 = 5)
    (m : Ideal BlocksAlgInt) (hm : m.IsMaximal) (h2 : (2 : BlocksAlgInt) ∈ m) {Z : Type}
    [Group Z] [Fintype Z] (hZ : Nat.card Z = 2) :
    (∀ D : Subgroup (Z × PSL(2, F)),
      (∀ χ ∈ BlocksPrincipalBlock m (Z × PSL(2, F)), blockDefect 2 m χ D) ↔
        ∃ P : Sylow 2 (Z × PSL(2, F)), (P : Subgroup (Z × PSL(2, F))) = D) ∧
    (∀ P : Sylow 2 (Z × PSL(2, F)), Nat.card P = 8 ∧ ∀ x ∈ P, x ^ 2 = 1) := by
  have := charP_two m hm h2
  have := hm
  exact ⟨(CFSG.BlockBasics.principal_block_defect 2 Nat.prime_two m (Z × PSL(2, F))).1,
    sylow_two_prod_psl2 hF hq hν h8 hZ⟩

end CFSG.PSL2Table
