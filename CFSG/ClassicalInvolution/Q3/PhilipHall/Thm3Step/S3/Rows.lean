module

import CFSG.ClassicalInvolution.Balance.WeakFrameExistsBasic
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf49G3Defs

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf.Thm3A

@[expose] def RowCentralizerFacts : Prop :=
  (∀ (X : Type) [Group X] [Finite X], CFSG.Blueprint.LieModel X .PSU 3 3 1 →
    ∀ z : X, z * z = 1 → z ≠ 1 →
      classicalInvolutionOddCore ↥(Subgroup.centralizer ({z} : Set X)) = ⊥) ∧
  (∀ (X : Type) [Group X] [Finite X], CFSG.Blueprint.NativeSporadic.IsSporadic X .M12 →
    ∀ z : X, z * z = 1 → z ≠ 1 →
      classicalInvolutionOddCore ↥(Subgroup.centralizer ({z} : Set X)) = ⊥) ∧
  (∀ (X : Type) [Group X] [Finite X], CFSG.Blueprint.LieModel X .G2 0 3 1 →
    ∀ z : X, z * z = 1 → z ≠ 1 →
      classicalInvolutionOddCore ↥(Subgroup.centralizer ({z} : Set X)) = ⊥)

section Transport

theorem oddCore_eq_bot_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : classicalInvolutionOddCore B = ⊥) : classicalInvolutionOddCore A = ⊥ := by
  have h1 : (classicalInvolutionOddCore A).map e.toMonoidHom = classicalInvolutionOddCore B :=
    CFSG.ComponentClassification.OddCore.equiv_invariant e
  rw [h] at h1
  exact (Subgroup.map_eq_bot_iff_of_injective (f := e.toMonoidHom) _ e.injective).mp h1

theorem oddCore_eq_bot_of_oddCoreIn {G : Type} [Group G] {H : Subgroup G}
    (h : Balance.oddCoreIn H = ⊥) : classicalInvolutionOddCore ↥H = ⊥ :=
  (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).mp h

theorem oddCoreIn_eq_bot {G : Type} [Group G] {H : Subgroup G}
    (h : classicalInvolutionOddCore ↥H = ⊥) : Balance.oddCoreIn H = ⊥ := by
  show (classicalInvolutionOddCore ↥H).map _ = ⊥
  rw [h, Subgroup.map_bot]

theorem map_centralizer_singleton {G H : Type} [Group G] [Group H] (e : G ≃* H) (g : G) :
    (Subgroup.centralizer ({g} : Set G)).map e.toMonoidHom =
      Subgroup.centralizer ({e g} : Set H) := by
  ext y
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h1 := congrArg e h
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h1
  · intro h
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact h

theorem oddCore_centralizer_eq_bot_of_mulEquiv {G H : Type} [Group G] [Group H] (e : G ≃* H)
    {g : G} (h : classicalInvolutionOddCore ↥(Subgroup.centralizer ({e g} : Set H)) = ⊥) :
    classicalInvolutionOddCore ↥(Subgroup.centralizer ({g} : Set G)) = ⊥ :=
  oddCore_eq_bot_of_mulEquiv
    ((e.subgroupMap _).trans (MulEquiv.subgroupCongr (map_centralizer_singleton e g))) h

theorem oddCore_inf_centralizer_eq_bot {Y : Type} [Group Y] {P : Subgroup Y} {z : Y}
    (hz : z ∈ P)
    (h : classicalInvolutionOddCore ↥(Subgroup.centralizer ({(⟨z, hz⟩ : ↥P)} : Set ↥P)) = ⊥) :
    classicalInvolutionOddCore ↥(P ⊓ Subgroup.centralizer ({z} : Set Y)) = ⊥ := by
  have heq : (P ⊓ Subgroup.centralizer ({z} : Set Y)).subgroupOf P =
      Subgroup.centralizer ({(⟨z, hz⟩ : ↥P)} : Set ↥P) := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨-, hx⟩
      exact Subtype.ext hx
    · intro hx
      exact ⟨x.2, congrArg Subtype.val hx⟩
  exact oddCore_eq_bot_of_mulEquiv
    ((Subgroup.subgroupOfEquivOfLe inf_le_left).symm.trans (MulEquiv.subgroupCongr heq)) h

end Transport

section Rows

variable {X : Type} [Group X] [Finite X]

theorem oddCore_centralizer_eq_bot_of_mem_normal (hO : classicalInvolutionOddCore X = ⊥)
    {W : Subgroup X} (hWn : W.Normal) (hW2 : IsPGroup 2 W) {z : X} (hz : z ∈ W) :
    classicalInvolutionOddCore ↥(Subgroup.centralizer ({z} : Set X)) = ⊥ :=
  oddCore_eq_bot_of_oddCoreIn (TC.oddCoreImg_centralizer_eq_bot hO hWn hW2 hz)

theorem dihedralGroup_six_mul_self :
    ∀ x : DihedralGroup 6, x * x * (x * x) = 1 → x * x = 1 := by
  decide

theorem mul_self_mem_of_dihedral {W : Subgroup X} [W.Normal]
    (d : (X ⧸ W) ≃* DihedralGroup 6) {a : X} (ha : a * a * (a * a) = 1) : a * a ∈ W := by
  have h1 : d (a : X ⧸ W) * d (a : X ⧸ W) * (d (a : X ⧸ W) * d (a : X ⧸ W)) = 1 := by
    rw [← map_mul, ← map_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, ha,
      QuotientGroup.mk_one, map_one]
  have h2 := dihedralGroup_six_mul_self _ h1
  rw [← map_mul, ← QuotientGroup.mk_mul] at h2
  have h3 : ((a * a : X) : X ⧸ W) = 1 := d.injective (h2.trans (map_one d).symm)
  exact (QuotientGroup.eq_one_iff _).mp h3

theorem oddCore_centralizer_eq_bot_of_index_two {N : Subgroup X} (hidx : N.index = 2) {z : X}
    (hzN : z ∈ N)
    (h : classicalInvolutionOddCore ↥(Subgroup.centralizer ({(⟨z, hzN⟩ : ↥N)} : Set ↥N)) = ⊥) :
    classicalInvolutionOddCore ↥(Subgroup.centralizer ({z} : Set X)) = ⊥ := by
  set C := Subgroup.centralizer ({z} : Set X)
  have hNC : Balance.oddCoreIn (N ⊓ C) = ⊥ :=
    oddCoreIn_eq_bot (oddCore_inf_centralizer_eq_bot hzN h)
  have hle : Balance.oddCoreIn C ≤ N ⊓ C := by
    intro b hb
    refine ⟨?_, Balance.oddCoreIn_le C hb⟩
    obtain ⟨k, hk⟩ : Odd (orderOf b) :=
      (Balance.odd_card_oddCoreIn C).of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hb)
    have hb' : b = b ^ (k + 1) * b ^ (k + 1) := by
      rw [← pow_add, show k + 1 + (k + 1) = orderOf b + 1 by omega, pow_succ, pow_orderOf_eq_one,
        one_mul]
    rw [hb']
    exact Subgroup.mul_self_mem_of_index_two hidx _
  have h2 : Balance.oddCoreIn C ≤ Balance.oddCoreIn (N ⊓ C) := fun b hb =>
    Balance.inf_oddCoreIn_le inf_le_right ⟨hle hb, hb⟩
  rw [hNC, le_bot_iff] at h2
  exact oddCore_eq_bot_of_oddCoreIn h2

theorem isPGroup_of_mem_WSet {Ω : Set (Subgroup X)} {W : Subgroup X} (hW : W ∈ WSet Ω) :
    IsPGroup 2 W := by
  obtain ⟨η, ⟨S, hS, -⟩, rfl⟩ := hW
  exact S.isPGroup'.to_le (iSup₂_le fun U hU => (hS.1 hU).2)

theorem oddCore_centralizer_mul_self_eq_bot_of_rows (hF : RowCentralizerFacts) {Y : Type}
    [Group Y] [Finite Y] {Δ : Set (Subgroup Y)} {P : Subgroup Y} (hrows : Thm3RowsG Δ P)
    {a : SecQuot P} (ha : a * a * (a * a) = 1) (ha1 : a * a ≠ 1) :
    classicalInvolutionOddCore ↥(Subgroup.centralizer ({a * a} : Set (SecQuot P))) = ⊥ := by
  have hO : classicalInvolutionOddCore (SecQuot P) = ⊥ :=
    CFSG.ComponentClassification.OddCore.quotient_corefree ↥P
  rcases hrows with hG | ⟨N, hN, hidx, hLie⟩ | hM | hL | ⟨W, hW, hWset, ⟨d⟩⟩
  · exact hF.2.2 _ hG _ ha ha1
  · have hzN : a * a ∈ N := Subgroup.mul_self_mem_of_index_two hidx a
    refine oddCore_centralizer_eq_bot_of_index_two hidx hzN (hF.1 _ hLie _ ?_ ?_)
    · exact Subtype.ext ha
    · exact fun h => ha1 (congrArg Subtype.val h)
  · exact hF.2.1 _ hM _ ha ha1
  · obtain ⟨E, hE, hEab, -, ⟨e⟩⟩ := hL
    exact oddCore_eq_bot_of_oddCoreIn (oddCoreIn_centralizer_eq_bot_of_l3e8 hO hEab e ha)
  · have hW2 : IsPGroup 2 W := isPGroup_of_mem_WSet (hWset ▸ Set.mem_singleton W)
    exact oddCore_centralizer_eq_bot_of_mem_normal hO hW hW2 (mul_self_mem_of_dihedral d ha)

end Rows

section Member

variable {Y : Type} [Group Y] [Finite Y]

theorem exists_mul_self_eq {Δ : Set (Subgroup Y)} (hΔ : TypeRHyp Δ) {M : Subgroup Y} (hM : M ∈ Δ)
    {z : Y} (hz : IsUniqueInvolution M z) : ∃ a ∈ M, a * a = z := by
  obtain ⟨R, hR, -⟩ := IsSylow2In.exists_ge (T := ⊥) (P := M) IsPGroup.of_bot bot_le
  obtain ⟨e⟩ := hΔ.sylow M hM R hR
  set r : ↥R := e.symm (QuaternionGroup.a 1) with hr
  have hrr : r * r = e.symm (QuaternionGroup.a 2) := by
    rw [hr, ← map_mul]
    congr 1
  have h1 : r * r ≠ 1 := by
    rw [hrr]
    intro h
    have := congrArg e h
    rw [MulEquiv.apply_symm_apply, map_one] at this
    exact absurd this (by decide)
  have h2 : r * r * (r * r) = 1 := by
    rw [hrr, ← map_mul]
    have : (QuaternionGroup.a 2 * QuaternionGroup.a 2 : QuaternionGroup 2) = 1 := by decide
    rw [this, map_one]
  refine ⟨r, hR.1 r.2, ?_⟩
  rcases hz.unique ((r : Y) * r) (M.mul_mem (hR.1 r.2) (hR.1 r.2))
    (congrArg Subtype.val h2) with h | h
  · exact absurd (Subtype.ext h) h1
  · exact h

theorem oddCore_inf_centralizer_eq_bot_of_rows (hF : RowCentralizerFacts)
    {Δ : Set (Subgroup Y)} (hΔ : TypeRHyp Δ) {P : Subgroup Y}
    (hOP : classicalInvolutionOddCore ↥P = ⊥) (hrows : Thm3RowsG Δ P) {M : Subgroup Y}
    (hM : M ∈ Δ) (hMP : M ≤ P) {z : Y} (hz : IsUniqueInvolution M z) :
    classicalInvolutionOddCore ↥(P ⊓ Subgroup.centralizer ({z} : Set Y)) = ⊥ := by
  obtain ⟨a, haM, haz⟩ := exists_mul_self_eq hΔ hM hz
  have hzP : z ∈ P := hMP hz.mem
  have hinj : Function.Injective (QuotientGroup.mk' (classicalInvolutionOddCore ↥P)) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hOP]
  let f : ↥P ≃* SecQuot P :=
    MulEquiv.ofBijective (QuotientGroup.mk' _) ⟨hinj, QuotientGroup.mk'_surjective _⟩
  have hsq : (⟨a, hMP haM⟩ : ↥P) * ⟨a, hMP haM⟩ = ⟨z, hzP⟩ := Subtype.ext haz
  have hf : f ⟨z, hzP⟩ = f ⟨a, hMP haM⟩ * f ⟨a, hMP haM⟩ := by rw [← map_mul, hsq]
  have hz1 : (⟨z, hzP⟩ : ↥P) ≠ 1 := fun h => hz.ne_one (congrArg Subtype.val h)
  have hz2 : (⟨z, hzP⟩ : ↥P) * ⟨z, hzP⟩ = 1 := Subtype.ext hz.sq
  refine oddCore_inf_centralizer_eq_bot hzP (oddCore_centralizer_eq_bot_of_mulEquiv f ?_)
  rw [hf]
  refine oddCore_centralizer_mul_self_eq_bot_of_rows hF hrows ?_ ?_
  · rw [← hf, ← map_mul, hz2, map_one]
  · rw [← hf]
    exact fun h => hz1 (f.injective (h.trans (map_one f).symm))

end Member

end CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S3
