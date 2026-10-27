module

public import CFSG.CGT.Foote81L6.TStruct.DihFour
public import CFSG.CGT.Foote81L6.TStruct.Transport

public section

namespace CFSG.CGT.Foote81L6.TStruct

open Subgroup DihedralGroup

variable {G : Type*} [Group G] {H : Subgroup G} {k : ℕ} (e : H ≃* DihedralGroup (2 ^ k))

@[expose] def IsFourIn (H V : Subgroup G) : Prop :=
  V ≤ H ∧ (∀ x ∈ V, x * x = 1) ∧ Nat.card V = 4

theorem isFourIn_liftSub_dihFour (hk : 1 ≤ k) (i : ZMod (2 ^ k)) :
    IsFourIn H (liftSub e (dihFour k i)) :=
  ⟨liftSub_le e _, mul_self_liftSub e (mul_self_of_mem_dihFour hk i),
    by rw [card_liftSub, card_dihFour hk]⟩

theorem exists_eq_liftSub_dihFour (hk : 1 ≤ k) {V : Subgroup G} (hV : IsFourIn H V) :
    ∃ i, V = liftSub e (dihFour k i) := by
  obtain ⟨hVH, hV2, hV4⟩ := hV
  obtain ⟨i, hi⟩ := eq_dihFour hk (mul_self_lowerSub e hV2) (by rw [card_lowerSub e hVH, hV4])
  exact ⟨i, by rw [← hi, liftSub_lowerSub e hVH]⟩

include e in
theorem symm_zc_mem_four (hk : 1 ≤ k) {V : Subgroup G} (hV : IsFourIn H V) :
    ((e.symm (zc k) : H) : G) ∈ V := by
  obtain ⟨i, rfl⟩ := exists_eq_liftSub_dihFour e hk hV
  exact (symm_mem_liftSub e).2 (zc_mem_dihFour i)

include e in
theorem symm_zc_eq (hk : 2 ≤ k) {c : G} (hc : c ∈ H) (hc1 : c ≠ 1)
    (hcc : ∀ y ∈ H, y * c = c * y) : ((e.symm (zc k) : H) : G) = c := by
  rcases eq_one_or_zc_of_comm hk (c := e ⟨c, hc⟩) (fun g => by
      obtain ⟨y, rfl⟩ := e.surjective g
      rw [← map_mul, ← map_mul]
      exact congrArg e (Subtype.ext (hcc y y.2))) with h | h
  · exact absurd (congrArg Subtype.val (e.injective (h.trans e.map_one.symm))) hc1
  · rw [← h, MulEquiv.symm_apply_apply]

include e in
theorem inf_centralizer_four (hk : 1 ≤ k) {V : Subgroup G} (hV : IsFourIn H V) :
    H ⊓ centralizer (V : Set G) = V := by
  obtain ⟨i, rfl⟩ := exists_eq_liftSub_dihFour e hk hV
  rw [inf_centralizer_liftSub, centralizer_dihFour hk]

include e in
theorem card_inf_normalizer_four (hk : 2 ≤ k) {V : Subgroup G} (hV : IsFourIn H V) :
    Nat.card ↥(H ⊓ normalizer (V : Set G)) = 8 := by
  obtain ⟨i, rfl⟩ := exists_eq_liftSub_dihFour e (by omega) hV
  rw [inf_normalizer_liftSub, card_liftSub, card_normalizer_dihFour hk]

include e in
theorem nonempty_inf_normalizer_four_equiv (hk : 2 ≤ k) {V : Subgroup G} (hV : IsFourIn H V) :
    Nonempty (DihedralGroup 4 ≃* ↥(H ⊓ normalizer (V : Set G))) := by
  obtain ⟨i, rfl⟩ := exists_eq_liftSub_dihFour e (by omega) hV
  rw [inf_normalizer_liftSub]
  obtain ⟨f⟩ := nonempty_normalizer_dihFour_equiv hk i
  set K := normalizer (dihFour k i : Set (DihedralGroup (2 ^ k)))
  exact ⟨f.trans ((equivMapOfInjective K e.symm.toMonoidHom e.symm.injective).trans
    (equivMapOfInjective _ H.subtype H.subtype_injective))⟩

include e in
theorem conj_of_mem_inf_normalizer_four (hk : 1 ≤ k) {V : Subgroup G} (hV : IsFourIn H V)
    {x : G} (hx : x ∈ H ⊓ normalizer (V : Set G)) {v : G} (hv : v ∈ V) :
    x * v * x⁻¹ = v ∨ x * v * x⁻¹ = v * ((e.symm (zc k) : H) : G) := by
  obtain ⟨i, rfl⟩ := exists_eq_liftSub_dihFour e hk hV
  rw [inf_normalizer_liftSub, mem_liftSub] at hx
  obtain ⟨hxH, hxN⟩ := hx
  obtain ⟨hvH, hvV⟩ := (mem_liftSub e).1 hv
  have h := conj_of_mem_normalizer hk hxN hvV
  have key : x * v * x⁻¹ = ((⟨x, hxH⟩ * ⟨v, hvH⟩ * ⟨x, hxH⟩⁻¹ : H) : G) := rfl
  rcases h with h | h
  · left
    rw [key]
    have : (⟨x, hxH⟩ * ⟨v, hvH⟩ * ⟨x, hxH⟩⁻¹ : H) = ⟨v, hvH⟩ :=
      e.injective (by rw [map_mul, map_mul, map_inv]; exact h)
    rw [this]
  · right
    rw [key]
    have : (⟨x, hxH⟩ * ⟨v, hvH⟩ * ⟨x, hxH⟩⁻¹ : H) = ⟨v, hvH⟩ * e.symm (zc k) :=
      e.injective (by rw [map_mul, map_mul, map_inv, map_mul, MulEquiv.apply_symm_apply]; exact h)
    rw [this]
    rfl

include e in
theorem exists_conj_of_not_mem_four (hk : 1 ≤ k) {V : Subgroup G} (hV : IsFourIn H V)
    {x : G} (hx : x ∈ H ⊓ normalizer (V : Set G)) (hxV : x ∉ V) :
    ∃ v ∈ V, x * v * x⁻¹ = v * ((e.symm (zc k) : H) : G) := by
  obtain ⟨i, rfl⟩ := exists_eq_liftSub_dihFour e hk hV
  have hx' := hx
  rw [inf_normalizer_liftSub, mem_liftSub] at hx'
  obtain ⟨hxH, hxN⟩ := hx'
  have hxV' : e ⟨x, hxH⟩ ∉ dihFour k i := by
    intro h
    exact hxV ((mem_liftSub e).2 ⟨hxH, h⟩)
  have h := conj_sr_of_not_mem hk hxN hxV'
  refine ⟨((e.symm (sr i) : H) : G), (symm_mem_liftSub e).2 (sr_mem_dihFour i), ?_⟩
  have key : x * ((e.symm (sr i) : H) : G) * x⁻¹ =
      ((⟨x, hxH⟩ * e.symm (sr i) * ⟨x, hxH⟩⁻¹ : H) : G) := rfl
  rw [key]
  have : (⟨x, hxH⟩ * e.symm (sr i) * ⟨x, hxH⟩⁻¹ : H) = e.symm (sr i) * e.symm (zc k) :=
    e.injective (by
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, map_mul,
        MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
      exact h)
  rw [this]
  rfl

include e in
theorem exists_involution_four (hk : 2 ≤ k) {V : Subgroup G} (hV : IsFourIn H V) :
    ∃ d ∈ H ⊓ normalizer (V : Set G), d ∉ V ∧ d * d = 1 := by
  obtain ⟨i, rfl⟩ := exists_eq_liftSub_dihFour e (by omega) hV
  refine ⟨((e.symm (sr (i + quarter k)) : H) : G), ?_, ?_, ?_⟩
  · rw [inf_normalizer_liftSub, symm_mem_liftSub]
    exact sr_quarter_mem_normalizer hk i
  · rw [symm_mem_liftSub]
    exact sr_quarter_not_mem hk i
  · have := congrArg Subtype.val (show e.symm (sr (i + quarter k)) * e.symm (sr (i + quarter k)) =
      1 by rw [← map_mul, sr_mul_self, map_one])
    exact this

section Classes

variable (hk : 1 ≤ k)

@[expose] noncomputable def fourClass (V : Subgroup G) : ZMod 2 :=
  open Classical in
  if h : ∃ i, V = liftSub e (dihFour k i) then zpar k hk h.choose else 0

theorem fourClass_liftSub (hk2 : 2 ≤ k) (i : ZMod (2 ^ k)) :
    fourClass e hk (liftSub e (dihFour k i)) = zpar k hk i := by
  have hex : ∃ j, liftSub e (dihFour k i) = liftSub e (dihFour k j) := ⟨i, rfl⟩
  rw [fourClass, dif_pos hex]
  have hspec := hex.choose_spec
  generalize hex.choose = j at hspec ⊢
  rw [liftSub_inj, dihFour_eq_iff hk] at hspec
  rcases hspec with rfl | rfl
  · rfl
  · rw [map_add, zpar_half hk hk2]
    generalize zpar k hk i = u
    revert u
    decide

theorem exists_conj_four_iff (hk2 : 2 ≤ k) {V V' : Subgroup G} (hV : IsFourIn H V)
    (hV' : IsFourIn H V') :
    (∃ h ∈ H, V.map (MulAut.conj h).toMonoidHom = V') ↔ fourClass e hk V = fourClass e hk V' := by
  obtain ⟨i, rfl⟩ := exists_eq_liftSub_dihFour e hk hV
  obtain ⟨j, rfl⟩ := exists_eq_liftSub_dihFour e hk hV'
  rw [fourClass_liftSub e hk hk2, fourClass_liftSub e hk hk2, ← exists_conj_dihFour_iff hk hk2]
  constructor
  · rintro ⟨h, hh, hconj⟩
    refine ⟨e ⟨h, hh⟩, ?_⟩
    rw [← liftSub_inj e, ← liftSub_map_conj e _ ⟨h, hh⟩]
    exact hconj
  · rintro ⟨g, hg⟩
    refine ⟨((e.symm g : H) : G), (e.symm g).2, ?_⟩
    rw [liftSub_map_conj e, MulEquiv.apply_symm_apply, hg]

theorem fourClass_map_conj (hk2 : 2 ≤ k) {V : Subgroup G} (hV : IsFourIn H V) {h : G}
    (hh : h ∈ H) : fourClass e hk (V.map (MulAut.conj h).toMonoidHom) = fourClass e hk V := by
  have hV' : IsFourIn H (V.map (MulAut.conj h).toMonoidHom) := by
    obtain ⟨hVH, hV2, hV4⟩ := hV
    refine ⟨?_, ?_, ?_⟩
    · rintro _ ⟨v, hv, rfl⟩
      exact mul_mem (mul_mem hh (hVH hv)) (inv_mem hh)
    · rintro _ ⟨v, hv, rfl⟩
      rw [← map_mul, hV2 v hv, map_one]
    · rw [card_map_of_injective (MulAut.conj h).injective, hV4]
  exact ((exists_conj_four_iff e hk hk2 hV hV').1 ⟨h, hh, rfl⟩).symm

theorem exists_conj_four_rep (hk2 : 2 ≤ k) {V : Subgroup G} (hV : IsFourIn H V) :
    ∃ h ∈ H, V.map (MulAut.conj h).toMonoidHom =
      liftSub e (dihFour k (if fourClass e hk V = 0 then 0 else 1)) := by
  have hrep := isFourIn_liftSub_dihFour e hk (if fourClass e hk V = 0 then 0 else 1)
  refine (exists_conj_four_iff e hk hk2 hV hrep).2 ?_
  rw [fourClass_liftSub e hk hk2]
  have h01 : ∀ u : ZMod 2, u = 0 ∨ u = 1 := by decide
  rcases h01 (fourClass e hk V) with h | h
  · rw [h, if_pos rfl, map_zero]
  · rw [h, if_neg (by decide), map_one]

end Classes

end CFSG.CGT.Foote81L6.TStruct
