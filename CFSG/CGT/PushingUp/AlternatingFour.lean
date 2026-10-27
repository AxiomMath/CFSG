module

public import CFSG.RankThree.PartOne.S12.PushingUp
import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.RankThree.PartOne.Assembly

public section

namespace CFSG.CGT.PushingUp

open CFSG CFSG.RankThree.PartOne Equiv

namespace AlternatingFour

private abbrev A4 : Type := ↥(alternatingGroup (Fin 4))

private def involution : Fin 3 → A4 :=
  ![⟨swap 0 1 * swap 2 3, by rw [Perm.mem_alternatingGroup]; decide⟩,
    ⟨swap 0 2 * swap 1 3, by rw [Perm.mem_alternatingGroup]; decide⟩,
    ⟨swap 0 3 * swap 1 2, by rw [Perm.mem_alternatingGroup]; decide⟩]

private lemma card_A4 : Nat.card A4 = 12 := by
  rw [Nat.card_eq_fintype_card]; decide

private lemma sq_mul_sq : ∀ x y : A4, x ^ 2 = 1 → y ^ 2 = 1 → (x * y) ^ 2 = 1 := by
  decide +kernel

private def kleinFour : Subgroup A4 where
  carrier := {x | x ^ 2 = 1}
  one_mem' := one_pow 2
  mul_mem' := fun {x y} hx hy => sq_mul_sq x y hx hy
  inv_mem' := fun {x} hx => by
    change x⁻¹ ^ 2 = 1
    rw [inv_pow, show x ^ 2 = 1 from hx, inv_one]

private lemma mem_kleinFour {x : A4} : x ∈ kleinFour ↔ x ^ 2 = 1 := Iff.rfl

private instance kleinFour_normal : kleinFour.Normal where
  conj_mem x hx g := by
    rw [mem_kleinFour] at hx ⊢
    rw [conj_pow, hx, mul_one, mul_inv_cancel]

private lemma card_kleinFour : Nat.card kleinFour = 4 := by
  change Nat.card {x : A4 // x ^ 2 = 1} = 4
  rw [Nat.card_eq_fintype_card]; decide +kernel

private lemma cube_or_sq : ∀ x : A4, x ^ 3 = 1 ∨ x ^ 2 = 1 := by decide +kernel

private lemma eq_one_of_cube_of_pow_two_pow {M : Type*} [Monoid M] {x : M} (h3 : x ^ 3 = 1)
    {n : ℕ} (h : x ^ 2 ^ n = 1) : x = 1 :=
  (pow_eq_one_iff_of_coprime (Nat.Coprime.pow_right n (by norm_num))).mp ⟨h3, h⟩

private lemma isPGroup_kleinFour : IsPGroup 2 kleinFour := fun g => ⟨1, Subtype.ext g.2⟩

private lemma le_kleinFour_of_isPGroup {N : Subgroup A4} (hN : IsPGroup 2 N) : N ≤ kleinFour := by
  intro x hx
  obtain ⟨n, hn⟩ := hN ⟨x, hx⟩
  rcases cube_or_sq x with h3 | h2
  · have h : x ^ 2 ^ n = 1 := congrArg Subtype.val hn
    rw [eq_one_of_cube_of_pow_two_pow h3 h]
    exact one_mem _
  · exact h2

private lemma pCore_eq : pCore 2 A4 = kleinFour :=
  le_antisymm (sSup_le fun _ hN => le_kleinFour_of_isPGroup hN.2)
    (le_sSup ⟨kleinFour_normal, isPGroup_kleinFour⟩)

private lemma centralizer_kleinFour :
    ∀ x : A4, (∀ y : A4, y ^ 2 = 1 → y * x = x * y) → x ^ 2 = 1 := by decide +kernel

private lemma kleinFour_comm : ∀ x y : A4, x ^ 2 = 1 → y ^ 2 = 1 → x * y = y * x := by
  decide +kernel

private lemma center_trivial : ∀ x : A4, (∀ g : A4, g * x = x * g) → x = 1 := by decide +kernel

private lemma kleinFour_conj : ∀ x y : A4, x ^ 2 = 1 → x ≠ 1 → y ^ 2 = 1 → y ≠ 1 →
    ∃ g : A4, g * x * g⁻¹ = y := by decide +kernel

private lemma kleinFour_commutator : ∀ v : A4, v ^ 2 = 1 →
    ∃ x g : A4, x ^ 2 = 1 ∧ x * g * x⁻¹ * g⁻¹ = v := by decide +kernel

private lemma prod_of_cubes : ∀ x : A4, ∃ y z : A4, y ^ 3 = 1 ∧ z ^ 3 = 1 ∧ y * z = x := by
  decide +kernel

private lemma shortU_eq : shortU A4 = kleinFour := by
  unfold shortU
  rw [pCore_eq]
  refine le_antisymm (Subgroup.commutator_le_left _ _) fun v hv => ?_
  obtain ⟨x, g, hx, rfl⟩ := kleinFour_commutator v hv
  exact Subgroup.commutator_mem_commutator hx (Subgroup.mem_top g)

private lemma shortC_eq : shortC A4 = ⊥ := by
  unfold shortC
  rw [eq_bot_iff]
  intro x hx
  exact Subgroup.mem_bot.2
    (center_trivial x (Subgroup.mem_center_iff.mp (Subgroup.mem_inf.mp hx).2))

private lemma sq_eq_one_of_mem_shortU {u : A4} (hu : u ∈ shortU A4) : u ^ 2 = 1 := by
  rw [shortU_eq] at hu
  exact hu

private lemma isShortGroup : IsShortGroup A4 where
  fitting_eq := by
    refine (isCharacteristicP_iff_generalizedFitting_eq_pCore A4 2).mp ?_
    change Subgroup.centralizer (pCore 2 A4 : Set A4) ≤ pCore 2 A4
    rw [pCore_eq]
    intro x hx
    exact centralizer_kleinFour x (Subgroup.mem_centralizer_iff.mp hx)
  residual_eq := by
    refine eq_top_iff.mpr (le_sInf ?_)
    rintro N ⟨hN, hp⟩
    have hcube : ∀ y : A4, y ^ 3 = 1 → y ∈ N := by
      intro y hy
      rw [← QuotientGroup.eq_one_iff]
      obtain ⟨n, hn⟩ := hp (y : A4 ⧸ N)
      exact eq_one_of_cube_of_pow_two_pow (by rw [← QuotientGroup.mk_pow, hy, QuotientGroup.mk_one])
        hn
    intro x _
    obtain ⟨y, z, hy, hz, rfl⟩ := prod_of_cubes x
    exact N.mul_mem (hcube y hy) (hcube z hz)
  quotient_type := Or.inr (by
    rw [pCore_eq]
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup kleinFour
    rw [card_A4, card_kleinFour] at h
    have h3 : Nat.card (A4 ⧸ kleinFour) = 3 := by omega
    rw [h3]
    exact Nat.prime_three)
  U_le_center := by
    rw [shortU_eq, pCore_eq]
    intro x hx
    refine ⟨⟨x, hx⟩, Subgroup.mem_center_iff.mpr fun y => ?_, rfl⟩
    exact Subtype.ext (kleinFour_comm y.1 x y.2 hx)
  nonzero := by
    rw [shortC_eq, shortU_eq]
    refine bot_lt_iff_ne_bot.mpr fun h => ?_
    have h4 := card_kleinFour
    rw [h, Subgroup.card_bot] at h4
    omega
  irreducible := by
    intro N hN hNU _
    rw [shortU_eq] at hNU
    rw [shortC_eq, shortU_eq]
    rcases N.bot_or_exists_ne_one with h | ⟨x, hx, hx1⟩
    · exact Or.inl h
    · right
      refine le_antisymm hNU fun y hy => ?_
      by_cases hy1 : y = 1
      · rw [hy1]; exact N.one_mem
      · obtain ⟨g, rfl⟩ := kleinFour_conj x y (hNU hx) hx1 hy hy1
        exact hN.conj_mem x hx g

private def conjIndex (l : A4) (i : Fin 3) : Fin 3 :=
  if l * involution i * l⁻¹ = involution 0 then 0
  else if l * involution i * l⁻¹ = involution 1 then 1 else 2

private lemma conjIndex_mul : ∀ (l m : A4) (i : Fin 3),
    conjIndex (l * m) i = conjIndex l (conjIndex m i) := by decide +kernel

private lemma conjIndex_one : ∀ i : Fin 3, conjIndex 1 i = i := by decide +kernel

private def conjPerm (l : A4) : Perm (Fin 3) where
  toFun := conjIndex l
  invFun := conjIndex l⁻¹
  left_inv i := by rw [← conjIndex_mul, inv_mul_cancel, conjIndex_one]
  right_inv i := by rw [← conjIndex_mul, mul_inv_cancel, conjIndex_one]

private lemma conjPerm_sign : ∀ l : A4, Perm.sign (conjPerm l) = 1 := by decide +kernel

private def conjAlt : A4 →* alternatingGroup (Fin 3) :=
  (MonoidHom.mk' conjPerm fun l m => Equiv.ext fun i => conjIndex_mul l m i).codRestrict
    (alternatingGroup (Fin 3)) fun l => Perm.mem_alternatingGroup.mpr (conjPerm_sign l)

private lemma conjAlt_surjective : Function.Surjective conjAlt := by
  change ∀ σ : alternatingGroup (Fin 3), ∃ l : A4, conjAlt l = σ
  decide +kernel

private lemma conjAlt_eq_one_iff : ∀ l : A4, conjAlt l = 1 ↔ l ^ 2 = 1 := by decide +kernel

private lemma conjAlt_ker : conjAlt.ker = pCore 2 A4 := by
  rw [pCore_eq]
  ext l
  rw [MonoidHom.mem_ker]
  exact conjAlt_eq_one_iff l

private noncomputable def quotientEquiv : (A4 ⧸ pCore 2 A4) ≃* alternatingGroup (Fin 3) :=
  (QuotientGroup.quotientMulEquivOfEq conjAlt_ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective conjAlt conjAlt_surjective)

private def coords (x : A4) : Fin 3 → ZMod 2 :=
  fun i => if x = 1 ∨ x = involution i then 0 else 1

private lemma coords_one : coords 1 = 0 := by
  funext i
  simp [coords]

private lemma coords_mul : ∀ x y : A4, x ^ 2 = 1 → y ^ 2 = 1 →
    coords (x * y) = coords x + coords y := by decide +kernel

private lemma coords_sum : ∀ x : A4, x ^ 2 = 1 → ∑ i, coords x i = 0 := by decide +kernel

private lemma coords_surjective : ∀ w : Fin 3 → ZMod 2, ∑ i, w i = 0 →
    ∃ x : A4, x ^ 2 = 1 ∧ coords x = w := by decide +kernel

private lemma coords_eq_zero_iff : ∀ x : A4, x ^ 2 = 1 → (coords x = 0 ↔ x = 1) := by
  decide +kernel

private lemma coords_conj : ∀ l u : A4, u ^ 2 = 1 →
    coords (l * u * l⁻¹) = permActionTwo (conjPerm l) (coords u) := by decide +kernel

private def coordsHom : ↥(shortU A4) →* Multiplicative (Fin 3 → ZMod 2) where
  toFun u := Multiplicative.ofAdd (coords u.1)
  map_one' := by
    change Multiplicative.ofAdd (coords 1) = 1
    rw [coords_one]
    rfl
  map_mul' u v := congrArg Multiplicative.ofAdd
    (coords_mul u.1 v.1 (sq_eq_one_of_mem_shortU u.2) (sq_eq_one_of_mem_shortU v.2))

private lemma isNaturalAltModule : IsNaturalAltModule A4 1 := by
  refine ⟨quotientEquiv, coordsHom, ?_, ?_, ?_, ?_⟩
  · intro u
    exact coords_sum u.1 (sq_eq_one_of_mem_shortU u.2)
  · intro w hw
    obtain ⟨x, hx, hxw⟩ := coords_surjective w hw
    exact ⟨⟨x, by rw [shortU_eq]; exact hx⟩, congrArg Multiplicative.ofAdd hxw⟩
  · ext u
    rw [MonoidHom.mem_ker, shortC_eq, Subgroup.mem_subgroupOf, Subgroup.mem_bot]
    exact (ofAdd_eq_one (x := coords u.1)).trans
      (coords_eq_zero_iff u.1 (sq_eq_one_of_mem_shortU u.2))
  · intro l u hu hu'
    exact congrArg Multiplicative.ofAdd (coords_conj l u (sq_eq_one_of_mem_shortU hu))

end AlternatingFour

theorem inClassX_alternatingGroup_four : InClassX ↥(alternatingGroup (Fin 4)) :=
  ⟨AlternatingFour.isShortGroup, Or.inl ⟨1, le_rfl, AlternatingFour.isNaturalAltModule⟩⟩

end CFSG.CGT.PushingUp
