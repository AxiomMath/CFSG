module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCBasic
public import CFSG.CharacterTheory.Burnside
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Cardinality

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.C

open CFSG Subgroup CFSG.ComponentClassification.TBLit
open scoped commutatorElement MatrixGroups

structure PropCData {P : Type} [Group P] (x : P) (R₁ R₂ : Subgroup P) (p n : ℕ) [Fact p.Prime] :
    Prop where
  p_ne_two : p ≠ 2
  n_pos : 0 < n
  orderOf_eq : orderOf x = 2
  le₁ : R₁ ≤ centralizer ({x} : Set P)
  comp₁ : IsPComponent 2 (R₁.subgroupOf (centralizer ({x} : Set P)))
  le₂ : R₂ ≤ centralizer ({x} : Set P)
  comp₂ : IsPComponent 2 (R₂.subgroupOf (centralizer ({x} : Set P)))
  iso₁ : Nonempty (R₁ ⧸ pPrimeCore 2 R₁ ≃* PSL(2, GaloisField p n))
  iso₂ : Nonempty (R₂ ⧸ pPrimeCore 2 R₂ ≃* SL(2, GaloisField p n))
  mem : x ∈ R₂

@[expose] def quotientPPrimeCoreEquiv {R S : Type*} [Group R] [Group S] (e : R ≃* S) :
    R ⧸ pPrimeCore 2 R ≃* S ⧸ pPrimeCore 2 S :=
  QuotientGroup.congr _ _ e (pPrimeCore_map_iso 2 e)

theorem PropCData.map {P P' : Type} [Group P] [Group P'] [Finite P] {x : P} {R₁ R₂ : Subgroup P}
    {p n : ℕ} [Fact p.Prime] (h : PropCData x R₁ R₂ p n) (e : P ≃* P') :
    PropCData (e x) (R₁.map e.toMonoidHom) (R₂.map e.toMonoidHom) p n := by
  have hmap : ∀ {R : Subgroup P}, R ≤ centralizer ({x} : Set P) →
      R.map e.toMonoidHom ≤ centralizer ({e x} : Set P') := by
    intro R hR
    rw [← map_centralizer_singleton e x]
    exact map_mono hR
  have hcomp : ∀ {R : Subgroup P}, IsPComponent 2 (R.subgroupOf (centralizer ({x} : Set P))) →
      IsPComponent 2 ((R.map e.toMonoidHom).subgroupOf (centralizer ({e x} : Set P'))) := by
    intro R hR
    rw [← map_centralizer_singleton e x]
    exact (isPComponent_subgroupOf_map_iff 2 Nat.prime_two e.injective).1 hR
  have hiso : ∀ (R : Subgroup P), R.map e.toMonoidHom ≃* R := fun R =>
    (R.equivMapOfInjective e.toMonoidHom e.injective).symm
  obtain ⟨e₁⟩ := h.iso₁
  obtain ⟨e₂⟩ := h.iso₂
  exact ⟨h.p_ne_two, h.n_pos, by rw [MulEquiv.orderOf_eq]; exact h.orderOf_eq, hmap h.le₁,
    hcomp h.comp₁, hmap h.le₂, hcomp h.comp₂, ⟨(quotientPPrimeCoreEquiv (hiso R₁)).trans e₁⟩,
    ⟨(quotientPPrimeCoreEquiv (hiso R₂)).trans e₂⟩, ⟨x, h.mem, rfl⟩⟩

section Socle

variable {X : Type} [Group X] [Finite X]

theorem exists_propCData_of_socle (hsimple : IsSimpleGroup (GeneralizedFitting.subgroup X))
    (hnab : ∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a)
    (hout : Group.IsSolvable (OuterAutomorphisms.Outer (GeneralizedFitting.subgroup X)))
    {P : Type} [Group P] (θ : GeneralizedFitting.subgroup X ≃* P) {r : X} (hr : orderOf r = 2)
    {R₁ R₂ : Subgroup X} (hR₁ : R₁ ≤ centralizer ({r} : Set X))
    (hR₁c : IsPComponent 2 (R₁.subgroupOf (centralizer ({r} : Set X))))
    (hR₂ : R₂ ≤ centralizer ({r} : Set X))
    (hR₂c : IsPComponent 2 (R₂.subgroupOf (centralizer ({r} : Set X)))) {p n : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) (hn : 0 < n)
    (e₁ : Nonempty (R₁ ⧸ pPrimeCore 2 R₁ ≃* PSL(2, GaloisField p n)))
    (e₂ : Nonempty (R₂ ⧸ pPrimeCore 2 R₂ ≃* SL(2, GaloisField p n))) (hrR₂ : r ∈ R₂) :
    ∃ (x : P) (R₁' R₂' : Subgroup P), PropCData x R₁' R₂' p n ∧
      socleAction θ r = MulAut.conj x ∧
      R₁.map (socleAction θ) = R₁'.map MulAut.conj ∧
      R₂.map (socleAction θ) = R₂'.map MulAut.conj := by
  have : Finite P := Finite.of_equiv _ θ.toEquiv
  have hR₁F : R₁ ≤ GeneralizedFitting.subgroup X := le_socle_of_commutator_eq hsimple hnab hout
    (commutator_eq_of_isPComponent hR₁ hR₁c)
  have hR₂F : R₂ ≤ GeneralizedFitting.subgroup X := le_socle_of_commutator_eq hsimple hnab hout
    (commutator_eq_of_isPComponent hR₂ hR₂c)
  have hrF : r ∈ GeneralizedFitting.subgroup X := hR₂F hrR₂
  set j : P →* X := (GeneralizedFitting.subgroup X).subtype.comp θ.symm.toMonoidHom with hj
  have hjinj : Function.Injective j := Subtype.val_injective.comp θ.symm.injective
  have hjrange : j.range = GeneralizedFitting.subgroup X := by
    rw [hj, MonoidHom.range_comp, MonoidHom.range_eq_top.2 θ.symm.surjective, Subgroup.map_top,
      Subgroup.range_subtype]
  set x : P := θ ⟨r, hrF⟩ with hx
  have hjx : j x = r := by
    change ((θ.symm (θ ⟨r, hrF⟩) : GeneralizedFitting.subgroup X) : X) = r
    rw [MulEquiv.symm_apply_apply]
  have hjc : (centralizer ({x} : Set P)).map j =
      GeneralizedFitting.subgroup X ⊓ centralizer ({r} : Set X) := by
    rw [map_centralizer_singleton_of_injective hjinj, hjrange, hjx]
  have hmapR : ∀ {R : Subgroup X}, R ≤ GeneralizedFitting.subgroup X → (R.comap j).map j = R :=
    fun hRF =>
    map_comap_eq_self (hjrange.symm ▸ hRF)
  have hle : ∀ {R : Subgroup X}, R ≤ centralizer ({r} : Set X) →
      R.comap j ≤ centralizer ({x} : Set P) := by
    intro R hR y hy
    rw [mem_centralizer_singleton_iff]
    apply hjinj
    rw [map_mul, map_mul, hjx]
    exact mem_centralizer_singleton_iff.1 (hR hy)
  have hcomp : ∀ {R : Subgroup X}, R ≤ GeneralizedFitting.subgroup X →
      R ≤ centralizer ({r} : Set X) →
      IsPComponent 2 (R.subgroupOf (centralizer ({r} : Set X))) →
      IsPComponent 2 ((R.comap j).subgroupOf (centralizer ({x} : Set P))) := by
    intro R hRF hR hRc
    rw [isPComponent_subgroupOf_map_iff 2 Nat.prime_two hjinj, hmapR hRF, hjc]
    exact isPComponent_subgroupOf_of_le (le_inf hRF hR) inf_le_right hRc
  have hiso : ∀ {R : Subgroup X}, R ≤ GeneralizedFitting.subgroup X → R.comap j ≃* R :=
    fun {R} hRF =>
    ((R.comap j).equivMapOfInjective j hjinj).trans (MulEquiv.subgroupCongr (hmapR hRF))
  have hsoc : ∀ y : P, socleAction θ (j y) = MulAut.conj y := fun y => socleAction_symm θ y
  have hmapsoc : ∀ {R : Subgroup X}, R ≤ GeneralizedFitting.subgroup X →
      R.map (socleAction θ) = (R.comap j).map MulAut.conj := by
    intro R hRF
    conv_lhs => rw [← hmapR hRF, Subgroup.map_map]
    congr 1
    exact MonoidHom.ext hsoc
  obtain ⟨e₁⟩ := e₁
  obtain ⟨e₂⟩ := e₂
  refine ⟨x, R₁.comap j, R₂.comap j, ⟨hp2, hn, ?_, hle hR₁, hcomp hR₁F hR₁ hR₁c, hle hR₂,
    hcomp hR₂F hR₂ hR₂c, ⟨(quotientPPrimeCoreEquiv (hiso hR₁F)).trans e₁⟩,
    ⟨(quotientPPrimeCoreEquiv (hiso hR₂F)).trans e₂⟩, ?_⟩, ?_, hmapsoc hR₁F, hmapsoc hR₂F⟩
  · rw [← orderOf_injective j hjinj, hjx]
    exact hr
  · change j x ∈ R₂
    rw [hjx]
    exact hrR₂
  · rw [← hjx]
    exact hsoc x

end Socle

section Orders

theorem card_PSL_mul_two {F : Type*} [Field F] [Finite F] (hF : ringChar F ≠ 2) :
    Nat.card PSL(2, F) * 2 = Nat.card SL(2, F) := by
  have hc : Nat.card (center SL(2, F)) = 2 := by
    rw [Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (0 : Fin 2)).toEquiv,
      Fintype.card_fin]
    have : CharP F (ringChar F) := ringChar.charP F
    have hnt : Nontrivial F := inferInstance
    exact (IsPrimitiveRoot.neg_one (ringChar F) hF).card_rootsOfUnity
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (center SL(2, F))
  rw [hc] at h
  exact h.symm

theorem lt_of_lt_cube {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) : a * (a ^ 2 - 1) < b * (b ^ 2 - 1) := by
  have h1 : a ^ 2 - 1 ≤ b ^ 2 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hab.le 2) 1
  have hb1 : 1 < b ^ 2 := Nat.one_lt_pow (by norm_num) (by omega)
  rcases Nat.eq_zero_or_pos (a ^ 2 - 1) with h0 | h0
  · rw [h0, mul_zero]
    exact Nat.mul_pos (by omega) (by omega)
  · calc a * (a ^ 2 - 1) < b * (a ^ 2 - 1) := Nat.mul_lt_mul_of_pos_right hab h0
      _ ≤ b * (b ^ 2 - 1) := Nat.mul_le_mul_left b h1

theorem eq_of_mul_sq_sub_eq {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (h : a * (a ^ 2 - 1) = b * (b ^ 2 - 1)) : a = b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · exact absurd h (lt_of_lt_cube ha hab).ne
  · exact hab
  · exact absurd h (lt_of_lt_cube hb hab).ne'

theorem card_eq_of_card_SL_eq {F F' : Type*} [Field F] [Field F'] [Finite F] [Finite F']
    (h : Nat.card SL(2, F) = Nat.card SL(2, F')) : Nat.card F = Nat.card F' := by
  rw [GorensteinWalter.sl2_card_formula, GorensteinWalter.sl2_card_formula] at h
  exact eq_of_mul_sq_sub_eq Nat.card_pos Nat.card_pos h

theorem card_eq_card_pPrimeCore_mul {R : Type*} [Group R] :
    Nat.card R = Nat.card (pPrimeCore 2 R) * Nat.card (R ⧸ pPrimeCore 2 R) := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 R), mul_comm]

theorem odd_card_pPrimeCore {R : Type*} [Group R] [Finite R] : Odd (Nat.card (pPrimeCore 2 R)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact Nat.coprime_two_left.mp pPrimeCore_coprime_card

theorem not_SL_of_PSL {R : Type*} [Group R] [Finite R] {F F' : Type*} [Field F] [Field F']
    [Finite F] [Finite F'] (hF : ringChar F ≠ 2) (hcard : Nat.card F = Nat.card F')
    (e : R ≃* SL(2, F')) (e' : R ⧸ pPrimeCore 2 R ≃* PSL(2, F)) : False := by
  have h1 := card_eq_card_pPrimeCore_mul (R := R)
  rw [Nat.card_congr e.toEquiv, Nat.card_congr e'.toEquiv] at h1
  have h2 := card_PSL_mul_two hF
  have hSL : Nat.card SL(2, F') = Nat.card SL(2, F) := by
    rw [GorensteinWalter.sl2_card_formula, GorensteinWalter.sl2_card_formula, hcard]
  rw [hSL, ← h2] at h1
  have hpos : 0 < Nat.card PSL(2, F) := Nat.card_pos
  have hO : Nat.card (pPrimeCore 2 R) = 2 := by
    have : Nat.card PSL(2, F) * 2 = Nat.card PSL(2, F) * Nat.card (pPrimeCore 2 R) := by
      rw [h1]; ring
    exact (Nat.eq_of_mul_eq_mul_left hpos this).symm
  have hodd := odd_card_pPrimeCore (R := R)
  rw [hO] at hodd
  exact absurd hodd (by decide)

theorem PropCData.card_ne {P : Type} [Group P] [Finite P] {x : P} {R₁ R₂ : Subgroup P}
    {p n : ℕ} [Fact p.Prime] (h : PropCData x R₁ R₂ p n) : Nat.card R₁ ≠ Nat.card R₂ := by
  intro heq
  obtain ⟨e₁⟩ := h.iso₁
  obtain ⟨e₂⟩ := h.iso₂
  have hGF : ringChar (GaloisField p n) ≠ 2 := by
    rw [ringChar.eq (GaloisField p n) p]
    exact h.p_ne_two
  have h1 := card_eq_card_pPrimeCore_mul (R := R₁)
  have h2 := card_eq_card_pPrimeCore_mul (R := R₂)
  rw [Nat.card_congr e₁.toEquiv] at h1
  rw [Nat.card_congr e₂.toEquiv, ← card_PSL_mul_two hGF] at h2
  have hpos : 0 < Nat.card PSL(2, GaloisField p n) := Nat.card_pos
  have hO : Nat.card (pPrimeCore 2 R₁) = 2 * Nat.card (pPrimeCore 2 R₂) := by
    have : Nat.card PSL(2, GaloisField p n) * Nat.card (pPrimeCore 2 R₁) =
        Nat.card PSL(2, GaloisField p n) * (2 * Nat.card (pPrimeCore 2 R₂)) := by
      rw [heq] at h1
      rw [mul_comm, ← h1, h2]
      ring
    exact Nat.eq_of_mul_eq_mul_left hpos this
  have hodd := odd_card_pPrimeCore (R := R₁)
  rw [hO] at hodd
  exact (Nat.not_odd_iff_even.2 (even_two_mul _)) hodd

end Orders

section Gen

open Matrix in
theorem sq_eq_one_of_mem_center_SL {F : Type*} [Field F] {z : SL(2, F)} (hz : z ∈ center SL(2, F)) :
    z ^ 2 = 1 := by
  obtain ⟨r, hr, hrz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hz
  rw [Fintype.card_fin] at hr
  rw [pow_two]
  apply Subtype.ext
  change (z : Matrix (Fin 2) (Fin 2) F) * z = 1
  rw [← hrz, Matrix.scalar_apply, diagonal_mul_diagonal, ← pow_two, hr, diagonal_one]

theorem two_ne_zero_galoisField {p n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    (2 : GaloisField p n) ≠ 0 := by
  have : ringChar (GaloisField p n) = p := ringChar.eq (GaloisField p n) p
  exact Ring.two_ne_zero (by rw [this]; exact hp2)

theorem ringChar_galoisField_ne_two {p n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    ringChar (GaloisField p n) ≠ 2 := by
  rw [ringChar.eq (GaloisField p n) p]
  exact hp2

theorem pPrimeCore_eq_bot_of_center {R : Type*} [Group R] [Finite R] (hR : IsQuasisimple R)
    {a : R} (ha : orderOf a = 2) (hZ : ∀ z ∈ center R, z ^ 2 = 1) : pPrimeCore 2 R = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hR
      (Normal.isSubnormal (pPrimeCore_normal (p := 2) (G := R))) with h | h
  · exact absurd (h.symm ▸ mem_top a) (not_mem_pPrimeCore_of_orderOf ha)
  · refine eq_bot_iff.2 fun y hy => ?_
    rw [mem_bot]
    have hy2 := hZ y (h hy)
    have hodd : Odd (orderOf (⟨y, hy⟩ : pPrimeCore 2 R)) := Odd.of_dvd_nat odd_card_pPrimeCore
      (orderOf_dvd_natCard _)
    rw [Subgroup.orderOf_mk] at hodd
    have hdvd : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one hy2
    have h1 : orderOf y = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
      · exact h
      · rw [h] at hodd; exact absurd hodd (by decide)
    exact orderOf_eq_one_iff.1 h1

theorem isSolvable_of_prime_dvd_two_three {G : Type*} [Group G] [Finite G]
    (h : ∀ p : ℕ, p.Prime → p ∣ Nat.card G → p = 2 ∨ p = 3) : Group.IsSolvable G := by
  have hpos : Nat.card G ≠ 0 := Nat.card_pos.ne'
  obtain ⟨a, m, hm2, hm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hpos 2 (by norm_num)
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hm
    exact hpos hm
  obtain ⟨b, k, hk3, hk⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm0 3 (by norm_num)
  have hk1 : k = 1 := by
    by_contra hk1
    obtain ⟨q, hq, hqk⟩ := Nat.exists_prime_and_dvd hk1
    have hqG : q ∣ Nat.card G := by
      rw [hm, hk]
      exact Dvd.dvd.mul_left (Dvd.dvd.mul_left hqk _) _
    rcases h q hq hqG with rfl | rfl
    · exact hm2 (hk ▸ Dvd.dvd.mul_left hqk _)
    · exact hk3 hqk
  have : Fintype G := Fintype.ofFinite G
  refine Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
    Nat.prime_three (by norm_num) (a := a) (b := b) ?_
  rw [← Nat.card_eq_fintype_card, hm, hk, hk1, mul_one]

theorem isSolvable_SL_two_of_card_three {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 3) :
    Group.IsSolvable SL(2, F) := by
  refine isSolvable_of_prime_dvd_two_three fun q hq hdvd => ?_
  rw [GorensteinWalter.sl2_card_formula, hF, show 3 * (3 ^ 2 - 1) = 2 ^ 3 * 3 by norm_num] at hdvd
  rcases (Nat.Prime.dvd_mul hq).1 hdvd with h | h
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow h))
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).1 h)

end Gen

end CFSG.ComponentClassification.Burgoyne.C
