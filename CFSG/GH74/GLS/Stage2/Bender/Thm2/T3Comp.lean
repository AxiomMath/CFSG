module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L915T3
public import CFSG.GH74.GLS.Stage2.Local.PerfInner

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.T3

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage12

theorem oPrimeResidual_two_normal (X : Type) [Group X] : (oPrimeResidual 2 X).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have h : oPrimeResidual 2 X ≤ (oPrimeResidual 2 X).comap (MulAut.conj g).toMonoidHom := by
    unfold oPrimeResidual
    rw [Subgroup.closure_le]
    rintro s ⟨k, hk⟩
    apply Subgroup.subset_closure
    refine ⟨k, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [conj_pow, hk]
    simp
  exact h hn

theorem sylow_le_oPrimeResidual {X : Type} [Group X] [Finite X] (T : Sylow 2 X) :
    (T : Subgroup X) ≤ oPrimeResidual 2 X := by
  intro x hx
  apply Subgroup.subset_closure
  have : IsPGroup 2 ↥(T : Subgroup X) := T.isPGroup'
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp this) ⟨x, hx⟩
  refine ⟨k, ?_⟩
  have h1 : (⟨x, hx⟩ : ↥(T : Subgroup X)) ^ (2 ^ k) = 1 := by
    rw [← hk]
    exact pow_orderOf_eq_one _
  have := congrArg Subtype.val h1
  simpa using this

theorem perfect_le_oPrimeResidual {X : Type} [Group X] [Finite X] (Y : Subgroup X)
    (hY : Group.IsPerfect ↥Y) : Y ≤ oPrimeResidual 2 X := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := oPrimeResidual_two_normal X
  obtain ⟨T⟩ : Nonempty (Sylow 2 X) := inferInstance
  have hidx : Odd (oPrimeResidual 2 X).index := by
    have h1 : (oPrimeResidual 2 X).index ∣ (T : Subgroup X).index :=
      Subgroup.index_dvd_of_le (sylow_le_oPrimeResidual T)
    have h2 : ¬ 2 ∣ (T : Subgroup X).index := T.not_dvd_index
    have h3 : ¬ 2 ∣ (oPrimeResidual 2 X).index := fun h => h2 (h.trans h1)
    exact Nat.odd_iff.mpr (by omega)
  have hodd : Odd (Nat.card (X ⧸ oPrimeResidual 2 X)) := by
    rw [← Subgroup.index_eq_card]; exact hidx
  have hsolv : Group.IsSolvable (X ⧸ oPrimeResidual 2 X) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  let q : ↥Y →* X ⧸ oPrimeResidual 2 X := (QuotientGroup.mk' (oPrimeResidual 2 X)).comp Y.subtype
  have hperf : Group.IsPerfect q.range := by
    have := hY
    exact Group.IsPerfect.range q
  have hsolvR : Group.IsSolvable q.range := by
    have := hsolv
    infer_instance
  have hbot : q.range = ⊥ := by
    by_contra hne
    have : Nontrivial q.range := (Subgroup.nontrivial_iff_ne_bot _).2 hne
    have := hperf
    exact Group.IsPerfect.not_isSolvable q.range hsolvR
  intro x hx
  have h1 : q ⟨x, hx⟩ = 1 := by
    have : q ⟨x, hx⟩ ∈ q.range := ⟨⟨x, hx⟩, rfl⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact this
  exact (QuotientGroup.eq_one_iff x).1 h1

theorem perfect_le_oPrimePResidual {X : Type} [Group X] [Finite X] (Y : Subgroup X)
    (hY : Group.IsPerfect ↥Y) : Y ≤ oPrimePResidual 2 X := by
  have hle : Y ≤ oPrimeResidual 2 X := perfect_le_oPrimeResidual Y hY
  let e : ↥(Y.subgroupOf (oPrimeResidual 2 X)) ≃* ↥Y := Subgroup.subgroupOfEquivOfLe hle
  have hperf : Group.IsPerfect ↥(Y.subgroupOf (oPrimeResidual 2 X)) := by
    have := hY
    exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have h2 := CFSG.GH74.GLS.Stage1.Main.perfect_le_oResidual (Y.subgroupOf (oPrimeResidual 2 X)) hperf
  intro x hx
  have hx1 : (⟨x, hle hx⟩ : ↥(oPrimeResidual 2 X)) ∈ Y.subgroupOf (oPrimeResidual 2 X) := hx
  exact ⟨_, h2 hx1, rfl⟩

theorem exists_elt_order_in_LC {G : Type} [Group G] [Finite G] {z : G} (hI : PerfInner z) {J : Subgroup G}
    (hzJ : z ∈ J) (hz : orderOf z = 2)
    (hnoc : ∀ c ∈ J, (∀ g ∈ J, c * g = g * c) → c * c = 1 → c = 1) {p n : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hn : 2 ≤ n) (hLie : LieModel (↥J ⧸ center ↥J) .PSL 3 p n)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓq : ℓ ∣ (p ^ n) ^ 2 - 1) :
    ∃ x : ↥(Cen z), orderOf x = ℓ ∧ (x : G) ∈ LC z := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨F, iF, fF, hFcard, Y, hYC, hYperf, φ, hφs, -⟩ :=
    L915.exists_perfect_lift_of_lieModel hzJ hz hnoc hp hp2 hn hLie
  have hcardSL := CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two F
  have h1 : Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) ∣ Nat.card ↥Y :=
    Subgroup.card_dvd_of_surjective hφs
  rw [hcardSL, hFcard] at h1
  have hℓY : ℓ ∣ Nat.card ↥Y := hℓq.trans ((dvd_mul_left _ _).trans h1)
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' ℓ hℓY
  have hmem : ∀ y : ↥Y, ((y : ↥J) : G) ∈ Cen z := by
    intro y
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := Subgroup.mem_centralizer_singleton_iff.mp (hYC y.2)
    exact congrArg Subtype.val this
  let f : ↥Y →* ↥(Cen z) := (J.subtype.comp Y.subtype).codRestrict (Cen z) hmem
  have hfinj : Function.Injective f := by
    intro a b hab
    have := congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext this)
  have hperf : Group.IsPerfect ↥f.range := by
    have := hYperf
    exact Group.IsPerfect.range f
  have hle : f.range ≤ oPrimePResidual 2 ↥(Cen z) := perfect_le_oPrimePResidual f.range hperf
  have hbar : Group.IsPerfect ↥(f.range.map (toBar z)) := by
    have := hperf
    exact Group.IsPerfect.map (toBar z)
  refine ⟨f y, ?_, ?_⟩
  · rw [orderOf_injective f hfinj y, hy]
  · exact (Stage1.Thm6.Prod.mem_LC_iff z (f y)).2 ⟨hle ⟨y, rfl⟩, hI _ hbar ⟨f y, ⟨y, rfl⟩, rfl⟩⟩

theorem exists_two_comps {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} {k : Kind}
    (hdata : Stage1Data G z S k) (hk : k = Kind.g2 ∨ k = Kind.psp4 ∨ ∃ ε : Bool, k = Kind.l4 ε) :
    ∃ (r₁ r₂ : ℕ) (L₁ L₂ : Subgroup (CentralizerBar z)), Odd r₁ ∧ Odd r₂ ∧ 3 < r₁ ∧
      IsCentralProd L₁ L₂ (LBar z) ∧ HasSL2Model ↥L₁ (fun q => q = r₁) ∧
      HasSL2Model ↥L₂ (fun q => q = r₂) := by
  cases hdata with
  | g2 h =>
    obtain ⟨r₁, r₂, L₁, L₂, hshape⟩ := h.shape
    obtain ⟨ho1, ho2, hgt, hprod, hs1, hs2, -⟩ := hshape
    exact ⟨r₁, r₂, L₁, L₂, ho1, ho2, hgt, hprod, hs1, hs2⟩
  | m12 h => rcases hk with h' | h' | ⟨ε, h'⟩ <;> cases h'
  | psp4 h =>
    obtain ⟨q, L₁, L₂, h⟩ := h
    exact ⟨q, q, L₁, L₂, h.pair.odd, h.pair.odd, h.pair.gt3, h.pair.prod, h.pair.sl₁, h.pair.sl₂⟩
  | l4 ε h =>
    obtain ⟨q, L₁, L₂, h⟩ := h
    exact ⟨q, q, L₁, L₂, h.pair.odd, h.pair.odd, h.pair.gt3, h.pair.prod, h.pair.sl₁, h.pair.sl₂⟩
  | mcl h => rcases hk with h' | h' | ⟨ε, h'⟩ <;> cases h'
  | ly h => rcases hk with h' | h' | ⟨ε, h'⟩ <;> cases h'

theorem perfInner_of_data {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} {k : Kind}
    (hdata : Stage1Data G z S k) (hk : k = Kind.g2 ∨ k = Kind.psp4 ∨ ∃ ε : Bool, k = Kind.l4 ε) :
    PerfInner z := by
  cases hdata with
  | g2 h => exact h.perf
  | m12 h => rcases hk with h' | h' | ⟨ε, h'⟩ <;> cases h'
  | psp4 h =>
    obtain ⟨q, L₁, L₂, h⟩ := h
    exact perfInner_of_pair h.pair
  | l4 ε h =>
    obtain ⟨q, L₁, L₂, h⟩ := h
    exact perfInner_of_pair h.pair
  | mcl h => rcases hk with h' | h' | ⟨ε, h'⟩ <;> cases h'
  | ly h => rcases hk with h' | h' | ⟨ε, h'⟩ <;> cases h'

theorem sl2_not_comm' (F : Type) [Field F] :
    ∃ a b : Matrix.SpecialLinearGroup (Fin 2) F, a * b ≠ b * a := by
  refine ⟨⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩,
    ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩, ?_⟩
  intro h
  have h2 := congrFun (congrFun (congrArg Subtype.val h) 0) 0
  change ((!![1, 1; 0, 1] * !![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) F) 0 0) =
    ((!![1, 0; 1, 1] * !![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) F) 0 0) at h2
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h2

theorem noncomm_of_hasSL2Model' {K : Type} [Group K] {P : ℕ → Prop} (h : HasSL2Model K P) :
    ∃ a b : K, a * b ≠ b * a := by
  obtain ⟨F, _, _, _, ⟨e⟩⟩ := h
  obtain ⟨a, b, hab⟩ := sl2_not_comm' F
  refine ⟨e.symm (specialLinearGroupEquivStatedSL 2 F a),
    e.symm (specialLinearGroupEquivStatedSL 2 F b), fun h => hab ?_⟩
  have h1 := congrArg e h
  rw [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h1
  exact (specialLinearGroupEquivStatedSL 2 F).injective (by rw [map_mul, map_mul]; exact h1)

@[expose] def conjAction {G : Type} [Group G] (P C : Subgroup G)
    (hnorm : ∀ e ∈ C, ∀ x ∈ P, e * x * e⁻¹ ∈ P) : ↥C →* MulAut ↥P where
  toFun e :=
    { toFun := fun x => ⟨(e : G) * x * (e : G)⁻¹, hnorm e e.2 x x.2⟩
      invFun := fun x => ⟨(e : G)⁻¹ * x * (e : G), by
        have := hnorm (e : G)⁻¹ (C.inv_mem e.2) x x.2
        simpa using this⟩
      left_inv := fun x => by ext; simp [mul_assoc]
      right_inv := fun x => by ext; simp [mul_assoc]
      map_mul' := fun x y => by ext; simp [mul_assoc] }
  map_one' := by ext; simp
  map_mul' := fun e f => by ext; simp [mul_assoc]

theorem coe_conjAction_apply {G : Type} [Group G] (P C : Subgroup G)
    (hnorm : ∀ e ∈ C, ∀ x ∈ P, e * x * e⁻¹ ∈ P) (e : ↥C) (x : ↥P) :
    ((conjAction P C hnorm e x : ↥P) : G) = (e : G) * x * (e : G)⁻¹ := rfl

theorem conjAction_injective {G : Type} [Group G] (P C : Subgroup G)
    (hnorm : ∀ e ∈ C, ∀ x ∈ P, e * x * e⁻¹ ∈ P)
    (hfaith : ∀ e ∈ C, (∀ x ∈ P, e * x * e⁻¹ = x) → e = 1) :
    Function.Injective (conjAction P C hnorm) := by
  rw [injective_iff_map_eq_one]
  intro e he
  apply Subtype.ext
  refine hfaith e e.2 fun x hx => ?_
  have h1 := DFunLike.congr_fun he ⟨x, hx⟩
  rw [MulAut.one_apply] at h1
  have h2 := congrArg Subtype.val h1
  rw [coe_conjAction_apply] at h2
  exact h2

end CFSG.GH74.GLS.Stage2.Bender.Thm2.T3
