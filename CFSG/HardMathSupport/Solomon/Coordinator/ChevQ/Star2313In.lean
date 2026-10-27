module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Gen2318E64In
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Gen2318Out
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.I102Uniq
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.E78Sylow
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E68FieldFix

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open CFSG.Open

@[expose] def LinearAutCube : Prop :=
  ∀ (F : Type) [Field F] [Finite F], Nat.card F = 4 → ∀ N : ℕ, 3 ≤ N →
    ∀ α : MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin N) F), α ^ 3 = 1 →
      ∃ g : Matrix.GeneralLinearGroup (Fin N) F, ∀ x y : Matrix.SpecialLinearGroup (Fin N) F,
        (y : Matrix (Fin N) (Fin N) F) = (g : Matrix (Fin N) (Fin N) F) * (x : Matrix (Fin N) (Fin N) F) *
          ((g⁻¹ : Matrix.GeneralLinearGroup (Fin N) F) : Matrix (Fin N) (Fin N) F) →
          α (x : Matrix.ProjectiveSpecialLinearGroup (Fin N) F) =
            (y : Matrix.ProjectiveSpecialLinearGroup (Fin N) F)

@[expose] def Star2313UnitaryInput : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA r q).Valid), Gen2318Index (TauCeti.LieTypeIndex.twistedA r q) →
    Nonempty (S ≃* (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.twistedA r q, hv⟩).Group) →
    ∀ D : Subgroup (MulAut S), IsElemAbelian 3 D →
      ∃ E : Subgroup (MulAut S), E ≤ D ∧ E.relIndex D ≤ 9 ∧
        ∃ U : Subgroup S, U ≠ ⊥ ∧ IsPGroup 2 ↥U ∧ ∀ φ ∈ E, ∀ u ∈ U, φ u ∈ U

namespace Star2313InAux

section Generic

theorem exists_fixed_involution {G : Type*} [Group G] [Finite G] (f : G →* G)
    (hf : ∀ x, f (f x) = x) (hG : Even (Nat.card G)) :
    ∃ t : G, t ≠ 1 ∧ t ^ 2 = 1 ∧ f t = t := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let inv : Function.End G := fun x => x⁻¹
  have hinv : inv ^ 2 ^ 1 = 1 := by
    funext x
    change (x⁻¹)⁻¹ = x
    exact inv_inv x
  have h1 := Equiv.Perm.card_fixedPoints_modEq (p := 2) (n := 1) hinv
  let I := {x : G // x⁻¹ = x}
  let fI : Function.End I := fun x => ⟨f x.1, by rw [← map_inv, x.2]⟩
  have hfI : fI ^ 2 ^ 1 = 1 := by
    funext x
    change fI (fI x) = x
    exact Subtype.ext (hf x.1)
  have h2 := Equiv.Perm.card_fixedPoints_modEq (p := 2) (n := 1) hfI
  have hIcard : Fintype.card inv.fixedPoints = Fintype.card I :=
    Fintype.card_congr (Equiv.subtypeEquivRight fun x => Iff.rfl)
  have hGeven : Fintype.card G % 2 = 0 := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.even_iff.1 hG
  have hfix : Fintype.card fI.fixedPoints % 2 = 0 := by
    have e1 : Fintype.card G % 2 = Fintype.card inv.fixedPoints % 2 := h1
    have e2 : Fintype.card I % 2 = Fintype.card fI.fixedPoints % 2 := h2
    omega
  let one : I := ⟨1, inv_one⟩
  have hone : one ∈ fI.fixedPoints := Subtype.ext (by simp [fI, one])
  by_contra hno
  push Not at hno
  have hsub : ∀ y : fI.fixedPoints, y = ⟨one, hone⟩ := by
    intro ⟨⟨y, hy⟩, hyf⟩
    have hfy : f y = y := congrArg Subtype.val hyf
    by_cases hy1 : y = 1
    · subst hy1
      rfl
    · exfalso
      have hy2 : y ^ 2 = 1 := by
        rw [sq]
        nth_rewrite 1 [← hy]
        exact inv_mul_cancel y
      exact hno y hy1 hy2 hfy
  have hcard1 : Fintype.card fI.fixedPoints = 1 :=
    Fintype.card_eq_one_iff.2 ⟨⟨one, hone⟩, hsub⟩
  omega

theorem mem_of_sq_eq_one_of_odd_index {G : Type*} [Group G] {N : Subgroup G} [N.Normal]
    (hN : Odd N.index) {t : G} (ht : t ^ 2 = 1) : t ∈ N := by
  haveI : Finite (G ⧸ N) := Nat.finite_of_card_ne_zero (by
    have : Nat.card (G ⧸ N) = N.index := rfl
    rw [this]
    exact (Nat.pos_of_ne_zero (by rintro h; rw [h] at hN; exact (Nat.not_odd_zero hN))).ne')
  have h2 : orderOf (t : G ⧸ N) ∣ 2 := orderOf_dvd_of_pow_eq_one (by
    rw [← QuotientGroup.mk_pow, ht, QuotientGroup.mk_one])
  have hc : orderOf (t : G ⧸ N) ∣ N.index := orderOf_dvd_natCard _
  have hodd : Odd (orderOf (t : G ⧸ N)) := Odd.of_dvd_nat hN hc
  have h1 : orderOf (t : G ⧸ N) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h | h
    · exact h
    · rw [h] at hodd
      exact absurd hodd (by decide)
  have := orderOf_eq_one_iff.1 h1
  exact (QuotientGroup.eq_one_iff t).1 this

theorem relIndex_centralizer_le {G : Type*} [Group G] (E : Subgroup G) (x : G) (T : Finset G)
    (hT : ∀ e ∈ E, e * x * e⁻¹ ∈ T) :
    (Subgroup.centralizer ({x} : Set G)).relIndex E ≤ T.card := by
  classical
  set C : Subgroup ↥E := (Subgroup.centralizer ({x} : Set G)).subgroupOf E with hC
  let φ : ↥E ⧸ C → ↥T := Quotient.lift (fun e : ↥E => (⟨(e : G) * x * (e : G)⁻¹, hT e e.2⟩ : ↥T))
    (by
      intro a b hab
      have hab' : a⁻¹ * b ∈ C := QuotientGroup.leftRel_apply.1 hab
      rw [hC, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at hab'
      have h := hab' x (Set.mem_singleton x)
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h
      apply Subtype.ext
      show (a : G) * x * (a : G)⁻¹ = (b : G) * x * (b : G)⁻¹
      calc (a : G) * x * (a : G)⁻¹ = (a : G) * (x * ((a : G)⁻¹ * (b : G))) * (b : G)⁻¹ := by group
        _ = (a : G) * (((a : G)⁻¹ * (b : G)) * x) * (b : G)⁻¹ := by rw [h]
        _ = (b : G) * x * (b : G)⁻¹ := by group)
  have hφ : Function.Injective φ := by
    intro a b hab
    induction a using QuotientGroup.induction_on with | H a => ?_
    induction b using QuotientGroup.induction_on with | H b => ?_
    have h : (a : G) * x * (a : G)⁻¹ = (b : G) * x * (b : G)⁻¹ := congrArg Subtype.val hab
    refine QuotientGroup.eq.2 ?_
    rw [hC, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc y * ((a : G)⁻¹ * (b : G)) = (a : G)⁻¹ * ((a : G) * y * (a : G)⁻¹) * (b : G) := by group
      _ = (a : G)⁻¹ * ((b : G) * y * (b : G)⁻¹) * (b : G) := by rw [h]
      _ = (a : G)⁻¹ * (b : G) * y := by group
  have hfin : Finite (↥E ⧸ C) := Finite.of_injective φ hφ
  calc (Subgroup.centralizer ({x} : Set G)).relIndex E = Nat.card (↥E ⧸ C) := rfl
    _ ≤ Nat.card ↥T := Nat.card_le_card_of_injective φ hφ
    _ = T.card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]

theorem exists_relIndex_stabilizer_le_three {H α : Type*} [Group H] [MulAction H α] [Finite H]
    {B : Subgroup H} (hB : IsPGroup 3 B) (X : Finset α) (hX : ∀ b ∈ B, ∀ x ∈ X, b • x ∈ X)
    (h9 : ¬ 9 ∣ X.card) : ∃ x ∈ X, (MulAction.stabilizer H x).relIndex B ≤ 3 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hcon
  push Not at hcon
  letI : MulAction ↥B ↥X :=
    { smul := fun b x => ⟨(b : H) • (x : α), hX b b.2 x x.2⟩
      one_smul := fun x => Subtype.ext (one_smul H (x : α))
      mul_smul := fun b c x => Subtype.ext (mul_smul (b : H) (c : H) (x : α)) }
  have hsmul : ∀ (b : ↥B) (x : ↥X), ((b • x : ↥X) : α) = (b : H) • (x : α) := fun _ _ => rfl
  have hstab : ∀ x : ↥X, MulAction.stabilizer ↥B x =
      (MulAction.stabilizer H (x : α)).subgroupOf B := by
    intro x
    ext b
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff,
      ← hsmul, Subtype.ext_iff]
  have horb : ∀ x : ↥X, 9 ∣ Nat.card (MulAction.orbit ↥B x) := by
    intro x
    haveI : Finite (MulAction.orbit ↥B x) := Subtype.finite
    obtain ⟨n, hn⟩ := hB.card_orbit x
    have hidx : Nat.card (MulAction.orbit ↥B x) = (MulAction.stabilizer H (x : α)).relIndex B := by
      rw [Subgroup.relIndex, ← hstab, MulAction.index_stabilizer, Nat.card_coe_set_eq]
    have hlt := hcon x x.2
    rw [← hidx, hn] at hlt
    have hn2 : 2 ≤ n := by
      by_contra h
      push Not at h
      interval_cases n <;> norm_num at hlt
    rw [hn]
    exact (show (9 : ℕ) = 3 ^ 2 by norm_num) ▸ pow_dvd_pow 3 hn2
  have hsum : Nat.card ↥X = ∑ ω : Quotient (MulAction.orbitRel ↥B ↥X),
      Nat.card (MulAction.orbit ↥B ω.out) := by
    rw [Nat.card_congr (MulAction.selfEquivSigmaOrbits ↥B ↥X), Nat.card_sigma]
  have h9X : 9 ∣ Nat.card ↥X := by
    rw [hsum]
    exact Finset.dvd_sum fun ω _ => horb ω.out
  apply h9
  rwa [Nat.card_eq_fintype_card, Fintype.card_coe] at h9X

@[expose] def InvCent (G : Type*) [Group G] : Prop :=
  ∀ P : Subgroup G, IsElemAbelian 3 P → ∃ E : Subgroup G, E ≤ P ∧ Nat.card P ≤ 9 * Nat.card E ∧
    ∃ t : G, t ≠ 1 ∧ t ^ 2 = 1 ∧ ∀ e ∈ E, e * t = t * e

theorem InvCent.of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) (h : InvCent G) :
    InvCent H := by
  intro P hP
  obtain ⟨E, hEP, hcard, t, ht1, ht2, hEt⟩ := h (P.map e.symm.toMonoidHom) (hP.map _)
  refine ⟨E.map e.toMonoidHom, ?_, ?_, e t, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, rfl⟩ := hEP hx
    simpa using hy
  · rw [Subgroup.card_map_of_injective e.injective, ← Subgroup.card_map_of_injective
      (f := e.symm.toMonoidHom) e.symm.injective]
    exact hcard
  · intro h1
    apply ht1
    apply e.injective
    rw [h1, map_one]
  · rw [← map_pow, ht2, map_one]
  · rintro _ ⟨x, hx, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, hEt x hx]

theorem star_of_inner {S : Type*} [Group S] [Finite S] (hZ : Subgroup.center S = ⊥) (hS : InvCent S)
    (D : Subgroup (MulAut S)) (hD : IsElemAbelian 3 D)
    (hinn : D ≤ (MulAut.conj : S →* MulAut S).range) :
    ∃ E : Subgroup (MulAut S), E ≤ D ∧ E.relIndex D ≤ 9 ∧
      ∃ U : Subgroup S, U ≠ ⊥ ∧ IsPGroup 2 ↥U ∧ ∀ φ ∈ E, ∀ u ∈ U, φ u ∈ U := by
  classical
  have hinj : Function.Injective (MulAut.conj : S →* MulAut S) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxZ : x ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h := congrArg (fun φ : MulAut S => φ y) hx
      simp only [MulAut.conj_apply, MulAut.one_apply] at h
      calc y * x = x * y * x⁻¹ * x := by rw [h]
        _ = x * y := by group
    rw [hZ, Subgroup.mem_bot] at hxZ
    exact hxZ
  set P : Subgroup S := D.comap MulAut.conj with hP
  have hPmap : P.map MulAut.conj = D := Subgroup.map_comap_eq_self hinn
  have hPel : IsElemAbelian 3 P := by
    refine ⟨⟨⟨fun a b => Subtype.ext (hinj ?_)⟩⟩, fun x hx => hinj ?_⟩
    · have h := congrArg Subtype.val (hD.1.is_comm.comm ⟨_, a.2⟩ ⟨_, b.2⟩)
      simp only [Subgroup.coe_mul] at h
      rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact h
    · rw [map_pow, map_one]
      exact hD.2 _ hx
  obtain ⟨E, hEP, hcard, t, ht1, ht2, hEt⟩ := hS P hPel
  refine ⟨E.map MulAut.conj, ?_, ?_, Subgroup.zpowers t, ?_, ?_, ?_⟩
  · rw [← hPmap]
    exact Subgroup.map_mono hEP
  · have hle : E.map MulAut.conj ≤ D := by
      rw [← hPmap]
      exact Subgroup.map_mono hEP
    have h1 := Subgroup.relIndex_mul_card (E.map MulAut.conj) D
    rw [inf_of_le_left hle, Subgroup.card_map_of_injective hinj] at h1
    have hD' : Nat.card D = Nat.card P := by
      rw [← hPmap, Subgroup.card_map_of_injective hinj]
    have hEpos : 0 < Nat.card E := Nat.card_pos
    by_contra hlt
    push Not at hlt
    have : 10 * Nat.card E ≤ (E.map MulAut.conj).relIndex D * Nat.card E :=
      Nat.mul_le_mul_right _ hlt
    omega
  · intro h
    apply ht1
    have : t ∈ Subgroup.zpowers t := Subgroup.mem_zpowers t
    rw [h, Subgroup.mem_bot] at this
    exact this
  · intro u
    refine ⟨1, Subtype.ext ?_⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 u.2
    rw [Subgroup.coe_pow, ← hk, pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, ht2, one_zpow, Subgroup.coe_one]
  · rintro _ ⟨e, he, rfl⟩ u hu
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    have hc : Commute e (t ^ k) := ((Commute.zpow_right (hEt e he) k))
    rw [MulAut.conj_apply, hc.eq, mul_inv_cancel_right]
    exact Subgroup.zpow_mem_zpowers t k

theorem relIndex_le_of_card_le {G : Type*} [Group G] {E D : Subgroup G} [Finite D] (hED : E ≤ D)
    {n : ℕ} (h : Nat.card D ≤ n * Nat.card E) : E.relIndex D ≤ n := by
  have h1 := Subgroup.relIndex_mul_card E D
  rw [inf_of_le_left hED] at h1
  haveI : Finite E := Finite.of_injective _ (Subgroup.inclusion_injective hED)
  have hEpos : 0 < Nat.card E := Nat.card_pos
  by_contra hlt
  push Not at hlt
  have : (n + 1) * Nat.card E ≤ E.relIndex D * Nat.card E := Nat.mul_le_mul_right _ hlt
  nlinarith

@[expose] def StarConcl {S : Type*} [Group S] (D : Subgroup (MulAut S)) : Prop :=
  ∃ E : Subgroup (MulAut S), E ≤ D ∧ E.relIndex D ≤ 9 ∧
    ∃ U : Subgroup S, U ≠ ⊥ ∧ IsPGroup 2 ↥U ∧ ∀ φ ∈ E, ∀ u ∈ U, φ u ∈ U

theorem starConcl_of_congr {S C : Type*} [Group S] [Group C] [Finite S] (e : S ≃* C)
    (D : Subgroup (MulAut S)) (h : StarConcl (D.map (MulAut.congr e).toMonoidHom)) : StarConcl D := by
  obtain ⟨E', hE'D, hidx, U', hU'0, hU'2, hU'⟩ := h
  set c := MulAut.congr e with hc
  have hEA : E'.map c.symm.toMonoidHom ≤ D := by
    rintro _ ⟨φ', hφ', rfl⟩
    obtain ⟨ψ, hψ, rfl⟩ := hE'D hφ'
    simpa using hψ
  haveI : Finite (MulAut S) := MulEquiv.finite_left
  refine ⟨E'.map c.symm.toMonoidHom, hEA, ?_, U'.map e.symm.toMonoidHom, ?_, hU'2.map _, ?_⟩
  · refine relIndex_le_of_card_le hEA (n := 9) ?_
    have hle : E' ≤ D.map c.toMonoidHom := hE'D
    have h1 := Subgroup.relIndex_mul_card E' (D.map c.toMonoidHom)
    rw [inf_of_le_left hle] at h1
    have h2 : Nat.card D = Nat.card (D.map c.toMonoidHom) :=
      (Subgroup.card_map_of_injective c.injective).symm
    have h3 : Nat.card (E'.map c.symm.toMonoidHom) = Nat.card E' :=
      Subgroup.card_map_of_injective c.symm.injective
    rw [h2, h3, ← h1]
    exact Nat.mul_le_mul_right _ hidx
  · intro h
    exact hU'0 ((Subgroup.map_eq_bot_iff_of_injective U' (f := e.symm.toMonoidHom)
      e.symm.injective).1 h)
  · rintro _ ⟨φ', hφ', rfl⟩ _ ⟨u', hu', rfl⟩
    refine ⟨φ' u', hU' φ' hφ' u' hu', ?_⟩
    simp [hc, MulAut.congr_apply]

end Generic

section Fields

@[expose] noncomputable def frobPow (K : Type) [Field K] [Finite K] [CharP K 2] (f : ℕ) : K ≃+* K :=
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  RingEquiv.ofBijective (iterateFrobenius K 2 f)
    ⟨(iterateFrobenius K 2 f).injective,
      Finite.surjective_of_injective (iterateFrobenius K 2 f).injective⟩

theorem frobPow_apply {K : Type} [Field K] [Finite K] [CharP K 2] (f : ℕ) (c : K) :
    frobPow K f c = c ^ 2 ^ f :=
  rfl

theorem frobPow_frobPow {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ}
    (hK : Nat.card K = (2 ^ f) ^ 2) (c : K) : frobPow K f (frobPow K f c) = c := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  rw [frobPow_apply, frobPow_apply, ← pow_mul, ← sq, ← hK, Nat.card_eq_fintype_card]
  exact FiniteField.pow_card c

theorem card_fixSubfield_frobPow {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ}
    (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2) :
    Nat.card ↥(CFSG.LieType.Chevalley.fixSubfield (frobPow K f)) = 2 ^ f := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hq : 1 < 2 ^ f := Nat.one_lt_two_pow (by omega)
  apply le_antisymm
  · set Z : Finset K := Finset.univ.filter (fun c => c ^ 2 ^ f = c) with hZ
    have hZc : Nat.card ↥(CFSG.LieType.Chevalley.fixSubfield (frobPow K f)) = Z.card := by
      rw [← Nat.card_eq_finsetCard]
      refine Nat.card_congr (Equiv.subtypeEquivRight fun c => ?_)
      rw [CFSG.LieType.Chevalley.mem_fixSubfield, frobPow_apply, hZ, Finset.mem_filter]
      simp
    rw [hZc]
    have hne : (Polynomial.X ^ 2 ^ f - Polynomial.X : Polynomial K) ≠ 0 :=
      FiniteField.X_pow_card_sub_X_ne_zero K hq
    calc Z.card ≤ (Polynomial.X ^ 2 ^ f - Polynomial.X : Polynomial K).natDegree :=
          Polynomial.card_le_degree_of_subset_roots (by
            intro c hc
            rw [Polynomial.mem_roots hne, Polynomial.IsRoot, Polynomial.eval_sub,
              Polynomial.eval_pow, Polynomial.eval_X, sub_eq_zero]
            have hc' : c ∈ Z := hc
            rw [hZ, Finset.mem_filter] at hc'
            exact hc'.2)
      _ = 2 ^ f := FiniteField.X_pow_card_sub_X_natDegree_eq K hq
  · obtain ⟨k, _, _, _, hk, -, hfix⟩ :=
      I102UniqAux.exists_fixed_subfield' (2 ^ f) K (frobPow K f) hK (frobPow_apply f) hq
    rw [← hk]
    exact Nat.card_le_card_of_injective (fun c => ⟨algebraMap k K c, hfix c⟩)
      (fun a b h => (algebraMap k K).injective (congrArg Subtype.val h))

theorem three_dvd_four_pow_sub_one (f : ℕ) : 3 ∣ (2 ^ f) ^ 2 - 1 := by
  have h : 4 ^ f ≡ 1 ^ f [MOD 3] := Nat.ModEq.pow f (by decide)
  rw [one_pow] at h
  have e : (2 ^ f) ^ 2 = 4 ^ f := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  rw [e]
  exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by norm_num))).1 h.symm

end Fields

section Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

set_option linter.unusedSectionVars false

variable {τ : Tag} {K : Type} [Field K]

@[expose] def OrbitProp (τ : Tag) : Prop :=
  ∀ B : Subgroup (WeylGroup τ), IsElemAbelian 3 B → ∃ γ : Fin τ.rank → ℤ, IsRoot τ γ ∧
    (MulAction.stabilizer (WeylGroup τ) γ).relIndex B ≤ 3

theorem exists_rootDiagUnit_of_mem_torusGroup {h : ModGL τ K} (hh : h ∈ torusGroup τ K) :
    ∃ a : Fin τ.rank → Kˣ, h = rootDiagUnit τ a := by
  have hle : torusGroup τ K ≤ (rootDiagUnitHom τ K).range := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨⟨i, t⟩, rfl⟩
    exact ⟨_, (torusElt_eq_rootDiagUnit i t).symm⟩
  obtain ⟨a, ha⟩ := hle hh
  exact ⟨a, ha.symm⟩

theorem canonicalRep_conj_pinnedX_two [CharP K 2] (w : WeylGroup τ) {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) (c : K) :
    canonicalRep (coxeterSystem τ) K w * pinnedX τ K γ c * (canonicalRep (coxeterSystem τ) K w)⁻¹ =
      pinnedX τ K (w • γ) c := by
  obtain ⟨ε, hε, hεc⟩ := exists_canonicalRep_mul_pinnedX_mul_inv K w hγ
  have hε1 : ε = 1 := by
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    have : (ε - 1) * (ε - 1) = 0 := by linear_combination hε + (1 - ε) * h2
    exact sub_eq_zero.1 (mul_self_eq_zero.1 this)
  rw [hεc, hε1, one_mul]

theorem exists_scalar_of_weyl_fix [CharP K 2] (g : ↥(monomialSubgroup τ K)) {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) (hw : weylQuotientHom τ K g • γ = γ) :
    ∃ l : Kˣ, ∀ c : K, (g : ModGL τ K) * pinnedX τ K γ c * (g : ModGL τ K)⁻¹ =
      pinnedX τ K γ ((l : K) * c) := by
  obtain ⟨w, k, hk, hg⟩ := monomialSubgroup_le_torusWeylCosets g.2
  have hw' : weylQuotientHom τ K g = w := weylQuotientHom_eq (by
    rw [hg]
    simpa using (mapsRootLines_of_mem_torusGroup hk).mul (mapsRootLines_canonicalRep (R := K) w))
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_of_mem_torusGroup hk
  refine ⟨rootChar a γ, fun c => ?_⟩
  rw [hg]
  have e : rootDiagUnit τ a * canonicalRep (coxeterSystem τ) K w * pinnedX τ K γ c *
      (rootDiagUnit τ a * canonicalRep (coxeterSystem τ) K w)⁻¹ =
      rootDiagUnit τ a * (canonicalRep (coxeterSystem τ) K w * pinnedX τ K γ c *
        (canonicalRep (coxeterSystem τ) K w)⁻¹) * (rootDiagUnit τ a)⁻¹ := by group
  rw [e, canonicalRep_conj_pinnedX_two w hγ c, ← hw', hw, rootDiagUnit_conj_pinnedX a hγ]

theorem core_centralizes [Finite K] [CharP K 2] (hO : OrbitProp τ) {P₁ : Subgroup (ModGL τ K)}
    (hP₁ : P₁ ≤ monomialSubgroup τ K) (hel : IsElemAbelian 3 P₁) :
    ∃ γ : Fin τ.rank → ℤ, IsRoot τ γ ∧ ∃ E₂ : Subgroup (ModGL τ K), E₂ ≤ P₁ ∧
      Nat.card P₁ ≤ 9 * Nat.card E₂ ∧ ∀ e ∈ E₂, e * pinnedX τ K γ 1 = pinnedX τ K γ 1 * e := by
  classical
  haveI : Finite (ModGL τ K) := finite_modGL
  let f : ↥P₁ →* WeylGroup τ := (weylQuotientHom τ K).comp (Subgroup.inclusion hP₁)
  have hf3 : ∀ b ∈ f.range, b ^ 3 = 1 := by
    rintro _ ⟨x, rfl⟩
    rw [← map_pow]
    have : x ^ 3 = 1 := Subtype.ext (by simpa using hel.2 x x.2)
    rw [this, map_one]
  have hfc : ∀ b ∈ f.range, ∀ b' ∈ f.range, b * b' = b' * b := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [← map_mul, ← map_mul, hel.1.is_comm.comm x y]
  have hrange : IsElemAbelian 3 f.range :=
    ⟨⟨⟨fun a b => Subtype.ext (hfc a a.2 b b.2)⟩⟩, hf3⟩
  obtain ⟨γ, hγ, hidx⟩ := hO f.range hrange
  set E₁' : Subgroup ↥P₁ := (MulAction.stabilizer (WeylGroup τ) γ).comap f with hE₁'
  have hE₁'idx : E₁'.index ≤ 3 := by
    rw [hE₁', Subgroup.index_comap]
    exact hidx
  set E₁ : Subgroup (ModGL τ K) := E₁'.map P₁.subtype with hE₁
  have hE₁P : E₁ ≤ P₁ := Subgroup.map_subtype_le _
  have hcard₁ : Nat.card P₁ ≤ 3 * Nat.card E₁ := by
    have h1 := Subgroup.card_mul_index E₁'
    have h2 : Nat.card E₁ = Nat.card E₁' := Subgroup.card_map_of_injective P₁.subtype_injective
    rw [h2, ← h1, mul_comm]
    exact Nat.mul_le_mul_right _ hE₁'idx
  have hscal : ∀ e ∈ E₁, ∃ l : K, l ^ 3 = 1 ∧ ∀ c : K,
      e * pinnedX τ K γ c * e⁻¹ = pinnedX τ K γ (l * c) := by
    rintro _ ⟨x, hx, rfl⟩
    have hfx : weylQuotientHom τ K ⟨(x : ModGL τ K), hP₁ x.2⟩ • γ = γ := hx
    obtain ⟨l, hl⟩ := exists_scalar_of_weyl_fix ⟨_, hP₁ x.2⟩ hγ hfx
    refine ⟨l, ?_, hl⟩
    have hx3 : (x : ModGL τ K) ^ 3 = 1 := hel.2 x x.2
    have key : ∀ n : ℕ, ∀ c : K, (x : ModGL τ K) ^ n * pinnedX τ K γ c * ((x : ModGL τ K) ^ n)⁻¹ =
        pinnedX τ K γ ((l : K) ^ n * c) := by
      intro n
      induction n with
      | zero => intro c; simp
      | succ n ih =>
        intro c
        have e : (x : ModGL τ K) ^ (n + 1) * pinnedX τ K γ c * ((x : ModGL τ K) ^ (n + 1))⁻¹ =
            (x : ModGL τ K) ^ n * ((x : ModGL τ K) * pinnedX τ K γ c * (x : ModGL τ K)⁻¹) *
              ((x : ModGL τ K) ^ n)⁻¹ := by group
        rw [e, hl c, ih, pow_succ, mul_assoc]
    have h3 := key 3 1
    rw [hx3, one_mul, inv_one, mul_one, mul_one] at h3
    have := pinnedX_injective τ K γ h3
    exact this.symm
  set x₀ := pinnedX τ K γ 1 with hx₀
  set T : Finset (ModGL τ K) := (Polynomial.nthRootsFinset 3 (1 : K)).image (pinnedX τ K γ) with hT
  have hT3 : T.card ≤ 3 := by
    refine Finset.card_image_le.trans ?_
    rw [Polynomial.nthRootsFinset_def]
    exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots 3 1)
  have hTmem : ∀ e ∈ E₁, e * x₀ * e⁻¹ ∈ T := by
    intro e he
    obtain ⟨l, hl3, hl⟩ := hscal e he
    rw [hx₀, hl 1, mul_one]
    exact Finset.mem_image.2 ⟨l, (Polynomial.mem_nthRootsFinset (by norm_num) 1).2 hl3, rfl⟩
  have hrel := relIndex_centralizer_le E₁ x₀ T hTmem
  set E₂ : Subgroup (ModGL τ K) := Subgroup.centralizer ({x₀} : Set (ModGL τ K)) ⊓ E₁ with hE₂
  refine ⟨γ, hγ, E₂, inf_le_right.trans hE₁P, ?_, ?_⟩
  · have h1 := Subgroup.relIndex_mul_card (Subgroup.centralizer ({x₀} : Set (ModGL τ K))) E₁
    have h2 : Nat.card E₁ ≤ 3 * Nat.card E₂ := by
      rw [← h1]
      exact Nat.mul_le_mul_right _ (hrel.trans hT3)
    omega
  · intro e he
    have hc := (Subgroup.mem_centralizer_iff.1 he.1) x₀ (Set.mem_singleton x₀)
    exact hc.symm

end Chevalley

section Orbit

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  CFSG.HardMathSupport.Lang.E6Descent.DiagWeyl

set_option linter.unusedSectionVars false

theorem orbitProp_E6 : OrbitProp Tag.E6 := by
  intro B hB
  have hB3 : ∀ b ∈ B, b ^ 3 = 1 := hB.2
  obtain ⟨v, hv⟩ := Gen2318E64InAux.exists_conj_le_Pw hB3
  set B₂ : Subgroup (WeylGroup Tag.E6) := B.map (MulAut.conj v⁻¹).toMonoidHom with hB₂
  have hB₂P : B₂ ≤ Pw := by
    rintro _ ⟨b, hb, rfl⟩
    have := hv b hb
    simpa [MulAut.conj_apply] using this
  obtain ⟨β, hβ, T, hT, hBT⟩ := Gen2318E64InAux.exists_root_orbit_subset hB₂P (hB.map _)
  set γ : Fin Tag.E6.rank → ℤ := v • β with hγdef
  have hγ : IsRoot Tag.E6 γ := IsRoot.smul hβ v
  have hT' : (T.image (fun t => v • t)).card ≤ 8 := Finset.card_image_le.trans hT
  have hBT' : ∀ b ∈ B, b • γ ∈ T.image (fun t => v • t) := by
    intro b hb
    have h1 : v⁻¹ * b * v ∈ B₂ := ⟨b, hb, by simp [MulAut.conj_apply]⟩
    refine Finset.mem_image.2 ⟨(v⁻¹ * b * v) • β, hBT _ h1, ?_⟩
    rw [hγdef, smul_smul, smul_smul]
    congr 1
    group
  exact ⟨γ, hγ, Gen2318E64InAux.relIndex_stabilizer_le_three hB3 hT' hBT'⟩

theorem toVec_ofFn' {r : ℕ} (v : Fin r → ℤ) : toVec r (List.ofFn v) = v := by
  funext i
  simp [toVec, vget]

theorem ofFn_toVec' {r : ℕ} {l : List ℤ} (hl : l.length = r) : List.ofFn (toVec r l) = l := by
  refine List.ext_getElem (by simp [hl]) fun n h1 h2 => ?_
  simp [toVec, vget, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

theorem orbitProp_of_not_dvd {τ : Tag} (h9 : ¬ 9 ∣ τ.rootCount) : OrbitProp τ := by
  classical
  intro B hB
  set X : Finset (Fin τ.rank → ℤ) := (τ.artifactRoots.map (toVec τ.rank)).toFinset with hX
  have hmem : ∀ v, v ∈ X ↔ IsRoot τ v := by
    intro v
    rw [hX, List.mem_toFinset, List.mem_map, isRoot_iff_mem_artifactRoots]
    constructor
    · rintro ⟨l, hl, rfl⟩
      rwa [ofFn_toVec' (length_of_mem_artifactRoots hl)]
    · intro hv
      exact ⟨_, hv, toVec_ofFn' v⟩
  have hnd : (τ.artifactRoots.map (toVec τ.rank)).Nodup := by
    refine List.Nodup.map_on ?_ (nodup_artifactRoots τ)
    intro l hl l' hl' h
    rw [← ofFn_toVec' (length_of_mem_artifactRoots hl), ← ofFn_toVec' (length_of_mem_artifactRoots hl'),
      h]
  have hcard : X.card = τ.rootCount := by
    rw [hX, List.toFinset_card_of_nodup hnd, List.length_map, Tag.length_artifactRoots]
  obtain ⟨γ, hγX, hγ⟩ := exists_relIndex_stabilizer_le_three hB.isPGroup X
    (fun b _ x hx => (hmem _).2 (IsRoot.smul ((hmem x).1 hx) b)) (by rw [hcard]; exact h9)
  exact ⟨γ, (hmem γ).1 hγX, hγ⟩

theorem orbitProp_E8 : OrbitProp Tag.E8 := orbitProp_of_not_dvd (by decide)

theorem orbitProp_F4 : OrbitProp Tag.F4 := orbitProp_of_not_dvd (by decide)

end Orbit

section WeylE7

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 CFSG.RankThree.Lattice
  CFSG.HardMathSupport.Lang.E6Descent.DiagWeyl

set_option linter.unusedSectionVars false

@[expose] def wordA7 : List (Fin Tag.E7.rank) := [3, 0, 2, 1, 3, 4, 5, 0, 2, 1, 3, 4, 1, 3, 2, 0]

@[expose] def wordB7 : List (Fin Tag.E7.rank) := [4, 5, 4, 3]

@[expose] def genA7 : List (List ℤ) := [[-1, 0, 0, 1, -1, 0, 1], [-2, 0, 1, 0, 0, 0, 1], [-2, 0, 0, 1, -1, 1, 1], [-3, 0, 0, 1, 0, 0, 2], [-2, 0, 0, 1, 0, 0, 1], [-1, 1, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1]]

@[expose] def genB7 : List (List ℤ) := [[1, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0], [0, 1, 1, -1, 1, 0, 0], [0, 1, 1, -1, 1, -1, 1], [0, 1, 1, -1, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1]]

@[expose] def genA7inv : List (List ℤ) := [[0, 0, 0, -1, 1, 0, 1], [0, 0, 0, -1, 1, 1, 0], [0, 1, 0, -2, 2, 0, 1], [0, 0, 0, -2, 3, 0, 1], [-1, 0, 0, -1, 2, 0, 1], [-1, 0, 1, -1, 1, 0, 1], [0, 0, 0, 0, 0, 0, 1]]

@[expose] def genB7inv : List (List ℤ) := [[1, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0], [0, 1, 1, 0, 0, -1, 1], [0, 0, 0, 1, 0, -1, 1], [0, 0, 0, 1, -1, 0, 1], [0, 0, 0, 0, 0, 0, 1]]

@[expose] def gA7 : WeylGroup Tag.E7 := (coxeterSystem Tag.E7).wordProd wordA7

@[expose] def gB7 : WeylGroup Tag.E7 := (coxeterSystem Tag.E7).wordProd wordB7

theorem weylMatrix_gA7 : weylMatrix gA7 = toMat Tag.E7.rank genA7 := by
  rw [gA7, I102UniqAux.weylMatrix_wordProd]
  exact I102UniqAux.wordMat_eq_toMat' Tag.E7 _ (by decide +kernel)

theorem weylMatrix_gB7 : weylMatrix gB7 = toMat Tag.E7.rank genB7 := by
  rw [gB7, I102UniqAux.weylMatrix_wordProd]
  exact I102UniqAux.wordMat_eq_toMat' Tag.E7 _ (by decide +kernel)

theorem toMat_lmul7 (A B : List (List ℤ)) :
    toMat Tag.E7.rank (lmul 7 A B) = toMat Tag.E7.rank A * toMat Tag.E7.rank B :=
  toMat_lmul 7 A B

theorem toMat_lid7 : toMat Tag.E7.rank (lid 7) = 1 := toMat_lid 7

theorem weylMatrix_gA7_inv : weylMatrix gA7⁻¹ = toMat Tag.E7.rank genA7inv :=
  eq_of_mul_eq_one (by rw [← weylMatrix_mul, inv_mul_cancel, weylMatrix_one])
    (by
      rw [weylMatrix_gA7, ← toMat_lmul7, ← toMat_lid7]
      exact congrArg (toMat Tag.E7.rank) (by decide +kernel))

theorem weylMatrix_gB7_inv : weylMatrix gB7⁻¹ = toMat Tag.E7.rank genB7inv :=
  eq_of_mul_eq_one (by rw [← weylMatrix_mul, inv_mul_cancel, weylMatrix_one])
    (by
      rw [weylMatrix_gB7, ← toMat_lmul7, ← toMat_lid7]
      exact congrArg (toMat Tag.E7.rank) (by decide +kernel))

@[expose] def dEval7 (ω : List Bool) : List (List ℤ) :=
  ω.foldl (fun M b => lmul 7 M (if b then genB7 else genA7)) (lid 7)

@[expose] def dMats7 : List (List (List ℤ)) := dWords.map dEval7

theorem dMats7_length : dMats7.length = 81 := by decide +kernel

theorem dMats7_closed : ∀ M ∈ dMats7, lmul 7 M genA7 ∈ dMats7 ∧ lmul 7 M genA7inv ∈ dMats7 ∧
    lmul 7 M genB7 ∈ dMats7 ∧ lmul 7 M genB7inv ∈ dMats7 := by decide +kernel

theorem dMats7_inj : ∀ M ∈ dMats7, ∀ M' ∈ dMats7,
    (∀ i j : Fin 7, lget M i j = lget M' i j) → M = M' := by decide +kernel

theorem dMats7_nodup : dMats7.Nodup := by decide +kernel

theorem lid_mem_dMats7 : lid 7 ∈ dMats7 := by decide +kernel

@[expose] def Pw7 : Subgroup (WeylGroup Tag.E7) := Subgroup.closure {gA7, gB7}

@[expose] def gSel7 (b : Bool) : WeylGroup Tag.E7 := if b then gB7 else gA7

@[expose] def gProd7 (ω : List Bool) : WeylGroup Tag.E7 := ω.foldl (fun g b => g * gSel7 b) 1

theorem gSel7_mem (b : Bool) : gSel7 b ∈ Pw7 := by
  cases b
  · exact Subgroup.subset_closure (Or.inl rfl)
  · exact Subgroup.subset_closure (Or.inr rfl)

theorem foldl_gSel7_mem (ω : List Bool) :
    ∀ g0 ∈ Pw7, ω.foldl (fun g b => g * gSel7 b) g0 ∈ Pw7 := by
  induction ω with
  | nil => exact fun g0 h => h
  | cons b ω ih => exact fun g0 h => ih _ (mul_mem h (gSel7_mem b))

theorem gProd7_mem (ω : List Bool) : gProd7 ω ∈ Pw7 := foldl_gSel7_mem ω 1 (one_mem _)

theorem weylMatrix_foldl7 (ω : List Bool) : ∀ (g0 : WeylGroup Tag.E7) (L0 : List (List ℤ)),
    weylMatrix g0 = toMat Tag.E7.rank L0 →
    weylMatrix (ω.foldl (fun g b => g * gSel7 b) g0) =
      toMat Tag.E7.rank (ω.foldl (fun M b => lmul 7 M (if b then genB7 else genA7)) L0) := by
  induction ω with
  | nil => exact fun _ _ h => h
  | cons b ω ih =>
    intro g0 L0 h
    refine ih _ _ ?_
    rw [weylMatrix_mul, h]
    show _ = toMat Tag.E7.rank (lmul 7 L0 (if b then genB7 else genA7))
    rw [toMat_lmul7]
    congr 1
    cases b
    · exact weylMatrix_gA7
    · exact weylMatrix_gB7

theorem weylMatrix_gProd7 (ω : List Bool) :
    weylMatrix (gProd7 ω) = toMat Tag.E7.rank (dEval7 ω) :=
  weylMatrix_foldl7 ω 1 (lid 7) (by rw [weylMatrix_one, toMat_lid7])

theorem exists_mem_dMats7_of_mem_Pw7 {w : WeylGroup Tag.E7} (hw : w ∈ Pw7) :
    ∃ M ∈ dMats7, weylMatrix w = toMat Tag.E7.rank M := by
  induction hw using Subgroup.closure_induction_right with
  | one => exact ⟨lid 7, lid_mem_dMats7, by rw [weylMatrix_one, toMat_lid7]⟩
  | mul_right x hx y hy ih =>
    obtain ⟨M, hM, hxM⟩ := ih
    obtain ⟨h1, -, h3, -⟩ := dMats7_closed M hM
    rcases hy with rfl | hy
    · exact ⟨_, h1, by rw [weylMatrix_mul, hxM, weylMatrix_gA7, toMat_lmul7]⟩
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact ⟨_, h3, by rw [weylMatrix_mul, hxM, weylMatrix_gB7, toMat_lmul7]⟩
  | mul_inv_cancel x hx y hy ih =>
    obtain ⟨M, hM, hxM⟩ := ih
    obtain ⟨-, h2, -, h4⟩ := dMats7_closed M hM
    rcases hy with rfl | hy
    · exact ⟨_, h2, by rw [weylMatrix_mul, hxM, weylMatrix_gA7_inv, toMat_lmul7]⟩
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact ⟨_, h4, by rw [weylMatrix_mul, hxM, weylMatrix_gB7_inv, toMat_lmul7]⟩

theorem mem_Pw7_iff {w : WeylGroup Tag.E7} : w ∈ Pw7 ↔ ∃ ω ∈ dWords, w = gProd7 ω := by
  constructor
  · intro hw
    obtain ⟨M, hM, hwM⟩ := exists_mem_dMats7_of_mem_Pw7 hw
    obtain ⟨ω, hω, rfl⟩ := List.mem_map.1 (show M ∈ dWords.map dEval7 from hM)
    exact ⟨ω, hω, weylMatrix_injective (by rw [hwM, weylMatrix_gProd7])⟩
  · rintro ⟨ω, -, rfl⟩
    exact gProd7_mem ω

theorem gProd7_nodup : (dWords.map gProd7).Nodup := by
  classical
  refine List.Nodup.of_map weylMatrix ?_
  have : (dWords.map gProd7).map weylMatrix = dMats7.map (toMat Tag.E7.rank) := by
    rw [List.map_map, dMats7, List.map_map]
    exact List.map_congr_left fun ω _ => weylMatrix_gProd7 ω
  rw [this]
  refine List.Nodup.map_on ?_ dMats7_nodup
  intro M hM M' hM' h
  exact dMats7_inj M hM M' hM' fun i j => congrFun (congrFun h i) j

theorem card_Pw7 : Nat.card Pw7 = 81 := by
  classical
  have h1 : Nat.card Pw7 = (dWords.map gProd7).toFinset.card := by
    rw [← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun w => by
      rw [List.mem_toFinset, List.mem_map, mem_Pw7_iff]
      exact ⟨fun ⟨ω, h1, h2⟩ => ⟨ω, h1, h2.symm⟩, fun ⟨ω, h1, h2⟩ => ⟨ω, h1, h2.symm⟩⟩)
  rw [h1, List.toFinset_card_of_nodup gProd7_nodup, List.length_map]
  have := dMats7_length
  rwa [dMats7, List.length_map] at this

theorem exists_conj_le_Pw7 {B : Subgroup (WeylGroup Tag.E7)} (hB3 : ∀ b ∈ B, b ^ 3 = 1) :
    ∃ v : WeylGroup Tag.E7, ∀ b ∈ B, v⁻¹ * b * v ∈ Pw7 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP : IsPGroup 3 Pw7 := IsPGroup.of_card (n := 4) (by rw [card_Pw7]; norm_num)
  have hidx : ¬ 3 ∣ Pw7.index := by
    have h := Subgroup.card_mul_index Pw7
    rw [card_Pw7, CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.card_weylGroup_E7'] at h
    have : Pw7.index = 35840 := by omega
    rw [this]
    norm_num
  let P0 : Sylow 3 (WeylGroup Tag.E7) := hP.toSylow hidx
  have hBp : IsPGroup 3 B := fun g => ⟨1, Subtype.ext (by simpa using hB3 g g.2)⟩
  obtain ⟨Q, hQ⟩ := hBp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (WeylGroup Tag.E7) P0 Q
  refine ⟨g, fun b hb => ?_⟩
  have hbQ : b ∈ (Q : Subgroup (WeylGroup Tag.E7)) := hQ hb
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hbQ
  have : (MulAut.conj g)⁻¹ • b = g⁻¹ * b * g := by
    rw [MulAut.smul_def]
    simp
  rw [this] at hbQ
  exact hbQ

@[expose] def beta0L7 : List ℤ := [1, 0, 0, 0, 0, 0, 0]

@[expose] def orb0L7 : List (List ℤ) :=
  [[1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 1, 1, 0, 0], [-1, 0, -1, -1, -1, 0, 0]]

@[expose] def roots70 : List (List ℤ) := Tag.E7.artifactRoots.filter fun β => vget β 6 = 0

@[expose] def fixRoots7 (M : List (List ℤ)) : List (List ℤ) :=
  roots70.filter fun β => lmulVec 7 M β = β

theorem orbit_check7 : ∀ M ∈ dMats7,
    (∀ i j : Fin 7, lget (lmul 7 M (lmul 7 M M)) i j = lget (lid 7) i j) →
    lmulVec 7 M beta0L7 ∉ orb0L7 → fixRoots7 M ≠ [] ∧ (fixRoots7 M).length ≤ 8 := by
  decide +kernel

theorem lastRow7 : ∀ M ∈ dMats7, ∀ j : Fin 7, lget M 6 j = if (j : ℕ) = 6 then 1 else 0 := by
  decide +kernel

theorem beta0L7_mem : beta0L7 ∈ roots70 := by decide +kernel

theorem lmulVec_ofFn7 (M : List (List ℤ)) (v : Fin Tag.E7.rank → ℤ) :
    lmulVec 7 M (List.ofFn v) = List.ofFn ((toMat Tag.E7.rank M).mulVec v) := by
  have h := toVec_lmulVec 7 M (List.ofFn v)
  have hlen : (lmulVec 7 M (List.ofFn v)).length = Tag.E7.rank := by
    simp [lmulVec, vofFn]
    rfl
  have h' : toVec Tag.E7.rank (lmulVec 7 M (List.ofFn v)) = (toMat Tag.E7.rank M).mulVec v := by
    have h'' : toVec Tag.E7.rank (lmulVec 7 M (List.ofFn v)) =
        (toMat Tag.E7.rank M).mulVec (toVec Tag.E7.rank (List.ofFn v)) := h
    rw [h'', toVec_ofFn']
  calc lmulVec 7 M (List.ofFn v) = List.ofFn (toVec Tag.E7.rank (lmulVec 7 M (List.ofFn v))) :=
        (ofFn_toVec' hlen).symm
    _ = List.ofFn ((toMat Tag.E7.rank M).mulVec v) := by rw [h']

theorem smul_last7 {u : WeylGroup Tag.E7} (hu : u ∈ Pw7) (v : Fin Tag.E7.rank → ℤ) :
    (u • v) 6 = v 6 := by
  obtain ⟨M, hM, huM⟩ := exists_mem_dMats7_of_mem_Pw7 hu
  rw [← weylMatrix_mulVec, huM]
  have h := lastRow7 M hM
  have hrow : ∀ j : Fin Tag.E7.rank, toMat Tag.E7.rank M 6 j = if j = 6 then 1 else 0 := by
    intro j
    have hj := h j
    have e1 : toMat Tag.E7.rank M 6 j = lget M 6 j := rfl
    rw [e1, hj]
    by_cases hj6 : j = 6
    · subst hj6
      rfl
    · have : (j : ℕ) ≠ 6 := fun h' => hj6 (Fin.ext h')
      rw [if_neg this, if_neg hj6]
  simp only [Matrix.mulVec, dotProduct, hrow, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

theorem exists_root_orbit_subset7 {B : Subgroup (WeylGroup Tag.E7)} (hBP : B ≤ Pw7)
    (hB : IsElemAbelian 3 B) :
    ∃ β : Fin Tag.E7.rank → ℤ, IsRoot Tag.E7 β ∧
      ∃ T : Finset (Fin Tag.E7.rank → ℤ), T.card ≤ 8 ∧ ∀ b ∈ B, b • β ∈ T := by
  classical
  set β₀ : Fin Tag.E7.rank → ℤ := toVec Tag.E7.rank beta0L7 with hβ₀
  set T₀ : Finset (Fin Tag.E7.rank → ℤ) := (orb0L7.map (toVec Tag.E7.rank)).toFinset with hT₀
  have hroot : ∀ l ∈ roots70, IsRoot Tag.E7 (toVec Tag.E7.rank l) ∧ l.length = Tag.E7.rank := by
    intro l hl
    have hl' := (List.mem_filter.1 hl).1
    have hlen := length_of_mem_artifactRoots hl'
    exact ⟨isRoot_iff_mem_artifactRoots.2 (by rw [ofFn_toVec' hlen]; exact hl'), hlen⟩
  by_cases hA : ∀ b ∈ B, b • β₀ ∈ T₀
  · refine ⟨β₀, (hroot _ beta0L7_mem).1, T₀, ?_, hA⟩
    refine (List.toFinset_card_le _).trans ?_
    simp [orb0L7]
  · push Not at hA
    obtain ⟨b, hb, hbT⟩ := hA
    obtain ⟨M, hM, hbM⟩ := exists_mem_dMats7_of_mem_Pw7 (hBP hb)
    have hcube : ∀ i j : Fin 7, lget (lmul 7 M (lmul 7 M M)) i j = lget (lid 7) i j := by
      intro i j
      have h := congrArg weylMatrix (hB.2 b hb)
      rw [weylMatrix_pow, weylMatrix_one, hbM] at h
      have h' : toMat Tag.E7.rank (lmul 7 M (lmul 7 M M)) = toMat Tag.E7.rank (lid 7) := by
        rw [toMat_lid7, toMat_lmul7, toMat_lmul7, ← pow_three]
        exact h
      exact congrFun (congrFun h' i) j
    have hsmul : ∀ v, b • v = (toMat Tag.E7.rank M).mulVec v := fun v => by
      rw [← weylMatrix_mulVec, hbM]
    have hnot : lmulVec 7 M beta0L7 ∉ orb0L7 := by
      intro hmem
      apply hbT
      have h1 : b • β₀ = toVec Tag.E7.rank (lmulVec 7 M beta0L7) := by
        rw [hsmul]
        exact (toVec_lmulVec 7 M beta0L7).symm
      rw [h1]
      exact List.mem_toFinset.2 (List.mem_map_of_mem hmem)
    obtain ⟨hne, hlen⟩ := orbit_check7 M hM hcube hnot
    obtain ⟨βl, hβl⟩ := List.exists_mem_of_ne_nil _ hne
    have hβl' := List.mem_filter.1 hβl
    obtain ⟨hβroot, hlenβ⟩ := hroot βl hβl'.1
    set β : Fin Tag.E7.rank → ℤ := toVec Tag.E7.rank βl with hβdef
    have hβofFn : List.ofFn β = βl := ofFn_toVec' hlenβ
    have hbβ : b • β = β := by
      rw [hsmul]
      apply List.ofFn_injective
      rw [← lmulVec_ofFn7, hβofFn]
      exact of_decide_eq_true hβl'.2
    have hβ6 : β 6 = 0 := by
      have h : vget βl 6 = 0 := of_decide_eq_true (List.mem_filter.1 hβl'.1).2
      exact h
    refine ⟨β, hβroot, ((fixRoots7 M).map (toVec Tag.E7.rank)).toFinset, ?_, ?_⟩
    · refine (List.toFinset_card_le _).trans ?_
      rw [List.length_map]
      exact hlen
    · intro u hu
      have hub : u * b = b * u := congrArg Subtype.val (hB.1.is_comm.comm ⟨u, hu⟩ ⟨b, hb⟩)
      have hγroot : IsRoot Tag.E7 (u • β) := IsRoot.smul hβroot u
      have hbγ : b • (u • β) = u • β := by
        rw [smul_smul, ← hub, mul_smul, hbβ]
      have hγ6 : (u • β) 6 = 0 := by rw [smul_last7 (hBP hu), hβ6]
      have hmem : List.ofFn (u • β) ∈ fixRoots7 M := by
        refine List.mem_filter.2 ⟨List.mem_filter.2 ⟨isRoot_iff_mem_artifactRoots.1 hγroot, ?_⟩, ?_⟩
        · refine decide_eq_true ?_
          exact (vget_vofFn (u • β) 6).trans hγ6
        · refine decide_eq_true ?_
          rw [lmulVec_ofFn7, ← hsmul, hbγ]
      exact List.mem_toFinset.2 (List.mem_map.2 ⟨_, hmem, toVec_ofFn' _⟩)

theorem orbitProp_E7 : OrbitProp Tag.E7 := by
  intro B hB
  have hB3 : ∀ b ∈ B, b ^ 3 = 1 := hB.2
  obtain ⟨v, hv⟩ := exists_conj_le_Pw7 hB3
  set B₂ : Subgroup (WeylGroup Tag.E7) := B.map (MulAut.conj v⁻¹).toMonoidHom with hB₂
  have hB₂P : B₂ ≤ Pw7 := by
    rintro _ ⟨b, hb, rfl⟩
    have := hv b hb
    simpa [MulAut.conj_apply] using this
  obtain ⟨β, hβ, T, hT, hBT⟩ := exists_root_orbit_subset7 hB₂P (hB.map _)
  set γ : Fin Tag.E7.rank → ℤ := v • β with hγdef
  have hγ : IsRoot Tag.E7 γ := IsRoot.smul hβ v
  have hT' : (T.image (fun t => v • t)).card ≤ 8 := Finset.card_image_le.trans hT
  have hBT' : ∀ b ∈ B, b • γ ∈ T.image (fun t => v • t) := by
    intro b hb
    have h1 : v⁻¹ * b * v ∈ B₂ := ⟨b, hb, by simp [MulAut.conj_apply]⟩
    refine Finset.mem_image.2 ⟨(v⁻¹ * b * v) • β, hBT _ h1, ?_⟩
    rw [hγdef, smul_smul, smul_smul]
    congr 1
    group
  refine ⟨γ, hγ, ?_⟩
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hBp : IsPGroup 3 B := fun g => ⟨1, Subtype.ext (by simpa using hB3 g g.2)⟩
  obtain ⟨k, hk⟩ := hBp.exists_card_eq
  have hdvd : (MulAction.stabilizer (WeylGroup Tag.E7) γ).relIndex B ∣ 3 ^ k :=
    hk ▸ Subgroup.relIndex_dvd_card _ _
  obtain ⟨j, -, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  have hle8 : (MulAction.stabilizer (WeylGroup Tag.E7) γ).relIndex B ≤ 8 := by
    have h1 : (MulAction.stabilizer (WeylGroup Tag.E7) γ).subgroupOf B =
        MulAction.stabilizer ↥B γ := by
      ext x
      simp [Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff]
    rw [Subgroup.relIndex, h1, MulAction.index_stabilizer]
    calc (MulAction.orbit ↥B γ).ncard ≤
          ((T.image (fun t => v • t) : Finset _) : Set (Fin Tag.E7.rank → ℤ)).ncard := by
          refine Set.ncard_le_ncard ?_ (Finset.finite_toSet _)
          rintro _ ⟨⟨b, hb⟩, rfl⟩
          exact hBT' b hb
      _ = (T.image (fun t => v • t)).card := Set.ncard_coe_finset _
      _ ≤ 8 := hT'
  rw [hjeq] at hle8 ⊢
  have hj : j ≤ 1 := by
    by_contra h
    push Not at h
    have : 3 ^ 2 ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) h
    omega
  interval_cases j <;> norm_num

end WeylE7

section Sigma

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

set_option linter.unusedSectionVars false

variable {τ : Tag} {K : Type} [Field K]

noncomputable abbrev sigmaStar (σ : K ≃+* K) : ModGL τ K →* ModGL τ K := Units.map (entrywiseHom σ.toRingHom)

theorem sigmaStar_mem_adjointGroup (σ : K ≃+* K) {g : ModGL τ K} (hg : g ∈ adjointGroup τ K) :
    sigmaStar σ g ∈ adjointGroup τ K := by
  have hle : adjointGroup τ K ≤ (adjointGroup τ K).comap (sigmaStar σ) := by
    refine (Subgroup.closure_le _).2 ?_
    rintro g ⟨i, c, h | h⟩
    · apply Subgroup.subset_closure
      refine ⟨i, σ c, Or.inl ?_⟩
      change entrywise σ.toRingHom (g : Module.End K (RootModule τ K)) = _
      rw [h]
      exact entrywise_xOp σ.toRingHom i c
    · apply Subgroup.subset_closure
      refine ⟨i, σ c, Or.inr ?_⟩
      change entrywise σ.toRingHom (g : Module.End K (RootModule τ K)) = _
      rw [h]
      exact entrywise_yOp σ.toRingHom i c
  exact hle hg

theorem sigmaStar_sigmaStar (σ : K ≃+* K) (hσ : ∀ c, σ (σ c) = c) (g : ModGL τ K) :
    sigmaStar σ (sigmaStar σ g) = g := by
  apply Units.ext
  change entrywise σ.toRingHom (entrywise σ.toRingHom (g : Module.End K (RootModule τ K))) = g
  rw [entrywise_entrywise]
  have : σ.toRingHom.comp σ.toRingHom = RingHom.id K := RingHom.ext hσ
  rw [this, entrywise_id]

theorem pinnedX_one_sq [CharP K 2] (γ : Fin τ.rank → ℤ) : pinnedX τ K γ 1 ^ 2 = 1 := by
  have h2 : (1 : K) + 1 = 0 := by
    rw [← two_mul, mul_one]
    exact CharTwo.two_eq_zero
  rw [sq, ← pinnedX_add, h2, pinnedX_zero]

theorem pinnedX_one_ne_one (γ : Fin τ.rank → ℤ) : pinnedX τ K γ 1 ≠ 1 := by
  intro h
  rw [← pinnedX_zero τ K γ] at h
  exact one_ne_zero (pinnedX_injective τ K γ h)

theorem odd_index_fixedFieldImage [Finite K] [CharP K 2] (σ : K ≃+* K) :
    Odd ((fixedFieldImage τ σ).subgroupOf (entrywiseFixedGroup τ σ)).index := by
  classical
  obtain ⟨-, h⟩ := fixedFieldImage_index_dvd_card (τ := τ) σ
  haveI : CharP ↥(fixSubfield σ) 2 := CharP.subring K 2 (fixSubfield σ).toSubring
  haveI : Fintype ↥(fixSubfield σ) := Fintype.ofFinite _
  obtain ⟨n, -, hn⟩ := FiniteField.card ↥(fixSubfield σ) 2
  rw [Nat.card_eq_fintype_card, hn] at h
  have hodd : Odd ((2 ^ (n : ℕ) - 1) ^ τ.rank) := by
    refine Odd.pow ?_
    have h1 : 1 ≤ 2 ^ (n : ℕ) := Nat.one_le_two_pow
    have h2 : Even (2 ^ (n : ℕ)) := (Nat.even_pow.2 ⟨even_two, n.ne_zero⟩)
    obtain ⟨m, hm⟩ := h2
    exact ⟨m - 1, by omega⟩
  exact Odd.of_dvd_nat hodd h

theorem sigma_trick [Finite K] [CharP K 2] (hO : OrbitProp τ)
    (h3N : ¬ 3 ∣ (monomialSubgroup τ K).relIndex (adjointGroup τ K)) (σ : K ≃+* K)
    (hσ : ∀ c, σ (σ c) = c) {P : Subgroup (ModGL τ ↥(fixSubfield σ))}
    (hPC : P ≤ adjointGroup τ ↥(fixSubfield σ)) (hel : IsElemAbelian 3 P) :
    ∃ E : Subgroup (ModGL τ ↥(fixSubfield σ)), E ≤ P ∧ Nat.card P ≤ 9 * Nat.card E ∧
      ∃ t ∈ adjointGroup τ ↥(fixSubfield σ), t ≠ 1 ∧ t ^ 2 = 1 ∧ ∀ e ∈ E, e * t = t * e := by
  classical
  haveI : Finite (ModGL τ K) := finite_modGL
  set φ : ModGL τ ↥(fixSubfield σ) →* ModGL τ K := baseChangeGL (fixSubfield σ).subtype with hφ
  have hφinj : Function.Injective φ := baseChangeGL_injective _
  set P' : Subgroup (ModGL τ K) := P.map φ with hP'
  have hP'J : P' ≤ fixedFieldImage τ σ := Subgroup.map_mono hPC
  have hP'Γ : P' ≤ entrywiseFixedGroup τ σ := hP'J.trans fixedFieldImage_le
  have hP'C : P' ≤ adjointGroup τ K := fun x hx => (hP'Γ hx).1
  have hP'fix : ∀ x ∈ P', sigmaStar σ x = x := fun x hx => (hP'Γ hx).2
  have hP'el : IsElemAbelian 3 P' := hel.map φ
  obtain ⟨u, huC, hu⟩ := Gen2318E64InAux.exists_conj_le_of_not_dvd hP'C hP'el.isPGroup h3N
  set P₁ : Subgroup (ModGL τ K) := P'.map (MulAut.conj u⁻¹).toMonoidHom with hP₁
  have hP₁N : P₁ ≤ monomialSubgroup τ K := by
    rintro _ ⟨x, hx, rfl⟩
    have := hu x hx
    simpa [MulAut.conj_apply] using this
  have hP₁el : IsElemAbelian 3 P₁ := hP'el.map _
  obtain ⟨γ, hγ, E₂, hE₂P₁, hcard₂, hE₂c⟩ := core_centralizes hO hP₁N hP₁el
  set t₁ : ModGL τ K := u * pinnedX τ K γ 1 * u⁻¹ with ht₁
  set E₂' : Subgroup (ModGL τ K) := E₂.map (MulAut.conj u).toMonoidHom with hE₂'
  have hE₂'P' : E₂' ≤ P' := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := hE₂P₁ hx
    have e : (MulAut.conj u).toMonoidHom x = y := by
      rw [← hyx]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [e]
    exact hy
  have hE₂'c : ∀ e ∈ E₂', e * t₁ = t₁ * e := by
    rintro _ ⟨x, hx, rfl⟩
    have h := hE₂c x hx
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ht₁]
    calc u * x * u⁻¹ * (u * pinnedX τ K γ 1 * u⁻¹) = u * (x * pinnedX τ K γ 1) * u⁻¹ := by group
      _ = u * (pinnedX τ K γ 1 * x) * u⁻¹ := by rw [h]
      _ = u * pinnedX τ K γ 1 * u⁻¹ * (u * x * u⁻¹) := by group
  set ς : ModGL τ K →* ModGL τ K := sigmaStar σ with hς
  have hςς : ∀ g, ς (ς g) = g := sigmaStar_sigmaStar σ hσ
  have hE₂'cς : ∀ e ∈ E₂', e * ς t₁ = ς t₁ * e := by
    intro e he
    have hfix : ς e = e := hP'fix e (hE₂'P' he)
    calc e * ς t₁ = ς e * ς t₁ := by rw [hfix]
      _ = ς (e * t₁) := (map_mul ς e t₁).symm
      _ = ς (t₁ * e) := by rw [hE₂'c e he]
      _ = ς t₁ * ς e := map_mul ς t₁ e
      _ = ς t₁ * e := by rw [hfix]
  set Z : Subgroup (ModGL τ K) := Subgroup.closure {t₁, ς t₁} with hZ
  have ht₁Z : t₁ ∈ Z := Subgroup.subset_closure (Set.mem_insert _ _)
  have hςt₁Z : ς t₁ ∈ Z := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hZς : ∀ z ∈ Z, ς z ∈ Z := by
    intro z hz
    have hle : Z ≤ Z.comap ς := by
      refine (Subgroup.closure_le _).2 ?_
      rintro x (rfl | hx)
      · exact hςt₁Z
      · rw [Set.mem_singleton_iff] at hx
        subst hx
        show ς (ς t₁) ∈ Z
        rw [hςς]
        exact ht₁Z
    exact hle hz
  let f : ↥Z →* ↥Z := (ς.comp Z.subtype).codRestrict Z (fun z => hZς z z.2)
  have hf : ∀ z, f (f z) = z := fun z => Subtype.ext (hςς z)
  have ht₁sq : t₁ ^ 2 = 1 := by
    rw [ht₁, conj_pow, pinnedX_one_sq, mul_one, mul_inv_cancel]
  have ht₁ne : t₁ ≠ 1 := by
    intro h
    apply pinnedX_one_ne_one (τ := τ) (K := K) γ
    calc pinnedX τ K γ 1 = u⁻¹ * t₁ * u := by rw [ht₁]; group
      _ = 1 := by rw [h]; group
  have hZeven : Even (Nat.card Z) := by
    have hord : orderOf (⟨t₁, ht₁Z⟩ : ↥Z) = 2 := by
      refine orderOf_eq_prime ?_ ?_
      · exact Subtype.ext (by simpa using ht₁sq)
      · intro h
        exact ht₁ne (congrArg Subtype.val h)
    exact even_iff_two_dvd.2 (hord ▸ orderOf_dvd_natCard _)
  obtain ⟨t', ht'1, ht'2, ht'f⟩ := exists_fixed_involution f hf hZeven
  have hZC : Z ≤ adjointGroup τ K := by
    have ht₁C : t₁ ∈ adjointGroup τ K := by
      have hx : pinnedX τ K γ 1 ∈ adjointGroup τ K := pinnedX_mem_adjointGroup γ 1
      exact mul_mem (mul_mem huC hx) (inv_mem huC)
    refine (Subgroup.closure_le _).2 ?_
    rintro x (rfl | hx)
    · exact ht₁C
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact sigmaStar_mem_adjointGroup σ ht₁C
  have htΓ : (t' : ModGL τ K) ∈ entrywiseFixedGroup τ σ :=
    ⟨hZC t'.2, congrArg Subtype.val ht'f⟩
  have htJ : (t' : ModGL τ K) ∈ fixedFieldImage τ σ := by
    have hsq : (⟨(t' : ModGL τ K), htΓ⟩ : ↥(entrywiseFixedGroup τ σ)) ^ 2 = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val ht'2)
    have h := mem_of_sq_eq_one_of_odd_index (odd_index_fixedFieldImage (τ := τ) σ) hsq
    exact Subgroup.mem_subgroupOf.1 h
  obtain ⟨t₀, ht₀C, ht₀⟩ := htJ
  set E : Subgroup (ModGL τ ↥(fixSubfield σ)) := E₂'.comap φ with hE
  have hEP : E ≤ P := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hE₂'P' hx
    rw [← hφinj hyx]
    exact hy
  have hEmap : E.map φ = E₂' := by
    refine Subgroup.map_comap_eq_self ?_
    intro x hx
    obtain ⟨y, -, hyx⟩ := hE₂'P' hx
    exact ⟨y, hyx⟩
  have hcardE : Nat.card E = Nat.card E₂' := by
    rw [← hEmap, Subgroup.card_map_of_injective hφinj]
  have hcardE₂' : Nat.card E₂' = Nat.card E₂ :=
    Subgroup.card_map_of_injective (MulAut.conj u).injective
  have hcardP₁ : Nat.card P₁ = Nat.card P := by
    rw [hP₁, Subgroup.card_map_of_injective (MulAut.conj u⁻¹).injective, hP',
      Subgroup.card_map_of_injective hφinj]
  refine ⟨E, hEP, ?_, t₀, ht₀C, ?_, ?_, ?_⟩
  · rw [hcardE, hcardE₂', ← hcardP₁]
    exact hcard₂
  · rintro rfl
    apply ht'1
    apply Subtype.ext
    rw [← ht₀, map_one]
    rfl
  · apply hφinj
    rw [map_pow, ht₀, map_one]
    simpa using congrArg Subtype.val ht'2
  · intro e he
    apply hφinj
    rw [map_mul, map_mul, ht₀]
    have hZc : ∀ z ∈ Z, φ e * z = z * φ e := by
      intro z hz
      have hle : Z ≤ Subgroup.centralizer ({φ e} : Set (ModGL τ K)) := by
        refine (Subgroup.closure_le _).2 ?_
        rintro x (rfl | hx)
        · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
          exact (hE₂'c (φ e) he).symm
        · rw [Set.mem_singleton_iff] at hx
          subst hx
          rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
          exact (hE₂'cς (φ e) he).symm
      exact ((Subgroup.mem_centralizer_singleton_iff.1 (hle hz))).symm
    exact hZc _ t'.2

theorem invCent_fix [Finite K] [CharP K 2] (hO : OrbitProp τ)
    (h3N : ¬ 3 ∣ (monomialSubgroup τ K).relIndex (adjointGroup τ K)) (σ : K ≃+* K)
    (hσ : ∀ c, σ (σ c) = c) : InvCent ↥(adjointGroup τ ↥(fixSubfield σ)) := by
  intro P hP
  obtain ⟨E, hEP, hcard, t, htC, ht1, ht2, hEt⟩ :=
    sigma_trick hO h3N σ hσ (Subgroup.map_subtype_le P)
      (IsElemAbelian.map hP (adjointGroup τ ↥(fixSubfield σ)).subtype)
  have hEC : E ≤ adjointGroup τ ↥(fixSubfield σ) := hEP.trans (Subgroup.map_subtype_le _)
  refine ⟨E.subgroupOf (adjointGroup τ ↥(fixSubfield σ)), ?_, ?_, ⟨t, htC⟩, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, hyx⟩ := hEP (Subgroup.mem_subgroupOf.1 hx)
    rw [← Subtype.ext hyx]
    exact hy
  · rw [show Nat.card (E.subgroupOf (adjointGroup τ ↥(fixSubfield σ))) = Nat.card E from
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEC).toEquiv]
    rw [← Subgroup.card_map_of_injective (f := (adjointGroup τ ↥(fixSubfield σ)).subtype)
      (adjointGroup τ ↥(fixSubfield σ)).subtype_injective]
    exact hcard
  · intro h
    exact ht1 (congrArg Subtype.val h)
  · exact Subtype.ext (by simpa using ht2)
  · intro e he
    exact Subtype.ext (hEt e (Subgroup.mem_subgroupOf.1 he))

theorem not_three_dvd_of_sylow [Finite K]
    (h : ∃ Q : Sylow 3 ↥(adjointGroup τ K), (Q : Subgroup ↥(adjointGroup τ K)) ≤ monomialSub τ K) :
    ¬ 3 ∣ (monomialSubgroup τ K).relIndex (adjointGroup τ K) := by
  obtain ⟨Q, hQ⟩ := h
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (ModGL τ K) := finite_modGL
  intro h3
  have hdvd : (monomialSub τ K).index ∣ (Q : Subgroup ↥(adjointGroup τ K)).index :=
    Subgroup.index_dvd_of_le hQ
  exact Q.not_dvd_index (h3.trans hdvd)

theorem exists_invCent (hO : OrbitProp τ)
    (h3N : ∀ (K : Type) [Field K] [Finite K], 3 ∣ Nat.card K - 1 →
      ¬ 3 ∣ (monomialSubgroup τ K).relIndex (adjointGroup τ K)) {f : ℕ} (hf : 1 ≤ f) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = 2 ^ f ∧
      InvCent ↥(adjointGroup τ k) := by
  let K := GaloisField 2 (2 * f)
  have hK : Nat.card K = (2 ^ f) ^ 2 := by
    rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]
  have h3 : 3 ∣ Nat.card K - 1 := by
    rw [hK]
    exact three_dvd_four_pow_sub_one f
  exact ⟨↥(fixSubfield (frobPow K f)), inferInstance, inferInstance,
    card_fixSubfield_frobPow hf hK,
    invCent_fix hO (h3N K h3) (frobPow K f) (frobPow_frobPow hK)⟩

end Sigma

section Monomial

open Matrix

variable {N : ℕ} {F : Type} [Field F]

@[expose] def monoMat (d : Fin N → Fˣ) (σ : Equiv.Perm (Fin N)) : Matrix (Fin N) (Fin N) F :=
  Matrix.of fun i j => if i = σ j then (d j : F) else 0

theorem monoMat_apply (d : Fin N → Fˣ) (σ : Equiv.Perm (Fin N)) (i j : Fin N) :
    monoMat d σ i j = if i = σ j then (d j : F) else 0 :=
  rfl

theorem monoMat_mul (d e : Fin N → Fˣ) (σ τ : Equiv.Perm (Fin N)) :
    monoMat d σ * monoMat e τ = monoMat (fun k => d (τ k) * e k) (σ * τ) := by
  ext i k
  rw [Matrix.mul_apply, Finset.sum_eq_single (τ k)]
  · rw [monoMat_apply, monoMat_apply, monoMat_apply, if_pos rfl]
    by_cases h : i = σ (τ k)
    · rw [if_pos h, if_pos (show i = (σ * τ) k from h), Units.val_mul]
    · rw [if_neg h, if_neg (show ¬ i = (σ * τ) k from h), zero_mul]
  · intro j _ hj
    rw [monoMat_apply (F := F) e τ j k, if_neg hj, mul_zero]
  · simp

theorem monoMat_one : monoMat (1 : Fin N → Fˣ) (1 : Equiv.Perm (Fin N)) = (1 : Matrix (Fin N) (Fin N) F) := by
  ext i j
  rw [monoMat_apply, Matrix.one_apply]
  by_cases h : i = j
  · subst h
    simp
  · rw [if_neg (show ¬ i = (1 : Equiv.Perm (Fin N)) j from h), if_neg h]

@[expose] def monoInv (d : Fin N → Fˣ) (σ : Equiv.Perm (Fin N)) : Fin N → Fˣ :=
  fun k => (d (σ⁻¹ k))⁻¹

theorem monoMat_mul_inv (d : Fin N → Fˣ) (σ : Equiv.Perm (Fin N)) :
    monoMat d σ * monoMat (monoInv d σ) σ⁻¹ = (1 : Matrix (Fin N) (Fin N) F) := by
  rw [monoMat_mul, mul_inv_cancel, ← monoMat_one]
  congr 1
  funext k
  simp [monoInv]

theorem monoMat_inv_mul (d : Fin N → Fˣ) (σ : Equiv.Perm (Fin N)) :
    monoMat (monoInv d σ) σ⁻¹ * monoMat d σ = (1 : Matrix (Fin N) (Fin N) F) := by
  rw [monoMat_mul, inv_mul_cancel, ← monoMat_one]
  congr 1
  funext k
  simp [monoInv]

@[expose] def mono (d : Fin N → Fˣ) (σ : Equiv.Perm (Fin N)) : GL (Fin N) F :=
  ⟨monoMat d σ, monoMat (monoInv d σ) σ⁻¹, monoMat_mul_inv d σ, monoMat_inv_mul d σ⟩

theorem coe_mono (d : Fin N → Fˣ) (σ : Equiv.Perm (Fin N)) :
    ((mono d σ : GL (Fin N) F) : Matrix (Fin N) (Fin N) F) = monoMat d σ :=
  rfl

theorem mono_mul (d e : Fin N → Fˣ) (σ τ : Equiv.Perm (Fin N)) :
    (mono d σ : GL (Fin N) F) * mono e τ = mono (fun k => d (τ k) * e k) (σ * τ) :=
  Units.ext (monoMat_mul d e σ τ)

theorem mono_one : (mono (1 : Fin N → Fˣ) (1 : Equiv.Perm (Fin N)) : GL (Fin N) F) = 1 :=
  Units.ext monoMat_one

theorem mono_inv (d : Fin N → Fˣ) (σ : Equiv.Perm (Fin N)) :
    (mono d σ : GL (Fin N) F)⁻¹ = mono (monoInv d σ) σ⁻¹ :=
  Units.ext rfl

theorem mono_injective {d e : Fin N → Fˣ} {σ τ : Equiv.Perm (Fin N)}
    (h : (mono d σ : GL (Fin N) F) = mono e τ) : d = e ∧ σ = τ := by
  have hm : monoMat d σ = (monoMat e τ : Matrix (Fin N) (Fin N) F) := congrArg Units.val h
  have hst : ∀ j, σ j = τ j := by
    intro j
    have hj := congrFun (congrFun hm (σ j)) j
    rw [monoMat_apply, monoMat_apply, if_pos rfl] at hj
    by_contra hne
    rw [if_neg hne] at hj
    exact (d j).ne_zero hj
  have hστ : σ = τ := Equiv.ext hst
  refine ⟨funext fun j => ?_, hστ⟩
  have hj := congrFun (congrFun hm (σ j)) j
  rw [monoMat_apply, monoMat_apply, if_pos rfl, if_pos (hst j)] at hj
  exact Units.ext hj

variable (N F) in
@[expose] def monoSub : Subgroup (GL (Fin N) F) where
  carrier := {g | ∃ p : (Fin N → Fˣ) × Equiv.Perm (Fin N), g = mono p.1 p.2}
  mul_mem' := by
    rintro _ _ ⟨⟨d, σ⟩, rfl⟩ ⟨⟨e, τ⟩, rfl⟩
    exact ⟨⟨_, _⟩, mono_mul d e σ τ⟩
  one_mem' := ⟨⟨1, 1⟩, mono_one.symm⟩
  inv_mem' := by
    rintro _ ⟨⟨d, σ⟩, rfl⟩
    exact ⟨⟨_, _⟩, mono_inv d σ⟩

theorem mono_mem (d : Fin N → Fˣ) (σ : Equiv.Perm (Fin N)) : mono d σ ∈ monoSub N F :=
  ⟨⟨d, σ⟩, rfl⟩

@[expose] noncomputable def monoPerm : ↥(monoSub N F) →* Equiv.Perm (Fin N) where
  toFun g := g.2.choose.2
  map_one' := by
    have h := (one_mem (monoSub N F)).choose_spec
    have h' : (mono (1 : Fin N → Fˣ) 1 : GL (Fin N) F) = mono _ _ := mono_one.trans h
    exact (mono_injective h').2.symm
  map_mul' g h := by
    have hg := g.2.choose_spec
    have hh := h.2.choose_spec
    have hgh := (g * h).2.choose_spec
    have e : (mono _ _ : GL (Fin N) F) = mono _ _ :=
      hgh.symm.trans ((congrArg₂ (· * ·) hg hh).trans (mono_mul _ _ _ _))
    exact (mono_injective e).2

theorem eq_mono_monoPerm (g : ↥(monoSub N F)) :
    ∃ d : Fin N → Fˣ, (g : GL (Fin N) F) = mono d (monoPerm g) :=
  ⟨g.2.choose.1, g.2.choose_spec⟩

theorem monoMat_conj_apply (d : Fin N → Fˣ) (σ : Equiv.Perm (Fin N)) (A : Matrix (Fin N) (Fin N) F)
    (i k : Fin N) :
    (monoMat d σ * A * monoMat (monoInv d σ) σ⁻¹) i k =
      (d (σ⁻¹ i) : F) * A (σ⁻¹ i) (σ⁻¹ k) * ((d (σ⁻¹ k))⁻¹ : Fˣ) := by
  have h1 : ∀ l, (monoMat d σ * A) i l = (d (σ⁻¹ i) : F) * A (σ⁻¹ i) l := by
    intro l
    rw [Matrix.mul_apply, Finset.sum_eq_single (σ⁻¹ i)]
    · rw [monoMat_apply, if_pos (by simp)]
    · intro j _ hj
      rw [monoMat_apply, if_neg]
      · simp
      · intro h
        apply hj
        rw [h]
        simp
    · simp
  rw [Matrix.mul_apply, Finset.sum_eq_single (σ⁻¹ k)]
  · rw [h1, monoMat_apply, if_pos rfl]
    simp [monoInv]
  · intro l _ hl
    rw [monoMat_apply (F := F) (monoInv d σ) σ⁻¹ l k, if_neg hl, mul_zero]
  · simp

theorem card_monoSub [Finite F] :
    Nat.card (monoSub N F) = Nat.card (Equiv.Perm (Fin N)) * Nat.card (Fin N → Fˣ) := by
  classical
  have hbij : Function.Bijective (fun p : (Fin N → Fˣ) × Equiv.Perm (Fin N) =>
      (⟨mono p.1 p.2, mono_mem p.1 p.2⟩ : ↥(monoSub N F))) := by
    refine ⟨fun p q h => ?_, fun g => ?_⟩
    · have h' := mono_injective (congrArg Subtype.val h)
      exact Prod.ext h'.1 h'.2
    · obtain ⟨⟨d, σ⟩, hg⟩ := g.2
      exact ⟨⟨d, σ⟩, Subtype.ext hg.symm⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_prod, mul_comm]

theorem factorization_three_GL_four (N : ℕ) :
    (∏ i : Fin N, (4 ^ N - 4 ^ (i : ℕ))).factorization 3 = N + (N.factorial).factorization 3 := by
  have hp : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  rw [Fin.prod_univ_eq_prod_range (fun i => 4 ^ N - 4 ^ i) N]
  have hne : ∀ i ∈ Finset.range N, 4 ^ N - 4 ^ i ≠ 0 := by
    intro i hi
    have h1 := Finset.mem_range.1 hi
    have : 4 ^ i < 4 ^ N := Nat.pow_lt_pow_right (by norm_num) h1
    omega
  rw [Nat.factorization_prod hne, Finset.sum_apply']
  have key : ∀ i ∈ Finset.range N,
      (4 ^ N - 4 ^ i).factorization 3 = 1 + (N - i).factorization 3 := by
    intro i hi
    have hiN := Finset.mem_range.1 hi
    have e : 4 ^ N - 4 ^ i = 4 ^ i * (4 ^ (N - i) - 1) := by
      rw [Nat.mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' hiN.le]
    have hpos : 4 ^ (N - i) - 1 ≠ 0 := by
      have : 1 < 4 ^ (N - i) := Nat.one_lt_pow (by omega) (by norm_num)
      omega
    rw [e, Nat.factorization_mul (by positivity) hpos, Finsupp.add_apply]
    have h4 : (4 ^ i).factorization 3 = 0 := by
      rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 4), mul_zero]
    have hlte := padicValNat.pow_sub_pow (p := 3) (by decide : Odd 3) (x := 4) (y := 1)
      (by norm_num) (by norm_num) (by norm_num) (n := N - i) (by omega)
    rw [one_pow] at hlte
    rw [h4, zero_add, Nat.factorization_def _ hp, Nat.factorization_def _ hp, hlte]
    have h3 : padicValNat 3 (4 - 1) = 1 := by norm_num
    rw [h3]
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    smul_eq_mul, mul_one]
  congr 1
  rw [← Finset.prod_range_add_one_eq_factorial, Nat.factorization_prod (by simp),
    Finset.sum_apply', ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun i hi => ?_
  have := Finset.mem_range.1 hi
  congr 2
  omega

theorem not_three_dvd_index_monoSub {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4) (N : ℕ) :
    ¬ 3 ∣ (monoSub N F).index := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  have hp : Nat.Prime 3 := Nat.prime_three
  have hGL : Nat.card (GL (Fin N) F) = ∏ i : Fin N, (4 ^ N - 4 ^ (i : ℕ)) := by
    rw [Matrix.card_GL_field, ← Nat.card_eq_fintype_card, hF]
  have hM : Nat.card (monoSub N F) = N.factorial * 3 ^ N := by
    rw [card_monoSub, Nat.card_perm, Nat.card_fin, Nat.card_fun, Nat.card_units, hF, Nat.card_fin]
  have h1 := Subgroup.card_mul_index (monoSub N F)
  have hidx : (monoSub N F).index ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h1
    exact (Nat.card_pos (α := GL (Fin N) F)).ne' h1.symm
  have hMne : Nat.card (monoSub N F) ≠ 0 := Nat.card_pos.ne'
  have hf : (Nat.card (monoSub N F) * (monoSub N F).index).factorization 3 =
      (Nat.card (GL (Fin N) F)).factorization 3 := by rw [h1]
  rw [Nat.factorization_mul hMne hidx, Finsupp.add_apply, hGL, factorization_three_GL_four, hM,
    Nat.factorization_mul (Nat.factorial_ne_zero N) (by positivity), Finsupp.add_apply,
    Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, Nat.Prime.factorization_self hp,
    mul_one] at hf
  have h0 : (monoSub N F).index.factorization 3 = 0 := by omega
  intro h3
  have := (hp.dvd_iff_one_le_factorization hidx).1 h3
  omega

@[expose] def conjSLFun (g : GL (Fin N) F) (x : Matrix.SpecialLinearGroup (Fin N) F) :
    Matrix.SpecialLinearGroup (Fin N) F :=
  ⟨(g : Matrix (Fin N) (Fin N) F) * (x : Matrix (Fin N) (Fin N) F) *
      ((g⁻¹ : GL (Fin N) F) : Matrix (Fin N) (Fin N) F), by
    rw [Matrix.det_mul, Matrix.det_mul, x.2, mul_one, ← Matrix.det_mul, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, Matrix.det_one]⟩

theorem coe_conjSLFun (g : GL (Fin N) F) (x : Matrix.SpecialLinearGroup (Fin N) F) :
    ((conjSLFun g x : Matrix.SpecialLinearGroup (Fin N) F) : Matrix (Fin N) (Fin N) F) =
      (g : Matrix (Fin N) (Fin N) F) * (x : Matrix (Fin N) (Fin N) F) *
        ((g⁻¹ : GL (Fin N) F) : Matrix (Fin N) (Fin N) F) :=
  rfl

@[expose] def conjSL (g : GL (Fin N) F) : MulAut (Matrix.SpecialLinearGroup (Fin N) F) where
  toFun := conjSLFun g
  invFun := conjSLFun g⁻¹
  left_inv x := Subtype.ext (by
    simp only [coe_conjSLFun, inv_inv]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mul, Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.mul_one])
  right_inv x := Subtype.ext (by
    simp only [coe_conjSLFun, inv_inv]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mul, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.mul_one])
  map_mul' x y := Subtype.ext (by
    simp only [coe_conjSLFun, Matrix.SpecialLinearGroup.coe_mul]
    have e : ((g⁻¹ : GL (Fin N) F) : Matrix (Fin N) (Fin N) F) * (g : Matrix (Fin N) (Fin N) F) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    calc (g : Matrix (Fin N) (Fin N) F) * ((x : Matrix (Fin N) (Fin N) F) * y) *
          ((g⁻¹ : GL (Fin N) F) : Matrix (Fin N) (Fin N) F) =
        (g : Matrix (Fin N) (Fin N) F) * (x : Matrix (Fin N) (Fin N) F) *
          (((g⁻¹ : GL (Fin N) F) : Matrix (Fin N) (Fin N) F) * (g : Matrix (Fin N) (Fin N) F)) *
          (y : Matrix (Fin N) (Fin N) F) * ((g⁻¹ : GL (Fin N) F) : Matrix (Fin N) (Fin N) F) := by
          rw [e, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc])

theorem coe_conjSL_apply (g : GL (Fin N) F) (x : Matrix.SpecialLinearGroup (Fin N) F) :
    ((conjSL g x : Matrix.SpecialLinearGroup (Fin N) F) : Matrix (Fin N) (Fin N) F) =
      (g : Matrix (Fin N) (Fin N) F) * (x : Matrix (Fin N) (Fin N) F) *
        ((g⁻¹ : GL (Fin N) F) : Matrix (Fin N) (Fin N) F) :=
  rfl

theorem conjSL_mul (g h : GL (Fin N) F) : conjSL (g * h) = conjSL g * conjSL h := by
  refine MulEquiv.ext fun x => Subtype.ext ?_
  rw [MulAut.mul_apply, coe_conjSL_apply, coe_conjSL_apply, coe_conjSL_apply, _root_.mul_inv_rev,
    Units.val_mul, Units.val_mul]
  simp only [Matrix.mul_assoc]

theorem conjSL_one : conjSL (1 : GL (Fin N) F) = 1 := by
  refine MulEquiv.ext fun x => Subtype.ext ?_
  rw [coe_conjSL_apply, inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_one]
  rfl

theorem map_center_mulAut {G : Type*} [Group G] (φ : MulAut G) :
    (Subgroup.center G).map φ.toMonoidHom = Subgroup.center G := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : y ∈ Subgroup.center G := hy
    rw [Subgroup.mem_center_iff] at hy'
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨v, rfl⟩ := φ.surjective w
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, hy' v]
  · intro hz
    refine ⟨φ.symm z, ?_, by simp⟩
    show φ.symm z ∈ Subgroup.center G
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro w
    apply φ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hz (φ w)]

@[expose] noncomputable def conjPSL (g : GL (Fin N) F) :
    MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin N) F) :=
  QuotientGroup.congr _ _ (conjSL g) (map_center_mulAut (conjSL g))

theorem conjPSL_mk (g : GL (Fin N) F) (x : Matrix.SpecialLinearGroup (Fin N) F) :
    conjPSL g (x : Matrix.ProjectiveSpecialLinearGroup (Fin N) F) =
      ((conjSL g x : Matrix.SpecialLinearGroup (Fin N) F) :
        Matrix.ProjectiveSpecialLinearGroup (Fin N) F) :=
  rfl

@[expose] noncomputable def conjPSLHom :
    GL (Fin N) F →* MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin N) F) where
  toFun := conjPSL
  map_one' := by
    refine MulEquiv.ext fun y => ?_
    induction y using QuotientGroup.induction_on with | H x => ?_
    rw [conjPSL_mk, conjSL_one]
    rfl
  map_mul' g h := by
    refine MulEquiv.ext fun y => ?_
    induction y using QuotientGroup.induction_on with | H x => ?_
    rw [MulAut.mul_apply, conjPSL_mk, conjPSL_mk, conjPSL_mk, conjSL_mul]
    rfl

@[expose] def SuppOn (O : Finset (Fin N)) (A : Matrix (Fin N) (Fin N) F) : Prop :=
  ∀ i j, A i j ≠ 0 → i ∈ O ∧ j ∉ O

theorem SuppOn.mul_eq_zero {O : Finset (Fin N)} {A B : Matrix (Fin N) (Fin N) F} (hA : SuppOn O A)
    (hB : SuppOn O B) : A * B = 0 := by
  ext i k
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases h1 : A i j = 0
  · rw [h1, zero_mul]
  · by_cases h2 : B j k = 0
    · rw [h2, mul_zero]
    · exact absurd (hB j k h2).1 (hA i j h1).2

theorem SuppOn.add {O : Finset (Fin N)} {A B : Matrix (Fin N) (Fin N) F} (hA : SuppOn O A)
    (hB : SuppOn O B) : SuppOn O (A + B) := by
  intro i j h
  rw [Matrix.add_apply] at h
  by_cases h1 : A i j = 0
  · rw [h1, zero_add] at h
    exact hB i j h
  · exact hA i j h1

theorem SuppOn.neg {O : Finset (Fin N)} {A : Matrix (Fin N) (Fin N) F} (hA : SuppOn O A) :
    SuppOn O (-A) := by
  intro i j h
  rw [Matrix.neg_apply, neg_ne_zero] at h
  exact hA i j h

variable (F) in
@[expose] def uSub (O : Finset (Fin N)) : Subgroup (Matrix.SpecialLinearGroup (Fin N) F) where
  carrier := {x | SuppOn O ((x : Matrix (Fin N) (Fin N) F) - 1)}
  mul_mem' := by
    intro x y hx hy
    have hx' : SuppOn O ((x : Matrix (Fin N) (Fin N) F) - 1) := hx
    have hy' : SuppOn O ((y : Matrix (Fin N) (Fin N) F) - 1) := hy
    show SuppOn O ((x : Matrix (Fin N) (Fin N) F) * (y : Matrix (Fin N) (Fin N) F) - 1)
    have h0 := hx'.mul_eq_zero hy'
    have e : (x : Matrix (Fin N) (Fin N) F) * (y : Matrix (Fin N) (Fin N) F) - 1 =
        ((x : Matrix (Fin N) (Fin N) F) - 1) + ((y : Matrix (Fin N) (Fin N) F) - 1) +
          ((x : Matrix (Fin N) (Fin N) F) - 1) * ((y : Matrix (Fin N) (Fin N) F) - 1) := by
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.one_mul]
      abel
    rw [e, h0, add_zero]
    exact hx'.add hy'
  one_mem' := by
    show SuppOn O ((1 : Matrix (Fin N) (Fin N) F) - 1)
    intro i j h
    rw [sub_self, Matrix.zero_apply] at h
    exact absurd rfl h
  inv_mem' := by
    intro x hx
    have hx' : SuppOn O ((x : Matrix (Fin N) (Fin N) F) - 1) := hx
    show SuppOn O (((x⁻¹ : Matrix.SpecialLinearGroup (Fin N) F) : Matrix (Fin N) (Fin N) F) - 1)
    have h0 := hx'.mul_eq_zero hx'
    have hinv : ((x⁻¹ : Matrix.SpecialLinearGroup (Fin N) F) : Matrix (Fin N) (Fin N) F) =
        1 - ((x : Matrix (Fin N) (Fin N) F) - 1) := by
      have h1 : (x : Matrix (Fin N) (Fin N) F) * (1 - ((x : Matrix (Fin N) (Fin N) F) - 1)) = 1 := by
        have e : (x : Matrix (Fin N) (Fin N) F) * (1 - ((x : Matrix (Fin N) (Fin N) F) - 1)) =
            1 - ((x : Matrix (Fin N) (Fin N) F) - 1) * ((x : Matrix (Fin N) (Fin N) F) - 1) := by
          simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.one_mul]
          abel
        rw [e, h0, sub_zero]
      have h2 : ((x⁻¹ : Matrix.SpecialLinearGroup (Fin N) F) : Matrix (Fin N) (Fin N) F) *
          (x : Matrix (Fin N) (Fin N) F) = 1 := by
        rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
      calc ((x⁻¹ : Matrix.SpecialLinearGroup (Fin N) F) : Matrix (Fin N) (Fin N) F) =
          ((x⁻¹ : Matrix.SpecialLinearGroup (Fin N) F) : Matrix (Fin N) (Fin N) F) *
            ((x : Matrix (Fin N) (Fin N) F) * (1 - ((x : Matrix (Fin N) (Fin N) F) - 1))) := by
            rw [h1, Matrix.mul_one]
        _ = _ := by rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
    rw [hinv, sub_sub_cancel_left]
    exact hx'.neg

theorem mem_uSub {O : Finset (Fin N)} {x : Matrix.SpecialLinearGroup (Fin N) F} :
    x ∈ uSub F O ↔ SuppOn O ((x : Matrix (Fin N) (Fin N) F) - 1) :=
  Iff.rfl

theorem sq_eq_one_of_mem_uSub [CharP F 2] {O : Finset (Fin N)} {x : Matrix.SpecialLinearGroup (Fin N) F}
    (hx : x ∈ uSub F O) : x ^ 2 = 1 := by
  apply Subtype.ext
  have h0 := (mem_uSub.1 hx).mul_eq_zero (mem_uSub.1 hx)
  rw [sq, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  have h2 : (2 : Matrix (Fin N) (Fin N) F) = 0 := by
    rw [show (2 : Matrix (Fin N) (Fin N) F) = Matrix.scalar (Fin N) (2 : F) by
      rw [Matrix.scalar_apply]; ext i j; simp [Matrix.ofNat_apply, Matrix.diagonal_apply]]
    rw [CharTwo.two_eq_zero, map_zero]
  have e : (x : Matrix (Fin N) (Fin N) F) * x =
      1 + 2 * ((x : Matrix (Fin N) (Fin N) F) - 1) +
        ((x : Matrix (Fin N) (Fin N) F) - 1) * ((x : Matrix (Fin N) (Fin N) F) - 1) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.one_mul, two_mul]
    abel
  rw [e, h0, h2, zero_mul, add_zero, add_zero]

theorem isPGroup_uSub [CharP F 2] (O : Finset (Fin N)) : IsPGroup 2 ↥(uSub F O) := by
  intro x
  refine ⟨1, Subtype.ext ?_⟩
  rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
  exact sq_eq_one_of_mem_uSub x.2

theorem transvection_mem_uSub {O : Finset (Fin N)} {i j : Fin N} (hi : i ∈ O) (hj : j ∉ O) :
    (⟨Matrix.transvection i j 1, Matrix.det_transvection_of_ne i j (by rintro rfl; exact hj hi) 1⟩ :
      Matrix.SpecialLinearGroup (Fin N) F) ∈ uSub F O := by
  refine mem_uSub.2 ?_
  intro a b h
  change (Matrix.transvection i j (1 : F) - 1) a b ≠ 0 at h
  rw [Matrix.transvection, add_sub_cancel_left, Matrix.single_apply] at h
  split_ifs at h with hab
  · obtain ⟨rfl, rfl⟩ := hab
    exact ⟨hi, hj⟩
  · exact absurd rfl h

theorem conjSL_mem_uSub {O : Finset (Fin N)} (d : Fin N → Fˣ) (σ : Equiv.Perm (Fin N))
    (hσ : ∀ i, σ i ∈ O ↔ i ∈ O) {x : Matrix.SpecialLinearGroup (Fin N) F} (hx : x ∈ uSub F O) :
    conjSL (mono d σ) x ∈ uSub F O := by
  rw [mem_uSub, coe_conjSL_apply, coe_mono, mono_inv, coe_mono]
  have e : monoMat d σ * (x : Matrix (Fin N) (Fin N) F) * monoMat (monoInv d σ) σ⁻¹ - 1 =
      monoMat d σ * ((x : Matrix (Fin N) (Fin N) F) - 1) * monoMat (monoInv d σ) σ⁻¹ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, monoMat_mul_inv]
  rw [e]
  intro a b h
  rw [monoMat_conj_apply] at h
  have h' : ((x : Matrix (Fin N) (Fin N) F) - 1) (σ⁻¹ a) (σ⁻¹ b) ≠ 0 := by
    intro h0
    rw [h0, mul_zero, zero_mul] at h
    exact h rfl
  obtain ⟨ha, hb⟩ := (mem_uSub.1 hx) _ _ h'
  refine ⟨?_, ?_⟩
  · have := (hσ (σ⁻¹ a)).2 ha
    simpa using this
  · intro hbO
    apply hb
    have : σ (σ⁻¹ b) ∈ O := by simpa using hbO
    exact (hσ _).1 this

theorem monoPerm_eq_one_of_conjPSL {N : ℕ} (hN : 2 ≤ N) (z : ↥(monoSub N F))
    (hz : conjPSLHom (z : GL (Fin N) F) = 1) : monoPerm z = 1 := by
  classical
  obtain ⟨d, hd⟩ := eq_mono_monoPerm z
  set σ := monoPerm z with hσ
  refine Equiv.ext fun i => ?_
  obtain ⟨j, hji⟩ : ∃ j : Fin N, j ≠ i := by
    by_cases h0 : i = ⟨0, by omega⟩
    · refine ⟨⟨1, by omega⟩, ?_⟩
      rw [h0]
      intro h
      exact absurd (congrArg Fin.val h) (by simp)
    · exact ⟨⟨0, by omega⟩, fun h => h0 h.symm⟩
  have hdet : (Matrix.transvection i j (1 : F)).det = 1 :=
    Matrix.det_transvection_of_ne i j (Ne.symm hji) 1
  let T : Matrix.SpecialLinearGroup (Fin N) F := ⟨Matrix.transvection i j 1, hdet⟩
  have hTm : (T : Matrix (Fin N) (Fin N) F) = Matrix.transvection i j 1 := rfl
  have hmk : ((conjSL (z : GL (Fin N) F) T : Matrix.SpecialLinearGroup (Fin N) F) :
      Matrix.ProjectiveSpecialLinearGroup (Fin N) F) =
      (T : Matrix.ProjectiveSpecialLinearGroup (Fin N) F) :=
    congrArg (fun φ : MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin N) F) =>
      φ (T : Matrix.ProjectiveSpecialLinearGroup (Fin N) F)) hz
  obtain ⟨r, hrN, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 (QuotientGroup.eq.1 hmk)
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [zero_pow (by simp; omega)] at hrN
    exact zero_ne_one hrN
  have hX : Matrix.transvection i j (1 : F) =
      monoMat d σ * Matrix.transvection i j 1 * monoMat (monoInv d σ) σ⁻¹ *
        Matrix.scalar (Fin N) r := by
    have h1 : ((conjSL (z : GL (Fin N) F) T : Matrix.SpecialLinearGroup (Fin N) F) :
        Matrix (Fin N) (Fin N) F) * Matrix.scalar (Fin N) r = (T : Matrix (Fin N) (Fin N) F) := by
      rw [hr, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel_left]
    rw [coe_conjSL_apply, hd, coe_mono, mono_inv, coe_mono, hTm] at h1
    exact h1.symm
  have hentry := congrFun (congrFun hX (σ i)) (σ j)
  rw [Matrix.scalar_apply, Matrix.mul_diagonal, monoMat_conj_apply] at hentry
  have e1 : σ⁻¹ (σ i) = i := by simp
  have e2 : σ⁻¹ (σ j) = j := by simp
  rw [e1, e2] at hentry
  have hTij : Matrix.transvection i j (1 : F) i j = 1 := by
    simp [Matrix.transvection, Matrix.single_apply, Matrix.one_apply, Ne.symm hji]
  rw [hTij, mul_one] at hentry
  have hne : Matrix.transvection i j (1 : F) (σ i) (σ j) ≠ 0 := by
    rw [hentry]
    exact mul_ne_zero (mul_ne_zero (d i).ne_zero (Units.ne_zero _)) hr0
  have hsij : σ i ≠ σ j := fun h => hji (σ.injective h).symm
  rw [Matrix.transvection, Matrix.add_apply, Matrix.one_apply_ne hsij, zero_add,
    Matrix.single_apply] at hne
  by_contra h
  exact hne (if_neg (fun h' => h h'.1.symm))

theorem perm_inv_apply_self {α : Type*} (σ : Equiv.Perm α) (x : α) : σ⁻¹ (σ x) = x := by simp

theorem exists_sub_card_pow' {G : Type*} [Group G] [Finite G] {p m k : ℕ} (hp : p.Prime)
    {A : Subgroup G} (hA : Nat.card A = p ^ m) (hk : k ≤ m) :
    ∃ E : Subgroup G, E ≤ A ∧ Nat.card E = p ^ k := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨D, hD⟩ := Sylow.exists_subgroup_card_pow_prime p
    (show p ^ k ∣ Nat.card A by rw [hA]; exact pow_dvd_pow p hk)
  refine ⟨D.map A.subtype, Subgroup.map_subtype_le D, ?_⟩
  rw [Subgroup.card_map_of_injective A.subtype_injective]
  exact hD

theorem exists_intransitive {N : ℕ} (hN : 2 ≤ N) (B : Subgroup (Equiv.Perm (Fin N)))
    (hB : IsElemAbelian 3 B) :
    ∃ B₀ : Subgroup (Equiv.Perm (Fin N)), B₀ ≤ B ∧ B₀.relIndex B ≤ 3 ∧
      ∃ O : Finset (Fin N), O.Nonempty ∧ O ≠ Finset.univ ∧ ∀ b ∈ B₀, ∀ i, b i ∈ O ↔ i ∈ O := by
  classical
  haveI : NeZero N := ⟨by omega⟩
  let orb (C : Subgroup (Equiv.Perm (Fin N))) : Finset (Fin N) :=
    Finset.univ.filter fun k => ∃ c ∈ C, c 0 = k
  have mem_orb : ∀ C k, k ∈ orb C ↔ ∃ c ∈ C, c 0 = k := by
    intro C k
    simp [orb]
  have orb_inv : ∀ C : Subgroup (Equiv.Perm (Fin N)), ∀ b ∈ C, ∀ i, b i ∈ orb C ↔ i ∈ orb C := by
    intro C b hb i
    rw [mem_orb, mem_orb]
    constructor
    · rintro ⟨c, hc, hci⟩
      refine ⟨b⁻¹ * c, mul_mem (inv_mem hb) hc, ?_⟩
      rw [Equiv.Perm.mul_apply, hci, perm_inv_apply_self]
    · rintro ⟨c, hc, rfl⟩
      exact ⟨b * c, mul_mem hb hc, rfl⟩
  have orb_ne : ∀ C : Subgroup (Equiv.Perm (Fin N)), (orb C).Nonempty :=
    fun C => ⟨0, (mem_orb C 0).2 ⟨1, one_mem C, rfl⟩⟩
  have orb_card : ∀ C : Subgroup (Equiv.Perm (Fin N)), (orb C).card ≤ Nat.card C := by
    intro C
    haveI : Fintype ↥C := Fintype.ofFinite _
    have hsub : orb C ⊆ Finset.univ.image (fun c : ↥C => (c : Equiv.Perm (Fin N)) 0) := by
      intro k hk
      obtain ⟨c, hc, rfl⟩ := (mem_orb C k).1 hk
      exact Finset.mem_image.2 ⟨⟨c, hc⟩, Finset.mem_univ _, rfl⟩
    calc (orb C).card ≤ (Finset.univ.image (fun c : ↥C => (c : Equiv.Perm (Fin N)) 0)).card :=
          Finset.card_le_card hsub
      _ ≤ (Finset.univ : Finset ↥C).card := Finset.card_image_le
      _ = Nat.card C := by rw [Finset.card_univ, Nat.card_eq_fintype_card]
  by_cases htr : ∀ k : Fin N, ∃ b ∈ B, b 0 = k
  ·
    have hcomm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := fun a ha b hb =>
      congrArg Subtype.val (hB.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    have hinj : Function.Injective (fun b : ↥B => (b : Equiv.Perm (Fin N)) 0) := by
      intro b b' h
      have h0 : ((b : Equiv.Perm (Fin N))⁻¹ * b') 0 = 0 := by
        rw [Equiv.Perm.mul_apply]
        have : (b' : Equiv.Perm (Fin N)) 0 = (b : Equiv.Perm (Fin N)) 0 := h.symm
        rw [this, perm_inv_apply_self]
      have hc : ((b : Equiv.Perm (Fin N))⁻¹ * b') = 1 := by
        refine Equiv.ext fun k => ?_
        obtain ⟨a, ha, rfl⟩ := htr k
        have hcm := hcomm _ (mul_mem (inv_mem b.2) b'.2) a ha
        rw [Equiv.Perm.one_apply, ← Equiv.Perm.mul_apply, hcm, Equiv.Perm.mul_apply, h0]
      apply Subtype.ext
      have := congrArg (fun c => (b : Equiv.Perm (Fin N)) * c) hc
      simpa using this.symm
    have hcardB : Nat.card B = N := by
      have hbij : Function.Bijective (fun b : ↥B => (b : Equiv.Perm (Fin N)) 0) :=
        ⟨hinj, fun k => by
          obtain ⟨b, hb, hbk⟩ := htr k
          exact ⟨⟨b, hb⟩, hbk⟩⟩
      rw [Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_fin]
    obtain ⟨m, hm⟩ := hB.isPGroup.exists_card_eq
    have hm1 : 1 ≤ m := by
      by_contra h
      push Not at h
      have : m = 0 := by omega
      rw [this, pow_zero] at hm
      omega
    obtain ⟨B₀, hB₀B, hB₀card⟩ := exists_sub_card_pow' Nat.prime_three hm (k := m - 1) (by omega)
    refine ⟨B₀, hB₀B, ?_, orb B₀, orb_ne B₀, ?_, fun b hb i => orb_inv B₀ b hb i⟩
    · have h1 := Subgroup.relIndex_mul_card B₀ B
      rw [inf_of_le_left hB₀B, hm, hB₀card] at h1
      have h3 : 3 ^ m = 3 * 3 ^ (m - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      rw [h3] at h1
      have hpos : 0 < 3 ^ (m - 1) := by positivity
      have := Nat.eq_of_mul_eq_mul_right hpos h1
      omega
    · intro heq
      have hle := orb_card B₀
      rw [heq, Finset.card_univ, Fintype.card_fin, hB₀card] at hle
      rw [← hcardB, hm] at hle
      have : 3 ^ m ≤ 3 ^ (m - 1) := hle
      have h' : 3 ^ (m - 1) < 3 ^ m := Nat.pow_lt_pow_right (by norm_num) (by omega)
      omega
  · push Not at htr
    obtain ⟨k, hk⟩ := htr
    refine ⟨B, le_rfl, by rw [Subgroup.relIndex_self]; norm_num, orb B, orb_ne B, ?_,
      fun b hb i => orb_inv B b hb i⟩
    intro heq
    have hkO : k ∈ orb B := by rw [heq]; exact Finset.mem_univ k
    obtain ⟨c, hc, hck⟩ := (mem_orb B k).1 hkO
    exact hk c hc hck

end Monomial

section LinearCase

open Matrix

theorem starConcl_linear (hAut : LinearAutCube) {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4)
    {N : ℕ} (hN : 3 ≤ N) (D : Subgroup (MulAut (ProjectiveSpecialLinearGroup (Fin N) F)))
    (hD : IsElemAbelian 3 D) : StarConcl D := by
  classical
  haveI : CharP F 2 := Gen2318E64InAux.charP_two_of_card_four F hF
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (MulAut (ProjectiveSpecialLinearGroup (Fin N) F)) := MulEquiv.finite_left
  have hΦ : ∀ α ∈ D, ∃ g : GL (Fin N) F, conjPSLHom g = α := by
    intro α hα
    obtain ⟨g, hg⟩ := hAut F hF N hN α (hD.2 α hα)
    refine ⟨g, MulEquiv.ext fun y => ?_⟩
    induction y using QuotientGroup.induction_on with | H x => ?_
    show conjPSL g (x : ProjectiveSpecialLinearGroup (Fin N) F) = α x
    rw [conjPSL_mk]
    exact (hg x _ (coe_conjSL_apply g x)).symm
  set X : Subgroup (GL (Fin N) F) := D.comap conjPSLHom with hX
  let f : ↥X →* ↥D := (conjPSLHom.comp X.subtype).codRestrict D (fun x => x.2)
  have hf : Function.Surjective f := by
    rintro ⟨α, hα⟩
    obtain ⟨g, hg⟩ := hΦ α hα
    exact ⟨⟨g, show conjPSLHom g ∈ D by rw [hg]; exact hα⟩, Subtype.ext hg⟩
  obtain ⟨Q⟩ : Nonempty (Sylow 3 ↥X) := inferInstance
  have hD3 : IsPGroup 3 ↥D := hD.isPGroup
  have htop : (Q.mapSurjective hf : Subgroup ↥D) = ⊤ :=
    ((Q.mapSurjective hf).is_maximal' (hD3.to_subgroup ⊤) le_top).symm
  set P : Subgroup (GL (Fin N) F) := (Q : Subgroup ↥X).map X.subtype with hP
  have hPp : IsPGroup 3 ↥P := Q.isPGroup'.map X.subtype
  have hPD : ∀ p ∈ P, conjPSLHom p ∈ D := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hPsurj : ∀ α ∈ D, ∃ p ∈ P, conjPSLHom p = α := by
    intro α hα
    have hmem : (⟨α, hα⟩ : ↥D) ∈ (Q.mapSurjective hf : Subgroup ↥D) := by
      rw [htop]
      exact Subgroup.mem_top _
    rw [Sylow.coe_mapSurjective] at hmem
    obtain ⟨x, hx, hxα⟩ := Subgroup.mem_map.1 hmem
    exact ⟨x, ⟨x, hx, rfl⟩, congrArg Subtype.val hxα⟩
  obtain ⟨u, -, hu⟩ := Gen2318E64InAux.exists_conj_le_of_not_dvd (A := ⊤) le_top hPp
    (by rw [Subgroup.relIndex_top_right]; exact not_three_dvd_index_monoSub hF N)
  set P₁ : Subgroup (GL (Fin N) F) := P.map (MulAut.conj u⁻¹).toMonoidHom with hP₁
  have hP₁M : P₁ ≤ monoSub N F := by
    rintro _ ⟨x, hx, rfl⟩
    have := hu x hx
    simpa [MulAut.conj_apply] using this
  have hconjP₁ : ∀ x ∈ P₁, u * x * u⁻¹ ∈ P := by
    rintro _ ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  have hΦP₁ : ∀ x ∈ P₁, conjPSLHom (u * x * u⁻¹) ∈ D := fun x hx => hPD _ (hconjP₁ x hx)
  have hker : ∀ x : ↥P₁, conjPSLHom (u * (x : GL (Fin N) F) * u⁻¹) = 1 →
      monoPerm (Subgroup.inclusion hP₁M x) = 1 := by
    intro x hx
    apply monoPerm_eq_one_of_conjPSL (by omega)
    have h1 : conjPSLHom (x : GL (Fin N) F) =
        (conjPSLHom u)⁻¹ * conjPSLHom (u * (x : GL (Fin N) F) * u⁻¹) * conjPSLHom u := by
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
      group
    rw [show ((Subgroup.inclusion hP₁M x : ↥(monoSub N F)) : GL (Fin N) F) = (x : GL (Fin N) F)
      from rfl, h1, hx, mul_one, inv_mul_cancel]
  let f₁ : ↥P₁ →* Equiv.Perm (Fin N) := monoPerm.comp (Subgroup.inclusion hP₁M)
  have hDcomm : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hD.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hB : IsElemAbelian 3 f₁.range := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
    · obtain ⟨x, hx⟩ := a.2
      obtain ⟨y, hy⟩ := b.2
      change (a : Equiv.Perm (Fin N)) * b = b * a
      rw [← hx, ← hy]
      have hc : f₁ (x * y * x⁻¹ * y⁻¹) = 1 := by
        apply hker
        have e : u * ((x * y * x⁻¹ * y⁻¹ : ↥P₁) : GL (Fin N) F) * u⁻¹ =
            (u * x * u⁻¹) * (u * y * u⁻¹) * (u * x * u⁻¹)⁻¹ * (u * y * u⁻¹)⁻¹ := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          group
        rw [e, map_mul, map_mul, map_mul, map_inv, map_inv,
          hDcomm _ (hΦP₁ x x.2) _ (hΦP₁ y y.2)]
        group
      rw [map_mul, map_mul, map_mul, map_inv, map_inv] at hc
      calc f₁ x * f₁ y = (f₁ x * f₁ y * (f₁ x)⁻¹ * (f₁ y)⁻¹) * f₁ y * f₁ x := by group
        _ = f₁ y * f₁ x := by rw [hc, one_mul]
    · rintro _ ⟨x, rfl⟩
      rw [← map_pow]
      apply hker
      have e : u * ((x ^ 3 : ↥P₁) : GL (Fin N) F) * u⁻¹ = (u * x * u⁻¹) ^ 3 := by
        rw [Subgroup.coe_pow, conj_pow]
      rw [e, map_pow]
      exact hD.2 _ (hΦP₁ x x.2)
  obtain ⟨B₀, hB₀B, hB₀idx, O, hOne, hOuniv, hBO⟩ := exists_intransitive (by omega) f₁.range hB
  set E₁' : Subgroup ↥P₁ := B₀.comap f₁ with hE₁'
  have hE₁'idx : E₁'.index ≤ 3 := by
    rw [hE₁', Subgroup.index_comap]
    exact hB₀idx
  set Eg : Subgroup (GL (Fin N) F) := (E₁'.map P₁.subtype).map (MulAut.conj u).toMonoidHom with hEg
  have hEgP : Eg ≤ P := by
    rintro _ ⟨_, ⟨x, -, rfl⟩, rfl⟩
    simpa [MulAut.conj_apply] using hconjP₁ x x.2
  have hcardEg : Nat.card P ≤ 3 * Nat.card Eg := by
    have h1 : Nat.card Eg = Nat.card E₁' := by
      rw [hEg, Subgroup.card_map_of_injective (MulAut.conj u).injective,
        Subgroup.card_map_of_injective P₁.subtype_injective]
    have h2 : Nat.card P₁ = Nat.card P :=
      Subgroup.card_map_of_injective (MulAut.conj u⁻¹).injective
    have h3 := Subgroup.card_mul_index E₁'
    rw [h1, ← h2, ← h3, mul_comm]
    exact Nat.mul_le_mul_right _ hE₁'idx
  set E : Subgroup (MulAut (ProjectiveSpecialLinearGroup (Fin N) F)) := Eg.map conjPSLHom with hE
  have hED : E ≤ D := by
    rintro _ ⟨g, hg, rfl⟩
    exact hPD g (hEgP hg)
  obtain ⟨i, hiO⟩ := hOne
  obtain ⟨j, hjO⟩ : ∃ j, j ∉ O := by
    by_contra h
    push Not at h
    exact hOuniv (Finset.eq_univ_of_forall h)
  set U : Subgroup (ProjectiveSpecialLinearGroup (Fin N) F) :=
    ((uSub F O).map (conjSL u).toMonoidHom).map (QuotientGroup.mk' _) with hU
  refine ⟨E, hED, ?_, U, ?_, ?_, ?_⟩
  ·
    let fP : ↥P →* ↥D := (conjPSLHom.comp P.subtype).codRestrict D (fun p => hPD p p.2)
    have hfP : Function.Surjective fP := by
      rintro ⟨α, hα⟩
      obtain ⟨p, hp, hpα⟩ := hPsurj α hα
      exact ⟨⟨p, hp⟩, Subtype.ext hpα⟩
    have hmap : (Eg.subgroupOf P).map fP = E.subgroupOf D := by
      ext x
      constructor
      · rintro ⟨p, hp, rfl⟩
        exact Subgroup.mem_subgroupOf.2 ⟨p, Subgroup.mem_subgroupOf.1 hp, rfl⟩
      · intro hx
        obtain ⟨g, hg, hgx⟩ := Subgroup.mem_subgroupOf.1 hx
        exact ⟨⟨g, hEgP hg⟩, Subgroup.mem_subgroupOf.2 hg, Subtype.ext hgx⟩
    have hidxEg : (Eg.subgroupOf P).index ≤ 3 := by
      have h1 := Subgroup.card_mul_index (Eg.subgroupOf P)
      have h2 : Nat.card (Eg.subgroupOf P) = Nat.card Eg :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEgP).toEquiv
      rw [h2] at h1
      have hpos : 0 < Nat.card Eg := Nat.card_pos
      by_contra hlt
      push Not at hlt
      have : 4 * Nat.card Eg ≤ (Eg.subgroupOf P).index * Nat.card Eg := Nat.mul_le_mul_right _ hlt
      rw [mul_comm (Eg.subgroupOf P).index, h1] at this
      omega
    have hdvd := Subgroup.index_map_dvd (H := Eg.subgroupOf P) hfP
    rw [hmap] at hdvd
    have hne : (Eg.subgroupOf P).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hdvd).trans (hidxEg.trans (by norm_num))
  ·
    intro hbot
    set T : SpecialLinearGroup (Fin N) F :=
      ⟨transvection i j 1, det_transvection_of_ne i j (by rintro rfl; exact hjO hiO) 1⟩ with hT
    have hTU : T ∈ uSub F O := transvection_mem_uSub hiO hjO
    have hmem : (QuotientGroup.mk' _ (conjSL u T) : ProjectiveSpecialLinearGroup (Fin N) F) ∈ U :=
      ⟨conjSL u T, ⟨T, hTU, rfl⟩, rfl⟩
    rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
    obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hmem
    have hTm : (T : Matrix (Fin N) (Fin N) F) = scalar (Fin N) r := by
      have h1 : ((conjSL u T : SpecialLinearGroup (Fin N) F) : Matrix (Fin N) (Fin N) F) =
          scalar (Fin N) r := hr.symm
      rw [coe_conjSL_apply] at h1
      have h2 : (T : Matrix (Fin N) (Fin N) F) =
          ((u⁻¹ : GL (Fin N) F) : Matrix (Fin N) (Fin N) F) *
            ((u : Matrix (Fin N) (Fin N) F) * (T : Matrix (Fin N) (Fin N) F) *
              ((u⁻¹ : GL (Fin N) F) : Matrix (Fin N) (Fin N) F)) * (u : Matrix (Fin N) (Fin N) F) := by
        simp only [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
        simp only [Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
      rw [h2, h1, ← Matrix.scalar_commute r (fun _ => Commute.all _ _), Matrix.mul_assoc,
        ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
    have hij := congrFun (congrFun hTm i) j
    have hne : i ≠ j := by rintro rfl; exact hjO hiO
    rw [hT] at hij
    simp [transvection, Matrix.one_apply, hne, scalar_apply, diagonal_apply_ne _ hne] at hij
  ·
    exact ((isPGroup_uSub O).map _).map _
  ·
    rintro _ ⟨g, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩ _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    obtain ⟨d, hd⟩ := eq_mono_monoPerm (Subgroup.inclusion hP₁M x)
    have hσO : ∀ k, monoPerm (Subgroup.inclusion hP₁M x) k ∈ O ↔ k ∈ O := hBO _ hx
    have hxm : ((x : ↥P₁) : GL (Fin N) F) = mono d (monoPerm (Subgroup.inclusion hP₁M x)) := hd
    have hvx : conjSL ((x : ↥P₁) : GL (Fin N) F) v ∈ uSub F O := by
      rw [hxm]
      exact conjSL_mem_uSub d _ hσO hv
    refine ⟨conjSL u (conjSL ((x : ↥P₁) : GL (Fin N) F) v),
      ⟨conjSL ((x : ↥P₁) : GL (Fin N) F) v, hvx, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, QuotientGroup.mk'_apply, MulAut.conj_apply]
    show _ = conjPSL (u * ((x : ↥P₁) : GL (Fin N) F) * u⁻¹) _
    rw [conjPSL_mk, ← MulAut.mul_apply, ← conjSL_mul, ← MulAut.mul_apply, ← conjSL_mul]
    congr 2
    group

theorem star_linear (hAut : LinearAutCube) {S : Type} [Group S] [Finite S] (r : ℕ)
    (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.A r q).Valid) (hq : IsTwoPow q 2)
    (hr : 3 ≤ r + 1) (eS : S ≃* (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.A r q, hv⟩).Group)
    (D : Subgroup (MulAut S)) (hD : IsElemAbelian 3 D) : StarConcl D := by
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  let e1 := CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r q hv
  have hF : Nat.card (GaloisField q.p q.exponent) = 4 := by
    rw [GaloisField.card _ _ q.exponent_pos.ne', hq.1, hq.2]
    norm_num
  exact starConcl_of_congr (eS.trans e1) D (starConcl_linear hAut hF hr _ (hD.map _))

end LinearCase

section Assembly

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.TauCetiBridge.Even

set_option linter.unusedSectionVars false

theorem h3N_E6 : ∀ (K : Type) [Field K] [Finite K], 3 ∣ Nat.card K - 1 →
    ¬ 3 ∣ (monomialSubgroup Tag.E6 K).relIndex (adjointGroup Tag.E6 K) :=
  fun _ _ _ h3 => CFSG.HardMathSupport.Lang.E6Descent.DiagTorus.not_three_dvd_relIndex_monomial h3

theorem h3N_E7 : ∀ (K : Type) [Field K] [Finite K], 3 ∣ Nat.card K - 1 →
    ¬ 3 ∣ (monomialSubgroup Tag.E7 K).relIndex (adjointGroup Tag.E7 K) :=
  fun K _ _ h3 => not_three_dvd_of_sylow
    (CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.exists_sylow_three_le_monomialSub_E7 K h3)

theorem h3N_E8 : ∀ (K : Type) [Field K] [Finite K], 3 ∣ Nat.card K - 1 →
    ¬ 3 ∣ (monomialSubgroup Tag.E8 K).relIndex (adjointGroup Tag.E8 K) :=
  fun K _ _ h3 => not_three_dvd_of_sylow
    (CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.exists_sylow_three_le_monomialSub_E8 K h3)

theorem h3N_F4 : ∀ (K : Type) [Field K] [Finite K], 3 ∣ Nat.card K - 1 →
    ¬ 3 ∣ (monomialSubgroup Tag.F4 K).relIndex (adjointGroup Tag.F4 K) :=
  fun K _ _ h3 => not_three_dvd_of_sylow
    (CFSG.HardMathSupport.Curtis.UnitaryLevi.exists_sylow_three_le_monomialSub_F4 K h3)

theorem invCent_of_card {τ : Tag} {q : ℕ}
    (h : ∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = q ∧ InvCent ↥(adjointGroup τ k))
    (k' : Type) [Field k'] [Finite k'] (hk' : Nat.card k' = q) : InvCent ↥(adjointGroup τ k') := by
  classical
  obtain ⟨k, _, _, hk, hI⟩ := h
  haveI : Fintype k := Fintype.ofFinite k
  haveI : Fintype k' := Fintype.ofFinite k'
  have hcard : Fintype.card k = Fintype.card k' := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hk, hk']
  exact hI.of_mulEquiv
    (CFSG.HardMathSupport.Lang.AnisoE6.adjointGroupCongr (FiniteField.ringEquivOfCardEq hcard))

theorem star_of_model_inner {S : Type} [Group S] [Finite S] {τ : Tag} {k : Type} [Field k] [Finite k]
    (e : S ≃* ↥(adjointGroup τ k)) (hI : InvCent ↥(adjointGroup τ k))
    (hinn : ∀ β : MulAut ↥(adjointGroup τ k), β ^ 3 = 1 →
      β ∈ (MulAut.conj : ↥(adjointGroup τ k) →* MulAut ↥(adjointGroup τ k)).range)
    (D : Subgroup (MulAut S)) (hD : IsElemAbelian 3 D) :
    ∃ E : Subgroup (MulAut S), E ≤ D ∧ E.relIndex D ≤ 9 ∧
      ∃ U : Subgroup S, U ≠ ⊥ ∧ IsPGroup 2 ↥U ∧ ∀ φ ∈ E, ∀ u ∈ U, φ u ∈ U :=
  star_of_inner (E68FieldFixAux.center_eq_bot_of_mulEquiv e center_adjointGroup_eq_bot)
    (hI.of_mulEquiv e.symm) D hD
    (Gen2318OutAux.transport_mem_range e hinn D (fun x hx => hD.2 x hx))

theorem inner_of_cube_E78 (τ : Tag) (hτ : τ = .E7 ∨ τ = .E8) {k : Type} [Field k] [Finite k]
    {f : ℕ} (hf1 : 1 ≤ f) (hf3 : ¬ 3 ∣ f) (hk : Nat.card k = 2 ^ f)
    (β : MulAut ↥(adjointGroup τ k)) (hβ : β ^ 3 = 1) :
    β ∈ (MulAut.conj : ↥(adjointGroup τ k) →* MulAut ↥(adjointGroup τ k)).range := by
  by_contra hout
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdet : ¬ 3 ∣ τ.cartan.det.natAbs := by
    rcases hτ with rfl | rfl
    · rw [det_cartan_E7]
      norm_num
    · rw [det_cartan_E8]
      norm_num
  obtain ⟨d, -, -, -, -, hfd, -⟩ :=
    CFSG.HardMathSupport.Lang.E6Descent.exists_conj_entrywise_of_outer_E τ (by tauto) hf1 k hk
      Nat.prime_three (by norm_num) hdet β hβ hout
  exact hf3 ⟨d, hfd⟩

theorem star_E8_inner {S : Type} [Group S] [Finite S] (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.E8 q).Valid) {f : ℕ} (hq : IsTwoPow q f) (hf1 : 1 ≤ f) (hf3 : ¬ 3 ∣ f)
    (eS : S ≃* (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.E8 q, hv⟩).Group)
    (D : Subgroup (MulAut S)) (hD : IsElemAbelian 3 D) :
    ∃ E : Subgroup (MulAut S), E ≤ D ∧ E.relIndex D ≤ 9 ∧
      ∃ U : Subgroup S, U ≠ ⊥ ∧ IsPGroup 2 ↥U ∧ ∀ φ ∈ E, ∀ u ∈ U, φ u ∈ U := by
  obtain ⟨hq2, hqe⟩ := hq
  have hk : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hqcard : q.card = 2 ^ f := by rw [TauCeti.PrimePower.card_def, hq2, hqe]
  obtain ⟨eB⟩ := untwistedBridgeEven_E8 q hv hq2 (GaloisField 2 f) (hk.trans hqcard.symm)
  let e : S ≃* ↥(adjointGroup Tag.E8 (GaloisField 2 f)) :=
    (eS.trans eB.symm).trans (Gen2318OutAux.adjointEquiv Tag.E8 (GaloisField 2 f))
  exact star_of_model_inner e
    (invCent_of_card (exists_invCent orbitProp_E8 h3N_E8 hf1) (GaloisField 2 f) hk)
    (inner_of_cube_E78 .E8 (Or.inr rfl) hf1 hf3 hk) D hD

theorem star_E7_inner (hO7 : OrbitProp Tag.E7) {S : Type} [Group S] [Finite S]
    (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E7 q).Valid) {f : ℕ} (hq : IsTwoPow q f)
    (hf1 : 1 ≤ f) (hf3 : ¬ 3 ∣ f)
    (eS : S ≃* (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.E7 q, hv⟩).Group)
    (D : Subgroup (MulAut S)) (hD : IsElemAbelian 3 D) :
    ∃ E : Subgroup (MulAut S), E ≤ D ∧ E.relIndex D ≤ 9 ∧
      ∃ U : Subgroup S, U ≠ ⊥ ∧ IsPGroup 2 ↥U ∧ ∀ φ ∈ E, ∀ u ∈ U, φ u ∈ U := by
  obtain ⟨hq2, hqe⟩ := hq
  have hk : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hqcard : q.card = 2 ^ f := by rw [TauCeti.PrimePower.card_def, hq2, hqe]
  obtain ⟨eB⟩ := untwistedBridgeEven_E7 q hv hq2 (GaloisField 2 f) (hk.trans hqcard.symm)
  let e : S ≃* ↥(adjointGroup Tag.E7 (GaloisField 2 f)) :=
    (eS.trans eB.symm).trans (Gen2318OutAux.adjointEquiv Tag.E7 (GaloisField 2 f))
  exact star_of_model_inner e
    (invCent_of_card (exists_invCent hO7 h3N_E7 hf1) (GaloisField 2 f) hk)
    (inner_of_cube_E78 .E7 (Or.inl rfl) hf1 hf3 hk) D hD

theorem star_outThreePrime {S : Type} [Group S] [Finite S] {τ : Tag} {k : Type} [Field k] [Finite k]
    (d : TauCeti.ValidLieTypeIndex) (hd : IsOutThreePrimeIndex d.1)
    (eS : S ≃* (TauCeti.CFSGIndex.lie d).Group) (e : S ≃* ↥(adjointGroup τ k))
    (hI : InvCent ↥(adjointGroup τ k)) (D : Subgroup (MulAut S)) (hD : IsElemAbelian 3 D) :
    ∃ E : Subgroup (MulAut S), E ≤ D ∧ E.relIndex D ≤ 9 ∧
      ∃ U : Subgroup S, U ≠ ⊥ ∧ IsPGroup 2 ↥U ∧ ∀ φ ∈ E, ∀ u ∈ U, φ u ∈ U :=
  star_of_inner (E68FieldFixAux.center_eq_bot_of_mulEquiv e center_adjointGroup_eq_bot)
    (hI.of_mulEquiv e.symm) D hD (gen2318OutThreePrime_holds S d hd ⟨eS⟩ D hD)

theorem star_F4 {S : Type} [Group S] [Finite S] (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.F4 q).Valid) (hq : IsTwoPow q 2)
    (eS : S ≃* (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.F4 q, hv⟩).Group)
    (D : Subgroup (MulAut S)) (hD : IsElemAbelian 3 D) :
    ∃ E : Subgroup (MulAut S), E ≤ D ∧ E.relIndex D ≤ 9 ∧
      ∃ U : Subgroup S, U ≠ ⊥ ∧ IsPGroup 2 ↥U ∧ ∀ φ ∈ E, ∀ u ∈ U, φ u ∈ U := by
  have hq' := hq
  obtain ⟨hq2, hqe⟩ := hq'
  have hk : Nat.card (GaloisField 2 2) = 2 ^ 2 := GaloisField.card 2 2 (by omega)
  have hqcard : q.card = 2 ^ 2 := by rw [TauCeti.PrimePower.card_def, hq2, hqe]
  obtain ⟨eB⟩ := untwistedBridgeEven_F4 q hv hq2 (GaloisField 2 2) (hk.trans hqcard.symm)
  let e : S ≃* ↥(adjointGroup Tag.F4 (GaloisField 2 2)) :=
    (eS.trans eB.symm).trans (Gen2318OutAux.adjointEquiv Tag.F4 (GaloisField 2 2))
  exact star_outThreePrime ⟨_, hv⟩ hq eS e
    (invCent_of_card (exists_invCent orbitProp_F4 h3N_F4 (by norm_num)) (GaloisField 2 2) hk) D hD

theorem star_E6_two {S : Type} [Group S] [Finite S] (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.E6 q).Valid) (hq : IsTwoPow q 1)
    (eS : S ≃* (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.E6 q, hv⟩).Group)
    (D : Subgroup (MulAut S)) (hD : IsElemAbelian 3 D) :
    ∃ E : Subgroup (MulAut S), E ≤ D ∧ E.relIndex D ≤ 9 ∧
      ∃ U : Subgroup S, U ≠ ⊥ ∧ IsPGroup 2 ↥U ∧ ∀ φ ∈ E, ∀ u ∈ U, φ u ∈ U := by
  have hq' := hq
  obtain ⟨hq2, hqe⟩ := hq'
  have hk : Nat.card (GaloisField 2 1) = 2 ^ 1 := GaloisField.card 2 1 (by omega)
  have hqcard : q.card = 2 ^ 1 := by rw [TauCeti.PrimePower.card_def, hq2, hqe]
  obtain ⟨eB⟩ := untwistedBridgeEven_E6 q hv hq2 (GaloisField 2 1) (hk.trans hqcard.symm)
  let e : S ≃* ↥(adjointGroup Tag.E6 (GaloisField 2 1)) :=
    (eS.trans eB.symm).trans (Gen2318OutAux.adjointEquiv Tag.E6 (GaloisField 2 1))
  exact star_outThreePrime ⟨_, hv⟩ hq eS e
    (invCent_of_card (exists_invCent orbitProp_E6 h3N_E6 le_rfl) (GaloisField 2 1) hk) D hD

theorem star_E6_four {S : Type} [Group S] [Finite S] (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.E6 q).Valid) (hq : IsTwoPow q 2)
    (eL : S ≃* (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.E6 q, hv⟩).Group)
    (A : Subgroup (MulAut S)) (hA : IsElemAbelian 3 A) :
    ∃ E : Subgroup (MulAut S), E ≤ A ∧ E.relIndex A ≤ 9 ∧
      ∃ U : Subgroup S, U ≠ ⊥ ∧ IsPGroup 2 ↥U ∧ ∀ φ ∈ E, ∀ u ∈ U, φ u ∈ U := by
  obtain ⟨hq1, hq2⟩ := hq
  have hK4 : Nat.card (GaloisField 2 2) = TauCeti.PrimePower.card q := by
    rw [TauCeti.PrimePower.card_def, GaloisField.card 2 2 (by norm_num), hq1, hq2]
  obtain ⟨eB⟩ := untwistedBridgeEven_E6 q hv hq1 (GaloisField 2 2) hK4
  let eS : S ≃* ↥(adjointGroup Tag.E6 (GaloisField 2 2)) :=
    eL.trans (eB.symm.trans (Gen2318OutAux.adjointEquiv Tag.E6 (GaloisField 2 2)))
  have hF : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  set e := MulAut.congr eS with he
  obtain ⟨E', hE'A', hcard, U', hU'0, hU'2, hU'⟩ :=
    Gen2318E64InAux.model_main hF (A.map e.toMonoidHom) (hA.map _)
  have hEA : E'.map e.symm.toMonoidHom ≤ A := by
    rintro _ ⟨φ', hφ', rfl⟩
    obtain ⟨ψ, hψ, rfl⟩ := hE'A' hφ'
    simpa using hψ
  refine ⟨E'.map e.symm.toMonoidHom, hEA, ?_, U'.map eS.symm.toMonoidHom, ?_, hU'2.map _, ?_⟩
  · refine relIndex_le_of_card_le hEA (n := 9) ?_
    have h1 : Nat.card A = Nat.card (A.map e.toMonoidHom) :=
      (Subgroup.card_map_of_injective e.injective).symm
    have h2 : Nat.card (E'.map e.symm.toMonoidHom) = Nat.card E' :=
      Subgroup.card_map_of_injective e.symm.injective
    rw [h1, h2]
    omega
  · intro h
    exact hU'0 ((Subgroup.map_eq_bot_iff_of_injective U' (f := eS.symm.toMonoidHom)
      eS.symm.injective).1 h)
  · rintro _ ⟨φ', hφ', rfl⟩ _ ⟨u', hu', rfl⟩
    refine ⟨φ' u', hU' φ' hφ' u' hu', ?_⟩
    simp [he, MulAut.congr_apply]

end Assembly

section FieldAut

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.TauCetiBridge.Even
open CFSG.RankThree.PartOne.CTP (fixedSubgroup mem_fixedSubgroup)

set_option linter.unusedSectionVars false

theorem entrywiseFixedGroup_eq_of_card_two {τ : Tag} {M : Type} [Field M] [Finite M] (σ : M ≃+* M)
    (h2 : Nat.card (fixSubfield σ) = 2) :
    entrywiseFixedGroup τ σ = fixedFieldImage τ σ := by
  refine le_antisymm ?_ fixedFieldImage_le
  obtain ⟨-, h⟩ := fixedFieldImage_index_dvd_card (τ := τ) σ
  rw [h2] at h
  have h1 : ((fixedFieldImage τ σ).subgroupOf (entrywiseFixedGroup τ σ)).index = 1 := by
    have h' : (2 - 1 : ℕ) ^ τ.rank = 1 := by simp
    rw [h'] at h
    exact Nat.dvd_one.1 h
  rw [Subgroup.index_eq_one] at h1
  intro g hg
  have hmem : (⟨g, hg⟩ : entrywiseFixedGroup τ σ) ∈
      (fixedFieldImage τ σ).subgroupOf (entrywiseFixedGroup τ σ) := by
    rw [h1]
    exact Subgroup.mem_top _
  exact hmem

theorem exists_fixed_equiv_E (τ : Tag) (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {k : Type} [Field k]
    [Finite k] (hk : Nat.card k = 2 ^ 3) (β : MulAut ↥(adjointGroup τ k)) (hβ3 : β ^ 3 = 1)
    (hβout : β ∉ (MulAut.conj : ↥(adjointGroup τ k) →* MulAut ↥(adjointGroup τ k)).range) :
    ∃ T : k ≃+* k, Nat.card ↥(fixSubfield T) = 2 ∧
      Nonempty (↥(fixedSubgroup β) ≃* ↥(adjointGroup τ ↥(fixSubfield T))) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨d, T, r, j, ψ, hd, -, hTcard, -, -, hβr, hψ⟩ :=
    CFSG.HardMathSupport.Lang.E6Descent.exists_conj_entrywise_of_not_innerDiag τ hτ
      (ℓ := 2) (f := 3) (p := 3) (by norm_num) k hk Nat.prime_three (by norm_num) β hβ3
      (fun g a h => by
        obtain ⟨-, h7⟩ := CFSG.HardMathSupport.Lang.E6Descent.prime_dvd_of_diag_noninner τ hτ k
          Nat.prime_three g a β h hβ3 hβout
        rw [hk] at h7
        norm_num at h7)
  have hd1 : d = 1 := by omega
  subst hd1
  have h2 : Nat.card (fixSubfield T) = 2 := by rw [hTcard]; norm_num
  have hΓJ := entrywiseFixedGroup_eq_of_card_two (τ := τ) T h2
  refine ⟨T, h2, ⟨?_⟩⟩
  have hfix : fixedSubgroup β = fixedSubgroup (β ^ r) := E68FieldFixAux.fixedSubgroup_pow_eq hβr
  have E2 : ↥(fixedSubgroup β) ≃* ↥(fixedSubgroup (entrywiseAdjointAut τ T)) :=
    (Subgroup.equivMapOfInjective _ ψ.toMonoidHom ψ.injective).trans
      (MulEquiv.subgroupCongr ((congrArg (Subgroup.map ψ.toMonoidHom) hfix).trans
        ((E68FieldFixAux.fixed_map_conj ψ (β ^ r)).trans (congrArg fixedSubgroup hψ))))
  exact E2.trans (CFSG.LieType.SeitzGeneration.ExcOuterLeOne.fixedEquivOfEq (τ := τ) T hΓJ)

theorem card_le_three_mul_inner (τ : Tag) (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {k : Type} [Field k]
    [Finite k] (hk : Nat.card k = 2 ^ 3) (D : Subgroup (MulAut ↥(adjointGroup τ k)))
    (hD : IsElemAbelian 3 D) :
    Nat.card D ≤ 3 * Nat.card ↥(D ⊓
      (MulAut.conj : ↥(adjointGroup τ k) →* MulAut ↥(adjointGroup τ k)).range) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (ModGL τ k) := finite_modGL
  obtain ⟨Θ, -, -, hker, -, -⟩ :=
    CFSG.LieType.Chevalley.ordinary_E_field_graph_quotient_and_involutions τ hτ k
  let f : ↥D →* RingAut k × Multiplicative (ZMod (exactE τ)) := Θ.comp D.subtype
  have hkerle : ∀ x : ↥D, f x = 1 → (x : MulAut ↥(adjointGroup τ k)) ∈
      (MulAut.conj : ↥(adjointGroup τ k) →* MulAut ↥(adjointGroup τ k)).range := by
    intro x hx
    obtain ⟨g, a, hga⟩ := (hker x).1 (MonoidHom.mem_ker.2 hx)
    have hxa : (x : MulAut ↥(adjointGroup τ k)) = MulAut.conj g * rootDiagAut τ k a := by
      refine MulEquiv.ext fun h => Subtype.ext ?_
      rw [hga h, MulAut.mul_apply, MulAut.conj_apply]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_rootDiagAut]
      group
    by_contra hout
    obtain ⟨-, h7⟩ := CFSG.HardMathSupport.Lang.E6Descent.prime_dvd_of_diag_noninner τ hτ k
      Nat.prime_three g a x hxa (hD.2 x x.2) hout
    rw [hk] at h7
    norm_num at h7
  have hRcard : Nat.card (RingAut k) = 3 :=
    (CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField.ringAut_card_and_cyclic (F := k)
      (n := 3) hk).1
  have hEcard : Nat.card (Multiplicative (ZMod (exactE τ))) ≤ 2 := by
    rw [Nat.card_congr Multiplicative.toAdd]
    rcases hτ with rfl | rfl | rfl <;> simp [exactE]
  haveI : NeZero (exactE τ) := ⟨by rcases hτ with rfl | rfl | rfl <;> simp [exactE]⟩
  haveI : Finite (RingAut k) := Nat.finite_of_card_ne_zero (by rw [hRcard]; norm_num)
  have hr3 : Nat.card f.range ≤ 3 := by
    have hp : IsPGroup 3 f.range := by
      rintro ⟨_, ⟨x, rfl⟩⟩
      refine ⟨1, Subtype.ext ?_⟩
      simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
      rw [← map_pow]
      have : x ^ 3 = 1 := Subtype.ext (by simpa using hD.2 x x.2)
      rw [this, map_one]
    obtain ⟨n, hn⟩ := hp.exists_card_eq
    have hdvd : Nat.card f.range ∣ Nat.card (RingAut k × Multiplicative (ZMod (exactE τ))) :=
      Subgroup.card_subgroup_dvd_card _
    rw [Nat.card_prod, hRcard] at hdvd
    rw [hn] at hdvd ⊢
    haveI : Finite (Multiplicative (ZMod (exactE τ))) :=
      Nat.finite_of_card_ne_zero (by
        rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
        exact NeZero.ne _)
    have hle : 3 ^ n ≤ 3 * 2 := (Nat.le_of_dvd (Nat.mul_pos (by norm_num) Nat.card_pos) hdvd).trans
      (Nat.mul_le_mul_left 3 hEcard)
    have hn1 : n ≤ 1 := by
      by_contra h
      push Not at h
      have : 3 ^ 2 ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) h
      omega
    interval_cases n <;> norm_num
  have h1 := Subgroup.card_mul_index f.ker
  rw [Subgroup.index_ker] at h1
  have hk3 : Nat.card f.ker ≤ Nat.card ↥(D ⊓
      (MulAut.conj : ↥(adjointGroup τ k) →* MulAut ↥(adjointGroup τ k)).range) :=
    Nat.card_le_card_of_injective (fun x => ⟨(x : ↥D), (x : ↥D).2, hkerle x x.2⟩)
      (fun a b h => by
        have h' := congrArg Subtype.val h
        exact Subtype.ext (Subtype.ext h'))
  calc Nat.card D = Nat.card f.ker * Nat.card f.range := h1.symm
    _ ≤ Nat.card ↥(D ⊓
        (MulAut.conj : ↥(adjointGroup τ k) →* MulAut ↥(adjointGroup τ k)).range) * 3 :=
      Nat.mul_le_mul hk3 hr3
    _ = _ := mul_comm _ _

theorem conj_injective_of_center {S : Type*} [Group S] (hZ : Subgroup.center S = ⊥) :
    Function.Injective (MulAut.conj : S →* MulAut S) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hxZ : x ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro y
    have h := congrArg (fun φ : MulAut S => φ y) hx
    simp only [MulAut.conj_apply, MulAut.one_apply] at h
    calc y * x = x * y * x⁻¹ * x := by rw [h]
      _ = x * y := by group
  rw [hZ, Subgroup.mem_bot] at hxZ
  exact hxZ

theorem conj_apply_eq {S : Type*} [Group S] (φ : MulAut S) (g : S) :
    MulAut.conj (φ g) = φ * MulAut.conj g * φ⁻¹ := by
  refine MulEquiv.ext fun x => ?_
  simp only [MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_apply, map_mul, map_inv,
    MulEquiv.apply_symm_apply]

theorem starConcl_field (τ : Tag) (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {k : Type} [Field k]
    [Finite k] (hk : Nat.card k = 2 ^ 3)
    (hI2 : ∀ (k₂ : Type) [Field k₂] [Finite k₂], Nat.card k₂ = 2 → InvCent ↥(adjointGroup τ k₂))
    (hI8 : InvCent ↥(adjointGroup τ k)) (D : Subgroup (MulAut ↥(adjointGroup τ k)))
    (hD : IsElemAbelian 3 D) : StarConcl D := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (ModGL τ k) := finite_modGL
  have hZ : Subgroup.center ↥(adjointGroup τ k) = ⊥ := center_adjointGroup_eq_bot
  by_cases hinn : D ≤ (MulAut.conj : ↥(adjointGroup τ k) →* MulAut ↥(adjointGroup τ k)).range
  · exact star_of_inner hZ hI8 D hD hinn
  obtain ⟨b, hbD, hbout⟩ := Set.not_subset.1 hinn
  have hb3 : b ^ 3 = 1 := hD.2 b hbD
  obtain ⟨T, hT2, ⟨F⟩⟩ := exists_fixed_equiv_E τ hτ hk b hb3 hbout
  have hIF : InvCent ↥(fixedSubgroup b) := (hI2 _ hT2).of_mulEquiv F.symm
  have hinj := conj_injective_of_center hZ
  have hP₀map : ((D ⊓ (MulAut.conj : ↥(adjointGroup τ k) →* MulAut ↥(adjointGroup τ k)).range).comap
      MulAut.conj).map MulAut.conj =
      D ⊓ (MulAut.conj : ↥(adjointGroup τ k) →* MulAut ↥(adjointGroup τ k)).range :=
    Subgroup.map_comap_eq_self inf_le_right
  set P₀ : Subgroup ↥(adjointGroup τ k) :=
    (D ⊓ (MulAut.conj : ↥(adjointGroup τ k) →* MulAut ↥(adjointGroup τ k)).range).comap
      MulAut.conj with hP₀
  have hP₀el : IsElemAbelian 3 P₀ :=
    I102UniqAux.isElemAbelian_comap' _ hinj (hD.mono inf_le_left)
  have hP₀F : P₀ ≤ fixedSubgroup b := by
    intro p hp
    have hpD : MulAut.conj p ∈ D := (show MulAut.conj p ∈ D ⊓ _ from hp).1
    have hc : b * MulAut.conj p = MulAut.conj p * b :=
      congrArg Subtype.val (hD.1.is_comm.comm ⟨b, hbD⟩ ⟨_, hpD⟩)
    have h2 : MulAut.conj (b p) = MulAut.conj p := by
      rw [conj_apply_eq, hc, mul_inv_cancel_right]
    rw [mem_fixedSubgroup]
    exact hinj h2
  obtain ⟨E₀', hE₀'P, hcard₀, t', ht'1, ht'2, hE₀'t⟩ :=
    hIF (P₀.subgroupOf (fixedSubgroup b)) (hP₀el.subgroupOf _)
  set E₀ : Subgroup ↥(adjointGroup τ k) := E₀'.map (fixedSubgroup b).subtype with hE₀
  have hE₀P₀ : E₀ ≤ P₀ := by
    rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_subgroupOf.1 (hE₀'P hx)
  set E₀c : Subgroup (MulAut ↥(adjointGroup τ k)) := E₀.map MulAut.conj with hE₀c
  have hE₀cDI : E₀c ≤ D ⊓ (MulAut.conj : ↥(adjointGroup τ k) →* MulAut ↥(adjointGroup τ k)).range := by
    rw [← hP₀map]
    exact Subgroup.map_mono hE₀P₀
  set E : Subgroup (MulAut ↥(adjointGroup τ k)) := Subgroup.zpowers b ⊔ E₀c with hE
  have hED : E ≤ D := sup_le ((Subgroup.zpowers_le).2 hbD) (hE₀cDI.trans inf_le_left)
  set t : ↥(adjointGroup τ k) := (t' : ↥(adjointGroup τ k)) with ht
  have hEt : ∀ φ ∈ E, φ t = t := by
    have hle : E ≤ MulAction.stabilizer (MulAut ↥(adjointGroup τ k)) t := by
      refine sup_le ((Subgroup.zpowers_le).2 ?_) ?_
      · rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
        exact (mem_fixedSubgroup.1 t'.2)
      · rintro _ ⟨e, ⟨e', he', rfl⟩, rfl⟩
        rw [MulAction.mem_stabilizer_iff, MulAut.smul_def, MulAut.conj_apply]
        have h := congrArg Subtype.val (hE₀'t e' he')
        simp only [Subgroup.coe_mul] at h
        rw [Subgroup.coe_subtype, ht, h, mul_inv_cancel_right]
    intro φ hφ
    have := hle hφ
    rwa [MulAction.mem_stabilizer_iff, MulAut.smul_def] at this
  refine ⟨E, hED, ?_, Subgroup.zpowers t, ?_, ?_, ?_⟩
  ·
    have hcardD := card_le_three_mul_inner τ hτ hk D hD
    have h1 : Nat.card ↥(D ⊓ (MulAut.conj : ↥(adjointGroup τ k) →* MulAut ↥(adjointGroup τ k)).range)
        = Nat.card P₀ := by
      rw [← hP₀map, Subgroup.card_map_of_injective hinj]
    have h2 : Nat.card (P₀.subgroupOf (fixedSubgroup b)) = Nat.card P₀ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP₀F).toEquiv
    have h3 : Nat.card E₀c = Nat.card E₀' := by
      rw [hE₀c, Subgroup.card_map_of_injective hinj, hE₀,
        Subgroup.card_map_of_injective (fixedSubgroup b).subtype_injective]
    have hE₀cE : E₀c ≤ E := le_sup_right
    have hidx3 : 3 ≤ E₀c.relIndex E := by
      have hdvd : E₀c.relIndex E ∣ Nat.card E := Subgroup.relIndex_dvd_card _ _
      have hEp : IsPGroup 3 E := (hD.mono hED).isPGroup
      obtain ⟨m, hm⟩ := hEp.exists_card_eq
      rw [hm] at hdvd
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
      have hne : E₀c.relIndex E ≠ 1 := by
        intro h1
        have hle := (Subgroup.relIndex_eq_one).1 h1
        exact hbout (hE₀cDI (hle (Subgroup.mem_sup_left (Subgroup.mem_zpowers b)))).2
      rw [hj] at hne ⊢
      have : j ≠ 0 := by
        rintro rfl
        exact hne (pow_zero 3)
      calc 3 = 3 ^ 1 := (pow_one 3).symm
        _ ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.2 this)
    have hcardE : 3 * Nat.card E₀c ≤ Nat.card E := by
      have h := Subgroup.relIndex_mul_card E₀c E
      rw [inf_of_le_left hE₀cE] at h
      rw [← h]
      exact Nat.mul_le_mul_right _ hidx3
    refine relIndex_le_of_card_le hED (n := 9) ?_
    omega
  · intro h
    apply ht'1
    have : t ∈ Subgroup.zpowers t := Subgroup.mem_zpowers t
    rw [h, Subgroup.mem_bot] at this
    exact Subtype.ext this
  · intro u
    refine ⟨1, Subtype.ext ?_⟩
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 u.2
    have ht2 : t ^ 2 = 1 := by
      have := congrArg Subtype.val ht'2
      simpa using this
    rw [Subgroup.coe_pow, ← hn, pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, ht2, one_zpow, Subgroup.coe_one]
  · intro φ hφ u hu
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    rw [map_zpow, hEt φ hφ]
    exact Subgroup.zpow_mem_zpowers t n

theorem star_eight (τ : Tag) (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hO : OrbitProp τ)
    (h3N : ∀ (K : Type) [Field K] [Finite K], 3 ∣ Nat.card K - 1 →
      ¬ 3 ∣ (monomialSubgroup τ K).relIndex (adjointGroup τ K))
    {S : Type} [Group S] [Finite S] {k : Type} [Field k] [Finite k] (hk : Nat.card k = 2 ^ 3)
    (e : S ≃* ↥(adjointGroup τ k)) (D : Subgroup (MulAut S)) (hD : IsElemAbelian 3 D) :
    StarConcl D :=
  starConcl_of_congr e D (starConcl_field τ hτ hk
    (fun k₂ _ _ hk₂ => invCent_of_card (exists_invCent hO h3N le_rfl) k₂ (by rw [hk₂]; norm_num))
    (invCent_of_card (exists_invCent hO h3N (by norm_num : 1 ≤ 3)) k hk) _ (hD.map _))

end FieldAut

end Star2313InAux

section Main

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.TauCetiBridge.Even Star2313InAux

set_option linter.unusedSectionVars false

theorem star2313Even_of_inputs (hAut : LinearAutCube) (hU : Star2313UnitaryInput) :
    Star2313Even := by
  have hO7 : OrbitProp Tag.E7 := orbitProp_E7
  intro S _ _ d hd hS D hD
  obtain ⟨eS⟩ := hS
  obtain ⟨d1, hv⟩ := d
  cases d1 with
  | A r q =>
    obtain ⟨hq, n, hn, hrn⟩ := hd
    have hr : 3 ≤ r + 1 := by
      rw [hrn]
      calc 3 ≤ 3 ^ 2 := by norm_num
        _ ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    exact star_linear hAut r q hv hq hr eS D hD
  | twistedA r q => exact hU S r q hv hd ⟨eS⟩ D hD
  | F4 q => exact star_F4 q hv hd eS D hD
  | E6 q =>
    rcases hd with h | h | h
    · exact star_E6_two q hv h eS D hD
    · exact star_E6_four q hv h eS D hD
    · obtain ⟨hq2, hqe⟩ := h
      have hk : Nat.card (GaloisField 2 3) = 2 ^ 3 := GaloisField.card 2 3 (by omega)
      have hqcard : q.card = 2 ^ 3 := by rw [TauCeti.PrimePower.card_def, hq2, hqe]
      obtain ⟨eB⟩ := untwistedBridgeEven_E6 q hv hq2 (GaloisField 2 3) (hk.trans hqcard.symm)
      exact star_eight .E6 (Or.inl rfl) orbitProp_E6 h3N_E6 hk
        ((eS.trans eB.symm).trans (Gen2318OutAux.adjointEquiv Tag.E6 (GaloisField 2 3))) D hD
  | E7 q =>
    rcases hd with h | h
    · exact star_E7_inner hO7 q hv h le_rfl (by norm_num) eS D hD
    · obtain ⟨hq2, hqe⟩ := h
      have hk : Nat.card (GaloisField 2 3) = 2 ^ 3 := GaloisField.card 2 3 (by omega)
      have hqcard : q.card = 2 ^ 3 := by rw [TauCeti.PrimePower.card_def, hq2, hqe]
      obtain ⟨eB⟩ := untwistedBridgeEven_E7 q hv hq2 (GaloisField 2 3) (hk.trans hqcard.symm)
      exact star_eight .E7 (Or.inr (Or.inl rfl)) hO7 h3N_E7 hk
        ((eS.trans eB.symm).trans (Gen2318OutAux.adjointEquiv Tag.E7 (GaloisField 2 3))) D hD
  | E8 q =>
    rcases hd with h | h | h
    · exact star_E8_inner q hv h le_rfl (by norm_num) eS D hD
    · exact star_E8_inner q hv h (by norm_num) (by norm_num) eS D hD
    · obtain ⟨hq2, hqe⟩ := h
      have hk : Nat.card (GaloisField 2 3) = 2 ^ 3 := GaloisField.card 2 3 (by omega)
      have hqcard : q.card = 2 ^ 3 := by rw [TauCeti.PrimePower.card_def, hq2, hqe]
      obtain ⟨eB⟩ := untwistedBridgeEven_E8 q hv hq2 (GaloisField 2 3) (hk.trans hqcard.symm)
      exact star_eight .E8 (Or.inr (Or.inr rfl)) orbitProp_E8 h3N_E8 hk
        ((eS.trans eB.symm).trans (Gen2318OutAux.adjointEquiv Tag.E8 (GaloisField 2 3))) D hD
  | B r q => exact hd.elim
  | C r q => exact hd.elim
  | D r q => exact hd.elim
  | twistedD r q => exact hd.elim
  | G2 q => exact hd.elim
  | twistedE6 q => exact hd.elim
  | trialityD4 q => exact hd.elim
  | suzuki m => exact hd.elim
  | reeG2 m => exact hd.elim
  | reeF4 m => exact hd.elim
  | tits => exact hd.elim

end Main

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
