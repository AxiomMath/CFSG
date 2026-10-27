module

public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.ClassicalInvolution.RouteD.GapsPerfect
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.AutRankThree.CentralAbelian
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open Matrix
open scoped IsMulCommutative

private theorem equivPi_single_mul {S : Type*} [CommRing S] [IsArtinianRing S] [IsReduced S]
    [DecidableEq (MaximalSpectrum S)] (I : MaximalSpectrum S) (u : S ⧸ I.asIdeal) (s : S) :
    IsArtinianRing.equivPi S ((IsArtinianRing.equivPi S).symm (Pi.single I u) * s) =
      Pi.single I (u * IsArtinianRing.equivPi S s I) := by
  rw [map_mul, AlgEquiv.apply_symm_apply]
  funext J
  by_cases h : J = I
  · subst h; simp
  · simp [h]

private theorem exists_mulVec_idempotent_ne_zero {K ι : Type*} [Field K] [Fintype ι]
    [DecidableEq ι] (S : Subalgebra K (Matrix ι ι K)) [IsMulCommutative S] [IsArtinianRing S]
    [IsReduced S] [Fintype (MaximalSpectrum S)] [DecidableEq (MaximalSpectrum S)] :
    ∃ w : ι → K, ∀ I : MaximalSpectrum S,
      (((IsArtinianRing.equivPi S).symm (Pi.single I 1) : S) : Matrix ι ι K) *ᵥ w ≠ 0 := by
  set φ := IsArtinianRing.equivPi S
  let e : MaximalSpectrum S → S := fun I => φ.symm (Pi.single I 1)
  have hφe : ∀ J, φ (e J) = Pi.single J 1 := fun J => φ.apply_symm_apply _
  have hv : ∀ I, ∃ v : ι → K, (e I : Matrix ι ι K) *ᵥ v ≠ 0 := fun I => by
    by_contra h
    push Not at h
    have h0 : e I = 0 :=
      Subtype.ext (Matrix.ext_of_mulVec_single fun i => by
        rw [h, ZeroMemClass.coe_zero, Matrix.zero_mulVec])
    have h1 := hφe I
    rw [h0, map_zero] at h1
    exact one_ne_zero (Pi.single_eq_zero_iff.mp h1.symm)
  choose v hv using hv
  refine ⟨∑ J, (e J : Matrix ι ι K) *ᵥ v J, fun I => ?_⟩
  simp only [Matrix.mulVec_sum, Matrix.mulVec_mulVec]
  rw [Finset.sum_eq_single I]
  · rw [← Subalgebra.coe_mul]
    convert hv I using 3
    apply φ.injective
    rw [equivPi_single_mul, hφe, Pi.single_eq_same, one_mul]
  · intro J _ hJ
    rw [← Subalgebra.coe_mul]
    have : e I * e J = 0 := by
      apply φ.injective
      rw [equivPi_single_mul, hφe, map_zero, Pi.single_eq_of_ne (Ne.symm hJ), mul_zero,
        Pi.single_zero]
    rw [this, ZeroMemClass.coe_zero, Matrix.zero_mulVec]
  · simp

theorem finrank_le_of_isReduced {K : Type} [Field K] [Finite K] {ι : Type} [Fintype ι]
    [DecidableEq ι] (S : Subalgebra K (Matrix ι ι K)) [IsMulCommutative S] [IsReduced S] :
    Module.finrank K S ≤ Fintype.card ι := by
  classical
  have : IsArtinianRing S := isArtinian_of_finite
  have := Fintype.ofFinite (MaximalSpectrum S)
  obtain ⟨w, hw⟩ := exists_mulVec_idempotent_ne_zero S
  set φ := IsArtinianRing.equivPi S
  let f : S →ₗ[K] (ι → K) :=
    { toFun := fun s => (s : Matrix ι ι K) *ᵥ w
      map_add' := fun s t => by simp [Matrix.add_mulVec]
      map_smul' := fun c s => by simp [Matrix.smul_mulVec] }
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro s hs
    apply φ.injective
    funext I
    by_contra hI
    obtain ⟨u, hu⟩ := Ideal.Quotient.exists_inv hI
    have hts : φ.symm (Pi.single I u) * s = φ.symm (Pi.single I 1) := by
      apply φ.injective
      rw [equivPi_single_mul, mul_comm u, hu, AlgEquiv.apply_symm_apply]
    apply hw I
    rw [← hts, Subalgebra.coe_mul, ← Matrix.mulVec_mulVec]
    have : (s : Matrix ι ι K) *ᵥ w = 0 := hs
    rw [this, Matrix.mulVec_zero]
  simpa using f.finrank_le_finrank_of_injective hf

private theorem exists_noncomm_coprime {Q : Type*} [Group Q] [Finite Q]
    (hQ : CFSG.IsQuasisimple Q) (p : ℕ) [hp : Fact p.Prime] :
    ∃ x y : Q, x * y ≠ y * x ∧ p.Coprime (orderOf x) := by
  obtain ⟨-, hsimp, a, b, hab⟩ := hQ
  by_contra h
  push Not at h
  obtain ⟨k, m, hm, hn⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (Nat.card_pos (α := Q)).ne' p hp.out.one_lt.ne'
  have hc : ∀ g : Q, g ^ p ^ k ∈ Subgroup.center Q := fun g => by
    rw [Subgroup.mem_center_iff]
    intro z
    by_contra hz
    refine h _ _ (fun e => hz e.symm) (Nat.Coprime.coprime_dvd_right
      (orderOf_dvd_of_pow_eq_one ?_) ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hm))
    rw [← pow_mul, ← hn, pow_card_eq_one']
  have hP : IsPGroup p (Q ⧸ Subgroup.center Q) := fun g => by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
    exact ⟨k, by rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact hc g⟩
  have : Nontrivial (Q ⧸ Subgroup.center Q) := nontrivial_of_ne _ _ hab
  have hZ := hP.center_nontrivial
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (Q ⧸ Subgroup.center Q))
    with h1 | h1
  · exact (Subgroup.nontrivial_iff_ne_bot _).mp hZ h1
  · exact hab (Subgroup.mem_center_iff.mp (h1 ▸ Subgroup.mem_top a) b).symm

private theorem finrank_adjoin_ge {K E : Type*} [Field K] [Ring E] [Algebra K E] [Nontrivial E]
    [FiniteDimensional K E] {k : ℕ} (a b : Fin k → E) (hab : ∀ i j, i ≠ j → Commute (a i) (b j))
    (hne : ∀ i, ¬ Commute (a i) (b i)) (s : Finset (Fin k)) :
    s.card + 1 ≤ Module.finrank K (Algebra.adjoin K (a '' s)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.coe_empty, Set.image_empty, Algebra.adjoin_empty, Subalgebra.finrank_bot]
    simp
  | insert j s hj ih =>
    rw [Finset.card_insert_of_notMem hj]
    have hlt : Algebra.adjoin K (a '' s) < Algebra.adjoin K (a '' ↑(insert j s)) := by
      refine lt_of_le_of_ne (Algebra.adjoin_mono (Set.image_mono (by simp))) fun h => hne j ?_
      have hj' : a j ∈ Algebra.adjoin K (a '' s) := h ▸ Algebra.subset_adjoin ⟨j, by simp, rfl⟩
      have hle : Algebra.adjoin K (a '' s) ≤ Subalgebra.centralizer K {b j} := by
        refine Algebra.adjoin_le ?_
        rintro _ ⟨i, hi, rfl⟩
        rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
        rintro _ rfl
        exact (hab i j (by rintro rfl; exact hj hi)).eq.symm
      exact ((Subalgebra.mem_centralizer_iff K).mp (hle hj') (b j) rfl).symm
    have := Submodule.finrank_lt_finrank_of_lt (Subalgebra.toSubmodule.strictMono hlt)
    change Module.finrank K (Algebra.adjoin K (a '' s)) <
      Module.finrank K (Algebra.adjoin K (a '' ↑(insert j s))) at this
    omega

private theorem not_dvd_card_closure {G : Type*} [Group G] [Finite G] {k : ℕ} (x : Fin k → G)
    (p : ℕ) [hp : Fact p.Prime] (hx : ∀ i, p.Coprime (orderOf (x i)))
    [hA : IsMulCommutative (Subgroup.closure (Set.range x))] :
    ¬ p ∣ Nat.card (Subgroup.closure (Set.range x)) := by
  intro hdvd
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hN : ∀ a ∈ Subgroup.closure (Set.range x), a ^ ∏ i, orderOf (x i) = 1 := by
    intro a ha
    induction ha using Subgroup.closure_induction with
    | mem a h =>
      obtain ⟨i, rfl⟩ := h
      exact orderOf_dvd_iff_pow_eq_one.mp (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
    | one => exact one_pow _
    | mul a b ha hb iha ihb =>
      have hab : Commute a b := congrArg Subtype.val (mul_comm (⟨a, ha⟩ : Subgroup.closure _) ⟨b, hb⟩)
      rw [hab.mul_pow, iha, ihb, one_mul]
    | inv a ha ih => rw [inv_pow, ih, inv_one]
  have h1 : orderOf g ∣ ∏ i, orderOf (x i) :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by rw [Subgroup.coe_pow, hN _ g.2]; rfl))
  rw [hg] at h1
  exact hp.out.one_lt.ne' ((Nat.Coprime.prod_right fun i _ => hx i).eq_one_of_dvd h1)

private theorem false_of_four_components {K : Type} [Field K] [Finite K] {ι : Type} [Fintype ι]
    [DecidableEq ι] (hι : Fintype.card ι ≤ 4) {Y : Subgroup (GL ι K)} {P : Fin 4 → Subgroup Y}
    (hP : ∀ i, CFSG.IsComponent (P i)) (hinj : Function.Injective P) : False := by
  have : Fact (ringChar K).Prime := ⟨CharP.prime_ringChar K⟩
  choose x y hxy hcop using fun i => exists_noncomm_coprime (hP i).1 (ringChar K)
  have hc : ∀ i j, i ≠ j → ∀ a ∈ P i, ∀ b ∈ P j, a * b = b * a := fun i j h a ha b hb => by
    have h1 := Subgroup.commutator_mem_commutator ha hb
    rwa [((CFSG.LocalCores.distinct_components_commute (hP i) (hP j)).resolve_left (hinj.ne h)),
      Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
  set A := Subgroup.closure (Set.range fun i => (x i : Y))
  have : IsMulCommutative A := Subgroup.isMulCommutative_closure (by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hij
    exact hc i j (by rintro rfl; exact hij rfl) _ (x i).2 _ (x j).2)
  have := isReduced_glAdjAlg A (not_dvd_card_closure _ (ringChar K) fun i => by
    rw [Subgroup.orderOf_coe]; exact hcop i)
  let m : Y → Matrix ι ι K := fun g => ((g : GL ι K) : Matrix ι ι K)
  have hm : ∀ a b : Y, a * b = b * a ↔ Commute (m a) (m b) := fun a b =>
    ⟨fun h => by show m a * m b = m b * m a; simpa [m] using congrArg m h,
     fun h => Subtype.ext (Units.ext (by simpa [m] using h.eq))⟩
  have hne : ∀ i, ¬ Commute (m (x i)) (m (y i)) := fun i h =>
    hxy i (Subtype.ext ((hm _ _).mpr h))
  have : Nontrivial (Matrix ι ι K) := nontrivial_of_ne _ _ (hne 0)
  have h2 := finrank_adjoin_ge (K := K) (fun i => m (x i)) (fun i => m (y i))
    (fun i j h => (hm _ _).mp (hc i j h _ (x i).2 _ (y j).2)) hne Finset.univ
  have h3 : Algebra.adjoin K ((fun i => m (x i)) '' ↑(Finset.univ : Finset (Fin 4))) ≤
      glAdjAlg A := Algebra.adjoin_mono (by
    rintro _ ⟨i, -, rfl⟩
    exact ⟨⟨x i, Subgroup.subset_closure ⟨i, rfl⟩⟩, rfl⟩)
  have h4 : Module.finrank K (Algebra.adjoin K
      ((fun i => m (x i)) '' ↑(Finset.univ : Finset (Fin 4)))) ≤ Module.finrank K (glAdjAlg A) :=
    Submodule.finrank_mono (Subalgebra.toSubmodule.monotone h3)
  have h5 := finrank_le_of_isReduced (glAdjAlg A)
  simp only [Finset.card_univ, Fintype.card_fin] at h2
  omega

private theorem mem_map_conj {G : Type*} [Group G] (Q : Subgroup G) (g x : G) :
    x ∈ Q.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ Q := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

private theorem inv_mul_mem_normalizer {G : Type*} [Group G] {Q : Subgroup G} {g h : G}
    (hgh : Q.map (MulAut.conj g).toMonoidHom = Q.map (MulAut.conj h).toMonoidHom) :
    g⁻¹ * h ∈ Subgroup.normalizer (Q : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro z
  calc z ∈ Q ↔ h⁻¹ * (h * z * h⁻¹) * h ∈ Q := by rw [show h⁻¹ * (h * z * h⁻¹) * h = z by group]
    _ ↔ h * z * h⁻¹ ∈ Q.map (MulAut.conj h).toMonoidHom := (mem_map_conj _ _ _).symm
    _ ↔ g⁻¹ * (h * z * h⁻¹) * g ∈ Q := by rw [← hgh, mem_map_conj]
    _ ↔ g⁻¹ * h * z * (g⁻¹ * h)⁻¹ ∈ Q := by
      rw [show g⁻¹ * (h * z * h⁻¹) * g = g⁻¹ * h * z * (g⁻¹ * h)⁻¹ by group]

private theorem card_quotient_normalizer_le {K : Type} [Field K] [Finite K] {ι : Type}
    [Fintype ι] [DecidableEq ι] (hι : Fintype.card ι ≤ 4) {Y : Subgroup (GL ι K)}
    {Q : Subgroup Y} (hQ : CFSG.IsComponent Q) :
    Nat.card (Y ⧸ Subgroup.normalizer (Q : Set Y)) ≤ 3 := by
  by_contra h
  push Not at h
  set N := Subgroup.normalizer (Q : Set Y)
  let c : Fin 4 → Y ⧸ N := (Finite.equivFin (Y ⧸ N)).symm ∘ Fin.castLE h
  have hc : Function.Injective c := (Finite.equivFin _).symm.injective.comp (Fin.castLE_injective h)
  refine false_of_four_components hι
    (P := fun i => Q.map (MulAut.conj (c i).out).toMonoidHom)
    (fun i => CFSG.LocalCores.isComponent_map_mulEquiv _ hQ) fun i j hij => hc ?_
  rw [← QuotientGroup.out_eq' (c i), ← QuotientGroup.out_eq' (c j), QuotientGroup.eq]
  exact inv_mul_mem_normalizer hij

theorem normal_of_isComponent {K : Type} [Field K] [Finite K] {ι : Type} [Fintype ι]
    [DecidableEq ι] (hι : Fintype.card ι ≤ 4) {Y : Subgroup (GL ι K)} (hY : Group.IsPerfect Y)
    {Q : Subgroup Y} (hQ : CFSG.IsComponent Q) : Q.Normal := by
  have : Group.IsPerfect Y := hY
  rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff]
  intro g _
  have h := CFSG.ClassicalInvolution.RouteD.Gaps.perfect_smul_eq_of_card_le_four
    ((card_quotient_normalizer_le hι hQ).trans (by norm_num)) g
    (QuotientGroup.mk 1 : Y ⧸ Subgroup.normalizer (Q : Set Y))
  rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, QuotientGroup.eq, mul_one] at h
  exact inv_mem_iff.mp h

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
