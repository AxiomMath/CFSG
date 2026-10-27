module

public import CFSG.LocalAnalysis.EvenBN.GMSK.FixedRootDatum
import CFSG.LocalAnalysis.EvenBN.GMSK.LayerRankOne
public import CFSG.LocalAnalysis.EvenBN.GMSK.ConsumerSections
import CFSG.LocalAnalysis.EvenBN.GMS.NormalForms
import CFSG.LocalAnalysis.EvenBN.TwoF4.BenderOutcomesExclusions
import CFSG.LocalAnalysis.EvenBN.Common.SL2TorusNine
import CFSG.LocalAnalysis.SteinbergCDEvenLinearThreeSemilinearFixed
import CFSG.RankThree.PartOne.AUTSL.Interface
import CFSG.LocalAnalysis.SteinbergBKOddNormalQuotientStandard
public import CFSG.LocalAnalysis.ComponentInitial.StandardBasics
import CFSG.Walter.PSL2Facts.Even

public section

namespace CFSG.LocalAnalysis.EvenBN.Sp4

namespace BothTrivialLayer

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis
open scoped MatrixGroups

@[expose] def SmallSurvivorsNoElementary : Prop :=
  (∀ (D : Type) [Group D] [Finite D],
    (NativeSporadic.IsSporadic D .J1 ∨ NativeSporadic.IsSporadic D .M12 ∨
      Nonempty (D ≃* alternatingGroup (Fin 7)) ∨ LieModel D .PSL 2 5 2 ∨
      LieModel D .PSL 3 5 1 ∨ LieModel D .PSU 3 5 1) →
    ∀ E : Subgroup D, (∀ x ∈ E, x * x = 1) → Nat.card E < 2 ^ 4) ∧
  (∀ (D : Type) [Group D], LieModel D .G2 0 3 1 →
    ∀ E : Subgroup D, (∀ x ∈ E, x * x = 1) → Nat.card E < 2 ^ 6)

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag in
theorem false_of_lieModel_PSL3 {H : Type} [Group H] [Finite H] {D : Subgroup H} [D.Normal]
    {a : H} (haa : a * a = 1) {n : ℕ} (hn1 : 1 ≤ n) (hn : LieModel D .PSL 3 2 n)
    (hnt : ∃ d ∈ D, a⁻¹ * d * a ≠ d) {J : Subgroup H} (hJD : J ≤ D)
    (hJa : J ≤ centralizer ({a} : Set H)) {k : Type} [Field k] [Finite k]
    (hk : Nat.card k = 2 ^ n) (ψ : J ≃* SL(2, k)) {E : Subgroup H} (hED : E ≤ D)
    (hE : ∀ x ∈ E, x * x = 1) (hcard : Nat.card E = 2 ^ (2 * n))
    (haE : a ∈ normalizer (E : Set H)) : False := by
  obtain ⟨K, hF, hfin, hK, ⟨e⟩⟩ :=
    CFSG.RankThree.PartOne.AUTSL.exists_projectiveSL_equiv_of_lieModel hn
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hn1 hK
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  set α : MulAut D := MulAut.conjNormal a with hα
  set y : MulAut (projectiveSL 3 K) := (e.symm.trans α).trans e with hy
  have hyapp : ∀ d : D, y (e d) = e (α d) := fun d => by simp [hy]
  have hαapp : ∀ d : D, ((α d : D) : H) = a * d * a⁻¹ := fun d => rfl
  have hy2 : y ^ 2 = 1 := by
    refine MulEquiv.ext fun p => ?_
    obtain ⟨d, rfl⟩ := e.surjective p
    rw [sq, MulAut.mul_apply, hyapp, hyapp, MulAut.one_apply, e.apply_eq_iff_eq,
      Subtype.ext_iff, hαapp, hαapp, hainv]
    calc a * (a * (d : H) * a) * a = (a * a) * d * (a * a) := by group
      _ = d := by rw [haa, one_mul, mul_one]
  have hy1 : y ≠ 1 := by
    intro h1
    obtain ⟨d, hd, hda⟩ := hnt
    apply hda
    have h2 : y (e ⟨d, hd⟩) = e ⟨d, hd⟩ := by rw [h1, MulAut.one_apply]
    rw [hyapp, e.apply_eq_iff_eq, Subtype.ext_iff, hαapp] at h2
    rw [hainv]
    calc a * d * a = a * d * a⁻¹ := by rw [hainv]
      _ = d := h2
  set E' : Subgroup (projectiveSL 3 K) := (E.subgroupOf D).map e.toMonoidHom with hE'
  have hE'2 : ∀ x ∈ E', x ^ 2 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
    exact Subtype.ext (by rw [sq]; exact hE _ (mem_subgroupOf.mp hx))
  have hE'card : Nat.card E' = Nat.card K ^ 2 := by
    rw [hE', card_map_of_injective e.injective, Nat.card_congr (subgroupOfEquivOfLe hED).toEquiv,
      hcard, hK, ← pow_mul, mul_comm]
  have hyE' : ∀ x ∈ E', y x ∈ E' := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨α x, mem_subgroupOf.mpr ?_, (hyapp x).symm⟩
    rw [hαapp]
    exact (mem_normalizer_iff.mp haE _).mp (mem_subgroupOf.mp hx)
  by_cases hsemi : y ∈ semilinearAutGroup 3 K
  ·
    obtain ⟨A, σ, ε, hε, hyeq⟩ := (automorphism_generation (K := K) (n := 3) le_rfl).2 y
    have hε0 : ε = 0 := by
      rcases (show ε = 0 ∨ ε = 1 by omega) with h | h
      · exact h
      · exfalso
        rw [h, pow_one] at hyeq
        apply ProjectivePlane.dualAut_not_mem_semilinearAutGroup (K := K) (n := 3) le_rfl
        have h3 : dualAut 3 K = (conjAut 3 K A * fieldAut 3 K σ)⁻¹ * y := by
          rw [hyeq]; group
        rw [h3]
        exact mul_mem (inv_mem (mul_mem (linearAutGroup_le_semilinearAutGroup
          (conjAut_mem_linearAutGroup A)) (fieldAut_mem_semilinearAutGroup σ))) hsemi
    rw [hε0, pow_zero, mul_one] at hyeq
    have hord : orderOf (conjAut 3 K A * fieldAut 3 K σ) = 2 := by
      rw [← hyeq]
      exact orderOf_eq_prime hy2 hy1
    obtain ⟨-, -, -, -, hno⟩ :=
      SteinbergCD.characteristic_two_linear_three_semilinear_involution_fixed_order
        K A σ hord
    set J' : Subgroup (projectiveSL 3 K) := (J.subgroupOf D).map e.toMonoidHom with hJ'
    have hJ'fix : J' ≤ CFSG.LocalAnalysis.SteinbergCD.semilinearFixed K A σ := by
      rintro _ ⟨x, hx, rfl⟩
      rw [CFSG.LocalAnalysis.SteinbergCD.semilinearFixed, TauCeti.mem_fixedSubgroup]
      change (conjAut 3 K A * fieldAut 3 K σ) (e x) = e x
      rw [← hyeq, hyapp, e.apply_eq_iff_eq]
      apply Subtype.ext
      rw [hαapp]
      have hc := mem_centralizer_singleton_iff.mp (hJa (mem_subgroupOf.mp hx))
      calc a * (x : H) * a⁻¹ = x * a * a⁻¹ := by rw [hc]
        _ = x := by group
    have hk' : Nat.card K = 2 ^ n := hK
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let eJ : J' ≃* SL(2, K) :=
      ((J.subgroupOf D).equivMapOfInjective e.toMonoidHom e.injective).symm.trans
        ((subgroupOfEquivOfLe hJD).trans (ψ.trans
          ((CFSG.ClassicalModels.specialLinearFieldEquiv
            (CFSG.ClassicalModels.finiteFieldEquivGaloisField k 2 n (by omega) hk) (Fin 2)).trans
          (CFSG.ClassicalModels.specialLinearFieldEquiv
            (CFSG.ClassicalModels.finiteFieldEquivGaloisField K 2 n (by omega) hk') (Fin 2)).symm)))
    exact (hno J' hJ'fix).false eJ
  · exact TwoF4.L3.false_of_not_mem_semilinear hE'2 hE'card hsemi hyE'

theorem conjNormal_not_mem_range {H : Type} [Group H] [Finite H] {N A : Subgroup H} [N.Normal]
    {t : H} (hC : centralizer (N : Set H) = ⊥) (ht1 : t ≠ 1) (ht : t * t = 1) (hAN : A ≤ N)
    (hAt : A ≤ centralizer ({t} : Set H)) (hAnab : ∃ x y : A, x * y ≠ y * x) {F : Type}
    [Field F] [Finite F] [CharP F 2] (ψ : N ≃* SL(2, F)) :
    (MulAut.conjNormal t : MulAut N) ∉ (MulAut.conj : N →* MulAut N).range := by
  rintro ⟨d, hd⟩
  have hdt : ∀ x : N, (d : H) * x * (d : H)⁻¹ = t * x * t⁻¹ := fun x => by
    have h1 := congrArg (fun β : MulAut N => ((β x : N) : H)) hd
    simpa [MulAut.conj_apply, MulAut.conjNormal_apply] using h1
  have htd : t = d := by
    have hmem : (d : H)⁻¹ * t ∈ centralizer (N : Set H) := by
      rw [mem_centralizer_iff]
      intro x hx
      have h1 := hdt ⟨x, hx⟩
      calc x * ((d : H)⁻¹ * t) = (d : H)⁻¹ * ((d : H) * x * (d : H)⁻¹) * t := by group
        _ = (d : H)⁻¹ * (t * x * t⁻¹) * t := by rw [h1]
        _ = (d : H)⁻¹ * t * x := by group
    rw [hC, mem_bot] at hmem
    calc t = (d : H) * ((d : H)⁻¹ * t) := by group
      _ = d := by rw [hmem, mul_one]
  have htN : t ∈ N := htd ▸ d.2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz2 : IsPGroup 2 (zpowers (⟨t, htN⟩ : N)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime (by rw [sq]; exact Subtype.ext ht) fun h => ht1 (congrArg Subtype.val h)
  obtain ⟨P, hP⟩ := hz2.exists_le_sylow
  set S : Subgroup H := (P : Subgroup N).map N.subtype with hS
  have hSN : S ≤ N := map_subtype_le _
  have hScard : Nat.card S = Nat.card F := by
    rw [hS, card_map_of_injective N.subtype_injective]
    exact Common.card_sylow_two_eq ψ P
  have htS : t ∈ S := ⟨⟨t, htN⟩, hP (mem_zpowers _), rfl⟩
  have hNt := Common.inf_centralizer_eq_of_mem_of_card ψ hSN hScard htS ht1
  have hScomm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := by
    intro x hx y hy
    by_cases hx1 : x = 1
    · rw [hx1, one_mul, mul_one]
    have h1 := Common.inf_centralizer_eq_of_mem_of_card ψ hSN hScard hx hx1
    have h2 : y ∈ N ⊓ centralizer ({x} : Set H) := h1 ▸ hy
    exact (mem_centralizer_singleton_iff.mp h2.2).symm
  obtain ⟨x, y, hxy⟩ := hAnab
  apply hxy
  have hxS : (x : H) ∈ S := hNt ▸ ⟨hAN x.2, hAt x.2⟩
  have hyS : (y : H) ∈ S := hNt ▸ ⟨hAN y.2, hAt y.2⟩
  exact Subtype.ext (hScomm _ hxS _ hyS)

open CFSG.LocalAnalysis.ComponentInitial in
theorem exists_sl2_of_lieModel {N : Type} [Group N] {m : ℕ} (hm : 1 ≤ m)
    (hL : LieModel N .PSL 2 2 m) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2), Nat.card F = 2 ^ m ∧
      Nonempty (N ≃* SL(2, F)) := by
  obtain ⟨F, _, _, hF, ⟨eN⟩⟩ : ∃ (F : Type) (_ : Field F) (_ : Finite F),
      Nat.card F = 2 ^ m ∧ Nonempty (N ≃* CFSG.Assembly.LowTwoRank.StatedProj
        (CFSG.Assembly.LowTwoRank.StatedSL 2 F)) := by
    rcases hL with ⟨-, -, h⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact h
    all_goals exact absurd h0 (by norm_num)
  have : CharP F 2 := finite_field_prime_power_characteristic Nat.prime_two hm hF
  exact ⟨F, inferInstance, inferInstance, inferInstance, hF, ⟨eN.trans
    ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm.trans
      CFSG.Walter.psl2MulEquivSL2OfCharTwo)⟩⟩

open CFSG.LocalAnalysis.ComponentInitial in
theorem alternative_two_of_lieModel {H : Type} [Group H] {A N : Subgroup H} [N.Normal]
    {t : H} {n : ℕ} (hn : 2 ≤ n) (htt : t * t = 1) (hAN : A ≤ N)
    (hAt : A ≤ centralizer ({t} : Set H)) {k : Type} [Field k] [Fintype k]
    (hk : Fintype.card k = 2 ^ n) (αA : A ≃* SL(2, k)) (hL : LieModel N .PSL 2 2 (2 * n))
    (hout : (MulAut.conjNormal t : MulAut N) ∉ (MulAut.conj : N →* MulAut N).range) :
    ∃ (k₂ : Type) (_ : Field k₂) (_ : Fintype k₂), Fintype.card k₂ = (2 ^ n) ^ 2 ∧
      ∃ ψ : N ≃* SL(2, k₂),
        (∀ x y : N, (y : H) = t⁻¹ * x * t →
          ((ψ y : SL(2, k₂)) : Matrix (Fin 2) (Fin 2) k₂) =
            (ψ x : Matrix (Fin 2) (Fin 2) k₂).map (fun c => c ^ 2 ^ n)) ∧
        ∀ g : SL(2, k₂), g ∈ (A.subgroupOf N).map ψ.toMonoidHom ↔
          ∀ i j, (g : Matrix (Fin 2) (Fin 2) k₂) i j ^ 2 ^ n =
            (g : Matrix (Fin 2) (Fin 2) k₂) i j := by
  obtain ⟨F, _, _, hF, ⟨eN⟩⟩ : ∃ (F : Type) (_ : Field F) (_ : Finite F),
      Nat.card F = 2 ^ (2 * n) ∧ Nonempty (N ≃* CFSG.Assembly.LowTwoRank.StatedProj
        (CFSG.Assembly.LowTwoRank.StatedSL 2 F)) := by
    rcases hL with ⟨-, -, h⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact h
    all_goals exact absurd h0 (by norm_num)
  have : CharP F 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hF
  let ψ₀ : N ≃* SL(2, F) := eN.trans
    ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm.trans
      CFSG.Walter.psl2MulEquivSL2OfCharTwo)
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  let α : MulAut N := MulAut.conjNormal t
  have hα : ∀ x : N, (α x : H) = t⁻¹ * x * t := by
    intro x
    change ((MulAut.conjNormal t) x : H) = _
    rw [MulAut.conjNormal_apply, htinv]
  have hαα : α * α = 1 := by
    ext x
    rw [MulAut.mul_apply, MulAut.one_apply, hα, hα]
    calc t⁻¹ * (t⁻¹ * (x : H) * t) * t = (t⁻¹ * t⁻¹) * x * (t * t) := by group
      _ = x := by rw [htinv, htt, one_mul, mul_one]
  obtain ⟨e', hfe', ψ, hψ⟩ := GMS.exists_frobenius_normal_form (by omega) hF ψ₀ α hαα hout
  have hen : e' = n := by omega
  subst hen
  let Fα : Subgroup N := (centralizer ({t} : Set H)).subgroupOf N
  have hFα : ∀ x : N, x ∈ Fα ↔ α x = x := by
    intro x
    rw [mem_subgroupOf, mem_centralizer_singleton_iff]
    constructor
    · intro hx
      apply Subtype.ext
      rw [hα]
      calc t⁻¹ * (x : H) * t = t⁻¹ * (t * x) := by rw [mul_assoc, hx]
        _ = x := by group
    · intro hx
      have h1 : t⁻¹ * (x : H) * t = x := by rw [← hα, hx]
      calc (x : H) * t = t * (t⁻¹ * x * t) := by group
        _ = t * x := by rw [h1]
  have hX' : ∀ g ∈ Fα.map ψ.toMonoidHom, ∀ i j,
      (g : Matrix (Fin 2) (Fin 2) F) i j ^ 2 ^ e' = (g : Matrix (Fin 2) (Fin 2) F) i j := by
    rintro _ ⟨x, hx, rfl⟩ i j
    have h1 := congrArg (fun m : Matrix (Fin 2) (Fin 2) F => m i j) (hψ x)
    simp only [Matrix.map_apply] at h1
    rw [(hFα x).mp hx] at h1
    exact h1.symm
  have hcardX : Nat.card (Fα.map ψ.toMonoidHom) ≤ Nat.card SL(2, k) :=
    GMS.card_le_of_frobenius_fixed (k := k) (by omega) (by rw [hF]) (by
      rw [Nat.card_eq_fintype_card, hk]) _ hX'
  have hP : (A.subgroupOf N).map ψ.toMonoidHom = Fα.map ψ.toMonoidHom := by
    apply eq_of_le_of_card_ge
    · exact map_mono fun x hx => mem_subgroupOf.mpr (hAt (mem_subgroupOf.mp hx))
    · calc Nat.card (Fα.map ψ.toMonoidHom) ≤ Nat.card SL(2, k) := hcardX
        _ = Nat.card A := (Nat.card_congr αA.toEquiv).symm
        _ = Nat.card (A.subgroupOf N) :=
          (Nat.card_congr (subgroupOfEquivOfLe hAN).toEquiv).symm
        _ = Nat.card ((A.subgroupOf N).map ψ.toMonoidHom) :=
          (card_map_of_injective ψ.injective).symm
  let _ : Fintype F := Fintype.ofFinite _
  refine ⟨F, inferInstance, inferInstance, ?_, ψ, ?_, ?_⟩
  · rw [← Nat.card_eq_fintype_card, hF]
    ring
  · intro x y hyx
    have hy : y = α x := Subtype.ext (by rw [hα]; exact hyx)
    rw [hy]
    exact hψ x
  · intro g
    rw [hP]
    constructor
    · exact hX' g
    · intro hg
      refine ⟨ψ.symm g, (hFα _).mpr (ψ.injective ?_), ψ.apply_symm_apply g⟩
      apply Subtype.ext
      rw [hψ, ψ.apply_symm_apply]
      ext i j
      exact hg i j

theorem card_map_of_injOn {G H : Type*} [Group G] [Group H] (f : G →* H) {V : Subgroup G}
    (h : Set.InjOn f (V : Set G)) : Nat.card (V.map f) = Nat.card V := by
  rw [← SetLike.coe_sort_coe, Subgroup.coe_map, Nat.card_image_of_injOn h]
  rfl

theorem isPGroup_of_mul_self {G : Type*} [Group G] {V : Subgroup G} (hV : ∀ v ∈ V, v * v = 1) :
    IsPGroup 2 V := fun v => ⟨1, by
  rw [pow_one, sq]
  exact Subtype.ext (hV _ v.2)⟩

theorem not_two_dvd_relIndex_of_sylow {G : Type*} [Group G] [Finite G] {C : Subgroup G}
    (hC : ∀ S : Sylow 2 C, Nat.card S = 2) {t : G} (htC : t ∈ C) (ht : orderOf t = 2) :
    ¬ 2 ∣ (zpowers t).relIndex C := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set u : C := ⟨t, htC⟩
  have hu : orderOf u = 2 := by rw [← Subgroup.orderOf_coe]; exact ht
  have hz2 : IsPGroup 2 (zpowers u) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu, pow_one])
  obtain ⟨S, hS⟩ := hz2.exists_le_sylow
  have hSz : zpowers u = (S : Subgroup C) :=
    eq_of_le_of_card_ge hS (by rw [hC S, Nat.card_zpowers, hu])
  have hsub : (zpowers t).subgroupOf C = (S : Subgroup C) := by
    rw [← hSz, show zpowers t = (zpowers u).map C.subtype from
      (MonoidHom.map_zpowers C.subtype u).symm, Subgroup.subgroupOf,
      comap_map_eq_self_of_injective C.subtype_injective]
  rw [Subgroup.relIndex, hsub]
  exact Sylow.not_dvd_index S

@[expose] def ClosureSelection {M : Type} [Group M] [Finite M] (A : Subgroup M) {k : Type}
    [Field k] (α : A ≃* SL(2, k)) (τ : M) (V : Subgroup M) (n : ℕ) : Prop :=
  let R := CFSG.Open.standardComponentOddCore M
  let π : M →* M ⧸ R := QuotientGroup.mk' R
  centralizer (CFSG.layer (M ⧸ R) : Set (M ⧸ R)) = ⊥ ∧
    CFSG.layer (M ⧸ R) = (normalClosure (A : Set M)).map π ∧
    V.map π ≤ CFSG.layer (M ⧸ R) ∧
    (∀ Q : Subgroup M, IsPGroup 2 Q → Set.InjOn π (Q : Set M)) ∧
    Xor
      (∃ ψ : CFSG.layer (M ⧸ R) ≃* SL(2, k) × SL(2, k),
        (∀ (a : A) (x : CFSG.layer (M ⧸ R)), (x : M ⧸ R) = π a → ψ x = (α a, α a)) ∧
        ∀ x y : CFSG.layer (M ⧸ R), (y : M ⧸ R) = (π τ)⁻¹ * x * π τ → ψ y = (ψ x).swap)
      (∃ (k₂ : Type) (_ : Field k₂) (_ : Fintype k₂), Fintype.card k₂ = (2 ^ n) ^ 2 ∧
        ∃ ψ : CFSG.layer (M ⧸ R) ≃* SL(2, k₂),
          (∀ x y : CFSG.layer (M ⧸ R), (y : M ⧸ R) = (π τ)⁻¹ * x * π τ →
            ((ψ y : SL(2, k₂)) : Matrix (Fin 2) (Fin 2) k₂) =
              (ψ x : Matrix (Fin 2) (Fin 2) k₂).map (fun c => c ^ 2 ^ n)) ∧
          ∀ g : SL(2, k₂),
            g ∈ ((A.map π).subgroupOf (CFSG.layer (M ⧸ R))).map ψ.toMonoidHom ↔
              ∀ i j, (g : Matrix (Fin 2) (Fin 2) k₂) i j ^ 2 ^ n =
                (g : Matrix (Fin 2) (Fin 2) k₂) i j)

theorem closure_layer_selection (hsel : GMSK.FixedRootSelector fun D _ => Catalog D)
    (hsmall : SmallSurvivorsNoElementary)
    {M : Type} [Group M] [Finite M] (hM : CFSG.SectionRank.IsKGroupCat M)
    {A : Subgroup M} {n : ℕ} (hn : 2 ≤ n) {k : Type} [Field k] [Fintype k]
    (hk : Fintype.card k = 2 ^ n) (α : A ≃* SL(2, k)) {τ : M} (hτ : orderOf τ = 2)
    (hAτ : A ≤ centralizer ({τ} : Set M))
    (hAn : (A.subgroupOf (centralizer ({τ} : Set M))).Normal)
    (hsyl : ∃ S : Sylow 2 ↥(centralizer (A : Set M) ⊓ centralizer ({τ} : Set M)),
      (S : Subgroup _).map (centralizer (A : Set M) ⊓ centralizer ({τ} : Set M)).subtype =
        zpowers τ)
    {V : Subgroup M} (hV2 : ∀ v ∈ V, v * v = 1) (hVcard : Nat.card V = (2 ^ n) ^ 2)
    (hVA : V ≤ normalClosure (A : Set M)) (hτV : τ ∈ normalizer (V : Set M)) :
    ClosureSelection A α τ V n := by
  unfold ClosureSelection
  intro R π
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR : Odd (Nat.card R) := GMSK.odd_card_standardComponentOddCore M
  have h2 : (2 : k) = 0 := GMSK.two_eq_zero_of_card (by omega) hk
  have hk4 : 4 ≤ Fintype.card k :=
    hk ▸ (Nat.pow_le_pow_right (by norm_num) hn : 2 ^ 2 ≤ 2 ^ n)
  have : IsSimpleGroup SL(2, k) := GMSK.sl2_isSimpleGroup h2 hk4
  have : IsSimpleGroup A := α.isSimpleGroup
  have hnab : ∃ x y : A, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := GMSK.sl2_exists_mul_ne (K := k)
    exact ⟨α.symm x, α.symm y, fun e => hxy (by simpa using congrArg α e)⟩
  have hE : ∃ E : Subgroup M, E ≤ A ∧ CFSG.Assembly.IsElemAbelian 2 E ∧ Nat.card E = 4 := by
    obtain ⟨E, hE, hE4⟩ := GMSK.exists_elementaryAbelian_four h2
      (hk ▸ pow_dvd_pow 2 hn : 2 ^ 2 ∣ Fintype.card k)
    set f : Multiplicative k →* M := A.subtype.comp (α.symm.toMonoidHom.comp (GMSK.sl2Upper k))
    have hf : Function.Injective f :=
      A.subtype_injective.comp (α.symm.injective.comp GMSK.sl2Upper_injective)
    have hEf : CFSG.IsElementaryAbelian 2 (E.map f) := CFSG.IsElementaryAbelian.map f
    refine ⟨E.map f, ?_, ⟨hEf.toIsMulCommutative, fun x hx =>
      CFSG.elemPow_eq_one_of_isElementaryAbelian x hx⟩, by rw [card_map_of_injective hf, hE4]⟩
    rintro _ ⟨x, -, rfl⟩
    exact (α.symm (GMSK.sl2Upper k x)).2
  obtain ⟨hinjA, hinj2, hθτ, -, -, hAθ, -, -, -, -, -, -⟩ :=
    CFSG.LocalAnalysis.SteinbergBK.simple_involution_centralizer_odd_normal_quotient_standardness
      hnab hE hτ hAτ hAn hsyl R hR
  have hVinj := hinj2 V (isPGroup_of_mul_self hV2)
  have hVcard' : Nat.card (V.map π) = (2 ^ n) ^ 2 := by rw [card_map_of_injOn π hVinj, hVcard]
  let ιA : A ≃* A.map π := MulEquiv.ofBijective (π.subgroupMap A)
    ⟨fun x y hxy => Subtype.ext (hinjA x.2 y.2 (congrArg Subtype.val hxy)),
      π.subgroupMap_surjective A⟩
  have hιA : ∀ a : A, (ιA a : M ⧸ R) = π a := fun _ => rfl
  let αA : A.map π ≃* SL(2, k) := ιA.symm.trans α
  have hαA : ∀ a : A, αA (ιA a) = α a := fun a => by simp [αA]
  have hNC : (normalClosure (A : Set M)).map π =
      normalClosure ((A.map π : Subgroup (M ⧸ R)) : Set (M ⧸ R)) := by
    rw [map_normalClosure _ _ (QuotientGroup.mk'_surjective R), ← coe_map]
  have hVN : V.map π ≤ normalClosure ((A.map π : Subgroup (M ⧸ R)) : Set (M ⧸ R)) :=
    hNC ▸ map_mono hVA
  have hnn : ¬ (A.map π).Normal := by
    intro hN
    have hle : V.map π ≤ A.map π := hVN.trans (normalClosure_le_normal le_rfl)
    have hd := card_dvd_of_le hle
    rw [hVcard', card_map_of_injOn π hinjA, Nat.card_congr α.toEquiv,
      CFSG.CGT.Timmesfeld75.card_sl2, Nat.card_eq_fintype_card, hk] at hd
    have hq0 : 0 < 2 ^ n := by positivity
    have h1 : 2 ^ n ∣ (2 ^ n) ^ 2 - 1 :=
      Nat.dvd_of_mul_dvd_mul_left hq0 (by rw [← pow_two]; exact hd)
    have h3 : 2 ∣ (2 ^ n) ^ 2 - 1 := (dvd_pow_self 2 (by omega)).trans h1
    have h4 : 2 ∣ (2 ^ n) ^ 2 := dvd_pow (dvd_pow_self 2 (by omega)) (by norm_num)
    have h5 : 1 ≤ (2 ^ n) ^ 2 := Nat.one_le_pow _ _ hq0
    omega
  obtain ⟨hstd, hsylq⟩ := GMSK.stdLinearData_odd_quotient hn hk α hτ hAτ hAn hsyl R hR hnn
  have hπτ : π τ ∈ centralizer ((A.map π : Subgroup (M ⧸ R)) : Set (M ⧸ R)) :=
    mem_centralizer_iff.mpr fun x hx => mem_centralizer_singleton_iff.mp (hAθ hx)
  have hodd := not_two_dvd_relIndex_of_sylow hsylq hπτ hθτ
  obtain ⟨-, -, hAL, hDE, hCE, halt, -⟩ := GMSK.oneOrTwoLayer_of_stdLinearData
    (GMSK.standardComponentOddCore_quotient_eq_bot M) hstd hθτ hπτ hodd
  have hττ : π τ * π τ = 1 := by rw [← sq, ← hθτ, pow_orderOf_eq_one]
  have hτ1 : π τ ≠ 1 := fun h => by rw [h, orderOf_one] at hθτ; omega
  refine ⟨by rw [← hDE]; exact hCE, hDE.symm.trans hNC.symm, hDE ▸ hVN, hinj2, ?_⟩
  rw [← hDE]
  set N := normalClosure ((A.map π : Subgroup (M ⧸ R)) : Set (M ⧸ R)) with hNdef
  have hexcl : ∀ (k₂ : Type) (_ : Field k₂) (_ : Fintype k₂), Fintype.card k₂ = (2 ^ n) ^ 2 →
      (N ≃* SL(2, k) × SL(2, k)) → (N ≃* SL(2, k₂)) → False := by
    intro k₂ _ _ hk₂ ψ₁ ψ₂
    have hk₂' : Nat.card k₂ = 2 ^ (2 * n) := by
      rw [Nat.card_eq_fintype_card, hk₂, ← pow_mul, mul_comm]
    exact (GMS.isEmpty_mulEquiv_sl2_prod (k := k) (by omega) hk₂').false (ψ₂.symm.trans ψ₁)
  rcases halt with ⟨⟨hDs, -, hAD, hnt⟩, -⟩ |
    ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, ψ, hψ₁, hψ₂⟩, -⟩
  ·
    have := hDs
    have hCt := (CFSG.LocalAnalysis.ComponentInitial.standard_involution_centralizer_normality
      hstd.isStandard hπτ hθτ).1
    have d := GMSK.fixedRootDatum_of_normal (D := N) hAD.le hθτ hπτ hCt hnt
      (fun P hPC hP => GMSK.card_le_two_of_sylow hsylq hPC hP) hn hk αA
    have hcat : Catalog N :=
      CFSG.SectionRank.catalog_of_isKGroupCat_of_surjective (hM.quotient R) N (MonoidHom.id N)
        Function.surjective_id
    have hsurv := hsel.survivors_of_datum hDs hcat d
    set E' : Subgroup N := (V.map π).subgroupOf N with hE'
    have hE'2 : ∀ x ∈ E', x * x = 1 := by
      intro x hx
      obtain ⟨v, hv, hvx⟩ := mem_subgroupOf.mp hx
      apply Subtype.ext
      rw [coe_mul, ← hvx, ← map_mul, hV2 v hv, map_one]
      rfl
    have hE'card : Nat.card E' = (2 ^ n) ^ 2 := by
      rw [hE', Nat.card_congr (subgroupOfEquivOfLe hVN).toEquiv, hVcard']
    have hq : 2 ^ n < (2 ^ n) ^ 2 := by
      have : 4 ≤ 2 ^ n := (Nat.pow_le_pow_right (by norm_num) hn : 2 ^ 2 ≤ 2 ^ n)
      nlinarith
    have hk' : Nat.card k = 2 ^ n := by rw [Nat.card_eq_fintype_card, hk]
    have hτV' : π τ ∈ normalizer ((V.map π : Subgroup (M ⧸ R)) : Set (M ⧸ R)) :=
      le_normalizer_map π ⟨τ, hτV, rfl⟩
    rcases hsurv with hL2 | hU3 | hL3 | ⟨rfl, hsm⟩ | ⟨rfl, hG2⟩
    ·
      obtain ⟨F, _, _, _, -, ⟨ψ₀⟩⟩ := exists_sl2_of_lieModel (by omega) hL2
      have hnabA : ∃ x y : A.map π, x * y ≠ y * x := by
        obtain ⟨x, y, hxy⟩ := hnab
        exact ⟨ιA x, ιA y, fun e => hxy (ιA.injective (by rw [map_mul, map_mul, e]))⟩
      have hout := conjNormal_not_mem_range hCE hτ1 hττ hAD.le hAθ hnabA ψ₀
      have h2 := alternative_two_of_lieModel hn hττ hAD.le hAθ hk αA hL2 hout
      refine Or.inr ⟨h2, ?_⟩
      rintro ⟨ψ₁, -⟩
      obtain ⟨k₂, _, _, hk₂, ψ₂, -⟩ := h2
      exact hexcl k₂ inferInstance inferInstance hk₂ ψ₁ ψ₂
    ·
      have h1 := TwoF4.card_le_of_lieModel_PSU3 hU3 hE'2
      rw [hE'card] at h1
      exact absurd h1 (not_le.mpr hq)
    ·
      exact (false_of_lieModel_PSL3 hττ (by omega) hL3 hnt hAD.le hAθ hk' αA hVN
        (fun x hx => by
          obtain ⟨v, hv, rfl⟩ := hx
          rw [← map_mul, hV2 v hv, map_one])
        (by rw [hVcard', ← pow_mul, mul_comm]) hτV').elim
    ·
      have := hsmall.1 N hsm E' hE'2
      rw [hE'card] at this
      norm_num at this
    ·
      have := hsmall.2 N hG2 E' hE'2
      rw [hE'card] at this
      norm_num at this
  ·
    let ψ' : N ≃* SL(2, k) × SL(2, k) := ψ.trans (MulEquiv.prodCongr αA αA)
    have hψ' : ∀ x : N, ψ' x = ((αA (ψ x).1), (αA (ψ x).2)) := fun _ => rfl
    have h1 : ∃ ψ : N ≃* SL(2, k) × SL(2, k),
        (∀ (a : A) (x : N), (x : M ⧸ R) = π a → ψ x = (α a, α a)) ∧
        ∀ x y : N, (y : M ⧸ R) = (π τ)⁻¹ * x * π τ → ψ y = (ψ x).swap := by
      refine ⟨ψ', fun a x hxa => ?_, fun x y hyx => ?_⟩
      · have hx : x = ⟨π a, hxa ▸ x.2⟩ := Subtype.ext hxa
        rw [hψ', hx, hψ₁ (π a) ⟨a, a.2, rfl⟩ (hxa ▸ x.2)]
        exact Prod.ext (hαA a) (hαA a)
      · have hy : y = ⟨(π τ)⁻¹ * x * π τ, hyx ▸ y.2⟩ := Subtype.ext hyx
        rw [hψ', hψ', hy, hψ₂ x x.2 (hyx ▸ y.2)]
        rfl
    refine Or.inl ⟨h1, ?_⟩
    rintro ⟨k₂, _, _, hk₂, ψ₂, -⟩
    exact hexcl k₂ inferInstance inferInstance hk₂ ψ' ψ₂

end BothTrivialLayer

end CFSG.LocalAnalysis.EvenBN.Sp4
