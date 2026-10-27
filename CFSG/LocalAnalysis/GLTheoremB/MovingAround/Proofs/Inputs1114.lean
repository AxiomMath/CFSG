module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1114
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1112b
import CFSG.RankThree.PartTwo.KFacts.L34Automizer
import CFSG.RankThree.PartTwo.KFacts.AutPSLOrderThree
import CFSG.HardMathSupport.Solomon.Coordinator.L3BL34

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs1114

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf barAut innerAut barAut_mk)
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open scoped commutatorElement

section Generic

variable {G : Type} [Group G]

theorem mem_centBar_iff_forall {p : ℕ} {X L : Subgroup G} {c : G} :
    c ∈ centBar p X L ↔ c ∈ X ∧ ∃ _ : c ∈ Subgroup.normalizer (L : Set G),
      ∀ l ∈ L, c * l * c⁻¹ * l⁻¹ ∈ GLAPPrimeCoreOf p L := by
  have key : ∀ γ : ↥(Subgroup.normalizer (L : Set G)), barAut p L γ = 1 ↔
      ∀ l ∈ L, (γ : G) * l * (γ : G)⁻¹ * l⁻¹ ∈ GLAPPrimeCoreOf p L := by
    intro γ
    have hN := GLAPPrimeCore.normal p ↥L
    constructor
    · intro h l hl
      have h1 : barAut p L γ (QuotientGroup.mk ⟨l, hl⟩) = QuotientGroup.mk ⟨l, hl⟩ := by
        rw [h]; rfl
      rw [barAut_mk, QuotientGroup.eq] at h1
      have h2 := hN.conj_mem _ (Subgroup.inv_mem _ h1) ⟨l, hl⟩
      refine ⟨_, h2, ?_⟩
      show ((⟨l, hl⟩ : ↥L) : G) * (((L.normalizerMonoidHom γ ⟨l, hl⟩ : ↥L) : G)⁻¹ * l)⁻¹ * l⁻¹ = _
      have e : ((L.normalizerMonoidHom γ ⟨l, hl⟩ : ↥L) : G) = (γ : G) * l * (γ : G)⁻¹ := rfl
      rw [e]
      group
    · intro h
      ext q
      induction q using QuotientGroup.induction_on with
      | H x =>
        rw [barAut_mk, MulAut.one_apply, QuotientGroup.eq]
        obtain ⟨y, hy, hyx⟩ := h (x : G) x.2
        simp only [Subgroup.coe_subtype] at hyx
        have h3 := hN.conj_mem _ (Subgroup.inv_mem _ hy) x⁻¹
        convert h3 using 1
        apply Subtype.ext
        have e : ((L.normalizerMonoidHom γ x : ↥L) : G) = (γ : G) * x * (γ : G)⁻¹ := rfl
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, e, hyx]
        group
  constructor
  · intro hc
    obtain ⟨⟨γ, hγ, hγc⟩, hcX⟩ := Subgroup.mem_inf.1 hc
    subst hγc
    exact ⟨hcX, γ.2, (key γ).1 (MonoidHom.mem_ker.1 hγ)⟩
  · rintro ⟨hcX, hcN, hc⟩
    exact Subgroup.mem_inf.2 ⟨⟨⟨c, hcN⟩, MonoidHom.mem_ker.2 ((key ⟨c, hcN⟩).2 hc), rfl⟩, hcX⟩

theorem inf_eq_bot_of_coprime {p : ℕ} [Fact p.Prime] {X : Type*} [Group X] [Finite X]
    {P N : Subgroup X} (hP : IsPGroup p P) (hN : ¬ p ∣ Nat.card N) : P ⊓ N = ⊥ := by
  obtain ⟨k, hk⟩ := (hP.to_le (inf_le_left : P ⊓ N ≤ P)).exists_card_eq
  have hdvd : Nat.card ↥(P ⊓ N) ∣ Nat.card N := Subgroup.card_dvd_of_le inf_le_right
  rcases k with _ | k
  · exact Subgroup.eq_bot_of_card_eq _ (by rw [hk, pow_zero])
  · exfalso
    apply hN
    rw [hk] at hdvd
    exact (dvd_pow_self p k.succ_ne_zero).trans hdvd

theorem mk_injOn_of_isPGroup {p : ℕ} [Fact p.Prime] {X : Type*} [Group X] [Finite X]
    {N P : Subgroup X} [N.Normal] (hN : ¬ p ∣ Nat.card N) (hP : IsPGroup p P) {x y : X}
    (hx : x ∈ P) (hy : y ∈ P) (hxy : (QuotientGroup.mk x : X ⧸ N) = QuotientGroup.mk y) : x = y := by
  have h1 : x⁻¹ * y ∈ N := QuotientGroup.eq.1 hxy
  have h2 : x⁻¹ * y ∈ P ⊓ N := Subgroup.mem_inf.2 ⟨P.mul_mem (P.inv_mem hx) hy, h1⟩
  rw [inf_eq_bot_of_coprime hP hN, Subgroup.mem_bot] at h2
  exact (inv_mul_eq_one.1 h2)

theorem card_map_mk_of_isPGroup {p : ℕ} [Fact p.Prime] {X : Type*} [Group X] [Finite X]
    {N P : Subgroup X} [N.Normal] (hN : ¬ p ∣ Nat.card N) (hP : IsPGroup p P) :
    Nat.card (P.map (QuotientGroup.mk' N)) = Nat.card P := by
  have hinj : Set.InjOn (QuotientGroup.mk' N) (P : Set X) := fun x hx y hy h =>
    mk_injOn_of_isPGroup hN hP hx hy h
  calc Nat.card (P.map (QuotientGroup.mk' N)) = Nat.card ((QuotientGroup.mk' N) '' (P : Set X)) := rfl
    _ = ((QuotientGroup.mk' N) '' (P : Set X)).ncard := Nat.card_coe_set_eq _
    _ = (P : Set X).ncard := hinj.ncard_image
    _ = Nat.card P := (Nat.card_coe_set_eq _).symm

end Generic

section L34

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem l34_normalizer_transitive {X : Type} [Group X] (hX : IsLThreeFour X) {E : Subgroup X}
    (hE : Nat.card E = 9) {x y : X} (hx : x ∈ E) (hx1 : x ≠ 1) (hy : y ∈ E) (hy1 : y ≠ 1) :
    ∃ n ∈ Subgroup.normalizer (E : Set X), n * x * n⁻¹ = y := by
  obtain ⟨k, _, hk, ⟨φ⟩⟩ := CFSG.HardMathSupport.Solomon.Coordinator.exists_equiv_projectiveSL hX
  have hE' : Nat.card (E.map φ.toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective φ.injective, hE]
  obtain ⟨m, hm, hmxy⟩ := CFSG.RankThree.PartTwo.KFacts.L34.exists_mem_normalizer_conj_eq_of_card_eq_nine
    hk hE' (x := φ x) (y := φ y) ⟨x, hx, rfl⟩ (by simpa using hx1) ⟨y, hy, rfl⟩ (by simpa using hy1)
  have hEE : (E.map φ.toMonoidHom).map φ.symm.toMonoidHom = E := by
    rw [Subgroup.map_map]
    convert Subgroup.map_id E
    ext z; simp
  refine ⟨φ.symm m, ?_, ?_⟩
  · have := CFSG.HardMathSupport.Solomon.Coordinator.mem_normalizer_map φ.symm hm
    rwa [hEE] at this
  · apply φ.injective
    simpa [map_mul, map_inv] using hmxy

theorem l34_mem_of_commute {X : Type} [Group X] (hX : IsLThreeFour X) {E : Subgroup X}
    (hE : Nat.card E = 9) {x : X} (hx : x ∈ E) (hx1 : x ≠ 1) {y : X} (hy : y * x = x * y) :
    y ∈ E := by
  obtain ⟨k, _, hk, ⟨φ⟩⟩ := CFSG.HardMathSupport.Solomon.Coordinator.exists_equiv_projectiveSL hX
  have hE' : Nat.card (E.map φ.toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective φ.injective, hE]
  have hC := CFSG.RankThree.PartTwo.KFacts.L34.centralizer_eq_of_card_eq_nine hk hE'
    (x := φ x) ⟨x, hx, rfl⟩ (by simpa using hx1)
  have hy' : φ y ∈ Subgroup.centralizer ({φ x} : Set (projectiveSL 3 k)) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hy]
  rw [hC] at hy'
  obtain ⟨z, hz, hzy⟩ := hy'
  have : z = y := φ.injective hzy
  rwa [← this]

theorem le_derivedSeries_of_perfect {X : Type*} [Group X] {H : Subgroup X} (hH : ⁅H, H⁆ = H)
    (n : ℕ) : H ≤ derivedSeries X n := by
  induction n with
  | zero => exact le_top
  | succ n ih =>
    rw [derivedSeries_succ, ← hH]
    exact Subgroup.commutator_mono ih ih

theorem l34_perfect_le_inner {X : Type} [Group X] (hX : IsLThreeFour X) {H : Subgroup (MulAut X)}
    (hH : ⁅H, H⁆ = H) : H ≤ (MulAut.conj : X →* MulAut X).range := by
  obtain ⟨k, _, hk, ⟨φ⟩⟩ := CFSG.HardMathSupport.Solomon.Coordinator.exists_equiv_projectiveSL hX
  have : Finite k := CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour.finite_of_card_eq_four hk
  set P := projectiveSL 3 k
  have h3 := (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.linear_higher_schreier
    (K := k) (n := 3) le_rfl).1
  have hD : derivedSeries (MulAut P) 3 ≤ CFSG.ComponentClassification.OuterAutomorphisms.inner P := by
    have hmap := map_derivedSeries_eq
      (QuotientGroup.mk'_surjective (CFSG.ComponentClassification.OuterAutomorphisms.inner P)) 3
    rw [h3] at hmap
    have := (Subgroup.map_eq_bot_iff _).1 hmap
    rwa [QuotientGroup.ker_mk'] at this
  set H' := H.map (MulAut.congr φ).toMonoidHom
  have hH' : ⁅H', H'⁆ = H' := by
    rw [← Subgroup.map_commutator, hH]
  have hle : H' ≤ CFSG.ComponentClassification.OuterAutomorphisms.inner P :=
    (le_derivedSeries_of_perfect hH' 3).trans hD
  intro h hh
  have hmem : MulAut.congr φ h ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner P :=
    hle ⟨h, hh, rfl⟩
  rw [← CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr φ] at hmem
  obtain ⟨h', hh', hhh'⟩ := hmem
  have : h' = h := (MulAut.congr φ).injective hhh'
  rw [← this]
  exact hh'

theorem units_pow_three_of_card_four {k : Type} [Field k] (hk : Nat.card k = 4) (u : kˣ) :
    u ^ 3 = 1 := by
  have : Finite k := CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour.finite_of_card_eq_four hk
  have : Fintype k := Fintype.ofFinite k
  have hcard : Nat.card kˣ = 3 := by
    rw [Nat.card_units, hk]
  rw [← hcard]
  exact pow_card_eq_one'

theorem l34_mul_mem_inner {X : Type} [Group X] (hX : IsLThreeFour X) {α β : MulAut X}
    (hα : α ^ 3 = 1) (hβ : β ^ 3 = 1) {n : ℕ} (hn : ¬ 3 ∣ n) (hαβ : (α * β) ^ n = 1) :
    α * β ∈ (MulAut.conj : X →* MulAut X).range := by
  obtain ⟨k, _, hk, ⟨φ⟩⟩ := CFSG.HardMathSupport.Solomon.Coordinator.exists_equiv_projectiveSL hX
  have : Finite k := CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour.finite_of_card_eq_four hk
  set P := projectiveSL 3 k
  have hlin : ∀ γ : MulAut P, γ ^ 3 = 1 → γ ∈ linearAutGroup 3 k := by
    intro γ hγ
    by_contra hD
    obtain ⟨σ, hσ, -⟩ := CFSG.RankThree.PartTwo.KFacts.linear_order_three_field_descent
      (n := 3) le_rfl γ hγ hD
    have := (CFSG.RankThree.PartTwo.KFacts.eq_frobenius_pow_of_orderOf_eq_three
      (p := 2) (f := 2) Nat.prime_two (by norm_num) (by rw [hk]; norm_num) hσ).1
    omega
  have hcube : ∀ γ ∈ linearAutGroup 3 k, γ ^ 3 ∈ (MulAut.conj : P →* MulAut P).range := by
    intro γ hγ
    obtain ⟨A, rfl⟩ := mem_linearAutGroup_iff.1 hγ
    have hdet : ((A ^ 3 : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k).det = 1 := by
      have h1 : (Matrix.GeneralLinearGroup.det (A ^ 3)) = 1 := by
        rw [map_pow]
        exact units_pow_three_of_card_four hk _
      have h2 := congrArg Units.val h1
      simpa [Matrix.GeneralLinearGroup.val_det_apply] using h2
    set B : Matrix.SpecialLinearGroup (Fin 3) k := ⟨((A ^ 3 : GL (Fin 3) k) : Matrix _ _ k), hdet⟩
    have hB : Matrix.SpecialLinearGroup.toGL B = A ^ 3 := by
      ext i j
      rfl
    refine ⟨proj 3 k B, ?_⟩
    rw [CFSG.RankThree.PartTwo.KFacts.conj_proj_eq_conjAut, hB, map_pow]
  set ψ : MulAut X ≃* MulAut P := MulAut.congr φ
  have hγ : ψ (α * β) ∈ linearAutGroup 3 k := by
    rw [map_mul]
    exact Subgroup.mul_mem _ (hlin _ (by rw [← map_pow, hα, map_one]))
      (hlin _ (by rw [← map_pow, hβ, map_one]))
  have hinn : ψ (α * β) ∈ (MulAut.conj : P →* MulAut P).range := by
    set γ := ψ (α * β) with hγdef
    have hγn : γ ^ n = 1 := by rw [hγdef, ← map_pow, hαβ, map_one]
    have hco : Nat.Coprime 3 (orderOf γ) :=
      Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hγn)
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hn)
    have hn0 : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; exact hn (dvd_zero 3))
    have hpos : 0 < orderOf γ := orderOf_pos_iff.2 (isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn0, hγn⟩)
    rcases Nat.lt_or_ge (orderOf γ) 2 with hlt | hge
    · have hγ1 : γ = 1 := orderOf_eq_one_iff.1 (by omega)
      rw [hγ1]
      exact Subgroup.one_mem _
    · obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hco (by omega)
      have : γ = (γ ^ 3) ^ m := by
        rw [← pow_mul, ← pow_mod_orderOf, hm, pow_one]
      rw [this]
      exact Subgroup.pow_mem _ (hcube γ hγ) m
  have hinn' : ψ (α * β) ∈ (CFSG.ComponentClassification.OuterAutomorphisms.inner X).map
      (MulAut.congr φ).toMonoidHom := by
    rw [CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr φ]
    exact hinn
  obtain ⟨h', hh', hhh'⟩ := hinn'
  have : h' = α * β := ψ.injective hhh'
  rw [← this]
  exact hh'

end L34

section Sylow

variable {G : Type} [Group G]

theorem card_le_nine_of_isPGroup {X : Type} [Group X] [Finite X]
    (hL : IsLThreeFour (X ⧸ GLAPPrimeCore 3 X)) {R : Subgroup X} (hR : IsPGroup 3 R) :
    Nat.card R ≤ 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hN : ¬ 3 ∣ Nat.card (GLAPPrimeCore 3 X) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1
    (CFSG.HardMathSupport.Solomon.LocalBalance.coprime_card_gLAPPrimeCore_aux 3 X)
  rw [← card_map_mk_of_isPGroup hN hR]
  obtain ⟨j, hj⟩ := (hR.map (QuotientGroup.mk' (GLAPPrimeCore 3 X))).exists_card_eq
  have hdvd : Nat.card (R.map (QuotientGroup.mk' (GLAPPrimeCore 3 X))) ∣ 20160 := by
    rw [← CFSG.HardMathSupport.Solomon.UniquenessMaximal.card_eq_of_isLThreeFour hL]
    exact Subgroup.card_subgroup_dvd_card _
  rw [hj] at hdvd ⊢
  have hj2 : j ≤ 2 := by
    by_contra hj2
    have h27 : 3 ^ 3 ∣ 3 ^ j := Nat.pow_dvd_pow 3 (by omega)
    have := h27.trans hdvd
    norm_num at this
  calc 3 ^ j ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hj2
    _ = 9 := by norm_num

theorem exists_mul_mem_normalizer {p : ℕ} [Fact p.Prime] {X : Type} [Group X] [Finite X]
    {N P : Subgroup X} (hP : IsPGroup p P)
    (hPmax : ∀ R : Subgroup X, IsPGroup p R → Nat.card R ≤ Nat.card P)
    {n₁ : X} (hn₁ : GLBConj n₁ P ≤ P ⊔ N) :
    ∃ w ∈ P ⊔ N, n₁ * w ∈ Subgroup.normalizer (P : Set X) := by
  set H := P ⊔ N with hH
  set P' : Subgroup ↥H := P.subgroupOf H
  set Q' : Subgroup ↥H := (GLBConj n₁ P).subgroupOf H
  have hcardP' : Nat.card P' = Nat.card P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : P ≤ H)).toEquiv
  have hP'syl : IsSylowIn p ⊤ P' := by
    refine ⟨le_top, hP.of_equiv (Subgroup.subgroupOfEquivOfLe (le_sup_left : P ≤ H)).symm, ?_⟩
    intro R' _ hR' hPR'
    have hcR : Nat.card (R'.map H.subtype) = Nat.card R' :=
      Subgroup.card_map_of_injective H.subtype_injective
    have hle := hPmax (R'.map H.subtype) (hR'.map H.subtype)
    rw [hcR] at hle
    exact (Subgroup.eq_of_le_of_card_ge hPR' (by rw [hcardP']; exact hle)).symm
  have hQp : IsPGroup p (GLBConj n₁ P) := by
    unfold GLBConj
    exact hP.map _
  have hQ'p : IsPGroup p Q' := hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hn₁).symm
  obtain ⟨g, hg⟩ := Lemma1112b.exists_glbConj_le_of_isSylowIn hP'syl hQ'p
  refine ⟨(g : X), g.2, ?_⟩
  have hle : GLBConj (n₁ * (g : X)) P ≤ P := by
    intro w hw
    rw [mem_gLBConj] at hw
    set z := n₁ * (g : X) * w * (n₁ * (g : X))⁻¹ with hz
    have hq : (g : X) * w * (g : X)⁻¹ ∈ GLBConj n₁ P := by
      rw [mem_gLBConj]
      have e : n₁ * ((g : X) * w * (g : X)⁻¹) * n₁⁻¹ = z := by rw [hz]; group
      rw [e]; exact hw
    have hqH : (g : X) * w * (g : X)⁻¹ ∈ H := hn₁ hq
    have hq' : (⟨(g : X) * w * (g : X)⁻¹, hqH⟩ : ↥H) ∈ Q' := Subgroup.mem_subgroupOf.2 hq
    have hmem : g⁻¹ * ⟨(g : X) * w * (g : X)⁻¹, hqH⟩ * g ∈ GLBConj g Q' := by
      rw [mem_gLBConj]
      simpa [mul_assoc] using hq'
    have h2 := hg hmem
    rw [Subgroup.mem_subgroupOf] at h2
    simpa [mul_assoc] using h2
  have heq : GLBConj (n₁ * (g : X)) P = P :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [Lemma1112b.card_glbConj])
  exact mem_normalizer_iff_gLBConj_eq.2 heq

theorem mem_normalizer_of_subgroupOf {K S : Subgroup G} (hSK : S ≤ K) {n : ↥K}
    (hn : n ∈ Subgroup.normalizer ((S.subgroupOf K : Subgroup ↥K) : Set ↥K)) :
    (n : G) ∈ Subgroup.normalizer (S : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · intro hz
    have h1 := (Subgroup.mem_normalizer_iff.1 hn ⟨z, hSK hz⟩).1 (Subgroup.mem_subgroupOf.2 hz)
    exact Subgroup.mem_subgroupOf.1 h1
  · intro hz
    have hzK : z ∈ K := by
      have := K.mul_mem (K.mul_mem (K.inv_mem n.2) (hSK hz)) n.2
      simpa [mul_assoc] using this
    have h1 := (Subgroup.mem_normalizer_iff.1 hn ⟨z, hzK⟩).2
      (Subgroup.mem_subgroupOf.2 (by simpa using hz))
    exact Subgroup.mem_subgroupOf.1 h1

end Sylow

section Fusion

variable {G : Type} [Group G] [Finite G]

theorem fusion_core {K A₀ : Subgroup G} (hL : IsLThreeFour (barOf 3 K)) (hA₀K : A₀ ≤ K)
    (hA₀el : IsElemAbelian 3 A₀) (hA₀9 : Nat.card A₀ = 9) {x y : G} (hx : x ∈ A₀) (hx1 : x ≠ 1)
    (hy : y ∈ A₀) (hy1 : y ≠ 1) :
    ∃ n ∈ K, n ∈ Subgroup.normalizer (A₀ : Set G) ∧ n⁻¹ * x * n = y := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := GLAPPrimeCore 3 ↥K
  set π := QuotientGroup.mk' N
  have hN : ¬ 3 ∣ Nat.card N := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1
    (CFSG.HardMathSupport.Solomon.LocalBalance.coprime_card_gLAPPrimeCore_aux 3 ↥K)
  set P : Subgroup ↥K := A₀.subgroupOf K
  have hPel : IsElemAbelian 3 P := hA₀el.subgroupOf K
  have hP3 : IsPGroup 3 P := hPel.isPGroup
  have hP9 : Nat.card P = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA₀K).toEquiv, hA₀9]
  have hPbar9 : Nat.card (P.map π) = 9 := by rw [card_map_mk_of_isPGroup hN hP3, hP9]
  set x' : ↥K := ⟨x, hA₀K hx⟩
  set y' : ↥K := ⟨y, hA₀K hy⟩
  have hx'P : x' ∈ P := Subgroup.mem_subgroupOf.2 hx
  have hy'P : y' ∈ P := Subgroup.mem_subgroupOf.2 hy
  have hne : ∀ z : ↥K, z ∈ P → (z : G) ≠ 1 → π z ≠ 1 := by
    intro z hz hz1 h
    apply hz1
    have := mk_injOn_of_isPGroup hN hP3 hz (Subgroup.one_mem P) (by rw [← map_one π] at h; exact h)
    rw [this]; rfl
  obtain ⟨m, hm, hmyx⟩ := l34_normalizer_transitive hL hPbar9 (x := π y') (y := π x')
    ⟨y', hy'P, rfl⟩ (hne y' hy'P hy1) ⟨x', hx'P, rfl⟩ (hne x' hx'P hx1)
  obtain ⟨n₁, rfl⟩ := QuotientGroup.mk'_surjective N m
  have hmyx' : π n₁ * π y' * (π n₁)⁻¹ = π x' := hmyx
  have hm' : π n₁ ∈ Subgroup.normalizer ((P.map π : Subgroup _) : Set _) := hm
  have hcomap : (P.map π).comap π = P ⊔ N := by
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
  have hn₁ : GLBConj n₁ P ≤ P ⊔ N := by
    intro w hw
    rw [mem_gLBConj] at hw
    rw [← hcomap, Subgroup.mem_comap]
    have h1 := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hm') (π (n₁ * w * n₁⁻¹))).1
      ⟨_, hw, rfl⟩
    simpa [π, mul_assoc] using h1
  have hPmax : ∀ R : Subgroup ↥K, IsPGroup 3 R → Nat.card R ≤ Nat.card P := by
    intro R hR
    rw [hP9]
    exact card_le_nine_of_isPGroup hL hR
  obtain ⟨w, hw, hnN⟩ := exists_mul_mem_normalizer hP3 hPmax hn₁
  set n := n₁ * w
  have hwbar : π w ∈ P.map π := by
    have : w ∈ (P.map π).comap π := by rw [hcomap]; exact hw
    exact this
  have hconjP : n⁻¹ * x' * n ∈ P := by
    have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hnN) x').1 hx'P
    simpa using this
  have himg : π (n⁻¹ * x' * n) = π y' := by
    have h1 : (π n₁)⁻¹ * π x' * π n₁ = π y' := by
      rw [← hmyx']; group
    obtain ⟨w₀, hw₀, hw₀w⟩ := hwbar
    have hcomm : π w * π y' = π y' * π w := by
      rw [← hw₀w]
      have := congrArg Subtype.val (hPel.1.is_comm.comm ⟨w₀, hw₀⟩ ⟨y', hy'P⟩)
      simp only [Subgroup.coe_mul] at this
      rw [← map_mul, ← map_mul, this]
    calc π (n⁻¹ * x' * n) = (π w)⁻¹ * ((π n₁)⁻¹ * π x' * π n₁) * π w := by
          simp only [n, map_mul, map_inv]; group
      _ = (π w)⁻¹ * (π y' * π w) := by rw [h1, mul_assoc]
      _ = π y' := by rw [← hcomm]; group
  have heq : n⁻¹ * x' * n = y' := mk_injOn_of_isPGroup hN hP3 hconjP hy'P himg
  refine ⟨(n : G), n.2, mem_normalizer_of_subgroupOf hA₀K hnN, ?_⟩
  have := congrArg Subtype.val heq
  simpa using this

theorem lemma1114FusionInput_of_inputs (h119 : Lemma119Statement) (h1112 : Lemma1112Statement) :
    Lemma1114.Lemma1114FusionInput := by
  intro G _ _ m p B M E A a K h hp hIL x hx hx1 y hy hy1
  subst hp
  have hAel : IsElemAbelian 3 A := h.pair.1.2.1.1.1.2.1
  have hA0el : IsElemAbelian 3 (E ⊓ A : Subgroup G) := hAel.mono inf_le_right
  have hA0card : Nat.card ((E ⊓ A : Subgroup G)) = 9 := by
    rw [Lemma1114.card_eq_pow_of_pRank hA0el, (h119 h).1]; norm_num
  obtain ⟨-, hEAK, -⟩ := h1112 h
  have hA0K : E ⊓ A ≤ K := by rw [hEAK]; exact inf_le_right
  exact fusion_core hIL hA0K hA0el hA0card hx hx1 hy hy1

end Fusion

section Config

variable {G : Type} [Group G] [Finite G]

structure Cfg (M E A K : Subgroup G) (a : G) : Prop where
  hAM : A ≤ M
  hAel : IsElemAbelian 3 A
  hA27 : Nat.card A = 27
  hA0card : Nat.card ↥(E ⊓ A) = 9
  hA0K : E ⊓ A ≤ K
  ha : a ∈ A
  ha1 : a ≠ 1
  haA0 : a ∉ E ⊓ A
  hK : GLAPComponent 3 (Cg a) K
  hL : IsLThreeFour (barOf 3 K)
  hsyl : IsSylowIn 3 (centBar 3 (Cg a) K) (Subgroup.zpowers a)
  hconj : ∀ U : Subgroup G, IsEkIn 3 1 A U → (¬ U ≤ E ⊓ A ↔ GConj (Subgroup.zpowers a) U)

theorem cfg_of (h1111 : Lemma1111Statement) (h119 : Lemma119Statement) (h1112 : Lemma1112Statement)
    {m : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G} (h : Cex117 G m 3 B M E A a K) :
    Cfg M E A K a := by
  obtain ⟨-, hA3, hIL⟩ := h1111 h
  have hAel : IsElemAbelian 3 A := h.pair.1.2.1.1.1.2.1
  have hA0el : IsElemAbelian 3 (E ⊓ A : Subgroup G) := hAel.mono inf_le_right
  obtain ⟨⟨hsyl, -⟩, hEAK, hconj⟩ := h1112 h
  refine ⟨h.pair.1.2.1.1.1.1, hAel, Lemma1114.card_eq_27_of_pRank hAel hA3, ?_, ?_, h.ha.1, h.ha.2,
    fun haE => h.notD ⟨E, h.pair.1.1, (Subgroup.mem_inf.1 haE).1⟩, h.hK, hIL, hsyl, hconj⟩
  · rw [Lemma1114.card_eq_pow_of_pRank hA0el, (h119 h).1]; norm_num
  · rw [hEAK]; exact inf_le_right

theorem exists_sub_nine {L : Subgroup G} (hL : IsLThreeFour (barOf 3 L)) :
    ∃ Q : Subgroup G, Q ≤ L ∧ IsPGroup 3 Q ∧ Nat.card Q = 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1 : 3 ^ 2 ∣ Nat.card L := by
    have h2 : Nat.card (barOf 3 L) ∣ Nat.card L := Subgroup.card_quotient_dvd_card _
    rw [CFSG.HardMathSupport.Solomon.UniquenessMaximal.card_eq_of_isLThreeFour hL] at h2
    exact (by norm_num : 3 ^ 2 ∣ 20160).trans h2
  obtain ⟨Q₀, hQ₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥L) 3 h1
  refine ⟨Q₀.map L.subtype, Subgroup.map_subtype_le _, (IsPGroup.of_card hQ₀).map _, ?_⟩
  rw [Subgroup.card_map_of_injective L.subtype_injective, hQ₀]
  norm_num

theorem eq_of_glaPComponent {X L J : Subgroup G} {b : G} (hL : GLAPComponent 3 X L)
    (hsyl : IsSylowIn 3 (centBar 3 X L) (Subgroup.zpowers b)) (hb3 : b ^ 3 = 1)
    (hJ : GLAPComponent 3 X J) {Q : Subgroup G} (hQJ : Q ≤ J) (hQ3 : IsPGroup 3 Q)
    (hQ9 : Nat.card Q = 9) : J = L := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hne
  have hLs := (CFSG.HardMathSupport.Solomon.Coordinator.i183_glaPComponent_iff_isPComponent
    Nat.prime_three).1 hL
  have hJs := (CFSG.HardMathSupport.Solomon.Coordinator.i183_glaPComponent_iff_isPComponent
    Nat.prime_three).1 hJ
  have hne' : J.subgroupOf X ≠ L.subgroupOf X := by
    intro h
    apply hne
    have := Subgroup.subgroupOf_inj.1 h
    rwa [inf_of_le_left hJ.1, inf_of_le_left hL.1] at this
  obtain ⟨-, hn2, hcomm, -⟩ :=
    (CFSG.ComponentClassification.CatalogueBPrimeJoin.distinct_p_components_core_commutation 3
      Nat.prime_three _ _ hJs.2 hLs.2).2 hne'
  have hJC : J ≤ centBar 3 X L := by
    intro j hj
    have hjX : j ∈ X := hJ.1 hj
    have hjs : (⟨j, hjX⟩ : ↥X) ∈ J.subgroupOf X := Subgroup.mem_subgroupOf.2 hj
    have hjN : j ∈ Subgroup.normalizer (L : Set G) :=
      mem_normalizer_of_subgroupOf hL.1 (n := ⟨j, hjX⟩) (hn2 hjs)
    refine mem_centBar_iff_forall.2 ⟨hjX, hjN, fun l hl => ?_⟩
    have hls : (⟨l, hL.1 hl⟩ : ↥X) ∈ L.subgroupOf X := Subgroup.mem_subgroupOf.2 hl
    have h1 := hcomm (Subgroup.commutator_mem_commutator hjs hls)
    obtain ⟨z, hz, hzc⟩ := (Subgroup.mem_inf.1 h1).2
    let e : ↥(L.subgroupOf X) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hL.1
    have hez : e z ∈ GLAPPrimeCore 3 ↥L := by
      have := glaPPrimeCore_map_iso 3 e
      rw [← this]
      exact ⟨z, hz, rfl⟩
    refine ⟨e z, hez, ?_⟩
    have : ((e z : ↥L) : G) = ((z : ↥X) : G) := rfl
    show ((e z : ↥L) : G) = j * l * j⁻¹ * l⁻¹
    rw [this]
    have h2 := congrArg (fun w : ↥X => (w : G)) hzc
    simpa [commutatorElement_def] using h2
  have hle := Lemma1112b.card_le_of_isSylowIn hsyl (hQJ.trans hJC) hQ3
  rw [hQ9] at hle
  have : Nat.card (Subgroup.zpowers b) ≤ 3 := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hb3)
  omega

theorem le_normalizer_of_sylow {X L : Subgroup G} {b : G} (hL : GLAPComponent 3 X L)
    (hsyl : IsSylowIn 3 (centBar 3 X L) (Subgroup.zpowers b)) (hb3 : b ^ 3 = 1)
    {Q : Subgroup G} (hQL : Q ≤ L) (hQ3 : IsPGroup 3 Q) (hQ9 : Nat.card Q = 9) :
    X ≤ Subgroup.normalizer (L : Set G) := by
  intro g hg
  have hX : GLBConj g X = X := mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer hg)
  have hL' : GLAPComponent 3 X (GLBConj g L) := by
    have := glaPComponent_gLBConj hL g
    rwa [hX] at this
  have hQ3' : IsPGroup 3 (GLBConj g Q) := by unfold GLBConj; exact hQ3.map _
  have heq := eq_of_glaPComponent hL hsyl hb3 hL' (gLBConj_mono g hQL) hQ3'
    (by rw [Lemma1112b.card_glbConj, hQ9])
  exact mem_normalizer_iff_gLBConj_eq.2 heq

variable {M E A K : Subgroup G} {a : G}

theorem Cfg.ha3 (c : Cfg M E A K a) : a ^ 3 = 1 := c.hAel.2 a c.ha

theorem Cfg.cg_le_normalizer (c : Cfg M E A K a) : Cg a ≤ Subgroup.normalizer (K : Set G) := by
  obtain ⟨Q, hQK, hQ3, hQ9⟩ := exists_sub_nine c.hL
  exact le_normalizer_of_sylow c.hK c.hsyl c.ha3 hQK hQ3 hQ9

theorem Cfg.exists_conj (c : Cfg M E A K a) {a₁ : G} (ha₁A : a₁ ∈ A) (ha₁A0 : a₁ ∉ E ⊓ A) :
    ∃ g : G, Subgroup.zpowers a₁ = GLBConj g (Subgroup.zpowers a) ∧ Cg a₁ = GLBConj g (Cg a) := by
  have ha₁1 : a₁ ≠ 1 := fun h1 => ha₁A0 (h1 ▸ (E ⊓ A).one_mem)
  have ha₁3 : a₁ ^ 3 = 1 := c.hAel.2 a₁ ha₁A
  have hIE : IsEkIn 3 1 A (Subgroup.zpowers a₁) :=
    ⟨Subgroup.zpowers_le.2 ha₁A, isElemAbelian_zpowers ha₁3, by
      rw [Nat.card_zpowers, orderOf_eq_prime ha₁3 ha₁1]; norm_num⟩
  obtain ⟨g, hg⟩ := (c.hconj _ hIE).1 fun hle => ha₁A0 (Subgroup.zpowers_le.1 hle)
  refine ⟨g, hg.symm, ?_⟩
  rw [Lemma1114.glbConj_centralizer_singleton]
  exact (Lemma1114.centralizer_singleton_eq_of_zpowers_eq
    ((Lemma1114.glbConj_zpowers g a).symm.trans hg)).symm

theorem Cfg.eq_conj_of_comp (c : Cfg M E A K a) {a₁ g : G} (hCg : Cg a₁ = GLBConj g (Cg a))
    {K₁ : Subgroup G} (hK₁ : GLAPComponent 3 (Cg a₁) K₁) (hL₁ : IsLThreeFour (barOf 3 K₁)) :
    K₁ = GLBConj g K ∧ Cg a₁ ≤ Subgroup.normalizer (K₁ : Set G) := by
  have hJ : GLAPComponent 3 (Cg a) (GLBConj g⁻¹ K₁) := by
    have := glaPComponent_gLBConj hK₁ g⁻¹
    rwa [hCg, gLBConj_inv_gLBConj] at this
  obtain ⟨Q, hQK, hQ3, hQ9⟩ := exists_sub_nine hL₁
  have hQ3' : IsPGroup 3 (GLBConj g⁻¹ Q) := by unfold GLBConj; exact hQ3.map _
  have heq := eq_of_glaPComponent c.hK c.hsyl c.ha3 hJ (gLBConj_mono g⁻¹ hQK) hQ3'
    (by rw [Lemma1112b.card_glbConj, hQ9])
  have hK₁eq : K₁ = GLBConj g K := by rw [← heq, gLBConj_gLBConj_inv]
  refine ⟨hK₁eq, ?_⟩
  rw [hK₁eq, normalizer_gLBConj, hCg]
  exact gLBConj_mono g c.cg_le_normalizer

end Config

section CompInput

variable {G : Type} [Group G] [Finite G]

theorem exists_mul_of_mem_sup {H N : Subgroup G} (hHN : H ≤ Subgroup.normalizer (N : Set G))
    {x : G} (hx : x ∈ H ⊔ N) : ∃ h ∈ H, ∃ n ∈ N, h * n = x := by
  have hx' : x ∈ ((H ⊔ N : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right H N hHN] at hx'
  obtain ⟨h, hh, n, hn, rfl⟩ := hx'
  exact ⟨h, hh, n, hn, rfl⟩

theorem exists_pow_mul {O : Subgroup G} {w o : G} (hw : w ∈ Subgroup.normalizer (O : Set G))
    (ho : o ∈ O) (n : ℕ) : ∃ o' ∈ O, (w * o) ^ n = w ^ n * o' := by
  induction n with
  | zero => exact ⟨1, O.one_mem, by simp⟩
  | succ n ih =>
    obtain ⟨o', ho', h⟩ := ih
    refine ⟨w⁻¹ * o' * w * o, O.mul_mem ?_ ho, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hw) o').1 ho'
      simpa [mul_assoc] using this
    · rw [pow_succ, h, pow_succ]; group

theorem pCoreOf_two_sup_le {X K₁ : Subgroup G} (hK₁ : GLAPComponent 3 X K₁)
    (hL : IsLThreeFour (barOf 3 K₁)) :
    pCoreOf 2 (K₁ ⊔ GLAPPrimeCoreOf 3 X) ≤ GLAPPrimeCoreOf 3 X := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set O := GLAPPrimeCoreOf 3 X with hOdef
  set Y := K₁ ⊔ O with hYdef
  set W := pCoreOf 2 Y with hWdef
  have hOX : O ≤ X := Subgroup.map_subtype_le _
  have hK₁X : K₁ ≤ X := hK₁.1
  have hXO : X ≤ Subgroup.normalizer (O : Set G) := le_normalizer_glaPPrimeCoreOf 3 X
  have hYX : Y ≤ X := sup_le hK₁X hOX
  have hWY : W ≤ Y := Subgroup.map_subtype_le _
  have hW2 : IsPGroup 2 W := Lemma1114.isPGroup_pCoreOf_two Y
  have hO3 : ¬ 3 ∣ Nat.card O := not_dvd_card_glaPPrimeCoreOf Nat.prime_three X
  have hcore : GLAPPrimeCoreOf 3 K₁ ≤ O :=
    CFSG.HardMathSupport.Solomon.LocalBalance.glaPPrimeCoreOf_le_of_isSubnormal 3 hK₁.2.1
  set V := W ⊔ O with hVdef
  have hVn : ∀ y ∈ Y, ∀ v ∈ V, y * v * y⁻¹ ∈ V := by
    intro y hy v hv
    obtain ⟨w, hw, o, ho, rfl⟩ := exists_mul_of_mem_sup (hWY.trans (hYX.trans hXO)) hv
    have h1 : y * w * y⁻¹ ∈ W := Lemma1114.pCoreOf_two_conj_mem hy hw
    have h2 : y * o * y⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.1 (hXO (hYX hy)) o).1 ho
    have e : y * (w * o) * y⁻¹ = (y * w * y⁻¹) * (y * o * y⁻¹) := by group
    rw [e]
    exact V.mul_mem (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_right h2)
  set U := V ⊓ K₁ with hUdef
  have hU : U ≤ GLAPPrimeCoreOf 3 K₁ := by
    set π := QuotientGroup.mk' (GLAPPrimeCore 3 ↥K₁)
    have hUn : (U.subgroupOf K₁).Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      obtain ⟨hnV, hnK⟩ := Subgroup.mem_inf.1 hn
      exact Subgroup.mem_inf.2 ⟨hVn _ (Subgroup.mem_sup_left g.2) _ hnV,
        K₁.mul_mem (K₁.mul_mem g.2 hnK) (K₁.inv_mem g.2)⟩
    haveI := (CFSG.HardMathSupport.Solomon.UniquenessMaximal.isSimpleGroup_of_isLThreeFour hL).1
    haveI := hUn.map π (QuotientGroup.mk'_surjective _)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((U.subgroupOf K₁).map π) with h | h
    · intro u hu
      have hu' : (⟨u, (Subgroup.mem_inf.1 hu).2⟩ : ↥K₁) ∈ U.subgroupOf K₁ :=
        Subgroup.mem_subgroupOf.2 hu
      have h1 : π ⟨u, (Subgroup.mem_inf.1 hu).2⟩ ∈ (U.subgroupOf K₁).map π := ⟨_, hu', rfl⟩
      rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact ⟨_, h1, rfl⟩
    ·
      exfalso
      have hK₁V : K₁ ≤ V := by
        intro k hk
        have h1 : π ⟨k, hk⟩ ∈ (U.subgroupOf K₁).map π := by rw [h]; exact Subgroup.mem_top _
        obtain ⟨u, hu, huk⟩ := h1
        have h2 : u⁻¹ * ⟨k, hk⟩ ∈ GLAPPrimeCore 3 ↥K₁ := QuotientGroup.eq.1 huk
        have h3 : ((u⁻¹ * ⟨k, hk⟩ : ↥K₁) : G) ∈ O := hcore ⟨_, h2, rfl⟩
        have h4 : (u : G) ∈ V := (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hu)).1
        have e : k = (u : G) * ((u⁻¹ * ⟨k, hk⟩ : ↥K₁) : G) := by simp
        rw [e]
        exact V.mul_mem h4 (Subgroup.mem_sup_right h3)
      have h3K : 3 ∣ Nat.card K₁ := by
        have h2 : Nat.card (barOf 3 K₁) ∣ Nat.card K₁ := Subgroup.card_quotient_dvd_card _
        rw [CFSG.HardMathSupport.Solomon.UniquenessMaximal.card_eq_of_isLThreeFour hL] at h2
        exact (by norm_num : 3 ∣ 20160).trans h2
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥K₁) 3 h3K
      have hxG : orderOf (x : G) = 3 := by rw [Subgroup.orderOf_coe, hx]
      have hxV : (x : G) ∈ V := hK₁V x.2
      obtain ⟨w, hw, o, ho, hwo⟩ :=
        exists_mul_of_mem_sup (hWY.trans (hYX.trans hXO)) hxV
      obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.1 hW2) ⟨w, hw⟩
      rw [Subgroup.orderOf_mk] at hn
      obtain ⟨o', ho', hpow⟩ := exists_pow_mul (hWY.trans (hYX.trans hXO) hw) ho (2 ^ n)
      have hw1 : w ^ (2 ^ n) = 1 := by rw [← hn]; exact pow_orderOf_eq_one w
      rw [hw1, one_mul, hwo] at hpow
      have hx3 : orderOf ((x : G) ^ 2 ^ n) = 3 := by
        rw [orderOf_pow' _ (pow_ne_zero _ (by norm_num)), hxG]
        have : Nat.gcd 3 (2 ^ n) = 1 :=
          Nat.Coprime.pow_right n (by norm_num : Nat.Coprime 3 2)
        rw [this, Nat.div_one]
      have hdvd : orderOf ((x : G) ^ 2 ^ n) ∣ Nat.card O := by
        rw [hpow]
        exact Subgroup.orderOf_dvd_natCard O ho'
      rw [hx3] at hdvd
      exact hO3 hdvd
  intro w hw
  obtain ⟨k, hk, o, ho, rfl⟩ := exists_mul_of_mem_sup (hK₁X.trans hXO) (hWY hw)
  have hkV : k ∈ V := by
    have e : k = (k * o) * o⁻¹ := by group
    rw [e]
    exact V.mul_mem (Subgroup.mem_sup_left hw) (Subgroup.mem_sup_right (O.inv_mem ho))
  exact O.mul_mem (hcore (hU (Subgroup.mem_inf.2 ⟨hkV, hk⟩))) ho

theorem lemma1115CompInput_of_inputs (h1111 : Lemma1111Statement) (h119 : Lemma119Statement)
    (h1112 : Lemma1112Statement) : Lemma1114.Lemma1115CompInput := by
  intro G _ _ m p B M E A a K h hp hIL a₁ ha₁A ha₁A0 K₁ hK₁ hL₁
  subst hp
  have c := cfg_of h1111 h119 h1112 h
  obtain ⟨g, -, hCg⟩ := c.exists_conj ha₁A ha₁A0
  obtain ⟨-, hN⟩ := c.eq_conj_of_comp hCg hK₁ hL₁
  refine ⟨fun x hx k hk => (Subgroup.mem_normalizer_iff.1 (hN hx) k).1 hk,
    pCoreOf_two_sup_le hK₁ hL₁⟩

end CompInput

section ChiefA

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_pCoreOf_two {M H : Subgroup G} (hHM : H ≤ M) :
    H ≤ Subgroup.normalizer ((pCoreOf 2 M : Subgroup G) : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro t
  constructor
  · exact fun ht => Lemma1114.pCoreOf_two_conj_mem (hHM hx) ht
  · intro ht
    have := Lemma1114.pCoreOf_two_conj_mem (M.inv_mem (hHM hx)) ht
    have e : x⁻¹ * (x * t * x⁻¹) * x⁻¹⁻¹ = t := by group
    rwa [e] at this

theorem mem_normalizer_inf' {H₁ H₂ : Subgroup G} {x : G} (h₁ : x ∈ Subgroup.normalizer (H₁ : Set G))
    (h₂ : x ∈ Subgroup.normalizer (H₂ : Set G)) :
    x ∈ Subgroup.normalizer ((H₁ ⊓ H₂ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_normalizer_iff.1 h₁ y,
    Subgroup.mem_normalizer_iff.1 h₂ y]

theorem le_normalizer_commutator {B H₁ H₂ : Subgroup G}
    (h₁ : B ≤ Subgroup.normalizer (H₁ : Set G)) (h₂ : B ≤ Subgroup.normalizer (H₂ : Set G)) :
    B ≤ Subgroup.normalizer ((⁅H₁, H₂⁆ : Subgroup G) : Set G) := by
  intro y hy
  rw [mem_normalizer_iff_gLBConj_eq]
  unfold GLBConj
  rw [Subgroup.map_commutator]
  have e₁ : H₁.map (MulAut.conj y⁻¹).toMonoidHom = H₁ := mem_normalizer_iff_gLBConj_eq.1 (h₁ hy)
  have e₂ : H₂.map (MulAut.conj y⁻¹).toMonoidHom = H₂ := mem_normalizer_iff_gLBConj_eq.1 (h₂ hy)
  rw [e₁, e₂]

theorem mem_normalizer_subgroupOf {K S : Subgroup G} {n : ↥K}
    (hn : (n : G) ∈ Subgroup.normalizer (S : Set G)) :
    n ∈ Subgroup.normalizer ((S.subgroupOf K : Subgroup ↥K) : Set ↥K) := by
  rw [Subgroup.mem_normalizer_iff]
  intro z
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  simpa using Subgroup.mem_normalizer_iff.1 hn (z : G)

variable {M E A K : Subgroup G} {a : G}

theorem Cfg.core_le (c : Cfg M E A K a) : GLAPPrimeCoreOf 3 K ≤ GLAPPrimeCoreOf 3 (Cg a) :=
  CFSG.HardMathSupport.Solomon.LocalBalance.glaPPrimeCoreOf_le_of_isSubnormal 3 c.hK.2.1

theorem Cfg.bar_A0 (c : Cfg M E A K a) :
    IsElemAbelian 3 (((E ⊓ A).subgroupOf K).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K))) ∧
      Nat.card (((E ⊓ A).subgroupOf K).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K))) = 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hel : IsElemAbelian 3 ((E ⊓ A).subgroupOf K) :=
    (c.hAel.mono (inf_le_right : E ⊓ A ≤ A)).subgroupOf K
  have hN : ¬ 3 ∣ Nat.card (GLAPPrimeCore 3 ↥K) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1
    (CFSG.HardMathSupport.Solomon.LocalBalance.coprime_card_gLAPPrimeCore_aux 3 ↥K)
  refine ⟨hel.map _, ?_⟩
  rw [card_map_mk_of_isPGroup hN hel.isPGroup,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe c.hA0K).toEquiv, c.hA0card]

theorem Cfg.chiefA (c : Cfg M E A K a) :
    ⁅(pCoreOf 2 M ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G), A⁆ ≤
      GLAPPrimeCoreOf 3 (Cg a) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set R := pCoreOf 2 M ⊓ Subgroup.centralizer ({a} : Set G) with hRdef
  set A₀ := E ⊓ A with hA₀def
  have hCN := c.cg_le_normalizer
  have hA₀A : A₀ ≤ A := inf_le_right
  have hAC : A ≤ Cg a := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.2 (Lemma1114.elemAb_comm c.hAel hx c.ha)
  have hA₀R : A₀ ≤ Subgroup.normalizer (R : Set G) := fun x hx =>
    mem_normalizer_inf' (le_normalizer_pCoreOf_two (hA₀A.trans c.hAM) hx)
      (Subgroup.le_normalizer (hAC (hA₀A hx)))
  set W := ⁅R, A₀⁆ with hWdef
  have hWK : W ≤ K := by
    rw [Subgroup.commutator_le]
    intro r hr x hx
    have hrN := hCN (Subgroup.mem_inf.1 hr).2
    rw [commutatorElement_def]
    exact K.mul_mem ((Subgroup.mem_normalizer_iff.1 hrN x).1 (c.hA0K hx)) (K.inv_mem (c.hA0K hx))
  have hW2 : IsPGroup 2 W := by
    refine (Lemma1114.isPGroup_pCoreOf_two M).to_le ?_
    exact Lemma1114.commutator_le_of_normal (le_normalizer_pCoreOf_two (hA₀A.trans c.hAM))
      inf_le_left
  have hA₀W : A₀ ≤ Subgroup.normalizer (W : Set G) :=
    le_normalizer_commutator hA₀R (fun x hx => Subgroup.le_normalizer hx)
  set π := QuotientGroup.mk' (GLAPPrimeCore 3 ↥K)
  obtain ⟨hbarel, hbar9⟩ := c.bar_A0
  have hWbar : (W.subgroupOf K).map π = ⊥ := by
    refine CFSG.HardMathSupport.Solomon.UniquenessMaximal.eq_bot_of_two_group_normalized_by_nine
      c.hL hbarel hbar9 ((hW2.of_equiv (Subgroup.subgroupOfEquivOfLe hWK).symm).map π) ?_
    rintro _ ⟨x, hx, rfl⟩
    exact Lemma1114.map_normalizer_mem π
      (mem_normalizer_subgroupOf (hA₀W (Subgroup.mem_subgroupOf.1 hx)))
  have hWO : W ≤ GLAPPrimeCoreOf 3 (Cg a) := by
    intro w hw
    have h1 : π ⟨w, hWK hw⟩ ∈ (W.subgroupOf K).map π := ⟨_, Subgroup.mem_subgroupOf.2 hw, rfl⟩
    rw [hWbar, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact c.core_le ⟨_, h1, rfl⟩
  rw [Subgroup.commutator_le]
  intro r hr x hx
  obtain ⟨x₀, hx₀, i, -, rfl⟩ :=
    Lemma1114.coord_decomp c.hAel c.hA27 hA₀A c.hA0card c.ha c.ha1 c.haA0 hx
  have hra : Commute r (a ^ i) :=
    Commute.pow_right (show Commute r a from
      Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hr).2) i
  have e : ⁅r, x₀ * a ^ i⁆ = ⁅r, x₀⁆ := by
    rw [commutatorElement_def, commutatorElement_def]
    calc r * (x₀ * a ^ i) * r⁻¹ * (x₀ * a ^ i)⁻¹ = r * x₀ * (a ^ i * r⁻¹) * (a ^ i)⁻¹ * x₀⁻¹ := by
          group
      _ = r * x₀ * (r⁻¹ * a ^ i) * (a ^ i)⁻¹ * x₀⁻¹ := by rw [hra.inv_left.eq]
      _ = r * x₀ * r⁻¹ * x₀⁻¹ := by group
  rw [e]
  exact hWO (Subgroup.commutator_mem_commutator hr hx₀)

theorem lemma1115ChiefAInput_of_inputs (h1111 : Lemma1111Statement) (h119 : Lemma119Statement)
    (h1112 : Lemma1112Statement) : Lemma1114.Lemma1115ChiefAInput := by
  intro G _ _ m p B M E A a K h hp hIL
  subst hp
  exact (cfg_of h1111 h119 h1112 h).chiefA

end ChiefA

section Constr

variable {G : Type} [Group G] [Finite G]

theorem conj_mem_core {p : ℕ} {K : Subgroup G} {y o : G} (hy : y ∈ Subgroup.normalizer (K : Set G))
    (ho : o ∈ GLAPPrimeCoreOf p K) : y * o * y⁻¹ ∈ GLAPPrimeCoreOf p K := by
  have h := glaPPrimeCoreOf_gLBConj p y⁻¹ K
  rw [mem_normalizer_iff_gLBConj_eq.1 (Subgroup.inv_mem _ hy)] at h
  rw [h, mem_gLBConj]
  simpa [mul_assoc] using ho

theorem commutatorElement_mul_mul {x y c d : G} (hcy : Commute c y) (hdx : Commute d x)
    (hcd : Commute c d) : ⁅x * c, y * d⁆ = ⁅x, y⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  calc x * c * (y * d) * (x * c)⁻¹ * (y * d)⁻¹
      = x * (c * y) * (d * c⁻¹) * x⁻¹ * d⁻¹ * y⁻¹ := by group
    _ = x * (y * c) * (c⁻¹ * d) * x⁻¹ * d⁻¹ * y⁻¹ := by rw [hcy.eq, ← (hcd.inv_left).eq]
    _ = x * y * (d * x⁻¹) * d⁻¹ * y⁻¹ := by group
    _ = x * y * (x⁻¹ * d) * d⁻¹ * y⁻¹ := by rw [(hdx.inv_right).eq]
    _ = x * y * x⁻¹ * y⁻¹ := by group

variable {M E A K : Subgroup G} {a : G}

theorem Cfg.centBar_conj (c : Cfg M E A K a) {y z : G} (hy : y ∈ Cg a)
    (hz : z ∈ centBar 3 (Cg a) K) : y * z * y⁻¹ ∈ centBar 3 (Cg a) K := by
  have hyN := c.cg_le_normalizer hy
  obtain ⟨hzC, hzN, hz⟩ := mem_centBar_iff_forall.1 hz
  refine mem_centBar_iff_forall.2 ⟨(Cg a).mul_mem ((Cg a).mul_mem hy hzC) ((Cg a).inv_mem hy),
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hyN hzN) (Subgroup.inv_mem _ hyN), fun l hl => ?_⟩
  have hl' : y⁻¹ * l * y ∈ K := by
    have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hyN) l).1 hl
    simpa using this
  have h1 := conj_mem_core hyN (hz _ hl')
  convert h1 using 1
  group

theorem Cfg.centBar_le (c : Cfg M E A K a) :
    centBar 3 (Cg a) K ≤ GLAPPrimeCoreOf 3 (Cg a) ⊔ Subgroup.zpowers a := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Z := centBar 3 (Cg a) K with hZdef
  have hZC : Z ≤ Cg a := inf_le_right
  have haZ : Subgroup.zpowers a ≤ Z := c.hsyl.1
  set P₀ : Subgroup ↥Z := (Subgroup.zpowers a).subgroupOf Z with hP₀def
  have hP₀3 : IsPGroup 3 P₀ := c.hsyl.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe haZ).symm
  let P : Sylow 3 ↥Z :=
    { toSubgroup := P₀
      isPGroup' := hP₀3
      is_maximal' := by
        intro Q hQ hPQ
        have hmap := c.hsyl.2.2 (Q.map Z.subtype) (Subgroup.map_subtype_le Q) (hQ.map _) (by
          intro x hx
          exact ⟨⟨x, haZ hx⟩, hPQ (Subgroup.mem_subgroupOf.2 hx), rfl⟩)
        refine le_antisymm (fun q hq => ?_) hPQ
        have : (q : G) ∈ Subgroup.zpowers a := by rw [← hmap]; exact ⟨q, hq, rfl⟩
        exact Subgroup.mem_subgroupOf.2 this }
  have hP : Subgroup.normalizer ((P : Subgroup ↥Z) : Set ↥Z) ≤
      Subgroup.centralizer ((P : Subgroup ↥Z) : Set ↥Z) := by
    intro z _
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hqa : (q : G) ∈ Subgroup.zpowers a := Subgroup.mem_subgroupOf.1 hq
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hqa
    have hza : Commute ((z : ↥Z) : G) a :=
      Subgroup.mem_centralizer_singleton_iff.1 (hZC z.2)
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← hk]
    exact (hza.zpow_right k).symm.eq
  obtain ⟨K₀, hK₀n, hK₀3, -, -, -, -, hsup, -⟩ := CFSG.GroupTheory.burnside_normal_complement P hP
  have hK₀O : K₀ ≤ GLAPPrimeCore 3 ↥Z :=
    le_sSup ⟨hK₀n, (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hK₀3⟩
  have hZn : (Z.subgroupOf (Cg a)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact c.centBar_conj g.2 hn
  have hcore : GLAPPrimeCoreOf 3 Z ≤ GLAPPrimeCoreOf 3 (Cg a) :=
    CFSG.HardMathSupport.Solomon.LocalBalance.glaPPrimeCoreOf_le_of_isSubnormal 3
      (IsSubnormal.step hZC hZn (IsSubnormal.refl _))
  intro z hz
  have h1 : (⟨z, hz⟩ : ↥Z) ∈ K₀ ⊔ (P : Subgroup ↥Z) := by rw [hsup]; exact Subgroup.mem_top _
  have h2 : (⟨z, hz⟩ : ↥Z) ∈ GLAPPrimeCore 3 ↥Z ⊔ P₀ := sup_le_sup_right hK₀O _ h1
  have h3 : z ∈ (GLAPPrimeCore 3 ↥Z ⊔ P₀).map Z.subtype := ⟨_, h2, rfl⟩
  rw [Subgroup.map_sup, hP₀def, Subgroup.subgroupOf_map_subtype] at h3
  exact sup_le_sup hcore inf_le_left h3

theorem perfect_le_core_of_le_sup {a : G} {J : Subgroup G} (hperf : ⁅J, J⁆ = J)
    (hJ : J ≤ GLAPPrimeCoreOf 3 (Cg a) ⊔ Subgroup.zpowers a) : J ≤ GLAPPrimeCoreOf 3 (Cg a) := by
  set O := GLAPPrimeCoreOf 3 (Cg a)
  have hOC : O ≤ Cg a := Subgroup.map_subtype_le _
  have haN : Subgroup.zpowers a ≤ Subgroup.normalizer (O : Set G) :=
    Subgroup.zpowers_le.2 (le_normalizer_glaPPrimeCoreOf 3 (Cg a)
      (Subgroup.mem_centralizer_singleton_iff.2 rfl))
  have hdec : ∀ u ∈ J, ∃ o ∈ O, ∃ k : ℤ, u = o * a ^ k := by
    intro u hu
    have hu' : u ∈ ((O ⊔ Subgroup.zpowers a : Subgroup G) : Set G) := hJ hu
    rw [Subgroup.coe_mul_of_right_le_normalizer_left O _ haN] at hu'
    obtain ⟨o, ho, z, hz, rfl⟩ := hu'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    exact ⟨o, ho, k, rfl⟩
  have hcomm : ∀ o ∈ O, ∀ k : ℤ, Commute (a ^ k) o := fun o ho k =>
    (Commute.zpow_right (show Commute o a from
      Subgroup.mem_centralizer_singleton_iff.1 (hOC ho)) k).symm
  rw [← hperf, Subgroup.commutator_le]
  intro u hu v hv
  obtain ⟨o₁, ho₁, k₁, rfl⟩ := hdec u hu
  obtain ⟨o₂, ho₂, k₂, rfl⟩ := hdec v hv
  rw [commutatorElement_mul_mul (hcomm o₂ ho₂ k₁) (hcomm o₁ ho₁ k₂)
    ((Commute.refl a).zpow_zpow k₁ k₂), commutatorElement_def]
  exact O.mul_mem (O.mul_mem (O.mul_mem ho₁ ho₂) (O.inv_mem ho₁)) (O.inv_mem ho₂)

theorem Cfg.layer_eq_bot (c : Cfg M E A K a) {e : G} (he : e ∈ E ⊓ A) (he1 : e ≠ 1) :
    GLAPLayer 3 (Subgroup.centralizer ({e, a} : Set G)) = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set X := Subgroup.centralizer ({e, a} : Set G) with hXdef
  have key : ∀ J : Subgroup G, GLAPComponent 3 X J → False := by
    intro J hJ
    have hXa : X ≤ Cg a := Subgroup.centralizer_le (by simp)
    have hJC : J ≤ Cg a := hJ.1.trans hXa
    have hJN : J ≤ Subgroup.normalizer (K : Set G) := hJC.trans c.cg_le_normalizer
    have hperf : ⁅J, J⁆ = J := glaPComponent_perfect hJ
    set N := Subgroup.normalizer (K : Set G)
    set H := (J.subgroupOf N).map (barAut 3 K) with hHdef
    have hJ'perf : ⁅J.subgroupOf N, J.subgroupOf N⁆ = J.subgroupOf N := by
      rw [← subgroupOf_commutator hJN hJN, hperf]
    have hHperf : ⁅H, H⁆ = H := by rw [hHdef, ← Subgroup.map_commutator, hJ'perf]
    have hHinn := l34_perfect_le_inner c.hL hHperf
    have heK : e ∈ K := c.hA0K he
    set π := QuotientGroup.mk' (GLAPPrimeCore 3 ↥K)
    obtain ⟨hbarel, hbar9⟩ := c.bar_A0
    have hebar : π ⟨e, heK⟩ ∈ ((E ⊓ A).subgroupOf K).map π :=
      ⟨⟨e, heK⟩, Subgroup.mem_subgroupOf.2 he, rfl⟩
    have hebar1 : π ⟨e, heK⟩ ≠ 1 := by
      intro h1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      have h2 : e ∈ GLAPPrimeCoreOf 3 K := ⟨_, h1, rfl⟩
      have h3 : e ^ 3 = 1 := c.hAel.2 e (Subgroup.mem_inf.1 he).2
      have h4 : orderOf e ∣ Nat.card (GLAPPrimeCoreOf 3 K) := Subgroup.orderOf_dvd_natCard _ h2
      rw [orderOf_eq_prime h3 he1] at h4
      exact not_dvd_card_glaPPrimeCoreOf Nat.prime_three K h4
    have hHA : ∀ h ∈ H, ∃ y ∈ ((E ⊓ A).subgroupOf K).map π, MulAut.conj y = h := by
      intro h hh
      obtain ⟨y, hy⟩ := hHinn hh
      refine ⟨y, ?_, hy⟩
      obtain ⟨j', hj', hj'h⟩ := hh
      have hj : (j' : G) ∈ J := Subgroup.mem_subgroupOf.1 hj'
      have hje : (j' : G) * e = e * (j' : G) :=
        Subgroup.mem_centralizer_iff.1 (hJ.1 hj) e (by simp) |>.symm
      have hfix : h (π ⟨e, heK⟩) = π ⟨e, heK⟩ := by
        rw [← hj'h]
        show barAut 3 K j' (QuotientGroup.mk ⟨e, heK⟩) = QuotientGroup.mk ⟨e, heK⟩
        rw [barAut_mk]
        congr 1
        apply Subtype.ext
        show (j' : G) * e * (j' : G)⁻¹ = e
        rw [hje]; group
      rw [← hy, MulAut.conj_apply] at hfix
      have hcomm : y * π ⟨e, heK⟩ = π ⟨e, heK⟩ * y := by
        calc y * π ⟨e, heK⟩ = y * π ⟨e, heK⟩ * y⁻¹ * y := by group
          _ = π ⟨e, heK⟩ * y := by rw [hfix]
      exact l34_mem_of_commute c.hL hbar9 hebar hebar1 hcomm
    have hHbot : H = ⊥ := by
      have hab : ⁅H, H⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro h₁ hh₁
        rw [Subgroup.mem_centralizer_iff]
        intro h₂ hh₂
        obtain ⟨y₁, hy₁, rfl⟩ := hHA h₁ hh₁
        obtain ⟨y₂, hy₂, rfl⟩ := hHA h₂ hh₂
        rw [← map_mul, ← map_mul]
        congr 1
        exact congrArg Subtype.val (hbarel.1.is_comm.comm ⟨y₂, hy₂⟩ ⟨y₁, hy₁⟩)
      rw [← hHperf, hab]
    have hJZ : J ≤ centBar 3 (Cg a) K := by
      intro j hj
      have h1 : barAut 3 K ⟨j, hJN hj⟩ ∈ H := ⟨⟨j, hJN hj⟩, Subgroup.mem_subgroupOf.2 hj, rfl⟩
      rw [hHbot, Subgroup.mem_bot] at h1
      exact Subgroup.mem_inf.2 ⟨⟨⟨j, hJN hj⟩, MonoidHom.mem_ker.2 h1, rfl⟩, hJC hj⟩
    have hJO : J ≤ GLAPPrimeCoreOf 3 (Cg a) :=
      perfect_le_core_of_le_sup hperf (hJZ.trans c.centBar_le)
    have hJ3 : ¬ 3 ∣ Nat.card J := fun h3 =>
      not_dvd_card_glaPPrimeCoreOf Nat.prime_three (Cg a) (h3.trans (Subgroup.card_dvd_of_le hJO))
    have hJcore : J ≤ GLAPPrimeCoreOf 3 J := by
      intro j hj
      refine ⟨⟨j, hj⟩, ?_, rfl⟩
      have : (⊤ : Subgroup ↥J) ≤ GLAPPrimeCore 3 ↥J := le_sSup ⟨inferInstance, by
        rw [Subgroup.card_top]; exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hJ3⟩
      exact this (Subgroup.mem_top _)
    have hJX' : J ≤ GLAPPrimeCoreOf 3 X := hJcore.trans
      (CFSG.HardMathSupport.Solomon.LocalBalance.glaPPrimeCoreOf_le_of_isSubnormal 3 hJ.2.1)
    have hbot : (J.subgroupOf X).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥X)) = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
      intro j hj
      obtain ⟨y, hy, hyj⟩ := hJX' (Subgroup.mem_subgroupOf.1 hj)
      have : y = j := Subtype.ext hyj
      rw [← this]
      exact hy
    have hsub : Subsingleton ↥((J.subgroupOf X).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥X))) := by
      constructor
      rintro ⟨x, hx⟩ ⟨y, hy⟩
      rw [hbot, Subgroup.mem_bot] at hx hy
      subst hx
      subst hy
      rfl
    have hsimple := hJ.2.2.1.2.2.2
    have hnt := hsimple.toNontrivial
    obtain ⟨p, q, hpq⟩ := hnt
    apply hpq
    induction p using QuotientGroup.induction_on with
    | H p =>
      induction q using QuotientGroup.induction_on with
      | H q => rw [Subsingleton.elim p q]
  unfold GLAPLayer
  exact sSup_eq_bot.2 fun J hJ => (key J hJ).elim

theorem lemma1114ConstrInput_of_inputs (h1111 : Lemma1111Statement) (h119 : Lemma119Statement)
    (h1112 : Lemma1112Statement) : Lemma1114.Lemma1114ConstrInput := by
  intro G _ _ m p B M E A a K h hp hIL e he he1
  subst hp
  exact (cfg_of h1111 h119 h1112 h).layer_eq_bot he he1

end Constr

section Chief

variable {G : Type} [Group G] [Finite G]

theorem barAut_of_mem {K : Subgroup G} {k : G} (hk : k ∈ K) :
    barAut 3 K ⟨k, Subgroup.le_normalizer hk⟩ =
      MulAut.conj (QuotientGroup.mk ⟨k, hk⟩ : barOf 3 K) := by
  ext q
  induction q using QuotientGroup.induction_on with
  | H x =>
    rw [barAut_mk, MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul]
    rfl

theorem centralizer_gLBConj (g : G) (B : Subgroup G) :
    Subgroup.centralizer ((GLBConj g B : Subgroup G) : Set G) =
      GLBConj g (Subgroup.centralizer (B : Set G)) := by
  ext x
  rw [mem_gLBConj, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h b hb
    have hb' : g⁻¹ * b * g ∈ GLBConj g B := by
      rw [mem_gLBConj]; simpa [mul_assoc] using hb
    have := h _ hb'
    calc b * (g * x * g⁻¹) = g * ((g⁻¹ * b * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * b * g)) * g⁻¹ := by rw [this]
      _ = g * x * g⁻¹ * b := by group
  · intro h b hb
    rw [SetLike.mem_coe, mem_gLBConj] at hb
    have := h _ hb
    calc b * x = g⁻¹ * ((g * b * g⁻¹) * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * (g * b * g⁻¹)) * g := by rw [this]
      _ = x * b := by group

variable {M E A K : Subgroup G} {a : G}

theorem Cfg.chief_core (c : Cfg M E A K a) {S B : Subgroup G} (hSC : S ≤ Cg a)
    (hS : ¬ 3 ∣ Nat.card S) (hBC : B ≤ Cg a) (hB : IsElemAbelian 3 B)
    (hBS : B ≤ Subgroup.normalizer (S : Set G)) :
    S ≤ K ⊔ GLAPPrimeCoreOf 3 (Cg a) ⊔ Subgroup.centralizer (B : Set G) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set O := GLAPPrimeCoreOf 3 (Cg a) with hOdef
  have hCN := c.cg_le_normalizer
  have hfac := CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_factorization 3
    Nat.prime_three B S hB.isPGroup hBS ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hS)
  rw [← hfac]
  refine sup_le ?_ (inf_le_right.trans le_sup_right)
  refine le_trans ?_ le_sup_left
  rw [Subgroup.commutator_le]
  intro s hs x hx
  have htS : ⁅s, x⁆ ∈ S := by
    rw [commutatorElement_def]
    have h1 : x * s⁻¹ * x⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.1 (hBS hx) s⁻¹).1 (S.inv_mem hs)
    have e : s * x * s⁻¹ * x⁻¹ = s * (x * s⁻¹ * x⁻¹) := by group
    rw [e]
    exact S.mul_mem hs h1
  set t := ⁅s, x⁆ with htdef
  have htC : t ∈ Cg a := hSC htS
  have hsN := hCN (hSC hs)
  have hxN := hCN (hBC hx)
  have htN := hCN htC
  have hρt : barAut 3 K ⟨t, htN⟩ = (barAut 3 K ⟨s, hsN⟩ * barAut 3 K ⟨x, hxN⟩ *
      (barAut 3 K ⟨s, hsN⟩)⁻¹) * (barAut 3 K ⟨x, hxN⟩)⁻¹ := by
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    congr 1
  have hx3 : (⟨x, hxN⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ 3 = 1 :=
    Subtype.ext (by simpa using hB.2 x hx)
  have hx3' : (barAut 3 K ⟨x, hxN⟩) ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
  have hα : (barAut 3 K ⟨s, hsN⟩ * barAut 3 K ⟨x, hxN⟩ * (barAut 3 K ⟨s, hsN⟩)⁻¹) ^ 3 = 1 := by
    rw [conj_pow, hx3', mul_one, mul_inv_cancel]
  have hβ : ((barAut 3 K ⟨x, hxN⟩)⁻¹) ^ 3 = 1 := by
    rw [inv_pow, hx3', inv_one]
  have hn : ¬ 3 ∣ orderOf t := fun h3 => hS (h3.trans (Subgroup.orderOf_dvd_natCard S htS))
  have htn : (barAut 3 K ⟨t, htN⟩) ^ orderOf t = 1 := by
    rw [← map_pow]
    have : (⟨t, htN⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ orderOf t = 1 :=
      Subtype.ext (by simp [pow_orderOf_eq_one])
    rw [this, map_one]
  rw [hρt] at htn
  obtain ⟨y, hy⟩ := l34_mul_mem_inner c.hL hα hβ hn htn
  rw [← hρt] at hy
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective y
  have hkC : (k : G) ∈ Cg a := c.hK.1 k.2
  have hkN : (k : G) ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer k.2
  have hz : (k : G)⁻¹ * t ∈ centBar 3 (Cg a) K := by
    refine Subgroup.mem_inf.2 ⟨⟨⟨(k : G)⁻¹ * t, Subgroup.mul_mem _ (Subgroup.inv_mem _ hkN) htN⟩,
      ?_, rfl⟩, (Cg a).mul_mem ((Cg a).inv_mem hkC) htC⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    have e : (⟨(k : G)⁻¹ * t, Subgroup.mul_mem _ (Subgroup.inv_mem _ hkN) htN⟩ :
        ↥(Subgroup.normalizer (K : Set G))) = (⟨(k : G), hkN⟩)⁻¹ * ⟨t, htN⟩ := rfl
    rw [e, map_mul, map_inv, ← hy, barAut_of_mem k.2]
    exact inv_mul_cancel _
  have haN : Subgroup.zpowers a ≤ Subgroup.normalizer (O : Set G) :=
    Subgroup.zpowers_le.2 (le_normalizer_glaPPrimeCoreOf 3 (Cg a)
      (Subgroup.mem_centralizer_singleton_iff.2 rfl))
  have hz' : (k : G)⁻¹ * t ∈ ((O ⊔ Subgroup.zpowers a : Subgroup G) : Set G) := c.centBar_le hz
  rw [Subgroup.coe_mul_of_right_le_normalizer_left O _ haN] at hz'
  obtain ⟨o, ho, w, hw, how⟩ := hz'
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
  have how' : o * a ^ j = (k : G)⁻¹ * t := how
  have ht : t = ((k : G) * o) * a ^ j := by
    rw [mul_assoc, how']; group
  set W := K ⊔ O with hWdef
  have hkoW : (k : G) * o ∈ W := W.mul_mem (Subgroup.mem_sup_left k.2) (Subgroup.mem_sup_right ho)
  have hkoC : (k : G) * o ∈ Cg a := (Cg a).mul_mem hkC (Subgroup.map_subtype_le _ ho)
  have hajW : a ^ j ∈ W := by
    have hcomm : Commute ((k : G) * o) (a ^ j) :=
      Commute.zpow_right (show Commute ((k : G) * o) a from
        Subgroup.mem_centralizer_singleton_iff.1 hkoC) j
    obtain ⟨n, hnt⟩ : ∃ n, orderOf t = n := ⟨_, rfl⟩
    have htn' : ((k : G) * o * a ^ j) ^ n = 1 := by
      rw [← ht, ← hnt]; exact pow_orderOf_eq_one t
    rw [hcomm.mul_pow] at htn'
    have h1 : (a ^ j) ^ n ∈ W := by
      rw [eq_inv_of_mul_eq_one_right htn']
      exact W.inv_mem (W.pow_mem hkoW _)
    have hco : Nat.Coprime n 3 := by
      rw [← hnt]; exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hn).symm
    obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hco (by norm_num)
    have ha3j : (a ^ j) ^ 3 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, c.ha3, one_zpow]
    have : a ^ j = ((a ^ j) ^ n) ^ m := by
      rw [← pow_mul, pow_eq_pow_mod _ ha3j, hm, pow_one]
    rw [this]
    exact W.pow_mem h1 m
  rw [ht]
  exact W.mul_mem hkoW hajW

theorem lemma1114ChiefInput_of_inputs (h1111 : Lemma1111Statement) (h119 : Lemma119Statement)
    (h1112 : Lemma1112Statement) : Lemma1114.Lemma1114ChiefInput := by
  intro G _ _ m p B M E A a K h hp hIL a₁ ha₁A ha₁A0 K₁ hK₁ hL₁ S hSC hS hAS
  subst hp
  have c := cfg_of h1111 h119 h1112 h
  obtain ⟨g, -, hCg⟩ := c.exists_conj ha₁A ha₁A0
  obtain ⟨hK₁eq, -⟩ := c.eq_conj_of_comp hCg hK₁ hL₁
  have hAC₁ : A ≤ Cg a₁ := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.2 (Lemma1114.elemAb_comm c.hAel hx ha₁A)
  have hS'C : GLBConj g⁻¹ S ≤ Cg a := by
    have := gLBConj_mono g⁻¹ hSC
    rwa [hCg, gLBConj_inv_gLBConj] at this
  have hB'C : GLBConj g⁻¹ A ≤ Cg a := by
    have := gLBConj_mono g⁻¹ hAC₁
    rwa [hCg, gLBConj_inv_gLBConj] at this
  have hS' : ¬ 3 ∣ Nat.card (GLBConj g⁻¹ S) := by rwa [Lemma1112b.card_glbConj]
  have hB'S' : GLBConj g⁻¹ A ≤ Subgroup.normalizer ((GLBConj g⁻¹ S : Subgroup G) : Set G) := by
    rw [normalizer_gLBConj]
    exact gLBConj_mono g⁻¹ hAS
  have hcore := gLBConj_mono g (c.chief_core hS'C hS' hB'C
    (Lemma1112b.isElemAbelian_glbConj c.hAel g⁻¹) hB'S')
  have hsup : ∀ H₁ H₂ : Subgroup G, GLBConj g (H₁ ⊔ H₂) = GLBConj g H₁ ⊔ GLBConj g H₂ :=
    fun H₁ H₂ => Subgroup.map_sup H₁ H₂ _
  rw [gLBConj_gLBConj_inv, hsup, hsup, ← hK₁eq, ← glaPPrimeCoreOf_gLBConj, ← hCg,
    ← centralizer_gLBConj, gLBConj_gLBConj_inv] at hcore
  exact hcore

end Chief

theorem lemma1114_of_siblings (h1111 : Lemma1111Statement) (h119 : Lemma119Statement)
    (h1112 : Lemma1112Statement) (h1113 : Lemma1113Statement) (h111 : Prop111Statement)
    (h112 : Prop112Statement) : Lemma1114Statement :=
  lemma1114_of_inputs h1111 h119 h1112 h1113 h111 h112 (lemma1114FusionInput_of_inputs h119 h1112)
    (lemma1114ChiefInput_of_inputs h1111 h119 h1112) (lemma1114ConstrInput_of_inputs h1111 h119 h1112)

theorem lemma1115_i_of_siblings (h1111 : Lemma1111Statement) (h119 : Lemma119Statement)
    (h1112 : Lemma1112Statement) (h111 : Prop111Statement) : Lemma1115_iStatement :=
  lemma1115_i_of_inputs h1111 h119 h1112 h111 (lemma1114FusionInput_of_inputs h119 h1112)
    (lemma1114ChiefInput_of_inputs h1111 h119 h1112) (lemma1115ChiefAInput_of_inputs h1111 h119 h1112)
    (lemma1115CompInput_of_inputs h1111 h119 h1112)

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs1114
