module

public import CFSG.LocalAnalysis.GLTheoremA.S9.Inputs96
public import CFSG.RankThree.GroupTheory.SteinbergCEExtraspecialMinusModule

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open scoped commutatorElement

namespace XRep

open scoped commutatorElement

section PGroupFacts

variable {P : Type*} [Group P] [Finite P]

theorem commutator_le_of_isCoatom [Group.IsNilpotent P] {M : Subgroup P} (hM : IsCoatom M) :
    _root_.commutator P ≤ M := by
  haveI : M.Normal :=
    Subgroup.NormalizerCondition.normal_of_coatom M Group.normalizerCondition_of_isNilpotent hM
  haveI : IsSimpleGroup (P ⧸ M) := Group.isSimpleGroup_of_isCoatom hM
  have hcomm : ∀ u v : P ⧸ M, u * v = v * u := fun u v => mul_comm u v
  rw [commutator_def, Subgroup.commutator_le]
  intro a _ b _
  rw [commutatorElement_def, ← QuotientGroup.eq_one_iff]
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  rw [hcomm (a : P ⧸ M) b]
  group

theorem eq_top_of_sup_commutator_eq [Group.IsNilpotent P] (H : Subgroup P)
    (h : H ⊔ _root_.commutator P = ⊤) : H = ⊤ := by
  have hle : _root_.commutator P ≤ frattini P :=
    le_iInf₂ fun M hM => commutator_le_of_isCoatom hM
  have h2 : H ⊔ frattini P = ⊤ := top_le_iff.mp (h ▸ sup_le_sup_left hle H)
  exact frattini_nongenerating h2

end PGroupFacts

section Coset

variable {P : Type*} [Group P] [Finite P]

theorem exists_fixed_mem_coset (N : Subgroup P) (hN : Odd (Nat.card N)) (σ : P →* P)
    (hσ : σ.comp σ = MonoidHom.id P) (hNσ : ∀ n ∈ N, σ n ∈ N) (x : P)
    (hx : ∃ n ∈ N, σ x = x * n) :
    ∃ y : P, σ y = y ∧ x⁻¹ * y ∈ N := by
  classical
  obtain ⟨n₀, hn₀, hxn₀⟩ := hx
  have hσσ : ∀ y, σ (σ y) = y := fun y => by
    simpa using DFunLike.congr_fun hσ y
  have hn₀σ : n₀ * σ n₀ = 1 := by
    have h1 : σ (σ x) = x := hσσ x
    rw [hxn₀, map_mul, hxn₀, mul_assoc] at h1
    simpa using h1
  let τ : N → N := fun n => ⟨n₀ * σ n, N.mul_mem hn₀ (hNσ n n.2)⟩
  have hτ : Function.Involutive τ := by
    intro n
    apply Subtype.ext
    show n₀ * σ (n₀ * σ n) = n
    rw [map_mul, hσσ, ← mul_assoc, hn₀σ, one_mul]
  haveI : Fintype N := Fintype.ofFinite N
  have hodd : ¬ 2 ∣ Fintype.card N := by
    rw [← Nat.card_eq_fintype_card]
    exact hN.not_two_dvd_nat
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hperm : (hτ.toPerm τ) ^ 2 ^ 1 = 1 := by
    ext n
    simp [pow_two, hτ n]
  obtain ⟨n, hn⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := 2) (n := 1) hodd hperm
  have hnfix : n₀ * σ n = n := by
    have := congrArg Subtype.val hn
    simpa [Function.Involutive.coe_toPerm, τ] using this
  refine ⟨x * n, ?_, ?_⟩
  · rw [map_mul, hxn₀, mul_assoc, hnfix]
  · simp

end Coset

open scoped commutatorElement

section Upper

theorem finrank_eq_pow_of_irreducible (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2) {T : Type*} [Group T]
    [Finite T] {n : ℕ} (hT : CFSG.IsExtraspecialPGroup 2 T) (hcard : Nat.card T = 2 ^ (1 + 2 * n))
    {z : T} (hz : Subgroup.center T = Subgroup.zpowers z)
    {V : Type*} [AddCommGroup V] [Module (ZMod q) V] [Finite V] [Nontrivial V]
    (ρ : Representation (ZMod q) T V) (hρz : ρ z = -1)
    (hirr : ∀ W : Submodule (ZMod q) V, (∀ t : T, ∀ w ∈ W, ρ t w ∈ W) → W = ⊥ ∨ W = ⊤) :
    Module.finrank (ZMod q) V = 2 ^ n := by
  classical
  have hqp : q.Prime := Fact.out
  have hq1 : 2 ≤ q := hqp.two_le
  have h2K : (2 : ZMod q) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod q) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hqp Nat.prime_two).mp h')
  have hzcard : Nat.card (Subgroup.zpowers z) = 2 := by
    rw [← hz]; exact hT.2.2.2
  have hzord : orderOf z = 2 := by rw [← Nat.card_zpowers]; exact hzcard
  haveI hEndfin : Finite (Module.End (ZMod q) V) :=
    Finite.of_injective (fun f : Module.End (ZMod q) V => (f : V → V)) DFunLike.coe_injective
  obtain ⟨R, hRmem, hRle⟩ : ∃ R : Subalgebra (ZMod q) (Module.End (ZMod q) V),
      (∀ t : T, ρ t ∈ R) ∧
        Subalgebra.toSubmodule R ≤ Submodule.span (ZMod q) (Set.range ρ) := by
    refine ⟨Algebra.adjoin (ZMod q) (Set.range ρ), fun t => Algebra.subset_adjoin ⟨t, rfl⟩, ?_⟩
    rw [Algebra.adjoin_eq_span]
    refine Submodule.span_le.mpr fun x hx => ?_
    have hx' : x ∈ MonoidHom.mrange ρ :=
      (Submonoid.closure_le.mpr (by rw [MonoidHom.coe_mrange])) hx
    obtain ⟨t, rfl⟩ := hx'
    exact Submodule.subset_span ⟨t, rfl⟩
  have hRdim : Module.finrank (ZMod q) R ≤ 2 ^ (2 * n) := by
    letI : Fintype (T ⧸ Subgroup.zpowers z) := Fintype.ofFinite _
    let f : T ⧸ Subgroup.zpowers z → Module.End (ZMod q) V := fun c => ρ (Quotient.out c)
    have hspan : Submodule.span (ZMod q) (Set.range ρ) ≤
        Submodule.span (ZMod q) (Set.range f) := by
      refine Submodule.span_le.mpr ?_
      rintro x ⟨t, rfl⟩
      obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (Subgroup.zpowers z) t
      have hh' : (h : T) = 1 ∨ (h : T) = z := by
        obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp h.2
        rw [← hj, ← zpow_mod_orderOf, hzord]
        rcases Int.emod_two_eq_zero_or_one j with h0 | h1
        · left; rw [Nat.cast_ofNat, h0, zpow_zero]
        · right; rw [Nat.cast_ofNat, h1, zpow_one]
      have hmem : f (t : T ⧸ Subgroup.zpowers z) ∈ Submodule.span (ZMod q) (Set.range f) :=
        Submodule.subset_span ⟨_, rfl⟩
      have hf : f (t : T ⧸ Subgroup.zpowers z) = ρ t * ρ h := by
        simp only [f]; rw [hh, map_mul]
      rw [hf] at hmem
      rcases hh' with h1 | hz'
      · rw [h1, map_one, mul_one] at hmem; exact hmem
      · rw [hz', hρz, mul_neg_one] at hmem
        simpa using Submodule.neg_mem _ hmem
    have h1 : Module.finrank (ZMod q) R ≤
        Module.finrank (ZMod q) (Submodule.span (ZMod q) (Set.range f)) := by
      rw [← Subalgebra.finrank_toSubmodule]
      exact Submodule.finrank_mono (hRle.trans hspan)
    have h2 : Module.finrank (ZMod q) (Submodule.span (ZMod q) (Set.range f)) ≤
        Fintype.card (T ⧸ Subgroup.zpowers z) := finrank_range_le_card (R := ZMod q) f
    have h3 : Fintype.card (T ⧸ Subgroup.zpowers z) = 2 ^ (2 * n) := by
      rw [Fintype.card_eq_nat_card]
      have h4 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.zpowers z)
      rw [hcard, hzcard, pow_add, pow_one] at h4
      omega
    omega
  haveI hsimple : IsSimpleModule R V := by
    refine (isSimpleModule_iff R V).mpr { eq_bot_or_eq_top := fun W => ?_ }
    let W' : Submodule (ZMod q) V :=
      { carrier := W
        add_mem' := W.add_mem
        zero_mem' := W.zero_mem
        smul_mem' := fun c w hw => by
          have h := W.smul_mem (algebraMap (ZMod q) R c) hw
          simpa [Subalgebra.smul_def] using h }
    have hW' : ∀ t : T, ∀ w ∈ W', ρ t w ∈ W' := fun t w hw =>
      W.smul_mem (⟨ρ t, hRmem t⟩ : R) hw
    rcases hirr W' hW' with h | h
    · left
      rw [Submodule.eq_bot_iff] at h ⊢
      exact fun x hx => h x hx
    · right
      rw [Submodule.eq_top_iff'] at h ⊢
      exact fun x => h x
  haveI hFfin : Finite (Module.End R V) :=
    Finite.of_injective (fun f : Module.End R V => (f : V → V)) DFunLike.coe_injective
  haveI hVfinF : Module.Finite (Module.End R V) V := Module.Finite.of_finite
  have hcomm : ∀ (f : Module.End R V) (t : T) (v : V), f (ρ t v) = ρ t (f v) := by
    intro f t v
    exact f.map_smul (⟨ρ t, hRmem t⟩ : R) v
  let ρF : Representation (Module.End R V) T V :=
    { toFun := fun t =>
        { toFun := ρ t
          map_add' := (ρ t).map_add
          map_smul' := fun f v => (hcomm f t v).symm }
      map_one' := by ext v; simp
      map_mul' := fun s t => by ext v; simp }
  have hρFz : ρF z = -1 := by
    ext v
    simp [ρF, hρz]
  have h2F : (2 : Module.End R V) ≠ 0 := by
    intro h
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have h1 : (2 : Module.End R V) v = v + v := by
      rw [← one_add_one_eq_two, LinearMap.add_apply, Module.End.one_apply]
    have h2 : (2 : ZMod q) • v = 0 := by
      rw [two_smul, ← h1, h, LinearMap.zero_apply]
    exact hv ((smul_eq_zero.mp h2).resolve_left h2K)
  have hlow := (CFSG.RankThree.GroupTheory.extraspecial_two_minus_module_bound
    (K := Module.End R V) hT hcard hz h2F ρF hρFz).1
  have hlow' : 2 ^ n ≤ Module.finrank (Module.End R V) V := hlow
  set m := Module.finrank (Module.End R V) V
  set d := Module.finrank (ZMod q) V
  have hm_pos : 0 < m := lt_of_lt_of_le (Nat.two_pow_pos n) hlow'
  have hcardV_K : Nat.card V = q ^ d := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod q), Nat.card_zmod]
  have hcardV_F : Nat.card V = Nat.card (Module.End R V) ^ m :=
    Module.natCard_eq_pow_finrank (K := Module.End R V)
  obtain ⟨k, -, hkF⟩ : ∃ k ≤ d, Nat.card (Module.End R V) = q ^ k := by
    rw [← Nat.dvd_prime_pow hqp, ← hcardV_K, hcardV_F]
    exact dvd_pow_self _ hm_pos.ne'
  have hk_pos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · exfalso
      have h' := Finite.one_lt_card (α := Module.End R V)
      rw [hkF, h, pow_zero] at h'
      exact lt_irrefl _ h'
    · exact h
  have hdkm : d = k * m := by
    apply Nat.pow_right_injective hq1
    simp only
    rw [← hcardV_K, hcardV_F, hkF, ← pow_mul]
  haveI hfreeF : Module.Free (Module.End R V) V := by
    exact Module.Free.of_divisionRing (Module.End R V) V
  have hcardEnd : Nat.card (Module.End (Module.End R V) V) = q ^ (k * (m * m)) := by
    let b := Module.finBasis (Module.End R V) V
    calc Nat.card (Module.End (Module.End R V) V) = Nat.card (Fin m → V) :=
          (Nat.card_congr (b.constr ℕ).toEquiv).symm
      _ = q ^ (k * (m * m)) := by
          rw [Nat.card_fun, Nat.card_fin, hcardV_F, hkF, ← pow_mul, ← pow_mul]
  have hsurj := Module.Finite.toModuleEnd_moduleEnd_surjective (R := R) (M := V)
  have hle1 : Nat.card (Module.End (Module.End R V) V) ≤ Nat.card R :=
    Nat.card_le_card_of_surjective _ hsurj
  haveI : Module.Finite (ZMod q) R := Module.Finite.of_finite
  have hcardR : Nat.card R = q ^ Module.finrank (ZMod q) R := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod q), Nat.card_zmod]
  have hkmm : k * (m * m) ≤ 2 ^ (2 * n) := by
    have h1 : q ^ (k * (m * m)) ≤ q ^ Module.finrank (ZMod q) R := by
      rw [← hcardEnd, ← hcardR]; exact hle1
    exact ((Nat.pow_le_pow_iff_right hq1).mp h1).trans hRdim
  have hsq : 2 ^ (2 * n) ≤ m * m := by
    rw [two_mul, pow_add]
    exact Nat.mul_le_mul hlow' hlow'
  have hk1 : k = 1 := by
    have h1 : k * (m * m) ≤ 1 * (m * m) := by rw [one_mul]; exact hkmm.trans hsq
    have h2 := Nat.le_of_mul_le_mul_right h1 (Nat.mul_pos hm_pos hm_pos)
    omega
  have hm_eq : m = 2 ^ n := by
    have h3 : m * m ≤ 2 ^ n * 2 ^ n := by
      rw [← pow_add, ← two_mul]; rw [hk1, one_mul] at hkmm; exact hkmm
    have h4 := Nat.mul_self_le_mul_self_iff.mp h3
    omega
  rw [hdkm, hk1, one_mul, hm_eq]

end Upper

open scoped commutatorElement

section Basic

variable {G : Type} [Group G]

@[expose] def conjQ (Q : Subgroup G) {t : G} (ht : t ∈ Subgroup.normalizer (Q : Set G)) :
    ↥Q →* ↥Q where
  toFun x := ⟨t * x * t⁻¹, (Subgroup.mem_normalizer_iff.1 ht x).1 x.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

theorem conjQ_coe (Q : Subgroup G) {t : G} (ht : t ∈ Subgroup.normalizer (Q : Set G))
    (x : ↥Q) : ((conjQ Q ht x : ↥Q) : G) = t * x * t⁻¹ := rfl

theorem conjQ_mul (Q : Subgroup G) {s t : G} (hs : s ∈ Subgroup.normalizer (Q : Set G))
    (ht : t ∈ Subgroup.normalizer (Q : Set G)) :
    conjQ Q (Subgroup.mul_mem _ hs ht) = (conjQ Q hs).comp (conjQ Q ht) := by
  ext x
  simp [conjQ_coe, mul_assoc, mul_inv_rev]

abbrev QA (Q : Subgroup G) : Type := Additive (Abelianization ↥Q)

@[expose] def piQ (Q : Subgroup G) (x : ↥Q) : QA Q := Additive.ofMul (Abelianization.of x)

theorem piQ_surjective (Q : Subgroup G) : Function.Surjective (piQ Q) := by
  intro v
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
  exact ⟨g, congrArg Additive.ofMul hg⟩

theorem piQ_mul (Q : Subgroup G) (x y : ↥Q) : piQ Q (x * y) = piQ Q x + piQ Q y := by
  simp [piQ]

theorem piQ_one (Q : Subgroup G) : piQ Q 1 = 0 := by
  simp [piQ]

theorem mem_commutator_iff (Q : Subgroup G) (x : ↥Q) :
    x ∈ _root_.commutator ↥Q ↔ (x : G) ∈ ⁅Q, Q⁆ := by
  have hmap : (_root_.commutator ↥Q).map Q.subtype = ⁅Q, Q⁆ := by
    show ((⁅(⊤ : Subgroup ↥Q), ⊤⁆ : Subgroup ↥Q)).map Q.subtype = ⁅Q, Q⁆
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [← hmap]
  exact (Subgroup.mem_map_iff_mem (f := Q.subtype) Q.subtype_injective).symm

theorem piQ_eq_zero_iff (Q : Subgroup G) (x : ↥Q) : piQ Q x = 0 ↔ (x : G) ∈ ⁅Q, Q⁆ := by
  rw [← mem_commutator_iff, piQ]
  exact (ofMul_eq_zero : Additive.ofMul (Abelianization.of x) = 0 ↔ _).trans (QuotientGroup.eq_one_iff x)

end Basic

section Module

variable {G : Type} [Group G] (Q : Subgroup G) (q : ℕ) [Module (ZMod q) (QA Q)]

@[expose] def linQ (f : ↥Q →* ↥Q) : QA Q →ₗ[ZMod q] QA Q :=
  AddMonoidHom.toZModLinearMap q (MonoidHom.toAdditive (Abelianization.map f))

theorem linQ_piQ (f : ↥Q →* ↥Q) (x : ↥Q) : linQ Q q f (piQ Q x) = piQ Q (f x) := by
  simp [linQ, piQ]

theorem linQ_comp (f g : ↥Q →* ↥Q) : linQ Q q (f.comp g) = linQ Q q f * linQ Q q g := by
  apply LinearMap.ext
  intro v
  obtain ⟨x, rfl⟩ := piQ_surjective Q v
  rw [Module.End.mul_apply, linQ_piQ, linQ_piQ, linQ_piQ]
  rfl

theorem linQ_id : linQ Q q (MonoidHom.id ↥Q) = 1 := by
  apply LinearMap.ext
  intro v
  obtain ⟨x, rfl⟩ := piQ_surjective Q v
  rw [linQ_piQ]
  rfl

end Module

section Key

variable {G : Type} [Group G]

theorem zpowers_cases {z g : G} (hz2 : z ^ 2 = 1) (hg : g ∈ Subgroup.zpowers z) :
    g = 1 ∨ g = z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
  have hd : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one hz2
  rcases (Nat.dvd_prime Nat.prime_two).1 hd with h1 | h2
  · rw [orderOf_eq_one_iff.1 h1, one_zpow]
    exact Or.inl rfl
  · rw [← zpow_mod_orderOf, h2]
    have hk : k % ((2 : ℕ) : ℤ) = 0 ∨ k % ((2 : ℕ) : ℤ) = 1 := by omega
    rcases hk with h | h
    · left
      rw [h, zpow_zero]
    · right
      rw [h, zpow_one]

theorem key_lemma {Q : Subgroup G} {z : G} (hzN : z ∈ Subgroup.normalizer (Q : Set G))
    (hz2 : z ^ 2 = 1) (hQz : ⁅Q, Subgroup.zpowers z⁆ = Q) (u : ↥Q) :
    z * (u : G) * z * u ∈ ⁅Q, Q⁆ := by
  classical
  have hzz : z * z = 1 := by rw [← sq]; exact hz2
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  set τ : Abelianization ↥Q →* Abelianization ↥Q := Abelianization.map (conjQ Q hzN) with hτdef
  have hc : (conjQ Q hzN).comp (conjQ Q hzN) = MonoidHom.id ↥Q := by
    ext x
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, conjQ_coe]
    rw [hzinv]
    calc z * (z * (x : G) * z) * z = (z * z) * (x : G) * (z * z) := by group
      _ = (x : G) := by rw [hzz, one_mul, mul_one]
  have hτ2 : ∀ v, τ (τ v) = v := by
    intro v
    have h : τ.comp τ = MonoidHom.id _ := by
      rw [hτdef, Abelianization.map_comp, hc, Abelianization.map_id]
    exact DFunLike.congr_fun h v
  let ψ : Abelianization ↥Q →* Abelianization ↥Q :=
    MonoidHom.mk' (fun v => τ v * v⁻¹) (fun a b => by
      simp only [map_mul, mul_inv]
      exact mul_mul_mul_comm _ _ _ _)
  set S := ψ.range with hS
  let Lz : Subgroup G :=
    { carrier := {g | ∃ h : g ∈ Q, Abelianization.of (⟨g, h⟩ : ↥Q) ∈ S}
      mul_mem' := by
        rintro a b ⟨ha, hA⟩ ⟨hb, hB⟩
        refine ⟨Q.mul_mem ha hb, ?_⟩
        have e : (⟨a * b, Q.mul_mem ha hb⟩ : ↥Q) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
        rw [e, map_mul]
        exact S.mul_mem hA hB
      one_mem' := ⟨Q.one_mem, by
        have e : (⟨1, Q.one_mem⟩ : ↥Q) = 1 := rfl
        rw [e, map_one]
        exact S.one_mem⟩
      inv_mem' := by
        rintro a ⟨ha, hA⟩
        refine ⟨Q.inv_mem ha, ?_⟩
        have e : (⟨a⁻¹, Q.inv_mem ha⟩ : ↥Q) = (⟨a, ha⟩ : ↥Q)⁻¹ := rfl
        rw [e, map_inv]
        exact S.inv_mem hA }
  have hle : ⁅Q, Subgroup.zpowers z⁆ ≤ Lz := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rcases zpowers_cases hz2 hb with h | h
    · rw [h, commutatorElement_one_right]
      exact Lz.one_mem
    · rw [h]
      have hc' : z * a⁻¹ * z⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.1 hzN a⁻¹).1 (Q.inv_mem ha)
      have e : ⁅a, z⁆ = a * (z * a⁻¹ * z⁻¹) := by
        rw [commutatorElement_def]
        group
      have hmem : ⁅a, z⁆ ∈ Q := by
        rw [e]
        exact Q.mul_mem ha hc'
      refine ⟨hmem, ?_⟩
      have e1 : (⟨⁅a, z⁆, hmem⟩ : ↥Q) = ⟨a, ha⟩ * ⟨z * a⁻¹ * z⁻¹, hc'⟩ :=
        Subtype.ext (by simp only [Subgroup.coe_mul, e])
      have e2 : Abelianization.of (⟨z * a⁻¹ * z⁻¹, hc'⟩ : ↥Q) =
          τ (Abelianization.of (⟨a⁻¹, Q.inv_mem ha⟩ : ↥Q)) := rfl
      have e3 : Abelianization.of (⟨a⁻¹, Q.inv_mem ha⟩ : ↥Q) =
          (Abelianization.of (⟨a, ha⟩ : ↥Q))⁻¹ := by
        rw [← map_inv]
        rfl
      rw [e1, map_mul, e2, e3, map_inv]
      have hw : (Abelianization.of (⟨a, ha⟩ : ↥Q)) * (τ (Abelianization.of (⟨a, ha⟩ : ↥Q)))⁻¹ =
          ((ψ (Abelianization.of (⟨a, ha⟩ : ↥Q)))⁻¹) := by
        simp only [ψ, MonoidHom.mk'_apply, mul_inv, inv_inv]
        rw [mul_comm]
      rw [hw]
      exact S.inv_mem (MonoidHom.mem_range.2 ⟨_, rfl⟩)
  have hQLz : Q ≤ Lz := hQz ▸ hle
  have hall : ∀ v : Abelianization ↥Q, v ∈ S := by
    intro v
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective v
    obtain ⟨h, hA⟩ := hQLz u.2
    have e : (⟨(u : G), h⟩ : ↥Q) = u := rfl
    rw [e] at hA
    exact hA
  have hτv : ∀ v : Abelianization ↥Q, τ v = v⁻¹ := by
    intro v
    obtain ⟨w, hw⟩ := MonoidHom.mem_range.1 (hall v)
    have hv : v = τ w * w⁻¹ := hw.symm
    rw [hv, map_mul, map_inv, hτ2, mul_inv, inv_inv, mul_comm]
  have h1 : τ (Abelianization.of u) = (Abelianization.of u)⁻¹ := hτv _
  have h2 : Abelianization.of (conjQ Q hzN u * u) = 1 := by
    rw [map_mul]
    have e : Abelianization.of (conjQ Q hzN u) = τ (Abelianization.of u) := rfl
    rw [e, h1, inv_mul_cancel]
  have h3 : conjQ Q hzN u * u ∈ _root_.commutator ↥Q := (QuotientGroup.eq_one_iff _).1 h2
  have h4 := (mem_commutator_iff Q _).1 h3
  rw [Subgroup.coe_mul, conjQ_coe, hzinv] at h4
  exact h4

end Key

section Irred

variable {G : Type} [Group G]

theorem conj_mem_commutator {Q : Subgroup G} {w : G} (hw : w ∈ Subgroup.normalizer (Q : Set G))
    {c : G} (hc : c ∈ ⁅Q, Q⁆) : w * c * w⁻¹ ∈ ⁅Q, Q⁆ := by
  have hle : ⁅Q, Q⁆ ≤ (⁅Q, Q⁆).comap (MulAut.conj w).toMonoidHom := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_comap]
    have ha' : w * a * w⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.1 hw a).1 ha
    have hb' : w * b * w⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.1 hw b).1 hb
    have e : (MulAut.conj w).toMonoidHom ⁅a, b⁆ = ⁅w * a * w⁻¹, w * b * w⁻¹⁆ := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Subgroup.commutator_mem_commutator ha' hb'
  exact (Subgroup.mem_comap.1 (hle hc))

theorem irr_of_minimal [Finite G] {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {Q T : Subgroup G} {z : G}
    (hzT : z ∈ T) (hzc : ∀ t ∈ T, z * t = t * z) (hz2 : z ^ 2 = 1)
    (hTN : T ≤ Subgroup.normalizer (Q : Set G)) (hexp : ∀ g ∈ Q, g ^ q = 1)
    (hkey : ∀ u : ↥Q, z * (u : G) * z * u ∈ ⁅Q, Q⁆)
    (hmin : ∀ Q' : Subgroup G, Q' ≤ Q → Q' ≠ ⊥ → T ≤ Subgroup.normalizer (Q' : Set G) →
      (⁅Q', Subgroup.zpowers z⁆ : Subgroup G) = Q' → Q' = Q)
    {P : Subgroup G} (hPQ : P ≤ Q) (hPN : ⁅Q, Q⁆ ≤ P) (hPT : T ≤ Subgroup.normalizer (P : Set G)) :
    P = ⁅Q, Q⁆ ∨ P = Q := by
  classical
  obtain ⟨m, hm⟩ : ∃ m : ℕ, q = 2 * m + 1 := by
    obtain ⟨m, hm⟩ := hq.odd_of_ne_two hq2
    exact ⟨m, hm⟩
  set N : Subgroup G := ⁅Q, Q⁆ with hN
  let S : Set (Subgroup G) := {X | X ≤ P ∧ T ≤ Subgroup.normalizer (X : Set G) ∧
    ∀ x ∈ P, ∃ w ∈ X, w⁻¹ * x ∈ N}
  have hPS : P ∈ S := ⟨le_rfl, hPT, fun x hx => ⟨x, hx, by simp⟩⟩
  obtain ⟨X, hXS, hXmin⟩ := Set.exists_min_image S (fun X => Nat.card X) (Set.toFinite _) ⟨P, hPS⟩
  obtain ⟨hXP, hXT, hXcov⟩ := hXS
  set Φ : Subgroup G := ⁅X, Subgroup.zpowers z⁆ with hΦ
  have hΦX : Φ ≤ X := by
    rw [hΦ, Subgroup.commutator_le]
    intro a ha b hb
    rcases zpowers_cases hz2 hb with h | h
    · rw [h, commutatorElement_one_right]
      exact X.one_mem
    · rw [h]
      have hc : z * a⁻¹ * z⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.1 (hXT hzT) a⁻¹).1 (X.inv_mem ha)
      have e : ⁅a, z⁆ = a * (z * a⁻¹ * z⁻¹) := by
        rw [commutatorElement_def]
        group
      rw [e]
      exact X.mul_mem ha hc
  have hconjΦ : ∀ t ∈ T, ∀ g ∈ Φ, t * g * t⁻¹ ∈ Φ := by
    intro t ht
    have hle : Φ ≤ Φ.comap (MulAut.conj t).toMonoidHom := by
      rw [hΦ, Subgroup.commutator_le]
      intro a ha b hb
      rw [Subgroup.mem_comap]
      have ha' : t * a * t⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.1 (hXT ht) a).1 ha
      have hb' : t * b * t⁻¹ ∈ Subgroup.zpowers z := by
        rcases zpowers_cases hz2 hb with h | h
        · rw [h, mul_one, mul_inv_cancel]
          exact Subgroup.one_mem _
        · rw [h]
          have : t * z * t⁻¹ = z := by
            rw [← hzc t ht]
            group
          rw [this]
          exact Subgroup.mem_zpowers z
      have e : (MulAut.conj t).toMonoidHom ⁅a, b⁆ = ⁅t * a * t⁻¹, t * b * t⁻¹⁆ := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        simp only [commutatorElement_def]
        group
      rw [e]
      exact Subgroup.commutator_mem_commutator ha' hb'
    intro g hg
    exact hle hg
  have hΦT : T ≤ Subgroup.normalizer (Φ : Set G) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact hconjΦ t ht h hh
    · intro hh
      have := hconjΦ t⁻¹ (T.inv_mem ht) _ hh
      simpa [mul_assoc] using this
  have hΦcov : ∀ x ∈ P, ∃ w ∈ Φ, w⁻¹ * x ∈ N := by
    intro x hx
    obtain ⟨w, hwX, hwx⟩ := hXcov x hx
    have hwQ : w ∈ Q := hPQ (hXP hwX)
    have hwN : w ∈ Subgroup.normalizer (Q : Set G) := Subgroup.le_normalizer hwQ
    set u : G := w ^ m with hu
    have huX : u ∈ X := X.pow_mem hwX m
    have huQ : u ∈ Q := Q.pow_mem hwQ m
    have hu2 : u ^ 2 = w⁻¹ := by
      have h1 : w ^ (2 * m) * w = 1 := by
        rw [← pow_succ, ← hm]
        exact hexp w hwQ
      rw [hu, ← pow_mul, mul_comm]
      exact eq_inv_of_mul_eq_one_left h1
    have hkk : z * u * z * u ∈ N := hkey ⟨u, huQ⟩
    have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hz2)
    have hcomm : ⁅u, z⁆ = u ^ 2 * (z * u * z * u)⁻¹ := by
      rw [commutatorElement_def, sq]
      simp only [mul_inv_rev, hzinv]
      group
    have hΦy : ⁅u, z⁆⁻¹ ∈ Φ :=
      Φ.inv_mem (Subgroup.commutator_mem_commutator huX (Subgroup.mem_zpowers z))
    refine ⟨⁅u, z⁆⁻¹, hΦy, ?_⟩
    have e1 : ⁅u, z⁆⁻¹⁻¹ = w⁻¹ * (z * u * z * u)⁻¹ := by
      rw [inv_inv, hcomm, hu2]
    rw [e1]
    have e2 : w⁻¹ * (z * u * z * u)⁻¹ * x = (w⁻¹ * (z * u * z * u)⁻¹ * w) * (w⁻¹ * x) := by
      group
    rw [e2]
    apply N.mul_mem _ hwx
    have hc := conj_mem_commutator (Subgroup.inv_mem _ hwN) (N.inv_mem hkk)
    simpa [inv_inv, mul_assoc] using hc
  have hΦeq : Φ = X :=
    Subgroup.eq_of_le_of_card_ge hΦX (hXmin Φ ⟨hΦX.trans hXP, hΦT, hΦcov⟩)
  have hXeq : ⁅X, Subgroup.zpowers z⁆ = X := hΦeq
  by_cases hX0 : X = ⊥
  · left
    apply le_antisymm
    · intro x hx
      obtain ⟨w, hw, hwx⟩ := hXcov x hx
      rw [hX0, Subgroup.mem_bot] at hw
      rw [hw, inv_one, one_mul] at hwx
      exact hwx
    · exact hPN
  · right
    have hXQ : X = Q := hmin X (hXP.trans hPQ) hX0 hXT hXeq
    exact le_antisymm hPQ (by rw [← hXQ]; exact hXP)

end Irred

section Rep

variable {G : Type} [Group G]

theorem conjQ_eq_id {Q : Subgroup G} {t : G} (ht : t ∈ Subgroup.normalizer (Q : Set G))
    (h : t = 1) : conjQ Q ht = MonoidHom.id ↥Q := by
  subst h
  ext x
  simp [conjQ_coe]

theorem piQ_inv (Q : Subgroup G) (x : ↥Q) : piQ Q x⁻¹ = -piQ Q x := by
  have h := piQ_mul Q x x⁻¹
  rw [mul_inv_cancel, piQ_one] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem piQ_eq_iff (Q : Subgroup G) (x y : ↥Q) :
    piQ Q x = piQ Q y ↔ x⁻¹ * y ∈ _root_.commutator ↥Q := by
  unfold piQ
  rw [Additive.ofMul.injective.eq_iff, ← QuotientGroup.eq]
  rfl

theorem qA_exp {q : ℕ} {Q : Subgroup G} (hexp : ∀ g ∈ Q, g ^ q = 1) (v : QA Q) : q • v = 0 := by
  obtain ⟨g, rfl⟩ := piQ_surjective Q v
  have hg : g ^ q = 1 := Subtype.ext (by simpa using hexp g g.2)
  have key : piQ Q (g ^ q) = q • piQ Q g := by
    simp only [piQ, map_pow, ofMul_pow]
  rw [hg, piQ_one] at key
  exact key.symm

variable (Q : Subgroup G) (q : ℕ) [Module (ZMod q) (QA Q)]

@[expose] def repQ (T : Subgroup G) (hT : T ≤ Subgroup.normalizer (Q : Set G)) :
    ↥T →* (QA Q →ₗ[ZMod q] QA Q) where
  toFun t := linQ Q q (conjQ Q (hT t.2))
  map_one' := by
    show linQ Q q (conjQ Q (hT (1 : ↥T).2)) = 1
    rw [conjQ_eq_id _ (by simp), linQ_id]
  map_mul' s t := by
    have h : conjQ Q (hT (s * t).2) = (conjQ Q (hT s.2)).comp (conjQ Q (hT t.2)) :=
      conjQ_mul Q (hT s.2) (hT t.2)
    show linQ Q q (conjQ Q (hT (s * t).2)) = linQ Q q (conjQ Q (hT s.2)) * linQ Q q (conjQ Q (hT t.2))
    rw [h, linQ_comp]

theorem repQ_piQ (T : Subgroup G) (hT : T ≤ Subgroup.normalizer (Q : Set G)) (t : ↥T)
    (x : ↥Q) : repQ Q q T hT t (piQ Q x) = piQ Q ⟨t * x * (t : G)⁻¹, (Subgroup.mem_normalizer_iff.1 (hT t.2) x).1 x.2⟩ := by
  show linQ Q q (conjQ Q (hT t.2)) (piQ Q x) = _
  rw [linQ_piQ]
  rfl

@[expose] def preQ (W : Submodule (ZMod q) (QA Q)) : Subgroup G where
  carrier := {g | ∃ h : g ∈ Q, piQ Q ⟨g, h⟩ ∈ W}
  mul_mem' := by
    rintro a b ⟨ha, hA⟩ ⟨hb, hB⟩
    refine ⟨Q.mul_mem ha hb, ?_⟩
    have e : (⟨a * b, Q.mul_mem ha hb⟩ : ↥Q) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
    rw [e, piQ_mul]
    exact W.add_mem hA hB
  one_mem' := ⟨Q.one_mem, by
    have e : (⟨1, Q.one_mem⟩ : ↥Q) = 1 := rfl
    rw [e, piQ_one]
    exact W.zero_mem⟩
  inv_mem' := by
    rintro a ⟨ha, hA⟩
    refine ⟨Q.inv_mem ha, ?_⟩
    have e : (⟨a⁻¹, Q.inv_mem ha⟩ : ↥Q) = (⟨a, ha⟩ : ↥Q)⁻¹ := rfl
    rw [e, piQ_inv]
    exact W.neg_mem hA

end Rep

section Irr2

variable {G : Type} [Group G] [Finite G]

theorem irr_module {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {Q T : Subgroup G} {z : G}
    (hzT : z ∈ T) (hzc : ∀ t ∈ T, z * t = t * z) (hz2 : z ^ 2 = 1)
    (hTN : T ≤ Subgroup.normalizer (Q : Set G)) (hexp : ∀ g ∈ Q, g ^ q = 1)
    [Module (ZMod q) (QA Q)]
    (hkey : ∀ u : ↥Q, z * (u : G) * z * u ∈ ⁅Q, Q⁆)
    (hmin : ∀ Q' : Subgroup G, Q' ≤ Q → Q' ≠ ⊥ → T ≤ Subgroup.normalizer (Q' : Set G) →
      (⁅Q', Subgroup.zpowers z⁆ : Subgroup G) = Q' → Q' = Q)
    (W : Submodule (ZMod q) (QA Q)) (hW : ∀ t : ↥T, ∀ w ∈ W, repQ Q q T hTN t w ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  have hle : preQ Q q W ≤ Q := fun g hg => hg.1
  have hcomm : ⁅Q, Q⁆ ≤ preQ Q q W := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have hmem : (⁅a, b⁆ : G) ∈ ⁅Q, Q⁆ := Subgroup.commutator_mem_commutator ha hb
    have hQ : (⁅a, b⁆ : G) ∈ Q := by
      rw [commutatorElement_def]
      exact Q.mul_mem (Q.mul_mem (Q.mul_mem ha hb) (Q.inv_mem ha)) (Q.inv_mem hb)
    refine ⟨hQ, ?_⟩
    have h0 : piQ Q ⟨⁅a, b⁆, hQ⟩ = 0 := (piQ_eq_zero_iff Q ⟨⁅a, b⁆, hQ⟩).2 hmem
    rw [h0]
    exact W.zero_mem
  have hnorm : T ≤ Subgroup.normalizer (preQ Q q W : Set G) := by
    have hconj : ∀ t : ↥T, ∀ g ∈ preQ Q q W, (t : G) * g * (t : G)⁻¹ ∈ preQ Q q W := by
      rintro t g ⟨hgQ, hgW⟩
      have hmemQ : (t : G) * g * (t : G)⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.1 (hTN t.2) g).1 hgQ
      refine ⟨hmemQ, ?_⟩
      have e := repQ_piQ Q q T hTN t ⟨g, hgQ⟩
      have hW' := hW t _ hgW
      rw [e] at hW'
      exact hW'
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact hconj ⟨t, ht⟩ h hh
    · intro hh
      have := hconj ⟨t⁻¹, T.inv_mem ht⟩ _ hh
      simpa [mul_assoc] using this
  rcases irr_of_minimal hq hq2 hzT hzc hz2 hTN hexp hkey hmin hle hcomm hnorm with h | h
  · left
    apply eq_bot_iff.2
    intro v hv
    obtain ⟨x, rfl⟩ := piQ_surjective Q v
    have hxP : (x : G) ∈ preQ Q q W := ⟨x.2, hv⟩
    rw [h] at hxP
    exact (Submodule.mem_bot _).2 ((piQ_eq_zero_iff Q x).2 hxP)
  · right
    apply eq_top_iff.2
    intro v _
    obtain ⟨x, rfl⟩ := piQ_surjective Q v
    have hxP : (x : G) ∈ preQ Q q W := by
      rw [h]
      exact x.2
    obtain ⟨_, hx⟩ := hxP
    exact hx

end Irr2

section Lift

variable {G : Type} [Group G] [Finite G]

theorem repQ_neg_one {q : ℕ} {Q T : Subgroup G} {z : G} (hzT : z ∈ T) (hz2 : z ^ 2 = 1)
    (hTN : T ≤ Subgroup.normalizer (Q : Set G)) [Module (ZMod q) (QA Q)]
    (hkey : ∀ u : ↥Q, z * (u : G) * z * u ∈ ⁅Q, Q⁆) :
    repQ Q q T hTN ⟨z, hzT⟩ = -1 := by
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hz2)
  apply LinearMap.ext
  intro v
  obtain ⟨x, rfl⟩ := piQ_surjective Q v
  rw [repQ_piQ, LinearMap.neg_apply, Module.End.one_apply]
  apply eq_neg_of_add_eq_zero_left
  rw [← piQ_mul, piQ_eq_zero_iff, Subgroup.coe_mul]
  show z * (x : G) * z⁻¹ * x ∈ _
  rw [hzinv]
  exact hkey x

theorem lift_fixed {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {Q : Subgroup G} (hexp : ∀ g ∈ Q, g ^ q = 1)
    [Module (ZMod q) (QA Q)] {T : Subgroup G} (hTN : T ≤ Subgroup.normalizer (Q : Set G))
    {t : G} (htT : t ∈ T) (ht2 : t ^ 2 = 1) (x : ↥Q)
    (hx : repQ Q q T hTN ⟨t, htT⟩ (piQ Q x) = piQ Q x) :
    ∃ y : ↥Q, t * (y : G) = (y : G) * t ∧ piQ Q y = piQ Q x := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  set σ : ↥Q →* ↥Q := conjQ Q (hTN htT) with hσdef
  have hσσ : σ.comp σ = MonoidHom.id ↥Q := by
    rw [hσdef, ← conjQ_mul]
    exact conjQ_eq_id _ (by rw [← sq]; exact ht2)
  have hmap : Subgroup.map σ (_root_.commutator ↥Q) ≤ _root_.commutator ↥Q := by
    show Subgroup.map σ ⁅(⊤ : Subgroup ↥Q), (⊤ : Subgroup ↥Q)⁆ ≤ ⁅(⊤ : Subgroup ↥Q), (⊤ : Subgroup ↥Q)⁆
    rw [Subgroup.map_commutator]
    exact Subgroup.commutator_mono le_top le_top
  have hNσ : ∀ n ∈ _root_.commutator ↥Q, σ n ∈ _root_.commutator ↥Q :=
    fun n hn => hmap (Subgroup.mem_map_of_mem σ hn)
  have hP : IsPGroup q ↥Q := fun g => ⟨1, Subtype.ext (by simpa using hexp g g.2)⟩
  have hodd : Odd (Nat.card (_root_.commutator ↥Q)) := by
    obtain ⟨k, hk⟩ := hP.exists_card_eq
    have hdvd : Nat.card (_root_.commutator ↥Q) ∣ q ^ k := by
      rw [← hk]
      exact Subgroup.card_subgroup_dvd_card _
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hq).1 hdvd
    rw [hj]
    exact Odd.pow (hq.odd_of_ne_two hq2)
  have hx' : σ x = x * (x⁻¹ * σ x) := by group
  have hxn : x⁻¹ * σ x ∈ _root_.commutator ↥Q := by
    have hxe : piQ Q (σ x) = piQ Q x := hx
    exact (piQ_eq_iff Q x (σ x)).1 hxe.symm
  obtain ⟨y, hyfix, hyx⟩ := exists_fixed_mem_coset (_root_.commutator ↥Q) hodd σ hσσ hNσ x
    ⟨x⁻¹ * σ x, hxn, hx'⟩
  refine ⟨y, ?_, ?_⟩
  · have h1 : (σ y : ↥Q) = y := by rw [hyfix]
    have h2 : t * (y : G) * t⁻¹ = y := by
      have := congrArg Subtype.val h1
      simpa [hσdef, conjQ_coe] using this
    exact (mul_inv_eq_iff_eq_mul).1 h2
  · exact ((piQ_eq_iff Q x y).2 hyx).symm

end Lift

section Count

variable {G : Type} [Group G] [Finite G]

theorem mem_centralizer_pair_iff {t g : G} : g ∈ Subgroup.centralizer ({t} : Set G) ↔ t * g = g * t := by
  constructor
  · intro hg
    exact Subgroup.mem_centralizer_iff.1 hg t (Set.mem_singleton t)
  · intro h
    exact Subgroup.mem_centralizer_iff.2 (fun k hk => by
      rw [Set.mem_singleton_iff.1 hk]
      exact h)

theorem card_centralizer_eq {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {Q T : Subgroup G}
    (hexp : ∀ g ∈ Q, g ^ q = 1) [Module (ZMod q) (QA Q)] (hTN : T ≤ Subgroup.normalizer (Q : Set G))
    {t : G} (htT : t ∈ T) (ht2 : t ^ 2 = 1) :
    Nat.card ↥(Q ⊓ Subgroup.centralizer ({t} : Set G)) =
      Nat.card ↥(Q ⊓ Subgroup.centralizer ({t} : Set G) ⊓ ⁅Q, Q⁆) *
        q ^ Module.finrank (ZMod q) ↥(Module.End.eigenspace (repQ Q q T hTN ⟨t, htT⟩) (1 : ZMod q)) := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  set C : Subgroup G := Q ⊓ Subgroup.centralizer ({t} : Set G) with hC
  set E := Module.End.eigenspace (repQ Q q T hTN ⟨t, htT⟩) (1 : ZMod q) with hE
  let ψ : ↥C →* Abelianization ↥Q := (Abelianization.of).comp (Subgroup.inclusion inf_le_left)
  have hψ : ∀ x : ↥C, ψ x = Abelianization.of (⟨(x : G), x.2.1⟩ : ↥Q) := fun x => rfl
  have hcard := Subgroup.card_ker_mul_card_range ψ
  have hmapk : ψ.ker.map C.subtype = C ⊓ ⁅Q, Q⁆ := by
    ext g
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : ψ x = 1 := hx
      rw [hψ] at hx'
      have hx2 := (QuotientGroup.eq_one_iff _).1 hx'
      exact Subgroup.mem_inf.2 ⟨x.2, (mem_commutator_iff Q _).1 hx2⟩
    · rintro ⟨hgC, hgN⟩
      refine ⟨⟨g, hgC⟩, ?_, rfl⟩
      show ψ ⟨g, hgC⟩ = 1
      rw [hψ]
      apply (QuotientGroup.eq_one_iff _).2
      exact (mem_commutator_iff Q _).2 hgN
  have hker : Nat.card ψ.ker = Nat.card ↥(C ⊓ ⁅Q, Q⁆) := by
    rw [← hmapk, Subgroup.card_map_of_injective C.subtype_injective]
  have hmemE : ∀ c : ↥Q, t * (c : G) = (c : G) * t → piQ Q c ∈ E := by
    intro c hc
    rw [hE, Module.End.mem_eigenspace_iff, repQ_piQ, one_smul]
    congr 1
    apply Subtype.ext
    show (t : G) * c * t⁻¹ = c
    rw [hc, mul_inv_cancel_right]
  have hrange : Nat.card ψ.range = Nat.card E := by
    apply Nat.card_congr
    refine Equiv.ofBijective (fun x => ⟨Additive.ofMul x.1, ?_⟩) ⟨?_, ?_⟩
    · obtain ⟨c, hc⟩ := MonoidHom.mem_range.1 x.2
      have hcomm : t * (c : G) = (c : G) * t := Subgroup.mem_centralizer_iff.1 c.2.2 t (Set.mem_singleton t)
      have := hmemE ⟨c, c.2.1⟩ hcomm
      rw [← hc, hψ]
      exact this
    · intro x x' hxx
      have h2 := congrArg (fun y : ↥E => (y : QA Q)) hxx
      exact Subtype.ext (Additive.ofMul.injective h2)
    · intro e
      obtain ⟨x, hx⟩ := piQ_surjective Q e.1
      have h1 : repQ Q q T hTN ⟨t, htT⟩ (e.1) = e.1 := by
        have h2 : e.1 ∈ Module.End.eigenspace (repQ Q q T hTN ⟨t, htT⟩) (1 : ZMod q) := e.2
        rw [Module.End.mem_eigenspace_iff, one_smul] at h2
        exact h2
      have hfix : repQ Q q T hTN ⟨t, htT⟩ (piQ Q x) = piQ Q x := by
        rw [hx]
        exact h1
      obtain ⟨y, hyc, hyx⟩ := lift_fixed hq hq2 hexp hTN htT ht2 x hfix
      have hyC : (y : G) ∈ C := ⟨y.2, mem_centralizer_pair_iff.2 hyc⟩
      refine ⟨⟨ψ ⟨y, hyC⟩, MonoidHom.mem_range.2 ⟨⟨y, hyC⟩, rfl⟩⟩, ?_⟩
      apply Subtype.ext
      show piQ Q y = e.1
      exact hyx.trans hx
  have hE_card : Nat.card ↥E = q ^ Module.finrank (ZMod q) ↥E := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod q) (V := ↥E), Nat.card_zmod]
  rw [← hcard, hker, hrange, hE_card]

end Count

end XRep

open XRep

section Glue

variable {G : Type} [Group G] [Finite G]

theorem map_commutator_subtype_eq (Q : Subgroup G) :
    (_root_.commutator ↥Q).map Q.subtype = ⁅Q, Q⁆ := by
  show ((⁅(⊤ : Subgroup ↥Q), (⊤ : Subgroup ↥Q)⁆ : Subgroup ↥Q)).map Q.subtype = ⁅Q, Q⁆
  rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem card_Q_eq (Q : Subgroup G) :
    Nat.card ↥Q = Nat.card (QA Q) * Nat.card ↥(⁅Q, Q⁆ : Subgroup G) := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (_root_.commutator ↥Q)
  have h2 : Nat.card ↥((_root_.commutator ↥Q).map Q.subtype) = Nat.card ↥(_root_.commutator ↥Q) :=
    Subgroup.card_map_of_injective Q.subtype_injective
  rw [map_commutator_subtype_eq] at h2
  have h3 : Nat.card (QA Q) = Nat.card (↥Q ⧸ _root_.commutator ↥Q) :=
    Nat.card_congr (Additive.toMul : QA Q ≃ Abelianization ↥Q)
  rw [h1, h2, h3]

theorem exists_ne_one_of_card_eq {Z : Subgroup G} (h : Nat.card ↥Z = 2 ^ 3) : ∃ e ∈ Z, e ≠ 1 := by
  by_contra hcon
  have hbot : Z = ⊥ := eq_bot_iff.2 (fun e he => by
    by_contra hne
    exact hcon ⟨e, he, hne⟩)
  rw [hbot, Subgroup.card_bot] at h
  norm_num at h

theorem sq_eq_one_of_center {T : Subgroup G} {n : ℕ} (hT : IsExtraspecialTwo T n) {z : G}
    (hzT : z ∈ T ⊓ Subgroup.centralizer (T : Set G)) : z ^ 2 = 1 := by
  have hc : Nat.card (Subgroup.center ↥T) = 2 := hT.1.2.2.2
  have hmem : (⟨z, hzT.1⟩ : ↥T) ∈ Subgroup.center ↥T := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hzT.2 (g : G) g.2)
  let a : ↥(Subgroup.center ↥T) := ⟨⟨z, hzT.1⟩, hmem⟩
  have h1 : a ^ Nat.card ↥(Subgroup.center ↥T) = 1 := pow_card_eq_one'
  rw [hc] at h1
  have h2 := congrArg (fun y : ↥(Subgroup.center ↥T) => ((y : ↥T) : G)) h1
  simpa [pow_two, a] using h2

end Glue

section RepAt

theorem two_ne_zero_zmod {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) : (2 : ZMod q) ≠ 0 := by
  intro h
  have h2 : ((2 : ℕ) : ZMod q) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff (ZMod q) q] at h2
  exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 h2)

theorem extraspecialRepAt_holds : CFSG.LocalAnalysis.GLTheoremA.ExtraspecialRepAt := by
  unfold CFSG.LocalAnalysis.GLTheoremA.ExtraspecialRepAt
  intro G _ _ q n T Q z hq hq2 hT hzT hz1 hexp hcl hTN hQne hQz hmin
  haveI : Fact q.Prime := ⟨hq⟩
  have hz2 : z ^ 2 = 1 := sq_eq_one_of_center hT hzT
  have hzT' : z ∈ T := hzT.1
  have hzN : z ∈ Subgroup.normalizer (Q : Set G) := hTN hzT'
  have hzc : ∀ t ∈ T, z * t = t * z := fun t ht => (Subgroup.mem_centralizer_iff.1 hzT.2 t ht).symm
  have hcard' : Nat.card ↥T = 2 ^ (1 + 2 * n) := by
    rw [hT.2, Nat.add_comm]
  have hcenter : Subgroup.center ↥T = Subgroup.zpowers (⟨z, hzT'⟩ : ↥T) := by
    have hzc' : (⟨z, hzT'⟩ : ↥T) ∈ Subgroup.center ↥T := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hzT.2 (g : G) g.2)
    have hord : orderOf (⟨z, hzT'⟩ : ↥T) = 2 := by
      apply orderOf_eq_prime
      · exact Subtype.ext (by simpa using hz2)
      · intro h
        apply hz1
        simpa using congrArg Subtype.val h
    have hcz : Nat.card (Subgroup.zpowers (⟨z, hzT'⟩ : ↥T)) = 2 := by
      rw [Nat.card_zpowers, hord]
    have hle : Subgroup.zpowers (⟨z, hzT'⟩ : ↥T) ≤ Subgroup.center ↥T :=
      Subgroup.zpowers_le.2 hzc'
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hT.1.2.2.2, hcz])).symm
  haveI : Module (ZMod q) (QA Q) := AddCommGroup.zmodModule (qA_exp hexp)
  haveI : Finite (QA Q) := inferInstance
  have hP : IsPGroup q ↥Q := fun g => ⟨1, Subtype.ext (by simpa using hexp g g.2)⟩
  haveI : Group.IsNilpotent ↥Q := hP.isNilpotent
  haveI : Nontrivial (QA Q) := by
    have hQnt : Nontrivial ↥Q := (Subgroup.nontrivial_iff_ne_bot Q).2 hQne
    obtain ⟨x, hx⟩ : ∃ x : ↥Q, x ∉ _root_.commutator ↥Q := by
      by_contra hcon
      push Not at hcon
      have htop : _root_.commutator ↥Q = ⊤ := eq_top_iff.2 (fun x _ => hcon x)
      have hlt := IsSolvable.commutator_lt_top_of_nontrivial (G := ↥Q)
      rw [htop] at hlt
      exact lt_irrefl _ hlt
    exact ⟨⟨piQ Q x, 0, fun h => hx ((mem_commutator_iff Q x).2 ((piQ_eq_zero_iff Q x).1 h))⟩⟩
  have hkey : ∀ u : ↥Q, z * (u : G) * z * u ∈ ⁅Q, Q⁆ := key_lemma hzN hz2 hQz
  have hirr : ∀ W : Submodule (ZMod q) (QA Q),
      (∀ t : ↥T, ∀ w : QA Q, w ∈ W → (repQ Q q T hTN t : QA Q →ₗ[ZMod q] QA Q) w ∈ W) →
        W = ⊥ ∨ W = ⊤ :=
    fun W hW => irr_module hq hq2 hzT' hzc hz2 hTN hexp hkey hmin W hW
  have hρz : repQ Q q T hTN ⟨z, hzT'⟩ = -1 := repQ_neg_one hzT' hz2 hTN hkey
  have hfin : Module.finrank (ZMod q) (QA Q) = 2 ^ n :=
    finrank_eq_pow_of_irreducible q hq2 hT.1 hcard' hcenter (repQ Q q T hTN) hρz hirr
  have hVcard : Nat.card (QA Q) = q ^ 2 ^ n := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod q) (V := QA Q), hfin, Nat.card_zmod]
  have hK : (2 : ZMod q) ≠ 0 := two_ne_zero_zmod hq hq2
  refine ⟨?_, ?_⟩
  · rw [card_Q_eq Q, hVcard]
  · intro t htT ht2 htZ
    have hs_notin : (⟨t, htT⟩ : ↥T) ∉ Subgroup.center ↥T := by
      intro hmem
      apply htZ
      refine ⟨htT, Subgroup.mem_centralizer_iff.2 (fun g hg => ?_)⟩
      have := Subgroup.mem_center_iff.1 hmem ⟨g, hg⟩
      exact congrArg Subtype.val this
    have hs1 : (⟨t, htT⟩ : ↥T) ≠ 1 := fun h => hs_notin (h ▸ Subgroup.one_mem _)
    have hs2 : (⟨t, htT⟩ : ↥T) ^ 2 = 1 := Subtype.ext (by simpa using ht2)
    have hord : orderOf (⟨t, htT⟩ : ↥T) = 2 := orderOf_eq_prime hs2 hs1
    have hmin2 := (CFSG.RankThree.GroupTheory.extraspecial_two_minus_module_bound hT.1 hcard'
      hcenter hK (ρ := repQ Q q T hTN) hρz).2 ⟨t, htT⟩ hs_notin hord
    have hfinE : Module.finrank (ZMod q)
        (Module.End.eigenspace (repQ Q q T hTN ⟨t, htT⟩) (1 : ZMod q)) = 2 ^ (n - 1) := by
      have h1 := hmin2.1
      rw [hfin] at h1
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        simp at h1
      · have h2 : 2 ^ n = 2 * 2 ^ (n - 1) := by
          rw [← pow_succ']
          congr 1
          omega
        omega
    rw [card_centralizer_eq hq hq2 hexp hTN htT ht2, hfinE, mul_comm]

end RepAt

theorem mem_T_of_inf {G : Type} [Group G] {T : Subgroup G} {C : Subgroup G} {x : G}
    (h : x ∈ T ⊓ C) : x ∈ T :=
  (Subgroup.mem_inf.1 h).1

section Faithful

variable {G : Type} [Group G] [Finite G]

theorem faithful_of {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {Q T : Subgroup G} (hexp : ∀ g ∈ Q, g ^ q = 1)
    [Module (ZMod q) (QA Q)] (hTN : T ≤ Subgroup.normalizer (Q : Set G))
    (hfaith : T ⊓ Subgroup.centralizer (Q : Set G) = ⊥) {e : G} (heT : e ∈ T) (he2 : e ^ 2 = 1)
    (hact : repQ Q q T hTN ⟨e, heT⟩ = 1) : e = 1 := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hP : IsPGroup q ↥Q := fun g => ⟨1, Subtype.ext (by simpa using hexp g g.2)⟩
  haveI : Group.IsNilpotent ↥Q := hP.isNilpotent
  set H : Subgroup ↥Q := (Subgroup.centralizer ({e} : Set G)).subgroupOf Q with hH
  have hcover : H ⊔ _root_.commutator ↥Q = ⊤ := by
    rw [Subgroup.eq_top_iff']
    intro x
    have hfix : repQ Q q T hTN ⟨e, heT⟩ (piQ Q x) = piQ Q x := by
      rw [hact]
      rfl
    obtain ⟨y, hyc, hyx⟩ := lift_fixed hq hq2 hexp hTN heT he2 x hfix
    have hyH : y ∈ H := by
      rw [hH, Subgroup.mem_subgroupOf]
      exact mem_centralizer_pair_iff.2 hyc
    have hn : y⁻¹ * x ∈ _root_.commutator ↥Q := (piQ_eq_iff Q y x).1 hyx
    have := Subgroup.mul_mem_sup hyH hn
    simpa using this
  have hHtop : H = ⊤ := eq_top_of_sup_commutator_eq H hcover
  have hmem : e ∈ T ⊓ Subgroup.centralizer (Q : Set G) := by
    refine Subgroup.mem_inf.2 ⟨heT, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have hgQ : (⟨g, hg⟩ : ↥Q) ∈ H := by
      rw [hHtop]
      exact Subgroup.mem_top _
    rw [hH, Subgroup.mem_subgroupOf] at hgQ
    exact (mem_centralizer_pair_iff.1 hgQ).symm
  rw [hfaith, Subgroup.mem_bot] at hmem
  exact hmem

end Faithful

section Scalar

theorem exists_scalar_invariant {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {ι : Type*} (f : ι → Module.End K V)
    (hcomm : ∀ i j, Commute (f i) (f j)) (hsq : ∀ i, f i * f i = 1) (h2 : (2 : K) ≠ 0)
    (U : Submodule K V) (hU : U ≠ ⊥) (hUinv : ∀ i, ∀ u ∈ U, f i u ∈ U) :
    ∃ W : Submodule K V, W ≤ U ∧ W ≠ ⊥ ∧ (∀ i, ∀ w ∈ W, f i w ∈ W) ∧
      ∀ i, (∀ w ∈ W, f i w = w) ∨ (∀ w ∈ W, f i w = -w) := by
  classical
  let 𝒮 : Submodule K V → Prop := fun W => W ≤ U ∧ W ≠ ⊥ ∧ ∀ i, ∀ w ∈ W, f i w ∈ W
  have hex : ∃ n, ∃ W, 𝒮 W ∧ Module.finrank K W = n := ⟨_, U, ⟨le_rfl, hU, hUinv⟩, rfl⟩
  obtain ⟨W, hW𝒮, hWn⟩ := Nat.find_spec hex
  have hmin : ∀ W' : Submodule K V, 𝒮 W' → Module.finrank K W ≤ Module.finrank K W' := by
    intro W' hW'
    have := Nat.find_min' hex ⟨W', hW', rfl⟩
    rw [← hWn] at this
    exact this
  obtain ⟨hWU, hW0, hWinv⟩ := hW𝒮
  have hfsq : ∀ i w, f i (f i w) = w := fun i w => by
    have := DFunLike.congr_fun (hsq i) w
    simpa [Module.End.mul_apply] using this
  have hA : ∀ i, ∀ w ∈ W, (2 : K)⁻¹ • (w + f i w) ∈ W ⊓ Module.End.eigenspace (f i) 1 := by
    intro i w hw
    refine Submodule.mem_inf.2 ⟨W.smul_mem _ (W.add_mem hw (hWinv i w hw)), ?_⟩
    rw [Module.End.mem_eigenspace_iff, map_smul, map_add, hfsq, add_comm, one_smul]
  have hB : ∀ i, ∀ w ∈ W, (2 : K)⁻¹ • (w - f i w) ∈ W ⊓ Module.End.eigenspace (f i) (-1) := by
    intro i w hw
    refine Submodule.mem_inf.2 ⟨W.smul_mem _ (W.sub_mem hw (hWinv i w hw)), ?_⟩
    rw [Module.End.mem_eigenspace_iff, map_smul, map_sub, hfsq, ← neg_sub w (f i w), smul_neg,
      neg_one_smul]
  have hdec : ∀ i, ∀ w ∈ W, w = (2 : K)⁻¹ • (w + f i w) + (2 : K)⁻¹ • (w - f i w) := by
    intro i w _
    have e1 : (w + f i w) + (w - f i w) = (2 : K) • w := by
      rw [two_smul]
      abel
    rw [← smul_add, e1, inv_smul_smul₀ h2]
  have hcase : ∀ i, (W ⊓ Module.End.eigenspace (f i) 1 = ⊥) ∨
      (W ⊓ Module.End.eigenspace (f i) (-1) = ⊥) := by
    intro i
    by_contra hcon
    push Not at hcon
    obtain ⟨hp, hm⟩ := hcon
    set Wp := W ⊓ Module.End.eigenspace (f i) 1 with hWp_def
    set Wm := W ⊓ Module.End.eigenspace (f i) (-1) with hWm_def
    have hWp𝒮 : 𝒮 Wp := by
      refine ⟨inf_le_of_left_le hWU, hp, fun j w hw => ?_⟩
      obtain ⟨hwW, hwe⟩ := Submodule.mem_inf.1 hw
      refine Submodule.mem_inf.2 ⟨hWinv j w hwW, ?_⟩
      rw [Module.End.mem_eigenspace_iff] at hwe ⊢
      have hc : f i (f j w) = f j (f i w) := by
        rw [← Module.End.mul_apply, (hcomm i j).eq, Module.End.mul_apply]
      rw [hc, hwe, map_smul, one_smul]
    have hWm𝒮 : 𝒮 Wm := by
      refine ⟨inf_le_of_left_le hWU, hm, fun j w hw => ?_⟩
      obtain ⟨hwW, hwe⟩ := Submodule.mem_inf.1 hw
      refine Submodule.mem_inf.2 ⟨hWinv j w hwW, ?_⟩
      rw [Module.End.mem_eigenspace_iff] at hwe ⊢
      have hc : f i (f j w) = f j (f i w) := by
        rw [← Module.End.mul_apply, (hcomm i j).eq, Module.End.mul_apply]
      rw [hc, hwe, map_smul]
    have hsum : Wp ⊔ Wm = W := by
      refine le_antisymm (sup_le inf_le_left inf_le_left) (fun w hw => ?_)
      have hdw := hdec i w hw
      rw [hdw]
      exact Submodule.add_mem_sup (hA i w hw) (hB i w hw)
    have hinf : Wp ⊓ Wm = ⊥ := by
      rw [eq_bot_iff]
      intro w hw
      obtain ⟨hwp, hwm⟩ := Submodule.mem_inf.1 hw
      obtain ⟨_, e1⟩ := Submodule.mem_inf.1 hwp
      obtain ⟨_, e2⟩ := Submodule.mem_inf.1 hwm
      rw [Module.End.mem_eigenspace_iff] at e1 e2
      have h4 : w = -w := by
        have := e1.symm.trans e2
        rwa [one_smul, neg_one_smul] at this
      have h3 : (2 : K) • w = 0 := by
        rw [two_smul]
        nth_rewrite 1 [h4]
        exact neg_add_cancel w
      exact (Submodule.mem_bot K).2 ((smul_eq_zero.1 h3).resolve_left h2)
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq Wp Wm
    rw [hsum, hinf, finrank_bot, add_zero] at h1
    have hm0 : Module.finrank K Wm ≠ 0 := fun h => hm (Submodule.finrank_eq_zero.1 h)
    have := hmin Wp hWp𝒮
    have := hmin Wm hWm𝒮
    omega
  refine ⟨W, hWU, hW0, hWinv, fun i => ?_⟩
  rcases hcase i with h | h
  · right
    intro w hw
    have hmemp := hA i w hw
    rw [h, Submodule.mem_bot] at hmemp
    have h5 : w + f i w = 0 := (smul_eq_zero.1 hmemp).resolve_left (inv_ne_zero h2)
    exact eq_neg_of_add_eq_zero_right h5
  · left
    intro w hw
    have hmemm := hB i w hw
    rw [h, Submodule.mem_bot] at hmemm
    have h5 : w - f i w = 0 := (smul_eq_zero.1 hmemm).resolve_left (inv_ne_zero h2)
    exact (sub_eq_zero.1 h5).symm

end Scalar

section Kernel

variable {G : Type} [Group G] [Finite G]

@[expose] def cenV0 {q : ℕ} {Q T : Subgroup G} [Module (ZMod q) (QA Q)]
    (hTN : T ≤ Subgroup.normalizer (Q : Set G)) (W : Submodule (ZMod q) (QA Q)) : Subgroup G where
  carrier := {g | ∃ hg : g ∈ T ⊓ Subgroup.centralizer (T : Set G),
    ∀ w ∈ W, repQ Q q T hTN ⟨g, hg.1⟩ w = w}
  mul_mem' := by
    rintro a b ⟨ha, hA⟩ ⟨hb, hB⟩
    refine ⟨Subgroup.mul_mem _ ha hb, fun w hw => ?_⟩
    have e : (⟨a * b, (Subgroup.mul_mem _ ha hb).1⟩ : ↥T) = ⟨a, ha.1⟩ * ⟨b, hb.1⟩ := rfl
    rw [e, map_mul, Module.End.mul_apply, hB w hw, hA w hw]
  one_mem' := ⟨Subgroup.one_mem _, fun w _ => by
    have e : (⟨1, (Subgroup.one_mem _ : (1 : G) ∈ T ⊓ Subgroup.centralizer (T : Set G)).1⟩ : ↥T) = 1 :=
      rfl
    rw [e, map_one, Module.End.one_apply]⟩
  inv_mem' := by
    rintro a ⟨ha, hA⟩
    refine ⟨Subgroup.inv_mem _ ha, fun w hw => ?_⟩
    have e : (⟨a⁻¹, (Subgroup.inv_mem _ ha).1⟩ : ↥T) = (⟨a, ha.1⟩ : ↥T)⁻¹ := rfl
    have hwa : repQ Q q T hTN ⟨a, ha.1⟩ w = w := hA w hw
    calc repQ Q q T hTN ⟨a⁻¹, (Subgroup.inv_mem _ ha).1⟩ w
        = repQ Q q T hTN ⟨a⁻¹, (Subgroup.inv_mem _ ha).1⟩
            (repQ Q q T hTN ⟨a, ha.1⟩ w) := by rw [hwa]
      _ = w := by
        rw [← Module.End.mul_apply, ← map_mul]
        have e2 : (⟨a⁻¹, (Subgroup.inv_mem _ ha).1⟩ : ↥T) * ⟨a, ha.1⟩ = 1 := by
          apply Subtype.ext
          simp
        rw [e2, map_one, Module.End.one_apply]

end Kernel

section KernelCard

variable {G : Type} [Group G] [Finite G]

theorem cenV0_mem_iff {q : ℕ} {Q T : Subgroup G} [Module (ZMod q) (QA Q)]
    (hTN : T ≤ Subgroup.normalizer (Q : Set G)) (W : Submodule (ZMod q) (QA Q)) (g : G) :
    g ∈ cenV0 hTN W ↔ ∃ hg : g ∈ T ⊓ Subgroup.centralizer (T : Set G),
      ∀ w ∈ W, repQ Q q T hTN ⟨g, hg.1⟩ w = w :=
  Iff.rfl

theorem cenV0_card {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {Q T : Subgroup G}
    [Module (ZMod q) (QA Q)] (hTN : T ≤ Subgroup.normalizer (Q : Set G))
    (hT2 : IsPGroup 2 T) (hZcard : Nat.card ↥(T ⊓ Subgroup.centralizer (T : Set G)) = 2 ^ 3)
    {e₀ : G} (he₀ : e₀ ∈ T ⊓ Subgroup.centralizer (T : Set G)) (he₀1 : e₀ ≠ 1)
    (he₀2 : e₀ ^ 2 = 1) (W : Submodule (ZMod q) (QA Q)) (hW0 : W ≠ ⊥)
    (hWU : W ≤ LinearMap.range (repQ Q q T hTN ⟨e₀, mem_T_of_inf he₀⟩ - 1))
    (hscal : ∀ e : G, ∀ he : e ∈ T ⊓ Subgroup.centralizer (T : Set G),
      (∀ w ∈ W, repQ Q q T hTN ⟨e, he.1⟩ w = w) ∨ (∀ w ∈ W, repQ Q q T hTN ⟨e, he.1⟩ w = -w)) :
    Nat.card ↥(cenV0 hTN W) = 4 ∧ e₀ ∉ cenV0 hTN W ∧
      cenV0 hTN W ≤ T ⊓ Subgroup.centralizer (T : Set G) := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  have hh : (2 : ZMod q) ≠ 0 := two_ne_zero_zmod hq hq2
  set Z : Subgroup G := T ⊓ Subgroup.centralizer (T : Set G) with hZ
  set V₀ : Subgroup G := cenV0 hTN W with hV₀
  have hV0Z : V₀ ≤ Z := fun g hg => (cenV0_mem_iff hTN W g).1 hg |>.elim fun hg' _ => hg'
  have hsq : ∀ v, repQ Q q T hTN ⟨e₀, mem_T_of_inf he₀⟩ (repQ Q q T hTN ⟨e₀, mem_T_of_inf he₀⟩ v) = v := by
    intro v
    rw [← Module.End.mul_apply, ← map_mul]
    have e : (⟨e₀, he₀.1⟩ * ⟨e₀, he₀.1⟩ : ↥T) = 1 := Subtype.ext (by simp [sq] at he₀2 ⊢; exact he₀2)
    rw [e, map_one, Module.End.one_apply]
  have hneg : ∀ w ∈ W, repQ Q q T hTN ⟨e₀, mem_T_of_inf he₀⟩ w = -w := by
    intro w hw
    obtain ⟨v, rfl⟩ := LinearMap.mem_range.1 (hWU hw)
    simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub, hsq]
    abel
  have hcover : ∀ g ∈ Z, g ∈ V₀ ∨ e₀ * g ∈ V₀ := by
    intro g hg
    rcases hscal g hg with hA | hB
    · exact Or.inl ((cenV0_mem_iff hTN W g).2 ⟨hg, hA⟩)
    · refine Or.inr ((cenV0_mem_iff hTN W (e₀ * g)).2 ⟨Subgroup.mul_mem _ he₀ hg, fun w hw => ?_⟩)
      have e : (⟨e₀ * g, (Subgroup.mul_mem _ he₀ hg).1⟩ : ↥T) = ⟨e₀, he₀.1⟩ * ⟨g, hg.1⟩ := rfl
      rw [e, map_mul, Module.End.mul_apply, hB w hw, map_neg, hneg w hw, neg_neg]
  have hZ8 : Nat.card ↥Z = 8 := by
    rw [hZcard]
    norm_num
  have hsub : (Z : Set G) ⊆ (V₀ : Set G) ∪ (fun g => e₀ * g) '' (V₀ : Set G) := by
    intro g hg
    rcases hcover g hg with h | h
    · exact Or.inl h
    · right
      refine ⟨e₀ * g, h, ?_⟩
      show e₀ * (e₀ * g) = g
      rw [← mul_assoc, ← sq, he₀2, one_mul]
  have hZcov : Nat.card ↥Z ≤ 2 * Nat.card ↥V₀ := by
    have h1 : Nat.card ↥Z = (Z : Set G).ncard := Nat.card_coe_set_eq (Z : Set G)
    have h2 : Nat.card ↥V₀ = (V₀ : Set G).ncard := Nat.card_coe_set_eq (V₀ : Set G)
    have h3 : ((fun g => e₀ * g) '' (V₀ : Set G)).ncard = (V₀ : Set G).ncard :=
      Set.ncard_image_of_injective _ (mul_right_injective e₀)
    rw [h1, h2]
    calc (Z : Set G).ncard ≤ ((V₀ : Set G) ∪ (fun g => e₀ * g) '' (V₀ : Set G)).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ (V₀ : Set G).ncard + ((fun g => e₀ * g) '' (V₀ : Set G)).ncard :=
          Set.ncard_union_le _ _
      _ = 2 * (V₀ : Set G).ncard := by rw [h3]; ring
  have hnot : e₀ ∉ V₀ := by
    intro h
    obtain ⟨_, hA⟩ := (cenV0_mem_iff hTN W e₀).1 h
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
    have h1 := hA w hw
    have h2 := hneg w hw
    have h4 : w = -w := h1.symm.trans h2
    have h3 : (2 : ZMod q) • w = 0 := by
      rw [two_smul]
      nth_rewrite 1 [h4]
      exact neg_add_cancel w
    exact hw0 ((smul_eq_zero.1 h3).resolve_left hh)
  have hV0lt : Nat.card ↥V₀ < 8 := by
    have hle : Nat.card ↥V₀ ≤ Nat.card ↥Z := Subgroup.card_le_of_le hV0Z
    rcases lt_or_eq_of_le hle with hlt | heq
    · rw [← hZ8]
      exact hlt
    · exfalso
      have hVZ : V₀ = Z := Subgroup.eq_of_le_of_card_ge hV0Z (le_of_eq heq.symm)
      apply hnot
      rw [hVZ]
      exact he₀
  have hP2 : IsPGroup 2 ↥V₀ := fun g => by
    obtain ⟨k, hk⟩ := hT2 ⟨(g : G), (hV0Z g.2).1⟩
    exact ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩
  obtain ⟨k, hk⟩ := hP2.exists_card_eq
  have hk4 : Nat.card ↥V₀ = 4 := by
    have h8 := hZcov
    rw [hZ8, hk] at h8
    rw [hk] at hV0lt
    have hk2 : 2 ≤ k := by
      by_contra hc
      push Not at hc
      interval_cases k <;> norm_num at h8
    have hk3 : k ≤ 2 := by
      by_contra hc
      push Not at hc
      have := Nat.pow_le_pow_right (by norm_num : 0 < 2) hc
      omega
    have hk2' : k = 2 := by omega
    rw [hk, hk2']
    norm_num
  exact ⟨hk4, hnot, hV0Z⟩

end KernelCard

section Lower

variable {G : Type} [Group G] [Finite G]

@[expose] def cenE (q : ℕ) {Q T : Subgroup G} [Module (ZMod q) (QA Q)]
    (hTN : T ≤ Subgroup.normalizer (Q : Set G)) (V₀ : Subgroup G)
    (hV : V₀ ≤ T ⊓ Subgroup.centralizer (T : Set G))
    {e₀ : G} (he₀ : e₀ ∈ T ⊓ Subgroup.centralizer (T : Set G)) : Submodule (ZMod q) (QA Q) :=
  (⨅ g : V₀, Module.End.eigenspace (repQ Q q T hTN ⟨(g : G), mem_T_of_inf (hV g.2)⟩) (1 : ZMod q)) ⊓
    Module.End.eigenspace (repQ Q q T hTN ⟨e₀, mem_T_of_inf he₀⟩) (-1 : ZMod q)

theorem mem_cenE (q : ℕ) {Q T : Subgroup G} [Module (ZMod q) (QA Q)]
    (hTN : T ≤ Subgroup.normalizer (Q : Set G)) (V₀ : Subgroup G)
    (hV : V₀ ≤ T ⊓ Subgroup.centralizer (T : Set G))
    {e₀ : G} (he₀ : e₀ ∈ T ⊓ Subgroup.centralizer (T : Set G)) (v : QA Q) :
    v ∈ cenE q hTN V₀ hV he₀ ↔ (∀ g : ↥V₀, repQ Q q T hTN ⟨(g : G), mem_T_of_inf (hV g.2)⟩ v = v) ∧
      repQ Q q T hTN ⟨e₀, mem_T_of_inf he₀⟩ v = -v := by
  unfold cenE
  rw [Submodule.mem_inf, Submodule.mem_iInf]
  simp only [Module.End.mem_eigenspace_iff, one_smul, neg_one_smul]

theorem cenE_invariant (q : ℕ) {Q T : Subgroup G} [Module (ZMod q) (QA Q)]
    (hTN : T ≤ Subgroup.normalizer (Q : Set G)) (V₀ : Subgroup G)
    (hV : V₀ ≤ T ⊓ Subgroup.centralizer (T : Set G))
    {e₀ : G} (he₀ : e₀ ∈ T ⊓ Subgroup.centralizer (T : Set G)) (t : ↥T) (v : QA Q)
    (hv : v ∈ cenE q hTN V₀ hV he₀) : repQ Q q T hTN t v ∈ cenE q hTN V₀ hV he₀ := by
  rw [mem_cenE] at hv ⊢
  obtain ⟨h1, h2⟩ := hv
  have key : ∀ x : G, ∀ hx : x ∈ T ⊓ Subgroup.centralizer (T : Set G),
      repQ Q q T hTN t (repQ Q q T hTN ⟨x, mem_T_of_inf hx⟩ v) =
        repQ Q q T hTN ⟨x, mem_T_of_inf hx⟩ (repQ Q q T hTN t v) := by
    intro x hx
    have hm : (t : ↥T) * ⟨x, mem_T_of_inf hx⟩ = ⟨x, mem_T_of_inf hx⟩ * t :=
      Subtype.ext (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hx).2 (t : G) t.2)
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, hm]
  constructor
  · intro g
    rw [← key (g : G) (hV g.2), h1 g]
  · rw [← key e₀ he₀, h2, map_neg]

end Lower

section LowerBound

variable {G : Type} [Group G] [Finite G]

theorem cen_lower_bound {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {Q T : Subgroup G}
    [Module (ZMod q) (QA Q)] (hTN : T ≤ Subgroup.normalizer (Q : Set G))
    (hV : ∀ V : Subgroup G, V ≤ T ⊓ Subgroup.centralizer (T : Set G) → Nat.card V = 4 →
      IsExtraspecialMod V T 3)
    (V₀ : Subgroup G) (hV0 : V₀ ≤ T ⊓ Subgroup.centralizer (T : Set G))
    (hV0card : Nat.card ↥V₀ = 4)
    {e₀ : G} (he₀ : e₀ ∈ T ⊓ Subgroup.centralizer (T : Set G)) (he₀2 : e₀ ^ 2 = 1)
    (he₀V : e₀ ∉ V₀) (W : Submodule (ZMod q) (QA Q)) (hW0 : W ≠ ⊥)
    (hWE : ∀ w ∈ W, w ∈ cenE q hTN V₀ hV0 he₀) :
    2 ^ 3 ≤ Module.finrank (ZMod q) (cenE q hTN V₀ hV0 he₀) := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨E', hgrp, π0, hπs, hπk0, hEext, hEcard⟩ := hV V₀ hV0 hV0card
  haveI : Finite E' := Nat.finite_of_card_ne_zero (by rw [hEcard]; norm_num)
  let π : ↥T →* E' := { toFun := π0, map_one' := π0.map_one, map_mul' := π0.map_mul }
  have hπk : π.ker = V₀.subgroupOf T := hπk0
  have hπs' : Function.Surjective π := hπs
  set E := cenE q hTN V₀ hV0 he₀ with hEdef
  let ρE : ↥T →* (E →ₗ[ZMod q] E) :=
    { toFun := fun t => (repQ Q q T hTN t).restrict (fun v hv => cenE_invariant q hTN V₀ hV0 he₀ t v hv)
      map_one' := LinearMap.ext fun v => Subtype.ext (by simp)
      map_mul' := fun s t => LinearMap.ext fun v => Subtype.ext (by simp [Module.End.mul_apply]) }
  have hker : π.ker ≤ ρE.ker := by
    intro t ht
    rw [hπk, Subgroup.mem_subgroupOf] at ht
    rw [MonoidHom.mem_ker]
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    have hv := ((mem_cenE q hTN V₀ hV0 he₀ v.1).1 v.2).1
    exact hv ⟨(t : G), ht⟩
  let ψ : E' →* (E →ₗ[ZMod q] E) :=
    (QuotientGroup.lift π.ker ρE hker).comp
      (QuotientGroup.quotientKerEquivOfSurjective π hπs').symm.toMonoidHom
  have hψπ : ∀ t : ↥T, ψ (π t) = ρE t := by
    intro t
    have e1 : (QuotientGroup.quotientKerEquivOfSurjective π hπs').symm (π t) =
        (QuotientGroup.mk t : ↥T ⧸ π.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    show QuotientGroup.lift π.ker ρE hker
      ((QuotientGroup.quotientKerEquivOfSurjective π hπs').symm (π t)) = ρE t
    rw [e1]
    rfl
  set e0' : ↥T := ⟨e₀, mem_T_of_inf he₀⟩ with he0'
  have hwc : π e0' ∈ Subgroup.center E' := by
    rw [Subgroup.mem_center_iff]
    intro x
    obtain ⟨g, rfl⟩ := hπs' x
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.1 he₀.2 (g : G) g.2
  have hw2 : π e0' ^ 2 = 1 := by
    rw [← map_pow]
    have : e0' ^ 2 = 1 := Subtype.ext (by simpa using he₀2)
    rw [this, map_one]
  have hw1 : π e0' ≠ 1 := by
    intro h
    have hmem : e0' ∈ π.ker := by
      rw [MonoidHom.mem_ker]
      exact h
    rw [hπk, Subgroup.mem_subgroupOf] at hmem
    exact he₀V hmem
  have hcenter : Subgroup.center E' = Subgroup.zpowers (π e0') := by
    have hle : Subgroup.zpowers (π e0') ≤ Subgroup.center E' := Subgroup.zpowers_le.2 hwc
    have hord : orderOf (π e0') = 2 := orderOf_eq_prime hw2 hw1
    have hcz : Nat.card (Subgroup.zpowers (π e0')) = 2 := by
      rw [Nat.card_zpowers, hord]
    have hcc : Nat.card (Subgroup.center E') = 2 := hEext.2.2.2
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcc, hcz])).symm
  have hψw : ψ (π e0') = -1 := by
    rw [hψπ]
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact ((mem_cenE q hTN V₀ hV0 he₀ v.1).1 v.2).2
  obtain ⟨w0, hw0, hw00⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  haveI : Nontrivial E := ⟨⟨⟨w0, hWE w0 hw0⟩, 0, fun h => hw00 (by simpa using congrArg Subtype.val h)⟩⟩
  have hcardE' : Nat.card E' = 2 ^ (1 + 2 * 3) := by
    rw [hEcard]
  exact (CFSG.RankThree.GroupTheory.extraspecial_two_minus_module_bound (K := ZMod q) (V := E)
    hEext hcardE' hcenter (two_ne_zero_zmod hq hq2) (ρ := ψ) hψw).1

end LowerBound

section Final

variable {G : Type} [Group G] [Finite G]

theorem comm_repQ {q : ℕ} {Q T : Subgroup G} [Module (ZMod q) (QA Q)]
    (hTN : T ≤ Subgroup.normalizer (Q : Set G)) {x y : G}
    (hx : x ∈ T ⊓ Subgroup.centralizer (T : Set G)) (hy : y ∈ T ⊓ Subgroup.centralizer (T : Set G)) :
    repQ Q q T hTN ⟨x, mem_T_of_inf hx⟩ * repQ Q q T hTN ⟨y, mem_T_of_inf hy⟩ =
      repQ Q q T hTN ⟨y, mem_T_of_inf hy⟩ * repQ Q q T hTN ⟨x, mem_T_of_inf hx⟩ := by
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  exact Subgroup.mem_centralizer_iff.1 hy.2 x (mem_T_of_inf hx)

theorem repQ_sq_apply {q : ℕ} {Q T : Subgroup G} [Module (ZMod q) (QA Q)]
    (hTN : T ≤ Subgroup.normalizer (Q : Set G)) {e₀ : G} (he₀ : e₀ ∈ T ⊓ Subgroup.centralizer (T : Set G))
    (he₀2 : e₀ ^ 2 = 1) (v : QA Q) :
    repQ Q q T hTN ⟨e₀, mem_T_of_inf he₀⟩ (repQ Q q T hTN ⟨e₀, mem_T_of_inf he₀⟩ v) = v := by
  rw [← Module.End.mul_apply, ← map_mul]
  have e : (⟨e₀, mem_T_of_inf he₀⟩ * ⟨e₀, mem_T_of_inf he₀⟩ : ↥T) = 1 :=
    Subtype.ext (by simpa [sq] using he₀2)
  rw [e, map_one, Module.End.one_apply]

theorem neg_on_range {q : ℕ} {Q T : Subgroup G} [Module (ZMod q) (QA Q)]
    (hTN : T ≤ Subgroup.normalizer (Q : Set G)) {e₀ : G} (he₀ : e₀ ∈ T ⊓ Subgroup.centralizer (T : Set G))
    (he₀2 : e₀ ^ 2 = 1) {u : QA Q}
    (hu : u ∈ LinearMap.range (repQ Q q T hTN ⟨e₀, mem_T_of_inf he₀⟩ - 1)) :
    repQ Q q T hTN ⟨e₀, mem_T_of_inf he₀⟩ u = -u := by
  obtain ⟨v, rfl⟩ := LinearMap.mem_range.1 hu
  simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub, repQ_sq_apply hTN he₀ he₀2]
  abel

theorem exists_ne_one_of_one_lt_card {Z : Subgroup G} (h : 1 < Nat.card ↥Z) :
    ∃ e ∈ Z, e ≠ 1 := by
  by_contra hcon
  have hbot : Z = ⊥ := eq_bot_iff.2 (fun e he => by
    by_contra hne
    exact hcon ⟨e, he, hne⟩)
  rw [hbot, Subgroup.card_bot] at h
  norm_num at h

theorem extraspecialRepCenterAt_holds : CFSG.LocalAnalysis.GLTheoremA.ExtraspecialRepCenterAt := by
  unfold CFSG.LocalAnalysis.GLTheoremA.ExtraspecialRepCenterAt
  intro G _ _ q T Q hq hq2 hT2 hZcard hZsq hV hexp hcl hTN hfaith
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Module (ZMod q) (QA Q) := AddCommGroup.zmodModule (qA_exp hexp)
  haveI : Finite (QA Q) := inferInstance
  obtain ⟨e₀, he₀Z, he₀1⟩ := exists_ne_one_of_card_eq hZcard
  have he₀2 : e₀ ^ 2 = 1 := hZsq e₀ he₀Z
  have hρe₀ : repQ Q q T hTN ⟨e₀, mem_T_of_inf he₀Z⟩ ≠ 1 := fun h =>
    he₀1 (faithful_of hq hq2 hexp hTN hfaith (mem_T_of_inf he₀Z) he₀2 h)
  set U : Submodule (ZMod q) (QA Q) :=
    LinearMap.range (repQ Q q T hTN ⟨e₀, mem_T_of_inf he₀Z⟩ - 1) with hUdef
  have hU : U ≠ ⊥ := by
    intro hbot
    apply hρe₀
    apply LinearMap.ext
    intro v
    have hmem : (repQ Q q T hTN ⟨e₀, mem_T_of_inf he₀Z⟩ - 1) v ∈ U := LinearMap.mem_range_self _ v
    rw [hbot, Submodule.mem_bot] at hmem
    rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hmem
    exact hmem
  have hUinv : ∀ i : ↥(T ⊓ Subgroup.centralizer (T : Set G)), ∀ u ∈ U,
      repQ Q q T hTN ⟨(i : G), mem_T_of_inf i.2⟩ u ∈ U := by
    intro i u hu
    obtain ⟨v, rfl⟩ := LinearMap.mem_range.1 hu
    refine LinearMap.mem_range.2 ⟨repQ Q q T hTN ⟨(i : G), mem_T_of_inf i.2⟩ v, ?_⟩
    have hc := comm_repQ (q := q) hTN he₀Z i.2
    simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub]
    have hc' := congrArg (fun F : QA Q →ₗ[ZMod q] QA Q => F v) hc
    simp only [Module.End.mul_apply] at hc'
    rw [hc']
  have h2 : (2 : ZMod q) ≠ 0 := two_ne_zero_zmod hq hq2
  obtain ⟨W, hWU, hW0, hWinv, hWscal⟩ := exists_scalar_invariant (K := ZMod q) (V := QA Q)
    (ι := ↥(T ⊓ Subgroup.centralizer (T : Set G)))
    (fun i => repQ Q q T hTN ⟨(i : G), mem_T_of_inf i.2⟩)
    (fun i j => comm_repQ (q := q) hTN i.2 j.2)
    (fun i => by
      rw [← map_mul]
      have e : (⟨(i : G), mem_T_of_inf i.2⟩ * ⟨(i : G), mem_T_of_inf i.2⟩ : ↥T) = 1 :=
        Subtype.ext (by simpa [sq] using hZsq (i : G) i.2)
      rw [e, map_one])
    h2 U hU hUinv
  have hscal : ∀ e : G, ∀ he : e ∈ T ⊓ Subgroup.centralizer (T : Set G),
      (∀ w ∈ W, repQ Q q T hTN ⟨e, mem_T_of_inf he⟩ w = w) ∨
        (∀ w ∈ W, repQ Q q T hTN ⟨e, mem_T_of_inf he⟩ w = -w) :=
    fun e he => hWscal ⟨e, he⟩
  obtain ⟨hcard4, he₀V, hV0Z⟩ := cenV0_card hq hq2 hTN hT2 hZcard he₀Z he₀1 he₀2 W hW0 hWU hscal
  have hWE : ∀ w ∈ W, w ∈ cenE q hTN (cenV0 hTN W) hV0Z he₀Z := by
    intro w hw
    rw [mem_cenE]
    refine ⟨fun g => ?_, neg_on_range hTN he₀Z he₀2 (hWU hw)⟩
    obtain ⟨_, hA⟩ := (cenV0_mem_iff hTN W (g : G)).1 g.2
    exact hA w hw
  have hlow := cen_lower_bound hq hq2 hTN hV (cenV0 hTN W) hV0Z hcard4 he₀Z he₀2 he₀V W hW0 hWE
  obtain ⟨h, hhV0, hh1⟩ := exists_ne_one_of_one_lt_card (by rw [hcard4]; norm_num)
  have hhZ : h ∈ T ⊓ Subgroup.centralizer (T : Set G) := hV0Z hhV0
  have hh2 : h ^ 2 = 1 := hZsq h hhZ
  have hEh : cenE q hTN (cenV0 hTN W) hV0Z he₀Z ≤
      Module.End.eigenspace (repQ Q q T hTN ⟨h, mem_T_of_inf hhZ⟩) (1 : ZMod q) := by
    intro v hv
    rw [Module.End.mem_eigenspace_iff, one_smul]
    exact ((mem_cenE q hTN _ hV0Z he₀Z v).1 hv).1 ⟨h, hhV0⟩
  have hfin : 2 ^ 3 ≤ Module.finrank (ZMod q)
      (Module.End.eigenspace (repQ Q q T hTN ⟨h, mem_T_of_inf hhZ⟩) (1 : ZMod q)) :=
    le_trans hlow (Submodule.finrank_mono hEh)
  have hpow : q ^ 8 ≤ q ^ Module.finrank (ZMod q)
      (Module.End.eigenspace (repQ Q q T hTN ⟨h, mem_T_of_inf hhZ⟩) (1 : ZMod q)) :=
    Nat.pow_le_pow_right hq.pos (by norm_num at hfin; exact hfin)
  refine ⟨h, hhZ, hh1, ?_⟩
  rw [card_centralizer_eq hq hq2 hexp hTN (mem_T_of_inf hhZ) hh2, mul_comm (q ^ 8)]
  exact Nat.mul_le_mul_left _ hpow

end Final

end CFSG.LocalAnalysis.GLTheoremA
