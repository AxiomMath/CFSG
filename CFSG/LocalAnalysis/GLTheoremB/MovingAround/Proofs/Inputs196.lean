module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs123a
public import CFSG.LargeExtraspecial.S8CBFSL2N
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8C12Sp4Surv
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.Final

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs196

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.LocalBalance (innerAut)
open CFSG.Yardstones.Md0ec50421ce4 (onLie ambiguousChev)

section CharTwo

variable {K : Type*} [Field K] [CharP K 2]

theorem sl2_mul_self_eq_one_of_commute_involution {z y : Matrix.SpecialLinearGroup (Fin 2) K}
    (hz1 : z ≠ 1) (hzz : z * z = 1) (hyz : y * z = z * y) : y * y = 1 := by
  set N : Matrix (Fin 2) (Fin 2) K := (z : Matrix (Fin 2) (Fin 2) K) - 1 with hNdef
  have hN2 : N * N = 0 := CFSG.LargeExtraspecial.S8.sl2_sub_one_mul_self hzz
  have hNs : N 0 1 ≠ 0 ∨ N 1 0 ≠ 0 ∨ N 0 0 ≠ N 1 1 := by
    rcases CFSG.LargeExtraspecial.S8.sl2_nonscalar_of_ne_one hz1 with h | h | h
    · left; simpa [hNdef] using h
    · right; left; simpa [hNdef] using h
    · right; right
      intro h'
      apply h
      simpa [hNdef] using h'
  have hyN : (y : Matrix (Fin 2) (Fin 2) K) * N = N * y := by
    have hyz' : (y : Matrix (Fin 2) (Fin 2) K) * z = z * y := congrArg Subtype.val hyz
    rw [hNdef, Matrix.mul_sub, Matrix.sub_mul, hyz', Matrix.mul_one, Matrix.one_mul]
  obtain ⟨α, β, hy⟩ :=
    CFSG.LargeExtraspecial.S8.exists_eq_smul_one_add_smul_of_commute_nonscalar_two hNs hyN
  have hyy : ((y * y : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      (α * α) • (1 : Matrix (Fin 2) (Fin 2) K) := by
    rw [Matrix.SpecialLinearGroup.coe_mul, hy]
    simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, hN2, smul_zero, add_zero, smul_smul]
    rw [add_assoc, ← add_smul, mul_comm β α, CharTwo.add_self_eq_zero, zero_smul, add_zero]
  by_contra hne
  rcases CFSG.LargeExtraspecial.S8.sl2_nonscalar_of_ne_one hne with h | h | h
  · apply h; rw [hyy]; simp
  · apply h; rw [hyy]; simp
  · apply h; rw [hyy]; simp

theorem center_sl2_eq_bot : Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) = ⊥ := by
  refine eq_bot_iff.2 fun A hA => ?_
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
  rw [Fintype.card_fin] at hr
  have h1 : r = 1 := by
    have h2 : (r - 1) * (r - 1) = 0 := by
      linear_combination hr + (1 - r) * (CharTwo.two_eq_zero : (2 : K) = 0)
    exact sub_eq_zero.1 (mul_self_eq_zero.1 h2)
  subst h1
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hrA]
  simp

theorem psl2_mk_injective :
    Function.Injective (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K))) := by
  rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', center_sl2_eq_bot]

theorem psl2_false_of_commute {u y : Matrix.ProjectiveSpecialLinearGroup (Fin 2) K}
    (hu : orderOf u = 2) (hy : orderOf y = 3) (huy : u * y = y * u) : False := by
  have hinj := psl2_mk_injective (K := K)
  obtain ⟨U, rfl⟩ := QuotientGroup.mk'_surjective
    (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) u
  obtain ⟨Y, rfl⟩ := QuotientGroup.mk'_surjective
    (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) y
  rw [orderOf_injective _ hinj] at hu hy
  have hUY : U * Y = Y * U := hinj (by rw [map_mul, map_mul]; exact huy)
  have hU1 : U ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hu
    exact absurd hu (by norm_num)
  have hUU : U * U = 1 := by
    have h := pow_orderOf_eq_one U
    rwa [hu, pow_two] at h
  have hYY := sl2_mul_self_eq_one_of_commute_involution hU1 hUU hUY.symm
  have h2 : orderOf Y ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hYY)
  rw [hy] at h2
  exact absurd h2 (by norm_num)

theorem psl2_exists_noncomm : ∃ a b : Matrix.ProjectiveSpecialLinearGroup (Fin 2) K, a * b ≠ b * a := by
  let u : Matrix.SpecialLinearGroup (Fin 2) K := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two_of]⟩
  let v : Matrix.SpecialLinearGroup (Fin 2) K := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two_of]⟩
  let π := QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K))
  refine ⟨π u, π v, fun h => ?_⟩
  have h1 : u * v = v * u := psl2_mk_injective (by rw [map_mul, map_mul]; exact h)
  have h2 := congrFun (congrFun (congrArg
    (fun z : Matrix.SpecialLinearGroup (Fin 2) K => (z : Matrix (Fin 2) (Fin 2) K)) h1) 0) 0
  simp only [Matrix.SpecialLinearGroup.coe_mul] at h2
  simp [u, v, Matrix.mul_apply, Fin.sum_univ_two] at h2

end CharTwo

section General

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner inner_map_congr congr_conj)

theorem mem_innerAut_of_congr {G K : Type*} [Group G] [Group K] (e : G ≃* K) {x : MulAut G}
    (h : MulAut.congr e x ∈ innerAut K) : x ∈ innerAut G := by
  have h' : MulAut.congr e x ∈ (inner G).map (MulAut.congr e).toMonoidHom := by
    rw [inner_map_congr]; exact h
  obtain ⟨y, hy, hyx⟩ := h'
  have hxy : y = x := (MulAut.congr e).injective hyx
  rw [← hxy]
  exact hy

theorem congr_mem_innerAut {G K : Type*} [Group G] [Group K] (e : G ≃* K) {x : MulAut G}
    (h : x ∈ innerAut G) : MulAut.congr e x ∈ innerAut K := by
  obtain ⟨g, rfl⟩ := h
  exact ⟨e g, (congr_conj e g).symm⟩

theorem mem_innerAut_of_not_dvd {G : Type*} [Group G] {p : ℕ} (hp : p.Prime)
    (h : ¬ p ∣ Nat.card (Outer G)) {α : MulAut G} (hα : α ^ p = 1) : α ∈ innerAut G := by
  have hp' : (QuotientGroup.mk α : Outer G) ^ p = 1 := by
    rw [← QuotientGroup.mk_pow, hα, QuotientGroup.mk_one]
  have hord : orderOf (QuotientGroup.mk α : Outer G) ∣ p := orderOf_dvd_of_pow_eq_one hp'
  rcases (Nat.dvd_prime hp).1 hord with h1 | h1
  · exact (QuotientGroup.eq_one_iff α).1 (orderOf_eq_one_iff.1 h1)
  · exact absurd (h1 ▸ orderOf_dvd_natCard _) h

theorem mem_innerAut_of_isPGroup_outer {G : Type*} [Group G] {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≠ q) (h : IsPGroup q (Outer G)) {α : MulAut G} (hα : α ^ p = 1) :
    α ∈ innerAut G := by
  obtain ⟨k, hk⟩ := h (QuotientGroup.mk α)
  have hp' : (QuotientGroup.mk α : Outer G) ^ p = 1 := by
    rw [← QuotientGroup.mk_pow, hα, QuotientGroup.mk_one]
  have hcop : Nat.Coprime p (q ^ k) := Nat.Coprime.pow_right _ ((Nat.coprime_primes hp hq).2 hpq)
  have h1 : orderOf (QuotientGroup.mk α : Outer G) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hp') (orderOf_dvd_of_pow_eq_one hk)
  exact (QuotientGroup.eq_one_iff α).1 (orderOf_eq_one_iff.1 h1)

theorem exists_noncomm_of_mem_innerAut {S : Type*} [Group S] {x : MulAut S} (hx : x ∈ innerAut S)
    (hx1 : x ≠ 1) : ∃ a b : S, a * b ≠ b * a := by
  obtain ⟨s, rfl⟩ := hx
  by_contra h
  push Not at h
  apply hx1
  ext y
  simp [MulAut.conj_apply, h s y]

theorem exists_noncomm_of_mulEquiv {S K : Type*} [Group S] [Group K] (e : S ≃* K)
    (h : ∃ a b : K, a * b ≠ b * a) : ∃ a b : S, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := h
  exact ⟨e.symm a, e.symm b, fun h' => hab (by simpa using congrArg e h')⟩

theorem eq_bot_of_le_of_card_six {G : Type*} [Group G] {C T : Subgroup G} (hC : Nat.card C = 6)
    (hnab : ∃ a b : ↥C, a * b ≠ b * a) (hTC : T ≤ C) (hT2 : IsPGroup 2 T)
    (hnorm : ∀ c ∈ C, ∀ t ∈ T, c * t * c⁻¹ ∈ T) : T = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite C := Nat.finite_of_card_ne_zero (by rw [hC]; norm_num)
  haveI : Finite T := Finite.of_injective _ (Subgroup.inclusion_injective hTC)
  obtain ⟨k, hk⟩ := hT2.exists_card_eq
  have hdvd : 2 ^ k ∣ 6 := by rw [← hk, ← hC]; exact Subgroup.card_dvd_of_le hTC
  have hk1 : k ≤ 1 := by
    by_contra h
    have h4 : 2 ^ 2 ∣ 6 := (Nat.pow_dvd_pow 2 (by omega)).trans hdvd
    norm_num at h4
  by_contra hne
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hne (Subgroup.eq_bot_of_card_eq T (by simpa using hk))
  have hT : Nat.card T = 2 := by rw [hk, show k = 1 by omega, pow_one]
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := T) 2 (by rw [hT])
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht
    exact absurd ht (by norm_num)
  obtain ⟨u, -, huniq⟩ := (Nat.card_eq_two_iff' (1 : T)).1 hT
  have hcent : ∀ c ∈ C, c * (t : G) = t * c := by
    intro c hc
    have h1 : (⟨c * t * c⁻¹, hnorm c hc t t.2⟩ : T) ≠ 1 := by
      intro h
      apply ht1
      have h2 : c * (t : G) * c⁻¹ = 1 := congrArg Subtype.val h
      apply Subtype.ext
      calc (t : G) = c⁻¹ * (c * t * c⁻¹) * c := by group
        _ = 1 := by rw [h2]; group
    have h3 := congrArg Subtype.val ((huniq _ h1).trans (huniq t ht1).symm)
    exact mul_inv_eq_iff_eq_mul.1 h3
  set t' : ↥C := ⟨t, hTC t.2⟩ with ht'
  have ht'2 : orderOf t' = 2 := by
    rw [← ht, ← Subgroup.orderOf_coe t, ← Subgroup.orderOf_coe t']
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := C) 3 (by rw [hC]; norm_num)
  have hyt : Commute y t' := Subtype.ext (hcent y y.2)
  have h6 : orderOf (y * t') = Nat.card C := by
    rw [hyt.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hy, ht'2]; norm_num), hy, ht'2, hC]
  haveI : IsCyclic C := isCyclic_of_orderOf_eq_card (y * t') h6
  obtain ⟨a, b, hab⟩ := hnab
  exact hab ((IsCyclic.commGroup (α := ↥C)).mul_comm a b)

end General

section LTwoEight

open CFSG.GorensteinWalter CFSG.ComponentClassification.AutL2Facts

variable {F : Type} [Field F] [Finite F]

theorem toPGL_surjective_of_charTwo [CharP F 2] :
    Function.Surjective (Matrix.ProjectiveSpecialLinearGroup.toPGL : PSL2 F →* PGL2 F) := by
  intro g
  obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
  haveI : Fintype F := Fintype.ofFinite F
  exact (pgl2_mk_mem_psl2_range_iff_det_isSquare A).2
    (FiniteField.isSquare_of_char_two (ringChar.eq F 2) _)

theorem charP_two_of_card (hF : Nat.card F = 2 ^ 3) : CharP F 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype F := Fintype.ofFinite F
  exact charP_of_card_eq_prime_pow (p := 2) (f := 3) (by rw [← Nat.card_eq_fintype_card, hF])

theorem l2Eight_autEquiv_eq_incl (hF : Nat.card F = 2 ^ 3) {S : Type} [Group S] (e : S ≃* PSL2 F)
    {τ : MulAut S} {k : ℕ} (hτ : τ ^ 2 ^ k = 1) : ∃ u : PSL2 F, autEquiv e τ = incl F u := by
  haveI : CharP F 2 := charP_two_of_card hF
  have hφ2 : autEquiv e τ ^ 2 ^ k = 1 := by rw [← map_pow, hτ, map_one]
  have hright : (autEquiv e τ).right = 1 := by
    refine eq_one_of_two_power_ringAut (p := 2) (f := 3) Nat.prime_two hF (by decide) _ k ?_
    have := congrArg (SemidirectProduct.rightHom : PGammaL2 F →* (F ≃+* F)) hφ2
    rw [map_pow, map_one] at this
    simpa using this
  have hinl : autEquiv e τ = SemidirectProduct.inl (autEquiv e τ).left :=
    SemidirectProduct.ext rfl hright
  obtain ⟨u, hu⟩ := toPGL_surjective_of_charTwo (autEquiv e τ).left
  exact ⟨u, by rw [hinl, incl_apply, hu]⟩

theorem l2Eight_pCoreOf_two_eq_bot (hF : Nat.card F = 2 ^ 3) {S : Type} [Group S] [Finite S]
    (e : S ≃* PSL2 F) {s : S} (hs : orderOf s = 3) (H : Subgroup (MulAut S)) :
    pCoreOf 2 (H ⊓ Subgroup.centralizer ({MulAut.conj s} : Set (MulAut S))) = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 := charP_two_of_card hF
  set X := H ⊓ Subgroup.centralizer ({MulAut.conj s} : Set (MulAut S)) with hX
  set T := pCoreOf 2 X with hT
  have hT2 : IsPGroup 2 T := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X
  have hTX : T ≤ X := CFSG.LieType.BorelTits.pCoreOf_le 2 X
  by_contra hne
  obtain ⟨k, hk⟩ := hT2.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hne (Subgroup.eq_bot_of_card_eq _ (by simpa using hk))
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := T) 2 (by rw [hk]; exact dvd_pow_self 2 hk0)
  set τ : MulAut S := (t : MulAut S) with hτ
  have hτ2 : orderOf τ = 2 := by rw [hτ, Subgroup.orderOf_coe, ht]
  have hτc : τ * MulAut.conj s = MulAut.conj s * τ :=
    Subgroup.mem_centralizer_singleton_iff.1 (hTX t.2).2
  have hτsq : τ ^ 2 ^ 1 = 1 := by
    have h := pow_orderOf_eq_one τ
    rwa [hτ2, ← pow_one 2] at h
  obtain ⟨u, hφu⟩ := l2Eight_autEquiv_eq_incl hF e hτsq
  have hu2 : orderOf u = 2 := by
    rw [← orderOf_injective (incl F) (incl_injective F) u, ← hφu, MulEquiv.orderOf_eq, hτ2]
  have hes : orderOf (e s) = 3 := by rw [MulEquiv.orderOf_eq, hs]
  have hcomm : u * e s = e s * u := by
    apply incl_injective F
    rw [map_mul, map_mul, ← hφu, ← autEquiv_conj e s, ← map_mul, ← map_mul, hτc]
  exact psl2_false_of_commute hu2 hes hcomm

end LTwoEight

section LTwoEightOuter

open CFSG.Open (StatedProj StatedSL)
open CFSG.GorensteinWalter CFSG.ComponentClassification.AutL2Facts
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns

variable {F : Type} [Field F] [Finite F]

theorem fieldType_of_not_mem_pglAction (β : MulAut (StatedProj (StatedSL 2 F))) (hβ3 : β ^ 3 = 1)
    (hβ1 : β ≠ 1)
    (hD : MulAut.congr (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm β ∉
      (pglAction F).range) :
    ∃ (σ : F ≃+* F) (φ γ : MulAut (StatedProj (StatedSL 2 F))),
      IsEntrywiseAutPSLn 2 σ φ ∧ β = γ * φ * γ⁻¹ := by
  let e₀ : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F ≃* StatedProj (StatedSL 2 F) :=
    CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F
  let β' : MulAut (PSL2 F) := MulAut.congr e₀.symm β
  have hβ'3 : β' ^ 3 = 1 := by
    change MulAut.congr e₀.symm β ^ 3 = 1
    rw [← map_pow, hβ3, map_one]
  have hβ'1 : β' ≠ 1 := by
    intro h
    apply hβ1
    apply (MulAut.congr e₀.symm).injective
    rw [map_one]; exact h
  have hback : MulAut.congr e₀ β' = β := by
    change MulAut.congr e₀ (MulAut.congr e₀.symm β) = β
    ext y
    simp [MulAut.congr_apply]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf β' = 3 := orderOf_eq_prime hβ'3 hβ'1
  obtain ⟨σ, -, g, hgσ⟩ :=
    CFSG.RankThree.PartTwo.KFacts.linear_two_prime_order_field_descent Nat.prime_three β' hord hD
  refine ⟨σ, MulAut.congr e₀ (psl2FieldAut F σ), MulAut.congr e₀ (pglAction F g), ?_, ?_⟩
  · intro A A' hA
    obtain ⟨B, rfl⟩ := (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F).surjective A
    have h1 : e₀ (psl2QuotientMap F B) = QuotientGroup.mk
        (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F B) := rfl
    have h2 : e₀.symm (QuotientGroup.mk
        (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F B)) =
          psl2QuotientMap F B := by
      rw [MulEquiv.symm_apply_eq]; exact h1.symm
    change e₀ (psl2FieldAut F σ (e₀.symm _)) = _
    rw [h2, CFSG.Quasithin.Vol2.Ch11.SecD.BK10.L2.psl2FieldAut_mk]
    have h3 : e₀ (psl2QuotientMap F (Matrix.SpecialLinearGroup.map σ.toRingHom B)) =
        QuotientGroup.mk (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F
          (Matrix.SpecialLinearGroup.map σ.toRingHom B)) := rfl
    rw [h3]
    congr 1
    apply Subtype.ext
    apply Units.ext
    rw [CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe] at hA ⊢
    rw [hA]
    ext i j
    rfl
  · rw [← hback, hgσ]
    simp only [map_mul, map_inv]

theorem l2Eight_outer_fixSubgroup (hF : Nat.card F = 2 ^ 3) {S : Type} [Group S] (e : S ≃* PSL2 F)
    {x : MulAut S} (hx3 : orderOf x = 3) (hxI : x ∉ innerAut S) :
    Nat.card (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup x) = 6 ∧
      ∃ a b : ↥(CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup x), a * b ≠ b * a := by
  haveI : CharP F 2 := charP_two_of_card hF
  set e₀ := CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F with he₀
  set e₁ : S ≃* StatedProj (StatedSL 2 F) := e.trans e₀ with he₁
  set β : MulAut (StatedProj (StatedSL 2 F)) := MulAut.congr e₁ x with hβ
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hx3
    exact absurd hx3 (by norm_num)
  have hβ3 : β ^ 3 = 1 := by
    rw [hβ, ← map_pow, ← hx3, pow_orderOf_eq_one, map_one]
  have hβ1 : β ≠ 1 := by
    intro h
    apply hx1
    apply (MulAut.congr e₁).injective
    rw [map_one]; exact h
  have hD : MulAut.congr e₀.symm β ∉ (pglAction F).range := by
    rintro ⟨g, hg⟩
    apply hxI
    apply mem_innerAut_of_congr e₁
    obtain ⟨u, rfl⟩ := toPGL_surjective_of_charTwo g
    have h1 : MulAut.congr e₀.symm β ∈ innerAut (PSL2 F) := ⟨u, by rw [← hg, pglAction_toPGL]⟩
    have h2 := congr_mem_innerAut e₀ h1
    have h3 : MulAut.congr e₀ (MulAut.congr e₀.symm β) = β := by
      ext y
      simp [MulAut.congr_apply]
    rw [h3] at h2
    exact h2
  obtain ⟨σ, φ, γ, hφ, hβγ⟩ := fieldType_of_not_mem_pglAction β hβ3 hβ1 hD
  obtain ⟨F₀, _, _, hcard, ⟨ψ⟩⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.l2FieldFixed_holds F β hβ3 hβ1 σ φ γ hφ hβγ
  have h8 : Nat.card F₀ ^ 3 = 2 ^ 3 := by rw [← hcard, hF]
  have h2 : Nat.card F₀ = 2 := Nat.pow_left_injective (n := 3) (by norm_num) h8
  have hmap : (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup x).map (e₁ : S →* _) = fixSub β := by
    ext y
    rw [mem_fixSub]
    constructor
    · rintro ⟨s, hs, rfl⟩
      have hs' : x s = s := hs
      simp [hβ, MulAut.congr_apply, hs']
    · intro hy
      refine ⟨e₁.symm y, ?_, by simp⟩
      show x (e₁.symm y) = e₁.symm y
      have hy' : e₁ (x (e₁.symm y)) = y := by simpa [hβ, MulAut.congr_apply] using hy
      simpa using congrArg e₁.symm hy'
  let ρ : ↥(CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup x) ≃* StatedProj (StatedSL 2 F₀) :=
    (((CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup x).equivMapOfInjective (e₁ : S →* _)
      e₁.injective).trans (MulEquiv.subgroupCongr hmap)).trans ψ
  haveI : Finite F₀ := inferInstance
  haveI : CharP F₀ 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : Fintype F₀ := Fintype.ofFinite F₀
    exact charP_of_card_eq_prime_pow (p := 2) (f := 1) (by rw [← Nat.card_eq_fintype_card, h2, pow_one])
  refine ⟨?_, exists_noncomm_of_mulEquiv
    (ρ.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F₀).symm)
    psl2_exists_noncomm⟩
  rw [Nat.card_congr ρ.toEquiv,
    CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (K := F₀) (n := 2) (by norm_num), h2]
  norm_num

theorem l2Eight_outer_pCoreOf_two_eq_bot (hF : Nat.card F = 2 ^ 3) {S : Type} [Group S] [Finite S]
    (e : S ≃* PSL2 F) (hZ : Subgroup.center S = ⊥) {x : MulAut S} (hx3 : orderOf x = 3)
    (hxI : x ∉ innerAut S) (H : Subgroup (MulAut S)) (hH : innerAut S ≤ H) :
    pCoreOf 2 (H ⊓ Subgroup.centralizer ({x} : Set (MulAut S))) = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinj := CFSG.HardMathSupport.Timmesfeld.DefChar.conj_injective_of_center_eq_bot hZ
  set X := H ⊓ Subgroup.centralizer ({x} : Set (MulAut S)) with hX
  set T := pCoreOf 2 X with hT
  have hT2 : IsPGroup 2 T := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X
  have hTX : T ≤ X := CFSG.LieType.BorelTits.pCoreOf_le 2 X
  have hXT : X ≤ Subgroup.normalizer (T : Set (MulAut S)) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X
  have hTinn : ∀ τ ∈ T, ∃ s : S, MulAut.conj s = τ := by
    intro τ hτ
    obtain ⟨k, hk⟩ := hT2 ⟨τ, hτ⟩
    have hk' : τ ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    obtain ⟨u, hu⟩ := l2Eight_autEquiv_eq_incl hF e hk'
    refine ⟨e.symm u, (autEquiv e).injective ?_⟩
    rw [autEquiv_conj, MulEquiv.apply_symm_apply, hu]
  set T₀ : Subgroup S := T.comap (MulAut.conj : S →* MulAut S) with hT₀
  have hT₀2 : IsPGroup 2 T₀ := by
    intro s
    obtain ⟨k, hk⟩ := hT2 ⟨MulAut.conj (s : S), s.2⟩
    refine ⟨k, Subtype.ext (hinj ?_)⟩
    have hk' : MulAut.conj (s : S) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    rw [Subgroup.coe_pow, map_pow, hk', Subgroup.coe_one, map_one]
  have hT₀fix : T₀ ≤ CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup x := by
    intro s hs
    exact (CFSG.HardMathSupport.Dickson.I271.conj_mem_centralizer_iff hZ x s).1 (hTX hs).2
  have hT₀norm : ∀ c ∈ CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup x, ∀ s ∈ T₀,
      c * s * c⁻¹ ∈ T₀ := by
    intro c hc s hs
    have hcX : MulAut.conj c ∈ X :=
      ⟨hH ⟨c, rfl⟩, (CFSG.HardMathSupport.Dickson.I271.conj_mem_centralizer_iff hZ x c).2 hc⟩
    have h1 := (Subgroup.mem_normalizer_iff.1 (hXT hcX) (MulAut.conj s)).1 hs
    show MulAut.conj (c * s * c⁻¹) ∈ T
    rw [map_mul, map_mul, map_inv]
    exact h1
  obtain ⟨hC6, hCnab⟩ := l2Eight_outer_fixSubgroup hF e hx3 hxI
  have hT₀bot : T₀ = ⊥ := eq_bot_of_le_of_card_six hC6 hCnab hT₀fix hT₀2 hT₀norm
  refine eq_bot_iff.2 fun τ hτ => ?_
  obtain ⟨s, rfl⟩ := hTinn τ hτ
  have hs : s ∈ T₀ := hτ
  rw [hT₀bot, Subgroup.mem_bot] at hs
  rw [hs, map_one]
  exact Subgroup.one_mem _

end LTwoEightOuter

theorem ambiguousChev_lie_odd {p : ℕ} (hp2 : p ≠ 2) {idx : TauCeti.ValidLieTypeIndex}
    (h : ambiguousChev p (TauCeti.CFSGIndex.lie idx)) :
    p = 3 ∧ ((∃ q : TauCeti.PrimePower, idx.1 = .A 1 q ∧ q.card = 8) ∨
      (∃ q : TauCeti.PrimePower, idx.1 = .twistedA 3 q ∧ q.card = 2)) := by
  obtain ⟨d, hv⟩ := idx
  simp only [ambiguousChev] at h
  split at h
  · rcases h with ⟨-, h⟩ | ⟨h8, h3⟩
    · exact absurd h hp2
    · exact ⟨h3, Or.inl ⟨_, rfl, h8⟩⟩
  · exact absurd h.2 hp2
  · exact ⟨h.2, Or.inr ⟨_, rfl, h.1⟩⟩
  · exact h.elim

theorem l2Eight_of_catalog {S : Type} [Group S] {q : TauCeti.PrimePower}
    {hv : (TauCeti.LieTypeIndex.A 1 q).Valid} (hq8 : q.card = 8)
    (e0 : S ≃* (TauCeti.CFSGIndex.lie ⟨.A 1 q, hv⟩).Group) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ 3 ∧
      Nonempty (S ≃* CFSG.GorensteinWalter.PSL2 F) := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hlin : CFSG.AGLEmbedding.IsLinTwoIndex q.p q.exponent ⟨.A 1 q, hv⟩ := ⟨q, rfl, rfl, rfl⟩
  obtain ⟨e1⟩ := CFSG.AGLEmbedding.nonempty_mulEquiv_psl2GF_of_isLinTwoIndex hlin
  refine ⟨GaloisField q.p q.exponent, inferInstance, inferInstance, ?_, ⟨e0.trans e1⟩⟩
  rw [GaloisField.card _ _ q.exponent_pos.ne', ← TauCeti.PrimePower.card_def, hq8]
  norm_num

theorem psp43_model_of_twistedA {S : Type} [Group S] {q : TauCeti.PrimePower}
    {hv : (TauCeti.LieTypeIndex.twistedA 3 q).Valid} (hq2 : q.card = 2)
    (e0 : S ≃* (TauCeti.CFSGIndex.lie ⟨.twistedA 3 q, hv⟩).Group) :
    CFSG.Assembly.LowTwoRank.StatedClassicalModel S .PSp 2 3 1 := by
  have hqp : q.p ^ q.exponent = 2 := by rw [← TauCeti.PrimePower.card_def]; exact hq2
  have hp : q.p = 2 := by
    have hdvd : q.p ∣ 2 := by
      rw [← hqp]
      exact dvd_pow_self q.p q.exponent_pos.ne'
    exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 hdvd
  have hf : q.exponent = 1 := by
    rw [hp] at hqp
    exact Nat.pow_right_injective (le_refl 2) (show 2 ^ q.exponent = 2 ^ 1 by simpa using hqp)
  have hm0 := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 q hv e0
  rw [hp, hf] at hm0
  exact CFSG.GH74.Exceptional.statedClassicalModel_PSp_two_three_of_PSU_four_two hm0

theorem mem_innerAut_of_psp43 {S : Type} [Group S]
    (hm : CFSG.Assembly.LowTwoRank.StatedClassicalModel S .PSp 2 3 1) {x : MulAut S} (hx : x ^ 3 = 1) :
    x ∈ innerAut S := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hm
  have hK3 : Nat.card K = 3 := by rw [hK, pow_one]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 3 := charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card, hK])
  have hodd : ringChar K ≠ 2 := by rw [ringChar.eq K 3]; norm_num
  have hout := CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.isPGroup_outer_psp4
    (CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.eq_zero_or_one_or_neg_one_of_card_three hK3) hodd
  apply mem_innerAut_of_congr e
  exact mem_innerAut_of_isPGroup_outer Nat.prime_three Nat.prime_two (by norm_num) hout
    (by rw [← map_pow, hx, map_one])

theorem input19_6_4Amb_holds : Inputs123a.Input19_6_4Amb := by
  intro p hp hp2 S _ _ hS idx hSe hi x hx hxo H hH
  obtain ⟨hp3, hidx⟩ := ambiguousChev_lie_odd hp2 hi
  subst hp3
  obtain ⟨e0⟩ := hSe
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hxo
    exact absurd hxo (by norm_num)
  have hnab := exists_noncomm_of_mem_innerAut hx hx1
  obtain ⟨d, hv⟩ := idx
  rcases hidx with ⟨q, hq, hq8⟩ | ⟨q, hq, hq2⟩
  ·
    simp only at hq
    subst hq
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := l2Eight_of_catalog hq8 e0
    have hZ : Subgroup.center S = ⊥ :=
      CFSG.HardMathSupport.Timmesfeld.DefChar.center_eq_bot_of_simple hS hnab
    obtain ⟨s, rfl⟩ := hx
    have hs : orderOf s = 3 := by
      rw [← orderOf_injective (MulAut.conj : S →* MulAut S)
        (CFSG.HardMathSupport.Timmesfeld.DefChar.conj_injective_of_center_eq_bot hZ) s]
      exact hxo
    exact l2Eight_pCoreOf_two_eq_bot hF e hs H
  ·
    simp only at hq
    subst hq
    have h0 := CFSG.HardMathSupport.Timmesfeld.DefChar.innerCoreFree_PSp_two hS hnab
      (psp43_model_of_twistedA hq2 e0) (by norm_num) x hx hxo H hH
    exact le_bot_iff.1 ((Inputs123a.pCoreOf_two_le_glaPPrimeCoreOf Nat.prime_three (by norm_num) _).trans
      h0.le)

theorem isLTwoTwentySeven_of_coordinator {X : Type} [Group X]
    (h : CFSG.HardMathSupport.Solomon.Coordinator.IsLTwoTwentySeven X) : IsLTwoTwentySeven X := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fintype (GaloisField 3 3) := Fintype.ofFinite _
  have hG : Nat.card (GaloisField 3 3) = 27 := by
    rw [GaloisField.card 3 3 (by norm_num)]
    norm_num
  have hc : Fintype.card F = Fintype.card (GaloisField 3 3) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF, hG]
  exact ⟨(e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm).trans
    (CFSG.GorensteinWalter.psl2RingEquiv (FiniteField.ringEquivOfCardEq hc))⟩

theorem input19_6_4Outer_of_outerCent (hO : CFSG.HardMathSupport.Dickson.DefCharOuter.Export.OuterCentAll) :
    Inputs123a.Input19_6_4Outer := by
  intro p hp hp2 S _ _ hS hchev x hxo hxI H hH _ hne
  have hxp : x ^ p = 1 := by rw [← hxo]; exact pow_orderOf_eq_one x
  rcases hchev with ⟨i, hi, ⟨e⟩⟩ | ⟨i, hi, ⟨e⟩⟩
  · cases i with
    | lie idx =>
      have hchar : idx.1.characteristic = p := hi
      obtain ⟨-, -, hnabC⟩ := (hO (CFSG.Yardstones.Md42047359a2a.lieFamily idx.1)).1 idx rfl
        (by rw [hchar]; exact hp2)
      have hnab := exists_noncomm_of_mulEquiv e hnabC
      by_contra hcon
      have hexc : ¬ (p = 3 ∧ CFSG.HardMathSupport.Solomon.Coordinator.IsLTwoTwentySeven S) :=
        fun h => hcon ⟨h.1, isLTwoTwentySeven_of_coordinator h.2⟩
      have h0 := CFSG.HardMathSupport.Dickson.I271.defCharOuterCoreFree_of_kdata
        (CFSG.HardMathSupport.Dickson.DefCharOuter.Export.kdOutCoreFree_of_outerCent hO)
        (CFSG.HardMathSupport.Dickson.DefCharOuter.Export.kdOutCentInner_of_outerCent hO)
        S hS hnab idx ⟨e⟩ p hp hp2 hchar hexc x hxo hxI H hH
      exact hne (le_bot_iff.1 ((Inputs123a.pCoreOf_two_le_glaPPrimeCoreOf hp hp2 _).trans h0.le))
    | cyclic _ _ => exact absurd hi (by simp [onLie])
    | alternating _ _ => exact absurd hi (by simp [onLie])
    | sporadic _ => exact absurd hi (by simp [onLie])
  · exfalso
    cases i with
    | alternating n hn =>
      have hn5 : 5 ≤ n := by
        simp only [ambiguousChev] at hi
        rcases hi with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> norm_num
      exact hxI (mem_innerAut_of_congr e (mem_innerAut_of_not_dvd hp
        (CFSG.AGLEmbedding.not_dvd_card_outer_alternatingGroup n hn5 p hp hp2)
        (by rw [← map_pow, hxp, map_one])))
    | lie idx =>
      obtain ⟨hp3, hidx⟩ := ambiguousChev_lie_odd hp2 hi
      subst hp3
      obtain ⟨d, hv⟩ := idx
      rcases hidx with ⟨q, hq, hq8⟩ | ⟨q, hq, hq2⟩
      ·
        simp only at hq
        subst hq
        obtain ⟨F, _, _, hF, ⟨e'⟩⟩ := l2Eight_of_catalog hq8 e
        haveI : CharP F 2 := charP_two_of_card hF
        have hZ : Subgroup.center S = ⊥ :=
          CFSG.HardMathSupport.Timmesfeld.DefChar.center_eq_bot_of_simple hS
            (exists_noncomm_of_mulEquiv e' psl2_exists_noncomm)
        exact hne (l2Eight_outer_pCoreOf_two_eq_bot hF e' hZ hxo hxI H hH)
      ·
        simp only at hq
        subst hq
        exact hxI (mem_innerAut_of_psp43 (psp43_model_of_twistedA hq2 e) hxp)
    | cyclic _ _ => exact absurd hi (by simp [ambiguousChev])
    | sporadic _ => exact absurd hi (by simp [ambiguousChev])

section Holds


theorem input19_6_4Outer_holds : Inputs123a.Input19_6_4Outer :=
  input19_6_4Outer_of_outerCent CFSG.HardMathSupport.Dickson.DefCharOuter.Export.outerCentAll_holds

theorem input19_6_4_holds : Lemma123.Input19_6_4 :=
  Inputs123a.input19_6_4_of CFSG.HardMathSupport.Solomon.Coordinator.defCharInnerCoreFree_holds
    input19_6_4Outer_holds input19_6_4Amb_holds

end Holds

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs196
