module

public import CFSG.HardMathSupport.Timmesfeld.DefChar.Families
public import CFSG.HardMathSupport.Timmesfeld.DefChar.CoreExcGeneric
public import CFSG.HardMathSupport.Timmesfeld.Balance.Basic
public import CFSG.Adapters.TauCetiExceptional.EvenAll
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67ExcPar
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67G2Aut
public import CFSG.LieType.Chevalley.G2FieldFourCoverRoots

public section

namespace CFSG.HardMathSupport.Timmesfeld.DefChar

open CFSG.Open CFSG.LieType.Chevalley CFSG.LieType.BorelTits CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.GH74.GLS.Stage2.OddAut CFSG.GH74.GLS.Stage2.Bender.Thm1
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.LieType.Ree CFSG.LocalAnalysis.ComponentInitial
  CFSG.LieType.AlgebraicGroups

theorem gLAPPrimeCoreOf_map_mulEquiv_F4G2 {M M' : Type} [Group M] [Group M'] (p : ℕ) (φ : M ≃* M')
    (B : Subgroup M) :
    GLAPPrimeCoreOf p (B.map φ.toMonoidHom) = (GLAPPrimeCoreOf p B).map φ.toMonoidHom := by
  let e : ↥B ≃* ↥(B.map φ.toMonoidHom) :=
    Subgroup.equivMapOfInjective B φ.toMonoidHom φ.injective
  have h := CFSG.HardMathSupport.Timmesfeld.Balance.gLAPPrimeCoreOf_eq_map_of_mulEquiv p
    (φ.toMonoidHom.comp B.subtype) e (fun x => rfl)
  rw [h]
  unfold GLAPPrimeCoreOf
  rw [Subgroup.map_map]

theorem gLAPPrimeCoreOf_inf_centralizer_of_congr_F4G2 {S Y : Type} [Group S] [Group Y] (p : ℕ)
    (e : S ≃* Y) (H : Subgroup (MulAut S)) (x : MulAut S)
    (h : GLAPPrimeCoreOf p (H.map (MulAut.congr e).toMonoidHom ⊓
      Subgroup.centralizer ({MulAut.congr e x} : Set (MulAut Y))) = ⊥) :
    GLAPPrimeCoreOf p (H ⊓ Subgroup.centralizer ({x} : Set (MulAut S))) = ⊥ := by
  set φ := MulAut.congr e with hφ
  have hmap : H.map φ.toMonoidHom ⊓ Subgroup.centralizer ({φ x} : Set (MulAut Y)) =
      (H ⊓ Subgroup.centralizer ({x} : Set (MulAut S))).map φ.toMonoidHom := by
    ext z
    obtain ⟨y, rfl⟩ := φ.surjective z
    simp only [Subgroup.mem_inf, Subgroup.mem_map, Subgroup.mem_centralizer_iff,
      Set.mem_singleton_iff, forall_eq]
    constructor
    · rintro ⟨⟨y', hy', hyy'⟩, hc⟩
      have : y' = y := φ.injective hyy'
      subst this
      refine ⟨y', ⟨hy', ?_⟩, rfl⟩
      apply φ.injective
      simpa using hc
    · rintro ⟨y', ⟨hy', hc⟩, hyy'⟩
      have : y' = y := φ.injective hyy'
      subst this
      refine ⟨⟨y', hy', rfl⟩, ?_⟩
      have := congrArg φ hc
      simpa using this
  rw [hmap, gLAPPrimeCoreOf_map_mulEquiv_F4G2] at h
  exact (Subgroup.map_eq_bot_iff_of_injective _ φ.injective).1 h

theorem innerCoreFree_transport_F4G2 {S Y : Type} [Group S] [Group Y] (e : S ≃* Y) {p : ℕ}
    (key : ∀ H' : Subgroup (MulAut Y), innerAut Y ≤ H' → ∀ x' ∈ innerAut Y, orderOf x' = p →
      GLAPPrimeCoreOf p (H' ⊓ Subgroup.centralizer ({x'} : Set (MulAut Y))) = ⊥) :
    ∀ x ∈ innerAut S, orderOf x = p → ∀ H : Subgroup (MulAut S), innerAut S ≤ H →
      GLAPPrimeCoreOf p (H ⊓ Subgroup.centralizer ({x} : Set (MulAut S))) = ⊥ := by
  intro x hx hxo H hH
  set φ := MulAut.congr e with hφ
  have hinn : innerAut Y ≤ H.map φ.toMonoidHom := by
    rintro _ ⟨y, rfl⟩
    refine ⟨MulAut.conj (e.symm y), hH ⟨e.symm y, rfl⟩, ?_⟩
    ext s
    simp [hφ, MulAut.congr_apply]
  have hx' : φ x ∈ innerAut Y := by
    obtain ⟨g, rfl⟩ := hx
    refine ⟨e g, ?_⟩
    ext s
    simp [hφ, MulAut.congr_apply]
  have h := key _ hinn (φ x) hx' (by rw [MulEquiv.orderOf_eq φ x]; exact hxo)
  exact gLAPPrimeCoreOf_inf_centralizer_of_congr_F4G2 p e H x h

theorem innerCoreFree_of_parCharP_top_F4G2 {Y : Type} [Group Y] [Finite Y] {p : ℕ} [Fact p.Prime]
    (hBT : Holds Y p) (hcen : Subgroup.center Y = ⊥) (hpc : ParCharP Y p ⊤) :
    ∀ H' : Subgroup (MulAut Y), innerAut Y ≤ H' → ∀ x' ∈ innerAut Y, orderOf x' = p →
      GLAPPrimeCoreOf p (H' ⊓ Subgroup.centralizer ({x'} : Set (MulAut Y))) = ⊥ :=
  fun _ hH' _ hx' hxo =>
    gLAPPrimeCoreOf_centralizer_eq_bot_of_parCharP hBT hcen hpc le_top hH' hx' hxo

theorem diagonalFieldActors_eq_top_F4_G2 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (K : Type) [Field K] (hK : Nat.card K = p ^ f) (τ : Tag) (hτ : τ = .F4 ∨ (τ = .G2 ∧ p ≠ 3)) :
    diagonalFieldActors τ K = ⊤ := by
  obtain ⟨hex, -⟩ := odd_F4_and_nonexceptional_G2_automorphism_normal_form hp hp2 hf K hK τ hτ
  refine eq_top_iff.mpr fun α _ => ?_
  obtain ⟨⟨g, σ⟩, hgσ, -⟩ := hex α
  exact EvenExceptionalActorCoverage.mem_diagonalFieldActors_of_inner_field g σ hgσ

theorem innerCoreFree_adjoint_of_actors_top {τ : Tag} {K : Type} [Field K] [Finite K] {p : ℕ}
    [Fact p.Prime] [CharP K p] (htop : diagonalFieldActors τ K = ⊤) :
    ∀ H' : Subgroup (MulAut (adjointGroup τ K)), innerAut (adjointGroup τ K) ≤ H' →
      ∀ x' ∈ innerAut (adjointGroup τ K), orderOf x' = p →
      GLAPPrimeCoreOf p (H' ⊓ Subgroup.centralizer ({x'} : Set (MulAut (adjointGroup τ K)))) = ⊥ := by
  have hcen : Subgroup.center (adjointGroup τ K) = ⊥ := center_adjointGroup_eq_bot
  have hpc : ParCharP (adjointGroup τ K) p (diagonalFieldActors τ K) :=
    parCharP_of_data hcen (pCharData_adjoint τ K p)
  rw [htop] at hpc
  exact innerCoreFree_of_parCharP_top_F4G2 (holds_adjointGroup_tag τ K p) hcen hpc


section G2Three

open Subgroup

theorem g2_ncard_radicalRoots_compl (i : Fin Tag.G2.rank) :
    (parabolicRadicalRoots Tag.G2 ({i}ᶜ : Set (Fin Tag.G2.rank))).ncard = 5 := by
  have h : parabolicRadicalRoots Tag.G2 ({i}ᶜ : Set (Fin Tag.G2.rank)) =
      {α | IsRoot Tag.G2 α ∧ (0 < height α ∧ ¬ α i = 0)} := by
    ext α
    simp only [parabolicRadicalRoots, parabolicPosRoots, parabolicRoots, Set.mem_sdiff,
      Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_singleton_iff, 
      not_and, not_not]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨h1, h2, fun h0 => ?_⟩
      exact absurd ⟨h1, fun k hk => by rwa [show k = i by simpa using hk]⟩ (fun hh => h3 hh h1 h2) 
    · rintro ⟨h1, h2, h3⟩
      refine ⟨⟨h1, h2⟩, fun hh _ _ => ?_⟩
      exact h3 (hh.2 i (by simp))
  rw [h, CFSG.Timmesfeld.ExceptionalOrders.ncard_setOf_isRoot_and]
  fin_cases i <;> decide +kernel


theorem g2_ncard_radicalRoots_ge {J : Set (Fin Tag.G2.rank)} (hJ : J ≠ Set.univ) :
    5 ≤ (parabolicRadicalRoots Tag.G2 J).ncard := by
  obtain ⟨i, hi⟩ : ∃ i, i ∉ J := by
    by_contra h
    push Not at h
    exact hJ (Set.eq_univ_of_forall h)
  have hsub : parabolicRadicalRoots Tag.G2 ({i}ᶜ : Set (Fin Tag.G2.rank)) ⊆
      parabolicRadicalRoots Tag.G2 J := by
    intro α hα
    obtain ⟨⟨h1, h2⟩, h3⟩ := hα
    refine ⟨⟨h1, h2⟩, fun hh => h3 ⟨⟨hh.1.1, fun k hk => ?_⟩, hh.2⟩⟩
    have : k = i := by simpa using hk
    subst this
    exact hh.1.2 _ hi
  have hfin : (parabolicRadicalRoots Tag.G2 J).Finite :=
    (Set.finite_of_ncard_ne_zero (s := {α : Fin Tag.G2.rank → ℤ | IsRoot Tag.G2 α ∧ 0 < height α})
      (by rw [G2FieldFour.ncard_posRoots]; norm_num)).subset (fun α hα => hα.1)
  have := Set.ncard_le_ncard hsub hfin
  rw [g2_ncard_radicalRoots_compl] at this
  exact this

theorem g2_card_radicalIn (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (J : Set (Fin Tag.G2.rank)) :
    Nat.card (parabolicRadicalIn Tag.G2 K J) =
      Nat.card K ^ (parabolicRadicalRoots Tag.G2 J).ncard := by
  obtain ⟨h, -, -⟩ := (parabolic_root_radical_Levi_factors Tag.G2 K J).2.2.2.2.2.2.2.2.2.2.2.2 p
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (parabolicRadical_le_adjointGroup J)).toEquiv).trans h

theorem exists_involution_of_sq_conj {Y : Type} [Group Y] {A : Subgroup (MulAut Y)}
    {Q : Subgroup Y} {p : ℕ} [Fact p.Prime] (hQ : IsPGroup p Q) (hp : Odd p) (α : MulAut Y)
    (hfix : ∀ q ∈ Q, α q = q) (hA2 : α ^ 2 ∈ A)
    (hsq : α ^ 2 ∈ Q.map (MulAut.conj : Y →* MulAut Y)) (hα : α ∉ A) :
    ∃ β : MulAut Y, β ^ 2 = 1 ∧ β ∉ A ∧ ∀ q ∈ Q, β q = q := by
  obtain ⟨q, hq, hqα⟩ := hsq
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 hQ ⟨q, hq⟩
  have hm : orderOf q = p ^ k := by rw [← Subgroup.orderOf_mk q hq, hk]
  have hmodd : Odd (orderOf q) := by rw [hm]; exact hp.pow
  have hpos : ∀ n : ℕ, ∀ x ∈ Q, (α ^ n) x = x := by
    intro n
    induction n with
    | zero => intro x _; simp
    | succ n ih =>
      intro x hx
      rw [pow_succ, MulAut.mul_apply, hfix x hx, ih x hx]
  have hsqm : (α ^ 2) ^ orderOf q = 1 := by
    rw [← hqα, ← map_pow, pow_orderOf_eq_one, map_one]
  obtain ⟨t, ht⟩ := hmodd
  refine ⟨α ^ orderOf q, ?_, ?_, fun x hx => hpos _ x hx⟩
  · rw [← pow_mul, mul_comm, pow_mul]
    exact hsqm
  · intro hβ
    apply hα
    have h1 : α ^ orderOf q = (α ^ 2) ^ t * α := by
      rw [ht, pow_succ, pow_mul]
    have : α = ((α ^ 2) ^ t)⁻¹ * α ^ orderOf q := by
      rw [h1]
      group
    rw [this]
    exact A.mul_mem (A.inv_mem (A.pow_mem hA2 t)) hβ

variable {f : ℕ} {K : Type} [Field K] [Finite K] [CharP K ReeTag.G2.prime]

theorem g2_three_even_mem (hf : 1 ≤ f) (hK : Nat.card K = 3 ^ f)
    (g : adjointGroup ReeTag.G2.tag K) (j : ℕ) :
    MulAut.conj g * ReeTag.G2.finiteExceptionalAut K ^ (2 * j) ∈
      diagonalFieldActors ReeTag.G2.tag K := by
  classical
  obtain ⟨fr, hfr, -, -⟩ := finite_field_automorphism_fixed_field_cardinality Nat.prime_three hf hK
  have hφ : ReeTag.G2.finiteExceptionalAut K ^ (2 * j) =
      exactNormalAut ReeTag.G2.tag K 1 (fr ^ j) 0 := by
    rw [finiteExceptionalAut_pow_two_mul,
      exactNormalAut_one_eq_finiteFrobeniusAut_pow ReeTag.G2
        (σ := fr ^ j) (ringAut_pow_apply_of_frobenius hfr j)]
  refine mem_diagonalFieldActors_of_entrywise ReeTag.G2.tag K _ g (fr ^ j) fun x => ?_
  have hx : ((MulAut.conj g * ReeTag.G2.finiteExceptionalAut K ^ (2 * j)) x :
      ModGL ReeTag.G2.tag K) = (g : ModGL ReeTag.G2.tag K) *
      ((ReeTag.G2.finiteExceptionalAut K ^ (2 * j)) x : ModGL ReeTag.G2.tag K) *
      (g : ModGL ReeTag.G2.tag K)⁻¹ := by
    simp [MulAut.conj_apply]
  rw [hx, hφ, coe_exactNormalAut_zero, rootDiagUnit_one]
  simp

theorem g2_three_sq_mem (hf : 1 ≤ f) (hK : Nat.card K = 3 ^ f)
    (α : MulAut (adjointGroup ReeTag.G2.tag K)) : α ^ 2 ∈ diagonalFieldActors ReeTag.G2.tag K := by
  obtain ⟨-, hex, -⟩ := G2_three_exact_automorphism_normal_form hf K hK
  obtain ⟨⟨g, k⟩, hk, -⟩ := hex α
  set φk := ReeTag.G2.finiteExceptionalAut K ^ (k : ℕ) with hφk
  have hc : φk * MulAut.conj g = MulAut.conj (φk g) * φk := by
    ext x
    simp [MulAut.conj_apply]
  have h2 : α ^ 2 = MulAut.conj (g * φk g) * ReeTag.G2.finiteExceptionalAut K ^ (2 * (k : ℕ)) := by
    rw [hk, pow_two, mul_assoc, ← mul_assoc φk, hc, map_mul, pow_mul', pow_two, ← hφk]
    group
  rw [h2]
  exact g2_three_even_mem hf hK _ _

theorem g2_card_finiteReeFixedGroup (a : ℕ) (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    Nat.card (ReeTag.G2.finiteReeFixedGroup K a) =
      (3 ^ (2 * a + 1)) ^ 3 * ((3 ^ (2 * a + 1)) ^ 3 + 1) * (3 ^ (2 * a + 1) - 1) := by
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element ReeTag.G2.tag
  obtain ⟨-, -, -, -, -, -, -, -, -, h, -⟩ := small_Ree_Borel_coset_Sylow_action a K hK w₀ hw₀
  rw [← mul_right_comm, ← h]
  change Nat.card (ReeTag.G2.finiteReeFixedGroup K a) =
    Nat.card ((ReeTag.G2.finiteReeFixedGroup K a).map (adjointGroup ReeTag.G2.tag K).subtype)
  rw [Subgroup.card_map_of_injective Subtype.val_injective]

theorem not_dvd_aux (k : ℕ) (hk : 1 ≤ k) :
    ¬ (3 ^ k) ^ 2 ∣ ((3 ^ k) ^ 3 + 1) * (3 ^ k - 1) := by
  intro h
  have h3 : 3 ∣ 3 ^ k := dvd_pow_self 3 (by omega)
  have hcop : Nat.Coprime ((3 ^ k) ^ 2) (((3 ^ k) ^ 3 + 1) * (3 ^ k - 1)) := by
    apply Nat.Coprime.pow_left
    apply Nat.Coprime.pow_left
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    intro hd
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 hd with h1 | h1
    · have h4 : 3 ∣ (3 ^ k) ^ 3 := h3.trans (dvd_pow_self _ (by norm_num))
      have := (Nat.dvd_add_right h4).1 h1
      omega
    · have h5 : 1 ≤ 3 ^ k := Nat.one_le_pow _ _ (by norm_num)
      have h7 := Nat.dvd_sub h3 h1
      have h8 : 3 ^ k - (3 ^ k - 1) = 1 := by omega
      rw [h8] at h7
      omega
  have := Nat.Coprime.eq_one_of_dvd hcop h
  have h6 : 3 ≤ 3 ^ k := by
    calc 3 = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  nlinarith

variable (K) in
theorem g2_three_outer_involution_not_fix (hf : 1 ≤ f) (hK : Nat.card K = 3 ^ f)
    {J : Set (Fin ReeTag.G2.tag.rank)} (hJ : J ≠ Set.univ)
    {β : MulAut (adjointGroup ReeTag.G2.tag K)} (hβ : β ^ 2 = 1)
    (hβA : β ∉ diagonalFieldActors ReeTag.G2.tag K)
    (hfix : ∀ q ∈ parabolicRadicalIn ReeTag.G2.tag K J, β q = q) : False := by
  classical
  have h1 : ∀ x : ModGL ReeTag.G2.tag K,
      Units.map (entrywiseHom (1 : K ≃+* K).toRingHom) x = x := fun x => Units.ext (entrywise_id _)
  rcases G2_three_involution_inner_quadratic_or_exceptional hf hK hβ with
    ⟨g, a, h⟩ | ⟨e, he, hKe, δ, hδ, g, a, h⟩ | ⟨b, g, hfb, rfl⟩
  · exact hβA ((EvenExceptionalActorCoverage.mem_diagonalFieldActors_iff β).2
      ⟨g, g.2, a, 1, fun x => by rw [h x, h1]⟩)
  · exact hβA ((EvenExceptionalActorCoverage.mem_diagonalFieldActors_iff β).2
      ⟨g, g.2, a, δ, h⟩)
  · have hK' : Nat.card K = 3 ^ (2 * b + 1) := hfb ▸ hK
    obtain ⟨ψ, hψ⟩ := G2_exceptional_coset_involution_conj b K hK' g hβ
    have hFq : ∀ q ∈ parabolicRadicalIn ReeTag.G2.tag K J,
        ReeTag.G2.finiteReeAut K b (ψ q) = ψ q := by
      intro q hq
      have h2 := congrArg (fun γ : MulAut (adjointGroup ReeTag.G2.tag K) => γ (ψ q)) hψ
      have h3 := hfix q hq
      simp only [MulAut.mul_apply, MulAut.inv_apply_self] at h2 h3
      rw [h3] at h2
      exact h2.symm
    have hle : (parabolicRadicalIn ReeTag.G2.tag K J).map ψ.toMonoidHom ≤
        ReeTag.G2.finiteReeFixedGroup K b := by
      rintro _ ⟨q, hq, rfl⟩
      exact ReeTag.mem_finiteReeFixedGroup.2 (hFq q hq)
    have hdvd := Subgroup.card_dvd_of_le hle
    have hc : Nat.card (parabolicRadicalIn ReeTag.G2.tag K J) =
        Nat.card K ^ (parabolicRadicalRoots ReeTag.G2.tag J).ncard := g2_card_radicalIn K 3 J
    have h5 : 5 ≤ (parabolicRadicalRoots ReeTag.G2.tag J).ncard := g2_ncard_radicalRoots_ge hJ
    rw [Subgroup.card_map_of_injective ψ.injective, hc,
      g2_card_finiteReeFixedGroup b hK', hK'] at hdvd
    have hq5 : (3 ^ (2 * b + 1)) ^ 5 ∣ (3 ^ (2 * b + 1)) ^ (parabolicRadicalRoots ReeTag.G2.tag J).ncard :=
      pow_dvd_pow _ h5
    have hdvd2 := hq5.trans hdvd
    have e1 : (3 ^ (2 * b + 1)) ^ 3 * ((3 ^ (2 * b + 1)) ^ 3 + 1) * (3 ^ (2 * b + 1) - 1) =
        (3 ^ (2 * b + 1)) ^ 3 * (((3 ^ (2 * b + 1)) ^ 3 + 1) * (3 ^ (2 * b + 1) - 1)) := by ring
    rw [e1, show (3 ^ (2 * b + 1)) ^ 5 = (3 ^ (2 * b + 1)) ^ 3 * (3 ^ (2 * b + 1)) ^ 2 by ring] at hdvd2
    exact not_dvd_aux (2 * b + 1) (by omega)
      (Nat.dvd_of_mul_dvd_mul_left (pow_pos (pow_pos (by norm_num) _) 3) hdvd2)

theorem g2_three_hOut (hf : 1 ≤ f) (hK : Nat.card K = 3 ^ f)
    {J : Set (Fin ReeTag.G2.tag.rank)} (hJ : J ≠ Set.univ)
    (α : MulAut (adjointGroup ReeTag.G2.tag K))
    (hfix : ∀ q ∈ parabolicRadicalIn ReeTag.G2.tag K J, α q = q)
    (hsq : α ^ 2 ∈ (parabolicRadicalIn ReeTag.G2.tag K J).map
      (MulAut.conj : adjointGroup ReeTag.G2.tag K →* MulAut (adjointGroup ReeTag.G2.tag K))) :
    α ∈ diagonalFieldActors ReeTag.G2.tag K := by
  by_contra hα
  have : CharP K 3 := ‹CharP K ReeTag.G2.prime›
  have hQp : IsPGroup 3 (parabolicRadicalIn ReeTag.G2.tag K J) :=
    (exact_parabolic_diagonal_field_normalizers_characteristic_p_ordinary (p := 3)
      ReeTag.G2.tag K hJ).2.2.1
  obtain ⟨β, hβ2, hβA, hβfix⟩ := exists_involution_of_sq_conj hQp (by decide) α hfix
    (g2_three_sq_mem hf hK α) hsq hα
  exact g2_three_outer_involution_not_fix K hf hK hJ hβ2 hβA hβfix


theorem pCharData_adjoint_top_of_outer (τ : Tag) (K : Type) [Field K] [Finite K] (p : ℕ)
    [Fact p.Prime] [CharP K p]
    (hSq : ∀ α : MulAut (adjointGroup τ K), α ^ 2 ∈ diagonalFieldActors τ K)
    (hOut : ∀ J : Set (Fin τ.rank), J ≠ Set.univ → ∀ α : MulAut (adjointGroup τ K),
      (∀ q ∈ parabolicRadicalIn τ K J, α q = q) →
      α ^ 2 ∈ (parabolicRadicalIn τ K J).map
        (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)) →
      α ∈ diagonalFieldActors τ K) :
    PCharData (adjointGroup τ K) p ⊤ := by
  classical
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element τ
  obtain ⟨⟨U, hU⟩, -⟩ := exceptional_ordinary_Sylow_opposition τ K p w₀ hw₀
  have hB := borel_self_normalizers τ K
  have hBC : borelGroup τ K ≤ adjointGroup τ K := by
    rw [← hB.1]
    exact inf_le_left
  have hBN : ∀ b ∈ borelGroup τ K,
      b ∈ Subgroup.normalizer (posUnipotent τ K : Set (ModGL τ K)) := by
    intro b hb
    rw [← hB.1] at hb
    exact hb.2
  refine PCharData.of_standard (le_top) U ?_
  intro P hNP hPtop
  have hBle : borelGroup τ K ≤ P.map (adjointGroup τ K).subtype := by
    intro b hb
    have hbC : b ∈ adjointGroup τ K := hBC hb
    have hbN : (⟨b, hbC⟩ : adjointGroup τ K) ∈
        Subgroup.normalizer ((U : Subgroup (adjointGroup τ K)) : Set (adjointGroup τ K)) := by
      rw [hU, Subgroup.mem_normalizer_iff]
      intro u
      have := Subgroup.mem_normalizer_iff.1 (hBN b hb) (u : ModGL τ K)
      constructor
      · intro hu
        exact Subgroup.mem_subgroupOf.2 (this.1 (Subgroup.mem_subgroupOf.1 hu))
      · intro hu
        exact Subgroup.mem_subgroupOf.2 (this.2 (Subgroup.mem_subgroupOf.1 hu))
    exact ⟨_, hNP hbN, rfl⟩
  have hP'C : P.map (adjointGroup τ K).subtype ≤ adjointGroup τ K := Subgroup.map_subtype_le _
  have hcl := (borel_overgroup_classification τ K).1 _ hBle hP'C
  set P' : Subgroup (ModGL τ K) := P.map (adjointGroup τ K).subtype with hP'
  set J : Set (Fin τ.rank) := {i | weylElt τ K i 1 ∈ P'} with hJdef
  have hJ : J ≠ Set.univ := by
    intro h
    apply hPtop
    have hP'top : P' = adjointGroup τ K := by
      rw [hcl, h, (standard_parabolic_cells τ K).2.2.2.2.2.1]
    rw [eq_top_iff]
    intro x _
    have hx : (x : ModGL τ K) ∈ P' := by rw [hP'top]; exact x.2
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := Subtype.ext hyx
    rw [← this]
    exact hy
  have hLevi := parabolic_root_radical_Levi_factors τ K J
  have hPJ : ∀ y : adjointGroup τ K, y ∈ P → (y : ModGL τ K) ∈ parabolicSubgroup τ K J := by
    intro y hy
    rw [← hcl]
    exact ⟨y, hy, rfl⟩
  have hQP : parabolicRadicalIn τ K J ≤ P := by
    intro x hx
    have h1 : (x : ModGL τ K) ∈ parabolicSubgroup τ K J := hLevi.1 (mem_parabolicRadicalIn.1 hx)
    rw [← hcl] at h1
    obtain ⟨y, hy, hyx⟩ := h1
    have : y = x := Subtype.ext hyx
    rw [← this]
    exact hy
  have hQn : ((parabolicRadicalIn τ K J).subgroupOf P).Normal := by
    refine ⟨fun x hx g => ?_⟩
    have hxQ : ((x : adjointGroup τ K) : ModGL τ K) ∈ parabolicRadical τ K J :=
      mem_parabolicRadicalIn.1 (Subgroup.mem_subgroupOf.1 hx)
    have hxP : ((x : adjointGroup τ K) : ModGL τ K) ∈ parabolicSubgroup τ K J := hLevi.1 hxQ
    have hgP := hPJ (g : adjointGroup τ K) g.2
    have key := hLevi.2.1.conj_mem
      (⟨((x : adjointGroup τ K) : ModGL τ K), hxP⟩ : ↥(parabolicSubgroup τ K J))
      (Subgroup.mem_subgroupOf.2 hxQ) ⟨((g : adjointGroup τ K) : ModGL τ K), hgP⟩
    have key' := Subgroup.mem_subgroupOf.1 key
    refine Subgroup.mem_subgroupOf.2 (mem_parabolicRadicalIn.2 ?_)
    simpa using key'
  have hQC : parabolicRadical τ K J ≤ adjointGroup τ K := parabolicRadical_le_adjointGroup J
  have hQp : IsPGroup p (parabolicRadicalIn τ K J) := by
    obtain ⟨-, hQp, -⟩ := hLevi.2.2.2.2.2.2.2.2.2.2.2.2 p
    exact hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQC).symm
  have hrigL :=
    (exact_parabolic_diagonal_field_normalizers_characteristic_p_ordinary (p := p) τ K hJ).2.2.2.1
  have hQP' : parabolicRadicalIn τ K J ≤ P := hQP
  have hkey : ∀ β : MulAut (adjointGroup τ K), β ∈ diagonalFieldActors τ K →
      (∀ q ∈ parabolicRadicalIn τ K J, β q = q) →
      β ∈ (parabolicRadicalIn τ K J).map (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)) := by
    intro β hβA hβfix
    obtain ⟨z, ⟨z', hz', hzz⟩, hzα⟩ := (hrigL β).1 ⟨hβA, hβfix⟩
    have hzQ : z ∈ parabolicRadicalIn τ K J := by
      rw [← hzz]
      exact z'.2
    exact ⟨z, hzQ, hzα⟩
  refine ⟨parabolicRadicalIn τ K J, hQP, hQn, hQp, fun α _ hfix => ?_⟩
  have hfix2 : ∀ q ∈ parabolicRadicalIn τ K J, (α ^ 2) q = q := fun q hq => by
    rw [pow_two, MulAut.mul_apply, hfix q hq, hfix q hq]
  have hα2 := hkey (α ^ 2) (hSq α) hfix2
  exact hkey α (hOut J hJ α hfix hα2) hfix

end G2Three

theorem innerCoreFree_G2_three {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    [CharP K ReeTag.G2.prime] (hK : Nat.card K = 3 ^ f) :
    ∀ H' : Subgroup (MulAut (adjointGroup ReeTag.G2.tag K)),
      innerAut (adjointGroup ReeTag.G2.tag K) ≤ H' →
      ∀ x' ∈ innerAut (adjointGroup ReeTag.G2.tag K), orderOf x' = 3 →
      GLAPPrimeCoreOf 3 (H' ⊓ Subgroup.centralizer
        ({x'} : Set (MulAut (adjointGroup ReeTag.G2.tag K)))) = ⊥ := by
  have : CharP K 3 := ‹CharP K ReeTag.G2.prime›
  have hcen : Subgroup.center (adjointGroup ReeTag.G2.tag K) = ⊥ := center_adjointGroup_eq_bot
  have hd := pCharData_adjoint_top_of_outer ReeTag.G2.tag K 3 (g2_three_sq_mem hf hK)
    (fun J hJ α hfix hsq => g2_three_hOut hf hK hJ α hfix hsq)
  exact innerCoreFree_of_parCharP_top_F4G2 (holds_adjointGroup_tag ReeTag.G2.tag K 3) hcen
    (parCharP_of_data hcen hd)

theorem defCharInnerCoreFreeFamG2 : DefCharInnerCoreFreeFam .G2 := by
  intro S _ _ _ _ idx hidx hS p hp hp2 hch x hx hxo H hH
  obtain ⟨q, hq⟩ := hidx
  obtain ⟨d, hv⟩ := idx
  simp only at hq
  subst hq
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨e0⟩ := hS
  have hpq : p = q.p := by simpa using hch.symm
  subst hpq
  set K := GaloisField q.p q.exponent
  have hK : Nat.card K = q.p ^ q.exponent := GaloisField.card _ _ q.exponent_pos.ne'
  have hK' : Nat.card K = q.card := by rw [hK, TauCeti.PrimePower.card_def]
  obtain ⟨b⟩ := (CFSG.TauCetiBridge.Even.chevalleyBridgesAll).g2 q hv K hK'
  let e : S ≃* adjointGroup .G2 K :=
    e0.trans (b.symm.trans ((QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
      QuotientGroup.quotientBot))
  by_cases h3 : q.p = 3
  · have hchar : CharP K ReeTag.G2.prime := by
      have : CharP K q.p := inferInstance
      rw [show ReeTag.G2.prime = 3 from rfl, ← h3]
      exact this
    have hK3 : Nat.card K = 3 ^ q.exponent := by rw [hK, h3]
    have hkey := innerCoreFree_G2_three q.exponent_pos K hK3
    rw [h3] at hxo
    rw [h3]
    exact innerCoreFree_transport_F4G2 e hkey x hx hxo H hH
  · have htop := diagonalFieldActors_eq_top_F4_G2 hp hp2 q.exponent_pos K hK .G2 (Or.inr ⟨rfl, h3⟩)
    exact innerCoreFree_transport_F4G2 e (innerCoreFree_adjoint_of_actors_top htop) x hx hxo H hH

theorem defCharInnerCoreFreeFamF4 : DefCharInnerCoreFreeFam .F4 := by
  intro S _ _ _ _ idx hidx hS p hp hp2 hch x hx hxo H hH
  obtain ⟨q, hq⟩ := hidx
  obtain ⟨d, hv⟩ := idx
  simp only at hq
  subst hq
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨e0⟩ := hS
  have hpq : p = q.p := by simpa using hch.symm
  subst hpq
  set K := GaloisField q.p q.exponent
  have hK : Nat.card K = q.p ^ q.exponent := GaloisField.card _ _ q.exponent_pos.ne'
  have hK' : Nat.card K = q.card := by rw [hK, TauCeti.PrimePower.card_def]
  obtain ⟨b⟩ := (CFSG.TauCetiBridge.Even.chevalleyBridgesAll).f4 q hv K hK'
  let e : S ≃* adjointGroup .F4 K :=
    e0.trans (b.symm.trans ((QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
      QuotientGroup.quotientBot))
  have htop := diagonalFieldActors_eq_top_F4_G2 hp hp2 q.exponent_pos K hK .F4 (Or.inl rfl)
  exact innerCoreFree_transport_F4G2 e (innerCoreFree_adjoint_of_actors_top htop) x hx hxo H hH

end CFSG.HardMathSupport.Timmesfeld.DefChar
