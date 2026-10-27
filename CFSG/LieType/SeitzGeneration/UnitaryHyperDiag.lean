module

public import CFSG.LieType.SeitzGeneration.UnitaryHyperEx
public import CFSG.LocalAnalysis.SectionRank.OddCover.ScalarCover

public noncomputable section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag CFSG.SectionRank.OddCover
  Matrix

variable {ℓ f p : ℕ} {K : Type} [Field K]

section Vec

@[expose] def extZero (n : ℕ) : (Fin 5 → ZMod p) →+ (Fin n → ZMod p) where
  toFun w i := if h : i.val < 5 then w ⟨i.val, h⟩ else 0
  map_zero' := by
    funext i
    simp
  map_add' w w' := by
    funext i
    simp only [Pi.add_apply]
    split_ifs <;> simp

@[expose] def diagVec (n : ℕ) : (Fin 3 → ZMod p) →+ (Fin n → ZMod p) :=
  (extZero n).comp (sumZeroHom 3)

theorem diagVec_apply_lt (n : ℕ) (u : Fin 3 → ZMod p) (i : Fin n) (h : i.val < 5) :
    diagVec n u i = sumZeroVec u ⟨i.val, h⟩ := by
  simp [diagVec, extZero, sumZeroHom, h]

theorem diagVec_apply_ge (n : ℕ) (u : Fin 3 → ZMod p) (i : Fin n) (h : 5 ≤ i.val) :
    diagVec n u i = 0 := by
  simp [diagVec, extZero, sumZeroHom, show ¬ i.val < 5 by omega]

theorem diagVec_three (n : ℕ) (u : Fin 3 → ZMod p) (i : Fin n) (h : i.val = 3) :
    diagVec n u i = 0 := by
  rw [diagVec_apply_lt n u i (by omega)]
  simp [sumZeroVec, Fin.snoc, h]

theorem sum_diagVec {n : ℕ} (hn : 5 ≤ n) (u : Fin 3 → ZMod p) : ∑ i, diagVec n u i = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 5 + k := ⟨n - 5, by omega⟩
  rw [Fin.sum_univ_add]
  have h1 : ∀ j : Fin 5, diagVec (5 + k) u (Fin.castAdd k j) = sumZeroVec u j := fun j => by
    rw [diagVec_apply_lt _ u _ (by simp)]
    rfl
  have h2 : ∀ j : Fin k, diagVec (5 + k) u (Fin.natAdd 5 j) = 0 := fun j =>
    diagVec_apply_ge _ u _ (by simp)
  simp only [h1, h2, Finset.sum_const_zero, add_zero]
  exact sum_sumZeroVec u

theorem diagVec_inj {n : ℕ} (hn : 5 ≤ n) (u : Fin 3 → ZMod p) (h : ∀ i, diagVec n u i = 0) :
    u = 0 := by
  funext j
  have hj : j.val < 3 := j.isLt
  have := h ⟨j.val, by omega⟩
  rw [diagVec_apply_lt n u _ (show j.val < 5 by omega)] at this
  have e : (⟨j.val, by omega⟩ : Fin 5) = (j.castSucc).castSucc := Fin.ext rfl
  rw [e] at this
  simpa [sumZeroVec] using this

end Vec

section Diag

variable (h : UnitaryFieldData ℓ f K) {n : ℕ}

@[expose] def diagSU (hn : 5 ≤ n) (ζ : Kˣ) (hζ : ζ ^ p = 1) (hζu : ζ ^ (ℓ ^ f + 1) = 1)
    [NeZero p] : Multiplicative (Fin 3 → ZMod p) →* unitarySU ℓ f K n :=
  (torusWit ζ hζ (diagVec n)).codRestrict _ fun u =>
    torusWit_mem_SU (pow_ne_zero _ h.prime.ne_zero) hζ hζu (diagVec n) (sum_diagVec hn) u

abbrev projSU' (n : ℕ) : unitarySU ℓ f K n →* StatedProj (StatedSU n (ℓ ^ f) K) :=
  QuotientGroup.mk' ((StatedScalars (Fin n) K).subgroupOf (unitarySU ℓ f K n))

theorem diagSU_proj_injective (hn : 5 ≤ n) (ζ : Kˣ) (hζ : ζ ^ p = 1) (hζr : orderOf ζ = p)
    (hζu : ζ ^ (ℓ ^ f + 1) = 1) [NeZero p] :
    Function.Injective ((projSU' (ℓ := ℓ) (f := f) (K := K) n).comp (diagSU h hn ζ hζ hζu)) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro u hu
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hu
  have h2 := (QuotientGroup.eq_one_iff _).1 hu
  obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 h2
  exact (Subgroup.mem_bot).2 (eq_one_of_torusWit_scalar hζ hζr (diagVec n) ⟨3, by omega⟩
    (fun u => diagVec_three n u _ rfl) (fun u hu => diagVec_inj hn u hu) u hc.symm)

theorem card_range_of_injective {G H : Type*} [Group G] [Group H] {φ : G →* H}
    (hφ : Function.Injective φ) : Nat.card φ.range = Nat.card G :=
  (Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv).symm

theorem isElemAbelian_range {H : Type*} [Group H] {k : ℕ}
    (φ : Multiplicative (Fin k → ZMod p) →* H) : IsElemAbelian p φ.range := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨a, ha⟩ := x.2
    obtain ⟨b, hb⟩ := y.2
    apply Subtype.ext
    change (x : H) * y = y * x
    rw [← ha, ← hb, ← map_mul, ← map_mul, mul_comm]
  · obtain ⟨a, rfl⟩ := hx
    rw [← map_pow, multiplicative_zmod_pow_eq_one, map_one]

theorem exists_zeta_unitary (h : UnitaryFieldData ℓ f K) (hp : p.Prime) (hpq : p ∣ ℓ ^ f + 1) :
    ∃ ζ : Kˣ, orderOf ζ = p ∧ ζ ^ p = 1 ∧ ζ ^ (ℓ ^ f + 1) = 1 := by
  have := h.finite
  have : Fact p.Prime := ⟨hp⟩
  have hq1 : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ h.prime.pos
  have hdvd : p ∣ Nat.card K - 1 := by
    rw [h.card_eq_sq, sq_sub_one_eq hq1]
    exact Dvd.dvd.mul_right hpq _
  obtain ⟨ζ, hζ⟩ := exists_zeta hdvd
  refine ⟨ζ, hζ, hζ ▸ pow_orderOf_eq_one ζ, ?_⟩
  exact orderOf_dvd_iff_pow_eq_one.mp (hζ ▸ hpq)

theorem exists_hyperGen_diag_toral (h : UnitaryFieldData ℓ f K) {n : ℕ} (hn : 5 ≤ n + 1)
    (hp : p.Prime) (hpq : p ∣ ℓ ^ f + 1) (hq : ℓ ^ f ≠ 2) :
    ∃ E : Subgroup (StatedProj (StatedSU (n + 1) (ℓ ^ f) K)), IsElemAbelian p E ∧
      Nat.card E = p ^ 3 ∧
        HyperGen p (⊤ : Subgroup (StatedProj (StatedSU (n + 1) (ℓ ^ f) K))) E := by
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζr, hζ, hζu⟩ := exists_zeta_unitary h hp hpq
  set φ := diagSU h hn ζ hζ hζu with hφ
  have hinj := diagSU_proj_injective h hn ζ hζ hζr hζu
  have hφinj : Function.Injective φ := fun a b hab => hinj (by
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hab])
  set A := φ.range with hA
  have hAcard : Nat.card A = p ^ 3 := by
    rw [hA, card_range_of_injective hφinj, card_multiplicative_zmod]
  have hAel := isElemAbelian_range (p := p) φ
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAel.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have htop := hyperClosure_eq_top_unitarySU_toral h hp hpq hq A hcomm hAel.2 hAcard
  have hdis : Disjoint A (projSU' (ℓ := ℓ) (f := f) (K := K) (n + 1)).ker := by
    rw [Subgroup.disjoint_def]
    rintro _ ⟨u, rfl⟩ hu
    have : u = 1 := hinj (by rw [MonoidHom.comp_apply, map_one]; exact hu)
    rw [this, map_one]
  refine ⟨((projSU' (n + 1)).comp φ).range, isElemAbelian_range _, ?_, ?_⟩
  · rw [card_range_of_injective hinj, card_multiplicative_zmod]
  · have hAE : A.map (projSU' (ℓ := ℓ) (f := f) (K := K) (n + 1)) =
        ((projSU' (n + 1)).comp φ).range := by
      rw [hA, MonoidHom.range_comp]
    intro k _
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ k
    have hg : g ∈ hyperClosure p ⊤ A := by
      rw [htop]
      exact Subgroup.mem_top g
    exact map_hyperClosure_le_of_lift hAE hdis ⟨g, hg, rfl⟩

theorem torusWit_diagVec_mulVec {n : ℕ} (hn : 6 ≤ n) (ζ : Kˣ) (hζ : ζ ^ p = 1) [NeZero p]
    (u : Multiplicative (Fin 3 → ZMod p)) :
    ((torusWit ζ hζ (diagVec n) u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
        (Pi.single ⟨3, by omega⟩ 1 + Pi.single ⟨5, by omega⟩ 1) =
      Pi.single ⟨3, by omega⟩ 1 + Pi.single ⟨5, by omega⟩ 1 := by
  classical
  rw [torusWit_apply, coe_diagHom]
  funext x
  rw [mulVec_diagonal]
  by_cases h3 : x = ⟨3, by omega⟩
  · subst h3
    rw [diagVec_three n _ _ rfl]
    simp
  by_cases h5 : x = ⟨5, by omega⟩
  · subst h5
    rw [diagVec_apply_ge n _ _ (le_refl 5)]
    simp
  · simp [h3, h5]

theorem exists_hyperGen_diag_two (h : UnitaryFieldData ℓ f K) (hq2 : ℓ ^ f = 2) {n : ℕ}
    (hn : 6 ≤ n) :
    ∃ E : Subgroup (StatedProj (StatedSU n (ℓ ^ f) K)), IsElemAbelian 3 E ∧
      Nat.card E = 3 ^ 3 ∧ HyperGen 3 (⊤ : Subgroup (StatedProj (StatedSU n (ℓ ^ f) K))) E := by
  classical
  have hfin := h.finite
  have : Fact ℓ.Prime := ⟨h.prime⟩
  have := h.charP
  have hℓ2 : ℓ = 2 := ((Nat.Prime.pow_eq_iff Nat.prime_two).mp hq2).1
  have : NeZero 3 := ⟨by norm_num⟩
  obtain ⟨ζ, hζr, hζ, hζu⟩ := exists_zeta_unitary h Nat.prime_three (by rw [hq2])
  set σ := CFSG.LieType.BorelTits.unitaryInvolution K ℓ f with hσdef
  have hσ : IsUnitaryInvolution σ := isUnitaryInvolution_unitaryInvolution h.card_eq_sq
  have hn5 : 5 ≤ n := by omega
  set φ := diagSU h hn5 ζ hζ hζu with hφ
  have hinj := diagSU_proj_injective h hn5 ζ hζ hζr hζu
  let φ' : Multiplicative (Fin 3 → ZMod 3) →* SUid σ n :=
    (MulEquiv.subgroupCongr (suid_unitaryInvolution_eq h n).symm).toMonoidHom.comp φ
  have hcompat : ∀ u, projSUid h n (φ' u) = projSU' (ℓ := ℓ) (f := f) (K := K) n (φ u) :=
    fun u => rfl
  have hφ'mat : ∀ u, (((φ' u : SUid σ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((torusWit ζ hζ (diagVec n) u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := fun u => rfl
  set E := ((projSU' (ℓ := ℓ) (f := f) (K := K) n).comp φ).range with hEdef
  have hE : IsElemAbelian 3 E := isElemAbelian_range _
  have hcard : Nat.card E = 3 ^ 3 := by
    rw [hEdef, card_range_of_injective hinj, card_multiplicative_zmod]
  refine ⟨E, hE, hcard, ?_⟩
  set w : Fin n → K := Pi.single ⟨3, by omega⟩ 1 + Pi.single ⟨5, by omega⟩ 1 with hw
  have hw0 : w ≠ 0 := by
    intro h0
    have := congrFun h0 ⟨3, by omega⟩
    simp [hw] at this
  have hfix : ∀ u, φ' u • w = w := fun u => by
    rw [smul_def σ, hφ'mat, hw]
    exact torusWit_diagVec_mulVec hn ζ hζ u
  have hww : herm σ w w = 0 := by
    subst hℓ2
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    simp only [hw, herm_add_left, herm_add_right, herm_single_left, map_one, one_mul,
      Pi.single_apply]
    simp only [Fin.mk.injEq, ite_true, ite_false, show (3 : ℕ) ≠ 5 by norm_num,
      show (5 : ℕ) ≠ 3 by norm_num, add_zero, zero_add]
    rw [← two_mul, h2, zero_mul]
  have hpK : ((3 : ℕ) : K) ≠ 0 := by
    subst hℓ2
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    have : ((3 : ℕ) : K) = 1 := by
      have : ((3 : ℕ) : K) = 2 + 1 := by push_cast; ring
      rw [this, h2, zero_add]
    rw [this]
    exact one_ne_zero
  refine hyperGen_top_of_isotropic_unitary hσ (by omega) (fun h3 => absurd h3 (by omega))
    (projSUid h n) (projSUid_surjective h n) (projSUid_ker_scalar h n) Nat.prime_three
    (by norm_num) hpK hE hcard (W := K ∙ w) ?_ ?_ ?_
  · exact fun hW => hw0 (Submodule.span_singleton_eq_bot.mp hW)
  · intro x hx y hy
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [herm_smul_left, herm_smul_right, hww, mul_zero, mul_zero]
  · intro g hg x hx
    obtain ⟨u, hu⟩ := hg
    rw [MonoidHom.comp_apply, ← hcompat] at hu
    have hz : (φ' u)⁻¹ * g ∈ (projSUid h n).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hu, inv_mul_cancel]
    obtain ⟨c, hc⟩ := projSUid_ker_scalar h n _ hz
    have hc' : ((((φ' u)⁻¹ * g : SUid σ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        c • 1 := hc
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hx
    have hgz : g = φ' u * ((φ' u)⁻¹ * g) := by group
    rw [hgz, mul_smul, smul_def σ ((φ' u)⁻¹ * g), hc', Matrix.smul_mulVec, Matrix.one_mulVec,
      smul_comm (φ' u) c, smul_comm (φ' u) t, hfix]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w))

theorem pRank_three_projSU_three_le [Finite K] (h : UnitaryFieldData ℓ f K)
    (h3 : 3 ∣ ℓ ^ f + 1) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedSU 3 (ℓ ^ f) K))) ≤ 2 := by
  have : Fact ℓ.Prime := ⟨h.prime⟩
  have := h.charP
  have hq1 : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ h.prime.pos
  have hD3 : Nat.card ((StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 (ℓ ^ f) K)) = 3 := by
    rw [← unitaryScalars_eq h (by norm_num), card_unitaryScalars h (by norm_num)]
    exact Nat.gcd_eq_left h3
  have hp3 : ℓ ≠ 3 := by
    rintro rfl
    have h3q : 3 ∣ 3 ^ f := dvd_pow_self 3 (by have := h.one_le; omega)
    have : 3 ∣ 1 := (Nat.dvd_add_right h3q).mp h3
    omega
  refine three_pRank_statedProj_le_two monomialData_statedSU ?_ hD3
  rw [card_statedSU_three h.card_eq_sq, card_normOne h.card_eq_sq,
    ← factorization_six_mul_three (by positivity)]
  have hqq : ℓ ^ f ≤ (ℓ ^ f) ^ 2 := Nat.le_self_pow (by norm_num) _
  have e1 : (ℓ ^ f) ^ 2 - 1 = (ℓ ^ f + 1) * (ℓ ^ f - 1) := sq_sub_one_eq hq1
  have e2 : (ℓ ^ f) ^ 3 + 1 = (ℓ ^ f + 1) * ((ℓ ^ f) ^ 2 - ℓ ^ f + 1) := by
    zify [hqq]
    ring
  rw [e1, e2]
  exact factorization_order_eq Nat.prime_three (by norm_num) (by positivity) (by omega)
    (by omega) (by omega)
    (fun hd => hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three h.prime).1
      (Nat.prime_three.dvd_of_dvd_pow hd)).symm)
    (by
      intro hd
      have h1 : 3 ∣ (ℓ ^ f + 1) - (ℓ ^ f - 1) := Nat.dvd_sub h3 hd
      rw [show (ℓ ^ f + 1) - (ℓ ^ f - 1) = 2 by omega] at h1
      omega)
    (factorization_sq_sub_add_one Nat.prime_three h3)

end Diag

section Index

open TauCeti

@[expose] def UToralRestPrime (d : ValidLieTypeIndex) (p : ℕ) : Prop :=
  ∃ (m : ℕ) (q : PrimePower), d.1 = .twistedA m q ∧ p ∣ q.card + 1 ∧
    (q.card = 2 ∨ p ∣ Nat.gcd (m + 1) (q.card + 1))

@[expose] def UNonsplitPrime (d : ValidLieTypeIndex) (p : ℕ) : Prop :=
  ∃ (m : ℕ) (q : PrimePower), d.1 = .twistedA m q ∧ ¬ p ∣ q.card - 1 ∧ ¬ p ∣ q.card + 1

@[expose] def UnitaryHyperExNonsplit : Prop := SeitzHyperLieEx fun d p _ => UNonsplitPrime d p

theorem hyperGen_map_symm {G G' : Type*} [Group G] [Group G'] (e : G ≃* G') {p : ℕ}
    {E : Subgroup G'} (h : HyperGen p (⊤ : Subgroup G') E) :
    HyperGen p (⊤ : Subgroup G) (E.map e.symm.toMonoidHom) := by
  refine hyperGen_top_of_mulEquiv e ?_
  have : (E.map e.symm.toMonoidHom).map e.toMonoidHom = E := by
    rw [Subgroup.map_map]
    convert Subgroup.map_id E
    ext x
    simp
  rwa [this]

theorem seitzHyperLieEx_unitary_toralRest : SeitzHyperLieEx fun d p _ => UToralRestPrime d p := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hlist ⟨E₀, hE, hc, m, q, hd, hpq, hrest⟩
  simp only at hd
  subst hd
  have hrange := (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
  have hm2 : 2 ≤ m := hrange.1
  have hU := CFSG.RankThree.PartTwo.Census.unitaryFieldData_galoisField
    (ValidLieTypeIndex.characteristic ⟨.twistedA m q, hv⟩)
    (ValidLieTypeIndex.fieldExponent ⟨.twistedA m q, hv⟩)
    (ValidLieTypeIndex.fieldExponent_pos ⟨.twistedA m q, hv⟩)
  have hfin := hU.finite
  have hqc := card_twistedA m q hv
  let e := CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj m q hv
  have hfinish : ∀ {E : Subgroup (StatedProj (StatedSU (m + 1)
      (ValidLieTypeIndex.characteristic ⟨.twistedA m q, hv⟩ ^
        ValidLieTypeIndex.fieldExponent ⟨.twistedA m q, hv⟩)
      (GaloisField (ValidLieTypeIndex.characteristic ⟨.twistedA m q, hv⟩)
        (2 * ValidLieTypeIndex.fieldExponent ⟨.twistedA m q, hv⟩))))},
      IsElemAbelian p E → Nat.card E = p ^ 3 → HyperGen p ⊤ E →
      ∃ E' : Subgroup (Cat ⟨.twistedA m q, hv⟩), IsElemAbelian p E' ∧ Nat.card E' = p ^ 3 ∧
        HyperGen p (⊤ : Subgroup (Cat ⟨.twistedA m q, hv⟩)) E' := by
    intro E hEl hEc hHG
    refine ⟨E.map e.symm.toMonoidHom,
      CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hEl _, ?_,
      hyperGen_map_symm e hHG⟩
    rw [Subgroup.card_map_of_injective e.symm.injective, hEc]
  by_cases hq2 : q.card = 2
  ·
    have hp3 : p = 3 := by
      rw [hq2] at hpq
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 hpq
    subst hp3
    have hqpe : q.p = 2 ∧ q.exponent = 1 := by
      rw [PrimePower.card_def] at hq2
      exact (Nat.Prime.pow_eq_iff Nat.prime_two).mp hq2
    have hm6 : 6 ≤ m + 1 := by
      by_contra hlt
      apply hlist
      have hm3 : m ≠ 2 := fun h => by
        have := hrange.2 h
        omega
      have hm4 : m ≤ 4 := by omega
      interval_cases m
      · exact absurd rfl hm3
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨q, Or.inr ⟨rfl, hqpe.1, hqpe.2, rfl⟩⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, q, hqpe.1, hqpe.2,
          Or.inr (Or.inr (Or.inl rfl))⟩))))
    obtain ⟨E, hEl, hEc, hHG⟩ := exists_hyperGen_diag_two hU (by rw [hqc]; exact hq2) hm6
    exact hfinish hEl hEc hHG
  · rcases hrest with hq2' | hgcd
    · exact absurd hq2' hq2
    have hpn : p ∣ m + 1 := hgcd.trans (Nat.gcd_dvd_left _ _)
    by_cases hm5 : 5 ≤ m + 1
    · obtain ⟨E, hEl, hEc, hHG⟩ := exists_hyperGen_diag_toral hU (n := m) hm5 hp
        (by rw [hqc]; exact hpq) (by rw [hqc]; exact hq2)
      exact hfinish hEl hEc hHG
    · have hm' : m + 1 = 3 ∨ m + 1 = 4 := by omega
      rcases hm' with h3 | h4
      ·
        have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (h3 ▸ hpn)
        subst hp3
        exfalso
        obtain rfl : m = 2 := by omega
        have hr := pRank_three_projSU_three_le hU (by rw [hqc]; exact hpq)
        have hE' : IsElemAbelian 3 (E₀.map e.toMonoidHom) :=
          CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 3 hE _
        have hc' : Nat.card (E₀.map e.toMonoidHom) = 3 ^ 3 := by
          rw [Subgroup.card_map_of_injective e.injective, hc]
        have h3le : 3 ≤ CFSG.Open.pRank 3
            (⊤ : Subgroup (StatedProj (StatedSU 3 _ (GaloisField _ _)))) :=
          le_csSup (CFSG.SectionRank.pRank_bddAbove (by norm_num) _) ⟨_, le_top, hE', hc'⟩
        omega
      · have hp2' : p ∣ 4 := h4 ▸ hpn
        have : p ∣ 2 ^ 2 := by norm_num; exact hp2'
        have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow this)
        exact absurd this hp2

theorem unitaryHyperExRest_of_nonsplit (h : UnitaryHyperExNonsplit) : UnitaryHyperExRest := by
  refine SeitzHyperLieEx.of_cover (S₁ := fun d p _ => UToralRestPrime d p)
    (S₂ := fun d p _ => UNonsplitPrime d p) (fun d p _ hd => ?_)
    seitzHyperLieEx_unitary_toralRest h
  obtain ⟨m, q, hd, h1, h2⟩ := hd
  by_cases h3 : p ∣ q.card + 1
  · left
    refine ⟨m, q, hd, h3, ?_⟩
    by_contra hcon
    push Not at hcon
    exact h2 ⟨h3, hcon.1, hcon.2⟩
  · exact Or.inr ⟨m, q, hd, h1, h3⟩

theorem hyperExFor_unitary_of_nonsplit (h : UnitaryHyperExNonsplit) :
    HyperExFor fun d => IsUnitaryIndex' d.1 :=
  hyperExFor_unitary_of_rest (unitaryHyperExRest_of_nonsplit h)

end Index

end CFSG.LieType.SeitzGeneration
