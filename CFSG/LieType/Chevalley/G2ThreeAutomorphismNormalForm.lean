module

public import CFSG.LieType.Chevalley.OddF4G2AutomorphismNormalForm
public import CFSG.LieType.Ree.RootBruhatEquivariance

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Ree

section Complement

variable {G : Type*} [Group G]

theorem eq_of_conj_mul_pow_eq (hZ : Subgroup.center G = ⊥) {φ : MulAut G} {n : ℕ} (hn : 0 < n)
    (hφn : φ ^ n = 1) (hinn : ∀ (k : ℕ) (h : G), φ ^ k = MulAut.conj h → n ∣ k)
    {g g' : G} {k k' : ℕ} (h : MulAut.conj g * φ ^ k = MulAut.conj g' * φ ^ k') :
    (k : ZMod n) = k' ∧ g = g' := by
  have hinv : (φ ^ k)⁻¹ = φ ^ ((n - 1) * k) := by
    refine inv_eq_of_mul_eq_one_right ?_
    have hk : k + (n - 1) * k = n * k := by
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.sub_add_cancel hn).symm⟩
      rw [Nat.add_sub_cancel]
      ring
    rw [← pow_add, hk, pow_mul, hφn, one_pow]
  have e : MulAut.conj (g'⁻¹ * g) = φ ^ (k' + (n - 1) * k) := by
    rw [pow_add, ← hinv, map_mul, map_inv, inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h,
      mul_inv_cancel_right]
  have hdvd := hinn _ _ e.symm
  have h1 : MulAut.conj (g'⁻¹ * g) = 1 := by
    obtain ⟨m, hm⟩ := hdvd
    rw [e, hm, pow_mul, hφn, one_pow]
  have h2 := mulAut_conj_injective_of_center_eq_bot hZ (h1.trans (map_one _).symm)
  refine ⟨?_, (inv_mul_eq_one.1 h2).symm⟩
  have h3 : ((k' + (n - 1) * k : ℕ) : ZMod n) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hdvd
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hn, Nat.cast_one, ZMod.natCast_self, zero_sub,
    neg_one_mul, add_neg_eq_zero] at h3
  exact h3.symm

theorem mulAut_cyclic_complement_normal_form (hZ : Subgroup.center G = ⊥) (φ : MulAut G)
    {n : ℕ} (hn : 0 < n) (hφn : φ ^ n = 1)
    (hex : ∀ α : MulAut G, ∃ (g : G) (k : ℕ), α = MulAut.conj g * φ ^ k)
    (hinn : ∀ (k : ℕ) (h : G), φ ^ k = MulAut.conj h → n ∣ k) :
    orderOf φ = n ∧
    (∀ α : MulAut G, ∃! gk : G × Fin n, α = MulAut.conj gk.1 * φ ^ (gk.2 : ℕ)) ∧
    (∃ Θ : MulAut G →* Multiplicative (ZMod n),
      (∀ (α : MulAut G) (g : G) (k : ℕ), α = MulAut.conj g * φ ^ k →
        Θ α = Multiplicative.ofAdd (k : ZMod n)) ∧
      Function.Surjective Θ ∧ Θ.ker = (MulAut.conj : G →* MulAut G).range) ∧
    ∀ (α : MulAut G) (g : G) (k : ℕ), α = MulAut.conj g * φ ^ k → α ^ 2 = 1 → n ∣ 2 * k := by
  have : NeZero n := ⟨hn.ne'⟩
  have hkey := fun {g g' : G} {k k' : ℕ} (h : MulAut.conj g * φ ^ k = MulAut.conj g' * φ ^ k') =>
    eq_of_conj_mul_pow_eq hZ hn hφn hinn h
  have hmod : ∀ k : ℕ, φ ^ k = φ ^ (k % n) := fun k => by
    conv_lhs => rw [← Nat.div_add_mod k n]
    rw [pow_add, pow_mul, hφn, one_pow, one_mul]
  have hex' : ∀ α : MulAut G, ∃ (g : G) (k : ℕ), k < n ∧ α = MulAut.conj g * φ ^ k := by
    intro α
    obtain ⟨g, k, rfl⟩ := hex α
    exact ⟨g, k % n, Nat.mod_lt k hn, by rw [← hmod]⟩
  choose gF kF hkF hF using hex'
  have hΘ : ∀ α g (k : ℕ), α = MulAut.conj g * φ ^ k → (kF α : ZMod n) = k := fun α g k h =>
    (hkey ((hF α).symm.trans h)).1
  let Θ : MulAut G →* Multiplicative (ZMod n) :=
    { toFun := fun α => Multiplicative.ofAdd (kF α : ZMod n)
      map_one' := by
        rw [hΘ 1 1 0 (by rw [map_one, one_mul, pow_zero]), Nat.cast_zero, ofAdd_zero]
      map_mul' := fun α β => by
        have e : α * β = MulAut.conj (gF α * (φ ^ kF α) (gF β)) * φ ^ (kF α + kF β) := by
          calc α * β = MulAut.conj (gF α) * φ ^ kF α * (MulAut.conj (gF β) * φ ^ kF β) := by
                rw [← hF α, ← hF β]
            _ = MulAut.conj (gF α) * (φ ^ kF α * MulAut.conj (gF β)) * φ ^ kF β := by
                simp only [mul_assoc]
            _ = MulAut.conj (gF α) * (MulAut.conj ((φ ^ kF α) (gF β)) * φ ^ kF α) *
                φ ^ kF β := by
                rw [mulAut_mul_conj]
            _ = MulAut.conj (gF α * (φ ^ kF α) (gF β)) * φ ^ (kF α + kF β) := by
                rw [map_mul, pow_add]
                simp only [mul_assoc]
        change Multiplicative.ofAdd (kF (α * β) : ZMod n) =
          Multiplicative.ofAdd (kF α : ZMod n) * Multiplicative.ofAdd (kF β : ZMod n)
        rw [hΘ _ _ _ e, Nat.cast_add, ofAdd_add] }
  have hΘ' : ∀ α g (k : ℕ), α = MulAut.conj g * φ ^ k → Θ α = Multiplicative.ofAdd (k : ZMod n) :=
    fun α g k h => congrArg Multiplicative.ofAdd (hΘ α g k h)
  refine ⟨?_, fun α => ?_, ⟨Θ, hΘ', fun z => ?_, ?_⟩, fun α g k hα h2 => ?_⟩
  ·
    refine (orderOf_eq_iff hn).2 ⟨hφn, fun m hm hm0 h1 => ?_⟩
    have := hinn m 1 (by rw [h1, map_one])
    exact absurd (Nat.le_of_dvd hm0 this) (by omega)
  ·
    refine ⟨(gF α, ⟨kF α, hkF α⟩), hF α, fun x hx => ?_⟩
    obtain ⟨h1, h2⟩ := hkey (hx.symm.trans (hF α))
    have h3 : (x.2 : ℕ) = kF α := by
      have := congrArg ZMod.val h1
      rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt x.2.2,
        Nat.mod_eq_of_lt (hkF α)] at this
    exact Prod.ext h2 (Fin.ext h3)
  ·
    refine ⟨φ ^ (Multiplicative.toAdd z).val, ?_⟩
    rw [hΘ' _ 1 _ (by rw [map_one, one_mul]), ZMod.natCast_zmod_val, ofAdd_toAdd]
  ·
    ext α
    rw [MonoidHom.mem_ker]
    constructor
    · intro h1
      have h2 : (kF α : ZMod n) = 0 := h1
      obtain ⟨m, hm⟩ := (ZMod.natCast_eq_zero_iff _ _).1 h2
      have h3 := hF α
      rw [hm, pow_mul, hφn, one_pow, mul_one] at h3
      exact ⟨gF α, h3.symm⟩
    · rintro ⟨g, rfl⟩
      rw [hΘ' _ g 0 (by rw [pow_zero, mul_one]), Nat.cast_zero, ofAdd_zero]
  ·
    have h3 : Θ α ^ 2 = 1 := by rw [← map_pow, h2, map_one]
    rw [hΘ' α g k hα, pow_two, ← ofAdd_add, ofAdd_eq_one] at h3
    refine (ZMod.natCast_eq_zero_iff _ _).1 ?_
    rw [Nat.cast_mul, Nat.cast_two, two_mul, h3]

end Complement

section Exceptional

variable {K : Type} [Field K] [Finite K] (t : ReeTag) [CharP K t.prime]

theorem finiteExceptionalAut_pow_exponent_surjective (i : Fin t.tag.rank) :
    Function.Surjective fun c : K => c ^ t.exponent i := by
  unfold ReeTag.exponent
  split_ifs
  · intro d
    exact ⟨d, pow_one d⟩
  · have := Finite.injective_iff_surjective.1 (frobenius K t.prime).injective
    intro d
    obtain ⟨c, hc⟩ := this d
    exact ⟨c, by rw [frobenius_def] at hc; exact hc⟩

theorem finiteExceptionalAut_mem_unipotentPairAut :
    t.finiteExceptionalAut K ∈ unipotentPairAut t.tag K := by
  have h0 : t.finiteReeAut K 0 = t.finiteExceptionalAut K := by
    rw [ReeTag.finiteReeAut, pow_zero, mul_one]
  refine ⟨?_, ?_⟩
  · rw [← h0]
    exact ReeTag.map_finiteReeAut_posUnipotentSub
  · rw [← h0]
    exact ReeTag.map_finiteReeAut_negUnipotentSub

theorem map_simplePosSubgroup_finiteExceptionalAut
    (i : Fin t.tag.rank) :
    (simplePosSubgroup t.tag K i).map (t.finiteExceptionalAut K).toMonoidHom =
      simplePosSubgroup t.tag K (t.perm i) :=
  map_simplePosSubgroup_of_adjX (finiteExceptionalAut_pow_exponent_surjective t i)
    (ReeTag.finiteExceptionalAut_xElement i)

theorem map_simpleNegSubgroup_finiteExceptionalAut
    (i : Fin t.tag.rank) :
    (simpleNegSubgroup t.tag K i).map (t.finiteExceptionalAut K).toMonoidHom =
      simpleNegSubgroup t.tag K (t.perm i) :=
  map_simpleNegSubgroup_of_adjY (finiteExceptionalAut_pow_exponent_surjective t i)
    (ReeTag.finiteExceptionalAut_yElement i)

theorem finiteExceptionalAut_mul_self :
    t.finiteExceptionalAut K * t.finiteExceptionalAut K = t.finiteFrobeniusAut K :=
  MulEquiv.ext fun g => DFunLike.congr_fun
    (ReeTag.exceptionalEndo_comp_self (CharP.cast_eq_zero K t.prime)
      (ReeTag.shortFaithful (CharP.cast_eq_zero K t.prime))) g

theorem finiteExceptionalAut_pow_two_mul
    (j : ℕ) :
    t.finiteExceptionalAut K ^ (2 * j) = t.finiteFrobeniusAut K ^ j := by
  rw [pow_mul, sq, finiteExceptionalAut_mul_self]

theorem exactNormalAut_one_eq_finiteFrobeniusAut_pow
    {σ : K ≃+* K} {j : ℕ}
    (hσ : ∀ c, σ c = c ^ t.prime ^ j) :
    exactNormalAut t.tag K 1 σ 0 = t.finiteFrobeniusAut K ^ j := by
  refine mulAut_ext_adjX_adjY (fun i c => ?_) fun i c => ?_
  · rw [exactNormalAut_zero_adjX, Pi.one_apply, Units.val_one, one_mul, hσ]
    exact (ReeTag.finiteFrobeniusAut_pow_xElement j i c).symm
  · rw [exactNormalAut_zero_adjY, Pi.one_apply, inv_one, Units.val_one, one_mul, hσ]
    exact (ReeTag.finiteFrobeniusAut_pow_yElement j i c).symm

theorem finiteFrobeniusAut_pow_card
    {f : ℕ} (hK : Nat.card K = t.prime ^ f) :
    t.finiteFrobeniusAut K ^ f = 1 := by
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = t.prime ^ f := by rw [← Nat.card_eq_fintype_card, hK]
  refine mulAut_ext_adjX_adjY (fun i c => ?_) fun i c => ?_
  · change (t.finiteFrobeniusAut K ^ f) (xElement i c) = xElement i c
    rw [ReeTag.finiteFrobeniusAut_pow_xElement, ← hcard, FiniteField.pow_card]
  · change (t.finiteFrobeniusAut K ^ f) (yElement i c) = yElement i c
    rw [ReeTag.finiteFrobeniusAut_pow_yElement, ← hcard, FiniteField.pow_card]

end Exceptional

theorem exactNormalAut_diag_eq_conj
    {τ : Tag} {K : Type} [Field K] (a : Fin τ.rank → Kˣ)
    (ha : rootDiagUnit τ a ∈ adjointGroup τ K) :
    exactNormalAut τ K a 1 0 = MulAut.conj (⟨rootDiagUnit τ a, ha⟩ : adjointGroup τ K) :=
  MulEquiv.ext fun h => Subtype.ext (by
    rw [coe_exactNormalAut_zero, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv]
    congr 2
    exact Units.ext (entrywise_id _))

section G2

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.G2.prime]

theorem G2_two_mul_dvd_of_pow_eq_conj
    {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 3 ^ f) {k : ℕ}
    {h : adjointGroup ReeTag.G2.tag K}
    (hk : ReeTag.G2.finiteExceptionalAut K ^ k = MulAut.conj h) : 2 * f ∣ k := by
  have hA : MulAut.conj h ∈ unipotentPairAut ReeTag.G2.tag K :=
    hk ▸ pow_mem (finiteExceptionalAut_mem_unipotentPairAut ReeTag.G2) k
  obtain ⟨b, hb⟩ := exists_conj_eq_exactNormalAut_diag hA
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' k
  · obtain ⟨fr, hfr, hord, -⟩ :=
      finite_field_automorphism_fixed_field_cardinality Nat.prime_three hf hK
    rw [finiteExceptionalAut_pow_two_mul, ← exactNormalAut_one_eq_finiteFrobeniusAut_pow
      ReeTag.G2 (σ := fr ^ j) (ringAut_pow_apply_of_frobenius hfr j), hb] at hk
    obtain ⟨-, h1⟩ := exactNormalAut_zero_injective hk
    exact Nat.mul_dvd_mul_left 2 (hord ▸ orderOf_dvd_of_pow_eq_one h1)
  · exfalso
    have e := congrArg (fun α : MulAut (adjointGroup ReeTag.G2.tag K) =>
      α (adjX ReeTag.G2.tag K ⟨0, by decide⟩ 1)) hk
    simp only [hb, exactNormalAut_zero_adjX] at e
    rw [pow_succ', MulAut.mul_apply, finiteExceptionalAut_pow_two_mul] at e
    have e2 : (ReeTag.G2.finiteFrobeniusAut K ^ j) (adjX ReeTag.G2.tag K ⟨0, by decide⟩ 1) =
        adjX ReeTag.G2.tag K ⟨0, by decide⟩ 1 := by
      change (ReeTag.G2.finiteFrobeniusAut K ^ j) (xElement _ 1) = xElement _ 1
      rw [ReeTag.finiteFrobeniusAut_pow_xElement, one_pow]
    have e3 : ReeTag.G2.finiteExceptionalAut K (adjX ReeTag.G2.tag K ⟨0, by decide⟩ 1) =
        adjX ReeTag.G2.tag K ⟨1, by decide⟩ 1 := by
      change ReeTag.G2.finiteExceptionalAut K (xElement _ 1) = xElement _ 1
      rw [ReeTag.finiteExceptionalAut_xElement, one_pow]
      rfl
    rw [e2, e3] at e
    have e' : xUnit ReeTag.G2.tag K ⟨1, by decide⟩ 1 = xUnit ReeTag.G2.tag K ⟨0, by decide⟩
        ((b ⟨0, by decide⟩ : K) * (1 : K ≃+* K) 1) := congrArg Subtype.val e
    apply not_commute_xUnit_yUnit (τ := ReeTag.G2.tag) (K := K) ⟨1, by decide⟩
    rw [e']
    exact commute_xUnit_yUnit_of_ne' (by decide) _ 1

theorem G2_exists_conj_mul_pow
    {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 3 ^ f)
    (α : MulAut (adjointGroup ReeTag.G2.tag K)) :
    ∃ (g : adjointGroup ReeTag.G2.tag K) (k : ℕ),
      α = MulAut.conj g * ReeTag.G2.finiteExceptionalAut K ^ k := by
  have hφ2f : ReeTag.G2.finiteExceptionalAut K ^ (2 * f) = 1 := by
    rw [finiteExceptionalAut_pow_two_mul]
    exact finiteFrobeniusAut_pow_card ReeTag.G2 hK
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem ReeTag.G2.tag).length
  obtain ⟨c, β, hU, hV, rfl⟩ :=
    (exceptional_ordinary_Sylow_opposition ReeTag.G2.tag K ReeTag.G2.prime w₀ hw₀).2.2.2.2.2 α
  obtain ⟨π, hπ⟩ :=
    exists_perm_map_simple (show β ∈ unipotentPairAut ReeTag.G2.tag K from ⟨hU, hV⟩)
  have hperm : ∀ π : Equiv.Perm (Fin ReeTag.G2.tag.rank), π = 1 ∨ π = ReeTag.G2.perm := by
    decide
  obtain ⟨ζ, ε, hζ, rfl⟩ : ∃ (ζ : MulAut (adjointGroup ReeTag.G2.tag K)) (ε : ℕ),
      ζ ∈ rootPairAut ReeTag.G2.tag K ∧ β = ζ * ReeTag.G2.finiteExceptionalAut K ^ ε := by
    rcases hperm π with rfl | rfl
    · exact ⟨β, 0, mem_rootPairAut.2 fun i => ⟨(hπ i).1, (hπ i).2⟩, by rw [pow_zero, mul_one]⟩
    · refine ⟨β * ReeTag.G2.finiteExceptionalAut K, 2 * f - 1,
        mem_rootPairAut.2 fun i => ⟨?_, ?_⟩, ?_⟩
      · rw [map_toMonoidHom_mul_mulAut, map_simplePosSubgroup_finiteExceptionalAut, (hπ _).1,
          ReeTag.perm_perm]
      · rw [map_toMonoidHom_mul_mulAut, map_simpleNegSubgroup_finiteExceptionalAut, (hπ _).2,
          ReeTag.perm_perm]
      · rw [mul_assoc, ← pow_succ', Nat.sub_add_cancel (by omega), hφ2f, mul_one]
  obtain ⟨p, hp, -⟩ :=
    (ordinary_Chevalley_root_pair_common_field_parameter ReeTag.G2.tag K).1 ζ hζ
  have hζN : ζ = exactNormalAut ReeTag.G2.tag K p.1 p.2 0 :=
    mulAut_ext_adjX_adjY (fun i c => by rw [(hp i).1, exactNormalAut_zero_adjX])
      fun i c => by rw [(hp i).2.1, exactNormalAut_zero_adjY]
  obtain ⟨fr, hfr, hord, htop, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality Nat.prime_three hf hK
  have hfin : IsOfFinOrder fr := orderOf_pos_iff.1 (by rw [hord]; omega)
  obtain ⟨m, hm⟩ := (Submonoid.mem_powers_iff _ _).1
    (hfin.mem_powers_iff_mem_zpowers.2 (by rw [htop]; exact Subgroup.mem_top p.2))
  have hdC : rootDiagUnit ReeTag.G2.tag p.1 ∈ adjointGroup ReeTag.G2.tag K := by
    obtain ⟨⟨B, hB, -⟩, hrest⟩ :=
      G2_F4_root_character_diagonals_inner ReeTag.G2.tag (Or.inl rfl) K
    exact (hrest B hB p.1).2.2.1
  have hN : exactNormalAut ReeTag.G2.tag K p.1 p.2 0 =
      MulAut.conj (⟨rootDiagUnit ReeTag.G2.tag p.1, hdC⟩ : adjointGroup ReeTag.G2.tag K) *
        ReeTag.G2.finiteExceptionalAut K ^ (2 * m) := by
    calc exactNormalAut ReeTag.G2.tag K p.1 p.2 0 =
        exactNormalAut ReeTag.G2.tag K (p.1 * 1) p.2 0 := by rw [mul_one]
      _ = exactNormalAut ReeTag.G2.tag K p.1 1 0 * exactNormalAut ReeTag.G2.tag K 1 p.2 0 :=
          (exactNormalAut_diag_mul _ _ _ _).symm
      _ = _ := by
          rw [exactNormalAut_diag_eq_conj _ hdC, ← hm, exactNormalAut_one_eq_finiteFrobeniusAut_pow
            ReeTag.G2 (ringAut_pow_apply_of_frobenius hfr m), finiteExceptionalAut_pow_two_mul]
  refine ⟨c * ⟨rootDiagUnit ReeTag.G2.tag p.1, hdC⟩, 2 * m + ε, ?_⟩
  rw [hζN, hN, map_mul, pow_add]
  simp only [mul_assoc]

end G2

theorem G2_three_exact_automorphism_normal_form
    {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K]
    [Finite K] [CharP K ReeTag.G2.prime] (hK : Nat.card K = 3 ^ f) :
    orderOf (ReeTag.G2.finiteExceptionalAut K) = 2 * f ∧
    (∀ α : MulAut (adjointGroup ReeTag.G2.tag K),
      ∃! gk : adjointGroup ReeTag.G2.tag K × Fin (2 * f),
        α = MulAut.conj gk.1 * ReeTag.G2.finiteExceptionalAut K ^ (gk.2 : ℕ)) ∧
    (∃ Θ : MulAut (adjointGroup ReeTag.G2.tag K) →* Multiplicative (ZMod (2 * f)),
      (∀ (α : MulAut (adjointGroup ReeTag.G2.tag K)) (g : adjointGroup ReeTag.G2.tag K) (k : ℕ),
        α = MulAut.conj g * ReeTag.G2.finiteExceptionalAut K ^ k →
          Θ α = Multiplicative.ofAdd (k : ZMod (2 * f))) ∧
      Function.Surjective Θ ∧
      Θ.ker = (MulAut.conj : adjointGroup ReeTag.G2.tag K →*
        MulAut (adjointGroup ReeTag.G2.tag K)).range) ∧
    (∀ (α : MulAut (adjointGroup ReeTag.G2.tag K)) (g : adjointGroup ReeTag.G2.tag K) (k : ℕ),
      k < 2 * f → α = MulAut.conj g * ReeTag.G2.finiteExceptionalAut K ^ k → α ^ 2 = 1 →
        k = 0 ∨ k = f) ∧
    ((ReeTag.G2.finiteExceptionalAut K ^ f) ^ 2 = 1 ∧ ReeTag.G2.finiteExceptionalAut K ^ f ≠ 1) ∧
    (Even f → ReeTag.G2.finiteExceptionalAut K ^ f = ReeTag.G2.finiteFrobeniusAut K ^ (f / 2) ∧
      ∃ σ : K ≃+* K, σ ≠ 1 ∧ σ ^ 2 = 1 ∧ (∀ c, σ c = c ^ (3 ^ (f / 2))) ∧
        Nat.card {c : K // σ c = c} = 3 ^ (f / 2) ∧
        ∀ g : adjointGroup ReeTag.G2.tag K,
          ((ReeTag.G2.finiteExceptionalAut K ^ f) g : ModGL ReeTag.G2.tag K) =
            Units.map (entrywiseHom σ.toRingHom) (g : ModGL ReeTag.G2.tag K)) ∧
    ∀ a : ℕ, f = 2 * a + 1 →
      ReeTag.G2.finiteExceptionalAut K ^ f =
          ReeTag.G2.finiteExceptionalAut K * ReeTag.G2.finiteFrobeniusAut K ^ a ∧
        ReeTag.G2.finiteExceptionalAut K ^ f = ReeTag.G2.finiteReeAut K a ∧
        ∀ g : adjointGroup ReeTag.G2.tag K,
          g ∈ ReeTag.G2.finiteReeFixedGroup K a ↔ (ReeTag.G2.finiteExceptionalAut K ^ f) g = g := by
  have hφ2f : ReeTag.G2.finiteExceptionalAut K ^ (2 * f) = 1 := by
    rw [finiteExceptionalAut_pow_two_mul]
    exact finiteFrobeniusAut_pow_card ReeTag.G2 hK
  obtain ⟨hord, hNF, hΘ, hinv⟩ := mulAut_cyclic_complement_normal_form center_adjointGroup_eq_bot
    (ReeTag.G2.finiteExceptionalAut K) (by omega) hφ2f (G2_exists_conj_mul_pow hf hK)
    fun k h hk => G2_two_mul_dvd_of_pow_eq_conj hf hK hk
  refine ⟨hord, hNF, hΘ, fun α g k hk hα h2 => ?_, ⟨?_, ?_⟩, fun hev => ?_, fun a ha => ?_⟩
  ·
    obtain ⟨m, rfl⟩ := (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 2)).1 (hinv α g k hα h2)
    have hm : m < 2 := Nat.lt_of_mul_lt_mul_left (by linarith : f * m < f * 2)
    interval_cases m <;> simp
  · rw [← pow_mul, mul_comm, hφ2f]
  · intro h1
    have := orderOf_dvd_of_pow_eq_one h1
    rw [hord] at this
    exact absurd (Nat.le_of_dvd (by omega) this) (by omega)
  ·
    have hf2 : 2 * (f / 2) = f := Nat.two_mul_div_two_of_even hev
    have hφf : ReeTag.G2.finiteExceptionalAut K ^ f =
        ReeTag.G2.finiteFrobeniusAut K ^ (f / 2) := by
      conv_lhs => rw [← hf2]
      exact finiteExceptionalAut_pow_two_mul ReeTag.G2 (f / 2)
    obtain ⟨fr, hfr, hfrord, -⟩ :=
      finite_field_automorphism_fixed_field_cardinality Nat.prime_three hf hK
    have hσc : ∀ c, (fr ^ (f / 2)) c = c ^ (3 ^ (f / 2)) := ringAut_pow_apply_of_frobenius hfr _
    have hσ1 : fr ^ (f / 2) ≠ 1 := by
      intro h1
      have := orderOf_dvd_of_pow_eq_one h1
      rw [hfrord] at this
      exact absurd (Nat.le_of_dvd (by omega) this) (by omega)
    have hσ2 : (fr ^ (f / 2)) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm, hf2, ← hfrord, pow_orderOf_eq_one]
    obtain ⟨-, -, hcard⟩ := ringEquiv_sq_eq_one_facts Nat.prime_three hf hK hσ2 hσ1
    refine ⟨hφf, fr ^ (f / 2), hσ1, hσ2, hσc, hcard, fun g => ?_⟩
    rw [hφf, ← exactNormalAut_one_eq_finiteFrobeniusAut_pow ReeTag.G2 hσc,
      coe_exactNormalAut_zero, rootDiagUnit_one, one_mul, inv_one, mul_one]
  ·
    have hφf : ReeTag.G2.finiteExceptionalAut K ^ f =
        ReeTag.G2.finiteExceptionalAut K * ReeTag.G2.finiteFrobeniusAut K ^ a := by
      rw [ha, pow_succ', finiteExceptionalAut_pow_two_mul]
    exact ⟨hφf, hφf, fun g => by rw [hφf]; exact Iff.rfl⟩

end CFSG.LieType.Chevalley
