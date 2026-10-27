module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShE6Defs
public import CFSG.RankThree.PartOne.KE.D4TranspositionInterface
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24D4T2Outer
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24D4T2Inner
import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.ExcTrialityOrient
public import CFSG.RankThree.PartOne.KD4T.Emb

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T158

section Search

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KD4T
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24

private def d4t2unPerms : List (Equiv.Perm (Fin Tag.E6.rank)) :=
  [Equiv.swap (e6Idx 1) (e6Idx 2), Equiv.swap (e6Idx 1) (e6Idx 4), Equiv.swap (e6Idx 2) (e6Idx 4)]

private def d4t2unCong (b : Fin Tag.E6.rank → ℤ) : Bool := (b 0 + b 5 - 1) % 3 == 0

private def d4t2unPair (π : Equiv.Perm (Fin Tag.E6.rank)) (b₀ b₅ : Fin Tag.E6.rank → ℤ) :
    Bool :=
  d4t2outGram π b₅ 5 && d4t2unCong b₅ && iform b₀ b₅ == 0 &&
    (List.finRange Tag.E6.rank).all fun t => (d4t2outVec π b₀ b₅ t - d4t2outZeta t) % 3 == 0

private def d4t2unCheck : Bool :=
  d4t2unPerms.all fun π => (List.range e6Certificate.roots.length).all fun k =>
    !(d4t2outGram π (e6Certificate.root k) 0 && d4t2unCong (e6Certificate.root k)) ||
      (List.range e6Certificate.roots.length).all fun m =>
        !d4t2unPair π (e6Certificate.root k) (e6Certificate.root m)

private theorem d4t2unCheck_eq : d4t2unCheck = true := by decide +kernel


private theorem d4t2un_no_weyl {π : Equiv.Perm (Fin Tag.E6.rank)} (hπ : π ∈ d4t2unPerms)
    {w₀ : WeylGroup Tag.E6}
    (hw₀ : ∀ j ∈ d4Set Tag.E6, w₀ • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) = Pi.single (π j) 1)
    (h0 : (3 : ℤ) ∣ (w₀ • (Pi.single 0 1 : Fin Tag.E6.rank → ℤ)) 0 +
      (w₀ • (Pi.single 0 1 : Fin Tag.E6.rank → ℤ)) 5 - 1)
    (h5 : (3 : ℤ) ∣ (w₀ • (Pi.single 5 1 : Fin Tag.E6.rank → ℤ)) 0 +
      (w₀ • (Pi.single 5 1 : Fin Tag.E6.rank → ℤ)) 5 - 1) : False := by
  obtain ⟨k, hk, hkb⟩ := RootCertificate.exists_root_eq e6Certificate_check
    (IsRoot.smul (IsRoot.basis (0 : Fin Tag.E6.rank)) w₀)
  obtain ⟨m, hm, hmb⟩ := RootCertificate.exists_root_eq e6Certificate_check
    (IsRoot.smul (IsRoot.basis (5 : Fin Tag.E6.rank)) w₀)
  have hJ : ∀ j ∈ ([1, 2, 3, 4] : List (Fin Tag.E6.rank)), j ∈ d4Set Tag.E6 := by
    intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩
  have hgram : ∀ i : Fin Tag.E6.rank, d4t2outGram π (w₀ • Pi.single i 1) i = true := fun i =>
    List.all_eq_true.2 fun j hj => beq_iff_eq.2 (by rw [← hw₀ j (hJ j hj), iform_smul])
  have hcong : ∀ b : Fin Tag.E6.rank → ℤ, (3 : ℤ) ∣ b 0 + b 5 - 1 → d4t2unCong b = true :=
    fun b hb => beq_iff_eq.2 (Int.emod_eq_zero_of_dvd hb)
  have hvec : w₀ • d4t2outZeta =
      d4t2outVec π (w₀ • Pi.single 0 1) (w₀ • Pi.single 5 1) := by
    rw [d4t2outZeta_eq]
    simp only [smul_add, smul_comm w₀ (_ : ℤ)]
    rw [hw₀ 1 ⟨by decide, by decide⟩, hw₀ 2 ⟨by decide, by decide⟩, hw₀ 3 ⟨by decide, by decide⟩,
      hw₀ 4 ⟨by decide, by decide⟩]
    rfl
  have hpair : d4t2unPair π (w₀ • Pi.single 0 1) (w₀ • Pi.single 5 1) = true := by
    simp only [d4t2unPair, Bool.and_eq_true]
    refine ⟨⟨⟨hgram 5, hcong _ h5⟩, beq_iff_eq.2 ?_⟩, List.all_eq_true.2 fun t _ => ?_⟩
    · rw [iform_smul]
      decide +kernel
    · refine beq_iff_eq.2 (Int.emod_eq_zero_of_dvd ?_)
      have := d4t2out_smul_zeta w₀ t
      rwa [hvec] at this
  have hc := d4t2unCheck_eq
  rw [d4t2unCheck, List.all_eq_true] at hc
  have hc1 := hc π hπ
  rw [List.all_eq_true] at hc1
  have hc2 := hc1 k (List.mem_range.2 hk)
  rw [hkb, hgram 0, hcong _ h0, Bool.and_self, Bool.not_true, Bool.false_or,
    List.all_eq_true] at hc2
  have hc3 := hc2 m (List.mem_range.2 hm)
  rw [hmb, hpair] at hc3
  exact Bool.false_ne_true hc3

end Search

section Cong

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.PartOne.KD4T CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24
open CFSG.RankThree.PartOne.KE (d4Nodes)



private theorem d4t2un_three_dvd {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup .E6 L p₀) (h3q : 3 ∣ S.D.q - 1) {a : Fin Tag.E6.rank → Lˣ}
    (hT : rootDiagUnit .E6 a ∈ S.D.torus) (hap : ∀ i, a i ^ 3 = 1)
    (i : KernelComponent (rootCharHom a)) (v : WeylGroup .E6)
    (hΨ : componentRoots (rootCharHom a) i =
      (fun α => v • α) '' parabolicRoots .E6 (d4Nodes .E6))
    (hall : kernelRoots (rootCharHom a) ⊆ componentRoots (rootCharHom a) i)
    {u w₀ : WeylGroup .E6} (hu : u ∈ parabolicWeylGroup .E6 (d4Set .E6))
    (hθ : ∀ γ, IsRoot .E6 γ → v⁻¹ • S.ρ (v • γ) = (u * w₀) • γ) :
    (3 : ℤ) ∣ (w₀ • (Pi.single 0 1 : Fin Tag.E6.rank → ℤ)) 0 +
        (w₀ • (Pi.single 0 1 : Fin Tag.E6.rank → ℤ)) 5 - 1 ∧
      (3 : ℤ) ∣ (w₀ • (Pi.single 5 1 : Fin Tag.E6.rank → ℤ)) 0 +
        (w₀ • (Pi.single 5 1 : Fin Tag.E6.rank → ℤ)) 5 - 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hker : ∀ γ, IsRoot .E6 γ → rootChar a (v • γ) = 1 →
      γ ∈ parabolicRoots .E6 (d4Nodes .E6) := by
    intro γ hγ h1
    have hmem : v • γ ∈ componentRoots (rootCharHom a) i :=
      hall ⟨(isRoot_smul_iff v).2 hγ, h1⟩
    rw [hΨ] at hmem
    obtain ⟨α, hα, hαe⟩ := hmem
    rwa [(smul_left_cancel_iff v).1 hαe] at hα
  have hJ : ∀ j ∈ d4Set .E6, rootChar a (v • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) = 1 := by
    intro j hj
    have hmem : v • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) ∈ componentRoots (rootCharHom a) i := by
      rw [hΨ]
      exact ⟨_, single_mem_parabolicRoots hj, rfl⟩
    exact hmem.1.2
  have hout : ∀ γ, IsRoot .E6 γ → γ 0 ≠ 0 → rootChar a (v • γ) ≠ 1 := fun γ hγ h0 h1 =>
    h0 ((hker γ hγ h1).2 0 fun h => absurd h.1 (by decide))
  have hout5 : ∀ γ, IsRoot .E6 γ → γ 5 ≠ 0 → rootChar a (v • γ) ≠ 1 := fun γ hγ h0 h1 =>
    h0 ((hker γ hγ h1).2 5 fun h => absurd h.2 (by decide))
  have hcube : ∀ x, rootChar a x ^ 3 = 1 := fun x => by
    rw [rootChar, ← Finset.prod_pow]
    refine Finset.prod_eq_one fun j _ => ?_
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hap j, one_zpow]
  obtain ⟨z, hz⟩ : ∃ z, rootChar a (v • (Pi.single 0 1 : Fin Tag.E6.rank → ℤ)) = z := ⟨_, rfl⟩
  have hz1 : z ≠ 1 := hz ▸ hout _ (IsRoot.basis 0) (by decide)
  have hz5 : rootChar a (v • (Pi.single 5 1 : Fin Tag.E6.rank → ℤ)) ≠ 1 :=
    hout5 _ (IsRoot.basis 5) (by decide)
  have hγ : IsRoot .E6 (Pi.single 0 1 + Pi.single 2 1 + Pi.single 3 1 + Pi.single 4 1 +
      Pi.single 5 1 : Fin Tag.E6.rank → ℤ) := by
    have e : (Pi.single 0 1 + Pi.single 2 1 + Pi.single 3 1 + Pi.single 4 1 + Pi.single 5 1 :
        Fin Tag.E6.rank → ℤ) =
        reflect .E6 0 (reflect .E6 2 (reflect .E6 3 (reflect .E6 4 (Pi.single 5 1)))) := by
      decide +kernel
    rw [e]
    exact .reflect _ (.reflect _ (.reflect _ (.reflect _ (.basis _))))
  have h05 : z * rootChar a (v • (Pi.single 5 1 : Fin Tag.E6.rank → ℤ)) ≠ 1 := by
    have h := hout _ hγ (by decide)
    simp only [smul_add, rootChar_add, hJ 2 ⟨by decide, by decide⟩, hJ 3 ⟨by decide, by decide⟩,
      hJ 4 ⟨by decide, by decide⟩, mul_one, hz] at h
    exact h
  have hq3 : ∀ y : Lˣ, y ^ 3 = 1 → y ≠ 1 → (y : L) ^ 2 + y + 1 = 0 := by
    intro y h3 h1
    have h3' : (y : L) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, h3, Units.val_one]
    have h1' : (y : L) ≠ 1 := fun h => h1 (Units.ext h)
    have : ((y : L) - 1) * ((y : L) ^ 2 + y + 1) = 0 := by linear_combination h3'
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 h1')
  have hz5' : rootChar a (v • (Pi.single 5 1 : Fin Tag.E6.rank → ℤ)) = z := by
    have e0 := hq3 z (hz ▸ hcube _) hz1
    have e5 := hq3 _ (hcube _) hz5
    set y := rootChar a (v • (Pi.single 5 1 : Fin Tag.E6.rank → ℤ))
    have : ((y : L) - z) * ((y : L) + z + 1) = 0 := by linear_combination e5 - e0
    rcases mul_eq_zero.1 this with h | h
    · exact Units.ext (sub_eq_zero.1 h)
    · refine absurd (Units.ext ?_) h05
      rw [Units.val_mul, Units.val_one]
      linear_combination (z : L) * h - e0
  have hcJ : ∀ c : Fin Tag.E6.rank, c ≠ 0 → c ≠ 5 → 1 ≤ c.val ∧ c.val ≤ 4 := by decide
  have hchi : ∀ x, rootChar a (v • x) = z ^ (x 0 + x 5) := by
    intro x
    rw [d4t2out_rootChar_smul a v x, Finset.prod_eq_mul (0 : Fin Tag.E6.rank) 5 (by decide)
      (fun c _ hc => by rw [hJ c (hcJ c hc.1 hc.2), one_zpow])
      (fun h => absurd (Finset.mem_univ _) h) (fun h => absurd (Finset.mem_univ _) h),
      hz, hz5', zpow_add]
  have hz3 : z ^ 3 = 1 := hz ▸ hcube _
  have hzq : z ^ S.D.q = z := by
    obtain ⟨c, hc⟩ := h3q
    have hq0 : 0 < S.D.q := S.hqpow.1.pos
    rw [show S.D.q = 3 * c + 1 by omega, pow_succ, pow_mul, hz3, one_pow, one_mul]
  have key : ∀ t : Fin Tag.E6.rank,
      (Pi.single t 1 : Fin Tag.E6.rank → ℤ) 0 + (Pi.single t 1 : Fin Tag.E6.rank → ℤ) 5 = 1 →
      (3 : ℤ) ∣ (w₀ • (Pi.single t 1 : Fin Tag.E6.rank → ℤ)) 0 +
        (w₀ • (Pi.single t 1 : Fin Tag.E6.rank → ℤ)) 5 - 1 := by
    intro t ht1
    have hfr := S.frob.rootChar_eq a hT _ (IsRoot.smul (IsRoot.basis t) v)
    have hρs : S.ρ (v • (Pi.single t 1 : Fin Tag.E6.rank → ℤ)) =
        v • (u • (w₀ • (Pi.single t 1 : Fin Tag.E6.rank → ℤ))) := by
      have h := hθ _ (IsRoot.basis t)
      rw [mul_smul] at h
      rw [← h, smul_inv_smul]
    rw [hρs, hchi, hchi, smul_apply_of_mem_parabolicWeylGroup hu _
      (fun h => absurd h.1 (by decide) : (0 : Fin Tag.E6.rank) ∉ d4Set .E6),
      smul_apply_of_mem_parabolicWeylGroup hu _
      (fun h => absurd h.2 (by decide) : (5 : Fin Tag.E6.rank) ∉ d4Set .E6), ht1,
      zpow_one, hzq] at hfr
    have h1 : z ^ ((w₀ • (Pi.single t 1 : Fin Tag.E6.rank → ℤ)) 0 +
        (w₀ • (Pi.single t 1 : Fin Tag.E6.rank → ℤ)) 5 - 1) = 1 := by
      rw [zpow_sub_one, hfr, mul_inv_cancel]
    have h2 := orderOf_dvd_iff_zpow_eq_one.2 h1
    rwa [orderOf_eq_prime hz3 hz1, Nat.cast_ofNat] at h2
  exact ⟨key 0 (by decide), key 5 (by decide)⟩

end Cong

section Layer

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.PartOne.KE6 CFSG.RankThree.PartOne.KD4T
  CFSG.RankThree.PartOne.KD4L CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24
open CFSG.RankThree.PartOne.KE (twistedFixedPoints mem_twistedFixedPoints frobenius_canonicalRep
  d4Nodes)

open CFSG.HardMathSupport.Dickson.DefCharOuter.Export
  (exists_mulEquiv_graphFixedRootGroup_frobenius_sq_D4)


private theorem d4t2un_layer_equiv {L : Type} [Field L] [IsAlgClosed L] {ℓ f : ℕ} [Fact ℓ.Prime]
    [CharP L ℓ] (hf : 1 ≤ f) {a b c : Fin Tag.E6.rank}
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (ha : a.val = 1 ∨ a.val = 2 ∨ a.val = 4)
    (hb : b.val = 1 ∨ b.val = 2 ∨ b.val = 4) (hc : c.val = 1 ∨ c.val = 2 ∨ c.val = 4)
    {n : ModGL Tag.E6 L} (hn : n ∈ monomialSubgroup Tag.E6 L)
    {u : WeylGroup Tag.E6} (hu : u ∈ parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6))
    (hact : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      weylQuotientHom Tag.E6 L ⟨n, hn⟩ • α = u • permLattice (List.formPerm [a, b, c]) α) :
    Nonempty (↥(rootSpan Tag.E6 L (parabolicRoots Tag.E6 (d4Nodes Tag.E6)) ⊓
        twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) ≃*
        (TauCeti.CFSGIndex.lie ⟨.trialityD4 ⟨ℓ, f, Fact.out, hf⟩,
          TauCeti.LieTypeIndex.valid_trialityD4 _⟩).Group) ∧
      Subgroup.center ↥(rootSpan Tag.E6 L (parabolicRoots Tag.E6 (d4Nodes Tag.E6)) ⊓
        twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) = ⊥ := by
  obtain ⟨hcyc, hπ, hπ'⟩ := leafCycle_E6 a b c ha hb hc hab hbc hac
  have key : ∀ e, (e = 1 ∨ e = 2) →
      (∀ k : Fin Tag.D4.rank, List.formPerm [a, b, c] (d4Id k) = d4Id (rhoE e k)) →
      Nonempty (↥(rootSpan Tag.E6 L (parabolicRoots Tag.E6 (d4Nodes Tag.E6)) ⊓
        twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) ≃*
        (TauCeti.CFSGIndex.lie ⟨.trialityD4 ⟨ℓ, f, Fact.out, hf⟩,
          TauCeti.LieTypeIndex.valid_trialityD4 _⟩).Group) ∧
      Subgroup.center ↥(rootSpan Tag.E6 L (parabolicRoots Tag.E6 (d4Nodes Tag.E6)) ⊓
        twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) = ⊥ := by
    intro e he hπe
    obtain ⟨K, _, _, σ, hKc, hσ, ⟨eP⟩⟩ := triality_layer_graph_equiv hf (List.formPerm [a, b, c])
      e he hπe (fun i hi => hπ i hi) (fun i hi => hπ' i hi) n hn ⟨u, hu, hact⟩ _ rfl
    have hqc : (⟨ℓ, f, Fact.out, hf⟩ : TauCeti.PrimePower).card = ℓ ^ f :=
      TauCeti.PrimePower.card_def _
    have hKc' : Nat.card K = (⟨ℓ, f, Fact.out, hf⟩ : TauCeti.PrimePower).card ^ 3 := by
      rw [hqc]
      exact hKc
    have hZ : Subgroup.center ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
      center_graphFixedRootGroup_eq_bot σ.surjective
    refine ⟨?_, d4t2out_center_eq_bot eP hZ⟩
    rcases he with rfl | rfl
    · obtain ⟨φ⟩ := catEquiv_trialityD4_of_field ⟨ℓ, f, Fact.out, hf⟩
        (TauCeti.LieTypeIndex.valid_trialityD4 _) K hKc' σ fun c => by rw [hσ, pow_one, hqc]
      exact ⟨eP.trans φ.symm⟩
    · have h₁ : ∀ c, σ.symm c = c ^ (ℓ ^ f) := fun c => by
        apply σ.injective
        rw [RingEquiv.apply_symm_apply, hσ, ← pow_mul]
        haveI : Fintype K := Fintype.ofFinite K
        have hcard : ℓ ^ f * (ℓ ^ f) ^ 2 = Fintype.card K := by
          rw [← Nat.card_eq_fintype_card, hKc]
          ring
        rw [hcard, FiniteField.pow_card]
      obtain ⟨ψ⟩ := exists_mulEquiv_graphFixedRootGroup_frobenius_sq_D4 K hKc σ σ.symm hσ h₁
      obtain ⟨φ⟩ := catEquiv_trialityD4_of_field ⟨ℓ, f, Fact.out, hf⟩
        (TauCeti.LieTypeIndex.valid_trialityD4 _) K hKc' σ.symm fun c => by rw [hqc]; exact h₁ c
      exact ⟨(eP.trans ψ).trans φ.symm⟩
  rcases hcyc with h1 | h2
  · exact key 1 (Or.inl rfl) h1
  · exact key 2 (Or.inr rfl) h2

private theorem d4t2un_rootSpan_model_equiv {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup .E6 L p₀) {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ] (hf : 1 ≤ f)
    (hΦ : S.D.Φ = Units.map (entrywiseHom (iterateFrobenius L ℓ f))) {w : WeylGroup .E6}
    (hn : S.D.n = canonicalRep (coxeterSystem .E6) L w) (v : WeylGroup .E6)
    {u : WeylGroup .E6} (hu : u ∈ parabolicWeylGroup .E6 (d4Nodes .E6)) {a b c : Fin Tag.E6.rank}
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (ha : a.val = 1 ∨ a.val = 2 ∨ a.val = 4)
    (hb : b.val = 1 ∨ b.val = 2 ∨ b.val = 4) (hc : c.val = 1 ∨ c.val = 2 ∨ c.val = 4)
    (hact : ∀ α ∈ parabolicRoots .E6 (d4Nodes .E6),
      (v⁻¹ * w * v) • α = u • permLattice (List.formPerm [a, b, c]) α) :
    Nonempty (↥(rootSpan .E6 L ((fun α => v • α) '' parabolicRoots .E6 (d4Nodes .E6)) ⊓
        S.D.model) ≃*
        (TauCeti.CFSGIndex.lie ⟨.trialityD4 ⟨ℓ, f, Fact.out, hf⟩,
          TauCeti.LieTypeIndex.valid_trialityD4 _⟩).Group) ∧
      Subgroup.center ↥(rootSpan .E6 L ((fun α => v • α) '' parabolicRoots .E6 (d4Nodes .E6)) ⊓
        S.D.model) = ⊥ := by
  set nv := canonicalRep (coxeterSystem Tag.E6) L v with hnv
  set nw := canonicalRep (coxeterSystem Tag.E6) L w with hnw
  have hroots : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6), IsRoot Tag.E6 α := fun α hα => hα.1
  have hmodel : rootSpan Tag.E6 L ((fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6)) ⊓
      S.D.model = rootSpan Tag.E6 L ((fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6)) ⊓
        twistedFixedPoints nw (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) := by
    ext x
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨hx, -, hxF⟩
      refine ⟨hx, ?_⟩
      have hxF' : S.D.n * S.D.Φ x * S.D.n⁻¹ = x := hxF
      rw [hn, hΦ] at hxF'
      exact hxF'
    · rintro ⟨hx, hxF⟩
      refine ⟨hx, rootSpan_le_adjointGroup L _ hx, ?_⟩
      change S.D.n * S.D.Φ x * S.D.n⁻¹ = x
      rw [hn, hΦ]
      exact hxF
  rw [hmodel, rootSpan_inf_twistedFixedPoints_smul _ v nw hroots]
  have hnvM := canonicalRep_mem_monomialSubgroup L v
  have hnwM := canonicalRep_mem_monomialSubgroup L w
  have hn'M : nv⁻¹ * nw * nv ∈ monomialSubgroup Tag.E6 L :=
    mul_mem (mul_mem (inv_mem hnvM) hnwM) hnvM
  have hπ : weylQuotientHom Tag.E6 L ⟨nv⁻¹ * nw * nv, hn'M⟩ = v⁻¹ * w * v := by
    have e : (⟨nv⁻¹ * nw * nv, hn'M⟩ : monomialSubgroup Tag.E6 L) =
        (⟨nv, hnvM⟩ : monomialSubgroup Tag.E6 L)⁻¹ * ⟨nw, hnwM⟩ * ⟨nv, hnvM⟩ := rfl
    rw [e, map_mul, map_mul, map_inv, weylQuotientHom_eq (mapsRootLines_canonicalRep v),
      weylQuotientHom_eq (mapsRootLines_canonicalRep w)]
  obtain ⟨⟨eQ⟩, hZQ⟩ := d4t2un_layer_equiv hf hab hbc hac ha hb hc hn'M hu
    (fun α hα => by rw [hπ]; exact hact α hα)
  have e := (rootSpan Tag.E6 L (parabolicRoots Tag.E6 (d4Nodes Tag.E6)) ⊓
    twistedFixedPoints (nv⁻¹ * nw * nv) (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))).equivMapOfInjective
      (MulAut.conj nv).toMonoidHom (MulAut.conj nv).injective
  exact ⟨⟨e.symm.trans eQ⟩, d4t2out_center_eq_bot e.symm hZQ⟩

theorem d4t2un_rationalComponent_equiv {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup .E6 L p₀) {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ S.D.q)
    (hΦ : S.D.Φ = Units.map (entrywiseHom Fr)) {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ] (hf : 1 ≤ f)
    (hq : S.D.q = ℓ ^ f) (h3q : 3 ∣ ℓ ^ f - 1) {a : Fin Tag.E6.rank → Lˣ}
    (hT : rootDiagUnit .E6 a ∈ S.D.torus) (hap : ∀ i, a i ^ 3 = 1)
    (i : KernelComponent (rootCharHom a)) (v : WeylGroup .E6)
    (hΨ : componentRoots (rootCharHom a) i =
      (fun α => v • α) '' parabolicRoots .E6 (d4Nodes .E6))
    (hall : kernelRoots (rootCharHom a) ⊆ componentRoots (rootCharHom a) i)
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i)
    (hnin : ¬ twistInner (componentRoots (rootCharHom a) i)
      (S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))) :
    Nonempty (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ≃*
        (TauCeti.CFSGIndex.lie ⟨.trialityD4 ⟨ℓ, f, Fact.out, hf⟩,
          TauCeti.LieTypeIndex.valid_trialityD4 _⟩).Group) ∧
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) = ⊥ := by
  classical
  obtain ⟨w, hn⟩ := S.D.n_weyl
  have hρw : ∀ γ, IsRoot Tag.E6 γ → S.ρ γ = w • γ := fun γ hγ =>
    S.rho_eq_smul_of_frob hFr hΦ hn hγ
  have hw : ∀ γ ∈ componentRoots (rootCharHom a) i, w • γ ∈ componentRoots (rootCharHom a) i :=
    fun γ hγ => by
      rw [← hρw γ hγ.1.1]
      exact hρ γ hγ
  have hmaps : MapsJ Tag.E6 (d4Set Tag.E6) (v⁻¹ * w * v) := by
    intro α hα
    obtain ⟨β, hβ, hβe⟩ := (hΨ ▸ hw (v • α) (hΨ ▸ ⟨α, hα, rfl⟩) :
      w • v • α ∈ (fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6))
    rw [mul_smul, mul_smul, ← hβe, inv_smul_smul]
    exact hβ
  obtain ⟨u, hu, w₀, hw₀, π, hπ, hw₀π⟩ := exists_d4_action d4Base_E6 hmaps
  have hlin0 : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6), w₀ • α = permLattice π α :=
    fun α hα => by
      have := smul_eq_of_simple (w := w₀) (u := 1) (π := π) (J := d4Set Tag.E6)
        (fun j hj => by rw [one_smul]; exact hw₀π j hj) hα.2
      rwa [one_smul] at this
  have hact : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      (v⁻¹ * w * v) • α = u • permLattice π α := fun α hα => by
    rw [hw₀, mul_smul, hlin0 α hα]
  have hπ1 : π ≠ 1 := by
    rintro rfl
    apply hnin
    refine ⟨v * u * v⁻¹, hΨ ▸ conj_mem_closure_rootReflection v hu, ?_⟩
    rintro γ hγ
    obtain ⟨α, hα, rfl⟩ :=
      (hΨ ▸ hγ : γ ∈ (fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6))
    rw [hρw _ hγ.1.1]
    calc w • v • α = v • ((v⁻¹ * w * v) • α) := by
          rw [mul_smul, mul_smul, smul_inv_smul]
      _ = v • (u • α) := by
          rw [hact α hα]
          rfl
      _ = (v * u * v⁻¹) • v • α := by
          rw [mul_smul, mul_smul, inv_smul_smul]
  have hF := d4t2un_three_dvd S (by rw [hq]; exact h3q) hT hap i v hΨ hall hu fun γ hγ => by
    rw [hρw _ ((isRoot_smul_iff v).2 hγ), ← hw₀, mul_smul, mul_smul]
  have hcyc : π = List.formPerm [e6Idx 1, e6Idx 2, e6Idx 4] ∨
      π = List.formPerm [e6Idx 1, e6Idx 4, e6Idx 2] := by
    rcases hπ with h | h | h | h | h | h
    · exact absurd h hπ1
    · exact (d4t2un_no_weyl (by rw [h]; simp [d4t2unPerms]) hw₀π hF.1 hF.2).elim
    · exact (d4t2un_no_weyl (by rw [h]; simp [d4t2unPerms]) hw₀π hF.1 hF.2).elim
    · exact (d4t2un_no_weyl (by rw [h]; simp [d4t2unPerms]) hw₀π hF.1 hF.2).elim
    · exact Or.inl h
    · exact Or.inr h
  have hFr' : Fr = iterateFrobenius L ℓ f := by
    ext x
    rw [hFr, hq, iterateFrobenius_def]
  have hΦ' : S.D.Φ = Units.map (entrywiseHom (iterateFrobenius L ℓ f)) := by rw [hΦ, hFr']
  have h12 : e6Idx (τ := Tag.E6) 1 ≠ e6Idx 2 := e6Idx_ne (by decide)
  have h14 : e6Idx (τ := Tag.E6) 1 ≠ e6Idx 4 := e6Idx_ne (by decide)
  have h24 : e6Idx (τ := Tag.E6) 2 ≠ e6Idx 4 := e6Idx_ne (by decide)
  have hv1 : (e6Idx (τ := Tag.E6) 1).val = 1 ∨ (e6Idx (τ := Tag.E6) 1).val = 2 ∨
      (e6Idx (τ := Tag.E6) 1).val = 4 := Or.inl rfl
  have hv2 : (e6Idx (τ := Tag.E6) 2).val = 1 ∨ (e6Idx (τ := Tag.E6) 2).val = 2 ∨
      (e6Idx (τ := Tag.E6) 2).val = 4 := Or.inr (Or.inl rfl)
  have hv4 : (e6Idx (τ := Tag.E6) 4).val = 1 ∨ (e6Idx (τ := Tag.E6) 4).val = 2 ∨
      (e6Idx (τ := Tag.E6) 4).val = 4 := Or.inr (Or.inr rfl)
  have hs1 : (e6Idx (τ := Tag.E6) 1).val ∈ ({1, 2, 4} : Set ℕ) := Or.inl rfl
  have hs2 : (e6Idx (τ := Tag.E6) 2).val ∈ ({1, 2, 4} : Set ℕ) := Or.inr (Or.inl rfl)
  have hs4 : (e6Idx (τ := Tag.E6) 4).val ∈ ({1, 2, 4} : Set ℕ) := Or.inr (Or.inr rfl)
  have hlayer : CFSG.IsQuasisimple
        ↥(rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) ⊓ S.D.model) ∧
      Nonempty (↥(rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) ⊓ S.D.model) ≃*
        (TauCeti.CFSGIndex.lie ⟨.trialityD4 ⟨ℓ, f, Fact.out, hf⟩,
          TauCeti.LieTypeIndex.valid_trialityD4 _⟩).Group) ∧
      Subgroup.center ↥(rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) ⊓ S.D.model) =
        ⊥ := by
    rw [hΨ]
    rcases hcyc with rfl | rfl
    · exact ⟨(rootSpan_inf_model_quasisimple_d4 d4TrialityLayer_E6 S hFr hΦ hn v hu h12 h24 h14
        hs1 hs2 hs4 hact).2,
        d4t2un_rootSpan_model_equiv S hf hΦ' hn v hu h12 h24 h14 hv1 hv2 hv4 hact⟩
    · exact ⟨(rootSpan_inf_model_quasisimple_d4 d4TrialityLayer_E6 S hFr hΦ hn v hu h14 h24.symm
        h12 hs1 hs4 hs2 hact).2,
        d4t2un_rootSpan_model_equiv S hf hΦ' hn v hu h14 h24.symm h12 hv1 hv4 hv2 hact⟩
  rw [rationalComponent_eq_of_layer S i hρ hlayer.1]
  exact hlayer.2

end Layer

section Catalog

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.Yardstones.Md0ec50421ce4 CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24


theorem e6D4T2_class {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}
    (S : LangSetup Tag.E6 L p₀) {a : Fin Tag.E6.rank → Lˣ}
    (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus) (hap : ∀ j, a j ^ 3 = 1)
    (h24 : (kernelRoots (rootCharHom a)).ncard = 24) (i : KernelComponent (rootCharHom a)) :
    ∃ v : WeylGroup Tag.E6, componentRoots (rootCharHom a) i =
        (fun α => v • α) '' parabolicRoots Tag.E6 (CFSG.RankThree.PartOne.KE.d4Nodes Tag.E6) ∧
      kernelRoots (rootCharHom a) ⊆ componentRoots (rootCharHom a) i ∧
      ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i := by
  have h3 : ((3 : ℕ) : L) ≠ 0 := fun h =>
    absurd ((CharP.cast_eq_zero_iff L 2 3).1 h) (by norm_num)
  obtain ⟨hr, hc⟩ := d4t2_class_of_card h3 hap h24 i
  have hTp : rootDiagUnit Tag.E6 a ^ 3 = 1 := by
    have h1 : rootDiagUnit Tag.E6 (a ^ 3) = rootDiagUnit Tag.E6 a ^ 3 :=
      (rootDiagUnitHom Tag.E6 L).map_pow a 3
    have h2 : a ^ 3 = 1 := funext fun j => by rw [Pi.pow_apply, hap j, Pi.one_apply]
    rw [← h1, h2, CFSG.LieType.Chevalley.rootDiagUnit_one]
  obtain ⟨v, hv, hρ⟩ := S.d4_pinnedT_of_prime Nat.prime_three h3 facts_E6 kacCount_E6_four
    (by decide) (by decide)
    (fun y hy => far_d4_E6 y fun z hz => by
      have h := hy z hz
      rwa [KacData.Adj, extRoot_eq_extRootOf] at h)
    ⟨none, by decide⟩ (lt_of_eq_of_lt kacCount_far_E6 (by decide)) hT hTp i hr hc
  have hfin : (kernelRoots (rootCharHom a)).Finite :=
    (finite_setOf_isRoot _).subset fun γ hγ => hγ.1
  have hle : componentRoots (rootCharHom a) i ⊆ kernelRoots (rootCharHom a) := fun γ hγ => hγ.1
  exact ⟨v, hv, (Set.eq_of_subset_of_ncard_le hle (h24.trans hc.symm).le hfin).ge, hρ⟩

private theorem e6D4T2_catalogIs_trialityD4 {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}
    (S : LangSetup Tag.E6 L p₀) (hS : E6ShapeSetup S) {a : Fin Tag.E6.rank → Lˣ}
    (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus) (hap : ∀ j, a j ^ 3 = 1)
    (h24 : (kernelRoots (rootCharHom a)).ncard = 24) (i : KernelComponent (rootCharHom a))
    (hnin : ¬ twistInner (componentRoots (rootCharHom a) i) S.ρ) :
    catalogIs (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))
      (onLie fun | .trialityD4 _ => True | _ => False) := by
  classical
  obtain ⟨v, hv, hsub, hρ⟩ := e6D4T2_class S hT hap h24 i
  obtain ⟨ℓ, f, hℓ, hchar, hf, hq⟩ := S.exists_char_pow
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : CharP L ℓ := hchar
  have hcat : Nonempty (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ≃*
        (TauCeti.CFSGIndex.lie ⟨.trialityD4 ⟨ℓ, f, Fact.out, hf⟩,
          TauCeti.LieTypeIndex.valid_trialityD4 _⟩).Group) ∧
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) = ⊥ := by
    obtain ⟨Fr, hFr, ⟨hΦ, h3q⟩ | ⟨hΦ, h3q⟩⟩ := hS
    · exact d4t2un_rationalComponent_equiv S hFr hΦ hf hq (hq ▸ h3q) hT hap i v hv hsub hρ hnin
    · exact d4t2out_rationalComponent_equiv S ⟨TwistTag.E6, rfl, Fr, hFr, fun g => by rw [hΦ]; rfl⟩
        hf hq (hq ▸ h3q) hT hap i v hv hsub hρ hnin
  obtain ⟨⟨e⟩, hZ⟩ := hcat
  exact ⟨.lie ⟨.trialityD4 ⟨ℓ, f, Fact.out, hf⟩, TauCeti.LieTypeIndex.valid_trialityD4 _⟩, trivial,
    ⟨(QuotientGroup.quotientMulEquivOfEq hZ).trans (QuotientGroup.quotientBot.trans e)⟩⟩

end Catalog

section Defs

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)

open CFSG.ComponentClassification.PerfectAutomorphisms (centerQuotientHom)

open CFSG.GroupActions (subgroupStabAut subgroupStabRestrict)



@[expose] def E6D4T2InnerCosetAction : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] (p₀ : ℕ) (S : LangSetup Tag.E6 L p₀),
    E6ShapeSetup S → ∀ a : Fin Tag.E6.rank → Lˣ, rootDiagUnit Tag.E6 a ∈ S.D.torus → (∀ j, a j ^ 3 = 1) →
    (kernelRoots (rootCharHom a)).ncard = 24 → ∀ i : KernelComponent (rootCharHom a),
    CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) →
    (∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i) →
    twistInner (componentRoots (rootCharHom a) i) S.ρ →
    ∀ y ∈ toralCentralizer Tag.E6 L a, S.D.step y = y →
    ∀ hyStab : MulAut.conj y ∈ subgroupStabAut (rationalComponent S.ρ S.Γ (rootCharHom a) i),
      centerQuotientHom ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)
          (subgroupStabRestrict (rationalComponent S.ρ S.Γ (rootCharHom a) i) ⟨MulAut.conj y, hyStab⟩) ∈
        innAutDerived (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
          Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))

end Defs

section Main


theorem e6D4T2CosetAction_of_inner (h : E6D4T2InnerCosetAction) : E6D4T2CosetAction := by
  intro L _ _ _ p₀ S hS a hT hap h24 i hQS y hyC hyF hyStab _
  obtain ⟨-, -, -, hρ⟩ := e6D4T2_class S hT hap h24 i
  by_cases hin : CFSG.HardMathSupport.Timmesfeld.LangTorus.twistInner
      (CFSG.LieType.Chevalley.componentRoots (CFSG.LieType.AlgebraicGroups.rootCharHom a) i) S.ρ
  · exact Or.inr (h L p₀ S hS a hT hap h24 i hQS hρ hin y hyC hyF hyStab)
  · exact Or.inl (e6D4T2_catalogIs_trialityD4 S hS hT hap h24 i hin)

end Main

end CFSG.LocalAnalysis.GLTheoremA.T158

end
