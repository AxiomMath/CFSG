module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.Copies
public import CFSG.HardMathSupport.Meierfrankenfeld.E7Curtis.FixedTranslate
public import CFSG.LieType.Chevalley.LangStronglyOrthogonalCommute

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc

open CFSG.Quasithin.SmithCurtis CFSG.Quasithin.SmithCurtis.Chev CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CoxeterSystem CFSG.QuasithinUnique.Setup.SL2Modules
open scoped MatrixGroups

section Abstract

variable {k : Type} [Field k] [CharP k 2] {V : Type} [AddCommGroup V] [Module k V]

private theorem orbitSpan_isSimple_of_isPGroup {H : Type*} [Group H] {P : Subgroup H} [Finite P]
    (hP : IsPGroup 2 P) (σ : Representation k H V) {v : V} (Fix : Submodule k V)
    (hvF : v ∈ Fix) (hFst : ∀ h : H, ∀ w ∈ Fix, σ h w ∈ Fix)
    (hfix : ∀ f ∈ Fix, f ∈ fixSub σ P → ∃ c : k, f = c • v)
    (W' : Submodule k V) (hW' : W' ≤ orbitSpan σ v)
    (hst : ∀ h : H, ∀ w ∈ W', σ h w ∈ W') :
    W' = ⊥ ∨ W' = orbitSpan σ v := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hbot : W' = ⊥
  · exact Or.inl hbot
  right
  have hN : orbitSpan σ v ≤ Fix := by
    rw [orbitSpan, Submodule.span_le]
    rintro _ ⟨h, rfl⟩
    exact hFst h v hvF
  obtain ⟨f, hfW, hf0, hffix⟩ := exists_fixed_mem σ hP hst hbot
  obtain ⟨c, hc⟩ := hfix f (hN (hW' hfW)) hffix
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hf0 (by rw [hc, zero_smul])
  have hvW : v ∈ W' := by
    have : c⁻¹ • f ∈ W' := W'.smul_mem _ hfW
    rwa [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul] at this
  refine le_antisymm hW' ?_
  rw [orbitSpan, Submodule.span_le]
  rintro _ ⟨h, rfl⟩
  exact hst h v hvW

theorem finrank_iSup_orbitSpan_of_isPGroup [Module.Finite k V] {H : Type*} [Group H]
    (σ : Representation k H V) (P : Subgroup H) [Finite P] (hP : IsPGroup 2 P)
    {ι : Type*} [DecidableEq ι] (v : ι → V) (Fix : ι → Submodule k V)
    (hvF : ∀ i, v i ∈ Fix i) (hFst : ∀ i, ∀ h : H, ∀ w ∈ Fix i, σ h w ∈ Fix i)
    (hfix : ∀ i, ∀ f ∈ Fix i, f ∈ fixSub σ P → ∃ c : k, f = c • v i)
    (hvu : ∀ i, v i ∈ fixSub σ P) (s : Finset ι)
    (hli : LinearIndepOn k v (↑s : Set ι)) :
    Module.finrank k (⨆ i ∈ s, orbitSpan σ (v i) : Submodule k V) =
        ∑ i ∈ s, Module.finrank k (orbitSpan σ (v i)) ∧
      (∀ f ∈ (⨆ i ∈ s, orbitSpan σ (v i) : Submodule k V),
        f ∈ fixSub σ P → f ∈ Submodule.span k (v '' (↑s : Set ι))) ∧
      s.SupIndep (fun i => orbitSpan σ (v i)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨by simp, fun f hf _ => ?_, Finset.supIndep_empty _⟩
    simp at hf
    simp [hf]
  | insert a s has ih =>
    have hli' : LinearIndepOn k v (↑s : Set ι) := hli.mono (by simp)
    have hins : LinearIndepOn k v (insert a (↑s : Set ι)) := by simpa using hli
    obtain ⟨hli1, hli2⟩ := (linearIndepOn_insert (by simpa using has)).1 hins
    obtain ⟨ihd, ihf, ihs⟩ := ih hli'
    set T : Submodule k V := ⨆ i ∈ s, orbitSpan σ (v i) with hT
    set Na : Submodule k V := orbitSpan σ (v a) with hNa
    have hTst : ∀ h : H, ∀ w ∈ T, σ h w ∈ T := by
      intro h w hw
      have : T ≤ (T.comap (σ h)) := by
        rw [hT]
        refine iSup₂_le fun i hi => ?_
        rw [orbitSpan, Submodule.span_le]
        rintro _ ⟨h', rfl⟩
        show σ h (σ h' (v i)) ∈ T
        rw [act_mul]
        exact Submodule.mem_iSup_of_mem i (Submodule.mem_iSup_of_mem hi
          (Submodule.subset_span ⟨h * h', rfl⟩))
      exact this hw
    have hv_notin : v a ∉ T := by
      intro hvT
      exact hli2 (ihf _ hvT (hvu a))
    have hinf : T ⊓ Na = ⊥ := by
      rcases orbitSpan_isSimple_of_isPGroup hP σ (Fix a) (hvF a) (hFst a) (hfix a)
        (T ⊓ Na) inf_le_right
        (fun h w hw => ⟨hTst h w hw.1, orbitSpan_stable σ (v a) h hw.2⟩) with h | h
      · exact h
      · exfalso
        apply hv_notin
        have : v a ∈ T ⊓ Na := by rw [h]; exact mem_orbitSpan_self σ _
        exact this.1
    have hsup : (⨆ i ∈ insert a s, orbitSpan σ (v i) : Submodule k V) = Na ⊔ T := by
      rw [Finset.iSup_insert]
    have hsup' : (⨆ i ∈ insert a s, orbitSpan σ (v i) : Submodule k V) = T ⊔ Na := by
      rw [hsup, sup_comm]
    refine ⟨?_, ?_, ?_⟩
    · rw [hsup', Finset.sum_insert has]
      have h := Submodule.finrank_sup_add_finrank_inf_eq T Na
      rw [hinf, finrank_bot, add_zero] at h
      change Module.finrank k ↥(T ⊔ Na) = Module.finrank k ↥Na +
        ∑ i ∈ s, Module.finrank k (orbitSpan σ (v i))
      rw [← ihd]
      omega
    · intro f hf hfu
      rw [hsup', Submodule.mem_sup] at hf
      obtain ⟨x, hx, y, hy, rfl⟩ := hf
      have hx0 : x ∈ fixSub σ P := by
        intro h hh
        have hsum : (σ h x - x) + (σ h y - y) = 0 := by
          have := hfu h hh
          rw [map_add] at this
          calc (σ h x - x) + (σ h y - y)
              = (σ h x + σ h y) - (x + y) := by abel
            _ = 0 := sub_eq_zero.2 this
        have h1 : σ h x - x ∈ T := T.sub_mem (hTst h x hx) hx
        have h2 : σ h x - x ∈ Na := by
          rw [eq_neg_of_add_eq_zero_left hsum]
          exact Na.neg_mem (Na.sub_mem (orbitSpan_stable σ (v a) h hy) hy)
        have : σ h x - x ∈ T ⊓ Na := ⟨h1, h2⟩
        rw [hinf, Submodule.mem_bot, sub_eq_zero] at this
        exact this
      have hy0 : y ∈ fixSub σ P := by
        intro h hh
        have := hfu h hh
        rw [map_add, hx0 h hh] at this
        exact add_left_cancel this
      have hNaFix : Na ≤ Fix a := by
        rw [hNa, orbitSpan, Submodule.span_le]
        rintro _ ⟨h, rfl⟩
        exact hFst a h _ (hvF a)
      obtain ⟨c, hc⟩ := hfix a y (hNaFix hy) hy0
      refine Submodule.add_mem _ ?_ ?_
      · exact Submodule.span_mono (Set.image_mono (Finset.coe_subset.2 (Finset.subset_insert a s)))
          (ihf x hx hx0)
      · rw [hc]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, by simp, rfl⟩)
    · refine ihs.insert ?_
      rw [Finset.sup_eq_iSup]
      exact disjoint_comm.1 (disjoint_iff.2 hinf)

end Abstract

section Levi

variable {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2]
  {hw : ∃ w₁ : WeylGroup τ, ∀ α : Fin τ.rank → ℤ, w₁ • α = -α}
  {k : Type} [Field k] [Algebra K k] [CharP k 2] {V : Type} [AddCommGroup V] [Module k V]

theorem nWC_conj_rankOne (hw : ∃ w₁ : WeylGroup τ, ∀ α : Fin τ.rank → ℤ, w₁ • α = -α)
    (w : WeylGroup τ) {r s : Fin τ.rank}
    (hws : w • (Pi.single r 1 : Fin τ.rank → ℤ) = Pi.single s 1) (g : SL(2, K)) :
    nWC τ K w * rankOne τ K r g = rankOne τ K s g * nWC τ K w := by
  let S : Subgroup (SL(2, K)) :=
    { carrier := {x | nWC τ K w * rankOne τ K r x = rankOne τ K s x * nWC τ K w}
      mul_mem' := by
        intro a b ha hb
        show nWC τ K w * rankOne τ K r (a * b) =
          rankOne τ K s (a * b) * nWC τ K w
        rw [map_mul, map_mul]
        calc nWC τ K w * (rankOne τ K r a * rankOne τ K r b)
            = (nWC τ K w * rankOne τ K r a) * rankOne τ K r b := by rw [mul_assoc]
          _ = (rankOne τ K s a * nWC τ K w) * rankOne τ K r b := by rw [ha]
          _ = rankOne τ K s a * (nWC τ K w * rankOne τ K r b) := by rw [mul_assoc]
          _ = rankOne τ K s a * (rankOne τ K s b * nWC τ K w) := by rw [hb]
          _ = (rankOne τ K s a * rankOne τ K s b) * nWC τ K w := by rw [mul_assoc]
      one_mem' := by
        show nWC τ K w * rankOne τ K r 1 = rankOne τ K s 1 * nWC τ K w
        rw [map_one, map_one, mul_one, one_mul]
      inv_mem' := by
        intro a ha
        have ha' : nWC τ K w * rankOne τ K r a * (nWC τ K w)⁻¹ = rankOne τ K s a := by
          rw [mul_inv_eq_iff_eq_mul]
          exact ha
        show nWC τ K w * rankOne τ K r a⁻¹ = rankOne τ K s a⁻¹ * nWC τ K w
        have hinv : nWC τ K w * rankOne τ K r a⁻¹ * (nWC τ K w)⁻¹ =
            rankOne τ K s a⁻¹ := by
          rw [map_inv, map_inv, ← ha']
          group
        rw [mul_inv_eq_iff_eq_mul] at hinv
        exact hinv }
  have hcl := CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower (K := K)
  have hle : Subgroup.closure (Set.range (CFSG.LocalAnalysis.ComponentInitial.sl2Upper K) ∪
      Set.range (CFSG.LocalAnalysis.ComponentInitial.sl2Lower K)) ≤ S := by
    rw [Subgroup.closure_le]
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · have e : CFSG.LocalAnalysis.ComponentInitial.sl2Upper K c = uElt c := rfl
      rw [e]
      show nWC τ K w * rankOne τ K r (uElt c) = rankOne τ K s (uElt c) * nWC τ K w
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, rankOne_u, rankOne_u]
      change ((nWC τ K w : adjointGroup τ K) : ModGL τ K) * xUnit τ K r c =
        xUnit τ K s c * ((nWC τ K w : adjointGroup τ K) : ModGL τ K)
      rw [← pinnedX_single, ← pinnedX_single]
      have h := (nWC_conj_pinnedX hw w (isRoot_single τ r) c).2
      rw [hws] at h
      rw [mul_inv_eq_iff_eq_mul] at h
      exact h
    · have e : CFSG.LocalAnalysis.ComponentInitial.sl2Lower K c = lElt c := rfl
      rw [e]
      show nWC τ K w * rankOne τ K r (lElt c) = rankOne τ K s (lElt c) * nWC τ K w
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, rankOne_l, rankOne_l]
      change ((nWC τ K w : adjointGroup τ K) : ModGL τ K) * yUnit τ K r c =
        yUnit τ K s c * ((nWC τ K w : adjointGroup τ K) : ModGL τ K)
      rw [← pinnedX_neg_single, ← pinnedX_neg_single]
      have hws' : w • (-(Pi.single r 1) : Fin τ.rank → ℤ) = -Pi.single s 1 := by
        rw [smul_neg, hws]
      have h := (nWC_conj_pinnedX hw w (isRoot_neg_single τ r) c).2
      rw [hws'] at h
      rw [mul_inv_eq_iff_eq_mul] at h
      exact h
  have : g ∈ S := by
    have hg : g ∈ (⊤ : Subgroup (SL(2, K))) := Subgroup.mem_top g
    rw [← hcl] at hg
    exact hle hg
  exact this

private theorem range_rankOne (s : Fin τ.rank) :
    (rankOne τ K s).range =
      Subgroup.closure (Set.range (xC τ K s) ∪ Set.range (yC τ K s)) := by
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    have hg : g ∈ Subgroup.closure
        (Set.range (CFSG.LocalAnalysis.ComponentInitial.sl2Upper K) ∪
          Set.range (CFSG.LocalAnalysis.ComponentInitial.sl2Lower K)) := by
      rw [CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower]
      exact Subgroup.mem_top g
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with ⟨c, rfl⟩ | ⟨c, rfl⟩
      · have e : CFSG.LocalAnalysis.ComponentInitial.sl2Upper K c = uElt c := rfl
        rw [e, rankOne_u]
        exact Subgroup.subset_closure (Or.inl ⟨c, rfl⟩)
      · have e : CFSG.LocalAnalysis.ComponentInitial.sl2Lower K c = lElt c := rfl
        rw [e, rankOne_l]
        exact Subgroup.subset_closure (Or.inr ⟨c, rfl⟩)
    | one => rw [map_one]; exact Subgroup.one_mem _
    | mul x y _ _ hx hy => rw [map_mul]; exact Subgroup.mul_mem _ hx hy
    | inv x _ hx => rw [map_inv]; exact Subgroup.inv_mem _ hx
  · rw [Subgroup.closure_le]
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact ⟨uElt c, rankOne_u s c⟩
    · exact ⟨lElt c, rankOne_l s c⟩

theorem rankOne_commute_of_orthogonal {r r' : Fin τ.rank}
    (h0 : CFSG.LieType.Steinberg.Adjoint.iform (τ := τ) (Pi.single r 1) (Pi.single r' 1) = 0)
    (hp : ¬ IsRoot τ ((Pi.single r 1 : Fin τ.rank → ℤ) + Pi.single r' 1))
    (hm : ¬ IsRoot τ ((Pi.single r 1 : Fin τ.rank → ℤ) - Pi.single r' 1)) (a b : SL(2, K)) :
    rankOne τ K r a * rankOne τ K r' b = rankOne τ K r' b * rankOne τ K r a := by
  have hgen : ∀ x ∈ (Set.range (xC τ K r) ∪ Set.range (yC τ K r)),
      ∀ y ∈ (Set.range (xC τ K r') ∪ Set.range (yC τ K r')), x * y = y * x := by
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩) _ (⟨d, rfl⟩ | ⟨d, rfl⟩)
    · apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      change xUnit τ K r c * xUnit τ K r' d = xUnit τ K r' d * xUnit τ K r c
      rw [← pinnedX_single, ← pinnedX_single]
      exact CFSG.LieType.Chevalley.pinnedX_commute_of_iform_eq_zero K (isRoot_single τ r)
        (isRoot_single τ r') h0 hp c d
    · apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      change xUnit τ K r c * yUnit τ K r' d = yUnit τ K r' d * xUnit τ K r c
      rw [← pinnedX_single, ← pinnedX_neg_single]
      exact CFSG.LieType.Chevalley.pinnedX_commute_of_iform_eq_zero K (isRoot_single τ r)
        (isRoot_neg_single τ r') (by rw [iform_neg_right, h0, neg_zero])
        (by simpa [sub_eq_add_neg] using hm) c d
    · apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      change yUnit τ K r c * xUnit τ K r' d = xUnit τ K r' d * yUnit τ K r c
      rw [← pinnedX_neg_single, ← pinnedX_single]
      exact CFSG.LieType.Chevalley.pinnedX_commute_of_iform_eq_zero K (isRoot_neg_single τ r)
        (isRoot_single τ r') (by rw [iform_neg_left, h0, neg_zero])
        (by intro h; exact hm (by simpa [sub_eq_add_neg, add_comm] using IsRoot.neg h)) c d
    · apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      change yUnit τ K r c * yUnit τ K r' d = yUnit τ K r' d * yUnit τ K r c
      rw [← pinnedX_neg_single, ← pinnedX_neg_single]
      exact CFSG.LieType.Chevalley.pinnedX_commute_of_iform_eq_zero K (isRoot_neg_single τ r)
        (isRoot_neg_single τ r') (by rw [iform_neg_left, iform_neg_right, h0, neg_zero, neg_zero])
        (by intro h; exact hp (by simpa [add_comm] using IsRoot.neg h)) c d
  have hcomm := CFSG.LieType.Chevalley.closure_commute
    (G := adjointGroup τ K) (S := Set.range (xC τ K r) ∪ Set.range (yC τ K r))
    (T := Set.range (xC τ K r') ∪ Set.range (yC τ K r')) hgen
  rw [← range_rankOne r, ← range_rankOne r'] at hcomm
  exact hcomm _ ⟨a, rfl⟩ _ ⟨b, rfl⟩

theorem linearIndependent_translates_of_isChevType_mem {ρ : Representation k (adjointGroup τ K) V}
    (hρ : IsSimpleRep ρ) {y : V} {χ : adjointGroup τ K → k} {J : Finset (Fin τ.rank)}
    (ht : IsChevType τ K 2 hw ρ y χ J) {v₀ : Fin τ.rank → ℤ}
    (hv : ∀ j ∈ J, reflect τ j v₀ = v₀) {m : ℕ} (w : Fin m → WeylGroup τ)
    (hinj : ∀ i j, i ≠ j → w i • v₀ ≠ w j • v₀) :
    LinearIndependent k (fun i => ρ (nWC τ K (w i)) y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨μ, hμ⟩ := ht.exists_mu hρ
  refine linearIndependent_translates hρ hμ w fun i j hij ω hω hωe => ?_
  have hmove : (coxeterSystem τ).wordProd ω • v₀ ≠ v₀ := by
    rw [hωe]
    intro h
    exact hinj i j hij (by
      have := congrArg (fun z => w i • z) h
      simpa [mul_smul] using this.symm)
  obtain ⟨s, hsω, hsJ⟩ :=
    CFSG.HardMathSupport.Meierfrankenfeld.E7Curtis.exists_letter_notMem_of_smul_ne
      (J := J) hv (l := ω) hmove
  exact ⟨s, hsω, mu_eq_dScalar_of_notMem ht hμ hsJ⟩

private theorem isPGroup_prod_subgroup {p : ℕ} {G N : Type*} [Group G] [Group N]
    (P : Subgroup G) (Q : Subgroup N) (hP : IsPGroup p P) (hQ : IsPGroup p Q) :
    IsPGroup p (P.prod Q) := by
  intro x
  obtain ⟨m, hm⟩ := hP ⟨x.1.1, (Subgroup.mem_prod.mp x.2).1⟩
  obtain ⟨n, hn⟩ := hQ ⟨x.1.2, (Subgroup.mem_prod.mp x.2).2⟩
  refine ⟨max m n, ?_⟩
  apply Subtype.ext
  refine Prod.ext ?_ ?_
  · have hm' : x.1.1 ^ p ^ m = 1 := by
      simpa using congrArg Subtype.val hm
    have hpow : x.1.1 ^ p ^ max m n = 1 := by
      rw [show p ^ max m n = p ^ m * p ^ (max m n - m) by
        rw [← pow_add, Nat.add_sub_cancel' (le_max_left m n)]]
      rw [pow_mul, hm', one_pow]
    simpa using hpow
  · have hn' : x.1.2 ^ p ^ n = 1 := by
      simpa using congrArg Subtype.val hn
    have hpow : x.1.2 ^ p ^ max m n = 1 := by
      rw [show p ^ max m n = p ^ n * p ^ (max m n - n) by
        rw [← pow_add, Nat.add_sub_cancel' (le_max_right m n)]]
      rw [pow_mul, hn', one_pow]
    simpa using hpow

private theorem inv_mul_of_mul_eq {G : Type*} [Group G] {n x y : G} (h : n * x = y * n) :
    n⁻¹ * y = x * n⁻¹ := by
  have hy : y = n * x * n⁻¹ := by
    calc y = y * n * n⁻¹ := by group
      _ = n * x * n⁻¹ := by rw [← h]
  rw [hy]; group

private theorem nWC_mul_prod (hw : ∃ w₁ : WeylGroup τ, ∀ α : Fin τ.rank → ℤ, w₁ • α = -α)
    {r r' : Fin τ.rank} {u : WeylGroup τ}
    (hu : (u • (Pi.single r 1 : Fin τ.rank → ℤ) = Pi.single r 1 ∧
        u • (Pi.single r' 1 : Fin τ.rank → ℤ) = Pi.single r' 1) ∨
      (u • (Pi.single r 1 : Fin τ.rank → ℤ) = Pi.single r' 1 ∧
        u • (Pi.single r' 1 : Fin τ.rank → ℤ) = Pi.single r 1))
    (hcomm : ∀ a b : SL(2, K),
      rankOne τ K r a * rankOne τ K r' b = rankOne τ K r' b * rankOne τ K r a)
    (a b : SL(2, K)) :
    (∃ c d, nWC τ K u * (rankOne τ K r a * rankOne τ K r' b) =
        (rankOne τ K r c * rankOne τ K r' d) * nWC τ K u) ∧
      (∃ c d, (nWC τ K u)⁻¹ * (rankOne τ K r a * rankOne τ K r' b) =
        (rankOne τ K r c * rankOne τ K r' d) * (nWC τ K u)⁻¹) := by
  rcases hu with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hf : nWC τ K u * (rankOne τ K r a * rankOne τ K r' b) =
        (rankOne τ K r a * rankOne τ K r' b) * nWC τ K u := by
      calc nWC τ K u * (rankOne τ K r a * rankOne τ K r' b)
          = (nWC τ K u * rankOne τ K r a) * rankOne τ K r' b := by rw [mul_assoc]
        _ = (rankOne τ K r a * nWC τ K u) * rankOne τ K r' b := by
            rw [nWC_conj_rankOne (hw := hw) u h1 a]
        _ = rankOne τ K r a * (nWC τ K u * rankOne τ K r' b) := by rw [mul_assoc]
        _ = rankOne τ K r a * (rankOne τ K r' b * nWC τ K u) := by
            rw [nWC_conj_rankOne (hw := hw) u h2 b]
        _ = (rankOne τ K r a * rankOne τ K r' b) * nWC τ K u := by rw [mul_assoc]
    have hi : (nWC τ K u)⁻¹ * (rankOne τ K r a * rankOne τ K r' b) =
        (rankOne τ K r a * rankOne τ K r' b) * (nWC τ K u)⁻¹ := by
      calc (nWC τ K u)⁻¹ * (rankOne τ K r a * rankOne τ K r' b)
          = ((nWC τ K u)⁻¹ * rankOne τ K r a) * rankOne τ K r' b := by rw [mul_assoc]
        _ = (rankOne τ K r a * (nWC τ K u)⁻¹) * rankOne τ K r' b := by
            rw [inv_mul_of_mul_eq (nWC_conj_rankOne (hw := hw) u h1 a)]
        _ = rankOne τ K r a * ((nWC τ K u)⁻¹ * rankOne τ K r' b) := by rw [mul_assoc]
        _ = rankOne τ K r a * (rankOne τ K r' b * (nWC τ K u)⁻¹) := by
            rw [inv_mul_of_mul_eq (nWC_conj_rankOne (hw := hw) u h2 b)]
        _ = (rankOne τ K r a * rankOne τ K r' b) * (nWC τ K u)⁻¹ := by rw [mul_assoc]
    exact ⟨⟨a, b, hf⟩, ⟨a, b, hi⟩⟩
  · have hf : nWC τ K u * (rankOne τ K r a * rankOne τ K r' b) =
        (rankOne τ K r' a * rankOne τ K r b) * nWC τ K u := by
      calc nWC τ K u * (rankOne τ K r a * rankOne τ K r' b)
          = (nWC τ K u * rankOne τ K r a) * rankOne τ K r' b := by rw [mul_assoc]
        _ = (rankOne τ K r' a * nWC τ K u) * rankOne τ K r' b := by
            rw [nWC_conj_rankOne (hw := hw) u h1 a]
        _ = rankOne τ K r' a * (nWC τ K u * rankOne τ K r' b) := by rw [mul_assoc]
        _ = rankOne τ K r' a * (rankOne τ K r b * nWC τ K u) := by
            rw [nWC_conj_rankOne (hw := hw) u h2 b]
        _ = (rankOne τ K r' a * rankOne τ K r b) * nWC τ K u := by rw [mul_assoc]
    have hi : (nWC τ K u)⁻¹ * (rankOne τ K r a * rankOne τ K r' b) =
        (rankOne τ K r' a * rankOne τ K r b) * (nWC τ K u)⁻¹ := by
      calc (nWC τ K u)⁻¹ * (rankOne τ K r a * rankOne τ K r' b)
          = ((nWC τ K u)⁻¹ * rankOne τ K r a) * rankOne τ K r' b := by rw [mul_assoc]
        _ = (rankOne τ K r' a * (nWC τ K u)⁻¹) * rankOne τ K r' b := by
            rw [inv_mul_of_mul_eq (nWC_conj_rankOne (hw := hw) u h2 a)]
        _ = rankOne τ K r' a * ((nWC τ K u)⁻¹ * rankOne τ K r' b) := by rw [mul_assoc]
        _ = rankOne τ K r' a * (rankOne τ K r b * (nWC τ K u)⁻¹) := by
            rw [inv_mul_of_mul_eq (nWC_conj_rankOne (hw := hw) u h1 b)]
        _ = (rankOne τ K r' a * rankOne τ K r b) * (nWC τ K u)⁻¹ := by rw [mul_assoc]
    exact ⟨⟨b, a, by rw [hf, ← hcomm b a]⟩, ⟨b, a, by rw [hi, ← hcomm b a]⟩⟩

private theorem map_mem_iSup_orbitSpan {H : Type*} [Group H] (σ : Representation k H V)
    {ι : Type*} (v : ι → V) {z : V} (hz : z ∈ Submodule.span k (Set.range v)) (h : H) :
    σ h z ∈ ⨆ j, orbitSpan σ (v j) := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨j, rfl⟩ := hz
    exact Submodule.mem_iSup_of_mem j (Submodule.subset_span ⟨h, rfl⟩)
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha

private noncomputable def leviModule {r r' : Fin τ.rank} {ι : Type*}
    (ρ : Representation k (adjointGroup τ K) V) (a : ι → SL(2, K)) (y : V) : Submodule k V :=
  ⨆ j, orbitSpan (ρ.comp (rankOne τ K r')) (ρ (rankOne τ K r (a j)) y)

private theorem levi_copies_inner [Module.Finite k V]
    {ρ : Representation k (adjointGroup τ K) V} (hρ : IsSimpleRep ρ) {y : V}
    {χ : adjointGroup τ K → k} {J : Finset (Fin τ.rank)}
    (ht : IsChevType τ K 2 hw ρ y χ J) {r r' : Fin τ.rank}
    (hcomm : ∀ a b : SL(2, K),
      rankOne τ K r a * rankOne τ K r' b = rankOne τ K r' b * rankOne τ K r a)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → SL(2, K))
    (hli : LinearIndependent k (fun j => ρ (rankOne τ K r (a j)) y))
    (hspan : orbitSpan (ρ.comp (rankOne τ K r)) y ≤
      Submodule.span k (Set.range fun j => ρ (rankOne τ K r (a j)) y)) :
    ∃ N : Submodule k V,
      N = leviModule (r := r) (r' := r') ρ a y ∧
        Module.finrank k N = Fintype.card ι *
          Module.finrank k (orbitSpan (ρ.comp (rankOne τ K r')) y) ∧
        y ∈ N ∧
        (∀ f ∈ N, (∀ c : K, ρ (rankOne τ K r (uElt c)) f = f) →
          (∀ c : K, ρ (rankOne τ K r' (uElt c)) f = f) → ∃ c : k, f = c • y) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set D := chevDatum τ K 2 hw with hD
  set σ : Representation k SL(2, K) V := ρ.comp (rankOne τ K r') with hσ
  set σr : Representation k SL(2, K) V := ρ.comp (rankOne τ K r) with hσr
  set v : ι → V := fun j => ρ (rankOne τ K r (a j)) y with hv
  set Fix : ι → Submodule k V := fun j =>
    (fixSub ρ (D.Us r')).map (ρ (rankOne τ K r (a j))) with hFix
  have hyFix : y ∈ fixSub ρ (D.Us r') := fun q hq => ht.1 q (D.Us_le r' hq)
  have hyu' : ∀ c : K, σ (uElt c) y = y := by
    intro c
    show ρ (rankOne τ K r' (uElt c)) y = y
    rw [rankOne_u]
    exact ht.1 _ (D.X_le r' (xC_mem_X r' c))
  have hyu : ∀ c : K, σr (uElt c) y = y := by
    intro c
    show ρ (rankOne τ K r (uElt c)) y = y
    rw [rankOne_u]
    exact ht.1 _ (D.X_le r (xC_mem_X r c))
  have hcomm' : ∀ j (g' : SL(2, K)) (w : V),
      σ g' (ρ (rankOne τ K r (a j)) w) = ρ (rankOne τ K r (a j)) (σ g' w) := by
    intro j g' w
    show ρ (rankOne τ K r' g') (ρ (rankOne τ K r (a j)) w) =
      ρ (rankOne τ K r (a j)) (ρ (rankOne τ K r' g') w)
    rw [act_mul, act_mul, ← hcomm (a j) g']
  obtain ⟨hxN, hyN⟩ := Us_normalized (hw := hw) (K := K) r'
  obtain ⟨hxNr, hyNr⟩ := Us_normalized (hw := hw) (K := K) r
  obtain ⟨hdim, hfixed, hsup⟩ :=
    finrank_iSup_orbitSpan_of_isPGroup (H := SL(2, K)) (σ := σ)
      (P := (upperHom K).range) (hP := isPGroup_range_upperHom) (v := v) (Fix := Fix)
      (hvF := fun j => Submodule.mem_map_of_mem hyFix)
      (hFst := by
        rintro j g' _ ⟨f, hf, rfl⟩
        rw [hcomm']
        exact Submodule.mem_map_of_mem
          (fixSub_stable_rankOne ρ r' (D.Us r') hxN hyN g' hf))
      (hfix := by
        rintro j _ ⟨f0, hf0, rfl⟩ hfu
        have h1 : ∀ c : K, ρ (xC τ K r' c) f0 = f0 := by
          intro c
          have h2 := hfu (uElt c) (by
            show uElt c ∈ (upperHom K).range
            exact ⟨Multiplicative.ofAdd c, rfl⟩)
          rw [hcomm' j (uElt c) f0] at h2
          have h3 : σ (uElt c) f0 = f0 :=
            (repEquiv ρ (rankOne τ K r (a j))).injective h2
          have h3' : ρ (rankOne τ K r' (uElt c)) f0 = f0 := h3
          rw [rankOne_u] at h3'
          exact h3' 
        obtain ⟨c, hc⟩ := fix_of_highest hρ ht r' hf0 h1
        exact ⟨c, by rw [hc, map_smul]⟩)
      (hvu := by
        rintro j p hp
        obtain ⟨c, rfl⟩ := hp
        show σ (uElt (Multiplicative.toAdd c)) (ρ (rankOne τ K r (a j)) y) =
          ρ (rankOne τ K r (a j)) y
        rw [hcomm' j (uElt (Multiplicative.toAdd c)), hyu' (Multiplicative.toAdd c)])
      (s := Finset.univ) (hli := hli.linearIndepOn (↑(Finset.univ : Finset ι) : Set ι))
  set N : Submodule k V := ⨆ j, orbitSpan σ (v j) with hN
  have hspan_le : Submodule.span k (Set.range v) ≤ orbitSpan σr y := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact Submodule.subset_span ⟨a j, rfl⟩
  have hspan_eq : Submodule.span k (Set.range v) = orbitSpan σr y :=
    le_antisymm hspan_le hspan
  have hNdim : ∀ j, Module.finrank k (orbitSpan σ (v j)) =
      Module.finrank k (orbitSpan σ y) := by
    intro j
    have hmap : orbitSpan σ (v j) = (orbitSpan σ y).map (ρ (rankOne τ K r (a j))) := by
      rw [orbitSpan, orbitSpan, Submodule.map_span, ← Set.range_comp]
      congr 1
      ext w
      simp only [Set.mem_range, Function.comp_apply]
      constructor
      · rintro ⟨g', rfl⟩
        exact ⟨g', (hcomm' j g' y).symm⟩
      · rintro ⟨g', rfl⟩
        exact ⟨g', hcomm' j g' y⟩
    rw [hmap]
    exact (repEquiv ρ (rankOne τ K r (a j))).finrank_map_eq _
  have hyN : y ∈ N := by
    have hySpan : y ∈ Submodule.span k (Set.range v) := by
      rw [hspan_eq]
      exact mem_orbitSpan_self σr y
    rw [hN]
    exact Submodule.span_le.2 (by
      rintro _ ⟨j, rfl⟩
      exact Submodule.mem_iSup_of_mem j (mem_orbitSpan_self σ (v j))) hySpan
  have hNfix : ∀ f ∈ N, (∀ c : K, ρ (rankOne τ K r (uElt c)) f = f) →
      (∀ c : K, ρ (rankOne τ K r' (uElt c)) f = f) → ∃ c : k, f = c • y := by
    intro f hfN hfr hfr'
    have hfP : f ∈ fixSub σ (upperHom K).range := mem_fixSub_upper.2 hfr'
    have hfspan : f ∈ Submodule.span k (v '' (↑(Finset.univ : Finset ι) : Set ι)) := by
      rw [hN] at hfN
      exact hfixed f (by simpa using hfN) hfP
    have hfv : f ∈ Submodule.span k (Set.range v) := by simpa using hfspan
    have hfNr : f ∈ orbitSpan σr y := hspan_eq ▸ hfv
    have hNrFix : orbitSpan σr y ≤ fixSub ρ (D.Us r) := by
      rw [orbitSpan, Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      exact fixSub_stable_rankOne ρ r (D.Us r) hxNr hyNr g
        (fun q hq => ht.1 q (D.Us_le r hq))
    have h1 : ∀ c : K, ρ (xC τ K r c) f = f := by
      intro c
      have := hfr c
      rwa [rankOne_u] at this
    exact fix_of_highest hρ ht r (hNrFix hfNr) h1
  have hNdef : N = leviModule (r := r) (r' := r') ρ a y := by
    rw [hN, hσ, hv]
    rfl
  refine ⟨N, hNdef, ?_, hyN, hNfix⟩
  rw [hN]
  have hdim' : Module.finrank k (⨆ j, orbitSpan σ (v j) : Submodule k V) =
      ∑ j : ι, Module.finrank k (orbitSpan σ (v j)) := by
    rw [show (⨆ j, orbitSpan σ (v j) : Submodule k V) =
        ⨆ j ∈ (Finset.univ : Finset ι), orbitSpan σ (v j) from by simp]
    simpa using hdim
  calc Module.finrank k (⨆ j, orbitSpan σ (v j) : Submodule k V)
      = ∑ j : ι, Module.finrank k (orbitSpan σ (v j)) := hdim'
    _ = ∑ _j : ι, Module.finrank k (orbitSpan σ y) :=
        Finset.sum_congr rfl fun j _ => hNdim j
    _ = Fintype.card ι * Module.finrank k (orbitSpan σ y) := by
        simp [Finset.sum_const, Finset.card_univ]

private noncomputable def leviProductRep {r r' : Fin τ.rank}
    (hcomm : ∀ a b : SL(2, K),
      rankOne τ K r a * rankOne τ K r' b = rankOne τ K r' b * rankOne τ K r a)
    {ρ : Representation k (adjointGroup τ K) V} :
    Representation k (SL(2, K) × SL(2, K)) V where
  toFun p := ρ (rankOne τ K r p.1 * rankOne τ K r' p.2)
  map_one' := by simp
  map_mul' p q := by
    change ρ (rankOne τ K r (p.1 * q.1) * rankOne τ K r' (p.2 * q.2)) =
      ρ (rankOne τ K r p.1 * rankOne τ K r' p.2) *
        ρ (rankOne τ K r q.1 * rankOne τ K r' q.2)
    have h1 : rankOne τ K r (p.1 * q.1) * rankOne τ K r' (p.2 * q.2) =
        (rankOne τ K r p.1 * rankOne τ K r' p.2) *
          (rankOne τ K r q.1 * rankOne τ K r' q.2) := by
      rw [map_mul, map_mul]
      calc (rankOne τ K r p.1 * rankOne τ K r q.1) *
            (rankOne τ K r' p.2 * rankOne τ K r' q.2)
          = rankOne τ K r p.1 * (rankOne τ K r q.1 * rankOne τ K r' p.2) *
              rankOne τ K r' q.2 := by group
        _ = rankOne τ K r p.1 * (rankOne τ K r' p.2 * rankOne τ K r q.1) *
              rankOne τ K r' q.2 := by rw [hcomm q.1 p.2]
        _ = (rankOne τ K r p.1 * rankOne τ K r' p.2) *
              (rankOne τ K r q.1 * rankOne τ K r' q.2) := by group
    rw [h1, map_mul]

private theorem levi_conj_id_eq (hw : ∃ w₁ : WeylGroup τ, ∀ α : Fin τ.rank → ℤ, w₁ • α = -α)
    {r r' : Fin τ.rank}
    (_hcomm : ∀ a b : SL(2, K),
      rankOne τ K r a * rankOne τ K r' b = rankOne τ K r' b * rankOne τ K r a)
    {u : WeylGroup τ}
    (h1 : u • (Pi.single r 1 : Fin τ.rank → ℤ) = Pi.single r 1)
    (h2 : u • (Pi.single r' 1 : Fin τ.rank → ℤ) = Pi.single r' 1)
    (p : SL(2, K) × SL(2, K)) :
    (nWC τ K u)⁻¹ * (rankOne τ K r p.1 * rankOne τ K r' p.2) * nWC τ K u =
      rankOne τ K r p.1 * rankOne τ K r' p.2 := by
  have e1 : (nWC τ K u)⁻¹ * rankOne τ K r p.1 * nWC τ K u = rankOne τ K r p.1 := by
    have h := inv_mul_of_mul_eq (nWC_conj_rankOne (hw := hw) u h1 p.1)
    calc (nWC τ K u)⁻¹ * rankOne τ K r p.1 * nWC τ K u
        = (rankOne τ K r p.1 * (nWC τ K u)⁻¹) * nWC τ K u := by rw [h]
      _ = rankOne τ K r p.1 := by group
  have e2 : (nWC τ K u)⁻¹ * rankOne τ K r' p.2 * nWC τ K u = rankOne τ K r' p.2 := by
    have h := inv_mul_of_mul_eq (nWC_conj_rankOne (hw := hw) u h2 p.2)
    calc (nWC τ K u)⁻¹ * rankOne τ K r' p.2 * nWC τ K u
        = (rankOne τ K r' p.2 * (nWC τ K u)⁻¹) * nWC τ K u := by rw [h]
      _ = rankOne τ K r' p.2 := by group
  rw [show (nWC τ K u)⁻¹ * (rankOne τ K r p.1 * rankOne τ K r' p.2) * nWC τ K u =
      ((nWC τ K u)⁻¹ * rankOne τ K r p.1 * nWC τ K u) *
        ((nWC τ K u)⁻¹ * rankOne τ K r' p.2 * nWC τ K u) by group, e1, e2]

private theorem levi_conj_swap_eq (hw : ∃ w₁ : WeylGroup τ, ∀ α : Fin τ.rank → ℤ, w₁ • α = -α)
    {r r' : Fin τ.rank}
    (hcomm : ∀ a b : SL(2, K),
      rankOne τ K r a * rankOne τ K r' b = rankOne τ K r' b * rankOne τ K r a)
    {u : WeylGroup τ}
    (h1 : u • (Pi.single r 1 : Fin τ.rank → ℤ) = Pi.single r' 1)
    (h2 : u • (Pi.single r' 1 : Fin τ.rank → ℤ) = Pi.single r 1)
    (p : SL(2, K) × SL(2, K)) :
    (nWC τ K u)⁻¹ * (rankOne τ K r p.1 * rankOne τ K r' p.2) * nWC τ K u =
      rankOne τ K r p.2 * rankOne τ K r' p.1 := by
  have e1 : (nWC τ K u)⁻¹ * rankOne τ K r p.1 * nWC τ K u = rankOne τ K r' p.1 := by
    have h := inv_mul_of_mul_eq (nWC_conj_rankOne (hw := hw) u h2 p.1)
    calc (nWC τ K u)⁻¹ * rankOne τ K r p.1 * nWC τ K u
        = (rankOne τ K r' p.1 * (nWC τ K u)⁻¹) * nWC τ K u := by rw [h]
      _ = rankOne τ K r' p.1 := by group
  have e2 : (nWC τ K u)⁻¹ * rankOne τ K r' p.2 * nWC τ K u = rankOne τ K r p.2 := by
    have h := inv_mul_of_mul_eq (nWC_conj_rankOne (hw := hw) u h1 p.2)
    calc (nWC τ K u)⁻¹ * rankOne τ K r' p.2 * nWC τ K u
        = (rankOne τ K r p.2 * (nWC τ K u)⁻¹) * nWC τ K u := by rw [h]
      _ = rankOne τ K r p.2 := by group
  rw [show (nWC τ K u)⁻¹ * (rankOne τ K r p.1 * rankOne τ K r' p.2) * nWC τ K u =
      ((nWC τ K u)⁻¹ * rankOne τ K r p.1 * nWC τ K u) *
        ((nWC τ K u)⁻¹ * rankOne τ K r' p.2 * nWC τ K u) by group, e1, e2]
  rw [← hcomm p.2 p.1]

private theorem levi_copy_orbit (hw : ∃ w₁ : WeylGroup τ, ∀ α : Fin τ.rank → ℤ, w₁ • α = -α)
    {r r' : Fin τ.rank}
    (hcomm : ∀ a b : SL(2, K),
      rankOne τ K r a * rankOne τ K r' b = rankOne τ K r' b * rankOne τ K r a)
    {u : WeylGroup τ}
    (hu : (u • (Pi.single r 1 : Fin τ.rank → ℤ) = Pi.single r 1 ∧
        u • (Pi.single r' 1 : Fin τ.rank → ℤ) = Pi.single r' 1) ∨
      (u • (Pi.single r 1 : Fin τ.rank → ℤ) = Pi.single r' 1 ∧
        u • (Pi.single r' 1 : Fin τ.rank → ℤ) = Pi.single r 1))
    {ρ : Representation k (adjointGroup τ K) V} {y : V} :
    orbitSpan (leviProductRep hcomm (ρ := ρ)) (ρ (nWC τ K u) y) =
      (orbitSpan (leviProductRep hcomm (ρ := ρ)) y).map (ρ (nWC τ K u)) := by
  apply le_antisymm
  · rw [orbitSpan, Submodule.span_le]
    rintro _ ⟨h, rfl⟩
    obtain ⟨hcfwd_ex, hcinv_ex⟩ := nWC_mul_prod (hw := hw) hu hcomm h.1 h.2
    obtain ⟨c', d', hcinv⟩ := hcinv_ex
    have hxn : (rankOne τ K r h.1 * rankOne τ K r' h.2) * nWC τ K u =
        nWC τ K u * (rankOne τ K r c' * rankOne τ K r' d') := by
      have hkey : (nWC τ K u)⁻¹ * (rankOne τ K r h.1 * rankOne τ K r' h.2) *
          nWC τ K u = rankOne τ K r c' * rankOne τ K r' d' := by
        have hh := hcinv
        calc (nWC τ K u)⁻¹ * (rankOne τ K r h.1 * rankOne τ K r' h.2) * nWC τ K u
            = ((rankOne τ K r c' * rankOne τ K r' d') * (nWC τ K u)⁻¹) * nWC τ K u := by
              rw [hh]
          _ = rankOne τ K r c' * rankOne τ K r' d' := by group
      calc (rankOne τ K r h.1 * rankOne τ K r' h.2) * nWC τ K u
          = nWC τ K u * ((nWC τ K u)⁻¹ *
              (rankOne τ K r h.1 * rankOne τ K r' h.2) * nWC τ K u) := by group
        _ = nWC τ K u * (rankOne τ K r c' * rankOne τ K r' d') := by rw [hkey]
    have hstep : (leviProductRep hcomm (ρ := ρ)) h (ρ (nWC τ K u) y) =
        ρ (nWC τ K u) ((leviProductRep hcomm (ρ := ρ)) (c', d') y) := by
      show ρ (rankOne τ K r h.1 * rankOne τ K r' h.2) (ρ (nWC τ K u) y) =
        ρ (nWC τ K u) (ρ (rankOne τ K r c' * rankOne τ K r' d') y)
      rw [act_mul, hxn]
      exact (act_mul ρ (nWC τ K u) (rankOne τ K r c' * rankOne τ K r' d') y).symm
    change (leviProductRep hcomm (ρ := ρ)) h (ρ (nWC τ K u) y) ∈
      (orbitSpan (leviProductRep hcomm (ρ := ρ)) y).map (ρ (nWC τ K u))
    rw [hstep]
    exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨(c', d'), rfl⟩)
  · rw [Submodule.map_le_iff_le_comap]
    rw [orbitSpan, Submodule.span_le]
    rintro _ ⟨h, rfl⟩
    obtain ⟨hcfwd_ex, hcinv_ex⟩ := nWC_mul_prod (hw := hw) hu hcomm h.1 h.2
    obtain ⟨c, d, hcfwd⟩ := hcfwd_ex
    have hstep : ρ (nWC τ K u) ((leviProductRep hcomm (ρ := ρ)) h y) =
        (leviProductRep hcomm (ρ := ρ)) (c, d) (ρ (nWC τ K u) y) := by
      show ρ (nWC τ K u) (ρ (rankOne τ K r h.1 * rankOne τ K r' h.2) y) =
        ρ (rankOne τ K r c * rankOne τ K r' d) (ρ (nWC τ K u) y)
      rw [act_mul, hcfwd]
      exact (act_mul ρ (rankOne τ K r c * rankOne τ K r' d) (nWC τ K u) y).symm
    change ρ (nWC τ K u) ((leviProductRep hcomm (ρ := ρ)) h y) ∈
      orbitSpan (leviProductRep hcomm (ρ := ρ)) (ρ (nWC τ K u) y)
    rw [hstep]
    exact Submodule.subset_span ⟨(c, d), rfl⟩

private theorem rankOne_upper_fixes {r : Fin τ.rank}
    {ρ : Representation k (adjointGroup τ K) V} {y : V} {χ : adjointGroup τ K → k}
    {J : Finset (Fin τ.rank)} (ht : IsChevType τ K 2 hw ρ y χ J)
    {a : SL(2, K)} (ha : a ∈ (upperHom K).range) :
    ρ (rankOne τ K r a) y = y := by
  obtain ⟨c, rfl⟩ := ha
  show ρ (rankOne τ K r (uElt (Multiplicative.toAdd c))) y = y
  rw [rankOne_u]
  exact ht.1 _ ((chevDatum τ K 2 hw).X_le r (xC_mem_X r _))

private theorem leviModule_le_orbit {r r' : Fin τ.rank} {ι : Type*}
    {ρ : Representation k (adjointGroup τ K) V} {y : V} (a : ι → SL(2, K))
    (hcomm : ∀ a b : SL(2, K),
      rankOne τ K r a * rankOne τ K r' b = rankOne τ K r' b * rankOne τ K r a) :
    leviModule (r := r) (r' := r') ρ a y ≤
      orbitSpan (leviProductRep hcomm (ρ := ρ)) y := by
  rw [leviModule]
  refine iSup_le fun j => ?_
  rw [orbitSpan, Submodule.span_le]
  rintro _ ⟨h, rfl⟩
  have hvj : (leviProductRep hcomm (ρ := ρ)) (a j, 1) y =
      ρ (rankOne τ K r (a j)) y := by
    show ρ (rankOne τ K r (a j) * rankOne τ K r' 1) y = ρ (rankOne τ K r (a j)) y
    rw [map_one, mul_one]
  have hstep : (ρ.comp (rankOne τ K r')) h (ρ (rankOne τ K r (a j)) y) =
      (leviProductRep hcomm (ρ := ρ)) (1, h)
        ((leviProductRep hcomm (ρ := ρ)) (a j, 1) y) := by
    rw [hvj]
    show ρ (rankOne τ K r' h) (ρ (rankOne τ K r (a j)) y) =
      ρ (rankOne τ K r 1 * rankOne τ K r' h) (ρ (rankOne τ K r (a j)) y)
    rw [map_one, one_mul]
  change (ρ.comp (rankOne τ K r')) h (ρ (rankOne τ K r (a j)) y) ∈
    orbitSpan (leviProductRep hcomm (ρ := ρ)) y
  rw [hstep, act_mul]
  exact Submodule.subset_span ⟨(1, h) * (a j, 1), rfl⟩

private theorem orbit_le_leviModule {r r' : Fin τ.rank} {ι : Type*}
    {ρ : Representation k (adjointGroup τ K) V} {y : V} (a : ι → SL(2, K))
    (hcomm : ∀ a b : SL(2, K),
      rankOne τ K r a * rankOne τ K r' b = rankOne τ K r' b * rankOne τ K r a)
    (hspan : orbitSpan (ρ.comp (rankOne τ K r)) y ≤
      Submodule.span k (Set.range fun j => ρ (rankOne τ K r (a j)) y)) :
    orbitSpan (leviProductRep hcomm (ρ := ρ)) y ≤ leviModule (r := r) (r' := r') ρ a y := by
  rw [orbitSpan, Submodule.span_le]
  rintro _ ⟨h, rfl⟩
  have hmem : ρ (rankOne τ K r h.1) y ∈
      Submodule.span k (Set.range fun j => ρ (rankOne τ K r (a j)) y) :=
    hspan (Submodule.subset_span ⟨h.1, rfl⟩)
  have hstep : (leviProductRep hcomm (ρ := ρ)) h y =
      (ρ.comp (rankOne τ K r')) h.2 (ρ (rankOne τ K r h.1) y) := by
    show ρ (rankOne τ K r h.1 * rankOne τ K r' h.2) y =
      ρ (rankOne τ K r' h.2) (ρ (rankOne τ K r h.1) y)
    rw [hcomm h.1 h.2, act_mul]
  change (leviProductRep hcomm (ρ := ρ)) h y ∈ leviModule (r := r) (r' := r') ρ a y
  rw [hstep]
  exact map_mem_iSup_orbitSpan (ρ.comp (rankOne τ K r'))
    (fun j => ρ (rankOne τ K r (a j)) y) hmem h.2

private theorem levi_op_mul {r r' : Fin τ.rank}
    (hcomm : ∀ a b : SL(2, K),
      rankOne τ K r a * rankOne τ K r' b = rankOne τ K r' b * rankOne τ K r a)
    {ρ : Representation k (adjointGroup τ K) V} {u : WeylGroup τ}
    {p q : SL(2, K) × SL(2, K)}
    (hconj : (nWC τ K u)⁻¹ * (rankOne τ K r p.1 * rankOne τ K r' p.2) * nWC τ K u =
      rankOne τ K r q.1 * rankOne τ K r' q.2) :
    (leviProductRep hcomm (ρ := ρ)) p * ρ (nWC τ K u) =
      ρ (nWC τ K u) * (leviProductRep hcomm (ρ := ρ)) q := by
  have hxn : (rankOne τ K r p.1 * rankOne τ K r' p.2) * nWC τ K u =
      nWC τ K u * (rankOne τ K r q.1 * rankOne τ K r' q.2) := by
    calc (rankOne τ K r p.1 * rankOne τ K r' p.2) * nWC τ K u
        = nWC τ K u * ((nWC τ K u)⁻¹ *
            (rankOne τ K r p.1 * rankOne τ K r' p.2) * nWC τ K u) := by group
      _ = nWC τ K u * (rankOne τ K r q.1 * rankOne τ K r' q.2) := by rw [hconj]
  change ρ (rankOne τ K r p.1 * rankOne τ K r' p.2) * ρ (nWC τ K u) =
    ρ (nWC τ K u) * ρ (rankOne τ K r q.1 * rankOne τ K r' q.2)
  rw [← map_mul, hxn, map_mul]

theorem levi_copies_finrank [Module.Finite k V] {ρ : Representation k (adjointGroup τ K) V}
    (hρ : IsSimpleRep ρ) {y : V} {χ : adjointGroup τ K → k} {J : Finset (Fin τ.rank)}
    (ht : IsChevType τ K 2 hw ρ y χ J) {r r' : Fin τ.rank} (hrr' : r ≠ r')
    (hcomm : ∀ a b : SL(2, K),
      rankOne τ K r a * rankOne τ K r' b = rankOne τ K r' b * rankOne τ K r a)
    {m : ℕ} (u : Fin m → WeylGroup τ)
    (hu : ∀ i, (u i • (Pi.single r 1 : Fin τ.rank → ℤ) = Pi.single r 1 ∧
        u i • (Pi.single r' 1 : Fin τ.rank → ℤ) = Pi.single r' 1) ∨
      (u i • (Pi.single r 1 : Fin τ.rank → ℤ) = Pi.single r' 1 ∧
        u i • (Pi.single r' 1 : Fin τ.rank → ℤ) = Pi.single r 1))
    (hli : LinearIndependent k (fun i => ρ (nWC τ K (u i)) y)) :
    m * (Module.finrank k (orbitSpan (ρ.comp (rankOne τ K r)) y) *
      Module.finrank k (orbitSpan (ρ.comp (rankOne τ K r')) y)) ≤ Module.finrank k V := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have _ := hrr'
  obtain ⟨t, hts, hcard, hspan_t, hliOn⟩ :=
    Submodule.exists_finset_span_eq_linearIndepOn (K := k) (M := V)
      (Set.range (fun g : SL(2, K) => ρ (rankOne τ K r g) y))
  let ι := {x : V // x ∈ t}
  have hex : ∀ x : ι, ∃ g : SL(2, K), ρ (rankOne τ K r g) y = x.1 := fun x =>
    Set.mem_range.mp (hts x.2)
  choose a ha using hex
  have hrange : Set.range (fun j : ι => ρ (rankOne τ K r (a j)) y) = (↑t : Set V) := by
    ext z
    constructor
    · rintro ⟨j, rfl⟩
      show ρ (rankOne τ K r (a j)) y ∈ (↑t : Set V)
      rw [ha j]
      simp
    · intro hz
      exact ⟨⟨z, hz⟩, ha ⟨z, hz⟩⟩
  have hli' : LinearIndependent k (fun j : ι => ρ (rankOne τ K r (a j)) y) := by
    have hfun : (fun j : ι => ρ (rankOne τ K r (a j)) y) = fun j : ι => j.1 := by
      funext j
      simpa using ha j
    rw [hfun]
    simpa using hliOn.linearIndependent
  have hspan_eq : Submodule.span k (Set.range fun j : ι => ρ (rankOne τ K r (a j)) y) =
      orbitSpan (ρ.comp (rankOne τ K r)) y := by
    rw [hrange, hspan_t]
    rfl
  have hspan : orbitSpan (ρ.comp (rankOne τ K r)) y ≤
      Submodule.span k (Set.range fun j : ι => ρ (rankOne τ K r (a j)) y) := hspan_eq.ge
  obtain ⟨N, hNdef, hNdim, hyN, hNfix⟩ :=
    levi_copies_inner hρ ht hcomm a hli' hspan
  have hcardι : Fintype.card ι =
      Module.finrank k (orbitSpan (ρ.comp (rankOne τ K r)) y) := by
    rw [show Fintype.card ι = t.card from Fintype.card_coe t, hcard]
    rfl
  have hNdim' : Module.finrank k N =
      Module.finrank k (orbitSpan (ρ.comp (rankOne τ K r)) y) *
        Module.finrank k (orbitSpan (ρ.comp (rankOne τ K r')) y) := by
    rw [hNdim, hcardι]
  set σ' : Representation k (SL(2, K) × SL(2, K)) V := leviProductRep hcomm (ρ := ρ) with hσ'
  have hN_orbit : N = orbitSpan σ' y := by
    rw [hNdef, hσ']
    exact le_antisymm (leviModule_le_orbit a hcomm) (orbit_le_leviModule a hcomm hspan)
  have hcopy : ∀ i, orbitSpan σ' (ρ (nWC τ K (u i)) y) =
      N.map (ρ (nWC τ K (u i))) := by
    intro i
    rw [hσ']
    rw [levi_copy_orbit (hw := hw) hcomm (hu := hu i)]
    rw [← hN_orbit]
  set P : Subgroup (SL(2, K) × SL(2, K)) :=
    (upperHom K).range.prod (upperHom K).range with hPdef
  have hP : IsPGroup 2 P :=
    isPGroup_prod_subgroup _ _ isPGroup_range_upperHom isPGroup_range_upperHom
  set v : Fin m → V := fun i => ρ (nWC τ K (u i)) y with hvdef
  set Fix : Fin m → Submodule k V := fun i => N.map (ρ (nWC τ K (u i))) with hFixdef
  have hFix_copy : ∀ i, Fix i = orbitSpan σ' (v i) := by
    intro i
    change N.map (ρ (nWC τ K (u i))) = orbitSpan σ' (ρ (nWC τ K (u i)) y)
    rw [← hcopy i]
  have hvu : ∀ i, v i ∈ fixSub σ' P := by
    intro i
    rw [mem_fixSub]
    intro p hp
    obtain ⟨hp1, hp2⟩ := Subgroup.mem_prod.mp hp
    rcases hu i with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hconj := levi_conj_id_eq (hw := hw) hcomm h1 h2 p
      have hop := levi_op_mul (ρ := ρ) hcomm (u := u i) hconj
      have hy1 : (leviProductRep hcomm (ρ := ρ)) p y = y := by
        change ρ (rankOne τ K r p.1 * rankOne τ K r' p.2) y = y
        rw [← act_mul, rankOne_upper_fixes (r := r') ht hp2,
          rankOne_upper_fixes (r := r) ht hp1]
      have h : (leviProductRep hcomm (ρ := ρ)) p (ρ (nWC τ K (u i)) y) =
          ρ (nWC τ K (u i)) ((leviProductRep hcomm (ρ := ρ)) p y) := by
        have := congrArg (fun T => T y) hop
        simpa only [Module.End.mul_apply] using this
      rw [hy1] at h
      exact h
    · have hconj := levi_conj_swap_eq (hw := hw) hcomm h1 h2 p
      have hop := levi_op_mul (ρ := ρ) hcomm (u := u i) (q := (p.2, p.1)) hconj
      have hy1 : (leviProductRep hcomm (ρ := ρ)) (p.2, p.1) y = y := by
        change ρ (rankOne τ K r p.2 * rankOne τ K r' p.1) y = y
        rw [← act_mul, rankOne_upper_fixes (r := r') ht hp1,
          rankOne_upper_fixes (r := r) ht hp2]
      have h : (leviProductRep hcomm (ρ := ρ)) p (ρ (nWC τ K (u i)) y) =
          ρ (nWC τ K (u i)) ((leviProductRep hcomm (ρ := ρ)) (p.2, p.1) y) := by
        have := congrArg (fun T => T y) hop
        simpa only [Module.End.mul_apply] using this
      rw [hy1] at h
      exact h
  have hFst : ∀ i, ∀ h : SL(2, K) × SL(2, K), ∀ w ∈ Fix i, σ' h w ∈ Fix i := by
    rintro i h w ⟨z, hzN, rfl⟩
    rcases hu i with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hconj := levi_conj_id_eq (hw := hw) hcomm h1 h2 h
      have hop := levi_op_mul (ρ := ρ) hcomm (u := u i) hconj
      have hstep : σ' h (ρ (nWC τ K (u i)) z) =
          ρ (nWC τ K (u i)) ((leviProductRep hcomm (ρ := ρ)) h z) := by
        have := congrArg (fun T => T z) hop
        simpa only [Module.End.mul_apply] using this
      rw [hstep]
      refine Submodule.mem_map_of_mem ?_
      have hz' : z ∈ orbitSpan σ' y := by rwa [hN_orbit] at hzN
      rw [hN_orbit]
      exact orbitSpan_stable σ' y h hz'
    · have hconj := levi_conj_swap_eq (hw := hw) hcomm h1 h2 h
      have hop := levi_op_mul (ρ := ρ) hcomm (u := u i) (q := (h.2, h.1)) hconj
      have hstep : σ' h (ρ (nWC τ K (u i)) z) =
          ρ (nWC τ K (u i)) ((leviProductRep hcomm (ρ := ρ)) (h.2, h.1) z) := by
        have := congrArg (fun T => T z) hop
        simpa only [Module.End.mul_apply] using this
      rw [hstep]
      refine Submodule.mem_map_of_mem ?_
      have hz' : z ∈ orbitSpan σ' y := by rwa [hN_orbit] at hzN
      rw [hN_orbit]
      exact orbitSpan_stable σ' y (h.2, h.1) hz'
  have hfix : ∀ i, ∀ f ∈ Fix i, f ∈ fixSub σ' P → ∃ c : k, f = c • v i := by
    rintro i f hfFix hfP
    rw [hFixdef] at hfFix
    obtain ⟨f0, hf0N, rfl⟩ := hfFix
    have hf0P : f0 ∈ fixSub σ' P := by
      rw [mem_fixSub]
      intro p hp
      obtain ⟨hp1, hp2⟩ := Subgroup.mem_prod.mp hp
      rcases hu i with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hconj := levi_conj_id_eq (hw := hw) hcomm h1 h2 p
        have hop := levi_op_mul (ρ := ρ) hcomm (u := u i) hconj
        have h := congrArg (fun T => T f0) hop
        rw [Module.End.mul_apply, Module.End.mul_apply] at h
        have hfixp := hfP p hp
        rw [hfixp] at h
        exact (repEquiv ρ (nWC τ K (u i))).injective h.symm
      · have hconj := levi_conj_swap_eq (hw := hw) hcomm h1 h2 (p.2, p.1)
        have hop := levi_op_mul (ρ := ρ) hcomm (u := u i) (q := p) hconj
        have hp' : (p.2, p.1) ∈ P := Subgroup.mem_prod.mpr ⟨hp2, hp1⟩
        have h := congrArg (fun T => T f0) hop
        rw [Module.End.mul_apply, Module.End.mul_apply] at h
        have hfixp := hfP (p.2, p.1) hp'
        rw [hfixp] at h
        exact (repEquiv ρ (nWC τ K (u i))).injective h.symm
    have h1 : ∀ c : K, ρ (rankOne τ K r (uElt c)) f0 = f0 := by
      intro c
      have := hf0P (uElt c, 1) (Subgroup.mem_prod.mpr
        ⟨⟨Multiplicative.ofAdd c, rfl⟩, Subgroup.one_mem _⟩)
      have hval : (leviProductRep hcomm (ρ := ρ)) (uElt c, 1) =
          ρ (rankOne τ K r (uElt c)) := by
        show ρ (rankOne τ K r (uElt c) * rankOne τ K r' 1) = ρ (rankOne τ K r (uElt c))
        rw [map_one, mul_one]
      rw [hval] at this
      exact this
    have h2 : ∀ c : K, ρ (rankOne τ K r' (uElt c)) f0 = f0 := by
      intro c
      have := hf0P (1, uElt c) (Subgroup.mem_prod.mpr
        ⟨Subgroup.one_mem _, ⟨Multiplicative.ofAdd c, rfl⟩⟩)
      have hval : (leviProductRep hcomm (ρ := ρ)) (1, uElt c) =
          ρ (rankOne τ K r' (uElt c)) := by
        show ρ (rankOne τ K r 1 * rankOne τ K r' (uElt c)) = ρ (rankOne τ K r' (uElt c))
        rw [map_one, one_mul]
      rw [hval] at this
      exact this
    obtain ⟨c, hc⟩ := hNfix f0 hf0N h1 h2
    exact ⟨c, by rw [hc, map_smul]⟩
  have hliP : LinearIndepOn k v (↑(Finset.univ : Finset (Fin m)) : Set (Fin m)) :=
    hli.linearIndepOn _
  obtain ⟨hdimP, -, -⟩ :=
    finrank_iSup_orbitSpan_of_isPGroup (H := SL(2, K) × SL(2, K)) (σ := σ')
      (P := P) (hP := hP) (v := v) (Fix := Fix)
      (hvF := fun i => by
        rw [hFixdef]
        exact Submodule.mem_map_of_mem hyN)
      (hFst := hFst) (hfix := hfix) (hvu := hvu)
      (s := Finset.univ) (hli := hliP)
  have hfin : ∀ i : Fin m, Module.finrank k (orbitSpan σ' (v i)) = Module.finrank k N := by
    intro i
    rw [← hFix_copy i]
    rw [hFixdef]
    exact (repEquiv ρ (nWC τ K (u i))).finrank_map_eq N
  have hsum : ∑ i : Fin m, Module.finrank k (orbitSpan σ' (v i)) =
      m * Module.finrank k N := by
    calc ∑ i : Fin m, Module.finrank k (orbitSpan σ' (v i))
        = ∑ _i : Fin m, Module.finrank k N := Finset.sum_congr rfl (fun i _ => hfin i)
      _ = m * Module.finrank k N := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  calc m * (Module.finrank k (orbitSpan (ρ.comp (rankOne τ K r)) y) *
        Module.finrank k (orbitSpan (ρ.comp (rankOne τ K r')) y))
      = m * Module.finrank k N := by rw [hNdim']
    _ = ∑ i : Fin m, Module.finrank k (orbitSpan σ' (v i)) := hsum.symm
    _ = Module.finrank k (⨆ i ∈ (Finset.univ : Finset (Fin m)), orbitSpan σ' (v i) :
        Submodule k V) := hdimP.symm
    _ ≤ Module.finrank k V := Submodule.finrank_le _

theorem levi_copies_two_pow [Module.Finite k V] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {ρ : Representation k (adjointGroup τ K) V} (hρ : IsSimpleRep ρ) {y : V}
    {χ : adjointGroup τ K → k} {J : Finset (Fin τ.rank)} (ht : IsChevType τ K 2 hw ρ y χ J)
    {r r' : Fin τ.rank} (hrr' : r ≠ r') (hr : r ∉ J) (hr' : r' ∉ J)
    (hcomm : ∀ a b : SL(2, K),
      rankOne τ K r a * rankOne τ K r' b = rankOne τ K r' b * rankOne τ K r a)
    {g : ℕ} (hg : 1 ≤ g) (hgn : g ∣ n)
    (hper : ∀ z : Kˣ, χ (dC τ K r z) ^ (2 ^ g) = χ (dC τ K r z))
    (hper' : ∀ z : Kˣ, χ (dC τ K r' z) ^ (2 ^ g) = χ (dC τ K r' z))
    {m : ℕ} (u : Fin m → WeylGroup τ)
    (hu : ∀ i, (u i • (Pi.single r 1 : Fin τ.rank → ℤ) = Pi.single r 1 ∧
        u i • (Pi.single r' 1 : Fin τ.rank → ℤ) = Pi.single r' 1) ∨
      (u i • (Pi.single r 1 : Fin τ.rank → ℤ) = Pi.single r' 1 ∧
        u i • (Pi.single r' 1 : Fin τ.rank → ℤ) = Pi.single r 1))
    (hli : LinearIndependent k (fun i => ρ (nWC τ K (u i)) y)) :
    m * (2 ^ (n / g) * 2 ^ (n / g)) ≤ Module.finrank k V := by
  have h1 := two_pow_le_finrank_orbitSpan (hw := hw) hn hK hρ ht hr hg hgn hper
  have h2 := two_pow_le_finrank_orbitSpan (hw := hw) hn hK hρ ht hr' hg hgn hper'
  calc m * (2 ^ (n / g) * 2 ^ (n / g))
      ≤ m * (Module.finrank k (orbitSpan (ρ.comp (rankOne τ K r)) y) *
          Module.finrank k (orbitSpan (ρ.comp (rankOne τ K r')) y)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul h1 h2)
    _ ≤ Module.finrank k V := levi_copies_finrank hρ ht hrr' hcomm u hu hli

end Levi

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc
